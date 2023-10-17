// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

//! Runtime representation of access control specifiers.
//!
//! Specifiers are represented as a list of inclusion and exclusion clauses. Each
//! of those clauses corresponds to an `acquires A`, `reads A`, or `writes A`
//! declaration in the language. Exclusions stem from negation, e.g. `!reads A`.
//!
//! Specifiers support access check via `AccessSpecifier::allows`. Moreover,
//! access specifiers can be joined via `AccessSpecifier::join`. Joining happens
//! when a function is entered which has access specifiers: then the current active access
//! specifier is joined with the function's specifier.
//!
//! The `join` operation attempts to simplify the resulting access specifier, making
//! access checks faster and keeping memory use low. This is only implemented for
//! inclusions, which are fully simplified. Exclusions are accumulated.
//! There is potential for optimization by simplifying exclusions are effectively negations,
//! such a simplification is not trivial and may require recursive specifiers, which
//! we like to avoid.

use crate::{
    loaded_data::runtime_types::{StructIdentifier, Type},
    values::Value,
};
use itertools::Itertools;
use move_binary_format::{errors::PartialVMResult, file_format, file_format::LocalIndex};
use move_core_types::{account_address::AccountAddress, language_storage::ModuleId};
use std::{fmt, fmt::Debug};

/// Represents an access specifier.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
pub enum AccessSpecifier {
    /// Universal access granted
    Any,
    /// A constraint in normalized form: `Constraint(inclusions, exclusions)`.
    /// The inclusions are a _disjunction_ and the exclusions a _conjunction_ of
    /// access clauses. An access is valid if it is allowed by any of the
    /// inclusions, and not allowed for each of the exclusions.
    Constraint(Vec<AccessSpecifierClause>, Vec<AccessSpecifierClause>),
}

/// Represents an access specifier clause
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
pub struct AccessSpecifierClause {
    pub kind: file_format::AccessKind,
    pub resource: ResourceSpecifier,
    pub address: AddressSpecifier,
}

/// Represents a resource specifier.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
pub enum ResourceSpecifier {
    Any,
    DeclaredAtAddress(AccountAddress),
    DeclaredInModule(ModuleId),
    Resource(StructIdentifier),
    ResourceInstantiation(StructIdentifier, Vec<Type>),
}

/// Represents an address specifier.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
pub enum AddressSpecifier {
    Any,
    Literal(AccountAddress),
    /// The `Eval` specifier represents a value dependent on a parameter of the
    /// current function. Once address specifiers are instantiated in a given
    /// caller context it is replaced by a literal.
    Eval(AddressSpecifierFunction, LocalIndex),
}

/// Represents a well-known function used in an address specifier.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy, Debug)]
pub enum AddressSpecifierFunction {
    Identity,
    SignerAddress,
    ObjectAddress,
}

/// A trait representing an environment for evaluating dynamic values in access specifiers.
pub trait AccessSpecifierEnv {
    fn eval_address_specifier_function(
        &self,
        fun: AddressSpecifierFunction,
        local: LocalIndex,
    ) -> PartialVMResult<AccountAddress>;
}

/// A struct to represent an access.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
pub struct AccessInstance {
    pub kind: file_format::AccessKind,
    pub resource: StructIdentifier,
    pub instance: Vec<Type>,
    pub address: AccountAddress,
}

impl AccessSpecifier {
    /// Returns true if this access specifier is known to have no accesses. Note that this
    /// may be under-approximated in the presence of exclusions. That is, if
    /// `!s.is_empty()`, it is still possible that all concrete accesses fail.
    pub fn is_empty(&self) -> bool {
        if let AccessSpecifier::Constraint(incl, _) = self {
            incl.is_empty()
        } else {
            false
        }
    }

    /// Specializes the access specifier for the given environment. This evaluates
    /// `AddressSpecifier::Eval` terms.
    pub fn specialize(&mut self, env: &impl AccessSpecifierEnv) -> PartialVMResult<()> {
        match self {
            AccessSpecifier::Any => Ok(()),
            AccessSpecifier::Constraint(incls, excls) => {
                for clause in incls {
                    clause.specialize(env)?;
                }
                for clause in excls {
                    clause.specialize(env)?;
                }
                Ok(())
            },
        }
    }

    /// Returns true of the concrete access instance is allowed.
    pub fn allows(&self, access: &AccessInstance) -> bool {
        use AccessSpecifier::*;
        match self {
            Any => true,
            Constraint(incls, excls) => {
                incls.iter().any(|c| c.allows(access)) && excls.iter().all(|c| !c.allows(access))
            },
        }
    }

    pub fn join(&self, other: &Self) -> Self {
        use AccessSpecifier::*;
        match (self, other) {
            (Any, s) | (s, Any) => s.clone(),
            (Constraint(incls, excls), Constraint(other_incls, other_excls)) => {
                // Inclusions are disjunctions. The join of two disjunctions is
                //   (a + b) * (c + d) = a*(c + d) + b*(c + d) = a*c + a*d + b*c + b*d
                // For the exclusions, we can simply concatenate them.
                // TODO: this is quadratic and  need to be metered
                let mut new_incls = vec![];
                for incl in incls {
                    for other_incl in other_incls {
                        // try_join returns None if the result is empty.
                        if let Some(new_incl) = incl.join(other_incl) {
                            new_incls.push(new_incl);
                        }
                    }
                }
                if new_incls.is_empty() {
                    // Drop exclusions since they are redundant
                    Constraint(new_incls, vec![])
                } else {
                    Constraint(
                        new_incls,
                        excls
                            .iter()
                            .cloned()
                            .chain(other_excls.iter().cloned())
                            .collect(),
                    )
                }
            },
        }
    }
}

impl AccessSpecifierClause {
    /// Checks whether this clause allows the access.
    fn allows(&self, access: &AccessInstance) -> bool {
        let AccessInstance {
            kind,
            resource,
            instance,
            address,
        } = access;
        if self.kind != file_format::AccessKind::Acquires && &self.kind != kind {
            return false;
        }
        self.resource.allows(resource, instance) && self.address.allows(address)
    }

    /// Specializes this clause.
    fn specialize(&mut self, env: &impl AccessSpecifierEnv) -> PartialVMResult<()> {
        // Only addresses can be specialized right now.
        self.address.specialize(env)
    }

    /// Join two clauses. Returns None if there is no intersection in access.
    fn join(&self, other: &Self) -> Option<Self> {
        let Self {
            kind,
            resource,
            address,
        } = self;
        let Self {
            kind: other_kind,
            resource: other_resource,
            address: other_address,
        } = other;

        kind.try_join(*other_kind).and_then(|kind| {
            resource.join(other_resource).and_then(|resource| {
                address.join(other_address).map(|address| Self {
                    kind,
                    resource,
                    address,
                })
            })
        })
    }
}

/// A few macros to make complex match arms better readable. Those data types are struct with
/// named fields, and formatters tend to layout those very verbose.
macro_rules! module_addr {
    ($addr:pat) => {
        ModuleId { address: $addr, .. }
    };
}

macro_rules! struct_identifier_module {
    ($m:pat) => {
        StructIdentifier { module: $m, .. }
    };
}

macro_rules! struct_identifier_addr {
    ($addr:pat) => {
        struct_identifier_module!(module_addr!($addr))
    };
}

macro_rules! some_if {
    ($val:expr, $check:expr) => {{
        if $check {
            Some($val)
        } else {
            None
        }
    }};
}

impl ResourceSpecifier {
    /// Checks whether the struct/type pair is allowed by this specifier.
    fn allows(&self, struct_id: &StructIdentifier, type_inst: &[Type]) -> bool {
        use ResourceSpecifier::*;
        match self {
            Any => true,
            DeclaredAtAddress(addr) => struct_id.module.address() == addr,
            DeclaredInModule(module_id) => &struct_id.module == module_id,
            Resource(allowed_struct_id) => allowed_struct_id == struct_id,
            ResourceInstantiation(allowed_struct_id, allowed_type_inst) => {
                allowed_struct_id == struct_id && allowed_type_inst == type_inst
            },
        }
    }

    /// Joins two resource specifiers. Returns none of there is no intersection.
    fn join(&self, other: &Self) -> Option<Self> {
        use ResourceSpecifier::*;
        match &self {
            Any => Some(other.clone()),
            DeclaredAtAddress(addr) => match &other {
                Any => Some(self.clone()),
                DeclaredAtAddress(other_addr)
                | DeclaredInModule(module_addr!(other_addr))
                | Resource(struct_identifier_addr!(other_addr))
                | ResourceInstantiation(struct_identifier_addr!(other_addr), _) => {
                    some_if!(other.clone(), addr == other_addr)
                },
            },
            DeclaredInModule(module_id) => match &other {
                Any => Some(self.clone()),
                DeclaredAtAddress(addr) => some_if!(self.clone(), addr == module_id.address()),
                DeclaredInModule(other_module_id)
                | Resource(struct_identifier_module!(other_module_id))
                | ResourceInstantiation(struct_identifier_module!(other_module_id), _) => {
                    some_if!(other.clone(), module_id == other_module_id)
                },
            },
            Resource(struct_id) => match &other {
                Any => Some(self.clone()),
                DeclaredAtAddress(addr) => {
                    some_if!(self.clone(), addr == struct_id.module.address())
                },
                DeclaredInModule(module_id) => {
                    some_if!(self.clone(), module_id == &struct_id.module)
                },
                Resource(other_struct_id) | ResourceInstantiation(other_struct_id, _) => {
                    some_if!(other.clone(), struct_id == other_struct_id)
                },
            },
            ResourceInstantiation(struct_id, inst) => match other {
                Any => Some(self.clone()),
                DeclaredAtAddress(addr) => {
                    some_if!(self.clone(), struct_id.module.address() == addr)
                },
                DeclaredInModule(module_id) => {
                    some_if!(self.clone(), &struct_id.module == module_id)
                },
                Resource(other_struct_id) => some_if!(self.clone(), struct_id == other_struct_id),
                ResourceInstantiation(other_struct_id, other_inst) => {
                    some_if!(
                        self.clone(),
                        struct_id == other_struct_id && inst == other_inst
                    )
                },
            },
        }
    }
}

impl AddressSpecifier {
    /// Checks whether the given address is allowed by this specifier.
    fn allows(&self, addr: &AccountAddress) -> bool {
        use AddressSpecifier::*;
        match self {
            Any => true,
            Literal(a) => a == addr,
            Eval(_, _) => false,
        }
    }

    /// Specializes this specifier, resolving `Eval` variants.
    fn specialize(&mut self, env: &impl AccessSpecifierEnv) -> PartialVMResult<()> {
        if let AddressSpecifier::Eval(fun, arg) = self {
            *self = AddressSpecifier::Literal(env.eval_address_specifier_function(*fun, *arg)?)
        }
        Ok(())
    }

    /// Joins two address specifiers. Returns None if there is no intersection.
    fn join(&self, other: &Self) -> Option<Self> {
        use AddressSpecifier::*;
        match (self, other) {
            (Any, s) | (s, Any) => Some(s.clone()),
            (Literal(a1), Literal(a2)) => some_if!(self.clone(), a1 == a2),
            (_, _) => {
                // Eval should be specialized away when join is called.
                debug_assert!(false, "unexpected AddressSpecifier::Eval found");
                None
            },
        }
    }
}

impl fmt::Display for AccessInstance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            kind,
            resource,
            instance,
            address,
        } = self;
        write!(
            f,
            "{} {}{}({})",
            kind,
            resource,
            if !instance.is_empty() {
                format!("<{}>", instance.iter().map(|t| t.to_string()).join(","))
            } else {
                "".to_owned()
            },
            address.short_str_lossless()
        )
    }
}

impl AddressSpecifierFunction {
    pub fn parse(module_str: &str, fun_str: &str) -> Option<AddressSpecifierFunction> {
        match (module_str, fun_str) {
            ("0x1::signer", "address_of") => Some(AddressSpecifierFunction::SignerAddress),
            ("0x1::object", "owner") => Some(AddressSpecifierFunction::ObjectAddress),
            _ => None,
        }
    }

    pub fn eval(&self, _arg: Value) -> PartialVMResult<AccountAddress> {
        unimplemented!()
    }
}

impl AccessInstance {
    pub fn new(kind: file_format::AccessKind, ty: &Type, address: AccountAddress) -> Option<Self> {
        let (resource, instance) = match ty {
            Type::Struct { name, .. } => (name.as_ref(), &[] as &[Type]),
            Type::StructInstantiation { name, ty_args, .. } => (name.as_ref(), ty_args.as_slice()),
            _ => return None,
        };
        Some(AccessInstance {
            kind,
            resource: resource.clone(),
            instance: instance.to_vec(),
            address,
        })
    }

    pub fn read(ty: &Type, address: AccountAddress) -> Option<Self> {
        Self::new(file_format::AccessKind::Reads, ty, address)
    }

    pub fn write(ty: &Type, address: AccountAddress) -> Option<Self> {
        Self::new(file_format::AccessKind::Writes, ty, address)
    }
}
