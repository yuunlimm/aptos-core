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

use crate::loaded_data::runtime_types::{StructIdentifier, Type};
use move_binary_format::file_format;
use move_core_types::{account_address::AccountAddress, language_storage::ModuleId};
use std::fmt::Debug;

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
    Eval(AddressSpecifierFunction, file_format::LocalIndex),
}

/// A well-known function used in an address specifier.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy, Debug)]
pub enum AddressSpecifierFunction {
    Identity,
    SignerAddressOf,
    ObjectAddressOf,
}

/// A struct to represent an access.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
pub struct AccessInstance {
    pub kind: file_format::AccessKind,
    pub resource: StructIdentifier,
    pub instance: Vec<Type>,
    pub address: AccountAddress,
}

/// A trait used for evaluating dynamic content of an address specifier.
pub trait AccessControlEnv {
    fn evaluate(
        &self,
        fun: AddressSpecifierFunction,
        local: file_format::LocalIndex,
    ) -> AccountAddress;
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

    /// Returns true of the concrete access instance is allowed.
    pub fn allows(&self, env: &mut impl AccessControlEnv, access: &AccessInstance) -> bool {
        use AccessSpecifier::*;
        match self {
            Any => true,
            Constraint(incls, excls) => {
                incls.iter().any(|c| c.allows(env, access))
                    && excls.iter().all(|c| !c.allows(env, access))
            },
        }
    }

    pub fn join(self, env: &mut impl AccessControlEnv, other: Self) -> Self {
        use AccessSpecifier::*;
        match (self, other) {
            (Any, s) | (s, Any) => s,
            (Constraint(incls, mut excls), Constraint(other_incls, other_excls)) => {
                // Inclusions are disjunctions. The join of two disjunctions is
                //   (a + b) * (c + d) = a*(c + d) + b*(c + d) = a*c + a*d + b*c + b*d
                // For the exclusions, we can simply concatenate them.
                // TODO: this is quadratic and  need to be metered
                let mut new_incls = vec![];
                for incl in &incls {
                    for other_incl in other_incls.clone() {
                        // try_join returns None if the result is empty.
                        if let Some(new_incl) = incl.clone().join(env, other_incl) {
                            new_incls.push(new_incl);
                        }
                    }
                }
                if new_incls.is_empty() {
                    // Drop exclusions since they are redundant
                    Constraint(new_incls, vec![])
                } else {
                    excls.extend(other_excls.into_iter());
                    Constraint(new_incls, excls)
                }
            },
        }
    }
}

impl AccessSpecifierClause {
    /// Checks whether this clause allows the access.
    fn allows(&self, env: &mut impl AccessControlEnv, access: &AccessInstance) -> bool {
        let AccessInstance {
            kind,
            resource,
            instance,
            address,
        } = access;
        if self.kind != file_format::AccessKind::Acquires && &self.kind != kind {
            return false;
        }
        self.resource.allows(resource, instance) && self.address.allows(env, address)
    }

    /// Join two clauses. Returns None if there is no intersection in access.
    fn join(self, env: &mut impl AccessControlEnv, other: Self) -> Option<Self> {
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

        kind.try_join(other_kind).and_then(|kind| {
            resource.join(env, other_resource).and_then(|resource| {
                address.join(env, other_address).map(|address| Self {
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
    fn join(self, _env: &mut impl AccessControlEnv, other: Self) -> Option<Self> {
        use ResourceSpecifier::*;
        match &self {
            Any => Some(other),
            DeclaredAtAddress(addr) => match &other {
                Any => Some(self),
                DeclaredAtAddress(other_addr)
                | DeclaredInModule(module_addr!(other_addr))
                | Resource(struct_identifier_addr!(other_addr))
                | ResourceInstantiation(struct_identifier_addr!(other_addr), _) => {
                    some_if!(other, addr == other_addr)
                },
            },
            DeclaredInModule(module_id) => match &other {
                Any => Some(self),
                DeclaredAtAddress(addr) => some_if!(self, addr == module_id.address()),
                DeclaredInModule(other_module_id)
                | Resource(struct_identifier_module!(other_module_id))
                | ResourceInstantiation(struct_identifier_module!(other_module_id), _) => {
                    some_if!(other, module_id == other_module_id)
                },
            },
            Resource(struct_id) => match &other {
                Any => Some(self),
                DeclaredAtAddress(addr) => some_if!(self, addr == struct_id.module.address()),
                DeclaredInModule(module_id) => some_if!(self, module_id == &struct_id.module),
                Resource(other_struct_id) | ResourceInstantiation(other_struct_id, _) => {
                    some_if!(other, struct_id == other_struct_id)
                },
            },
            ResourceInstantiation(struct_id, inst) => match other {
                Any => Some(self),
                DeclaredAtAddress(addr) => some_if!(self, struct_id.module.address() == &addr),
                DeclaredInModule(module_id) => some_if!(self, struct_id.module == module_id),
                Resource(other_struct_id) => some_if!(self, struct_id == &other_struct_id),
                ResourceInstantiation(other_struct_id, other_inst) => {
                    some_if!(
                        self,
                        struct_id == &other_struct_id
                            && inst.len() == other_inst.len()
                            && inst.iter().zip(other_inst.iter()).all(|(t1, t2)| t1 == t2)
                    )
                },
            },
        }
    }
}

impl AddressSpecifier {
    /// Checks whether the given address is allowed by this specifier.
    fn allows(&self, env: &mut impl AccessControlEnv, addr: &AccountAddress) -> bool {
        use AddressSpecifier::*;
        match self {
            Any => true,
            Eval(fun, arg) => &env.evaluate(*fun, *arg) == addr,
        }
    }

    /// Joins two address specifiers. Returns None if there is no intersection.
    fn join(self, env: &mut impl AccessControlEnv, other: Self) -> Option<Self> {
        use AddressSpecifier::*;
        match (self, other) {
            (Any, s) | (s, Any) => Some(s),
            (Eval(fun, arg), Eval(other_fun, other_arg)) => {
                if env.evaluate(fun, arg) == env.evaluate(other_fun, other_arg) {
                    // Choose self
                    Some(Eval(fun, arg))
                } else {
                    None
                }
            },
        }
    }
}
