// Copyright © Aptos Foundation
// SPDX-License-Identifier: Apache-2.0

/// AST Simplifier
///
/// Simplify the AST before conversion to bytecode
use crate::options::Options;
use codespan_reporting::diagnostic::Severity;
use move_binary_format::file_format::Ability;
use move_model::{
    ast::{Exp, ExpData, Operation, Pattern, TempIndex, Value},
    constant_folder::ConstantFolder,
    exp_rewriter::ExpRewriterFunctions,
    model::{GlobalEnv, NodeId, Parameter, TypeParameter},
    symbol::Symbol,
    ty::{ReferenceKind, Type, TypeDisplayContext},
};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Debug,
    iter::{zip, IntoIterator, Iterator},
    vec::Vec,
};

static SIMPLIFIER_DEBUG: bool = false;

pub fn run_simplifier(env: &mut GlobalEnv, eliminate_code: bool) {
    let mut rewriter = SimplifierRewriter::new(env, eliminate_code);
    for module in env.get_modules() {
        for func in module.get_functions() {
            let mut changed = false;
            if func.get_def().is_some() {
                let value = func.get_mut_def().take();
                if let Some(def) = value {
                    let params = &func.get_parameters();
                    let type_params = &func.get_type_parameters();
                    let rewritten =
                        rewriter.rewrite_function_body(params, type_params, def.clone());
                    if rewriter.debug {
                        eprintln!(
                            "After rewrite_function_body, function body is `{}`",
                            rewritten.display(env)
                        );
                    }

                    changed = !ExpData::ptr_eq(&rewritten, &def);
                    *func.get_mut_def() = Some(rewritten);
                }
            }
            if changed && rewriter.debug {
                eprintln!("After simplifier, function is `{}`", env.dump_fun(&func),);
            }
        }
    }
}

struct ScopedMap<K, V> {
    saved: Vec<BTreeMap<K, V>>,
    values: BTreeMap<K, V>,
}

impl<K, V> ScopedMap<K, V>
where
    K: Ord + Copy,
    V: Clone,
{
    pub fn new() -> Self {
        Self {
            saved: Vec::new(),
            values: BTreeMap::new(),
        }
    }

    pub fn clear(&mut self) {
        self.saved.clear();
        self.values.clear();
    }

    // Freeze the current value map so it can be restored
    // when scope is exited.
    pub fn enter_scope(&mut self) {
        // We lazily add old values as they are changed.
        self.saved.push(self.values.clone());
    }

    // Restore `values` to what they were before the corresponding
    // `enter_scope` call.
    pub fn exit_scope(&mut self) {
        self.values = self.saved.pop().expect("Bug: imbalanced enter/exit");
    }

    // Set a `value` for `key`, valid until the current scope is
    // exited.
    pub fn insert(&mut self, key: K, value: V) {
        self.values.insert(key, value);
    }

    #[allow(unused)]
    // Remove any value for `key` for the current scope.
    pub fn remove(&mut self, key: &K) {
        self.values.remove(key);
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        self.values.get(key)
    }

    #[allow(unused)]
    pub fn contains_key(&self, key: &K) -> bool {
        self.values.contains_key(key)
    }

    pub fn borrow_map(&self) -> &BTreeMap<K, V> {
        &self.values
    }
}

// Finds sets of local vars that may be modified, and shouldn't be treated as constant.
// Vars are identified by symbol name and by the scope in which they are defined.
// Scope is either
// - `None`: procedure parameter scope (uses are usually a temporary but may not be, notably in
//    the case of `Assign`)
// - `Some(NodeId)`: the let which creates the variable scope.
//
// Note that as expression simplification occurs, the `NodeId` of the original `Let` expression
// may change/disappear, but not until the scope is exited.  So the "possibly modified" property
// shouldn't be trusted after that.
fn find_possibly_modified_vars(
    env: &GlobalEnv,
    params: &[Parameter],
    exp: &ExpData,
) -> BTreeSet<(Symbol, Option<NodeId>)> {
    let mut visiting_binding: ScopedMap<Symbol, NodeId> = ScopedMap::new();
    let mut unsafe_variables: BTreeSet<(Symbol, Option<NodeId>)> = BTreeSet::new();

    // Track when we are in a modifying scope.
    let mut modifying = false;
    // Use a stack to keep the modification status properly scoped.
    let mut modifying_stack = Vec::new();
    exp.visit_pre_post(&mut |up, e| {
        use ExpData::*;
        match e {
            Invalid(_) | Value(..) | LoopCont(..) | SpecBlock(..) => {},
            LocalVar(_id, sym) => {
                let current_binding = visiting_binding.get(sym);
                if modifying {
                    if SIMPLIFIER_DEBUG {
                        eprintln!(
                            "Var {} in binding {:?} is unsafe",
                            sym.display(env.symbol_pool()),
                            current_binding
                        );
                    }
                    unsafe_variables.insert((*sym, current_binding.copied()));
                };
            },
            Temporary(id, idx) => {
                if let Some(sym) = params.get(*idx).map(|p| p.0) {
                    if modifying {
                        let current_binding = visiting_binding.get(&sym);
                        if SIMPLIFIER_DEBUG {
                            eprintln!(
                                "Temp {} = Var {} in binding {:?} is unsafe",
                                *idx,
                                sym.display(env.symbol_pool()),
                                current_binding
                            );
                        }
                        unsafe_variables.insert((sym, current_binding.copied()));
                    };
                } else {
                    let loc = env.get_node_loc(*id);
                    env.diag(
                        Severity::Bug,
                        &loc,
                        &format!("Use of temporary with no corresponding parameter `{}`", idx),
                    );
                }
            },
            Call(_, op, _explist) => {
                match op {
                    // NOTE: we don't consider values in globals, so no need to
                    // consider BorrowGlobal(ReferenceKind::Mutable)} here.
                    Operation::MoveTo
                    | Operation::MoveFrom
                    | Operation::Move
                    | Operation::Borrow(ReferenceKind::Mutable) => {
                        if !up {
                            // Add all mentioned vars to modified vars.
                            modifying_stack.push(modifying);
                            modifying = true;
                        } else {
                            // stop adding vars
                            modifying = modifying_stack.pop().expect("unbalanced visit 1");
                        }
                    },
                    Operation::MoveFunction(module_id, fun_id) => {
                        let qfid = module_id.qualified(*fun_id);
                        let func_env = env.get_function(qfid);
                        if func_env.is_inline() {
                            // Inline function may modify parameters.
                            if !up {
                                // Add all mentioned vars to modified vars.
                                modifying_stack.push(modifying);
                                modifying = true;
                            } else {
                                // stop adding vars
                                modifying = modifying_stack.pop().expect("unbalanaced visit 2");
                            }
                        } else {
                            // Function calls other than inline ones cannot modify parameter var.
                            if !up {
                                modifying_stack.push(modifying);
                                modifying = false;
                            } else {
                                modifying = modifying_stack.pop().expect("unbalanced visit 3");
                            }
                        }
                    },
                    _ => {
                        // Other operations don't modify argument variables.
                        if !up {
                            modifying_stack.push(modifying);
                            modifying = false;
                        } else {
                            modifying = modifying_stack.pop().expect("unbalanced visit 4");
                        }
                    },
                };
            },
            Invoke(..) | Return(..) | Quant(..) | Loop(..) | Mutate(..) => {
                // We don't modify top-level variables here.
                if !up {
                    modifying_stack.push(modifying);
                    modifying = false;
                } else {
                    modifying = modifying_stack.pop().expect("unbalanced visit 5");
                }
            },
            Lambda(node_id, pat, _) | Block(node_id, pat, _, _) => {
                // Define a new scope for bound vars
                if !up {
                    visiting_binding.enter_scope();
                    for (_, sym) in pat.vars() {
                        visiting_binding.insert(sym, *node_id);
                    }
                } else {
                    // remove a scope
                    visiting_binding.exit_scope();
                };
            },
            IfElse(_, _cond, _then, _else) => {
                // Ideally, we would turn off `modifying` during visitation of the _cond,
                // but we don't have a mechanism to do that without also affecting
                // then and else.  For now, do nothing.
                // TODO(?): see if we can do something here.
            },
            Sequence(_, _exp_vec) => {
                // Ideally, iff `modifying` is on now we should turn it off for all exprs except
                // the last.  For now, do nothing.
                // TODO(?): see if we can do something here.
            },
            Assign(_loc, pat, _) => {
                if !up {
                    // add vars in pat to modified vars
                    for (_pat_var_id, sym) in pat.vars() {
                        let current_binding = visiting_binding.get(&sym);
                        if SIMPLIFIER_DEBUG {
                            eprintln!(
                                "Var {} in binding {:?} is unsafe",
                                sym.display(env.symbol_pool()),
                                current_binding
                            );
                        }
                        unsafe_variables.insert((sym, current_binding.copied()));
                    }
                };
            },
        };
        true
    });
    unsafe_variables
}

struct SimplifierRewriter<'env> {
    pub env: &'env GlobalEnv,
    #[allow(dead_code)]
    pub debug: bool,
    pub constant_folder: ConstantFolder<'env>,
    pub eliminate_code: bool,

    // Parameters to currently processed function
    cached_params: Vec<Parameter>,

    // Type Parameters to currently processed function
    cached_type_params: Vec<TypeParameter>,

    // Tracks which definition (`Let` statement `NodeId`) is visible during visit to find modified
    // local vars.  A use of a symbol which is missing must be a `Parameter`.  This is used only
    // to determine if a symbol is in `unsafe_variables`.
    visiting_binding: ScopedMap<Symbol, NodeId>,

    // Unsafe variables are keyed by `Symbol` and `Let` statement `NodeId`,
    // except function parameters, which are denoted by `None`.
    unsafe_variables: BTreeSet<(Symbol, Option<NodeId>)>,

    // Rename symbols to avoid name conflicts between nested symbols:
    // The outermost occurrence of a `Symbol` is mapped to itself.  Other symbols whose
    // scope is nested inside other identical symbols are mapped to new, unique symbols.
    // (This is used to allow references to symbols which are shadowed by inner reuse.)
    remapped_symbol: ScopedMap<Symbol, Symbol>,

    // Tracks constant values from scope.  All symbols in keys and values are remapped.
    // A variable without a constant value is unbound here.
    values: ScopedMap<Symbol, SimpleValue>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum SimpleValue {
    Value(Value),
    Temporary(TempIndex),
    LocalVar(Symbol),
    Unknown,
}

impl<'env> SimplifierRewriter<'env> {
    fn new(env: &'env GlobalEnv, eliminate_code: bool) -> Self {
        let debug = env
            .get_extension::<Options>()
            .expect("Options is available")
            .debug;
        let constant_folder = ConstantFolder::new(env, false);
        Self {
            env,
            debug,
            constant_folder,
            eliminate_code,
            cached_params: Vec::new(),
            cached_type_params: Vec::new(),
            visiting_binding: ScopedMap::new(),
            unsafe_variables: BTreeSet::new(),
            remapped_symbol: ScopedMap::new(),
            values: ScopedMap::new(),
        }
    }

    /// Process a function.
    pub fn rewrite_function_body(
        &mut self,
        params: &[Parameter],
        type_params: &[TypeParameter],
        exp: Exp,
    ) -> Exp {
        self.cached_params = params.to_vec();
        self.cached_type_params = type_params.to_vec();
        self.unsafe_variables = find_possibly_modified_vars(self.env, params, exp.as_ref());
        self.visiting_binding.clear();
        self.values.clear();
        self.remapped_symbol.clear();
        if SIMPLIFIER_DEBUG {
            eprintln!("Unsafe variables are {:#?}", self.unsafe_variables);
        }
        self.rewrite_exp(exp)
    }

    /// If symbol `sym` has a recorded value that is currently visible, then
    /// build an expression to produce that value. `sym` is unremapped.
    fn rewrite_to_recorded_value(&mut self, id: NodeId, sym: Symbol) -> Option<Exp> {
        let remapped_sym = self.remapped_symbol.get(&sym).unwrap_or(&sym);
        if let Some(val) = self.values.get(remapped_sym) {
            use SimpleValue::*;
            match val {
                Value(val) => Some(ExpData::Value(id, val.clone()).into_exp()),
                Temporary(idx) => Some(ExpData::Temporary(id, *idx).into_exp()),
                LocalVar(sym) => Some(ExpData::LocalVar(id, *sym).into_exp()),
                Unknown => Some(ExpData::LocalVar(id, *remapped_sym).into_exp()),
            }
        } else {
            Some(ExpData::LocalVar(id, *remapped_sym).into_exp())
        }
    }

    // Try resolving the value of `remapped_sym`.
    // If we can find value for it, return a `SimpleValue` describing that value.
    // If no useful value is found, returns `SimpleValue::Unknown`.
    fn resolve_var_value(&self, id: NodeId, remapped_sym: Symbol, count: usize) -> SimpleValue {
        if SIMPLIFIER_DEBUG {
            eprintln!(
                "resolve_var_value({:#?}, {}) iteration {}",
                id,
                remapped_sym.display(self.env.symbol_pool()),
                count
            );
        }
        if let Some(val) = self.values.get(&remapped_sym) {
            self.resolve_simple_value(id, val.clone(), count)
        } else {
            SimpleValue::LocalVar(remapped_sym)
        }
    }

    // Try resolving `value`, returning it directly if it is already in its simplest form.
    //
    // If it is a variable, then try to resolve the variable to a more interesting
    // value using `resolve_var_value`.
    //
    // Note that a variable in `value` may be remapped or not.
    fn resolve_simple_value(&self, id: NodeId, value: SimpleValue, count: usize) -> SimpleValue {
        // While value is a valid variable, keep trying to resolve it.
        use SimpleValue::*;
        if SIMPLIFIER_DEBUG {
            eprintln!(
                "resolve_simple_value({:#?}, {:#?}) iteration {}",
                id, value, count
            );
        }
        let new_count = count + 1;
        assert!(new_count < 10);
        if let LocalVar(sym) = value {
            if let Some(mapped_sym) = self.remapped_symbol.get(&sym) {
                self.resolve_var_value(id, *mapped_sym, new_count)
            } else {
                self.resolve_var_value(id, sym, new_count)
            }
        } else {
            value
        }
    }

    fn get_constant_or_unmodified_variable(&mut self, exp: Option<Exp>) -> SimpleValue {
        if let Some(exp) = exp {
            match exp.as_ref() {
                ExpData::Value(_, val) => SimpleValue::Value(val.clone()),
                ExpData::LocalVar(id, sym) => {
                    self.resolve_simple_value(*id, SimpleValue::LocalVar(*sym), 0)
                },
                ExpData::Temporary(_id, idx) => SimpleValue::Temporary(*idx),
                _ => SimpleValue::Unknown,
            }
        } else {
            SimpleValue::Unknown
        }
    }

    // Expand a `Value::Tuple` value expression to a call to `Tuple`
    fn expand_tuple(&mut self, exp: Exp) -> Exp {
        if let ExpData::Value(id, Value::Tuple(x)) = exp.as_ref() {
            if x.is_empty() {
                ExpData::Call(*id, Operation::Tuple, Vec::new()).into_exp()
            } else {
                let loc = self.env.get_node_loc(*id);
                self.env.diag(
                    Severity::Bug,
                    &loc,
                    &format!(
                        "Illegal use of non-empty Tuple constant of length {}",
                        x.len()
                    ),
                );
                exp
            }
        } else if let ExpData::Value(id, Value::Vector(x)) = exp.as_ref() {
            if x.is_empty() {
                ExpData::Call(*id, Operation::Vector, Vec::new()).into_exp()
            } else {
                let loc = self.env.get_node_loc(*id);
                self.env.diag(
                    Severity::Bug,
                    &loc,
                    &format!(
                        "Illegal use of non-empty Vector constant of length {}",
                        x.len()
                    ),
                );
                exp
            }
        } else {
            exp
        }
    }
}

impl<'env> ExpRewriterFunctions for SimplifierRewriter<'env> {
    fn rewrite_enter_scope<'a>(
        &mut self,
        id: NodeId,
        vars: impl Iterator<Item = &'a (NodeId, Symbol)>,
    ) {
        self.visiting_binding.enter_scope();
        self.values.enter_scope();
        self.remapped_symbol.enter_scope();
        for (_, sym) in vars {
            self.visiting_binding.insert(*sym, id);
            let mapped_sym = {
                let new_sym = if self.remapped_symbol.contains_key(sym) {
                    self.env.symbol_pool().make_unique(*sym)
                } else {
                    *sym
                };
                if SIMPLIFIER_DEBUG {
                    eprintln!(
                        "adding symbol {} remapping to {} at node {}",
                        sym.display(self.env.symbol_pool()),
                        new_sym.display(self.env.symbol_pool()),
                        id.as_usize()
                    );
                }
                self.remapped_symbol.insert(*sym, new_sym);
                new_sym
            };
            if SIMPLIFIER_DEBUG {
                eprintln!(
                    "removing values[{}] at node {}",
                    mapped_sym.display(self.env.symbol_pool()),
                    id.as_usize()
                );
            }
            self.values.insert(mapped_sym, SimpleValue::Unknown);
        }
    }

    fn rewrite_exit_scope(&mut self, _id: NodeId) {
        self.visiting_binding.exit_scope();
        self.values.exit_scope();
        self.remapped_symbol.exit_scope();
    }

    fn rewrite_local_var(&mut self, id: NodeId, sym: Symbol) -> Option<Exp> {
        self.rewrite_to_recorded_value(id, sym)
    }

    fn rewrite_assign(&mut self, id: NodeId, lhs: &Pattern, rhs: &Exp) -> Option<Exp> {
        let mut remove_vars = BTreeSet::new();
        for (var, opt_exp) in lhs.vars_and_exprs(rhs) {
            if let Some(exp) = opt_exp {
                if let ExpData::LocalVar(_, sym) = exp.as_ref() {
                    if var == *sym {
                        remove_vars.insert(var);
                    }
                }
            }
        }
        if !remove_vars.is_empty() {
            let new_lhs = lhs.clone().remove_vars(&remove_vars);
            Some(ExpData::Assign(id, new_lhs, rhs.clone()).into_exp())
        } else {
            None
        }
    }

    fn rewrite_temporary(&mut self, _id: NodeId, _idx: TempIndex) -> Option<Exp> {
        // Note that at this phase of compilation, any temporary must refer to
        // a parameter.  This means that the value is comes from outside and is
        // unknown, so no rewrite will be useful.
        None
    }

    fn rewrite_call(&mut self, id: NodeId, oper: &Operation, args: &[Exp]) -> Option<Exp> {
        self.constant_folder
            .rewrite_call(id, oper, args)
            .map(|exp| self.expand_tuple(exp))
            .or({
                // Not completely a constant.
                // TODO(BUGBUG): consider matching some expressions,
                // e.g., ((x + c1) + c2) -> (x + (c1 + c2))
                None
            })
    }

    fn rewrite_if_else(&mut self, _id: NodeId, cond: &Exp, then: &Exp, else_: &Exp) -> Option<Exp> {
        match cond.as_ref() {
            ExpData::Value(_, Value::Bool(true)) => Some(then.clone()),
            ExpData::Value(_, Value::Bool(false)) => Some(else_.clone()),
            _ => None,
        }
    }

    fn rewrite_sequence(&mut self, id: NodeId, seq: &[Exp]) -> Option<Exp> {
        if self.eliminate_code {
            // Check which elements are side-effect-free
            let mut siter = seq.iter();
            let _ignore = siter.next_back(); // ignore last element, we have to keep it
            let mut side_effect_free_elts: Vec<_> = siter
                .map(|exp| exp.as_ref().is_side_effect_free())
                .collect();
            if side_effect_free_elts.iter().all(|elt| *elt) {
                // All elements other than the last are side-effect free.
                // (Note that this case includes a singleton sequence.)
                seq.iter().next_back().cloned()
            } else if side_effect_free_elts
                .iter()
                .any(|elt_is_side_effect_free| *elt_is_side_effect_free)
            {
                // At least one element can be removed.
                side_effect_free_elts.push(false);
                let new_vec: Vec<_> = zip(seq, side_effect_free_elts)
                    .filter_map(|(elt, is_side_effect_free)| {
                        if !is_side_effect_free {
                            Some(elt.clone())
                        } else {
                            None
                        }
                    })
                    .collect();
                Some(ExpData::Sequence(id, new_vec).into_exp())
            } else {
                None
            }
        } else {
            None
        }
    }

    fn rewrite_pattern(&mut self, pat: &Pattern, entering_scope: bool) -> Option<Pattern> {
        // Note that scope entry patterns are handled in `rewrite_enter_block_scope`, and
        // `rewrite_lambda`, and `rewrite_block`, if appropriate.
        if !entering_scope {
            // This is an Assign, replace vars if needed
            pat.replace_vars(self.remapped_symbol.borrow_map())
        } else {
            None
        }
    }

    fn rewrite_lambda(&mut self, id: NodeId, _pat: &Pattern, _body: &Exp) -> Option<Exp> {
        let loc = self.env.get_node_loc(id);
        self.env.diag(
            Severity::Bug,
            &loc,
            "There should be no lambdas in simplifier pass",
        );
        None
    }

    fn rewrite_enter_block_scope(
        &mut self,
        id: NodeId,
        pat: &Pattern,
        binding: &Option<Exp>,
    ) -> Option<Pattern> {
        // Binding was rewritten before we got here, pat is not yet rewritten.
        let mut new_binding = Vec::new();
        if let Some(exp) = binding {
            for (old_var, opt_new_binding_exp) in pat.vars_and_exprs(exp) {
                if !self.unsafe_variables.contains(&(old_var, Some(id))) {
                    // Try to evaluate opt_new_binding_exp as a constant/var  using current variable bindings
                    let val = self.get_constant_or_unmodified_variable(opt_new_binding_exp);
                    new_binding.push((old_var, val));
                } else {
                    // In the current scope, old_var may be modified.  Shadow old value.
                    new_binding.push((old_var, SimpleValue::Unknown));
                }
            }
        } else {
            // Body with no bindings, just shadow any old values.
            for (_, old_var) in pat.vars() {
                new_binding.push((old_var, SimpleValue::Unknown));
            }
        }
        // Bound vars block any prior values
        self.rewrite_enter_scope(id, pat.vars().iter());
        // Add any const bindings to our map.
        for (var, value) in new_binding.into_iter() {
            let mapped_var = self
                .remapped_symbol
                .get(&var)
                .expect("Was just set in rewrite_enter_scope");
            if SIMPLIFIER_DEBUG {
                eprintln!(
                    "Entering block {:#?}, adding var {} -> {} -> {:#?}",
                    id.as_usize(),
                    var.display(self.env.symbol_pool()),
                    mapped_var.display(self.env.symbol_pool()),
                    value
                );
            }
            // Note that binding was already rewritten (but outside this scope).
            self.values.insert(*mapped_var, value);
        }
        // Rename local variables in the pattern.
        let opt_new_pat = pat.replace_vars(self.remapped_symbol.borrow_map());
        if let Some(new_pat) = &opt_new_pat {
            if SIMPLIFIER_DEBUG {
                eprintln!(
                    "Entering block {}, Pat was {}, renamed to {}, remapped_symbol map is {:#?}",
                    id.as_usize(),
                    pat.to_string(self.env, &TypeDisplayContext::new(self.env)),
                    new_pat.to_string(self.env, &TypeDisplayContext::new(self.env)),
                    self.remapped_symbol.borrow_map(),
                );
            }
        } else {
            if SIMPLIFIER_DEBUG {
                eprintln!(
                    "Entering block {}, Pat was {}, renamed to None, remapped_symbol map is {:#?}",
                    id.as_usize(),
                    pat.to_string(self.env, &TypeDisplayContext::new(self.env)),
                    self.remapped_symbol.borrow_map(),
                );
            }
        }
        opt_new_pat
    }

    // Note that `rewrite_block` is called *after* `rewrite_exit_scope`.
    fn rewrite_block(
        &mut self,
        id: NodeId,
        pat: &Pattern,
        opt_binding: &Option<Exp>,
        body: &Exp,
    ) -> Option<Exp> {
        if let Some(exp) = opt_binding {
            let pat_id = pat.node_id();
            let exp_id = exp.node_id();
            let pat_type = self.env.get_node_type(pat_id);
            let exp_type = self.env.get_node_type(exp_id);
            let type_display_context = TypeDisplayContext::new(self.env);
            if SIMPLIFIER_DEBUG {
                eprintln!(
                    "Starting rewrite_block(id={}, pat={}, opt_binding={}, body={}, pat_type={}, exp_type={}, {})",
                    id.as_usize(),
                    pat.to_string(self.env, &type_display_context),
                    exp.display_verbose(self.env),
                    body.display_verbose(self.env),
                    pat_type.display(&type_display_context),
                    exp_type.display(&type_display_context),
                    if pat_type == exp_type { "MATCHES" } else { "NO MATCH" },
                );
            }
        } else {
            if SIMPLIFIER_DEBUG {
                eprintln!(
                    "Starting rewrite_block(id={}, pat={}, opt_binding={}, body={})",
                    id.as_usize(),
                    pat.to_string(self.env, &TypeDisplayContext::new(self.env)),
                    "None",
                    body.display_verbose(self.env)
                );
            }
        }

        // Simplify binding:
        //   A few ideas for simplification which are implemented below:
        //     (1) if no binding, then simplify to just the body.
        //     (2) if all pattern vars are unused in body and binding is side-effect free, again return body.
        //     (3) if some pattern vars are unused in the body, turn them into wildcards.

        let pat_vars = pat.vars();
        // (1) if no binding, then simplify to just the body
        if opt_binding.is_none() && pat_vars.is_empty() {
            if SIMPLIFIER_DEBUG {
                eprintln!(
                    "No binding, dropping all but body for rewrite_block(id={})",
                    id.as_usize()
                );
            }
            return Some(body.clone());
        }
        let bound_vars = pat.vars();

        // (2) If all pattern vars are unused in body and binding is side-effect free, again return
        // body.  But to avoid introducing a drop of a struct value that might not have "drop",
        // also check that opt_binding type has drop.
        let free_vars = body.free_vars();
        let unused_bound_vars: BTreeSet<_> = bound_vars
            .iter()
            .filter_map(|(id, sym)| {
                let ty = self.env.get_node_type(*id);
                if !free_vars.contains(sym) {
                    if matches!(ty, Type::Tuple(_)) {
                        // Tuple type for vairable is not valid, but won't be flagged until bytecode
                        // generation; leave it in place so diagnostic can be generated.
                        None
                    } else {
                        Some(sym)
                    }
                } else {
                    None
                }
            })
            .cloned()
            .collect();
        let binding_can_be_dropped = pat.has_no_struct()
            || if let Some(binding) = opt_binding {
                let node_id = binding.node_id();
                let opt_type = self.env.get_node_type_opt(node_id);
                if let Some(ty) = opt_type {
                    let ability_set = self.env.type_abilities(&ty, &self.cached_type_params);
                    ability_set.has_ability(Ability::Drop)
                } else {
                    // We're missing type info, be conservative
                    false
                }
            } else {
                true
            };
        let can_eliminate_bindings = binding_can_be_dropped
            && bound_vars.len() == unused_bound_vars.len()
            && if let Some(binding) = opt_binding {
                binding.is_side_effect_free()
            } else {
                true
            };
        if can_eliminate_bindings {
            if SIMPLIFIER_DEBUG {
                eprintln!(
                    "No used vars, dropping all but body for rewrite_block(id={})",
                    id.as_usize()
                );
            }
            return Some(body.clone());
        }

        // (3) If some pattern vars are unused in the body, turn them into wildcards.
        let new_pat = if !unused_bound_vars.is_empty() {
            Some(pat.clone().remove_vars(&unused_bound_vars))
        } else {
            None
        };

        // Ideas not yet implemented:
        //     (4) simplify the pattern: if subpat is wildcard and subexpr is side-effect-free,
        //         can remove it and corresponding subexpr.
        //     (5) simplify the pattern: if subpat is wildcard, corresponding subexpr can be
        //         simplified to not produce a value
        //     (6) if body is also a block and its binding has no references to our bound vars,
        //         then merge patterns and blocks
        //     (7) if pattern is a singleton `Tuple` and binding is a `Tuple`, turn it into let x = val.

        if let Some(pat) = new_pat {
            let exp = ExpData::Block(id, pat, opt_binding.clone(), body.clone()).into_exp();
            if SIMPLIFIER_DEBUG {
                eprintln!(
                    "Dropping some vars  for rewrite_block(id={}), result = {}",
                    id.as_usize(),
                    exp.display_verbose(self.env),
                );
            }
            Some(exp)
        } else {
            None
        }
    }

    fn rewrite_exp(&mut self, exp: Exp) -> Exp {
        let old_id = exp.as_ref().node_id().as_usize();
        if SIMPLIFIER_DEBUG {
            eprintln!(
                "Before rewrite, expr {} is `{}`",
                old_id,
                exp.display_verbose(self.env)
            );
        }
        let r = self.rewrite_exp_descent(exp);
        let new_id = r.as_ref().node_id().as_usize();
        if SIMPLIFIER_DEBUG {
            eprintln!(
                "After rewrite, expr {} is now {}: `{}`",
                old_id,
                new_id,
                r.display_verbose(self.env)
            );
        }
        r
    }
}
