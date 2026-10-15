//! Deferred definedness of the operands that `KEQUAL.ite`, `BOOL.andThen` and `BOOL.orElse`
//! do not evaluate.
//!
//! `#if C #then T #else E #fi`, `B1 andThenBool B2` and `B1 orElseBool B2` are applications of
//! hooked function symbols, and every symbol application in matching logic is strict: it is
//! undefined wherever one of its arguments is. So `#if true #then 1 #else u #fi` denotes
//! `1 /\ \ceil(u)`, and the definedness of the operand the condition discards is part of the
//! value. Evaluating that operand to decide its definedness would make recursion guarded by the
//! conditional diverge and would perform the operand's effects, which the conditional is there
//! to avoid. The backend therefore keeps the following invariant.
//!
//! Every statement of the definedness of (i) the operand a literal deciding operand discards, or
//! (ii) an operand other than the deciding one while the deciding operand is not a literal (such
//! operands are left unsimplified), exists only as [`Predicate::Defined`] atoms, created only by
//! [`deferred_obligations`]. Such an operand is not evaluated beyond the bounded steps that decide
//! its atoms: an atom is decided only by [`decide_defined`] (folding by pure builtin hooks on
//! ground constructor-like arguments, collections included, with the value of one equation step on
//! literal arguments whose right-hand side those hooks fold to a literal; ceil equations whose
//! instantiated condition that folding decides, or whose instance is stated in the atom's place
//! over hook arithmetic; the key condition of a collection of literal keys; one equation step
//! selected by matching alone) and by a known fact or the solver, which reads it as the opaque
//! atom of `\ceil(t)`. Each of these steps is bounded by the size of the atom's subject or by one
//! selection scan per application, and none repeats on its own result, so deciding an atom
//! terminates whatever the definition's equations do.
//!
//! An operand whose definedness depends on an impure application (a console read, or a function
//! whose equations perform an effect) cannot be decided without performing it, and a constraint
//! must never hold an impure application: [`deferred_obligations`] returns that case as a
//! [`DeferredOutcome`], which its callers turn into the step's unsupported-hook stop.

use std::{cell::RefCell, collections::VecDeque, marker::PhantomData, sync::Arc};

use k_rust_kore::names::{BuiltinSort, OWISE_RULE_PRIORITY};

use crate::{
    builtin::{
        BuiltinError, BuiltinResult, UnsupportedHookReason, evaluate_in_definition,
        implementation_chosen,
    },
    definition::BackendDefinition,
    evaluation::EvaluationMode,
    rule::{Predicate, RewriteRule, RuleRhs, applicable_groups, term_index},
    simplify::{EquationInstances, Instance, SimplificationError, equation_instances},
    stop::{self, Stoppable},
    substitution::{Substitution, substitute},
    term::{FunctionType, NodeIdentity, Sort, Symbol, SymbolType, Term, TermKind, VariableKind},
};

/// The three hooked symbols whose deciding operand selects the operand that is evaluated.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ShortCircuit {
    /// `KEQUAL.ite`: `ite(C, T, E)`.
    Ite,
    /// `BOOL.andThen`: `B1 andThenBool B2`.
    AndThen,
    /// `BOOL.orElse`: `B1 orElseBool B2`.
    OrElse,
}

impl ShortCircuit {
    /// The kind of `term` and its arguments, when `term` is an application of one of the three
    /// hooks at its declared arity.
    pub(crate) fn of(term: &Term) -> Option<(Self, &[Term])> {
        let TermKind::Application {
            symbol, arguments, ..
        } = term.kind()
        else {
            return None;
        };
        let kind = match symbol.attributes.hook.as_deref()? {
            "KEQUAL.ite" if arguments.len() == 3 => Self::Ite,
            "BOOL.andThen" if arguments.len() == 2 => Self::AndThen,
            "BOOL.orElse" if arguments.len() == 2 => Self::OrElse,
            _ => return None,
        };
        Some((kind, arguments.as_slice()))
    }

    /// The operand evaluated and the operand discarded, as argument positions, once the deciding
    /// operand (position 0) is the literal `value`.
    pub(crate) fn select(self, value: bool) -> (Option<usize>, Option<usize>) {
        match (self, value) {
            (Self::Ite, true) => (Some(1), Some(2)),
            (Self::Ite, false) => (Some(2), Some(1)),
            (Self::AndThen, false) | (Self::OrElse, true) => (None, Some(1)),
            (Self::AndThen, true) | (Self::OrElse, false) => (Some(1), None),
        }
    }
}

/// The literal value of a Boolean domain value.
pub(crate) fn bool_literal(term: &Term) -> Option<bool> {
    let TermKind::DomainValue { sort, value } = term.kind() else {
        return None;
    };
    if !sort.is_builtin(BuiltinSort::Bool) {
        return None;
    }
    match value.as_utf8().ok()? {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    }
}

/// The argument positions of `term` whose definedness is deferred: when `term` is a short-circuit
/// application, the operand a literal deciding operand discards, or every operand but the
/// deciding one while that is not a literal. Empty for any other term.
pub(crate) fn deferred_positions(term: &Term) -> Vec<usize> {
    let Some((kind, arguments)) = ShortCircuit::of(term) else {
        return Vec::new();
    };
    match bool_literal(&arguments[0]) {
        Some(value) => kind.select(value).1.into_iter().collect(),
        None => (1..arguments.len()).collect(),
    }
}

/// An operand whose definedness depends on an impure application: the unsupported outcome at
/// the point where the operand's definedness is stated. Nothing is performed and nothing is
/// kept as a constraint.
#[derive(Clone, Debug)]
pub struct DeferredOutcome {
    hook: String,
    reason: UnsupportedHookReason,
    term: Term,
}

impl DeferredOutcome {
    fn new(application: &Term, detail: &str) -> Self {
        let TermKind::Application { symbol, .. } = application.kind() else {
            unreachable!("an impure subterm is an application");
        };
        Self {
            hook: symbol
                .attributes
                .hook
                .as_deref()
                .map_or_else(|| symbol.name.to_string(), str::to_owned),
            reason: UnsupportedHookReason::ArgumentOutOfRange {
                detail: detail.to_owned(),
            },
            term: application.clone(),
        }
    }

    /// The hook of the impure application, or its symbol's name when it has none.
    pub(crate) fn hook(&self) -> &str {
        &self.hook
    }

    /// Why the application is not performed.
    pub(crate) fn reason(&self) -> &UnsupportedHookReason {
        &self.reason
    }
}

impl From<DeferredOutcome> for SimplificationError {
    fn from(outcome: DeferredOutcome) -> Self {
        SimplificationError::UnsupportedHook {
            hook: outcome.hook,
            reason: outcome.reason,
            term: outcome.term,
        }
    }
}

const IMPURE_UNDER_OBLIGATION: &str = "the definedness of an operand that #if, andThenBool or \
     orElseBool does not evaluate depends on this impure application, which is not performed";

const CONSOLE_OUTSIDE_DOMAIN: &str = "a console operation in an operand that #if, andThenBool or \
     orElseBool does not evaluate, on arguments outside the console's domain; it is not performed";

/// Whether `application`'s symbol performs an effect: declared `impure` (which the frontend
/// sets on every function whose equations reach an impure symbol), or an `IO.` hook.
pub(crate) fn is_impure_application(definition: &BackendDefinition, application: &Term) -> bool {
    let TermKind::Application { symbol, .. } = application.kind() else {
        return false;
    };
    definition.is_impure(&symbol.name)
        || symbol
            .attributes
            .hook
            .as_deref()
            .is_some_and(|hook| hook.starts_with("IO."))
}

/// Whether `application`, a console hook application, has arguments in the console's domain,
/// where it denotes an element whatever the console holds (domains.md: an IO operation returns
/// its result or an `IOError`): `#write`/`#putc` on descriptor 1 or 2 with code points in
/// 0..=255, `#getc` on descriptor 0, `#read` on descriptor 0 with a non-negative length. `None`
/// for a hook that is not a console hook.
fn console_domain(application: &Term) -> Option<bool> {
    let TermKind::Application {
        symbol, arguments, ..
    } = application.kind()
    else {
        return None;
    };
    let hook = symbol.attributes.hook.as_deref()?;
    let int = |term: &Term| match term.kind() {
        TermKind::DomainValue { sort, value } if sort.is_builtin(BuiltinSort::Int) => {
            value.as_utf8().ok()?.parse::<i128>().ok()
        }
        _ => None,
    };
    let string = |term: &Term| match term.kind() {
        TermKind::DomainValue { sort, value } if sort.is_builtin(BuiltinSort::String) => {
            value.as_utf8().ok().map(str::to_owned)
        }
        _ => None,
    };
    let output = |descriptor: &Term| matches!(int(descriptor), Some(1 | 2));
    Some(match (hook, arguments.as_slice()) {
        ("IO.getc", [descriptor]) => int(descriptor) == Some(0),
        ("IO.read", [descriptor, length]) => {
            int(descriptor) == Some(0) && int(length).is_some_and(|length| length >= 0)
        }
        ("IO.putc", [descriptor, byte]) => {
            output(descriptor) && int(byte).is_some_and(|byte| (0..=255).contains(&byte))
        }
        ("IO.write", [descriptor, text]) => {
            output(descriptor)
                && string(text).is_some_and(|text| text.chars().all(|c| u32::from(c) <= 0xFF))
        }
        ("IO.getc" | "IO.read" | "IO.putc" | "IO.write", _) => false,
        _ => return None,
    })
}

/// The immediate subterms of `term`.
fn children(term: &Term) -> Vec<&Term> {
    match term.kind() {
        TermKind::Application { arguments, .. } => arguments.iter().collect(),
        TermKind::And(left, right) => vec![left, right],
        TermKind::Injection { term, .. } => vec![term],
        TermKind::Map { entries, rest, .. } => entries
            .iter()
            .flat_map(|(key, value)| [key, value])
            .chain(rest)
            .collect(),
        TermKind::List { heads, rest, .. } => heads
            .iter()
            .chain(
                rest.iter()
                    .flat_map(|(middle, tails)| std::iter::once(middle).chain(tails)),
            )
            .collect(),
        TermKind::Set { elements, rest, .. } => elements.iter().chain(rest).collect(),
        TermKind::DomainValue { .. } | TermKind::Variable(_) => Vec::new(),
    }
}

/// The outcome of an atom over `subject` when `subject` holds an impure application.
pub(crate) fn impure_outcome(
    definition: &BackendDefinition,
    subject: &Term,
) -> Option<DeferredOutcome> {
    impure_subterm(definition, subject)
        .map(|impure| DeferredOutcome::new(&impure, IMPURE_UNDER_OBLIGATION))
}

/// The first impure application in `term`, if any.
fn impure_subterm(definition: &BackendDefinition, term: &Term) -> Option<Term> {
    let mut pending = vec![term];
    while let Some(term) = pending.pop() {
        if is_impure_application(definition, term) {
            return Some(term.clone());
        }
        pending.extend(children(term));
    }
    None
}

/// The definedness of `term`, an operand that is not evaluated, as [`Predicate::Defined`]
/// atoms, without calling `ceil_term`, a ceil equation or the simplifier.
///
/// One walk in pre-order: a domain value or an element variable gives nothing (a set variable
/// gives its atom, since it ranges over every pattern); an injection, an application of a
/// constructor or of a symbol declared total (an `impure` one included: the attribute states its
/// definedness, so nothing is performed) gives its arguments' atoms, by strictness; an
/// application of any other symbol gives its own atom, then its arguments'; a map or a set gives
/// its own atom (the distinctness of its keys or elements) when it is not `ceil_free`, then its
/// parts'; a list gives its items'. A console hook application on arguments in the console's
/// domain ([`console_domain`]) is defined and gives only its arguments' atoms.
///
/// An atom is kept only if its subject holds no impure application: its truth would depend on
/// an effect that is not performed, which no later step can decide. A partial impure
/// application, a console hook outside its domain, and an atom whose subject holds an impure
/// application are the [`DeferredOutcome`].
pub(crate) fn deferred_obligations(
    definition: &BackendDefinition,
    term: &Term,
) -> Result<Vec<Predicate>, DeferredOutcome> {
    let mut atoms = Vec::new();
    let mut pending = vec![term];
    while let Some(term) = pending.pop() {
        if term.attributes().ceil_free() {
            continue;
        }
        let mut children: Vec<&Term> = Vec::new();
        match term.kind() {
            TermKind::DomainValue { .. } => {}
            TermKind::Variable(variable) => {
                if variable.kind != VariableKind::Element {
                    atoms.push(Predicate::Defined(term.clone()));
                }
            }
            TermKind::Injection { term: inner, .. } => children.push(inner),
            TermKind::And(left, right) => children.extend([left, right]),
            TermKind::Application {
                symbol, arguments, ..
            } => {
                children.extend(arguments);
                match symbol.attributes.symbol_type {
                    SymbolType::Constructor | SymbolType::Function(FunctionType::Total) => {}
                    SymbolType::Function(FunctionType::Partial) => match console_domain(term) {
                        Some(true) => {}
                        Some(false) => {
                            return Err(DeferredOutcome::new(term, CONSOLE_OUTSIDE_DOMAIN));
                        }
                        None if is_impure_application(definition, term) => {
                            return Err(DeferredOutcome::new(term, IMPURE_UNDER_OBLIGATION));
                        }
                        None => atoms.push(Predicate::Defined(term.clone())),
                    },
                }
            }
            TermKind::Map { entries, rest, .. } => {
                atoms.push(Predicate::Defined(term.clone()));
                for (key, value) in entries {
                    children.extend([key, value]);
                }
                children.extend(rest);
            }
            TermKind::Set { elements, rest, .. } => {
                atoms.push(Predicate::Defined(term.clone()));
                children.extend(elements);
                children.extend(rest);
            }
            TermKind::List { heads, rest, .. } => {
                children.extend(heads);
                if let Some((middle, tails)) = rest {
                    children.push(middle);
                    children.extend(tails);
                }
            }
        }
        pending.extend(children.into_iter().rev());
    }
    let mut unique = Vec::with_capacity(atoms.len());
    for atom in atoms {
        let Predicate::Defined(subject) = &atom else {
            unreachable!("the walk creates only deferred atoms");
        };
        if let Some(impure) = impure_subterm(definition, subject) {
            return Err(DeferredOutcome::new(&impure, IMPURE_UNDER_OBLIGATION));
        }
        if !unique.contains(&atom) {
            unique.push(atom);
        }
    }
    Ok(unique)
}

/// The result of folding a term by pure builtin hooks on ground values ([`fold_hooks`]).
pub(crate) enum Folded {
    /// The folded term, the input itself when nothing folded.
    Term(Term),
    /// A hooked application in the term is undefined on its ground arguments, so the term is.
    Bottom(Term),
}

/// `term` with every application of a pure builtin hook whose arguments fold to ground
/// constructor-like terms (domain values, constructor applications, closed collections of such
/// items; [`pure_hook_on_values`]) replaced by its value, innermost first: no function or
/// simplification equation, no `impure` or `IO.` hook, no `evaluated` mark and no entry in the
/// simplifier's caches. A hook's result is read from and kept in the open [`HookValueScope`]
/// ([`evaluate_pure_hook`]). A hook that is undefined on its arguments makes the whole term
/// undefined ([`Folded::Bottom`]), since every application is strict. The walk enters
/// applications and injections only, so a collection is read as it stands: a hook inside one of
/// its items is not folded.
///
/// A value only an execution chooses is not computed outside one, as in term simplification
/// (`crate::evaluation`). A builtin failure leaves its application as it is.
pub(crate) fn fold_hooks(definition: &BackendDefinition, term: &Term) -> Stoppable<Folded> {
    fold(definition, term, false)
}

/// [`fold_hooks`], where a ground application of a function that no hook folds also takes the
/// value of its one equation step ([`step_value`]): the step [`single_step`] selects, whose
/// instantiated right-hand side `fold_hooks` folds to a domain value. One step per application,
/// on literal arguments, with a right-hand side folded by hooks alone and never stepped again: no
/// recursion of the definition's equations, no effect, and a bound of one selection scan per
/// node of the term (F5 of the fix round; docs/compatibility.md).
fn fold_with_values(definition: &BackendDefinition, term: &Term) -> Stoppable<Folded> {
    fold(definition, term, true)
}

fn fold(definition: &BackendDefinition, term: &Term, values: bool) -> Stoppable<Folded> {
    stop::with_stack_headroom(|| {
        let (symbol, sort_arguments, arguments) = match term.kind() {
            TermKind::Application {
                symbol,
                sort_arguments,
                arguments,
            } => (symbol, sort_arguments, arguments),
            TermKind::Injection {
                source,
                target,
                term: inner,
            } => {
                return Ok(match fold(definition, inner, values)? {
                    Folded::Term(folded) if folded.ptr_eq(inner) => Folded::Term(term.clone()),
                    Folded::Term(folded) => {
                        Folded::Term(Term::injection(source.clone(), target.clone(), folded))
                    }
                    bottom @ Folded::Bottom(_) => bottom,
                });
            }
            _ => return Ok(Folded::Term(term.clone())),
        };
        if term.attributes().ceil_free() && term.attributes().constructor_like {
            return Ok(Folded::Term(term.clone()));
        }
        let mut changed = false;
        let mut folded_arguments = Vec::with_capacity(arguments.len());
        for argument in arguments {
            match fold(definition, argument, values)? {
                Folded::Term(folded) => {
                    changed |= !folded.ptr_eq(argument);
                    folded_arguments.push(folded);
                }
                bottom @ Folded::Bottom(_) => return Ok(bottom),
            }
        }
        let node = if changed {
            Term::application(symbol.clone(), sort_arguments.clone(), folded_arguments)
        } else {
            term.clone()
        };
        let TermKind::Application {
            symbol, arguments, ..
        } = node.kind()
        else {
            return Ok(Folded::Term(node));
        };
        // The one equation step is taken on literal arguments only; a hook is evaluated on any
        // ground constructor-like ones (`pure_hook_on_values`).
        let literal_arguments = arguments
            .iter()
            .all(|argument| matches!(argument.kind(), TermKind::DomainValue { .. }));
        let values = values && literal_arguments && !is_impure_application(definition, &node);
        if symbol.attributes.hook.is_none() {
            if values && let Some(value) = step_value(definition, &node)? {
                return Ok(Folded::Term(value));
            }
            return Ok(Folded::Term(node));
        }
        if !pure_hook_on_values(definition, &node) {
            return Ok(Folded::Term(node));
        }
        Ok(match evaluate_pure_hook(definition, &node)? {
            Ok(BuiltinResult::Value(_))
                if crate::evaluation::current() == EvaluationMode::Proof
                    && implementation_chosen(&node).is_some() =>
            {
                Folded::Term(node)
            }
            Ok(BuiltinResult::Value(value)) => Folded::Term(value),
            Ok(BuiltinResult::Bottom) => Folded::Bottom(node),
            Ok(BuiltinResult::NotApplicable | BuiltinResult::Unsupported(_)) if values => {
                match step_value(definition, &node)? {
                    Some(value) => Folded::Term(value),
                    None => Folded::Term(node),
                }
            }
            Ok(
                BuiltinResult::NotApplicable
                | BuiltinResult::Effect(_)
                | BuiltinResult::Unsupported(_),
            )
            | Err(_) => Folded::Term(node),
        })
    })
}

/// Whether `application` applies a pure builtin hook (its symbol is not `impure` and its hook is
/// no `IO.` operation) to ground constructor-like arguments: domain values, constructor
/// applications and closed collections of such items (`TermAttributes::constructor_like`, which
/// no term holding a variable or a function application has).
///
/// The hook's evaluator reads those arguments only: it applies no equation of the definition,
/// performs no effect, and refuses a result above its own size bounds, so evaluating it is one
/// bounded step, whatever the definition's equations do.
fn pure_hook_on_values(definition: &BackendDefinition, application: &Term) -> bool {
    let TermKind::Application {
        symbol, arguments, ..
    } = application.kind()
    else {
        return false;
    };
    symbol.attributes.hook.is_some()
        && !is_impure_application(definition, application)
        && arguments
            .iter()
            .all(|argument| argument.attributes().constructor_like)
}

/// Whether `term`, which [`fold_with_values`] left as it is, is a pure builtin hook application
/// on ground constructor-like arguments that its evaluator shows defined although this
/// evaluation does not take its value: a value only an execution chooses
/// (`implementation_chosen`, which the fold withholds on a proof route) or one of several values
/// the definition admits (`Unspecified` with `defined`). The application has a value in every
/// model, whichever it is, so its atom holds and no value is chosen. A result above a size bound
/// decides nothing here.
fn defined_without_value(definition: &BackendDefinition, term: &Term) -> Stoppable<bool> {
    if !pure_hook_on_values(definition, term) {
        return Ok(false);
    }
    Ok(matches!(
        evaluate_pure_hook(definition, term)?,
        Ok(BuiltinResult::Value(_)
            | BuiltinResult::Unsupported(UnsupportedHookReason::Unspecified { defined: true, .. }))
    ))
}

/// The evaluator's result on `application`, a pure builtin hook application on ground
/// constructor-like arguments ([`pure_hook_on_values`]), read from the open [`HookValueScope`]
/// of `definition` when that scope keeps it.
///
/// Such an evaluator reads its arguments only, so its result is a function of the application,
/// the definition (the sorts and kinds it checks its constructions against) and the evaluation
/// mode: no path condition, console, step or other state enters it. A kept result is read for an
/// application of the same symbol at the same sort arguments whose arguments are the very term
/// nodes the result was computed from, in the same mode, under the same definition. The entry
/// holds those nodes' identities ([`NodeIdentity`]), so no other node can take their addresses
/// while it exists, and the same nodes are equal terms: the key is exact. Comparing identities
/// costs one pointer comparison per argument, never a walk of a collection. An equal argument
/// that is another node (a copy, or a collection a step rebuilt) is not recognised, and the
/// application is evaluated, as it would be without the scope.
///
/// A result is kept the second time its application is read: the first read records only the
/// identities, which hold no term alive. So a collection that a step rebuilds, whose
/// applications are read once each, leaves nothing alive behind it, and one that stays the same
/// node is evaluated at most twice.
///
/// An application whose arguments are all domain values is evaluated each time, since its
/// evaluation costs no more than the lookup would; one with a collection or constructor argument
/// is the work that grows with its argument. A stop is never kept.
fn evaluate_pure_hook(
    definition: &BackendDefinition,
    application: &Term,
) -> Stoppable<Result<BuiltinResult, BuiltinError>> {
    let TermKind::Application { arguments, .. } = application.kind() else {
        return evaluate_in_definition(application, definition);
    };
    if arguments
        .iter()
        .all(|argument| matches!(argument.kind(), TermKind::DomainValue { .. }))
    {
        return evaluate_in_definition(application, definition);
    }
    let mode = crate::evaluation::current();
    let seen = HOOK_VALUES.with_borrow(|values| {
        values
            .as_ref()
            .filter(|values| std::ptr::eq(values.definition, definition))
            .and_then(|values| values.entry(mode, application))
            .map(|entry| entry.result.clone())
    });
    if let Some(Some(result)) = seen {
        return Ok(result);
    }
    #[cfg(test)]
    tests::HOOK_EVALUATIONS.with(|count| count.set(count.get() + 1));
    let result = evaluate_in_definition(application, definition)?;
    HOOK_VALUES.with_borrow_mut(|values| {
        let Some(values) = values
            .as_mut()
            .filter(|values| std::ptr::eq(values.definition, definition))
        else {
            return;
        };
        if let Some(entry) = values
            .entries
            .iter_mut()
            .find(|entry| entry.names(mode, application))
        {
            entry.result = Some(result.clone());
            return;
        }
        if values.entries.len() >= HOOK_VALUES_CAPACITY {
            values.entries.pop_front();
        }
        if let Some(entry) = HookValue::first_read(mode, application) {
            values.entries.push_back(entry);
        }
    });
    Ok(result)
}

/// How many applications a [`HookValueScope`] remembers; past it, the oldest is forgotten. Each
/// kept result can be as large as a collection argument, so the count bounds what the scope
/// holds alive to a few collections. A step reads at most two applications of one discarded
/// operand (a listing and its size), and the following steps read them again while the
/// collection is the same node.
const HOOK_VALUES_CAPACITY: usize = 4;

/// One application [`evaluate_pure_hook`] read, by the identity of its argument nodes.
struct HookValue {
    mode: EvaluationMode,
    symbol: Arc<Symbol>,
    sort_arguments: Vec<Sort>,
    arguments: Vec<NodeIdentity>,
    /// The evaluator's result, kept from the second read on.
    result: Option<Result<BuiltinResult, BuiltinError>>,
}

impl HookValue {
    /// The entry of a first read of `application`, which keeps no result.
    fn first_read(mode: EvaluationMode, application: &Term) -> Option<Self> {
        let TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } = application.kind()
        else {
            return None;
        };
        Some(Self {
            mode,
            symbol: Arc::clone(symbol),
            sort_arguments: sort_arguments.clone(),
            arguments: arguments.iter().map(Term::identity).collect(),
            result: None,
        })
    }

    /// Whether `application`, in `mode`, applies this entry's symbol at its sort arguments to
    /// the very argument nodes it names.
    fn names(&self, mode: EvaluationMode, application: &Term) -> bool {
        let TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } = application.kind()
        else {
            return false;
        };
        self.mode == mode
            && self.arguments.len() == arguments.len()
            && self
                .arguments
                .iter()
                .zip(arguments)
                .all(|(identity, argument)| identity.is(argument))
            && (Arc::ptr_eq(&self.symbol, symbol) || self.symbol == *symbol)
            && self.sort_arguments == *sort_arguments
    }
}

/// The applications [`evaluate_pure_hook`] read under the innermost open [`HookValueScope`],
/// oldest first.
struct HookValues {
    /// The scope's definition, which the scope borrows, so it is alive and unmoved while these
    /// results are reachable.
    definition: *const BackendDefinition,
    entries: VecDeque<HookValue>,
}

impl HookValues {
    fn entry(&self, mode: EvaluationMode, application: &Term) -> Option<&HookValue> {
        self.entries
            .iter()
            .find(|entry| entry.names(mode, application))
    }
}

thread_local! {
    /// The results of the innermost open [`HookValueScope`] on this thread.
    static HOOK_VALUES: RefCell<Option<HookValues>> = const { RefCell::new(None) };
}

/// A backend entry point's scope for the results of pure builtin hooks that the deferred
/// definedness steps evaluate ([`evaluate_pure_hook`]): within it, an application to the same
/// argument nodes under the same definition and evaluation mode is evaluated at most twice
/// while it is among the last [`HOOK_VALUES_CAPACITY`] read, however many steps, hook sites,
/// constraint simplifications and atom decisions read it. Opened beside
/// `term::domain::DomainScope` by the simplification, rewrite-step, execution and proof entry
/// points.
///
/// A scope entered with the definition of the innermost open scope shares that scope's results,
/// so a proof's or an execution's simplifications share its results; one entered with another
/// definition holds its own until it closes, and the enclosing results come back then. Scopes
/// close innermost first, as local guards do; the guard is not `Send`.
#[must_use = "the results are kept only while the scope is alive"]
pub(crate) struct HookValueScope<'a> {
    /// The enclosing results this scope replaced, restored when it closes; `None` when it
    /// shares them.
    replaced: Option<Option<HookValues>>,
    _definition: PhantomData<&'a BackendDefinition>,
    /// Not `Send` or `Sync`: the scope restores this thread's results.
    _thread: PhantomData<*const ()>,
}

impl<'a> HookValueScope<'a> {
    pub(crate) fn enter(definition: &'a BackendDefinition) -> Self {
        let shares = HOOK_VALUES.with_borrow(|values| {
            values
                .as_ref()
                .is_some_and(|values| std::ptr::eq(values.definition, definition))
        });
        let replaced = (!shares).then(|| {
            HOOK_VALUES.replace(Some(HookValues {
                definition,
                entries: VecDeque::with_capacity(HOOK_VALUES_CAPACITY),
            }))
        });
        Self {
            replaced,
            _definition: PhantomData,
            _thread: PhantomData,
        }
    }
}

impl Drop for HookValueScope<'_> {
    fn drop(&mut self) {
        if let Some(previous) = self.replaced.take() {
            HOOK_VALUES.set(previous);
        }
    }
}

/// The value of `application`, a ground application with literal arguments, by its one equation
/// step: the instance [`single_step`] selects, whose instantiated right-hand side [`fold_hooks`]
/// folds to a domain value (which is defined, so the step's instance has an obligation-free
/// result). `None` otherwise.
fn step_value(definition: &BackendDefinition, application: &Term) -> Stoppable<Option<Term>> {
    let Some((rule, substitution)) = select_single_step(definition, application)? else {
        return Ok(None);
    };
    let RuleRhs::Term(rhs) = &rule.rhs else {
        return Ok(None);
    };
    Ok(
        match fold_hooks(definition, &substitute(rhs, &substitution))? {
            Folded::Term(value) if matches!(value.kind(), TermKind::DomainValue { .. }) => {
                Some(value)
            }
            Folded::Term(_) | Folded::Bottom(_) => None,
        },
    )
}

/// [`fold_hooks`] where a stop only forgoes the fold: the term is kept as it is, which is sound,
/// and a stop of the request stays raised for its owner's next poll.
pub(crate) fn fold_hooks_or_keep(definition: &BackendDefinition, term: &Term) -> Folded {
    match fold_hooks(definition, term) {
        Ok(folded) => folded,
        Err(stop) => {
            stop.forgo_refinement();
            Folded::Term(term.clone())
        }
    }
}

/// The truth of `predicate`, an instantiated condition, when [`fold_hooks`] of its terms decides
/// it; `None` otherwise. Only Boolean literals, and domain values of the builtin Bool, Int and
/// String sorts (which have one text per value), are compared. The `\ceil` of a `ceil_free`
/// term holds, and so does that of one of `siblings`, the arguments of the atom's subject, whose
/// definedness the atom's sibling atoms state ([`deferred_obligations`] states every argument's).
fn fold_predicate(
    definition: &BackendDefinition,
    predicate: &Predicate,
    siblings: &[Term],
) -> Stoppable<Option<bool>> {
    let fold = |term: &Term| -> Stoppable<Option<Term>> {
        Ok(match fold_hooks(definition, term)? {
            Folded::Term(folded) => Some(folded),
            Folded::Bottom(_) => None,
        })
    };
    let comparable = |term: &Term| match term.kind() {
        TermKind::DomainValue { sort, .. } => {
            sort.is_builtin(BuiltinSort::Bool)
                || sort.is_builtin(BuiltinSort::Int)
                || sort.is_builtin(BuiltinSort::String)
        }
        _ => false,
    };
    Ok(match predicate {
        Predicate::True => Some(true),
        Predicate::False => Some(false),
        Predicate::Term(term) => fold(term)?.as_ref().and_then(bool_literal),
        Predicate::Equals(left, right) => match (fold(left)?, fold(right)?) {
            (Some(left), Some(right)) if comparable(&left) && comparable(&right) => {
                (left.sort() == right.sort()).then_some(left == right)
            }
            _ => None,
        },
        Predicate::Not(inner) => fold_predicate(definition, inner, siblings)?.map(|value| !value),
        Predicate::And(conjuncts) => {
            let mut all = Some(true);
            for conjunct in conjuncts {
                match fold_predicate(definition, conjunct, siblings)? {
                    Some(false) => return Ok(Some(false)),
                    Some(true) => {}
                    None => all = None,
                }
            }
            all
        }
        Predicate::Ceil(term) | Predicate::Defined(term)
            if term.attributes().ceil_free() || siblings.contains(term) =>
        {
            Some(true)
        }
        _ => None,
    })
}

/// What [`decide_defined`] made of an atom `Defined(t)`.
pub(crate) enum DeferredDecision {
    /// `t` is defined.
    Established,
    /// `t` is undefined.
    Refuted,
    /// `t` folded to another term: these atoms state its definedness instead.
    Replaced(Vec<Predicate>),
    /// Undecided: the atom stays.
    Open,
}

/// Decide `Defined(t)` by bounded steps, which take at most one equation instance per application
/// and never evaluate its result, in order:
/// - D1, fold `t` by pure builtin hooks on ground constructor-like arguments, a ground function
///   application on literal arguments also taking the value of its one equation step when hooks
///   fold that step's right-hand side to a literal ([`fold_with_values`]): an undefined hook
///   refutes the atom, and a changed term replaces it by the [`deferred_obligations`] of the
///   result; a hook application the evaluator shows defined without this evaluation taking its
///   value establishes the atom ([`defined_without_value`]);
/// - D3, a map or set without a rest whose keys or elements fold to domain values: pairwise
///   distinct ones establish its own condition, a repeated one refutes it (the atoms of its
///   values and elements are its siblings);
/// - D2, an unconditional ceil equation of `t`'s root, used when hooks decide every conjunct of
///   its instantiated condition, or, when `t`'s arguments and what is left of the condition are
///   hook arithmetic over variables and literals, stated in the atom's place (D2');
/// - D4, one function equation step selected by matching alone ([`single_step`]).
///
/// Known facts (D6) and the solver (D7) are read by the predicate simplifier and the solver
/// around this decision.
pub(crate) fn decide_defined(
    definition: &BackendDefinition,
    term: &Term,
) -> Stoppable<Result<DeferredDecision, DeferredOutcome>> {
    if term.attributes().ceil_free() {
        return Ok(Ok(DeferredDecision::Established));
    }
    // An atom whose subject holds an impure application is never kept: it is the outcome.
    if let Some(outcome) = impure_outcome(definition, term) {
        return Ok(Err(outcome));
    }
    match fold_with_values(definition, term)? {
        Folded::Bottom(_) => return Ok(Ok(DeferredDecision::Refuted)),
        Folded::Term(folded) if !folded.ptr_eq(term) && folded != *term => {
            return Ok(deferred_obligations(definition, &folded).map(DeferredDecision::Replaced));
        }
        Folded::Term(_) => {}
    }
    if defined_without_value(definition, term)? {
        return Ok(Ok(DeferredDecision::Established));
    }
    if let Some(decision) = literal_collection(definition, term)? {
        return Ok(Ok(decision));
    }
    if let Some(decision) = ceil_equation(definition, term)? {
        return Ok(Ok(decision));
    }
    if let Some(decision) = single_step(definition, term)? {
        return Ok(Ok(decision));
    }
    Ok(Ok(DeferredDecision::Open))
}

/// D3: the key condition of a map or set without a rest whose keys or elements fold to domain
/// values.
fn literal_collection(
    definition: &BackendDefinition,
    term: &Term,
) -> Stoppable<Option<DeferredDecision>> {
    let keys: Vec<&Term> = match term.kind() {
        TermKind::Map {
            entries,
            rest: None,
            ..
        } => entries.iter().map(|(key, _)| key).collect(),
        TermKind::Set {
            elements,
            rest: None,
            ..
        } => elements.iter().collect(),
        _ => return Ok(None),
    };
    let mut folded = Vec::with_capacity(keys.len());
    for key in keys {
        match fold_hooks(definition, key)? {
            Folded::Term(key) if matches!(key.kind(), TermKind::DomainValue { .. }) => {
                if folded.contains(&key) {
                    return Ok(Some(DeferredDecision::Refuted));
                }
                folded.push(key);
            }
            // An undefined key is stated by the key's own atom, and a key that is not a literal
            // leaves the condition undecided.
            Folded::Term(_) | Folded::Bottom(_) => return Ok(None),
        }
    }
    Ok(Some(DeferredDecision::Established))
}

/// D2: the first unconditional ceil equation of `term`'s root whose instantiated condition
/// [`fold_predicate`] decides.
fn ceil_equation(
    definition: &BackendDefinition,
    term: &Term,
) -> Stoppable<Option<DeferredDecision>> {
    let arguments = match term.kind() {
        TermKind::Application { arguments, .. } => arguments.as_slice(),
        _ => &[],
    };
    let groups = applicable_groups(definition.ceil_theory(), &term_index(term));
    for rules in groups.values() {
        for rule in rules {
            if !rule.requires.is_empty()
                || !rule.computed_attributes.unbound_result_variables.is_empty()
                || !matches!(rule.rhs, RuleRhs::Predicates(_))
            {
                continue;
            }
            let (rule, EquationInstances::Matched(instances)) =
                equation_instances(definition, rule, term, &[])
            else {
                continue;
            };
            let RuleRhs::Predicates(predicates) = &rule.rhs else {
                unreachable!("renaming keeps the kind of the right-hand side");
            };
            for instance in instances {
                let Instance::Usable(substitution) = instance else {
                    continue;
                };
                let mut conjuncts = Vec::new();
                for predicate in predicates {
                    flatten_conjuncts(
                        substitute_predicate(predicate, &substitution),
                        &mut conjuncts,
                    );
                }
                let mut residual = Vec::new();
                for conjunct in conjuncts {
                    match fold_predicate(definition, &conjunct, arguments)? {
                        Some(false) => return Ok(Some(DeferredDecision::Refuted)),
                        Some(true) => {}
                        None => residual.push(conjunct),
                    }
                }
                if residual.is_empty() {
                    return Ok(Some(DeferredDecision::Established));
                }
                // D2': over hook arithmetic the instance of the ceil axiom is stated instead of
                // the opaque atom (`W1 =/=Int 0` for `W0 /Int W1`). It is an equivalence, and its
                // terms hold no part of the operand but variables and literals, so no definition
                // equation can reach the operand through it.
                if arguments
                    .iter()
                    .all(|argument| hook_arithmetic(definition, argument))
                    && residual.iter().all(|predicate| {
                        let mut arithmetic = true;
                        predicate.visit_terms(&mut |term| {
                            arithmetic &= hook_arithmetic(definition, term);
                        });
                        arithmetic
                    })
                {
                    return Ok(Some(DeferredDecision::Replaced(residual)));
                }
            }
        }
    }
    Ok(None)
}

/// The conjuncts of `predicate`, nested conjunctions flattened, `\top` left out.
fn flatten_conjuncts(predicate: Predicate, into: &mut Vec<Predicate>) {
    match predicate {
        Predicate::And(conjuncts) => {
            for conjunct in conjuncts {
                flatten_conjuncts(conjunct, into);
            }
        }
        Predicate::True => {}
        predicate => into.push(predicate),
    }
}

/// Whether `term` is built from element variables, domain values and applications of pure
/// `total` builtin hooks only: deciding a predicate over it applies no equation of the
/// definition to anything but hooks, and evaluates no function and performs no effect.
fn hook_arithmetic(definition: &BackendDefinition, term: &Term) -> bool {
    let mut pending = vec![term];
    while let Some(term) = pending.pop() {
        match term.kind() {
            TermKind::DomainValue { .. } => {}
            TermKind::Variable(variable) if variable.kind == VariableKind::Element => {}
            TermKind::Injection { term, .. } => pending.push(term),
            TermKind::Application {
                symbol, arguments, ..
            } if symbol.attributes.symbol_type == SymbolType::Function(FunctionType::Total)
                && symbol
                    .attributes
                    .hook
                    .as_deref()
                    .is_some_and(|hook| !hook.starts_with("IO."))
                && !definition.is_impure(&symbol.name) =>
            {
                pending.extend(arguments);
            }
            _ => return false,
        }
    }
    true
}

fn substitute_predicate(predicate: &Predicate, substitution: &Substitution) -> Predicate {
    #[expect(
        clippy::disallowed_methods,
        reason = "an instantiated ceil-equation or equation condition that is only folded by hooks; the definedness of the bindings is stated by the sibling atoms of the subject's arguments"
    )]
    let mut instantiated =
        crate::rewrite::substitute_predicates(std::slice::from_ref(predicate), substitution);
    instantiated.pop().expect("one predicate in, one out")
}

/// Whether `term`, below its root, has a function symbol (the hooked collection constructors
/// included, as a map, set or list pattern).
fn function_below_root(term: &Term) -> bool {
    let has_function = |term: &Term| {
        let mut pending = vec![term];
        while let Some(term) = pending.pop() {
            match term.kind() {
                TermKind::Application { symbol, .. }
                    if matches!(symbol.attributes.symbol_type, SymbolType::Function(_)) =>
                {
                    return true;
                }
                TermKind::Map { .. } | TermKind::Set { .. } | TermKind::List { .. } => return true,
                _ => pending.extend(children(term)),
            }
        }
        false
    };
    children(term).into_iter().any(has_function)
}

/// D4: decide `Defined(term)` by one function equation step whose selection is decided by
/// matching alone, without evaluating its right-hand side.
///
/// The step is an instance of an equation `term = r`, an axiom: an instantiated right-hand side
/// `\bottom` refutes the atom, and one whose [`deferred_obligations`] are empty establishes it
/// (the definedness of the arguments the instance binds is stated by the atom's siblings). The
/// selection is stricter than the evaluator's:
/// - function-theory equations only; simplification lemmas are neither competitors nor
///   selected;
/// - every higher-priority group is refuted by a failed match of every equation in it, and the
///   selected group has one equation with one usable instance, every other equation of it
///   failing to match;
/// - when a left-hand side it consults has a function symbol below its root, every argument of
///   `term` must be instance-normal, since a failed match against an unevaluated argument is a
///   refutation only of that argument's syntax;
/// - an `owise` equation's competitor antecedent (its first `requires` conjunct, stating that
///   no higher equation applies) is discharged by that refutation, and the rest of its
///   `requires` must fold to `true` by hooks, as must the whole `requires` of any other
///   equation;
/// - no `ensures`, and no right-hand-side variable the left-hand side does not bind.
///
/// Otherwise it decides nothing. It is one selection scan, so it terminates.
fn single_step(definition: &BackendDefinition, term: &Term) -> Stoppable<Option<DeferredDecision>> {
    let Some((rule, substitution)) = select_single_step(definition, term)? else {
        return Ok(None);
    };
    Ok(match &rule.rhs {
        RuleRhs::Bottom => Some(DeferredDecision::Refuted),
        RuleRhs::Term(rhs) => {
            let instantiated = substitute(rhs, &substitution);
            match deferred_obligations(definition, &instantiated) {
                Ok(atoms) if atoms.is_empty() => Some(DeferredDecision::Established),
                Ok(_) | Err(_) => None,
            }
        }
        _ => None,
    })
}

/// The equation instance [`single_step`] selects for `term`, with its `requires` folded to
/// `true` by hooks; `None` when the selection does not decide one.
fn select_single_step(
    definition: &BackendDefinition,
    term: &Term,
) -> Stoppable<Option<(RewriteRule, Substitution)>> {
    let TermKind::Application {
        symbol, arguments, ..
    } = term.kind()
    else {
        return Ok(None);
    };
    if !matches!(symbol.attributes.symbol_type, SymbolType::Function(_)) {
        return Ok(None);
    }
    let groups = applicable_groups(definition.function_theory(), &term_index(term));
    let mut arguments_normal = None;
    for rules in groups.values() {
        let mut candidate: Option<(RewriteRule, Substitution)> = None;
        for rule in rules {
            if function_below_root(&rule.lhs)
                && !*arguments_normal.get_or_insert_with(|| {
                    arguments
                        .iter()
                        .all(|argument| definition.instance_normal(argument).is_some())
                })
            {
                return Ok(None);
            }
            let (renamed, instances) = equation_instances(definition, rule, term, &[]);
            match instances {
                EquationInstances::NotMatched(_) => {}
                EquationInstances::Undecided => return Ok(None),
                EquationInstances::Matched(mut instances) => {
                    if candidate.is_some() || instances.len() != 1 {
                        return Ok(None);
                    }
                    let Some(Instance::Usable(substitution)) = instances.pop() else {
                        return Ok(None);
                    };
                    candidate = Some((renamed.into_owned(), substitution));
                }
            }
        }
        if let Some((rule, substitution)) = candidate {
            return Ok(
                selected_instance_applies(definition, &rule, &substitution, arguments)?
                    .then_some((rule, substitution)),
            );
        }
    }
    Ok(None)
}

/// Whether the selected instance of [`single_step`] applies: no `ensures`, no unbound result
/// variable, and a `requires` folded to `true` by hooks (an `owise` equation's competitor
/// antecedent discharged by the refutation of the higher groups).
fn selected_instance_applies(
    definition: &BackendDefinition,
    rule: &RewriteRule,
    substitution: &Substitution,
    arguments: &[Term],
) -> Stoppable<bool> {
    if !rule.ensures.is_empty() || !rule.computed_attributes.unbound_result_variables.is_empty() {
        return Ok(false);
    }
    let mut requires = rule.requires.iter().peekable();
    if rule.attributes.priority == OWISE_RULE_PRIORITY
        && requires
            .peek()
            .is_some_and(|first| matches!(first, Predicate::Not(_)))
    {
        requires.next();
    }
    for predicate in requires {
        let instantiated = substitute_predicate(predicate, substitution);
        if fold_predicate(definition, &instantiated, arguments)? != Some(true) {
            return Ok(false);
        }
    }
    Ok(true)
}

/// The constraints of a state given to an execution, with each `\ceil(t)` read as the deferred
/// atoms of `t` ([`deferred_obligations`]).
///
/// A state a run reports prints its open deferred atoms as `\ceil(t)`, and a client resumes
/// from such states. Read back as an ordinary `\ceil`, the obligation would be decided by
/// evaluating `t`, the operand the conditional never evaluated; read back as a lone atom,
/// `Defined(1 |-> f())` would lose the sibling `Defined(f())` its decision relies on. The input
/// cannot tell an ordinary `\ceil` from a deferred one, so every one over a term that holds a
/// function application is read this way, which can only leave open an obligation a continuous
/// run would have decided by evaluation; one over a term without a function application is kept,
/// since deciding it evaluates nothing. A `\ceil` whose deferred reading would hold an impure
/// application is the [`DeferredOutcome`].
pub(crate) fn resumed_constraints(
    definition: &BackendDefinition,
    constraints: Vec<Predicate>,
) -> Result<Vec<Predicate>, DeferredOutcome> {
    let mut read = Vec::with_capacity(constraints.len());
    for constraint in constraints {
        match resumed_predicate(definition, constraint)? {
            Predicate::And(conjuncts) => {
                for conjunct in conjuncts {
                    if !read.contains(&conjunct) {
                        read.push(conjunct);
                    }
                }
            }
            Predicate::True => {}
            predicate if !read.contains(&predicate) => read.push(predicate),
            _ => {}
        }
    }
    Ok(read)
}

/// Whether `term` holds an application of a function symbol.
fn has_function_application(term: &Term) -> bool {
    let mut pending = vec![term];
    while let Some(term) = pending.pop() {
        if let TermKind::Application { symbol, .. } = term.kind()
            && matches!(symbol.attributes.symbol_type, SymbolType::Function(_))
        {
            return true;
        }
        pending.extend(children(term));
    }
    false
}

fn resumed_predicate(
    definition: &BackendDefinition,
    predicate: Predicate,
) -> Result<Predicate, DeferredOutcome> {
    let recurse = |inner: Box<Predicate>| resumed_predicate(definition, *inner).map(Box::new);
    Ok(match predicate {
        // A subject without a function application has nothing to evaluate: its ordinary
        // `\ceil` is decided by its collections' key conditions over constructors and values
        // alone, and keeps what it states about them (the absence of a key from a rest).
        Predicate::Ceil(term) if !has_function_application(&term) => Predicate::Ceil(term),
        Predicate::Ceil(term) => {
            let mut atoms = deferred_obligations(definition, &term)?;
            match atoms.len() {
                0 => Predicate::True,
                1 => atoms.pop().expect("one atom"),
                _ => Predicate::And(atoms),
            }
        }
        Predicate::Not(inner) => Predicate::Not(recurse(inner)?),
        Predicate::And(inner) => Predicate::And(
            inner
                .into_iter()
                .map(|inner| resumed_predicate(definition, inner))
                .collect::<Result<_, _>>()?,
        ),
        Predicate::Or(inner) => Predicate::Or(
            inner
                .into_iter()
                .map(|inner| resumed_predicate(definition, inner))
                .collect::<Result<_, _>>()?,
        ),
        Predicate::Implies(left, right) => Predicate::Implies(recurse(left)?, recurse(right)?),
        Predicate::Iff(left, right) => Predicate::Iff(recurse(left)?, recurse(right)?),
        Predicate::Exists(variable, inner) => Predicate::Exists(variable, recurse(inner)?),
        Predicate::Forall(variable, inner) => Predicate::Forall(variable, recurse(inner)?),
        predicate @ (Predicate::True
        | Predicate::False
        | Predicate::Term(_)
        | Predicate::Equals(..)
        | Predicate::Defined(_)
        | Predicate::Floor(_)
        | Predicate::In(..)
        | Predicate::Absent(_)) => predicate,
    })
}

/// What the result of a short-circuit hook states about the operands it evaluated: the deciding
/// operand and, when its value is a literal, the selected one (the positions other than the
/// deferred ones).
///
/// The result is taken under the conditions of the deciding operand's simplification, which
/// state that operand defined and equal to its value, and is the selected operand's value, which
/// is defined wherever the result is and equal to the selected operand there. So on the result's
/// instances each evaluated operand is defined and equal to its simplified form, and two facts
/// follow without evaluating the discarded operand:
/// - an occurrence of an evaluated operand in the discarded one denotes its value, so it is read
///   as that value (`#if X ==K none #then M[N] #else X and {M[N]}:>Pred #fi` states the
///   definedness of `{v}:>Pred` for the value `v` of `M[N]`);
/// - every subterm of an evaluated operand is defined (application is strict), so no atom is
///   stated over one (`findChar`'s equation discards an operand that holds the very call its
///   condition evaluates).
///
/// An operand that holds an impure application is no such fact: two occurrences of a console
/// read are two reads. Operands are compared after the folding by builtin hooks on literals that
/// the discarded operand had.
pub(crate) struct EvaluatedOperands {
    /// Each evaluated operand as it was, folded, and its value.
    values: Vec<(Term, Term)>,
    /// The subterms of the evaluated operands as they were, folded.
    subterms: rustc_hash::FxHashSet<Term>,
}

impl EvaluatedOperands {
    /// The facts of `application`, a short-circuit hook's application with its operands
    /// simplified as the hook saw them, given `before`, the application before its operands were
    /// simplified, and the `deferred` positions. Nothing when `before` is not the same hook's.
    pub(crate) fn of(
        definition: &BackendDefinition,
        application: &Term,
        before: &Term,
        deferred: &[usize],
    ) -> Self {
        let mut facts = Self {
            values: Vec::new(),
            subterms: rustc_hash::FxHashSet::default(),
        };
        let (Some((kind, values)), Some((before_kind, operands))) =
            (ShortCircuit::of(application), ShortCircuit::of(before))
        else {
            return facts;
        };
        if kind != before_kind {
            return facts;
        }
        for (position, (operand, value)) in operands.iter().zip(values).enumerate() {
            if deferred.contains(&position) || impure_subterm(definition, operand).is_some() {
                continue;
            }
            let Folded::Term(folded) = fold_hooks_or_keep(definition, operand) else {
                continue;
            };
            if folded != *value && !folded.attributes().ceil_free() {
                facts.values.push((folded.clone(), value.clone()));
            }
            let mut pending = vec![folded];
            while let Some(term) = pending.pop() {
                if term.attributes().ceil_free() || !facts.subterms.insert(term.clone()) {
                    continue;
                }
                pending.extend(children(&term).into_iter().cloned());
            }
        }
        facts
    }

    /// The deferred atoms of `operand`, a discarded operand already folded by hooks, with the
    /// evaluated operands read as their values and the atoms over their subterms left out.
    pub(crate) fn discarded_obligations(
        &self,
        definition: &BackendDefinition,
        operand: &Term,
    ) -> Result<Vec<Predicate>, DeferredOutcome> {
        let replaced = self.replace(operand);
        let operand = if replaced.ptr_eq(operand) {
            replaced
        } else {
            match fold_hooks_or_keep(definition, &replaced) {
                Folded::Term(folded) => folded,
                Folded::Bottom(_) => return Ok(vec![Predicate::False]),
            }
        };
        let mut atoms = deferred_obligations(definition, &operand)?;
        atoms.retain(
            |atom| !matches!(atom, Predicate::Defined(subject) if self.subterms.contains(subject)),
        );
        Ok(atoms)
    }

    /// `term` with each occurrence of an evaluated operand replaced by its value, through
    /// applications, injections and conjunctions.
    fn replace(&self, term: &Term) -> Term {
        if self.values.is_empty() {
            return term.clone();
        }
        if let Some((_, value)) = self.values.iter().find(|(operand, _)| operand == term) {
            return value.clone();
        }
        match term.kind() {
            TermKind::Application {
                symbol,
                sort_arguments,
                arguments,
            } => {
                let replaced = arguments
                    .iter()
                    .map(|argument| self.replace(argument))
                    .collect::<Vec<_>>();
                if replaced
                    .iter()
                    .zip(arguments)
                    .all(|(new, old)| new.ptr_eq(old))
                {
                    term.clone()
                } else {
                    Term::application(symbol.clone(), sort_arguments.clone(), replaced)
                }
            }
            TermKind::Injection {
                source,
                target,
                term: inner,
            } => {
                let replaced = self.replace(inner);
                if replaced.ptr_eq(inner) {
                    term.clone()
                } else {
                    Term::injection(source.clone(), target.clone(), replaced)
                }
            }
            TermKind::And(left, right) => {
                let (new_left, new_right) = (self.replace(left), self.replace(right));
                if new_left.ptr_eq(left) && new_right.ptr_eq(right) {
                    term.clone()
                } else {
                    Term::and(new_left, new_right)
                }
            }
            _ => term.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;

    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::{HOOK_VALUES_CAPACITY, HookValueScope, evaluate_pure_hook};
    use crate::{
        builtin::BuiltinResult,
        definition::BackendDefinition,
        evaluation::EvaluationMode,
        proof::{ProofOptions, ProofStatus, prove_claim},
        rewrite::{ExecutionOptions, Pattern, execute},
        smt::NoSolver,
        stop::{CancellationToken, StopCause},
        term::{Sort, Symbol, Term, TermKind},
    };
    use std::sync::Arc;

    thread_local! {
        /// Test builds: the evaluator calls [`super::evaluate_pure_hook`] made on this thread.
        pub(super) static HOOK_EVALUATIONS: Cell<usize> = const { Cell::new(0) };
    }

    fn hook_evaluations() -> usize {
        HOOK_EVALUATIONS.with(Cell::get)
    }

    /// `loop(I, M, _) => loop(I -Int 1, M, #if true #then I #else choice(M) #fi)` while `I > 0`,
    /// and `loop(0, _, _) => done()`; the claim runs it six steps from a two-binding map, so
    /// every step discards the same `choice(M)`, whose value only an execution chooses.
    fn definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                hooked-sort SortMap{}
                    [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
                hooked-symbol mapUnit{}() : SortMap{} [function{}(), total{}(), hook{}("MAP.unit")]
                hooked-symbol mapItem{}(SortInt{}, SortInt{}) : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.element")]
                hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{}
                    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
                hooked-symbol choice{}(SortMap{}) : SortInt{} [function{}(), hook{}("MAP.choice")]
                hooked-symbol sizeMap{}(SortMap{}) : SortInt{}
                    [function{}(), total{}(), hook{}("MAP.size")]
                hooked-symbol iteP{S}(SortBool{}, S, S) : S
                    [function{}(), total{}(), hook{}("KEQUAL.ite")]
                hooked-symbol subInt{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), hook{}("INT.sub"), smt-hook{}("-")]
                hooked-symbol gtInt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.gt"), smt-hook{}(">")]
                hooked-symbol ite{}(SortBool{}, SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), hook{}("KEQUAL.ite")]
                sort SortState{} []
                symbol loop{}(SortInt{}, SortMap{}, SortInt{}) : SortState{} [constructor{}()]
                symbol done{}() : SortState{} [constructor{}()]
                alias weakAlwaysFinally{S}(S) : S
                    where weakAlwaysFinally{S}(@X:S) := @X:S []
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        loop{}(I:SortInt{}, M:SortMap{}, X:SortInt{}),
                        \equals{SortBool{}, SortState{}}(
                            gtInt{}(I:SortInt{}, \dv{SortInt{}}("0")),
                            \dv{SortBool{}}("true")
                        )
                    ),
                    loop{}(
                        subInt{}(I:SortInt{}, \dv{SortInt{}}("1")),
                        M:SortMap{},
                        ite{}(\dv{SortBool{}}("true"), I:SortInt{}, choice{}(M:SortMap{}))
                    )
                ) [label{}("step")]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        loop{}(\dv{SortInt{}}("0"), M:SortMap{}, X:SortInt{}),
                        \top{SortState{}}()
                    ),
                    done{}()
                ) [label{}("stop")]
                claim{} \implies{SortState{}}(
                    \and{SortState{}}(
                        loop{}(
                            \dv{SortInt{}}("6"),
                            mapConcat{}(
                                mapItem{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("10")),
                                mapItem{}(\dv{SortInt{}}("2"), \dv{SortInt{}}("20"))
                            ),
                            \dv{SortInt{}}("0")
                        ),
                        \top{SortState{}}()
                    ),
                    weakAlwaysFinally{SortState{}}(done{}())
                ) [label{}("loop")]
            endmodule []"#,
        )
        .expect("the definition parses");
        BackendDefinition::internalize(&syntax, "MAIN").expect("the definition internalizes")
    }

    fn term(definition: &BackendDefinition, source: &str) -> Term {
        let syntax = parse_pattern(source).expect("the term parses");
        definition
            .internalize_term(&syntax, &[])
            .expect("the term internalizes")
    }

    #[test]
    fn a_discarded_operand_is_evaluated_at_most_twice_whatever_the_steps_and_sites_that_read_it() {
        // Six steps each discard `choice(M)` over the same map node. Its evaluator's result
        // depends on the application, the definition and the evaluation mode alone, so it is
        // computed on the first read and on the second, which keeps it: on the proof route the
        // hook site, the state's constraints and the undefined-step check each read it, and on
        // the execution route each step's hook site.
        let definition = definition();
        let claim = &definition.reachability_claims()[0];
        let before = hook_evaluations();
        let proof = prove_claim(&definition, claim, &[], ProofOptions::default(), &NoSolver)
            .expect("the proof runs");
        assert_eq!(proof.status, ProofStatus::Proven, "{proof:#?}");
        let proof_route = hook_evaluations() - before;

        let before = hook_evaluations();
        let result = execute(
            &definition,
            Pattern {
                term: claim.lhs.term.clone(),
                constraints: Vec::new(),
            },
            ExecutionOptions {
                evaluation: EvaluationMode::Execution,
                ..ExecutionOptions::default()
            },
        );
        let [leaf] = result.leaves.as_slice() else {
            panic!("{:?}", result.leaves);
        };
        assert_eq!(leaf.pattern.term, term(&definition, "done{}()"));
        let execution_route = hook_evaluations() - before;
        assert_eq!(
            (proof_route, execution_route),
            (2, 2),
            "evaluations of the discarded choice(M) on the proof and execution routes"
        );
    }

    /// `choice(1 |-> 10 2 |-> 20)` in `definition`.
    fn choice(definition: &BackendDefinition) -> Term {
        term(
            definition,
            r#"choice{}(mapConcat{}(mapItem{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("10")), mapItem{}(\dv{SortInt{}}("2"), \dv{SortInt{}}("20"))))"#,
        )
    }

    /// The evaluator calls `read` makes, and the value it read.
    fn evaluations(definition: &BackendDefinition, application: &Term) -> (usize, BuiltinResult) {
        let before = hook_evaluations();
        let result = evaluate_pure_hook(definition, application)
            .expect("no stop is armed")
            .expect("the hook evaluates");
        (hook_evaluations() - before, result)
    }

    /// The evaluator calls of `reads` successive reads of `application`.
    fn reads(definition: &BackendDefinition, application: &Term, reads: usize) -> Vec<usize> {
        (0..reads)
            .map(|_| evaluations(definition, application).0)
            .collect()
    }

    #[test]
    fn a_result_is_read_for_the_same_argument_nodes_under_the_innermost_scope_of_its_definition() {
        // The first read records the argument nodes, the second keeps the result, and later
        // reads take it, with the same value. An equal copy is other nodes and is evaluated. The
        // scope's results are its definition's only: the same nodes under another definition
        // are neither read nor kept, a nested scope of another definition reads none of the
        // enclosing results and keeps none for them, and they come back when it closes.
        let first = definition();
        let second = definition();
        let application = choice(&first);
        let _outer = HookValueScope::enter(&first);
        let (count, value) = evaluations(&first, &application);
        assert_eq!(count, 1);
        assert_eq!(evaluations(&first, &application), (1, value.clone()));
        assert_eq!(evaluations(&first, &application), (0, value.clone()));
        assert_eq!(
            evaluations(&first, &application.unshared_copy()),
            (1, value.clone())
        );
        assert_eq!(reads(&second, &application, 3), [1, 1, 1]);
        {
            let _inner = HookValueScope::enter(&second);
            assert_eq!(reads(&second, &choice(&second), 3), [1, 1, 0]);
            assert_eq!(reads(&first, &application, 3), [1, 1, 1]);
        }
        assert_eq!(evaluations(&first, &application), (0, value));
    }

    #[test]
    fn a_stopped_evaluation_is_not_kept() {
        // A read that stops records nothing: the next reads are a first and a second read.
        let definition = definition();
        let application = choice(&definition);
        let _scope = HookValueScope::enter(&definition);
        let token = CancellationToken::new();
        token.cancel();
        for _ in 0..2 {
            match token.scope(|| evaluate_pure_hook(&definition, &application)) {
                Err(stop) => assert_eq!(stop.into_cause(), StopCause::Cancelled),
                Ok(result) => panic!("the cancelled request evaluated {result:?}"),
            }
        }
        assert_eq!(reads(&definition, &application, 3), [1, 1, 0]);
    }

    #[test]
    fn a_scope_keeps_its_last_applications_only() {
        // Past the capacity the oldest application is forgotten, which bounds the results a
        // scope holds alive.
        let definition = definition();
        let _scope = HookValueScope::enter(&definition);
        let applications: Vec<Term> = (0..=HOOK_VALUES_CAPACITY)
            .map(|_| choice(&definition).unshared_copy())
            .collect();
        for application in &applications {
            assert_eq!(reads(&definition, application, 2), [1, 1]);
        }
        assert_eq!(
            reads(&definition, &applications[HOOK_VALUES_CAPACITY], 1),
            [0]
        );
        assert_eq!(reads(&definition, &applications[1], 1), [0]);
        assert_eq!(reads(&definition, &applications[0], 1), [1]);
    }

    /// The evaluator calls of one read of `application`, whatever its result.
    fn one_read(definition: &BackendDefinition, application: &Term) -> usize {
        let before = hook_evaluations();
        let _ = evaluate_pure_hook(definition, application).expect("no stop is armed");
        hook_evaluations() - before
    }

    /// `application`'s symbol, sort arguments and argument nodes.
    fn parts(application: &Term) -> (Arc<Symbol>, Vec<Sort>, Vec<Term>) {
        let TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } = application.kind()
        else {
            panic!("{application:?} is no application");
        };
        (symbol.clone(), sort_arguments.clone(), arguments.clone())
    }

    #[test]
    fn another_hook_on_the_same_argument_nodes_takes_its_own_value() {
        // `choice(M)` is kept; `size(M)` on the very same map node is another application and
        // is evaluated: its value is the map's size, not the kept choice.
        let definition = definition();
        let chosen = choice(&definition);
        let (_, _, map) = parts(&chosen);
        let (size, _, _) = parts(&term(&definition, r#"sizeMap{}(mapUnit{}())"#));
        let sized = Term::application(size, Vec::new(), map);
        let _scope = HookValueScope::enter(&definition);
        assert_eq!(reads(&definition, &chosen, 3), [1, 1, 0]);
        assert_eq!(
            evaluations(&definition, &sized),
            (
                1,
                BuiltinResult::Value(term(&definition, r#"\dv{SortInt{}}("2")"#))
            )
        );
    }

    #[test]
    fn the_same_symbol_at_other_sort_arguments_is_another_application() {
        // `iteP{SortMap}(true, M, M)` is kept; the application of `iteP` at `SortState` to the
        // very same argument nodes differs in its sort arguments only, which fix its result
        // sort, and is evaluated.
        let definition = definition();
        let map = r#"mapConcat{}(mapItem{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("10")), mapItem{}(\dv{SortInt{}}("2"), \dv{SortInt{}}("20")))"#;
        let at_map = term(
            &definition,
            &format!(r#"iteP{{SortMap{{}}}}(\dv{{SortBool{{}}}}("true"), {map}, {map})"#),
        );
        let (ite, _, arguments) = parts(&at_map);
        let at_state = Term::application(ite, vec![Sort::simple("SortState")], arguments);
        let _scope = HookValueScope::enter(&definition);
        assert_eq!(
            [
                one_read(&definition, &at_map),
                one_read(&definition, &at_map),
                one_read(&definition, &at_map)
            ],
            [1, 1, 0]
        );
        assert_eq!(one_read(&definition, &at_state), 1);
    }
}
