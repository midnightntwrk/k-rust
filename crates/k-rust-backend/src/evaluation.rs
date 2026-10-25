//! Whether an evaluation runs inside an execution, which may compute a value the definition
//! leaves to the implementation, or outside one, where only consequences of the definition are
//! computed.
//!
//! Some hooks have several values the definition admits on the same arguments: `keys_list`,
//! `values` and `Set2List` of two or more items list them in some order that domains.md does not
//! fix. A run of a program needs a value, and any one the definition admits is a correct run, so
//! an execution lists the items in k-rust's documented order. A proof, an implication check, a
//! simplification or a model asked for outside an execution must not depend on that choice: a
//! verdict that holds only in k-rust's order is not a consequence of the definition, so there the
//! application stays unevaluated, as a defined value the definition leaves open
//! (`UnsupportedHookReason::Unspecified` with `defined: true`).
//!
//! The mode is the innermost open [`EvaluationScope`] on the thread, and [`EvaluationMode::Proof`]
//! when none is open. An execution or search entry point of the engine opens a scope with the mode
//! its options ask for (`ExecutionOptions::evaluation`, `SearchOptions::evaluation`), so every
//! evaluation it runs, a rule's or an equation's condition included, sees that mode, and nothing
//! outside it does. Everything an entry point evaluates runs on its own thread before it returns:
//! deep evaluation grows the stack on the same thread (`nesting`), and results are collected
//! before the scope closes.

use std::{cell::Cell, marker::PhantomData};

/// The mode an evaluation runs in.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Hash)]
pub enum EvaluationMode {
    /// Compute only values that are consequences of the definition: a hook application whose
    /// value the definition leaves to the implementation stays unevaluated, as a defined value.
    /// Proofs, implication checks, simplification, models, and every request that does not ask
    /// for an execution.
    #[default]
    Proof,
    /// Run a program: a hook application whose value the definition leaves to the
    /// implementation takes k-rust's documented value (docs/compatibility.md,
    /// "Implementation-chosen hook values").
    Execution,
}

thread_local! {
    /// The mode of the innermost open [`EvaluationScope`] on this thread.
    static MODE: Cell<EvaluationMode> = const { Cell::new(EvaluationMode::Proof) };
    /// Whether the innermost open [`EvaluationScope`] on this thread is that of a run with a
    /// console ([`console_attached`]).
    static CONSOLE: Cell<bool> = const { Cell::new(false) };
}

/// The mode evaluations on this thread run in now: that of the innermost open scope, or
/// [`EvaluationMode::Proof`] when none is open.
pub fn current() -> EvaluationMode {
    MODE.with(Cell::get)
}

/// Whether the evaluations on this thread belong to a run of a program that has a console: the
/// innermost open scope is the one an execution with console input opened
/// ([`EvaluationScope::enter_run`]). It is a property of the run, not of one simplification, so
/// it holds also where the run simplifies without the console, as in a function equation's
/// condition: an effect left unperformed there is one another backend may perform
/// (`crate::simplify`, `note_effect_order`). A scope opened inside the run, such as a proof route
/// or a definition load, has no console.
pub(crate) fn console_attached() -> bool {
    CONSOLE.with(Cell::get)
}

/// Run `action` with the evaluation mode `mode`, restoring the previous mode afterwards (also when
/// `action` unwinds). Only a run of a program may ask for `Execution`; see [`EvaluationScope`].
pub fn with_evaluation<R>(mode: EvaluationMode, action: impl FnOnce() -> R) -> R {
    let _scope = EvaluationScope::enter(mode);
    action()
}

/// An open evaluation mode: evaluations on this thread run in its mode until it is dropped, or
/// until a scope opened inside it is open, and then the previous mode is restored.
///
/// A proof, an implication check, a simplification or a model must never run inside an
/// `Execution` scope: its verdict would read values the definition leaves open. The k-rust
/// facade's proof routes, and every definition load, enter a `Proof` scope themselves.
///
/// Scopes must be dropped innermost first, as local guards are: dropping restores the mode that
/// was current when this scope was entered, so dropping an outer scope before an inner one leaves
/// the inner scope's predecessor in place. [`with_evaluation`] keeps that order by construction.
/// The guard is not `Send`, since the mode belongs to the thread that entered it.
#[must_use = "the mode holds only while the scope is alive"]
pub struct EvaluationScope {
    previous: EvaluationMode,
    previous_console: bool,
    /// Not `Send` or `Sync`: the scope restores this thread's mode.
    _thread: PhantomData<*const ()>,
}

impl EvaluationScope {
    /// A scope of `mode` without a console.
    pub fn enter(mode: EvaluationMode) -> Self {
        Self::enter_run(mode, false)
    }

    /// The scope of a run in `mode`, which has a console when `console` holds
    /// ([`console_attached`]).
    pub(crate) fn enter_run(mode: EvaluationMode, console: bool) -> Self {
        Self {
            previous: MODE.with(|current| current.replace(mode)),
            previous_console: CONSOLE.with(|current| current.replace(console)),
            _thread: PhantomData,
        }
    }
}

impl Drop for EvaluationScope {
    fn drop(&mut self) {
        MODE.with(|current| current.set(self.previous));
        CONSOLE.with(|current| current.set(self.previous_console));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_innermost_scope_gives_the_mode_and_no_scope_is_proof() {
        assert_eq!(current(), EvaluationMode::Proof);
        with_evaluation(EvaluationMode::Execution, || {
            assert_eq!(current(), EvaluationMode::Execution);
            with_evaluation(EvaluationMode::Proof, || {
                assert_eq!(current(), EvaluationMode::Proof);
            });
            assert_eq!(current(), EvaluationMode::Execution);
        });
        assert_eq!(current(), EvaluationMode::Proof);
    }

    #[test]
    fn a_console_belongs_to_the_run_scope_and_not_to_a_scope_inside_it() {
        assert!(!console_attached());
        {
            let _run = EvaluationScope::enter_run(EvaluationMode::Execution, true);
            assert!(console_attached());
            with_evaluation(EvaluationMode::Proof, || assert!(!console_attached()));
            assert!(console_attached());
        }
        assert!(!console_attached());
    }

    #[test]
    fn a_scope_restores_the_mode_when_its_action_unwinds() {
        let unwound = std::panic::catch_unwind(|| {
            with_evaluation(EvaluationMode::Execution, || panic!("unwinds"));
        });
        assert!(unwound.is_err());
        assert_eq!(current(), EvaluationMode::Proof);
    }
}
