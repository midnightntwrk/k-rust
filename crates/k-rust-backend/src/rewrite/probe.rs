//! A probe: an in-process caller that observes the steps of selected rules along a run's path,
//! and may end the request or the path there ([`ExecutionOptions::probe_rules`](super::ExecutionOptions::probe_rules)).
//!
//! # Meaning
//!
//! A *point* is a step `s → s'` by a rule [`ProbeRules`] selects, on its before or after side,
//! whose successor `s'` is defined, and which the path takes. Its *observed state* is `s` for a
//! before point and the normalized `s'` for an after point, the same states a stop's cut-point
//! and terminal rules end a path at ([`StopSide`]). A rule is selected by its label or its
//! `UNIQUE_ID`, as a stop rule is.
//!
//! The probe is asked at each point ([`Probe::observe`]), once, in path order; at one step the
//! before point is asked before the after point. Its answer decides what follows:
//! - [`ProbeDecision::Continue`]: nothing; the path goes on as without the probe.
//! - [`ProbeDecision::Differs`]: the request ends. The path's leaf is the observed state, with
//!   the halt [`HaltReason::ProbeDifference`](super::HaltReason::ProbeDifference), and no
//!   pending state is explored.
//! - [`ProbeDecision::Done`]: the path ends, its leaf the observed state with the halt
//!   [`HaltReason::ProbeDone`](super::HaltReason::ProbeDone).
//!
//! Neither halt is an end of the system: each says where the probe stopped the run, never that
//! the configuration is final. Neither is ever merged with another leaf, and only a request
//! with a probe has them.
//!
//! A point exists only because its step's successor is defined, so the leaf an answer makes
//! carries the successor's diagnostics: the path's up to the step and every one the step and
//! the successor's normalization added (a simplification budget spent before an equation that
//! would have shown the successor undefined, a path fact). At an after point they are the
//! observed state's own; at a before point the leaf is otherwise the state before the step.
//!
//! Whether a step's successor is defined is shown by the successor's own normalization, so the
//! points of a step are asked once that normalization shows it defined, before anything else
//! is done with it (the depth bound, merging, the next step). A step whose successor is
//! undefined, or whose normalization did not finish (a stop, a failed simplification, the work
//! budget reached first), has no point. A step a stop ends the path before is not taken, so the
//! `stop_count`th event of a cut-point rule has no point; a terminal rule's step is taken, so
//! its after point is asked, and the path then ends at the terminal rule unless the probe ended
//! it first.
//!
//! # One path
//!
//! The probe observes one path. A run's path splits where the state being expanded leaves more
//! than one path: several successors (applied candidates or a remainder), a successor beside
//! leaves of the same step (an undefined step's instances), or a branch leaf reporting several
//! successors. There the probe is told once ([`Probe::branched`]), and from then on it is asked
//! nothing: its callbacks name no path, so the points of several paths, in the order the run
//! explores them, are no sequence of one path. Where the path ends first, at any leaf other than
//! the probe's own, the probe is told once ([`Probe::ended`]) and reads the leaf's state.
//! Under strategy `any` each instance of a state takes the successors of one rule at most, but
//! a state still leaves several paths where its instances take different rules or a remainder
//! (a symbolic state), or where the rule's right-hand side has several alternatives; the probe
//! is told of a split there as under `all`.
//!
//! # What the run records of a step with a point
//!
//! A step whose points are asked is taken: its successor was built, normalized and shown
//! defined. Where an answer ends the path at a before point, the run's own records count the
//! step as they count every taken step: the rule is committed and its bindings recorded
//! (coverage), and the successor is matched as a reached state
//! ([`ExecutionOptions::match_states`](super::ExecutionOptions::match_states)); so is the
//! successor at an after point, which takes part in no merging. The leaf is the observed state:
//! its depth, trace, branch, observations, effects and counts end before the step, and only its
//! diagnostics, as above, include the step's. A cut-point rule's last event differs: its step is
//! not taken, so it is proposed and never committed, its successor is not matched, and the leaf
//! carries it as a proposal.
//!
//! # Continue changes nothing
//!
//! A probe that always continues leaves the run as it is without the probe: the same leaves,
//! coverage, traces and work. The probe is asked at a point of the successor's normalization
//! the run reaches anyway and costs the run no state visit; nothing the probe does is the run's
//! (below).
//!
//! # Isolation
//!
//! The probe is asked from the stepping loop, between two phases of a state's expansion, never
//! inside a simplification or a rewrite, and isolated from the run as a stop condition is
//! (`stop_condition`, "Isolation"): it reports to no coverage set, emits no diagnostic into
//! the run, notes no path fact, fills none of the run's memos, runs off the run's clock, in a
//! proof evaluation scope without a console and outside the run's definition scope. A
//! cancellation of the request stays visible inside it and ends the run at its next poll.
//!
//! # Reading a state
//!
//! The observed state is read through [`ProbeState`]: a cell by its path of cell symbols, its
//! cost the walk down the path and the size of the cell; a handle on a cell
//! ([`ProbeState::cell_handle`]), which tells an unchanged cell from a changed one at the cost
//! of a pointer comparison while the handle is held; and a list cell's length and the items
//! from a position on ([`ProbeState::list_len`], [`ProbeState::list_items`]), so a log is read
//! by what was appended since the last read.

use std::collections::BTreeSet;

use k_rust_kore::kore::ast as kore;

use super::{HaltReason, StopSide};
use crate::term::{Term, TermKind};

/// The rules whose steps a probe observes, by label or `UNIQUE_ID`, on each side of the step
/// ([module documentation](self)).
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ProbeRules {
    /// The rules whose steps are before points: the observed state is the state before the step.
    pub before: BTreeSet<String>,
    /// The rules whose steps are after points: the observed state is the normalized successor.
    pub after: BTreeSet<String>,
}

impl ProbeRules {
    /// Whether no rule is selected on either side.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.before.is_empty() && self.after.is_empty()
    }
}

/// What a [`Probe`] answers at a point.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProbeDecision {
    /// The path goes on as without the probe.
    Continue,
    /// The request ends at the observed state, `probe-difference`, with this reason.
    Differs(String),
    /// The path ends at the observed state, `probe-done`.
    Done,
}

/// An in-process observer of a run's path ([module documentation](self)).
pub trait Probe {
    /// Answer a point: a taken step of a selected rule whose successor is defined. A before
    /// point reads the state before the step, an after point the normalized successor.
    fn observe(&mut self, point: &ProbeArrival<'_>) -> ProbeDecision;

    /// The path split at the state at `depth`: from here the run has more than one path, and
    /// the probe is asked nothing more. Asked at most once.
    fn branched(&mut self, depth: u64) {
        let _ = depth;
    }

    /// The path ended at `leaf`, a leaf other than one the probe's own answer made, before it
    /// split. Asked at most once, and never after [`Self::branched`].
    fn ended(&mut self, leaf: &ProbeLeaf<'_>);
}

/// A state as a probe reads it: its depth and its configuration.
pub struct ProbeState<'a> {
    pub(crate) depth: u64,
    pub(crate) term: &'a Term,
}

impl ProbeState<'_> {
    /// The depth of the state on its path.
    #[must_use]
    pub fn depth(&self) -> u64 {
        self.depth
    }

    /// The state's whole configuration (its term, without its constraints), as KORE. Its cost
    /// is the size of the configuration; [`Self::cell`] converts one cell.
    #[must_use]
    pub fn configuration(&self) -> kore::Pattern {
        crate::externalize::term(self.term)
    }

    /// The cell at `path` of the configuration, as KORE, or `None` where the configuration holds
    /// no such cell.
    ///
    /// `path` names cell symbols from the configuration's top cell down: `path[0]` is the
    /// configuration's own symbol, and each further symbol is that of a cell the previous one
    /// holds as a direct argument. Only that cell is converted, so the cost is the walk down the
    /// path and the size of the cell, not of the configuration.
    #[must_use]
    pub fn cell(&self, path: &[&str]) -> Option<kore::Pattern> {
        cell_term(self.term, path).map(crate::externalize::term)
    }

    /// A handle on the cell at `path` ([`Self::cell`]), or `None` where there is no such cell.
    /// Two handles are [`CellHandle::same`] when they hold the same term node: a cell no step
    /// rewrote keeps its node, so an unchanged cell is told from a changed one without
    /// converting either. The handle holds the node, so it is not freed while the handle exists.
    #[must_use]
    pub fn cell_handle(&self, path: &[&str]) -> Option<CellHandle> {
        cell_term(self.term, path).map(|cell| CellHandle(cell.clone()))
    }

    /// The number of items of the list the cell at `path` holds, or `None` where there is no
    /// such cell or its content is not a list of known items.
    ///
    /// The cell's content is the cell's one argument, a list of a collection sort, or the cell
    /// itself where `path` names no cell symbol below a list. A list whose middle is not a list
    /// of items (a variable, an unevaluated application) has no known items.
    #[must_use]
    pub fn list_len(&self, path: &[&str]) -> Option<usize> {
        list_heads(self.term, path).map(crate::term::Items::len)
    }

    /// The items of the list the cell at `path` holds ([`Self::list_len`]) from position `from`
    /// on, each element as KORE (without its `ListItem` wrapper), or `None` where there is no
    /// such list. Only those items are converted, so a log read by what was appended since its
    /// last length costs the walk down the path and the size of the new items. A `from` past the
    /// end reads none.
    #[must_use]
    pub fn list_items(&self, path: &[&str], from: usize) -> Option<Vec<kore::Pattern>> {
        let heads = list_heads(self.term, path)?;
        if from >= heads.len() {
            return Some(Vec::new());
        }
        Some(heads.range(from..).map(crate::externalize::term).collect())
    }
}

/// A point a [`Probe`] is asked about: the rule, the side and the observed state.
pub struct ProbeArrival<'a> {
    pub(crate) rule: &'a str,
    pub(crate) side: StopSide,
    pub(crate) state: ProbeState<'a>,
}

impl<'a> ProbeArrival<'a> {
    /// The rule, by the name the request selected it by.
    #[must_use]
    pub fn rule(&self) -> &str {
        self.rule
    }

    /// Whether the observed state is before the rule's step or its normalized successor.
    #[must_use]
    pub fn side(&self) -> StopSide {
        self.side
    }

    /// The observed state.
    #[must_use]
    pub fn state(&self) -> &ProbeState<'a> {
        &self.state
    }
}

impl<'a> std::ops::Deref for ProbeArrival<'a> {
    type Target = ProbeState<'a>;

    fn deref(&self) -> &Self::Target {
        &self.state
    }
}

/// The leaf a path ended at, as [`Probe::ended`] is told of it.
pub struct ProbeLeaf<'a> {
    pub(crate) halt: &'a HaltReason,
    pub(crate) state: ProbeState<'a>,
}

impl<'a> ProbeLeaf<'a> {
    /// The leaf's halt.
    #[must_use]
    pub fn halt(&self) -> &HaltReason {
        self.halt
    }

    /// The leaf's state: its depth and configuration.
    #[must_use]
    pub fn state(&self) -> &ProbeState<'a> {
        &self.state
    }
}

impl<'a> std::ops::Deref for ProbeLeaf<'a> {
    type Target = ProbeState<'a>;

    fn deref(&self) -> &Self::Target {
        &self.state
    }
}

/// A held cell of an observed state ([`ProbeState::cell_handle`]).
#[derive(Clone, Debug)]
pub struct CellHandle(Term);

impl CellHandle {
    /// Whether both handles hold the same term node. Equal nodes are equal cells; distinct
    /// nodes may still be equal cells, which [`Self::kore`] then tells.
    #[must_use]
    pub fn same(&self, other: &Self) -> bool {
        self.0.ptr_eq(&other.0)
    }

    /// The cell as KORE.
    #[must_use]
    pub fn kore(&self) -> kore::Pattern {
        crate::externalize::term(&self.0)
    }
}

/// The cell at `path` of `term` ([`ProbeState::cell`]).
pub(super) fn cell_term<'t>(term: &'t Term, path: &[&str]) -> Option<&'t Term> {
    let (first, below) = path.split_first()?;
    let mut current = term;
    if application_symbol(current)? != *first {
        return None;
    }
    for symbol in below {
        let TermKind::Application { arguments, .. } = current.kind() else {
            return None;
        };
        current = arguments
            .iter()
            .find(|argument| application_symbol(argument) == Some(symbol))?;
    }
    Some(current)
}

/// The items of the list the cell at `path` of `term` holds, where the list has no middle
/// ([`ProbeState::list_len`]).
fn list_heads<'t>(term: &'t Term, path: &[&str]) -> Option<&'t crate::term::Items<Term>> {
    let cell = cell_term(term, path)?;
    let list = match cell.kind() {
        TermKind::Application { arguments, .. } => match arguments.as_slice() {
            [content] => content,
            _ => return None,
        },
        _ => cell,
    };
    match list.kind() {
        TermKind::List {
            heads, rest: None, ..
        } => Some(heads),
        _ => None,
    }
}

fn application_symbol(term: &Term) -> Option<&str> {
    match term.kind() {
        TermKind::Application { symbol, .. } => Some(&symbol.name),
        _ => None,
    }
}

/// Run `ask`, an in-process caller's work, isolated from the run ([module documentation](self),
/// "Isolation"): no coverage, no diagnostic, no path fact, off the run's clock, in a proof
/// evaluation scope, outside the run's definition scope.
pub(super) fn isolated<R>(ask: impl FnOnce() -> R) -> R {
    let (answer, _) = crate::coverage::isolated(u64::MAX, || {
        let _proof =
            crate::evaluation::EvaluationScope::enter(crate::evaluation::EvaluationMode::Proof);
        crate::term::domain::outside_definition_scopes(ask)
    });
    answer
}
