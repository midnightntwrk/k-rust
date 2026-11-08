//! Stop conditions: a named observation of the state, evaluated at each arrival at a stop, that
//! decides whether the arrival ends the run ([`crate::StopWhen`]).
//!
//! # What a stop condition is
//!
//! A run under stop rules ends at its `count`th *arrival* ([`crate::StopCriterion::Rules`]). A
//! stop condition is a function of named leaf cells, of result sort `Bool`, applied to the
//! arrival's *stop state*: the state the run would end at there, the state before a stop-before
//! rule's step and the successor of a stop-after rule's. An arrival whose stop state the
//! condition holds of is a *stop event*; the run ends at its `count`th event, and takes every
//! other arrival as any other step. The condition is a statement about the end the run would
//! report, so it is asked of that end and of no other state of the path, and only at arrivals:
//! the states between arrivals include the compiled definition's own steps (strictness, contexts),
//! which no KRS rule names, while an arrival at a KRS-named rule is a fact of the definition.
//!
//! # The observer
//!
//! The condition is resolved and evaluated in one fixed definition, its *observer*: a definition
//! compiled from a package that depends on the run's definition (as a view's observer is,
//! [`crate::views`]), or the run's own definition. It is never evaluated in the running
//! definition itself: an observation of a system does not change the system, and a run of an
//! edited definition (a mutant) under the same condition must ask the same question of its
//! states. Each read cell's value is carried to the observer by its constructors' KRS
//! declarations, as a view's is: a value with a part that has no KRS description (a variable,
//! an unevaluated application, a freezer) has no observation.
//!
//! # Cells
//!
//! A condition reads declared, observable leaf cells, named by Rust field path, in the order of
//! its parameters. A cell below a repeated or optional holder is refused: applied per instance
//! it would give a set of answers, not one. An unobservable cell is refused: where the run ends
//! decides which ends are compared, so a condition over an unobservable cell would make a
//! comparison rest on it.
//!
//! # Answers
//!
//! The condition is evaluated as views are ([`crate::views`], "Evaluation"): as a consequence of
//! the observer alone, under the run's view budget of polls. `true` and `false` decide the
//! arrival. A result short of a value that the observer was shown to give no value is no
//! observation: the stop criterion is undefined on this run, which is refused
//! ([`crate::ExecError::StopCondition`]). An evaluation that stopped before it ended, or that
//! ended short of a value after the solver answered `Unknown`, leaves the arrival undecided: the
//! run ends there, `stop-undecided` ([`crate::Halt::StopUndecided`]), which is inconclusive.
//!
//! # Evaluating an observation at a state
//!
//! [`ResolvedCondition`] is a function of named cells resolved in an observer, of any result
//! sort; [`ResolvedCondition::evaluate`] evaluates it at any state that hands out its cells
//! ([`ObservedState`]: a stop's arrival, a probe's point, a state a run reached) and returns its
//! value whatever its sort. The stop condition is the use that reads a `Bool` from it
//! ([`ArrivalObservation`]); a run's observations ([`crate::observations`]) evaluate their
//! filters and function components with it too, so a condition and an observation are evaluated
//! alike.

use std::fmt;
use std::sync::Arc;

use k_rust::backend::{ProbeState, StopArrival, StopCondition, StopDecision, StopSide};
use k_rust::kore::ast::Pattern;
use krs_ir::{BuiltinSort, CellMultiplicity};

use crate::inputs::InputType;
use crate::values::{Decl, SortRef, Value, ValueIndex};
use crate::views::EvaluationError;
use crate::{ExecError, Semantics, StopWhen};

/// A state whose cells an observation reads: a stop's arrival ([`StopArrival`]), a probe's point
/// ([`ProbeState`]), or a state a run reached, as KORE.
pub trait ObservedState {
    /// The cell at `path` of cell symbols from the configuration's top cell down, as KORE, or
    /// `None` where the state holds no such cell.
    fn cell(&self, path: &[&str]) -> Option<Pattern>;
}

impl ObservedState for StopArrival<'_> {
    fn cell(&self, path: &[&str]) -> Option<Pattern> {
        StopArrival::cell(self, path)
    }
}

impl ObservedState for ProbeState<'_> {
    fn cell(&self, path: &[&str]) -> Option<Pattern> {
        ProbeState::cell(self, path)
    }
}

/// One cell a condition reads: its path as written, and the cell symbols from the
/// configuration's top down to it, which the backend follows to convert that cell alone.
#[derive(Clone, Debug)]
pub(crate) struct ReadCell {
    pub(crate) path: String,
    pub(crate) symbols: Vec<String>,
    parameter: Arc<str>,
}

impl ReadCell {
    /// The cell symbols as the backend's walk takes them.
    pub(crate) fn symbol_path(&self) -> Vec<&str> {
        self.symbols.iter().map(String::as_str).collect()
    }
}

/// How a resolution's refusals name the use being resolved: `what` as the subject of a
/// sentence ("a stop condition"), `noun` as the reader of a cell ("a condition").
#[derive(Clone, Copy, Debug)]
pub(crate) struct Use {
    pub(crate) what: &'static str,
    pub(crate) noun: &'static str,
}

impl Use {
    /// A stop condition's spelling, which every stop-condition refusal keeps.
    pub(crate) const STOP_CONDITION: Self = Self {
        what: "a stop condition",
        noun: "a condition",
    };
}

/// The value of the leaf cell `cell` reads in `state`, decoded by `subject`, the definition the
/// state is of; the refusal naming the cell where it has none to carry to an observer.
pub(crate) fn leaf_value(
    subject: &ValueIndex,
    cell: &ReadCell,
    state: &(impl ObservedState + ?Sized),
) -> Result<Value, ObservationError> {
    let refuse = |reason: String| ObservationError::Cell {
        cell: cell.path.clone(),
        reason,
    };
    let pattern = state
        .cell(&cell.symbol_path())
        .ok_or_else(|| refuse("is not held by the state".to_owned()))?;
    let content = leaf_content(&pattern)
        .ok_or_else(|| refuse("is not a leaf cell of the state".to_owned()))?;
    let value = subject
        .decode(content)
        .map_err(|error| refuse(format!("holds no term of the definition: {error}")))?;
    if let Some(part) = crate::views::opaque_part(subject, &value) {
        return Err(refuse(format!(
            "holds {part}, which has no KRS description to carry to an observer"
        )));
    }
    Ok(value)
}

/// The content of a leaf cell's KORE: its one argument.
pub(crate) fn leaf_content(pattern: &Pattern) -> Option<&Pattern> {
    match pattern {
        Pattern::Application { arguments, .. } => match arguments.as_slice() {
            [content] => Some(content),
            _ => None,
        },
        _ => None,
    }
}

/// A stop condition resolved in its observer for the definition a run executes
/// ([`Semantics::stop_condition`]).
#[derive(Clone, Debug)]
pub struct ResolvedCondition {
    /// The function as the condition named it.
    function: String,
    /// The observer's function.
    decl: Decl,
    /// The cells, in parameter order.
    cells: Vec<ReadCell>,
    /// The run's definition's values, which read the cells.
    subject: Arc<ValueIndex>,
    /// The observer's values, which the condition is evaluated with.
    observer: Arc<ValueIndex>,
    /// The function's declared result type, `None` for a sort no KRS declaration names.
    pub(crate) result: Option<InputType>,
}

impl ResolvedCondition {
    /// The function as the condition named it.
    #[must_use]
    pub fn function(&self) -> &str {
        &self.function
    }

    /// The observer's function the name resolved to, by its full KRS path.
    #[must_use]
    pub fn function_path(&self) -> &str {
        self.decl.path()
    }

    /// Each cell the condition reads, in parameter order, as the cell symbols from the
    /// configuration's top down to it: the path [`StopArrival::cell`] follows to convert that
    /// cell alone.
    pub fn cell_symbols(&self) -> impl Iterator<Item = &[String]> {
        self.cells.iter().map(|cell| cell.symbols.as_slice())
    }

    /// The cells the function reads, in parameter order.
    pub(crate) fn cells(&self) -> &[ReadCell] {
        &self.cells
    }

    /// The observer's values the function was resolved in.
    pub(crate) const fn observer_values(&self) -> &Arc<ValueIndex> {
        &self.observer
    }

    /// The function's value at the cells of `state`, evaluated in `observer`, the definition it
    /// was resolved in (the caller checks that it is), within `budget` polls when there is one.
    ///
    /// # Errors
    ///
    /// Returns [`ObservationError::Cell`] for a cell with no value to carry, and
    /// [`ObservationError::Evaluation`] for an evaluation without a value.
    pub(crate) fn evaluate(
        &self,
        observer: &mut Semantics,
        state: &(impl ObservedState + ?Sized),
        budget: Option<u64>,
    ) -> Result<Value, ObservationError> {
        let mut arguments = Vec::with_capacity(self.cells.len());
        for cell in &self.cells {
            arguments.push((
                cell.parameter.clone(),
                leaf_value(&self.subject, cell, state)?,
            ));
        }
        observer
            .evaluate_within(
                self.decl.path(),
                arguments
                    .iter()
                    .map(|(parameter, value)| (&**parameter, value.clone()))
                    .collect(),
                budget,
            )
            .map_err(ObservationError::Evaluation)
    }
}

/// Why an observation at an arrival has no value.
#[derive(Debug)]
pub enum ObservationError {
    /// A read cell has no value to carry to the observer: the state holds no such cell, or its
    /// content has a part with no KRS description, or is no term of the definition.
    Cell {
        /// The cell's path as written.
        cell: String,
        /// Why.
        reason: String,
    },
    /// The function's evaluation in the observer has no value ([`EvaluationError`]).
    Evaluation(EvaluationError),
}

impl fmt::Display for ObservationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Cell { cell, reason } => write!(formatter, "the cell `{cell}` {reason}"),
            Self::Evaluation(error) => error.fmt(formatter),
        }
    }
}

impl std::error::Error for ObservationError {}

impl ObservationError {
    /// Whether the observation is not known rather than absent: the evaluation stopped, or the
    /// solver left a condition undecided ([`EvaluationError::Stopped`],
    /// [`EvaluationError::Spent`], [`EvaluationError::Undecided`]).
    #[must_use]
    pub const fn is_undecided(&self) -> bool {
        matches!(
            self,
            Self::Evaluation(
                EvaluationError::Stopped(_)
                    | EvaluationError::Spent(_)
                    | EvaluationError::Undecided(_)
            )
        )
    }

    /// Whether the evaluation spent its budget of polls ([`EvaluationError::Spent`]), which a
    /// larger budget can decide, unlike another stop or an `Unknown` answer of the solver.
    #[must_use]
    pub const fn spent_budget(&self) -> bool {
        matches!(self, Self::Evaluation(EvaluationError::Spent(_)))
    }
}

/// The evaluation of a resolved condition's function at an arrival, in its observer, each
/// evaluation bounded by `budget` polls when there is one.
pub struct ArrivalObservation<'o> {
    condition: &'o ResolvedCondition,
    observer: &'o mut Semantics,
    budget: Option<u64>,
}

impl<'o> ArrivalObservation<'o> {
    /// The observation of `condition` at arrivals, evaluated in `observer`, the definition it
    /// was resolved in.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::StopWhen`] when `observer` is not that definition.
    pub fn new(
        condition: &'o ResolvedCondition,
        observer: &'o mut Semantics,
        budget: Option<u64>,
    ) -> Result<Self, ExecError> {
        if !Arc::ptr_eq(&condition.observer, observer.values()) {
            return Err(ExecError::StopWhen(format!(
                "the stop condition `{}` is evaluated in a definition other than the observer it was resolved in",
                condition.function
            )));
        }
        Ok(Self {
            condition,
            observer,
            budget,
        })
    }

    /// The function's value at the cells of `arrival`'s stop state.
    ///
    /// # Errors
    ///
    /// Returns [`ObservationError::Cell`] for a cell with no value to carry, and
    /// [`ObservationError::Evaluation`] for an evaluation without a value.
    pub fn observe(
        &mut self,
        arrival: &(impl ObservedState + ?Sized),
    ) -> Result<Value, ObservationError> {
        self.condition.evaluate(self.observer, arrival, self.budget)
    }
}

/// A stop condition's refusal at an arrival, as the oracle recorded it: the run's error names
/// the rule, the depth and the reason ([`ExecError::StopCondition`]).
#[derive(Clone, Debug)]
pub(crate) struct Refusal {
    /// The rule's `UNIQUE_ID`, as the run selected it.
    pub(crate) rule_id: String,
    /// The depth of the stop state along the request's path.
    pub(crate) depth: u64,
    pub(crate) reason: String,
}

/// An arrival where a stop condition was left undecided, as the oracle recorded it: the run's
/// report names the rule, the side of its step and the reason ([`crate::RunReport::undecided`]).
#[derive(Clone, Debug)]
pub(crate) struct UndecidedArrival {
    /// The rule's `UNIQUE_ID`, as the run selected it.
    pub(crate) rule_id: String,
    pub(crate) side: StopSide,
    /// Why the observation is not known ([`ObservationError::is_undecided`]).
    pub(crate) reason: String,
    /// Whether the evaluation spent its budget of polls ([`ObservationError::spent_budget`]).
    pub(crate) budget_spent: bool,
}

/// The backend's stop condition of a run ([`StopCondition`]): the observation's `Bool`, an
/// undecided observation undecided, any other observation without a value refused. A caller
/// that runs another backend under the condition (kink's runs of a definition and its mutants)
/// asks it as the backend's own runs do.
pub struct ConditionOracle<'o> {
    observation: ArrivalObservation<'o>,
    /// The refusal that failed the request, once one did.
    pub(crate) refusal: Option<Refusal>,
    /// The last arrival the condition was left undecided at: a path of the request ends there.
    pub(crate) undecided: Option<UndecidedArrival>,
}

impl<'o> ConditionOracle<'o> {
    /// The stop condition that answers by `observation`.
    #[must_use]
    pub const fn new(observation: ArrivalObservation<'o>) -> Self {
        Self {
            observation,
            refusal: None,
            undecided: None,
        }
    }
}

impl StopCondition for ConditionOracle<'_> {
    fn decide(&mut self, arrival: &StopArrival<'_>) -> StopDecision {
        let refuse = |oracle: &mut Self, reason: String| {
            oracle.refusal = Some(Refusal {
                rule_id: arrival.rule().to_owned(),
                depth: arrival.depth(),
                reason: reason.clone(),
            });
            StopDecision::Refused(reason)
        };
        match self.observation.observe(arrival) {
            Ok(Value::Bool(true)) => StopDecision::Holds,
            Ok(Value::Bool(false)) => StopDecision::Fails,
            Ok(other) => refuse(
                self,
                format!(
                    "`{}` gives no Bool here: {other:?}",
                    self.observation.condition.function
                ),
            ),
            Err(error) if error.is_undecided() => {
                let reason = error.to_string();
                let decision = StopDecision::Undecided(format!(
                    "`{}`: {reason}",
                    self.observation.condition.function
                ));
                self.undecided = Some(UndecidedArrival {
                    rule_id: arrival.rule().to_owned(),
                    side: arrival.side(),
                    reason,
                    budget_spent: error.spent_budget(),
                });
                decision
            }
            Err(error @ ObservationError::Cell { .. }) => refuse(self, error.to_string()),
            Err(error) => refuse(
                self,
                format!(
                    "`{}` has no value: {error}",
                    self.observation.condition.function
                ),
            ),
        }
    }
}

impl Semantics {
    /// Resolve the stop condition `when` in `observer`, the definition it is evaluated in (this
    /// definition itself, or another one composing it), for runs of this definition
    /// ([module documentation](crate::condition)).
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::StopWhen`] naming the cause: a function the observer does not hold,
    /// evaluated in an instance, parametric, or whose parameters are not one per cell, each of a
    /// sort that admits its cell's sort, or whose result is not `Bool`; and a cell that is
    /// unknown, unobservable, a group cell, or below a repeated or optional holder.
    pub fn stop_condition(
        &self,
        observer: &Self,
        when: &StopWhen,
    ) -> Result<ResolvedCondition, ExecError> {
        let resolved = self
            .cell_function(observer, &when.function, &when.cells, Use::STOP_CONDITION)
            .map_err(|message| {
                ExecError::StopWhen(format!("the stop condition `{}`: {message}", when.function))
            })?;
        match &resolved.result {
            Some(InputType {
                sort: SortRef::Builtin(BuiltinSort::Bool),
                ..
            }) => Ok(resolved),
            _ => Err(ExecError::StopWhen(format!(
                "the stop condition `{}`: `{}` does not return Bool; a stop condition holds or does not at a state",
                when.function, resolved.decl
            ))),
        }
    }

    /// Resolve `function`, a function of the leaf cells `cells` read in parameter order, in
    /// `observer` for states of this definition, whatever its result sort; the refusal's text
    /// otherwise, naming the use as `role` does: a function the observer does not hold,
    /// evaluated in an instance, parametric, or whose parameters are not one per cell, each of a
    /// sort that admits its cell's sort; a cell that is unknown, unobservable, a group cell, or
    /// below a repeated or optional holder.
    pub(crate) fn cell_function(
        &self,
        observer: &Self,
        function: &str,
        cells: &[String],
        role: Use,
    ) -> Result<ResolvedCondition, String> {
        let decl = observer
            .values
            .function_decl(function)
            .map_err(|error| error.to_string())?;
        let Some(info) = observer.values.info(&decl) else {
            return Err(format!("`{decl}` has no production"));
        };
        if !observer.values.is_loaded(&decl) {
            return Err(format!(
                "`{decl}` is declared by a package whose module the observer's main module does not import, so the observer does not hold it"
            ));
        }
        if let Some(reason) = observer.values.instance_function(&decl, role.what) {
            return Err(reason);
        }
        if info.parameters != 0 {
            return Err(format!(
                "`{decl}` is a parametric function; {} is a function of the cells it reads",
                role.what
            ));
        }
        if info.fields.len() != cells.len() {
            return Err(format!(
                "`{decl}` takes {} parameter{}, but the {} reads {} cell{}: one parameter per cell, in order",
                info.fields.len(),
                if info.fields.len() == 1 { "" } else { "s" },
                role.noun.trim_start_matches("a ").trim_start_matches("an "),
                cells.len(),
                if cells.len() == 1 { "" } else { "s" },
            ));
        }
        let read = info
            .fields
            .iter()
            .zip(&info.field_types)
            .zip(cells)
            .map(|((parameter, parameter_type), path)| {
                self.condition_cell(
                    observer,
                    &decl,
                    parameter,
                    parameter_type.as_ref(),
                    path,
                    role,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(ResolvedCondition {
            function: function.to_owned(),
            result: info.result.clone(),
            decl,
            cells: read,
            subject: Arc::clone(&self.values),
            observer: Arc::clone(&observer.values),
        })
    }

    /// The leaf cell `path` resolved for a read by `role` (no function): its symbols and its
    /// declared type, or the refusal's text as [`Self::cell_function`] words it.
    pub(crate) fn read_leaf_cell(
        &self,
        path: &str,
        role: Use,
    ) -> Result<(ReadCell, InputType), String> {
        let (symbols, node) = self.leaf_cell_node(path, role)?;
        let Some((sort, arguments)) = &node.content else {
            unreachable!("a leaf cell node has a content sort");
        };
        let declared = crate::inputs::input_type(&self.values, sort, arguments)
            .unwrap_or_else(InputType::untyped);
        Ok((
            ReadCell {
                path: path.to_owned(),
                symbols,
                parameter: Arc::from(""),
            },
            declared,
        ))
    }

    /// The symbols down to the leaf cell `path` and its node, refused as
    /// [`Self::cell_function`] refuses a cell.
    fn leaf_cell_node(
        &self,
        path: &str,
        role: Use,
    ) -> Result<(Vec<String>, &crate::values::CellNode), String> {
        let cell = |message: String| format!("the cell `{path}` {message}");
        let positions = self.resolve_cell(path).map_err(|error| error.to_string())?;
        let mut nodes = self.values.cells();
        let mut symbols = vec![self.values.top_symbol().to_owned()];
        let mut node = None;
        for position in positions {
            let found = &nodes[position];
            if let Some(multiplicity) = found.multiplicity {
                let holder = match multiplicity {
                    CellMultiplicity::Star => "repeated",
                    CellMultiplicity::Optional => "optional",
                };
                return Err(cell(format!(
                    "is or is below the {holder} cell `{}`: applied in each instance {} would give several answers, not one",
                    found.field, role.noun
                )));
            }
            symbols.push(found.symbol.clone());
            nodes = &found.children;
            node = Some(found);
        }
        let Some(node) = node else {
            return Err(cell("names no cell".to_owned()));
        };
        if node.content.is_none() {
            return Err(cell(format!(
                "is a group cell; {} reads leaf cells",
                role.noun
            )));
        }
        Ok((symbols, node))
    }

    /// The cell `path` a condition's parameter `parameter` (of type `parameter_type`) of
    /// `decl` reads, resolved in this definition, its sort judged in `observer`; the refusal's
    /// text otherwise ([`Self::cell_function`]).
    fn condition_cell(
        &self,
        observer: &Self,
        decl: &Decl,
        parameter: &Arc<str>,
        parameter_type: Option<&InputType>,
        path: &str,
        role: Use,
    ) -> Result<ReadCell, String> {
        let cell = |message: String| format!("the cell `{path}` {message}");
        let (symbols, node) = self.leaf_cell_node(path, role)?;
        let Some((sort, _)) = &node.content else {
            unreachable!("a leaf cell node has a content sort");
        };
        let Some(cell_sort) = self.values.sort_ref(sort) else {
            return Err(cell("has a sort with no KRS declaration".to_owned()));
        };
        let Some(InputType {
            sort: parameter_sort,
            ..
        }) = parameter_type
        else {
            return Err(format!(
                "the parameter `{parameter}` of `{decl}` has a sort with no KRS declaration"
            ));
        };
        match observer.values.is_subsort(&cell_sort, parameter_sort) {
            Some(true) => Ok(ReadCell {
                path: path.to_owned(),
                symbols,
                parameter: parameter.clone(),
            }),
            Some(false) => Err(format!(
                "the parameter `{parameter}` of `{decl}` is of sort {}, which does not admit the sort {} of the cell `{path}`",
                ValueIndex::sort_name(parameter_sort),
                ValueIndex::sort_name(&cell_sort)
            )),
            None => Err(format!(
                "the observer does not declare the sort {} of the cell `{path}`",
                ValueIndex::sort_name(&cell_sort)
            )),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every stop of an evaluation leaves its arrival undecided, but only a spent budget of polls
    /// is one a larger budget can decide: a stop of the backend other than the budget, or the
    /// solver's `Unknown`, is not (`undecided.budget_spent`).
    #[test]
    fn only_a_spent_budget_is_decided_by_a_larger_budget() {
        let spent = ObservationError::Evaluation(EvaluationError::Spent(5));
        let stopped = ObservationError::Evaluation(EvaluationError::Stopped("a stop".to_owned()));
        let unknown = ObservationError::Evaluation(EvaluationError::Undecided(1));
        for error in [&spent, &stopped, &unknown] {
            assert!(error.is_undecided(), "{error}");
        }
        assert!(spent.spent_budget());
        assert!(!stopped.spent_budget());
        assert!(!unknown.spent_budget());
    }
}
