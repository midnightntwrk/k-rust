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
//! # Evaluating an observation at an arrival
//!
//! [`ArrivalObservation`] evaluates a function of named cells at an arrival and returns its value
//! whatever its sort; the stop condition is the use that reads a `Bool` from it.

use std::fmt;
use std::sync::Arc;

use k_rust::backend::{StopArrival, StopCondition, StopDecision, StopSide};
use krs_ir::{BuiltinSort, CellMultiplicity};

use crate::inputs::InputType;
use crate::values::{Decl, SortRef, Value, ValueIndex};
use crate::views::EvaluationError;
use crate::{ExecError, Semantics, StopWhen};

/// One cell a condition reads: its path as written, and the cell symbols from the
/// configuration's top down to it, which the backend follows to convert that cell alone.
#[derive(Clone, Debug)]
struct ReadCell {
    path: String,
    symbols: Vec<String>,
    parameter: Arc<str>,
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
}

impl ResolvedCondition {
    /// The function as the condition named it.
    #[must_use]
    pub fn function(&self) -> &str {
        &self.function
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
    /// [`EvaluationError::Undecided`]).
    #[must_use]
    pub const fn is_undecided(&self) -> bool {
        matches!(
            self,
            Self::Evaluation(EvaluationError::Stopped(_) | EvaluationError::Undecided(_))
        )
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
    pub fn observe(&mut self, arrival: &StopArrival<'_>) -> Result<Value, ObservationError> {
        let mut arguments = Vec::with_capacity(self.condition.cells.len());
        for cell in &self.condition.cells {
            let refuse = |reason: String| ObservationError::Cell {
                cell: cell.path.clone(),
                reason,
            };
            let symbols = cell.symbols.iter().map(String::as_str).collect::<Vec<_>>();
            let pattern = arrival
                .cell(&symbols)
                .ok_or_else(|| refuse("is not held by the state".to_owned()))?;
            let content = match &pattern {
                k_rust::kore::ast::Pattern::Application { arguments, .. } => {
                    match arguments.as_slice() {
                        [content] => content,
                        _ => return Err(refuse("is not a leaf cell of the state".to_owned())),
                    }
                }
                _ => return Err(refuse("is not a leaf cell of the state".to_owned())),
            };
            let value = self
                .condition
                .subject
                .decode(content)
                .map_err(|error| refuse(format!("holds no term of the definition: {error}")))?;
            if let Some(part) = crate::views::opaque_part(&self.condition.subject, &value) {
                return Err(refuse(format!(
                    "holds {part}, which has no KRS description to carry to the condition"
                )));
            }
            arguments.push((cell.parameter.clone(), value));
        }
        self.observer
            .evaluate_within(
                self.condition.decl.path(),
                arguments
                    .iter()
                    .map(|(parameter, value)| (&**parameter, value.clone()))
                    .collect(),
                self.budget,
            )
            .map_err(ObservationError::Evaluation)
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
}

/// The backend's stop condition of a run ([`StopCondition`]): the observation's `Bool`, an
/// undecided observation undecided, any other observation without a value refused.
pub(crate) struct ConditionOracle<'o> {
    observation: ArrivalObservation<'o>,
    /// The refusal that failed the request, once one did.
    pub(crate) refusal: Option<Refusal>,
    /// The last arrival the condition was left undecided at: a path of the request ends there.
    pub(crate) undecided: Option<UndecidedArrival>,
}

impl<'o> ConditionOracle<'o> {
    pub(crate) const fn new(observation: ArrivalObservation<'o>) -> Self {
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
        let refuse = |message: String| {
            ExecError::StopWhen(format!("the stop condition `{}`: {message}", when.function))
        };
        let decl = observer
            .values
            .function_decl(&when.function)
            .map_err(|error| refuse(error.to_string()))?;
        let Some(info) = observer.values.info(&decl) else {
            return Err(refuse(format!("`{decl}` has no production")));
        };
        if !observer.values.is_loaded(&decl) {
            return Err(refuse(format!(
                "`{decl}` is declared by a package whose module the observer's main module does not import, so the observer does not hold it"
            )));
        }
        if let Some(reason) = observer.values.instance_function(&decl, "a stop condition") {
            return Err(refuse(reason));
        }
        if info.parameters != 0 {
            return Err(refuse(format!(
                "`{decl}` is a parametric function; a stop condition is a function of the cells it reads"
            )));
        }
        if info.fields.len() != when.cells.len() {
            return Err(refuse(format!(
                "`{decl}` takes {} parameter{}, but the condition reads {} cell{}: one parameter per cell, in order",
                info.fields.len(),
                if info.fields.len() == 1 { "" } else { "s" },
                when.cells.len(),
                if when.cells.len() == 1 { "" } else { "s" },
            )));
        }
        match &info.result {
            Some(InputType {
                sort: SortRef::Builtin(BuiltinSort::Bool),
                ..
            }) => {}
            _ => {
                return Err(refuse(format!(
                    "`{decl}` does not return Bool; a stop condition holds or does not at a state"
                )));
            }
        }
        let cells = info
            .fields
            .iter()
            .zip(&info.field_types)
            .zip(&when.cells)
            .map(|((parameter, parameter_type), path)| {
                self.condition_cell(observer, &decl, parameter, parameter_type.as_ref(), path)
                    .map_err(refuse)
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(ResolvedCondition {
            function: when.function.clone(),
            decl,
            cells,
            subject: Arc::clone(&self.values),
            observer: Arc::clone(&observer.values),
        })
    }
}

impl Semantics {
    /// The cell `path` a condition's parameter `parameter` (of type `parameter_type`) of
    /// `decl` reads, resolved in this definition, its sort judged in `observer`; the refusal's
    /// text otherwise ([`Self::stop_condition`]).
    fn condition_cell(
        &self,
        observer: &Self,
        decl: &Decl,
        parameter: &Arc<str>,
        parameter_type: Option<&InputType>,
        path: &str,
    ) -> Result<ReadCell, String> {
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
                    "is or is below the {holder} cell `{}`: applied in each instance a condition would give several answers, not one",
                    found.field
                )));
            }
            symbols.push(found.symbol.clone());
            nodes = &found.children;
            node = Some(found);
        }
        let Some(node) = node else {
            return Err(cell("names no cell".to_owned()));
        };
        let Some((sort, _)) = &node.content else {
            return Err(cell(
                "is a group cell; a condition reads leaf cells".to_owned(),
            ));
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
