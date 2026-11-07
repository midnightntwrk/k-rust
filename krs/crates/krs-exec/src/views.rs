//! Views: a function a comparison applies to a cell's value on both sides before it compares
//! them, so that ends are compared on what a use observes of the cell (a tier of an event log,
//! a store with its default entries dropped) rather than on the whole value.
//!
//! # What a view is
//!
//! A comparison decides whether two ends are the same by computing an *observation* of each end
//! and comparing the observations: the default observation is the value of every compared cell
//! ([`crate::ends`], "Compared cells"). A view replaces one cell's component of that observation
//! by a function of the cell's value. Both sides are viewed by the same function of the same
//! definition, so a difference of viewed values is a difference of the ends: a view weakens the
//! comparison, never makes it report two equal ends as different.
//!
//! A view is a function with exactly one parameter, whose sort is at least the cell's declared
//! sort; it is applied to a leaf cell's value, in every instance of a repeated cell and in a
//! present optional cell, and an absent optional cell stays absent. Fixed arguments and
//! composition are written as a wrapper function (`fn WritesView(log) = TierLog(Writes,
//! Lift(log))`). A view is named per cell by the comparison that uses it, by the function's path
//! or a `::`-aligned suffix of it ([`crate::ValueIndex::function_decl`]); no attribute marks it.
//!
//! # The observer
//!
//! A view is resolved and evaluated in an *observer*: a compiled definition that declares the
//! function, by default the compared definition itself. It may be another definition, compiled
//! from a package that depends on the compared definition's package and that no semantics
//! imports, so that editing a view changes neither the compared definition, nor its rules, nor
//! anything keyed by it. Like every composed definition, the observer is its package's own
//! dependency closure: the compared definition, and whatever else the package depends on (a
//! package of observations no semantics depends on), held by its definition because the package
//! depends on them, whether or not its source names anything of them. A function the observer's
//! Definition IR declares but its loaded definition does not hold (a module the main module does
//! not import) is no view. A cell's
//! value is carried to the observer by its constructors' KRS declarations ([`crate::Decl`]): a
//! constructor is free, so a value made of constructors and builtin values denotes the same
//! term in every definition that declares those constructors with the same fields, which the
//! observer's encoder checks. A value with a part that has no KRS description (a variable, an
//! unevaluated application, a freezer) is the compared definition's KORE, which no other
//! definition need read alike, and has no view.
//!
//! # Evaluation
//!
//! [`crate::Semantics::evaluate`] computes a function's value at arguments as a consequence of
//! the definition alone: a value the definition leaves to the implementation (an
//! implementation-chosen hook value, such as the order of `keys_list` of two or more keys) stays
//! unevaluated, as does a partial function outside its domain, and either is no value. A view
//! without a value at an end refuses the comparison, naming the view, the side and the cell:
//! an observation that does not exist makes the ends neither equal nor different.
//!
//! The simplification that evaluates a view is not bounded by the definition: a function whose
//! equations do not reach a value never ends. A caller may bound each evaluation by a budget of
//! polls ([`CellViews::evaluate_within`]): the points at which the simplification polls for a
//! stop, so that where the budget stops it is a function of the evaluation, not of the host's
//! speed or load. An evaluation that stops before it ends, for that budget or for another stop
//! of the backend (the simplifier's stack, the solver's prelude), has no value yet rather than
//! none at all: the definition was not shown to give it none. So has an evaluation that ends
//! short of a value after the solver answered `Unknown` to a query it asked (a bound of the
//! solver ran out, or the query is beyond what it decides): a condition so answered was left
//! undecided by the solver run, not by the definition, and another run of the solver may decide
//! it. A condition left undecided on decided answers alone (one the definition does not
//! determine) and a condition decided false are facts about the definition, and the result
//! short of a value they leave is no value. Both of the first kind are reported as an error of
//! their own ([`EndError::ViewStopped`]), which a front end reports as inconclusive: never as
//! equal, and never as a refusal of the view. Neither can change a value that is computed: an
//! equation applies only where its condition is decided true, so an evaluation that reaches a
//! value gives the definition's value whatever stopped work it dismissed and whatever answers
//! were `Unknown` on the way, and a verdict under a budget is the verdict without one, or
//! inconclusive. The budget counts the evaluation's own polls, which reuse of answers the
//! observer's solver decided earlier can only lower; the solver's bounds and the process's
//! stack budget, which threads share, are outside it.
//!
//! A view with no value at one viewed value refuses the comparison even where the evaluation at
//! another value stopped: the refusal holds whatever the budget, and no more work at the other
//! value makes the missing observation exist. So the error a comparison reports is a refusal when
//! any viewed value has no value, and a stop only when every value has one or stopped. Which of the
//! two it is depends on each value's own result, never on the order the sides or a repeated cell's
//! instances are given in, which only chooses the value the error names; the exception is a value
//! whose evaluation ends, within the budget or without an `Unknown` answer, only because it reuses
//! an answer the observer's solver decided for a value evaluated before it. To find whether any
//! value has no value, a comparison whose evaluations stop evaluates every distinct viewed value,
//! so its cost grows with their number, up to one budget for each. A value with a part that has no
//! KRS description refuses without an evaluation, and since it decides that the comparison is
//! refused, no value is evaluated when one does.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;

use k_rust::backend::StepTimeoutMode;
use k_rust::k_rust_backend::definition::Admission;
use k_rust::k_rust_backend::stop::{with_operation_record, with_poll_budget};

use crate::Semantics;
use crate::ends::{EndCell, EndCells, EndError, Side};
use crate::inputs::InputType;
use crate::report::Halt;
use crate::values::{CellNode, Decl, SortRef, Value, ValueError, ValueIndex};

/// Why [`Semantics::evaluate`] has no value.
#[derive(Debug)]
pub enum EvaluationError {
    /// The function or its arguments are no application of a function of the definition.
    Application(ValueError),
    /// The definition's backend refused the term, or its result is no term of the definition.
    Backend(String),
    /// The definition gives the application no value: the result still holds this part.
    NoValue(String),
    /// The evaluation stopped before it ended, for a stop of the backend other than the caller's
    /// budget ([`Semantics::evaluate_within`]), which this says: whether it has a value is not
    /// known.
    Stopped(String),
    /// The evaluation spent the caller's budget of this many polls before it ended
    /// ([`Semantics::evaluate_within`]): whether it has a value is not known, and a larger budget
    /// can decide it.
    Spent(u64),
    /// The evaluation ended short of a value after the solver answered `Unknown` this many
    /// times to the queries it asked: a condition so answered is undecided by the solver run,
    /// not by the definition, so whether it has a value is not known.
    Undecided(usize),
}

impl fmt::Display for EvaluationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Application(error) => error.fmt(formatter),
            Self::Backend(message) => formatter.write_str(message),
            Self::NoValue(part) => write!(
                formatter,
                "the definition gives it no value: its result holds {part}"
            ),
            Self::Stopped(stop) => write!(
                formatter,
                "its evaluation stopped before it ended ({stop}), so whether it has a value is not known"
            ),
            Self::Spent(budget) => write!(
                formatter,
                "its evaluation stopped before it ended (it spent its budget of {budget} poll{}), so whether it has a value is not known",
                if *budget == 1 { "" } else { "s" }
            ),
            Self::Undecided(answers) => write!(
                formatter,
                "the solver answered `Unknown` to {answers} quer{} of its evaluation, which ended short of a value, so whether it has a value is not known",
                if *answers == 1 { "y" } else { "ies" }
            ),
        }
    }
}

impl std::error::Error for EvaluationError {}

impl From<ValueError> for EvaluationError {
    fn from(error: ValueError) -> Self {
        Self::Application(error)
    }
}

/// One resolved view.
#[derive(Clone, Debug)]
struct CellView {
    /// The cell's declared path.
    cell: String,
    /// The function as the comparison named it.
    function: String,
    /// The observer's function.
    decl: Decl,
    /// Its parameter's name.
    parameter: Arc<str>,
    /// The type a viewed value is written at: the function's declared result type, element types
    /// included (`Map<Reg8, Int>`, whose keys are then written `"B"`).
    result: InputType,
}

/// The views a comparison applies, resolved in their observer ([`Semantics::cell_views`]) and
/// evaluated at the ends compared ([`Self::evaluate`]).
#[derive(Clone, Default)]
pub struct CellViews {
    /// The views by the K symbol of the viewed cell, which names the cell alone.
    by_symbol: BTreeMap<String, CellView>,
    /// The observer's value index, which writes viewed values; `None` with no view.
    observer: Option<Arc<ValueIndex>>,
    /// The observer's printer, which prints a viewed value as K text where it has no document
    /// (its sort may be the observer's alone); `None` with no view.
    printer: Option<Arc<krs_unparse::Unparser>>,
    /// The compared definition's value index, whose cell tree the ends are read by; `None` with
    /// no view.
    subject: Option<Arc<ValueIndex>>,
    /// The values the views took, by cell symbol and argument.
    results: BTreeMap<String, BTreeMap<Value, Value>>,
}

impl fmt::Debug for CellViews {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.debug_map().entries(self.named()).finish()
    }
}

impl CellViews {
    /// Whether no view is applied.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.by_symbol.is_empty()
    }

    /// The views as the comparison named them: the function by declared cell path.
    #[must_use]
    pub fn named(&self) -> BTreeMap<String, String> {
        self.by_symbol
            .values()
            .map(|view| (view.cell.clone(), view.function.clone()))
            .collect()
    }

    /// The value index of the definition the views were resolved for.
    pub(crate) const fn subject(&self) -> Option<&Arc<ValueIndex>> {
        self.subject.as_ref()
    }

    /// The observer's index and the view's result type, for the cell `node` when it is viewed.
    /// The printer of the values `index` writes: the observer's for its value index, which
    /// writes viewed values, and `None` for another index.
    pub(crate) fn printer(&self, index: &ValueIndex) -> Option<&krs_unparse::Unparser> {
        self.observer
            .as_deref()
            .filter(|observer| std::ptr::eq(*observer, index))
            .and(self.printer.as_deref())
    }

    /// The observer's printer; `None` with no view.
    pub(crate) fn observer_printer(&self) -> Option<&krs_unparse::Unparser> {
        self.printer.as_deref()
    }

    /// Whether the cell `node`, or a cell below it, is viewed.
    pub(crate) fn holds_view(&self, node: &CellNode) -> bool {
        self.by_symbol.contains_key(&node.symbol)
            || node.children.iter().any(|child| self.holds_view(child))
    }

    pub(crate) fn lens(&self, node: &CellNode) -> Option<(&ValueIndex, &InputType)> {
        let view = self.by_symbol.get(&node.symbol)?;
        Some((self.observer.as_deref()?, &view.result))
    }

    /// The viewed value of `value` in the cell `node`: `value` itself when the cell is not
    /// viewed.
    ///
    /// # Errors
    ///
    /// Returns [`EndError::View`] when the view was not evaluated at `value`: the ends compared
    /// were not the ones [`Self::evaluate`] was given.
    pub(crate) fn apply(&self, node: &CellNode, value: &Value) -> Result<Value, EndError> {
        let Some(view) = self.by_symbol.get(&node.symbol) else {
            return Ok(value.clone());
        };
        self.results
            .get(&node.symbol)
            .and_then(|results| results.get(value))
            .cloned()
            .ok_or_else(|| EndError::View {
                cell: view.cell.clone(),
                function: view.function.clone(),
                message: "it was not evaluated at this end: evaluate the views at the ends compared first".to_owned(),
            })
    }

    /// Evaluate every view at every value its cell holds in the ends of `sides`, in `observer`,
    /// the definition the views were resolved in; each distinct value once. `subject` is the
    /// compared definition, which reads the ends and names a value's place in them, when it is
    /// not `observer` itself: `None` where the views were resolved in the compared definition.
    ///
    /// # Errors
    ///
    /// Returns [`EndError::View`] for a view without a value at an end (naming the side and the
    /// cell, an instance of a collection as a difference names it: a `List` collection's by its
    /// index, a `Map` collection's by its key, a `Set` collection's by its canonical text), and
    /// [`EndError::State`] for an `observer` other than the one the views were resolved in, or a
    /// compared definition (`subject`, or else `observer`) other than the one they were resolved
    /// for.
    pub fn evaluate(
        &mut self,
        observer: &mut Semantics,
        subject: Option<&Semantics>,
        sides: &[Side<'_>],
    ) -> Result<(), EndError> {
        self.evaluate_within(observer, subject, sides, None)
    }

    /// [`Self::evaluate`], each evaluation bounded by a budget of `budget` polls when there is
    /// one ([module documentation](crate::views#evaluation)).
    ///
    /// # Errors
    ///
    /// Fails as [`Self::evaluate`] does, and returns [`EndError::ViewStopped`] for an evaluation
    /// that stopped before it ended (it spent `budget`, or another stop of the backend ended it)
    /// or that ended short of a value after the solver answered `Unknown`, when no value refuses.
    /// The error names, in the order of `sides` and then of the cells and instances of each end,
    /// the first value with a part that has no KRS description, or else the first value that
    /// refuses, or, when none does, the first that stopped, each at its place in its end, an
    /// instance named as [`Self::evaluate`] names it. The order the sides are given in
    /// chooses which value is named, and not the kind of error, except where an evaluation ends
    /// only by reusing an answer an earlier one decided ([module documentation](crate::views)).
    pub fn evaluate_within(
        &mut self,
        observer: &mut Semantics,
        subject: Option<&Semantics>,
        sides: &[Side<'_>],
        budget: Option<u64>,
    ) -> Result<(), EndError> {
        let (Some(index), Some(compared)) = (&self.observer, &self.subject) else {
            return Ok(());
        };
        if !Arc::ptr_eq(index, observer.values()) {
            return Err(EndError::State(
                "the views are evaluated in a definition other than the observer they were resolved in".to_owned(),
            ));
        }
        let namer: &Semantics = subject.unwrap_or(&*observer);
        if !Arc::ptr_eq(compared, namer.values()) {
            return Err(EndError::State(
                "the views are evaluated at the ends of a definition other than the one they were resolved for".to_owned(),
            ));
        }
        let subject = Arc::clone(compared);
        let mut pending = Vec::new();
        for side in sides {
            for end in &side.ends.ends {
                if end.class.halt != Halt::Undefined {
                    self.collect(
                        namer,
                        subject.cells(),
                        &end.cells,
                        side.name,
                        "",
                        &mut pending,
                    );
                }
            }
        }
        // Each value once, in side then instance order: the order the first refusal and the
        // first stop are named in.
        let mut seen = BTreeSet::new();
        pending.retain(|(symbol, value, _, _)| {
            !self
                .results
                .get(symbol)
                .is_some_and(|results| results.contains_key(value))
                && seen.insert((symbol.clone(), value.clone()))
        });
        // A refusal is a fact about the definition and the value, whatever the budget; a stop
        // is not. So the comparison is refused when any value refuses, and stopped only when
        // none does. A value with no KRS description refuses without an evaluation, which
        // settles the comparison: no evaluation can change that it is refused.
        for (symbol, value, side, path) in &pending {
            if let Some(part) = opaque_part(&subject, value) {
                let view = &self.by_symbol[symbol];
                return Err(EndError::View {
                    cell: view.cell.clone(),
                    function: view.function.clone(),
                    message: format!(
                        "it has no value at the {side} end's `{path}`: the cell holds {part}, which has no KRS description to carry to the view"
                    ),
                });
            }
        }
        let mut stopped = None;
        for (symbol, value, side, path) in pending {
            let view = &self.by_symbol[&symbol];
            let refuse = |message: String| EndError::View {
                cell: view.cell.clone(),
                function: view.function.clone(),
                message: format!("it has no value at the {side} end's `{path}`: {message}"),
            };
            match observer.evaluate_within(
                view.decl.path(),
                vec![(&*view.parameter, value.clone())],
                budget,
            ) {
                Ok(viewed) => {
                    self.results
                        .entry(symbol)
                        .or_default()
                        .insert(value, viewed);
                }
                Err(
                    error @ (EvaluationError::Stopped(_)
                    | EvaluationError::Spent(_)
                    | EvaluationError::Undecided(_)),
                ) => {
                    stopped.get_or_insert_with(|| EndError::ViewStopped {
                        cell: view.cell.clone(),
                        function: view.function.clone(),
                        message: format!("at the {side} end's `{path}`, {error}"),
                    });
                }
                Err(error) => return Err(refuse(error.to_string())),
            }
        }
        stopped.map_or(Ok(()), Err)
    }

    /// Every viewed leaf value below `cells`, with its side and its path, an instance named as
    /// `namer`, the compared definition, names it in a difference.
    fn collect(
        &self,
        namer: &Semantics,
        nodes: &[CellNode],
        cells: &EndCells,
        side: &str,
        prefix: &str,
        output: &mut Vec<(String, Value, String, String)>,
    ) {
        for node in nodes {
            let Some(cell) = cells.get(&node.field) else {
                continue;
            };
            let path = format!("{prefix}{}", node.field);
            match cell {
                EndCell::Repeated(instances) => {
                    for (position, instance) in instances.iter().enumerate() {
                        self.collect_content(
                            namer,
                            node,
                            instance,
                            side,
                            &namer.instance_path(node, &path, position, instance),
                            output,
                        );
                    }
                }
                EndCell::Optional(Some(content)) => {
                    self.collect_content(namer, node, content, side, &path, output);
                }
                EndCell::Optional(None) => {}
                content => self.collect_content(namer, node, content, side, &path, output),
            }
        }
    }

    fn collect_content(
        &self,
        namer: &Semantics,
        node: &CellNode,
        content: &EndCell,
        side: &str,
        path: &str,
        output: &mut Vec<(String, Value, String, String)>,
    ) {
        match content {
            EndCell::Leaf(value) if self.by_symbol.contains_key(&node.symbol) => output.push((
                node.symbol.clone(),
                value.clone(),
                side.to_owned(),
                path.to_owned(),
            )),
            EndCell::Group(cells) => {
                self.collect(
                    namer,
                    &node.children,
                    cells,
                    side,
                    &format!("{path}."),
                    output,
                );
            }
            _ => {}
        }
    }
}

/// The first part of `value` with no KRS description, described.
pub(crate) fn opaque_part(index: &ValueIndex, value: &Value) -> Option<String> {
    match value {
        Value::Opaque(pattern) => Some(index.opaque_part(pattern)),
        Value::Ctor(ctor) => ctor
            .fields()
            .iter()
            .find_map(|(_, field)| opaque_part(index, field)),
        Value::Seq(items) | Value::List(items) => {
            items.iter().find_map(|item| opaque_part(index, item))
        }
        Value::Set(items) => items.iter().find_map(|item| opaque_part(index, item)),
        Value::Map(entries) => entries
            .iter()
            .find_map(|(key, item)| opaque_part(index, key).or_else(|| opaque_part(index, item))),
        Value::Int(_)
        | Value::Bool(_)
        | Value::String(_)
        | Value::Bytes(_)
        | Value::Float(_)
        | Value::Token { .. } => None,
    }
}

impl Semantics {
    /// The value of the function named `function` (as [`ValueIndex::function_decl`] resolves
    /// it) at `arguments`, its parameters given by name: the application simplified in this
    /// definition as a consequence of the definition alone, so that a value the definition leaves
    /// to the implementation stays unevaluated ([module documentation](crate::views#evaluation)).
    ///
    /// # Errors
    ///
    /// Returns [`EvaluationError::Application`] for a name that resolves to no function or
    /// arguments that do not fit it, [`EvaluationError::Backend`] for a term the backend
    /// refuses or a result that is no term of the definition, [`EvaluationError::NoValue`] when
    /// the result holds a part with no KRS description (an unevaluated application, `\bottom`,
    /// a disjunction) and no stop or `Unknown` solver answer explains it,
    /// [`EvaluationError::Stopped`] for a simplification that a stop of the backend ended before
    /// it reached a value (with no budget of the caller's, never [`EvaluationError::Spent`]), and
    /// [`EvaluationError::Undecided`] for one that ended short of a value after the solver
    /// answered `Unknown`.
    pub fn evaluate(
        &mut self,
        function: &str,
        arguments: Vec<(&str, Value)>,
    ) -> Result<Value, EvaluationError> {
        self.evaluate_within(function, arguments, None)
    }

    /// [`Self::evaluate`], the simplification bounded by a budget of `budget` polls, when there
    /// is one ([module documentation](crate::views#evaluation)).
    ///
    /// # Errors
    ///
    /// Fails as [`Self::evaluate`] does, and returns [`EvaluationError::Spent`] for a
    /// simplification that spent `budget` before it reached a value, which a larger budget can
    /// decide, and [`EvaluationError::Stopped`] for one that a stop of the backend other than
    /// `budget` ended first.
    /// The simplification is one operation of the backend: what it met
    /// (`stop::with_operation_record`) is read, whatever record or budget encloses the call.
    pub fn evaluate_within(
        &mut self,
        function: &str,
        arguments: Vec<(&str, Value)>,
        budget: Option<u64>,
    ) -> Result<Value, EvaluationError> {
        let application = self.values.call(function, arguments)?;
        let kast = self.values.to_kast(&application)?;
        let pattern = self.configuration.typed_kore(&kast).map_err(|error| {
            EvaluationError::Backend(format!(
                "the application is no term of the definition: {error}"
            ))
        })?;
        let backend = &mut self.backend;
        // With no budget the scope still records a stack stop a site dismissed on the way; the
        // operation's record counts the solver's `Unknown` answers it received.
        let ((simplified, record), operation) = with_operation_record(|| {
            with_poll_budget(
                budget.unwrap_or(u64::MAX),
                StepTimeoutMode::Manual(std::time::Duration::ZERO),
                || backend.simplify_kore(None, &pattern, Admission::Unverified),
            )
        });
        let spent = || match budget {
            Some(budget) if record.budget_exhausted => Some(EvaluationError::Spent(budget)),
            _ if record.stack_exhausted => Some(EvaluationError::Stopped(
                "it ran out of the simplifier's native stack".to_owned(),
            )),
            _ => None,
        };
        let simplified = simplified.map_err(|error| match (spent(), error.stop_cause()) {
            (Some(stop), _) => stop,
            (None, Some(_)) => EvaluationError::Stopped(error.to_string()),
            (None, None) => EvaluationError::Backend(error.to_string()),
        })?;
        let value = self.values.decode(&simplified).map_err(|error| {
            EvaluationError::Backend(format!(
                "the simplified application is no term of the definition: {error}"
            ))
        })?;
        // A value reached is the definition's value, whatever stopped work was dismissed and
        // whatever answers were `Unknown` on the way; a result short of one is no value only where
        // nothing stopped and every answer of the solver was decided.
        match (opaque_part(&self.values, &value), spent()) {
            (None, _) => Ok(value),
            (Some(_), Some(stop)) => Err(stop),
            (Some(_), None) if operation.unknown_answers > 0 => {
                Err(EvaluationError::Undecided(operation.unknown_answers))
            }
            (Some(part), None) => Err(EvaluationError::NoValue(part)),
        }
    }

    /// Resolve the views `named` (a function by declared cell path) in `observer`, the
    /// definition that declares them: this definition itself, or another one
    /// ([module documentation](crate::views#the-observer)).
    ///
    /// # Errors
    ///
    /// Returns [`EndError::UnknownCell`] and [`EndError::Unobservable`] for a path that names no
    /// observable cell, and [`EndError::View`] for a group cell, a cell of a sort the observer
    /// does not declare, a name that resolves to no function of the observer, a function
    /// evaluated in one instance of a Map collection, which a view, evaluated in no instance,
    /// cannot apply ([`ValueIndex::instance_function`]), and a function that does not take
    /// exactly one parameter of a sort at least the cell's.
    pub fn cell_views(
        &self,
        observer: &Self,
        named: &BTreeMap<String, String>,
    ) -> Result<CellViews, EndError> {
        let mut views = CellViews::default();
        for (cell, function) in named {
            let refuse = |message: String| EndError::View {
                cell: cell.clone(),
                function: function.clone(),
                message,
            };
            let mut nodes = self.values.cells();
            let mut node = None;
            for position in self.resolve_cell(cell)? {
                let found = &nodes[position];
                nodes = &found.children;
                node = Some(found);
            }
            let Some(node) = node else {
                return Err(refuse("the path names no cell".to_owned()));
            };
            let Some((sort, _)) = &node.content else {
                return Err(refuse(
                    "the cell is a group cell; a view applies to a leaf cell's value".to_owned(),
                ));
            };
            let Some(cell_sort) = self.values.sort_ref(sort) else {
                return Err(refuse("the cell's sort has no KRS declaration".to_owned()));
            };
            let decl = observer
                .values
                .function_decl(function)
                .map_err(|error| refuse(error.to_string()))?;
            let Some(info) = observer.values.info(&decl) else {
                return Err(refuse(format!("`{decl}` has no production")));
            };
            if !observer.values.is_loaded(&decl) {
                return Err(refuse(format!(
                    "`{decl}` is declared by a package whose module the definition's main module does not import, so the definition does not hold it"
                )));
            }
            // Checked before the parameters: the instance's key is a hidden argument, no
            // parameter a view could be given.
            if let Some(reason) = observer.values.instance_function(&decl, "a view") {
                return Err(refuse(reason));
            }
            if info.parameters != 0 {
                return Err(refuse(format!(
                    "`{decl}` is a parametric function; a view is a function of one sort"
                )));
            }
            let [parameter] = info.fields.as_slice() else {
                return Err(refuse(format!(
                    "`{decl}` takes {} parameters; a view takes exactly one, the cell's value (a wrapper function fixes the others)",
                    info.fields.len()
                )));
            };
            let Some(Some(InputType {
                sort: parameter_sort,
                ..
            })) = info.field_types.first()
            else {
                return Err(refuse(format!(
                    "the parameter `{parameter}` of `{decl}` has a sort with no KRS declaration"
                )));
            };
            match observer.values.is_subsort(&cell_sort, parameter_sort) {
                Some(true) => {}
                Some(false) => {
                    return Err(refuse(format!(
                        "the parameter `{parameter}` of `{decl}` is of sort {}, which does not admit the cell's sort {}",
                        ValueIndex::sort_name(parameter_sort),
                        ValueIndex::sort_name(&cell_sort)
                    )));
                }
                None => {
                    return Err(refuse(format!(
                        "the definition `{decl}` is in does not declare the cell's sort {}",
                        cell_sort_name(&cell_sort)
                    )));
                }
            }
            views.by_symbol.insert(
                node.symbol.clone(),
                CellView {
                    cell: cell.clone(),
                    function: function.clone(),
                    decl: decl.clone(),
                    parameter: parameter.clone(),
                    result: info.result.clone().unwrap_or_else(InputType::untyped),
                },
            );
        }
        if !views.by_symbol.is_empty() {
            views.observer = Some(Arc::clone(&observer.values));
            views.printer = Some(Arc::clone(&observer.unparser));
            views.subject = Some(Arc::clone(&self.values));
        }
        Ok(views)
    }
}

fn cell_sort_name(sort: &SortRef) -> String {
    match sort {
        SortRef::Declared(decl) => format!("`{decl}`"),
        SortRef::Builtin(builtin) => builtin.k_name().to_owned(),
    }
}
