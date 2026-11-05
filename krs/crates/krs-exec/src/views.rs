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
//! from a package that depends on the compared definition's package, refers to it (so that its
//! module imports the configured module and is the composed definition's main module), and that
//! no semantics imports, so that editing a view changes neither the compared definition, nor its
//! rules, nor anything keyed by it. A function the observer's Definition IR declares but its
//! loaded definition does not hold (its package's module is not imported) is no view. A cell's
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

use std::collections::BTreeMap;
use std::fmt;
use std::sync::Arc;

use k_rust::k_rust_backend::definition::Admission;

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
    /// The type a viewed value is written at: the function's result sort.
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
    /// the definition the views were resolved in; each distinct value once.
    ///
    /// # Errors
    ///
    /// Returns [`EndError::View`] for a view without a value at an end (naming the side and the
    /// cell), and for an `observer` other than the one the views were resolved in.
    pub fn evaluate(
        &mut self,
        observer: &mut Semantics,
        sides: &[Side<'_>],
    ) -> Result<(), EndError> {
        let (Some(index), Some(subject)) = (&self.observer, &self.subject) else {
            return Ok(());
        };
        if !Arc::ptr_eq(index, observer.values()) {
            return Err(EndError::State(
                "the views are evaluated in a definition other than the observer they were resolved in".to_owned(),
            ));
        }
        let subject = Arc::clone(subject);
        let mut pending = Vec::new();
        for side in sides {
            for end in &side.ends.ends {
                if end.class.halt != Halt::Undefined {
                    self.collect(subject.cells(), &end.cells, side.name, "", &mut pending);
                }
            }
        }
        for (symbol, value, side, path) in pending {
            if self
                .results
                .get(&symbol)
                .is_some_and(|results| results.contains_key(&value))
            {
                continue;
            }
            let view = &self.by_symbol[&symbol];
            let refuse = |message: String| EndError::View {
                cell: view.cell.clone(),
                function: view.function.clone(),
                message: format!("it has no value at the {side} end's `{path}`: {message}"),
            };
            if let Some(part) = opaque_part(&subject, &value) {
                return Err(refuse(format!(
                    "the cell holds {part}, which has no KRS description to carry to the view"
                )));
            }
            let viewed = observer
                .evaluate(view.decl.path(), vec![(&*view.parameter, value.clone())])
                .map_err(|error| refuse(error.to_string()))?;
            self.results
                .entry(symbol)
                .or_default()
                .insert(value, viewed);
        }
        Ok(())
    }

    /// Every viewed leaf value below `cells`, with its side and its path, instances indexed.
    fn collect(
        &self,
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
                            node,
                            instance,
                            side,
                            &format!("{path}[{position}]"),
                            output,
                        );
                    }
                }
                EndCell::Optional(Some(content)) => {
                    self.collect_content(node, content, side, &path, output);
                }
                EndCell::Optional(None) => {}
                content => self.collect_content(node, content, side, &path, output),
            }
        }
    }

    fn collect_content(
        &self,
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
                self.collect(&node.children, cells, side, &format!("{path}."), output);
            }
            _ => {}
        }
    }
}

/// The first part of `value` with no KRS description, described.
fn opaque_part(index: &ValueIndex, value: &Value) -> Option<String> {
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
    /// refuses or a result that is no term of the definition, and [`EvaluationError::NoValue`] when the result holds a part with no KRS
    /// description: an unevaluated application, `\bottom`, a disjunction.
    pub fn evaluate(
        &mut self,
        function: &str,
        arguments: Vec<(&str, Value)>,
    ) -> Result<Value, EvaluationError> {
        let application = self.values.call(function, arguments)?;
        let kast = self.values.to_kast(&application)?;
        let pattern = self.configuration.typed_kore(&kast).map_err(|error| {
            EvaluationError::Backend(format!(
                "the application is no term of the definition: {error}"
            ))
        })?;
        let simplified = self
            .backend
            .simplify_kore(None, &pattern, Admission::Unverified)
            .map_err(|error| EvaluationError::Backend(error.to_string()))?;
        let value = self.values.decode(&simplified).map_err(|error| {
            EvaluationError::Backend(format!(
                "the simplified application is no term of the definition: {error}"
            ))
        })?;
        match opaque_part(&self.values, &value) {
            Some(part) => Err(EvaluationError::NoValue(part)),
            None => Ok(value),
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
    /// does not declare, a name that resolves to no function of the observer, and a function
    /// that does not take exactly one parameter of a sort at least the cell's.
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
            let Some(Some(parameter_sort)) = info.field_sorts.first() else {
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
                    result: info
                        .result
                        .clone()
                        .map_or_else(InputType::untyped, InputType::of),
                },
            );
        }
        if !views.by_symbol.is_empty() {
            views.observer = Some(Arc::clone(&observer.values));
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
