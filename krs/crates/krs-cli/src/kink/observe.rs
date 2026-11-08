//! `[observe]` in a KRS corpus: observation channels named with KRS's spellings, as `krs run
//! --observe` and a case's `observe` name them (krs-exec [`krs_exec::ObservationSpec`]): each
//! point class's rules by KRS item or label, as a stop names them; its cells and a log's cell by
//! Rust field path; its views, components and filter (`views`, `components`, `when`) and a log's
//! element function (`element`) by KRS path; and the observer every function is evaluated in as
//! `PACKAGE:DEFINITION`, by default the corpus's own definition, the baseline, never the mutant.
//!
//! The front end resolves the declaration before anything runs, through krs-exec's own resolver
//! ([`krs_exec::Semantics::observations`]), so a declaration is refused here exactly where `krs
//! run` refuses it, with its message (stage `observe`, reason `observe-unresolved`; a rule name
//! that selects no rewrite rule, `point-unresolved`). It then hands kink-flow the declaration at
//! the K level (each rule name mapped to the exact K labels of the rewrite rules it selects, as
//! the `stop` submodule maps a stop's, and each cell to its K cell name) and kink-campaign the
//! functions that give its elements ([`kink_flow::ObserveFunctions`]): an identity, which every
//! key and document of a run with the declaration names, and an oracle, which evaluates every
//! content, filter and log element of a run with krs-exec's evaluator
//! ([`krs_exec::ObservationOracle::evaluator`]). The oracle reads each run's cells with the
//! baseline's declarations and evaluates each function in the observer, never in the definition
//! being run, so the baseline and every mutant are observed alike; kink-campaign does not admit a
//! mutant whose read cells (the declaration's and its functions') could hold a term that denotes
//! another value on it than on the baseline (`observation-incompatible`), and the oracle reads no
//! value from a cell holding a symbol the baseline does not declare.
//!
//! Every content is the front end's, a declaration without functions included: its elements are
//! then the cells' values as krs-exec digests them, and their documents are the typed encoding's,
//! so a kill's evidence shows every element by Rust path and canonical document
//! (`krs-difference/4`, [`super::render`]).
//!
//! The observer is loaded once per thread that runs a program, as a stop condition's is
//! ([`super::condition`]). Each evaluation is bounded by the view budget `krs run` gives one by
//! default ([`crate::DEFAULT_VIEW_BUDGET`]).
//!
//! The identity is `{observer: {definition, definition_ir}, declaration}`: the observer's name
//! as written (`null` for the baseline) and its Definition IR digest, and the declaration with
//! KRS's spellings as written; with a named observer also `subject: {definition_ir}`, the
//! baseline's Definition IR digest. The digest and the names decide every function a name
//! resolves to and every answer it gives, and the subject how each cell's term is read as a value
//! of the observer: the baseline as observer is its own subject, a named observer reads the cells
//! with the baseline's declarations. kink-campaign holds equal declarations as one value with one
//! oracle, so two corpora whose baselines differ give two declarations even where they name one
//! observer.

use std::collections::BTreeMap;
use std::sync::Arc;

use k_rust::backend::ProbeState;
use k_rust::kore::ast::Pattern;
use kink_flow::{
    Evaluated, FlowManifest, ObservationEvaluator, ObservationFunctions, ObserveFunctions,
    ObserveSection,
};
use krs_exec::{
    Component, Filter, LogChannel, ObservationOracle, ObservationSpec, PointClass,
    ResolvedObservations, Semantics, Stutter,
};
use serde_json::{Value, json};

use super::cells::CellNames;
use super::condition::Subject;
use super::inputs::KrsInputs;
use super::render::{Observer, Observers, definition_digest};
use super::stop::{Unbound, rule_labels};

/// `manifest` with its `[observe]` resolved (module documentation): the rule names mapped to
/// exact K labels, the cells to K cell names, and the functions set
/// ([`FlowManifest::with_observe_functions`]); and the `krs` object the documents' `observe`
/// gains: `items`, each rule name as written to the labels it selects, and `cells`, each cell by
/// Rust path to its K cell. `manifest` unchanged, no object and no compile without `[observe]`.
/// The names resolve over `decoder`'s native compile; the observer is the one `observers` holds
/// by its name, else `definition`, the corpus's own.
///
/// # Errors
///
/// `observe-unresolved` with krs's refusal of the declaration or of its observer, or with why a
/// front end's key is not of its shape; `point-unresolved` with why a rule name selects no
/// rewrite rule, or why a selected rule has no label to name it by; `native-compile` when the
/// definition does not compile natively.
pub(crate) fn bind(
    mut manifest: FlowManifest,
    decoder: &Arc<KrsInputs>,
    observers: &Observers,
    definition: &krs_ir_levels::DefinitionIr,
) -> Result<(FlowManifest, Option<Value>), Unbound> {
    let Some(mut section) = manifest.observe.clone() else {
        return Ok((manifest, None));
    };
    let spec = written(&section)?;
    let functions = KrsObservations::bind(spec.clone(), definition, decoder, observers)?;
    let names = spec
        .points
        .iter()
        .flat_map(|point| {
            let place = |side: &str| format!("[observe] point `{}` {side}", point.name);
            point
                .before
                .iter()
                .map(move |name| (place("before"), name.clone()))
                .chain(
                    point
                        .after
                        .iter()
                        .map(move |name| (place("after"), name.clone())),
                )
        })
        .collect::<Vec<_>>();
    let selections = decoder
        .with_semantics("resolving the [observe] rules", |semantics| {
            Ok(names
                .into_iter()
                .map(|(place, name)| {
                    let labels = rule_labels(semantics, &place, &name, "a point's rules");
                    (name, labels)
                })
                .collect::<Vec<_>>())
        })
        .map_err(|detail| Unbound {
            reason: "native-compile",
            detail,
        })?;
    let mut items = BTreeMap::<String, Vec<String>>::new();
    for (name, labels) in selections {
        let mut labels = labels.map_err(|detail| Unbound {
            reason: "point-unresolved",
            detail,
        })?;
        labels.sort();
        labels.dedup();
        items.insert(name, labels);
    }
    let labels = |names: &[String]| {
        let mut labels = names
            .iter()
            .flat_map(|name| items[name].iter().cloned())
            .collect::<Vec<_>>();
        labels.sort();
        labels.dedup();
        labels
    };
    let cell_names = CellNames::of(definition);
    let mut cells = BTreeMap::<String, String>::new();
    let mut k_name = |path: &str| -> Result<String, Unbound> {
        let name = cell_names.name_of(path).ok_or_else(|| Unbound {
            reason: "observe-unresolved",
            detail: format!(
                "[observe] reads the cell `{path}`, which is no Rust path of a cell of the \
                 configuration"
            ),
        })?;
        cells.insert(path.to_owned(), name.to_owned());
        Ok(name.to_owned())
    };
    for (point, written) in section.points.iter_mut().zip(&spec.points) {
        point.before = labels(&written.before);
        point.after = labels(&written.after);
        point.cells = written
            .cells
            .iter()
            .map(|path| k_name(path))
            .collect::<Result<_, _>>()?;
    }
    for (log, written) in section.logs.iter_mut().zip(&spec.logs) {
        log.cell = k_name(&written.cell)?;
    }
    manifest.observe = Some(section);
    let manifest = manifest.with_observe_functions(functions);
    Ok((manifest, Some(json!({"items": items, "cells": cells}))))
}

/// The declaration `section` states with KRS's spellings, its front end's keys read.
fn written(section: &ObserveSection) -> Result<ObservationSpec, Unbound> {
    let refuse = |detail: String| Unbound {
        reason: "observe-unresolved",
        detail,
    };
    let points = section
        .points
        .iter()
        .enumerate()
        .map(|(index, point)| {
            let key = |name: &str| format!("observe.point[{index}].{name}");
            let views = match point.front_end.get("views") {
                None => BTreeMap::new(),
                Some(views) => serde_json::from_value::<BTreeMap<String, String>>(views.clone())
                    .map_err(|error| refuse(format!("{}: {error}", key("views"))))?,
            };
            let components = match point.front_end.get("components") {
                None => Vec::new(),
                Some(components) => components
                    .as_array()
                    .into_iter()
                    .flatten()
                    .enumerate()
                    .map(|(position, component)| {
                        let at = format!("{}[{position}]", key("components"));
                        let (cells, function) =
                            function_of(component, &at, true).map_err(refuse)?;
                        let name = component["name"]
                            .as_str()
                            .ok_or_else(|| refuse(format!("{at}.name: expected a string")))?;
                        Ok(Component {
                            name: name.to_owned(),
                            cells,
                            function,
                        })
                    })
                    .collect::<Result<Vec<_>, Unbound>>()?,
            };
            let when = point
                .front_end
                .get("when")
                .map(|when| {
                    function_of(when, &key("when"), false)
                        .map(|(cells, function)| Filter { function, cells })
                        .map_err(refuse)
                })
                .transpose()?;
            Ok(PointClass {
                name: point.name.clone(),
                before: point.before.clone(),
                after: point.after.clone(),
                stutter: Stutter::parse(point.stutter.name())
                    .ok_or_else(|| refuse(format!("{}: no stuttering mode", key("stutter"))))?,
                cells: point.cells.clone(),
                views,
                components,
                when,
            })
        })
        .collect::<Result<Vec<_>, Unbound>>()?;
    let logs = section
        .logs
        .iter()
        .map(|log| LogChannel {
            name: log.name.clone(),
            cell: log.cell.clone(),
            element: log
                .front_end
                .get("element")
                .and_then(Value::as_str)
                .map(str::to_owned),
            at: log.at.clone(),
        })
        .collect();
    Ok(ObservationSpec {
        points,
        logs,
        observer: section.observer.clone(),
    })
}

/// A function of named cells as written at `key`: `{function, cells}`, with `name` beside them
/// where `named` (a component); its cells and its function.
fn function_of(value: &Value, key: &str, named: bool) -> Result<(Vec<String>, String), String> {
    let Some(table) = value.as_object() else {
        return Err(format!("{key}: expected a table"));
    };
    let known = ["function", "cells", "name"];
    if let Some(unknown) = table
        .keys()
        .find(|name| !known[..if named { 3 } else { 2 }].contains(&name.as_str()))
    {
        return Err(format!("{key}: unknown key `{unknown}`"));
    }
    let function = table
        .get("function")
        .and_then(Value::as_str)
        .filter(|function| !function.trim().is_empty())
        .ok_or_else(|| format!("{key}.function: expected a nonempty string"))?;
    let cells = table
        .get("cells")
        .and_then(Value::as_array)
        .and_then(|cells| {
            cells
                .iter()
                .map(|cell| cell.as_str().map(str::to_owned))
                .collect::<Option<Vec<_>>>()
        })
        .filter(|cells| !cells.is_empty())
        .ok_or_else(|| format!("{key}.cells: expected a nonempty array of strings"))?;
    Ok((cells, function.to_owned()))
}

/// The declaration with KRS's spellings, as the identity names it: every key as written.
fn written_value(spec: &ObservationSpec) -> Value {
    let points = spec
        .points
        .iter()
        .map(|point| {
            json!({
                "name": point.name,
                "before": point.before,
                "after": point.after,
                "stutter": point.stutter.as_str(),
                "cells": point.cells,
                "views": point.views,
                "components": point.components.iter().map(|component| json!({
                    "name": component.name,
                    "cells": component.cells,
                    "function": component.function,
                })).collect::<Vec<_>>(),
                "when": point.when.as_ref().map(|when| json!({
                    "function": when.function,
                    "cells": when.cells,
                })),
            })
        })
        .collect::<Vec<_>>();
    let logs = spec
        .logs
        .iter()
        .map(|log| {
            json!({
                "name": log.name,
                "cell": log.cell,
                "element": log.element,
                "at": log.at,
            })
        })
        .collect::<Vec<_>>();
    json!({"points": points, "logs": logs, "observer": spec.observer})
}

/// The functions of one corpus's `[observe]` ([`ObservationFunctions`]).
struct KrsObservations {
    spec: ObservationSpec,
    observer: Arc<Observer>,
    subject: Subject,
    cells: Vec<Vec<String>>,
}

impl KrsObservations {
    /// The declaration `spec` of the corpus whose definition is `definition`, resolved: its
    /// observer prepared (`observers` holds a named one; the baseline is `definition` itself),
    /// the declaration resolved as `krs run` resolves it, and its identity.
    fn bind(
        spec: ObservationSpec,
        definition: &krs_ir_levels::DefinitionIr,
        inputs: &Arc<KrsInputs>,
        observers: &Observers,
    ) -> Result<ObserveFunctions, Unbound> {
        let unresolved = |detail: String| Unbound {
            reason: "observe-unresolved",
            detail: format!("[observe]: {detail}"),
        };
        let named = match &spec.observer {
            Some(name) => observers
                .get(name)
                .map_err(|reason| unresolved(format!("the observer `{name}`: {reason}")))?,
            None => None,
        };
        let (observer, subject) = match named {
            Some(observer) => (observer, Subject::Inputs(Arc::clone(inputs))),
            None => (
                Arc::new(
                    Observer::compile("the definition", definition.clone()).map_err(unresolved)?,
                ),
                Subject::Observer,
            ),
        };
        let mut functions = Self {
            spec,
            observer,
            subject,
            cells: Vec::new(),
        };
        let resolved = functions
            .observer
            .with_loaded(|observer| functions.resolve(observer))
            .map_err(unresolved)?;
        functions.cells = resolved.read_cells();
        let digest = definition_digest(functions.observer.definition()).map_err(unresolved)?;
        let mut identity = json!({
            "observer": {
                "definition": functions.spec.observer,
                "definition_ir": digest,
            },
            "declaration": written_value(&functions.spec),
        });
        // A named observer reads the cells with the baseline's declarations (the subject), which
        // its own digest does not name; the baseline as observer is its own subject.
        if let Subject::Inputs(_) = &functions.subject {
            identity["subject"] =
                json!({"definition_ir": definition_digest(definition).map_err(unresolved)?});
        }
        Ok(ObserveFunctions::new(identity, Arc::new(functions)))
    }

    /// The declaration resolved for runs of the baseline, evaluated in `observer` (this
    /// declaration's observer, loaded on this thread).
    fn resolve(&self, observer: &Semantics) -> Result<ResolvedObservations, String> {
        match &self.subject {
            Subject::Observer => observer
                .observations(observer, &self.spec)
                .map_err(|error| error.to_string()),
            Subject::Inputs(inputs) => {
                inputs.with_semantics("reading an observation's cells", |subject| {
                    subject
                        .observations(observer, &self.spec)
                        .map_err(|error| error.to_string())
                })
            }
        }
    }
}

impl ObservationFunctions for KrsObservations {
    fn cells(&self) -> &[Vec<String>] {
        &self.cells
    }

    fn filtered(&self, class: usize) -> bool {
        self.spec
            .points
            .get(class)
            .is_some_and(|point| point.when.is_some())
    }

    fn with_evaluator(
        &self,
        body: &mut dyn FnMut(&mut dyn ObservationEvaluator),
    ) -> Result<(), String> {
        self.observer.with_loaded(|observer| {
            let resolved = self.resolve(observer)?;
            let oracle = ObservationOracle::evaluator(
                &resolved,
                Some(observer),
                Some(crate::DEFAULT_VIEW_BUDGET),
            )
            .map_err(|error| error.to_string())?;
            body(&mut KrsEvaluator(oracle));
            Ok(())
        })
    }
}

/// krs-exec's evaluating oracle as kink-campaign's evaluator of one request.
struct KrsEvaluator<'o>(ObservationOracle<'o>);

/// An element as kink-campaign compares and shows it.
fn evaluated(element: krs_exec::Evaluated) -> Evaluated {
    let mut digest = [0; 32];
    digest.copy_from_slice(element.digest.as_bytes());
    Evaluated {
        digest,
        value: element.value,
    }
}

impl ObservationEvaluator for KrsEvaluator<'_> {
    fn holds(&mut self, class: usize, state: &ProbeState<'_>) -> Option<Result<bool, String>> {
        self.0.holds(class, state)
    }

    fn content(
        &mut self,
        class: usize,
        state: &ProbeState<'_>,
        value: bool,
    ) -> Result<Evaluated, String> {
        self.0.keep_values(value);
        self.0.content(class, state).map(evaluated)
    }

    fn elements(
        &mut self,
        log: usize,
        item: &Pattern,
        value: bool,
    ) -> Result<Vec<Evaluated>, String> {
        self.0.keep_values(value);
        self.0
            .item_elements(log, item)
            .map(|elements| elements.into_iter().map(evaluated).collect())
    }

    fn item_digest(&mut self, item: &Pattern) -> [u8; 32] {
        let mut digest = [0; 32];
        digest.copy_from_slice(self.0.item_digest(item).as_bytes());
        digest
    }
}
