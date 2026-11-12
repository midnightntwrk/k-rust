//! `krs kink compare`'s cell vocabulary: kink-flow's [`Vocabulary`] implemented with krs-exec's
//! ends, so that an implementation of a KRS corpus's system is given its start and writes its
//! end as `krs run --output end` writes an end's `cells` (cells by Rust field path, values as
//! documents of the typed encoding), and is compared with the definition as `krs compare`
//! compares two ends, each view's `compare`, `views` and `observer` read as a case's
//! expectation reads them.
//!
//! - The request's `start` is the `cells` of the end document of the definition's start, the
//!   state of its depth-0 run, every cell stated; its `inputs` are the program's typed inputs,
//!   each decoded at its parameter's declared type and written as its canonical document, by the
//!   parameter's Rust name, a program file bound to the main parameter included (its bytes as a
//!   `Bytes` document, a text program as `{"$text": ..}`), so a request is a function of the
//!   values, never of the files that hold them.
//! - An answer's `cells` are read as an end document's: a path the configuration does not
//!   declare and a value of another type make it malformed, and so does a cell it does not state
//!   that it does not omit (`omits`), among the observable leaf cells, which every view may read.
//! - A view compares its `compare` cells (default: every observable leaf cell the implementation
//!   states), through its `views` functions, resolved in its `observer` (default: the
//!   definition). A compared cell the implementation omits makes the view `not-compared`
//!   (`omitted`), as does one the corpus's ends leave out (`[result]`, `left-out`).
//! - The definition's ends are kink's (its baseline run, truncated at `[stop]`), each read as a
//!   krs-exec end with the cells kink leaves out unstated; both sides are compared by their
//!   cells, since kink-flow compares the words `stopped` and `final` itself. Where the definition
//!   has several ends and they differ under the view from each other, one answer cannot be
//!   compared with them by equality: `several-ends`.
//! - A trace view (`channels`) compares no cell: it compares the implementation's record of the
//!   corpus's `[observe]` channels with the definition's ([`super::traces`]). The request's
//!   `observe` asks each channel in the declaration's own vocabulary
//!   ([`krs_exec::ResolvedObservations::channel_shapes`]), and a view over a channel some
//!   component of which has no value with a document is refused before any run, since no
//!   implementation can state an element of it. An implementation with no end view states the
//!   cells it likes: those it states are read as an end's, and none is demanded.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use k_rust::kore::ast::Pattern;
use kink_flow::{
    ImplementationSection, Judged, NotCompared, Program, Question, TraceAnswer, TraceQuestion,
    ViewSection, Vocabulary,
};
use krs_exec::{
    CellInfo, Compared, Comparison, ConfigValue, End, EndClass, EndError, Ends, Halt, Semantics,
    Side,
};
use serde_json::{Value, json};

use super::inputs::{KrsInputs, ManifestFiles};
use super::observe::KrsObservations;
use super::render::{Observers, read_ends, unstated};
use crate::DEFAULT_VIEW_BUDGET;

/// The vocabulary of one emission, over the decoder's native compile and the corpus's
/// observers.
pub(crate) struct KrsImplementations {
    inputs: Arc<KrsInputs>,
    observers: Arc<Observers>,
    /// The corpus's `[observe]`, which a trace view's channels are of; `None` without one.
    observations: Option<Arc<KrsObservations>>,
}

impl KrsImplementations {
    pub(crate) const fn new(
        inputs: Arc<KrsInputs>,
        observers: Arc<Observers>,
        observations: Option<Arc<KrsObservations>>,
    ) -> Self {
        Self {
            inputs,
            observers,
            observations,
        }
    }

    /// The corpus's `[observe]`, which a trace is a record of.
    fn observations(&self) -> Result<&KrsObservations, String> {
        self.observations
            .as_deref()
            .ok_or_else(|| "the corpus declares no `[observe]`, so it has no channel".to_owned())
    }

    /// `body` with the definition's semantics and the observer `view` names, when it names one
    /// other than the definition.
    fn with_observer<T>(
        &self,
        need: &str,
        view: &ViewSection,
        body: impl FnOnce(&mut Semantics, Option<&mut Semantics>) -> Result<T, String>,
    ) -> Result<T, String> {
        let observer = match view.front_end.get("observer").and_then(Value::as_str) {
            Some(name) => self
                .observers
                .get(name)
                .map_err(|reason| format!("view `{}`: `observer`: {reason}", view.name))?,
            None => None,
        };
        self.inputs
            .with_semantics_mut(need, |semantics| match observer {
                Some(observer) => observer.with_loaded(|loaded| body(semantics, Some(loaded))),
                None => body(semantics, None),
            })
    }
}

/// The class both sides' ends are read with: kink-flow compares the words itself.
const fn stuck() -> EndClass {
    EndClass {
        halt: Halt::Stuck,
        rule: None,
    }
}

/// Whether the cell at `path` is `cell` or lies inside it.
fn within(path: &str, cell: &str) -> bool {
    path == cell
        || path
            .strip_prefix(cell)
            .is_some_and(|rest| rest.starts_with('.'))
}

/// Whether the cells at `left` and `right` overlap: one is, or holds, the other.
fn overlap(left: &str, right: &str) -> bool {
    within(left, right) || within(right, left)
}

/// The observable leaf cells, by declared path, none inside a cell of `left_out`.
fn leaves<'c>(cells: &'c [CellInfo], left_out: &[&str]) -> Vec<&'c str> {
    cells
        .iter()
        .filter(|cell| cell.ty.is_some() && !cell.unobservable)
        .map(|cell| cell.path.as_str())
        .filter(|path| !left_out.iter().any(|out| within(path, out)))
        .collect()
}

/// A view's `views`, a function by cell.
fn named_views(view: &ViewSection) -> BTreeMap<String, String> {
    view.front_end
        .get("views")
        .and_then(Value::as_object)
        .map(|views| {
            views
                .iter()
                .filter_map(|(cell, function)| Some((cell.clone(), function.as_str()?.to_owned())))
                .collect()
        })
        .unwrap_or_default()
}

/// A view's `compare`, when it names its cells.
fn named_compare(view: &ViewSection) -> Option<Vec<String>> {
    view.front_end
        .get("compare")
        .and_then(Value::as_array)
        .map(|cells| {
            cells
                .iter()
                .filter_map(|cell| cell.as_str().map(str::to_owned))
                .collect()
        })
}

/// The comparison `view` of `implementation` states, its views resolved in `observer` (else
/// `semantics`), given the cells the corpus's ends leave out (`left_out`, by declared path):
/// `Ok(Err(..))` when it is not compared, `Err` when it is no comparison of the definition.
fn comparison(
    semantics: &Semantics,
    observer: Option<&Semantics>,
    implementation: &ImplementationSection,
    view: &ViewSection,
    left_out: &[&str],
) -> Result<Result<(Comparison, Vec<String>), NotCompared>, String> {
    let refuse = |error: EndError| format!("view `{}`: {error}", view.name);
    let cells = semantics.cells();
    let views = named_views(view);
    let named = named_compare(view);
    // The compared cells the implementation omits, and those the corpus's ends leave out.
    let compared: Vec<String> = match &named {
        Some(named) => named.clone(),
        None => views.keys().cloned().collect(),
    };
    let omitted = compared
        .iter()
        .filter(|path| implementation.omits.iter().any(|cell| overlap(path, cell)))
        .cloned()
        .collect::<Vec<_>>();
    if !omitted.is_empty() {
        return Ok(Err(NotCompared::Omitted(omitted)));
    }
    if let Some(path) = compared
        .iter()
        .find(|path| left_out.iter().any(|cell| overlap(path, cell)))
    {
        return Ok(Err(NotCompared::LeftOut(format!(
            "the view compares `{path}`, which the corpus's ends leave out ([result], unobservable \
             cells): the definition's side does not state it"
        ))));
    }
    let left_out_or_omitted = left_out
        .iter()
        .copied()
        .chain(implementation.omits.iter().map(String::as_str))
        .collect::<Vec<_>>();
    let compare = named.unwrap_or_else(|| {
        leaves(&cells, &left_out_or_omitted)
            .into_iter()
            .map(str::to_owned)
            .collect()
    });
    // What the comparison leaves out because the implementation omits it, for the row.
    let omits = implementation
        .omits
        .iter()
        .filter(|cell| compare.iter().all(|path| !overlap(path, cell)))
        .cloned()
        .collect::<Vec<_>>();
    let mut comparison = Comparison {
        compare: Some(compare),
        ..Comparison::default()
    };
    comparison.views = semantics
        .cell_views(observer.unwrap_or(semantics), &views)
        .map_err(refuse)?;
    semantics.check_comparison(&comparison).map_err(refuse)?;
    Ok(Ok((comparison, omits)))
}

/// An answer's `cells` read as an end of the definition.
fn answer_end(semantics: &Semantics, cells: &Value) -> Result<End, String> {
    semantics
        .read_end(&json!({"halt": Halt::Stuck.as_str(), "cells": cells}))
        .map_err(|error| error.to_string())
}

impl Vocabulary for KrsImplementations {
    fn check(&self, implementation: &ImplementationSection) -> Result<(), String> {
        self.inputs
            .with_semantics("checking an implementation's cells", |semantics| {
                let cells = semantics.cells();
                if let Some(cell) = implementation
                    .omits
                    .iter()
                    .find(|cell| !cells.iter().any(|known| known.path == **cell))
                {
                    return Err(format!(
                        "omits: `{cell}` is no cell of the definition (its cells: {})",
                        cells
                            .iter()
                            .map(|cell| cell.path.as_str())
                            .collect::<Vec<_>>()
                            .join(", ")
                    ));
                }
                Ok(())
            })?;
        for (index, view) in implementation.views.iter().enumerate() {
            // A trace view compares channels, never cells: it is no end view over every cell.
            if let Some(channels) = &view.channels {
                self.observations()
                    .and_then(|observations| {
                        observations.with_resolved(|resolved| resolved.document_forms(channels))
                    })
                    .map_err(|reason| {
                        format!(
                            "views[{index}].channels: {reason}; no implementation can state an                              element of it, so the view `{}` would compare nothing",
                            view.name
                        )
                    })?;
                continue;
            }
            self.with_observer(
                "resolving an implementation's views",
                view,
                |semantics, observer| {
                    comparison(semantics, observer.as_deref(), implementation, view, &[])
                        .map(|_| ())
                },
            )?;
        }
        Ok(())
    }

    fn start(&self, state: &Pattern) -> Result<Value, String> {
        self.inputs
            .with_semantics("writing the definition's start", |semantics| {
                let end = semantics
                    .read_configuration(state, stuck(), &BTreeSet::new())
                    .map_err(|error| error.to_string())?;
                let mut document = semantics
                    .end_document(&end)
                    .map_err(|error| error.to_string())?;
                Ok(document["cells"].take())
            })
    }

    fn inputs(
        &self,
        program: &Program,
        files: &mut dyn kink_flow::admit::InputFiles,
    ) -> Result<Value, String> {
        self.inputs
            .with_semantics("writing a program's typed inputs", |semantics| {
                let mut inputs = serde_json::Map::new();
                for (name, document) in &program.inputs {
                    let document =
                        krs_exec::toml_document(document).map_err(|error| error.to_string())?;
                    let parameter = semantics
                        .parameter(name)
                        .map_err(|error| error.to_string())?
                        .clone();
                    let value = match semantics
                        .decode_input(name, &document, &mut ManifestFiles(files))
                        .map_err(|error| error.to_string())?
                    {
                        ConfigValue::Value(value) => semantics
                            .encode(&value, &parameter.ty)
                            .map_err(|error| format!("`{name}`: {error}"))?,
                        ConfigValue::Text(text) => json!({ "$text": text }),
                        ConfigValue::TextFile(file) => json!({ "$text": file.text }),
                    };
                    inputs.insert(parameter.name.clone(), value);
                }
                if let Some(source) = &program.source {
                    let (name, bytes) = match source {
                        kink_corpus::ProgramSource::Text(text) => {
                            ("the program text".to_owned(), text.clone().into_bytes())
                        }
                        kink_corpus::ProgramSource::File(path) => files.read(None, path)?,
                    };
                    let value = match semantics
                        .program_file(&name, bytes)
                        .map_err(|error| error.to_string())?
                    {
                        krs_exec::ProgramFile::Bytes { parameter, value } => {
                            let ty = semantics
                                .parameter(&parameter)
                                .map_err(|error| error.to_string())?
                                .ty
                                .clone();
                            let document = semantics
                                .encode(&value, &ty)
                                .map_err(|error| format!("`{parameter}`: {error}"))?;
                            (parameter, document)
                        }
                        krs_exec::ProgramFile::Text(text) => (
                            semantics
                                .program_parameter()
                                .map_err(|error| error.to_string())?
                                .name
                                .clone(),
                            json!({ "$text": text.text }),
                        ),
                    };
                    inputs.insert(value.0, value.1);
                }
                Ok(Value::Object(inputs))
            })
    }

    fn read_answer(
        &self,
        implementation: &ImplementationSection,
        cells: &Value,
    ) -> Result<(), String> {
        self.inputs
            .with_semantics("reading an implementation's end", |semantics| {
                let end = answer_end(semantics, cells)?;
                // Only an end view compares cells: without one, the cells stated are read, and
                // none is demanded.
                if implementation.views.iter().all(ViewSection::is_trace) {
                    return Ok(());
                }
                let all = semantics.cells();
                let omitted = implementation
                    .omits
                    .iter()
                    .map(String::as_str)
                    .collect::<Vec<_>>();
                let stated = Comparison {
                    compare: Some(
                        leaves(&all, &omitted)
                            .into_iter()
                            .map(str::to_owned)
                            .collect(),
                    ),
                    ..Comparison::default()
                };
                semantics
                    .check_stated(&stated, &end, "implementation")
                    .map_err(|error| match error {
                        EndError::MissingCell { .. } => format!(
                            "{error}; an implementation states every observable cell it does not \
                         declare in `omits`"
                        ),
                        other => other.to_string(),
                    })
            })
    }

    fn compare(&self, question: &Question<'_>) -> Result<Judged, String> {
        let Question {
            implementation,
            view,
            cells,
            ends,
            not_compared,
        } = *question;
        self.with_observer(
            "comparing an implementation's end",
            view,
            |semantics, observer| {
                let all = semantics.cells();
                let unstated = unstated(&all, not_compared);
                let left_out = unstated
                    .iter()
                    .map(|cell| cell.path.as_str())
                    .collect::<Vec<_>>();
                let (mut comparison, omitted) = match comparison(
                    semantics,
                    observer.as_deref(),
                    implementation,
                    view,
                    &left_out,
                )? {
                    Ok(comparison) => comparison,
                    Err(reason) => return Ok(Judged::NotCompared(reason)),
                };
                let definition = match read_ends(semantics, ends, &stuck(), &unstated) {
                    Ok(ends) => Ends {
                        ends,
                        incomplete: None,
                    },
                    Err(detail) => return Ok(Judged::NotCompared(NotCompared::Unreadable(detail))),
                };
                let answered = Ends::one(answer_end(semantics, cells)?);
                if let Some(reason) =
                    evaluate_views(semantics, observer, &mut comparison, &definition, &answered)
                {
                    return Ok(Judged::NotCompared(reason));
                }
                judge(semantics, &comparison, &definition, &answered, omitted)
            },
        )
    }

    fn observe_request(&self, channels: &[String]) -> Result<Vec<Value>, String> {
        self.observations()?.with_resolved(|resolved| {
            resolved.document_forms(channels)?;
            let shapes = resolved.channel_shapes(channels)?;
            channels
                .iter()
                .map(|name| {
                    shapes
                        .iter()
                        .find(|shape| shape["name"] == name.as_str())
                        .cloned()
                        .ok_or_else(|| format!("`[observe]` has no shape of the channel `{name}`"))
                })
                .collect()
        })
    }

    fn judge_trace(&self, question: &TraceQuestion<'_>) -> Result<TraceAnswer, String> {
        let mut answer = self
            .observations()?
            .with_resolved(|resolved| super::traces::judge(resolved, question))?;
        if let TraceAnswer::Judged(judged) = &mut answer
            && judged
                .iter()
                .any(|judged| matches!(judged, kink_flow::TraceJudged::Different(_)))
        {
            self.inputs
                .with_semantics("naming a difference's rule", |semantics| {
                    super::traces::name_rules(semantics, judged);
                    Ok(())
                })?;
        }
        Ok(answer)
    }
}

/// The two sides of a comparison, named as a difference shows them.
fn sides<'e>(definition: &'e Ends, answered: &'e Ends) -> [Side<'e>; 2] {
    [
        Side {
            name: "definition",
            ends: definition,
        },
        Side {
            name: "implementation",
            ends: answered,
        },
    ]
}

/// Evaluate `comparison`'s views at both sides' ends, in `observer` (else `semantics`): why the
/// view is not compared when an evaluation stops before it ends (`undecided`) or has no value
/// (`unreadable`), else `None`.
fn evaluate_views(
    semantics: &mut Semantics,
    observer: Option<&mut Semantics>,
    comparison: &mut Comparison,
    definition: &Ends,
    answered: &Ends,
) -> Option<NotCompared> {
    if comparison.views.is_empty() {
        return None;
    }
    let (observer, subject) = match observer {
        Some(observer) => (observer, Some(&*semantics)),
        None => (&mut *semantics, None),
    };
    match comparison.views.evaluate_within(
        observer,
        subject,
        &sides(definition, answered),
        Some(DEFAULT_VIEW_BUDGET),
    ) {
        Ok(()) => None,
        Err(error @ EndError::ViewStopped { .. }) => {
            Some(NotCompared::Undecided(error.to_string()))
        }
        Err(error) => Some(NotCompared::Unreadable(error.to_string())),
    }
}

/// The verdict of `comparison` of the definition's ends with the answered one; `omitted` the
/// cells it left out because the implementation omits them.
fn judge(
    semantics: &Semantics,
    comparison: &Comparison,
    definition: &Ends,
    answered: &Ends,
    omitted: Vec<String>,
) -> Result<Judged, String> {
    let [left, right] = sides(definition, answered);
    let compared = match semantics.compare_ends(comparison, left, right) {
        Ok(compared) => compared,
        Err(error @ EndError::MissingCell { .. }) => {
            return Ok(Judged::NotCompared(NotCompared::LeftOut(error.to_string())));
        }
        Err(error) => return Err(error.to_string()),
    };
    Ok(match compared {
        Compared::Equal => Judged::Equal { omitted },
        Compared::Inconclusive(reason) => Judged::NotCompared(NotCompared::Undecided(reason)),
        Compared::Differs(difference) => {
            // Several ends that differ from each other under the view: one answer is compared
            // with them by inclusion, not equality.
            if definition.ends.len() > 1 {
                let first = Ends::one(definition.ends[0].clone());
                let one = Side {
                    name: "definition",
                    ends: &first,
                };
                if semantics
                    .compare_ends(comparison, left, one)
                    .map_err(|error| error.to_string())?
                    != Compared::Equal
                {
                    return Ok(Judged::NotCompared(NotCompared::SeveralEnds(format!(
                        "the definition's run has {} ends that differ under the view: one answer \
                         against several ends is a question of inclusion, which compare does not \
                         decide",
                        definition.ends.len()
                    ))));
                }
            }
            let mut difference =
                serde_json::to_value(&*difference).map_err(|error| error.to_string())?;
            // Both sides were read with one class: kink-flow compared their words.
            for side in ["left", "right"] {
                if let Some(side) = difference[side].as_object_mut() {
                    side.remove("class");
                }
            }
            Judged::Different {
                difference,
                omitted,
            }
        }
    })
}
