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
//!   definition). A view naming a projection compares what the projection does, resolved once
//!   for the command ([`super::projections`]), and a projection without `compare` compares every
//!   observable leaf cell. A compared cell the implementation omits makes the view
//!   `not-compared` (`omitted`), as does one the corpus's ends leave out (the projections' cells,
//!   `left-out`).
//! - Each end view is resolved once per command: its observation and observer on first use, and
//!   what it compares (its cells, the refusals above, its comparison checked) once per set of
//!   cells the corpus's ends leave out, which a command does not change; a question only binds
//!   the view's functions in the instances loaded on its thread, once per pair of instances
//!   ([`super::render::Observers::bound_views`]).
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
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use k_rust::kore::ast::Pattern;
use kink_flow::{
    Distance, EndsJudged, EndsQuestion, ImplementationSection, Judged, NotCompared, Program,
    Question, RefusalJudged, RefusalQuestion, TraceAnswer, TraceQuestion, ViewSection, Vocabulary,
};
use krs_exec::{
    Compared, Comparison, ConfigValue, End, EndClass, EndError, Ends, Halt, Semantics, Side,
};
use serde_json::{Value, json};

use super::inputs::{KrsInputs, ManifestFiles};
use super::observe::KrsObservations;
use super::projections::{KrsProjections, Observation, leaves, within};
use super::render::{Observer, Observers, read_ends, unstated, with_declared_classes};
use crate::DEFAULT_VIEW_BUDGET;

/// The vocabulary of one emission, over the decoder's native compile and the corpus's
/// observers.
pub(crate) struct KrsImplementations {
    inputs: Arc<KrsInputs>,
    observers: Arc<Observers>,
    /// The corpus's `[observe]`, which a trace view's channels are of; `None` without one.
    observations: Option<Arc<KrsObservations>>,
    /// The corpus's end projections, resolved once for the command.
    projections: Arc<KrsProjections>,
    /// Each end view resolved so far, by implementation and view name ([`Self::view`]).
    views: Mutex<BTreeMap<(String, String), Arc<ResolvedView>>>,
    /// How many end views were resolved, and how many decisions of what one compares were made
    /// ([`Self::decided`]).
    counts: [AtomicUsize; 2],
}

/// One end view of one implementation, resolved once per command: its observation (a named
/// projection's, or its own keys' for an inline view), its observer prepared (`None`: the
/// definition), and what it compares given the cells the corpus's ends leave out, decided once
/// per such set ([`KrsImplementations::decided`]).
struct ResolvedView {
    observation: Arc<Observation>,
    observer: Option<Arc<Observer>>,
    decided: Mutex<Vec<(Vec<String>, Decision)>>,
}

/// What one end view compares: its compared cells by path and the cells it leaves out because
/// the implementation omits them (the row's `omits`), or why it is not compared.
type Decision = Result<(Vec<String>, Vec<String>), NotCompared>;

impl KrsImplementations {
    pub(crate) fn new(
        inputs: Arc<KrsInputs>,
        observers: Arc<Observers>,
        observations: Option<Arc<KrsObservations>>,
        projections: Arc<KrsProjections>,
    ) -> Self {
        Self {
            inputs,
            observers,
            observations,
            projections,
            views: Mutex::new(BTreeMap::new()),
            counts: [AtomicUsize::new(0), AtomicUsize::new(0)],
        }
    }

    /// The work counters of the command's resolution of projections and views, by name: each a
    /// function of the corpus's declarations, never of how many programs were compared
    /// (`kink.projections.resolved`, `kink.views.resolved`, `kink.views.decided`,
    /// `kink.views.bound`).
    pub(crate) fn counters(&self) -> [(&'static str, usize); 4] {
        [
            ("kink.projections.resolved", self.projections.resolved()),
            (
                "kink.views.resolved",
                self.counts[0].load(Ordering::Relaxed),
            ),
            ("kink.views.decided", self.counts[1].load(Ordering::Relaxed)),
            ("kink.views.bound", self.observers.bindings()),
        ]
    }

    /// The corpus's `[observe]`, which a trace is a record of.
    fn observations(&self) -> Result<&KrsObservations, String> {
        self.observations
            .as_deref()
            .ok_or_else(|| "the corpus declares no `[observe]`, so it has no channel".to_owned())
    }

    /// The end view `view` of `implementation`, resolved on first use: a view naming a projection
    /// takes the projection's resolution, by name; an inline view is read from its keys and its
    /// observer prepared.
    fn view(
        &self,
        implementation: &ImplementationSection,
        view: &ViewSection,
    ) -> Result<Arc<ResolvedView>, String> {
        let key = (implementation.name.clone(), view.name.clone());
        let mut views = self.views.lock().unwrap_or_else(PoisonError::into_inner);
        if let Some(resolved) = views.get(&key) {
            return Ok(Arc::clone(resolved));
        }
        let (observation, observer) = if let Some(name) = &view.projection {
            let projection = self.projections.get(name).ok_or_else(|| {
                format!(
                    "view `{}`: `{name}` is no end projection of the flow",
                    view.name
                )
            })?;
            (
                Arc::clone(&projection.observation),
                projection.observer.clone(),
            )
        } else {
            let observation = Observation::of_view(view);
            let observer = match &observation.observer {
                Some(name) => self
                    .observers
                    .get(name)
                    .map_err(|reason| format!("view `{}`: `observer`: {reason}", view.name))?,
                None => None,
            };
            (Arc::new(observation), observer)
        };
        let resolved = Arc::new(ResolvedView {
            observation,
            observer,
            decided: Mutex::new(Vec::new()),
        });
        self.counts[0].fetch_add(1, Ordering::Relaxed);
        views.insert(key, Arc::clone(&resolved));
        Ok(resolved)
    }

    /// What `resolved`, the end view `view` of `implementation`, compares given the cells the
    /// corpus's ends leave out (`left_out`, by declared path), decided on first use for that set
    /// ([`comparison`]); `semantics` and `observer` the instances loaded on this thread.
    fn decided(
        &self,
        resolved: &ResolvedView,
        semantics: &Semantics,
        observer: Option<&Semantics>,
        (implementation, view): (&ImplementationSection, &ViewSection),
        left_out: &[&str],
    ) -> Result<Decision, String> {
        let mut decided = resolved
            .decided
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        if let Some((_, decision)) = decided.iter().find(|(cells, _)| {
            cells
                .iter()
                .map(String::as_str)
                .eq(left_out.iter().copied())
        }) {
            return Ok(decision.clone());
        }
        let decision = comparison(
            &self.observers,
            semantics,
            observer,
            implementation,
            view,
            &resolved.observation,
            left_out,
        )?;
        self.counts[1].fetch_add(1, Ordering::Relaxed);
        decided.push((
            left_out.iter().map(|&cell| cell.to_owned()).collect(),
            decision.clone(),
        ));
        Ok(decision)
    }

    /// `body` with the definition's semantics and the observer of `resolved`, when it has one
    /// other than the definition, each loaded on this thread.
    fn with_observer<T>(
        &self,
        need: &str,
        resolved: &ResolvedView,
        body: impl FnOnce(&mut Semantics, Option<&mut Semantics>) -> Result<T, String>,
    ) -> Result<T, String> {
        self.inputs
            .with_semantics_mut(need, |semantics| match &resolved.observer {
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
        declared: None,
    }
}

/// Whether the cells at `left` and `right` overlap: one is, or holds, the other.
fn overlap(left: &str, right: &str) -> bool {
    within(left, right) || within(right, left)
}

/// What the end view `view` of `implementation`, observing `observation`, compares, its views
/// bound in `observer` (else `semantics`) through `observers`, given the cells the corpus's ends
/// leave out (`left_out`, by declared path): `Ok(Err(..))` when it is not compared, `Err` when it
/// is no comparison of the definition.
fn comparison(
    observers: &Observers,
    semantics: &Semantics,
    observer: Option<&Semantics>,
    implementation: &ImplementationSection,
    view: &ViewSection,
    observation: &Observation,
    left_out: &[&str],
) -> Result<Decision, String> {
    let refuse = |error: EndError| format!("view `{}`: {error}", view.name);
    let cells = semantics.cells();
    // The compared cells the implementation omits, and those the corpus's ends leave out: a
    // projection without `compare` compares every observable cell, whichever the implementation
    // states.
    let compared = observation.named(&cells, left_out);
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
            "the view compares `{path}`, which the corpus's ends leave out (cells no projection \
             compares, unobservable cells): the definition's side does not state it"
        ))));
    }
    let compare = if observation.cells == super::projections::Cells::Stated {
        let left_out_or_omitted = left_out
            .iter()
            .copied()
            .chain(implementation.omits.iter().map(String::as_str))
            .collect::<Vec<_>>();
        leaves(&cells, &left_out_or_omitted)
            .into_iter()
            .map(str::to_owned)
            .collect()
    } else {
        compared
    };
    // What the comparison leaves out because the implementation omits it, for the row.
    let omits = implementation
        .omits
        .iter()
        .filter(|cell| compare.iter().all(|path| !overlap(path, cell)))
        .cloned()
        .collect::<Vec<_>>();
    let comparison = Comparison {
        compare: Some(compare),
        views: observers
            .bound_views(semantics, observer, &observation.views)
            .map_err(refuse)?,
    };
    semantics.check_comparison(&comparison).map_err(refuse)?;
    Ok(Ok((comparison.compare.unwrap_or_default(), omits)))
}

/// An answer's `cells` read as an end of the definition.
fn answer_end(semantics: &Semantics, cells: &Value) -> Result<End, String> {
    semantics
        .read_end(&json!({"halt": Halt::Stuck.as_str(), "cells": cells}))
        .map_err(|error| error.to_string())
}

/// A `rejected` answer's `refused` (`{end, reason}`) read as an end document's declared class
/// (`class = "refused"`, its `end` and its `reason`), with no cell: the refusal the
/// implementation names, in the definition's vocabulary. The reader refuses an `end` that is no
/// declared refused end of the definition and a `reason` not of that end's reason type.
fn refusal_end(semantics: &Semantics, refused: &Value) -> Result<End, String> {
    let mut document = json!({"halt": Halt::Stuck.as_str(), "cells": {}, "class": "refused"});
    document["end"] = refused["end"].clone();
    if let Some(reason) = refused.get("reason") {
        document["reason"] = reason.clone();
    }
    semantics
        .read_end(&document)
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
            // An acceptance view compares whether each side accepts the program: no cell.
            if view.accepts {
                continue;
            }
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
            let resolved = self.view(implementation, view)?;
            self.with_observer(
                "resolving an implementation's views",
                &resolved,
                |semantics, observer| {
                    self.decided(
                        &resolved,
                        semantics,
                        observer.as_deref(),
                        (implementation, view),
                        &[],
                    )
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
                if !implementation.has_end_view() {
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
        let resolved = self.view(implementation, view)?;
        self.with_observer(
            "comparing an implementation's end",
            &resolved,
            |semantics, observer| {
                let all = semantics.cells();
                let unstated = unstated(&all, not_compared);
                let left_out = unstated
                    .iter()
                    .map(|cell| cell.path.as_str())
                    .collect::<Vec<_>>();
                let (compare, omitted) = match self.decided(
                    &resolved,
                    semantics,
                    observer.as_deref(),
                    (implementation, view),
                    &left_out,
                )? {
                    Ok(decided) => decided,
                    Err(reason) => return Ok(Judged::NotCompared(reason)),
                };
                let mut comparison = Comparison {
                    compare: Some(compare),
                    views: self
                        .observers
                        .bound_views(semantics, observer.as_deref(), &resolved.observation.views)
                        .map_err(|error| format!("view `{}`: {error}", view.name))?,
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

    /// The definition's ends against a mutant's, both K ends of the definition read with the
    /// cells the record leaves out unstated, compared on the projection's cells through its views
    /// evaluated in its one observer, as two sets ([`Semantics::compare_ends`]); a view whose
    /// evaluation stops or has no value, a side that cannot be read and a compared cell the
    /// record leaves out are inconclusive.
    fn compare_ends(&self, question: &EndsQuestion<'_>) -> Result<EndsJudged, String> {
        let EndsQuestion {
            projection,
            baseline,
            mutant,
            not_compared,
        } = *question;
        let resolved = self
            .projections
            .get(&projection.name)
            .ok_or_else(|| format!("`{}` is no end projection of the flow", projection.name))?;
        let judge = |semantics: &mut Semantics, mut observer: Option<&mut Semantics>| {
            let all = semantics.cells();
            let unstated = unstated(&all, not_compared);
            let left_out = unstated
                .iter()
                .map(|cell| cell.path.as_str())
                .collect::<Vec<_>>();
            let compare = resolved.observation.named(&all, &left_out);
            if let Some(path) = compare
                .iter()
                .find(|path| left_out.iter().any(|cell| overlap(path, cell)))
            {
                return Ok(EndsJudged::Inconclusive(format!(
                    "the projection compares `{path}`, which the record leaves out"
                )));
            }
            let mut comparison = Comparison {
                compare: Some(compare),
                views: self
                    .observers
                    .bound_views(semantics, observer.as_deref(), &resolved.observation.views)
                    .map_err(|error| format!("projection `{}`: {error}", projection.name))?,
            };
            let read = |semantics: &Semantics, ends| {
                read_ends(semantics, ends, &stuck(), &unstated).map(|ends| Ends {
                    ends,
                    incomplete: None,
                })
            };
            let (definition, mutated) = match (read(semantics, baseline), read(semantics, mutant)) {
                (Ok(definition), Ok(mutated)) => (definition, mutated),
                (Err(detail), _) | (_, Err(detail)) => {
                    return Ok(EndsJudged::Inconclusive(detail));
                }
            };
            if let Some(reason) = evaluate_views(
                semantics,
                observer.as_deref_mut(),
                &mut comparison,
                &definition,
                &mutated,
            ) {
                return Ok(EndsJudged::Inconclusive(reason.detail()));
            }
            let left = Side {
                name: "baseline",
                ends: &definition,
            };
            let right = Side {
                name: "mutant",
                ends: &mutated,
            };
            Ok(match semantics.compare_ends(&comparison, left, right) {
                Ok(Compared::Equal) => EndsJudged::Equal,
                Ok(Compared::Differs(difference)) => EndsJudged::Different(
                    serde_json::to_value(&*difference).map_err(|error| error.to_string())?,
                ),
                Ok(Compared::Inconclusive(reason)) => EndsJudged::Inconclusive(reason),
                Err(error) => EndsJudged::Inconclusive(error.to_string()),
            })
        };
        self.inputs
            .with_semantics_mut("comparing a mutant's ends", |semantics| {
                match &resolved.observer {
                    Some(observer) => observer.with_loaded(|loaded| judge(semantics, Some(loaded))),
                    None => judge(semantics, None),
                }
            })
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

    fn declares_finished_end(&self) -> bool {
        self.inputs
            .with_semantics("reading the definition's declared ends", |semantics| {
                Ok(semantics.declares_finished_end())
            })
            .unwrap_or(false)
    }

    fn read_refusal(&self, refused: &Value) -> Result<Value, String> {
        self.inputs
            .with_semantics("reading an implementation's refusal", |semantics| {
                let declared = refusal_end(semantics, refused)?
                    .class
                    .declared
                    .unwrap_or_default();
                Ok(json!({
                    "end": declared.end,
                    "reason": declared.reason.and_then(|reason| reason.document),
                }))
            })
    }

    /// Each definition end gets its declared class as an expectation's comparison gives it
    /// ([`with_declared_classes`]), and is compared with the answer's refusal under a comparison
    /// of no cell, so only the parts of the declared class both state decide
    /// ([`krs_exec::Semantics::compare_ends`]).
    fn judge_refusal(&self, question: &RefusalQuestion<'_>) -> Result<RefusalJudged, String> {
        self.inputs
            .with_semantics_mut("comparing an implementation's refusal", |semantics| {
                let answered = Ends::one(refusal_end(semantics, question.refused)?);
                let cells = semantics.cells();
                let unstated = unstated(&cells, question.not_compared);
                let left_out = !unstated.is_empty();
                let ends = read_ends(semantics, question.ends, &stuck(), &unstated)?;
                let class = answered.ends[0].class.clone();
                let ends =
                    match with_declared_classes(semantics, question.ends, ends, &class, left_out) {
                        Ok(ends) => ends,
                        Err(reason) => return Ok(RefusalJudged::Undecided(reason)),
                    };
                let comparison = Comparison {
                    compare: Some(Vec::new()),
                    ..Comparison::default()
                };
                let total = ends.len();
                let mut agree = 0;
                let mut first = None;
                for end in ends {
                    let one = Ends::one(end);
                    let compared = semantics
                        .compare_ends(
                            &comparison,
                            Side {
                                name: "definition",
                                ends: &one,
                            },
                            Side {
                                name: "implementation",
                                ends: &answered,
                            },
                        )
                        .map_err(|error| error.to_string())?;
                    match compared {
                        Compared::Equal => agree += 1,
                        Compared::Differs(difference) => {
                            if first.is_none() {
                                first = Some(
                                    serde_json::to_value(&*difference)
                                        .map_err(|error| error.to_string())?,
                                );
                            }
                        }
                        Compared::Inconclusive(reason) => {
                            return Ok(RefusalJudged::Undecided(reason));
                        }
                    }
                }
                Ok(match first {
                    None => RefusalJudged::Agree,
                    Some(difference) if agree == 0 => RefusalJudged::Different(difference),
                    Some(_) => RefusalJudged::SeveralEnds(format!(
                        "the refusal the answer names agrees with {agree} of the definition's \
                         {total} ends and not the others: one answer against several ends is \
                         a question of inclusion, which compare does not decide"
                    )),
                })
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
    // The view's compared leaf cells, which every difference names as `compared` and an equal
    // comparison has no document to name.
    let compared_cells = semantics
        .compared_leaves(comparison)
        .map_err(|error| error.to_string())?
        .len();
    Ok(match compared {
        Compared::Equal => Judged::Equal {
            omitted,
            compared_cells,
        },
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
            // The first difference's cell (none where the classes differ) and every other
            // compared cell that differs: one full walk of the compared cells gives both.
            let distance = Distance {
                differing_cells: usize::from(difference.cell.is_some())
                    + difference.also_differ.len(),
                compared_cells,
            };
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
                distance,
            }
        }
    })
}
