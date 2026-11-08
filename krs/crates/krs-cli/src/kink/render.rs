//! A kill's evidence at the KRS level: kink-flow's [`EndRenderer`] implemented with krs-exec's
//! comparison of ends, so that a kill's difference is the document that comparison writes
//! wherever KRS shows two ends differ (`krs-difference/3`, as `krs run --case` shows an unmet
//! expectation): the cell by Rust field path and both values as their canonical documents.
//!
//! kink gives the renderer the two sets of ends its slot compared, final configurations of the
//! K the front end emitted. Each is read as a krs-exec end of the definition the K was emitted
//! from ([`krs_exec::Semantics::read_configuration`]), with the cells the slot leaves out not
//! stated: the slot replaced each by `\top` of its sort, which states nothing of it. The
//! comparison then compares every observable leaf cell the ends state, which are the cells the
//! slot compared, and chooses its pair of ends by krs-exec's rule, which is kink's (an end
//! outside the other set and its nearest end there); the sides are named `baseline` and
//! `mutant`.
//!
//! Every end kink compares is an end of the system its run explores (truncated at its stop, when
//! the corpus has one): a state with no successor there, compared by its configuration alone, so
//! a path stopped at a configuration and a path stuck at it give one end. The renderer is given
//! no class, so it states none: krs-exec's comparison is given each end with one class, `stuck`,
//! so that it compares the cells alone, and each side of the document leaves its `class` out.
//!
//! The renderer judges nothing: kink's slot proved the kill. Two decoded values are equal exactly
//! when their terms are, so the comparison finds a difference wherever the slot did in a cell the
//! definition declares; where it does not (a difference only in compilation's cells, an end it
//! cannot read, a native compile that fails), kink gives its own evidence with the reason.
//!
//! The documents depend on the ends, on the Definition IR's names and types (cells by Rust field,
//! constructors and fields by Rust name) and on krs's build. The tier-1 context names the build
//! (`kink_build`, the running executable) and the emitted K up to positions (the execution
//! digest), but a constructor's field names never reach the K: its non-terminals are emitted as
//! sorts. So the renderer's identity ([`EndRenderer::identity`]) is the SHA-256 of the Definition
//! IR's JSON without its provenance tables, which hold the IR's source positions and which no
//! document reads; a field renamed under the same syntax changes it, an edit that only moves
//! text does not.
//!
//! # Expectations
//!
//! The renderer also reads a case's expectation, the `expect` table of a case document, as
//! `krs run --case` reads it ([`krs_exec::Semantics::expectation`]: cells by Rust field path,
//! values as documents of the encoding, the stop rule named as `--stop-before` names one), and
//! checks it against the ends of the case's baseline run by krs-exec's rule
//! ([`krs_exec::Semantics::check_expectation`]: met when every end agrees with it on the class and
//! the compared cells, each viewed cell on its view's value, "Views" below), each end read as
//! above, the sides named `expected` and `baseline`.
//!
//! An end's class is what kink's observation of the run says of it. Without `[stop]` every end
//! kink keeps is a state of no successor, `stuck`, so the class is compared. With `[stop]` an end
//! is stuck, or stopped at a rule of the stop, and the ends do not say which: a run merges the
//! paths that reach one configuration, whichever way each reached it. So the halt of an
//! expectation of a stuck end, or of one stopped at a rule the stop stops at, is not observed:
//! its cells are compared, an end that differs on them makes it unmet (whatever the halt, the
//! end is not the one expected), and the detail says the halt was not compared, but ends that
//! agree on every compared cell make it inconclusive, not met, since met is agreement on the
//! halt as well. The halt of an expectation of another halt is decided, since no end of the
//! truncated system has it: it is compared with ends of class `stuck`, which differ from it at
//! the class, the baseline's side of its difference stating no class, and the detail says so.
//! An expectation kink's observation cannot decide is inconclusive, saying why: an end stopped
//! at a rule the corpus does not stop at, or with no `[stop]`. An expectation of a `depth-bound`
//! end is refused as `krs run --case` refuses it, since no end meets it. A cell the
//! expectation compares that the corpus's `[result]` leaves out is not in the ends kink keeps,
//! which makes the check inconclusive too.
//!
//! # Views
//!
//! An expectation states one question, and `krs run --case` answers it with the expectation's
//! `views` applied, so the check applies them too: a viewed cell is compared on what its view
//! gives at the expected value and at each end's value, not on the value itself. The views are
//! resolved ([`krs_exec::Semantics::cell_views`]) in the definition the cases run on, or in the
//! observer the expectation names (`observer`, `PACKAGE:DEFINITION`), whose package is composed
//! with the command's selection as `krs run --case` composes it. An observer is prepared and
//! compiled once per command, the first time an expectation names it, and its semantics is loaded
//! once per thread that checks an expectation, as the definition's own compile is. Reading an
//! expectation's views moves no identity: an expectation is in no digest, cache key or stored
//! record, and every command that reports it checks it again. (A view the definition declares is
//! part of its Definition IR, so editing it moves the renderer's identity and `definition.k`, as
//! any edit of the definition does; editing an observer's view moves nothing kink keys.)
//!
//! Admission resolves the views of every case and evaluates them at the expected end: an observer
//! that cannot be prepared, a view that names no function of its observer or does not apply to
//! its cell, a view of a cell the expectation does not compare, and a view without a value at the
//! expected end refuse the case (`expectation-value`). Each depends on the case alone (its
//! expected end, views and observer), never on what the definition runs the case to, so the case
//! states no question any baseline answers; `krs run --case` refuses each too. An evaluation at
//! the expected end that stops before it ends admits the case, since the view may yet have a
//! value there; the check then reports it. The check evaluates each view at the expected end and
//! at every baseline end, each evaluation within `krs run --case`'s default budget
//! ([`crate::DEFAULT_VIEW_BUDGET`]). An evaluation that stops before it ends makes the
//! expectation inconclusive, since the view may yet have a value. A view without a value at a
//! baseline end refuses the case under `krs run --case`; kink refuses no case after admission, so
//! the check reports that it cannot check the expectation, which kink-flow makes an inconclusive
//! verdict with the refusal as its detail. Every verdict reached through the views' values names
//! the views in its detail, and the observer when the expectation names one; an unmet verdict's
//! difference names the views too. A verdict decided before any view is evaluated (an expected
//! end kink compares no end to, a stop rule the corpus does not stop at) names none.
//!
//! # Observation differences
//!
//! A kill by `[observe]`'s channels is a difference kink's observation slot found at a channel and
//! an index, re-derived from both sides' values. The front end gives every element of a KRS
//! corpus's channels through krs-exec's evaluator ([`super::observe`]), so each side's element is
//! a document of the typed encoding (a class's content an object of its components by name, each
//! a Rust path or a component's name; a log's element its document), or the channel's closure
//! there. The evidence is `krs-difference/4`: `{format, position: {channel, index, at_end},
//! kind, at, cell, path, baseline: {element}, mutant: {element}}`, where `kind` is `point` or
//! `log`, `cell` the log's cell by Rust path or the class's first component whose values differ,
//! `path` the place inside the two values where they first differ (krs-exec `value_path`), and
//! `at` all of it as one place (`bus[0]`, `boundary[3].pc`). Each element is the document, or
//! `"end"`, `"undefined"`, `"cycle"` (the side's path returned to an earlier state, so its channel
//! has no element there, ever) or `"undecided"`. The document depends on what an end difference's
//! depends on, and its format enters the tier-1 context beside it.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, OnceLock, PoisonError};

use k_rust::kast::identifier::label_or_name;
use k_rust::kore::ast::Pattern;
use kink_campaign::Element;
use kink_flow::{
    CheckedExpectation, EndRenderer, ExpectationCheck, ExpectationVerdict, ObserveSection,
    ObservedDifference, StopSection,
};
use krs_exec::{
    CellInfo, Compared, Comparison, CompiledStage, DIFFERENCE_FORMAT, End, EndClass, EndError,
    Ends, Expectation, Halt, Semantics, Side,
};
use krs_ir::measure::Timings;
use krs_ir_levels::DefinitionIr;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

use super::inputs::{KrsInputs, ManifestFiles};
use crate::{CommandRequest, DEFAULT_VIEW_BUDGET, DiagnosticSources};

/// The renderer of one emission's kill evidence, over the decoder's native compile.
pub(crate) struct KrsEnds {
    inputs: Arc<KrsInputs>,
    /// The renderer's identity, computed on first use (tier 1's context names it, in both
    /// profiles; a run with tier 1 off never asks).
    identity: OnceLock<Result<Value, String>>,
    /// The observers the corpus's expectations name.
    observers: Arc<Observers>,
}

impl KrsEnds {
    pub(crate) const fn new(inputs: Arc<KrsInputs>, observers: Arc<Observers>) -> Self {
        Self {
            inputs,
            identity: OnceLock::new(),
            observers,
        }
    }

    /// `body` with the views of `expectation` resolved into its comparison (module
    /// documentation, "Views"), given the definition the case runs on, `semantics`, and the
    /// observer they are evaluated in when the expectation names one other than it.
    fn with_views<T>(
        &self,
        semantics: &mut Semantics,
        expectation: &mut Expectation,
        body: impl FnOnce(&mut Semantics, Option<&mut Semantics>, &mut Expectation) -> Result<T, String>,
    ) -> Result<T, String> {
        if expectation.views.is_empty() {
            return body(semantics, None, expectation);
        }
        let observer = match &expectation.observer {
            Some(name) => self
                .observers
                .get(name)
                .map_err(|reason| format!("`expect.observer`: {reason}"))?,
            None => None,
        };
        if let Some(observer) = observer {
            observer.with_loaded(|loaded| {
                resolve_views(semantics, Some(loaded), expectation)?;
                body(semantics, Some(loaded), expectation)
            })
        } else {
            resolve_views(semantics, None, expectation)?;
            body(semantics, None, expectation)
        }
    }
}

/// The observers a corpus's expectations name, each prepared (its package collected and
/// composed with the definition) and compiled once per command, on first use, and loaded once
/// per thread that checks an expectation (module documentation, "Views"). Preparing one observer
/// holds back only the threads that need that observer.
pub(crate) struct Observers {
    /// The command's selection, which an observer is composed with.
    request: CommandRequest,
    /// The command's source roots, which render an observer's diagnostics.
    sources: DiagnosticSources,
    /// Each observer named so far, by name, set once its preparation ends.
    prepared: Mutex<BTreeMap<String, Arc<OnceLock<Prepared>>>>,
}

/// An observer named by a corpus: compiled, `None` for the definition itself, or why it cannot be
/// prepared.
pub(crate) type Prepared = Result<Option<Arc<Observer>>, String>;

impl Observers {
    pub(crate) fn new(request: CommandRequest, sources: DiagnosticSources) -> Self {
        Self {
            request,
            sources,
            prepared: Mutex::new(BTreeMap::new()),
        }
    }

    /// The observer `name`, prepared and compiled the first time an expectation names it;
    /// `None` when it names the definition the cases run on.
    pub(crate) fn get(&self, name: &str) -> Prepared {
        // The map's lock is held only to find the observer's slot, not while it is prepared.
        let slot = Arc::clone(
            self.prepared
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .entry(name.to_owned())
                .or_default(),
        );
        slot.get_or_init(|| {
            crate::command::observer_definition(&self.request, name, &self.sources).and_then(
                |definition| {
                    definition
                        .map(|definition| Observer::compile(name, definition).map(Arc::new))
                        .transpose()
                },
            )
        })
        .clone()
    }
}

/// An observer definition and its compiled stage.
pub(crate) struct Observer {
    /// Tells this observer's load apart from another's in a thread's cache.
    id: u64,
    name: String,
    definition: DefinitionIr,
    stage: CompiledStage,
}

impl Observer {
    /// The observer's Definition IR.
    pub(crate) const fn definition(&self) -> &DefinitionIr {
        &self.definition
    }

    pub(crate) fn compile(name: &str, definition: DefinitionIr) -> Result<Self, String> {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let stage = CompiledStage::compile(&definition, &mut Timings::disabled())
            .map_err(|error| format!("the observer `{name}` cannot be compiled: {error}"))?;
        Ok(Self {
            id: NEXT.fetch_add(1, Ordering::Relaxed),
            name: name.to_owned(),
            definition,
            stage,
        })
    }

    /// `body` with this observer's semantics on this thread, loaded on first use under the
    /// solver options the definition's own compile has.
    pub(crate) fn with_loaded<T>(
        &self,
        body: impl FnOnce(&mut Semantics) -> Result<T, String>,
    ) -> Result<T, String> {
        LOADED.with(|loaded| {
            let mut loaded = loaded.borrow_mut();
            let position = if let Some(position) = loaded.iter().position(|(id, _)| *id == self.id)
            {
                position
            } else {
                let semantics = Semantics::from_stage(
                    &self.definition,
                    self.stage.clone(),
                    None,
                    &mut Timings::disabled(),
                )
                .map_err(|error| format!("krs cannot load the observer `{}`: {error}", self.name));
                loaded.push((self.id, semantics));
                loaded.len() - 1
            };
            let semantics = loaded[position]
                .1
                .as_mut()
                .map_err(|reason| reason.clone())?;
            body(semantics)
        })
    }
}

thread_local! {
    /// Each observer's semantics on this thread, or why it failed to load, by observer id.
    static LOADED: RefCell<Vec<(u64, Result<Semantics, String>)>> = const { RefCell::new(Vec::new()) };
}

/// Resolve the views `expectation` names into its comparison, in `observer` when it names one
/// and in `semantics` otherwise, refusing, as `krs run --case` does before the case runs, a view
/// that does not apply to its cell or applies to a cell the expectation does not compare.
fn resolve_views(
    semantics: &Semantics,
    observer: Option<&Semantics>,
    expectation: &mut Expectation,
) -> Result<(), String> {
    let refuse = |error: EndError| format!("`expect.views`: {error}");
    expectation.comparison.views = semantics
        .cell_views(observer.unwrap_or(semantics), &expectation.views)
        .map_err(refuse)?;
    semantics
        .check_stated(&expectation.comparison, &expectation.end, "expected")
        .map_err(refuse)
}

/// The format of a kill's evidence of a difference of observation channels
/// ([`EndRenderer::observation_difference`]; module documentation, "Observation differences").
pub(crate) const OBSERVATION_DIFFERENCE_FORMAT: &str = "krs-difference/4";

impl EndRenderer for KrsEnds {
    fn format(&self) -> &'static str {
        DIFFERENCE_FORMAT
    }

    fn observation_format(&self) -> Option<&'static str> {
        Some(OBSERVATION_DIFFERENCE_FORMAT)
    }

    fn observation_difference(
        &self,
        difference: &ObservedDifference,
        observe: Option<&ObserveSection>,
    ) -> Result<Value, String> {
        observation_difference(self.inputs.definition(), difference, observe)
    }

    fn identity(&self) -> Result<Value, String> {
        self.identity
            .get_or_init(|| {
                definition_digest(self.inputs.definition())
                    .map(|digest| json!({ "definition_ir": digest }))
            })
            .clone()
    }

    fn difference(
        &self,
        baseline: &BTreeSet<Pattern>,
        mutant: &BTreeSet<Pattern>,
        mutant_complete: bool,
        not_compared: &[String],
    ) -> Result<Value, String> {
        self.inputs
            .with_semantics("showing a kill's evidence at the KRS level", |semantics| {
                difference(semantics, baseline, mutant, mutant_complete, not_compared)
            })
    }

    fn read_expectation(
        &self,
        expect: &toml::Table,
        files: &mut dyn kink_flow::admit::InputFiles,
    ) -> Result<(), String> {
        let document = expectation_document(expect)?;
        self.inputs
            .with_semantics_mut("reading a case's expectation", |semantics| {
                let mut expectation = semantics
                    .expectation(&document, None, &mut ManifestFiles(files))
                    .map_err(|error| error.to_string())?;
                self.with_views(semantics, &mut expectation, expected_views)
            })
    }

    fn check_expectation(&self, check: ExpectationCheck<'_>) -> Result<CheckedExpectation, String> {
        let document = expectation_document(check.expect)?;
        let rule = check
            .expect
            .get("rule")
            .and_then(toml::Value::as_str)
            .map(str::to_owned);
        let ExpectationCheck {
            files,
            ends,
            not_compared,
            stop,
            ..
        } = check;
        self.inputs
            .with_semantics_mut("checking a case's expectation", |semantics| {
                let mut expectation = semantics
                    .expectation(&document, None, &mut ManifestFiles(files))
                    .map_err(|error| error.to_string())?;
                self.with_views(
                    semantics,
                    &mut expectation,
                    |semantics, observer, expectation| {
                        checked_expectation(
                            Viewed {
                                semantics,
                                observer,
                            },
                            expectation,
                            rule.as_deref(),
                            ends,
                            not_compared,
                            stop,
                        )
                    },
                )
            })
    }
}

/// The evidence of a difference of observation channels (module documentation, "Observation
/// differences"), the declaration `observe` bound to the definition `definition`.
fn observation_difference(
    definition: &DefinitionIr,
    difference: &ObservedDifference,
    observe: Option<&ObserveSection>,
) -> Result<Value, String> {
    let shown = |element: &Element| match element {
        Element::Evaluated(value) => Ok(value.clone()),
        Element::End => Ok(json!("end")),
        Element::Undefined => Ok(json!("undefined")),
        Element::Cycle => Ok(json!("cycle")),
        Element::Undecided => Ok(json!("undecided")),
        Element::Content(_) => {
            Err("the element is a K term, not a value the front end's functions gave".to_owned())
        }
    };
    let (baseline, mutant) = (shown(&difference.baseline)?, shown(&difference.mutant)?);
    let position = &difference.position;
    let log =
        observe.and_then(|observe| observe.logs.iter().find(|log| log.name == position.channel));
    let values = match (&difference.baseline, &difference.mutant) {
        (Element::Evaluated(left), Element::Evaluated(right)) => Some((left, right)),
        _ => None,
    };
    let (kind, cell, path) = if let Some(log) = log {
        let cell = super::cells::CellNames::of(definition)
            .path_of(&log.cell)
            .map_or_else(|| log.cell.clone(), str::to_owned);
        let path = values.and_then(|(left, right)| krs_exec::value_path(left, right));
        ("log", Some(cell), path)
    } else {
        // A class's content is an object of its components by name: the first that differs.
        let differing = values.and_then(|(left, right)| {
            let (Value::Object(left), Value::Object(right)) = (left, right) else {
                return None;
            };
            left.keys()
                .chain(right.keys())
                .collect::<BTreeSet<_>>()
                .into_iter()
                .find(|name| left.get(*name) != right.get(*name))
                .map(|name| {
                    let path = match (left.get(name), right.get(name)) {
                        (Some(left), Some(right)) => krs_exec::value_path(left, right),
                        _ => None,
                    };
                    (name.clone(), path)
                })
        });
        match differing {
            Some((name, path)) => ("point", Some(name), path),
            None => ("point", None, None),
        }
    };
    let mut at = format!("{}[{}]", position.channel, position.index);
    if kind == "point"
        && let Some(cell) = &cell
    {
        at.push('.');
        at.push_str(cell);
    }
    if let Some(path) = &path {
        if !path.starts_with('[') {
            at.push('.');
        }
        at.push_str(path);
    }
    Ok(json!({
        "format": OBSERVATION_DIFFERENCE_FORMAT,
        "position": {
            "channel": position.channel,
            "index": position.index,
            "at_end": position.at_end,
        },
        "kind": kind,
        "at": at,
        "cell": cell,
        "path": path,
        "baseline": {"element": baseline},
        "mutant": {"element": mutant},
    }))
}

/// Admit `expectation`, its views resolved, unless a view has no value at its expected end
/// (module documentation, "Views"): that depends on the case alone, so the case states no
/// question any baseline answers. An evaluation that stops before it ends admits it.
fn expected_views(
    semantics: &mut Semantics,
    observer: Option<&mut Semantics>,
    expectation: &mut Expectation,
) -> Result<(), String> {
    if expectation.comparison.views.is_empty() {
        return Ok(());
    }
    let (observer, subject) = match observer {
        Some(observer) => (observer, Some(&*semantics)),
        None => (semantics, None),
    };
    let expected = Ends::one(expectation.end.clone());
    let expected = Side {
        name: "expected",
        ends: &expected,
    };
    match expectation.comparison.views.evaluate_within(
        observer,
        subject,
        &[expected],
        Some(DEFAULT_VIEW_BUDGET),
    ) {
        Ok(()) | Err(EndError::ViewStopped { .. }) => Ok(()),
        Err(error) => Err(format!("`expect.views`: {error}")),
    }
}

/// An `expect` table in the JSON data model, as krs-exec reads a case document's.
fn expectation_document(expect: &toml::Table) -> Result<Value, String> {
    krs_exec::toml_document(&toml::Value::Table(expect.clone())).map_err(|error| error.to_string())
}

/// What an end kink keeps under `[stop]` is (module documentation, "Expectations").
const HALT_UNDER_STOP: &str = "under [stop] an end kink keeps is stuck or stopped at a rule of \
     the stop";

/// Why the ends do not say an end's halt under `[stop]`, after [`HALT_UNDER_STOP`].
const HALT_UNOBSERVED: &str = "and the ends do not say which, since a run merges the paths that \
     reach one configuration";

/// How the check treats the expectation's halt (module documentation, "Expectations").
#[derive(Clone, Copy, PartialEq, Eq)]
enum HaltCheck {
    /// Without `[stop]`: every end is `stuck`, and the class is compared.
    Compared,
    /// Under `[stop]`, a halt no end has: unmet at the class, the baseline's class unstated.
    Decided,
    /// Under `[stop]`, a halt an end may have: only the cells are compared.
    Unobserved,
}

/// The definition a case runs on and the observer its expectation's views are evaluated in,
/// when it names one other than that definition.
struct Viewed<'a> {
    semantics: &'a mut Semantics,
    observer: Option<&'a mut Semantics>,
}

/// The check of `expectation` (whose `rule` is written `rule`) against the baseline's ends
/// `ends` (module documentation, "Expectations"), its views evaluated as `viewed` says.
fn checked_expectation(
    viewed: Viewed<'_>,
    expectation: &mut Expectation,
    rule: Option<&str>,
    ends: &BTreeSet<Pattern>,
    not_compared: &[String],
    stop: Option<&StopSection>,
) -> Result<CheckedExpectation, String> {
    let Viewed {
        semantics,
        observer,
    } = viewed;
    let expected = &expectation.end.class;
    let stuck = EndClass {
        halt: Halt::Stuck,
        rule: None,
    };
    // The class each end is read with, and how the halt is checked.
    let (class, halt) = match (expected.halt, stop) {
        (Halt::Stopped, None) => {
            return Ok(CheckedExpectation::inconclusive(format!(
                "the expectation's end is stopped at `{}`, and the corpus declares no [stop]: \
                 kink runs every program as the corpus says",
                rule.unwrap_or_default()
            )));
        }
        (Halt::Stopped, Some(stop)) => {
            let Some(rule) = rule else {
                return Ok(CheckedExpectation::inconclusive(
                    "the expectation's end is stopped, at a rule it does not name",
                ));
            };
            let selected = semantics
                .stop_rules(rule)
                .map_err(|error| error.to_string())?;
            if !selected
                .iter()
                .filter_map(|(_, label)| label.as_deref())
                .any(|label| stop.names(label))
            {
                return Ok(CheckedExpectation::inconclusive(format!(
                    "the expectation's end is stopped at `{rule}`, a rule the corpus's [stop] \
                     does not stop at"
                )));
            }
            (expected.clone(), HaltCheck::Unobserved)
        }
        (Halt::Stuck, Some(_)) => (expected.clone(), HaltCheck::Unobserved),
        (_, Some(_)) => (stuck, HaltCheck::Decided),
        (_, None) => (stuck, HaltCheck::Compared),
    };
    let cells = semantics.cells();
    let unstated = unstated(&cells, not_compared);
    let baseline = Ends {
        ends: read_ends(semantics, ends, &class, &unstated)?,
        incomplete: None,
    };
    let expected = Ends::one(expectation.end.clone());
    let expected = Side {
        name: "expected",
        ends: &expected,
    };
    let baseline = Side {
        name: "baseline",
        ends: &baseline,
    };
    if !expectation.comparison.views.is_empty() {
        let (observer, subject) = match observer {
            Some(observer) => (observer, Some(&*semantics)),
            None => (&mut *semantics, None),
        };
        let evaluated = expectation.comparison.views.evaluate_within(
            observer,
            subject,
            &[expected, baseline],
            Some(DEFAULT_VIEW_BUDGET),
        );
        if let Some(checked) = evaluation_verdict(evaluated)? {
            return Ok(naming_views(checked, expectation));
        }
    }
    let compared = semantics.check_expectation(&expectation.comparison, expected, baseline);
    checked(compared, halt).map(|checked| naming_views(checked, expectation))
}

/// What the evaluation of an expectation's views, `evaluated`, decides before the comparison
/// (module documentation, "Views"): nothing when every view has its values, an inconclusive
/// verdict for an evaluation that stopped before it ended, and the refusal of the case, as an
/// error, for a view without a value at an end (a baseline end, since admission refuses a case
/// whose view has no value at its expected end).
fn evaluation_verdict(
    evaluated: Result<(), EndError>,
) -> Result<Option<CheckedExpectation>, String> {
    match evaluated {
        Ok(()) => Ok(None),
        Err(error @ EndError::ViewStopped { .. }) => {
            Ok(Some(CheckedExpectation::inconclusive(error.to_string())))
        }
        Err(error) => Err(format!(
            "a view refuses the case, as `krs run --case` refuses it: {error}"
        )),
    }
}

/// `checked`, a verdict reached through the values of the views `expectation` applies, with its
/// detail naming them, and the observer they were evaluated in when it names one.
fn naming_views(mut checked: CheckedExpectation, expectation: &Expectation) -> CheckedExpectation {
    if expectation.views.is_empty() {
        return checked;
    }
    let listed = expectation
        .views
        .iter()
        .map(|(cell, function)| format!("`{cell}` = `{function}`"))
        .collect::<Vec<_>>()
        .join(", ");
    let views = match &expectation.observer {
        Some(observer) => format!("views: {listed}, in `{observer}`"),
        None => format!("views: {listed}"),
    };
    checked.detail = Some(match checked.detail.take() {
        Some(detail) => format!("{detail}; {views}"),
        None => views,
    });
    checked
}

/// The verdict of `compared`, krs-exec's check of the expectation, whose halt is checked by
/// `halt` (module documentation, "Expectations").
fn checked(
    compared: Result<Compared, EndError>,
    halt: HaltCheck,
) -> Result<CheckedExpectation, String> {
    let detail = match halt {
        HaltCheck::Compared => None,
        HaltCheck::Decided => Some(format!(
            "the halt is compared: {HALT_UNDER_STOP}, and the expectation's end is neither"
        )),
        HaltCheck::Unobserved => Some(format!(
            "the halt is not compared: {HALT_UNDER_STOP}, {HALT_UNOBSERVED}"
        )),
    };
    Ok(match compared {
        Err(error @ EndError::MissingCell { .. }) => CheckedExpectation::inconclusive(format!(
            "{error}: the ends kink keeps leave out the cells the corpus does not compare \
             ([result], unobservable cells)"
        )),
        Err(error) => return Err(error.to_string()),
        Ok(Compared::Equal) if halt == HaltCheck::Unobserved => {
            CheckedExpectation::inconclusive(format!(
                "every end agrees with the expectation on the compared cells, but its halt is not \
                 observed: {HALT_UNDER_STOP}, {HALT_UNOBSERVED}"
            ))
        }
        Ok(Compared::Equal) => CheckedExpectation {
            verdict: ExpectationVerdict::Met,
            detail,
            difference: None,
        },
        Ok(Compared::Differs(difference)) => {
            let mut document =
                serde_json::to_value(&*difference).map_err(|error| error.to_string())?;
            if halt != HaltCheck::Compared
                && let Some(side) = document["right"].as_object_mut()
            {
                side.remove("class");
            }
            CheckedExpectation {
                verdict: ExpectationVerdict::Unmet,
                detail,
                difference: Some(document),
            }
        }
        Ok(Compared::Inconclusive(reason)) => CheckedExpectation::inconclusive(reason),
    })
}

/// The cells of `cells` that `not_compared` (by K cell name) leaves out.
fn unstated<'c>(cells: &'c [CellInfo], not_compared: &[String]) -> Vec<&'c CellInfo> {
    let labels = not_compared
        .iter()
        .map(|name| format!("<{name}>"))
        .collect::<BTreeSet<_>>();
    cells
        .iter()
        .filter(|cell| labels.contains(&label_or_name(&cell.symbol)))
        .collect()
}

/// Each configuration of `set` read as an end of class `class`, the cells of `unstated` not
/// stated.
fn read_ends(
    semantics: &Semantics,
    set: &BTreeSet<Pattern>,
    class: &EndClass,
    unstated: &[&CellInfo],
) -> Result<Vec<End>, String> {
    let symbols = unstated
        .iter()
        .map(|cell| cell.symbol.as_str())
        .collect::<BTreeSet<_>>();
    set.iter()
        .map(|configuration| {
            semantics
                .read_configuration(configuration, class.clone(), &symbols)
                .map_err(|error| format!("an end does not read as the definition's: {error}"))
        })
        .collect()
}

/// The krs-exec comparison of the slot's two sets of ends (module documentation).
fn difference(
    semantics: &Semantics,
    baseline: &BTreeSet<Pattern>,
    mutant: &BTreeSet<Pattern>,
    mutant_complete: bool,
    not_compared: &[String],
) -> Result<Value, String> {
    let cells = semantics.cells();
    let unstated = unstated(&cells, not_compared);
    let stuck = EndClass {
        halt: Halt::Stuck,
        rule: None,
    };
    let baseline = Ends {
        ends: read_ends(semantics, baseline, &stuck, &unstated)?,
        incomplete: None,
    };
    let mutant = Ends {
        ends: read_ends(semantics, mutant, &stuck, &unstated)?,
        incomplete: (!mutant_complete).then(|| {
            "the mutant's run reached its work budget: these are the ends of its explored complete \
             paths that killed"
                .to_owned()
        }),
    };
    // The observable leaf cells the ends state: every one unless the slot left some out.
    let left_out = |path: &str| {
        unstated.iter().any(|cell| {
            path == cell.path
                || path
                    .strip_prefix(cell.path.as_str())
                    .is_some_and(|rest| rest.starts_with('.'))
        })
    };
    let compare = (!unstated.is_empty()).then(|| {
        cells
            .iter()
            .filter(|cell| cell.ty.is_some() && !cell.unobservable && !left_out(&cell.path))
            .map(|cell| cell.path.clone())
            .collect::<Vec<_>>()
    });
    let comparison = Comparison {
        compare,
        ..Comparison::default()
    };
    let compared = semantics
        .compare_ends(
            &comparison,
            Side {
                name: "baseline",
                ends: &baseline,
            },
            Side {
                name: "mutant",
                ends: &mutant,
            },
        )
        .map_err(|error| error.to_string())?;
    evidence(compared, mutant_complete)
}

/// The SHA-256 of `definition`'s JSON without its provenance tables (module documentation), in
/// lowercase hexadecimal.
pub(crate) fn definition_digest(
    definition: &krs_ir_levels::DefinitionIr,
) -> Result<String, String> {
    let mut value = serde_json::to_value(definition)
        .map_err(|error| format!("the Definition IR does not serialize: {error}"))?;
    if let Some(root) = value.as_object_mut() {
        root.remove(krs_ir::provenance_table::PROVENANCE_FIELD);
    }
    let bytes = serde_json::to_vec(&value).map_err(|error| error.to_string())?;
    Ok(krs_ir::identity::lower_hex(&Sha256::digest(&bytes)))
}

/// The evidence of the kill whose ends krs-exec compared as `compared`, or why there is none.
///
/// Both sides have ends, and every end has the class `stuck`, so the comparison is inconclusive
/// only where the side it needs complete is not: no end of the mutant lies outside the
/// baseline's ends in the cells the definition declares, and the baseline's ends are not all
/// among an incomplete mutant's. The slot's kill of an incomplete mutant is a mutant end outside
/// the baseline's set (a baseline end the mutant's explored paths lack proves nothing), so there,
/// as for equal ends of two complete sides, the slot's difference lies in a cell compilation adds.
fn evidence(compared: Compared, mutant_complete: bool) -> Result<Value, String> {
    match compared {
        Compared::Differs(difference) => {
            let mut document =
                serde_json::to_value(&*difference).map_err(|error| error.to_string())?;
            // The renderer was given no class (module documentation): the sides state none.
            for side in ["left", "right"] {
                if let Some(side) = document[side].as_object_mut() {
                    side.remove("class");
                }
            }
            Ok(document)
        }
        Compared::Equal => Err(
            "the ends are equal in every cell the definition declares: the slot's difference is \
             in a cell of compilation's"
                .to_owned(),
        ),
        Compared::Inconclusive(_) if !mutant_complete => Err(
            "every end of the mutant's explored paths agrees with a baseline end in every cell \
             the definition declares: the slot's difference is in a cell of compilation's"
                .to_owned(),
        ),
        Compared::Inconclusive(reason) => Err(reason),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use krs_exec::{Difference, DifferenceAt, DifferenceSide};

    fn side(name: &str, complete: bool) -> DifferenceSide {
        DifferenceSide {
            name: name.to_owned(),
            ends: 1,
            complete,
            class: EndClass {
                halt: Halt::Stuck,
                rule: None,
            },
            value: None,
        }
    }

    /// A difference keeps krs-exec's document but states no class; equal ends, and an
    /// inconclusive comparison of an incomplete mutant, place the slot's difference in a cell
    /// compilation adds; another inconclusive comparison keeps krs-exec's reason.
    #[test]
    fn the_evidence_states_no_class_and_names_why_it_has_none() {
        let difference = Difference {
            format: DIFFERENCE_FORMAT,
            at: DifferenceAt::Cell,
            cell: Some("k".to_owned()),
            path: Some("k[0]".to_owned()),
            segments: vec!["[0]".to_owned()],
            outside: "mutant".to_owned(),
            also_differ: Vec::new(),
            compared: vec!["k".to_owned()],
            not_compared: Vec::new(),
            views: std::collections::BTreeMap::new(),
            left: side("baseline", true),
            right: side("mutant", false),
        };
        let document = evidence(Compared::Differs(Box::new(difference)), false).unwrap();
        assert_eq!(document["format"], DIFFERENCE_FORMAT);
        assert_eq!(document["path"], "k[0]");
        for name in ["left", "right"] {
            assert_eq!(document[name].get("class"), None, "{document:#}");
            assert!(document[name].get("complete").is_some(), "{document:#}");
        }
        for complete in [true, false] {
            assert!(
                evidence(Compared::Equal, complete)
                    .unwrap_err()
                    .ends_with("the slot's difference is in a cell of compilation's")
            );
        }
        let incomplete = Compared::Inconclusive("the mutant side's ends are incomplete".into());
        let reason = evidence(incomplete.clone(), false).unwrap_err();
        assert!(reason.starts_with("every end of the mutant's explored paths agrees"));
        assert!(reason.ends_with("the slot's difference is in a cell of compilation's"));
        assert_eq!(
            evidence(incomplete, true).unwrap_err(),
            "the mutant side's ends are incomplete"
        );
    }

    /// A view's evaluation that stopped makes the expectation inconclusive, with the stop as its
    /// detail; one without a value at a baseline end refuses the case, which the check reports as
    /// an error; and a verdict reached through the views' values names them, after the detail it
    /// had.
    #[test]
    fn a_stopped_view_is_inconclusive_and_a_refused_one_refuses() {
        assert_eq!(evaluation_verdict(Ok(())), Ok(None));
        let stopped = EndError::ViewStopped {
            cell: "bus".to_owned(),
            function: "Spin".to_owned(),
            message: "at the baseline end's `bus`, the budget is spent".to_owned(),
        };
        let reason = stopped.to_string();
        let checked = evaluation_verdict(Err(stopped)).unwrap().unwrap();
        assert_eq!(checked, CheckedExpectation::inconclusive(reason));
        let refused = EndError::View {
            cell: "bus".to_owned(),
            function: "OnlyZero".to_owned(),
            message: "it has no value at the baseline end's `bus`".to_owned(),
        };
        let message = refused.to_string();
        let error = evaluation_verdict(Err(refused)).unwrap_err();
        assert!(error.starts_with("a view refuses the case"), "{error}");
        assert!(error.ends_with(&message), "{error}");

        let expectation = |observer: Option<&str>| Expectation {
            end: End {
                class: EndClass {
                    halt: Halt::Stuck,
                    rule: None,
                },
                cells: krs_exec::EndCells::default(),
            },
            comparison: Comparison::default(),
            views: std::iter::once(("bus".to_owned(), "Count".to_owned())).collect(),
            observer: observer.map(str::to_owned),
        };
        let met = CheckedExpectation {
            verdict: ExpectationVerdict::Met,
            detail: None,
            difference: None,
        };
        assert_eq!(
            naming_views(met, &expectation(None)).detail.as_deref(),
            Some("views: `bus` = `Count`")
        );
        let stopped = CheckedExpectation::inconclusive("stopped");
        assert_eq!(
            naming_views(stopped, &expectation(Some("obs:main")))
                .detail
                .as_deref(),
            Some("stopped; views: `bus` = `Count`, in `obs:main`")
        );
    }
}
