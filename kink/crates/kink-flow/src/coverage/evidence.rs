//! The evidence of an argued item's invariant on the corpus's runs (module documentation of
//! [`crate::coverage`], "Argued obligations"): whether the invariant holds at every state of the
//! baseline's runs where the item's rule can match ([`evidence`]).
//!
//! # Which states
//!
//! The connection shows, at each axiom of the item's rule, that a state the left-hand side `L`
//! matches and the invariant `F` holds of does not have the item's valuation. Its premise is that
//! `F` holds at every reachable state `L` matches, and the evidence tests that premise on the
//! corpus's runs. A state of a path where `L` matches is one of:
//! - a state before a step whose successor is defined: the rule that takes it matches the state
//!   too, so its left-hand side unifies with `L` (kink-native `invariant::stepping_rules`), and the
//!   state is before a step of a rule of `S_R`, the rules whose left-hand side unifies with one of
//!   the item's axioms';
//! - an end: no rule steps there, or a stop ends the path there;
//! - the state before a step whose result is undefined, the last of its path, which is no end and
//!   no point;
//! - the state at which a bound cut the path.
//!
//! The evidence reads the first two kinds: before every step of `S_R`, and at every end. `S_R`
//! holds the item's own rules, and the other states it adds are reachable states too. It reads no
//! state of the last two, so a run with an undefined step, or a prefix program's run (a bound
//! cut it), leaves the evidence incomplete, and so does a rule of `S_R` with no label, whose
//! steps a run cannot observe. The initial state is read as well: it is the base case of the
//! inductive argument the invariant stands for.
//!
//! # The runs
//!
//! Each invariant is read on one evidence run per comparable or `comparable-prefix` program: the
//! program's baseline run with the corpus's `[stop]` and budget, observing only one point class
//! per label of the union of its entries' `S_R` (each on its before side, every event an
//! element), whose content is `F` evaluated in the baseline definition (kink-native
//! `invariant::evaluate`; an element is decided only at a ground `true` or `false`). `F` is read at
//! the initial configuration and at each end of the run, its terminal values, in the same way.
//! The corpus's own `[observe]` plays no part, and no invariant channel takes part in a
//! comparison: the evidence run is a run of its own, and its record is not the program's result
//! record.
//!
//! The budget's `time_ms` bounds the program's run, not the evidence's reading of it: each
//! evaluation of `F` is off the run's clock (kink-native `execution::off_the_clock`). Charging
//! the evaluations to the run would make the evidence of a program the baseline ran within its
//! bound depend on `F`'s cost on the host. Each evaluation, at a point, at the initial state and
//! at an end, is bounded by its own work bound instead, kink-native
//! `invariant::EVALUATION_POLLS` polls of the backend's interruption point (kink-native
//! `invariant`, "The work bound"). The simplifier's iteration budget alone bounds nothing here:
//! it does not count a determined step of a ground function application (k-rust-backend
//! `simplify`), and an evaluation is of ground cells. The bound is spent by the evaluation's own
//! polls, so an evaluation that spends it is undecided as a function of the cells, the
//! definition and the bound, and the reason names the bound; such a state leaves the evidence
//! `incomplete`, never `fails`. The bound is per evaluation, not a total of the run: the value at
//! a state is then a function of that state's cells alone, whatever the evaluations before it
//! cost, and the run reads at most one evaluation per point, its initial state and its ends,
//! which its own depth bounds, so the run's reading ends without the watchdog's help, and its
//! states are those of the run the baseline admitted within `time_ms`. A run the watchdog stops
//! all the same gives no evidence, and the reason says so, with the evaluations' count and time.
//! Where every cell holds the term node the previous decided evaluation read, the value is that
//! evaluation's (the `Evaluator`).
//!
//! Only states of real, clean paths count. An element the run's observation record keeps was read
//! at a real state of a path with no diagnostic (kink-campaign `observation`, "The slot"); a record
//! of several paths counts only where it is real. A comparable program's run is complete with no
//! diagnostic and ends at values, so its initial state and ends are states of its paths; a
//! prefix program's run kept an element of the corpus's channels, which only a settled path does.
//! A record of several paths keeps each channel's prefix sets and only the nearest index at which
//! some path stops being explored (cut, undecided, or at an undecided element): where it has one,
//! what the other paths hold past their own such point is not known, and the channel is
//! undecided.
//!
//! The failure is the first state that gives `false` in path order: the initial state, then the
//! steps, then the ends. In a run of one path the run's functions log every evaluation in path
//! order with the cells read there, and where that log is the record's elements, the first
//! `false` it holds is the path's first, with the event's cells; otherwise, and in a run of
//! several paths, whose record orders no state across rules, it is the first `false` of the first
//! rule in label order that has one, and the failure says why its cells are not given
//! (`cells_missing`).
//!
//! # Answers
//!
//! For an argued item, over every program:
//! - `fails`: some state read gives `false`; the failure names the program, where (`initial`,
//!   before the step of a rule, or an `end`), the rule's arrival index or the end's index, and the
//!   cells read there as KORE, or why they are not known;
//! - `incomplete`: otherwise, where some state of the item's set is undecided, a program is not
//!   comparable (or its evidence run gave no sides), or a rule of the item's `S_R` cannot be
//!   observed;
//! - `holds`: every state read gives `true`, and some state is before a step of the item's `S_R`;
//! - `vacuous`: every state read gives `true`, and none is before a step of the item's `S_R`.
//!
//! # The cache
//!
//! What one program's evidence run reads of an invariant is kept in the evidence memo
//! ([`crate::memo::evidence_key`]) under the program's result key, the invariant's identity and
//! the labels observed, where the result store is on (`crate::results::result_store`) and the
//! run's campaign gave it sides; `--verify` reads and writes no record. The record is a function
//! of those and of kink's build, which fixes the work bound, except where an evaluation's outcome
//! was the host's (kink-native `invariant::Unvalued::host_bound`: the native stack ran out, or the
//! system refused one): such a record is not kept.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, PoisonError};
use std::time::{Duration, Instant};

use k_rust::k_rust_backend::definition::BackendDefinition;
use k_rust::k_rust_backend::rewrite::{CellHandle, ProbeState};
use k_rust::kore::ast::Pattern;
use k_rust::kore::printer::Printer;
use kink_campaign::{
    BaselineRecord, ChannelEnd, Evaluated, Observation, ObservationEvaluator, ObservationFunctions,
    ObserveFunctions, Opening, PathRecord, PrefixChain, Stutter, TestEvidence,
};
use kink_native::invariant::{
    EVALUATION_POLLS, Invariant, Unvalued, evaluate, evaluate_configuration, stepping_rules,
};
use kink_patch::payload_digest;
use serde_json::{Value, json};

use super::ARGUED;
use super::invariants::{CONNECTION_FAILS, ResolvedInvariant};
use crate::admit::{AdmittedSpec, InputSession};
use crate::digest::ExecutionDigest;
use crate::manifest::{FlowManifest, ObserveFunctionsSlot, ObserveSection, PointSection};
use crate::memo;
use crate::results::{BaselineRunner, ResultClass, ResultsUpdate, result_key, result_store};

/// The evidence of an item every state of whose set gives `true`, one of them before a step of its
/// `S_R`.
pub const EVIDENCE_HOLDS: &str = "holds";
/// The evidence of an item every state of whose set gives `true`, none before a step of its `S_R`.
pub const EVIDENCE_VACUOUS: &str = "vacuous";
/// The evidence of an item some state read gives `false` at.
pub const EVIDENCE_FAILS: &str = "fails";
/// The evidence of an item neither shown to fail nor read at every state of its set.
pub const EVIDENCE_INCOMPLETE: &str = "incomplete";

/// The domain of an element's digest: `true` and `false`, the only values an element has.
const ELEMENT_DOMAIN: &str = "kink-flow/invariant-evidence/element/v1";

/// The digest of the element `value`.
fn element_digest(value: bool) -> [u8; 32] {
    *payload_digest(ELEMENT_DOMAIN, if value { b"true" } else { b"false" }).as_bytes()
}

/// The 8 bytes of `value`'s digest a record keeps.
fn short(value: bool) -> [u8; 8] {
    let mut bytes = [0; 8];
    bytes.copy_from_slice(&element_digest(value)[..8]);
    bytes
}

/// Each evidence run's own functions are a declaration of their own: two runs never share the
/// evaluations one of them logs (`Observe` interns a declaration by its identity).
static RUNS: AtomicU64 = AtomicU64::new(0);

/// One evaluation of an evidence run's functions, in the order the run's requests asked them: its
/// point class and its value.
struct Logged {
    class: usize,
    value: Value3,
}

/// The value of one evaluation: `true`, `false` with the cells read there as KORE text, or not
/// known, with why.
#[derive(Clone)]
enum Value3 {
    True,
    False(Vec<String>),
    Undecided(String),
}

/// The value of an evaluation at an initial state or an end: with its cells, or why it is not
/// known, and whether the host decided that.
type Valued = Result<(bool, Vec<Pattern>), Unvalued>;

#[derive(Default)]
struct Log {
    requests: usize,
    entries: Vec<Logged>,
    /// The evaluations of the invariant the run's functions made, and the time they took: an
    /// element whose cells are the previous evaluation's is not evaluated again ([`Evaluator`]).
    evaluations: usize,
    evaluating: Duration,
    /// Whether an evaluation's outcome was the host's (module documentation, "The cache").
    host_bound: bool,
}

/// The invariant as the functions of an evidence run's declaration (module documentation, "The
/// runs"): every point's content is the invariant's value, evaluated in the baseline definition.
struct Functions {
    definition: Arc<BackendDefinition>,
    symbol: String,
    cells: Vec<Vec<String>>,
    log: Arc<Mutex<Log>>,
}

impl ObservationFunctions for Functions {
    fn cells(&self) -> &[Vec<String>] {
        &self.cells
    }

    fn filtered(&self, _: usize) -> bool {
        false
    }

    fn with_evaluator(
        &self,
        body: &mut dyn FnMut(&mut dyn ObservationEvaluator),
    ) -> Result<(), String> {
        self.log
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .requests += 1;
        body(&mut Evaluator {
            functions: self,
            last: None,
        });
        Ok(())
    }
}

/// The evaluation of one request of an evidence run. The invariant's value is a function of the
/// cells it reads, and its evaluation on the proof route with no solver is a function of their
/// terms; a step that does not rewrite a cell keeps its term node. So where every cell holds the
/// node the previous decided evaluation read (`last`), the value is that evaluation's, and is not
/// evaluated again: the points of the rules of one instruction, before which no step rewrote
/// memory, read one map. An undecided evaluation is not reused: a stop of the run that ended it
/// says nothing about the cells.
struct Evaluator<'f> {
    functions: &'f Functions,
    last: Option<(Vec<CellHandle>, Value3)>,
}

impl Evaluator<'_> {
    fn log(&self, class: usize, value: Value3, evaluated: Option<Duration>) {
        let mut log = self
            .functions
            .log
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        if let Some(took) = evaluated {
            log.evaluations += 1;
            log.evaluating += took;
        }
        log.entries.push(Logged { class, value });
    }

    /// The element of a decided `value`, with its value where `value` is asked.
    fn element(holds: bool, value: bool) -> Evaluated {
        Evaluated {
            digest: element_digest(holds),
            value: value.then(|| json!(holds)),
        }
    }
}

impl ObservationEvaluator for Evaluator<'_> {
    fn holds(&mut self, _: usize, _: &ProbeState<'_>) -> Option<Result<bool, String>> {
        None
    }

    /// The invariant's value at `state`, read off the run's clock: the run's time bound bounds
    /// the program's run, and each evaluation is bounded by its own work bound (module
    /// documentation, "The runs").
    fn content(
        &mut self,
        class: usize,
        state: &ProbeState<'_>,
        value: bool,
    ) -> Result<Evaluated, String> {
        kink_native::execution::off_the_clock(|| self.read(class, state, value))
    }

    fn elements(&mut self, _: usize, _: &Pattern, _: bool) -> Result<Vec<Evaluated>, String> {
        Err("an evidence run declares no log".to_owned())
    }

    fn item_digest(&mut self, item: &Pattern) -> [u8; 32] {
        *payload_digest(
            ELEMENT_DOMAIN,
            Printer::compact().print_pattern(item).as_bytes(),
        )
        .as_bytes()
    }
}

impl Evaluator<'_> {
    /// [`ObservationEvaluator::content`], off the run's clock.
    fn read(
        &mut self,
        class: usize,
        state: &ProbeState<'_>,
        value: bool,
    ) -> Result<Evaluated, String> {
        let functions = self.functions;
        let paths = functions
            .cells
            .iter()
            .map(|path| path.iter().map(String::as_str).collect::<Vec<_>>())
            .collect::<Vec<_>>();
        let handles = paths
            .iter()
            .map(|path| state.cell_handle(path))
            .collect::<Option<Vec<_>>>();
        if let (Some(handles), Some((read, logged))) = (&handles, &self.last)
            && handles.len() == read.len()
            && handles.iter().zip(read).all(|(now, then)| now.same(then))
        {
            let logged = logged.clone();
            let holds = matches!(logged, Value3::True);
            self.log(class, logged, None);
            return Ok(Self::element(holds, value));
        }
        let cells = handles
            .as_ref()
            .map(|handles| handles.iter().map(CellHandle::kore).collect::<Vec<_>>());
        let started = Instant::now();
        let answer = match &cells {
            None => Err("the state holds no cell the invariant reads".to_owned()),
            Some(cells) => evaluate(
                &functions.definition,
                &cells.iter().collect::<Vec<_>>(),
                Invariant {
                    symbol: &functions.symbol,
                    cells: &functions.cells,
                },
                EVALUATION_POLLS,
            )
            .map_err(|unvalued| {
                if unvalued.host_bound {
                    functions
                        .log
                        .lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .host_bound = true;
                }
                unvalued.reason
            }),
        };
        let took = started.elapsed();
        match answer {
            Ok(holds) => {
                // The cells of the event itself, where it gives `false`.
                let logged = if holds {
                    Value3::True
                } else {
                    Value3::False(
                        cells
                            .iter()
                            .flatten()
                            .map(|cell| Printer::compact().print_pattern(cell))
                            .collect(),
                    )
                };
                self.last = handles.map(|handles| (handles, logged.clone()));
                self.log(class, logged, Some(took));
                Ok(Self::element(holds, value))
            }
            Err(reason) => {
                self.last = None;
                self.log(class, Value3::Undecided(reason.clone()), Some(took));
                Err(reason)
            }
        }
    }
}

/// The rules of an argued item's `S_R`: the labels a run observes them by, and the ids of those
/// that have none.
#[derive(Clone, Debug, Default)]
struct Steps {
    labels: BTreeSet<String>,
    unlabeled: BTreeSet<String>,
}

/// What [`evidence`] gives: each argued item's evidence by id, and the summary's
/// `invariant_runs`.
pub(super) struct Evidence {
    pub(super) items: BTreeMap<String, Value>,
    pub(super) runs: Value,
}

/// The inputs of the evidence runs of one command.
pub(super) struct Context<'c, 'i> {
    pub(super) spec: &'c AdmittedSpec,
    pub(super) manifest: &'c FlowManifest,
    pub(super) update: &'c ResultsUpdate,
    pub(super) inputs: &'c mut InputSession<'i>,
    pub(super) depth: std::num::NonZeroU64,
    pub(super) execution: &'c ExecutionDigest,
    pub(super) cache: &'c Path,
    pub(super) verify: bool,
}

/// The evidence of each argued item of the derived document `probe` whose entry names an
/// invariant of `resolved` and whose connection (`checks`, by item id) does not fail (module
/// documentation): `{status, rules, states, steps, programs, failure, reason, cached}` by item
/// id, and `invariant_runs`, `{run, cached}`, the evidence runs this command ran and read from
/// the memo.
pub(super) fn evidence(
    probe: &Value,
    resolved: &BTreeMap<String, (ResolvedInvariant, Value)>,
    checks: &Value,
    context: &mut Context<'_, '_>,
) -> Evidence {
    let manifest = context.manifest;
    let definition = match &context.spec.definition {
        Ok(definition) => Some(Arc::clone(definition)),
        Err(_) => None,
    };
    // Each argued item that rests on an invariant, with its rule's axioms.
    let mut items = BTreeMap::<String, (String, Result<Steps, String>)>::new();
    for entry in &manifest.coverage.argued {
        let Some(invariant) = &entry.invariant else {
            continue;
        };
        let argued = ["rules", "requirements"].into_iter().any(|family| {
            probe["families"][family]["items"]
                .as_array()
                .into_iter()
                .flatten()
                .any(|item| item["id"] == entry.item.as_str() && item["status"] == ARGUED)
        });
        let connection = &checks[entry.item.as_str()]["connection"];
        if !argued || connection.is_null() || connection["status"] == CONNECTION_FAILS {
            continue;
        }
        let axioms = connection["axioms"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(|axiom| axiom["axiom"].as_str().map(str::to_owned))
            .collect::<BTreeSet<_>>();
        let steps = match &definition {
            None => Err("the baseline definition cannot be read".to_owned()),
            Some(_) if axioms.is_empty() => Err("the item names no axiom".to_owned()),
            Some(definition) => stepping_rules(definition, &axioms)
                .map(|rules| {
                    let mut steps = Steps::default();
                    for rule in rules {
                        match rule.label {
                            Some(label) => steps.labels.insert(label),
                            None => steps.unlabeled.insert(rule.unique_id),
                        };
                    }
                    steps
                })
                .map_err(|refusal| refusal.to_string()),
        };
        items.insert(entry.item.clone(), (invariant.clone(), steps));
    }
    let mut runs = (0_usize, 0_usize);
    let mut read = BTreeMap::<String, Vec<Read>>::new();
    let invariants = items
        .values()
        .map(|(invariant, _)| invariant.clone())
        .collect::<BTreeSet<_>>();
    for name in &invariants {
        let (Some((invariant, identity)), Some(definition)) = (resolved.get(name), &definition)
        else {
            continue;
        };
        let labels = items
            .values()
            .filter(|(of, _)| of == name)
            .filter_map(|(_, steps)| steps.as_ref().ok())
            .flat_map(|steps| steps.labels.iter().cloned())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        read.insert(
            name.clone(),
            program_evidence(context, definition, invariant, identity, &labels, &mut runs),
        );
    }
    let items = items
        .into_iter()
        .map(|(id, (invariant, steps))| {
            let value = item_evidence(&steps, read.get(&invariant).map(Vec::as_slice));
            (id, value)
        })
        .collect();
    Evidence {
        items,
        runs: json!({"run": runs.0, "cached": runs.1}),
    }
}

/// What one program's evidence run read of an invariant: the program's id, the record or why the
/// program gives none, and whether the record was read from the memo.
type Read = (String, Result<Value, String>, bool);

/// What each program's evidence run read of `invariant` at the points of `labels`, each run
/// counted in `runs` (run, cached).
fn program_evidence(
    context: &mut Context<'_, '_>,
    definition: &Arc<BackendDefinition>,
    invariant: &ResolvedInvariant,
    identity: &Value,
    labels: &[String],
    runs: &mut (usize, usize),
) -> Vec<Read> {
    let manifest = context.manifest;
    let log = Arc::new(Mutex::new(Log::default()));
    let runner_manifest = (!labels.is_empty()).then(|| {
        let functions = Functions {
            definition: Arc::clone(definition),
            symbol: invariant.symbol.clone(),
            cells: invariant.cells.clone(),
            log: Arc::clone(&log),
        };
        let functions = ObserveFunctions::new(
            json!({
                "evidence": identity,
                "run": RUNS.fetch_add(1, Ordering::Relaxed),
            }),
            Arc::new(functions),
        );
        let mut observed = manifest.clone();
        observed.observe = Some(ObserveSection {
            points: labels
                .iter()
                .map(|label| PointSection {
                    name: label.clone(),
                    before: vec![label.clone()],
                    after: Vec::new(),
                    stutter: Stutter::Count,
                    cells: Vec::new(),
                    front_end: BTreeMap::new(),
                })
                .collect(),
            logs: Vec::new(),
            observer: None,
        });
        observed.observe_functions = ObserveFunctionsSlot(Some(functions));
        observed
    });
    let runner = runner_manifest
        .as_ref()
        .map(|observed| BaselineRunner::with_depth(context.spec, observed, context.depth));
    let build = kink_campaign::kink_build()
        .ok()
        .filter(|_| !context.verify && result_store(manifest.budget.backend_options()).is_ok());
    let store = kink_corpus::Store::new(context.cache.to_path_buf());
    let asked = Invariant {
        symbol: &invariant.symbol,
        cells: &invariant.cells,
    };
    let mut programs = Vec::new();
    for (program, row) in manifest.programs.iter().zip(&context.update.rows) {
        let class = row.row["class"].as_str().unwrap_or("error");
        if !ResultClass::can_kill(&json!(class)) {
            programs.push((
                program.id.clone(),
                Err(format!("the program `{}` is {class}", program.id)),
                false,
            ));
            continue;
        }
        let (Some(digest), Some(case)) = (row.digest, row.inputs.as_ref()) else {
            programs.push((
                program.id.clone(),
                Err(format!("the program `{}` has no inputs", program.id)),
                false,
            ));
            continue;
        };
        let key = build.map(|build| {
            let result = result_key(
                *context.execution,
                digest,
                manifest.budget,
                Some(build),
                manifest.program_stop(program),
                manifest
                    .syntax
                    .as_ref()
                    .map(crate::manifest::SyntaxSelection::key_value),
                manifest.observe_value(),
            );
            memo::evidence_key(&result, identity, labels)
        });
        let path = key
            .as_ref()
            .map(|key| memo::evidence_path(context.cache, key));
        if let (Some(key), Some(path)) = (&key, &path)
            && let Some(record) = memo::read_evidence(path, key)
        {
            runs.1 += 1;
            programs.push((program.id.clone(), Ok(record), true));
            continue;
        }
        let test = match row.test.clone() {
            Some(test) => test,
            None => match context.inputs.test_case(program, case) {
                Ok(test) => test,
                Err(refusal) => {
                    programs.push((
                        program.id.clone(),
                        Err(format!(
                            "the program `{}` is refused: {}",
                            program.id, refusal.detail
                        )),
                        false,
                    ));
                    continue;
                }
            },
        };
        let initial =
            evaluate_configuration(definition, &test.initial_state, asked, EVALUATION_POLLS);
        let observed = match &runner {
            None => Ok(None),
            Some(Err(reason)) => Err(reason.clone()),
            Some(Ok(runner)) => {
                *log.lock().unwrap_or_else(PoisonError::into_inner) = Log::default();
                runs.0 += 1;
                runner.evidence_of(test).map(Some)
            }
        };
        let evidence = match observed {
            Ok(evidence) => evidence,
            Err(reason) => {
                // How many evaluations of the invariant the run made before it failed, and
                // their time, off the run's clock: what the reading cost, beside the run's cause.
                let log = std::mem::take(&mut *log.lock().unwrap_or_else(PoisonError::into_inner));
                let evaluated = if log.evaluations == 0 {
                    String::new()
                } else {
                    format!(
                        "; the run evaluated the invariant {} times, for {} ms",
                        log.evaluations,
                        crate::results::millis(log.evaluating)
                    )
                };
                programs.push((
                    program.id.clone(),
                    Err(format!(
                        "the evidence run of the program `{}` failed: {reason}{evaluated}",
                        program.id
                    )),
                    false,
                ));
                continue;
            }
        };
        let logged = std::mem::take(&mut *log.lock().unwrap_or_else(PoisonError::into_inner));
        let (record, host_bound) = record(
            definition,
            asked,
            labels,
            initial,
            evidence.as_ref(),
            ResultClass::ComparablePrefix.as_str() == class,
            &logged,
        );
        // A record an outcome of the host's decided is no function of its key (module
        // documentation, "The cache").
        if let (Some(key), Some(path)) = (&key, &path)
            && !host_bound
        {
            memo::write_evidence(&store, path, key, &record);
        }
        programs.push((program.id.clone(), Ok(record), false));
    }
    programs
}

/// What one program's evidence run read (module documentation, "The runs"): `{channels: [{rule,
/// steps, undecided}], ends, undecided, failure}`, a channel per label of `labels` with the number
/// of states read before its rule's steps and why one was not decided, the number of ends read,
/// why a state of the run itself was not decided (its initial state, an end, an undefined step, a
/// bound's cut, its paths), and the first state that gives `false` ([`failure`]). `initial` is
/// the value at the initial state with its cells; `evidence` the run's (`None`: no rule was
/// observed, so no run was made, and no end is read); `prefix` whether the program is a prefix
/// program; `logged` the evaluations the run's functions logged. Also whether an evaluation's
/// outcome was the host's (module documentation, "The cache").
fn record(
    definition: &BackendDefinition,
    invariant: Invariant<'_>,
    labels: &[String],
    initial: Valued,
    evidence: Option<&TestEvidence>,
    prefix: bool,
    logged: &Log,
) -> (Value, bool) {
    let mut undecided = None;
    let mut failure = Value::Null;
    let mut host_bound = logged.host_bound;
    match initial {
        Ok((true, _)) => {}
        Ok((false, cells)) => failure = failure_value("initial", None, None, Ok(texts(&cells))),
        Err(unvalued) => {
            host_bound |= unvalued.host_bound;
            undecided = Some(format!("at the initial state: {unvalued}"));
        }
    }
    let mut channels = labels
        .iter()
        .map(|label| json!({"rule": label, "steps": 0, "undecided": null}))
        .collect::<Vec<_>>();
    let Some(evidence) = evidence else {
        return (
            json!({"channels": channels, "ends": 0, "undecided": undecided,
                   "failure": failure}),
            host_bound,
        );
    };
    if prefix {
        // The state a bound cut the path at is reached, and the item's rule may match it; the
        // record keeps no state of it.
        undecided.get_or_insert_with(|| {
            "a bound cut the run at a state the evidence does not read".to_owned()
        });
    }
    if evidence.undefined_steps {
        undecided.get_or_insert_with(|| {
            "a path ends at an undefined step, whose state the evidence does not read".to_owned()
        });
    }
    match &evidence.notes.observation {
        Some(Observation::Recorded(record)) => {
            let step = match &record.paths {
                None => one_path(record, prefix, labels, &mut channels, logged),
                Some(paths) => several_paths(paths, labels, &mut channels, &mut undecided),
            };
            if failure.is_null() {
                failure = step;
            }
        }
        _ => {
            undecided.get_or_insert_with(|| "the run recorded no observation".to_owned());
        }
    }
    for (index, end) in evidence.ends.iter().enumerate() {
        match evaluate_configuration(definition, end, invariant, EVALUATION_POLLS) {
            Ok((true, _)) => {}
            Ok((false, cells)) if failure.is_null() => {
                failure = failure_value("end", None, Some(index), Ok(texts(&cells)));
            }
            Ok((false, _)) => {}
            Err(unvalued) => {
                host_bound |= unvalued.host_bound;
                undecided.get_or_insert_with(|| format!("at the end {index}: {unvalued}"));
            }
        }
    }
    (
        json!({"channels": channels, "ends": evidence.ends.len(), "undecided": undecided,
               "failure": failure}),
        host_bound,
    )
}

/// Each cell as KORE text.
fn texts(cells: &[Pattern]) -> Vec<String> {
    cells
        .iter()
        .map(|cell| Printer::compact().print_pattern(cell))
        .collect()
}

/// A failure, `{at, rule, index, cells, cells_missing}`: where (`initial`, `step` or `end`), the
/// rule's label and its arrival index, or the end's index, and the cells read there as KORE, or
/// why the record cannot give them.
fn failure_value(
    at: &str,
    rule: Option<&str>,
    index: Option<usize>,
    cells: Result<Vec<String>, &str>,
) -> Value {
    let (cells, missing) = match cells {
        Ok(cells) => (json!(cells), Value::Null),
        Err(why) => (Value::Null, json!(why)),
    };
    json!({"at": at, "rule": rule, "index": index, "cells": cells, "cells_missing": missing})
}

/// Reads a record of a run of one path into `channels` (each label's states read, and why one was
/// not decided); gives the first state of the path that gives `false`, as a failure. A channel is
/// read to its end where it is closed, and up to its horizon where a bound cut a prefix
/// program's path.
///
/// The run's functions logged each evaluation in path order (a run of one path asks each point
/// once, in path order), so where the log of the one request is the record's elements, class by
/// class, the first `false` the log holds is the path's first, with the cells of that event. Where
/// it is not (the record holds no element of a path not settled, for one), the first `false` of
/// the first channel in label order that holds one is given, without cells, and the failure says
/// why.
fn one_path(
    record: &BaselineRecord,
    prefix: bool,
    labels: &[String],
    channels: &mut [Value],
    logged: &Log,
) -> Value {
    let no = short(false);
    for (class, (recorded, channel)) in record.channels.iter().zip(channels.iter_mut()).enumerate()
    {
        channel["steps"] = json!(recorded.elements.len());
        if recorded.elements.iter().any(Option::is_none) {
            // Why: the first evaluation of the class the run's functions left undecided.
            let why = logged.entries.iter().find_map(|entry| match &entry.value {
                Value3::Undecided(why) if entry.class == class => Some(why.as_str()),
                _ => None,
            });
            channel["undecided"] = json!(why.map_or_else(
                || "the invariant's value is not known at a state".to_owned(),
                |why| format!("the invariant's value is not known at a state: {why}")
            ));
        } else if let ChannelEnd::Open(opened) = &recorded.end
            && !(prefix && opened.opening == Opening::Bound)
        {
            channel["undecided"] = json!(opened.reason);
        }
    }
    let matches = logged.requests == 1
        && record.channels.iter().enumerate().all(|(class, recorded)| {
            let log = logged
                .entries
                .iter()
                .filter(|entry| entry.class == class)
                .map(|entry| match entry.value {
                    Value3::True => Some(short(true)),
                    Value3::False(_) => Some(no),
                    Value3::Undecided(_) => None,
                });
            log.eq(recorded.elements.iter().copied())
        });
    if matches {
        let mut arrivals = vec![0_usize; labels.len()];
        for entry in &logged.entries {
            if let Value3::False(cells) = &entry.value {
                return failure_value(
                    "step",
                    Some(&labels[entry.class]),
                    Some(arrivals[entry.class]),
                    Ok(cells.clone()),
                );
            }
            arrivals[entry.class] += 1;
        }
        return Value::Null;
    }
    record
        .channels
        .iter()
        .enumerate()
        .find_map(|(class, recorded)| {
            let index = recorded.elements.iter().position(|e| *e == Some(no))?;
            Some(failure_value(
                "step",
                Some(&labels[class]),
                Some(index),
                Err(
                    "the evaluations the run logged are not the record's, so neither the cells \
                     nor the order of the rules' states is known: this is the first rule in \
                     label order with a state that gives false",
                ),
            ))
        })
        .unwrap_or(Value::Null)
}

/// Reads a record of a run of several paths into `channels` and `undecided`; gives a state that
/// gives `false`, as a failure. Only a real record is read. Its prefix sets keep, per channel, the
/// nearest index at which some path stops being explored, so where a path is cut, or ends
/// undecided, or holds an undecided element, what the other paths hold past their own such point
/// is not known: the run is then undecided. Every element of every path is read through the sets:
/// a path's prefix at an index is the all-`true` prefix of that length or holds a `false`, which
/// first shows at the index of its first `false`. The record orders no state across rules or
/// paths, so the failure is the first `false` index of the first channel in label order that has
/// one, without cells.
fn several_paths(
    paths: &PathRecord,
    labels: &[String],
    channels: &mut [Value],
    undecided: &mut Option<String>,
) -> Value {
    if !paths.real {
        undecided
            .get_or_insert_with(|| "the run's paths are not all shown real and clean".to_owned());
        return Value::Null;
    }
    let (yes, no) = (short(true), short(false));
    let mut failure = Value::Null;
    for (class, (sets, channel)) in paths.channels.iter().zip(channels.iter_mut()).enumerate() {
        let mut chain = PrefixChain::empty();
        let mut steps = 0_usize;
        for index in 0..sets.prefixes.len() {
            if sets.holds(index, chain.then(no).digest()) {
                if failure.is_null() {
                    failure = failure_value(
                        "step",
                        Some(&labels[class]),
                        Some(index),
                        Err(
                            "the run has several paths, whose record keeps no state's cells and \
                             orders no state across rules or paths: this is the first rule in \
                             label order with a state that gives false",
                        ),
                    );
                }
                break;
            }
            let next = chain.then(yes);
            if !sets.holds(index, next.digest()) {
                break;
            }
            chain = next;
            steps += 1;
        }
        channel["steps"] = json!(steps);
        if let Some(horizon) = sets.complete_to {
            channel["undecided"] = json!(format!(
                "the run has several paths, and one stops being explored at its element {} ({}): \
                 what the others hold past their own such point is not known",
                horizon.elements,
                horizon.opening.name()
            ));
        }
    }
    failure
}

/// An item's evidence from its rules `steps` and what each program's run read of its invariant
/// (`read`; `None`: no run read it).
fn item_evidence(steps: &Result<Steps, String>, read: Option<&[Read]>) -> Value {
    let steps = match steps {
        Ok(steps) => steps,
        Err(reason) => {
            return json!({
                "status": EVIDENCE_INCOMPLETE,
                "rules": [],
                "states": 0,
                "steps": 0,
                "programs": [],
                "failure": null,
                "reason": format!("the rules that step where the item's rule matches are not known: {reason}"),
                "cached": false,
            });
        }
    };
    let read = read.unwrap_or(&[]);
    let mut reasons = steps
        .unlabeled
        .iter()
        .map(|id| {
            format!("the rule {id} can step where the item's rule matches, and has no label a run observes it by")
        })
        .collect::<Vec<_>>();
    let mut failure = Value::Null;
    let (mut states, mut stepped) = (0_u64, 0_u64);
    let mut programs = Vec::new();
    let cached = !read.is_empty() && read.iter().all(|(_, _, cached)| *cached);
    for (program, record, _) in read {
        let record = match record {
            Ok(record) => record,
            Err(reason) => {
                reasons.push(reason.clone());
                continue;
            }
        };
        programs.push(program.clone());
        if failure.is_null() && !record["failure"].is_null() {
            failure = record["failure"].clone();
            failure["program"] = json!(program);
        }
        if let Some(reason) = record["undecided"].as_str() {
            reasons.push(format!("in the program `{program}`, {reason}"));
        }
        for channel in record["channels"].as_array().into_iter().flatten() {
            if !channel["rule"]
                .as_str()
                .is_some_and(|rule| steps.labels.contains(rule))
            {
                continue;
            }
            stepped += channel["steps"].as_u64().unwrap_or(0);
            if let Some(reason) = channel["undecided"].as_str() {
                reasons.push(format!(
                    "in the program `{program}`, before the steps of `{}`: {reason}",
                    channel["rule"].as_str().unwrap_or("?")
                ));
            }
        }
        // The initial state, and each end the run read.
        states += 1 + record["ends"].as_u64().unwrap_or(0);
    }
    states += stepped;
    let status = if !failure.is_null() {
        EVIDENCE_FAILS
    } else if !reasons.is_empty() {
        EVIDENCE_INCOMPLETE
    } else if programs.is_empty() {
        reasons.push("no program's run was read".to_owned());
        EVIDENCE_INCOMPLETE
    } else if stepped > 0 {
        EVIDENCE_HOLDS
    } else {
        EVIDENCE_VACUOUS
    };
    json!({
        "status": status,
        "rules": steps.labels.iter().chain(&steps.unlabeled).collect::<Vec<_>>(),
        "states": states,
        "steps": stepped,
        "programs": programs,
        "failure": failure,
        "reason": if status == EVIDENCE_FAILS || reasons.is_empty() {
            Value::Null
        } else {
            json!(reasons.join("; "))
        },
        "cached": cached,
    })
}
