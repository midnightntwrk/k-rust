//! The evidence of an argued item's invariant on the corpus's runs (module documentation of
//! [`crate::coverage`], "Argued obligations"): whether the invariant holds at every state of the
//! baseline's runs where the item's rule can match ([`evidence`]).
//!
//! # Which states
//!
//! The connection shows, at each axiom of the item's rule, that a state the left-hand side `L`
//! matches and the invariant `F` holds of does not have the item's valuation. Its premise is that
//! `F` holds at every reachable state `L` matches, and the evidence tests that premise on the
//! corpus's runs. At a state `L` matches, either some rule takes a step, and that rule's
//! left-hand side matches the state too, so it unifies with `L` (kink-native
//! `invariant::stepping_rules`), or no rule does, and the state is an end. So the states before a
//! step of a rule of `S_R`, the rules whose left-hand side unifies with one of the item's axioms',
//! together with the ends, hold every state where `L` matched; `S_R` holds the item's own rules,
//! and the other states it adds are reachable states too. The initial state is read as well: it is
//! the base case of the inductive argument the invariant stands for.
//!
//! A state the evidence does not read is no state of the premise only where it is no state `L`
//! matched; a path that ends at an undefined step has such a state (its last, before a step of a
//! rule whose result is undefined), which is no end and no point, so a run with one leaves the
//! evidence incomplete. So does a rule of `S_R` with no label, whose steps a run cannot observe.
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
//! Only states of real, clean paths count. An element the run's observation record keeps was read
//! at a real state of a path with no diagnostic (kink-campaign `observation`, "The slot"); a record
//! of several paths counts only where it is real. A comparable program's run is complete with no
//! diagnostic and ends at values, so its initial state and ends are states of its paths; a
//! prefix program's run kept an element of the corpus's channels, which only a settled path does,
//! and its evidence covers the prefix it ran, as its coverage does.
//!
//! # Answers
//!
//! For an argued item, over every program:
//! - `fails`: some state read gives `false`; the failure names the program, where (`initial`,
//!   before the step of a rule, or an `end`), the rule's arrival index or the end's index, and the
//!   cells read there as KORE, where they are known;
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
//! run's campaign gave it sides; `--verify` reads and writes no record.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use k_rust::k_rust_backend::definition::BackendDefinition;
use k_rust::k_rust_backend::rewrite::ProbeState;
use k_rust::kore::ast::Pattern;
use k_rust::kore::printer::Printer;
use kink_campaign::{
    BaselineRecord, ChannelEnd, Evaluated, Observation, ObservationEvaluator, ObservationFunctions,
    ObserveFunctions, Opening, PrefixChain, Stutter, TestEvidence,
};
use kink_native::invariant::{Invariant, evaluate, evaluate_configuration, stepping_rules};
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

/// An evaluation that did not give `true`, in the order the run's requests asked them.
struct Logged {
    class: usize,
    /// Its index among its class's points in the request.
    index: usize,
    /// `false`, with the cells read as KORE text; or why it is not known.
    value: Result<Vec<String>, String>,
}

#[derive(Default)]
struct Log {
    requests: usize,
    entries: Vec<Logged>,
}

/// The invariant as the functions of an evidence run's declaration (module documentation, "The
/// runs"): every point's content is the invariant's value, evaluated in the baseline definition.
struct Functions {
    definition: Arc<BackendDefinition>,
    symbol: String,
    cells: Vec<Vec<String>>,
    classes: usize,
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
            calls: vec![0; self.classes],
        });
        Ok(())
    }
}

/// The evaluation of one request of an evidence run.
struct Evaluator<'f> {
    functions: &'f Functions,
    calls: Vec<usize>,
}

impl Evaluator<'_> {
    fn log(&self, class: usize, index: usize, value: Result<Vec<String>, String>) {
        self.functions
            .log
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .entries
            .push(Logged {
                class,
                index,
                value,
            });
    }
}

impl ObservationEvaluator for Evaluator<'_> {
    fn holds(&mut self, _: usize, _: &ProbeState<'_>) -> Option<Result<bool, String>> {
        None
    }

    fn content(
        &mut self,
        class: usize,
        state: &ProbeState<'_>,
        value: bool,
    ) -> Result<Evaluated, String> {
        let index = self.calls.get(class).copied().unwrap_or(0);
        if let Some(calls) = self.calls.get_mut(class) {
            *calls += 1;
        }
        let functions = self.functions;
        let cells = functions
            .cells
            .iter()
            .map(|path| {
                let path = path.iter().map(String::as_str).collect::<Vec<_>>();
                state.cell(&path)
            })
            .collect::<Option<Vec<_>>>();
        let answer = match &cells {
            None => Err("the state holds no cell the invariant reads".to_owned()),
            Some(cells) => evaluate(
                &functions.definition,
                &cells.iter().collect::<Vec<_>>(),
                Invariant {
                    symbol: &functions.symbol,
                    cells: &functions.cells,
                },
            ),
        };
        match answer {
            Ok(holds) => {
                if !holds {
                    let text = cells
                        .iter()
                        .flatten()
                        .map(|cell| Printer::compact().print_pattern(cell))
                        .collect();
                    self.log(class, index, Ok(text));
                }
                Ok(Evaluated {
                    digest: element_digest(holds),
                    value: value.then(|| json!(holds)),
                })
            }
            Err(reason) => {
                self.log(class, index, Err(reason.clone()));
                Err(reason)
            }
        }
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
            classes: labels.len(),
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
        let initial = evaluate_configuration(definition, &test.initial_state, asked);
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
                programs.push((
                    program.id.clone(),
                    Err(format!(
                        "the evidence run of the program `{}` failed: {reason}",
                        program.id
                    )),
                    false,
                ));
                continue;
            }
        };
        let logged = std::mem::take(&mut *log.lock().unwrap_or_else(PoisonError::into_inner));
        let record = record(
            definition,
            asked,
            labels,
            initial,
            evidence.as_ref(),
            ResultClass::ComparablePrefix.as_str() == class,
            &logged,
        );
        if let (Some(key), Some(path)) = (&key, &path) {
            memo::write_evidence(&store, path, key, &record);
        }
        programs.push((program.id.clone(), Ok(record), false));
    }
    programs
}

/// What one program's evidence run read (module documentation, "The runs"): `{channels: [{rule,
/// steps, undecided}], undecided, failure}`, a channel per label of `labels` with the number of
/// states read before its rule's steps and why one was not decided, why a state of the run itself
/// was not decided (its initial state, an end, an undefined step, its paths not real), and the
/// first state that gives `false` (`{at, rule, index, cells}`), in path order: the initial state,
/// then a step, then an end. `initial` is the value at the initial state; `evidence` the run's
/// (`None`: no rule was observed, so no run was made, and no end is read); `prefix` whether the
/// program is a prefix program; `logged` the evaluations the run's functions logged.
fn record(
    definition: &BackendDefinition,
    invariant: Invariant<'_>,
    labels: &[String],
    initial: Result<bool, String>,
    evidence: Option<&TestEvidence>,
    prefix: bool,
    logged: &Log,
) -> Value {
    let mut undecided = None;
    let mut failure = Value::Null;
    match initial {
        Ok(true) => {}
        Ok(false) => {
            failure = json!({"at": "initial", "rule": null, "index": null, "cells": null});
        }
        Err(reason) => undecided = Some(format!("at the initial state: {reason}")),
    }
    let mut channels = labels
        .iter()
        .map(|label| json!({"rule": label, "steps": 0, "undecided": null}))
        .collect::<Vec<_>>();
    let Some(evidence) = evidence else {
        return json!({"channels": channels, "ends": 0, "undecided": undecided,
                      "failure": failure});
    };
    let observed = match &evidence.notes.observation {
        Some(Observation::Recorded(record)) => Some(record),
        _ => None,
    };
    match observed {
        None => {
            undecided.get_or_insert_with(|| "the run recorded no observation".to_owned());
        }
        Some(record) => {
            let steps = read_channels(record, prefix, &mut channels, &mut undecided);
            // In a run of one path its functions logged every value in path order, so the first
            // logged `false` the record keeps is the path's first, with its cells; in a run of
            // several paths the first index at which some path's element is `false`.
            let first = (record.paths.is_none() && logged.requests == 1)
                .then(|| {
                    logged.entries.iter().find_map(|entry| match &entry.value {
                        Ok(cells) if steps.contains(&(entry.class, entry.index)) => {
                            Some((entry.class, entry.index, json!(cells)))
                        }
                        _ => None,
                    })
                })
                .flatten()
                .or_else(|| {
                    steps
                        .iter()
                        .min_by_key(|&&(_, index)| index)
                        .map(|&(class, index)| (class, index, Value::Null))
                });
            if failure.is_null()
                && let Some((class, index, cells)) = first
            {
                failure = json!({"at": "step", "rule": labels[class], "index": index,
                                 "cells": cells});
            }
        }
    }
    if evidence.undefined_steps {
        undecided.get_or_insert_with(|| {
            "a path ends at an undefined step, whose state the evidence does not read".to_owned()
        });
    }
    for (index, end) in evidence.ends.iter().enumerate() {
        match evaluate_configuration(definition, end, invariant) {
            Ok(true) => {}
            Ok(false) if failure.is_null() => {
                let cells = invariant
                    .cells
                    .iter()
                    .map(|path| {
                        cell_of(end, path).map(|cell| Printer::compact().print_pattern(cell))
                    })
                    .collect::<Option<Vec<_>>>();
                failure = json!({"at": "end", "rule": null, "index": index, "cells": cells});
            }
            Ok(false) => {}
            Err(reason) => {
                undecided.get_or_insert_with(|| format!("at the end {index}: {reason}"));
            }
        }
    }
    json!({"channels": channels, "ends": evidence.ends.len(), "undecided": undecided,
           "failure": failure})
}

/// Reads `record`'s channels into `channels` (each label's states read, and why one was not
/// decided), and `undecided` where the record is not real; gives, for each channel with an element
/// `false`, the channel and the first such index. A channel is read to its end where it is closed,
/// and up to its horizon where a bound cut a prefix program's path.
fn read_channels(
    record: &BaselineRecord,
    prefix: bool,
    channels: &mut [Value],
    undecided: &mut Option<String>,
) -> Vec<(usize, usize)> {
    let (yes, no) = (short(true), short(false));
    let open = |opening: Opening| !(prefix && opening == Opening::Bound);
    let mut failures = Vec::new();
    if let Some(paths) = &record.paths {
        if !paths.real {
            undecided.get_or_insert_with(|| {
                "the run's paths are not all shown real and clean".to_owned()
            });
            return Vec::new();
        }
        for (class, (sets, channel)) in paths.channels.iter().zip(channels.iter_mut()).enumerate() {
            let mut chain = PrefixChain::empty();
            let mut steps = 0_usize;
            for index in 0..sets.prefixes.len() {
                if sets.holds(index, chain.then(no).digest()) {
                    failures.push((class, index));
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
            if let Some(horizon) = sets.complete_to
                && open(horizon.opening)
            {
                channel["undecided"] = json!(format!(
                    "a path of the run is not explored past its element {} ({})",
                    horizon.elements,
                    horizon.opening.name()
                ));
            }
        }
    } else {
        for (class, (recorded, channel)) in
            record.channels.iter().zip(channels.iter_mut()).enumerate()
        {
            channel["steps"] = json!(recorded.elements.len());
            if let Some(index) = recorded
                .elements
                .iter()
                .position(|element| *element == Some(no))
            {
                failures.push((class, index));
            }
            if recorded.elements.iter().any(Option::is_none) {
                channel["undecided"] = json!("the invariant's value is not known at a state");
            } else if let ChannelEnd::Open(opened) = &recorded.end
                && open(opened.opening)
            {
                channel["undecided"] = json!(opened.reason);
            }
        }
    }
    failures
}

/// The cell at `path` of the configuration `term` (KORE): `path[0]` is its own symbol, and each
/// further symbol that of a cell the previous one holds as a direct argument.
fn cell_of<'p>(term: &'p Pattern, path: &[String]) -> Option<&'p Pattern> {
    let (first, below) = path.split_first()?;
    let applies = |pattern: &Pattern, name: &str| matches!(pattern, Pattern::Application { symbol, .. } if symbol.name.as_str() == name);
    if !applies(term, first) {
        return None;
    }
    let mut current = term;
    for name in below {
        let Pattern::Application { arguments, .. } = current else {
            return None;
        };
        current = arguments.iter().find(|argument| applies(argument, name))?;
    }
    Some(current)
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
        "reason": if status == EVIDENCE_FAILS {
            Value::Null
        } else {
            reasons.first().map_or(Value::Null, |reason| json!(reason))
        },
        "cached": cached,
    })
}
