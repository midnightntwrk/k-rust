//! The result cache (flow README 5.3): one record per program's baseline run, keyed by the
//! result schema version, kink's build identity and semantics identity (kink-campaign
//! `identity`), the execution digest, the program digest and the budget's bounds.
//!
//! Each program runs as its own zero-mutant campaign through `kink_campaign::run_campaign_multi`
//! (the way kink-corpus admission's `baseline_only` does), with the specification's two oracles
//! (README 5.4: exit stop without an exit-code cell, then the final term, without the cells the
//! specification leaves out when it leaves any out, [`crate::observed`]; crash policy `reject`), the
//! all-normal classifier and the manifest's budget, and every program of one command shares one
//! `NativeValidator`, so the baseline compiles once. One program's failure never touches another.
//!
//! Every campaign call of one command goes through the command's one [`BaselineRunner`], whose
//! in-memory `kink_campaign::BaselineSession` runs each program's baseline live at most once per
//! command (flow F-12, README 6.3): `coverage` runs each program once, and `run` reuses those
//! live runs in its kill search. The session is never written to disk, so a later command runs
//! every baseline it needs live again. The documents report the count as `baseline_runs`.
//!
//! A program is `comparable` exactly when that campaign admits its baseline run and gives it sides:
//! the run is complete, no exclusion holds (a run whose leaf contradicts a trusted claim is
//! admitted but gives none, re-pin decision 2; one excluded by k-rust's run-level lists is refused,
//! re-pin adoption A-1), and every oracle side is a value. Only a comparable program can later kill
//! a mutant. Every record carries the baseline run's contradicted-claim records as specification
//! diagnostics and its count of undecided solver answers (re-pin adoption A-1), and the entries of
//! its short-circuit readings that exclude it (`short_circuit_readings`: on a definition whose
//! short-circuit analysis flags a rule, and for a program whose initial configuration applies a
//! reading-dependent function, the campaign runner judges each run by k-rust's
//! `shortCircuitReadings` list of that run, kink-native `DefinitionExclusions::run_exclusion` and
//! `state_exclusion`, so such a program is comparable when its run reads no skipped operand that
//! counts, and otherwise `unknown` with the step named), outside the key and the run digest. When
//! the campaign refuses the baseline run, the runner returns no evidence; a diagnostic run of the
//! same initial state through the kink-native execution adapter then tells a timeout from an
//! unknown or failed run and supplies the cause, the final states and the coverage for the reader.
//! The diagnostic run never makes a program comparable.
//!
//! Under `[observe]` every program's run carries the declaration (kink-campaign
//! `RunOptions::observe`), and its baseline row holds the channels the run recorded
//! (`observations`, kink-campaign `BaselineRecord::value`: each element's 8 digest bytes, and how
//! each channel ends), which the run digest covers ([`run_digest`]). A run that a deterministic
//! bound cut before it ended, every other path complete, is `comparable-prefix`: the campaign
//! admits it for its channels, each compared up to its horizon, and it can kill by them. One
//! none of whose channels kept an element within its budget observed nothing, so it is `unknown`
//! (reason `observed-nothing` in its cause). The
//! record's `observations` summarizes the channels for the program's row, and the key names the
//! declaration ([`result_key`]).
//!
//! The cache is plain JSON under `<cache>/results/<execution digest>/<program digest>.json`. A
//! record holds each end once, as KORE text: a comparable program's ends in the whole-term (or
//! cells) side of its baseline row, which the run digest covers, and an unknown program's
//! diagnostic leaves in `final_configuration` ([`record_final_configuration`] reads either). It
//! is written by streaming its members ([`write_record`]), never built as one value, and its JSON
//! depth is independent of what its ends hold. A
//! record is used only when its key equals the current key; any other record, or one that does not
//! parse, is recomputed and replaced. A record names its writer's build, so a record another
//! build wrote is recomputed (packet CACHE-ID-fix-1); when the executable cannot be read, no
//! record is read or written. Deleting the cache is always safe.
//!
//! **What is stored.** A store may hold a value only under a key that names every input the
//! value depends on, and only when the value is a function of those inputs on every host. The
//! key ([`result_key`]) names the execution digest (`digest::execution_digest`: the loaded
//! definition without positions, so a comment or layout edit keeps every record), the program
//! digest, the bounds a stored class depends on ([`budget_value`]: not `time_ms`), kink's build
//! and its semantics identity. Of the classes, only `comparable` and `unknown` are written, and
//! of `unknown` only one whose cause is not a host event ([`HostDependence`]): a `timeout`
//! depends on the host's load, an `error` can come from the host (a refused stack segment, a
//! solver that could not be created) and kink cannot tell when, and a stack stop or an allowance
//! refusal is a fact of the host. Such a program's row says why it was not cached
//! (`not_cached`), and the next command runs it again; a stored record of such a class is never
//! read. Under the Z3 profile every solver query of a command, a run's and kink's own outside a
//! run (leaf feasibility, the observation decider), is bounded by Z3 resource units (`[budget]
//! smt_resource_limit`), so its answer, decided or not, is a function of the query, the units and
//! the Z3 build, which the key names ([`budget_value`]): a class is then a function of its key,
//! and the cache is on. The record counts the undecided answers, k-rust's (`smt_unknowns`) and
//! kink's (`decider_smt_unknowns`), reported and never an exclusion: a stored class is the class
//! the same run gets again, and the counts say where a larger budget could decide more. The cache
//! is off where the key cannot name the solver: a solver the clock bounds ([`RESULT_CACHE_Z3`]),
//! whose answers depend on the host's load, and a Z3 build that cannot be named (kink-native
//! `UNNAMED_Z3_BUILD`). A baseline bounded by `[budget] baseline_max_work`
//! that the bound stops is `unknown`, a function of the key, which names the bound.

use crate::{
    admit::{AdmittedSpec, CaseInputs, InputSession},
    digest::{ExecutionDigest, execution_digest, program_digest, spec_digest},
    evidence::EndReader,
    expect::Baseline,
    manifest::{Budget, FlowManifest, Program},
};
use k_rust::{
    backend::Backend,
    definition::{AttributeKey, Sentence},
    kast::identifier::{decode_sort_name, label_or_name},
    kore::{
        ast::{Definition as KoreDefinition, Pattern},
        parser::parse_definition,
        printer::Printer,
    },
};
use kink_campaign::{
    BaselineSession, CallRecording, Campaign, CampaignFailure, CampaignFailureKind,
    CampaignOptions, CampaignReport, CampaignRun, ChannelEnd, CrashPolicy, FinalResult, FirstTests,
    OracleDeclaration, OracleSide, OracleValue, Projection, RunStop, ScheduleMode, SideRun,
    StateProjection, TestCase, TestEvidence, run_campaign_multi_ordered, run_campaign_multi_with,
};
use kink_corpus::{Store, StoreError, runner::all_normal};
use kink_native::{
    bridge::{LeafTerm, leaf_terms},
    coverage::{RuleAuthors, TestCoverage, coverage_domain, non_executable_ids},
    data::{DataFacts, data_ends},
    exclusion::{DefinitionExclusions, Exclusion},
    execution::{
        AdaptedExecution, AdaptedLeaf, ExecutionAdapter, ExecutionBudget, HaltClass, ResultRun,
        SolverProfile,
    },
    feasibility::{LeafFeasibility, TestInitialState},
    step_events::{EntryRole, NonValue, NonValueStep, ObservationDecider},
};
use kink_patch::{
    CandidateGeneration, Discovery, MAX_JSON_DEPTH, Patch, SelectionPolicy, SentenceRef,
    Sha256Digest, canonical_json, payload_digest, select, value_depth,
};
use serde_json::{Value, json};
use std::{
    cell::{Cell, OnceCell, RefCell},
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
    time::Duration,
};

/// The result schema version, the first component of every result key (kink-campaign
/// `identity::RESULT_SCHEMA_VERSION`, where its history is; it is a component of kink's
/// semantics identity, so the identity names it). It changes whenever kink changes what counts
/// as a comparable result or what a record holds, so that older records are recomputed rather
/// than trusted.
pub use kink_campaign::RESULT_SCHEMA_VERSION;
/// The `schema` field of a result record.
pub const RECORD_SCHEMA: &str = "kink-flow-result";
/// Domain of a run digest: the digest of the `run` part of a baseline row. v2 since the row
/// writes each pattern of a side as its KORE text (kink-campaign report version 6), where v1
/// digested the row with KORE JSON objects: a v2 digest is never compared with a v1 one.
pub const RUN_DOMAIN: &str = "kink-flow/run/v2";
/// The cache directory's name next to `FLOW.toml`.
pub const CACHE_DIRECTORY: &str = ".kink-flow";
/// Simplifier iterations per rewrite step of every program run (not a manifest key).
pub const SIMPLIFICATION_ITERATIONS: usize = 10_000;
/// The operator name of the empty generation each zero-mutant campaign runs.
const BASELINE_ONLY_OPERATOR: &str = "kink-flow/baseline-only/v1";

/// The class of a program's baseline run (README 5.3).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResultClass {
    /// The baseline run is complete and every oracle side is a value: the program can kill.
    Comparable,
    /// Under `[observe]`, the baseline run has no end within its deterministic bounds (its depth
    /// bound or `[budget] baseline_max_work` cut it, and every other path of it is complete):
    /// its end slots compare nothing, and it can kill by its observation channels, each compared
    /// up to its horizon (kink-campaign `BaselineRecord::prefix`). Some channel kept an element
    /// within the budget; a prefix program with none is [`Self::Unknown`].
    ComparablePrefix,
    /// The run did not finish within the budget's time.
    Timeout,
    /// The run produced no comparable value (for example a collection with a Bytes key,
    /// a depth limit, or an undecided step).
    Unknown,
    /// The program's input was refused (not read, parsed or assembled); never stored.
    Refused,
    /// The run or the runner failed.
    Error,
}

impl ResultClass {
    /// Whether `class`, a row's or a record's class, names a program that can kill: `comparable`,
    /// or `comparable-prefix` (compared by its observation channels up to their horizons).
    #[must_use]
    pub fn can_kill(class: &Value) -> bool {
        *class == Self::Comparable.as_str() || *class == Self::ComparablePrefix.as_str()
    }

    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Comparable => "comparable",
            Self::ComparablePrefix => "comparable-prefix",
            Self::Timeout => "timeout",
            Self::Unknown => "unknown",
            Self::Refused => "refused",
            Self::Error => "error",
        }
    }
}

/// The names of the oracle slots of [`fixed_oracles`], in slot order: the slots of a
/// specification that leaves no cell out ([`crate::observed::WHOLE_TERM_SLOTS`]).
pub const ORACLE_SLOTS: [&str; 2] = crate::observed::WHOLE_TERM_SLOTS;

/// The two oracles of a flow program of a specification that leaves no cell out (README 5.4):
/// the exit stop with no exit-code cell, then the whole final term; a semantic crash is outside
/// the operand domain (`reject`). A program's oracles are its specification's
/// ([`crate::observed::ResultProjection::oracles`]), which are these unless some cell is left out.
pub fn fixed_oracles() -> Vec<OracleDeclaration> {
    oracle_declarations(StateProjection::WholeTerm)
}

/// The two oracles of a flow program whose second slot projects `state`: the exit stop with no
/// exit-code cell, then `state`; a semantic crash is outside the operand domain (`reject`).
pub(crate) fn oracle_declarations(state: StateProjection) -> Vec<OracleDeclaration> {
    [
        StateProjection::ExitStop {
            exit_code_cell: None,
        },
        state,
    ]
    .into_iter()
    .map(|projection| {
        OracleDeclaration::new(CrashPolicy::Reject, Projection::State(projection))
            .expect("state projections without term paths are valid")
    })
    .collect()
}

/// The execution budget of every program run.
pub fn execution_budget(budget: Budget) -> ExecutionBudget {
    ExecutionBudget {
        time: Duration::from_millis(budget.time_ms),
        max_simplification_iterations: SIMPLIFICATION_ITERATIONS,
        max_depth: Some(budget.max_depth),
        max_breadth: None,
    }
}

/// The result key: schema version, kink's build identity `kink_build` (kink-campaign
/// `identity::kink_build`, the running executable's digest, which guards every piece of verdict
/// code, versioned or not; packet CACHE-ID-fix-1), kink's semantics identity `kink` (the k-rust
/// revision, the definition exclusions, the execution request, ...; packet CACHE-ID, re-pin
/// R0-tail review 1 minor), the execution digest `{kind, digest}` (`digest::execution_digest`),
/// the program digest and the budget ([`budget_value`]), and the program's stop
/// (`FlowManifest::program_stop`: the rules and the program's count) when the manifest declares
/// one; without one the key has no `stop`, and is the key it was before stops existed. Where a
/// front end gives the syntax family's selection (`FlowManifest::syntax`: its authored sorts and
/// template binders, which decide the bindings every baseline run records), the key names it
/// (`syntax`); kink-flow's own selection is a function of the definition, which the execution
/// digest names, so without a front end's the key has no `syntax`. A record
/// written by another build, or by one before CACHE-ID-fix-1 (whose key has no `kink_build`),
/// misses and is recomputed. `kink_build` is `None` when the executable cannot be read; such a
/// key is never read or written ([`update_results`]). Where the manifest declares observation
/// channels, the key names the declaration (`observe`, `FlowManifest::observe_value`), on which
/// the record's channels and whether the program is a prefix program depend; without one the key
/// has no `observe`, and is the key it was before observations existed.
pub fn result_key(
    execution: ExecutionDigest,
    program: Sha256Digest,
    budget: Budget,
    kink_build: Option<Sha256Digest>,
    stop: Option<Value>,
    syntax: Option<Value>,
    observe: Option<Value>,
) -> Value {
    let mut key = json!({
        "schema_version": RESULT_SCHEMA_VERSION,
        "kink_build": kink_build.map(|build| build.to_string()),
        "kink": kink_campaign::kink_identity(),
        "execution": execution.value(),
        "program": program.to_string(),
        "budget": budget_value(budget),
    });
    if let Some(stop) = stop {
        key["stop"] = stop;
    }
    if let Some(syntax) = syntax {
        key["syntax"] = syntax;
    }
    if let Some(observe) = observe {
        key["observe"] = observe;
    }
    key
}

/// The bounds of a program run that a stored class depends on, `{max_depth,
/// max_simplification_iterations, max_breadth}` and `baseline_max_work` when it is set: each
/// stops a run deterministically, so a stored `unknown` depends on it. Under the Z3 profile it
/// also has `smt` (kink-native `solver_value`): `[budget] smt_resource_limit`, the retries and
/// the Z3 build, on which whether each solver query of a run is decided depends; under the no-Z3
/// profile no backend reads them, and the member is absent, so a no-Z3 key is the key it was
/// before the member existed. `time_ms` is not a member: no stored class depends on it, since a
/// run the watchdog stopped is never stored and a run it did not stop is the uncancelled
/// request, whose result does not depend on the bound. The result key, the tier-1 context
/// (`digest::outcome_context`) and the pattern key (`query::answer_key`) all take this object, so
/// the three name the same bounds.
pub fn budget_value(budget: Budget) -> Value {
    let mut value = json!({
        "max_depth": budget.max_depth,
        "max_simplification_iterations": SIMPLIFICATION_ITERATIONS,
        "max_breadth": null,
    });
    if let Some(max_work) = budget.baseline_max_work {
        value["baseline_max_work"] = json!(max_work);
    }
    if let Some(solver) = kink_native::solver_value(budget.backend_options()) {
        value["smt"] = solver;
    }
    value
}

/// Why a baseline result is not a function of its key: such a result is never written, and a
/// stored record of its class is never read ([`program_row`], [`read_record`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HostDependence {
    /// The watchdog stopped a run at the budget's `time_ms`.
    Time,
    /// A run or the runner failed: an adapter, backend or runner failure can come from the host
    /// (a refused stack segment, a solver that could not be created), and kink cannot tell.
    Failure,
    /// The run is excluded for a reason of the host ([`host_exclusion`]).
    Exclusion(Exclusion),
    /// The run's stop condition (`[stop] when`) was left undecided at an arrival, or refused at
    /// one (kink-campaign `ExecutionFailureKind::StopCondition`). An undecided answer can be its
    /// evaluation's budget, which the answer does not tell from a fact of the definition, so no
    /// such result is kept, as a timeout is not.
    StopCondition,
}

impl HostDependence {
    /// The row's `not_cached`: the class, why it depends on the host, and what follows.
    fn reason(self, class: ResultClass, time_ms: u128) -> String {
        let why = match self {
            Self::Time => {
                format!("{WATCHDOG_STOPPED} = {time_ms}; a timeout depends on the host's load")
            }
            Self::Failure => "a run or runner failure can come from the host (a refused stack \
                              segment, a solver that could not be created), and kink cannot tell \
                              when"
                .to_owned(),
            Self::Exclusion(exclusion) => format!(
                "the run is excluded ({}), a fact of the host rather than of the definition and \
                 the program",
                exclusion.name()
            ),
            Self::StopCondition => "the stop condition was left undecided or had no value at an \
                                    arrival of the run, and an undecided answer can be its \
                                    evaluation's budget rather than a fact of the definition"
                .to_owned(),
        };
        format!(
            "{}: {why}, so the next command runs this program again",
            class.as_str()
        )
    }
}

/// How a program row's `not_cached` begins, after its class, where the watchdog stopped the run
/// ([`HostDependence::Time`]); [`crate::clock::baseline_stopped`] reads it.
pub const WATCHDOG_STOPPED: &str = "the watchdog stopped the run at time_ms";

/// Whether an exclusion is a fact of the host rather than of the definition and the program: a
/// stop for lack of native stack (the host's threads) and a refusal for the process's memory
/// allowance. Exhaustive, so that a new exclusion is classified when it is added.
pub const fn host_exclusion(exclusion: Exclusion) -> bool {
    match exclusion {
        Exclusion::StackStop | Exclusion::LoadStackStop | Exclusion::AllowanceRefusal => true,
        Exclusion::ContradictedClaim
        | Exclusion::ImplementationChosenHook
        | Exclusion::ShortCircuitReading
        | Exclusion::EqualsCondition
        | Exclusion::ImplementationChosenValue
        | Exclusion::UnsupportedHook
        | Exclusion::PassedStop => false,
    }
}

/// Whether a program's result of class `class` depends on the host, given the exclusion its
/// cause names, how this command's live run of its baseline ended (`live_stop`; `None`: no
/// baseline ran, as for a validation refusal before execution) and the host exclusion the
/// diagnostic run that supplied the result met itself (`diagnostic`, [`diagnostic_host_exclusion`]:
/// that run loads and runs on a backend of its own, so it can stop for lack of stack where the
/// live run did not). A `timeout` depends on the clock; an `error` on
/// whatever failed; an `unknown` on a host exclusion of either run, or on a live run that the
/// watchdog stopped or that failed naming no exclusion (the diagnostic run then supplied the
/// class); any other `unknown` is a deterministic bound, an exclusion of the definition or the
/// program, or a validation refusal, and `comparable` is the uncancelled request's result.
pub fn host_dependence(
    class: ResultClass,
    exclusion: Option<Exclusion>,
    live_stop: Option<RunStop>,
    diagnostic: Option<Exclusion>,
) -> Option<HostDependence> {
    match class {
        ResultClass::Comparable | ResultClass::ComparablePrefix | ResultClass::Refused => None,
        ResultClass::Timeout => Some(HostDependence::Time),
        ResultClass::Error => Some(HostDependence::Failure),
        ResultClass::Unknown => match (exclusion, live_stop) {
            (Some(exclusion), _) if host_exclusion(exclusion) => {
                Some(HostDependence::Exclusion(exclusion))
            }
            (_, Some(RunStop::Time)) => Some(HostDependence::Time),
            (None, Some(RunStop::Failed)) => Some(HostDependence::Failure),
            _ => diagnostic
                .filter(|&exclusion| host_exclusion(exclusion))
                .map(HostDependence::Exclusion),
        },
    }
}

/// Whether the campaign's refusal of a baseline is the `unknown` of a run that
/// `[budget] baseline_max_work` (`bound`) stopped, read from this command's live run with no
/// diagnostic run: an oracle refusal (`kind`) that names no exclusion, of a run that ended in a
/// `work-bound` leaf. Any other refusal of such a run goes to the diagnostic run: one that names
/// an exclusion, to name it (possibly one of the host), and an error side or an invalid baseline,
/// which is an `error` and never cached.
pub fn work_bound_refusal(
    kind: CampaignFailureKind,
    exclusion: Option<Exclusion>,
    bound: Option<u64>,
    work_bound_leaf: bool,
) -> bool {
    kind == CampaignFailureKind::BaselineOracleFailed
        && exclusion.is_none()
        && bound.is_some()
        && work_bound_leaf
}

/// The host exclusion the diagnostic run of a baseline met itself, whatever exclusion the
/// campaign named: a stop for lack of native stack while its backend loaded the definition
/// (`load-stack-stop`) or while it ran (`stack-stop`), or an allowance hook left unevaluated
/// (`allowance-refusal`). The record's cause, final configuration and coverage come from that
/// run, so such a result is not a function of its key even when the live run met none.
pub fn diagnostic_host_exclusion(
    backend: &mut Backend,
    execution: &AdaptedExecution,
) -> Option<Exclusion> {
    let load_stack_stops = backend.select_definition(None).ok().map(|definition| {
        definition.discharge_counts().stack_stops
            + definition.value_claims().counts().condition_stack_stops
    });
    if load_stack_stops.is_some_and(|stops| stops > 0) {
        Some(Exclusion::LoadStackStop)
    } else if execution.stack_stops() > 0 {
        Some(Exclusion::StackStop)
    } else if !execution.facts().allowance_refusals.is_empty()
        || execution
            .leaves()
            .iter()
            .any(kink_native::exclusion::allowance_refusal)
    {
        Some(Exclusion::AllowanceRefusal)
    } else {
        None
    }
}

/// The digest of a baseline row's `run` part, which depends neither on the program id nor on
/// any other test of the campaign. `None` when the row has no `run`.
pub fn run_digest(row: &Value) -> Option<Sha256Digest> {
    let run = row.get("run")?;
    // A row with an observation record ([`baseline_row`]) digests both, so that a record whose
    // channels differ is another run; a row without one digests its run as before observations.
    let payload = match row.get("observations") {
        Some(observations) => canonical_json(&json!({"run": run, "observations": observations})),
        None => canonical_json(run),
    };
    Some(payload_digest(RUN_DOMAIN, payload.as_bytes()))
}

/// The baseline row of a run's evidence: kink-campaign's row (`CampaignReport::baseline_row`),
/// with the run's observation record (kink-campaign `BaselineRecord::value`) under
/// `observations` when the run recorded one, which [`run_digest`] covers. A run without an
/// observation declaration has the row it had before observations existed.
pub fn baseline_row(evidence: &TestEvidence) -> Value {
    let mut row = CampaignReport::baseline_row(evidence);
    if let Some(kink_campaign::Observation::Recorded(record)) = &evidence.notes.observation {
        row["observations"] = record.value();
    }
    row
}

/// The observation summary a program's row shows (`observations`), from its baseline row's record
/// ([`baseline_row`]): `{channels: [{name, elements, closed, open}], horizon}`, `elements` the
/// number recorded, `closed` and `open` as the record has them, and `horizon` each open channel's
/// horizon by name, `{elements, opening}` (kink-campaign `Horizon::value`); `None` for a row
/// without a record.
///
/// A record of a run with several paths (its `paths`) holds no element in `channels`, each open
/// at 0 by `branch`, so its summary gives the prefix sets' facts instead: `{paths, real, channels:
/// [{name, complete_to}], horizon}`, the number of paths, whether the record is real, and per
/// channel the horizon to which every path is explored (null where every path is explored to its
/// end), which `horizon` holds by name for each channel that has one.
fn observations_summary(row: &Value) -> Option<Value> {
    let record = row.get("observations")?;
    if let Some(paths) = record.get("paths").filter(|paths| paths.is_object()) {
        let mut horizon = serde_json::Map::new();
        let names = record["channels"].as_array()?;
        let channels = paths["channels"]
            .as_array()?
            .iter()
            .zip(names)
            .map(|(sets, channel)| {
                let name = channel["name"].clone();
                if sets["complete_to"].is_object() {
                    horizon.insert(
                        name.as_str().unwrap_or_default().to_owned(),
                        sets["complete_to"].clone(),
                    );
                }
                json!({"name": name, "complete_to": sets["complete_to"]})
            })
            .collect::<Vec<_>>();
        return Some(json!({
            "paths": paths["paths"],
            "real": paths["real"],
            "channels": channels,
            "horizon": horizon,
        }));
    }
    let channels = record["channels"].as_array()?;
    let mut horizon = serde_json::Map::new();
    let channels = channels
        .iter()
        .map(|channel| {
            let elements = channel["elements"].as_array().map_or(0, Vec::len);
            if channel["open"].is_object() {
                horizon.insert(
                    channel["name"].as_str().unwrap_or_default().to_owned(),
                    json!({"elements": elements, "opening": channel["open"]["opening"]}),
                );
            }
            json!({
                "name": channel["name"],
                "elements": elements,
                "closed": channel["closed"],
                "open": channel["open"],
            })
        })
        .collect::<Vec<_>>();
    Some(json!({"channels": channels, "horizon": horizon}))
}

/// What one program's baseline run produced.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProgramResult {
    pub class: ResultClass,
    pub cause: Option<String>,
    /// The baseline row exactly as kink-campaign's report encodes it; comparable only. It holds
    /// the run's final configurations as KORE text, one per terminal, in its whole-term (or
    /// cells) side, the one place the result holds them ([`Self::final_terms`]).
    pub baseline: Option<Value>,
    /// The final state of each leaf of the diagnostic run as KORE text (unknown and error runs
    /// that have leaves); `None` for a comparable result, whose final configurations are its
    /// baseline row's.
    pub final_configuration: Option<Vec<String>>,
    /// Each end's summary, `{head, class}`, in the order of the baseline row's whole-term (or
    /// cells) side ([`Self::final_terms`]; `evidence::EndReader::summary`): comparable only,
    /// `None` otherwise. Outside the key and
    /// the run digest; a record names its writer's build, so every record this build reads has
    /// it.
    pub ends: Option<Value>,
    /// The run's rule coverage; `None` when no run produced any.
    pub coverage: Option<TestCoverage>,
    /// The wall time of the program's live baseline run in milliseconds (the campaign's run,
    /// recorded by the command's baseline session); outside the key and the run digest.
    pub wall_ms: Option<u64>,
    /// k-rust's contradicted-claim records of the baseline run (the campaign's, or the diagnostic
    /// run's), its definition's load included, as specification diagnostics (re-pin adoption
    /// A-1, `report::specification_diagnostics_value`); an empty array when there are none or no
    /// run produced any. Outside the key and the run digest.
    pub specification_diagnostics: Value,
    /// k-rust's count of the baseline run's undecided solver answers (`smtUnknowns`; decision
    /// D-7 (a1): reported, never an exclusion); 0 without a run or without Z3.
    pub smt_unknowns: usize,
    /// kink's count of the undecided solver answers of the questions it asked outside the
    /// baseline run to judge it (kink-campaign `RunNotes::decider_smt_unknowns`; for a diagnostic
    /// run, its adapter's leaf feasibility); reported, never an exclusion; 0 without a run or
    /// without Z3. Outside the key and the run digest.
    pub decider_smt_unknowns: usize,
    /// The entries of the baseline run's `shortCircuitReadings` list that exclude it
    /// (`short-circuit-reading`; kink-native
    /// `DefinitionExclusions::counting_short_circuit_readings`, or `state_short_circuit_readings`
    /// for a run excluded by its initial state, on the diagnostic run), as
    /// [`crate::exclusion::readings_value`] prints them: the step that excluded the run. An empty
    /// array for every other result. Outside the key and the run digest.
    pub short_circuit_readings: Value,
    /// Why the result is not a function of its key ([`host_dependence`]); `None` when it is.
    /// Outside the record: a result with a host dependence is never written.
    pub host: Option<HostDependence>,
}

impl ProgramResult {
    /// The observation summary of the result's baseline row (`observations`, under
    /// `[observe]`): null without a record.
    #[must_use]
    pub fn observations(&self) -> Value {
        self.baseline
            .as_ref()
            .and_then(observations_summary)
            .unwrap_or(Value::Null)
    }
}

impl ProgramResult {
    fn refused(cause: String) -> Self {
        Self {
            class: ResultClass::Refused,
            cause: Some(cause),
            baseline: None,
            final_configuration: None,
            ends: None,
            coverage: None,
            wall_ms: None,
            specification_diagnostics: json!([]),
            smt_unknowns: 0,
            decider_smt_unknowns: 0,
            short_circuit_readings: json!([]),
            host: None,
        }
    }

    /// The run digest of the baseline row.
    pub fn run_sha256(&self) -> Option<Sha256Digest> {
        self.baseline.as_ref().and_then(run_digest)
    }

    /// The final configurations as KORE text: a comparable result's ends, from its baseline
    /// row, else the diagnostic run's leaves; `None` when the result has neither, or when an end
    /// of its baseline row is not a text.
    #[must_use]
    pub fn final_terms(&self) -> Option<Vec<&str>> {
        match &self.baseline {
            Some(row) => row_final_terms(row),
            None => self
                .final_configuration
                .as_ref()
                .map(|terms| terms.iter().map(String::as_str).collect()),
        }
    }
}

/// The whole-term (or cells) value of a baseline row: the first side that holds one, as the
/// row's KORE texts; `None` when no side holds one, or when an entry of it is not a text, which
/// no row kink-campaign writes holds.
fn row_final_terms(row: &Value) -> Option<Vec<&str>> {
    row["run"]["sides"]
        .as_array()?
        .iter()
        .find_map(|side| side["normal"]["whole-term"].as_array())?
        .iter()
        .map(Value::as_str)
        .collect()
}

/// A result record's final configurations as KORE text, as [`ProgramResult::final_terms`] gives
/// them: a comparable record's from its baseline row's whole-term (or cells) side, any other
/// record's from its `final_configuration`; `None` when it has neither, or when an entry of the
/// one it reads is not a text, which no record kink-flow writes holds.
#[must_use]
pub fn record_final_configuration(record: &Value) -> Option<Vec<&str>> {
    match record.get("baseline").filter(|row| !row.is_null()) {
        Some(row) => row_final_terms(row),
        None => record["final_configuration"]
            .as_array()?
            .iter()
            .map(Value::as_str)
            .collect(),
    }
}

/// Runs the campaign calls of one command over one admitted specification: each program's
/// zero-mutant campaign (`coverage`) and the kill search's calls (`run`). It holds the command's
/// one validator (the specification's), so the baseline compiles once, and the command's one
/// in-memory baseline session, so each program's baseline runs live at most once per command.
pub struct BaselineRunner<'a> {
    spec: &'a AdmittedSpec,
    main_module: &'a str,
    module: String,
    generations: Vec<CandidateGeneration<'a>>,
    budget: ExecutionBudget,
    /// `[budget] baseline_max_work`: the work bound of every baseline result run of the command.
    baseline_max_work: Option<u64>,
    /// `[budget] smt_resource_limit`: the solver budget of every run of the command.
    smt_resource_limit: std::num::NonZeroU32,
    /// `[stop]`: where every result run of the command ends besides its own end, each program
    /// with its own count (`FlowManifest::campaign_stop`).
    stop: kink_campaign::Stop,
    /// `[observe]`: the observation channels every result run of the command is compared by
    /// (`FlowManifest::campaign_observe`).
    observe: kink_campaign::Observe,
    authors: RuleAuthors,
    /// The command's session (every call uses the all-normal classifier; the session re-applies
    /// a call's classifier on every reused baseline run, flow F-16).
    session: RefCell<BaselineSession<'a>>,
    /// Diagnostic runs this command made (a refused baseline that did not stop on time).
    diagnostic: Cell<usize>,
    /// The compiled ids of each authored rule a run can observe, for causes; computed on
    /// first use.
    observable: OnceCell<Vec<BTreeSet<String>>>,
    /// What kill evidence and end summaries read from the compiled specification (CF-16), built
    /// on first use.
    ends: OnceCell<EndReader>,
    /// The front end's renderer of kill evidence (`FlowManifest::end_renderer`).
    renderer: crate::evidence::Renderer,
    /// The depth up to which every baseline run of the command collects rule windows and syntax
    /// paths ([`Self::with_depth`]); a stored record answers only where it collected at least as
    /// far ([`record_answers`]).
    depth: std::num::NonZeroUsize,
}

impl<'a> BaselineRunner<'a> {
    /// The runner of a command at the manifest's `[coverage] depth`.
    pub fn new(spec: &'a AdmittedSpec, manifest: &'a FlowManifest) -> Result<Self, String> {
        Self::with_depth(spec, manifest, manifest.coverage.depth)
    }

    /// The runner of a command whose baseline runs collect rule windows and syntax paths up to
    /// `depth` (`coverage --depth`, else `[coverage] depth`): every run it makes records them,
    /// and a stored record collected at a smaller depth does not answer, so its program runs
    /// again and its record is replaced by one at `depth` (kink-native `TestCoverage::depth`).
    pub fn with_depth(
        spec: &'a AdmittedSpec,
        manifest: &'a FlowManifest,
        depth: std::num::NonZeroU64,
    ) -> Result<Self, String> {
        let depth = usize::try_from(depth.get())
            .ok()
            .and_then(std::num::NonZeroUsize::new)
            .ok_or_else(|| format!("the depth {depth} does not fit this host's word"))?;
        // The runner needs a generation. A checked empty discovery yields zero candidates,
        // so no operator code and no mutant can be reached (kink-corpus `baseline_only`).
        let discovery = Discovery::empty(spec.validator.baseline(), false, false);
        let generation = select(&discovery, SelectionPolicy::Each, 1)
            .and_then(|selection| {
                selection.fold(BASELINE_ONLY_OPERATOR, |_| -> Patch {
                    unreachable!("an empty discovery has no fold calls")
                })
            })
            .map_err(|e| format!("cannot build the empty generation: {e}"))?;
        assert!(generation.candidates().is_empty());
        Ok(Self {
            spec,
            main_module: &manifest.spec.main_module,
            module: k_rust::kast::identifier::encode(&manifest.spec.main_module),
            generations: vec![generation],
            budget: execution_budget(manifest.budget),
            baseline_max_work: manifest.budget.baseline_max_work,
            smt_resource_limit: manifest.budget.smt_resource_limit,
            stop: manifest.campaign_stop(),
            observe: manifest.campaign_observe(),
            authors: RuleAuthors::of(&spec.compiled),
            session: RefCell::new(
                BaselineSession::new(&spec.validator)
                    .assuming(manifest.assume_joined_k())
                    .with_baseline_data(spec.data.clone())
                    .with_bindings(crate::coverage::binding_collection(spec, manifest))
                    .with_depth(depth),
            ),
            diagnostic: Cell::new(0),
            observable: OnceCell::new(),
            ends: OnceCell::new(),
            renderer: manifest.end_renderer.clone(),
            depth,
        })
    }

    /// The depth up to which the command's baseline runs collect rule windows and syntax paths.
    pub const fn depth(&self) -> std::num::NonZeroUsize {
        self.depth
    }

    /// What the last campaign call of this command ran: wall times, leaf censuses and baseline
    /// coverage, as the session recorded them (outside every evidence row, digest and key).
    pub fn last_call(&self) -> CallRecording {
        self.session.borrow().last_call().clone()
    }

    /// The command's reader of ends: the printer, cells and maps of the compiled specification
    /// (CF-16), and the front end's renderer of kill evidence.
    pub fn end_reader(&self) -> &EndReader {
        self.ends.get_or_init(|| {
            EndReader::of(&self.spec.compiled)
                .projecting(self.spec.result.cells().cloned())
                .rendering(self.renderer.clone(), self.spec.result.not_compared.clone())
        })
    }

    /// The specification's definition exclusion as a document's `spec.exclusion` prints it
    /// ([`crate::exclusion::definition_exclusion`]; null when there is none).
    pub fn definition_exclusion(&self) -> Value {
        if self.spec.exclusions.definition_exclusion().is_none() {
            return Value::Null;
        }
        crate::exclusion::definition_exclusion(self.spec, self.end_reader())
    }

    /// The rules the specification's short-circuit analysis flags, as a document's
    /// `spec.short_circuit` prints them ([`crate::exclusion::short_circuit`]; null when it flags
    /// none).
    pub fn short_circuit(&self) -> Value {
        if !self.spec.exclusions.short_circuit_flagged() {
            return Value::Null;
        }
        crate::exclusion::short_circuit(self.spec, self.end_reader())
    }

    /// Why every run of `test` on the baseline is excluded, read as admission reads it
    /// (`crate::admit::InputSession::exclusion` and its depth-0 run) on `backend`, a load of the
    /// specification's compiled KORE: the definition exclusion, else the exclusion of the
    /// test's initial configuration on the definition `backend` selects, as the campaign runner
    /// reads both for a run judged with its lists, here those of the baseline run whose facts
    /// are `facts` (its list holds the initial configuration's normalization).
    fn program_exclusion(
        &self,
        backend: &mut Backend,
        test: &TestCase,
        facts: &kink_native::execution::RunFacts,
    ) -> Option<crate::admit::ProgramExclusion> {
        use crate::exclusion::ExclusionScope;
        let exclusions = &self.spec.exclusions;
        if let Some(exclusion) = exclusions.definition_exclusion() {
            return Some(crate::admit::ProgramExclusion {
                exclusion,
                scope: ExclusionScope::Definition,
            });
        }
        let definition = backend.select_definition(None).ok()?;
        exclusions
            .state_exclusion(&definition, &test.initial_state, facts)
            .map(|exclusion| crate::admit::ProgramExclusion {
                exclusion,
                scope: ExclusionScope::InitialState,
            })
    }

    /// The budget's `time_ms`, as causes say it.
    pub fn time_ms(&self) -> u128 {
        self.budget.time.as_millis()
    }

    /// The compiled ids of each authored rule of the specification a run can observe (a rule
    /// that compiles to a rewrite rule).
    pub fn observable_rules(&self) -> &[BTreeSet<String>] {
        self.observable
            .get_or_init(|| observable_rules(self.spec, &self.authors))
    }

    /// One campaign call of this command over `tests` (their oracles as given): the
    /// specification's validator and module, the all-normal classifier, the manifest's budget,
    /// no step observation, and every baseline run through the command's session. Every baseline
    /// result run of the call is bounded by `[budget] baseline_max_work`, whatever `options` say,
    /// so every baseline of a command has one bound and the results update and the kill search
    /// share the session's runs; likewise every run's solver queries by `[budget]
    /// smt_resource_limit`, and every result run, baseline and mutant, ends at `[stop]`.
    pub fn call(
        &self,
        tests: &[TestCase],
        generations: &[CandidateGeneration<'_>],
        options: &CampaignOptions,
    ) -> Result<CampaignRun, CampaignFailure> {
        let mut options = options.clone();
        options.run.baseline_max_work = self.baseline_max_work;
        options.run.smt_resource_limit = self.smt_resource_limit;
        options.run.stop = self.stop;
        options.run.observe = self.observe;
        let options = &options;
        let campaign = Campaign {
            validator: &self.spec.validator,
            module: &self.module,
            observation: &[],
            classify: &classify,
            tests,
            budget: self.budget,
        };
        run_campaign_multi_with(
            &campaign,
            generations,
            options,
            &mut self.session.borrow_mut(),
        )
    }

    /// The baseline run of `test` with the specification's oracles, as [`Self::run`] makes it,
    /// and the campaign's evidence of it: what the run recorded (its observations included) and
    /// its ends. `Err` says why the campaign gave the run no sides (it refused the baseline, or
    /// the run failed), naming what ended the run where this command's live run of it says
    /// ([`refused_run`]).
    pub(crate) fn evidence_of(&self, mut test: TestCase) -> Result<TestEvidence, String> {
        test.oracles = self.spec.result.oracles();
        let options = CampaignOptions {
            schedule: ScheduleMode::FirstKill,
            selection: kink_campaign::SelectionPolicy::None,
            share_evidence: true,
            run: kink_campaign::RunOptions::default(),
            compile_workers: 1,
        };
        let run = self
            .call(std::slice::from_ref(&test), &self.generations, &options)
            .map_err(|failure| {
                let recording = self.last_call();
                let live_stop = recording
                    .baseline_of(&test.id)
                    .map(|live| live.run.census.stop);
                refused_run(&failure, live_stop, self.budget.time.as_millis())
            })?;
        let [evidence] = <[TestEvidence; 1]>::try_from(run.baseline)
            .map_err(|_| "the campaign gave no single baseline run".to_owned())?;
        match evidence.run {
            SideRun::Sides { .. } => Ok(evidence),
            SideRun::Failed(kind) => Err(format!(
                "the campaign gave the run no sides: {}",
                kind.exclusion().map_or("a failed run", |e| e.name())
            )),
        }
    }

    /// [`Self::call`] with each mutant's programs ordered once it compiles: `first` gets the
    /// compiled edit of the side the programs run on and names the programs that run first
    /// (kink-campaign `run_campaign_multi_ordered`; the kill search's witness order).
    pub fn call_ordered(
        &self,
        tests: &[TestCase],
        generations: &[CandidateGeneration<'_>],
        options: &CampaignOptions,
        first: &mut FirstTests<'_>,
    ) -> Result<CampaignRun, CampaignFailure> {
        let mut options = options.clone();
        options.run.baseline_max_work = self.baseline_max_work;
        // The manifest's units bound every solver query of the kill search too, as `call`'s do:
        // the tier-1 context names them (`budget_value`'s `smt`), so a call under any other units
        // would write an outcome its key does not name (CF-33d review).
        options.run.smt_resource_limit = self.smt_resource_limit;
        options.run.stop = self.stop;
        options.run.observe = self.observe;
        let campaign = Campaign {
            validator: &self.spec.validator,
            module: &self.module,
            observation: &[],
            classify: &classify,
            tests,
            budget: self.budget,
        };
        run_campaign_multi_ordered(
            &campaign,
            generations,
            &options,
            &mut self.session.borrow_mut(),
            first,
        )
    }

    /// The two elements of the observation difference `verdict` reports for `test` (a test of a
    /// call of this command, with the specification's oracles), whose baseline's run recorded
    /// `record`: kink-campaign `observed_difference` under the options every call of the command
    /// runs with, so the capture run of the baseline is the baseline's request.
    ///
    /// # Errors
    ///
    /// Why the difference is not re-derived (kink-campaign `observed_difference`).
    pub fn observed_difference(
        &self,
        test: &TestCase,
        record: &kink_campaign::BaselineRecord,
        verdict: &kink_campaign::ObservationVerdict,
    ) -> Result<kink_campaign::ObservedDifference, String> {
        let options = kink_campaign::RunOptions {
            baseline_max_work: self.baseline_max_work,
            smt_resource_limit: self.smt_resource_limit,
            stop: self.stop,
            observe: self.observe,
            ..kink_campaign::RunOptions::default()
        };
        let campaign = Campaign {
            validator: &self.spec.validator,
            module: &self.module,
            observation: &[],
            classify: &classify,
            tests: std::slice::from_ref(test),
            budget: self.budget,
        };
        kink_campaign::observed_difference(&campaign, &options, test, record, verdict)
    }

    /// The compiled baseline's rule authors: the baseline sentences behind each compiled id.
    pub const fn authors(&self) -> &RuleAuthors {
        &self.authors
    }

    /// `{live, reused, diagnostic}`: the baseline runs this command made live, the baseline
    /// requests of its campaign calls answered by one of them, and the diagnostic runs it made
    /// for refused baselines that did not stop on time (outside every digest and key).
    pub fn baseline_runs(&self) -> Value {
        let session = self.session.borrow();
        json!({
            "live": session.live_runs(),
            "reused": session.reused_runs(),
            "diagnostic": self.diagnostic.get(),
        })
    }

    /// Run one admitted program (its oracles are replaced by the specification's,
    /// [`crate::observed::ResultProjection::oracles`]). Its baseline runs live unless this
    /// command already ran the same program live.
    pub fn run(&self, mut test: TestCase) -> ProgramResult {
        test.oracles = self.spec.result.oracles();
        let options = CampaignOptions {
            schedule: ScheduleMode::FirstKill,
            selection: kink_campaign::SelectionPolicy::None,
            share_evidence: true,
            run: kink_campaign::RunOptions::default(),
            compile_workers: 1,
        };
        let result = self.call(std::slice::from_ref(&test), &self.generations, &options);
        let recording = self.last_call();
        let live = recording.baseline_of(&test.id);
        let live_stop = live.map(|live| live.run.census.stop);
        let wall_ms = live.map(|live| millis(live.run.wall));
        let mut result = match result {
            Ok(run) => {
                assert!(run.mutants.is_empty() && run.baseline.len() == 1);
                let evidence = &run.baseline[0];
                // The campaign admits a baseline run that contradicts a trusted claim and makes
                // only its own test unknown (re-pin decision 2, per test): such a program is
                // never comparable.
                if let SideRun::Failed(kind) = evidence.run {
                    let mut result = self.diagnose(
                        &test,
                        CampaignFailureKind::BaselineOracleFailed,
                        kind.exclusion(),
                        live_stop,
                        &format!(
                            "the campaign runner gave the baseline run no sides: {}",
                            kind.exclusion().map_or("a failed run", |e| e.name())
                        ),
                    );
                    result.wall_ms = wall_ms;
                    return result;
                }
                // Under `[observe]`, a run its deterministic bounds cut is compared by its
                // channels up to their horizons ([`ResultClass::ComparablePrefix`]).
                let prefix = match &evidence.notes.observation {
                    Some(kink_campaign::Observation::Recorded(record)) if record.prefix => {
                        Some(record)
                    }
                    _ => None,
                };
                // A prefix program none of whose channels kept an element within its budget
                // observed nothing: no mutant can differ from it within its horizons, so it
                // covers nothing, and the class is `unknown` (a function of the key). An element
                // kept undecided (under `count`) is an observed event: END against it decides;
                // and a channel closed by a cycle observed its silence, which an element decides.
                // A run of several paths observed nothing where no path kept a prefix.
                if let Some(record) = prefix
                    && record.observed_nothing()
                {
                    return ProgramResult {
                        class: ResultClass::Unknown,
                        cause: Some(observed_nothing_cause(record)),
                        baseline: None,
                        final_configuration: None,
                        ends: None,
                        coverage: run.baseline_coverage.first().cloned(),
                        wall_ms,
                        specification_diagnostics: json!([]),
                        smt_unknowns: evidence.notes.smt_unknowns,
                        decider_smt_unknowns: evidence.notes.decider_smt_unknowns,
                        short_circuit_readings: json!([]),
                        host: None,
                    };
                }
                ProgramResult {
                    class: if prefix.is_some() {
                        ResultClass::ComparablePrefix
                    } else {
                        ResultClass::Comparable
                    },
                    cause: None,
                    baseline: Some(baseline_row(evidence)),
                    final_configuration: None,
                    ends: final_ends(&evidence.run).map(|ends| {
                        if self.stop.is_none() {
                            self.end_reader().summaries(ends)
                        } else {
                            self.end_reader()
                                .halted_summaries(ends, &evidence.stop_ends)
                        }
                    }),
                    coverage: run.baseline_coverage.first().cloned(),
                    wall_ms: None,
                    specification_diagnostics: crate::report::specification_diagnostics_value(
                        &evidence.notes.contradicted_claims,
                    ),
                    smt_unknowns: evidence.notes.smt_unknowns,
                    decider_smt_unknowns: evidence.notes.decider_smt_unknowns,
                    short_circuit_readings: json!([]),
                    host: None,
                }
            }
            // No second full-length run (flow F-13, README 6.4): when this command's live run
            // of the baseline stopped on time, the class and the cause come from that run. A
            // session record never makes a program comparable: only the campaign admitting
            // the baseline does (the arm above).
            Err(_) if live.is_some_and(|live| live.run.census.stop == RunStop::Time) => {
                let live = live.expect("checked");
                ProgramResult {
                    class: ResultClass::Timeout,
                    cause: Some(timeout_cause(
                        self.budget.time.as_millis(),
                        self.baseline_max_work,
                        &live.run.census,
                        self.observable_rules(),
                    )),
                    baseline: None,
                    final_configuration: None,
                    ends: None,
                    coverage: live.coverage.clone(),
                    wall_ms: None,
                    specification_diagnostics: json!([]),
                    smt_unknowns: 0,
                    decider_smt_unknowns: 0,
                    short_circuit_readings: json!([]),
                    host: Some(HostDependence::Time),
                }
            }
            // A baseline that `[budget] baseline_max_work` stopped: the bound stops a run
            // deterministically, so the class is `unknown`, a function of the key, which names
            // the bound; the class and the cause come from this command's live run, with no
            // diagnostic run ([`work_bound_refusal`]).
            Err(failure)
                if work_bound_refusal(
                    failure.kind(),
                    failure.exclusion(),
                    self.baseline_max_work,
                    live.is_some_and(|live| {
                        live.run.census.leaves.contains_key(&HaltClass::WorkBound)
                    }),
                ) =>
            {
                let (bound, live) = (
                    self.baseline_max_work.expect("checked"),
                    live.expect("checked"),
                );
                ProgramResult {
                    class: ResultClass::Unknown,
                    cause: Some(work_bound_cause(
                        bound,
                        &live.run.census,
                        self.observable_rules(),
                    )),
                    baseline: None,
                    final_configuration: None,
                    ends: None,
                    coverage: live.coverage.clone(),
                    wall_ms: None,
                    specification_diagnostics: json!([]),
                    smt_unknowns: 0,
                    decider_smt_unknowns: 0,
                    short_circuit_readings: json!([]),
                    host: None,
                }
            }
            // A baseline whose stop condition was left undecided at an arrival, or refused at
            // one: whether the run ended where the condition says is not known, so the program is
            // not judged; the cause names the arrival and the condition's reason, and the result
            // is never kept ([`HostDependence::StopCondition`]). No diagnostic run: it would ask
            // the same condition at the same arrivals.
            Err(failure) if failure.stop_condition().is_some() => ProgramResult {
                class: ResultClass::Unknown,
                cause: Some(format!(
                    "stop-condition: the stop condition ([stop] when) of this program's run gave \
                     no answer the run can rest on: {}",
                    failure.stop_condition().unwrap_or_default()
                )),
                baseline: None,
                final_configuration: None,
                ends: None,
                coverage: live.and_then(|live| live.coverage.clone()),
                wall_ms: None,
                specification_diagnostics: json!([]),
                smt_unknowns: 0,
                decider_smt_unknowns: 0,
                short_circuit_readings: json!([]),
                host: Some(HostDependence::StopCondition),
            },
            Err(failure) => self.diagnose(
                &test,
                failure.kind(),
                failure.exclusion(),
                live_stop,
                &format!("the campaign runner refused the baseline run ({failure})"),
            ),
        };
        result.wall_ms = wall_ms;
        result
    }

    fn error(&self, cause: String) -> ProgramResult {
        ProgramResult {
            class: ResultClass::Error,
            cause: Some(cause),
            baseline: None,
            final_configuration: None,
            ends: None,
            coverage: None,
            wall_ms: None,
            specification_diagnostics: json!([]),
            smt_unknowns: 0,
            decider_smt_unknowns: 0,
            short_circuit_readings: json!([]),
            host: Some(HostDependence::Failure),
        }
    }

    /// The campaign refused the baseline run, or gave it no sides, and it did not stop on time:
    /// run the initial state once more through the execution adapter, for the class, the cause,
    /// the final states and the coverage. When the campaign named the exclusion of the baseline
    /// run (`exclusion`), the cause's hint is that exclusion's, not one read from the leaves'
    /// shape (re-pin adoption A-1b): an excluded run's leaves can all be clean. An exclusion that
    /// holds for every run of the program, the definition's or its initial configuration's, is
    /// said as `check` says it ([`crate::exclusion::program_detail`]); any other as
    /// [`exclusion_hint`] says it, a short-circuit reading with the entries of the diagnostic
    /// run's list that count against it (the step that excluded the run, which the result also
    /// carries as data, [`ProgramResult::short_circuit_readings`]). The diagnostic run is the
    /// campaign's request: the same budget and `[budget] baseline_max_work`. `live_stop` is how
    /// this command's live run of the baseline ended (`None` when none ran), which with the class
    /// and the exclusion says whether the result depends on the host ([`host_dependence`]).
    fn diagnose(
        &self,
        test: &TestCase,
        kind: CampaignFailureKind,
        exclusion: Option<Exclusion>,
        live_stop: Option<RunStop>,
        refused: &str,
    ) -> ProgramResult {
        self.diagnostic.set(self.diagnostic.get() + 1);
        // Loaded as the campaign runner loads a side (kink-campaign `LoadedSide::load`): the
        // parsed KORE also gives the definition exclusions and the symbol sorts the cause of a
        // leaf without a terminal value is read with ([`Self::non_value_cause`]).
        let loaded = parse_definition(&self.spec.compiled.artifacts().definition_kore)
            .map_err(|e| e.to_string())
            .and_then(|parsed| {
                Backend::from_definition(
                    parsed.clone(),
                    k_rust::kast::identifier::encode(self.main_module),
                    kink_native::backend_options(self.smt_resource_limit),
                )
                .map(|backend| (parsed, backend))
                .map_err(|e| e.to_string())
            });
        let (parsed, mut backend) = match loaded {
            Ok(loaded) => loaded,
            Err(e) => return self.error(format!("{refused}; no diagnostic run: {e}")),
        };
        let adapter = ExecutionAdapter::with_profile(SolverProfile::BUILD);
        // The campaign's request: with a stop, the staged run to the program's count.
        let execution = match self.stop.execute_result(
            &adapter,
            &mut backend,
            &test.id,
            &test.initial_state,
            self.budget,
            ResultRun {
                max_work: self.baseline_max_work,
                ..ResultRun::default()
            },
        ) {
            Ok(execution) => execution,
            Err(e) => return self.error(format!("{refused}; the diagnostic run failed: {e:?}")),
        };
        let coverage = Some(TestCoverage::of_execution(
            &test.id,
            &execution,
            &self.authors,
        ));
        if execution.timed_out() {
            // Only when the campaign's own run ended otherwise (or ran no baseline): the
            // diagnostic run then hit the time bound itself.
            return ProgramResult {
                class: ResultClass::Timeout,
                cause: Some(format!(
                    "the run did not finish within time_ms = {}",
                    self.budget.time.as_millis()
                )),
                baseline: None,
                final_configuration: None,
                ends: None,
                coverage,
                wall_ms: None,
                specification_diagnostics: json!([]),
                smt_unknowns: 0,
                decider_smt_unknowns: 0,
                short_circuit_readings: json!([]),
                host: Some(HostDependence::Time),
            };
        }
        let leaves = execution.leaves();
        let class = match kind {
            CampaignFailureKind::BaselineOracleFailed => ResultClass::Unknown,
            _ => ResultClass::Error,
        };
        let halts = leaves
            .iter()
            .map(|leaf| {
                format!(
                    "{} at depth {}",
                    kebab(&format!("{:?}", leaf.halt)),
                    leaf.branch.depth
                )
            })
            .collect::<Vec<_>>();
        // The entries that exclude the run, as the campaign runner reads them for the baseline
        // (the specification's exclusions are those of the compiled definition it loads): those
        // that count against the run, else, on a definition the analysis clears, those that count
        // against its initial state, the one route by which such a run is excluded for the
        // reading.
        let readings = if exclusion == Some(Exclusion::ShortCircuitReading) {
            let exclusions = &self.spec.exclusions;
            let facts = execution.facts();
            let counting = exclusions.counting_short_circuit_readings(facts);
            if counting.is_empty() {
                exclusions.state_short_circuit_readings(facts)
            } else {
                counting
            }
            .into_iter()
            .cloned()
            .collect::<Vec<_>>()
        } else {
            Vec::new()
        };
        let hint = if let Some(exclusion) = exclusion {
            match self.program_exclusion(&mut backend, test, execution.facts()) {
                Some(known) if known.exclusion == exclusion && !readings.is_empty() => format!(
                    "the run is excluded ({}): {}; the step: {}",
                    exclusion.name(),
                    known.detail(),
                    crate::exclusion::readings_text(&readings)
                ),
                Some(known) if known.exclusion == exclusion => {
                    format!(
                        "the run is excluded ({}): {}",
                        exclusion.name(),
                        known.detail()
                    )
                }
                _ if !readings.is_empty() => format!(
                    "{}; the step: {}",
                    exclusion_hint(exclusion, false),
                    crate::exclusion::readings_text(&readings)
                ),
                _ if exclusion == Exclusion::ShortCircuitReading
                    && execution.facts().short_circuit_readings.is_none() =>
                {
                    format!(
                        "{}; the backend lists no short-circuit readings, so no run of a \
                         definition whose analysis flags a rule can be judged on it",
                        exclusion_hint(exclusion, false)
                    )
                }
                _ => exclusion_hint(exclusion, !execution.facts().contradicted_claims.is_empty()),
            }
        } else if let Some(bound) = self
            .baseline_max_work
            .filter(|_| leaves.iter().any(|leaf| leaf.halt == HaltClass::WorkBound))
        {
            format!("the run reached baseline_max_work = {bound}")
        } else if leaves.iter().any(|leaf| leaf.halt == HaltClass::DepthBound) {
            format!(
                "the run reached max_depth = {}",
                self.budget.max_depth.unwrap_or_default()
            )
        } else if !leaves.is_empty()
            && leaves.iter().all(|leaf| {
                matches!(
                    leaf.halt,
                    HaltClass::Stuck | HaltClass::Trivial | HaltClass::Vacuous
                )
            })
        {
            self.non_value_cause(&mut backend, &parsed, test, leaves)
                .unwrap_or_else(|| {
                    format!(
                        "{NON_VALUE_LEAD} (for example it holds a collection kink cannot compare, \
                         such as one with a Bytes key, an unevaluated function or a symbolic term)"
                    )
                })
        } else {
            "a path did not end".to_owned()
        };
        let final_configuration = Some(
            leaves
                .iter()
                .map(|leaf| leaf.branch.state.to_string())
                .collect::<Vec<_>>(),
        );
        ProgramResult {
            class,
            cause: Some(format!(
                "{refused}; {hint}; leaves: {}",
                if halts.is_empty() {
                    "none".to_owned()
                } else {
                    halts.join(", ")
                }
            )),
            baseline: None,
            final_configuration,
            ends: None,
            coverage,
            wall_ms: None,
            specification_diagnostics: crate::report::specification_diagnostics_value(
                &execution.facts().contradicted_claims,
            ),
            smt_unknowns: execution.facts().smt_unknowns,
            decider_smt_unknowns: execution.facts().decider_smt_unknowns,
            short_circuit_readings: crate::exclusion::readings_value(&readings),
            host: host_dependence(
                class,
                exclusion,
                live_stop,
                diagnostic_host_exclusion(&mut backend, &execution),
            ),
        }
    }

    /// The hint for a baseline every path of which ended but which the runner refused: which
    /// leaf is incomplete and why (fz26 KINK-CAUSE-SUBTERM). TV-01 is the end check of `stuck`
    /// leaves: the first such leaf, in the run's order, whose state's term has no terminal value
    /// is named with the first node of that term, in pre-order, that fails its own test
    /// (kink-native `ObservationDecider::first_non_value`). A `trivial` leaf is an undefined step,
    /// whose pre-step configuration needs only to exist (kink27 R3-UNDEF-BRIDGE): one the adapter
    /// did not show feasible, whose ground term has no terminal value and that k-rust does not
    /// show to exist (`ObservationDecider::configuration_exists`), is named in the same order.
    /// The decider is built as the campaign runner builds the baseline's (`Runtime::judge_with`):
    /// on the definition this backend selected, with its exclusions' collection trust and the
    /// data ends of the session's baseline facts. A leaf whose state is not one decided or
    /// feasible term is named when no leaf is named for its term. `None` when neither exists, or
    /// no definition can be selected.
    ///
    /// The cause is the baseline's own judgement: whether an end is data under a mutant's
    /// definition is judged by the runner for each pair (`judge_across`), never here.
    fn non_value_cause(
        &self,
        backend: &mut Backend,
        parsed: &KoreDefinition,
        test: &TestCase,
        leaves: &[AdaptedLeaf],
    ) -> Option<String> {
        let selected = backend.select_definition(None).ok()?;
        let trusted = DefinitionExclusions::of(
            parsed,
            &selected,
            &self.spec.compiled.compile_options().builtin_source_prefixes,
        )
        .collections_trusted();
        let session = self.session.borrow();
        let computed;
        let facts = match session.baseline_data() {
            Some(facts) => facts,
            None => {
                computed = DataFacts::of(&selected, session.assume_joined());
                &computed
            }
        };
        let own = data_ends(facts);
        let terms = leaf_terms(leaves, parsed);
        backend
            .with_solver(None, |definition, solver| {
                let decider = ObservationDecider::new(
                    definition,
                    solver,
                    TestInitialState::of_test(&test.initial_state),
                )
                .trusting_collections(trusted)
                .judging_data(own, own);
                // A host's refusal of a stack a judgement needed names the host, not a leaf.
                let cause = decider.host_refusal_during(|| {
                    let mut undecided = None;
                    for (leaf, term) in leaves.iter().zip(&terms) {
                        let trivial = leaf.halt == HaltClass::Trivial;
                        match term {
                            Ok(LeafTerm::Term(term)) if trivial => {
                                let feasible = matches!(
                                    leaf.feasibility,
                                    LeafFeasibility::Syntactic | LeafFeasibility::Solver
                                );
                                if !feasible
                                    && decider.terminal_value(term).is_none()
                                    && !decider.configuration_exists(term)
                                {
                                    return Some(format!(
                                        "{UNDEFINED_STEP_LEAD}: in the {}, k-rust does not show it \
                                     defined on this definition, or kink cannot read it back \
                                     exactly (it may hold an application of a function not \
                                     declared total that no equation reduced, map keys or set \
                                     elements not shown apart, a collection term of a definition \
                                     with an axiom rooted at a collection role symbol, or a \
                                     domain value without an injective codec)",
                                        leaf_name(leaf)
                                    ));
                                }
                            }
                            Ok(LeafTerm::Term(term)) => {
                                if let Some(failure) = decider.first_non_value(term) {
                                    return Some(format!(
                                        "{NON_VALUE_LEAD}: in the {}, {}",
                                        leaf_name(leaf),
                                        non_value_text(&failure)
                                    ));
                                }
                            }
                            Ok(LeafTerm::Undecided) if undecided.is_none() => {
                                undecided = Some(if trivial {
                                    format!(
                                        "{UNDEFINED_STEP_LEAD}: the state of the {} is not one \
                                     ground term without a path condition, and kink did not \
                                     show it feasible",
                                        leaf_name(leaf)
                                    )
                                } else {
                                    format!(
                                        "{NON_VALUE_LEAD}: the state of the {} is not one ground \
                                     term without a path condition",
                                        leaf_name(leaf)
                                    )
                                });
                            }
                            _ => {}
                        }
                    }
                    undecided
                });
                Ok::<_, k_rust::backend::BackendError>(cause.unwrap_or_else(|refused| {
                    Some(format!("kink could not judge the leaves: {refused}"))
                }))
            })
            .ok()
            .flatten()
    }
}

/// The lead of a refused baseline's hint whose `stuck` leaf has no terminal value (TV-01).
const NON_VALUE_LEAD: &str =
    "every path ended, but a final configuration is not a value kink can compare";

/// The lead of a refused baseline's hint whose undefined step's pre-step configuration is not
/// shown to exist (kink27 R3-UNDEF-BRIDGE).
const UNDEFINED_STEP_LEAD: &str =
    "every path ended, but the configuration an undefined step is taken from is not shown to exist";

/// A leaf, as the cause's `leaves:` list names it: its halt and depth.
fn leaf_name(leaf: &AdaptedLeaf) -> String {
    format!(
        "{} leaf at depth {}",
        kebab(&format!("{:?}", leaf.halt)),
        leaf.branch.depth
    )
}

/// The longest node text a cause prints, in characters.
const NODE_TEXT_LIMIT: usize = 160;

/// A [`NonValue`] in the reader's words: the node, where it sits (its cells, from the outermost
/// below the top cell, and the collection entries on the way), the test it fails, for an overload
/// application the first node inside it that fails its own test ([`NonValue::inside`]), and the
/// KORE of the last node named, cut after [`NODE_TEXT_LIMIT`] characters.
pub(crate) fn non_value_text(failure: &NonValue) -> String {
    let place = cell_place(&failure.path);
    let mut text = format!(
        "the first node, in pre-order, that fails its own test is {} at {}: {}",
        node_name(&failure.node),
        if place.is_empty() {
            "the top of the configuration".to_owned()
        } else {
            place.join("/")
        },
        failure.test.description()
    );
    let mut shown = &failure.node;
    if let Some(inside) = &failure.inside {
        let place = cell_place(&inside.path);
        text.push_str(&format!(
            "; inside it{}, {} fails its own test: {}",
            if place.is_empty() {
                String::new()
            } else {
                format!(" at {}", place.join("/"))
            },
            node_name(&inside.node),
            inside.test.description()
        ));
        shown = &inside.node;
    }
    let mut kore = Printer::compact().print_pattern(shown);
    if let Some((cut, _)) = kore.char_indices().nth(NODE_TEXT_LIMIT) {
        kore.truncate(cut);
        kore.push_str("...");
    }
    format!("{text} (node: {kore})")
}

/// The cells (below the top cell) and collection entries of a [`NonValue`] path, outermost first.
fn cell_place(path: &[NonValueStep]) -> Vec<String> {
    path.iter()
        .filter_map(|step| match step {
            NonValueStep::Argument { symbol, .. } => {
                let label = label_or_name(symbol);
                (label.len() > 2
                    && label.starts_with('<')
                    && label.ends_with('>')
                    && label != "<generatedTop>")
                    .then_some(label)
            }
            NonValueStep::Entry {
                collection,
                entry,
                role,
                ..
            } => Some(format!(
                "{} entry {} {}",
                decode_sort_name(collection).unwrap_or_else(|_| collection.clone()),
                entry + 1,
                match role {
                    EntryRole::Key => "key",
                    EntryRole::Value => "value",
                    EntryRole::Element => "element",
                }
            )),
        })
        .collect()
}

/// A node, by its kind and, for an application, its head's label.
fn node_name(node: &Pattern) -> String {
    match node {
        Pattern::Application { symbol, .. } => {
            format!("an application of `{}`", label_or_name(&symbol.name))
        }
        Pattern::DomainValue { .. } => "a domain value".to_owned(),
        Pattern::Variable(_) => "a variable".to_owned(),
        _ => "a node".to_owned(),
    }
}

/// Why an excluded baseline run is not comparable, and what to fix, in the reader's words (re-pin
/// adoption A-1b). `records`: the diagnostic run lists a contradicted-claim record, which the
/// program's row reports as a specification diagnostic.
fn exclusion_hint(exclusion: Exclusion, records: bool) -> String {
    let why = match exclusion {
        Exclusion::ContradictedClaim if records => {
            "the run contradicts a trusted claim of the definition: k-rust lists a contradicted \
             claim the run or the definition's load observed, named with the application it is \
             false at in this row's specification_diagnostics; the definition, not the program, \
             is wrong there, so fix the claim (or the rule it is about), not the program"
        }
        Exclusion::ContradictedClaim => {
            "the run contradicts a trusted claim of the definition: a leaf takes an undefined \
             step that falsifies a `total` or `preserves-definedness` claim (see this row's \
             specification_diagnostics for any record k-rust lists); the definition, not the \
             program, is wrong there, so fix the claim (or the rule it is about), not the program"
        }
        Exclusion::StackStop => {
            "the run met a stop for lack of native stack, so its result can depend on the host's \
             threads"
        }
        Exclusion::LoadStackStop => {
            "loading the definition met a stop for lack of native stack, so its loaded theory can \
             depend on the host's threads"
        }
        Exclusion::ImplementationChosenHook => {
            "the definition uses a hook whose value the definition leaves open and k-rust chooses"
        }
        Exclusion::ShortCircuitReading => {
            "the run read the definedness of an operand a skipping backend may skip: the operand \
             after the deciding one of andBool, orBool, impliesBool, #if, andThenBool or \
             orElseBool, which k-rust found undefined or left undecided, at a step the \
             definition's short-circuit analysis does not clear, so another reading the \
             definition leaves to the backend may give the run another result"
        }
        Exclusion::AllowanceRefusal => {
            "a Bytes hook of the run was refused for the process's memory allowance, a property \
             of the host"
        }
        Exclusion::EqualsCondition => {
            "a rule or equation condition equates two terms ({ A #Equals B }), which k-rust may \
             decide wrongly when they may be undefined"
        }
        Exclusion::ImplementationChosenValue => {
            "the run read a value the definition leaves open, which k-rust chose (k-rust's list \
             of the run's open values)"
        }
        Exclusion::UnsupportedHook => {
            "the run, or the definition's load, left an application unevaluated as an \
             unsupported hook"
        }
        Exclusion::PassedStop => {
            "the run went on past a step of a stop rule that had another successor (k-rust's \
             list of the run's passed stops), so its ends need not be the ends of the observation \
             the stop states"
        }
    };
    format!("the run is excluded ({}): {why}", exclusion.name())
}

/// A duration in whole milliseconds.
pub fn millis(duration: Duration) -> u64 {
    u64::try_from(duration.as_millis()).unwrap_or(u64::MAX)
}

/// The cause of a baseline that this command's live run stopped on time (flow F-13): the
/// bound, the leaf census of the run when the bound fired, and how many of the rules a run can
/// observe (`observable`: each rule's compiled ids) the returned leaves had applied. The rule
/// count comes from the census, not from the record's coverage, which lists nothing for a
/// timed-out run (kink-native `TestCoverage`); it is a hint, read from the leaves k-rust
/// returned after the cancel. It ends with [`TIMEOUT_NOT_CACHED`] and, without a
/// `[budget] baseline_max_work`, [`TIMEOUT_BOUND_BY_WORK`].
pub fn timeout_cause(
    time_ms: u128,
    baseline_max_work: Option<u64>,
    census: &kink_campaign::LeafCensus,
    observable: &[BTreeSet<String>],
) -> String {
    format!(
        "the run did not finish within time_ms = {time_ms}; when the bound fired {}{}{}",
        census_hint(census, observable),
        TIMEOUT_NOT_CACHED,
        if baseline_max_work.is_none() {
            TIMEOUT_BOUND_BY_WORK
        } else {
            ""
        }
    )
}

/// Why the campaign gave a run no evidence, where it refused the run (`failure`): what ended this
/// command's live run of it (`live_stop`, `None` where none ran) where that is known, and
/// otherwise the refusal. The campaign's refusal of a baseline that is neither excluded nor
/// stopped by its condition does not say what failed (`BaselineError`): a run the watchdog
/// cancelled at `time_ms` is one, and so is a run the execution adapter returned nothing for, and
/// the live run tells the two apart. A timeout depends on the host's load, so a reader that keeps
/// what a run read keeps nothing of it.
pub(crate) fn refused_run(
    failure: &CampaignFailure,
    live_stop: Option<RunStop>,
    time_ms: u128,
) -> String {
    if let Some(reason) = failure.stop_condition() {
        return format!(
            "the stop condition ([stop] when) gave no answer the run can rest on: {reason}"
        );
    }
    match live_stop {
        Some(RunStop::Time) => format!(
            "the watchdog stopped the run at time_ms = {time_ms}, before it ended; a timeout \
             depends on the host's load"
        ),
        Some(RunStop::Failed) => format!(
            "the execution adapter returned no execution (an adapter or backend failure), and \
             the campaign refused the run: {failure}"
        ),
        Some(RunStop::Finished) | None => format!("the campaign refused the run: {failure}"),
    }
}

/// The clause a timeout's cause continues with: a timeout is never cached.
pub const TIMEOUT_NOT_CACHED: &str = "; a timeout depends on the host's load and is not cached: \
     the next command runs this program again";
/// The clause a timeout's cause ends with when the manifest bounds no baseline by work.
pub const TIMEOUT_BOUND_BY_WORK: &str =
    "; set [budget] baseline_max_work to bound the run by work instead";

/// The cause of a prefix program none of whose observation channels kept an element within its
/// budget or closed by a cycle (`record`, its baseline's record): each channel with why it
/// opened.
fn observed_nothing_cause(record: &kink_campaign::BaselineRecord) -> String {
    if let Some(paths) = &record.paths {
        return format!(
            "{OBSERVED_NOTHING}: a bound cut the run before it ended, and none of its {} paths \
             kept an element of any observation channel within the budget, so no mutant can \
             differ from it within its horizons",
            paths.paths
        );
    }
    let channels = record
        .channels
        .iter()
        .map(|channel| match &channel.end {
            ChannelEnd::Open(opened) => format!(
                "`{}` opened before its first element ({}: {})",
                channel.name,
                opened.opening.name(),
                opened.reason
            ),
            ChannelEnd::Closed(closure) => {
                format!("`{}` closed by {}", channel.name, closure.name())
            }
        })
        .collect::<Vec<_>>();
    format!(
        "{OBSERVED_NOTHING}: a bound cut the run before it ended, and none of its observation \
         channels kept an element within the budget, so no mutant can differ from it within its \
         horizons: {}",
        channels.join("; ")
    )
}

/// The reason a prefix program that observed nothing is `unknown` ([`observed_nothing_cause`]).
pub const OBSERVED_NOTHING: &str = "observed-nothing";

/// The cause of a baseline that `[budget] baseline_max_work` stopped: the bound, the leaf
/// census of the run and how many of the rules a run can observe its leaves had applied, as
/// [`timeout_cause`] says them.
pub fn work_bound_cause(
    bound: u64,
    census: &kink_campaign::LeafCensus,
    observable: &[BTreeSet<String>],
) -> String {
    format!(
        "the run reached baseline_max_work = {bound}; {}",
        census_hint(census, observable)
    )
}

/// A census as a cause says it: [`crate::report::census_clause`], and how many of the rules a run
/// can observe (`observable`: each rule's compiled ids) the returned leaves had applied.
fn census_hint(census: &kink_campaign::LeafCensus, observable: &[BTreeSet<String>]) -> String {
    let reached = if census.total() > 0 {
        let count = observable
            .iter()
            .filter(|ids| !ids.is_disjoint(&census.rule_ids))
            .count();
        format!(
            "; those leaves had applied {count} of the {} rules a run can observe",
            observable.len()
        )
    } else {
        String::new()
    };
    format!("{}{reached}", crate::report::census_clause(census))
}

/// The compiled ids of each authored rule of the specification with an id in the coverage domain
/// (kink-native `coverage_domain`: the rules and equations a run's coverage can name; re-pin
/// L2-1, before which only rewrite rules counted).
fn observable_rules(spec: &AdmittedSpec, authors: &RuleAuthors) -> Vec<BTreeSet<String>> {
    let rewrites = coverage_domain(&spec.compiled);
    spec.loaded
        .baseline
        .authored_sentences()
        .filter(|(_, sentence)| matches!(sentence, Sentence::Rule { .. }))
        .map(|(at, _)| {
            authors
                .ids_of(&at)
                .map(str::to_owned)
                .collect::<BTreeSet<_>>()
        })
        .filter(|ids| ids.iter().any(|id| rewrites.contains(id)))
        .collect()
}

pub(crate) fn kebab(name: &str) -> String {
    let mut out = String::new();
    for (index, c) in name.chars().enumerate() {
        if index > 0 && c.is_uppercase() {
            out.push('-');
        }
        out.extend(c.to_lowercase());
    }
    out
}

/// The flow's classifier: kink-corpus `all_normal`, digest `CLASSIFIER`. Every campaign call of
/// the flow classifies terminals with it ([`BaselineRunner::call`]), and kill evidence reads an
/// end's class from it (`evidence::class`), so the two cannot differ.
pub(crate) fn classify(end: &Pattern) -> kink_pattern::ExecutionTerminalKind {
    all_normal(end)
}

/// The whole-term value of a side's run, when it is one: its ends with the counter erased.
fn final_ends(run: &SideRun) -> Option<&BTreeSet<Pattern>> {
    let SideRun::Sides { sides } = run else {
        return None;
    };
    sides.iter().find_map(|side| match side {
        OracleSide::Normal(OracleValue::FinalResult(FinalResult::WholeTerm(terms))) => Some(terms),
        _ => None,
    })
}

/// A sentence's source position: `{module, index, label, file, start_line, end_line}`.
pub fn sentence_value(spec: &AdmittedSpec, at: &SentenceRef) -> Value {
    let sentence = spec.loaded.baseline.sentence(at);
    let attributes = sentence.map(Sentence::attributes);
    let location = attributes.and_then(|a| a.location());
    json!({
        "module": at.module,
        "index": at.index,
        "label": attributes.and_then(|a| a.string(AttributeKey::Label)),
        "file": attributes.and_then(|a| a.source()),
        "start_line": location.map(|l| l.start_line),
        "end_line": location.map(|l| l.end_line),
    })
}

/// A sentence as a record's coverage stores it: `{module, index, label}`. The label is content
/// (part of the sentence's fingerprint); file and lines are not stored, since a record answers
/// under an execution digest that ignores positions, and documents render them from the current
/// load ([`sentence_value`]).
fn stored_sentence(spec: &AdmittedSpec, at: &SentenceRef) -> Value {
    let sentence = spec.loaded.baseline.sentence(at);
    json!({
        "module": at.module,
        "index": at.index,
        "label": sentence.and_then(|s| s.attributes().string(AttributeKey::Label)),
    })
}

/// A record's coverage (kink-native `TestCoverage`, coverage v2 since re-pin L2-1): `sentences`
/// are the baseline sentences the run matched (k-rust `matched`), `applied_sentences` those it
/// applied (`applied`: a step built a successor or found the step undefined, which orders a run's
/// programs), and `fired_sentences` (result schema v6, KINK-R4) those it fired, which a rule's
/// `fired_by` lists: a rewrite rule whose step some explored path takes (k-rust `committed`), an
/// equation whose instance gave a result (`applied`); `guards` (result schema v15) the guard
/// outcomes of the guarded sentences it entered ([`crate::guards`]); `bindings` (result
/// schema v17) what its fired instances bound, by sentence ([`bindings_value`]), null when the
/// run collected none (a diagnostic run); and `strictness` (result schema v20) the heating and
/// cooling rules it matched and fired, by compiled id (`{matched, fired}`, kink-native
/// `TestCoverage::strictness`), since every such rule of one production has the production as
/// its sentence, so the sentences cannot say which argument position a run heated; `depth`
/// (result schema v24) the depth its request asked for, the longest rule window and syntax path
/// it collected (kink-native `TestCoverage::depth`), 1 for a run that asked for neither; and
/// `windows` (result schema v23) the rule windows it took, every window up to `depth`, each a
/// list of `{module, index}` in step order (kink-native `TestCoverage::windows`), null for a run
/// that asked for none.
fn coverage_value(spec: &AdmittedSpec, coverage: &TestCoverage) -> Value {
    let sentences = |sentences: &BTreeSet<SentenceRef>| {
        sentences
            .iter()
            .map(|at| stored_sentence(spec, at))
            .collect::<Vec<_>>()
    };
    json!({
        "complete": coverage.complete,
        "sentences": sentences(&coverage.sentences),
        "applied_sentences": sentences(&coverage.applied_sentences),
        "fired_sentences": sentences(&coverage.fired_sentences),
        "strictness": {
            "matched": coverage.strictness.matched,
            "fired": coverage.strictness.fired,
        },
        "guards": crate::guards::record_value(coverage),
        "bindings": coverage
            .bindings
            .as_ref()
            .map_or(Value::Null, |bindings| bindings_value(spec, bindings)),
        "depth": coverage.depth,
        "windows": coverage.windows.as_ref().map_or(Value::Null, |windows| {
            json!(
                windows
                    .sequences
                    .iter()
                    .map(|window| {
                        window
                            .iter()
                            .map(|at| json!({"module": at.module, "index": at.index}))
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>()
            )
        }),
    })
}

/// The depth a record's run collected at (its coverage's `depth`): the longest rule window and
/// syntax path it holds, 1 for a run that asked for neither, whose windows of length 1 are its
/// `fired_sentences` and whose paths of length 1 are its operand heads and its axioms' own
/// symbols; or `None` for a record without coverage, which holds no window and no path at any
/// depth. Every depth-dependent family reads this one depth.
pub fn record_depth(record: &Value) -> Option<u64> {
    let coverage = &record["coverage"];
    if !coverage.is_object() {
        return None;
    }
    Some(coverage["depth"].as_u64().unwrap_or(1))
}

/// Whether a stored record answers a command whose runs collect rule windows and syntax paths up
/// to `depth`: it collected every window and path up to at least that length, or it holds no
/// coverage, which a new run of the same key would not hold either. A record collected at `D`
/// lists every window and every path of length `1..=D` (k-rust reads each length the same way at
/// every depth), so it answers every depth up to `D`.
pub fn record_answers(record: &Value, depth: std::num::NonZeroUsize) -> bool {
    record_depth(record).is_none_or(|collected| {
        usize::try_from(collected).is_ok_and(|collected| collected >= depth.get())
    })
}

/// What a run's fired instances bound as a record stores it: `operands`, per sentence
/// (`{module, index, label}`, [`stored_sentence`]) the authored symbols that were the head of an
/// operand of a fired instance (`symbols`), `binders`, per selected template binder bound at
/// some fired instance, its axiom, the sentences behind it, its variable and its values
/// (`{axiom, sentences, variable, values, truncated, nonliteral}`), and `alternatives`, per
/// alternative of an axiom with several that a fired instance took, its axiom, its left-hand
/// and right-hand side alternatives (null where the side has one) and the sentences behind the
/// axiom (`{axiom, lhs, rhs, sentences}`), and `paths` (result schema v24), per sentence the
/// syntax paths of length `2..=depth` its fired instances touched (`{module, index, label,
/// paths: [{symbols, positions}]}`, `positions` 0-based), null for a run of depth 1.
fn bindings_value(
    spec: &AdmittedSpec,
    bindings: &kink_native::coverage::SentenceBindings,
) -> Value {
    json!({
        "operands": bindings
            .operands
            .iter()
            .map(|(at, symbols)| {
                let mut value = stored_sentence(spec, at);
                value["symbols"] = json!(symbols);
                value
            })
            .collect::<Vec<_>>(),
        "binders": bindings
            .binders
            .iter()
            .map(|binder| {
                json!({
                    "axiom": binder.axiom,
                    "sentences": binder
                        .sentences
                        .iter()
                        .map(|at| stored_sentence(spec, at))
                        .collect::<Vec<_>>(),
                    "variable": binder.variable,
                    "values": binder.values,
                    "truncated": binder.truncated,
                    "nonliteral": binder.nonliteral,
                })
            })
            .collect::<Vec<_>>(),
        "alternatives": bindings
            .alternatives
            .iter()
            .map(|alternative| {
                json!({
                    "axiom": alternative.key.axiom,
                    "lhs": alternative.key.lhs,
                    "rhs": alternative.key.rhs,
                    "sentences": alternative
                        .sentences
                        .iter()
                        .map(|at| stored_sentence(spec, at))
                        .collect::<Vec<_>>(),
                })
            })
            .collect::<Vec<_>>(),
        "paths": bindings.paths.as_ref().map_or(Value::Null, |paths| {
            json!(
                paths
                    .iter()
                    .map(|(at, paths)| {
                        let mut value = stored_sentence(spec, at);
                        value["paths"] = json!(
                            paths
                                .iter()
                                .map(|path| {
                                    json!({"symbols": path.symbols, "positions": path.positions})
                                })
                                .collect::<Vec<_>>()
                        );
                        value
                    })
                    .collect::<Vec<_>>()
            )
        }),
    })
}

/// The members a result record holds beside its ends ([`RECORD_ENDS`]): every member a reader of
/// a program's row reads (never for a refused program). `spec_digest` is the writer's exact
/// specification digest, outside the key, for diagnosis only: a reader can tell that a record
/// was written under other bytes. `coverage` is the run's coverage as a record stores it
/// ([`coverage_value`]), null when no run produced any.
fn record_facts(
    key: &Value,
    spec_digest: Sha256Digest,
    id: &str,
    result: &ProgramResult,
    coverage: Value,
) -> Value {
    let mut facts = json!({
        "schema": RECORD_SCHEMA,
        "key": key,
        "spec_digest": spec_digest.to_string(),
        "program_id": id,
        "class": result.class.as_str(),
        "cause": result.cause,
        "run_sha256": result.run_sha256().map(|d| d.to_string()),
        "ends": result.ends,
        "coverage": coverage,
        "wall_ms": result.wall_ms,
        "specification_diagnostics": result.specification_diagnostics,
        "smt_unknowns": result.smt_unknowns,
        "decider_smt_unknowns": result.decider_smt_unknowns,
        "short_circuit_readings": result.short_circuit_readings,
    });
    // Under `[observe]`, the channels the baseline recorded and their horizons; absent without a
    // record, so a record without `[observe]` has the members it had.
    let observations = result.observations();
    if !observations.is_null() {
        facts["observations"] = observations;
    }
    facts
}

/// The members of a result record that hold its ends: the baseline row (comparable only) and the
/// diagnostic run's leaves. [`write_record`] writes them from the [`ProgramResult`] itself, and a
/// program's row holds its record without them ([`ProgramRow::record`]).
pub const RECORD_ENDS: [&str; 2] = ["baseline", "final_configuration"];

/// The record facts of `result` ([`record_facts`]), its coverage read under `spec`.
pub fn record_value(
    spec: &AdmittedSpec,
    key: &Value,
    spec_digest: Sha256Digest,
    id: &str,
    result: &ProgramResult,
) -> Value {
    let coverage = result
        .coverage
        .as_ref()
        .map_or(Value::Null, |c| coverage_value(spec, c));
    record_facts(key, spec_digest, id, result, coverage)
}

/// Writes the result record of `result` to `path`: the members of `facts` ([`record_value`]) and
/// its ends ([`RECORD_ENDS`]: the baseline row, the diagnostic leaves), member by member, in the
/// sorted order of canonical JSON, so the bytes are those `canonical_json` gives for the record
/// as one value, and neither that value nor the record's whole text is ever held. Every end is a
/// KORE text, so the record nests a fixed number of levels; a record deeper than kink-patch
/// `MAX_JSON_DEPTH`, which [`read_record`] would refuse, is refused before anything is written.
/// The members are serialized on a stack sized from the record's depth, as `canonical_json`
/// serializes a value, so a record of any depth up to that limit is written on any thread, and
/// one whose stack the system refuses is refused before anything is written too.
///
/// # Errors
/// [`StoreError::Invalid`] when `facts` is not an object, the record would be too deep or the
/// system refuses the stack its depth needs, and the store's I/O error.
pub fn write_record(
    store: &Store,
    path: &Path,
    facts: &Value,
    result: &ProgramResult,
) -> Result<(), StoreError> {
    enum Member<'a> {
        Value(&'a Value),
        Texts(Option<&'a [String]>),
    }
    let Value::Object(facts) = facts else {
        return Err(StoreError::Invalid("a result record is an object".into()));
    };
    let baseline = result.baseline.as_ref().unwrap_or(&Value::Null);
    let depth = 1 + facts
        .values()
        .chain(std::iter::once(baseline))
        .map(value_depth)
        .max()
        .unwrap_or(0)
        .max(1);
    if depth > MAX_JSON_DEPTH {
        return Err(StoreError::Invalid(format!(
            "the result record nests {depth} levels deep, more than kink's limit of \
             {MAX_JSON_DEPTH} (kink-patch MAX_JSON_DEPTH)"
        )));
    }
    let mut members = facts
        .iter()
        .filter(|(name, _)| !RECORD_ENDS.contains(&name.as_str()))
        .map(|(name, value)| (name.as_str(), Member::Value(value)))
        .chain([
            (RECORD_ENDS[0], Member::Value(baseline)),
            (
                RECORD_ENDS[1],
                Member::Texts(result.final_configuration.as_deref()),
            ),
        ])
        .collect::<Vec<_>>();
    members.sort_by(|a, b| a.0.cmp(b.0));
    let write = || {
        store.write_streamed(path, |out| {
            out.write_all(b"{")?;
            for (index, (name, member)) in members.iter().enumerate() {
                if index > 0 {
                    out.write_all(b",")?;
                }
                serde_json::to_writer(&mut *out, name)?;
                out.write_all(b":")?;
                match member {
                    Member::Value(value) => serde_json::to_writer(&mut *out, value)?,
                    Member::Texts(texts) => serde_json::to_writer(&mut *out, texts)?,
                }
            }
            out.write_all(b"}")
        })
    };
    kink_patch::with_document_stack(depth, write).map_err(|refusal| {
        StoreError::Invalid(format!(
            "the result record nests {depth} levels deep and cannot be serialized: {refusal}"
        ))
    })?
}

/// `record` without its ends ([`RECORD_ENDS`]), as a program's row holds it.
fn without_ends(mut record: Value) -> Value {
    if let Value::Object(members) = &mut record {
        for name in RECORD_ENDS {
            members.remove(name);
        }
    }
    record
}

/// A stored record: `None` when the file is absent; `Some(None)` when it exists but does not
/// parse, has another schema or key, or holds a class this build never writes (anything but
/// `comparable` and `unknown`: a file another writer left, or a hand edit); it is then
/// recomputed, never used. A stored `unknown` is honoured: the writer stores one only when it
/// does not depend on the host, and the cache directory's integrity is the cache's premise.
fn read_record(path: &Path, key: &Value) -> Option<Option<Value>> {
    let text = fs::read_to_string(path).ok()?;
    Some(kink_patch::parse_json(&text).ok().filter(|record| {
        record["schema"] == RECORD_SCHEMA
            && record["key"] == *key
            && (ResultClass::can_kill(&record["class"])
                || record["class"] == ResultClass::Unknown.as_str())
    }))
}

/// How `--verify` compares a stored record with a new run of its program: every difference,
/// including a record whose `run_sha256` is not the digest of its own baseline row.
fn verify_record(record: &Value, result: &ProgramResult) -> Vec<String> {
    let mut differences = Vec::new();
    let stored_digest = record["run_sha256"].as_str();
    let row_digest = record
        .get("baseline")
        .filter(|row| !row.is_null())
        .and_then(run_digest)
        .map(|d| d.to_string());
    if stored_digest != row_digest.as_deref() {
        differences.push(format!(
            "the record's run_sha256 {} is not the digest of its baseline row ({})",
            stored_digest.unwrap_or("null"),
            row_digest.as_deref().unwrap_or("no row"),
        ));
    }
    if record["class"] != result.class.as_str() {
        differences.push(format!(
            "class: cached {}, now {}",
            record["class"],
            result.class.as_str()
        ));
    }
    let now = result.run_sha256().map(|d| d.to_string());
    if stored_digest != now.as_deref() {
        differences.push(format!(
            "run_sha256: cached {}, now {}",
            stored_digest.unwrap_or("null"),
            now.as_deref().unwrap_or("null"),
        ));
    }
    differences
}

/// One program's row of a document that lists the programs' baseline runs (`coverage`, `run`,
/// `query`), with its record when it has one.
pub struct ProgramRow {
    /// The program's row.
    pub row: Value,
    /// The program's current record (stored or just written), if it has one, without its ends
    /// ([`RECORD_ENDS`]): no reader of a row reads them, and a row holds its record until the
    /// command's document is written, so holding them would keep one more copy, as KORE text, of
    /// every program's ends until then (the command's baseline session holds each live run's
    /// execution, its ends included, for the whole command).
    pub record: Option<Value>,
    /// Under `--verify`, when the program has a stored record: the record this command's own run
    /// gives, without its ends, which `record` (the stored one) was compared with. `None`
    /// otherwise (`record` is then this command's run, or the stored record a command without
    /// `--verify` uses).
    pub live: Option<Value>,
    /// The program was refused, its run failed or its record could not be written.
    pub failed: bool,
    /// The program's digest, when its inputs could be read.
    pub digest: Option<Sha256Digest>,
    /// The program's inputs exactly as its digest was computed from them.
    pub inputs: Option<CaseInputs>,
    /// The program's admitted test case (no oracles), when this command assembled it.
    pub test: Option<TestCase>,
}

impl ProgramRow {
    /// The record's class, when the program has a record.
    pub fn class(&self) -> Option<&str> {
        self.record
            .as_ref()
            .and_then(|record| record["class"].as_str())
    }
}

/// The result cache brought up to date for one admitted specification: one row per manifest
/// program, in manifest order.
pub struct ResultsUpdate {
    /// The exact specification digest, which keys the memos and names the specification in every
    /// document.
    pub spec_digest: Sha256Digest,
    /// The execution digest, computed once per command, which keys the result cache, tier 1 and
    /// the pattern cache (`digest::execution_digest`).
    pub execution: ExecutionDigest,
    pub rows: Vec<ProgramRow>,
    pub mismatches: Vec<Value>,
}

impl ResultsUpdate {
    /// No program was refused or failed and `--verify` found no mismatch.
    pub fn ok(&self) -> bool {
        self.rows.iter().all(|row| !row.failed) && self.mismatches.is_empty()
    }
}

/// The cache directory of a manifest: `options.cache`, else `.kink-flow` next to it.
pub fn cache_directory(manifest: &FlowManifest, cache: Option<&Path>) -> PathBuf {
    corpus_cache_directory(&manifest.directory, cache)
}

/// [`cache_directory`] of the corpus whose manifest is in `directory`: a function of that
/// directory and `cache` alone.
pub fn corpus_cache_directory(directory: &Path, cache: Option<&Path>) -> PathBuf {
    cache.map_or_else(|| directory.join(CACHE_DIRECTORY), Path::to_path_buf)
}

/// The refusal of a specification whose baseline runner cannot be built.
pub fn runner_refusal(detail: String) -> kink_corpus::admission::AdmissionRefusal {
    kink_corpus::admission::AdmissionRefusal {
        stage: "baseline".into(),
        reason: "invalid-declaration".into(),
        detail,
    }
}

/// Bring the result cache of `spec` up to date (README 5.3) with `runner`, whose validator
/// is the specification's, so every program shares one baseline compile.
///
/// `progress`, when given, gets one line as each program's row is decided: its place, its id,
/// its class, and whether its record was stored (``run: baseline of program 2 of 20, `t2`:
/// comparable, stored``), a function of the corpus and the cache ([`crate::cli::FrontEnd::progress`]).
pub fn update_results(
    spec: &AdmittedSpec,
    manifest: &FlowManifest,
    inputs: &mut InputSession<'_>,
    runner: &BaselineRunner<'_>,
    cache: &Path,
    verify: bool,
    progress: Option<&(dyn Fn(&str) + Sync)>,
) -> ResultsUpdate {
    let spec_digest = spec_digest(manifest, &spec.loaded.files);
    let execution = execution_digest(manifest, spec);
    let store = Store::new(cache);
    let directory = cache.join("results").join(execution.digest.to_string());
    let build = kink_campaign::kink_build().ok();
    let mut mismatches = Vec::new();
    let rows = manifest
        .programs
        .iter()
        .enumerate()
        .map(|(position, program)| {
            let row = program_row(
                spec,
                manifest,
                inputs,
                runner,
                &ProgramContext {
                    spec_digest,
                    execution,
                    build,
                    store: result_store(manifest.budget.backend_options()),
                    directory: &directory,
                    cache,
                    writer: &store,
                    verify,
                },
                program,
                &mut mismatches,
            );
            if let Some(progress) = progress {
                progress(&format!(
                    "run: baseline of program {} of {}, `{}`: {}{}",
                    position + 1,
                    manifest.programs.len(),
                    program.id,
                    row.row["class"].as_str().unwrap_or("no class"),
                    if row.row["cached"] == true {
                        ", stored"
                    } else {
                        ""
                    },
                ));
            }
            row
        })
        .collect::<Vec<_>>();
    ResultsUpdate {
        spec_digest,
        execution,
        rows,
        mismatches,
    }
}

/// Why the result cache is off under the Z3 profile when solver queries are bounded by the clock.
pub const RESULT_CACHE_Z3: &str = "the result cache is off under the z3 profile when solver \
     queries are bounded by the clock: an answer then depends on the host's load, which no key \
     can name, so a baseline class is not a function of its key; every program runs live";
/// Why the result cache is off when kink's build identity is unknown (packet CACHE-ID-fix-1).
pub const RESULT_CACHE_NO_BUILD: &str = "kink's build identity is unknown (the executable cannot \
     be read): the result cache is neither read nor written";

/// kink's build identity when the result cache of runs on backends built with `solver` is on,
/// else why it is off: under the Z3 profile when the key cannot name the Z3 build (kink-native
/// `UNNAMED_Z3_BUILD`) and when the clock bounds `solver` ([`RESULT_CACHE_Z3`]; kink-native
/// `solver_answers_keyed`), and when the executable cannot be read ([`RESULT_CACHE_NO_BUILD`]).
pub fn result_store(solver: k_rust::backend::BackendOptions) -> Result<Sha256Digest, &'static str> {
    kink_native::solver_named()?;
    if !kink_native::solver_answers_keyed(solver) {
        return Err(RESULT_CACHE_Z3);
    }
    kink_campaign::kink_build().map_err(|_| RESULT_CACHE_NO_BUILD)
}

/// A document's `result_cache` for runs on backends built with `solver`:
/// `{enabled, reason}`.
pub fn result_cache_value(solver: k_rust::backend::BackendOptions) -> Value {
    let store = result_store(solver);
    json!({"enabled": store.is_ok(), "reason": store.err()})
}

struct ProgramContext<'a> {
    /// The writer's exact specification digest, which a record names outside its key.
    spec_digest: Sha256Digest,
    /// The execution digest, which keys the records.
    execution: ExecutionDigest,
    /// kink's build identity, the key's `kink_build`; `None` when the executable cannot be read.
    build: Option<Sha256Digest>,
    /// kink's build identity when the result cache is on, else why it is off ([`result_store`]):
    /// no record is then read or written.
    store: Result<Sha256Digest, &'static str>,
    directory: &'a Path,
    cache: &'a Path,
    writer: &'a Store,
    verify: bool,
}

fn program_row(
    spec: &AdmittedSpec,
    manifest: &FlowManifest,
    inputs: &mut InputSession<'_>,
    runner: &BaselineRunner<'_>,
    context: &ProgramContext<'_>,
    program: &Program,
    mismatches: &mut Vec<Value>,
) -> ProgramRow {
    // `wall_ms`: the wall time of the program's live baseline run, from the record (outside
    // the key and the run digest; flow F-13).
    let row = |digest: Option<Sha256Digest>, class: &str, cause: &Value, cached, verify: Value| {
        json!({
            "id": program.id,
            "digest": digest.map(|d| d.to_string()),
            "class": class,
            "cause": cause,
            "cached": cached,
            "verify": verify,
            "wall_ms": null,
        })
    };
    // Re-pin adoption A-1: the record's specification diagnostics and undecided solver answers
    // too (outside the key and the run digest).
    let with_wall = |mut row: Value, record: &Value| {
        row["wall_ms"] = record["wall_ms"].clone();
        row["specification_diagnostics"] = record["specification_diagnostics"].clone();
        row["smt_unknowns"] = record["smt_unknowns"].clone();
        row["decider_smt_unknowns"] = record["decider_smt_unknowns"].clone();
        // CF-16: each end's computation head and class (null unless comparable).
        row["ends"] = record.get("ends").cloned().unwrap_or(Value::Null);
        // The step that excluded a `short-circuit-reading` run (empty otherwise).
        row["short_circuit_readings"] = record
            .get("short_circuit_readings")
            .cloned()
            .unwrap_or_else(|| json!([]));
        // Under `[observe]`, the channels the baseline recorded and their horizons; absent
        // without a record, so a row without `[observe]` is the row it was.
        if let Some(observations) = record.get("observations").filter(|value| !value.is_null()) {
            row["observations"] = observations.clone();
        }
        row
    };
    // A case's expectation, checked against its baseline record or inconclusive for why it has
    // none (`crate::expect`); absent from the row of a program without one.
    let expected = |mut row: Value, expectation: Option<Value>| {
        if let Some(expectation) = expectation {
            row["expectation"] = expectation;
        }
        row
    };
    let refused = |digest, refusal: kink_corpus::admission::AdmissionRefusal| {
        let result = ProgramResult::refused(format!(
            "{}/{}: {}",
            refusal.stage, refusal.reason, refusal.detail
        ));
        let expectation = crate::expect::expectation_value(
            &manifest.end_renderer,
            None,
            program,
            Err("the case is refused, so it has no baseline run"),
            &[],
            None,
        );
        ProgramRow {
            row: expected(
                row(
                    digest,
                    result.class.as_str(),
                    &json!(result.cause),
                    false,
                    Value::Null,
                ),
                expectation,
            ),
            record: None,
            live: None,
            failed: true,
            digest,
            inputs: None,
            test: None,
        }
    };
    let case = match inputs.read(program) {
        Ok(case) => case,
        Err(refusal) => return refused(None, refusal),
    };
    let digest = program_digest(program, &case);
    let key = result_key(
        context.execution,
        digest,
        manifest.budget,
        context.build,
        manifest.program_stop(program),
        manifest
            .syntax
            .as_ref()
            .map(crate::manifest::SyntaxSelection::key_value),
        manifest.observe_value(),
    );
    let path = context.directory.join(format!("{digest}.json"));
    // Where the store is off (no build identity, an unnamed Z3 build or a solver the clock
    // bounds: `result_store`), no record is honoured (packet CACHE-ID-fix-1).
    // A record collected at a smaller window depth than the command's does not answer: the
    // program runs again and its record is replaced.
    let stored = context
        .store
        .ok()
        .and_then(|_| read_record(&path, &key))
        .flatten()
        .filter(|record| record_answers(record, runner.depth()));
    let stop = manifest.stop.as_ref();
    if let (Some(record), false) = (&stored, context.verify) {
        return ProgramRow {
            row: expected(
                with_wall(
                    row(
                        Some(digest),
                        record["class"].as_str().unwrap_or("error"),
                        &record["cause"],
                        true,
                        Value::Null,
                    ),
                    record,
                ),
                inputs.expectation(program, Ok(Baseline::of_record(record)), stop),
            ),
            failed: record["class"] == ResultClass::Error.as_str(),
            record: stored.map(without_ends),
            live: None,
            digest: Some(digest),
            inputs: Some(case),
            test: None,
        };
    }
    let test = match inputs.test_case(program, &case) {
        Ok(test) => test,
        Err(refusal) => return refused(Some(digest), refusal),
    };
    let result = runner.run(test.clone());
    if let Some(record) = stored {
        let differences = verify_record(&record, &result);
        let relative = path
            .strip_prefix(context.cache)
            .unwrap_or(&path)
            .to_string_lossy()
            .into_owned();
        for detail in &differences {
            mismatches.push(json!({"program": program.id, "record": relative, "detail": detail}));
        }
        let verdict = if differences.is_empty() {
            "match"
        } else {
            "mismatch"
        };
        return ProgramRow {
            row: expected(
                with_wall(
                    row(
                        Some(digest),
                        record["class"].as_str().unwrap_or("error"),
                        &record["cause"],
                        true,
                        json!(verdict),
                    ),
                    &record,
                ),
                inputs.expectation(program, Ok(Baseline::of_record(&record)), stop),
            ),
            failed: record["class"] == ResultClass::Error.as_str(),
            record: Some(without_ends(record)),
            live: Some(record_value(
                spec,
                &key,
                context.spec_digest,
                &program.id,
                &result,
            )),
            digest: Some(digest),
            inputs: Some(case),
            test: Some(test),
        };
    }
    let record = record_value(spec, &key, context.spec_digest, &program.id, &result);
    let mut row = expected(
        with_wall(
            row(
                Some(digest),
                result.class.as_str(),
                &json!(result.cause),
                false,
                Value::Null,
            ),
            &record,
        ),
        inputs.expectation(program, Ok(Baseline::of_result(&result)), stop),
    );
    // A record is written only when the store is on and the result is a function of its key;
    // an error row still fails the command, cached or not.
    let mut failed = result.class == ResultClass::Error;
    if context.build.is_none() {
        row["cache_error"] = json!(RESULT_CACHE_NO_BUILD);
    } else if context.store.is_err() {
        // The document's `result_cache` says why the store is off.
    } else if let Some(host) = result.host {
        row["not_cached"] = json!(host.reason(result.class, runner.time_ms()));
    } else if let Err(e) = write_record(context.writer, &path, &record, &result) {
        row["cache_error"] = json!(format!("cannot write the result record: {e}"));
        failed = true;
    }
    ProgramRow {
        row,
        record: Some(record),
        live: None,
        failed,
        digest: Some(digest),
        inputs: Some(case),
        test: Some(test),
    }
}

/// The authored rules none of whose compiled ids k-rust's run coverage can name (status
/// `no-coverage-signal`, [`crate::coverage`]), each with the reason: no program can be shown to
/// match them.
pub fn no_coverage_signal(spec: &AdmittedSpec) -> BTreeMap<SentenceRef, &'static str> {
    let domain = coverage_domain(&spec.compiled);
    let non_executable = non_executable_ids(&spec.compiled);
    let authors = RuleAuthors::of(&spec.compiled);
    spec.loaded
        .baseline
        .authored_sentences()
        .filter(|(_, sentence)| matches!(sentence, Sentence::Rule { .. }))
        .filter_map(|(at, _)| {
            let ids = authors.ids_of(&at).collect::<Vec<_>>();
            if ids.iter().any(|id| domain.contains(*id)) {
                return None;
            }
            let reason = if ids.is_empty() {
                "compiles to no rule"
            } else if ids.iter().all(|id| non_executable.contains(*id)) {
                "a non-executable rule: k-rust never runs it, so no program can match it"
            } else {
                "a macro, alias or smt-lemma rule: k-rust's run coverage has no recording site for it"
            };
            Some((at, reason))
        })
        .collect()
}

/// The current result record of `program`, whose inputs are `inputs`, read from the cache `cache`
/// without running anything: the record `coverage` would use, or `None` when there is none (no
/// file, another key, a class never written, or the store off, [`result_store`]). `execution` is
/// the execution digest of the admitted specification (`digest::execution_digest`).
pub fn current_record(
    manifest: &FlowManifest,
    execution: ExecutionDigest,
    program: &Program,
    inputs: &CaseInputs,
    cache: &Path,
) -> Option<Value> {
    let build = result_store(manifest.budget.backend_options()).ok()?;
    let digest = program_digest(program, inputs);
    let key = result_key(
        execution,
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
    let path = cache
        .join("results")
        .join(execution.digest.to_string())
        .join(format!("{digest}.json"));
    read_record(&path, &key).flatten()
}

/// `rows` (program rows of a document), each comparable row marked `unable_to_kill:
/// "baseline-findings"` while the baseline has a finding no `[spec] assume_joined` name assumes
/// (fz26 KINK-BASELINE-FINDINGS): its class and coverage are facts of the run k-rust made, but
/// no end of the definition is data (kink-native `data::data_ends`), so it kills nothing.
pub fn data_marked(mut rows: Vec<Value>, data: &kink_native::data::DataFacts) -> Vec<Value> {
    if kink_native::data::data_ends(data) == kink_native::data::DataEnds::None {
        for row in &mut rows {
            if ResultClass::can_kill(&row["class"]) {
                row["unable_to_kill"] = json!("baseline-findings");
            }
        }
    }
    rows
}

#[cfg(test)]
mod tests {
    use super::*;

    const EXCLUSIONS: [Exclusion; 10] = [
        Exclusion::StackStop,
        Exclusion::LoadStackStop,
        Exclusion::ContradictedClaim,
        Exclusion::ImplementationChosenHook,
        Exclusion::ShortCircuitReading,
        Exclusion::AllowanceRefusal,
        Exclusion::EqualsCondition,
        Exclusion::ImplementationChosenValue,
        Exclusion::UnsupportedHook,
        Exclusion::PassedStop,
    ];

    #[test]
    fn the_host_exclusions_are_the_stack_stops_and_the_allowance_refusal() {
        let host = EXCLUSIONS
            .into_iter()
            .filter(|&exclusion| host_exclusion(exclusion))
            .collect::<Vec<_>>();
        assert_eq!(
            host,
            [
                Exclusion::StackStop,
                Exclusion::LoadStackStop,
                Exclusion::AllowanceRefusal
            ]
        );
    }

    /// Every arm of [`host_dependence`]: a stored class is one no run of it depended on the host
    /// for, the diagnostic run's own host exclusions included.
    #[test]
    fn a_result_depends_on_the_host_through_either_run() {
        use HostDependence::{Exclusion as Host, Failure, Time};
        use ResultClass::{Comparable, Error, Refused, Timeout, Unknown};
        let finished = Some(RunStop::Finished);
        let claim = Some(Exclusion::ContradictedClaim);
        let stack = Some(Exclusion::StackStop);
        let cases = [
            (Comparable, None, finished, None, None),
            (Refused, None, None, None, None),
            (Timeout, None, Some(RunStop::Time), None, Some(Time)),
            (Error, None, finished, None, Some(Failure)),
            (Error, claim, finished, stack, Some(Failure)),
            // The live run's own facts.
            (
                Unknown,
                stack,
                finished,
                None,
                Some(Host(Exclusion::StackStop)),
            ),
            (Unknown, claim, Some(RunStop::Time), None, Some(Time)),
            (Unknown, None, Some(RunStop::Failed), None, Some(Failure)),
            (Unknown, claim, Some(RunStop::Failed), None, None),
            // A deterministic unknown, from either run.
            (Unknown, claim, finished, claim, None),
            (Unknown, None, finished, None, None),
            (Unknown, None, None, None, None),
            // The diagnostic run met a host exclusion the live run did not.
            (
                Unknown,
                None,
                finished,
                stack,
                Some(Host(Exclusion::StackStop)),
            ),
            (
                Unknown,
                claim,
                finished,
                stack,
                Some(Host(Exclusion::StackStop)),
            ),
            (
                Unknown,
                None,
                None,
                Some(Exclusion::AllowanceRefusal),
                Some(Host(Exclusion::AllowanceRefusal)),
            ),
            (
                Unknown,
                None,
                finished,
                Some(Exclusion::LoadStackStop),
                Some(Host(Exclusion::LoadStackStop)),
            ),
        ];
        for (class, exclusion, live_stop, diagnostic, expected) in cases {
            assert_eq!(
                host_dependence(class, exclusion, live_stop, diagnostic),
                expected,
                "{class:?} {exclusion:?} {live_stop:?} {diagnostic:?}"
            );
        }
    }

    /// A refused run's reason names what ended this command's live run of it: the campaign's
    /// `BaselineError` says only that admission produced no trustworthy evidence, which a run the
    /// watchdog cancelled and a run the adapter returned nothing for both give.
    #[test]
    fn a_refused_runs_reason_names_what_ended_the_live_run() {
        let error = kink_campaign::validate_baseline(kink_campaign::BaselineAdmission::Error)
            .expect_err("an error admission refuses");
        assert_eq!(
            refused_run(&error, Some(RunStop::Time), 30_000),
            "the watchdog stopped the run at time_ms = 30000, before it ended; a timeout depends \
             on the host's load"
        );
        let failed = refused_run(&error, Some(RunStop::Failed), 30_000);
        assert!(
            failed.starts_with("the execution adapter returned no execution")
                && failed.ends_with(&error.to_string()),
            "{failed}"
        );
        for live_stop in [Some(RunStop::Finished), None] {
            assert_eq!(
                refused_run(&error, live_stop, 30_000),
                format!("the campaign refused the run: {error}")
            );
        }
    }

    /// Only an oracle refusal naming no exclusion of a run the work bound stopped is read as a
    /// cached `unknown` without a diagnostic run; an error side of such a run is an `error`.
    #[test]
    fn only_an_oracle_refusal_of_a_work_bound_run_is_a_work_bound_unknown() {
        use CampaignFailureKind::{BaselineError, BaselineInvalid, BaselineOracleFailed};
        let bound = Some(20_000);
        assert!(work_bound_refusal(BaselineOracleFailed, None, bound, true));
        assert!(!work_bound_refusal(BaselineError, None, bound, true));
        assert!(!work_bound_refusal(BaselineInvalid, None, bound, true));
        assert!(!work_bound_refusal(
            BaselineOracleFailed,
            Some(Exclusion::StackStop),
            bound,
            true
        ));
        assert!(!work_bound_refusal(BaselineOracleFailed, None, None, true));
        assert!(!work_bound_refusal(
            BaselineOracleFailed,
            None,
            bound,
            false
        ));
    }

    /// A `ListItem(z)` list of `entries` entries, right-nested as k-rust hands an end in, built
    /// from the inside out (a pattern's clone, comparison, printing and drop keep their work on
    /// the heap).
    fn deep_list(entries: usize) -> Pattern {
        use k_rust::kompile::initial_configuration::kore_application;
        let z = kore_application("Lblz", Vec::new(), Vec::new());
        let mut list = kore_application("Lbl'Stop'List", Vec::new(), Vec::new());
        for _ in 0..entries {
            list = kore_application(
                "Lbl'Unds'List'Unds'",
                Vec::new(),
                vec![
                    kore_application("LblListItem", Vec::new(), vec![z.clone()]),
                    list,
                ],
            );
        }
        list
    }

    /// The comparable result whose one end is `end`, with its baseline row as kink-campaign
    /// writes it.
    fn comparable(end: &Pattern) -> ProgramResult {
        let evidence = kink_campaign::TestEvidence {
            test_id: "deep".into(),
            run: SideRun::Sides {
                sides: vec![OracleSide::Normal(OracleValue::FinalResult(
                    FinalResult::WholeTerm([end.clone()].into()),
                ))],
            },
            notes: kink_campaign::RunNotes::default(),
            ends: [end.clone()].into(),
            undefined_steps: false,
            one_sided_ends: BTreeSet::new(),
            stop_ends: BTreeSet::new(),
            payloads: BTreeMap::new(),
        };
        ProgramResult {
            class: ResultClass::Comparable,
            cause: None,
            baseline: Some(CampaignReport::baseline_row(&evidence)),
            final_configuration: None,
            ends: Some(json!([])),
            coverage: None,
            wall_ms: Some(1),
            specification_diagnostics: json!([]),
            smt_unknowns: 0,
            decider_smt_unknowns: 0,
            short_circuit_readings: json!([]),
            host: None,
        }
    }

    fn scratch(name: &str) -> PathBuf {
        let directory =
            std::env::temp_dir().join(format!("kink-flow-record-{name}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&directory);
        directory
    }

    /// The streamed record is the record's canonical JSON: the bytes `canonical_json` gives for it
    /// built as one value, so the change of writer changes no byte of a record.
    #[test]
    fn a_streamed_record_is_its_canonical_json() {
        let directory = scratch("canonical");
        let store = Store::new(&directory);
        let key = json!({"schema_version": RESULT_SCHEMA_VERSION, "program": "p"});
        let digest = payload_digest("test", b"spec");
        let mut unknown = ProgramResult::refused("a cause".into());
        unknown.class = ResultClass::Unknown;
        unknown.final_configuration = Some(vec!["Lblz{}()".into(), "\"\\n\u{e9}".into()]);
        for result in [comparable(&deep_list(3)), unknown] {
            let facts = record_facts(&key, digest, "p", &result, Value::Null);
            let path = directory.join("record.json");
            write_record(&store, &path, &facts, &result).unwrap();
            let mut whole = facts.clone();
            whole["baseline"] = json!(result.baseline);
            whole["final_configuration"] = json!(result.final_configuration);
            assert_eq!(fs::read_to_string(&path).unwrap(), canonical_json(&whole));
            assert_eq!(
                record_final_configuration(&whole),
                result.final_terms(),
                "{whole:#}"
            );
        }
        fs::remove_dir_all(&directory).unwrap();
    }

    /// A record member as deep as the limit allows is written on a stack sized from its depth, as
    /// `canonical_json` writes a value, so the promise that only a record deeper than
    /// `MAX_JSON_DEPTH` is refused holds on a thread whose own stack is far smaller than that
    /// member's serialization: no member is that deep today, but `write_record` must not depend
    /// on it.
    #[test]
    fn a_member_at_the_depth_limit_is_written_on_a_small_thread() {
        let directory = scratch("member-depth");
        let path = directory.join("record.json");
        let written = std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn({
                let (directory, path) = (directory.clone(), path.clone());
                move || {
                    let store = Store::new(&directory);
                    let key = json!({"schema_version": RESULT_SCHEMA_VERSION, "program": "p"});
                    let result = comparable(&deep_list(3));
                    let mut member = Value::Array(Vec::new());
                    for _ in 1..MAX_JSON_DEPTH - 1 {
                        member = Value::Array(vec![member]);
                    }
                    let mut facts = record_facts(
                        &key,
                        payload_digest("test", b"spec"),
                        "p",
                        &result,
                        Value::Null,
                    );
                    facts["coverage"] = member;
                    assert_eq!(value_depth(&facts), MAX_JSON_DEPTH);
                    let written = write_record(&store, &path, &facts, &result);
                    facts["baseline"] = json!(result.baseline);
                    facts["final_configuration"] = json!(result.final_configuration);
                    let written = written
                        .map(|()| canonical_json(&facts) == fs::read_to_string(&path).unwrap());
                    // serde_json drops a value one stack frame per level.
                    kink_patch::with_document_stack(MAX_JSON_DEPTH, move || drop(facts)).unwrap();
                    written.map_err(|error| error.to_string())
                }
            })
            .unwrap()
            .join()
            .unwrap();
        assert_eq!(written, Ok(true));
        fs::remove_dir_all(&directory).unwrap();
    }

    /// A record for a leaf deeper than the old bound is written and read back. Until result schema
    /// v12 the record held the baseline row's end as KORE JSON, two levels per list entry, so a
    /// list of more than `MAX_JSON_DEPTH / 2` entries was refused where the row was written, and a
    /// longer one aborted the process in the row's drop (about 840,000 entries in this build). Now
    /// the end is held once, as KORE text in the row: the record nests as deep as for a three-entry
    /// list, `read_record` honours it, its run digest is its row's, and the text decodes to the
    /// leaf. `MAX_JSON_DEPTH` entries (128,000 here) are past the old refusal; since no JSON depth
    /// depends on the entries, a longer list would show nothing more.
    #[test]
    fn a_record_for_a_deep_leaf_is_written_and_read_back() {
        let directory = scratch("deep");
        let store = Store::new(&directory);
        let key = json!({"schema_version": RESULT_SCHEMA_VERSION, "program": "deep"});
        let digest = payload_digest("test", b"spec");
        let deep = deep_list(MAX_JSON_DEPTH);
        let result = comparable(&deep);
        let facts = record_facts(&key, digest, "deep", &result, Value::Null);
        let path = directory.join("deep.json");
        write_record(&store, &path, &facts, &result).unwrap();
        let shallow = comparable(&deep_list(3));
        let shallow_path = directory.join("shallow.json");
        write_record(
            &store,
            &shallow_path,
            &record_facts(&key, digest, "deep", &shallow, Value::Null),
            &shallow,
        )
        .unwrap();
        let depth = |path: &Path| kink_patch::json_depth(&fs::read_to_string(path).unwrap());
        assert_eq!(depth(&path), depth(&shallow_path));
        let record = read_record(&path, &key)
            .unwrap()
            .expect("the record is honoured");
        assert!(
            record["final_configuration"].is_null(),
            "the ends are held once"
        );
        assert_eq!(
            record["run_sha256"],
            json!(result.run_sha256().map(|d| d.to_string()))
        );
        assert!(verify_record(&record, &result).is_empty());
        let ends = record_final_configuration(&record).unwrap();
        assert_eq!(ends.len(), 1);
        let decoded = k_rust::kore::parser::parse_pattern(ends[0]).unwrap();
        assert!(
            decoded == deep,
            "the record's end decodes to another pattern"
        );
        fs::remove_dir_all(&directory).unwrap();
    }
}
