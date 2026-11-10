//! `kink-flow query FLOW.toml PATTERNS.toml` (flow F-18): the per-input pattern checks of
//! [`crate::pattern`], with a cache of their definitive answers.
//!
//! The command admits the specification, brings the result cache up to date (`coverage` without
//! `--verify`, or with it under `query --verify`), lowers every selected pattern once, and asks
//! each pattern of each program it names (its claimed programs, then its obligation's walk:
//! "The obligation", below), unless a cached answer stands, by one of two routes
//! ([`crate::pattern::Route`]):
//! - a corpus without `[stop]`: one `search_pattern_kore` per (pattern, program), which explores
//!   the definition's own reachable states;
//! - a corpus with `[stop]`: the program's run as every campaign of the command makes it (the
//!   stop's rules, the program's count and the stop's condition, in one execute request), which
//!   matches every state it reaches against the pattern (`Searcher::run_stopped`). A stop is part
//!   of a case's meaning: a path of the case ends at its last stop event, so a state past it is no
//!   state of the case. A pattern only such a state matches is a `no`, and a complete exploration
//!   of the truncated system is a complete answer, also for a program whose untruncated run never
//!   ends. A run that passed a stop (a step of a stop rule that had another successor), whose
//!   condition refused, or that some count left undecided answers `unknown`.
//!
//! `[observe]` is admitted and ignored on both routes, and the document says so (`observe`): an
//! observation channel is the instrument by which two definitions' runs are compared, and it
//! changes neither which states one definition's run reaches nor where it ends. Its one effect on
//! a query is that a program a bound cuts is `comparable-prefix`, not `comparable`, and a `no`
//! keeps requiring `comparable`.
//!
//! **The cache** holds only `hit` and a final `no`, one record per (pattern, program):
//! `patterns/<execution digest>/<pattern digest>/<program digest>.json` in the cache directory,
//! written atomically, `{schema: "kink-flow-pattern", key, pattern_id, program_id, answer, witness,
//! baseline_run_sha256, record_sha256}`, a hit's `witness` its facts (`{depth, state, bindings,
//! rules}`, the state and the bindings as whole KORE text; `crate::pattern`, "A witness"): the
//! document prints it when it is written, a cached hit as a live one, so the printing is in no
//! key. The key ([`answer_key`]) names every input an answer
//! depends on: the record's schema, the lowering version, the k-rust revision, kink's build
//! (`kink_build`, the executable's SHA-256, so any rebuild starts a new key: packet CACHE-ID-fix-1)
//! and its semantics identity (`kink`), the execution digest (`digest::execution_digest`: the
//! loaded definition without positions, the k-rust revision and the profile, so a comment or layout
//! edit keeps every answer), the program digest (its bytes, start sort and variables), the
//! pattern's digest (its KORE target and generated variables), the budget's bounds
//! (`results::budget_value`, without `time_ms`: a stored answer is a hit or the `no` of a complete
//! exploration, neither of which the clock decided), and the search's modality (search type all,
//! state set, at most one result), and on the stopped route the program's stop
//! (`FlowManifest::program_stop`: the rules, the program's count and the condition's identity)
//! with the route's modality ([`crate::pattern::stopped_modality`]); a key without a stop keeps
//! the bytes it had before the stopped route existed. A record is used only when its key is exactly the current one
//! and its `record_sha256` recomputes; a `no` also only while the program's current result record
//! is comparable with the baseline run digest the `no` was given against. A used record's answer is
//! judged again with the current command's facts (the definition exclusions of this command's load,
//! the initial state's exclusion, the baseline class, the profile), so a record never answers more
//! than a live search would.
//!
//! **Trust.** A cached answer stands without a search in this command. It rests on the integrity
//! of the cache directory (whoever can write it can forge an answer, as for every kink cache) and
//! on the key naming every input; it does not rest on k-rust's determinism: a `hit` and a final
//! `no` are facts about the definition and the program, which a later search can only fail to
//! re-derive (an unknown), never contradict. `--verify` re-derives every answer of the selected
//! patterns live, compares it with each stored record a command without `--verify` would use
//! (the answer, and for a hit what is a fact of it: the witness's depth and state, and its
//! bindings and rules where both sides carry them, [`same_witness`]),
//! reports every difference (`mismatches`: `{pattern, program, record, cached, live}`) and exits 1
//! on one; it writes no pattern record. Each live answer is judged with the program's live
//! baseline run (`ProgramRow::live`), not with a stored result record `--verify` found different.
//! The cache is off where tier 1 is (`search::tier1_refusal`: under the Z3 profile with a solver
//! the clock bounds, or whose build cannot be named) and when kink's build identity is unknown.
//! Under the Z3 profile with kink's resource-bounded solver an answer is a function of its key,
//! which names the solver's units and Z3 build (the budget's `smt`).
//!
//! **The obligation** (FB54-WITNESS). A pattern also states "some program's run reaches a state
//! that matches it", an existential over the corpus of the shape of a mutant's "some program
//! tells it apart", and a witness discharges it as a killer discharges a mutant. Let w be the
//! pattern's recorded witness (the `[query]` section of the lock, [`crate::lock`]). The witness
//! is w when w names a program of the corpus and w hits, else the first program in corpus order
//! that hits, else none ([`obligation`]): a function of the record and the corpus, not of what
//! was asked or in which order, so adding a program moves no witness while w still hits, and
//! deleting w re-opens the obligation. Its status is `hit`, `open` (every program answered a final
//! `no`) or `undecided`. The pattern's claims (`programs`) are asked first, then the obligation's
//! walk: w first, then corpus order, until the first hit ([`walk_order`]), reusing every answer a
//! claim gave; `--full` asks every pair and lists every hitter, with the same witness. A
//! pattern's `expect = "no"` is checked against its obligation ([`pattern_expectation`]) and
//! enters no lock. With `--lock` the section is read before anything runs and settled after
//! ([`Lock::settle`]); an obligation whose value rests on a run the clock stopped keeps its
//! recorded value ([`keep`]).
//!
//! No answer enters a result record, an outcome record, a run document or the `[run]` and
//! `[coverage]` sections of a lock: pattern answers feed no kill and no mutation verdict. The
//! `[query]` section records each obligation, which only `query` reads.

use crate::{
    admit::admit_spec,
    clock::Kept,
    digest::ExecutionDigest,
    evidence::EndReader,
    lock::{Lock, LockKind, Settle},
    manifest::{FlowManifest, ManifestError},
    pattern::{
        Answer, Facts, INVALID_PATTERN, LOWERING_VERSION, LoweredPattern, Lowering, PatternEntry,
        PatternExpect, PatternForm, PatternList, Route, SearchOutcome, Searcher, judge,
        search_modality, stopped_modality,
    },
    results::{
        BaselineRunner, ProgramRow, ResultsUpdate, budget_value, cache_directory, runner_refusal,
        update_results,
    },
    search::tier1_refusal,
};
use kink_corpus::{Store, admission::AdmissionRecord};
use kink_native::{K_RUST_REVISION, execution::SolverProfile};
use kink_patch::{Sha256Digest, canonical_json, parse_json, payload_digest};
use serde_json::{Map, Value, json};
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
};

/// The query document's schema and version. Version 2 adds the refusal at stage `stop` (reason
/// `unsupported-verb`) of a corpus with `[stop]`. Added to 2 without a new version, since a
/// corpus without a case expectation or a named case has the document it had and no command
/// reads a query document back: a program row of a case with an expectation carries
/// `expectation` (`crate::expect`). Version 3 (KINK-query-no-z3) answers `no` under the Z3
/// profile where the search received no undecided solver answer, with a `cause` naming that
/// count, and names the count in the `cause` of an `unknown` it withholds a `no` for. Version 4
/// names, under the Z3 profile, the Z3 build the answers were decided on (`z3`,
/// [`crate::with_z3_build`]): whether a search's solver queries are decided within their units is
/// a function of the build that counts them, so a `hit`, a `no` and an `unknown` are too. Version
/// 5 (FB-41) admits a corpus with `[stop]`, answered by its stopped run (module docs), and one
/// with `[observe]`, which it ignores: the refusals at stages `stop` and `observe` are gone, the
/// document names the stop (`stop`, as `check`, `coverage` and `run` do) and the observation
/// (`observe`: `{declaration, ignored}`, the declaration and why the query ignores it) when the
/// manifest has them, and each row names its route (`route`: `search` or `stopped-run`); a hit's
/// witness on the stopped route has `rules` null.
pub const QUERY_SCHEMA: &str = "kink-flow-query";
/// Version 6 names each finding of the full critical-pair check by its kind, sentences and a digest
/// of its compiled sentences (`root:A,B#D`, k-rust-backend `data_term::names`) where it named it by
/// generated-K positions, gives each finding its `sentences` (`{part, at}`, `at` information only),
/// and refuses a `[spec] assume_joined` name with one of the reasons `malformed`, `position-name`,
/// `unnamed-sentence`, `no-digest`, `changed`, `no-finding`, `decided` or `ambiguous` where it
/// refused `name-refused` (KINK-FINDING-NAMES).
/// Version 7 (FB54-WITNESS) makes every pattern an obligation of the corpus: `obligations`, one
/// per selected pattern (`{id, status, witness, recorded_witness, witness_change, hitters,
/// unanswered, expect, expectation, clock_stopped}`, module docs), each row's `clock_stopped`,
/// `full` and, with `--lock`, `lock`. A pattern without `programs` is asked until its first hit
/// (its recorded witness first, then corpus order) unless `--full`, where version 6 asked every
/// program, so `rows` holds only the pairs asked; a pattern with `programs` is also asked for
/// its obligation.
/// Version 8 (FB-51) prints a hit's witness for a reader (`crate::pattern::rendered_witness`): the
/// state `{cells: [{path, named, value}]}`, the cells the pattern names in full as K text and every
/// other shortened by its structure (`crate::evidence`, "A query witness"), each binding's
/// `variable` by its name and its `value` printed likewise, `rendering` `k`, where version 7 gave
/// the state and the bindings as KORE text cut to 4000 characters (`{kore, truncated}`). A
/// `--verify` mismatch keeps the witnesses' facts, KORE text in full, since two witnesses may
/// differ in a cell the printing shortens. A pattern that does not parse and writes a cell tag
/// that is no cell of the configuration names it, and the configuration's cells, in its `cause`
/// (FB-53).
pub const QUERY_VERSION: u64 = 8;
/// A cached answer's schema, and its key's `schema_version`.
pub const RECORD_SCHEMA: &str = "kink-flow-pattern";
/// The record's format and what its answers mean: it changes whenever what counts as a hit or a
/// no changes (v2, flow F-18 tail: a matched state holding a term-level `\and` is not a hit; v3,
/// fz26 KRUST-ANYWHERE-HEAD: a matched state is defined when k-rust's `ground_defined` holds,
/// which also accepts an irreducible `value-production` application such as SIMPLE's `a[4]`; v4,
/// KINK-R4: a match is no hit when the search left a hook application unevaluated, its
/// `unsupportedHooks` or `allowanceRefusals` list not empty, so a v3 `hit` may no longer be one;
/// an exploration with such a list is not complete, so a v3 `no` may no longer be one either; and
/// a `no` needs the definition to have data, its check complete as well as finding-free; v5, kink27
/// R3-CENSUS-RUNLEVEL: a `no` also needs the search's `implementationChosenValues` empty, since
/// k-rust's classes are judged per run rather than by the census, so a v4 `no` may no longer be
/// one; v6, CF-03: on a definition whose short-circuit analysis flags a rule, a `no` needs the
/// search's `shortCircuitReadings` list to hold no entry that counts, as a run's list is judged,
/// where before no `no` was given on such a definition, and an initial state that applies a
/// reading-dependent function is judged by the same list on every definition, as a run's is; a
/// `no` may now be given where a v5 answer was `unknown`, and a `hit` is unchanged; v7: answers
/// are stored under the Z3 profile too, where the solver is resource-bounded and the key's budget
/// names its units and Z3 build, so a record may hold an answer that rests on solver answers; v8,
/// KINK-query-no-z3: a `no` is given under the Z3 profile too, on a completed search that received
/// no undecided solver answer, so a `no` may now be given where a v7 answer was `unknown`, and a
/// stored `no` stands for a search that counted none; the stopped route's records are v8 too:
/// their key holds a `stop`, which no earlier record's does, so no stored answer changes meaning;
/// v9, FB-51: a hit's witness is kept as facts, `{depth, state, bindings, rules}`, the state and
/// each binding as whole KORE text, where a v8 witness held the text cut to 4000 characters and a
/// rendering; the answers mean what they meant).
pub const ANSWER_SCHEMA_VERSION: &str = "kink-flow/pattern-answer/v9";
/// Domain of a record's digest.
pub const PATTERN_RECORD_DOMAIN: &str = "kink-flow/pattern-answer/v1";
/// The cache's directory in the cache directory.
pub const PATTERN_DIRECTORY: &str = "patterns";
/// Every answer a row can have, in the order `counts` lists them.
pub const ANSWERS: [&str; 5] = ["hit", "no", "unknown", INVALID_PATTERN, "error"];

/// Options of the `query` command.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct QueryOptions {
    /// The ids of the patterns to ask; empty asks every pattern.
    pub only: Vec<String>,
    /// Re-derive every answer and compare it with its stored record (module docs).
    pub verify: bool,
    /// The cache directory; default `<directory of FLOW.toml>/.kink-flow`.
    pub cache: Option<PathBuf>,
    /// `--full`: ask every (pattern, program) pair, and list each obligation's `hitters`, where
    /// a query without it stops each obligation at its first hit (module docs). The witness, the
    /// status and the lock are the same either way.
    pub full: bool,
    /// `--lock FILE`: the corpus record whose `[query]` section the command reads (each
    /// pattern's recorded witness, asked first) and rewrites after a query of the whole list.
    pub lock: Option<PathBuf>,
    /// `--locked`: compare the section the query would write with the file's, and write nothing.
    pub locked: bool,
}

/// The key of a cached answer (module docs); `stop` is the program's stop on the stopped route
/// (`FlowManifest::program_stop`), `None` on the search route.
pub fn answer_key(
    build: Sha256Digest,
    execution: ExecutionDigest,
    program: Sha256Digest,
    pattern: Sha256Digest,
    budget: crate::manifest::Budget,
    stop: Option<Value>,
) -> Value {
    let mut key = json!({
        "schema_version": ANSWER_SCHEMA_VERSION,
        "lowering": LOWERING_VERSION,
        "k_rust_revision": K_RUST_REVISION,
        "kink_build": build.to_string(),
        "kink": kink_campaign::kink_identity(),
        "execution": execution.value(),
        "program": program.to_string(),
        "pattern": pattern.to_string(),
        // The result key's budget object, so both keys name the same bounds.
        "budget": budget_value(budget),
        "modality": search_modality(),
    });
    if let Some(stop) = stop {
        key["stop"] = stop;
        key["modality"] = stopped_modality();
    }
    key
}

/// Where the record of (`pattern`, `program`) is kept under the execution digest `execution`.
/// The key decides what a record may be used for; the path only finds it.
pub fn answer_path(
    cache: &Path,
    execution: Sha256Digest,
    pattern: Sha256Digest,
    program: Sha256Digest,
) -> PathBuf {
    cache
        .join(PATTERN_DIRECTORY)
        .join(execution.to_string())
        .join(pattern.to_string())
        .join(format!("{program}.json"))
}

/// The digest a record carries: of its key, answer, witness and baseline run digest.
pub fn record_sha256(
    key: &Value,
    answer: &str,
    witness: &Value,
    baseline_run_sha256: &Value,
) -> Sha256Digest {
    payload_digest(
        PATTERN_RECORD_DOMAIN,
        canonical_json(&json!({
            "key": key,
            "answer": answer,
            "witness": witness,
            "baseline_run_sha256": baseline_run_sha256,
        }))
        .as_bytes(),
    )
}

/// A stored answer that may be used (module docs): `(answer, witness, baseline_run_sha256)`.
struct Stored {
    answer: String,
    witness: Value,
    baseline_run_sha256: Value,
}

impl Stored {
    /// The search outcome the record stands for. A `no` is stored only as `judge` gave it, on a
    /// completed search that received no undecided solver answer, so it stands for that search.
    fn outcome(&self) -> SearchOutcome {
        if self.answer == "hit" {
            SearchOutcome::Hit(self.witness.clone())
        } else {
            SearchOutcome::Complete { smt_unknowns: 0 }
        }
    }
}

fn read_record(path: &Path, key: &Value) -> Option<Stored> {
    let record = parse_json(&fs::read_to_string(path).ok()?).ok()?;
    let answer = record["answer"].as_str()?.to_owned();
    let witness = record.get("witness")?.clone();
    let baseline = record.get("baseline_run_sha256")?.clone();
    let well_formed = match answer.as_str() {
        "hit" => witness.is_object() && baseline.is_null(),
        "no" => witness.is_null() && baseline.is_string(),
        _ => false,
    };
    (record["schema"] == RECORD_SCHEMA
        && record["key"] == *key
        && well_formed
        && record["record_sha256"].as_str()
            == Some(
                record_sha256(key, &answer, &witness, &baseline)
                    .to_string()
                    .as_str(),
            ))
    .then_some(Stored {
        answer,
        witness,
        baseline_run_sha256: baseline,
    })
}

/// Why the cache is off for this command, whose backends are built with `solver`, or `None`.
fn cache_refusal(
    build: Option<Sha256Digest>,
    solver: k_rust::backend::BackendOptions,
) -> Option<String> {
    if let Some(reason) = tier1_refusal(SolverProfile::BUILD, solver) {
        return Some(format!("the pattern cache is off, as tier 1 is: {reason}"));
    }
    build.is_none().then(|| {
        "kink's build identity is unknown (the executable cannot be read): the pattern cache is \
         neither read nor written"
            .to_owned()
    })
}

/// `kink-flow query`: the query document and whether the command found no corpus or
/// infrastructure error; the exit status joins it with the status the document gives
/// (`crate::cli::query_status`).
pub fn query(manifest: &FlowManifest, list: &PatternList, options: &QueryOptions) -> (Value, bool) {
    query_spelled(manifest, list, options, "kink-flow query")
}

/// [`query`], with `command`, the front end's spelling of the verb, which a refusal of the lock
/// under `--locked` names as the command that rewrites it.
pub fn query_spelled(
    manifest: &FlowManifest,
    list: &PatternList,
    options: &QueryOptions,
    command: &str,
) -> (Value, bool) {
    query_with(manifest, list, options, command, &|_| {})
}

/// [`query_spelled`], with `adjust` applied to the definition exclusions of the searcher's load
/// before any answer is judged: the unit tests' seam for a load fact a test cannot provoke (a load
/// stack stop depends on the host's stack).
///
/// With `options.lock` the record's `[query]` section is read before anything runs (a record
/// that does not decode, or under `--locked` one of another version, refuses the command) and
/// settled after ([`Lock::settle`]): the document's `lock`. A query of the whole list (no
/// `--only`, no `--verify`, not refused) without `--locked` rewrites the section.
pub(crate) fn query_with(
    manifest: &FlowManifest,
    list: &PatternList,
    options: &QueryOptions,
    command: &str,
    adjust: &dyn Fn(&mut kink_native::exclusion::DefinitionExclusions),
) -> (Value, bool) {
    let lock = match options.lock.as_deref() {
        None => None,
        Some(path) => match Lock::read_for(path, LockKind::Query, None, options.locked, command) {
            Ok(lock) => Some(lock),
            Err(detail) => {
                let mut document = refused_document(&AdmissionRecord::new(&manifest.spec.entry));
                document["spec"] = Value::Null;
                document["lock"] = crate::lock::refused_value(path, &detail);
                return (named(manifest, document), false);
            }
        },
    };
    let recorded = lock.as_ref().map(Lock::witnesses).unwrap_or_default();
    let (mut document, mut ok) = query_unnamed(manifest, list, options, &recorded, adjust);
    if let Some(lock) = &lock {
        document["lock"] = if document["spec"]["outcome"] == "admitted" {
            let store = Store::new(cache_directory(manifest, options.cache.as_deref()));
            let settle = Settle {
                locked: options.locked,
                verify: options.verify,
                only: &options.only,
                stopped: false,
            };
            let (value, written) = lock.settle(&store, &document, settle);
            ok &= written;
            value
        } else {
            lock.not_written("refused")
        };
    }
    (named(manifest, document), ok)
}

/// Why a query refuses a list whose selected patterns hold a chain (`steps`): a chain is decoded
/// and its variables are checked ([`crate::pattern::chain`]), but no route evaluates one yet, and
/// answering it as any other pattern would answer another question.
pub const CHAIN_NOT_EVALUATED: &str = "chain patterns are not evaluated yet: this build decodes \
     and checks `steps` but has no route that answers a chain; ask the other patterns with --only";

/// Why a query ignores `[observe]` (module docs).
pub const OBSERVE_IGNORED: &str = "a pattern query asks which states one definition's run \
     reaches; observation channels compare two definitions' runs, and change neither which states \
     a run reaches nor where it ends";

/// `document` naming the manifest's stop (`stop`) and observation (`observe`: the declaration,
/// and why the query ignores it) when it has them, as every query document does, a refused one's
/// too (version 5).
pub fn named(manifest: &FlowManifest, mut document: Value) -> Value {
    if let Some(stop) = manifest.stop_value() {
        document["stop"] = stop;
    }
    if let Some(observe) = manifest.observe_value() {
        document["observe"] = json!({"declaration": observe, "ignored": OBSERVE_IGNORED});
    }
    document
}

fn query_unnamed(
    manifest: &FlowManifest,
    list: &PatternList,
    options: &QueryOptions,
    recorded: &BTreeMap<String, String>,
    adjust: &dyn Fn(&mut kink_native::exclusion::DefinitionExclusions),
) -> (Value, bool) {
    if let Err(error) = list.check_programs(manifest) {
        return (pattern_list_refused(&error), false);
    }
    if let Some(entry) = list.patterns.iter().find(|entry| {
        matches!(entry.form, PatternForm::Chain(_))
            && (options.only.is_empty() || options.only.contains(&entry.id))
    }) {
        let error = ManifestError::new(
            format!("{}.steps", crate::pattern::pattern_key(&entry.id)),
            CHAIN_NOT_EVALUATED,
        );
        return (pattern_list_refused(&error), false);
    }
    let (mut record, admitted) = admit_spec(manifest);
    let Some((spec, mut inputs)) = admitted else {
        return (refused_document(&record), false);
    };
    let mut inputs = inputs.session(&spec);
    let cache = cache_directory(manifest, options.cache.as_deref());
    let runner = match BaselineRunner::new(&spec, manifest) {
        Ok(runner) => runner,
        Err(e) => {
            record.refusal = Some(runner_refusal(e));
            return (refused_document(&record), false);
        }
    };
    let update = update_results(
        &spec,
        manifest,
        &mut inputs,
        &runner,
        &cache,
        options.verify,
        None,
    );
    let mut ok = update.ok();
    let setup =
        Searcher::new(&spec, &manifest.spec.main_module, manifest.budget).and_then(|searcher| {
            Lowering::new(&spec, &manifest.spec.main_module).map(|lowering| (searcher, lowering))
        });
    let (mut searcher, lowering) = match setup {
        Ok(setup) => setup,
        Err(detail) => {
            record.refusal = Some(kink_corpus::admission::AdmissionRefusal {
                stage: "query".into(),
                reason: "search-backend".into(),
                detail,
            });
            return (refused_document(&record), false);
        }
    };
    let mut exclusions = searcher.exclusions().clone();
    adjust(&mut exclusions);
    let route = if manifest.stop.is_some() {
        Route::StoppedRun
    } else {
        Route::Search
    };
    let build = kink_campaign::kink_build().ok();
    let refusal = cache_refusal(build, manifest.budget.backend_options());
    let cache_build = build.filter(|_| refusal.is_none());
    let store = Store::new(&cache);
    let spec_digest = update.spec_digest;
    let execution = update.execution;
    let mut mismatches = update.mismatches.clone();
    let mut accounting = json!({"from_cache": 0, "records_written": 0});
    let mut patterns = Vec::new();
    let mut rows = Vec::new();
    let mut obligations = Vec::new();
    let context = Context {
        manifest,
        update: &update,
        cache: &cache,
        store: &store,
        build: cache_build,
        execution,
        verify: options.verify,
        exclusions: &exclusions,
        route,
        reader: runner.end_reader(),
    };
    for entry in list
        .patterns
        .iter()
        .filter(|entry| options.only.is_empty() || options.only.contains(&entry.id))
    {
        let PatternForm::Single(text) = &entry.form else {
            unreachable!("a chain among the selected patterns refuses the list before admission")
        };
        let lowered = lowering.lower(text, searcher.definition());
        let claimed = entry.programs.is_some();
        patterns.push(json!({
            "id": entry.id,
            "note": entry.note,
            "pattern": text,
            "outcome": if lowered.is_ok() { "valid" } else { INVALID_PATTERN },
            "detail": lowered.as_ref().err(),
            "digest": lowered.as_ref().ok().map(|l| l.digest.to_string()),
            "kore": lowered.as_ref().ok().map(LoweredPattern::kore),
            "asked": if claimed { "claimed" } else { "corpus" },
            "expect": entry.expect.map(PatternExpect::as_str),
        }));
        // Each program's row of this pattern, by corpus index, in the order they were asked: the
        // claims first, then the obligation's walk, which reuses every answer a claim gave and,
        // without `--full`, stops at its first hit.
        let mut answered: Vec<(usize, Value)> = Vec::new();
        let claims = entry
            .programs
            .iter()
            .flatten()
            .map(|program_id| {
                manifest
                    .programs
                    .iter()
                    .position(|p| &p.id == program_id)
                    .expect("check_programs: every claimed program exists")
            })
            .collect::<Vec<_>>();
        let recorded_witness = recorded.get(&entry.id).map(String::as_str);
        // An invalid pattern never runs: it is answered for its claims, or, without claims, for
        // every program, and its obligation is undecided either way.
        let walk = if lowered.is_err() && entry.programs.is_some() {
            Vec::new()
        } else {
            walk_order(manifest, recorded_witness, options.full)
        };
        for (index, claim) in claims
            .into_iter()
            .map(|index| (index, true))
            .chain(walk.into_iter().map(|index| (index, false)))
        {
            let answer = match answered.iter().find(|(at, _)| *at == index) {
                Some((_, row)) => row["answer"].clone(),
                None => {
                    let program_id = manifest.programs[index].id.as_str();
                    let mut row = Map::new();
                    row.insert("pattern".into(), json!(entry.id));
                    row.insert("program".into(), json!(program_id));
                    row.insert("claimed".into(), json!(claim));
                    row.insert("route".into(), json!(route.name()));
                    let (row, row_ok) = match &lowered {
                        Ok(lowered) => ask(
                            &context,
                            &mut inputs,
                            &spec,
                            &mut searcher,
                            index,
                            &entry.id,
                            lowered,
                            row,
                            claim,
                            &mut mismatches,
                            &mut accounting,
                        ),
                        Err(detail) => {
                            let answer = Answer {
                                answer: INVALID_PATTERN,
                                cause: Some(detail.clone()),
                                witness: None,
                            };
                            let mut row = finish_row(row, &answer, false, None, claim);
                            row["clock_stopped"] = Value::Null;
                            (row, true)
                        }
                    };
                    ok &= row_ok;
                    let answer = row["answer"].clone();
                    answered.push((index, row.clone()));
                    rows.push(row);
                    answer
                }
            };
            if !claim && !options.full && answer == "hit" {
                break;
            }
        }
        obligations.push(obligation(
            manifest,
            entry,
            recorded_witness,
            &answered,
            options.full,
        ));
    }
    ok &= mismatches.is_empty();
    let pattern_cache = json!({
        "enabled": refusal.is_none(),
        "reason": refusal,
        "verify": options.verify,
        "from_cache": accounting["from_cache"],
        "records_written": accounting["records_written"],
    });
    let programs = crate::results::data_marked(
        update.rows.iter().map(|row| row.row.clone()).collect(),
        &spec.data,
    );
    let mut document = document(
        &record,
        Some(spec_digest),
        programs,
        patterns,
        rows,
        mismatches,
        pattern_cache,
        runner.baseline_runs(),
    );
    document["spec"]["execution_digest"] = execution.value();
    document["data"] = spec.data.value();
    document["obligations"] = json!(obligations);
    document["full"] = json!(options.full);
    (document, ok)
}

/// The order a pattern's obligation asks the corpus in: its recorded witness first, where it
/// names a program of the corpus, then every other program in corpus order. Under `--full`
/// every program is asked, in corpus order. The order decides only what is asked, not the
/// witness ([`obligation`]).
fn walk_order(manifest: &FlowManifest, recorded: Option<&str>, full: bool) -> Vec<usize> {
    let first = recorded
        .filter(|_| !full)
        .and_then(|id| manifest.programs.iter().position(|p| p.id == id));
    first
        .into_iter()
        .chain((0..manifest.programs.len()).filter(|index| Some(*index) != first))
        .collect()
}

/// The obligation of the pattern `entry` (module docs, "The obligation"), from the rows of its
/// programs it asked (`answered`, by corpus index) and its recorded witness `recorded`:
/// `{id, status, witness, recorded_witness, witness_change, hitters, unanswered, expect,
/// expectation, clock_stopped}`.
///
/// - The witness is the recorded witness where it hit, else the first program in corpus order
///   that hit: a function of the corpus and the record, not of what else was asked or in which
///   order, so a query and a `--full` one give the same.
/// - `status`: `hit` with a witness, `open` when every program of the corpus answered a final
///   `no`, else `undecided` (no hit, and some program's answer is `unknown`, an error or
///   `invalid-pattern`).
/// - `hitters`: under `--full`, every program that hit, in corpus order; else null.
/// - `unanswered`: the programs whose answer is neither a hit nor a final `no`, in corpus order.
/// - `witness_change`: null when the witness is the recorded one, else `no-record`,
///   `not-in-corpus`, `clock-stopped` (the clock stopped the recorded witness's search, so
///   whether it still hits is not decided on this host), `no-longer-hits` (it was asked, live or
///   cached, and did not hit) or `not-run` (its search never ran: the pattern is invalid).
/// - `clock_stopped`: the runs the clock stopped that the status and witness depend on
///   (`{program, run}`, `run` `search` or `baseline`, in corpus order): for a hit by the recorded
///   witness none; for another hit each search it stopped of the recorded witness or of a
///   program before the witness in corpus order (it could have hit); for `undecided` each run it
///   stopped (a search could have hit, a baseline could have licensed a `no`); for `open` none.
fn obligation(
    manifest: &FlowManifest,
    entry: &PatternEntry,
    recorded: Option<&str>,
    answered: &[(usize, Value)],
    full: bool,
) -> Value {
    let mut by_index = answered.iter().collect::<Vec<_>>();
    by_index.sort_by_key(|(index, _)| *index);
    let id_of = |index: usize| manifest.programs[index].id.clone();
    let hit = |row: &Value| row["answer"] == "hit";
    let recorded_index = recorded.and_then(|id| manifest.programs.iter().position(|p| p.id == id));
    let recorded_row = recorded_index.and_then(|at| {
        answered
            .iter()
            .find(|(index, _)| *index == at)
            .map(|(_, row)| row)
    });
    let witness_index = recorded_index
        .filter(|_| recorded_row.is_some_and(hit))
        .or_else(|| {
            by_index
                .iter()
                .find(|(_, row)| hit(row))
                .map(|(index, _)| *index)
        });
    let witness = witness_index.map(id_of);
    let every_no = by_index.len() == manifest.programs.len()
        && by_index.iter().all(|(_, row)| row["answer"] == "no");
    let status = if witness.is_some() {
        "hit"
    } else if every_no {
        "open"
    } else {
        "undecided"
    };
    let change = match recorded {
        _ if witness.as_deref() == recorded => None,
        None => Some("no-record"),
        Some(_) => Some(match recorded_row {
            None if recorded_index.is_none() => "not-in-corpus",
            None => "not-run",
            Some(row) if row["clock_stopped"] == "search" => "clock-stopped",
            Some(row) if row["answer"] == INVALID_PATTERN => "not-run",
            Some(_) => "no-longer-hits",
        }),
    };
    let stop = |(index, row): &&(usize, Value)| {
        row["clock_stopped"]
            .as_str()
            .map(|run| json!({"program": id_of(*index), "run": run}))
    };
    let clock_stopped: Vec<Value> = match (status, witness_index) {
        ("hit", Some(at)) if Some(at) == recorded_index => Vec::new(),
        ("hit", Some(at)) => by_index
            .iter()
            .filter(|(index, row)| {
                row["clock_stopped"] == "search" && (*index < at || Some(*index) == recorded_index)
            })
            .filter_map(stop)
            .collect(),
        ("undecided", _) => by_index.iter().filter_map(stop).collect(),
        _ => Vec::new(),
    };
    let unanswered = by_index
        .iter()
        .filter(|(_, row)| !hit(row) && row["answer"] != "no")
        .map(|(index, _)| id_of(*index))
        .collect::<Vec<_>>();
    let hitters = full.then(|| {
        by_index
            .iter()
            .filter(|(_, row)| hit(row))
            .map(|(index, _)| id_of(*index))
            .collect::<Vec<_>>()
    });
    let mut obligation = json!({
        "id": entry.id,
        "status": status,
        "witness": witness,
        "recorded_witness": recorded,
        "witness_change": change,
        "hitters": hitters,
        "unanswered": unanswered,
        "expect": entry.expect.map(PatternExpect::as_str),
        "expectation": null,
        "clock_stopped": clock_stopped,
    });
    obligation["expectation"] = pattern_expectation(&obligation);
    obligation
}

/// The `expectation` of an obligation whose pattern states `expect` (the obligation's own
/// `expect`): `{verdict, detail}`, null for a pattern without one. `expect = "no"` claims that
/// no program of the corpus reaches a state matching the pattern: it is `met` when every program
/// answered a final `no` (`open`), `unmet` on a hit, a finding, and `inconclusive` otherwise
/// (`undecided`: some program's answer is not final).
#[must_use]
pub fn pattern_expectation(obligation: &Value) -> Value {
    if obligation["expect"] != PatternExpect::No.as_str() {
        return Value::Null;
    }
    let names = |key: &str| {
        obligation[key]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .collect::<Vec<_>>()
            .join(", ")
    };
    match obligation["status"].as_str() {
        Some("open") => json!({
            "verdict": "met",
            "detail": "expected no: every program of the corpus answered a final no",
        }),
        Some("hit") => json!({
            "verdict": "unmet",
            "detail": format!(
                "expected no, but {}'s run reaches a state that matches the pattern",
                obligation["witness"].as_str().unwrap_or("a program")
            ),
        }),
        _ => json!({
            "verdict": "inconclusive",
            "detail": format!(
                "expected no: no program hits, but {} answered no final no",
                names("unanswered")
            ),
        }),
    }
}

/// `document` with each obligation the clock leaves undecided given its recorded value from
/// `lock` (`crate::clock`'s rule, applied to `query`), with the stopped runs and the kept
/// entries. An obligation whose `clock_stopped` is not empty keeps its recorded `{status,
/// witness}`, unless the lock records nothing for it, the recorded status is not one a query
/// gives, the recorded witness is no program of the corpus, or the query found a hit where the
/// lock records none: each is a fact the run decided that the recorded entry contradicts, and
/// the query's own value is written.
#[must_use]
pub fn keep(lock: &Lock, document: &Value) -> Kept {
    let mut kept = Kept {
        document: document.clone(),
        stopped: Vec::new(),
        kept: Vec::new(),
        failed: Vec::new(),
    };
    let programs = document["programs"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|row| row["id"].as_str())
        .collect::<Vec<_>>();
    let Some(obligations) = kept
        .document
        .pointer_mut("/obligations")
        .and_then(Value::as_array_mut)
    else {
        return kept;
    };
    for obligation in obligations {
        let id = obligation["id"].as_str().unwrap_or_default().to_owned();
        let stops = obligation["clock_stopped"]
            .as_array()
            .cloned()
            .unwrap_or_default();
        if stops.is_empty() {
            continue;
        }
        for stop in &stops {
            kept.stopped
                .push(json!({"pattern": id, "program": stop["program"], "run": stop["run"]}));
        }
        let Some(record) = lock.rows.iter().find(|row| row.id == id) else {
            continue;
        };
        let status = record.status.as_deref().unwrap_or_default();
        let keepable = matches!(status, "hit" | "open" | "undecided")
            && (status == "hit")
                == record
                    .witness
                    .as_deref()
                    .is_some_and(|witness| programs.contains(&witness));
        if !keepable || (obligation["status"] == "hit" && status != "hit") {
            continue;
        }
        let before = json!({"status": record.status, "witness": record.witness});
        let now = json!({"status": obligation["status"], "witness": obligation["witness"]});
        if now != before {
            kept.kept
                .push(json!({"pattern": id, "recorded": before, "now": now}));
        }
        obligation["status"] = json!(record.status);
        obligation["witness"] = json!(record.witness);
    }
    kept
}

/// One line per run the clock stopped that a query's lock entry depends on, and per entry the
/// lock kept unverified ([`keep`]), as `kink-flow` prints them on stderr.
#[must_use]
pub fn clock_lines(document: &Value) -> Vec<String> {
    let lock = &document["lock"];
    let path = lock["path"].as_str().unwrap_or(crate::lock::LOCK_FILE);
    let text = |value: &Value| value.as_str().unwrap_or("?").to_owned();
    let mut lines = Vec::new();
    for stop in lock["clock_stopped"].as_array().into_iter().flatten() {
        let run = if stop["run"] == "baseline" {
            "baseline run"
        } else {
            "search"
        };
        lines.push(format!(
            "{path}: {}: the clock (budget.time_ms) stopped the {run} of {}: its entry is not \
             decided on this host",
            text(&stop["pattern"]),
            text(&stop["program"])
        ));
    }
    let side = |value: &Value| match value["witness"].as_str() {
        Some(witness) => format!("{} (witness {witness})", text(&value["status"])),
        None => text(&value["status"]),
    };
    for entry in lock["kept"].as_array().into_iter().flatten() {
        lines.push(format!(
            "{path}: {}: kept {} unverified: this host gives {}",
            text(&entry["pattern"]),
            side(&entry["recorded"]),
            side(&entry["now"])
        ));
    }
    lines
}

struct Context<'a> {
    manifest: &'a FlowManifest,
    update: &'a ResultsUpdate,
    cache: &'a Path,
    store: &'a Store,
    /// kink's build when the cache is on.
    build: Option<Sha256Digest>,
    /// The execution digest, which keys the answers.
    execution: ExecutionDigest,
    verify: bool,
    /// The definition exclusions of the searcher's load.
    exclusions: &'a kink_native::exclusion::DefinitionExclusions,
    /// How every (pattern, program) of the command is asked.
    route: Route,
    /// The printer of a hit's witness ([`rendered`]).
    reader: &'a EndReader,
}

/// One (pattern, program) row and whether it found no error.
#[allow(clippy::too_many_arguments)]
fn ask(
    context: &Context<'_>,
    inputs: &mut crate::admit::InputSession<'_>,
    spec: &crate::admit::AdmittedSpec,
    searcher: &mut Searcher,
    index: usize,
    pattern_id: &str,
    lowered: &LoweredPattern,
    row: Map<String, Value>,
    claimed: bool,
    mismatches: &mut Vec<Value>,
    accounting: &mut Value,
) -> (Value, bool) {
    let program = &context.manifest.programs[index];
    let result: &ProgramRow = &context.update.rows[index];
    let (Some(digest), Some(case)) = (result.digest, result.inputs.as_ref()) else {
        let answer = Answer::error(format!(
            "the program is not admitted: {}",
            result.row["cause"]
                .as_str()
                .unwrap_or("its inputs cannot be read")
        ));
        return (
            unstopped(finish_row(row, &answer, false, None, claimed)),
            false,
        );
    };
    let test = match &result.test {
        Some(test) => test.clone(),
        None => match inputs.test_case(program, case) {
            Ok(test) => test,
            Err(refusal) => {
                let answer = Answer::error(format!(
                    "the program is not admitted: {}/{}: {}",
                    refusal.stage, refusal.reason, refusal.detail
                ));
                return (
                    unstopped(finish_row(row, &answer, false, None, claimed)),
                    false,
                );
            }
        },
    };
    let state = searcher.state_exclusion(&test.initial_state);
    // The stored result record decides which stored no may be used (as a command without
    // --verify would); the answer is judged with this command's own baseline run, which under
    // --verify is the live run, not a stored record it may differ from.
    let baseline_run = result
        .record
        .as_ref()
        .and_then(|record| record["run_sha256"].as_str())
        .map(str::to_owned);
    let baseline = result.live.as_ref().or(result.record.as_ref());
    let mut facts = Facts {
        exclusions: context.exclusions,
        state,
        baseline_class: baseline.and_then(|record| record["class"].as_str()),
        baseline_cause: baseline.map_or_else(
            || result.row["cause"].as_str(),
            |record| record["cause"].as_str(),
        ),
        profile: SolverProfile::BUILD,
        no_data: crate::pattern::no_data(&spec.data),
        route: context.route,
    };
    let stop = match context.route {
        Route::Search => None,
        Route::StoppedRun => context.manifest.program_stop(program),
    };
    let keyed = context.build.map(|build| {
        (
            answer_key(
                build,
                context.execution,
                digest,
                lowered.digest,
                context.manifest.budget,
                stop,
            ),
            answer_path(
                context.cache,
                context.execution.digest,
                lowered.digest,
                digest,
            ),
        )
    });
    let stored = keyed
        .as_ref()
        .and_then(|(key, path)| read_record(path, key))
        .filter(|stored| {
            stored.answer == "hit"
                || (result.class() == Some("comparable")
                    && stored.baseline_run_sha256.as_str() == baseline_run.as_deref())
        });
    if !context.verify
        && let Some(stored) = &stored
    {
        let answer = judge(&stored.outcome(), &facts);
        accounting["from_cache"] = json!(accounting["from_cache"].as_u64().unwrap_or(0) + 1);
        return (
            unstopped(rendered(
                finish_row(row, &answer, true, None, claimed),
                lowered,
                context.reader,
            )),
            true,
        );
    }
    let (outcome, wall_ms) = match context.route {
        Route::Search => searcher.search(&test.initial_state, lowered),
        Route::StoppedRun => {
            let (outcome, state, wall_ms) = searcher.run_stopped(
                context.manifest.campaign_stop(),
                &test.id,
                &test.initial_state,
                lowered,
                context.exclusions,
            );
            // The initial state's exclusion read with the run's lists (its short-circuit
            // readings), as the baseline runner reads it.
            facts.state = state;
            (outcome, wall_ms)
        }
    };
    let answer = judge(&outcome, &facts);
    let mut ok = answer.answer != "error";
    // Which run the clock stopped that this answer rests on, as the search and the baseline
    // runner state it: the search itself, when the clock stopped it and its cause is the answer's
    // (no exclusion of the load overrides it; it could have hit, or completed, on a faster host),
    // or the baseline run, when the exploration completed with no match and the baseline's class
    // is the one premise of a `no` that failed (a faster host could have given the `no`).
    let clock = if answer.answer != "unknown" {
        None
    } else if matches!(&outcome, SearchOutcome::ClockStopped(cause) if answer.cause.as_ref() == Some(cause))
    {
        Some("search")
    } else if matches!(outcome, SearchOutcome::Complete { .. })
        && result.clock_stopped
        && judge(
            &outcome,
            &Facts {
                baseline_class: Some("comparable"),
                ..facts.clone()
            },
        )
        .answer
            == "no"
    {
        Some("baseline")
    } else {
        None
    };
    let mut row = rendered(
        finish_row(row, &answer, false, Some(wall_ms), claimed),
        lowered,
        context.reader,
    );
    row["clock_stopped"] = json!(clock);
    if context.verify {
        if let (Some(stored), Some((_, path))) = (&stored, &keyed)
            && (stored.answer != answer.answer
                || (stored.answer == "hit"
                    && !same_witness(answer.witness.as_ref(), &stored.witness)))
        {
            let relative = path
                .strip_prefix(context.cache)
                .unwrap_or(path)
                .to_string_lossy()
                .into_owned();
            mismatches.push(json!({
                "pattern": pattern_id,
                "program": program.id,
                "record": relative,
                "cached": {"answer": stored.answer, "witness": stored.witness},
                "live": {"answer": answer.answer, "cause": answer.cause, "witness": answer.witness},
            }));
            row["verify"] = json!("mismatch");
        } else if stored.is_some() {
            row["verify"] = json!("match");
        }
        return (row, ok);
    }
    if let Some((key, path)) = &keyed
        && matches!(answer.answer, "hit" | "no")
    {
        let witness = answer.witness.clone().unwrap_or(Value::Null);
        let baseline = if answer.answer == "no" {
            json!(baseline_run)
        } else {
            Value::Null
        };
        let record = json!({
            "schema": RECORD_SCHEMA,
            "key": key,
            "pattern_id": pattern_id,
            "program_id": program.id,
            "answer": answer.answer,
            "witness": witness,
            "baseline_run_sha256": baseline,
            "record_sha256": record_sha256(key, answer.answer, &witness, &baseline).to_string(),
        });
        match context.store.write_json(path, &record) {
            Ok(()) => {
                accounting["records_written"] =
                    json!(accounting["records_written"].as_u64().unwrap_or(0) + 1);
            }
            Err(e) => {
                row["cache_error"] = json!(format!("cannot write the answer's record: {e}"));
                ok = false;
            }
        }
    }
    (row, ok)
}

/// `row` with its witness, a hit's facts, printed for the reader
/// ([`crate::pattern::rendered_witness`]); the answer's own witness keeps the facts, which the
/// record stores and `--verify` compares.
fn rendered(mut row: Value, lowered: &LoweredPattern, reader: &EndReader) -> Value {
    if row["witness"].is_object() {
        row["witness"] = crate::pattern::rendered_witness(&row["witness"], lowered, reader);
    }
    row
}

/// `row` with `clock_stopped` null: an answer no run the clock stopped decided (a cached one, a
/// program that is not admitted).
fn unstopped(mut row: Value) -> Value {
    row["clock_stopped"] = Value::Null;
    row
}

/// Whether a live hit's witness (`live`) and a stored one agree on what is a fact of the answer,
/// both as facts (`crate::pattern::rendered_witness` prints a document's, and is compared never):
/// the matching state's depth and whole state, and the bindings and the rules wherever both sides
/// carry them as arrays. Bindings one side could not produce (`{absent: reason}`, a stopped
/// route's) and the rules the stopped route never reports (null) are left out, so `--verify`
/// reports a difference only where two answers differ.
fn same_witness(live: Option<&Value>, stored: &Value) -> bool {
    let Some(live) = live else {
        return false;
    };
    live["depth"] == stored["depth"]
        && live["state"] == stored["state"]
        && ["bindings", "rules"]
            .iter()
            .all(|key| match (&live[*key], &stored[*key]) {
                (Value::Array(live), Value::Array(stored)) => live == stored,
                _ => true,
            })
}

/// A row with its answer: `{pattern, program, claimed, route, answer, cause, witness, cached,
/// wall_ms, claim}`. `claim` is null for a program the corpus form asked, else `confirmed` (hit),
/// `refuted` (no: the run reaches no state matching the pattern) or `unconfirmed`.
fn finish_row(
    mut row: Map<String, Value>,
    answer: &Answer,
    cached: bool,
    wall_ms: Option<u64>,
    claimed: bool,
) -> Value {
    row.insert("answer".into(), json!(answer.answer));
    row.insert("cause".into(), json!(answer.cause));
    row.insert(
        "witness".into(),
        answer.witness.clone().unwrap_or(Value::Null),
    );
    row.insert("cached".into(), json!(cached));
    row.insert("wall_ms".into(), json!(wall_ms));
    row.insert(
        "claim".into(),
        if claimed {
            json!(match answer.answer {
                "hit" => "confirmed",
                "no" => "refuted",
                _ => "unconfirmed",
            })
        } else {
            Value::Null
        },
    );
    Value::Object(row)
}

#[allow(clippy::too_many_arguments)]
fn document(
    record: &AdmissionRecord,
    digest: Option<Sha256Digest>,
    programs: Vec<Value>,
    patterns: Vec<Value>,
    rows: Vec<Value>,
    mismatches: Vec<Value>,
    pattern_cache: Value,
    baseline_runs: Value,
) -> Value {
    let refusal = record.refusal.as_ref();
    let counts = ANSWERS
        .iter()
        .map(|answer| {
            (
                (*answer).to_owned(),
                json!(rows.iter().filter(|row| row["answer"] == *answer).count()),
            )
        })
        .collect::<Map<_, _>>();
    let refuted = rows
        .iter()
        .filter(|row| row["claim"] == "refuted")
        .map(|row| json!({"pattern": row["pattern"], "program": row["program"]}))
        .collect::<Vec<_>>();
    crate::with_z3_build(json!({
        "schema": QUERY_SCHEMA,
        "version": QUERY_VERSION,
        "k_rust_revision": crate::k_rust_revision(),
        "profile": SolverProfile::BUILD.name(),
        "kink_build": kink_campaign::kink_build().map_or(Value::Null, |b| json!(b.to_string())),
        "kink": kink_campaign::kink_identity(),
        "spec": {
            "outcome": if refusal.is_some() { "refused" } else { "admitted" },
            "stage": refusal.map(|r| &r.stage),
            "reason": refusal.map(|r| &r.reason),
            "detail": refusal.map(|r| &r.detail),
            "digest": digest.map(|d| d.to_string()),
            "execution_digest": null,
            "files": record
                .files
                .iter()
                .map(|f| json!({"name": f.name, "sha256": f.sha256.to_string()}))
                .collect::<Vec<_>>(),
        },
        "programs": programs,
        "patterns": patterns,
        "rows": rows,
        "counts": counts,
        "refuted_claims": refuted,
        "mismatches": mismatches,
        "pattern_cache": pattern_cache,
        "baseline_runs": baseline_runs,
    }))
}

fn refused_document(record: &AdmissionRecord) -> Value {
    document(
        record,
        None,
        Vec::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        Value::Null,
        Value::Null,
    )
}

/// The query document of a pattern list that does not decode (or names a program the manifest
/// does not have).
pub fn pattern_list_refused(error: &ManifestError) -> Value {
    crate::with_z3_build(json!({
        "schema": QUERY_SCHEMA,
        "version": QUERY_VERSION,
        "k_rust_revision": crate::k_rust_revision(),
        "profile": SolverProfile::BUILD.name(),
        "pattern_list": {"outcome": "refused", "detail": error.to_string()},
    }))
}

#[cfg(test)]
// Under Z3 the one test here compiles out, since its subject is a cached `no`, and its helpers
// with it.
#[cfg_attr(feature = "z3", allow(dead_code, unused_imports))]
mod tests {
    //! A cached answer is judged again with the current command's facts (F-18 fix 1): the load
    //! facts a test cannot provoke are set through [`query_with`].
    use super::*;
    use kink_native::exclusion::{DefinitionExclusions, HookReference};

    fn calc() -> (FlowManifest, PatternList) {
        let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/flow/calc");
        (
            FlowManifest::read(&dir.join("FLOW.toml")).unwrap(),
            PatternList::read(&dir.join("PATTERNS.toml")).unwrap(),
        )
    }

    /// `query_with` on calc with the cache `cache`, on a thread with the command's stack.
    fn run(
        cache: &Path,
        adjust: impl Fn(&mut DefinitionExclusions) + Send + 'static,
    ) -> (Value, bool) {
        let cache = cache.to_path_buf();
        std::thread::Builder::new()
            .stack_size(kink_corpus::cli::DEFINITION_STACK_BYTES)
            .spawn(move || {
                let (manifest, list) = calc();
                let options = QueryOptions {
                    cache: Some(cache),
                    ..QueryOptions::default()
                };
                query_with(&manifest, &list, &options, "kink-flow query", &adjust)
            })
            .unwrap()
            .join()
            .unwrap()
    }

    fn row<'a>(document: &'a Value, pattern: &str, program: &str) -> &'a Value {
        document["rows"]
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["pattern"] == pattern && row["program"] == program)
            .unwrap_or_else(|| panic!("no row ({pattern}, {program}) in {document:#}"))
    }

    /// The witness fixture's manifest: programs A, B and C, in that order.
    fn witness_manifest() -> FlowManifest {
        let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/flow/witness");
        FlowManifest::read(&dir.join("FLOW.toml")).unwrap()
    }

    /// A row of `program` answering `answer`, which the clock stopped (`clock`) or not.
    fn answered(index: usize, program: &str, answer: &str, clock: Option<&str>) -> (usize, Value) {
        (
            index,
            json!({"pattern": "p", "program": program, "answer": answer, "clock_stopped": clock}),
        )
    }

    fn entry(expect: Option<PatternExpect>) -> PatternEntry {
        PatternEntry {
            id: "p".into(),
            form: PatternForm::Single("<k> 7 </k>".into()),
            programs: None,
            expect,
            note: None,
        }
    }

    /// An admitted query document whose one obligation is `obligation`.
    fn obliged(obligation: Value) -> Value {
        json!({
            "schema": QUERY_SCHEMA,
            "profile": "no-z3",
            "spec": {"outcome": "admitted"},
            "programs": [{"id": "A"}, {"id": "B"}, {"id": "C"}],
            "obligations": [obligation],
        })
    }

    /// FB54-WITNESS: the witness is the recorded one while it hits, else the first hitter in
    /// corpus order, whatever was asked first; a recorded witness the clock stopped is
    /// `clock-stopped`, and the lock keeps it unverified (`undecided` under `--locked`, exit 3)
    /// rather than moving it to the program that hit on this host. A program that answered no
    /// final `no` makes a pattern without a hit `undecided`, and its `expect = "no"`
    /// inconclusive.
    #[test]
    fn the_witness_rule_and_the_clock() {
        let manifest = witness_manifest();
        // The recorded witness C hits: it stays, though B, earlier in corpus order, hits too.
        let rows = [
            answered(2, "C", "hit", None),
            answered(0, "A", "no", None),
            answered(1, "B", "hit", None),
        ];
        let kept = obligation(&manifest, &entry(None), Some("C"), &rows, true);
        assert_eq!(kept["witness"], "C");
        assert!(kept["witness_change"].is_null());
        assert_eq!(kept["hitters"], json!(["B", "C"]));
        assert_eq!(kept["clock_stopped"], json!([]));
        // Without a record the first hitter in corpus order is the witness.
        let first = obligation(&manifest, &entry(None), None, &rows, false);
        assert_eq!(
            (&first["witness"], &first["witness_change"]),
            (&json!("B"), &json!("no-record"))
        );
        // The recorded witness's search was stopped by the clock: C hits on this host, but the
        // entry depends on B's run.
        let rows = [
            answered(1, "B", "unknown", Some("search")),
            answered(0, "A", "no", None),
            answered(2, "C", "hit", None),
        ];
        let stopped = obligation(&manifest, &entry(None), Some("B"), &rows, false);
        assert_eq!(stopped["status"], "hit");
        assert_eq!(stopped["witness"], "C");
        assert_eq!(stopped["witness_change"], "clock-stopped");
        assert_eq!(
            stopped["clock_stopped"],
            json!([{"program": "B", "run": "search"}])
        );
        let document = obliged(stopped);
        let text = "schema = \"kink-flow-verdicts\"\n\n[query]\nversion = 27\n\
                    profile = \"no-z3\"\n\n[[query.pattern]]\nid = \"p\"\nstatus = \"hit\"\n\
                    witness = \"B\"\n";
        let dir = std::env::temp_dir().join(format!("kink-flow-query-keep-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        let path = dir.join("kink.lock");
        fs::write(&path, text).unwrap();
        let lock = Lock::read_kind(&path, LockKind::Query).unwrap();
        let kept = keep(&lock, &document);
        assert_eq!(kept.document["obligations"][0]["witness"], "B");
        assert_eq!(
            kept.kept,
            vec![
                json!({"pattern": "p", "recorded": {"status": "hit", "witness": "B"},
                        "now": {"status": "hit", "witness": "C"}})
            ]
        );
        let store = Store::new(&dir);
        let settle = Settle {
            locked: true,
            verify: false,
            only: &[],
            stopped: false,
        };
        let (value, _) = lock.settle(&store, &document, settle);
        // The record's header and comments differ from the rendering, so it is stale; a record
        // the query wrote is undecided.
        assert_eq!(value["status"], "stale", "{value:#}");
        let write = Settle {
            locked: false,
            ..settle
        };
        let (written, _) = lock.settle(&store, &document, write);
        assert_eq!(written["status"], "written", "{written:#}");
        let lock = Lock::read_kind(&path, LockKind::Query).unwrap();
        assert_eq!(lock.witnesses()["p"], "B");
        assert!(lock.killers().is_empty());
        let (value, _) = lock.settle(&store, &document, settle);
        assert_eq!(value["status"], "undecided", "{value:#}");
        assert_eq!(
            crate::cli::query_status(&json!({"lock": value})),
            crate::cli::EXIT_UNANSWERED
        );
        assert_eq!(
            clock_lines(&json!({"lock": value})),
            vec![
                format!(
                    "{}: p: the clock (budget.time_ms) stopped the search of B: its entry is not \
                     decided on this host",
                    path.display()
                ),
                format!(
                    "{}: p: kept hit (witness B) unverified: this host gives hit (witness C)",
                    path.display()
                ),
            ]
        );
        // A recorded witness gone from the corpus is not kept, whatever the clock stopped.
        let mut gone = document.clone();
        gone["programs"] = json!([{"id": "A"}, {"id": "C"}]);
        fs::write(&path, text).unwrap();
        let lock = Lock::read_kind(&path, LockKind::Query).unwrap();
        assert_eq!(
            keep(&lock, &gone).document["obligations"][0]["witness"],
            "C"
        );
        // A pattern no program hits, one of whose answers is no final no, is undecided.
        let rows = [
            answered(0, "A", "no", None),
            answered(1, "B", "unknown", None),
            answered(2, "C", "no", None),
        ];
        let undecided = obligation(
            &manifest,
            &entry(Some(PatternExpect::No)),
            None,
            &rows,
            false,
        );
        assert_eq!(undecided["status"], "undecided");
        assert_eq!(undecided["unanswered"], json!(["B"]));
        assert_eq!(undecided["expectation"]["verdict"], "inconclusive");
        assert_eq!(undecided["clock_stopped"], json!([]));
        let _ = fs::remove_dir_all(&dir);
    }

    mod kink_tier {
        use super::*;

        // In both profiles: calc's searches ask no solver query, so under Z3 too each completed
        // one counts no undecided answer and its answer is a `no`.
        #[test]
        #[ignore = "kink"]
        fn a_cached_answer_is_judged_with_the_current_facts() {
            let cache = std::env::temp_dir()
                .join(format!("kink-flow-query-rejudge-{}", std::process::id()));
            let _ = fs::remove_dir_all(&cache);
            let (first, ok) = run(&cache, |_| {});
            assert!(ok, "{first:#}");
            assert_eq!(row(&first, "result-three", "add")["answer"], "hit");
            assert_eq!(row(&first, "result-four", "add")["answer"], "no");
            assert_eq!(row(&first, "result-four", "add")["cached"], false);

            // The same facts: both answers come from the cache.
            let (second, _) = run(&cache, |_| {});
            for (pattern, answer) in [("result-three", "hit"), ("result-four", "no")] {
                let row = row(&second, pattern, "add");
                assert_eq!(row["answer"], answer, "{row:#}");
                assert_eq!(row["cached"], true, "{row:#}");
            }

            // This command's load counts a stack stop: neither cached answer stands.
            let (stopped, _) = run(&cache, |exclusions| exclusions.load_stack_stops = 1);
            for pattern in ["result-three", "result-four"] {
                let row = row(&stopped, pattern, "add");
                assert_eq!(row["cached"], true, "{row:#}");
                assert_eq!(row["answer"], "unknown", "{row:#}");
                assert!(
                    row["cause"].as_str().unwrap().contains("load-stack-stop"),
                    "{row:#}"
                );
            }

            // This command's census flags a hook: the cached no is unknown, the cached hit stands.
            let (census, _) = run(&cache, |exclusions| {
                exclusions.implementation_chosen.push(HookReference {
                    module: "M".into(),
                    sentence: "r".into(),
                    symbol: "Lblkeys'Unds'list".into(),
                    hook: "MAP.keys_list".into(),
                });
            });
            let no = row(&census, "result-four", "add");
            assert_eq!(
                (no["cached"].clone(), no["answer"].clone()),
                (json!(true), json!("unknown"))
            );
            assert!(
                no["cause"]
                    .as_str()
                    .unwrap()
                    .contains("implementation-chosen-hook"),
                "{no:#}"
            );
            let hit = row(&census, "result-three", "add");
            assert_eq!(
                (hit["cached"].clone(), hit["answer"].clone()),
                (json!(true), json!("hit"))
            );
            let _ = fs::remove_dir_all(&cache);
        }
    }
}
