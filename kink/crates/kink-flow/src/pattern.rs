//! Per-input pattern checks (flow F-18): does some run of a corpus program, from its input, reach
//! a state that matches a pattern written in K? The LLM proposes a pattern it thinks a test should
//! hit and writes a program meant to hit it; kink validates the claim (an anti-hallucination check)
//! and caches the answer ([`crate::query`]). The initial state, every reached state and the final
//! states all count. "Every path hits" is not asked.
//!
//! **`PATTERNS.toml`** ([`PatternList`]): `[[pattern]]` entries with a unique non-empty `id`, a
//! `pattern` and optional `programs` (the corpus programs the author claims hit it: the per-input
//! claims), `expect` (`"no"`: the author claims no program hits it) and `note`. Every pattern is
//! also an obligation of the corpus, "some program's run reaches a state matching it", which
//! `query` discharges by a witness ([`crate::query`]). Decoding is strict, as for `FLOW.toml` and
//! `MUTATIONS.toml`: an unknown key, a value of the wrong type, a duplicate or empty id or program
//! id, `expect` beside `programs`, and a claimed program the manifest does not have are errors
//! naming the key.
//!
//! **Chains** ([`chain`]): a `[[pattern]]` may write `steps = [{ pattern = "...", unless =
//! "..." }, ...]` in place of `pattern`: some path of the run passes states matching each step in
//! order, under one assignment of the variables the steps share, with no state matching a step's
//! `unless` between it and the step before. Each step and each `unless` is lowered as a single
//! pattern is, and the variables the parts share are checked ([`Lowering::lower_chain`]). A
//! `steps` of one step without `unless` is that step's `pattern`. `query` does not evaluate a
//! chain yet: a list holding one among the selected patterns is refused.
//!
//! **Lowering** ([`Lowering`]). A pattern is K text, parsed by the specification's own grammar: it
//! is compiled by k-rust's public `kompile::compile_search_pattern` (the compiler `krun --pattern`
//! uses), which parses the text as the content of a rule (`#RuleContent`) in the main module's
//! rule grammar of the admitted definition and lowers it with the passes a rule's left-hand side
//! goes through (anonymous variables, semantic casts, cell completion, macro expansion, sort
//! injection as a left-hand side) against the execution definition of the specification's own
//! compile (`CompiledKoreArtifacts::execution_definition`, which k-rust documents as the context a
//! standalone surface pattern must use). The KORE target is `\and(body, P...)`, with one predicate
//! `P` for each conjunct `C` of a `requires`, or `\and(body, \top)`: a `requires` is supported.
//! k-rust emits each `P` as it emits a rule's condition (`module_to_kore::predicate_at`): for a
//! plain Bool conjunct, which is every pattern kink has met, `P` is `\equals(C, true)`; since
//! k-rust MLP/9 (head 8c34a8ab6, merge 7b516dfd0) a conjunct with matching-logic connectives on
//! its spine (`#Equals`, `#Or`, `#Not`, `#Implies`, `#Ceil`, a quantifier) compiles too, its
//! connectives as predicate connectives and each Bool term below them as `\equals(_, true)`.
//! As for a rule's condition, k-rust instantiates it with the definedness of its atoms, so a
//! `requires` undefined at a state does not hold there: that state does not match, which can give
//! a final `no` (a refuted claim); one whose definedness k-rust cannot decide is undecided
//! (`unknown`).
//! k-rust refuses an `ensures` and a variable that occurs only on a rewrite's right side (a pattern
//! denotes the configurations its left side matches). The compiled target must then pass the
//! backend's verified admission of a standalone pattern (`verify_standalone_pattern`), as `krun`
//! requires, so a pattern naming a symbol the baseline's compiled definition lacks is refused.
//! Any refusal is `invalid-pattern` with k-rust's message, and the pattern never runs. No overlay
//! module is loaded and the definition is not compiled again: the compile of the admission is the
//! one every program runs on.
//!
//! **Evaluation** ([`Searcher`]): one k-rust `search_pattern_kore` per (pattern, program) on the
//! baseline, from the program's admitted initial state: search type all (`=>*`, every reachable
//! configuration, the initial one included), state set, `max_results` 1 (the search stops at the
//! first match), the manifest's `max_depth` and simplifier iterations, under kink's watchdog of
//! `budget.time_ms`. A search has no work budget at k-rust 0068938b1 (KINK-24, drafted), so the
//! clock is its only bound on a runaway program.
//!
//! **The stopped route** ([`Route::StoppedRun`], [`Searcher::run_stopped`]): on a corpus with
//! `[stop]` the case's system is the truncated one, whose every path ends at its last stop event
//! or at its own end, so a search of the definition's own reachable states would ask about states
//! no case has. Each (pattern, program) is then the program's run as every campaign of the
//! command makes it (kink-campaign `Stop::execute_result_matching`: the stop's rules, the
//! program's count and the stop's condition in one execute request, all paths, state set, the
//! manifest's `max_depth`, `baseline_max_work` and `time_ms`), matching every state it reaches
//! (k-rust `match_states`) with proof agreement, so a state is refuted only where both
//! evaluation modes refute it (a refutation in execution mode alone may rest on a value the
//! definition leaves open that nothing records; for a pattern that evaluates nothing agreement
//! costs a second match and changes no verdict); kink-campaign `judge_matches` answers it, and [`judge`] then applies
//! the premises both routes share (the load's facts, data, the initial state, the baseline
//! class). A hit's witness is the reached state and its depth, the bindings of an unconditional
//! match of the pattern against that state (a search of depth 0 from it, bounded work under no
//! clock), or `{absent: reason}`, and `rules` null: the run reports no path to the state.
//!
//! **A witness** is kept as facts, `{depth, state, bindings, rules}`, the state and every
//! binding's variable and value as whole KORE text: what the cache record stores and `--verify`
//! compares. A document prints it for a reader when it is written ([`rendered_witness`]): the
//! state listed by its cells, those the pattern names printed in full as K text and every other
//! shortened by its structure, and each binding printed likewise (`crate::evidence`, "A query
//! witness"), so a cached hit is printed as a live one is, and how a witness is printed is in no
//! key.
//!
//! **Answers** ([`judge`]):
//! - `hit`: the search returned a decided match: no condition (`constraints` empty), no diagnostic
//!   of the match or of the matching state's path, a state that carries no predicate, a state whose
//!   term is defined (below), no hook application the search left unevaluated (below), and the
//!   watchdog did not fire. A hit is sound even when the run read a value the definition leaves
//!   open (an implementation-chosen hook, an operand a short-circuiting backend may skip, an
//!   initial state flagged for either): k-rust's choice is one model of the definition, and the
//!   claim is existential. For the short-circuit reading this is K's own latitude: `domains.md`
//!   says `andBool` and `orBool` "may be short-circuited in concrete backends" and that `#if` "does
//!   not short-circuit on symbolic backends", so k-rust's strict reading (a condition with an
//!   undefined operand is undefined, and the rule does not apply) is one reading K allows. The
//!   consequence: a hit may be on a state that only the strict reading reaches (for example an
//!   `owise` rule that fired because another rule's condition was undefined), which a
//!   short-circuiting backend might not reach.
//!
//!   **A defined state.** A reached state that holds an irreducible application of a function not
//!   declared total (a user function with no equation for its argument: `f(3)` where `f` has an
//!   equation for `f(0)` only) denotes no configuration wherever that application is undefined.
//!   k-rust's search match states each fact of the state's definedness it leaves undecided in its
//!   condition (k-rust-backend `search.rs`, `SearchMatch::constraints`; `docs/compatibility.md`,
//!   "Search results"), so the match on such a state carries `\ceil(f(3))` and is not decided
//!   (above). kink does not rest the hit on that condition alone: it also runs its own check of
//!   the state, below, which refuses at least what the empty condition refuses on the states a
//!   hit can have (ground, no predicate). (A hooked partial
//!   operation k-rust evaluates is not such a case: k-rust evaluates `7 /Int 0` or a lookup of a
//!   missing map key to bottom, so the step to it has no successor, the state is never reached,
//!   and the answer is a correct `no`.) So a hit also needs the matched state's term, and with it
//!   every binding, to be defined: the state is internalized on the searcher's definition and
//!   must be shown to exist by k-rust's one existence predicate
//!   (`BackendDefinition::ground_defined`, fz26 KRUST-ANYWHERE-HEAD: ground, and its definedness
//!   walk owes nothing; every application's symbol is a constructor, a function the definition
//!   declares total, or a `value-production` symbol, such as SIMPLE's `_[_]`, whose application
//!   no equation of its head can reach, which that declaration makes a value of its sort, or a
//!   partial application k-rust shows defined: by an unconditional ceil equation whose condition
//!   simplifies to `\top`, or by its source-checked observation catalog (a compiler sort
//!   projection on its exact image, a field of a one-constructor sort; since k-rust 68e362935 and
//!   fdb3ac1a5, re-read at kink27 R1-TRUST); a hooked map lookup or list access it leaves
//!   unevaluated owes its key membership or length bound, which is never discharged here; every
//!   collection a map or set whose keys k-rust shows apart, or a list, over such subterms; it
//!   accepts every state the stored `ceil_free` attribute, read before, accepts) and hold no
//!   term-level `\and` anywhere (the walk owes nothing for `\and(a, a)`, but kink refuses every
//!   conjunction; no K rule writes one on a right-hand side, so this refuses no state known to be
//!   reached). A state that is not, or whose definedness kink cannot read (it does not
//!   verify or internalize on that definition, k-rust provides no stack for it, or k-rust
//!   panics), makes the answer `unknown` (`undefined-state`).
//!
//!   **An unevaluated hook** (KINK-R4, KINK-HOOKED-VP-QUERY-HIT). `ground_defined` counts an
//!   irreducible `value-production` application as a value from its declaration alone, also when
//!   its symbol is hooked and k-rust left it unevaluated (a hook k-rust does not evaluate, or a
//!   `Bytes` result its memory allowance refused). Where such a hook is undefined at its
//!   arguments, the state denotes no configuration and the step to it has no successor, which
//!   k-rust did not compute; no path diagnostic records it. So a match is a hit only when the
//!   search response's `unsupportedHooks` and `allowanceRefusals` lists are empty; otherwise the
//!   answer is `unknown` (`unsupported-hook`). The lists are the search's as a whole, so an entry
//!   on another branch also refuses the hit (fail-closed), and a non-empty list also makes a
//!   completed exploration incomplete (no `no`, below).
//! - `no`: the exploration completed (k-rust's `incomplete` list is empty, the watchdog did not
//!   fire, and the search left no hook application unevaluated, its `unsupportedHooks` and
//!   `allowanceRefusals` lists empty: KINK-R4 review N2, since such an application's value, or its
//!   undefinedness, decides successors k-rust did not compute; and the search read no value the
//!   definition leaves open, its `implementationChosenValues` list empty: kink27
//!   R3-CENSUS-RUNLEVEL, since k-rust's classes are judged per run rather than by the census, and a
//!   search lists every class value it took, the pattern's own matching included, so with one on
//!   the list another model of that value may reach the pattern; and, on a definition whose
//!   short-circuit analysis flags a rule, or for an initial state that applies a function or
//!   operator whose value depends on the short-circuit reading, the search's `shortCircuitReadings`
//!   list holds no entry that counts, as kink-campaign judges a run's list, kink-native
//!   `DefinitionExclusions::short_circuit_excludes` and `state_exclusion`: an empty list means that
//!   every evaluation the search used, the initial state's normalization included, gives the same
//!   value under a reading that skips the operand after a deciding one, so its states and its
//!   exploration are that reading's too, while an entry that counts is a place where another
//!   reading may reach another state; a backend that lists no readings gives no `no` there), and
//!   also the program's baseline run, kink's plain state-set run of the same initial state under
//!   the same budget (the result cache), is `comparable`: complete and free of every exclusion
//!   kink-campaign reads (a stack stop the run counted, a load stack stop, a contradicted claim, a
//!   short-circuit reading that counts on its list, an allowance refusal); the definition passes
//!   decision 1's census and kink's other definition exclusions (no implementation-chosen hook, no
//!   condition equating two terms, no load stack stop), and so does the initial state (it applies
//!   no such hook, kink-native `state_references_implementation_chosen`); and the search received
//!   no undecided solver answer (its count is zero, below). Another model of an open value could
//!   reach the pattern, so a `no` is relative to the definition only when no implementation-chosen
//!   value is in play. Under the Z3 profile a `no`'s cause names the count that licensed it.
//!
//!   **Undecided solver answers** (KINK-query-no-z3). A search's decisions take the answers of
//!   the solver k-rust's facade gives the operation, and every one of them passes through the
//!   facade's counting solver (`Backend::with_solver_on`, `smt::UndecidedCounting`), which notes
//!   each undecided answer in the innermost open operation record of the thread
//!   (`stop::with_operation_record`); [`Searcher::search`] opens one around the search and reads its
//!   `unknown_answers`. An answer is one of: a decided answer (`Sat`, `Unsat`, a validity verdict, a
//!   model), a fact about the query and the build; a failure (`Err`: a query that does not
//!   translate, a script Z3 rejects, an internal error of Z3, no solver), also a function of the
//!   query and the build; a model `Unknown` that reports an approximate translation, a fact about
//!   the query; an undecided `Unknown` (a query Z3 did not decide within
//!   `budget.smt_resource_limit` and its retries, or did not decide by its incompleteness), the
//!   one kind counted; or a stop (a cancellation, a failed prelude), which ends
//!   the search ([`outcome`]: the clock, or `error`) or the state it met (an incomplete entry), so a
//!   completed exploration has none. Every query kind goes through that solver: a rule's condition
//!   and its remainder, an equation's side condition, a definedness obligation, a state's
//!   feasibility and the pattern's match against each state, since the backend builds no solver of
//!   its own outside the caller's (the load's discharge and critical-pair check use none, and run
//!   before the search, detached from it). The record is the calling thread's, and the search runs
//!   on it (a deeper stack is a segment of the same thread). Work isolated from the run
//!   (`coverage::isolated`, a condition record or execute's state matcher) is counted by no record,
//!   and the search request asks for none of it. So a completed search whose count is zero took
//!   every decision from decided answers and failures: from facts about its queries (the
//!   definition's `smt-hook` and `smt-lemma` claims are trusted as every claim of the baseline is,
//!   and an `Unsat` is no K valuation on every definition kink answers on, since a condition
//!   equating two terms makes every answer unknown), and from failures, which k-rust reads as no
//!   refutation wherever a search takes a solver answer: only a decided `Unsat` or refutation
//!   refutes a condition, a match or a state. Without Z3 every failure is `Unavailable`; under Z3 a
//!   query can also fail with `Translation`, `SolverFault` or `MalformedScript`, which no portable
//!   run exercises, so the `no` also rests on k-rust reading those as no refutation, which
//!   `kink/trust.md` checks site by site. Such a `no` rests on nothing else the portable
//!   profile's does not, besides Z3's decided answers. The solver's caches hold decided answers
//!   only, and k-rust's memos of condition verdicts close inside the search, so a served verdict
//!   that rested on an undecided answer was counted when the search first decided it. A search
//!   that counted an undecided answer gives `unknown` with its count: its `no` would also rest on
//!   every consumer of an undecided answer reading it as no information about reachability, a
//!   premise the portable profile, whose solver never answers `Unknown`, does not exercise.
//!
//!   **A pattern holding an equation-head application** (fz26 KRUST-ANYWHERE-HEAD, review N5),
//!   such as SIMPLE's `array(_, _)[2]`, which an `anywhere` rule reduces. Neither the pattern
//!   compiler nor the search normalizes the pattern (the facade verifies and internalizes it,
//!   `prepare_backend_match_target`), and it need not: the search matches its target in k-rust's
//!   `Implies` mode, which reads an application of an equation head in the pattern as the value of
//!   its normal form, never by its root as written (k-rust-backend `matching`, `pattern_reading`).
//!   A reached state compared at such a position leaves the match undecided, so the exploration is
//!   incomplete and the answer `unknown`; a `no` rests only on refutations at positions the
//!   matcher reads as values, which hold whatever the equations make of that application.
//! - `unknown`, with its cause, in every other case: a depth bound, the clock, an undecided step
//!   or match, a matched state not shown defined, a stack-exhausted state, the census, a load
//!   stack stop, a baseline run that is not comparable, an undecided solver answer the search
//!   received.
//! - `invalid-pattern` (above) and `error` (a program that is not admitted, a search k-rust
//!   refuses).
//!
//! **Premises** (the kink-flow README, "Checking a pattern", states them for the reader). Every
//! answer rests on k-rust's search being sound and exact for "some reachable state matches" under
//! the state set (M-2: on IMP and IMP++ it found the distinct states and hits stepping finds), on
//! k-rust's parser and pattern compiler being the authority on what a pattern denotes, and on the
//! baseline's own claims being trusted, as every baseline run does. Load stack stops are read on
//! the backend every search runs on and make both answers unknown, as does a condition equating
//! two terms (`equals-condition`, a gap of k-rust's own answers). A search does not count the
//! stack stops it dismisses while it only refines a result (k-rust `docs/compatibility.md`,
//! "Execute"), so the run-level count kink requires of a comparison is not available for a search.
//! k-rust states at every site a search can reach that the kept outcome is sound: a definedness
//! condition is kept unsimplified, a fold is forgone. Such a stop can leave a condition on a state
//! or a step or a match undecided, and the answer is then `unknown` (an incomplete entry, a match
//! with a condition), but it cannot make a decided match or a completed exploration false: whether
//! an answer is definitive can depend on the host's stack, its truth cannot. For a `no` the
//! baseline run's own count is required to be zero as well, over the same states. A detected
//! contradicted claim does not end its path: since k-rust KINK-18/2 (head 16e88a6d4, merge
//! 7d4c588f9) a path whose decisions rest on one goes on (a condition refuted through it, an `owise`
//! alternative after it, a candidate it removed), and the `contradicted-claim` record is a path
//! fact on the path's states, witnesses and matches, and on the search response's
//! `contradictedClaims` list (k-rust `docs/compatibility.md`, "A contradicted `total` attribute is
//! named, not repaired"). A hit needs a match and a state path with no diagnostic, so a witness
//! whose path rests on a detected contradiction is `unknown`, never a hit. A `no` needs a
//! comparable baseline run, and a record on that run excludes it (so the program is not
//! comparable), on a leaf or, since re-pin adoption A-1, on the run's `contradictedClaims` list
//! (work that ended on no leaf, the load), as a contradicted `total` on a leaf does. kink does not
//! read the search response's list yet (re-pin adoption A-2 will), so a record of the search's own
//! work that ended on no leaf is not seen; such a contradiction rests on the baseline's claims,
//! which are a premise (above). No pattern answer ever feeds a kill or a mutation verdict: pattern-only differences
//! stay unknown by design.

use crate::{
    admit::AdmittedSpec,
    evidence::{EndReader, VALUE_CAP},
    manifest::{Budget, FlowManifest, ManifestError},
    results::{SIMPLIFICATION_ITERATIONS, execution_budget, sentence_value},
};
use k_rust::backend::ShortCircuitReadingOutput;
use k_rust::{
    backend::{
        BACKEND_SCHEMA_VERSION, Backend, BackendError, IncompleteSearchOutput,
        KorePatternSearchResponse, SearchFailureOutput, SearchMatchOutput, SearchPatternRequest,
        SearchTypeArg,
    },
    definition::{AttributeKey, Attributes, ResolvedDefinition, configuration::declared_cells},
    k_rust_backend::{
        definition::{BackendDefinition, DefinitionError},
        stop::{CancellationToken, StopCause, with_operation_record},
    },
    kompile::{CompileSearchPatternError, ProgramGrammar, compile_search_pattern},
    kore::{
        ast::{Associativity, Pattern},
        json as kore_json,
        parser::{parse_definition, parse_pattern},
    },
};
use kink_campaign::{MatchAnswer, MatchUnknown};
use kink_native::{
    coverage::{Authorship, RuleAuthors},
    exclusion::{DefinitionExclusions, Exclusion, state_references_implementation_chosen},
    execution::{
        DefinitionTables, ExecutionAdapter, HaltClass, MatchedState, ResultRun, RunFacts,
        SolverProfile, StateMatchRequest, UndecidedMatchReasonOutput,
    },
};
use kink_patch::{Sha256Digest, canonical_json, payload_digest};
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
        mpsc,
    },
    thread,
    time::{Duration, Instant},
};
use toml::{Table, Value as TomlValue};

pub mod chain;
pub use chain::{CHAIN_DOMAIN, LoweredChain, LoweredStep, LoweredUnless, StepText};

/// The lowering of a pattern's K text to its KORE target ([`Lowering`]), a component of every
/// cached answer's key: it changes whenever kink changes how a pattern's text becomes a target.
pub const LOWERING_VERSION: &str = "kink-flow/pattern-lowering/v1";
/// Domain of a pattern's digest: its KORE target and the variables the compiler generated.
pub const PATTERN_DOMAIN: &str = "kink-flow/pattern/v1";
/// The answer of a refused pattern.
pub const INVALID_PATTERN: &str = "invalid-pattern";
/// The search every check of a corpus without `[stop]` makes, as the cache key names it.
pub fn search_modality() -> Value {
    json!({"search_type": "all", "result_modality": "state-set", "max_results": 1})
}

/// The run every check of a corpus with `[stop]` makes ([`Searcher::run_stopped`]), as the cache
/// key names it: one execute request of every path, state set, matching every state it reaches.
pub fn stopped_modality() -> Value {
    json!({"route": Route::StoppedRun.name(), "search_type": "all", "result_modality": "state-set"})
}

/// How a (pattern, program) is asked (module docs): by a pattern search of the definition's own
/// reachable states (a corpus without `[stop]`), or by the program's stopped run matching every
/// state of the truncated system it reaches (a corpus with `[stop]`).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Route {
    Search,
    StoppedRun,
}

impl Route {
    /// The name a query row and a key give the route.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Search => "search",
            Self::StoppedRun => "stopped-run",
        }
    }
}

/// A decoded `PATTERNS.toml`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PatternList {
    pub patterns: Vec<PatternEntry>,
}

/// One `[[pattern]]`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PatternEntry {
    pub id: String,
    /// The pattern's K text (key `pattern`), or its chain of steps (key `steps`).
    pub form: PatternForm,
    /// The corpus programs the author claims hit the pattern (per-input claims), each asked and
    /// checked; `None` when the pattern states none. Whether or not it has claims, every pattern
    /// is an obligation of the corpus ([`crate::query`]).
    pub programs: Option<Vec<String>>,
    /// The answer the author claims the corpus gives the pattern's obligation (key `expect`),
    /// when the list states one: [`PatternExpect::No`], no program of the corpus reaches a state
    /// that matches the pattern. `query` checks it against the obligation
    /// ([`crate::query::pattern_expectation`]); it changes no answer and enters no digest, key or
    /// lock. A pattern with `expect` has no `programs`: the two claims contradict each other.
    pub expect: Option<PatternExpect>,
    /// Free text for the reader; it enters no digest.
    pub note: Option<String>,
}

impl PatternEntry {
    /// The K text of a single pattern; `None` for a chain.
    #[must_use]
    pub fn single(&self) -> Option<&str> {
        match &self.form {
            PatternForm::Single(text) => Some(text),
            PatternForm::Chain(_) => None,
        }
    }
}

/// What a `[[pattern]]` asks of a run ([`PatternEntry::form`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PatternForm {
    /// Key `pattern`, K text: a configuration fragment as a rule's left-hand side is written,
    /// cells completed by k-rust as for rules, optionally followed by `requires` and a condition.
    /// Some state of the run matches it.
    Single(String),
    /// Key `steps`, a chain of at least two steps ([`chain`]): the run passes states matching
    /// each step in order, under one assignment of the variables the steps share. A `steps` of
    /// one step without `unless` asks what its `pattern` asks, and is decoded as that pattern.
    Chain(Vec<StepText>),
}

/// The answer a pattern states it expects of the corpus ([`PatternEntry::expect`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PatternExpect {
    /// `expect = "no"`: every program of the corpus gives a final `no`, so no program's run
    /// reaches a state that matches the pattern.
    No,
}

impl PatternExpect {
    /// The value as the list and the query document write it.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::No => "no",
        }
    }

    /// The value the list writes as `text`, if it is one.
    #[must_use]
    pub fn parse(text: &str) -> Option<Self> {
        match text {
            "no" => Some(Self::No),
            _ => None,
        }
    }
}

pub(crate) fn pattern_key(id: &str) -> String {
    format!("pattern {id:?}")
}

fn join(prefix: &str, key: &str) -> String {
    if prefix.is_empty() {
        key.to_owned()
    } else {
        format!("{prefix}.{key}")
    }
}

fn known_keys(table: &Table, prefix: &str, known: &[&str]) -> Result<(), ManifestError> {
    match table.keys().find(|key| !known.contains(&key.as_str())) {
        Some(key) => Err(ManifestError::new(join(prefix, key), "unknown key")),
        None => Ok(()),
    }
}

fn non_empty(value: &TomlValue, key: &str) -> Result<String, ManifestError> {
    match value.as_str() {
        Some(text) if !text.trim().is_empty() => Ok(text.to_owned()),
        Some(_) => Err(ManifestError::new(key, "must not be empty")),
        None => Err(ManifestError::new(key, "expected a string")),
    }
}

impl PatternList {
    /// Read and decode the pattern list at `path`.
    pub fn read(path: &Path) -> Result<Self, ManifestError> {
        let text = fs::read_to_string(path)
            .map_err(|e| ManifestError::new("", format!("cannot read the pattern list: {e}")))?;
        Self::decode(&text)
    }

    /// Decode a pattern list. Unknown keys, values of the wrong type, duplicate or empty ids, an
    /// empty pattern, and an empty, duplicated or empty-named `programs` entry are errors naming
    /// the key.
    pub fn decode(text: &str) -> Result<Self, ManifestError> {
        let top: Table = toml::from_str(text)
            .map_err(|e| ManifestError::new("", format!("invalid TOML: {e}")))?;
        known_keys(&top, "", &["pattern"])?;
        let patterns = match top.get("pattern") {
            None => Vec::new(),
            Some(TomlValue::Array(entries)) => entries
                .iter()
                .enumerate()
                .map(|(index, entry)| pattern_entry(index, entry))
                .collect::<Result<Vec<_>, _>>()?,
            Some(_) => {
                return Err(ManifestError::new("pattern", "expected [[pattern]] tables"));
            }
        };
        let mut ids = BTreeSet::new();
        for entry in &patterns {
            if !ids.insert(entry.id.as_str()) {
                return Err(ManifestError::new(
                    pattern_key(&entry.id),
                    "duplicate pattern id",
                ));
            }
        }
        Ok(Self { patterns })
    }

    /// Check every claimed program against the manifest: a claim naming a program the corpus
    /// does not have is an error naming the key.
    pub fn check_programs(&self, manifest: &FlowManifest) -> Result<(), ManifestError> {
        for entry in &self.patterns {
            for (index, id) in entry.programs.iter().flatten().enumerate() {
                if !manifest.programs.iter().any(|program| &program.id == id) {
                    return Err(ManifestError::new(
                        format!("{}.programs[{index}]", pattern_key(&entry.id)),
                        format!("no program of the manifest has the id {id:?}"),
                    ));
                }
            }
        }
        Ok(())
    }
}

fn pattern_entry(index: usize, value: &TomlValue) -> Result<PatternEntry, ManifestError> {
    let position = format!("pattern[{index}]");
    let table = value
        .as_table()
        .ok_or_else(|| ManifestError::new(&position, "expected a table"))?;
    let id = non_empty(
        table
            .get("id")
            .ok_or_else(|| ManifestError::new(join(&position, "id"), "missing required key"))?,
        &join(&position, "id"),
    )?;
    let key = pattern_key(&id);
    known_keys(
        table,
        &key,
        &["id", "pattern", "steps", "programs", "expect", "note"],
    )?;
    let form = match (table.get("pattern"), table.get("steps")) {
        (Some(_), Some(_)) => {
            return Err(ManifestError::new(
                join(&key, "steps"),
                "a pattern is either one `pattern` or a chain of `steps`: keep one of the two",
            ));
        }
        (Some(pattern), None) => PatternForm::Single(non_empty(pattern, &join(&key, "pattern"))?),
        (None, Some(steps)) => chain::decode_steps(steps, &join(&key, "steps"))?,
        (None, None) => {
            return Err(ManifestError::new(
                join(&key, "pattern"),
                "missing required key (a pattern has `pattern`, or `steps` for a chain)",
            ));
        }
    };
    let note = table
        .get("note")
        .map(|value| match value.as_str() {
            Some(text) => Ok(text.to_owned()),
            None => Err(ManifestError::new(join(&key, "note"), "expected a string")),
        })
        .transpose()?;
    let programs = match table.get("programs") {
        None => None,
        Some(TomlValue::Array(ids)) => {
            if ids.is_empty() {
                return Err(ManifestError::new(
                    join(&key, "programs"),
                    "must not be empty; leave it out to ask every program",
                ));
            }
            let mut seen = BTreeSet::new();
            let ids = ids
                .iter()
                .enumerate()
                .map(|(i, id)| {
                    let item = format!("{}[{i}]", join(&key, "programs"));
                    let id = non_empty(id, &item)?;
                    if seen.insert(id.clone()) {
                        Ok(id)
                    } else {
                        Err(ManifestError::new(item, "duplicate program id"))
                    }
                })
                .collect::<Result<Vec<_>, _>>()?;
            Some(ids)
        }
        Some(_) => {
            return Err(ManifestError::new(
                join(&key, "programs"),
                "expected an array of program ids",
            ));
        }
    };
    let expect =
        match table.get("expect") {
            None => None,
            Some(value) => Some(value.as_str().and_then(PatternExpect::parse).ok_or_else(
                || {
                    ManifestError::new(
                        join(&key, "expect"),
                        "expected \"no\": the answer the corpus gives the pattern",
                    )
                },
            )?),
        };
    if expect.is_some() && programs.is_some() {
        return Err(ManifestError::new(
            join(&key, "expect"),
            "a pattern with `programs` claims those programs hit it, which contradicts `expect = \
             \"no\"`: keep one of the two",
        ));
    }
    Ok(PatternEntry {
        id,
        form,
        programs,
        expect,
        note,
    })
}

/// A pattern lowered to its KORE target.
#[derive(Clone, Debug)]
pub struct LoweredPattern {
    /// The compiled target (`\and(body, ...)`).
    pub target: Pattern,
    /// The KORE names of the variables the compiler generated (anonymous variables, cell
    /// completion): their bindings name nothing the author wrote and are not reported.
    pub generated: BTreeSet<String>,
    /// [`PATTERN_DOMAIN`] digest of the canonical KORE JSON of the target and the generated
    /// variables.
    pub digest: Sha256Digest,
    /// The KORE names of the variables the pattern's `requires` names that its configuration
    /// body does not ([`requires_only_variables`]); derived from `target`, so not digested.
    pub requires_only: BTreeSet<String>,
}

impl LoweredPattern {
    /// The target's KORE text.
    pub fn kore(&self) -> String {
        self.target.to_string()
    }

    /// The note an undecided match's cause carries when the `requires` names a variable the
    /// body does not bind, or an empty string. Such a variable is existential: the condition
    /// holds where some value of it makes it hold, so the matcher decides it only where the
    /// application holding the variable evaluates to a value, which it does not over an unknown
    /// argument (`f(W) in L`). The same term written in a cell pattern
    /// (`L1:List ListItem(f(W)) L2:List`) binds the variable by matching instead. The note is
    /// added to every cause such a condition can leave: an undecided match, and a solver query
    /// it needs that failed or is unavailable (the portable profile).
    pub fn requires_only_note(&self) -> String {
        if self.requires_only.is_empty() {
            return String::new();
        }
        let names = self
            .requires_only
            .iter()
            .map(|name| name.strip_prefix("Var").unwrap_or(name))
            .collect::<Vec<_>>()
            .join(", ");
        format!(
            "; the pattern's requires names {names}, which its cell patterns do not bind \
             (requires-only variable): such a condition is decided only when the application \
             holding the variable evaluates, so write the term that holds {names} in a cell \
             pattern instead (for an element of a list, `L1:List ListItem(E) L2:List` with E \
             holding {names}), where matching binds it"
        )
    }
}

/// The variables the `requires` of the lowered target `\and(body, P...)` names (free in some
/// `P`) that `body` does not, by KORE name, leaving out those the compiler generated.
fn requires_only_variables(target: &Pattern, generated: &BTreeSet<String>) -> BTreeSet<String> {
    let Pattern::And { arguments, .. } = target else {
        return BTreeSet::new();
    };
    let Some((body, predicates)) = arguments.split_first() else {
        return BTreeSet::new();
    };
    let bound = body
        .free_variables()
        .into_iter()
        .map(|variable| variable.name)
        .collect::<BTreeSet<_>>();
    predicates
        .iter()
        .flat_map(Pattern::free_variables)
        .map(|variable| variable.name)
        .filter(|name| !bound.contains(name) && !generated.contains(name))
        .collect()
}

/// The lowering context of one admitted specification: its rule grammar and the execution
/// definition of its compile (module docs).
pub struct Lowering {
    grammar: ProgramGrammar,
    execution: ResolvedDefinition,
    module: String,
}

impl Lowering {
    /// The lowering context of `spec`, whose main module is `main_module` (its K name).
    pub fn new(spec: &AdmittedSpec, main_module: &str) -> Result<Self, String> {
        let grammar = ProgramGrammar::new(spec.loaded.baseline.definition())
            .map_err(|e| format!("cannot resolve the specification's grammar: {e}"))?;
        let execution =
            ResolvedDefinition::resolve(&spec.compiled.artifacts().execution_definition)
                .map_err(|e| format!("cannot resolve the compiled execution definition: {e}"))?;
        Ok(Self {
            grammar,
            execution,
            module: main_module.to_owned(),
        })
    }

    /// The cells of the configuration by K name, in configuration pre-order (a cell before the
    /// cells it holds, those in argument order), the top cell and `generatedCounter` left out, then
    /// any cell no cell of the tree holds, in sentence order: the cells a refusal of a pattern
    /// names as declared ([`unknown_cells`]). A cell holds the cell whose argument sort (its cell
    /// sort, or a `*` cell's collection sort) is one of its own argument sorts.
    fn configuration_cells(&self) -> Vec<String> {
        let module = self
            .execution
            .module_id(&self.module)
            .unwrap_or_else(|| self.execution.main_module_id());
        let cells = declared_cells(&self.execution, module);
        let mut order = Vec::new();
        let mut pending = cells
            .iter()
            .filter(|cell| cell.name == GENERATED_TOP)
            .collect::<Vec<_>>();
        while let Some(cell) = pending.pop() {
            if order.contains(&cell.name) {
                continue;
            }
            order.push(cell.name.clone());
            let held = cell
                .child_kore_sorts
                .iter()
                .filter_map(|sort| cells.iter().find(|child| child.position_kore_sort == *sort))
                .collect::<Vec<_>>();
            pending.extend(held.into_iter().rev());
        }
        for cell in &cells {
            if !order.contains(&cell.name) {
                order.push(cell.name.clone());
            }
        }
        order.retain(|name| name != GENERATED_TOP && name != GENERATED_COUNTER);
        order
    }

    /// Lower `text` (module docs), checking the target against `definition`, the baseline
    /// definition every search runs on. The error is k-rust's message; a position in it is a
    /// line and column of the pattern's own text, its surrounding whitespace removed, under the
    /// source name [`PATTERN_SOURCE`], never a line of the file the pattern list came from
    /// (GUIDE-USABILITY 4).
    pub fn lower(
        &self,
        text: &str,
        definition: &BackendDefinition,
    ) -> Result<LoweredPattern, String> {
        let contents = text.trim();
        let compiled = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            compile_search_pattern(
                self.grammar.resolved(),
                &self.execution,
                &self.module,
                contents,
                pattern_attributes(contents),
            )
        }))
        .map_err(|_| "k-rust panicked while compiling the pattern".to_owned())?
        .map_err(|e| {
            let mut message = format!(
                "{e} (a position `{PATTERN_SOURCE}:LINE:COLUMN` is a line and column of the \
                 pattern's text, its surrounding whitespace removed, not of the pattern list's \
                 file)"
            );
            if matches!(e, CompileSearchPatternError::Rule(_))
                && let Some(unknown) = unknown_cells(contents, &self.configuration_cells())
            {
                message.push_str("; ");
                message.push_str(&unknown);
            }
            message
        })?;
        // The target is checked as the search admits it ([`Searcher::search`]): as a match
        // target, whose variables are existential, so a set variable matching binds (`@_`
        // compiles to one) is admitted and others are refused, by k-rust's one admission
        // (`Admitted::as_match_target`). The lowering and the search then refuse the same
        // patterns.
        definition
            .verify_standalone_pattern(&compiled.pattern, &[])
            .map_err(|e| format!("the compiled pattern is not a pattern of the baseline: {e}"))?
            .as_match_target()
            .internalize_pattern()
            .map_err(|e| format!("the compiled pattern does not internalize: {e:?}"))?;
        let generated = compiled
            .generated_anonymous_variables
            .iter()
            .map(|identity| identity.name.clone())
            .collect::<BTreeSet<_>>();
        let target_json = kore_json::to_value(&compiled.pattern)
            .map_err(|e| format!("cannot encode the compiled pattern: {e}"))?;
        let digest = payload_digest(
            PATTERN_DOMAIN,
            canonical_json(&json!({"target": target_json, "generated": generated})).as_bytes(),
        );
        let requires_only = requires_only_variables(&compiled.pattern, &generated);
        Ok(LoweredPattern {
            target: compiled.pattern,
            generated,
            digest,
            requires_only,
        })
    }
}

/// The K name of the top cell a configuration's expansion declares (k-rust `declared_cells`).
const GENERATED_TOP: &str = "generatedTop";
/// The K name of the counter cell compilation adds beside the declared ones.
const GENERATED_COUNTER: &str = "generatedCounter";

/// What a pattern that does not parse says of its cell tags (FB-53): each name written as a
/// tag `<name>` or `</name>` in `text` that is no cell of `cells` (the configuration's, by K
/// name), in the order first written, and the cells the configuration declares; `None` when every
/// tag names one. k-rust's rule grammar scans each cell's tags as one terminal, so an unknown tag
/// is refused as an unexpected character sequence, which names no cell; this names it. It reads
/// the text alone, after the parse refused it, and changes nothing about what parses.
fn unknown_cells(text: &str, cells: &[String]) -> Option<String> {
    let bytes = text.as_bytes();
    let mut unknown: Vec<&str> = Vec::new();
    for (at, _) in text.match_indices('<') {
        let start = at + 1 + usize::from(bytes.get(at + 1) == Some(&b'/'));
        let length = bytes[start..]
            .iter()
            .take_while(|byte| byte.is_ascii_alphanumeric() || **byte == b'_' || **byte == b'-')
            .count();
        let name = &text[start..start + length];
        if length > 0
            && bytes.get(start + length) == Some(&b'>')
            && !cells.iter().any(|cell| cell == name)
            && !unknown.contains(&name)
        {
            unknown.push(name);
        }
    }
    if unknown.is_empty() {
        return None;
    }
    let tags = |names: &mut dyn Iterator<Item = &str>| {
        names
            .map(|name| format!("<{name}>"))
            .collect::<Vec<_>>()
            .join(", ")
    };
    Some(format!(
        "the pattern names {}, which {} of the configuration; the configuration declares: {}",
        tags(&mut unknown.iter().copied()),
        if unknown.len() == 1 {
            "is no cell"
        } else {
            "are no cells"
        },
        tags(&mut cells.iter().map(String::as_str)),
    ))
}

/// The source name of a pattern's text in k-rust's messages: a pattern list can come from any
/// file, and the text's positions are its own, not that file's.
pub const PATTERN_SOURCE: &str = "pattern";

/// The source attributes of a pattern's text, as `krun` gives a command-line pattern.
fn pattern_attributes(contents: &str) -> Attributes {
    let (mut end_line, mut end_column) = (1_u32, 1_u32);
    for character in contents.chars() {
        if character == '\n' {
            end_line += 1;
            end_column = 1;
        } else {
            end_column += 1;
        }
    }
    let mut attributes = Attributes::default();
    attributes.set(AttributeKey::Source, json!(PATTERN_SOURCE));
    attributes.set(AttributeKey::SourceId, json!(0));
    attributes.set(AttributeKey::Location, json!([1, 1, end_line, end_column]));
    attributes.set(AttributeKey::ContentStartOffset, json!(0));
    attributes.set(AttributeKey::ContentStartLine, json!(1));
    attributes.set(AttributeKey::ContentStartColumn, json!(1));
    attributes
}

/// What one search found, before the answer rules ([`judge`]).
#[derive(Clone, Debug, PartialEq)]
pub enum SearchOutcome {
    /// A decided match: the witness's facts (`{depth, state, bindings, rules}`, the state and
    /// the bindings as whole KORE text, [`witness`]), which a document prints through
    /// [`rendered_witness`].
    Hit(Value),
    /// The exploration completed and no state matched: with the undecided solver answers the
    /// search received (its operation record's `unknown_answers`, module docs), always zero
    /// without Z3.
    Complete { smt_unknowns: usize },
    /// The search found no decided answer: the cause.
    Incomplete(String),
    /// The clock (`budget.time_ms`) stopped the search before it found a decided answer: the
    /// watchdog cancelled the search or the stopped run, or the exploration has a cancelled
    /// entry. The cause is the reader's text; this variant is the fact a lock reads: on a faster
    /// host the search could have hit or completed ([`crate::query`]).
    ClockStopped(String),
    /// k-rust refused the search: its message.
    Failed(String),
}

/// What the answer rules read besides the search ([`judge`]).
#[derive(Clone, Debug)]
pub struct Facts<'a> {
    /// The definition exclusions of the backend the search ran on.
    pub exclusions: &'a DefinitionExclusions,
    /// The exclusion of the program's initial state, if any.
    pub state: Option<Exclusion>,
    /// The program's baseline result class and cause (the result cache).
    pub baseline_class: Option<&'a str>,
    pub baseline_cause: Option<&'a str>,
    /// The build's solver profile.
    pub profile: SolverProfile,
    /// Why the definition has no data under `[spec] assume_joined` (kink-native
    /// `DataFacts::has_data` is false: its full critical-pair check has a finding no name assumes,
    /// fz26 KINK-BASELINE-FINDINGS, or did not read the whole definition), `None` when it has:
    /// while it has none, no `no` is given ([`no_data`]).
    pub no_data: Option<String>,
    /// How the outcome was found, which names what a `no`'s cause counted.
    pub route: Route,
}

/// [`Facts::no_data`] of `data`: the gate `run` and `coverage` read for an end
/// (kink-native `data_ends`), so a `no` rests on the same facts a kill does (final review K3).
pub fn no_data(data: &kink_native::data::DataFacts) -> Option<String> {
    if data.has_data() {
        return None;
    }
    let unnamed = data.heads().findings().len();
    Some(if unnamed > 0 {
        format!(
            "the definition's full critical-pair check has {unnamed} finding(s) no [spec] \
             assume_joined name assumes (baseline-findings; the document's data lists them)"
        )
    } else {
        format!(
            "the definition's full critical-pair check did not read the whole definition ({}), \
             so a pair it did not read may not join",
            data.incomplete()
                .unwrap_or_else(|| "k-rust does not show it complete".to_owned())
        )
    })
}

/// An answer: `hit`, `no`, `unknown`, `invalid-pattern` or `error`, with its cause (null for a
/// `hit`, and for a `no` without Z3; under Z3 a `no`'s cause names the count of undecided solver
/// answers that licensed it) and its witness (a hit's).
#[derive(Clone, Debug, PartialEq)]
pub struct Answer {
    pub answer: &'static str,
    pub cause: Option<String>,
    pub witness: Option<Value>,
}

impl Answer {
    pub fn unknown(cause: impl Into<String>) -> Self {
        Self {
            answer: "unknown",
            cause: Some(cause.into()),
            witness: None,
        }
    }

    pub fn error(cause: impl Into<String>) -> Self {
        Self {
            answer: "error",
            cause: Some(cause.into()),
            witness: None,
        }
    }
}

/// Why an exclusion makes an answer unknown, in the reader's words.
fn exclusion_cause(exclusion: Exclusion, what: &str) -> String {
    let why = match exclusion {
        Exclusion::LoadStackStop => {
            "the definition's load counted a stop for lack of native stack (load-stack-stop), so \
             the rewrite theory every search runs on is not a function of the definition"
        }
        Exclusion::ImplementationChosenHook => {
            "the definition references a hook whose value the definition leaves open and k-rust \
             chooses (implementation-chosen-hook, decision 1's census): another model of that \
             value could reach the pattern"
        }
        Exclusion::ShortCircuitReading => {
            "a function or operator whose value depends on whether andBool, orBool, impliesBool, \
             #if, andThenBool or orElseBool skip an operand that may be undefined is applied \
             (short-circuit-reading): another reading could reach the pattern"
        }
        Exclusion::EqualsCondition => {
            "a rule or equation has a condition equating two terms (equals-condition), a gap of \
             k-rust's answers"
        }
        Exclusion::StackStop => "the run counted a stop for lack of native stack (stack-stop)",
        Exclusion::ContradictedClaim => {
            "the run contradicts a trusted claim of the definition, on a leaf or on k-rust's \
             list of the run's contradicted claims, its definition's load included \
             (contradicted-claim)"
        }
        Exclusion::AllowanceRefusal => {
            "a Bytes hook refused a result for the memory allowance (allowance-refusal)"
        }
        Exclusion::ImplementationChosenValue => {
            "the run read a value the definition leaves open and k-rust chooses \
             (implementation-chosen-value, k-rust's list of the run's open values)"
        }
        Exclusion::UnsupportedHook => {
            "the run or its definition's load left an application unevaluated as an unsupported \
             hook (unsupported-hook)"
        }
        Exclusion::PassedStop => {
            "the run went on past a step of a stop rule that had another successor (passed-stop)"
        }
    };
    format!("{what}: {why}")
}

/// The answer rules (module docs) applied to one search's outcome.
pub fn judge(outcome: &SearchOutcome, facts: &Facts<'_>) -> Answer {
    let exclusions = facts.exclusions;
    // Exclusions that make every answer unknown: a load that is not a function of the
    // definition, and a gap of k-rust's own answers.
    if exclusions.load_stack_stops > 0 {
        return Answer::unknown(exclusion_cause(
            Exclusion::LoadStackStop,
            "no answer is given",
        ));
    }
    if !exclusions.equals_conditions.is_empty() {
        return Answer::unknown(exclusion_cause(
            Exclusion::EqualsCondition,
            "no answer is given",
        ));
    }
    match outcome {
        SearchOutcome::Hit(witness) => Answer {
            answer: "hit",
            cause: None,
            witness: Some(witness.clone()),
        },
        SearchOutcome::Failed(message) => Answer::error(message.clone()),
        SearchOutcome::Incomplete(cause) | SearchOutcome::ClockStopped(cause) => {
            Answer::unknown(cause.clone())
        }
        SearchOutcome::Complete { smt_unknowns } => {
            let would = "the exploration completed with no match, but a no is not given";
            // The short-circuit reading is judged on the search's own list ([`outcome`]).
            if let Some(exclusion) = exclusions.definition_exclusion() {
                return Answer::unknown(exclusion_cause(exclusion, would));
            }
            // fz26 KINK-BASELINE-FINDINGS: matching is syntactic, while a pair that does not join
            // can identify a reached state with an instance of the pattern in every model; a hit
            // stays a hit (k-rust reached that configuration).
            if let Some(why) = &facts.no_data {
                return Answer::unknown(format!(
                    "{would}: {why}, so the definition may identify a reached configuration with \
                     an instance of the pattern"
                ));
            }
            if let Some(exclusion) = facts.state {
                return Answer::unknown(exclusion_cause(
                    exclusion,
                    &format!("{would} (the program's initial state)"),
                ));
            }
            // KINK-query-no-z3 (module docs): a no rests on decided answers and failures only.
            if *smt_unknowns > 0 {
                return Answer::unknown(format!(
                    "{would}: the search received {smt_unknowns} undecided solver answer(s) (a \
                     query Z3 did not decide within budget.smt_resource_limit and its retries, \
                     or by its incompleteness), so a decision it took may rest on one"
                ));
            }
            match facts.baseline_class {
                Some("comparable") => Answer {
                    answer: "no",
                    // Under Z3 the count licensed the no; without Z3 no query is ever undecided.
                    cause: (facts.profile == SolverProfile::Z3).then(|| match facts.route {
                        Route::Search => "the exploration completed with no match, and the \
                                          search received 0 undecided solver answers, so no \
                                          solver query it made was left undecided"
                            .to_owned(),
                        Route::StoppedRun => "the stopped run explored the truncated system to \
                                              its ends with no match, and its run, its leaves' \
                                              feasibility questions and its matcher received 0 \
                                              undecided solver answers, so no solver query the \
                                              answer rests on was left undecided"
                            .to_owned(),
                    }),
                    witness: None,
                },
                class => Answer::unknown(format!(
                    "{would}: a no also needs the program's baseline run to be comparable \
                     (complete, with no stack stop and no exclusion), and it is {}{}",
                    class.unwrap_or("not known"),
                    facts
                        .baseline_cause
                        .map(|cause| format!(" ({cause})"))
                        .unwrap_or_default(),
                )),
            }
        }
    }
}

/// The searches of one command: one baseline backend, the definition it selected and that
/// definition's exclusions, read on this backend (as kink-campaign reads them for every run).
pub struct Searcher {
    backend: Backend,
    definition: Arc<BackendDefinition>,
    exclusions: DefinitionExclusions,
    budget: Budget,
    /// How a witness names each compiled rule: its label, else `file:line` of the authored rule
    /// behind it, else its id.
    rule_names: BTreeMap<String, String>,
    /// The definition tables of `backend`, kept beside it for every stopped run
    /// ([`Self::run_stopped`]; kink-native `DefinitionTables`).
    tables: DefinitionTables,
}

/// The name of every compiled rule of `spec` an authored rule is behind (`file:line` of its
/// first author, or its label when it has one).
fn rule_names(spec: &AdmittedSpec) -> BTreeMap<String, String> {
    RuleAuthors::of(&spec.compiled)
        .iter()
        .filter_map(|(id, authors)| {
            let Authorship::Sentences(sentences) = authors else {
                return None;
            };
            let at = sentences.first()?;
            let place = sentence_value(spec, at);
            let name = place["label"].as_str().map(str::to_owned).or_else(|| {
                Some(format!(
                    "{}:{}",
                    place["file"].as_str()?,
                    place["start_line"].as_u64()?
                ))
            })?;
            Some((id.to_owned(), name))
        })
        .collect()
}

impl Searcher {
    /// The searcher of `spec`, whose main module is `main_module`.
    pub fn new(spec: &AdmittedSpec, main_module: &str, budget: Budget) -> Result<Self, String> {
        let kore = parse_definition(&spec.compiled.artifacts().definition_kore)
            .map_err(|e| format!("cannot parse the compiled definition: {e}"))?;
        let mut backend = Backend::from_definition(
            kore.clone(),
            k_rust::kast::identifier::encode(main_module),
            budget.backend_options(),
        )
        .map_err(|e| format!("cannot build the search backend: {e}"))?;
        // Selecting the default module loads it; its load counts are then final (as
        // kink-campaign's `Runtime::prepare` reads them).
        let definition = backend
            .select_definition(None)
            .map_err(|e| format!("cannot select the main module: {e}"))?;
        let exclusions = DefinitionExclusions::of(
            &kore,
            &definition,
            &spec.compiled.compile_options().builtin_source_prefixes,
        );
        Ok(Self {
            backend,
            definition,
            exclusions,
            budget,
            rule_names: rule_names(spec),
            tables: DefinitionTables::new(),
        })
    }

    /// The definition every search runs on.
    pub fn definition(&self) -> &BackendDefinition {
        &self.definition
    }

    /// The exclusions of that definition.
    pub const fn exclusions(&self) -> &DefinitionExclusions {
        &self.exclusions
    }

    /// The exclusion of a program's initial state on that definition known before it is
    /// searched, if any: it applies a hook whose value the definition leaves open (kink-native
    /// `state_references_implementation_chosen`, as the campaign runner reads it). Whether its
    /// value depends on the short-circuit reading is judged on the search's own list, which holds
    /// the initial state's normalization ([`Self::search`]), as the runner judges a run's
    /// (`DefinitionExclusions::state_exclusion`).
    pub fn state_exclusion(&self, initial: &Pattern) -> Option<Exclusion> {
        state_references_implementation_chosen(&self.definition, initial)
            .then_some(Exclusion::ImplementationChosenHook)
    }

    /// One search (module docs) and its wall time.
    pub fn search(&mut self, initial: &Pattern, lowered: &LoweredPattern) -> (SearchOutcome, u64) {
        let request = SearchPatternRequest {
            state: initial.clone(),
            pattern: lowered.target.clone(),
            module_name: None,
            search_type: SearchTypeArg::All,
            max_depth: Some(self.budget.max_depth),
            max_breadth: None,
            max_results: Some(1),
            max_simplification_iterations: SIMPLIFICATION_ITERATIONS,
            schema_version: BACKEND_SCHEMA_VERSION,
        };
        let time = Duration::from_millis(self.budget.time_ms);
        let listed = self.backend.capabilities().short_circuit_readings;
        let ground = initial.free_variables().is_empty();
        let started = Instant::now();
        // The search's undecided solver answers are read from its operation record (module docs).
        let ((result, record), fired) = watchdog(time, || {
            with_operation_record(|| self.backend.search_pattern_kore(request))
        });
        let definition = &self.definition;
        let exclusions = &self.exclusions;
        let outcome = outcome(
            result,
            record.unknown_answers,
            fired,
            self.budget,
            lowered,
            &self.rule_names,
            &|state| defined_state(definition, state),
            &|readings| {
                readings_cause(exclusions, readings, listed, ground, &|| {
                    exclusions.state_depends_on_short_circuit(definition, initial)
                })
            },
        );
        let wall_ms = u64::try_from(started.elapsed().as_millis()).unwrap_or(u64::MAX);
        (outcome, wall_ms)
    }

    /// One check of a corpus with `[stop]` (module docs, the stopped route): the run of the
    /// test `test_id` from `initial` as every campaign of the command makes it (`stop`, the
    /// test's count and the stop's condition in one request, under the budget's bounds and
    /// `baseline_max_work`), matching every state it reaches against `lowered` with proof
    /// agreement (module docs); its outcome, the
    /// exclusion of the initial state read with the run's lists (kink-native
    /// `DefinitionExclusions::state_exclusion`, as the baseline runner reads it), and its wall
    /// time. `exclusions` are the definition exclusions the run is judged with.
    pub fn run_stopped(
        &mut self,
        stop: kink_campaign::Stop,
        test_id: &str,
        initial: &Pattern,
        lowered: &LoweredPattern,
        exclusions: &DefinitionExclusions,
    ) -> (SearchOutcome, Option<Exclusion>, u64) {
        let started = Instant::now();
        let matched = stop.execute_result_matching(
            &ExecutionAdapter::with_profile(SolverProfile::BUILD),
            &mut self.backend,
            &mut self.tables,
            test_id,
            initial,
            execution_budget(self.budget),
            ResultRun {
                max_work: self.budget.baseline_max_work,
                ..ResultRun::default()
            },
            // Proof agreement: a refutation in execution mode alone may rest on a value the
            // definition leaves open that nothing records, so a no needs both modes to refute.
            &StateMatchRequest {
                proof_agreement: true,
                ..StateMatchRequest::new(lowered.target.clone())
            },
            exclusions,
        );
        let (outcome, state) = match matched {
            Err(failure) => (
                SearchOutcome::Failed(format!("k-rust refused the stopped run: {failure:?}")),
                None,
            ),
            Ok(matched) => {
                let state = matched.execution.as_ref().and_then(|execution| {
                    exclusions.state_exclusion(&self.definition, initial, execution.facts())
                });
                let outcome = match &matched.answer {
                    MatchAnswer::Hit(reach) => {
                        SearchOutcome::Hit(self.stopped_witness(reach, lowered))
                    }
                    MatchAnswer::No => SearchOutcome::Complete { smt_unknowns: 0 },
                    MatchAnswer::Unknown(unknown) => {
                        let cause = stopped_cause(
                            unknown,
                            matched.execution.as_ref(),
                            self.budget,
                            lowered,
                        );
                        if matches!(unknown, MatchUnknown::Clock) {
                            SearchOutcome::ClockStopped(cause)
                        } else {
                            SearchOutcome::Incomplete(cause)
                        }
                    }
                };
                (outcome, state)
            }
        };
        let wall_ms = u64::try_from(started.elapsed().as_millis()).unwrap_or(u64::MAX);
        (outcome, state, wall_ms)
    }

    /// The facts of a stopped run's witness (module docs, the stopped route; [`witness`]): its
    /// depth and state as the run reported them, `rules` null, and the bindings of an unconditional match
    /// of the pattern against the reached state ([`Self::stopped_bindings`]).
    fn stopped_witness(&mut self, reach: &MatchedState, lowered: &LoweredPattern) -> Value {
        let bindings = self.stopped_bindings(&reach.state, lowered);
        json!({
            "depth": reach.depth,
            "state": reach.state.to_string(),
            "bindings": bindings,
            "rules": null,
        })
    }

    /// The bindings of the author's variables in a match of `lowered` against `state`, a state
    /// the stopped run reached: a search of depth 0 from `state`, every match it gives, and the
    /// first of them without a condition, which is the kind of match the run's matcher reached
    /// (a reach is matched with empty constraints). The work is bounded by itself, not by a
    /// clock: one normalization of a state already in normal form within the simplification
    /// bound, and one match, whose solver queries are bounded by the manifest's resource units.
    /// So with no watchdog to fire, the bindings are a function of the state, the pattern and the
    /// definition, as the answer they explain is. Where the search fails or gives no match
    /// without a condition, the bindings are absent, `{absent: reason}`, which no array of
    /// bindings is (an empty array says the author wrote no variable). The bindings are for the
    /// reader only: no answer reads them.
    fn stopped_bindings(&mut self, state: &Pattern, lowered: &LoweredPattern) -> Value {
        let request = SearchPatternRequest {
            state: state.clone(),
            pattern: lowered.target.clone(),
            module_name: None,
            search_type: SearchTypeArg::All,
            max_depth: Some(0),
            max_breadth: None,
            max_results: None,
            max_simplification_iterations: SIMPLIFICATION_ITERATIONS,
            schema_version: BACKEND_SCHEMA_VERSION,
        };
        let absent = |reason: String| json!({ "absent": reason });
        match self.backend.search_pattern_kore(request) {
            Err(error) => absent(format!(
                "matching the reached state against the pattern again failed: {error}"
            )),
            Ok(response) => response
                .matches
                .iter()
                .find(|found| found.constraints.is_empty())
                .map_or_else(
                    || {
                        absent(
                            "matching the reached state against the pattern again gave no match \
                             without a condition"
                                .to_owned(),
                        )
                    },
                    |found| witness(found, lowered, &self.rule_names)["bindings"].take(),
                ),
        }
    }
}

/// The note of a witness on the search route ([`rendered_witness`]).
const SEARCH_WITNESS_NOTE: &str = "the state is listed by its cells: a cell the pattern names is \
     printed in full, every other cell shortened (a collection of more than a few elements by its \
     length and its last elements for a list, its first entries for a map or a set; any other \
     content cut), each value as K text or, where the K printer refused it, as KORE; a binding is \
     printed in full, a long collection shortened likewise; rules name the rewrite steps of one \
     path from the initial state to the matching state, each by its label, else by the file and \
     line of the rule written for it, else by its compiled id; the cache record keeps the state \
     and the bindings whole, as KORE";

/// The note of a stopped run's witness ([`Searcher::stopped_witness`], [`rendered_witness`]).
const STOPPED_WITNESS_NOTE: &str = "the state and the bindings are printed as a search's witness \
     prints them; rules is null: the stopped run reports the depth and the state of the first state it reached that matches, not \
     the rewrite steps of the path to it, and a search for that path could find another path, \
     past a stop; the bindings are those of a match of the pattern against that state without a \
     condition, or {absent: reason} where none was produced";

/// The cause of a stopped run's `unknown` (kink-campaign `MatchUnknown`), in the reader's words,
/// each naming its cause; `execution` is the run, when it has a result.
fn stopped_cause(
    unknown: &MatchUnknown,
    execution: Option<&kink_native::execution::AdaptedExecution>,
    budget: Budget,
    lowered: &LoweredPattern,
) -> String {
    let name = unknown.name();
    let reach = |what: &str, state: &MatchedState| {
        format!(
            "the first state the stopped run reached that matches (depth {}) {what} ({name})",
            state.depth
        )
    };
    let would = "the stopped run reached no state that matches, but a no is not given";
    match unknown {
        MatchUnknown::Clock => format!(
            "the stopped run did not finish within time_ms = {}, so its states are not read \
             ({name}: the clock is no answer)",
            budget.time_ms
        ),
        MatchUnknown::StopConditionRefused(reason) => format!(
            "the stop's condition refused at an arrival or could not be asked ({reason}), so the \
             stop is not defined on this run, nor is the system it truncates ({name})"
        ),
        MatchUnknown::PassedStop(passed) => format!(
            "the stopped run went on past a step of a stop rule that had another successor \
             ({name}: {}), so on that branch its states need not be states of the truncated \
             system, and neither a match nor its lack is an answer",
            passed
                .iter()
                .map(|stop| format!("{} at depth {}", stop.rule, stop.depth))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        MatchUnknown::DirtyReach(state) => reach(
            &format!(
                "rests on its path's diagnostics ({}), so the path may not exist",
                state
                    .diagnostics
                    .iter()
                    .map(diagnostic_kind)
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            state,
        ),
        MatchUnknown::TermConjunction(state) => reach(
            "holds a term-level \\and, which denotes a configuration only where its sides are \
             equal, which kink does not decide",
            state,
        ),
        MatchUnknown::UnevaluatedHook => {
            let hooks = execution
                .map(|execution| {
                    let facts = execution.facts();
                    facts
                        .unsupported_hooks
                        .iter()
                        .chain(&facts.allowance_refusals)
                        .map(|entry| entry.hook.clone())
                        .collect::<BTreeSet<_>>()
                        .into_iter()
                        .collect::<Vec<_>>()
                        .join(", ")
                })
                .unwrap_or_default();
            format!(
                "a state the stopped run reached matches, but the run left applications \
                 unevaluated ({UNSUPPORTED_HOOK}: {hooks}; a hook it does not evaluate, or a \
                 result its memory allowance refused), and a state holding one denotes a \
                 configuration only where the hook is defined at its arguments, which k-rust did \
                 not compute"
            )
        }
        MatchUnknown::UndecidedMatch(undecided) => format!(
            "{would}: the matcher left the verdict of some reached state undecided ({name}: \
             {}){}",
            undecided
                .iter()
                .map(|(reason, count)| format!("{} {count}", undecided_reason(*reason)))
                .collect::<Vec<_>>()
                .join(", "),
            lowered.requires_only_note()
        ),
        MatchUnknown::StopConditionUndecided(reason) => format!(
            "{would}: a path ended at an arrival at a stop where the condition was left \
             undecided (stop-undecided{}), which is no end of the truncated system ({name})",
            reason
                .as_deref()
                .map(|reason| format!(": {reason}"))
                .unwrap_or_default()
        ),
        MatchUnknown::Incomplete { halt, leaves } => {
            let first = match halt {
                HaltClass::DepthBound => format!("a path reached max_depth = {}", budget.max_depth),
                HaltClass::WorkBound => format!(
                    "the run reached baseline_max_work = {}",
                    budget
                        .baseline_max_work
                        .map_or_else(|| "unset".to_owned(), |work| work.to_string())
                ),
                halt => format!("a {} leaf", crate::results::kebab(&format!("{halt:?}"))),
            };
            format!(
                "{would}: the run did not explore the truncated system to its ends ({name}: \
                 {leaves} leaf/leaves ended where the system goes on, the first: {first})"
            )
        }
        MatchUnknown::DiagnosedLeaf { halt, leaves } => format!(
            "{would}: {leaves} leaf/leaves of the run carry a diagnostic of their path, the first a \
             {} leaf ({name}): a rule whose condition was left unsimplified, failed to simplify \
             or exhausted the simplification budget may have been left unapplied there, so the \
             leaf need not be an end of the truncated system",
            crate::results::kebab(&format!("{halt:?}"))
        ),
        MatchUnknown::ExecutionModeRefutation => format!(
            "{would}: the run's states were refuted in execution mode alone ({name}), where the \
             matcher may read a value the definition leaves open without the run recording it"
        ),
        MatchUnknown::Exclusion(exclusion) => exclusion_cause(*exclusion, would),
        MatchUnknown::MatcherStackStop(stops) => format!(
            "{would}: the matcher stopped {stops} time(s) for lack of native stack ({name}), \
             which leaves its match undecided"
        ),
        MatchUnknown::UndecidedAnswers {
            run,
            feasibility,
            matcher,
        } => format!(
            "{would}: the run received {run}, its leaves' feasibility questions {feasibility} \
             and its matcher {matcher} undecided solver answer(s) ({name}: a query Z3 did not \
             decide within budget.smt_resource_limit and its retries, or by its \
             incompleteness), so a decision the answer rests on may rest on one"
        ),
        MatchUnknown::Unmatched => {
            format!("the stopped run reports no state matches ({name}), so it answers nothing")
        }
    }
}

/// The kind of a path diagnostic, as k-rust's wire `kind` spells it (kebab case of its variant).
fn diagnostic_kind(diagnostic: &k_rust::backend::BackendDiagnosticOutput<Pattern>) -> String {
    let debug = format!("{diagnostic:?}");
    let variant = debug
        .split(|c: char| !c.is_alphanumeric())
        .next()
        .unwrap_or_default();
    crate::results::kebab(variant)
}

/// k-rust's name of an undecided match's reason.
fn undecided_reason(reason: UndecidedMatchReasonOutput) -> String {
    serde_json::to_value(reason)
        .ok()
        .and_then(|value| value.as_str().map(str::to_owned))
        .unwrap_or_else(|| format!("{reason:?}"))
}

/// Run `body` under a watchdog that cancels it after `time`; whether the watchdog fired.
fn watchdog<T>(time: Duration, body: impl FnOnce() -> T) -> (T, bool) {
    let token = CancellationToken::new();
    let fired = Arc::new(AtomicBool::new(false));
    if time.is_zero() {
        fired.store(true, Ordering::Release);
        token.cancel();
    }
    let (done, finished) = mpsc::channel::<()>();
    let guard = {
        let token = token.clone();
        let fired = Arc::clone(&fired);
        thread::spawn(move || {
            if finished.recv_timeout(time) == Err(mpsc::RecvTimeoutError::Timeout) {
                fired.store(true, Ordering::Release);
                token.cancel();
            }
        })
    };
    let value = token.scope(body);
    drop(done);
    guard.join().expect("the watchdog thread does not panic");
    (value, fired.load(Ordering::Acquire))
}

/// The tag KORE JSON writes for the root of `pattern` (`App`, `And`, `DV`, ...), which names
/// its construct in a refusal.
fn kore_tag(pattern: &Pattern) -> &'static str {
    match pattern {
        Pattern::String(_) => "String",
        Pattern::Variable(variable) => match variable.kind {
            k_rust::kore::ast::VariableKind::Element => "EVar",
            k_rust::kore::ast::VariableKind::Set => "SVar",
        },
        Pattern::Application { .. } => "App",
        Pattern::Top { .. } => "Top",
        Pattern::Bottom { .. } => "Bottom",
        Pattern::And { .. } => "And",
        Pattern::Or { .. } => "Or",
        Pattern::Not { .. } => "Not",
        Pattern::Next { .. } => "Next",
        Pattern::Implies { .. } => "Implies",
        Pattern::Iff { .. } => "Iff",
        Pattern::Rewrites { .. } => "Rewrites",
        Pattern::Exists { .. } => "Exists",
        Pattern::Forall { .. } => "Forall",
        Pattern::Mu { .. } => "Mu",
        Pattern::Nu { .. } => "Nu",
        Pattern::Ceil { .. } => "Ceil",
        Pattern::Floor { .. } => "Floor",
        Pattern::Equals { .. } => "Equals",
        Pattern::In { .. } => "In",
        Pattern::DomainValue { .. } => "DV",
        Pattern::AssociativeApplication {
            associativity: Associativity::Left,
            ..
        } => "LeftAssoc",
        Pattern::AssociativeApplication { .. } => "RightAssoc",
    }
}

/// The cause a hit is refused for when its state is not shown defined (module docs).
const UNDEFINED_STATE: &str = "undefined-state";

/// Runs the internalization of a matched state on a stack sized for its pattern:
/// `BackendDefinition::with_stack_for` itself in [`defined_state`] (its `Err` is a refused
/// stack). The unit tests' seam for a k-rust panic and a stack refusal, which no fixture
/// provokes (a refusal needs a state about a million levels deep, or a host that refuses to map
/// the segment).
type StackFor<'a> = &'a dyn Fn(
    &Pattern,
    &dyn Fn() -> Result<bool, String>,
) -> Result<Result<bool, String>, DefinitionError>;

/// Whether the term of a matched state (`state`) is defined: k-rust's `ground_defined` of the
/// state internalized on `definition`, the definition the search ran on (module docs).
/// `Err` says why the state is not shown defined, or why kink could not tell.
fn defined_state(definition: &BackendDefinition, state: &Pattern) -> Result<(), String> {
    defined_state_with(definition, state, &|pattern, work| {
        definition.with_stack_for(&[pattern], work)
    })
}

/// [`defined_state`] whose internalization runs under `stack_for` ([`StackFor`]). Only an
/// internalized term that k-rust shows `ground_defined` is `Ok`: a state that holds a term-level
/// `\and`, does not verify or internalize, a refused stack and a k-rust panic are each `Err` (the
/// answer is then unknown, never a hit).
fn defined_state_with(
    definition: &BackendDefinition,
    pattern: &Pattern,
    stack_for: StackFor<'_>,
) -> Result<(), String> {
    if holds_conjunction(pattern) {
        return Err(format!(
            "it holds a term-level \\and ({UNDEFINED_STATE}): a conjunction of different sides \
             denotes a configuration only where its sides are equal, which kink does not decide, \
             so the state may denote none"
        ));
    }
    let unknown = |why: String| format!("{why}, so its definedness is not known");
    // The internalized term is dropped inside the work, on the stack k-rust sizes for it.
    let work = || {
        stack_for(pattern, &|| {
            definition
                .verify_standalone_pattern(pattern, &[])
                .and_then(|admitted| admitted.internalize_term())
                .map(|term| definition.ground_defined(&term))
                .map_err(|e| format!("it does not internalize on the searched definition ({e})"))
        })
    };
    let free = std::panic::catch_unwind(std::panic::AssertUnwindSafe(work))
        .map_err(|_| unknown("k-rust panicked while internalizing it".to_owned()))?
        .map_err(|e| unknown(format!("k-rust provides no stack to internalize it ({e})")))?
        .map_err(unknown)?;
    if free {
        Ok(())
    } else {
        Err(format!(
            "k-rust does not show its term defined ({UNDEFINED_STATE}): it holds an application \
             of a function the definition does not declare total that no equation reduced (such \
             as `f(3)` for a function with an equation for `f(0)` only, or an application an \
             `anywhere` rule of its head still matches), or a map or set whose keys k-rust does \
             not show apart, so the state may denote no configuration"
        ))
    }
}

/// Whether `pattern` holds a term-level `\and`, at its root or below: k-rust's definedness walk
/// owes nothing for `\and(a, a)`, and `\and(a, b)` is empty when `a` and `b` differ, which kink
/// does not decide, so a state holding one is not shown defined (module docs). An associative application of `\and`
/// counts too. The walk keeps its pending nodes on k-rust's explicit stack.
fn holds_conjunction(pattern: &Pattern) -> bool {
    let mut found = false;
    k_rust::kore::walk::for_each_post_order(pattern, |node| {
        found |= match node {
            Pattern::And { .. } => true,
            Pattern::AssociativeApplication { symbol, .. } => symbol.name == "\\and",
            _ => false,
        };
    });
    found
}

/// The search's outcome (module docs: what makes a match decided and an exploration complete);
/// `smt_unknowns` is the undecided solver answers the search received, which a completed
/// exploration carries.
/// `defined` decides whether a decided match's state is defined ([`defined_state`] on the
/// searcher's definition; the unit tests pass their own); `readings` says why the search's
/// `shortCircuitReadings` list keeps a completed exploration from being complete, or `None`
/// ([`readings_cause`] on the searcher's definition).
#[allow(clippy::too_many_arguments)]
fn outcome(
    result: Result<KorePatternSearchResponse, BackendError>,
    smt_unknowns: usize,
    fired: bool,
    budget: Budget,
    lowered: &LoweredPattern,
    rule_names: &BTreeMap<String, String>,
    defined: &dyn Fn(&Pattern) -> Result<(), String>,
    readings: &dyn Fn(Vec<ShortCircuitReadingOutput<Pattern>>) -> Option<String>,
) -> SearchOutcome {
    let clock = || {
        SearchOutcome::ClockStopped(format!(
            "the search did not finish within time_ms = {} (a search has no work budget at this \
             k-rust pin, so the clock bounds it)",
            budget.time_ms
        ))
    };
    let response = match result {
        Ok(response) => response,
        Err(_) if fired => return clock(),
        Err(error) if matches!(error.stop_cause(), Some(StopCause::Cancelled)) => return clock(),
        Err(error) => return SearchOutcome::Failed(format!("k-rust refused the search: {error}")),
    };
    // A token cancelled before the call returned can leave a state unsimplified (k-rust's
    // Execute promise excludes it), so nothing a cancelled search returned is an answer.
    if fired {
        return clock();
    }
    if response.initial_bottom {
        return SearchOutcome::Incomplete(
            "the initial state has no instance (k-rust's initial_bottom), so no run starts"
                .to_owned(),
        );
    }
    if let Some(found) = response.matches.first() {
        if let Some(why) = unevaluated(&response) {
            return SearchOutcome::Incomplete(format!(
                "the first matching state the search found (depth {}) is not shown to be a \
                 configuration: {why}; the search stops at its first match, so no other state was \
                 asked",
                found.state.depth
            ));
        }
        return match decided(found).and_then(|()| defined(&found.state.state)) {
            Ok(()) => SearchOutcome::Hit(witness(found, lowered, rule_names)),
            Err(why) => SearchOutcome::Incomplete(format!(
                "the first matching state the search found (depth {}) is not a decided match: \
                 {why}; the search stops at its first match, so no other state was asked{}",
                found.state.depth,
                lowered.requires_only_note()
            )),
        };
    }
    if !response.incomplete.is_empty() {
        let cause = incomplete_cause(&response.incomplete, budget, lowered);
        // A cancelled entry is the clock's: without it the exploration could have completed.
        return if response
            .incomplete
            .iter()
            .any(|entry| matches!(entry, IncompleteSearchOutput::Cancelled { .. }))
        {
            SearchOutcome::ClockStopped(cause)
        } else {
            SearchOutcome::Incomplete(cause)
        };
    }
    // KINK-R4 review N2: an exploration that left a hook application unevaluated is not shown to
    // have explored the reachable configurations. Where the hook is undefined at its arguments
    // the step to that state has no successor, and where it is defined its value can let a rule
    // apply that the unevaluated application did not; k-rust computed neither. So no `no` rests
    // on it, whether or not the program's separate baseline run met the same hook.
    if let Some(why) = unevaluated(&response) {
        return SearchOutcome::Incomplete(format!(
            "the exploration found no match, but its states are not shown to be the reachable \
             configurations: {why}, nor which successors the hook's value would give"
        ));
    }
    // kink27 R3-CENSUS-RUNLEVEL (gap G1): k-rust's classes are judged per run, not by the census.
    // A search lists every class value it took, on any branch, a vanished candidate and the
    // pattern's matching included, and only a search whose list is empty has the same results and
    // end in every model of the definition (compat "Marks in executions"). So no `no` rests on a
    // search that read one: another model of the value may reach the pattern. A hit is unchanged:
    // a decided match carries no diagnostic, so no mark is on its own path, and it matches there in
    // every such model.
    if let Some(hooks) = chosen_values(&response) {
        return SearchOutcome::Incomplete(format!(
            "the exploration found no match, but the search read values the definition leaves \
             open ({IMPLEMENTATION_CHOSEN_VALUE}: {hooks}), so another model of the definition \
             may reach the pattern"
        ));
    }
    // A hit is unchanged by the list (module docs): a decided match is one model's reached
    // configuration, and the claim is existential.
    if let Some(why) = readings(response.short_circuit_readings) {
        return SearchOutcome::Incomplete(format!(
            "the exploration found no match, but {why}, so a backend that skips that operand may \
             reach the pattern"
        ));
    }
    SearchOutcome::Complete { smt_unknowns }
}

/// The cause a `no` is refused for when the search read an operand a short-circuiting backend
/// may skip.
const SHORT_CIRCUIT_READING: &str = "short-circuit-reading";

/// Why a search's `shortCircuitReadings` list (`readings`; `listed`: whether the searching
/// backend lists them, its `short_circuit_readings` capability; `ground`: whether the search
/// started from a state without free variables) keeps its completed exploration from a `no` on
/// the definition whose exclusions are `exclusions`, or `None`: the list is judged as
/// kink-campaign judges a run's (kink-native `DefinitionExclusions::short_circuit_excludes`, and
/// for an initial state that applies a reading-dependent function, which `state` tells and is
/// asked only when the list leaves the question open, `DefinitionExclusions::state_exclusion`),
/// so the search is excluded exactly where a run of it would be.
fn readings_cause(
    exclusions: &DefinitionExclusions,
    readings: Vec<ShortCircuitReadingOutput<Pattern>>,
    listed: bool,
    ground: bool,
    state: &dyn Fn() -> bool,
) -> Option<String> {
    let facts = RunFacts {
        short_circuit_readings: listed.then_some(readings),
        ground,
        ..RunFacts::default()
    };
    let (counting, of_state) = if exclusions.short_circuit_excludes(&facts) {
        (exclusions.counting_short_circuit_readings(&facts), false)
    } else {
        let counting = exclusions.state_short_circuit_readings(&facts);
        if (listed && counting.is_empty()) || !state() {
            return None;
        }
        (counting, true)
    };
    let counting = counting.into_iter().cloned().collect::<Vec<_>>();
    let flagged = if of_state {
        "the program's initial state applies a function or operator whose value depends on the \
         short-circuit reading"
    } else {
        "the definition's short-circuit analysis flags a rule"
    };
    Some(if counting.is_empty() {
        format!(
            "{flagged} and the backend lists no short-circuit readings ({SHORT_CIRCUIT_READING}), \
             so kink cannot tell whether the search read an operand a short-circuiting backend \
             may skip"
        )
    } else if of_state {
        format!(
            "{flagged}, and the search read the definedness of an operand a short-circuiting \
             backend may skip ({SHORT_CIRCUIT_READING}: {})",
            crate::exclusion::readings_text(&counting)
        )
    } else {
        format!(
            "the search read the definedness of an operand a short-circuiting backend may skip \
             ({SHORT_CIRCUIT_READING}: {})",
            crate::exclusion::readings_text(&counting)
        )
    })
}

/// The cause a `no` is refused for when the search read a value the definition leaves open.
const IMPLEMENTATION_CHOSEN_VALUE: &str = "implementation-chosen-value";

/// The hooks of the search response's `implementationChosenValues` list, each with its class, or
/// `None` when the list is empty.
fn chosen_values(response: &KorePatternSearchResponse) -> Option<String> {
    let marks = response
        .implementation_chosen_values
        .iter()
        .map(|mark| format!("{} ({})", mark.hook, mark.class))
        .collect::<BTreeSet<_>>();
    (!marks.is_empty()).then(|| marks.into_iter().collect::<Vec<_>>().join(", "))
}

/// The cause a hit is refused for when the search left a hook application unevaluated.
const UNSUPPORTED_HOOK: &str = "unsupported-hook";

/// Why the search's states are not shown to be configurations because k-rust left a hook
/// application unevaluated, or `None` (module docs, KINK-HOOKED-VP-QUERY-HIT): the response's
/// `unsupportedHooks` (a hook k-rust does not evaluate) and `allowanceRefusals` (a `Bytes` result
/// the memory allowance refused) lists. Such an application stays in the state as written, and
/// `ground_defined` counts an irreducible application of a `value-production` symbol as a value
/// from its declaration alone, hooked or not; but where the hook is undefined at its arguments the
/// state denotes no configuration and the step to it has no successor, which k-rust did not
/// compute. No path diagnostic records it, and the lists are the search's as a whole, so any entry
/// refuses the hit (a fail-closed loss when the entry is on another branch) and makes a completed
/// exploration incomplete (review N2).
fn unevaluated(response: &KorePatternSearchResponse) -> Option<String> {
    let hooks = response
        .unsupported_hooks
        .iter()
        .chain(&response.allowance_refusals)
        .map(|entry| entry.hook.clone())
        .collect::<BTreeSet<_>>();
    (!hooks.is_empty()).then(|| {
        format!(
            "k-rust left applications of {} unevaluated in the search ({UNSUPPORTED_HOOK}: a hook \
             it does not evaluate, or a result its memory allowance refused), and a state holding \
             one denotes a configuration only where the hook is defined at its arguments, which \
             k-rust did not compute",
            hooks.into_iter().collect::<Vec<_>>().join(", ")
        )
    })
}

/// Why a match is not a decided hit, or `Ok`.
fn decided(found: &SearchMatchOutput<Pattern>) -> Result<(), String> {
    if !found.constraints.is_empty() {
        return Err("it holds under a condition k-rust did not decide".to_owned());
    }
    if !found.diagnostics.is_empty() {
        return Err("matching it emitted a backend diagnostic".to_owned());
    }
    if !found.state.diagnostics.is_empty() {
        return Err(
            "its path emitted a backend diagnostic (the state may not be the normal form, a \
             condition on the path was left undecided, or a hook was refused)"
                .to_owned(),
        );
    }
    let state = &found.state.state;
    if !matches!(state, Pattern::Application { .. }) {
        return Err(format!(
            "the state is a {} pattern, not a configuration without predicates",
            kore_tag(state)
        ));
    }
    Ok(())
}

/// Whether the KORE variable `name` is one k-rust's pattern compiler generated: one it lists
/// (`generated_anonymous_variables`), or one spelled as its fresh-name passes spell an anonymous
/// variable (`_Gen<n>`, `?_Gen<n>`, `!_Gen<n>`, `@_Gen<n>`, `_DotVar<n>`: k-rust
/// `kompile::fresh_names`). At k-rust 501f18b9 the list omits the variables that complete the
/// omitted sibling cells of a pattern, so both are read. A witness's bindings leave such a
/// variable out, and a chain does not share it between its parts ([`chain`]): each part's
/// generated variables are its own.
fn generated(lowered: &LoweredPattern, name: &str) -> bool {
    if lowered.generated.contains(name) {
        return true;
    }
    let (_, decoded) = k_rust::kast::identifier::decode_variable(name);
    decoded.is_ok_and(|decoded| {
        ["_Gen", "?_Gen", "!_Gen", "@_Gen", "_DotVar"]
            .iter()
            .any(|prefix| {
                decoded.strip_prefix(prefix).is_some_and(|suffix| {
                    !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
                })
            })
    })
}

/// A hit's witness as facts (module docs): `{depth, state, bindings, rules}`, the state and each
/// binding's variable and value as whole KORE text, which the cache record keeps and `--verify`
/// compares; [`rendered_witness`] prints it for the reader.
fn witness(
    found: &SearchMatchOutput<Pattern>,
    lowered: &LoweredPattern,
    rule_names: &BTreeMap<String, String>,
) -> Value {
    let state = &found.state;
    let bindings = found
        .bindings
        .iter()
        .filter(|binding| {
            !matches!(&binding.variable, Pattern::Variable(variable)
                if generated(lowered, &variable.name))
        })
        .map(|binding| {
            json!({
                "variable": binding.variable.to_string(),
                "value": binding.value.to_string(),
            })
        })
        .collect::<Vec<_>>();
    let rules = state
        .trace
        .iter()
        .filter(|entry| entry.kind == "rewrite")
        .map(|entry| {
            let name = entry.label.as_deref().unwrap_or_else(|| {
                rule_names
                    .get(&entry.unique_id)
                    .map_or(entry.unique_id.as_str(), String::as_str)
            });
            json!(name)
        })
        .collect::<Vec<_>>();
    json!({
        "depth": state.depth,
        "state": state.state.to_string(),
        "bindings": bindings,
        "rules": rules,
    })
}

/// A hit's witness for the reader (module docs), derived from its facts `facts` (the form a
/// search gives and the cache record keeps, [`witness`]) when a document is written, so a cached
/// hit is printed as a live one is: `{depth, state, bindings, rules, rendering, note}`, the state
/// listed by its cells and each binding printed (`crate::evidence`, "A query witness"), the cells
/// `lowered` names printed in full. A KORE text of the facts that does not parse (a forged
/// record) is shown as KORE, cut at [`VALUE_CAP`], with the parser's error.
pub fn rendered_witness(facts: &Value, lowered: &LoweredPattern, reader: &EndReader) -> Value {
    let parsed = |text: &Value| -> Result<Pattern, Value> {
        let text = text.as_str().unwrap_or_default();
        parse_pattern(text).map_err(|error| {
            json!({
                "text": text.chars().take(VALUE_CAP).collect::<String>(),
                "rendering": "kore",
                "truncated": text.chars().count() > VALUE_CAP,
                "note": format!("the witness's KORE text does not parse: {error}"),
            })
        })
    };
    let named = reader.named_cells(&lowered.target, &|name| generated(lowered, name));
    let state = parsed(&facts["state"]).map_or_else(
        |unreadable| json!({ "unreadable": unreadable }),
        |state| reader.witness_state(&state, &named),
    );
    let bindings = match &facts["bindings"] {
        Value::Array(bindings) => Value::Array(
            bindings
                .iter()
                .map(|binding| {
                    json!({
                        "variable": variable_name(&binding["variable"]),
                        "value": parsed(&binding["value"])
                            .map_or_else(|unreadable| unreadable, |value| reader.witness_value(&value)),
                    })
                })
                .collect(),
        ),
        absent => absent.clone(),
    };
    json!({
        "depth": facts["depth"],
        "state": state,
        "bindings": bindings,
        "rules": facts["rules"],
        "rendering": "k",
        "note": if facts["rules"].is_null() { STOPPED_WITNESS_NOTE } else { SEARCH_WITNESS_NOTE },
    })
}

/// The name the author wrote for a binding's variable, its KORE text `variable`
/// (`VarN:SortInt{}` is `N`, a set variable keeps its `@`); the text itself where it is no
/// variable whose name decodes.
fn variable_name(variable: &Value) -> Value {
    let text = variable.as_str().unwrap_or_default();
    let name = parse_pattern(text).ok().and_then(|pattern| match &pattern {
        Pattern::Variable(variable) => {
            let (kind, decoded) = k_rust::kast::identifier::decode_variable(&variable.name);
            decoded.ok().map(|name| match kind {
                k_rust::kore::ast::VariableKind::Set => format!("@{name}"),
                k_rust::kore::ast::VariableKind::Element => name,
            })
        }
        _ => None,
    });
    json!(name.unwrap_or_else(|| text.to_owned()))
}

/// The cause of an incomplete exploration, from k-rust's incomplete entries.
fn incomplete_cause(
    incomplete: &[IncompleteSearchOutput<Pattern>],
    budget: Budget,
    lowered: &LoweredPattern,
) -> String {
    use IncompleteSearchOutput as I;
    let mut kinds = BTreeSet::new();
    for entry in incomplete {
        kinds.insert(match entry {
            I::DepthBound { .. } => format!("a path reached max_depth = {}", budget.max_depth),
            I::BreadthBound { .. } => "the frontier exceeded the breadth bound".to_owned(),
            I::Cancelled { .. } => format!(
                "the search did not finish within time_ms = {}",
                budget.time_ms
            ),
            I::Indeterminate { .. } => "a step k-rust could not decide (indeterminate)".to_owned(),
            I::Simplification {
                error: SearchFailureOutput::StackExhausted,
                ..
            } => "a state's simplification stopped for lack of native stack (stack-exhausted)"
                .to_owned(),
            I::Simplification { .. } => "a state's simplification failed".to_owned(),
            I::Match { .. } => format!(
                "a state's match against the pattern was left undecided{}",
                lowered.requires_only_note()
            ),
            I::PlacementBound { bound, .. } => format!(
                "a state's match against the pattern placed a list pattern's items on the \
                 state's list and stopped at its bound of {bound} placements tried \
                 (placement-bound)"
            ),
            I::Smt { .. } => format!(
                "a solver query failed or was undecided{}",
                lowered.requires_only_note()
            ),
            I::ResultBound => "the search stopped at its result bound".to_owned(),
        });
    }
    format!(
        "the exploration did not complete: {}",
        kinds.into_iter().collect::<Vec<_>>().join("; ")
    )
}

#[cfg(test)]
mod tests {
    //! The outcome of hand-built k-rust search responses (F-18 fix 1): what makes a match a
    //! decided hit and an exploration complete, one condition at a time.
    use super::*;
    use k_rust::{
        backend::{
            BackendDiagnosticOutput, BudgetSubjectOutput, ChosenValueOutput, ObservedInOutput,
            ReadingOutcomeOutput, ResultModalityOutput, SearchStateOutput, UnevaluatedHookOutput,
        },
        kore::{codec::from_value, parser::parse_pattern},
    };
    use std::cell::Cell;

    fn kore(text: &str) -> Pattern {
        parse_pattern(text).unwrap()
    }

    fn lowered() -> LoweredPattern {
        LoweredPattern {
            target: kore(r"\top{SortInt{}}()"),
            generated: BTreeSet::new(),
            digest: payload_digest(PATTERN_DOMAIN, b"test"),
            requires_only: BTreeSet::new(),
        }
    }

    /// A configuration term without predicates.
    fn configuration() -> Pattern {
        kore("Lbl'-LT-'k'-GT-'{}()")
    }

    /// A search state at `depth`, without diagnostics, trace or observations.
    fn reached(state: Pattern, depth: u64) -> SearchStateOutput<Pattern> {
        SearchStateOutput {
            state,
            diagnostics: Vec::new(),
            depth,
            trace: Vec::new(),
            branch: Vec::new(),
            observations: Vec::new(),
        }
    }

    /// A decided match at depth 2: no condition, no diagnostic, a term state.
    fn decided_match() -> SearchMatchOutput<Pattern> {
        SearchMatchOutput {
            bindings: Vec::new(),
            constraints: Vec::new(),
            state: reached(configuration(), 2),
            diagnostics: Vec::new(),
        }
    }

    fn response(
        matches: Vec<SearchMatchOutput<Pattern>>,
        incomplete: Vec<IncompleteSearchOutput<Pattern>>,
    ) -> KorePatternSearchResponse {
        KorePatternSearchResponse {
            schema_version: BACKEND_SCHEMA_VERSION,
            modality: ResultModalityOutput::StateSet,
            matches,
            effects: Vec::new(),
            incomplete,
            initial_bottom: false,
            implementation_chosen_values: Vec::new(),
            contradicted_claims: Vec::new(),
            allowance_refusals: Vec::new(),
            unsupported_hooks: Vec::new(),
            short_circuit_readings: Vec::new(),
        }
    }

    fn run(
        response: KorePatternSearchResponse,
        defined: &dyn Fn(&Pattern) -> Result<(), String>,
    ) -> SearchOutcome {
        outcome(
            Ok(response),
            0,
            false,
            Budget::default(),
            &lowered(),
            &BTreeMap::new(),
            defined,
            &|_| None,
        )
    }

    fn always(_: &Pattern) -> Result<(), String> {
        Ok(())
    }

    #[track_caller]
    fn incomplete(outcome: &SearchOutcome, cause: &str) {
        match outcome {
            SearchOutcome::Incomplete(why) | SearchOutcome::ClockStopped(why) => {
                assert!(why.contains(cause), "{why}");
            }
            other => panic!("expected an unknown with {cause:?}, got {other:?}"),
        }
    }

    #[test]
    fn a_decided_match_on_a_defined_state_is_a_hit() {
        let asked = Cell::new(0);
        let outcome = run(response(vec![decided_match()], vec![]), &|state| {
            asked.set(asked.get() + 1);
            assert_eq!(*state, configuration());
            Ok(())
        });
        assert!(
            matches!(&outcome, SearchOutcome::Hit(w) if w["depth"] == 2),
            "{outcome:?}"
        );
        assert_eq!(asked.get(), 1, "the state's definedness is asked once");
    }

    /// A hit's witness keeps the state and the bindings as whole KORE text (its facts) and names
    /// the path's rewrite steps by label, else by the rule name kink knows for the id, else by
    /// the id; a binding of a generated variable is left out.
    #[test]
    fn a_hit_witness_prints_the_state_bindings_and_rules() {
        use k_rust::backend::{BindingOutput, TraceEntry};
        let mut found = decided_match();
        found.bindings = vec![
            BindingOutput {
                variable: kore("VarN:SortInt{}"),
                value: kore(r#"\dv{SortInt{}}("3")"#),
            },
            BindingOutput {
                variable: kore("VarHidden:SortInt{}"),
                value: kore(r#"\dv{SortInt{}}("4")"#),
            },
        ];
        let entry = |kind: &str, label: Option<&str>, id: &str| TraceEntry {
            depth: 0,
            kind: kind.to_owned(),
            label: label.map(str::to_owned),
            unique_id: id.to_owned(),
        };
        found.state.trace = vec![
            entry("rewrite", Some("M.labelled"), "a"),
            entry("simplification", None, "s"),
            entry("rewrite", None, "b"),
            entry("rewrite", None, "c"),
        ];
        let names = BTreeMap::from([("b".to_owned(), "lib.rs:7".to_owned())]);
        let mut lowered = lowered();
        lowered.generated.insert("VarHidden".to_owned());
        let outcome = outcome(
            Ok(response(vec![found], vec![])),
            0,
            false,
            Budget::default(),
            &lowered,
            &names,
            &always,
            &|_| None,
        );
        let SearchOutcome::Hit(witness) = outcome else {
            panic!("a hit: {outcome:?}");
        };
        assert_eq!(witness["depth"], 2);
        assert_eq!(witness["state"], json!("Lbl'-LT-'k'-GT-'{}()"));
        assert_eq!(
            witness["bindings"],
            json!([{"variable": "VarN:SortInt{}", "value": r#"\dv{SortInt{}}("3")"#}])
        );
        assert_eq!(witness["rules"], json!(["M.labelled", "lib.rs:7", "c"]));
        assert_eq!(witness.get("rendering"), None, "facts carry no rendering");
    }

    /// FB-53: a pattern that does not parse and writes a tag naming no cell of the configuration
    /// names it and the configuration's cells; a known tag, a closing tag of a known cell and a
    /// `<` that opens no tag name nothing.
    #[test]
    fn an_unknown_cell_tag_is_named_with_the_declared_cells() {
        let cells = ["k".to_owned(), "regs".to_owned()];
        assert_eq!(
            unknown_cells("<IF> 5 </IF> <k> X <Int 3 </k> <JP>", &cells).as_deref(),
            Some(
                "the pattern names <IF>, <JP>, which are no cells of the configuration; the \
                 configuration declares: <k>, <regs>"
            )
        );
        assert_eq!(
            unknown_cells("</IF>", &cells).as_deref(),
            Some(
                "the pattern names <IF>, which is no cell of the configuration; the configuration \
                 declares: <k>, <regs>"
            )
        );
        assert_eq!(
            unknown_cells("<k> 1 +* </k> <regs> R </regs>", &cells),
            None
        );
    }

    /// FB-51: the rendered witness names the author's variables by name, keeps depth and rules,
    /// says it is printed (`rendering`), and shows a forged KORE text that does not parse as
    /// KORE with the parser's error rather than refusing the document.
    #[test]
    fn a_rendered_witness_prints_its_facts() {
        let k = "Lbl'-LT-'k'-GT-'";
        let reader = EndReader::with_symbols(
            &[k],
            &[k],
            [
                "Lbl'Unds'Map'Unds'",
                "Lbl'UndsPipe'-'-GT-Unds'",
                "Lbl'Stop'Map",
            ],
            ["Lbl'Unds'List'Unds'", "LblListItem", "Lbl'Stop'List"],
        );
        let facts = json!({
            "depth": 2,
            "state": "Lbl'-LT-'k'-GT-'{}(\\dv{SortInt{}}(\"1\"))",
            "bindings": [{"variable": "VarN:SortInt{}", "value": "not kore ("}],
            "rules": ["M.labelled"],
        });
        let rendered = rendered_witness(&facts, &lowered(), &reader);
        assert_eq!(rendered["depth"], 2);
        assert_eq!(rendered["rules"], json!(["M.labelled"]));
        assert_eq!(rendered["rendering"], "k");
        assert_eq!(rendered["note"], SEARCH_WITNESS_NOTE);
        assert_eq!(rendered["bindings"][0]["variable"], "N");
        let value = &rendered["bindings"][0]["value"];
        assert_eq!(value["rendering"], "kore", "{rendered:#}");
        assert!(
            value["note"].as_str().unwrap().contains("does not parse"),
            "{rendered:#}"
        );
        let cells = rendered["state"]["cells"].as_array().unwrap();
        assert_eq!(cells.len(), 1, "{rendered:#}");
        assert_eq!(cells[0]["path"], json!(["<k>"]));
        let absent = json!({"absent": "why"});
        let stopped = rendered_witness(
            &json!({"depth": 0, "state": "Lbl'-LT-'k'-GT-'{}()", "bindings": absent, "rules": null}),
            &lowered(),
            &reader,
        );
        assert_eq!(stopped["bindings"], absent);
        assert_eq!(stopped["note"], STOPPED_WITNESS_NOTE);
    }

    #[test]
    fn a_match_on_a_state_not_shown_defined_is_not_a_hit() {
        let outcome = run(response(vec![decided_match()], vec![]), &|_| {
            Err(format!(
                "k-rust does not show its term defined ({UNDEFINED_STATE})"
            ))
        });
        incomplete(&outcome, UNDEFINED_STATE);
        incomplete(&outcome, "is not a decided match");
    }

    #[test]
    fn a_conditional_or_diagnosed_match_is_not_a_hit() {
        let diagnostic = || BackendDiagnosticOutput::SimplificationBudgetExhausted {
            limit: 3,
            subject: BudgetSubjectOutput::Predicates,
        };
        let mut constrained = decided_match();
        constrained.constraints = vec![kore(r"\top{SortBool{}}()")];
        let mut diagnosed = decided_match();
        diagnosed.diagnostics = vec![diagnostic()];
        let mut path = decided_match();
        path.state.diagnostics = vec![diagnostic()];
        let mut predicate = decided_match();
        predicate.state.state = kore(
            r"\and{SortGeneratedTopCell{}}(Lbl'-LT-'k'-GT-'{}(), \top{SortGeneratedTopCell{}}())",
        );
        for (found, cause) in [
            (constrained, "under a condition k-rust did not decide"),
            (diagnosed, "matching it emitted a backend diagnostic"),
            (path, "its path emitted a backend diagnostic"),
            (predicate, "the state is a And pattern"),
        ] {
            // The definedness check is not what refuses these.
            incomplete(&run(response(vec![found], vec![]), &always), cause);
        }
    }

    /// KINK-HOOKED-VP-QUERY-HIT (final review S2): a match beside a hook application k-rust
    /// left unevaluated is not a hit, whatever list names it, and a completed exploration beside
    /// one gives no `no` (review N2). Before the fix both matches were hits and both explorations
    /// `Complete`.
    #[test]
    fn a_match_beside_an_unevaluated_hook_is_not_a_hit() {
        let record = || UnevaluatedHookOutput {
            hook: "FOO.bar".into(),
            reason: "unsupported".into(),
            observed_in: ObservedInOutput::Run,
        };
        let lists: [fn(&mut KorePatternSearchResponse) -> &mut Vec<UnevaluatedHookOutput>; 2] = [
            |response| &mut response.unsupported_hooks,
            |response| &mut response.allowance_refusals,
        ];
        for list in lists {
            let mut hooked = response(vec![decided_match()], vec![]);
            list(&mut hooked).push(record());
            let outcome = run(hooked, &always);
            incomplete(&outcome, UNSUPPORTED_HOOK);
            incomplete(&outcome, "FOO.bar");
            // Review N2: a completed exploration beside such a hook is not complete either, so it
            // gives no `no` whatever the program's baseline run met (before: `Complete`).
            let mut complete = response(vec![], vec![]);
            list(&mut complete).push(record());
            let outcome = run(complete, &always);
            incomplete(&outcome, UNSUPPORTED_HOOK);
            incomplete(&outcome, "FOO.bar");
        }
        assert_eq!(
            run(response(vec![], vec![]), &always),
            SearchOutcome::Complete { smt_unknowns: 0 }
        );
    }

    /// kink27 R3-CENSUS-RUNLEVEL (gap G1): a completed exploration whose response lists a value
    /// the definition leaves open gives no `no`, since another model of that value may reach the
    /// pattern; a decided match is still a hit, as a match without a mark on its own path matches
    /// on that path in every such model. Before the fix the exploration was `Complete`.
    #[test]
    fn a_search_that_read_an_open_value_gives_no_no() {
        let mark = || {
            vec![ChosenValueOutput {
                hook: "MAP.keys_list".into(),
                class: "order".into(),
            }]
        };
        let mut complete = response(vec![], vec![]);
        complete.implementation_chosen_values = mark();
        let outcome = run(complete, &always);
        incomplete(&outcome, IMPLEMENTATION_CHOSEN_VALUE);
        incomplete(&outcome, "MAP.keys_list");
        let mut matched = response(vec![decided_match()], vec![]);
        matched.implementation_chosen_values = mark();
        assert!(
            matches!(run(matched, &always), SearchOutcome::Hit(_)),
            "a decided match is a hit"
        );
        // An empty list is no mark.
        assert_eq!(
            run(response(vec![], vec![]), &always),
            SearchOutcome::Complete { smt_unknowns: 0 }
        );
    }

    #[test]
    fn an_initial_state_without_instance_gives_no_answer() {
        let mut bottom = response(vec![], vec![]);
        bottom.initial_bottom = true;
        incomplete(&run(bottom, &always), "initial_bottom");
        // Even beside a match (k-rust gives none then), it is not a hit.
        let mut both = response(vec![decided_match()], vec![]);
        both.initial_bottom = true;
        incomplete(&run(both, &always), "initial_bottom");
    }

    /// KINK-query-no-z3: a completed exploration carries the undecided solver answers the search
    /// received, which [`judge`] reads; an incomplete one and a hit are what they are without it.
    #[test]
    fn a_complete_exploration_carries_the_searchs_undecided_answers() {
        let counted = |response, smt_unknowns| {
            outcome(
                Ok(response),
                smt_unknowns,
                false,
                Budget::default(),
                &lowered(),
                &BTreeMap::new(),
                &always,
                &|_| None,
            )
        };
        assert_eq!(
            counted(response(vec![], vec![]), 3),
            SearchOutcome::Complete { smt_unknowns: 3 }
        );
        assert!(matches!(
            counted(response(vec![decided_match()], vec![]), 3),
            SearchOutcome::Hit(_)
        ));
        incomplete(
            &counted(
                response(
                    vec![],
                    vec![IncompleteSearchOutput::DepthBound {
                        state: reached(configuration(), 3),
                    }],
                ),
                3,
            ),
            "max_depth",
        );
    }

    /// An exploration is complete only when its incomplete list is empty; each entry names its
    /// cause, a simplification that stopped for lack of stack apart from one that failed
    /// otherwise.
    #[test]
    fn a_complete_exploration_has_no_incomplete_entry() {
        assert_eq!(
            run(response(vec![], vec![]), &always),
            SearchOutcome::Complete { smt_unknowns: 0 }
        );
        incomplete(
            &run(
                response(
                    vec![],
                    vec![IncompleteSearchOutput::DepthBound {
                        state: reached(configuration(), 3),
                    }],
                ),
                &always,
            ),
            "max_depth",
        );
        let simplification = |error| IncompleteSearchOutput::Simplification {
            state: reached(configuration(), 1),
            error,
        };
        incomplete(
            &run(
                response(
                    vec![],
                    vec![simplification(SearchFailureOutput::StackExhausted)],
                ),
                &always,
            ),
            "stopped for lack of native stack (stack-exhausted)",
        );
        let failed = run(
            response(
                vec![],
                vec![simplification(SearchFailureOutput::ConflictingResults {
                    rules: vec!["r".into()],
                })],
            ),
            &always,
        );
        incomplete(&failed, "a state's simplification failed");
        assert!(
            !matches!(&failed, SearchOutcome::Incomplete(why) if why.contains("stack-exhausted")),
            "{failed:?}"
        );
    }

    #[test]
    fn a_fired_watchdog_leaves_no_answer() {
        let fired = outcome(
            Ok(response(vec![decided_match()], vec![])),
            0,
            true,
            Budget::default(),
            &lowered(),
            &BTreeMap::new(),
            &always,
            &|_| None,
        );
        incomplete(&fired, "time_ms");
        // The clock's stop is stated as such, not read from the cause's words.
        assert!(matches!(fired, SearchOutcome::ClockStopped(_)), "{fired:?}");
    }

    /// CF-03: a completed exploration of a definition whose short-circuit analysis flags a rule
    /// gives a `no` exactly when the search's `shortCircuitReadings` list holds no entry that
    /// counts, as kink-campaign judges a run's list: an entry of a flagged rule's work, or of no
    /// rule's, keeps it incomplete with the entry named (rule, operator, outcome, operand); an
    /// entry of an unflagged rule's work on a ground search does not; a backend that lists no
    /// readings gives none; a definition the analysis clears ignores the list, unless the
    /// program's initial state applies a reading-dependent function, whose search is judged by
    /// the same entries on every definition; and a decided match is a hit whatever the list
    /// holds.
    #[test]
    fn a_search_that_read_a_skipped_operand_gives_no_no() {
        let flagged = DefinitionExclusions {
            short_circuit_rules: std::iter::once("at".to_owned()).collect(),
            short_circuit_results: vec!["at".to_owned()],
            ..DefinitionExclusions::default()
        };
        let clear = DefinitionExclusions::default();
        let entry = |rule: Option<&str>| ShortCircuitReadingOutput {
            operator: Some("BOOL.andThen".into()),
            outcome: ReadingOutcomeOutput::Undefined,
            head: Some("Lbl'Unds-GT-'Int'Unds'".into()),
            operand: kore("VarX:SortBool{}"),
            rewrite_rule_id: rule.map(str::to_owned),
            rewrite_rule_label: rule.map(|rule| format!("M.{rule}")),
            rewrite_rule_origin: None,
            observed_in: ObservedInOutput::Run,
        };
        let judged_with = |exclusions: &DefinitionExclusions,
                           list: Vec<ShortCircuitReadingOutput<Pattern>>,
                           listed: bool,
                           ground: bool,
                           state: bool,
                           matches| {
            let mut response = response(matches, vec![]);
            response.short_circuit_readings = list;
            outcome(
                Ok(response),
                0,
                false,
                Budget::default(),
                &lowered(),
                &BTreeMap::new(),
                &always,
                &|readings| readings_cause(exclusions, readings, listed, ground, &|| state),
            )
        };
        let judged = |exclusions: &DefinitionExclusions, list, listed, ground, matches| {
            judged_with(exclusions, list, listed, ground, false, matches)
        };
        let counted = judged(&flagged, vec![entry(Some("at"))], true, true, vec![]);
        incomplete(&counted, SHORT_CIRCUIT_READING);
        incomplete(&counted, "the work of rule M.at");
        incomplete(
            &counted,
            "the operand of BOOL.andThen after its deciding one",
        );
        incomplete(&counted, "undefined");
        incomplete(
            &judged(&flagged, vec![entry(None)], true, true, vec![]),
            "work of no rule",
        );
        assert_eq!(
            judged(&flagged, vec![entry(Some("other"))], true, true, vec![]),
            SearchOutcome::Complete { smt_unknowns: 0 },
            "an unflagged rule's entry on a ground search counts not"
        );
        incomplete(
            &judged(&flagged, vec![entry(Some("other"))], true, false, vec![]),
            "the work of rule M.other",
        );
        assert_eq!(
            judged(&flagged, vec![], true, true, vec![]),
            SearchOutcome::Complete { smt_unknowns: 0 },
            "an empty list on a backend that lists readings"
        );
        incomplete(
            &judged(&flagged, vec![], false, true, vec![]),
            "lists no short-circuit readings",
        );
        assert_eq!(
            judged(&clear, vec![entry(None)], true, true, vec![]),
            SearchOutcome::Complete { smt_unknowns: 0 },
            "a definition the analysis clears does not read the list"
        );
        assert!(matches!(
            judged(
                &flagged,
                vec![entry(Some("at"))],
                true,
                true,
                vec![decided_match()]
            ),
            SearchOutcome::Hit(_)
        ));
        // An initial state that applies a reading-dependent function is judged by the same
        // entries, whatever the analysis flags elsewhere.
        let of_state = judged_with(&clear, vec![entry(None)], true, true, true, vec![]);
        incomplete(&of_state, "the program's initial state applies");
        incomplete(&of_state, "work of no rule");
        for exclusions in [&clear, &flagged] {
            assert_eq!(
                judged_with(exclusions, vec![], true, true, true, vec![]),
                SearchOutcome::Complete { smt_unknowns: 0 },
                "a state whose search lists nothing is judged"
            );
            assert_eq!(
                judged_with(
                    exclusions,
                    vec![entry(Some("other"))],
                    true,
                    true,
                    true,
                    vec![]
                ),
                SearchOutcome::Complete { smt_unknowns: 0 },
                "an unflagged rule's entry on a ground search counts not against the state"
            );
            incomplete(
                &judged_with(exclusions, vec![], false, true, true, vec![]),
                "lists no short-circuit readings",
            );
        }
    }

    /// A state's KORE JSON envelope, which the tests below edit.
    fn json_of(pattern: &Pattern) -> Value {
        kore_json::to_value(pattern).unwrap()
    }

    /// The pattern of a KORE JSON term, in its envelope or not.
    fn pattern_of(value: &Value) -> Pattern {
        let envelope = if value.get("format").is_some() {
            value.clone()
        } else {
            json!({"format": "KORE", "version": 1, "term": value})
        };
        from_value(&envelope).unwrap()
    }

    /// The KORE term of a state's JSON, without its envelope.
    fn term(value: &Value) -> &Value {
        value.get("term").unwrap_or(value)
    }

    /// calc's searcher and the state its search for `<k> 3 </k>` reached from `add` (a real
    /// defined configuration), given to `body` on a thread with the command's stack.
    fn on_calc(body: impl FnOnce(&Searcher, Pattern) + Send + 'static) {
        std::thread::Builder::new()
            .stack_size(kink_corpus::cli::DEFINITION_STACK_BYTES)
            .spawn(move || {
                let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/flow/calc");
                let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
                let (_, admitted) = crate::admit::admit_spec(&manifest);
                let (spec, mut inputs) = admitted.expect("calc is admitted");
                let main = &manifest.spec.main_module;
                let mut searcher = Searcher::new(&spec, main, manifest.budget).unwrap();
                let lowered = Lowering::new(&spec, main)
                    .unwrap()
                    .lower("<k> 3 </k>", searcher.definition())
                    .unwrap();
                let program = manifest.programs.iter().find(|p| p.id == "add").unwrap();
                let mut inputs = inputs.session(&spec);
                let case = inputs.read(program).unwrap();
                let test = inputs.test_case(program, &case).unwrap();
                let mut response = searcher
                    .backend
                    .search_pattern_kore(SearchPatternRequest {
                        state: test.initial_state.clone(),
                        pattern: lowered.target.clone(),
                        module_name: None,
                        search_type: SearchTypeArg::All,
                        max_depth: Some(manifest.budget.max_depth),
                        max_breadth: None,
                        max_results: Some(1),
                        max_simplification_iterations: SIMPLIFICATION_ITERATIONS,
                        schema_version: BACKEND_SCHEMA_VERSION,
                    })
                    .unwrap();
                let state = response.matches.swap_remove(0).state.state;
                assert!(matches!(state, Pattern::Application { .. }), "{state}");
                body(&searcher, state);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// `state` with the symbol of every application named `from` renamed `to`.
    fn rename(state: &Value, from: &str, to: &str) -> Value {
        match state {
            Value::Object(object) => Value::Object(
                object
                    .iter()
                    .map(|(key, value)| {
                        let value = if key == "name" && value == from && object["tag"] == "App" {
                            json!(to)
                        } else {
                            rename(value, from, to)
                        };
                        (key.clone(), value)
                    })
                    .collect(),
            ),
            Value::Array(items) => {
                Value::Array(items.iter().map(|v| rename(v, from, to)).collect())
            }
            other => other.clone(),
        }
    }

    /// The first argument of the state's top cell: calc's `<k>` cell.
    fn k_cell(state: &mut Value) -> &mut Value {
        let root = if state.get("format").is_some() {
            &mut state["term"]
        } else {
            state
        };
        assert_eq!(root["name"], "Lbl'-LT-'generatedTop'-GT-'", "{root:#}");
        let cell = &mut root["args"][0];
        assert_eq!(cell["name"], "Lbl'-LT-'k'-GT-'", "{cell:#}");
        cell
    }

    #[track_caller]
    fn not_defined(result: Result<(), String>, cause: &str) {
        match result {
            Err(why) => assert!(why.contains(cause), "{why}"),
            Ok(()) => panic!("expected a state not shown defined ({cause:?}), got Ok"),
        }
    }

    /// The seam run on the caller's stack.
    fn here(
        _: &Pattern,
        work: &dyn Fn() -> Result<bool, String>,
    ) -> Result<Result<bool, String>, DefinitionError> {
        Ok(work())
    }

    /// F-18 tail: every failure arm of `defined_state` is not-defined, never defined. A state
    /// naming a symbol calc does not declare does not verify; a k-rust panic and a refused stack
    /// (the seam, on calc's real defined state and on the unverifiable one) are each `Err`; and
    /// through `outcome` each is an unknown, while the real defined state is a hit.
    #[test]
    fn a_state_whose_definedness_kink_cannot_read_is_not_a_hit() {
        on_calc(|searcher, state| {
            let definition = searcher.definition();
            // The control: calc's reached state is defined, on the real stack and on the seam's.
            assert_eq!(defined_state(definition, &state), Ok(()));
            assert_eq!(defined_state_with(definition, &state, &here), Ok(()));
            let undeclared = pattern_of(&rename(
                &json_of(&state),
                "Lbl'-LT-'k'-GT-'",
                "Lblundeclared'Unds'symbol",
            ));
            assert_ne!(undeclared, state);
            not_defined(
                defined_state(definition, &undeclared),
                "does not internalize",
            );
            let panics: StackFor<'_> = &|_, _| panic!("a k-rust panic (test)");
            let refuses: StackFor<'_> = &|_, _| {
                Err(DefinitionError::InsufficientStack {
                    depth: 1 << 20,
                    required: 8 << 30,
                    limit: 4 << 30,
                })
            };
            let cases: [(&str, StackFor<'_>, &Pattern, Option<&str>); 6] = [
                ("defined", &here, &state, None),
                (
                    "undeclared",
                    &here,
                    &undeclared,
                    Some("does not internalize"),
                ),
                ("panic", panics, &state, Some("panicked")),
                ("panic, undeclared", panics, &undeclared, Some("panicked")),
                ("no stack", refuses, &state, Some("no stack")),
                (
                    "no stack, undeclared",
                    refuses,
                    &undeclared,
                    Some("no stack"),
                ),
            ];
            for (name, stack_for, subject, cause) in cases {
                let result = defined_state_with(definition, subject, stack_for);
                let mut found = decided_match();
                found.state.state = subject.clone();
                let outcome = run(response(vec![found], vec![]), &|s| {
                    defined_state_with(definition, s, stack_for)
                });
                match cause {
                    None => {
                        assert_eq!(result, Ok(()), "{name}");
                        assert!(
                            matches!(outcome, SearchOutcome::Hit(_)),
                            "{name}: {outcome:?}"
                        );
                    }
                    Some(cause) => {
                        not_defined(result, cause);
                        incomplete(&outcome, cause);
                        incomplete(&outcome, "so its definedness is not known");
                    }
                }
            }
        });
    }

    /// F-18 tail: a term-level `\and` anywhere in the state, below the root included, is not
    /// shown defined (`undefined-state`), although k-rust's `ground_defined` alone accepts it.
    #[test]
    fn a_state_holding_a_conjunction_is_not_a_hit() {
        on_calc(|searcher, state| {
            let definition = searcher.definition();
            let state = json_of(&state);
            let mut nested = state.clone();
            let cell = k_cell(&mut nested);
            let conjunct = cell.clone();
            *cell = json!({
                "tag": "And",
                "sort": {"tag": "SortApp", "name": "SortKCell", "args": []},
                "patterns": [conjunct.clone(), conjunct],
            });
            let nested = pattern_of(&nested);
            not_defined(defined_state(definition, &nested), "term-level \\and");
            not_defined(defined_state(definition, &nested), UNDEFINED_STATE);
            // What the refusal adds: the conjunction verifies, internalizes and is ground_defined.
            let free = definition.with_stack_for(&[&nested], || {
                definition
                    .verify_standalone_pattern(&nested, &[])
                    .and_then(|admitted| admitted.internalize_term())
                    .map(|term| definition.ground_defined(&term))
                    .map_err(|e| e.to_string())
            });
            assert_eq!(free.map_err(|e| e.to_string()), Ok(Ok(true)));
            // The same conjunction at the root.
            let root = term(&state).clone();
            let top = json!({"tag": "SortApp", "name": "SortGeneratedTopCell", "args": []});
            let at_root = json!({"tag": "And", "sort": top, "patterns": [root.clone(), root]});
            not_defined(
                defined_state(definition, &pattern_of(&at_root)),
                "term-level \\and",
            );
            // An associative application of `\and` below the root.
            let mut assoc = state.clone();
            let cell = k_cell(&mut assoc);
            let conjunct = cell.clone();
            *cell = json!({
                "tag": "LeftAssoc",
                "symbol": "\\and",
                "sorts": [{"tag": "SortApp", "name": "SortKCell", "args": []}],
                "argss": [conjunct.clone(), conjunct],
            });
            not_defined(
                defined_state(definition, &pattern_of(&assoc)),
                "term-level \\and",
            );
            // Through `outcome`: an unknown with undefined-state, not a hit.
            let mut found = decided_match();
            found.state.state = nested.clone();
            let outcome = run(response(vec![found], vec![]), &|s| {
                defined_state(definition, s)
            });
            incomplete(&outcome, UNDEFINED_STATE);
        });
    }

    /// The digests of the calc and loop fixtures' patterns, as every cached answer's key names
    /// them: a change to how a single pattern is decoded, lowered or digested moves them, and
    /// every record cached under them with it.
    #[test]
    fn the_fixture_pattern_digests_are_pinned() {
        const PINNED: [(&str, &str, &str); 7] = [
            (
                "calc",
                "result-three",
                "a585d2cf629504e1272931036566d3324ffd48219377fa22ad71569f1c4800cb",
            ),
            (
                "calc",
                "result-four",
                "ace32289902c3f9dc876da649c5c6eccf24a1bafe317aedff6b8bdfa10d23846",
            ),
            (
                "calc",
                "result-above-five",
                "02f22d51e1cc4d2ef97f4cc7ad04ea9ad73310f361718c5302a9fecc1c09cf3f",
            ),
            (
                "calc",
                "adding-one-and-two",
                "8465d1ac59de5e8e4d8beb7cf04be9e1d6bab4520cc6056c62afaa57bdbe0467",
            ),
            (
                "loop",
                "countdown-starts",
                "0dfeff8f745a06e62a566e64e4cce1d4f9298c5428ce9a9b21cf5115d2d56ea3",
            ),
            (
                "loop",
                "zero",
                "c4a7081c857f2d94092eae80b2724b2e7688da4ddd4a3c1b446f4725b2abeaa6",
            ),
            (
                "loop",
                "spin-five",
                "7e5ae33ee0d2260b5c9389a99f0691e2e9de279bc816adafc06f907f96e9e15e",
            ),
        ];
        std::thread::Builder::new()
            .stack_size(kink_corpus::cli::DEFINITION_STACK_BYTES)
            .spawn(|| {
                for fixture in ["calc", "loop"] {
                    let dir = Path::new(env!("CARGO_MANIFEST_DIR"))
                        .join("../../testdata/flow")
                        .join(fixture);
                    let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
                    let list = PatternList::read(&dir.join("PATTERNS.toml")).unwrap();
                    let (_, admitted) = crate::admit::admit_spec(&manifest);
                    let (spec, _) = admitted.expect("the fixture is admitted");
                    let main = &manifest.spec.main_module;
                    let searcher = Searcher::new(&spec, main, manifest.budget).unwrap();
                    let lowering = Lowering::new(&spec, main).unwrap();
                    for entry in &list.patterns {
                        let lowered = lowering
                            .lower(entry.single().unwrap(), searcher.definition())
                            .unwrap();
                        let pinned = PINNED
                            .iter()
                            .find(|(at, id, _)| *at == fixture && *id == entry.id)
                            .unwrap_or_else(|| panic!("{fixture} {} is pinned", entry.id));
                        assert_eq!(
                            lowered.digest.to_string(),
                            pinned.2,
                            "{fixture} {}",
                            entry.id
                        );
                    }
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// A pattern is lowered to the target the search reads, and admitted as the search admits
    /// it (`Admitted::as_match_target`): `@_` compiles to a set variable matching binds, so
    /// `<k> @_ </k>` lowers and finds the state `add` reaches; a set variable written twice is
    /// refused by the lowering as the search refuses it.
    #[test]
    fn a_pattern_is_admitted_as_its_search_admits_it() {
        std::thread::Builder::new()
            .stack_size(kink_corpus::cli::DEFINITION_STACK_BYTES)
            .spawn(|| {
                let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/flow/calc");
                let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
                let (_, admitted) = crate::admit::admit_spec(&manifest);
                let (spec, mut inputs) = admitted.expect("calc is admitted");
                let main = &manifest.spec.main_module;
                let mut searcher = Searcher::new(&spec, main, manifest.budget).unwrap();
                let lowering = Lowering::new(&spec, main).unwrap();
                let lowered = lowering
                    .lower("<k> @_ </k>", searcher.definition())
                    .expect("a once-occurring set variable is a match target's");
                assert!(
                    !lowered.generated.is_empty(),
                    "`@_` is a generated variable"
                );
                let program = manifest.programs.iter().find(|p| p.id == "add").unwrap();
                let mut inputs = inputs.session(&spec);
                let case = inputs.read(program).unwrap();
                let test = inputs.test_case(program, &case).unwrap();
                let (outcome, _) = searcher.search(&test.initial_state, &lowered);
                assert!(
                    matches!(outcome, SearchOutcome::Hit(_)),
                    "`<k> @_ </k>` matches a state of `add`: {outcome:?}"
                );
                let refused = lowering
                    .lower("<k> @X ~> @X </k>", searcher.definition())
                    .expect_err("a set variable written twice is no match target");
                assert!(refused.contains("SetVariable"), "{refused}");
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
