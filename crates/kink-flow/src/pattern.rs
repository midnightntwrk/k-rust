//! Per-input pattern checks (flow F-18): does some run of a corpus program, from its input, reach
//! a state that matches a pattern written in K? The LLM proposes a pattern it thinks a test should
//! hit and writes a program meant to hit it; kink validates the claim (an anti-hallucination check)
//! and caches the answer ([`crate::query`]). The initial state, every reached state and the final
//! states all count. "Every path hits" is not asked (`draft/goal/README.md`, "Pattern queries").
//!
//! **`PATTERNS.toml`** ([`PatternList`]): `[[pattern]]` entries with a unique non-empty `id`, a
//! `pattern` and optional `programs` (the corpus programs the author claims hit it: the per-input
//! claims; absent, every program of the corpus is asked) and `note`. Decoding is strict, as for
//! `FLOW.toml` and `MUTATIONS.toml`: an unknown key, a value of the wrong type, a duplicate or empty
//! id or program id, and a claimed program the manifest does not have are errors naming the key.
//!
//! **Lowering** ([`Lowering`]). A pattern is K text, parsed by the specification's own grammar: it
//! is compiled by k-rust's public `kompile::compile_search_pattern` (the compiler `krun --pattern`
//! uses), which parses the text as the content of a rule (`#RuleContent`) in the main module's
//! rule grammar of the admitted definition and lowers it with the passes a rule's left-hand side
//! goes through (anonymous variables, semantic casts, cell completion, macro expansion, sort
//! injection as a left-hand side) against the execution definition of the specification's own
//! compile (`CompiledKoreArtifacts::execution_definition`, which k-rust documents as the context a
//! standalone surface pattern must use). The KORE target is `\and(body, \equals(C, true)...)` for
//! each conjunct `C` of a `requires`, or `\and(body, \top)`: a `requires` is supported. k-rust
//! refuses an `ensures` and a variable that occurs only on a rewrite's right side (a pattern
//! denotes the configurations its left side matches). The compiled target must then pass the
//! backend's verified admission of a standalone pattern (`verify_standalone_pattern`), as `krun`
//! requires, so a pattern naming a symbol the baseline's compiled definition lacks is refused.
//! Any refusal is `invalid-pattern` with k-rust's message, and the pattern never runs. No overlay
//! module is loaded and the definition is not compiled again: the compile of the admission is the
//! one every program runs on.
//!
//! **Evaluation** ([`Searcher`]): one k-rust `search_pattern` per (pattern, program) on the
//! baseline, from the program's admitted initial state: search type all (`=>*`, every reachable
//! configuration, the initial one included), state set, `max_results` 1 (the search stops at the
//! first match), the manifest's `max_depth` and simplifier iterations, under kink's watchdog of
//! `budget.time_ms`. A search has no work budget at k-rust 501f18b9 (KINK-24, drafted), so the
//! clock is its only bound on a runaway program.
//!
//! **Answers** ([`judge`]):
//! - `hit`: the search returned a decided match: no condition (`constraints` empty), no
//!   diagnostic of the match or of the matching state's path, a state that carries no predicate,
//!   and the watchdog did not fire. A hit is sound even when the run read a value the definition
//!   leaves open (an implementation-chosen hook, the short-circuit reading): k-rust's choice is one
//!   model of the definition, and the claim is existential.
//! - `no`: the exploration completed (k-rust's `incomplete` list is empty and the watchdog did not
//!   fire), and also the program's baseline run, kink's plain state-set run of the same initial
//!   state under the same budget (the result cache), is `comparable`: complete and free of every
//!   exclusion kink-campaign reads (a stack stop the run counted, a load stack stop, a
//!   contradicted claim, an undefined step of the short-circuit reading, an allowance refusal);
//!   the definition passes decision 1's census and kink's other definition exclusions (no
//!   implementation-chosen hook, no rule that depends on the short-circuit reading, no condition
//!   equating two terms, no load stack stop), and so does the initial state; and the build is not
//!   the Z3 profile. Another model of an open value could reach the pattern, so a `no` is relative
//!   to the definition only when no implementation-chosen value is in play.
//! - `unknown`, with its cause, in every other case: a depth bound, the clock, an undecided step
//!   or match, a stack-exhausted state, the census, a load stack stop, a baseline run that is not
//!   comparable, the Z3 profile.
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
//! contradicted claim ends its path (an undefined step has no successor), so a witness path passes
//! through none; a `no` needs a comparable baseline run, which has none anywhere. No pattern answer
//! ever feeds a kill or a mutation verdict: pattern-only differences stay unknown by design.

use crate::{
    admit::AdmittedSpec,
    manifest::{Budget, FlowManifest, ManifestError},
    results::{SIMPLIFICATION_ITERATIONS, sentence_value},
};
use k_rust::{
    backend::{
        BACKEND_SCHEMA_VERSION, Backend, BackendError, BackendOptions, SearchPatternRequest,
        SearchTypeArg,
    },
    definition::{AttributeKey, Attributes, ResolvedDefinition},
    k_rust_backend::{
        definition::BackendDefinition,
        stop::{CancellationToken, StopCause},
    },
    kompile::{ProgramGrammar, compile_search_pattern},
    kore::{ast::Pattern, codec::from_value, json as kore_json, parser::parse_definition},
};
use kink_native::{
    coverage::{Authorship, RuleAuthors},
    exclusion::{DefinitionExclusions, Exclusion},
    execution::SolverProfile,
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

/// The lowering of a pattern's K text to its KORE target ([`Lowering`]), a component of every
/// cached answer's key: it changes whenever kink changes how a pattern's text becomes a target.
pub const LOWERING_VERSION: &str = "kink-flow/pattern-lowering/v1";
/// Domain of a pattern's digest: its KORE target and the variables the compiler generated.
pub const PATTERN_DOMAIN: &str = "kink-flow/pattern/v1";
/// The answer of a refused pattern.
pub const INVALID_PATTERN: &str = "invalid-pattern";
/// Characters of a witness state's KORE text kept in a document (as the run document cuts a
/// killer's final configurations).
pub const WITNESS_CUT: usize = 4000;
/// The search every check makes, as the cache key names it.
pub fn search_modality() -> Value {
    json!({"search_type": "all", "result_modality": "state-set", "max_results": 1})
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
    /// K text: a configuration fragment as a rule's left-hand side is written, cells completed
    /// by k-rust as for rules, optionally followed by `requires` and a condition.
    pub pattern: String,
    /// The corpus programs the author claims hit the pattern (per-input claims); `None` asks
    /// every program of the corpus.
    pub programs: Option<Vec<String>>,
    /// Free text for the reader; it enters no digest.
    pub note: Option<String>,
}

fn pattern_key(id: &str) -> String {
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
    known_keys(table, &key, &["id", "pattern", "programs", "note"])?;
    let pattern = non_empty(
        table
            .get("pattern")
            .ok_or_else(|| ManifestError::new(join(&key, "pattern"), "missing required key"))?,
        &join(&key, "pattern"),
    )?;
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
    Ok(PatternEntry {
        id,
        pattern,
        programs,
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
}

impl LoweredPattern {
    /// The target's KORE text.
    pub fn kore(&self) -> String {
        self.target.to_string()
    }
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

    /// Lower `text` (module docs), checking the target against `definition`, the baseline
    /// definition every search runs on. The error is k-rust's message.
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
        .map_err(|e| e.to_string())?;
        definition
            .verify_standalone_pattern(&compiled.pattern, &[])
            .map_err(|e| format!("the compiled pattern is not a pattern of the baseline: {e}"))?
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
        Ok(LoweredPattern {
            target: compiled.pattern,
            generated,
            digest,
        })
    }
}

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
    attributes.set(AttributeKey::Source, json!("PATTERNS.toml"));
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
    /// A decided match: the witness (`{depth, state: {kore, truncated}, bindings, rules,
    /// rendering, note}`).
    Hit(Value),
    /// The exploration completed and no state matched.
    Complete,
    /// The search found no decided answer: the cause.
    Incomplete(String),
    /// k-rust refused the search: its message.
    Failed(String),
}

/// What the answer rules read besides the search ([`judge`]).
#[derive(Clone, Copy, Debug)]
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
}

/// An answer: `hit`, `no`, `unknown`, `invalid-pattern` or `error`, with its cause (null for
/// `hit` and `no`) and its witness (a hit's).
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
            "a rule's condition or result depends on whether andBool, orBool or #if skip an \
             operand that may be undefined (short-circuit-reading): another reading could reach \
             the pattern"
        }
        Exclusion::EqualsCondition => {
            "a rule or equation has a condition equating two terms (equals-condition), a gap of \
             k-rust's answers"
        }
        Exclusion::StackStop => "the run counted a stop for lack of native stack (stack-stop)",
        Exclusion::ContradictedClaim => {
            "the run contradicts a trusted claim of the definition (contradicted-claim)"
        }
        Exclusion::AllowanceRefusal => {
            "a Bytes hook refused a result for the memory allowance (allowance-refusal)"
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
        SearchOutcome::Incomplete(cause) => Answer::unknown(cause.clone()),
        SearchOutcome::Complete => {
            let would = "the exploration completed with no match, but a no is not given";
            if let Some(exclusion) = exclusions.definition_exclusion() {
                return Answer::unknown(exclusion_cause(exclusion, would));
            }
            if let Some(exclusion) = facts.state {
                return Answer::unknown(exclusion_cause(
                    exclusion,
                    &format!("{would} (the program's initial state)"),
                ));
            }
            if facts.profile == SolverProfile::Z3 {
                return Answer::unknown(format!(
                    "{would} under the z3 profile: a solver query can time out and k-rust \
                     reports no per-run signal that one did"
                ));
            }
            match facts.baseline_class {
                Some("comparable") => Answer {
                    answer: "no",
                    cause: None,
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
            BackendOptions::default(),
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

    /// The exclusion of a program's initial state on that definition, if any.
    pub fn state_exclusion(&self, initial: &Pattern) -> Option<Exclusion> {
        self.exclusions.state_exclusion(&self.definition, initial)
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
        let started = Instant::now();
        let (result, fired) = watchdog(time, || self.backend.search_pattern_json(request));
        let wall_ms = u64::try_from(started.elapsed().as_millis()).unwrap_or(u64::MAX);
        let outcome = outcome(result, fired, self.budget, lowered, &self.rule_names);
        (outcome, wall_ms)
    }
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

/// A KORE JSON pattern as KORE text, or a note when it does not decode.
fn kore_text(value: &Value) -> String {
    let envelope = if value.get("format").is_some() {
        value.clone()
    } else {
        json!({"format": "KORE", "version": 1, "term": value})
    };
    from_value(&envelope).map_or_else(
        |e| format!("<KORE that does not decode: {e}>"),
        |pattern| pattern.to_string(),
    )
}

fn cut(text: String) -> Value {
    if text.chars().count() > WITNESS_CUT {
        json!({"kore": text.chars().take(WITNESS_CUT).collect::<String>(), "truncated": true})
    } else {
        json!({"kore": text, "truncated": false})
    }
}

/// The KORE term of a state, without its envelope.
fn term(value: &Value) -> &Value {
    value.get("term").unwrap_or(value)
}

/// The search's outcome (module docs: what makes a match decided and an exploration complete).
fn outcome(
    result: Result<String, BackendError>,
    fired: bool,
    budget: Budget,
    lowered: &LoweredPattern,
    rule_names: &BTreeMap<String, String>,
) -> SearchOutcome {
    let clock = || {
        SearchOutcome::Incomplete(format!(
            "the search did not finish within time_ms = {} (a search has no work budget at this \
             k-rust pin, so the clock bounds it)",
            budget.time_ms
        ))
    };
    let text = match result {
        Ok(text) => text,
        Err(_) if fired => return clock(),
        Err(error) if matches!(error.stop_cause(), Some(StopCause::Cancelled)) => return clock(),
        Err(error) => return SearchOutcome::Failed(format!("k-rust refused the search: {error}")),
    };
    // A token cancelled before the call returned can leave a state unsimplified (k-rust's
    // Execute promise excludes it), so nothing a cancelled search returned is an answer.
    if fired {
        return clock();
    }
    let response = match kink_patch::parse_json(&text) {
        Ok(response) => response,
        Err(error) => {
            return SearchOutcome::Failed(format!("cannot read k-rust's search result: {error}"));
        }
    };
    let incomplete = response["incomplete"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    if let Some(found) = response["matches"].as_array().and_then(|m| m.first()) {
        return match decided(found) {
            Ok(()) => SearchOutcome::Hit(witness(found, lowered, rule_names)),
            Err(why) => SearchOutcome::Incomplete(format!(
                "the first matching state the search found (depth {}) is not a decided match: \
                 {why}; the search stops at its first match, so no other state was asked",
                found["state"]["depth"]
            )),
        };
    }
    if response["initialBottom"] == true {
        return SearchOutcome::Incomplete(
            "the initial state has no instance (k-rust's initial_bottom), so no run starts"
                .to_owned(),
        );
    }
    if incomplete.is_empty() {
        return SearchOutcome::Complete;
    }
    SearchOutcome::Incomplete(incomplete_cause(&incomplete, budget))
}

/// Why a match is not a decided hit, or `Ok`.
fn decided(found: &Value) -> Result<(), String> {
    let nonempty = |value: &Value| value.as_array().is_some_and(|items| !items.is_empty());
    if nonempty(&found["constraints"]) {
        return Err("it holds under a condition k-rust did not decide".to_owned());
    }
    if nonempty(&found["diagnostics"]) {
        return Err("matching it emitted a backend diagnostic".to_owned());
    }
    if nonempty(&found["state"]["diagnostics"]) {
        return Err(
            "its path emitted a backend diagnostic (the state may not be the normal form, a \
             condition on the path was left undecided, or a hook was refused)"
                .to_owned(),
        );
    }
    let state = term(&found["state"]["state"]);
    if state["tag"] != "App" {
        return Err(format!(
            "the state is a {} pattern, not a configuration without predicates",
            state["tag"].as_str().unwrap_or("non-term")
        ));
    }
    Ok(())
}

/// Whether the KORE variable `name` is one k-rust's pattern compiler generated: one it lists
/// (`generated_anonymous_variables`), or one spelled as its fresh-name passes spell an anonymous
/// variable (`_Gen<n>`, `?_Gen<n>`, `!_Gen<n>`, `@_Gen<n>`, `_DotVar<n>`: k-rust
/// `kompile::fresh_names`). At k-rust 501f18b9 the list omits the variables that complete the
/// omitted sibling cells of a pattern, so both are read. A display rule only: no answer reads it.
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

/// A hit's witness for the reader (module docs).
fn witness(
    found: &Value,
    lowered: &LoweredPattern,
    rule_names: &BTreeMap<String, String>,
) -> Value {
    let state = &found["state"];
    let bindings = found["bindings"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|binding| {
            !term(&binding["variable"])["name"]
                .as_str()
                .is_some_and(|name| generated(lowered, name))
        })
        .map(|binding| {
            json!({
                "variable": kore_text(&binding["variable"]),
                "value": cut(kore_text(&binding["value"])),
            })
        })
        .collect::<Vec<_>>();
    let rules = state["trace"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|entry| entry["kind"] == "rewrite")
        .map(|entry| {
            entry
                .get("label")
                .and_then(Value::as_str)
                .or_else(|| {
                    let id = entry["uniqueId"].as_str()?;
                    rule_names.get(id).map(String::as_str).or(Some(id))
                })
                .map_or(Value::Null, |name| json!(name))
        })
        .collect::<Vec<_>>();
    json!({
        "depth": state["depth"],
        "state": cut(kore_text(&state["state"])),
        "bindings": bindings,
        "rules": rules,
        "rendering": "kore",
        "note": "k-rust 501f18b9 has no unparser from KORE to the specification's K syntax, so the \
                 state and the bindings are KORE text; rules name the rewrite steps of one path from the \
                 initial state to the matching state, each by its label, else by the file and \
                 line of the rule written for it, else by its compiled id",
    })
}

/// The cause of an incomplete exploration, from k-rust's incomplete entries.
fn incomplete_cause(incomplete: &[Value], budget: Budget) -> String {
    let mut kinds = BTreeSet::new();
    for entry in incomplete {
        let kind = entry
            .as_str()
            .map(str::to_owned)
            .or_else(|| entry["kind"].as_str().map(str::to_owned))
            .or_else(|| entry.as_object().and_then(|o| o.keys().next().cloned()))
            .unwrap_or_else(|| "unknown".to_owned());
        let stack = entry.to_string().contains("stack-exhausted");
        kinds.insert(match kind.as_str() {
            "depth-bound" => format!("a path reached max_depth = {}", budget.max_depth),
            "breadth-bound" => "the frontier exceeded the breadth bound".to_owned(),
            "cancelled" => format!(
                "the search did not finish within time_ms = {}",
                budget.time_ms
            ),
            "indeterminate" => "a step k-rust could not decide (indeterminate)".to_owned(),
            "simplification" if stack => {
                "a state's simplification stopped for lack of native stack (stack-exhausted)"
                    .to_owned()
            }
            "simplification" => "a state's simplification failed".to_owned(),
            "match" => "a state's match against the pattern was left undecided".to_owned(),
            "smt" => "a solver query failed or was undecided".to_owned(),
            "result-bound" => "the search stopped at its result bound".to_owned(),
            other => format!("an incomplete entry of kind {other}"),
        });
    }
    format!(
        "the exploration did not complete: {}",
        kinds.into_iter().collect::<Vec<_>>().join("; ")
    )
}
