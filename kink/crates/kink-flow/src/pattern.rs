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
//!   no such hook, kink-native `state_references_implementation_chosen`); and the build is not the
//!   Z3 profile. Another model of an open value could reach the pattern, so a `no` is relative to
//!   the definition only when no implementation-chosen value is in play.
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
//!   stack stop, a baseline run that is not comparable, the Z3 profile.
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
    manifest::{Budget, FlowManifest, ManifestError},
    results::{SIMPLIFICATION_ITERATIONS, sentence_value},
};
use k_rust::backend::ShortCircuitReadingOutput;
use k_rust::{
    backend::{
        BACKEND_SCHEMA_VERSION, Backend, BackendError, BackendOptions, IncompleteSearchOutput,
        KorePatternSearchResponse, SearchFailureOutput, SearchMatchOutput, SearchPatternRequest,
        SearchTypeArg,
    },
    definition::{AttributeKey, Attributes, ResolvedDefinition},
    k_rust_backend::{
        definition::{BackendDefinition, DefinitionError},
        stop::{CancellationToken, StopCause},
    },
    kompile::{ProgramGrammar, compile_search_pattern},
    kore::{
        ast::{Associativity, Pattern},
        json as kore_json,
        parser::parse_definition,
    },
};
use kink_native::{
    coverage::{Authorship, RuleAuthors},
    exclusion::{DefinitionExclusions, Exclusion, state_references_implementation_chosen},
    execution::{RunFacts, SolverProfile},
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
            format!(
                "{e} (a position `{PATTERN_SOURCE}:LINE:COLUMN` is a line and column of the \
                 pattern's text, its surrounding whitespace removed, not of the pattern list's \
                 file)"
            )
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
        Ok(LoweredPattern {
            target: compiled.pattern,
            generated,
            digest,
        })
    }
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
}

/// [`Facts::no_data`] of `data`: the gate `run` and `results` read for an end
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
        SearchOutcome::Incomplete(cause) => Answer::unknown(cause.clone()),
        SearchOutcome::Complete => {
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
        let (result, fired) = watchdog(time, || self.backend.search_pattern_kore(request));
        let definition = &self.definition;
        let exclusions = &self.exclusions;
        let outcome = outcome(
            result,
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

fn cut(text: String) -> Value {
    if text.chars().count() > WITNESS_CUT {
        json!({"kore": text.chars().take(WITNESS_CUT).collect::<String>(), "truncated": true})
    } else {
        json!({"kore": text, "truncated": false})
    }
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

/// The search's outcome (module docs: what makes a match decided and an exploration complete).
/// `defined` decides whether a decided match's state is defined ([`defined_state`] on the
/// searcher's definition; the unit tests pass their own); `readings` says why the search's
/// `shortCircuitReadings` list keeps a completed exploration from being complete, or `None`
/// ([`readings_cause`] on the searcher's definition).
fn outcome(
    result: Result<KorePatternSearchResponse, BackendError>,
    fired: bool,
    budget: Budget,
    lowered: &LoweredPattern,
    rule_names: &BTreeMap<String, String>,
    defined: &dyn Fn(&Pattern) -> Result<(), String>,
    readings: &dyn Fn(Vec<ShortCircuitReadingOutput<Pattern>>) -> Option<String>,
) -> SearchOutcome {
    let clock = || {
        SearchOutcome::Incomplete(format!(
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
                 {why}; the search stops at its first match, so no other state was asked",
                found.state.depth
            )),
        };
    }
    if !response.incomplete.is_empty() {
        return SearchOutcome::Incomplete(incomplete_cause(&response.incomplete, budget));
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
    SearchOutcome::Complete
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
                "value": cut(binding.value.to_string()),
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
        "state": cut(state.state.to_string()),
        "bindings": bindings,
        "rules": rules,
        "rendering": "kore",
        "note": "the state and the bindings are KORE text (query does not print them through \
                 krs-unparse, the K-text printer kill evidence uses); rules name the rewrite steps \
                 of one path from the initial state to the matching state, each by its label, else \
                 by the file and line of the rule written for it, else by its compiled id",
    })
}

/// The cause of an incomplete exploration, from k-rust's incomplete entries.
fn incomplete_cause(incomplete: &[IncompleteSearchOutput<Pattern>], budget: Budget) -> String {
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
            I::Match { .. } => "a state's match against the pattern was left undecided".to_owned(),
            I::Smt { .. } => "a solver query failed or was undecided".to_owned(),
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
            SearchOutcome::Incomplete(why) => assert!(why.contains(cause), "{why}"),
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

    /// A hit's witness names the state and the bindings as KORE text and the path's rewrite
    /// steps by label, else by the rule name kink knows for the id, else by the id; a binding of
    /// a generated variable is left out.
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
        assert_eq!(
            witness["state"],
            json!({"kore": "Lbl'-LT-'k'-GT-'{}()", "truncated": false})
        );
        assert_eq!(
            witness["bindings"],
            json!([{
                "variable": "VarN:SortInt{}",
                "value": {"kore": r#"\dv{SortInt{}}("3")"#, "truncated": false},
            }])
        );
        assert_eq!(witness["rules"], json!(["M.labelled", "lib.rs:7", "c"]));
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
            SearchOutcome::Complete
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
            SearchOutcome::Complete
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

    /// An exploration is complete only when its incomplete list is empty; each entry names its
    /// cause, a simplification that stopped for lack of stack apart from one that failed
    /// otherwise.
    #[test]
    fn a_complete_exploration_has_no_incomplete_entry() {
        assert_eq!(
            run(response(vec![], vec![]), &always),
            SearchOutcome::Complete
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
            true,
            Budget::default(),
            &lowered(),
            &BTreeMap::new(),
            &always,
            &|_| None,
        );
        incomplete(&fired, "time_ms");
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
            SearchOutcome::Complete,
            "an unflagged rule's entry on a ground search counts not"
        );
        incomplete(
            &judged(&flagged, vec![entry(Some("other"))], true, false, vec![]),
            "the work of rule M.other",
        );
        assert_eq!(
            judged(&flagged, vec![], true, true, vec![]),
            SearchOutcome::Complete,
            "an empty list on a backend that lists readings"
        );
        incomplete(
            &judged(&flagged, vec![], false, true, vec![]),
            "lists no short-circuit readings",
        );
        assert_eq!(
            judged(&clear, vec![entry(None)], true, true, vec![]),
            SearchOutcome::Complete,
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
                SearchOutcome::Complete,
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
                SearchOutcome::Complete,
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
