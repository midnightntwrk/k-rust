//! kink's semantics identity and kink's build identity: what a stored verdict is bound to
//! (packets CACHE-ID and CACHE-ID-fix-1 of the k-rust 501f18b9 re-pin).
//!
//! A verdict (a mutant's status, a baseline's comparability, a program's result class) depends on
//! the k-rust revision and on all of kink's verdict code. A stored verdict may be honoured
//! without re-deriving it only if the code that derived it is the code now running. Two
//! identities say so:
//! - [`kink_build`], kink's build identity, the SHA-256 of the running executable (decision D14-1
//!   (a), kink-flow tier 1, extended to every honouring store by packet CACHE-ID-fix-1). It
//!   guards everything: the comparison and its Distinguish, the status fold, pattern-oracle
//!   matching, leaf adaptation, step events, feasibility, the census and every other piece of
//!   verdict code that has no version constant, as well as the versioned algorithms and the
//!   linked k-rust. Nothing has to be bumped for it to change;
//! - [`KINK_IDENTITY`], the semantics identity, names the versioned algorithms by their version
//!   constants: how a patch is addressed and admitted, which claims a mutant loses, whether its
//!   equations are consistent, what its edit changes, which definitions have data (each
//!   definition's full critical-pair check, fz26 KINK-BASELINE-FINDINGS), which comparisons are
//!   excluded, what execution request is sent, what counts as a comparable result, how coverage is read, when a
//!   work-bound mutant run kills one-sidedly, and the k-rust revision. [`kink_identity`] is their
//!   object, `{key: value}`. It is the human-readable part: a store from another build says
//!   which versioned algorithm differs, when one does, and the identity keeps campaign reports
//!   (which must not depend on the build) bound to the algorithms they were made with.
//!
//! Every store that is honoured without re-deriving its verdicts carries both, and is refused or
//! missed when either differs from this build's ([`writer_difference`], [`identity_difference`]):
//! - kink-corpus: each index entry and admission record names its writer's build
//!   (`kink_build`), outside the campaign report's bytes, and the report's manifest names the
//!   identity (`kink`). Resume and summary refuse an entry written by another build or under
//!   another identity; summary reads an admission record of another build as missing;
//! - kink-flow's result cache keys every record on both (`results::result_key`, members
//!   `kink_build` and `kink`);
//! - kink-flow's tier-1 outcome context holds both (`digest::outcome_context`);
//! - kink-flow's warm-path memos key every record on both (`memo::resolution_key`,
//!   `memo::census_key`, re-pin L1-4), and `run --verify` re-derives every memoised value and
//!   reports a record that differs;
//! - kink-flow's run document names both, and `kink-flow report` refuses a document that names
//!   another.
//!
//! Replay (kink-campaign `replay`, `kink-corpus replay-check`) re-derives instead: it regenerates
//! the manifest, re-runs the campaign and returns `Reproduced` only for byte-identical
//! regeneration, so it needs no build binding. It still refuses another identity in its
//! environment check (`kink.<key>`) before regenerating anything. kink-flow's killer hints
//! decide no status, so they carry neither.
//!
//! An unreadable executable gives no build identity: every honouring store then recomputes or
//! refuses, never accepts.
//!
//! The rule for adding to the semantics identity: a constant whose change can change a verdict is
//! a component here (bump the constant whenever its algorithm changes what it decides; the stores
//! then miss without further edits, and the refusal names it). Every other versioned constant (a
//! `const` or `static` whose name ends in `_VERSION` or `_DOMAIN`, whose string value ends in
//! `/v<N>`, `/v<N>.<M>` or `-v<N>`, or whose value names such a constant) is listed in
//! [`OUTSIDE_IDENTITY`] with the reason it cannot change a verdict on its own. kink-campaign's
//! `tests/identity.rs` parses every workspace member's sources and fails on a versioned constant
//! that is in neither list. Verdict code without a version constant needs no entry: the build
//! identity guards it.

use kink_patch::{Sha256Digest, sha256};
use serde_json::{Map, Value, json};
use std::{path::Path, sync::OnceLock};

/// The result schema of kink-flow's result cache: what counts as a comparable baseline result
/// and what a result record holds. It lives here so the identity can name it; kink-flow
/// re-exports it as `results::RESULT_SCHEMA_VERSION`. Bump it whenever kink-flow changes what
/// counts as a comparable result or what a record holds. v3 (flow F-13): every record carries
/// `wall_ms`, the wall time of the program's live baseline run, outside the key and the run
/// digest. v4 (re-pin R0b): a baseline run that is excluded (kink-native `exclusion`: stack
/// stops, load stack stops, a contradicted claim, an implementation-chosen hook, an allowance
/// refusal) is not comparable, and neither is a breadth-bound or role-axiom collection terminal,
/// so a v3 `comparable` record may no longer be. Since packet CACHE-ID the result key also holds
/// the whole [`kink_identity`], so a change of the exclusions (or of any other component) misses
/// without a bump here; v4 stayed through six exclusion widenings before that (re-pin R0-tail
/// review 1, minor). v5 (re-pin adoption A-1): a record holds `specification_diagnostics`, the
/// baseline run's contradicted-claim records, and `smt_unknowns`, its undecided solver answers;
/// and a baseline run whose k-rust lists hold any entry is excluded, so a v4 `comparable` record
/// may no longer be.
pub const RESULT_SCHEMA_VERSION: &str = "kink-flow/result/v5";

/// One component of [`KINK_IDENTITY`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Component {
    /// Its key in [`kink_identity`].
    pub key: &'static str,
    /// The crate that defines the constant (its package name).
    pub krate: &'static str,
    /// The constant's name in that crate.
    pub constant: &'static str,
    /// The constant's value.
    pub value: &'static str,
}

/// Every component of kink's semantics identity, in the order [`identity_difference`] reports
/// the first that differs. The k-rust revision comes last: a campaign manifest also names it in
/// its `k_rust` member, which replay checks first, and a manifest written before packet CACHE-ID
/// lacks it in `kink`, where the first kink algorithm it lacks is the more useful report.
pub const KINK_IDENTITY: [Component; 14] = [
    Component {
        key: "fingerprint",
        krate: "kink-patch",
        constant: "FINGERPRINT_DOMAIN",
        value: kink_patch::FINGERPRINT_DOMAIN,
    },
    Component {
        key: "canonical_patch",
        krate: "kink-patch",
        constant: "CANONICAL_PATCH_DOMAIN",
        value: kink_patch::CANONICAL_PATCH_DOMAIN,
    },
    Component {
        key: "compiled_kore",
        krate: "kink-patch",
        constant: "COMPILED_KORE_DOMAIN",
        value: kink_patch::COMPILED_KORE_DOMAIN,
    },
    Component {
        key: "patch_admission",
        krate: "kink-patch",
        constant: "PATCH_ADMISSION_VERSION",
        value: kink_patch::PATCH_ADMISSION_VERSION,
    },
    Component {
        key: "claim_removal",
        krate: "kink-patch",
        constant: "CLAIM_REMOVAL_VERSION",
        value: kink_patch::CLAIM_REMOVAL_VERSION,
    },
    Component {
        key: "mutant_consistency",
        krate: "kink-native",
        constant: "MUTANT_CONSISTENCY_VERSION",
        value: kink_native::consistency::MUTANT_CONSISTENCY_VERSION,
    },
    Component {
        key: "mutant_effect",
        krate: "kink-native",
        constant: "MUTANT_EFFECT_VERSION",
        value: kink_native::consistency::MUTANT_EFFECT_VERSION,
    },
    Component {
        key: "data_facts",
        krate: "kink-native",
        constant: "DATA_FACTS_VERSION",
        value: kink_native::data::DATA_FACTS_VERSION,
    },
    Component {
        key: "definition_exclusion",
        krate: "kink-native",
        constant: "DEFINITION_EXCLUSION_VERSION",
        value: kink_native::exclusion::DEFINITION_EXCLUSION_VERSION,
    },
    Component {
        key: "execution_request",
        krate: "kink-native",
        constant: "EXECUTION_REQUEST_VERSION",
        value: kink_native::execution::EXECUTION_REQUEST_VERSION,
    },
    Component {
        key: "result_schema",
        krate: "kink-campaign",
        constant: "RESULT_SCHEMA_VERSION",
        value: RESULT_SCHEMA_VERSION,
    },
    Component {
        key: "coverage",
        krate: "kink-native",
        constant: "COVERAGE_DOMAIN",
        value: kink_native::coverage::COVERAGE_DOMAIN,
    },
    Component {
        key: "one_sided",
        krate: "kink-campaign",
        constant: "ONE_SIDED_VERSION",
        value: crate::runner::ONE_SIDED_VERSION,
    },
    Component {
        key: "k_rust_revision",
        krate: "kink-native",
        constant: "K_RUST_REVISION",
        value: kink_native::K_RUST_REVISION,
    },
];

/// A versioned constant that is not a component of [`KINK_IDENTITY`], with the reason.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Outside {
    /// The crate that defines the constant (its package name).
    pub krate: &'static str,
    /// The constant's name in that crate.
    pub constant: &'static str,
    /// Why a change of it cannot change a verdict without another component or key changing.
    pub reason: &'static str,
}

/// Every versioned constant outside [`KINK_IDENTITY`]. Each reason names the path that checks
/// the constant, or says why nothing has to.
pub const OUTSIDE_IDENTITY: [Outside; 30] = [
    Outside {
        krate: "kink-patch",
        constant: "TEST_MANIFEST_DOMAIN",
        reason: "the domain of the campaign manifest's tests digest (`tests.sha256`): `kink-corpus \
                 run` recomputes it from the stored inputs before it resumes (cli.rs \
                 verify_binding), replay regenerates the manifest and requires equal text, and \
                 kink-corpus summary and `definition` resume honour only an index entry whose \
                 `kink_build` is this build",
    },
    Outside {
        krate: "kink-patch",
        constant: "OBSERVATION_DOMAIN",
        reason: "the domain of the campaign manifest's `observation_sha256`: `kink-corpus run` \
                 recomputes it from the corpus declaration before it resumes (cli.rs \
                 verify_binding), replay regenerates the manifest and requires equal text, and \
                 kink-corpus summary and `definition` resume honour only an index entry whose \
                 `kink_build` is this build",
    },
    Outside {
        krate: "kink-patch",
        constant: "CAMPAIGN_MANIFEST_DOMAIN",
        reason: "the domain of the campaign manifest's digest: every reader recomputes it from the \
                 stored manifest and requires the indexed digest (kink-corpus runner.rs resume, \
                 summary.rs read_report, cli.rs replay_check, kink-campaign replay)",
    },
    Outside {
        krate: "kink-patch",
        constant: "OPERATOR_DOMAIN",
        reason: "the domain of an operator specification's digest (`spec_sha256` in the campaign \
                 manifest): `kink-corpus run` compares every stored operator row with the corpus's \
                 specifications before it resumes (cli.rs verify_binding), replay regenerates the \
                 manifest and requires equal text, and kink-corpus summary and `definition` \
                 resume honour only an index entry whose `kink_build` is this build",
    },
    Outside {
        krate: "kink-native",
        constant: "CENSUS_DOMAIN",
        reason: "the domain of a declaration census's digest, which the campaign manifest and the \
                 admission records hold: replay regenerates the manifest and requires equal \
                 text, and kink-corpus summary and `definition` resume honour only an index entry \
                 (and summary only an admission record) whose `kink_build` is this build, whose \
                 census code wrote it",
    },
    Outside {
        krate: "kink-corpus",
        constant: "CORPUS_MANIFEST_DOMAIN",
        reason: "the domain of the corpus manifest's digest, which names the store's directory: \
                 every command recomputes it from the stored declaration and requires the \
                 directory's name (store.rs read_manifest)",
    },
    Outside {
        krate: "kink-flow",
        constant: "SPEC_DOMAIN",
        reason: "the domain of the specification digest: every kink-flow command recomputes it \
                 from the sources it loads (digest.rs spec_digest), and it enters the result key, \
                 which also holds `kink_build`, and the tier-1 execution digest",
    },
    Outside {
        krate: "kink-flow",
        constant: "EXECUTION_DIGEST_KIND",
        reason: "the kind of the tier-1 execution digest (today SPEC_DOMAIN itself): it is a member \
                 of the tier-1 context, which also holds `kink_build`, and every command \
                 recomputes the context (digest.rs outcome_context)",
    },
    Outside {
        krate: "kink-flow",
        constant: "PROGRAM_DOMAIN",
        reason: "the domain of the program digest: every kink-flow command recomputes it from the \
                 program it reads (digest.rs program_digest), and it enters the result key, which \
                 also holds `kink_build`, and the tier-1 key",
    },
    Outside {
        krate: "kink-flow",
        constant: "RUN_DOMAIN",
        reason: "the domain of a result record's `run_sha256`: `results --verify` and the timeout \
                 refresh recompute it from a new run (results.rs verify_record), and a record is \
                 read only under a key that holds `kink_build`",
    },
    Outside {
        krate: "kink-flow",
        constant: "RECORD_DOMAIN",
        reason: "the domain of a tier-1 record's digest: the tier-1 reader recomputes it from the \
                 record (outcomes.rs record_sha256), and reads a record only under a context that \
                 holds `kink_build`",
    },
    Outside {
        krate: "kink-flow",
        constant: "OUTCOME_CONTEXT_DOMAIN",
        reason: "the domain of the tier-1 context's digest, which names its directory: every \
                 command recomputes it from its context (digest.rs context_sha256), and the reader \
                 requires the stored context to equal it (outcomes.rs OutcomeStore::file)",
    },
    Outside {
        krate: "kink-flow",
        constant: "MUTATION_IDENTITY_DOMAIN",
        reason: "the domain of a mutation's tier-1 identity: every command recomputes it from the \
                 mutation's patch (digest.rs mutation_identity), inside a context that holds \
                 `kink_build`",
    },
    Outside {
        krate: "kink-flow",
        constant: "HINT_DOMAIN",
        reason: "the domain of a killer-hint key; a hint only orders the kill search, which proves \
                 every status live or from tier 1",
    },
    Outside {
        krate: "kink-campaign",
        constant: "CAMPAIGN_REPORT_VERSION",
        reason: "the campaign report's format: replay, kink-corpus resume and its summary refuse \
                 a report of another version",
    },
    Outside {
        krate: "kink-corpus",
        constant: "CLASSIFIER",
        reason: "kink-corpus's terminal classifier, recorded in every campaign manifest it writes \
                 (`classifier`): `kink-corpus run` compares it before it resumes (cli.rs \
                 verify_binding), replay regenerates the manifest with this build's classifier \
                 and requires equal text, and kink-corpus summary and `definition` resume honour \
                 only an index entry whose `kink_build` is this build",
    },
    Outside {
        krate: "kink-flow",
        constant: "OUTCOME_SCHEMA_VERSION",
        reason: "what a tier-1 outcome record means: a member of the tier-1 context, the only store \
                 of outcome records, which the reader requires to equal this build's context",
    },
    Outside {
        krate: "kink-flow",
        constant: "OUTCOMES_VERSION",
        reason: "the tier-1 outcome file's format, which its reader requires (outcomes.rs)",
    },
    Outside {
        krate: "kink-flow",
        constant: "HINTS_VERSION",
        reason: "the killer-hints file's format; a hint only orders the kill search, which proves \
                 every status live or from tier 1",
    },
    Outside {
        krate: "kink-flow",
        constant: "RUN_VERSION",
        reason: "the run document's format, which `kink-flow report` requires (report.rs \
                 read_report)",
    },
    Outside {
        krate: "kink-native",
        constant: "REPORT_VERSION",
        reason: "the format of kink-native's step-3 report, a diagnostic output nothing reads back",
    },
    Outside {
        krate: "kink-flow",
        constant: "BASELINE_ONLY_OPERATOR",
        reason: "the operator name of the empty generation of a zero-mutant baseline campaign: it \
                 builds no mutant",
    },
    Outside {
        krate: "kink-flow",
        constant: "RESOLUTION_MEMO_VERSION",
        reason: "the resolution memo record's format and meaning (re-pin L1-4): its reader requires \
                 it in the record's key, which also holds `kink_build` and the whole identity, and \
                 checks the record's digest under that key (memo.rs read); a record decides a row \
                 only for a mutation tier 1 decides with no call",
    },
    Outside {
        krate: "kink-flow",
        constant: "CENSUS_MEMO_VERSION",
        reason: "the census memo record's format and meaning (re-pin L1-4): its reader requires it \
                 in the record's key, which also holds `kink_build` and the whole identity, and \
                 checks the record's digest under that key (memo.rs read)",
    },
    Outside {
        krate: "kink-flow",
        constant: "MUTATION_OPERATOR",
        reason: "the operator name of a written mutation's generation; what the mutation builds is \
                 its patch, which the mutation identity of the tier-1 key digests",
    },
    Outside {
        krate: "kink-flow",
        constant: "ANSWER_SCHEMA_VERSION",
        reason: "the pattern answer record's format and meaning (flow F-18): its reader requires it \
                 in the record's key, which also holds `kink_build` and the whole identity, and \
                 checks the record's digest under that key (query.rs read_record); a pattern answer \
                 decides no status",
    },
    Outside {
        krate: "kink-flow",
        constant: "LOWERING_VERSION",
        reason: "how a pattern's K text becomes its search target (flow F-18): a member of every \
                 pattern answer's key, which also holds `kink_build` (query.rs answer_key); a \
                 pattern answer decides no status",
    },
    Outside {
        krate: "kink-flow",
        constant: "PATTERN_DOMAIN",
        reason: "the domain of a pattern's digest (flow F-18): every query recomputes it from the \
                 compiled target (pattern.rs Lowering::lower), and it enters the pattern answer's \
                 key, which also holds `kink_build`",
    },
    Outside {
        krate: "kink-flow",
        constant: "PATTERN_RECORD_DOMAIN",
        reason: "the domain of a pattern answer record's digest (flow F-18): the reader recomputes \
                 it from the record under a key that holds `kink_build` (query.rs read_record)",
    },
    Outside {
        krate: "kink-flow",
        constant: "QUERY_VERSION",
        reason: "the query document's format (flow F-18): no command reads a query document back",
    },
];

/// kink's build identity (decision D14-1 (a), kink-flow tier 1; every honouring store since packet
/// CACHE-ID-fix-1): the SHA-256 of the running executable's bytes (`std::env::current_exe`),
/// computed once per process. Any rebuild of kink, debug or release, is another identity, so no
/// store honours a verdict that other verdict code produced, whether or not that code has a
/// version constant. `Err` when the executable cannot be read: every honouring store then
/// recomputes or refuses, never accepts ([`writer_difference`]).
///
/// # Errors
/// When the running executable has no path or cannot be read.
pub fn kink_build() -> Result<Sha256Digest, String> {
    static BUILD: OnceLock<Result<Sha256Digest, String>> = OnceLock::new();
    BUILD
        .get_or_init(|| {
            let path = std::env::current_exe()
                .map_err(|e| format!("the running executable has no path: {e}"))?;
            build_identity_of(&path)
        })
        .clone()
}

/// The build identity of the executable at `path`: the SHA-256 of its bytes.
///
/// # Errors
/// When the file cannot be read.
pub fn build_identity_of(path: &Path) -> Result<Sha256Digest, String> {
    let bytes = std::fs::read(path)
        .map_err(|e| format!("cannot read the executable {}: {e}", path.display()))?;
    Ok(sha256(&bytes))
}

/// Why a stored record may not be honoured by the build `build` ([`kink_build`]), or `None`
/// when it may: `recorded_build` is the record's `kink_build` member (its writer's build) and
/// `recorded_identity` its semantics identity. A record written by another build, one that names
/// no build (every record written before packet CACHE-ID-fix-1), and any record when this build's
/// identity is unknown, are refused. The reason names both builds and, when the identities
/// differ too, the first component that differs ([`identity_difference`]). A record of this
/// build whose identity differs (only a forged one) gives `None` here; the caller's identity
/// check refuses it.
#[must_use]
pub fn writer_difference(
    recorded_build: &Value,
    recorded_identity: &Value,
    build: &Result<Sha256Digest, String>,
) -> Option<String> {
    let build = match build {
        Err(e) => {
            return Some(format!(
                "this build's identity is unknown ({e}), so no stored verdict is honoured"
            ));
        }
        Ok(build) => build.to_string(),
    };
    let writer = match recorded_build.as_str() {
        Some(writer) if writer == build => return None,
        Some(writer) => format!("kink build {writer}"),
        None => "a kink build it does not name".to_owned(),
    };
    let algorithms = match identity_difference(recorded_identity) {
        Some(key) if key.is_empty() => "and it names no kink identity".to_owned(),
        Some(key) => format!("and its kink identity differs at `{key}`"),
        None => "and its kink identity is this build's, so what differs is verdict code that has \
                 no version constant"
            .to_owned(),
    };
    Some(format!(
        "it was written by {writer}, not by this build {build}, {algorithms}"
    ))
}

/// kink's semantics identity, `{key: value}` for every component of [`KINK_IDENTITY`].
#[must_use]
pub fn kink_identity() -> Value {
    Value::Object(
        KINK_IDENTITY
            .iter()
            .map(|component| (component.key.to_owned(), json!(component.value)))
            .collect::<Map<_, _>>(),
    )
}

/// The first way a recorded identity differs from this build's [`kink_identity`]: the key of the
/// first component it lacks or names with another value, else the first key it has that is no
/// component; `Some("")` when it is not an object; `None` when it is this build's.
#[must_use]
pub fn identity_difference(recorded: &Value) -> Option<String> {
    let Some(recorded) = recorded.as_object() else {
        return Some(String::new());
    };
    KINK_IDENTITY
        .iter()
        .find(|component| recorded.get(component.key) != Some(&json!(component.value)))
        .map(|component| component.key.to_owned())
        .or_else(|| {
            recorded
                .keys()
                .find(|key| KINK_IDENTITY.iter().all(|component| component.key != *key))
                .cloned()
        })
}
