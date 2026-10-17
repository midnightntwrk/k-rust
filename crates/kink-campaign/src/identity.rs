//! kink's semantics identity: the one list of everything in kink that can change a verdict
//! (packet CACHE-ID of the k-rust 501f18b9 re-pin).
//!
//! A verdict (a mutant's status, a baseline's comparability, a program's result class) depends on
//! the k-rust revision and on kink's own algorithms: how a patch is addressed and admitted, which
//! claims a mutant loses, whether its equations are consistent, what its edit changes, which
//! comparisons are excluded, what execution request is sent, what counts as a comparable result
//! and how coverage is read. [`KINK_IDENTITY`] names each one by its version constant, and
//! [`kink_identity`] is their object, `{key: value}`. Every persistent store derives its key or
//! its refusal from that one object, so a record written by a build with any other component
//! misses or is refused:
//! - the campaign manifest's `kink` member is [`kink_identity`]. kink-corpus resume and its
//!   summary refuse a stored report whose manifest names another ([`crate::same_admission`]),
//!   and replay's environment check refuses one before regenerating anything, naming the
//!   component (`kink.<key>`). Replay also regenerates the manifest, which would refuse it too;
//! - kink-flow's result cache keys every record on it (`results::result_key`, member `kink`);
//! - kink-flow's tier-1 outcome context holds it (`digest::outcome_context`, member `kink`),
//!   beside the executable's hash;
//! - kink-flow's run document names it, and `kink-flow report` refuses a document that names
//!   another.
//!
//! The rule for adding to it: a constant whose change can change a verdict is a component here
//! (bump the constant whenever its algorithm changes what it decides; the stores then miss
//! without further edits). Every other versioned constant (a name ending in `_VERSION`, or a
//! string value ending in `/v<N>`) is listed in [`OUTSIDE_IDENTITY`] with the reason it cannot
//! change a verdict on its own. kink-campaign's `tests/identity.rs` reads every crate's sources
//! and fails on a versioned constant that is in neither list.

use serde_json::{Map, Value, json};

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
/// review 1, minor).
pub const RESULT_SCHEMA_VERSION: &str = "kink-flow/result/v4";

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
pub const KINK_IDENTITY: [Component; 12] = [
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

const DOMAIN: &str = "a digest domain: a change changes the digest it names, and so the key or \
                      the record that digest is part of";

/// Every versioned constant outside [`KINK_IDENTITY`].
pub const OUTSIDE_IDENTITY: [Outside; 22] = [
    Outside {
        krate: "kink-patch",
        constant: "TEST_MANIFEST_DOMAIN",
        reason: DOMAIN,
    },
    Outside {
        krate: "kink-patch",
        constant: "OBSERVATION_DOMAIN",
        reason: DOMAIN,
    },
    Outside {
        krate: "kink-patch",
        constant: "CAMPAIGN_MANIFEST_DOMAIN",
        reason: DOMAIN,
    },
    Outside {
        krate: "kink-patch",
        constant: "OPERATOR_DOMAIN",
        reason: DOMAIN,
    },
    Outside {
        krate: "kink-native",
        constant: "CENSUS_DOMAIN",
        reason: DOMAIN,
    },
    Outside {
        krate: "kink-corpus",
        constant: "CORPUS_MANIFEST_DOMAIN",
        reason: "a digest domain: the corpus manifest's digest names the store's directory",
    },
    Outside {
        krate: "kink-flow",
        constant: "SPEC_DOMAIN",
        reason: DOMAIN,
    },
    Outside {
        krate: "kink-flow",
        constant: "PROGRAM_DOMAIN",
        reason: DOMAIN,
    },
    Outside {
        krate: "kink-flow",
        constant: "RUN_DOMAIN",
        reason: DOMAIN,
    },
    Outside {
        krate: "kink-flow",
        constant: "RECORD_DOMAIN",
        reason: DOMAIN,
    },
    Outside {
        krate: "kink-flow",
        constant: "OUTCOME_CONTEXT_DOMAIN",
        reason: DOMAIN,
    },
    Outside {
        krate: "kink-flow",
        constant: "MUTATION_IDENTITY_DOMAIN",
        reason: DOMAIN,
    },
    Outside {
        krate: "kink-flow",
        constant: "HINT_DOMAIN",
        reason: DOMAIN,
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
                 (`classifier`)",
    },
    Outside {
        krate: "kink-flow",
        constant: "OUTCOME_SCHEMA_VERSION",
        reason: "what a tier-1 outcome record means, in the tier-1 context, the only store of \
                 outcome records",
    },
    Outside {
        krate: "kink-flow",
        constant: "OUTCOMES_VERSION",
        reason: "the tier-1 outcome file's format, which its reader requires",
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
        reason: "the run document's format, which `kink-flow report` requires",
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
        constant: "MUTATION_OPERATOR",
        reason: "the operator name of a written mutation's generation; what the mutation builds is \
                 its patch, which the mutation identity of the tier-1 key digests",
    },
];

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
