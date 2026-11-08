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
//! Under the Z3 profile a verdict is also a function of the Z3 build ([`z3_build`]): whether a
//! resource-bounded query is decided depends on the machine code that counts its units. A
//! statically linked Z3 is part of the executable [`kink_build`] digests, but a dynamically linked
//! one is not, so a store honoured on [`kink_build`] alone would honour, after the shared library
//! was replaced, verdicts another Z3 build decided. Every honouring store therefore also names the
//! Z3 build its verdicts were decided on and honours a record only when it is this process's
//! ([`z3_difference`]): kink-flow's keys hold it inside the solver's value (`budget.smt.z3`) and
//! its run document as `z3`, which `kink-flow report` requires; a kink-campaign manifest names it
//! as `z3`, so a campaign report and its digest do, and kink-corpus resume and summary and
//! replay's environment check read it there; a kink-corpus admission record names it beside
//! `kink_build`.
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
/// may no longer be. v6 (KINK-R4): a record's coverage holds `fired_sentences`, which a rule's
/// `fired_by` now lists in place of `applied_sentences`: a rewrite rule only when some path of the
/// run takes its step (k-rust `committed`), not when its candidate was rolled back or its step was
/// undefined; a v5 record has no such member, and its `applied_sentences` hold rules no path took.
/// v7 (kink27 R1-UNDEF, with its fix round 1): an undefined step is no end (kink's `trust.md`,
/// "What a kill trusts"), so every state side projects a run's ends only. A record's baseline
/// row no longer holds an undefined step's pre-step configuration in its whole-term side or in
/// `final_configuration`, nor the exit-stop class `undefined-step` (a run whose every path takes
/// an undefined step holds the empty set in each state side); a v6 record holds them. Comparison
/// verdicts moved with it: a whole term or term path that read a pre-step configuration now
/// reads ends only (a removed end distinguishes where the pre-step configuration equalled the
/// baseline's end), an exit stop no longer distinguishes by an undefined path alone, and the
/// single-crash and free-variable rules ignore undefined steps; so campaign reports, memos and
/// every other store bound to the identity are refused or missed. v8 (kink27 R3-UNDEF-BRIDGE): an
/// undefined step's leaf completes when its pre-step configuration is shown to exist, not when its
/// term is a terminal value, so a baseline that was `unknown` for that reason may be `comparable`,
/// a side may be a value and a pattern side decided where they were `unknown`. v9 (CF-16): a
/// comparable record holds `ends`, each end's computation head and class, outside the key and the
/// run digest; what counts as comparable is unchanged. v10 (CF-42, CF-43): the key names
/// kink-flow's execution digest (the loaded definition without positions) in place of the
/// specification digest, and its budget names no `time_ms` and names `baseline_max_work` when it is
/// set; a record's coverage entries are `{module, index, label}`, without file and lines, and the
/// record names its writer's specification digest outside the key; and no `timeout`, `error` or
/// host-dependent `unknown` record is written or read, so a v9 record, which may be one, is never
/// honoured. v11 (CF-03): a record holds `short_circuit_readings`, the entries of the baseline
/// run's `shortCircuitReadings` list that exclude it (empty unless the run is
/// `short-circuit-reading`), outside the key and the run digest; on a definition whose
/// short-circuit analysis flags a rule, and for a program whose initial configuration applies a
/// reading-dependent function, a program whose run lists no such entry is `comparable`, as the
/// campaign runner judges it since its run-level judgement of that list. v12: a record
/// holds each end once, as KORE text: its baseline row writes each pattern of a side as its
/// KORE text (kink-campaign report version 6, run digest domain `kink-flow/run/v2`), and a
/// comparable record no longer repeats its ends in `final_configuration`, which holds only an
/// unknown record's diagnostic leaves; what counts as comparable is unchanged, but every v11
/// record's row and run digest are another encoding, so none is honoured. v13: a record of a
/// program run with a stop (kink-flow `[stop]`) holds ends that say how the run reached them
/// (`halt`), and a comparable record is an end set of the truncated system, keyed by its stop
/// (the key's `stop`); a record of a program run without a stop is unchanged. v14: a record holds
/// `decider_smt_unknowns`, the undecided solver answers of kink's own questions about the baseline
/// run (its leaf feasibility and observation decider), beside k-rust's `smt_unknowns`, outside the
/// key and the run digest; and records are written under the Z3 profile too, where the solver is
/// resource-bounded and the key's budget names its units and Z3 build. v15: a program run with a
/// stop condition (kink-flow `[stop] when`) is keyed by the condition (the key's `stop.when`), and
/// one whose condition was left undecided at an arrival, or refused at one, is `unknown`, cause
/// `stop-condition`, and never written; a record of a program run without a condition is
/// unchanged. v16: a record's coverage holds `guards`, the guard outcomes of the guarded sentences
/// the baseline run entered (each node's outcomes where it was reached, the guard outcomes, the
/// valuation combinations), which `results` reports; a v15 record has none, so its rows would
/// report no guard outcome. v17: a record's coverage holds `bindings`, what the baseline run's
/// fired instances bound (the requested authored symbols that were the head of an operand, by
/// sentence, and the values of the selected template binders), which `coverage`'s syntax family
/// reads, and the key names the binding collection the run asked with (`bindings`); a v16 record
/// has none, so every production would read unreached. v18: a program's result may rest on an
/// observation declaration (kink-campaign `Observe`): a baseline run with one records its
/// channels, and one that a deterministic bound cut and that is otherwise complete is a prefix
/// program, comparable over its channels up to their horizons, where a v17 record of it was
/// `unknown`; a record of a program run without a declaration is unchanged. v19: a record's
/// `bindings` hold `alternatives`, the alternatives of an axiom with several (a disjunctive
/// left-hand side, a function equation's readings, a rewrite rule's disjunctive right-hand side)
/// that a fired instance took, from which the syntax family credits what an alternative
/// inspects and builds; and an operand head is recorded only for a variable the axiom reads
/// beside its left-hand side, so a v18 record's heads include values a step only carried past or
/// dropped. v20: a record's coverage holds `strictness`, the heating and cooling rules the run
/// matched and fired by compiled id, which `coverage`'s rules family reads per argument position;
/// a v19 record has none, so every heating rule would read unmatched. v21: a record's
/// `observations` holds `paths`, each channel's prefix set over the run's paths, where the run
/// split (kink-campaign `PathRecord`); a v20 record of such a run holds channels opened at the
/// branch, which would read as a prefix that observed nothing. v22: a record's program summary
/// `observations` of a run with several paths gives its prefix sets' facts (`paths`, `real`, each
/// channel's `complete_to`); a v21 record of such a run summarizes it as channels open at 0 by
/// the branch.
pub const RESULT_SCHEMA_VERSION: &str = "kink-flow/result/v22";

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
pub const KINK_IDENTITY: [Component; 18] = [
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
    // kink27 R5-WEAKENING: a mutation's status `unkillable` is a verdict this test decides.
    Component {
        key: "weakening",
        krate: "kink-patch",
        constant: "WEAKENING_VERSION",
        value: kink_patch::WEAKENING_VERSION,
    },
    Component {
        key: "data_facts",
        krate: "kink-native",
        constant: "DATA_FACTS_VERSION",
        value: kink_native::data::DATA_FACTS_VERSION,
    },
    Component {
        key: "terminal_value",
        krate: "kink-native",
        constant: "TERMINAL_VALUE_VERSION",
        value: kink_native::data::TERMINAL_VALUE_VERSION,
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
        key: "stop",
        krate: "kink-campaign",
        constant: "STOP_VERSION",
        value: crate::runner::STOP_VERSION,
    },
    Component {
        key: "observation",
        krate: "kink-campaign",
        constant: "OBSERVATION_VERSION",
        value: crate::observation::OBSERVATION_VERSION,
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
pub const OUTSIDE_IDENTITY: [Outside; 40] = [
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
                 from the sources it loads (digest.rs spec_digest); it keys the resolution and \
                 census memos, whose keys also hold `kink_build`, names each document's \
                 `spec.digest`, and is the execution digest's fallback, a member of keys that \
                 hold `kink_build`",
    },
    Outside {
        krate: "kink-flow",
        constant: "EXECUTION_DOMAIN",
        reason: "the domain of the execution digest (the loaded definition without positions): \
                 every command recomputes it from the admitted specification (digest.rs \
                 execution_digest), and it enters the result key, the tier-1 context and the \
                 pattern key, each of which also holds `kink_build`",
    },
    Outside {
        krate: "kink-flow",
        constant: "EXECUTION_DIGEST_KIND",
        reason: "the kind of an execution digest that exists (EXECUTION_DOMAIN itself; SPEC_DOMAIN \
                 on the fallback): it is a member of the result key, the tier-1 context and the \
                 pattern key, each of which also holds `kink_build`, and every command recomputes \
                 them",
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
        reason: "the domain of a result record's `run_sha256`: `results --verify` recomputes it \
                 from a new run (results.rs verify_record), and a record is read only under a key \
                 that holds `kink_build`",
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
        krate: "kink-campaign",
        constant: "CAMPAIGN_REPORT_VERSION",
        reason: "the campaign report's format: replay, kink-corpus resume and its summary refuse \
                 a report of another version",
    },
    Outside {
        krate: "kink-campaign",
        constant: "CAMPAIGN_MANIFEST_VERSION",
        reason: "the campaign manifest's format: replay and kink-corpus's summary refuse a \
                 manifest of another version (replay.rs, summary.rs); the solver options a \
                 run's verdict depends on are not named by a version: the manifest records \
                 those of its runs (backend_options) and, under the Z3 profile, the Z3 build that \
                 counts their units (`z3`), so its text and digest name them",
    },
    Outside {
        krate: "kink-campaign",
        constant: "CHAIN_DOMAIN",
        reason: "the domain of an observation prefix's chain and of a path's history \
                 (observation.rs): a mutant's chains are compared with its baseline's record of \
                 the same campaign call, folded by the same build, and how a prefix set is \
                 built and compared is named by the component `observation` \
                 (OBSERVATION_VERSION), which moves with any change of this domain",
    },
    Outside {
        krate: "kink-campaign",
        constant: "ELEMENT_DOMAIN",
        reason: "the domain of an observation element's digest (observation.rs): a mutant's \
                 elements are compared with its baseline's record of the same campaign call, \
                 digested by the same build, and what an element is and how two are compared \
                 is named by the component `observation` (OBSERVATION_VERSION), which moves \
                 with any change of this domain",
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
        constant: "K_EVIDENCE_VERSION",
        reason: "the format of kink's own kill evidence (evidence.rs), named by each difference \
                 object: evidence is printed for a reader of a kill the slot already proved and \
                 decides no status; a `killed` outcome record stores it inside its digest, in an \
                 outcome file whose version its reader requires (outcomes.rs)",
    },
    Outside {
        krate: "kink-flow",
        constant: "K_SET_EVIDENCE_VERSION",
        reason: "the format of kink's evidence of a difference of prefix sets (evidence.rs), named \
                 by each such difference object: evidence is printed for a reader of a kill the \
                 slot already proved and decides no status; a `killed` outcome record stores it \
                 inside its digest, in an outcome file whose version its reader requires \
                 (outcomes.rs)",
    },
    Outside {
        krate: "kink-flow",
        constant: "RUN_VERSION",
        reason: "the run document's format, which `kink-flow report` requires (report.rs \
                 read_report)",
    },
    Outside {
        krate: "kink-flow",
        constant: "FUZZ_VERSION",
        reason: "the `fuzz` command's document format, an output nothing reads back; the command \
                 decides no status, since kink's `run` proves each program it prints (fuzz.rs)",
    },
    Outside {
        krate: "kink-flow",
        constant: "FILTER_VERSION",
        reason: "the composition of the witness filter `fuzz` runs inside its campaign (fz26 \
                 FZ-COMPARABLE-B), recorded in that campaign's identity: it decides only which \
                 candidates `fuzz` keeps, and kink's `run` proves each program it prints \
                 (fuzz_filter.rs, fuzz.rs)",
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
    Outside {
        krate: "kink-flow",
        constant: "CHECK_VERSION",
        reason: "the check document's format: no command reads a check document back; check \
                 decides no status, since `run` proves each mutation it reports (cli.rs)",
    },
    Outside {
        krate: "kink-flow",
        constant: "VERDICTS_VERSION",
        reason: "the format of the verdicts rendering of a results or run document \
                 (`--output verdicts`, verdicts.rs): no command reads it back, and it is printed \
                 from a document after every status is decided",
    },
    Outside {
        krate: "kink-flow",
        constant: "COVERAGE_VERSION",
        reason: "the coverage document's format (coverage.rs): its readers (its derived part, its \
                 text and verdicts renderings) select it by its `schema` and read no version \
                 back, and it is built from result records read only under keys that hold \
                 `kink_build` and RESULT_SCHEMA_VERSION and, for the flips family, from outcome \
                 records (outcomes.rs) read only under a context that holds `kink_build` and \
                 OUTCOMES_VERSION, after every status is decided",
    },
    Outside {
        krate: "kink-corpus",
        constant: "MANIFEST_VERSION",
        reason: "the corpus manifest's format: every reader requires this version and refuses \
                 any other (manifest.rs from_canonical_json), so a manifest is never read under \
                 another format; what a manifest declares enters the campaign through its own \
                 digest (CORPUS_MANIFEST_DOMAIN)",
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

/// The Z3 build of this process as a store names it (kink-native `z3_build_value`): `Ok(None)`
/// under the no-Z3 profile, where no verdict depends on a solver; under the Z3 profile
/// `Ok(Some({version, library_sha256}))`. `Err` under the Z3 profile when the build cannot name
/// its library (kink-native `solver_named`): every unnamed build would share the record's value,
/// so no store honours a record then, as none does when kink's own build is unknown.
///
/// # Errors
/// kink-native's `UNNAMED_Z3_BUILD` under the Z3 profile when the build cannot be named.
pub fn z3_build() -> Result<Option<Value>, &'static str> {
    kink_native::solver_named()?;
    Ok(kink_native::z3_build_value())
}

/// Why a stored record may not be honoured by a process on the Z3 build `build` ([`z3_build`]),
/// or `None` when it may: `recorded` is the record's `z3` member, the Z3 build its verdicts were
/// decided on (absent under the no-Z3 profile). A record is honoured only when it names exactly
/// this build, or when neither names one; when this build cannot be named, never.
///
/// Under the Z3 profile with resource-bounded queries every verdict is a function of the query,
/// its units and the Z3 build that counts them, so a record decided on another build may hold a
/// class, a status or a killer this build would not decide. The build identity does not show
/// it for a dynamically linked Z3, whose code is outside the executable.
#[must_use]
pub fn z3_difference(
    recorded: Option<&Value>,
    build: &Result<Option<Value>, &'static str>,
) -> Option<String> {
    let build = match build {
        Err(e) => return Some((*e).to_owned()),
        Ok(build) => build.as_ref(),
    };
    if recorded == build {
        return None;
    }
    let named = |value: &Value| kink_patch::canonical_json(value);
    Some(match (recorded, build) {
        (Some(recorded), Some(build)) => format!(
            "it was decided on the Z3 build {}, not on this process's {}",
            named(recorded),
            named(build)
        ),
        (None, Some(build)) => format!(
            "it names no Z3 build, and this process decides on the Z3 build {}",
            named(build)
        ),
        (Some(recorded), None) => format!(
            "it was decided on the Z3 build {}, and this build has no Z3",
            named(recorded)
        ),
        (None, None) => unreachable!("equal values return above"),
    })
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
