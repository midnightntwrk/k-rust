//! The digests that key kink-flow's caches.
//!
//! The specification and program digests key the result cache (flow README 5.3). F-14 adds the
//! keys of the outcome cache (README 7.5): the execution digest, kink's build identity, the
//! tier-1 context, the position-free mutation identity and the killer-hint key.
//!
//! Every digest is `payload_digest(domain, canonical JSON)` (kink-patch), so it depends on
//! values, never on how `FLOW.toml` or `MUTATIONS.toml` is formatted, and a program's id enters
//! none: renaming a program keeps its cached result and outcomes.

use crate::{
    manifest::{Budget, FlowManifest, Program},
    mutation::{EditAction, Mutation, ResolvedMutation},
    results::{ORACLE_SLOTS, RESULT_SCHEMA_VERSION, result_key},
};
use kink_corpus::{LoadedSource, SourceFile};
use kink_native::{K_RUST_REVISION, execution::SolverProfile};
use kink_patch::{
    Baseline, Edit, POSITION_KEYS, Patch, SentenceFingerprint, Sha256Digest, canonical_json,
    payload_digest, sha256,
};
use serde_json::{Value, json};
use std::sync::OnceLock;

/// Domain of the specification digest.
pub const SPEC_DOMAIN: &str = "kink-flow/spec/v1";
/// Domain of the program digest.
pub const PROGRAM_DOMAIN: &str = "kink-flow/program/v1";

/// The payload of the specification digest: the k-rust revision and solver profile of this
/// build, how the specification is loaded, and every non-builtin source file the load read
/// (`files`, kink-corpus `load_source`), as `{name, sha256}` sorted by name. Builtin sources
/// are fixed by the k-rust revision.
pub fn spec_payload(manifest: &FlowManifest, files: &[SourceFile]) -> Value {
    let spec = &manifest.spec;
    let mut files = files
        .iter()
        .map(|file| (file.name.clone(), file.sha256.to_string()))
        .collect::<Vec<_>>();
    files.sort();
    json!({
        "k_rust_revision": K_RUST_REVISION,
        "profile": SolverProfile::BUILD.name(),
        "entry": spec.entry,
        "main_module": spec.main_module,
        "syntax_module": spec.syntax_module,
        "md_selector": spec.md_selector,
        "include_dirs": spec.include_dirs,
        "files": files
            .into_iter()
            .map(|(name, sha256)| json!({"name": name, "sha256": sha256}))
            .collect::<Vec<_>>(),
    })
}

/// The specification digest of README 5.3.
pub fn spec_digest(manifest: &FlowManifest, files: &[SourceFile]) -> Sha256Digest {
    payload_digest(
        SPEC_DOMAIN,
        canonical_json(&spec_payload(manifest, files)).as_bytes(),
    )
}

/// The payload of a program digest: the sha256 of the program's bytes (its file's bytes, or
/// its inline text), its start sort and its configuration variables sorted by name.
pub fn program_payload(program: &Program, text: &str) -> Value {
    let mut variables = program.variables.clone();
    variables.sort();
    json!({
        "program_sha256": sha256(text.as_bytes()).to_string(),
        "start_sort": program.start_sort,
        "variables": variables
            .into_iter()
            .map(|(name, text)| json!({"name": name, "text": text}))
            .collect::<Vec<_>>(),
    })
}

/// The program digest of README 5.3; `text` is the program's text as read for admission.
pub fn program_digest(program: &Program, text: &str) -> Sha256Digest {
    payload_digest(
        PROGRAM_DOMAIN,
        canonical_json(&program_payload(program, text)).as_bytes(),
    )
}

/// The kind of [`execution_digest`] until k-rust's KINK-14 `execution_digest()` exists: the
/// exact specification digest of README 5.3.
pub const EXECUTION_DIGEST_KIND: &str = SPEC_DOMAIN;
/// The `outcome_schema` of every tier-1 context: what an outcome record means (flow README
/// 7.5.3).
pub const OUTCOME_SCHEMA_VERSION: &str = "kink-flow/outcome/v1";
/// Domain of the digest of a tier-1 context, which names its directory under `outcomes/`.
pub const OUTCOME_CONTEXT_DOMAIN: &str = "kink-flow/outcome-context/v1";
/// Domain of a mutation's position-free identity (flow README 7.5.4).
pub const MUTATION_IDENTITY_DOMAIN: &str = "kink-flow/mutation-identity/v1";
/// Domain of a mutation's killer-hint key (flow README 7.5.5).
pub const HINT_DOMAIN: &str = "kink-flow/hint/v1";
/// The classifier of every flow campaign, as the tier-1 context names it.
pub const CLASSIFIER: &str = "all-normal";
/// The schedule of every kill-search call, as the tier-1 context names it.
pub const SCHEDULE: &str = "first-kill";

/// The digest of what a specification's execution depends on, with its kind.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ExecutionDigest {
    pub kind: &'static str,
    pub digest: Sha256Digest,
}

impl ExecutionDigest {
    /// `{kind, digest}`.
    pub fn value(&self) -> Value {
        json!({"kind": self.kind, "digest": self.digest.to_string()})
    }
}

/// The execution digest of the loaded specification, the tier-1 key's specification
/// component (flow README 7.5.3). Every tier-1 caller goes through this function.
///
/// Today it is the exact specification digest ([`spec_digest`], kind
/// [`EXECUTION_DIGEST_KIND`]): every source byte, so any edit of the specification, a comment
/// included, misses tier 1, and tier 2 then makes the re-proof one call per killed mutation.
/// When k-rust's KINK-14 `execution_digest()` lands, swapping it in is a change of this one
/// function, under the preconditions of README 7.5.4: equal digests of two baselines must give
/// equal executions after the same position-free sentence replacement or deletion (a
/// congruence: the digest may drop positions, comments and non-semantic order only, never a
/// rule merely because the baseline does not fire it), and the digest must cover the syntax
/// definition the programs are parsed with, because the program digest hashes program text.
pub fn execution_digest(manifest: &FlowManifest, loaded: &LoadedSource) -> ExecutionDigest {
    ExecutionDigest {
        kind: EXECUTION_DIGEST_KIND,
        digest: spec_digest(manifest, &loaded.files),
    }
}

/// kink's own build identity (decision D14-1 (a)): the SHA-256 of the running executable's
/// bytes (`std::env::current_exe`), computed once per process. Any rebuild of kink, debug or
/// release, is another identity, so tier 1 never trusts an outcome that other verdict code
/// produced. `Err` when the executable cannot be read: tier 1 is then disabled for the
/// command, never keyed without it.
pub fn kink_build_identity() -> Result<Sha256Digest, String> {
    static IDENTITY: OnceLock<Result<Sha256Digest, String>> = OnceLock::new();
    IDENTITY
        .get_or_init(|| {
            let path = std::env::current_exe()
                .map_err(|e| format!("the running executable has no path: {e}"))?;
            let bytes = std::fs::read(&path)
                .map_err(|e| format!("cannot read the executable {}: {e}", path.display()))?;
            Ok(sha256(&bytes))
        })
        .clone()
}

/// The tier-1 context (flow README 7.5.3, "The key"): every component of the key except the
/// mutation and the program, shared by every mutation of one command.
pub fn outcome_context(
    kink_build: Sha256Digest,
    execution: ExecutionDigest,
    budget: Budget,
) -> Value {
    // The budget object of the result key, so both keys name the same bounds.
    let budget = result_key(execution.digest, execution.digest, budget)["budget"].clone();
    json!({
        "outcome_schema": OUTCOME_SCHEMA_VERSION,
        "result_schema": RESULT_SCHEMA_VERSION,
        "kink_build": kink_build.to_string(),
        "k_rust_revision": K_RUST_REVISION,
        "profile": SolverProfile::BUILD.name(),
        "execution_digest": execution.value(),
        "budget": budget,
        "oracles": ORACLE_SLOTS,
        "classifier": CLASSIFIER,
        "schedule": SCHEDULE,
    })
}

/// The digest of a tier-1 context: `payload_digest("kink-flow/outcome-context/v1", canonical
/// JSON)`.
pub fn context_sha256(context: &Value) -> Sha256Digest {
    payload_digest(OUTCOME_CONTEXT_DOMAIN, canonical_json(context).as_bytes())
}

/// The position-free identity of a resolved mutation's patch against `baseline` (flow README
/// 7.5.4): `payload_digest("kink-flow/mutation-identity/v1", canonical JSON of {edits})`, one
/// entry `{op, module, target, occurrence, replacement}` per edit, sorted by (module, target,
/// occurrence, op). `target` is the edit's pin (the addressed sentence's fingerprint),
/// `occurrence` the number of sentences of that module before it with the same fingerprint
/// (two identical rules share a fingerprint), and `replacement` the replacement's fingerprint
/// or null for a deletion.
///
/// Within one baseline it names exactly one patch: the occurrence separates identical rules,
/// the fingerprint is the replacement's whole content except its position attributes, and
/// those must be the addressed sentence's (checked here, which also closes `InputAddresses`,
/// the one position key kink-patch does not check). `None` (the mutation then bypasses tier 1)
/// for any other edit kind, an unpinned or stale patch, a sentence without a fingerprint, or a
/// replacement whose ten position attributes differ from the addressed sentence's. Across
/// baselines it is only meaningful together with the execution digest.
pub fn mutation_identity(baseline: &Baseline, patch: &Patch) -> Option<Sha256Digest> {
    if !patch.is_pinned() {
        return None;
    }
    let mut edits = Vec::with_capacity(patch.edits().len());
    for edit in patch.edits() {
        let (op, at, replacement) = match edit {
            Edit::ReplaceSentence { at, replacement } => {
                ("replace-sentence", at, Some(replacement))
            }
            Edit::DeleteSentence { at } => ("delete-sentence", at, None),
            _ => return None,
        };
        let original = baseline.sentence(at)?;
        let target = *patch.pins().get(at)?;
        if SentenceFingerprint::of(original).ok()? != target {
            return None;
        }
        let replacement = match replacement {
            None => Value::Null,
            Some(replacement) => {
                for key in POSITION_KEYS {
                    if replacement.attributes().get(key.as_str())
                        != original.attributes().get(key.as_str())
                    {
                        return None;
                    }
                }
                json!(SentenceFingerprint::of(replacement).ok()?.to_string())
            }
        };
        let module = baseline
            .definition()
            .modules
            .iter()
            .find(|module| module.name == at.module)?;
        let before = module
            .local_sentences
            .get(..usize::try_from(at.index).ok()?)?;
        let occurrence = before
            .iter()
            .filter(|sentence| SentenceFingerprint::of(sentence).ok() == Some(target))
            .count();
        edits.push((
            (at.module.clone(), target.to_string(), occurrence, op),
            replacement,
        ));
    }
    edits.sort_by(|left, right| left.0.cmp(&right.0));
    let edits = edits
        .into_iter()
        .map(|((module, target, occurrence, op), replacement)| {
            json!({
                "op": op,
                "module": module,
                "target": target,
                "occurrence": occurrence,
                "replacement": replacement,
            })
        })
        .collect::<Vec<_>>();
    Some(payload_digest(
        MUTATION_IDENTITY_DOMAIN,
        canonical_json(&json!({"edits": edits})).as_bytes(),
    ))
}

/// The killer-hint key of a mutation (flow README 7.5.5): `payload_digest("kink-flow/hint/v1",
/// canonical JSON of {edits, rules})`. `edits` are the `MUTATIONS.toml` entry's edits as
/// written, in list order, each `{file, rule, find, replace, delete}` without `line` (a line
/// number moves with unrelated edits); `rules` are, per addressed rule in sentence order,
/// `{module, label, text}` with the rule's K text before the edit. No position, no
/// specification digest, no mutation id or note: the key survives edits elsewhere in the
/// specification, and a hint only orders the work.
pub fn hint_key(mutation: &Mutation, resolved: &ResolvedMutation) -> Sha256Digest {
    let edits = mutation
        .edits
        .iter()
        .map(|edit| {
            let (find, replace, delete) = match &edit.action {
                EditAction::Replace { find, replace } => (json!(find), json!(replace), false),
                EditAction::Delete => (Value::Null, Value::Null, true),
            };
            json!({
                "file": edit.file,
                "rule": edit.rule,
                "find": find,
                "replace": replace,
                "delete": delete,
            })
        })
        .collect::<Vec<_>>();
    let rules = resolved
        .rules
        .iter()
        .map(|rule| json!({"module": rule.at.module, "label": rule.label, "text": rule.before}))
        .collect::<Vec<_>>();
    payload_digest(
        HINT_DOMAIN,
        canonical_json(&json!({"edits": edits, "rules": rules})).as_bytes(),
    )
}
