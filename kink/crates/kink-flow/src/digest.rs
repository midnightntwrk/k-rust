//! The digests that key kink-flow's caches.
//!
//! The execution digest ([`execution_digest`]: the loaded definition without positions) and the
//! program digest key the result cache (flow README 5.3), tier 1 and the pattern cache. The
//! specification digest ([`spec_digest`]: every source byte) keys the resolution and census
//! memos, whose values cite lines, texts and sources, and names the specification in every
//! document. F-14 adds the other keys of the outcome cache (README 7.5): the tier-1 context and the
//! position-free mutation identity. kink's build identity, which every
//! cache and the run document hold, is kink-campaign's `identity::kink_build` (packet
//! CACHE-ID-fix-1).
//!
//! Every digest is `payload_digest(domain, canonical JSON)` (kink-patch), so it depends on
//! values, never on how `FLOW.toml` or `MUTATIONS.toml` is formatted, and a program's id enters
//! none: renaming a program keeps its cached result and outcomes.

use crate::{
    admit::{AdmittedSpec, CaseInputs},
    manifest::{Budget, FlowManifest, Program},
    observed::ResultProjection,
    results::budget_value,
};
use k_rust::definition::{Attributes, Definition, FlatModule};
use kink_corpus::SourceFile;
use kink_native::{K_RUST_REVISION, execution::SolverProfile};
use kink_patch::{
    Baseline, Edit, POSITION_KEYS, Patch, SentenceFingerprint, Sha256Digest, canonical_json,
    payload_digest, sha256,
};
use serde_json::{Value, json};

/// Domain of the specification digest.
pub const SPEC_DOMAIN: &str = "kink-flow/spec/v1";
/// Domain of the program digest.
pub const PROGRAM_DOMAIN: &str = "kink-flow/program/v1";

/// The payload of the specification digest: the k-rust revision and solver profile of this
/// build, how the specification is loaded, every non-builtin source file the load read
/// (`files`, kink-corpus `load_source`), as `{name, sha256}` sorted by name, and the
/// `assume_joined` premises when there are any, and the `[result] cells` (sorted) when the
/// manifest narrows the compared cells. Builtin sources are fixed by the k-rust revision.
pub fn spec_payload(manifest: &FlowManifest, files: &[SourceFile]) -> Value {
    let spec = &manifest.spec;
    let mut files = files
        .iter()
        .map(|file| (file.name.clone(), file.sha256.to_string()))
        .collect::<Vec<_>>();
    files.sort();
    let mut payload = json!({
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
    });
    // The author's premises (fz26 KINK-BASELINE-FINDINGS): every verdict is relative to them, so
    // every store keyed on this digest misses when they change. Absent when there are none, so a
    // specification without premises keeps its digest.
    if !spec.assume_joined.is_empty() {
        payload["assume_joined"] = json!(spec.assume_joined);
    }
    // The compared cells, when the manifest narrows them: a program's comparable result holds
    // the ends its second slot projects, so every store keyed on this digest misses when they
    // change. Absent without `[result]`, so a manifest without it keeps its digest; which cells
    // the specification declares unobservable is in its files.
    if let Some(result) = &manifest.result {
        let mut cells = result.cells.clone();
        cells.sort();
        payload["result_cells"] = json!(cells);
    }
    payload
}

/// The specification digest of README 5.3.
pub fn spec_digest(manifest: &FlowManifest, files: &[SourceFile]) -> Sha256Digest {
    payload_digest(
        SPEC_DOMAIN,
        canonical_json(&spec_payload(manifest, files)).as_bytes(),
    )
}

/// The payload of a program digest: the sha256 of the program's bytes (its file's bytes, or
/// its inline text) when it has a program, its start sort, its configuration variables'
/// texts sorted by name, and, when it has typed inputs, each one's decoded term.
///
/// The program enters by its bytes whichever way the front end binds them
/// ([`crate::admit::InputDecoder::program`]: `$PGM` text, another variable's text, or a term),
/// so a program bound as `$PGM` text has the digest it had before front ends could bind
/// programs. A program bound as `$PGM` text enters by that text's bytes, which are the file's
/// bytes under kink's rule and under a front end that binds them unchanged; a front end that
/// rewrites the text it binds to `$PGM` keys the program by what it binds. How the bytes bind is
/// a function of the definition and of the build that read them, which the result and outcome
/// keys name beside the program digest.
///
/// A typed input enters by what it denotes, not by how it is written: `{name, kast_sha256}`,
/// the variable's K name and the sha256 of the KAST JSON of its decoded term (k-rust
/// `kast::json::to_string`, which writes a term's content without its annotations, so two equal
/// terms give one text), sorted by name. Editing a value in a data or binary file an input reads
/// changes the term and so the digest, and reformatting the file does not. A program with a
/// program text and no typed inputs has exactly the payload it had before typed inputs existed,
/// so its digest, and every result and outcome cached under it, is unchanged.
pub fn program_payload(program: &Program, inputs: &CaseInputs) -> Value {
    let mut variables = program.variables.clone();
    variables.sort();
    let mut payload = json!({
        "start_sort": program.start_sort,
        "variables": variables
            .into_iter()
            .map(|(name, text)| json!({"name": name, "text": text}))
            .collect::<Vec<_>>(),
    });
    if let Some(text) = &inputs.text {
        payload["program_sha256"] = json!(sha256(text.as_bytes()).to_string());
    } else if let Some(bound) = &inputs.bound {
        payload["program_sha256"] = json!(bound.sha256.to_string());
    }
    if !inputs.typed.is_empty() {
        let mut typed = inputs
            .typed
            .iter()
            .map(|(name, term)| {
                let kast = k_rust::kast::json::to_string(term)
                    .expect("KAST JSON writes every term (`to_string` has no failing path)");
                (name.clone(), sha256(kast.as_bytes()).to_string())
            })
            .collect::<Vec<_>>();
        typed.sort();
        payload["typed"] = typed
            .into_iter()
            .map(|(name, kast_sha256)| json!({"name": name, "kast_sha256": kast_sha256}))
            .collect();
    }
    payload
}

/// The program digest of README 5.3; `inputs` are the program's inputs as read for admission
/// (`admit::ProgramInputs::read`).
pub fn program_digest(program: &Program, inputs: &CaseInputs) -> Sha256Digest {
    payload_digest(
        PROGRAM_DOMAIN,
        canonical_json(&program_payload(program, inputs)).as_bytes(),
    )
}

/// Domain of the execution digest: the loaded definition without positions ([`execution_digest`]).
pub const EXECUTION_DOMAIN: &str = "kink-flow/execution/v1";
/// The kind of an execution digest that exists ([`execution_digest`]); its fallback's kind is
/// [`SPEC_DOMAIN`].
pub const EXECUTION_DIGEST_KIND: &str = EXECUTION_DOMAIN;
/// The `outcome_schema` of every tier-1 context: what an outcome record means (flow README
/// 7.5.3). v2: outcomes are recorded under the Z3 profile too, where the solver is
/// resource-bounded and the context's budget names its units and Z3 build, so a record may hold
/// an outcome that rests on solver answers. v3 (CF-33d): a record may hold an `unknown` outcome,
/// one whose run is a function of the context (`crate::outcomes`, "Unknown outcomes"), with its
/// cause.
pub const OUTCOME_SCHEMA_VERSION: &str = "kink-flow/outcome/v3";
/// Domain of the digest of a tier-1 context, which names its directory under `outcomes/`.
pub const OUTCOME_CONTEXT_DOMAIN: &str = "kink-flow/outcome-context/v1";
/// Domain of a mutation's position-free identity (flow README 7.5.4).
pub const MUTATION_IDENTITY_DOMAIN: &str = "kink-flow/mutation-identity/v1";
/// The classifier of every flow campaign, as the tier-1 context names it.
pub const CLASSIFIER: &str = "all-normal";

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

/// The SHA-256 of the KAST JSON (k-rust `definition::json::to_string`) of `definition`, whose
/// attribute lists the caller has already stripped of [`POSITION_KEYS`]; `None` when it does not
/// encode.
fn wrapper_sha256(definition: &Definition) -> Option<String> {
    k_rust::definition::json::to_string(definition)
        .ok()
        .map(|text| sha256(text.as_bytes()).to_string())
}

/// `attributes` without [`POSITION_KEYS`].
fn without_positions(attributes: &Attributes) -> Attributes {
    let mut attributes = attributes.clone();
    for key in POSITION_KEYS {
        attributes.remove(key.as_str());
    }
    attributes
}

/// The position-free reading of a loaded definition: `{main_module, attributes, modules}`, where
/// `attributes` is the SHA-256 of the definition's attribute list without [`POSITION_KEYS`] and
/// each module, in definition order, is `{header, sentences}`: `header` the SHA-256 of the module
/// with no sentences (its name, imports and attributes without [`POSITION_KEYS`]), each held in an
/// otherwise empty definition as kink-patch's `fingerprint_payload` holds a sentence, and
/// `sentences`, in module order, each `{fingerprint, located, builtin_source}`: its kink-patch
/// [`SentenceFingerprint`] (the reading tier 1's mutation identity uses), whether it has a
/// `location`, and its `source` verbatim when that starts with one of `builtin_prefixes`, else
/// null. Order is kept: execution reads it (strategy, equations of one priority, leaf order, what
/// a work bound reaches). `None` when a sentence has no fingerprint (a context alias) or an
/// attribute list does not encode.
pub fn definition_value(definition: &Definition, builtin_prefixes: &[String]) -> Option<Value> {
    let attributes = wrapper_sha256(&Definition {
        main_module: String::new(),
        modules: Vec::new(),
        attributes: without_positions(&definition.attributes),
    })?;
    let modules = definition
        .modules
        .iter()
        .map(|module| {
            let header = wrapper_sha256(&Definition {
                main_module: String::new(),
                modules: vec![FlatModule {
                    name: module.name.clone(),
                    imports: module.imports.clone(),
                    local_sentences: Vec::new(),
                    attributes: without_positions(&module.attributes),
                }],
                attributes: Attributes::default(),
            })?;
            let sentences = module
                .local_sentences
                .iter()
                .map(|sentence| {
                    let attributes = sentence.attributes();
                    let builtin_source = attributes.source().filter(|source| {
                        builtin_prefixes
                            .iter()
                            .any(|prefix| source.starts_with(prefix.as_str()))
                    });
                    Some(json!({
                        "fingerprint": SentenceFingerprint::of(sentence).ok()?.to_string(),
                        "located": attributes.location().is_some(),
                        "builtin_source": builtin_source,
                    }))
                })
                .collect::<Option<Vec<_>>>()?;
            Some(json!({"header": header, "sentences": sentences}))
        })
        .collect::<Option<Vec<_>>>()?;
    Some(json!({
        "main_module": definition.main_module,
        "attributes": attributes,
        "modules": modules,
    }))
}

/// The builtin source prefixes the execution payload reads a sentence's `source` against: the
/// union of k-rust's default compile options' (kink-patch's reading, `authored_sentences`) and
/// the specification's compile's (kink-native's), sorted, so that each reading of a sentence's
/// origin is a function of the payload whichever list it uses.
fn builtin_prefixes(spec: &AdmittedSpec) -> Vec<String> {
    let mut prefixes = k_rust::kompile::CompileOptions::default().builtin_source_prefixes;
    prefixes.extend(
        spec.compiled
            .compile_options()
            .builtin_source_prefixes
            .iter()
            .cloned(),
    );
    prefixes.sort();
    prefixes.dedup();
    prefixes
}

/// The payload of the execution digest of the admitted `spec`: `{k_rust_revision, profile,
/// main_module, syntax_module, definition}`, plus `assumed` when `[spec] assume_joined` is not
/// empty and `result_cells` (sorted) when the manifest has `[result]`; `None` when
/// [`definition_value`] is `None`.
///
/// - `syntax_module` is the module the loader resolved, which programs are parsed in.
/// - `definition` is [`definition_value`] of the loaded baseline, which also holds every
///   `unobservable` declaration (an attribute, inside a fingerprint) and the syntax definition
///   program text is parsed with.
/// - `assumed` is the sorted identities (kink-native `NamedFinding::identity`: kind, the
///   equations' `UNIQUE_ID`s, the overlap's position in the term) of the baseline's findings an
///   `assume_joined` name assumes. The names are not members, since they hold source positions;
///   a name that matches no finding refuses the specification at admission, before any store is
///   read.
/// - `result_cells` is the specification digest's member, with its presence rule.
///
/// The entry, the include directories, the Markdown selector and the file list are not members:
/// they decide which definition is loaded, and the loaded definition is the member.
pub fn execution_payload(manifest: &FlowManifest, spec: &AdmittedSpec) -> Option<Value> {
    let definition = definition_value(spec.loaded.baseline.definition(), &builtin_prefixes(spec))?;
    let mut payload = json!({
        "k_rust_revision": K_RUST_REVISION,
        "profile": SolverProfile::BUILD.name(),
        "main_module": manifest.spec.main_module,
        "syntax_module": spec.loaded.syntax_module(),
        "definition": definition,
    });
    if !manifest.spec.assume_joined.is_empty() {
        let mut assumed = spec
            .data
            .findings()
            .into_iter()
            .filter(|finding| finding.assumed)
            .map(|finding| finding.identity)
            .collect::<Vec<_>>();
        assumed.sort();
        payload["assumed"] = json!(assumed);
    }
    if let Some(result) = &manifest.result {
        let mut cells = result.cells.clone();
        cells.sort();
        payload["result_cells"] = json!(cells);
    }
    Some(payload)
}

/// The execution digest of the admitted specification (flow README 5.3 and 7.5.3): what a
/// baseline or mutant run, and every judgement kink makes of it, depends on. It keys the result
/// cache, tier 1 and the pattern cache; it is computed once per command (`results::update_results`)
/// and passed to everything else that needs it.
///
/// It is `payload_digest(EXECUTION_DOMAIN, canonical JSON of execution_payload)`, kind
/// [`EXECUTION_DOMAIN`]; when there is no payload, the exact specification digest, kind
/// [`SPEC_DOMAIN`], which only costs misses.
///
/// **Why a store may answer under it.** A stored value stands for a recomputation when its key
/// names every input it depends on. With this digest "the same inputs" means the same loaded
/// definition up to positions instead of the same bytes, which rests on three premises:
///
/// - P1 (k-rust, compile): for one build compiling is deterministic, and positions and source
///   names reach `definition.kore` only through its `Source` and `Location` attributes. So two
///   loaded definitions equal up to [`POSITION_KEYS`] compile to KORE definitions equal up to
///   those attributes, the baseline's and, since a mutant is the baseline with sentences replaced
///   or deleted, every mutant's.
/// - P2 (k-rust, execution digest): KORE definitions equal up to `Source` and `Location` give
///   equal results outside k-rust's Execute exclusions (which no stored value comes from:
///   `results::HostDependence`), except in texts that cite a position.
/// - P3 (kink): kink's judgement reads a sentence's origin only as two facts, whether it is
///   located and whether its source is builtin (with one exact builtin file name, kink-patch's
///   cell-frame reading), both members here. Every other read of a position in kink is
///   presentation (rule rows, which documents render from the current load), a memo value or
///   mutation resolution, none of which is keyed by this digest. A new read of a position in a
///   judgement breaks this premise.
///
/// The digest is a congruence for tier 1, as README 7.5.4 requires: a mutation's identity
/// addresses a sentence by fingerprint and occurrence and requires a replacement to keep the
/// addressed sentence's position attributes, so two baselines with one digest give, after one
/// position-free replacement or deletion, mutants equal up to [`POSITION_KEYS`], and P1-P3 apply
/// to them. k-rust's own KORE execution digest is not such a congruence (compiling maps several
/// definitions to one KORE definition), and it cannot see K-level content that is not emitted to
/// KORE, such as which cells are `unobservable`. A failed premise shows as a `--verify`
/// mismatch, never silently: `results --verify` and `run --verify` re-derive every stored value
/// from the current bytes.
pub fn execution_digest(manifest: &FlowManifest, spec: &AdmittedSpec) -> ExecutionDigest {
    match execution_payload(manifest, spec) {
        Some(payload) => ExecutionDigest {
            kind: EXECUTION_DIGEST_KIND,
            digest: payload_digest(EXECUTION_DOMAIN, canonical_json(&payload).as_bytes()),
        },
        None => ExecutionDigest {
            kind: SPEC_DOMAIN,
            digest: spec_digest(manifest, &spec.loaded.files),
        },
    }
}

/// The tier-1 context (flow README 7.5.3, "The key"): every component of the key except the
/// mutation and the program, shared by every mutation of one command. `result` is what the
/// programs' second slot compares: the context names the slots, and the cells left out when
/// there are any. The execution digest already holds every `unobservable` declaration and
/// `[result] cells`; the cells left out are named here too, so that the context says on its face
/// which projection an outcome was decided for. `stop` is the manifest's stop
/// (`FlowManifest::stop_value`: its rules, its count and each program's own count), on which every
/// end a run reaches depends; absent without one, so a context without a stop is the context it
/// was before stops existed. `evidence` is a front end's kill evidence's format and further
/// inputs (`Renderer::evidence`, `{format, identity}`), on which the evidence a `killed` record
/// stores depends: absent for kink's own evidence, so a store written with one renderer, or with
/// one renderer over other names, never serves another's evidence, and a context without a front
/// end's renderer is the context it was before renderers existed.
pub fn outcome_context(
    kink_build: Sha256Digest,
    execution: ExecutionDigest,
    budget: Budget,
    result: &ResultProjection,
    stop: Option<&Value>,
    evidence: Option<&Value>,
) -> Value {
    // The budget object of the result key, so both keys name the same bounds, and the mutants'
    // work budget, which bounds only mutant runs (re-pin L1-1; absent without one, so a
    // context without a work budget is unchanged).
    let work_factor = budget.work_factor;
    let mut budget = budget_value(budget);
    if let Some(factor) = work_factor {
        budget["work"] = json!({"factor": factor, "floor": crate::manifest::WORK_FLOOR});
    }
    let mut context = json!({
        "outcome_schema": OUTCOME_SCHEMA_VERSION,
        "kink_build": kink_build.to_string(),
        // kink's semantics identity (kink-campaign `identity`, packet CACHE-ID): the k-rust
        // revision, the result schema, claim removal (re-pin R0c-fix-2), the consistency check
        // (R0c-fix-3), the compiled reading of an edit (R0c-fix-4), the definition exclusions
        // (R0-tail), patch admission (L2-2-fix-1), the execution request (L1-1) and the coverage
        // reading. `kink_build` (kink-campaign `identity::kink_build`) changes with every build and
        // guards all verdict code, versioned or not; the identity names the versioned algorithms
        // an outcome rests on, so a context says which of them a stale one predates.
        "kink": kink_campaign::kink_identity(),
        "profile": SolverProfile::BUILD.name(),
        "execution_digest": execution.value(),
        "budget": budget,
        "oracles": result.slots(),
        "classifier": CLASSIFIER,
        // No schedule: a record is the outcome of one executed test, and the schedule decides
        // only whether a test is executed, never its request, sides or slots, so one store
        // serves the first-kill search and `run --full` (search.rs module documentation).
    });
    // Absent when nothing is left out, so a whole-term context is unchanged.
    if result.cells().is_some() {
        context["not_compared"] = json!(result.not_compared);
    }
    if let Some(stop) = stop {
        context["stop"] = stop.clone();
    }
    if let Some(evidence) = evidence {
        context["evidence"] = evidence.clone();
    }
    context
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
