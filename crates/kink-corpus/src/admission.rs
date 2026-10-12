//! Ordered corpus refusals. The baseline check has no candidate to execute.

use crate::{
    LoadedSource, ProgramSource, SourceFile, assemble_input,
    manifest::{CorpusInput, CorpusManifest, DefinitionSpec, exclusion_applies, path_excluded},
};
use k_rust::{
    backend::{Backend, BackendOptions},
    builtin,
    kompile::{CompilationBackend, CompileOptions},
    kore::{ast::Pattern, codec::from_value},
    outer::{LoadOptions, ResolvedSource, SourceResolver, load_for_compilation},
};
use kink_campaign::{Campaign, CampaignFailureKind, CampaignOptions, TestCase, run_campaign_multi};
use kink_native::{
    CensusVerdict, DeclarationCensus, NativeValidator, ValidatedDefinition,
    bridge::validate_test_initial_state,
    declaration_census,
    execution::SolverProfile,
    representation::{RepresentationError, validate_representation},
};
use kink_patch::{
    Baseline, Discovery, SelectionPolicy, SemanticInput, canonical_json, select, sha256,
};
use kink_pattern::ExecutionTerminalKind;
use serde_json::{Value, json};
use std::{
    collections::BTreeMap,
    fs,
    path::{Component, Path, PathBuf},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AdmissionRefusal {
    pub stage: String,
    pub reason: String,
    pub detail: String,
}
impl AdmissionRefusal {
    fn new(stage: &str, reason: &str, detail: impl ToString) -> Self {
        Self {
            stage: stage.into(),
            reason: reason.into(),
            detail: detail.to_string(),
        }
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct KompileWarning {
    pub code: String,
    pub message: String,
}
#[derive(Clone, Debug)]
pub struct AdmissionRecord {
    pub definition: String,
    pub refusal: Option<AdmissionRefusal>,
    pub files: Vec<SourceFile>,
    pub census: Option<DeclarationCensus>,
    pub representation: Option<Value>,
    /// Compile fidelity only; no admission decision reads this list.
    pub kompile_warnings: Option<Vec<KompileWarning>>,
}
impl AdmissionRecord {
    fn new(definition: &str) -> Self {
        Self {
            definition: definition.into(),
            refusal: None,
            files: Vec::new(),
            census: None,
            representation: None,
            kompile_warnings: None,
        }
    }
    pub fn value(&self) -> Value {
        json!({"definition": self.definition, "outcome": if self.refusal.is_some() { "refused" } else { "admitted" },
            "stage": self.refusal.as_ref().map(|r| &r.stage), "reason": self.refusal.as_ref().map(|r| &r.reason), "detail": self.refusal.as_ref().map(|r| &r.detail),
            "files": self.files.iter().map(|f| json!({"name": f.name, "sha256": f.sha256.to_string()})).collect::<Vec<_>>(),
            "census": self.census.as_ref().map(DeclarationCensus::value), "representation": self.representation,
            "kompile_warnings": self.kompile_warnings.as_ref().map(|w| w.iter().map(|d| json!({"code":d.code,"message":d.message})).collect::<Vec<_>>())})
    }
    pub fn text(&self) -> String {
        canonical_json(&self.value())
    }
}
#[derive(Clone, Debug)]
pub struct AdmittedDefinition {
    pub loaded: LoadedSource,
    pub semantic_input: SemanticInput,
    pub compiled: ValidatedDefinition,
    pub tests: Vec<TestCase>,
}
#[derive(Clone, Debug)]
pub struct AdmissionResult {
    pub record: AdmissionRecord,
    pub admitted: Option<AdmittedDefinition>,
}

/// The semantic-input stage, shared by admission and callers validating artifact text.
pub fn check_semantic_input(text: &str) -> Result<SemanticInput, AdmissionRefusal> {
    let (input, _) = SemanticInput::read(text)
        .map_err(|e| AdmissionRefusal::new("semantic-input", "non-canonical", e))?;
    if input.text() != text {
        return Err(AdmissionRefusal::new(
            "semantic-input",
            "non-canonical",
            "SemanticInput bytes differ",
        ));
    }
    Ok(input)
}
/// Admit the named definition of an immutable, validated manifest.
pub fn admit_definition(
    manifest: &CorpusManifest,
    definition_id: &str,
    workspace: &Path,
) -> AdmissionResult {
    let mut record = AdmissionRecord::new(definition_id);
    let result = manifest
        .definitions
        .iter()
        .find(|d| d.id == definition_id)
        .ok_or_else(|| AdmissionRefusal::new("exclusion", "other", "definition is not listed"))
        .and_then(|d| admit(manifest, d, workspace, &mut record));
    match result {
        Ok(admitted) => AdmissionResult {
            record,
            admitted: Some(admitted),
        },
        Err(refusal) => {
            record.refusal = Some(refusal);
            AdmissionResult {
                record,
                admitted: None,
            }
        }
    }
}
fn admit(
    manifest: &CorpusManifest,
    d: &DefinitionSpec,
    workspace: &Path,
    record: &mut AdmissionRecord,
) -> Result<AdmittedDefinition, AdmissionRefusal> {
    for exclusion in &manifest.exclusions {
        // Inspect path identities only: an alias cannot hide a below-floor source.
        let canonical = fs::canonicalize(workspace.join(&d.root.path).join(&d.entry)).ok();
        let resolved_match = canonical.as_ref().is_some_and(|p| {
            let parts = p
                .components()
                .filter_map(|c| match c {
                    Component::Normal(n) => n.to_str().map(str::to_owned),
                    _ => None,
                })
                .collect::<Vec<_>>();
            path_excluded(&parts, &exclusion.case)
        });
        if exclusion_applies(d, exclusion) || resolved_match {
            return Err(AdmissionRefusal::new(
                "exclusion",
                &exclusion.reason,
                &exclusion.citation,
            ));
        }
    }
    if d.requires_profile
        .is_some_and(|p| p != SolverProfile::BUILD)
    {
        return Err(AdmissionRefusal::new(
            "profile",
            "profile",
            "definition requires z3",
        ));
    }
    let (loaded, input_texts) = pinned_load(d, workspace, record)?;
    let generated = SemanticInput::of(&loaded.baseline)
        .map_err(|e| AdmissionRefusal::new("semantic-input", "non-canonical", e))?;
    let semantic_input = check_semantic_input(generated.text())?;
    let validator = NativeValidator::bind(loaded.baseline.clone(), CompileOptions::default());
    let compiled = validator
        .compile_baseline()
        .map_err(|e| AdmissionRefusal::new("compile", "compile-error", e))?;
    let warnings = compiled
        .artifacts()
        .diagnostics
        .iter()
        .map(|d| (format!("{:?}", d.code), d.message.clone()))
        .collect::<std::collections::BTreeSet<_>>();
    record.kompile_warnings = Some(
        warnings
            .into_iter()
            .map(|(code, message)| KompileWarning { code, message })
            .collect(),
    );
    if let Err(e) = validate_representation(&compiled) {
        let clause = match &e {
            RepresentationError::Finding(f) => f.clause.to_string(),
            RepresentationError::KoreParse(_) => "kore-parse".into(),
        };
        record.representation = Some(json!({"refused": clause}));
        return Err(AdmissionRefusal::new("representation", &clause, e));
    }
    record.representation = Some(json!("admitted"));
    let census = declaration_census(&compiled)
        .map_err(|e| AdmissionRefusal::new("declaration-census", "census-error", e))?;
    let flagged = census.verdict() == CensusVerdict::Flagged;
    record.census = Some(census);
    if flagged {
        return Err(AdmissionRefusal::new(
            "declaration-census",
            "vi-t13",
            "non-natural declarations; see census findings",
        ));
    }
    let mut backend = Backend::new(
        &compiled.artifacts().definition_kore,
        k_rust::kast::identifier::encode(&d.main_module),
        BackendOptions::default(),
    )
    .map_err(|e| AdmissionRefusal::new("inputs", "input-gate", e))?;
    let mut tests = Vec::new();
    for test in &d.tests {
        let initial_state = match &test.input {
            CorpusInput::Program(spec) => {
                let mut spec = spec.clone();
                if let ProgramSource::File(file) = &spec.program {
                    spec.program = ProgramSource::Text(input_texts[file].clone());
                }
                assemble_input(&loaded, &spec).map_err(|e| {
                    let reason = match e {
                        crate::InputError::Parse(_) => "parse",
                        _ => "assemble",
                    };
                    AdmissionRefusal::new("inputs", reason, e)
                })?
            }
            CorpusInput::KoreState { file, .. } => {
                let value = serde_json::from_str(&input_texts[file])
                    .map_err(|e| AdmissionRefusal::new("inputs", "parse", e))?;
                from_value(&value).map_err(|e| AdmissionRefusal::new("inputs", "parse", e))?
            }
        };
        if !initial_state.free_variables().is_empty() {
            return Err(AdmissionRefusal::new(
                "inputs",
                "input-gate",
                "corpus v1 requires a concrete initial state",
            ));
        }
        validate_test_initial_state(&mut backend, &initial_state)
            .map_err(|e| AdmissionRefusal::new("inputs", "input-gate", format!("{e:?}")))?;
        tests.push(TestCase {
            id: test.id.clone(),
            initial_state,
            oracles: test.oracles.clone(),
        });
    }
    baseline_only(manifest, d, &validator, &tests)?;
    Ok(AdmittedDefinition {
        loaded,
        semantic_input,
        compiled,
        tests,
    })
}
fn all_normal(_: &Pattern) -> ExecutionTerminalKind {
    ExecutionTerminalKind::Normal
}
fn baseline_only(
    manifest: &CorpusManifest,
    d: &DefinitionSpec,
    validator: &NativeValidator,
    tests: &[TestCase],
) -> Result<(), AdmissionRefusal> {
    // The runner requires a generation. This checked empty discovery yields zero
    // candidates, so neither operator code nor candidate execution can be reached.
    let discovery = Discovery::empty(validator.baseline(), false, false);
    let selection = select(&discovery, SelectionPolicy::Each, 1)
        .map_err(|e| AdmissionRefusal::new("baseline", "invalid-declaration", e))?;
    let generation = selection
        .fold("kink-corpus/baseline-only/v1", |_| {
            unreachable!("an empty discovery has no fold calls")
        })
        .map_err(|e| AdmissionRefusal::new("baseline", "invalid-declaration", e))?;
    assert!(generation.candidates().is_empty());
    let mut budget = manifest.campaign.budget;
    if let Some(depth) = d.max_depth {
        budget.max_depth = Some(depth);
    }
    let module = k_rust::kast::identifier::encode(&d.main_module);
    let campaign = Campaign {
        validator,
        module: &module,
        observation: &d.observation,
        classify: &all_normal,
        tests,
        budget,
    };
    let options = CampaignOptions {
        schedule: manifest.campaign.schedule,
        selection: manifest.campaign.selection,
        share_evidence: true,
    };
    run_campaign_multi(&campaign, &[generation], &options)
        .map(|run| {
            assert!(run.mutants.is_empty());
        })
        .map_err(|e| {
            let reason = match e.kind() {
                CampaignFailureKind::InvalidManifest => "invalid-manifest",
                CampaignFailureKind::InvalidDeclaration => "invalid-declaration",
                CampaignFailureKind::ForeignGeneration => "foreign-generation",
                CampaignFailureKind::FabricatedSkip => "fabricated-skip",
                CampaignFailureKind::BaselineInvalid => "baseline-invalid",
                CampaignFailureKind::BaselineOracleFailed => "baseline-oracle-failed",
                CampaignFailureKind::BaselineError => "baseline-error",
            };
            AdmissionRefusal::new("baseline", reason, e)
        })
}

// The CS-02 resolver has no pin callback. This local adapter follows that exact
// lookup order but verifies bytes before handing any source to k-rust's loader.
struct PinnedResolver<'a> {
    root: PathBuf,
    includes: &'a [String],
    pins: BTreeMap<String, kink_patch::Sha256Digest>,
    files: BTreeMap<String, kink_patch::Sha256Digest>,
    failure: Option<AdmissionRefusal>,
}
impl PinnedResolver<'_> {
    fn read(&mut self, name: &str) -> Result<ResolvedSource, AdmissionRefusal> {
        let path = fs::canonicalize(self.root.join(name)).map_err(|_| {
            AdmissionRefusal::new("load", "load-error", format!("cannot resolve {name}"))
        })?;
        let relative = path.strip_prefix(&self.root).map_err(|_| {
            AdmissionRefusal::new("load", "load-error", "source escapes definition root")
        })?;
        let logical = relative
            .to_str()
            .ok_or_else(|| AdmissionRefusal::new("load", "load-error", "non-UTF-8 path"))?
            .to_owned();
        let digest = self.pins.get(&logical).ok_or_else(|| {
            AdmissionRefusal::new("load", "source-pin", format!("unlisted source {logical}"))
        })?;
        let bytes = fs::read(path).map_err(|_| {
            AdmissionRefusal::new("load", "load-error", format!("cannot read {logical}"))
        })?;
        let actual = sha256(&bytes);
        self.files.insert(logical.clone(), actual);
        if actual != *digest {
            return Err(AdmissionRefusal::new(
                "load",
                "source-pin",
                format!("source digest differs: {logical}"),
            ));
        }
        let text =
            String::from_utf8(bytes).map_err(|e| AdmissionRefusal::new("load", "load-error", e))?;
        Ok(ResolvedSource::new(logical, text))
    }
    fn lookup(
        &mut self,
        requiring: &str,
        required: &str,
    ) -> Result<ResolvedSource, AdmissionRefusal> {
        if Path::new(required).is_absolute() {
            return Err(AdmissionRefusal::new(
                "load",
                "load-error",
                "absolute require path",
            ));
        }
        let mut candidates = self
            .includes
            .iter()
            .map(|dir| Some(Path::new(dir).join(required)))
            .collect::<Vec<_>>();
        candidates.push(None);
        if !requiring.starts_with("krust-builtin://")
            && let Some(parent) = Path::new(requiring).parent()
        {
            candidates.insert(1.min(candidates.len()), Some(parent.join(required)));
        }
        for candidate in candidates {
            match candidate {
                None => {
                    if let Some(source) = builtin::embedded(required) {
                        return Ok(source);
                    }
                }
                Some(path) => match fs::canonicalize(self.root.join(&path)) {
                    Err(e) if e.kind() == std::io::ErrorKind::NotFound => continue,
                    Err(_) => {
                        return Err(AdmissionRefusal::new(
                            "load",
                            "load-error",
                            format!("cannot resolve {required}"),
                        ));
                    }
                    Ok(p) if !p.starts_with(&self.root) => {
                        return Err(AdmissionRefusal::new(
                            "load",
                            "load-error",
                            "source escapes definition root",
                        ));
                    }
                    Ok(_) => {
                        return self.read(path.to_str().ok_or_else(|| {
                            AdmissionRefusal::new("load", "load-error", "non-UTF-8 path")
                        })?);
                    }
                },
            }
        }
        Err(AdmissionRefusal::new(
            "load",
            "load-error",
            format!("{required} not found from {requiring}"),
        ))
    }
}
impl SourceResolver for PinnedResolver<'_> {
    fn resolve(&mut self, requiring: &str, required: &str) -> Result<ResolvedSource, String> {
        self.lookup(requiring, required).map_err(|e| {
            let text = e.detail.clone();
            self.failure = Some(e);
            text
        })
    }
}
type InputTexts = BTreeMap<String, String>;
fn pinned_load(
    d: &DefinitionSpec,
    workspace: &Path,
    record: &mut AdmissionRecord,
) -> Result<(LoadedSource, InputTexts), AdmissionRefusal> {
    let root = fs::canonicalize(workspace.join(&d.root.path))
        .map_err(|_| AdmissionRefusal::new("load", "load-error", "definition root unavailable"))?;
    let mut resolver = PinnedResolver {
        root: root.clone(),
        includes: &d.include_dirs,
        pins: d.files.iter().map(|f| (f.name.clone(), f.sha256)).collect(),
        files: BTreeMap::new(),
        failure: None,
    };
    let result = (|| {
        let entry = resolver.read(&d.entry)?;
        let options = LoadOptions {
            markdown_selector: d.md_selector.clone().unwrap_or_else(|| "k".into()),
            implicit_sources: vec![
                builtin::embedded("kast.md").expect("embedded kast"),
                builtin::embedded("prelude.md").expect("embedded prelude"),
            ],
            excluded_module_attributes: vec![
                CompilationBackend::Rust.excluded_module_attribute().into(),
            ],
            ..LoadOptions::default()
        };
        let loaded = load_for_compilation(
            entry,
            &d.main_module,
            d.syntax_module.as_deref(),
            &mut resolver,
            &options,
        );
        if let Some(e) = resolver.failure.take() {
            return Err(e);
        }
        let (loaded, syntax_module) =
            loaded.map_err(|e| AdmissionRefusal::new("load", "load-error", e))?;
        let mut texts = BTreeMap::new();
        for test in &d.tests {
            let file = match &test.input {
                CorpusInput::Program(s) => match &s.program {
                    ProgramSource::File(f) => Some((f, None)),
                    _ => None,
                },
                CorpusInput::KoreState { file, sha256 } => Some((file, Some(*sha256))),
            };
            if let Some((file, own_pin)) = file {
                if let Some(digest) = own_pin {
                    let target = fs::canonicalize(root.join(file)).map_err(|_| {
                        AdmissionRefusal::new("load", "load-error", "input file unavailable")
                    })?;
                    let relative = target.strip_prefix(&root).map_err(|_| {
                        AdmissionRefusal::new("load", "load-error", "input escapes definition root")
                    })?;
                    let name = relative.to_str().ok_or_else(|| {
                        AdmissionRefusal::new("load", "load-error", "non-UTF-8 path")
                    })?;
                    if resolver.pins.get(name).is_some_and(|p| *p != digest) {
                        return Err(AdmissionRefusal::new(
                            "load",
                            "source-pin",
                            "inconsistent input pins",
                        ));
                    }
                    resolver.pins.insert(name.into(), digest);
                }
                let input = resolver.read(file)?;
                texts.insert(file.clone(), input.text);
            }
        }
        Ok((loaded, syntax_module, texts))
    })();
    record.files = resolver
        .files
        .into_iter()
        .map(|(name, sha256)| SourceFile { name, sha256 })
        .collect();
    let (loaded, syntax_module, texts) = result?;
    Ok((
        LoadedSource {
            baseline: Baseline::new(loaded),
            files: record.files.clone(),
            root,
            syntax_module,
        },
        texts,
    ))
}
