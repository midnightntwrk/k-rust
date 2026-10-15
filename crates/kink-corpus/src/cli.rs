//! Process plumbing for the corpus library; campaign evidence is published by
//! `run_definition`, and summaries are computed by `summarize`.

use crate::{
    CorpusSource, ProgramSource, load_source,
    manifest::{CorpusInput, CorpusManifest, DefinitionSpec, exclusion_applies, path_excluded},
    resolver::read_under_root,
    runner::{CLASSIFIER, all_normal, run_definition},
    store::{Store, StoreError, time_bound_fired},
    summary::summarize,
};
use kink_campaign::{
    Projection, ReplayDeclaration, ReplayOperator, ReplayOutcome, replay_with_budget,
};
use kink_native::execution::SolverProfile;
use kink_patch::{
    Baseline, CAMPAIGN_MANIFEST_DOMAIN, CandidateDisposition, CandidateGeneration, Completeness,
    OBSERVATION_DOMAIN, OperatorSpec, SemanticInput, Sha256Digest, TEST_MANIFEST_DOMAIN,
    canonical_json, payload_digest, resolve_universe, sha256,
};
use serde_json::{Value, json};
use std::{
    collections::BTreeMap,
    ffi::OsString,
    fs,
    io::Write,
    path::{Component, Path, PathBuf},
    process::Command,
    time::Instant,
};

/// The corpus scout used this stack for KMIR and KEVM admission and compilation
/// (prototype/corpora/s6_corpus_probe.rs, `with_stack`; README section 2 records
/// the measured 449 MB / 1.54 GB process footprints). Keep the measured stack
/// allowance explicit rather than relying on the platform's thread default.
pub const DEFINITION_STACK_BYTES: usize = 256 << 20;

const USAGE: &str = "usage: kink-corpus pin --workspace DIR MANIFEST | run --workspace DIR --store DIR MANIFEST | definition --workspace DIR --store DIR MANIFEST ID | summary --store DIR MANIFEST_SHA256 PROFILE | replay-check --workspace DIR --store DIR MANIFEST ID";

struct Arguments {
    command: String,
    workspace: Option<PathBuf>,
    store: Option<PathBuf>,
    positional: Vec<OsString>,
}
impl Arguments {
    fn parse(args: Vec<OsString>) -> Result<Self, StoreError> {
        let mut args = args.into_iter();
        let command = args
            .next()
            .and_then(|s| s.into_string().ok())
            .ok_or_else(|| invalid(USAGE))?;
        let mut result = Self {
            command,
            workspace: None,
            store: None,
            positional: Vec::new(),
        };
        let mut rest = args;
        while let Some(arg) = rest.next() {
            if arg == "--" {
                result.positional.extend(rest);
                break;
            }
            let slot = match arg.to_str() {
                Some("--workspace") => Some(&mut result.workspace),
                Some("--store") => Some(&mut result.store),
                Some(s) if s.starts_with('-') => return Err(invalid(USAGE)),
                _ => None,
            };
            if let Some(slot) = slot {
                if slot.is_some() {
                    return Err(invalid(USAGE));
                }
                *slot = Some(PathBuf::from(rest.next().ok_or_else(|| invalid(USAGE))?));
            } else {
                result.positional.push(arg);
            }
        }
        Ok(result)
    }
    fn workspace(&self) -> Result<&Path, StoreError> {
        self.workspace.as_deref().ok_or_else(|| invalid(USAGE))
    }
    fn store(&self) -> Result<Store, StoreError> {
        self.store
            .as_ref()
            .map(Store::new)
            .ok_or_else(|| invalid(USAGE))
    }
    fn text(&self, index: usize) -> Result<&str, StoreError> {
        self.positional
            .get(index)
            .and_then(|s| s.to_str())
            .ok_or_else(|| invalid(USAGE))
    }
    fn check(&self, count: usize, workspace: bool, store: bool) -> Result<(), StoreError> {
        if self.positional.len() != count
            || self.workspace.is_some() != workspace
            || self.store.is_some() != store
        {
            return Err(invalid(USAGE));
        }
        Ok(())
    }
    fn manifest(&self) -> Result<CorpusManifest, StoreError> {
        let text = fs::read_to_string(Path::new(&self.positional[0]))?;
        CorpusManifest::from_canonical_json(&text).map_err(|e| invalid(e.to_string()))
    }
}

fn invalid(message: impl Into<String>) -> StoreError {
    StoreError::Invalid(message.into())
}

/// Execute one command. Only `definition` reads KINK_CORPUS_TEST_ABORT: it is a
/// test-only child-process abort hook, never a campaign or manifest input.
pub fn execute(args: Vec<OsString>) -> Result<(), StoreError> {
    let args = Arguments::parse(args)?;
    match args.command.as_str() {
        "pin" => {
            args.check(1, true, false)?;
            let workspace = args.workspace()?.to_owned();
            let manifest = args.manifest()?;
            let path = PathBuf::from(&args.positional[0]);
            on_stack(move || pin(&workspace, &manifest, &path))
        }
        "run" => {
            args.check(1, true, true)?;
            run(&args, &args.manifest()?, &args.store()?)
        }
        "definition" => {
            args.check(2, true, true)?;
            let manifest = args.manifest()?;
            let id = args.text(1)?.to_owned();
            if !manifest.definitions().iter().any(|d| d.id == id) {
                return Err(invalid("definition is not listed"));
            }
            if std::env::var("KINK_CORPUS_TEST_ABORT").is_ok_and(|value| value == id) {
                std::process::abort();
            }
            let workspace = args.workspace()?.to_owned();
            let store = args.store()?;
            on_stack(move || {
                let outcome = run_definition(&workspace, &manifest, &id, &store)?;
                let _ = writeln!(
                    std::io::stdout().lock(),
                    "{id}: {}",
                    if outcome.resumed {
                        "resumed"
                    } else {
                        "completed"
                    }
                );
                Ok(())
            })
        }
        "summary" => {
            args.check(2, false, true)?;
            publish_summary(&args.store()?, args.text(0)?, args.text(1)?, false)
        }
        "replay-check" => {
            args.check(2, true, true)?;
            let manifest = args.manifest()?;
            let store = args.store()?;
            let id = args.text(1)?.to_owned();
            on_stack(move || replay_check(&store, &manifest, &id))
        }
        _ => Err(invalid(USAGE)),
    }
}

fn on_stack(
    body: impl FnOnce() -> Result<(), StoreError> + Send + 'static,
) -> Result<(), StoreError> {
    std::thread::Builder::new()
        .name("corpus-definition".into())
        .stack_size(DEFINITION_STACK_BYTES)
        .spawn(body)?
        .join()
        .map_err(|_| invalid("definition thread panicked"))?
}

fn pin(workspace: &Path, manifest: &CorpusManifest, path: &Path) -> Result<(), StoreError> {
    let mut value = manifest.value();
    for (row, definition) in value["definitions"]
        .as_array_mut()
        .expect("validated definitions")
        .iter_mut()
        .zip(manifest.definitions())
    {
        let root = fs::canonicalize(workspace.join(&definition.root.path))?;
        let loaded = load_source(&CorpusSource {
            root: root.clone(),
            entry: definition.entry.clone(),
            include_dirs: definition.include_dirs.clone(),
            main_module: definition.main_module.clone(),
            syntax_module: definition.syntax_module.clone(),
            md_selector: definition.md_selector.clone(),
        })
        .map_err(|e| invalid(e.to_string()))?;
        let mut files = loaded
            .files
            .into_iter()
            .map(|f| (f.name, f.sha256))
            .collect::<BTreeMap<_, _>>();
        for test in &definition.tests {
            let file = match &test.input {
                CorpusInput::Program(spec) => match &spec.program {
                    ProgramSource::File(file) => Some(file),
                    ProgramSource::Text(_) => None,
                },
                CorpusInput::KoreState { file, .. } => Some(file),
            };
            if let Some(file) = file {
                let (name, bytes) =
                    read_under_root(&root, file).map_err(|e| invalid(e.to_string()))?;
                files.insert(name, sha256(&bytes));
            }
        }
        row["files"] = json!(
            files
                .into_iter()
                .map(|(name, sha256)| json!({"name":name,"sha256":sha256.to_string()}))
                .collect::<Vec<_>>()
        );
    }
    let text = canonical_json(&value);
    CorpusManifest::from_canonical_json(&text).map_err(|e| invalid(e.to_string()))?;
    Store::new(PathBuf::new()).write_text(path, &text)
}

fn run(args: &Arguments, manifest: &CorpusManifest, store: &Store) -> Result<(), StoreError> {
    // Shared declaration precedes child launch, including a child that aborts.
    store.ensure_manifest(manifest)?;
    let profile = SolverProfile::BUILD.name();
    for definition in manifest.definitions() {
        remove_process_record(store, manifest, &definition.id)?;
        if resume_completed(args.workspace()?, manifest, &definition.id, store)? {
            let _ = writeln!(std::io::stdout().lock(), "{}: resumed", definition.id);
            continue;
        }
        let start = Instant::now();
        let status = Command::new(std::env::current_exe()?)
            .arg("definition")
            .arg("--workspace")
            .arg(args.workspace()?)
            .arg("--store")
            .arg(store.root())
            .arg("--")
            .arg(
                store
                    .corpus_path(manifest.digest())
                    .join("corpus-manifest.json"),
            )
            .arg(&definition.id)
            .status();
        let failed = match &status {
            Ok(status) => !status.success(),
            Err(_) => true,
        };
        let completed_after_failure = failed
            && resume_completed(args.workspace()?, manifest, &definition.id, store)
                .unwrap_or(false);
        if failed && !completed_after_failure {
            // Process availability is admission metadata, never campaign evidence.
            store.write_json(
                &store.admission_path(manifest.digest(), profile, &definition.id)?,
                &process_record(&definition.id),
            )?;
        }
        let log = store
            .profile_path(manifest.digest(), profile)
            .join("timings.log");
        fs::create_dir_all(log.parent().expect("profile directory"))?;
        let mut log = fs::OpenOptions::new().create(true).append(true).open(log)?;
        writeln!(
            log,
            "{}\t{:.6}\t{}",
            definition.id,
            start.elapsed().as_secs_f64(),
            if completed_after_failure {
                "completed after child failure"
            } else if failed {
                "process-error"
            } else {
                "completed"
            }
        )?;
    }
    publish_summary(store, &manifest.digest().to_string(), profile, true)
}

fn process_record(id: &str) -> Value {
    json!({"definition":id,"outcome":"error","stage":"process","reason":"process","detail":null,"files":[],"census":null,"representation":null,"kompile_warnings":null})
}

/// Only remove this parent's exact process metadata, never campaign evidence.
/// An absent admission makes the library re-admit the definition in a child,
/// even when an earlier failed attempt left a published index entry.
fn remove_process_record(
    store: &Store,
    manifest: &CorpusManifest,
    id: &str,
) -> Result<(), StoreError> {
    let path = store.admission_path(manifest.digest(), SolverProfile::BUILD.name(), id)?;
    if path.exists() && store.read_json(&path)? == process_record(id) {
        fs::remove_file(path)?;
    }
    Ok(())
}

/// Probe file presence before asking the library to validate a completed entry.
/// Missing files go to an isolated child; corrupt completed evidence refuses
/// without replacing its admission record with a process error.
fn resume_completed(
    workspace: &Path,
    manifest: &CorpusManifest,
    id: &str,
    store: &Store,
) -> Result<bool, StoreError> {
    let profile = SolverProfile::BUILD.name();
    let index = store.read_index(manifest.digest(), profile)?;
    let Some(entry) = index.get(id) else {
        return Ok(false);
    };
    let digest = entry["manifest_sha256"]
        .as_str()
        .and_then(Sha256Digest::parse)
        .ok_or_else(|| invalid("indexed campaign digest"))?;
    let base = store.profile_path(manifest.digest(), profile);
    let report_path = base.join(format!("campaigns/{digest}.json"));
    if !store
        .admission_path(manifest.digest(), profile, id)?
        .exists()
        || !report_path.exists()
    {
        return Ok(false);
    }
    let report = store.read_json(&report_path)?;
    let artifact = report["manifest"]["baseline"]["semantic_input_sha256"]
        .as_str()
        .and_then(Sha256Digest::parse)
        .ok_or_else(|| invalid("indexed artifact digest"))?;
    if !base
        .join(format!("semantic-input/{artifact}.json"))
        .exists()
    {
        return Ok(false);
    }
    let workspace = workspace.to_owned();
    let manifest = manifest.clone();
    let id = id.to_owned();
    let store = store.clone();
    on_stack(move || {
        let outcome = run_definition(&workspace, &manifest, &id, &store)?;
        if !outcome.resumed {
            return Err(invalid("completed entry disappeared during resume"));
        }
        verify_binding(&workspace, &store, &manifest, &id, &report)?;
        Ok(())
    })?;
    Ok(true)
}

/// The store directory selects the corpus declaration. Also bind a completed
/// report to that declaration before skipping a child, so moving old evidence
/// into another corpus directory cannot silently resume it.
fn verify_binding(
    workspace: &Path,
    store: &Store,
    corpus: &CorpusManifest,
    id: &str,
    report: &serde_json::Value,
) -> Result<(), StoreError> {
    let definition_index = corpus
        .definitions()
        .iter()
        .position(|d| d.id == id)
        .ok_or_else(|| invalid("definition is not listed"))?;
    let definition = &corpus.definitions()[definition_index];
    verify_admission_stages(workspace, corpus, definition)?;
    let declaration = corpus.value();
    let campaign = &report["manifest"];
    let mut budget = declaration["campaign"]["budget"].clone();
    if let Some(depth) = definition.max_depth {
        budget["max_depth"] = json!(depth);
    }
    if campaign["module"] != k_rust::kast::identifier::encode(&definition.main_module)
        || campaign["budget"] != budget
        || campaign["budget_mutants"] != declaration["campaign"]["budget_mutants"]
        || campaign["schedule"] != declaration["campaign"]["schedule"]
        || campaign["selection"] != declaration["campaign"]["selection"]
        || campaign["classifier"] != CLASSIFIER
    {
        return Err(invalid("stored campaign declaration differs"));
    }
    let operators = campaign["operators"]
        .as_array()
        .ok_or_else(|| invalid("stored operators"))?;
    if operators.len() != corpus.operators().len()
        || operators
            .iter()
            .zip(corpus.operators())
            .any(|(row, spec)| row["kind"] != "spec" || row["spec"] != spec.canonical_value())
    {
        return Err(invalid("stored operator declaration differs"));
    }
    let digest = campaign["baseline"]["semantic_input_sha256"]
        .as_str()
        .and_then(Sha256Digest::parse)
        .ok_or_else(|| invalid("baseline artifact digest"))?;
    let artifact = fs::read_to_string(
        store
            .profile_path(corpus.digest(), SolverProfile::BUILD.name())
            .join(format!("semantic-input/{digest}.json")),
    )?;
    let (_, baseline) = SemanticInput::read(&artifact).map_err(|e| invalid(e.to_string()))?;
    let admission = store.read_json(&store.admission_path(
        corpus.digest(),
        SolverProfile::BUILD.name(),
        id,
    )?)?;
    verify_sources(workspace, corpus, definition, &admission, digest)?;
    verify_generations(corpus, &baseline, campaign, operators)?;
    let tests = store.rebuild_tests(corpus.digest(), id, &baseline)?;
    let mut rows = Vec::new();
    for (test_index, test) in tests.iter().enumerate() {
        let mut oracles =
            declaration["definitions"][definition_index]["tests"][test_index]["oracles"].clone();
        for (row, oracle) in oracles
            .as_array_mut()
            .expect("validated oracles")
            .iter_mut()
            .zip(&test.oracles)
        {
            if let Projection::Pattern { plan, .. } = oracle.projection() {
                // PatternPlan stores variables in name order; all other oracle
                // fields round-trip through the corpus/campaign data grammar.
                row["projection"]["pattern"]["plan"]["variables"] = json!(
                    plan.variables
                        .iter()
                        .map(|(name, sort)| json!({"name":name,"sort":sort.to_string()}))
                        .collect::<Vec<_>>()
                );
            }
        }
        rows.push(json!({"id":test.id,"initial_state":k_rust::kore::codec::to_value(&test.initial_state).map_err(|e| invalid(e.to_string()))?,"oracles":oracles}));
    }
    let tests_digest = payload_digest(
        TEST_MANIFEST_DOMAIN,
        canonical_json(&json!(rows)).as_bytes(),
    );
    let observation = definition.observation.iter().map(|spec| Ok(json!({"constructor":spec.constructor,"pre":k_rust::kore::codec::to_value(&spec.pre).map_err(|e| invalid(e.to_string()))?,"post":spec.post.as_ref().map(k_rust::kore::codec::to_value).transpose().map_err(|e| invalid(e.to_string()))?,"payload":spec.payload}))).collect::<Result<Vec<_>, StoreError>>()?;
    if campaign["tests"] != json!({"count":tests.len(),"sha256":tests_digest.to_string()})
        || campaign["observation_sha256"]
            != payload_digest(
                OBSERVATION_DOMAIN,
                canonical_json(&json!(observation)).as_bytes(),
            )
            .to_string()
    {
        return Err(invalid("stored tests or observation differ"));
    }
    Ok(())
}

fn verify_admission_stages(
    workspace: &Path,
    corpus: &CorpusManifest,
    definition: &DefinitionSpec,
) -> Result<(), StoreError> {
    // Match both lexical identities and resolved paths, exactly as admission.
    let canonical = fs::canonicalize(
        workspace
            .join(&definition.root.path)
            .join(&definition.entry),
    )
    .ok();
    let parts = canonical.as_ref().map(|path| {
        path.components()
            .filter_map(|part| match part {
                Component::Normal(name) => name.to_str().map(str::to_owned),
                _ => None,
            })
            .collect::<Vec<_>>()
    });
    if corpus.exclusions().iter().any(|exclusion| {
        exclusion_applies(definition, exclusion)
            || parts
                .as_ref()
                .is_some_and(|p| path_excluded(p, &exclusion.case))
    }) {
        return Err(invalid("stored definition is excluded"));
    }
    if definition
        .requires_profile
        .is_some_and(|p| p != SolverProfile::BUILD)
    {
        return Err(invalid("stored definition requires another profile"));
    }
    Ok(())
}

fn verify_sources(
    workspace: &Path,
    corpus: &CorpusManifest,
    definition: &DefinitionSpec,
    admission: &Value,
    artifact_digest: Sha256Digest,
) -> Result<(), StoreError> {
    let root = fs::canonicalize(workspace.join(&definition.root.path))?;
    let loaded = load_source(&CorpusSource {
        root: root.clone(),
        entry: definition.entry.clone(),
        include_dirs: definition.include_dirs.clone(),
        main_module: definition.main_module.clone(),
        syntax_module: definition.syntax_module.clone(),
        md_selector: definition.md_selector.clone(),
    })
    .map_err(|e| invalid(e.to_string()))?;
    // Every loaded source, as admission checks it (flow F-16): a store admitted before that
    // check cannot resume a definition that reads a below-floor source.
    crate::admission::check_loaded_exclusions(
        corpus.exclusions(),
        Path::new(&definition.root.path),
        &root,
        &loaded.files,
    )
    .map_err(|_| invalid("stored definition is excluded"))?;
    let mut expected = BTreeMap::new();
    for file in &loaded.files {
        if !definition.files.iter().any(|pin| pin == file) {
            return Err(invalid("loaded source pins differ"));
        }
        expected.insert(file.name.clone(), file.sha256);
    }
    // Admission's files list is the union of loaded sources and file inputs.
    // Bind the input rows to their declared pins; test bytes still come only
    // from the digest-checked store, not from the workspace.
    for test in &definition.tests {
        let input = match &test.input {
            CorpusInput::Program(spec) => match &spec.program {
                ProgramSource::File(file) => Some((
                    file,
                    definition
                        .files
                        .iter()
                        .find(|pin| pin.name == *file)
                        .ok_or_else(|| invalid("missing input pin"))?
                        .sha256,
                )),
                ProgramSource::Text(_) => None,
            },
            CorpusInput::KoreState { file, sha256 } => Some((file, *sha256)),
        };
        if let Some((file, digest)) = input {
            let name = match fs::canonicalize(root.join(file)) {
                Ok(path) => path
                    .strip_prefix(&root)
                    .map_err(|_| invalid("input escapes definition root"))?
                    .to_str()
                    .ok_or_else(|| invalid("non-UTF-8 input name"))?
                    .to_owned(),
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => file.clone(),
                Err(error) => return Err(error.into()),
            };
            if expected
                .insert(name, digest)
                .is_some_and(|old| old != digest)
            {
                return Err(invalid("inconsistent source and input pins"));
            }
        }
    }
    let files = expected
        .into_iter()
        .map(|(name, sha256)| json!({"name":name,"sha256":sha256.to_string()}))
        .collect::<Vec<_>>();
    if admission["files"] != json!(files)
        || SemanticInput::of(&loaded.baseline)
            .map_err(|e| invalid(e.to_string()))?
            .digest()
            != artifact_digest
    {
        return Err(invalid("stored sources differ from declared load"));
    }
    Ok(())
}

/// Reproduce the campaign encoder's generation metadata, without compiling.
fn generation_value(generation: &CandidateGeneration<'_>) -> Value {
    let failure = generation.failure().map(|failure| {
        let mut name = String::new();
        for (index, ch) in format!("{failure:?}").chars().enumerate() {
            if index > 0 && ch.is_uppercase() {
                name.push('-');
            }
            name.extend(ch.to_lowercase());
        }
        name
    });
    json!({"origins":generation.selected_origins().len(),
        "rejected_origins":generation.dispositions().iter().filter(|d| matches!(d, CandidateDisposition::Rejected(_))).count(),
        "completeness":match generation.completeness() { Completeness::CompleteFinite => "complete-finite", Completeness::Incomplete => "incomplete" },
        "failure":failure,"scored":generation.scored()})
}

fn verify_generations(
    corpus: &CorpusManifest,
    baseline: &Baseline,
    campaign: &Value,
    operators: &[Value],
) -> Result<(), StoreError> {
    let config = corpus.campaign();
    let universe = resolve_universe(baseline, corpus.universe());
    if campaign["universe"] != universe.value() {
        return Err(invalid("stored universe differs"));
    }
    let cap = usize::try_from(config.max_candidates_per_spec)
        .map_err(|_| invalid("candidate maximum does not fit usize"))?;
    let specs = corpus
        .operators()
        .iter()
        .map(|spec| (spec, cap))
        .collect::<Vec<_>>();
    let budget = config.budget_mutants.as_ref();
    let declaration = corpus.value();
    let generations = OperatorSpec::generate_all(
        baseline,
        &universe,
        &specs,
        budget.map(|b| (b.per_spec_max, b.total_max, b.seed.as_slice())),
    )
    .map_err(|e| invalid(e.to_string()))?;
    let mutants = campaign["mutants"]
        .as_array()
        .ok_or_else(|| invalid("stored mutants"))?;
    let mut mutant_index = 0;
    for (operator_index, ((spec, generation), row)) in corpus
        .operators()
        .iter()
        .zip(&generations)
        .zip(operators)
        .enumerate()
    {
        let (population, digest) = spec
            .population(baseline, &universe)
            .map_err(|e| invalid(e.to_string()))?;
        let sampling = budget.map(|_| {
            json!({"seed":declaration["campaign"]["budget_mutants"]["seed"],
            "size":generation.selected_origins().len(),"population":population})
        });
        if row["generation"] != generation_value(generation)
            || row["population"] != json!(population)
            || row["population_sha256"] != digest.to_string()
            || row["sampling"] != json!(sampling)
        {
            return Err(invalid("stored generation differs"));
        }
        for candidate in generation.candidates() {
            let row = mutants
                .get(mutant_index)
                .ok_or_else(|| invalid("stored candidate count differs"))?;
            if row["operator"] != json!(operator_index)
                || row["patch_sha256"]
                    != candidate
                        .patch
                        .digest()
                        .map_err(|e| invalid(e.to_string()))?
                        .to_string()
            {
                return Err(invalid("stored candidate differs"));
            }
            mutant_index += 1;
        }
    }
    if mutant_index != mutants.len() {
        return Err(invalid("stored candidate count differs"));
    }
    Ok(())
}

fn publish_summary(
    store: &Store,
    digest: &str,
    profile: &str,
    ignore_print_error: bool,
) -> Result<(), StoreError> {
    let store = store.clone();
    let digest = digest.to_owned();
    let profile = profile.to_owned();
    on_stack(move || publish_summary_on_stack(&store, &digest, &profile, ignore_print_error))
}

fn publish_summary_on_stack(
    store: &Store,
    digest: &str,
    profile: &str,
    ignore_print_error: bool,
) -> Result<(), StoreError> {
    let summary = summarize(store, digest, profile)?;
    let digest = Sha256Digest::parse(digest).ok_or_else(|| invalid("corpus manifest digest"))?;
    store.write_text(
        &store.profile_path(digest, profile).join("summary.json"),
        &summary.text(),
    )?;
    let printed = writeln!(std::io::stdout().lock(), "{}", summary.text());
    if !ignore_print_error {
        printed?;
    }
    Ok(())
}

fn replay_check(store: &Store, requested: &CorpusManifest, id: &str) -> Result<(), StoreError> {
    let corpus = store.read_manifest(requested.digest())?;
    let definition = corpus
        .definitions()
        .iter()
        .find(|d| d.id == id)
        .ok_or_else(|| invalid("definition is not listed"))?;
    let profile = SolverProfile::BUILD.name();
    let index = store.read_index(corpus.digest(), profile)?;
    let entry = index
        .get(id)
        .ok_or_else(|| invalid("definition has no stored campaign"))?;
    let digest = entry["manifest_sha256"]
        .as_str()
        .and_then(Sha256Digest::parse)
        .ok_or_else(|| invalid("indexed campaign digest"))?;
    let base = store.profile_path(corpus.digest(), profile);
    let path = base.join(format!("campaigns/{digest}.json"));
    let report_text = fs::read_to_string(&path)?;
    let report = store.read_json(&path)?;
    if report["manifest_sha256"] != digest.to_string()
        || report["manifest"]["profile"] != profile
        || sha256(report_text.as_bytes()).to_string() != entry["report_sha256"]
        || payload_digest(
            CAMPAIGN_MANIFEST_DOMAIN,
            canonical_json(&report["manifest"]).as_bytes(),
        ) != digest
        || entry["time_bound_fired"] != time_bound_fired(&report)
    {
        return Err(invalid("indexed report differs"));
    }
    if entry["time_bound_fired"] == true {
        println!("not-applicable: time-bound");
        return Ok(());
    }
    let artifact_digest = report["manifest"]["baseline"]["semantic_input_sha256"]
        .as_str()
        .and_then(Sha256Digest::parse)
        .ok_or_else(|| invalid("baseline artifact digest"))?;
    let artifact_name = format!("semantic-input/{artifact_digest}.json");
    if report["manifest"]["baseline"]["artifact"] != artifact_name {
        return Err(invalid("baseline artifact path differs"));
    }
    let artifact = fs::read_to_string(base.join(artifact_name))?;
    if sha256(artifact.as_bytes()) != artifact_digest {
        return Err(invalid("baseline artifact digest differs"));
    }
    let (_, baseline) = SemanticInput::read(&artifact).map_err(|e| invalid(e.to_string()))?;
    let tests = store.rebuild_tests(corpus.digest(), id, &baseline)?;
    let config = corpus.campaign();
    let mut budget = config.budget;
    if let Some(depth) = definition.max_depth {
        budget.max_depth = Some(depth);
    }
    let cap = usize::try_from(config.max_candidates_per_spec)
        .map_err(|_| invalid("candidate maximum does not fit usize"))?;
    let operators = corpus
        .operators()
        .iter()
        .map(|spec| ReplayOperator::Spec { spec, cap })
        .collect::<Vec<_>>();
    let module = k_rust::kast::identifier::encode(&definition.main_module);
    let declaration = ReplayDeclaration {
        module: &module,
        observation: &definition.observation,
        classify: &all_normal,
        classifier: CLASSIFIER,
        tests: &tests,
        budget,
        schedule: config.schedule,
        selection: config.selection,
        operators: &operators,
    };
    let outcome = replay_with_budget(
        &report_text,
        &artifact,
        &declaration,
        config.budget_mutants.as_ref(),
    );
    println!("{outcome:?}");
    if outcome == ReplayOutcome::Reproduced {
        Ok(())
    } else {
        Err(invalid("STOP: stored replay was not Reproduced"))
    }
}
