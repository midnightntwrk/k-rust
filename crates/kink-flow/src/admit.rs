//! Admission of a flow specification and its programs, through kink-corpus's admission
//! stages (`kink_corpus::admission`), with kink-corpus's stage names and refusal reasons.
//!
//! The order is kink-corpus's, without the stages that only a corpus manifest has (source
//! pins, solver profile, oracles): the below-floor exclusion of the entry, the load
//! (`kink_corpus::load_source`, which records every non-builtin file read), the
//! below-floor exclusion of every loaded file, the semantic-input canonical check, the
//! compile with its kompile warnings, the representation gate (TB-03), the declaration
//! census (VI-T13) and the input backend. Then each program is admitted on its own: its
//! file is read inside the manifest's directory, its configuration is assembled, and the
//! concrete-state check and the input gate run. A refused program never stops the others.

use crate::manifest::{FlowManifest, Program};
use kink_campaign::TestCase;
use kink_corpus::{
    CorpusSource, LoadedSource, ProgramSource, TestInputSpec,
    admission::{
        AdmissionRecord, AdmissionRefusal, below_floor_exclusions, check_exclusions,
        check_initial_state, check_loaded_semantic_input, compile_definition, input_backend,
        path_names_case, program_input,
    },
    load_source,
    manifest::Exclusion,
};
use kink_native::{NativeValidator, ValidatedDefinition};
use kink_patch::SemanticInput;
use std::{
    fs,
    path::{Path, PathBuf},
};

/// The record name of a flow specification in its [`AdmissionRecord`].
pub const SPEC_RECORD_NAME: &str = "spec";

/// An admitted specification.
#[derive(Clone, Debug)]
pub struct AdmittedSpec {
    pub loaded: LoadedSource,
    pub semantic_input: SemanticInput,
    pub compiled: ValidatedDefinition,
    /// The validator the specification was compiled with; its baseline compile is memoised.
    pub validator: NativeValidator,
}

/// The admission of one program.
#[derive(Clone, Debug)]
pub struct ProgramAdmission {
    pub id: String,
    /// The program's concrete initial configuration as a test case with no oracles (the
    /// caller chooses the oracles), or the refusal.
    pub outcome: Result<TestCase, AdmissionRefusal>,
}

/// The admission of a whole manifest. A refused specification has no programs.
#[derive(Clone, Debug)]
pub struct FlowAdmission {
    pub record: AdmissionRecord,
    pub spec: Option<AdmittedSpec>,
    pub programs: Vec<ProgramAdmission>,
}

impl FlowAdmission {
    /// The specification is admitted and every program is admitted.
    pub fn all_admitted(&self) -> bool {
        self.spec.is_some() && self.programs.iter().all(|p| p.outcome.is_ok())
    }
}

/// Admit the manifest's specification and then each of its programs.
pub fn admit(manifest: &FlowManifest) -> FlowAdmission {
    let mut record = AdmissionRecord::new(SPEC_RECORD_NAME);
    let admitted = admit_spec(manifest, &mut record).and_then(|spec| {
        let backend = input_backend(&spec.compiled, &manifest.spec.main_module)?;
        Ok((spec, backend))
    });
    let (spec, mut backend) = match admitted {
        Ok(admitted) => admitted,
        Err(refusal) => {
            record.refusal = Some(refusal);
            return FlowAdmission {
                record,
                spec: None,
                programs: Vec::new(),
            };
        }
    };
    let root = spec_root(manifest);
    let programs = manifest
        .programs
        .iter()
        .map(|program| ProgramAdmission {
            id: program.id.clone(),
            outcome: root.clone().and_then(|root| {
                let test = initial_state(&spec.loaded, &root, program)?;
                check_initial_state(&mut backend, &test.initial_state)?;
                Ok(test)
            }),
        })
        .collect();
    FlowAdmission {
        record,
        spec: Some(spec),
        programs,
    }
}

fn load_refusal(detail: impl ToString) -> AdmissionRefusal {
    AdmissionRefusal {
        stage: "load".into(),
        reason: "load-error".into(),
        detail: detail.to_string(),
    }
}

fn spec_root(manifest: &FlowManifest) -> Result<PathBuf, AdmissionRefusal> {
    fs::canonicalize(&manifest.directory)
        .map_err(|_| load_refusal("the manifest's directory is unavailable"))
}

/// The below-floor exclusion stage for one source path, matched both lexically (as the
/// manifest names it) and after resolving links (kink-corpus `check_exclusions`).
fn check_below_floor(
    exclusions: &[Exclusion],
    lexical: &Path,
    resolved: &Path,
) -> Result<(), AdmissionRefusal> {
    check_exclusions(exclusions, resolved, |exclusion| {
        path_names_case(lexical, &exclusion.case)
    })
}

fn admit_spec(
    manifest: &FlowManifest,
    record: &mut AdmissionRecord,
) -> Result<AdmittedSpec, AdmissionRefusal> {
    let spec = &manifest.spec;
    let exclusions = below_floor_exclusions();
    let entry = manifest.directory.join(&spec.entry);
    check_below_floor(&exclusions, &entry, &entry)?;
    let loaded = load_source(&CorpusSource {
        root: manifest.directory.clone(),
        entry: spec.entry.clone(),
        include_dirs: spec.include_dirs.clone(),
        main_module: spec.main_module.clone(),
        syntax_module: spec.syntax_module.clone(),
        md_selector: Some(spec.md_selector.clone()),
    })
    .map_err(load_refusal)?;
    record.files = loaded.files.clone();
    let root = spec_root(manifest)?;
    for file in &loaded.files {
        check_below_floor(
            &exclusions,
            &manifest.directory.join(&file.name),
            &root.join(&file.name),
        )?;
    }
    let semantic_input = check_loaded_semantic_input(&loaded)?;
    let validator = NativeValidator::bind(loaded.baseline.clone(), Default::default());
    let compiled = compile_definition(&validator, record)?;
    Ok(AdmittedSpec {
        loaded,
        semantic_input,
        compiled,
        validator,
    })
}

/// Read a program file inside the canonical manifest directory `root`, as kink-corpus
/// reads corpus input files (`load` stage, `load-error` reason; the detail names the file
/// as the manifest does, never by an absolute path).
fn read_program(root: &Path, name: &str) -> Result<String, AdmissionRefusal> {
    let path = fs::canonicalize(root.join(name))
        .map_err(|e| load_refusal(format!("cannot read {name}: {e}")))?;
    if !path.starts_with(root) {
        return Err(load_refusal(format!(
            "{name} escapes the manifest's directory"
        )));
    }
    let bytes = fs::read(&path).map_err(|e| load_refusal(format!("cannot read {name}: {e}")))?;
    String::from_utf8(bytes).map_err(|e| load_refusal(format!("{name} is not UTF-8: {e}")))
}

fn initial_state(
    loaded: &LoadedSource,
    root: &Path,
    program: &Program,
) -> Result<TestCase, AdmissionRefusal> {
    let text = match &program.source {
        ProgramSource::Text(text) => text.clone(),
        ProgramSource::File(name) => read_program(root, name)?,
    };
    let initial_state = program_input(
        loaded,
        &TestInputSpec {
            program: ProgramSource::Text(text),
            start_sort: program.start_sort.clone(),
            variables: program.variables.clone(),
        },
    )?;
    Ok(TestCase {
        id: program.id.clone(),
        initial_state,
        oracles: Vec::new(),
    })
}
