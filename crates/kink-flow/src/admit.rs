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
use k_rust::backend::Backend;
use kink_campaign::TestCase;
use kink_corpus::{
    CorpusSource, LoadedSource, ProgramSource, TestInputSpec,
    admission::{
        AdmissionRecord, AdmissionRefusal, below_floor_exclusions, check_exclusions,
        check_initial_state, check_loaded_exclusions, check_loaded_semantic_input,
        compile_definition, input_backend, path_names_case, program_input,
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
    let (record, admitted) = admit_spec(manifest);
    let Some((spec, mut inputs)) = admitted else {
        return FlowAdmission {
            record,
            spec: None,
            programs: Vec::new(),
        };
    };
    let programs = manifest
        .programs
        .iter()
        .map(|program| ProgramAdmission {
            id: program.id.clone(),
            outcome: inputs
                .text(program)
                .and_then(|text| inputs.test_case(&spec, program, text)),
        })
        .collect();
    FlowAdmission {
        record,
        spec: Some(spec),
        programs,
    }
}

/// Admit the manifest's specification alone: its record (refused or not) and, when it is
/// admitted, the specification with the means to admit its programs one at a time.
pub fn admit_spec(
    manifest: &FlowManifest,
) -> (AdmissionRecord, Option<(AdmittedSpec, ProgramInputs)>) {
    let mut record = AdmissionRecord::new(SPEC_RECORD_NAME);
    let admitted = admit_definition(manifest, &mut record).and_then(|spec| {
        let backend = input_backend(&spec.compiled, &manifest.spec.main_module)?;
        Ok((spec, backend))
    });
    match admitted {
        Ok((spec, backend)) => (
            record,
            Some((
                spec,
                ProgramInputs {
                    root: spec_root(manifest),
                    backend,
                },
            )),
        ),
        Err(refusal) => {
            record.refusal = Some(refusal);
            (record, None)
        }
    }
}

/// Admits the programs of an admitted specification, one at a time and in any order: the
/// manifest's canonical directory and the input gate's backend.
pub struct ProgramInputs {
    root: Result<PathBuf, AdmissionRefusal>,
    backend: Backend,
}

impl ProgramInputs {
    /// The program's text: its file read inside the manifest's directory (stage `load`,
    /// reason `load-error`), or its inline text.
    pub fn text(&self, program: &Program) -> Result<String, AdmissionRefusal> {
        let root = self.root.clone()?;
        match &program.source {
            ProgramSource::Text(text) => Ok(text.clone()),
            ProgramSource::File(name) => read_program(&root, name),
        }
    }

    /// The program's concrete initial configuration (`text` is [`Self::text`]'s result):
    /// assembled, then the concrete-state check and the input gate.
    pub fn test_case(
        &mut self,
        spec: &AdmittedSpec,
        program: &Program,
        text: String,
    ) -> Result<TestCase, AdmissionRefusal> {
        let test = initial_state(&spec.loaded, program, text)?;
        check_initial_state(&mut self.backend, &test.initial_state)?;
        Ok(test)
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

/// How kink-corpus `load_source` loads the manifest's specification (it records every
/// non-builtin file it reads).
pub fn corpus_source(manifest: &FlowManifest) -> CorpusSource {
    let spec = &manifest.spec;
    CorpusSource {
        root: manifest.directory.clone(),
        entry: spec.entry.clone(),
        include_dirs: spec.include_dirs.clone(),
        main_module: spec.main_module.clone(),
        syntax_module: spec.syntax_module.clone(),
        md_selector: Some(spec.md_selector.clone()),
    }
}

fn admit_definition(
    manifest: &FlowManifest,
    record: &mut AdmissionRecord,
) -> Result<AdmittedSpec, AdmissionRefusal> {
    let spec = &manifest.spec;
    let exclusions = below_floor_exclusions();
    let entry = manifest.directory.join(&spec.entry);
    check_below_floor(&exclusions, &entry, &entry)?;
    let loaded = load_source(&corpus_source(manifest)).map_err(load_refusal)?;
    record.files = loaded.files.clone();
    let root = spec_root(manifest)?;
    // kink-corpus's loaded-file exclusion stage (shared since flow F-16).
    check_loaded_exclusions(&exclusions, &manifest.directory, &root, &loaded.files)?;
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
    program: &Program,
    text: String,
) -> Result<TestCase, AdmissionRefusal> {
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
