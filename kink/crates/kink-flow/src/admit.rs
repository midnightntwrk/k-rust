//! Admission of a flow specification and its programs, through kink-corpus's admission
//! stages (`kink_corpus::admission`), with kink-corpus's stage names and refusal reasons.
//!
//! The order is kink-corpus's, without the stages that only a corpus manifest has (source
//! pins, solver profile, oracles): the below-floor case check of the entry (stage
//! `refused-case`), the load (`kink_corpus::load_source`, which records every non-builtin file
//! read), the below-floor case check of every loaded file, the semantic-input canonical check,
//! the compile with its kompile warnings, the representation gate (TB-03), the declaration
//! census (VI-T13), the input backend, and the definition's full critical-pair check on that
//! backend (stage `assume-joined`: every name of `[spec] assume_joined` must name exactly one
//! finding that can be assumed; fz26 KINK-BASELINE-FINDINGS). Then each program is admitted on
//! its own: its
//! file is read inside the manifest's directory, its configuration is assembled, and the
//! concrete-state check and the input gate run. A refused program never stops the others.
//!
//! Beside the data facts, admission reads the definition exclusions of the input backend's load
//! ([`AdmittedSpec::exclusions`], kink-native `DefinitionExclusions::of`, as the campaign runner
//! reads them for every run), and for each admitted program whether every run of it on the
//! baseline is excluded before it runs ([`ProgramAdmission::exclusion`]): by the definition
//! exclusion, or by the exclusion of its initial configuration. Neither refuses anything: a
//! program so excluded is admitted, `results` runs it and reports its class, and `check` fails
//! on it, since it cannot be judged on the baseline (README, `check`).

pub use crate::exclusion::ExclusionScope;
use crate::manifest::{FlowManifest, Program};
use k_rust::backend::{Backend, BackendOptions};
use kink_campaign::TestCase;
use kink_corpus::{
    CorpusSource, InputAssembler, InputError, InputGrammar, LoadedSource, ProgramSource,
    admission::{
        AdmissionRecord, AdmissionRefusal, below_floor_cases, check_initial_state,
        check_loaded_refused_cases, check_loaded_semantic_input, check_refused_cases,
        compile_definition_with, input_refusal, path_names_case,
    },
    load_source,
    manifest::RefusedCase,
};
use kink_native::{
    CensusError, DeclarationCensus, NativeValidator, ValidatedDefinition,
    data::DataFacts,
    declaration_census,
    exclusion::{CeilMemo, DefinitionExclusions, Exclusion},
};
use kink_patch::SemanticInput;
use std::{
    cell::OnceCell,
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
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
    /// The baseline's full critical-pair check under `[spec] assume_joined`, computed once, on
    /// the input backend (`Backend::from_definition` of the compile, the route kink runs it on;
    /// fz26 KINK-BASELINE-FINDINGS). While a finding is left no end is data, so no mutation can
    /// be killed (`baseline-findings`), no comparable program can kill, and no query `no` is
    /// given.
    pub data: DataFacts,
    /// The definition exclusions of the input backend's load (kink-native
    /// `DefinitionExclusions::of` of the compiled KORE and the definition the backend selected
    /// for the main module), the facts the campaign runner reads for every baseline run: while
    /// [`DefinitionExclusions::definition_exclusion`] holds, every run on the specification is
    /// excluded, so no program can be judged on it, and `check` fails. Read once, beside `data`,
    /// from what admission already loaded.
    pub exclusions: DefinitionExclusions,
    /// Which admission produced this specification; the [`ProgramInputs`] admitted beside it
    /// carry the same value, and only this specification opens a session on them.
    admission: AdmissionId,
}

/// The identity of one admission (`admit_spec_with` call): unique within the process, shared
/// by its [`AdmittedSpec`] (and the specification's clones) and its [`ProgramInputs`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct AdmissionId(u64);

impl AdmissionId {
    fn fresh() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        Self(NEXT.fetch_add(1, Ordering::Relaxed))
    }
}

/// The admission of one program.
#[derive(Clone, Debug)]
pub struct ProgramAdmission {
    pub id: String,
    /// The program's concrete initial configuration as a test case with no oracles (the
    /// caller chooses the oracles), or the refusal.
    pub outcome: Result<TestCase, AdmissionRefusal>,
    /// For an admitted program, why every run of it on the baseline is excluded, when that is
    /// known before it runs ([`InputSession::exclusion`]); `None` for a refused program.
    pub exclusion: Option<ProgramExclusion>,
}

impl ProgramAdmission {
    /// Whether the program can be judged on the baseline as far as admission shows without
    /// running it: it is admitted and no exclusion holds for every run of it.
    pub fn judgeable(&self) -> bool {
        self.outcome.is_ok() && self.exclusion.is_none()
    }
}

/// Why every run of an admitted program on the baseline is excluded (kink-native `exclusion`: a
/// run that is no evidence), read without running it: the specification's definition exclusion,
/// else the exclusion of the program's initial configuration. The campaign runner excludes the
/// program's baseline run for this reason, unless a reason only the run shows comes first (a
/// timeout, a stack stop, a contradicted claim, a value the definition leaves open).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ProgramExclusion {
    pub exclusion: Exclusion,
    pub scope: ExclusionScope,
}

impl ProgramExclusion {
    /// Why the program cannot be judged, in the reader's words (`crate::exclusion`).
    #[must_use]
    pub fn detail(&self) -> String {
        crate::exclusion::program_detail(self.exclusion, self.scope)
    }
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

    /// The specification is admitted and every program can be judged on the baseline as far as
    /// admission shows ([`ProgramAdmission::judgeable`]): no program is refused, and no exclusion
    /// holds for every run of one, the definition exclusion included. `check` exits 0 exactly
    /// when this holds (and, with `--mutations`, the list is not refused).
    pub fn all_judgeable(&self) -> bool {
        self.spec.is_some() && self.programs.iter().all(ProgramAdmission::judgeable)
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
    let mut session = inputs.session(&spec);
    let programs = manifest
        .programs
        .iter()
        .map(|program| session.admit(program))
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
    admit_spec_with(manifest, &mut |_, side| declaration_census(side))
}

/// [`admit_spec`] whose declaration census of the compiled baseline is `census` (given the
/// admitted load and the compile): kink-native `declaration_census`, or `run`'s census memo of it
/// (re-pin L1-4, `memo`), which gives the same census.
pub fn admit_spec_with(
    manifest: &FlowManifest,
    census: &mut dyn FnMut(
        &LoadedSource,
        &ValidatedDefinition,
    ) -> Result<DeclarationCensus, CensusError>,
) -> (AdmissionRecord, Option<(AdmittedSpec, ProgramInputs)>) {
    let mut record = AdmissionRecord::new(SPEC_RECORD_NAME);
    let admitted = admit_definition(manifest, &mut record, census);
    match admitted {
        Ok((spec, backend)) => {
            let inputs = ProgramInputs {
                admission: spec.admission,
                root: spec_root(manifest),
                backend,
                grammar: OnceCell::new(),
            };
            (record, Some((spec, inputs)))
        }
        Err(refusal) => {
            record.refusal = Some(refusal);
            (record, None)
        }
    }
}

/// Admits the programs of an admitted specification, one at a time and in any order, through
/// an [`InputSession`]: the manifest's canonical directory, the input gate's backend, and the
/// specification's input grammar, built on the first program assembled.
pub struct ProgramInputs {
    /// The admission these inputs came from; only its [`AdmittedSpec`] opens a session.
    admission: AdmissionId,
    root: Result<PathBuf, AdmissionRefusal>,
    backend: Backend,
    /// The input grammar of the specification of `admission`, the only one sessions accept,
    /// so it outlives every session.
    grammar: OnceCell<Result<InputGrammar, InputError>>,
}

impl ProgramInputs {
    /// The program's text: its file read inside the manifest's directory (stage `load`,
    /// reason `load-error`), or its inline text.
    pub fn text(&self, program: &Program) -> Result<String, AdmissionRefusal> {
        read_text(&self.root, program)
    }

    /// A session that admits programs of `spec`, which must be the specification these inputs
    /// were admitted with (the other half of the pair `admit_spec` returned, or a clone of
    /// it): the input grammar is a function of the specification, and these inputs keep the
    /// one they built for it.
    ///
    /// # Panics
    ///
    /// If `spec` comes from another admission: initial states assembled with another
    /// specification's grammar would be wrong inputs, not a refusal.
    pub fn session<'a>(&'a mut self, spec: &'a AdmittedSpec) -> InputSession<'a> {
        assert_eq!(
            spec.admission, self.admission,
            "ProgramInputs::session: the specification is not the one these inputs were \
             admitted with (pass the AdmittedSpec that admit_spec returned beside them)"
        );
        InputSession {
            spec,
            root: &self.root,
            backend: &mut self.backend,
            grammar: &self.grammar,
            assembler: None,
            ceil_memo: CeilMemo::default(),
        }
    }
}

fn read_text(
    root: &Result<PathBuf, AdmissionRefusal>,
    program: &Program,
) -> Result<String, AdmissionRefusal> {
    let root = root.clone()?;
    match &program.source {
        ProgramSource::Text(text) => Ok(text.clone()),
        ProgramSource::File(name) => read_program(&root, name),
    }
}

/// Admits the programs of one admitted specification. The program grammar and the
/// configuration assembler are built once, on the first program, and serve every later one:
/// each is a function of the specification alone, and the assembler is cleared before each
/// program, so a program's initial configuration and refusal are those a fresh assembly gives
/// (k-rust `ConfigurationAssembler`).
pub struct InputSession<'a> {
    spec: &'a AdmittedSpec,
    root: &'a Result<PathBuf, AdmissionRefusal>,
    backend: &'a mut Backend,
    grammar: &'a OnceCell<Result<InputGrammar, InputError>>,
    assembler: Option<InputAssembler<'a>>,
    /// The ceil-theory judgements of the initial-state exclusions read so far, on the input
    /// backend's definition ([`Self::exclusion`]).
    ceil_memo: CeilMemo,
}

impl InputSession<'_> {
    /// The admission of one program: its text, its test case ([`Self::test_case`]) and, when it
    /// is admitted, its exclusion ([`Self::exclusion`]).
    pub fn admit(&mut self, program: &Program) -> ProgramAdmission {
        let outcome = self
            .text(program)
            .and_then(|text| self.test_case(program, text));
        let exclusion = outcome
            .as_ref()
            .ok()
            .and_then(|test| self.exclusion(&test.initial_state));
        ProgramAdmission {
            id: program.id.clone(),
            outcome,
            exclusion,
        }
    }

    /// Why every run on the baseline from `initial` (an admitted program's initial
    /// configuration) is excluded, before it runs: the specification's definition exclusion
    /// first, then the exclusion of `initial` on the input backend's definition (kink-native
    /// `DefinitionExclusions::state_exclusion`), as the campaign runner reads both for a
    /// baseline run, on the same compiled definition.
    pub fn exclusion(&mut self, initial: &k_rust::kore::ast::Pattern) -> Option<ProgramExclusion> {
        let exclusions = &self.spec.exclusions;
        if let Some(exclusion) = exclusions.definition_exclusion() {
            return Some(ProgramExclusion {
                exclusion,
                scope: ExclusionScope::Definition,
            });
        }
        // Admission selected this definition (`baseline_data`), so the selection is the one
        // the exclusions were read from.
        let definition = self.backend.select_definition(None).ok()?;
        exclusions
            .state_exclusion_memoized(&definition, initial, &mut self.ceil_memo)
            .map(|exclusion| ProgramExclusion {
                exclusion,
                scope: ExclusionScope::InitialState,
            })
    }

    /// The program's text, as [`ProgramInputs::text`].
    pub fn text(&self, program: &Program) -> Result<String, AdmissionRefusal> {
        read_text(self.root, program)
    }

    /// The program's concrete initial configuration (`text` is [`Self::text`]'s result):
    /// assembled with the session's specification's own baseline compile (re-pin L1-4: no
    /// compile per program), then the concrete-state check and the input gate. A failure to
    /// build the specification's grammar refuses every program with the same refusal.
    pub fn test_case(
        &mut self,
        program: &Program,
        text: String,
    ) -> Result<TestCase, AdmissionRefusal> {
        let assembler = match &mut self.assembler {
            Some(assembler) => assembler,
            None => {
                let spec = self.spec;
                let grammar = self
                    .grammar
                    .get_or_init(|| InputGrammar::prepare(&spec.loaded, Some(&spec.compiled)))
                    .as_ref()
                    .map_err(|e| input_refusal(e.clone()))?;
                self.assembler.insert(InputAssembler::new(grammar))
            }
        };
        let initial_state = assembler
            .assemble(&text, program.start_sort.as_deref(), &program.variables)
            .map_err(input_refusal)?;
        check_initial_state(self.backend, &initial_state)?;
        Ok(TestCase {
            id: program.id.clone(),
            initial_state,
            oracles: Vec::new(),
        })
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

/// The below-floor case check (stage `refused-case`) for one source path, matched both
/// lexically (as the manifest names it) and after resolving links (kink-corpus
/// `check_refused_cases`).
fn check_below_floor(
    cases: &[RefusedCase],
    lexical: &Path,
    resolved: &Path,
) -> Result<(), AdmissionRefusal> {
    check_refused_cases(cases, resolved, |case| path_names_case(lexical, &case.case))
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
    census: &mut dyn FnMut(
        &LoadedSource,
        &ValidatedDefinition,
    ) -> Result<DeclarationCensus, CensusError>,
) -> Result<(AdmittedSpec, Backend), AdmissionRefusal> {
    let spec = &manifest.spec;
    let cases = below_floor_cases();
    let entry = manifest.directory.join(&spec.entry);
    check_below_floor(&cases, &entry, &entry)?;
    let loaded = load_source(&corpus_source(manifest)).map_err(load_refusal)?;
    record.files = loaded.files.clone();
    let root = spec_root(manifest)?;
    // kink-corpus's loaded-file refused-case stage (shared since flow F-16).
    check_loaded_refused_cases(&cases, &manifest.directory, &root, &loaded.files)?;
    let semantic_input = check_loaded_semantic_input(&loaded)?;
    let validator = NativeValidator::bind(loaded.baseline.clone(), Default::default());
    let compiled = compile_definition_with(&validator, record, |side| census(&loaded, side))?;
    // The input backend (kink-corpus `input_backend`: the compiled KORE for the main module with
    // default options, refused as `inputs`/`input-gate`), from KORE parsed once here, since the
    // definition exclusions read the parsed KORE too.
    let kore = k_rust::kore::parser::parse_definition(&compiled.artifacts().definition_kore)
        .map_err(|e| input_gate_refusal(format!("could not parse KORE definition: {e}")))?;
    let mut backend = Backend::from_definition(
        kore.clone(),
        k_rust::kast::identifier::encode(&spec.main_module),
        BackendOptions::default(),
    )
    .map_err(|e| input_gate_refusal(e.to_string()))?;
    let (data, exclusions) = baseline_data(
        &mut backend,
        &kore,
        &compiled.compile_options().builtin_source_prefixes,
        &spec.assume_joined,
    )?;
    Ok((
        AdmittedSpec {
            loaded,
            semantic_input,
            compiled,
            validator,
            data,
            exclusions,
            admission: AdmissionId::fresh(),
        },
        backend,
    ))
}

fn input_gate_refusal(detail: String) -> AdmissionRefusal {
    AdmissionRefusal {
        stage: "inputs".into(),
        reason: "input-gate".into(),
        detail,
    }
}

/// The baseline's data facts and definition exclusions on its input backend, whose compiled
/// KORE is `kore`: the definition the backend selected for the main module (selecting it loads
/// it, so its load counts are final, as kink-campaign's `Runtime::prepare` reads them), its
/// definition exclusions (kink-native `DefinitionExclusions::of`, with the compile's builtin
/// source prefixes), its full critical-pair check, and every name of `assume_joined` checked
/// against it (stage `assume-joined`; kink-native `DataFacts::refused_names`: a name must name
/// exactly one finding, and not a decided one). A definition exclusion refuses nothing.
fn baseline_data(
    backend: &mut Backend,
    kore: &k_rust::kore::ast::Definition,
    builtin_source_prefixes: &[String],
    assume_joined: &[String],
) -> Result<(DataFacts, DefinitionExclusions), AdmissionRefusal> {
    let selected = backend
        .select_definition(None)
        .map_err(|e| input_gate_refusal(e.to_string()))?;
    let data = DataFacts::of(&selected, assume_joined);
    let refused = data.refused_names();
    if refused.is_empty() {
        let exclusions = DefinitionExclusions::of(kore, &selected, builtin_source_prefixes);
        Ok((data, exclusions))
    } else {
        Err(AdmissionRefusal {
            stage: "assume-joined".into(),
            reason: "name-refused".into(),
            detail: refused
                .iter()
                .map(|refusal| format!("`{}`: {}", refusal.name, refusal.reason))
                .collect::<Vec<_>>()
                .join("; "),
        })
    }
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
