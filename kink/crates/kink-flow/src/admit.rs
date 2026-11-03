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
//! its own: its file is read inside the manifest's directory, its typed inputs are decoded by
//! the front end's [`InputDecoder`], its configuration is assembled, the concrete-state check and
//! the input gate run, and its initial configuration must have a value on the baseline. A
//! refused program never stops the others.
//!
//! A case is an assignment of a value to each configuration variable: the program text binds
//! `$PGM` (a definition without `$PGM` takes none, and refuses one: `stray-program`), and each
//! other variable is bound by name, from K text (`variables`) or from a typed input (`inputs`).
//! kink reads K text only; a typed input is a document of a front end's encoding, which only the
//! front end that knows the inputs' declared types can read, so kink asks that front end's
//! decoder for the term it denotes and binds the term. Without a decoder (a `FLOW.toml` read at
//! the K level) a program with `inputs` is refused (`typed-inputs`).
//!
//! A test's expected result is what the specification computes from its inputs. When the
//! baseline's initial configuration has no value (an input divides by zero, directly or through
//! a function), the specification computes no start, so the case has no expected result, and a
//! kill by it would be false. Admission runs the baseline to depth 0 and refuses such a case
//! (`initial-undefined`), whichever way its inputs are written.
//!
//! Beside the data facts, admission reads the definition exclusions of the input backend's load
//! ([`AdmittedSpec::exclusions`], kink-native `DefinitionExclusions::of`, as the campaign runner
//! reads them for every run), and for each admitted program whether every run of it on the
//! baseline is excluded before it runs ([`ProgramAdmission::exclusion`]): by the definition
//! exclusion, or by the exclusion of its initial configuration. Neither refuses anything: a
//! program so excluded is admitted, `results` runs it and reports its class, and `check` fails
//! on it, since it cannot be judged on the baseline (README, `check`).

pub use crate::exclusion::ExclusionScope;
use crate::manifest::{Decoder, FlowManifest, Program};
use k_rust::{
    backend::{Backend, BackendOptions},
    kast::Term,
};
use kink_campaign::TestCase;
use kink_corpus::{
    CorpusSource, InputAssembler, InputError, InputGrammar, LoadedSource, ProgramSource,
    VariableInput,
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
    execution::{ExecutionAdapter, ExecutionBudget, HaltClass, SolverProfile},
};
use kink_patch::SemanticInput;
use std::{
    cell::OnceCell,
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
    time::Duration,
};

/// A front end's reading of typed inputs (the krs front end: the encoding derived from the
/// specification's declared types). kink never reads a typed input itself.
pub trait InputDecoder {
    /// The configuration variable (its K name, without `$`) and the term that `document`,
    /// written for the input `name`, denotes; `files` reads the files the document names, inside
    /// the manifest's directory. The term is bound as a value built without the parser: kink
    /// types it in the definition's grammar and refuses it when its sort is not at most the
    /// variable's, so a decoder that disagrees with the definition fails closed. The error is
    /// the reader's message, which admission reports as the refusal's detail (`input-value`).
    fn decode(
        &self,
        name: &str,
        document: &toml::Value,
        files: &mut dyn InputFiles,
    ) -> Result<(String, Term), String>;
}

/// Where a decoder reads the files a typed input names.
pub trait InputFiles {
    /// The bytes of `path`, relative to the directory of the file `from` (a name this method
    /// returned before), or to the manifest's directory when `from` is `None`, with the file's
    /// name: its path relative to the manifest's directory once links are resolved, the name
    /// messages, parse locations and a decoder's cycle detection use (one file has one name,
    /// however it is reached). The path names the file the operating system resolves it to, as
    /// a program file's does; an absolute path, or one whose file lies outside the manifest's
    /// directory, is refused.
    fn read(&mut self, from: Option<&str>, path: &str) -> Result<(String, Vec<u8>), String>;
}

/// The files of a manifest's directory, read by the rule a program file is read by
/// ([`read_program`]): the path is resolved by the operating system, links and `..` included,
/// and the file it resolves to must lie inside the canonical manifest directory `root`.
struct ManifestFiles<'a> {
    root: &'a Path,
}

impl InputFiles for ManifestFiles<'_> {
    fn read(&mut self, from: Option<&str>, path: &str) -> Result<(String, Vec<u8>), String> {
        if Path::new(path).has_root() || Path::new(path).is_absolute() {
            return Err(format!(
                "{path} is absolute: name a file by its path relative to the manifest's directory"
            ));
        }
        let base = from
            .and_then(|from| Path::new(from).parent())
            .unwrap_or_else(|| Path::new(""));
        let written = base.join(path);
        let shown = written.to_string_lossy().replace('\\', "/");
        let resolved = fs::canonicalize(self.root.join(&written))
            .map_err(|e| format!("cannot read {shown}: {e}"))?;
        let Ok(name) = resolved.strip_prefix(self.root) else {
            return Err(format!("{shown} escapes the manifest's directory"));
        };
        let name = name.to_string_lossy().replace('\\', "/");
        let bytes = fs::read(&resolved).map_err(|e| format!("cannot read {name}: {e}"))?;
        Ok((name, bytes))
    }
}

/// A program's inputs as admission reads them: its program text and its typed inputs decoded.
/// Its program digest is computed from it (`digest::program_digest`), and its test case is
/// assembled from it ([`InputSession::test_case`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CaseInputs {
    /// The text bound to `$PGM`: its file's text, or its inline text; `None` for a program-less
    /// case.
    pub text: Option<String>,
    /// Each typed input as the front end's decoder read it: the configuration variable's K name
    /// (without `$`) and the term it is bound to, sorted by name.
    pub typed: Vec<(String, Term)>,
}

impl CaseInputs {
    /// The inputs of a program with the text `text` and no typed inputs.
    #[must_use]
    pub fn text(text: impl Into<String>) -> Self {
        Self {
            text: Some(text.into()),
            typed: Vec::new(),
        }
    }
}

impl From<&str> for CaseInputs {
    fn from(text: &str) -> Self {
        Self::text(text)
    }
}

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
                decoder: manifest.input_decoder.clone(),
                time: Duration::from_millis(manifest.budget.time_ms),
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
    /// The manifest's front-end decoder of typed inputs.
    decoder: Decoder,
    /// The time bound of one program run (`[budget] time_ms`), which bounds the depth-0 run
    /// that decides whether a program's initial configuration has a value.
    time: Duration,
}

impl ProgramInputs {
    /// The program's inputs ([`read_inputs`]).
    pub fn read(&self, program: &Program) -> Result<CaseInputs, AdmissionRefusal> {
        read_inputs(&self.root, &self.decoder, program)
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
            decoder: &self.decoder,
            time: self.time,
            assembler: None,
            main_module_assembler: None,
            ceil_memo: CeilMemo::default(),
        }
    }
}

/// A program's inputs: its text, its file read inside the manifest's directory (stage `load`,
/// reason `load-error`) or its inline text, and each of its typed inputs decoded by the
/// manifest's decoder (stage `inputs`: reason `typed-inputs` without a decoder, `input-value`
/// for a document the decoder refuses or a variable bound twice: by an input and `variables`, by
/// two inputs, or `$PGM` by an input and the program text).
fn read_inputs(
    root: &Result<PathBuf, AdmissionRefusal>,
    decoder: &Decoder,
    program: &Program,
) -> Result<CaseInputs, AdmissionRefusal> {
    let root = root.clone()?;
    let text = match &program.source {
        None => None,
        Some(ProgramSource::Text(text)) => Some(text.clone()),
        Some(ProgramSource::File(name)) => Some(read_program(&root, name)?),
    };
    if program.inputs.is_empty() {
        return Ok(CaseInputs {
            text,
            typed: Vec::new(),
        });
    }
    let Some(decoder) = decoder.get() else {
        return Err(AdmissionRefusal {
            stage: "inputs".into(),
            reason: "typed-inputs".into(),
            detail: "typed inputs are read by the front end that knows the inputs' declared types \
                     (the krs front end, `krs kink`); at the K level bind K text under `variables`"
                .into(),
        });
    };
    let value_refusal = |detail: String| AdmissionRefusal {
        stage: "inputs".into(),
        reason: "input-value".into(),
        detail,
    };
    let mut files = ManifestFiles { root: &root };
    // By K name, with the input name each came from.
    let mut typed = BTreeMap::<String, (String, Term)>::new();
    for (name, document) in &program.inputs {
        let (variable, term) = decoder
            .decode(name, document, &mut files)
            .map_err(|message| value_refusal(format!("input `{name}`: {message}")))?;
        let variable = variable.strip_prefix('$').unwrap_or(&variable).to_owned();
        if variable == "PGM" && text.is_some() {
            return Err(value_refusal(format!(
                "input `{name}` binds $PGM, which the program text binds too; bind it once"
            )));
        }
        if program
            .variables
            .iter()
            .any(|(bound, _)| bound.strip_prefix('$').unwrap_or(bound) == variable)
        {
            return Err(value_refusal(format!(
                "input `{name}` binds ${variable}, which `variables` binds too; bind it once"
            )));
        }
        if let Some((other, _)) = typed.get(&variable) {
            return Err(value_refusal(format!(
                "inputs `{other}` and `{name}` both bind ${variable}; bind it once"
            )));
        }
        typed.insert(variable, (name.clone(), term));
    }
    Ok(CaseInputs {
        text,
        typed: typed
            .into_iter()
            .map(|(variable, (_, term))| (variable, term))
            .collect(),
    })
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
    decoder: &'a Decoder,
    time: Duration,
    assembler: Option<InputAssembler<'a>>,
    /// The assembler of [`Self::assemble_reading_main_module`], built on its first use.
    main_module_assembler: Option<InputAssembler<'a>>,
    /// The ceil-theory judgements of the initial-state exclusions read so far, on the input
    /// backend's definition ([`Self::exclusion`]).
    ceil_memo: CeilMemo,
}

impl<'a> InputSession<'a> {
    /// The admission of one program: its inputs ([`Self::read`]), its test case
    /// ([`Self::test_case`]) and, when it is admitted, its exclusion ([`Self::exclusion`]),
    /// which the test case's value check has already read.
    pub fn admit(&mut self, program: &Program) -> ProgramAdmission {
        let (outcome, exclusion) = match self
            .read(program)
            .and_then(|inputs| self.case(program, &inputs))
        {
            Ok((test, exclusion)) => (Ok(test), exclusion),
            Err(refusal) => (Err(refusal), None),
        };
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

    /// The program's inputs, as [`ProgramInputs::read`].
    pub fn read(&self, program: &Program) -> Result<CaseInputs, AdmissionRefusal> {
        read_inputs(self.root, self.decoder, program)
    }

    /// The program's concrete initial configuration (`inputs` is [`Self::read`]'s result):
    /// assembled with the session's specification's own baseline compile (re-pin L1-4: no
    /// compile per program), the program text bound to `$PGM`, the text variables and then the
    /// typed inputs bound by name; then the concrete-state check, the input gate, and the
    /// baseline's depth-0 run, which refuses a configuration with no value
    /// ([`Self::check_initial_value`]). A failure to build the specification's grammar refuses
    /// every program with the same refusal.
    pub fn test_case(
        &mut self,
        program: &Program,
        inputs: &CaseInputs,
    ) -> Result<TestCase, AdmissionRefusal> {
        self.case(program, inputs).map(|(test, _)| test)
    }

    /// [`Self::test_case`] with the initial configuration's exclusion ([`Self::exclusion`]),
    /// read once for both the value check and the program's admission.
    fn case(
        &mut self,
        program: &Program,
        inputs: &CaseInputs,
    ) -> Result<(TestCase, Option<ProgramExclusion>), AdmissionRefusal> {
        let grammar = self.grammar()?;
        let assembler = self
            .assembler
            .get_or_insert_with(|| InputAssembler::new(grammar));
        let initial_state = assembler
            .assemble(
                inputs
                    .text
                    .as_deref()
                    .map(|text| (text, program.start_sort.as_deref())),
                &bindings(program, inputs),
            )
            .map_err(input_refusal)?;
        check_initial_state(self.backend, &initial_state)?;
        let exclusion = self.exclusion(&initial_state);
        self.check_initial_value(program, inputs, &initial_state, exclusion.is_some())?;
        Ok((
            TestCase {
                id: program.id.clone(),
                initial_state,
                oracles: Vec::new(),
            },
            exclusion,
        ))
    }

    /// The program's initial configuration as krun's `-c` reading and a k-rust-fuzz campaign
    /// assemble it: [`Self::test_case`]'s assembly, with every configuration variable's text
    /// read with the main module's grammar alone (kink-corpus
    /// `InputAssembler::reading_with_main_module`), and none of its checks. It differs from
    /// kink's own assembly only where kink reads a variable of
    /// [`Self::syntax_read_variables`] with the syntax module's grammar as another term; the
    /// error is the assembler's message.
    pub fn assemble_reading_main_module(
        &mut self,
        program: &Program,
        inputs: &CaseInputs,
    ) -> Result<k_rust::kore::ast::Pattern, String> {
        let grammar = self.grammar().map_err(|refusal| refusal.detail)?;
        self.main_module_assembler
            .get_or_insert_with(|| InputAssembler::reading_with_main_module(grammar))
            .assemble(
                inputs
                    .text
                    .as_deref()
                    .map(|text| (text, program.start_sort.as_deref())),
                &bindings(program, inputs),
            )
            .map_err(|error| error.to_string())
    }

    /// The configuration variables, without `$`, whose text kink reads with the syntax module's
    /// grammar first (kink-corpus `InputGrammar::syntax_read_variables`); empty when the
    /// specification's grammar does not build.
    pub fn syntax_read_variables(&self) -> Vec<String> {
        self.grammar().map_or_else(
            |_| Vec::new(),
            |grammar| grammar.syntax_read_variables().map(str::to_owned).collect(),
        )
    }

    /// The specification's input grammar, built on first use.
    fn grammar(&self) -> Result<&'a InputGrammar, AdmissionRefusal> {
        let spec = self.spec;
        self.grammar
            .get_or_init(|| InputGrammar::prepare(&spec.loaded, Some(&spec.compiled)))
            .as_ref()
            .map_err(|e| input_refusal(e.clone()))
    }
}

/// A program's bindings by name, in binding order: its text variables, then its typed inputs.
fn bindings(program: &Program, inputs: &CaseInputs) -> Vec<(String, VariableInput)> {
    program
        .variables
        .iter()
        .map(|(name, text)| (name.clone(), VariableInput::Text(text.clone())))
        .chain(
            inputs
                .typed
                .iter()
                .map(|(name, term)| (name.clone(), VariableInput::Term(term.clone()))),
        )
        .collect()
}

/// The longest K text an `initial-undefined` refusal quotes in full.
const QUOTED_TEXT_CHARS: usize = 60;

/// Each input of a case, as an `initial-undefined` refusal names it: `$PGM` by its file or text,
/// each text variable with its text, each typed input by its variable.
fn named_inputs(program: &Program, inputs: &CaseInputs) -> String {
    let quote = |text: &str| {
        let text = text.split_whitespace().collect::<Vec<_>>().join(" ");
        if text.chars().count() <= QUOTED_TEXT_CHARS {
            format!("`{text}`")
        } else {
            let head = text.chars().take(QUOTED_TEXT_CHARS).collect::<String>();
            format!("`{head}...`")
        }
    };
    let program_text = match (&program.source, &inputs.text) {
        (Some(ProgramSource::File(name)), Some(_)) => Some(format!("$PGM (the file {name})")),
        (_, Some(text)) => Some(format!("$PGM = {}", quote(text))),
        (_, None) => None,
    };
    program_text
        .into_iter()
        .chain(program.variables.iter().map(|(name, text)| {
            format!(
                "${} = {}",
                name.strip_prefix('$').unwrap_or(name),
                quote(text)
            )
        }))
        .chain(
            inputs
                .typed
                .iter()
                .map(|(name, _)| format!("${name} (a typed input)")),
        )
        .collect::<Vec<_>>()
        .join(", ")
}

impl InputSession<'_> {
    /// Refuses `initial` (`program`'s assembled, concrete initial configuration from `inputs`)
    /// when it has no value on the baseline (stage `inputs`, reason `initial-undefined`): the
    /// baseline's run of it to depth 0, kink's run request bounded by `[budget] time_ms`, ends in
    /// vacuous leaves only, and that run is evidence. A run's state at depth 0 is the initial
    /// configuration with its function applications evaluated by the definition's equations and
    /// restricted to its defined instances (k-rust E3), so a vacuous leaf at depth 0 is the
    /// initial configuration itself having no instance, and every later run of the program on
    /// the baseline starts from no state. The bound keeps the check to the start: admission
    /// runs no step of the program (one that never ends is admitted at once), and a later step
    /// with no value is the program's behavior, which its own run reports as an undefined step.
    ///
    /// The vacuity is a fact of the specification only where the run is evidence. Where the
    /// initial configuration is excluded (`excluded`, [`Self::exclusion`]: the definition
    /// exclusion, or a value that depends on the short-circuit reading or the implementation) or
    /// the depth-0 run is (kink-native `DefinitionExclusions::run_exclusion`: a contradicted
    /// `total` claim, a stack stop, ...), whether the start has a value depends on what the
    /// definition leaves open, and the program is admitted and reported as excluded instead: no
    /// run of it is judged, so it kills nothing. Any other answer admits the program too: a
    /// defined start, a timeout or a failure is what the program's own run then reports.
    fn check_initial_value(
        &mut self,
        program: &Program,
        inputs: &CaseInputs,
        initial: &k_rust::kore::ast::Pattern,
        excluded: bool,
    ) -> Result<(), AdmissionRefusal> {
        if excluded {
            return Ok(());
        }
        let budget = ExecutionBudget {
            time: self.time,
            max_simplification_iterations: crate::results::SIMPLIFICATION_ITERATIONS,
            max_depth: Some(0),
            max_breadth: None,
        };
        let adapter = ExecutionAdapter::new(SolverProfile::of(self.backend));
        let Ok(run) = adapter.execute(self.backend, initial, budget) else {
            return Ok(());
        };
        let leaves = run.leaves();
        if run.timed_out()
            || leaves.is_empty()
            || leaves.iter().any(|leaf| leaf.halt != HaltClass::Vacuous)
            || self.spec.exclusions.run_exclusion(&run).is_some()
        {
            return Ok(());
        }
        Err(AdmissionRefusal {
            stage: "inputs".into(),
            reason: "initial-undefined".into(),
            detail: format!(
                "the initial configuration has no value on the baseline: some input's value is \
                 undefined (it applies an operator or a function outside its domain), so the \
                 specification computes no start from this case and the case has no expected \
                 result; its inputs: {}",
                named_inputs(program, inputs)
            ),
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
