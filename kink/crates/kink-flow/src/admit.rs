//! Admission of a flow specification and its programs, through kink-corpus's admission
//! stages (`kink_corpus::admission`), with kink-corpus's stage names and refusal reasons.
//!
//! The order is kink-corpus's, without the stages that only a corpus manifest has (source
//! pins, solver profile, oracles): the below-floor case check of the entry (stage
//! `refused-case`), the load (`kink_corpus::load_source`, which records every non-builtin file
//! read), the below-floor case check of every loaded file, the semantic-input canonical check,
//! the compile with its kompile warnings, the representation gate (TB-03), the declaration
//! census (VI-T13), the cells the programs' second slot compares (stage `result`:
//! [`crate::observed`]), the input backend, the rules of `[stop]` on that backend (stage `stop`,
//! reason `stop-unresolved`: each name must be the exact label of a rewrite rule of the
//! specification, or the observation the stop states is not defined on it), and the definition's
//! full critical-pair check on that backend (stage `assume-joined`: every name of `[spec]
//! assume_joined` must name exactly one finding that can be assumed; fz26
//! KINK-BASELINE-FINDINGS). Then each program is admitted on
//! its own: its file is read inside the manifest's directory, its typed inputs are decoded by
//! the front end's [`InputDecoder`], its configuration is assembled, the concrete-state check and
//! the input gate run, and its initial configuration must have a value on the baseline. A
//! refused program never stops the others.
//!
//! A case is an assignment of a value to each configuration variable: the program text binds
//! `$PGM` (a definition without `$PGM` takes none, and refuses one: `stray-program`), and each
//! other variable is bound by name, from K text (`variables`) or from a typed input (`inputs`).
//! Which variable a program binds is kink's convention, `$PGM`, only while no front end says
//! otherwise: a front end that knows the definition's main input reads the program's bytes
//! itself ([`InputDecoder::program`]) and says which variable they bind, as K text or as a term.
//! kink reads K text only; a typed input is a document of a front end's encoding, which only the
//! front end that knows the inputs' declared types can read, so kink asks that front end's
//! decoder for the term it denotes and binds the term. Without a decoder (a `FLOW.toml` read at
//! the K level) a program with `inputs` is refused (`typed-inputs`). A case's expectation is a
//! document of the front end's encoding of ends likewise, read by the manifest's renderer of
//! ends, and refused without one (`typed-expectation`; `crate::expect`).
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
//! baseline is excluded before it runs a step ([`ProgramAdmission::exclusion`]): by the
//! definition exclusion, or by the exclusion of its initial configuration, read on its depth-0
//! run for the short-circuit reading. Neither refuses anything: a
//! program so excluded is admitted, `coverage` runs it and reports its class, and `check` fails
//! on it, since it cannot be judged on the baseline (README, `check`). A finding of the full
//! critical-pair check that `[spec] assume_joined` leaves unnamed refuses nothing either, and
//! `check` fails on it too, since no mutation can then have a verdict but `unknown`
//! ([`FlowAdmission::verdicts_possible`]).

use crate::evidence::Renderer;
pub use crate::exclusion::ExclusionScope;
use crate::manifest::{Decoder, FlowManifest, Program};
use crate::observed::{ResultProjection, result_projection};
use k_rust::{backend::Backend, kast::Term};
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
    exclusion::{
        CeilMemo, DefinitionExclusions, Exclusion, state_references_implementation_chosen,
    },
    execution::{ExecutionAdapter, ExecutionBudget, HaltClass, SolverProfile},
};
use kink_patch::SemanticInput;
use std::{
    borrow::Cow,
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

    /// How a program's bytes bind, when the front end knows the definition's main input: the
    /// variable they bind and its value, read from `bytes`, the program's file (`name`, its path
    /// relative to the manifest's directory) or its inline text (`name` is `None`). `None` keeps
    /// kink's rule, under which the bytes are UTF-8 text bound to `$PGM`, and is the default, so a
    /// front end that does not implement this method binds every program as kink does. The
    /// error is the reader's message, which admission reports as the refusal's detail
    /// (`input-value`).
    fn program(&self, name: Option<&str>, bytes: &[u8]) -> Option<Result<ProgramBinding, String>> {
        let _ = (name, bytes);
        None
    }
}

/// What a program binds, as a front end reads its bytes ([`InputDecoder::program`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProgramBinding {
    /// K text, read at the variable's sort: as a program where the variable is `$PGM` (at the
    /// program's `start_sort`, or the start position of `$PGM`'s sort), and as `variables` text
    /// of the variable otherwise.
    Text {
        /// The configuration variable's K name, with or without `$`.
        variable: String,
        text: String,
    },
    /// A term built without the parser, which kink binds as it binds a decoded typed input.
    Term {
        /// The configuration variable's K name, with or without `$`.
        variable: String,
        term: Term,
    },
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
pub(crate) struct ManifestFiles<'a> {
    pub(crate) root: &'a Path,
    /// The case document the inputs were written in (`Program::case`, its path as matched),
    /// whose directory as written a path named by no other file is relative to, as `krs run
    /// --case` reads it, or the file a named case is written in where the document includes it
    /// (`Program::case_file`, a name this reader gave); `None`: the manifest's directory. A path
    /// named from another file is relative to that file's name, links resolved.
    pub(crate) document: Option<&'a str>,
}

impl InputFiles for ManifestFiles<'_> {
    fn read(&mut self, from: Option<&str>, path: &str) -> Result<(String, Vec<u8>), String> {
        if Path::new(path).has_root() || Path::new(path).is_absolute() {
            return Err(format!(
                "{path} is absolute: name a file by its path relative to the manifest's directory"
            ));
        }
        let base = from
            .or(self.document)
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
    /// case and for a program the front end binds otherwise ([`Self::bound`]).
    pub text: Option<String>,
    /// Each typed input as the front end's decoder read it: the configuration variable's K name
    /// (without `$`) and the term it is bound to, sorted by name.
    pub typed: Vec<(String, Term)>,
    /// The program, where the front end's decoder binds it otherwise than as `$PGM` text
    /// ([`InputDecoder::program`]): to another variable, or as a term.
    pub bound: Option<BoundProgram>,
}

/// A program the front end bound otherwise than as `$PGM` text.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BoundProgram {
    /// The configuration variable's K name, without `$`.
    pub variable: String,
    /// Its value: K text read at the variable's sort, or a term.
    pub value: VariableInput,
    /// The SHA-256 of the program's bytes (its file's, or its inline text's), which the program
    /// digest holds as a program text's ([`crate::digest::program_payload`]).
    pub sha256: kink_patch::Sha256Digest,
}

impl CaseInputs {
    /// The inputs of a program with the text `text` and no typed inputs.
    #[must_use]
    pub fn text(text: impl Into<String>) -> Self {
        Self {
            text: Some(text.into()),
            typed: Vec::new(),
            bound: None,
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
    /// be killed (`baseline-findings`), no comparable program can kill, no query `no` is given,
    /// and `check` fails ([`FlowAdmission::verdicts_possible`]).
    pub data: DataFacts,
    /// The definition exclusions of the input backend's load (kink-native
    /// `DefinitionExclusions::of` of the compiled KORE and the definition the backend selected
    /// for the main module), the facts the campaign runner reads for every baseline run: while
    /// [`DefinitionExclusions::definition_exclusion`] holds, every run on the specification is
    /// excluded, so no program can be judged on it, and `check` fails. Read once, beside `data`,
    /// from what admission already loaded.
    pub exclusions: DefinitionExclusions,
    /// What every program's second slot compares: the cells the specification does not declare
    /// unobservable, narrowed by `[result] cells` (stage `result`; [`crate::observed`]).
    pub result: ResultProjection,
    /// The skeleton of the condition of every authored sentence behind a guarded rewrite rule or
    /// function equation (kink-native `coverage::guard_skeletons`), read once from the input
    /// backend's load: a guard's nodes, whether or not a program entered it, so that the
    /// requirements a guard states are a function of the definition ([`crate::coverage`]).
    /// `Err` holds why the backend's definition could not be selected to read them; a sentence
    /// whose skeleton cannot be read is listed with its reason (`unreadable`).
    pub guard_skeletons: Result<kink_native::coverage::GuardSkeletons, String>,
    /// What the definition says of its syntax (kink-native `coverage::syntax_facts`): its
    /// constructors, and the symbols each authored sentence's axioms inspect and build, read once
    /// from the input backend's load, so that the syntax family's universe and the static part of
    /// what a fired sentence touched are functions of the definition ([`crate::coverage`]).
    /// `Err` holds why the backend's definition could not be selected to read them.
    pub syntax: Result<kink_native::coverage::SyntaxFacts, String>,
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
    /// known before it runs any step ([`InputSession::exclusion`], and its depth-0 run for the
    /// short-circuit reading); `None` for a refused program.
    pub exclusion: Option<ProgramExclusion>,
    /// The program's `expectation` member in the check document, when it has `expect` and the
    /// command checked it (`crate::expect`: `check` checks it against the program's current
    /// result record); `None` otherwise.
    pub expectation: Option<serde_json::Value>,
}

impl ProgramAdmission {
    /// Whether the program can be judged on the baseline as far as admission shows without
    /// running a step of it: it is admitted and no exclusion holds for every run of it.
    pub fn judgeable(&self) -> bool {
        self.outcome.is_ok() && self.exclusion.is_none()
    }
}

/// Why every run of an admitted program on the baseline is excluded (kink-native `exclusion`: a
/// run that is no evidence), read without running a step of it: the specification's definition
/// exclusion, else the exclusion of the program's initial configuration (a hook whose value the
/// definition leaves open, or a function whose value depends on the short-circuit reading where
/// the normalization of that configuration, the depth-0 run every run starts with, lists a
/// reading that counts against it). The campaign runner excludes the program's baseline run for
/// this reason, unless a reason only the run shows comes first (a timeout, a stack stop, a
/// contradicted claim, a value the definition leaves open).
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
    /// The manifest's stop as documents name it (`FlowManifest::stop_value`), whether or not the
    /// specification is admitted; `None` without `[stop]`.
    pub stop: Option<serde_json::Value>,
    /// The manifest's observation declaration as documents name it
    /// (`FlowManifest::observe_value`), whether or not the specification is admitted; `None`
    /// without `[observe]`.
    pub observe: Option<serde_json::Value>,
}

impl FlowAdmission {
    /// The specification is admitted and every program is admitted.
    pub fn all_admitted(&self) -> bool {
        self.spec.is_some() && self.programs.iter().all(|p| p.outcome.is_ok())
    }

    /// The specification is admitted and every program can be judged on the baseline as far as
    /// admission shows ([`ProgramAdmission::judgeable`]): no program is refused, and no exclusion
    /// holds for every run of one, the definition exclusion included.
    pub fn all_judgeable(&self) -> bool {
        self.spec.is_some() && self.programs.iter().all(ProgramAdmission::judgeable)
    }

    /// No fact known before any mutant runs makes a verdict impossible: every program can be
    /// judged on the baseline ([`Self::all_judgeable`]), and the baseline has data under
    /// `[spec] assume_joined` (kink-native `DataFacts::has_data` of [`AdmittedSpec::data`]: no
    /// finding is left unnamed and the check read the whole definition), without which `run`
    /// makes every mutation with a program to run `unknown` (`baseline-findings`) and `query`
    /// gives no `no`. `check` exits 0 exactly when this holds (and, with `--mutations`, the list
    /// is not refused).
    pub fn verdicts_possible(&self) -> bool {
        self.all_judgeable() && self.spec.as_ref().is_some_and(|spec| spec.data.has_data())
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
            stop: manifest.stop_value(),
            observe: manifest.observe_value(),
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
        stop: manifest.stop_value(),
        observe: manifest.observe_value(),
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
                renderer: manifest.end_renderer.clone(),
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
    /// The manifest's front-end renderer of ends, which reads expectations.
    renderer: Renderer,
    /// The time bound of one program run (`[budget] time_ms`), which bounds the depth-0 run
    /// that decides whether a program's initial configuration has a value.
    time: Duration,
}

impl ProgramInputs {
    /// The program's inputs ([`read_inputs`]).
    pub fn read(&self, program: &Program) -> Result<CaseInputs, AdmissionRefusal> {
        read_inputs(&self.root, &self.decoder, &self.renderer, program)
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
            renderer: &self.renderer,
            time: self.time,
            assembler: None,
            ceil_memo: CeilMemo::default(),
        }
    }
}

/// A program's inputs: its text, its file read inside the manifest's directory (stage `load`,
/// reason `load-error`) or its inline text, and each of its typed inputs decoded by the
/// manifest's decoder (stage `inputs`: reason `typed-inputs` without a decoder, `input-value`
/// for a document the decoder refuses or a variable bound twice: by an input and `variables`, by
/// two inputs, or the program's variable by an input or `variables`). A decoder that binds the
/// program ([`InputDecoder::program`]) reads its bytes; one that refuses them, or binds them
/// otherwise than as `$PGM` text on a program with a `start_sort` (which reads `$PGM` text
/// only), refuses the program (`inputs`/`input-value`). Without a decoder, or where it keeps
/// kink's rule, the bytes are UTF-8 text bound to `$PGM`. A program with an expectation is
/// refused without a renderer of ends (`inputs`/`typed-expectation`), and where the renderer
/// refuses it (`inputs`/`expectation-value`; `crate::expect`).
fn read_inputs(
    root: &Result<PathBuf, AdmissionRefusal>,
    decoder: &Decoder,
    renderer: &Renderer,
    program: &Program,
) -> Result<CaseInputs, AdmissionRefusal> {
    let inputs = read_typed_inputs(root, decoder, program)?;
    if program.expect.is_some() {
        crate::expect::admit_expectation(renderer, &root.clone()?, program)?;
    }
    Ok(inputs)
}

/// [`read_inputs`] without the expectation.
fn read_typed_inputs(
    root: &Result<PathBuf, AdmissionRefusal>,
    decoder: &Decoder,
    program: &Program,
) -> Result<CaseInputs, AdmissionRefusal> {
    let root = root.clone()?;
    let value_refusal = |detail: String| AdmissionRefusal {
        stage: "inputs".into(),
        reason: "input-value".into(),
        detail,
    };
    let (text, bound) = match &program.source {
        None => (None, None),
        Some(source) => {
            let (name, bytes) = match source {
                ProgramSource::Text(text) => (None, Cow::Borrowed(text.as_bytes())),
                ProgramSource::File(name) => {
                    (Some(name.as_str()), Cow::Owned(read_program(&root, name)?))
                }
            };
            let described = || {
                name.map_or_else(
                    || "the program text".to_owned(),
                    |name| format!("the program file {name}"),
                )
            };
            match decoder
                .get()
                .and_then(|decoder| decoder.program(name, &bytes))
            {
                None => (Some(program_text(source, bytes)?), None),
                Some(Err(message)) => {
                    return Err(value_refusal(format!("{}: {message}", described())));
                }
                Some(Ok(binding)) => {
                    let (variable, value) = match binding {
                        ProgramBinding::Text { variable, text } => {
                            (variable, VariableInput::Text(text))
                        }
                        ProgramBinding::Term { variable, term } => {
                            (variable, VariableInput::Term(term))
                        }
                    };
                    let variable = variable.strip_prefix('$').unwrap_or(&variable).to_owned();
                    match value {
                        VariableInput::Text(text) if variable == "PGM" => (Some(text), None),
                        value => {
                            if program.start_sort.is_some() {
                                return Err(value_refusal(format!(
                                    "{} binds ${variable}, and a start_sort reads $PGM text \
                                     only; give no start_sort",
                                    described(),
                                )));
                            }
                            if program.variables.iter().any(|(written, _)| {
                                written.strip_prefix('$').unwrap_or(written) == variable
                            }) {
                                return Err(value_refusal(format!(
                                    "{} binds ${variable}, which `variables` binds too; bind it once",
                                    described()
                                )));
                            }
                            let sha256 = kink_patch::sha256(&bytes);
                            (
                                None,
                                Some(BoundProgram {
                                    variable,
                                    value,
                                    sha256,
                                }),
                            )
                        }
                    }
                }
            }
        }
    };
    // The variable the program binds, with how a refusal names the program.
    let program_variable = match (&text, &bound) {
        (Some(_), _) => Some(("PGM", "the program text")),
        (None, Some(bound)) => Some((bound.variable.as_str(), "the program")),
        (None, None) => None,
    };
    if program.inputs.is_empty() {
        return Ok(CaseInputs {
            text,
            typed: Vec::new(),
            bound,
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
    let mut files = ManifestFiles {
        root: &root,
        document: program.case_file.as_deref().or(program.case.as_deref()),
    };
    // By K name, with the input name each came from.
    let mut typed = BTreeMap::<String, (String, Term)>::new();
    for (name, document) in &program.inputs {
        let (variable, term) = decoder
            .decode(name, document, &mut files)
            .map_err(|message| value_refusal(format!("input `{name}`: {message}")))?;
        let variable = variable.strip_prefix('$').unwrap_or(&variable).to_owned();
        if let Some((bound, by)) = program_variable
            && bound == variable
        {
            return Err(value_refusal(format!(
                "input `{name}` binds ${variable}, which {by} binds too; bind it once"
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
        bound,
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
    renderer: &'a Renderer,
    time: Duration,
    assembler: Option<InputAssembler<'a>>,
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
            expectation: None,
        }
    }

    /// Why every run on the baseline from `initial` (an admitted program's initial
    /// configuration) is excluded, known before the program runs any step: the specification's
    /// definition exclusion first, then an implementation-chosen hook `initial` applies on the
    /// input backend's definition (kink-native `DefinitionExclusions::definition_exclusion` and
    /// `state_references_implementation_chosen`), as the campaign runner reads both for a
    /// baseline run, on the same compiled definition. Whether `initial`'s value depends on the
    /// short-circuit reading is judged by a run's list of readings, as the runner judges it, and
    /// so on the depth-0 run ([`Self::check_initial_value`]); a definition whose short-circuit
    /// analysis flags a rule has no exclusion for it either, since the runner judges each of its
    /// runs by that run's list.
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
        state_references_implementation_chosen(&definition, initial).then_some(ProgramExclusion {
            exclusion: Exclusion::ImplementationChosenHook,
            scope: ExclusionScope::InitialState,
        })
    }

    /// The program's inputs, as [`ProgramInputs::read`].
    pub fn read(&self, program: &Program) -> Result<CaseInputs, AdmissionRefusal> {
        read_inputs(self.root, self.decoder, self.renderer, program)
    }

    /// The inputs of a program this session admitted ([`Self::admit`]), without its expectation:
    /// admission read the expectation, and it is in no digest or key that the inputs give.
    pub(crate) fn admitted_inputs(
        &self,
        program: &Program,
    ) -> Result<CaseInputs, AdmissionRefusal> {
        read_typed_inputs(self.root, self.decoder, program)
    }

    /// The `expectation` member of `program`'s row, when it has `expect` (`crate::expect`):
    /// checked against `baseline`, its baseline result, or why it has none; `stop` is the
    /// manifest's `[stop]`.
    pub fn expectation(
        &self,
        program: &Program,
        baseline: Result<crate::expect::Baseline<'_>, &str>,
        stop: Option<&crate::manifest::StopSection>,
    ) -> Option<serde_json::Value> {
        crate::expect::expectation_value(
            self.renderer,
            self.root.as_deref().ok(),
            program,
            baseline,
            &self.spec.result.not_compared,
            stop,
        )
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
        let exclusion = match self.exclusion(&initial_state) {
            Some(exclusion) => Some(exclusion),
            None => self.check_initial_value(program, inputs, &initial_state)?,
        };
        Ok((
            TestCase {
                id: program.id.clone(),
                initial_state,
                oracles: Vec::new(),
            },
            exclusion,
        ))
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

/// A program's bindings by name, in binding order: the program where the front end binds it
/// by name ([`CaseInputs::bound`]), its text variables, then its typed inputs.
fn bindings(program: &Program, inputs: &CaseInputs) -> Vec<(String, VariableInput)> {
    inputs
        .bound
        .iter()
        .map(|bound| (bound.variable.clone(), bound.value.clone()))
        .chain(
            program
                .variables
                .iter()
                .map(|(name, text)| (name.clone(), VariableInput::Text(text.clone()))),
        )
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

/// Each input of a case, as an `initial-undefined` refusal names it: the program's variable by
/// its file or text (by its file or as the program text, where the front end binds it), each text
/// variable with its text, each typed input by its variable.
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
    let program_text = match (&program.source, &inputs.text, &inputs.bound) {
        (Some(ProgramSource::File(name)), Some(_), _) => Some(format!("$PGM (the file {name})")),
        (_, Some(text), _) => Some(format!("$PGM = {}", quote(text))),
        (Some(ProgramSource::File(name)), None, Some(bound)) => {
            Some(format!("${} (the file {name})", bound.variable))
        }
        (_, None, Some(bound)) => Some(format!("${} (the program text)", bound.variable)),
        (_, None, None) => None,
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
    /// The depth-0 run also judges the initial configuration's short-circuit reading as the
    /// campaign runner judges a run's (kink-native `DefinitionExclusions::state_exclusion`, with
    /// that run's facts): its list holds the entries of the normalization of `initial`, which
    /// every run of the program on the baseline starts with (the run record has no rollback), so
    /// where `initial` applies a reading-dependent function and an entry there counts against it,
    /// every such run is excluded, and the program is admitted and reported as excluded at stage
    /// `initial-state` (returned). Where no entry counts, only the program's own run can show one.
    ///
    /// The vacuity is a fact of the specification only where the run is evidence. Where the
    /// initial configuration is excluded so, or the depth-0 run is (kink-native
    /// `DefinitionExclusions::run_exclusion`: a contradicted `total` claim, a stack stop, ...),
    /// whether the start has a value depends on what the definition leaves open, and the program
    /// is admitted instead: no run of it is judged, so it kills nothing. Where neither is, the
    /// vacuity is a fact of both readings (a run with no counting entry is the same run in both),
    /// and the program is refused. Any other answer admits the program too: a defined start, a
    /// timeout or a failure is what the program's own run then reports.
    fn check_initial_value(
        &mut self,
        program: &Program,
        inputs: &CaseInputs,
        initial: &k_rust::kore::ast::Pattern,
    ) -> Result<Option<ProgramExclusion>, AdmissionRefusal> {
        let budget = ExecutionBudget {
            time: self.time,
            max_simplification_iterations: crate::results::SIMPLIFICATION_ITERATIONS,
            max_depth: Some(0),
            max_breadth: None,
        };
        let adapter = ExecutionAdapter::new(SolverProfile::of(self.backend));
        let Ok(run) = adapter.execute(self.backend, initial, budget) else {
            return Ok(None);
        };
        if run.timed_out() {
            return Ok(None);
        }
        let exclusions = &self.spec.exclusions;
        let state = self
            .backend
            .select_definition(None)
            .ok()
            .and_then(|definition| {
                exclusions.state_exclusion_memoized(
                    &definition,
                    initial,
                    run.facts(),
                    &mut self.ceil_memo,
                )
            });
        if let Some(exclusion) = state {
            return Ok(Some(ProgramExclusion {
                exclusion,
                scope: ExclusionScope::InitialState,
            }));
        }
        let leaves = run.leaves();
        if leaves.is_empty()
            || leaves.iter().any(|leaf| leaf.halt != HaltClass::Vacuous)
            || exclusions.run_exclusion(&run).is_some()
        {
            return Ok(None);
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
    // The compiled KORE, parsed once here: the compared cells, the input backend and the
    // definition exclusions all read it.
    let kore = k_rust::kore::parser::parse_definition(&compiled.artifacts().definition_kore)
        .map_err(|e| input_gate_refusal(format!("could not parse KORE definition: {e}")))?;
    let result = result_projection(
        &compiled,
        &kore,
        manifest
            .result
            .as_ref()
            .map(|section| section.cells.as_slice()),
    )
    .map_err(|refusal| AdmissionRefusal {
        stage: "result".into(),
        reason: refusal.reason().into(),
        detail: refusal.to_string(),
    })?;
    // The input backend (kink-corpus `input_backend`: the compiled KORE for the main module,
    // refused as `inputs`/`input-gate`), with the corpus's solver budget.
    let mut backend = Backend::from_definition(
        kore.clone(),
        k_rust::kast::identifier::encode(&spec.main_module),
        manifest.budget.backend_options(),
    )
    .map_err(|e| input_gate_refusal(e.to_string()))?;
    if let Some(stop) = &manifest.stop {
        stop_resolved(stop, &mut backend)?;
        stop_condition_bound(stop, &manifest.stop_when)?;
    }
    if let Some(observe) = &manifest.observe {
        observe_resolved(observe, &mut backend, &compiled, &kore)?;
    }
    let (data, exclusions) = baseline_data(
        &mut backend,
        &kore,
        &compiled.compile_options().builtin_source_prefixes,
        &spec.assume_joined,
    )?;
    // The skeleton of every guarded sentence's condition, read from the definition the input
    // backend selected: what a guard can show, whether or not a program enters it.
    let authors = kink_native::coverage::RuleAuthors::of(&compiled);
    let selected = backend.select_definition(None);
    let guard_skeletons = selected
        .as_ref()
        .map(|definition| kink_native::coverage::guard_skeletons(definition, &authors))
        .map_err(|error| {
            format!("the backend's definition could not be selected to read the skeleton: {error}")
        });
    // A front end's binders name each binder once: one selected under its axiom's `UNIQUE_ID`
    // and under its label would be refused by every baseline run's request.
    if let (Some(selection), Ok(definition)) = (&manifest.syntax, &selected) {
        binders_selected_once(selection, definition)?;
    }
    // The definition's syntax, read from the same load: what a sentence inspects and builds.
    let syntax = selected
        .as_ref()
        .map(|definition| kink_native::coverage::syntax_facts(definition, &authors))
        .map_err(|error| {
            format!("the backend's definition could not be selected to read its syntax: {error}")
        });
    Ok((
        AdmittedSpec {
            loaded,
            semantic_input,
            compiled,
            validator,
            data,
            exclusions,
            result,
            guard_skeletons,
            syntax,
            admission: AdmissionId::fresh(),
        },
        backend,
    ))
}

/// Each binder of a front end's syntax selection (`FlowManifest::syntax`) is selected once, or
/// the specification is refused at stage `syntax`, reason `binder-selected-twice`, naming the
/// binder and its two selections: a binder is a variable of one axiom, which a selection may name
/// by its `UNIQUE_ID` or its label, and two selections of it would state two caps for one set of
/// values (k-rust `collectBindings` refuses them). The manifest refuses one name selected twice
/// (`FlowManifest::with_syntax`); the two names of one axiom are told apart only by the loaded
/// definition, so here, before any run.
fn binders_selected_once(
    selection: &crate::manifest::SyntaxSelection,
    definition: &k_rust::k_rust_backend::definition::BackendDefinition,
) -> Result<(), AdmissionRefusal> {
    let collection = selection.binders.iter().fold(
        k_rust::k_rust_backend::coverage::BindingCollection::default(),
        |collection, (axiom, variable, cap)| collection.with_binder(axiom, variable, *cap),
    );
    match collection.selected_twice(definition) {
        None => Ok(()),
        Some((by_id, by_label)) => Err(AdmissionRefusal {
            stage: "syntax".into(),
            reason: "binder-selected-twice".into(),
            detail: format!(
                "the binder {} of {} is selected under its UNIQUE_ID and again under its label {}",
                by_id.variable, by_id.axiom, by_label.axiom
            ),
        }),
    }
}

/// Every name of `[stop]` labels a rewrite rule of the specification `backend` loads (kink-native
/// `StopRules::unresolved`: exactly, by label; a `UNIQUE_ID` or an equation's label selects no
/// step), or the specification is refused at stage `stop`, reason `stop-unresolved`, naming each
/// name that does not: a stop no rule of the specification can take states no observation of it.
/// A backend that cannot list its rules refuses it at stage `stop`, reason `backend-error`.
fn stop_resolved(
    stop: &crate::manifest::StopSection,
    backend: &mut Backend,
) -> Result<(), AdmissionRefusal> {
    // A failure to read the rules is the backend's, not a fault of the names: its own reason.
    let unresolved = stop.rules().unresolved(backend).map_err(|failure| AdmissionRefusal {
        stage: "stop".into(),
        reason: "backend-error".into(),
        detail: format!(
            "the specification's rewrite rules could not be read from its backend, so the stop's \
             names could not be checked: {failure:?}"
        ),
    })?;
    if unresolved.is_empty() {
        return Ok(());
    }
    let side = |name: &String| {
        if stop.before.contains(name) {
            format!("before `{name}`")
        } else {
            format!("after `{name}`")
        }
    };
    Err(AdmissionRefusal {
        stage: "stop".into(),
        reason: "stop-unresolved".into(),
        detail: format!(
            "[stop] {}: no rewrite rule of the specification has this label (a stop names a \
             rewrite rule by its exact K label, `MODULE.label`; an equation's label names no \
             step)",
            unresolved.iter().map(side).collect::<Vec<_>>().join(", ")
        ),
    })
}

/// `[stop] when` has a front end that asks it ([`FlowManifest::with_stop_when`]), or the
/// specification is refused at stage `stop`, reason `unsupported-front-end`. A condition is a
/// function of the values of named cells, evaluated in an observer definition; kink-flow's own
/// front end reads a K definition's terms, not values of a definition that declares them, and
/// has no observer to evaluate a function in, so a run would end at other arrivals than the
/// condition names. A K-level condition (a function symbol of a K observer definition applied to
/// cells by label) would be sound by the same argument, but no front end states one.
fn stop_condition_bound(
    stop: &crate::manifest::StopSection,
    slot: &crate::manifest::StopWhenSlot,
) -> Result<(), AdmissionRefusal> {
    match (&stop.when, &slot.0) {
        (Some(when), None) => Err(AdmissionRefusal {
            stage: "stop".into(),
            reason: "unsupported-front-end".into(),
            detail: format!(
                "[stop] when `{}`: a stop condition is a function of the values of the cells it \
                 reads, evaluated in an observer definition, and kink-flow's K front end reads \
                 terms of a K definition with no observer to evaluate it in; run the corpus \
                 through a front end that states the condition's values (`krs kink`), or remove \
                 `when`",
                when.function
            ),
        }),
        _ => Ok(()),
    }
}

/// `[observe]` states an observation of the specification, or the specification is refused at
/// stage `observe`:
/// - `unsupported-front-end`: a key that names a function of an observer (`observer`, a class's
///   `views`, `components` or `when`, a log's `element`). kink-flow's K front end reads terms of a
///   K definition and has no observer to evaluate a function in; every channel it compares is a
///   cell's content as the cell holds it, which is sound by the end projection's argument.
/// - `point-unresolved`: a class names a rule no rewrite rule of the specification is labelled
///   with (an equation's label names no step), so the class has no events
///   (`backend-error` when the backend cannot list the rules).
/// - `cell-refused`: a cell the configuration does not have, one declared `unobservable`, one
///   that is not a leaf cell of multiplicity 1 below cells of multiplicity 1, or a log cell that
///   does not hold a `List` (kink-campaign `Observe::cell_refusal`), each as the campaign would
///   refuse it before any run.
fn observe_resolved(
    observe: &crate::manifest::ObserveSection,
    backend: &mut Backend,
    compiled: &ValidatedDefinition,
    kore: &k_rust::kore::ast::Definition,
) -> Result<(), AdmissionRefusal> {
    let refused = |reason: &str, detail: String| AdmissionRefusal {
        stage: "observe".into(),
        reason: reason.into(),
        detail,
    };
    let keys = observe.front_end_keys();
    if !keys.is_empty() {
        return Err(refused(
            "unsupported-front-end",
            format!(
                "{}: a function of an observer is evaluated on the values of the cells it reads, \
                 and kink-flow's K front end reads terms of a K definition with no observer to \
                 evaluate it in: observer functions need a front end that reads values, which \
                 `krs kink` will be and does not yet accept them; observe the cells as they are",
                keys.join(", ")
            ),
        ));
    }
    let declared = observe
        .campaign()
        .map_err(|reason| refused("declaration", reason))?;
    let unresolved = declared.rules().unresolved(backend).map_err(|failure| {
        refused(
            "backend-error",
            format!(
                "the specification's rewrite rules could not be read from its backend, so the \
                 observation's rules could not be checked: {failure:?}"
            ),
        )
    })?;
    if !unresolved.is_empty() {
        return Err(refused(
            "point-unresolved",
            format!(
                "[observe] {}: no rewrite rule of the specification has this label (a point \
                 class names a rewrite rule by its exact K label, `MODULE.label`; an equation's \
                 label names no step)",
                unresolved
                    .iter()
                    .map(|name| format!("`{name}`"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        ));
    }
    let layout = kink_campaign::CellLayout::of_parsed(compiled, kore)
        .map_err(|refusal| refused("cell-refused", format!("{refusal:?}")))?;
    match declared.cell_refusal(&layout, kore) {
        Some(reason) => Err(refused("cell-refused", format!("[observe] {reason}"))),
        None => Ok(()),
    }
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

/// The bytes of a program file inside the canonical manifest directory `root`, read as
/// kink-corpus reads corpus input files (`load` stage, `load-error` reason; the detail names the
/// file as the manifest does, never by an absolute path).
fn read_program(root: &Path, name: &str) -> Result<Vec<u8>, AdmissionRefusal> {
    let path = fs::canonicalize(root.join(name))
        .map_err(|e| load_refusal(format!("cannot read {name}: {e}")))?;
    if !path.starts_with(root) {
        return Err(load_refusal(format!(
            "{name} escapes the manifest's directory"
        )));
    }
    fs::read(&path).map_err(|e| load_refusal(format!("cannot read {name}: {e}")))
}

/// The program text of `source`, whose bytes are `bytes`, by kink's rule: a file must be UTF-8
/// (`load` stage, `load-error` reason), and inline text is its text.
fn program_text(source: &ProgramSource, bytes: Cow<'_, [u8]>) -> Result<String, AdmissionRefusal> {
    match source {
        ProgramSource::Text(text) => Ok(text.clone()),
        ProgramSource::File(name) => String::from_utf8(bytes.into_owned())
            .map_err(|e| load_refusal(format!("{name} is not UTF-8: {e}"))),
    }
}
