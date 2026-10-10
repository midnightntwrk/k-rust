//! Parse, run, search, and prove a KRS definition through the in-process k-rust backend.
//!
//! [`Semantics::compile`] lowers Definition IR through [`krs_k_rust::compile_definition_with_context_timed`] with the symbolic (Haskell-dialect) backend, as `krs-gate` always has, and loads the KORE into a [`k_rust::backend::Backend`].
//! Every operation then works on that one compiled definition:
//!
//! - [`Semantics::parse`] parses program text at a sort, as `kast --sort` does;
//! - [`Semantics::configure`] builds `initGeneratedTopCell` from `$PGM` and the other configuration variables, as krun does;
//! - [`Semantics::run`] follows one path with strategy `any`, as krun does;
//! - [`Semantics::search`] returns the set of reachable states, as `krun --search` does;
//! - [`Semantics::prove`] proves the selected claims, as kprove does;
//! - [`Semantics::unparse`] prints a term through the definition's grammar, as `krun --output pretty` does, and [`Semantics::unparse_program`] prints a parsed program as `kast --output program` does (`krs-unparse`).
//!
//! The crate is filesystem-free: the caller supplies Definition IR, program text, and (optionally) the authored source text that trace origins are positioned in.
//! The serialized reports form the `krs-exec/1` JSON shape that `krs run --output json` prints.
//! Every operation can recurse deeply through large terms: callers run it on a thread with a large stack, as the CLI and the gate session do (64 MiB).

mod claims;
mod configuration;
mod console;
mod origin;
mod report;
mod stage;

use std::collections::BTreeMap;
use std::fmt;

use k_rust::{
    backend::{
        Backend, BackendOptions, ExecuteRequest, ExecutionResult, ExecutionStrategy,
        PatternRequest, ProveRequest, SearchRequest, SearchResponse, SearchTypeArg, TraceEntry,
    },
    inner::{ParseError, ProgramError, ProgramParseError},
    kast::{Sort as KastSort, convert::convert, json as kast_json, printer::Printer},
    kore::{ast::Pattern, json as kore_json},
};
use krs_ir::{SourceFileId, measure::Timings};
use krs_ir_levels::DefinitionIr;
use krs_k_rust::{
    CompileOptions, CompiledArtifacts, ConfigurationContext, DefinitionCompileError,
    NativeDefinition, SentenceProvenance, compile_definition_with_context_timed,
    compile_spec_definition_with_context_timed,
};
pub use stage::{CompiledStage, STAGE_FORMAT};

pub use configuration::Configuration;
pub use k_rust::backend::BackendError;
pub use krs_unparse::{Mode as UnparseMode, Printed, Warning as UnparseWarning};
pub use report::{
    Capabilities, ClaimInfo, ConfigVariable, Halt, Modality, ProofLeaf, ProofReport, REPORT_SCHEMA,
    RunReport, SearchReport, Solution, SourceSpan, Step, StepOrigin, Term, Verdict,
};

/// Authored source text by file identity, used to position trace and claim origins.
///
/// A provider returns `None` when the text is unavailable or no longer matches the file's digest;
/// origins then carry the file without a line and column.
pub type SourceText = Box<dyn Fn(&SourceFileId) -> Option<String>>;

/// Options for [`Semantics::run`].
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct RunOptions {
    /// At most this many rewrite steps; equation evaluation is not a step.
    pub depth: Option<u64>,
    /// Record each rewrite step.
    pub trace: bool,
}

/// K's search modes.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum SearchMode {
    /// `=>!`: final states (the default).
    #[default]
    Final,
    /// `=>*`: every reachable state.
    All,
    /// `=>1`: states one step away.
    OneStep,
    /// `=>+`: states one or more steps away.
    OneOrMoreSteps,
}

impl SearchMode {
    /// Every mode, in command-line catalog order.
    pub const ALL: [Self; 4] = [Self::Final, Self::All, Self::OneStep, Self::OneOrMoreSteps];

    /// The command-line spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Final => "final",
            Self::All => "all",
            Self::OneStep => "one-step",
            Self::OneOrMoreSteps => "one-or-more-steps",
        }
    }

    const fn backend(self) -> SearchTypeArg {
        match self {
            Self::Final => SearchTypeArg::Final,
            Self::All => SearchTypeArg::All,
            Self::OneStep => SearchTypeArg::OneStep,
            Self::OneOrMoreSteps => SearchTypeArg::OneOrMoreSteps,
        }
    }
}

/// Options for [`Semantics::search`].
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct SearchOptions {
    /// Which states count as solutions.
    pub mode: SearchMode,
    /// At most this many rewrite steps on any path.
    pub depth: Option<u64>,
    /// At most this many solutions.
    pub max_solutions: Option<usize>,
    /// Record each solution's rewrite steps.
    pub trace: bool,
}

/// Options for [`Semantics::prove`].
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ProveOptions {
    /// An author spec module (KF-041); `None` selects the generated `<MAIN>-SPEC`.
    pub module: Option<String>,
    /// Claim labels, resolved by exact match or unique `.`-suffix; empty selects every claim.
    pub claims: Vec<String>,
    /// At most this many rewrite steps on any proof path.
    pub depth: Option<u64>,
}

/// The program text bound to `$PGM`, with the name diagnostics cite.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProgramInput {
    /// The file name, or `<stdin>`.
    pub name: String,
    /// The program text.
    pub text: String,
}

/// The inputs of one initial configuration.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ConfigInputs {
    /// FILE, bound to `$PGM`.
    pub program: Option<ProgramInput>,
    /// `-c NAME=TEXT` bindings in command-line order. NAME is `ENV`, `$ENV`, or the init parameter `env`.
    pub variables: Vec<(String, String)>,
    /// Console input for the `stream = "stdin"` cell, as krun reads standard input under `--io off`;
    /// `None` binds an empty stream. It is ignored when the definition has no stdin stream cell.
    pub stdin: Option<Vec<u8>>,
}

/// An initial configuration, ready to run or search.
#[derive(Clone, Debug)]
pub struct State(Pattern);

impl State {
    /// The KORE pattern of `initGeneratedTopCell`.
    #[must_use]
    pub const fn kore(&self) -> &Pattern {
        &self.0
    }
}

/// How [`Semantics::print`] renders a term.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum PrintStyle {
    /// Textual KAST, as `kast --output kast` prints it.
    #[default]
    Kast,
    /// The KAST JSON envelope, as `--output json` prints it.
    Json,
    /// KORE text, as `--output kore` prints it.
    Kore,
    /// Grammar-directed text without colour, as `krun --output pretty` prints it; warnings are dropped (see [`Semantics::unparse`]).
    Pretty,
}

/// A failure of a `krs-exec` operation.
#[derive(Debug)]
pub enum ExecError {
    /// The definition did not compile.
    Compile(DefinitionCompileError),
    /// The backend rejected an operation.
    Backend(String),
    /// FILE was given but the init function takes no program.
    StrayProgram,
    /// The init function takes a program but FILE was not given.
    MissingProgram,
    /// `-c` named a variable the definition does not declare.
    UnknownVariable {
        /// The name as written.
        name: String,
        /// Every declared variable.
        variables: Vec<ConfigVariable>,
    },
    /// A variable was bound twice.
    DuplicateVariable(String),
    /// Declared variables that were not bound.
    MissingVariables(Vec<ConfigVariable>),
    /// Program or `-c` text that does not parse.
    Parse {
        /// The input (`prog.imp`, `<stdin>`, or `-c ENV`).
        input: String,
        /// The sort it was parsed at.
        sort: String,
        /// The parser's message, with its location.
        message: String,
    },
    /// `--sort` named a sort the program grammar does not have.
    UnknownSort {
        /// The sort as written.
        sort: String,
        /// The program sorts.
        sorts: Vec<String>,
    },
    /// `krs parse` without `--sort` on a definition without `$PGM`.
    NoProgramSort,
    /// `--claim` matched no claim.
    UnknownClaim {
        /// The label as written.
        requested: String,
        /// A close label, when one exists.
        suggestion: Option<String>,
    },
    /// `--claim` matched several claims by suffix.
    AmbiguousClaim {
        /// The label as written.
        requested: String,
        /// The matching labels.
        matches: Vec<String>,
    },
    /// `prove` on a definition without claims.
    NoClaims,
    /// `--spec-module` named an author spec module without claims (KF-041).
    NoSpecClaims(String),
    /// `--spec-module` named no author spec module, or (without it) every
    /// claim is in a spec module (KF-041).
    UnknownSpecModule {
        /// The module as written, or `None` when `--spec-module` was not given.
        requested: Option<String>,
        /// The author spec modules.
        modules: Vec<String>,
        /// The generated module of the loose claims.
        generated: String,
    },
    /// `search` on a definition with stream cells.
    SearchWithStreams,
    /// An operation this build or this unit does not provide.
    Unavailable(String),
    /// The backend returned a result KRS cannot read.
    Result(String),
}

impl fmt::Display for ExecError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Compile(error) => error.fmt(formatter),
            Self::Backend(message) | Self::Unavailable(message) | Self::Result(message) => {
                formatter.write_str(message)
            }
            Self::StrayProgram => formatter
                .write_str("the init function takes no program (no $PGM); do not pass FILE"),
            Self::MissingProgram => formatter.write_str(
                "the init function takes a program ($PGM); pass FILE, or `-` for standard input",
            ),
            Self::UnknownVariable { name, variables } => {
                write!(formatter, "unknown configuration variable `{name}`")?;
                write_variables(formatter, "the definition declares", variables)
            }
            Self::DuplicateVariable(name) => {
                write!(formatter, "configuration variable `${name}` is bound twice")
            }
            Self::MissingVariables(variables) => {
                let names = variables
                    .iter()
                    .map(|variable| format!("-c {}=VALUE", variable.parameter))
                    .collect::<Vec<_>>()
                    .join(" and ");
                write!(formatter, "missing configuration variables; pass {names}")?;
                write_variables(formatter, "missing", variables)
            }
            Self::Parse {
                input,
                sort,
                message,
            } => write!(formatter, "{input} does not parse at sort {sort}: {message}"),
            Self::UnknownSort { sort, sorts } => write!(
                formatter,
                "the program grammar has no sort `{sort}`; program sorts: {}",
                sorts.join(", ")
            ),
            Self::NoProgramSort => formatter.write_str(
                "the init function takes no program (no $PGM), so there is no default sort; pass --sort",
            ),
            Self::UnknownClaim {
                requested,
                suggestion,
            } => {
                write!(formatter, "no claim has label `{requested}`")?;
                if let Some(suggestion) = suggestion {
                    write!(formatter, "; did you mean `{suggestion}`?")?;
                }
                Ok(())
            }
            Self::AmbiguousClaim { requested, matches } => write!(
                formatter,
                "claim label `{requested}` is ambiguous; matches {}",
                matches
                    .iter()
                    .map(|label| format!("`{label}`"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Self::NoClaims => formatter.write_str("this definition has no claims"),
            Self::NoSpecClaims(module) => write!(
                formatter,
                "spec module `{module}` has no claims of its own or through its imports"
            ),
            Self::UnknownSpecModule {
                requested,
                modules,
                generated,
            } => {
                let modules = modules
                    .iter()
                    .map(|module| format!("`{module}`"))
                    .collect::<Vec<_>>()
                    .join(", ");
                match requested {
                    Some(requested) => write!(
                        formatter,
                        "no spec module is named `{requested}`; the definition's spec modules are {} and the generated `{generated}`",
                        if modules.is_empty() { "none".to_owned() } else { modules }
                    ),
                    None => write!(
                        formatter,
                        "every claim of this definition is in a spec module; pass --spec-module with one of {modules}"
                    ),
                }
            }
            Self::SearchWithStreams => formatter.write_str(
                "krs search cannot run a definition with stream cells; K's search has no console I/O (k-rust rejects --io on in search)",
            ),
        }
    }
}

fn write_variables(
    formatter: &mut fmt::Formatter<'_>,
    heading: &str,
    variables: &[ConfigVariable],
) -> fmt::Result {
    write!(formatter, "; {heading}:")?;
    for variable in variables {
        write!(formatter, "\n  {variable}")?;
    }
    Ok(())
}

impl std::error::Error for ExecError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Compile(error) => Some(error),
            _ => None,
        }
    }
}

impl From<BackendError> for ExecError {
    fn from(error: BackendError) -> Self {
        Self::Backend(error.0)
    }
}

/// One compiled definition, ready to parse, configure, run, search, and prove.
pub struct Semantics {
    backend: Backend,
    unparser: krs_unparse::Unparser,
    configuration: Configuration,
    frontend_definition: NativeDefinition,
    main_module: String,
    definition_kore: String,
    provenance: SentenceProvenance,
    variables: Vec<ConfigVariable>,
    claims: Vec<ClaimInfo>,
    user_sorts: Vec<String>,
    origins: origin::Origins,
    console: console::ConsoleCells,
    /// The author spec modules (KF-041), by name.
    spec_modules: Vec<String>,
    /// The Definition IR, kept to compile a spec module's proof definition on demand.
    spec_definition: Option<Box<DefinitionIr>>,
    /// Compiled spec-module proof definitions, by spec module.
    spec_provers: BTreeMap<String, SpecProver>,
}

/// One author spec module's compiled proof definition (KF-041).
struct SpecProver {
    backend: Backend,
    claims: Vec<ClaimInfo>,
}

impl Semantics {
    /// Compile Definition IR without authored source text.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::Compile`] when the native frontend rejects the definition, or [`ExecError::Backend`] when the backend cannot load it.
    pub fn compile(definition: &DefinitionIr) -> Result<Self, ExecError> {
        Self::compile_with(definition, None, &mut Timings::disabled())
    }

    /// Compile Definition IR, positioning origins in the source text `sources` supplies, and recording `native.*` spans.
    ///
    /// # Errors
    ///
    /// Fails exactly when [`Self::compile`] fails.
    pub fn compile_with(
        definition: &DefinitionIr,
        sources: Option<SourceText>,
        timings: &mut Timings,
    ) -> Result<Self, ExecError> {
        let stage = CompiledStage::compile(definition, timings)?;
        Self::from_stage(definition, stage, sources, timings)
    }

    /// Build the semantics of `definition` from its compiled stage, which [`CompiledStage::compile`] made from the same Definition IR (or [`CompiledStage::decode`] read back), recording `exec.*` spans.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::Backend`] when the backend, the program grammar, or the printer cannot load the stage.
    pub fn from_stage(
        definition: &DefinitionIr,
        stage: CompiledStage,
        sources: Option<SourceText>,
        timings: &mut Timings,
    ) -> Result<Self, ExecError> {
        let CompiledStage {
            definition_kore,
            syntax_definition_kore,
            macros_kore,
            provenance: sentence_provenance,
            frontend_definition,
            source_table: _,
            configuration_variables,
        } = stage;

        let main_module = frontend_definition.main_module.clone();
        let variables = config_variables(&configuration_variables);
        let configuration = timings.try_span("exec.configuration", |_| {
            Configuration::new(&frontend_definition, configuration_variables)
                .map_err(|error| ExecError::Backend(error.to_string()))
        })?;
        let unparser = timings.try_span("exec.unparser", |_| {
            krs_unparse::Unparser::from_kore(&syntax_definition_kore, &macros_kore)
                .map(|unparser| unparser.with_program_grammar(&frontend_definition))
                .map_err(|error| ExecError::Backend(error.to_string()))
        })?;
        let backend = timings.try_span("exec.backend", |_| {
            Backend::new(
                &definition_kore,
                main_module.clone(),
                BackendOptions::default(),
            )
            .map_err(ExecError::from)
        })?;
        let user_sorts = user_sorts(definition, &frontend_definition);
        let console = console::ConsoleCells::of(definition);
        let mut origins = origin::Origins::new(sources);
        let claims = claims::catalog(
            &definition_kore,
            &main_module,
            &sentence_provenance,
            &mut origins,
        )?;
        let spec_modules = definition
            .modules()
            .iter()
            .filter(|module| module.is_spec())
            .map(|module| module.id().as_str().to_owned())
            .collect::<Vec<_>>();
        let spec_definition = (!spec_modules.is_empty()).then(|| Box::new(definition.clone()));
        Ok(Self {
            backend,
            unparser,
            configuration,
            frontend_definition,
            main_module,
            definition_kore,
            provenance: sentence_provenance,
            variables,
            claims,
            user_sorts,
            origins,
            console,
            spec_modules,
            spec_definition,
            spec_provers: BTreeMap::new(),
        })
    }

    /// The author spec modules (KF-041), by name.
    #[must_use]
    pub fn spec_modules(&self) -> &[String] {
        &self.spec_modules
    }

    /// The claims of one author spec module's proof definition, compiling it on first use.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::UnknownSpecModule`], or the compile or backend error.
    pub fn spec_claims(&mut self, module: &str) -> Result<&[ClaimInfo], ExecError> {
        Ok(&self.spec_prover(module)?.claims)
    }

    fn spec_prover(&mut self, module: &str) -> Result<&mut SpecProver, ExecError> {
        if !self.spec_provers.contains_key(module) {
            let definition = self
                .spec_definition
                .as_deref()
                .filter(|_| self.spec_modules.iter().any(|name| name == module))
                .ok_or_else(|| ExecError::UnknownSpecModule {
                    requested: Some(module.to_owned()),
                    modules: self.spec_modules.clone(),
                    generated: claims::spec_module(&self.main_module),
                })?;
            let (artifacts, _) = compile_spec_definition_with_context_timed(
                definition,
                module,
                CompileOptions {
                    backend: krs_k_rust::Backend::Haskell,
                    ..CompileOptions::default()
                },
                &mut Timings::disabled(),
            )
            .map_err(ExecError::Compile)?;
            let backend = Backend::new(
                &artifacts.definition_kore,
                module.to_owned(),
                BackendOptions::default(),
            )?;
            let claims = claims::spec_catalog(
                &artifacts.definition_kore,
                &artifacts.sentence_provenance,
                &mut self.origins,
            )?;
            self.spec_provers
                .insert(module.to_owned(), SpecProver { backend, claims });
        }
        Ok(self
            .spec_provers
            .get_mut(module)
            .expect("the spec prover was just inserted"))
    }

    /// The compiled KORE definition text.
    #[must_use]
    pub fn definition_kore(&self) -> &str {
        &self.definition_kore
    }

    /// The main module's name.
    #[must_use]
    pub fn main_module(&self) -> &str {
        &self.main_module
    }

    /// The prepared frontend definition the program grammar was built from.
    #[must_use]
    pub const fn frontend_definition(&self) -> &NativeDefinition {
        &self.frontend_definition
    }

    /// The surface parsing context, for callers that parse cell expectations.
    pub const fn configuration_mut(&mut self) -> &mut Configuration {
        &mut self.configuration
    }

    /// The loaded backend, for callers that issue raw k-rust requests.
    pub const fn backend_mut(&mut self) -> &mut Backend {
        &mut self.backend
    }

    /// What this build supports. Every route of this crate executes, searches, and proves; SMT needs the `z3-inference` feature.
    #[must_use]
    pub fn capabilities(&self) -> Capabilities {
        let backend = self.backend.capabilities();
        Capabilities {
            execute: backend.execution,
            search: backend.search,
            prove: backend.proving,
            smt: backend.smt,
        }
    }

    /// The configuration variables, `$PGM` first, then by name.
    #[must_use]
    pub fn variables(&self) -> &[ConfigVariable] {
        &self.variables
    }

    /// The claims of the generated spec module, in label order.
    #[must_use]
    pub fn claims(&self) -> &[ClaimInfo] {
        &self.claims
    }

    /// Whether the definition declares stream cells (`$STDIN` or `$IO`).
    #[must_use]
    pub fn has_stream_cells(&self) -> bool {
        self.variables
            .iter()
            .any(|variable| matches!(variable.name.as_str(), "STDIN" | "IO"))
    }

    /// Parse program text at `sort` (default: the sort of `$PGM`) with the program grammar.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::UnknownSort`], [`ExecError::NoProgramSort`], or [`ExecError::Parse`].
    pub fn parse(&mut self, sort: Option<&str>, input: &ProgramInput) -> Result<Term, ExecError> {
        let sort = self.program_sort(sort)?;
        let parsed = self
            .configuration
            .parse_program(&sort, &input.text)
            .map_err(|error| parse_error(input, &sort, error.as_ref()))?;
        let kast = parsed.term().clone();
        let kore = self
            .configuration
            .parse_program_kore(&sort, &input.text)
            .map_err(|error| ExecError::Parse {
                input: input.name.clone(),
                sort: sort.to_string(),
                message: error.to_string(),
            })?;
        Ok(Term::new(kore, kast))
    }

    /// Parse program text as [`Self::parse`] does and print it through the program grammar, as `kast --output program` does.
    ///
    /// Macros print as parsed, and the main module's aliases are reversed.
    ///
    /// # Errors
    ///
    /// Fails exactly when [`Self::parse`] fails.
    pub fn unparse_program(
        &mut self,
        sort: Option<&str>,
        input: &ProgramInput,
        color: bool,
    ) -> Result<Printed, ExecError> {
        let sort = self.program_sort(sort)?;
        let kore = self
            .configuration
            .parse_program_presented_kore(&sort, &input.text)
            .map_err(|error| parse_error(input, &sort, error.as_ref()))?;
        Ok(self.unparser.print_kore(
            &kore,
            &krs_unparse::Options::new(krs_unparse::Mode::Program).with_color(color),
        ))
    }

    fn program_sort(&self, sort: Option<&str>) -> Result<KastSort, ExecError> {
        match sort {
            Some(name) => {
                let sorts = self.configuration.program_sorts();
                if !sorts.contains(name) {
                    return Err(ExecError::UnknownSort {
                        sort: name.to_owned(),
                        sorts: self
                            .user_sorts
                            .iter()
                            .filter(|sort| sorts.contains(*sort))
                            .cloned()
                            .collect(),
                    });
                }
                Ok(KastSort::new(name))
            }
            None => self
                .configuration
                .variables()
                .get("PGM")
                .cloned()
                .ok_or(ExecError::NoProgramSort),
        }
    }

    /// Build the initial configuration from FILE and `-c` bindings.
    ///
    /// # Errors
    ///
    /// Returns a typed error for a stray or missing FILE, an unknown, duplicate, or missing variable, or text that does not parse.
    pub fn configure(&mut self, inputs: &ConfigInputs) -> Result<State, ExecError> {
        let has_program = self.variables.iter().any(|variable| variable.is_main);
        match (&inputs.program, has_program) {
            (Some(_), false) => return Err(ExecError::StrayProgram),
            (None, true) => return Err(ExecError::MissingProgram),
            _ => {}
        }
        let mut bound = BTreeMap::new();
        let mut names = BTreeMap::new();
        for (written, text) in &inputs.variables {
            let variable = self.resolve_variable(written)?;
            if bound.insert(variable.name.clone(), text.clone()).is_some() {
                return Err(ExecError::DuplicateVariable(variable.name.clone()));
            }
            names.insert(variable.name.clone(), written.clone());
        }
        let missing = self
            .variables
            .iter()
            .filter(|variable| {
                !variable.is_main
                    && !matches!(variable.name.as_str(), "IO" | "STDIN")
                    && !bound.contains_key(&variable.name)
            })
            .cloned()
            .collect::<Vec<_>>();
        if !missing.is_empty() {
            return Err(ExecError::MissingVariables(missing));
        }
        let program = inputs.program.as_ref();
        let stdin = inputs
            .stdin
            .as_deref()
            .filter(|_| self.console.stdin)
            .map(console::buffered_input);
        self.configuration
            .assemble_pattern(
                program.map(|program| program.text.as_str()),
                &bound,
                stdin.as_deref(),
            )
            .map(State)
            .map_err(|error| configuration_error(&error, program, &names, &self.variables))
    }

    fn resolve_variable(&self, written: &str) -> Result<&ConfigVariable, ExecError> {
        let name = written.strip_prefix('$').unwrap_or(written);
        self.variables
            .iter()
            .find(|variable| {
                !variable.is_main && (variable.name == name || variable.parameter == name)
            })
            .ok_or_else(|| ExecError::UnknownVariable {
                name: written.to_owned(),
                variables: self.variables.clone(),
            })
    }

    /// Follow one path from `state`, with strategy `any`, as krun does.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::Backend`] when the backend fails, or [`ExecError::Result`] when it does not return exactly one leaf.
    pub fn run(&mut self, state: &State, options: RunOptions) -> Result<RunReport, ExecError> {
        let mut request = ExecuteRequest::new(state.0.clone());
        request.strategy = ExecutionStrategy::Any;
        request.max_depth = options.depth;
        let ExecutionResult { leaves, .. } = self.backend.execute(request)?;
        let [leaf] = <[_; 1]>::try_from(leaves).map_err(|leaves: Vec<_>| {
            ExecError::Result(format!(
                "a run must end in exactly one state; the backend returned {}",
                leaves.len()
            ))
        })?;
        let trace = if options.trace {
            self.steps(&leaf.trace)
        } else {
            Vec::new()
        };
        let state = term(&leaf.state)?;
        let halt = Halt::from_backend(leaf.reason);
        let stdout = if self.console.stdout {
            console::stdout_buffer(state.kore())
        } else {
            None
        };
        let exit_code = if self.console.exit && halt.is_complete() {
            self.exit_code(&state)?
        } else {
            None
        };
        Ok(RunReport {
            halt,
            steps: leaf.depth,
            state,
            trace,
            stdout,
            exit_code,
        })
    }

    /// The exit cell's final value: `getExitCode` of the final configuration, as krun computes the status.
    fn exit_code(&mut self, state: &Term) -> Result<Option<i64>, ExecError> {
        let Some(request) = console::exit_code_request(state.kore()) else {
            return Ok(None);
        };
        let simplified = self.backend.simplify(PatternRequest::new(request))?;
        let source = serde_json::to_string(&simplified)
            .map_err(|error| ExecError::Result(error.to_string()))?;
        let pattern =
            kore_json::from_str(&source).map_err(|error| ExecError::Result(error.to_string()))?;
        Ok(console::exit_value(&pattern))
    }

    /// Return the set of reachable states that match the search mode, as `krun --search` does.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::SearchWithStreams`] for a definition with stream cells, or [`ExecError::Backend`] when the backend fails.
    pub fn search(
        &mut self,
        state: &State,
        options: SearchOptions,
    ) -> Result<SearchReport, ExecError> {
        if self.has_stream_cells() {
            return Err(ExecError::SearchWithStreams);
        }
        let response = search_backend(&mut self.backend, state.0.clone(), options)?;
        let complete = response.incomplete.is_empty()
            && options
                .max_solutions
                .is_none_or(|limit| response.states.len() < limit);
        let solutions = response
            .states
            .iter()
            .map(|solution| {
                Ok(Solution {
                    state: term(&solution.state)?,
                    depth: solution.depth,
                    trace: if options.trace {
                        self.steps(&solution.trace)
                    } else {
                        Vec::new()
                    },
                })
            })
            .collect::<Result<Vec<_>, ExecError>>()?;
        Ok(SearchReport {
            complete,
            solutions,
        })
    }

    /// Prove the selected claims, one backend proof per claim, in selection order.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::NoClaims`], a claim-resolution error, [`ExecError::Unavailable`] for an author spec module, or [`ExecError::Backend`].
    pub fn prove(&mut self, options: &ProveOptions) -> Result<Vec<ProofReport>, ExecError> {
        if let Some(module) = &options.module
            && module != &claims::spec_module(&self.main_module)
        {
            let prover = self.spec_prover(module)?;
            if prover.claims.is_empty() {
                return Err(ExecError::NoSpecClaims(module.clone()));
            }
            return prove_claims(&mut prover.backend, &prover.claims, options);
        }
        if self.claims.is_empty() {
            if !self.spec_modules.is_empty() {
                return Err(ExecError::UnknownSpecModule {
                    requested: None,
                    modules: self.spec_modules.clone(),
                    generated: claims::spec_module(&self.main_module),
                });
            }
            return Err(ExecError::NoClaims);
        }
        prove_claims(&mut self.backend, &self.claims, options)
    }

    /// Render a term.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::Result`] when the term cannot be encoded.
    pub fn print(&self, term: &Term, style: PrintStyle) -> Result<String, ExecError> {
        Ok(match style {
            PrintStyle::Kast => Printer::new().print_term(term.kast()),
            PrintStyle::Json => kast_json::to_string(term.kast())
                .map_err(|error| ExecError::Result(error.to_string()))?,
            PrintStyle::Kore => term.kore().to_string(),
            PrintStyle::Pretty => self.unparse(term, false).text,
        })
    }

    /// Print a term through the definition's grammar, as `krun --output pretty` prints a configuration (KF-017).
    ///
    /// The text has no trailing newline; [`Printed::warnings`] lists the problems that degraded it (labels printed as KAST, invalid colour lists).
    #[must_use]
    pub fn unparse(&self, term: &Term, color: bool) -> Printed {
        self.unparser.print_kore(
            term.kore(),
            &krs_unparse::Options::new(krs_unparse::Mode::Pretty).with_color(color),
        )
    }

    fn steps(&mut self, trace: &[TraceEntry]) -> Vec<Step> {
        trace
            .iter()
            .filter(|entry| entry.kind == "rewrite")
            .enumerate()
            .map(|(index, entry)| Step {
                index: u64::try_from(index).unwrap_or(u64::MAX).saturating_add(1),
                label: entry.label.clone(),
                rule_id: entry.unique_id.clone(),
                origin: self
                    .origins
                    .step_origin(self.provenance.get(&entry.unique_id)),
            })
            .collect()
    }
}

/// Compile Definition IR to symbolic KORE with the options every `krs-exec` operation and the gate's one-shot compiler share.
///
/// # Errors
///
/// Returns the native frontend's typed rejection.
pub fn compile_definition(
    definition: &DefinitionIr,
    timings: &mut Timings,
) -> Result<(CompiledArtifacts, ConfigurationContext), DefinitionCompileError> {
    compile_definition_with_context_timed(
        definition,
        CompileOptions {
            backend: krs_k_rust::Backend::Haskell,
            ..CompileOptions::default()
        },
        timings,
    )
}

/// Prove the selected claims of `catalog` on `backend`, one proof per claim, in selection order.
fn prove_claims(
    backend: &mut Backend,
    catalog: &[ClaimInfo],
    options: &ProveOptions,
) -> Result<Vec<ProofReport>, ExecError> {
    let selected = claims::select(catalog, &options.claims)?;
    let mut reports = Vec::with_capacity(selected.len());
    for index in selected {
        let claim = catalog[index].clone();
        let result = backend.prove(ProveRequest {
            claim: Some(claim.backend_label.clone()),
            max_depth: options.depth,
            ..ProveRequest::default()
        })?;
        let mut verdict = Verdict::from_backend(&result.status).ok_or_else(|| {
            ExecError::Result(format!("unknown proof status `{}`", result.status))
        })?;
        // The backend assumes a trusted claim and reports it proven; KRS never calls an
        // assumption proven (KF-042).
        if claim.trusted && verdict == Verdict::Proven {
            verdict = Verdict::Trusted;
        }
        let leaves = result
            .leaves
            .iter()
            .map(|leaf| {
                Ok(ProofLeaf {
                    state: term(&leaf.state)?,
                    depth: leaf.depth,
                    outcome: leaf.outcome.clone(),
                })
            })
            .collect::<Result<Vec<_>, ExecError>>()?;
        reports.push(ProofReport {
            claim: claim.label,
            modality: claim.modality,
            origin: claim.origin,
            verdict,
            leaves,
        });
    }
    Ok(reports)
}

fn search_backend(
    backend: &mut Backend,
    state: Pattern,
    options: SearchOptions,
) -> Result<SearchResponse, ExecError> {
    let mut request = SearchRequest::new(state);
    request.search_type = options.mode.backend();
    request.max_depth = options.depth;
    request.max_results = options.max_solutions;
    Ok(backend.search(request)?)
}

impl Term {
    /// A term from a KORE pattern, with its KAST conversion.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::Result`] when the pattern has no KAST form.
    pub fn from_kore(kore: Pattern) -> Result<Self, ExecError> {
        let kast = convert(&kore).map_err(|error| ExecError::Result(error.to_string()))?;
        Ok(Self::new(kore, kast))
    }
}

fn term(value: &serde_json::Value) -> Result<Term, ExecError> {
    let source =
        serde_json::to_string(value).map_err(|error| ExecError::Result(error.to_string()))?;
    let kore =
        kore_json::from_str(&source).map_err(|error| ExecError::Result(error.to_string()))?;
    let kast = convert(&kore).map_err(|error| ExecError::Result(error.to_string()))?;
    Ok(Term::new(kore, kast))
}

fn config_variables(declared: &BTreeMap<String, KastSort>) -> Vec<ConfigVariable> {
    let mut variables = declared
        .iter()
        .map(|(name, sort)| ConfigVariable {
            name: name.clone(),
            parameter: name.to_ascii_lowercase(),
            sort: sort.to_string(),
            is_main: name == "PGM",
        })
        .collect::<Vec<_>>();
    variables.sort_by_key(|variable| (!variable.is_main, variable.name.clone()));
    variables
}

/// The sorts the package's own modules declare, by name: the program sorts worth listing.
fn user_sorts(definition: &DefinitionIr, frontend: &NativeDefinition) -> Vec<String> {
    let modules = definition
        .modules()
        .iter()
        .map(|module| module.id().as_str())
        .collect::<std::collections::BTreeSet<_>>();
    frontend
        .modules
        .iter()
        .filter(|module| modules.contains(module.name.as_str()))
        .flat_map(|module| &module.local_sentences)
        .filter_map(|sentence| match &**sentence {
            k_rust::definition::Sentence::SyntaxSort { sort, .. }
            | k_rust::definition::Sentence::Production { sort, .. } => Some(sort.name.clone()),
            _ => None,
        })
        .filter(|sort| !sort.starts_with('#') && !sort.ends_with("Cell"))
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn parse_error(
    input: &ProgramInput,
    sort: &KastSort,
    error: &(dyn std::error::Error + 'static),
) -> ExecError {
    ExecError::Parse {
        input: located(&input.name, &input.text, boxed_parse_position(error)),
        sort: sort.to_string(),
        message: error.to_string(),
    }
}

/// The byte offset at which program text stopped parsing, when the parser reports one.
fn parse_position(error: &ProgramParseError) -> Option<usize> {
    match error.error.as_ref() {
        ParseError::NoParse { position, .. } => Some(*position),
        _ => None,
    }
}

fn boxed_parse_position(error: &(dyn std::error::Error + 'static)) -> Option<usize> {
    if let Some(ProgramError::Parse(error)) = error.downcast_ref::<ProgramError>() {
        return parse_position(error);
    }
    error
        .downcast_ref::<ProgramParseError>()
        .and_then(parse_position)
}

/// `name:line:column` for a byte offset in `text`, or `name` when the offset is unknown.
fn located(name: &str, text: &str, position: Option<usize>) -> String {
    let index = krs_ir::LineIndex::new(text);
    match position.and_then(|position| index.byte_to_position(position).ok()) {
        Some(position) => format!("{name}:{}:{}", position.line(), position.scalar_column()),
        None => name.to_owned(),
    }
}

fn configuration_error(
    error: &k_rust::kompile::ConfigurationError,
    program: Option<&ProgramInput>,
    names: &BTreeMap<String, String>,
    variables: &[ConfigVariable],
) -> ExecError {
    use k_rust::kompile::ConfigurationError as Error;
    let sort_of = |name: &str| {
        variables
            .iter()
            .find(|variable| variable.name == name)
            .map_or_else(String::new, |variable| variable.sort.clone())
    };
    match error {
        Error::Program(parse) => ExecError::Parse {
            input: program.map_or_else(
                || "the program".to_owned(),
                |program| located(&program.name, &program.text, parse_position(parse)),
            ),
            sort: sort_of("PGM"),
            message: parse.to_string(),
        },
        Error::Parse {
            variable,
            sort,
            error,
        } => {
            let name = variable.strip_prefix('$').unwrap_or(variable);
            ExecError::Parse {
                input: format!("-c {}", names.get(name).map_or(name, String::as_str)),
                sort: sort.to_string(),
                message: error.to_string(),
            }
        }
        Error::Missing { names: missing } => ExecError::MissingVariables(
            variables
                .iter()
                .filter(|variable| {
                    missing
                        .iter()
                        .any(|name| name.trim_start_matches('$') == variable.name)
                })
                .cloned()
                .collect(),
        ),
        other => ExecError::Backend(other.to_string()),
    }
}

#[cfg(test)]
mod tests;
