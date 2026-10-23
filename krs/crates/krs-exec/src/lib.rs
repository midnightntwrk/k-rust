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
//! - [`Semantics::values`] names constructors and sorts by their KRS declarations, so a configuration variable can be given as a [`Value`] ([`ConfigValue::Value`]), and [`Semantics::views`] reads a result's cells as values by their Rust field names.
//!
//! The crate is filesystem-free: the caller supplies Definition IR, program text, and (optionally) the authored source text that trace origins are positioned in.
//! The serialized reports form the `krs-exec/1` JSON shape that `krs run --output json` prints.
//! Every operation can recurse deeply through large terms: callers run it on a thread with a large stack, as the CLI and the gate session do (64 MiB).

mod cell_types;
mod claims;
mod configuration;
mod console;
mod origin;
mod report;
mod stage;
mod values;
mod view;

use std::collections::BTreeMap;
use std::sync::Arc;
use std::{collections::HashMap, fmt};

use k_rust::{
    backend::{
        Backend, BackendOptions, EffectOutput, ExecuteRequest, ExecutionLeaf, ExecutionResult,
        ExecutionStrategy, HaltReasonOutput, PatternRequest, ProveRequest, SearchRequest,
        SearchResponse, SearchTypeArg, TraceEntry,
    },
    inner::{ParseError, ProgramError, ProgramParseError},
    kast::{
        Sort as KastSort,
        convert::{Converter, sort_hooks},
        json as kast_json,
        printer::Printer,
    },
    kore::{ast::Pattern, json as kore_json},
};
use krs_ir::{SourceFileId, measure::Timings};
use krs_ir_levels::DefinitionIr;
use krs_k_rust::{
    CompileOptions, CompiledArtifacts, ConfigurationContext, DefinitionCompileError,
    NativeDefinition, SentenceProvenance, compile_definition_with_context_timed,
    compile_spec_definition_with_context_timed,
};
pub use stage::{CompiledStage, SPEC_STAGE_FORMAT, STAGE_FORMAT, SpecStage};

pub use configuration::Configuration;
pub use k_rust::backend::BackendError;
pub use krs_unparse::{Mode as UnparseMode, Printed, Warning as UnparseWarning};
pub use report::{
    Capabilities, ClaimInfo, ConfigVariable, Halt, Modality, ProofLeaf, ProofReport, REPORT_SCHEMA,
    RunReport, SearchReport, Solution, SourceSpan, Step, StepOrigin, Term, Verdict,
};
pub use values::{Ctor, Decl, Float, SortRef, Value, ValueError, ValueIndex};
pub use view::{CellError, StateView, View};

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

/// The value of one configuration variable.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ConfigValue {
    /// Surface text, parsed at the variable's declared sort as `krun -c` parses it.
    Text(String),
    /// A value, typed at the variable's declared sort without a parse
    /// ([`ValueIndex::ctor`], [`Value::map`], ...).
    Value(Value),
}

impl From<String> for ConfigValue {
    fn from(text: String) -> Self {
        Self::Text(text)
    }
}

impl From<&str> for ConfigValue {
    fn from(text: &str) -> Self {
        Self::Text(text.to_owned())
    }
}

impl From<Value> for ConfigValue {
    fn from(value: Value) -> Self {
        Self::Value(value)
    }
}

/// The inputs of one initial configuration.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ConfigInputs {
    /// FILE, bound to `$PGM`.
    pub program: Option<ProgramInput>,
    /// Variable bindings, as `-c NAME=TEXT` gives them in command-line order. NAME is `ENV`,
    /// `$ENV`, or the init parameter `env`; text and values may be mixed.
    pub variables: Vec<(String, ConfigValue)>,
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

/// A part of a configuration value that does not fit the element types of the typed collection
/// cell its variable fills ([`ExecError::CollectionElementSort`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ElementSortMismatch {
    /// The variable, without `$`.
    pub variable: String,
    /// The Rust field of the cell.
    pub cell: String,
    /// The cell's declared type (`Map<Id, Value>`).
    pub declared: String,
    /// Where the part is in the value (``the value at key `x` ``).
    pub position: String,
    /// The part, printed through the definition's grammar.
    pub element: String,
    /// The part's sort.
    pub sort: String,
    /// The declared element sort it is not at most.
    pub expected: String,
}

impl fmt::Display for ElementSortMismatch {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self {
            variable,
            cell,
            declared,
            position,
            element,
            sort,
            expected,
        } = self;
        write!(
            formatter,
            "configuration variable `${variable}`: the cell `{cell}` is declared `{declared}`, but {position} is `{element}` of sort {sort}, which is not a subsort of {expected}"
        )
    }
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
    /// A configuration value that is no term of the definition, or not of its variable's sort.
    Value {
        /// The variable, without `$`.
        variable: String,
        /// Why the value does not fit.
        error: ValueError,
    },
    /// A configuration value with a part that does not fit the element types of the typed
    /// collection cell the variable fills (`skip` stored in a `Map<Id, Value>` cell).
    CollectionElementSort(Box<ElementSortMismatch>),
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
            Self::Value { variable, error } => {
                write!(formatter, "configuration variable `${variable}`: {error}")
            }
            Self::CollectionElementSort(mismatch) => mismatch.fmt(formatter),
            Self::SearchWithStreams => formatter.write_str(
                "krs search cannot run a definition with stream cells; K's search has no console I/O (k-rust rejects --io on in search)",
            ),
        }
    }
}

/// The value of an `initGeneratedTopCell` map entry: the map holds each value boxed as one
/// `KItem`, `#KConfigValue(V ~> .K)`, and `V` is the sequence's one item.
fn unboxed_configuration_value(boxed: &Pattern) -> &Pattern {
    let box_symbol = k_rust::kompile::encode_kore_label(&k_rust::kast::Label::new("#KConfigValue"));
    let Pattern::Application { symbol, arguments } = boxed else {
        return boxed;
    };
    let [sequence] = arguments.as_slice() else {
        return boxed;
    };
    if symbol.name != box_symbol.name {
        return boxed;
    }
    match sequence {
        Pattern::Application { symbol, arguments }
            if symbol.name == k_rust::names::WellKnownSymbol::KSeq.as_str() =>
        {
            match arguments.as_slice() {
                [item, Pattern::Application { symbol: tail, .. }]
                    if tail.name == k_rust::names::WellKnownSymbol::DotK.as_str() =>
                {
                    item
                }
                _ => sequence,
            }
        }
        _ => sequence,
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
        Self::Backend(error.message().to_owned())
    }
}

/// One compiled definition, ready to parse, configure, run, search, and prove.
pub struct Semantics {
    backend: Backend,
    /// The sort hooks of `backend`'s definition, by KAST sort name, with which its results are
    /// converted to KAST (`result_sort_hooks`).
    sort_hooks: HashMap<String, String>,
    unparser: krs_unparse::Unparser,
    configuration: Configuration,
    values: Arc<ValueIndex>,
    /// The typed cells configuration variables fill, which [`Self::configure`] checks.
    cell_types: cell_types::CellTypes,
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
    /// The sort hooks of `backend`'s definition (`result_sort_hooks`).
    sort_hooks: HashMap<String, String>,
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
        let mut backend = timings.try_span("exec.backend", |_| {
            Backend::new(
                &definition_kore,
                main_module.clone(),
                BackendOptions::default(),
            )
            .map_err(ExecError::from)
        })?;
        let sort_hooks = result_sort_hooks(&mut backend)?;
        let (values, cell_types) = timings.try_span("exec.values", |_| {
            let backend_definition = backend
                .select_definition(None)
                .map_err(|error| ExecError::Backend(error.to_string()))?;
            let values = ValueIndex::new(definition, &backend_definition, &sort_hooks);
            let cell_types = cell_types::CellTypes::new(definition, &backend_definition, &values);
            Ok::<_, ExecError>((Arc::new(values), cell_types))
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
            sort_hooks,
            unparser,
            configuration,
            values,
            cell_types,
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

    /// Load one author spec module's compiled proof definition, which [`SpecStage::compile`] made from this Definition IR (or [`SpecStage::decode`] read back); a later proof of that module uses it instead of compiling.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::UnknownSpecModule`] when the stage is not of one of [`Self::spec_modules`], or [`ExecError::Backend`] when the backend cannot load it.
    pub fn load_spec_stage(&mut self, stage: SpecStage) -> Result<(), ExecError> {
        if !self.spec_modules.contains(&stage.module) {
            return Err(self.unknown_spec_module(&stage.module));
        }
        let mut backend = Backend::new(
            &stage.definition_kore,
            stage.module.clone(),
            BackendOptions::default(),
        )?;
        let sort_hooks = result_sort_hooks(&mut backend)?;
        let claims =
            claims::spec_catalog(&stage.definition_kore, &stage.provenance, &mut self.origins)?;
        self.spec_provers.insert(
            stage.module,
            SpecProver {
                backend,
                sort_hooks,
                claims,
            },
        );
        Ok(())
    }

    fn unknown_spec_module(&self, module: &str) -> ExecError {
        ExecError::UnknownSpecModule {
            requested: Some(module.to_owned()),
            modules: self.spec_modules.clone(),
            generated: claims::spec_module(&self.main_module),
        }
    }

    fn spec_prover(&mut self, module: &str) -> Result<&mut SpecProver, ExecError> {
        if !self.spec_provers.contains_key(module) {
            let definition = self
                .spec_definition
                .as_deref()
                .filter(|_| self.spec_modules.iter().any(|name| name == module))
                .ok_or_else(|| self.unknown_spec_module(module))?;
            let stage = SpecStage::compile(definition, module, &mut Timings::disabled())?;
            self.load_spec_stage(stage)?;
        }
        Ok(self
            .spec_provers
            .get_mut(module)
            .expect("the spec prover was just loaded"))
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
        for (written, value) in &inputs.variables {
            let variable = self.resolve_variable(written)?;
            let binding = match value {
                ConfigValue::Text(text) => configuration::Binding::Text(text.clone()),
                ConfigValue::Value(value) => {
                    configuration::Binding::Term(self.values.to_kast(value).map_err(|error| {
                        ExecError::Value {
                            variable: variable.name.clone(),
                            error,
                        }
                    })?)
                }
            };
            if bound.insert(variable.name.clone(), binding).is_some() {
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
        let pattern = self
            .configuration
            .assemble_pattern(
                program.map(|program| program.text.as_str()),
                &bound,
                stdin.as_deref(),
            )
            .map_err(|error| match error {
                configuration::AssemblyError::Value { variable, error } => ExecError::Value {
                    variable,
                    error: ValueError::Unencodable(match error.as_ref() {
                        k_rust::kompile::ConfigurationError::ValueSort(mismatch) => format!(
                            "its sort {} is not at most the declared sort {}",
                            mismatch.actual, mismatch.declared
                        ),
                        error => error.to_string(),
                    }),
                },
                configuration::AssemblyError::Configuration(error) => {
                    configuration_error(&error, program, &names, &self.variables)
                }
            })?;
        self.check_cell_types(&pattern)?;
        Ok(State(pattern))
    }

    /// Check every configuration variable's value in `pattern`, an assembled
    /// `initGeneratedTopCell`, against the typed cell it fills ([`cell_types`]).
    fn check_cell_types(&self, pattern: &Pattern) -> Result<(), ExecError> {
        let Pattern::Application { arguments, .. } = pattern else {
            return Ok(());
        };
        let Some(entries) = arguments
            .first()
            .and_then(|map| self.values.collection_items(map, krs_ir::BuiltinSort::Map))
        else {
            return Ok(());
        };
        let mut bindings = entries
            .iter()
            .filter_map(|entry| {
                let [key, value] = entry.as_slice() else {
                    return None;
                };
                let Pattern::DomainValue { value: name, .. } = values::strip_injections(key) else {
                    return None;
                };
                let name = name.as_utf8().ok()?.strip_prefix('$')?.to_owned();
                Some((name, unboxed_configuration_value(value)))
            })
            .collect::<Vec<_>>();
        bindings.sort_by(|left, right| left.0.cmp(&right.0));
        let print = |pattern: &Pattern| {
            self.unparser
                .print_kore(
                    pattern,
                    &krs_unparse::Options::new(krs_unparse::Mode::Pretty),
                )
                .text
        };
        for (variable, value) in bindings {
            if let Some(mismatch) = self.cell_types.check(&self.values, &variable, value) {
                return Err(ExecError::CollectionElementSort(Box::new(
                    ElementSortMismatch {
                        variable,
                        cell: mismatch.cell,
                        declared: mismatch.declared,
                        position: cell_types::describe(&mismatch.path, print),
                        element: print(mismatch.element),
                        sort: mismatch.sort,
                        expected: mismatch.expected,
                    },
                )));
            }
        }
        Ok(())
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
    /// Returns [`ExecError::Backend`] when the backend fails, or [`ExecError::Result`] when more than one leaf has a defined state.
    pub fn run(&mut self, state: &State, options: RunOptions) -> Result<RunReport, ExecError> {
        let mut request = ExecuteRequest::new(state.0.clone());
        request.strategy = ExecutionStrategy::Any;
        request.max_depth = options.depth;
        let ExecutionResult { leaves, .. } = self.backend.execute(request)?;
        let leaf = one_path(leaves)?;
        let trace = if options.trace {
            self.steps(&leaf.trace)
        } else {
            Vec::new()
        };
        let state = term(&leaf.state, &self.sort_hooks)?;
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
            state: self.krun_floats(state)?,
            trace,
            stdout,
            exit_code,
            log: log_lines(&leaf.effects),
        })
    }

    /// A run or search result with each binary32 and binary64 Float as `krun` prints it in every
    /// output format, in the LLVM runtime's form (`0.15000000000000000e1`, not k-rust's
    /// `1.5000000000000000e+00p53x11`).
    fn krun_floats(&self, state: Term) -> Result<Term, ExecError> {
        match self.unparser.llvm_floats(state.kore()) {
            Some(kore) => self.term(kore),
            None => Ok(state),
        }
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
                    state: self.krun_floats(term(&solution.state, &self.sort_hooks)?)?,
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
            log: log_lines(&response.effects),
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
            return prove_claims(
                &mut prover.backend,
                &prover.sort_hooks,
                &prover.claims,
                options,
            );
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
        prove_claims(&mut self.backend, &self.sort_hooks, &self.claims, options)
    }

    /// The value tables of this definition: names constructors and sorts
    /// ([`ValueIndex::decl`], [`ValueIndex::ctor`]) and decodes patterns ([`ValueIndex::decode`]).
    #[must_use]
    pub const fn values(&self) -> &Arc<ValueIndex> {
        &self.values
    }

    /// The states of a result term, one for each disjunct of a `\or` (a run's or search
    /// solution's state is one), with their cells addressed by KRS names.
    ///
    /// # Errors
    ///
    /// Returns [`ValueError::Malformed`] when a disjunct is not `\bottom` and not one
    /// configuration of this definition conjoined with predicates.
    pub fn views<'t>(&self, term: &'t Term) -> Result<Vec<View<'t>>, ValueError> {
        view::views(&self.values, term.kore())
    }

    /// The state of a result term that is not a disjunction, as [`Self::views`] reads it.
    ///
    /// # Errors
    ///
    /// Fails as [`Self::views`] does, and with [`ValueError::Malformed`] for a disjunction of
    /// several states.
    pub fn view<'t>(&self, term: &'t Term) -> Result<View<'t>, ValueError> {
        let mut views = self.views(term)?;
        if views.len() != 1 {
            return Err(ValueError::Malformed(format!(
                "the term is a disjunction of {} states; read them with `views`",
                views.len()
            )));
        }
        Ok(views.remove(0))
    }

    /// A term from a KORE pattern of this definition, with its KAST conversion, which renders
    /// each domain value by its sort's hook.
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::Result`] when the pattern has no KAST form.
    pub fn term(&self, kore: Pattern) -> Result<Term, ExecError> {
        let kast = Converter::new(&self.sort_hooks)
            .convert(&kore)
            .map_err(|error| ExecError::Result(error.to_string()))?;
        Ok(Term::new(kore, kast))
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

    /// Print the first item of a term's `<k>` cell through the definition's grammar, as
    /// [`Semantics::unparse`] prints it inside the whole term: `Some(None)` when `<k>` is empty,
    /// `None` without a `<k>` cell (see [`Term::k_head_kore`]).
    ///
    /// A symbol without a printable production is printed as KAST and reported in [`Printed::warnings`].
    #[must_use]
    pub fn unparse_k_head(&self, term: &Term) -> Option<Option<Printed>> {
        term.k_head_kore().map(|head| {
            head.map(|item| {
                self.unparser
                    .print_kore(item, &krs_unparse::Options::new(krs_unparse::Mode::Pretty))
            })
        })
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

/// Compile the proof definition of one author spec module to symbolic KORE with the same options as [`compile_definition`].
fn compile_spec_definition(
    definition: &DefinitionIr,
    module: &str,
    timings: &mut Timings,
) -> Result<CompiledArtifacts, DefinitionCompileError> {
    compile_spec_definition_with_context_timed(
        definition,
        module,
        CompileOptions {
            backend: krs_k_rust::Backend::Haskell,
            ..CompileOptions::default()
        },
        timings,
    )
    .map(|(artifacts, _)| artifacts)
}

/// Prove the selected claims of `catalog` on `backend`, one proof per claim, in selection order.
fn prove_claims(
    backend: &mut Backend,
    sort_hooks: &HashMap<String, String>,
    catalog: &[ClaimInfo],
    options: &ProveOptions,
) -> Result<Vec<ProofReport>, ExecError> {
    let selected = claims::select(catalog, &options.claims)?;
    let mut reports = Vec::with_capacity(selected.len());
    for index in selected {
        let claim = catalog[index].clone();
        // A claim whose left-hand side is a disjunction is one backend claim per disjunct, each
        // proven by its own request; the claim holds only if every disjunct does, so its verdict
        // is the weakest of theirs and its leaves are all of theirs.
        let disjuncts = backend.claim_disjuncts(None, &claim.backend_label)?;
        let selectors = if disjuncts.len() > 1 {
            disjuncts
        } else {
            vec![claim.backend_label.clone()]
        };
        let mut verdict = Verdict::Proven;
        let mut leaves = Vec::new();
        for selector in selectors {
            let result = backend.prove(ProveRequest {
                claim: Some(selector),
                max_depth: options.depth,
                ..ProveRequest::default()
            })?;
            let disjunct = Verdict::from_backend(&result.status).ok_or_else(|| {
                ExecError::Result(format!("unknown proof status `{}`", result.status))
            })?;
            verdict = verdict.weakest(disjunct);
            for leaf in &result.leaves {
                leaves.push(ProofLeaf {
                    state: term(&leaf.state, sort_hooks)?,
                    depth: leaf.depth,
                    outcome: leaf.outcome.name().to_owned(),
                    detail: leaf.detail.clone(),
                });
            }
        }
        // The backend assumes a trusted claim and reports it proven; KRS never calls an
        // assumption proven (KF-042).
        if claim.trusted && verdict == Verdict::Proven {
            verdict = Verdict::Trusted;
        }
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

/// The `io::log` lines among committed backend effects, in order.
fn log_lines(effects: &[EffectOutput]) -> Vec<String> {
    effects
        .iter()
        .map(|effect| match effect {
            EffectOutput::UserLog { message } => message.clone(),
        })
        .collect()
}

/// The leaf that is the path of a one-path run.
///
/// A `trivial` or `vacuous` leaf denotes no configuration: its result or its path condition is
/// `#Bottom`, as where a partial function is applied outside its domain.
/// Where the backend splits on whether a result is defined, it returns the leaf under that
/// definedness and such an undefined leaf beside it; their disjunction is the defined leaf alone,
/// so that leaf is the path.
/// The run is undefined only when every leaf is.
fn one_path(leaves: Vec<ExecutionLeaf>) -> Result<ExecutionLeaf, ExecError> {
    let (undefined, defined): (Vec<_>, Vec<_>) = leaves.into_iter().partition(|leaf| {
        matches!(
            leaf.reason,
            HaltReasonOutput::Trivial | HaltReasonOutput::Vacuous
        )
    });
    if defined.is_empty() {
        return undefined.into_iter().next().ok_or_else(|| {
            ExecError::Result(
                "a run must end in exactly one state; the backend returned none".to_owned(),
            )
        });
    }
    <[_; 1]>::try_from(defined)
        .map(|[leaf]| leaf)
        .map_err(|defined: Vec<_>| {
            ExecError::Result(format!(
                "a run must end in exactly one state; the backend returned {} defined states",
                defined.len()
            ))
        })
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

/// The sort hooks of the definition `backend` runs, by KAST sort name: a result's domain value
/// is a token whose text depends on its sort's hook (a `BYTES.Bytes` value is a byte string,
/// not UTF-8 text, and a `STRING.String` value is quoted), and only the definition states them.
fn result_sort_hooks(backend: &mut Backend) -> Result<HashMap<String, String>, ExecError> {
    let definition = backend
        .select_definition(None)
        .map_err(|error| ExecError::Backend(error.to_string()))?;
    Ok(sort_hooks(definition.sorts().iter().filter_map(
        |(name, sort)| Some((name.as_ref(), sort.hook.as_deref()?)),
    )))
}

/// A backend result's term, converted to KAST with its definition's `sort_hooks`.
fn term(
    value: &serde_json::Value,
    sort_hooks: &HashMap<String, String>,
) -> Result<Term, ExecError> {
    let source =
        serde_json::to_string(value).map_err(|error| ExecError::Result(error.to_string()))?;
    let kore =
        kore_json::from_str(&source).map_err(|error| ExecError::Result(error.to_string()))?;
    let kast = Converter::new(sort_hooks)
        .convert(&kore)
        .map_err(|error| ExecError::Result(error.to_string()))?;
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
