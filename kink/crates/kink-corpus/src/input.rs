//! Program parsing and configuration assembly through k-rust's concrete-input API.

use std::{collections::BTreeMap, fmt};

use k_rust::{
    definition::{AttributeKey, Definition, Sentence},
    kast::{Sort, Term},
    kompile::{
        CompileOptions,
        initial_configuration::{
            ConfigurationAssembler, ConfigurationError, ProgramGrammar, program_start_position,
            variable_reading_modules,
        },
    },
    kore::ast::Pattern,
};
use kink_native::{NativeValidator, ValidatedDefinition};

use crate::resolver::{LoadedSource, read_under_root};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProgramSource {
    Text(String),
    File(String),
}

/// One test's inputs: an assignment of a value to each configuration variable the definition
/// declares. `$PGM` is bound by `program`, read at `start_sort`; a definition without `$PGM` takes
/// no program, and its test binds every variable by name in `variables`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TestInputSpec {
    pub program: Option<ProgramSource>,
    pub start_sort: Option<String>,
    pub variables: Vec<(String, VariableInput)>,
}

/// The value of one configuration variable: K text, read at the variable's sort with the rule
/// every tool reads a variable's text with (k-rust `variable_reading_modules`), or a KAST term a
/// front end built without the parser, which is typed and macro-expanded as a parsed value is and
/// must have a sort at most the variable's (k-rust `ConfigurationAssembler::bind_term`).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum VariableInput {
    Text(String),
    Term(Term),
}

impl From<&str> for VariableInput {
    fn from(text: &str) -> Self {
        Self::Text(text.to_owned())
    }
}

impl From<String> for VariableInput {
    fn from(text: String) -> Self {
        Self::Text(text)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum InputError {
    Parse(String),
    Assemble(String),
    Streams(String),
    /// The program binds `$IO` on a definition with stream cells (`stream-mode`): kink runs
    /// stream definitions with IO off only (see [`assemble_input_with`]).
    StreamMode(String),
    MissingVariable(String),
    /// A program given to a definition that declares no `$PGM` (`stray-program`): the program
    /// would bind nothing, so the test would not be the input its author wrote.
    StrayProgram(String),
}

impl fmt::Display for InputError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Parse(message)
            | Self::Assemble(message)
            | Self::Streams(message)
            | Self::StreamMode(message)
            | Self::MissingVariable(message)
            | Self::StrayProgram(message) => f.write_str(message),
        }
    }
}
impl std::error::Error for InputError {}

/// Parse the program and declared variable texts, using deterministic, empty stream defaults.
///
/// It compiles `loaded`'s baseline for its configuration variables; a caller that already holds
/// that compile passes it to [`assemble_input_with`] instead, which gives the same configuration
/// without compiling again.
pub fn assemble_input(loaded: &LoadedSource, spec: &TestInputSpec) -> Result<Pattern, InputError> {
    assemble_input_with(loaded, None, spec)
}

/// [`assemble_input`] with `compiled`, the caller's compile of `loaded`'s baseline under
/// `CompileOptions::default()` (re-pin L1-4): a compile of the same loaded definition under the
/// same options, which k-rust's compile determinism makes the compile `assemble_input` would make
/// (the premise of `NativeValidator::compile_baseline`'s memo and of every kill). Each program
/// input then costs no compile: before L1-4 every program bound a fresh validator and compiled the
/// baseline again (`examples/imp` cold: 7 of the run's 9 baseline compiles, 1.6 s of 14.8 s).
///
/// The caller must pass the compile of the same loaded value (`loaded.baseline`, bound under
/// `CompileOptions::default()`); every caller does (kink-flow's admission, kink-corpus admission
/// and `Store::rebuild_tests`). The guard below is structural only: it refuses a `compiled` whose
/// options differ or whose source definition is unequal under k-rust's definition equality, and
/// then compiles the baseline here, as without it. That equality ignores term metadata (spans,
/// production identity, explicit compiler sorts, origins), so a compile of a definition that
/// differs from `loaded`'s only there passes the guard (re-pin L1-4 fix 1, review D7).
///
/// On a definition with stream cells (a cell declared `stream="stdin"` or `stream="stdout"`) a
/// program may not bind `IO` (`InputError::StreamMode`, reason `stream-mode`; KINK-CENSUS-RUNLIST,
/// fz26): kink binds `$IO` to `"off"`. With IO off the stream cells are data, like `$PGM`: the
/// stdout cell holds the text the program printed and the stdin cell the input not yet read, so
/// the final configuration states the output, and comparing two runs' ends compares output text
/// and unread input. With IO on, output would leave the configuration through `#write`, so an
/// end would no longer state it. The refusal keeps that meaning; soundness does not rest on it,
/// since an execute request performs no console operation and lists every one a run needs on its
/// `unsupportedHooks`, which excludes the run. A stream-free definition that declares its own
/// `$IO` variable may bind it.
pub fn assemble_input_with(
    loaded: &LoadedSource,
    compiled: Option<&ValidatedDefinition>,
    spec: &TestInputSpec,
) -> Result<Pattern, InputError> {
    let text = match &spec.program {
        None => None,
        Some(ProgramSource::Text(text)) => Some(text.clone()),
        Some(ProgramSource::File(name)) => {
            let (_, bytes) = read_under_root(&loaded.root, name)
                .map_err(|e| InputError::Parse(e.to_string()))?;
            Some(String::from_utf8(bytes).map_err(|e| InputError::Parse(e.to_string()))?)
        }
    };
    let grammar = InputGrammar::prepare(loaded, compiled)?;
    InputAssembler::new(&grammar).assemble(
        text.as_deref()
            .map(|text| (text, spec.start_sort.as_deref())),
        &spec.variables,
    )
}

#[cfg(feature = "measure")]
thread_local! {
    static INPUT_GRAMMAR_BUILDS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// How many times [`InputGrammar::prepare`] ran on this thread; a test reads it to pin how often
/// a caller builds the grammar. A test instrument: only the `measure` feature, which dependents
/// enable from their dev-dependencies, compiles it.
#[cfg(feature = "measure")]
pub fn input_grammar_builds() -> usize {
    INPUT_GRAMMAR_BUILDS.with(std::cell::Cell::get)
}

/// What assembling inputs of one compiled definition needs, built once per definition: the
/// program grammar, the declared variables, the grammar each variable's text is read with first,
/// the start sort and whether the definition has stream cells.
pub struct InputGrammar {
    grammar: ProgramGrammar,
    main_module: String,
    syntax_module: String,
    variables: BTreeMap<String, Sort>,
    /// The variables whose text is read with the syntax module's grammar first, as a program is
    /// (k-rust `variable_reading_modules`): the rule krs-exec reads them with, so one text denotes
    /// one term in both tools.
    reading_modules: BTreeMap<String, String>,
    default_start: Sort,
    stream_cells: bool,
}

impl fmt::Debug for InputGrammar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("InputGrammar")
            .field("main_module", &self.main_module)
            .field("syntax_module", &self.syntax_module)
            .field("variables", &self.variables)
            .field("default_start", &self.default_start)
            .field("stream_cells", &self.stream_cells)
            .finish_non_exhaustive()
    }
}

impl InputGrammar {
    /// The grammar of `loaded`'s baseline, with `compiled` as in [`assemble_input_with`] (the
    /// same guard: a `compiled` that is not that compile is replaced by a compile made here).
    pub fn prepare(
        loaded: &LoadedSource,
        compiled: Option<&ValidatedDefinition>,
    ) -> Result<Self, InputError> {
        #[cfg(feature = "measure")]
        INPUT_GRAMMAR_BUILDS.with(|builds| builds.set(builds.get() + 1));
        let fresh;
        let compiled = match compiled {
            Some(compiled)
                if *compiled.compile_options() == CompileOptions::default()
                    && compiled.definition() == loaded.baseline.definition() =>
            {
                compiled
            }
            _ => {
                fresh = NativeValidator::bind(loaded.baseline.clone(), CompileOptions::default())
                    .compile_baseline()
                    .map_err(|e| InputError::Assemble(e.to_string()))?;
                &fresh
            }
        };
        let grammar = ProgramGrammar::new(loaded.baseline.definition()).map_err(input_error)?;
        let variables = compiled.artifacts().configuration_variables.clone();
        let default_start =
            program_start_position(variables.get("PGM").unwrap_or(&Sort::new("KItem")));
        let syntax_module = loaded.syntax_module.to_string();
        let reading_modules =
            variable_reading_modules(&grammar, &syntax_module, &variables).map_err(input_error)?;
        Ok(Self {
            grammar,
            main_module: loaded.baseline.definition().main_module.to_string(),
            syntax_module,
            variables,
            reading_modules,
            default_start,
            stream_cells: has_stream_cells(&compiled.artifacts().execution_definition),
        })
    }

    /// The configuration variables, without `$`, whose text kink reads with the syntax module's
    /// grammar first (k-rust `variable_reading_modules`), in name order. Only these can read
    /// differently under [`InputAssembler::reading_with_main_module`].
    pub fn syntax_read_variables(&self) -> impl Iterator<Item = &str> {
        self.reading_modules.keys().map(String::as_str)
    }
}

/// Assembles the initial configurations of one [`InputGrammar`] with one k-rust
/// [`ConfigurationAssembler`], whose parsers, macro-expansion views and sort injectors are built
/// on first use and then serve every later program.
pub struct InputAssembler<'g> {
    grammar: &'g InputGrammar,
    assembler: ConfigurationAssembler<'g>,
}

impl fmt::Debug for InputAssembler<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("InputAssembler")
            .field("grammar", self.grammar)
            .finish_non_exhaustive()
    }
}

impl<'g> InputAssembler<'g> {
    pub fn new(grammar: &'g InputGrammar) -> Self {
        Self {
            grammar,
            assembler: ConfigurationAssembler::new(
                &grammar.grammar,
                grammar.main_module.as_str(),
                grammar.syntax_module.as_str(),
                &grammar.variables,
            )
            .reading_variables_with(grammar.reading_modules.clone()),
        }
    }

    /// An assembler that reads every configuration variable's text with the main module's
    /// grammar alone (or the module its cell's `parser` attribute names), as krun reads `-c` and
    /// a k-rust-fuzz campaign assembles a case. It differs from [`Self::new`] only on the
    /// variables [`InputGrammar::syntax_read_variables`] names, and only on texts the two
    /// grammars read as different terms (or that one of them does not parse): kink-flow's `fuzz`
    /// uses it to recognize a case whose campaign input is not kink's.
    pub fn reading_with_main_module(grammar: &'g InputGrammar) -> Self {
        Self {
            grammar,
            assembler: ConfigurationAssembler::new(
                &grammar.grammar,
                grammar.main_module.as_str(),
                grammar.syntax_module.as_str(),
                &grammar.variables,
            ),
        }
    }

    /// The initial configuration of `program`, a program text read at its start sort (the
    /// start position of `$PGM`'s sort by default), and the variable values `variables`, as
    /// [`assemble_input_with`] assembles it. Without a program `$PGM` is left unbound, so a
    /// definition that declares it refuses the configuration as missing `$PGM`, unless a term
    /// binds it: a [`VariableInput::Term`] for `PGM` is bound as a program built without the
    /// parser (k-rust `ConfigurationAssembler::program_term`), and with a program text as well it
    /// is a second `$PGM`. A program given to a definition that declares no `$PGM` is refused
    /// (`StrayProgram`), since it would bind nothing.
    ///
    /// The assembler is cleared first, so a configuration an earlier call abandoned on an error
    /// leaves nothing behind: each call gives what a fresh assembler gives.
    pub fn assemble(
        &mut self,
        program: Option<(&str, Option<&str>)>,
        variables: &[(String, VariableInput)],
    ) -> Result<Pattern, InputError> {
        let assembler = &mut self.assembler;
        assembler.clear();
        if let Some((text, start_sort)) = program {
            if !self.grammar.variables.contains_key("PGM") {
                return Err(InputError::StrayProgram(stray_program(
                    &self.grammar.variables,
                )));
            }
            let start = start_sort.map_or_else(|| self.grammar.default_start.clone(), Sort::new);
            assembler.program(&start, text).map_err(input_error)?;
        }
        if let Some((name, _)) = variables.iter().find(|(name, _)| is_io(name))
            && self.grammar.stream_cells
        {
            return Err(InputError::StreamMode(format!(
                "the program binds {name} on a definition with stream cells: kink runs a stream \
                 definition with $IO = \"off\" only, so that its stream cells state the program's \
                 output and unread input"
            )));
        }
        for (name, value) in variables {
            match value {
                VariableInput::Text(text) => assembler.bind(name, text),
                VariableInput::Term(term) if name.strip_prefix('$').unwrap_or(name) == "PGM" => {
                    assembler.program_term(term.clone())
                }
                VariableInput::Term(term) => assembler.bind_term(name, term.clone()),
            }
            .map_err(input_error)?;
        }
        assembler
            .bind_stream_defaults::<ConfigurationError>(false, false, || Ok(Vec::new()))
            .map_err(input_error)?;
        assembler.finish().map_err(input_error)
    }
}

/// Why a program text is refused on a definition without `$PGM`, naming every declared variable
/// with its sort.
fn stray_program(variables: &BTreeMap<String, Sort>) -> String {
    let declared = variables
        .iter()
        .map(|(name, sort)| format!("${name}:{sort}"))
        .collect::<Vec<_>>();
    if declared.is_empty() {
        "the definition declares no $PGM, so a program text binds nothing; it declares no \
         configuration variable either, so its case binds none"
            .to_owned()
    } else {
        format!(
            "the definition declares no $PGM, so a program text binds nothing; bind its \
             configuration variables by name: {}",
            declared.join(", ")
        )
    }
}

/// Whether a program variable's name names `$IO` (it may be written with or without its `$`).
fn is_io(name: &str) -> bool {
    name.strip_prefix('$').unwrap_or(name) == "IO"
}

/// Whether `definition` (a compile's execution definition) declares a stream cell: a production
/// carrying the `stream` attribute, which configuration expansion gives the cell declared with it.
fn has_stream_cells(definition: &Definition) -> bool {
    definition.modules.iter().any(|module| {
        module.local_sentences.iter().any(|sentence| {
            matches!(&**sentence, Sentence::Production { attributes, .. }
                if attributes.string(AttributeKey::Stream).is_some())
        })
    })
}

fn input_error(error: ConfigurationError) -> InputError {
    let message = error.to_string();
    match error {
        ConfigurationError::Program(_)
        | ConfigurationError::Parse { .. }
        | ConfigurationError::Parser(_) => InputError::Parse(message),
        ConfigurationError::Missing { names }
            if names
                .iter()
                .any(|name| matches!(name.as_str(), "$IO" | "$STDIN")) =>
        {
            InputError::Streams(message)
        }
        ConfigurationError::Missing { .. } | ConfigurationError::UnknownVariable { .. } => {
            InputError::MissingVariable(message)
        }
        _ => InputError::Assemble(message),
    }
}
