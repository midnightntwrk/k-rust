//! Program parsing and configuration assembly through k-rust's concrete-input API.

use std::{collections::BTreeMap, fmt};

use k_rust::{
    definition::{AttributeKey, Definition, Sentence},
    inner::{ParseError, ProgramParseError},
    kast::{Sort, Term},
    kompile::{
        CompileOptions,
        initial_configuration::{
            ConfigurationAssembler, ConfigurationError, ProgramGrammar, program_start_position,
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
/// every tool reads a variable's text with (k-rust `variable_reading_modules`), a KAST term a
/// front end built without the parser, which is typed and macro-expanded as a parsed value is and
/// must have a sort at most the variable's (k-rust `ConfigurationAssembler::bind_term`), or a
/// KORE value a front end lowered with the definition at exactly the variable's declared sort
/// (an input's declared default), placed as every value is and not typed again (k-rust
/// `ConfigurationAssembler::bind_pattern`).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum VariableInput {
    Text(String),
    Term(Term),
    Pattern(Pattern),
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
    /// A K text does not parse: the program text at its start sort, or a variable's text at its
    /// sort (k-rust `ConfigurationError::Program`, `ConfigurationError::Parse`); from
    /// [`assemble_input_with`] also a program file that cannot be read as UTF-8 text.
    Parse(String),
    /// The definition's grammar gives no parser for a text (k-rust
    /// `ConfigurationError::Parser`: a missing module, a grammar the parser generator refuses):
    /// a fault of the definition, not of the text, which was not read. Refused with the reason
    /// of a parse failure, `parse` ([`crate::admission::input_refusal`]), and told apart from one
    /// so that a statement that a text must not parse is never met by it.
    Grammar(String),
    Assemble(String),
    Streams(String),
    /// The program binds `$IO` on a definition with stream cells (`stream-mode`): kink runs
    /// stream definitions with IO off only (see [`assemble_input_with`]).
    StreamMode(String),
    MissingVariable(String),
    /// A program given to a definition that declares no `$PGM` (`stray-program`): the program
    /// would bind nothing, so the test would not be the input its author wrote.
    StrayProgram(String),
    /// k-rust's checked sort inference (`KRUST_TYPE_INFERENCE_MODE=checked`) found its portable
    /// and Z3 engines disagreeing on a text (`ParseError::InferenceEngineDisagreement`), in the
    /// program text's or a variable's parse, in any attempt assembly made at it: whether the text
    /// parses is not decided (`inference-disagreement`). k-rust keeps the disagreement apart from
    /// a sort-inference rejection so that a caller expecting a rejection does not take it for
    /// one; it is never [`Self::Parse`], so it never meets a statement that the text must not
    /// parse, and a grammar mutant's reparse never reads it as a rejection.
    InferenceDisagreement(String),
}

impl fmt::Display for InputError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Parse(message)
            | Self::Grammar(message)
            | Self::Assemble(message)
            | Self::Streams(message)
            | Self::StreamMode(message)
            | Self::MissingVariable(message)
            | Self::StrayProgram(message)
            | Self::InferenceDisagreement(message) => f.write_str(message),
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
/// program grammar, the declared variables, the start sort and whether the definition has stream
/// cells.
pub struct InputGrammar {
    grammar: ProgramGrammar,
    main_module: String,
    syntax_module: String,
    variables: BTreeMap<String, Sort>,
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
        Ok(Self {
            grammar,
            main_module: loaded.baseline.definition().main_module.to_string(),
            syntax_module,
            variables,
            default_start,
            stream_cells: has_stream_cells(&compiled.artifacts().execution_definition),
        })
    }

    /// This grammar with its program grammar built from `definition` instead: the grammar a
    /// mutant whose edits change only grammar sentences reads its programs with (kink-flow, PJ-34).
    /// The main and syntax module, the configuration variables with their sorts, the default
    /// start sort and the stream-cell flag are kept: each is a function of the configuration and
    /// the module names, which an edit of productions, token, lexical, priority or associativity
    /// declarations does not change (kink-patch refuses an edit of a configuration, a sort
    /// declaration or a cell production).
    ///
    /// # Errors
    ///
    /// k-rust's refusal to build the program grammar of `definition`.
    pub fn with_program_grammar_of(&self, definition: &Definition) -> Result<Self, InputError> {
        let grammar = ProgramGrammar::new(definition).map_err(input_error)?;
        Ok(Self {
            grammar,
            main_module: self.main_module.clone(),
            syntax_module: self.syntax_module.clone(),
            variables: self.variables.clone(),
            default_start: self.default_start.clone(),
            stream_cells: self.stream_cells,
        })
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
            ),
        }
    }

    /// The initial configuration of `program`, a program text read at its start sort (the
    /// start position of `$PGM`'s sort by default), and the variable values `variables`, as
    /// [`assemble_input_with`] assembles it. Without a program `$PGM` is left unbound, so a
    /// definition that declares it refuses the configuration as missing `$PGM`, unless a term
    /// binds it: a [`VariableInput::Term`] for `PGM` is bound as a program built without the
    /// parser (k-rust `ConfigurationAssembler::program_term`), and a [`VariableInput::Pattern`]
    /// for it as a lowered program (`program_pattern`); with a program text as well either is a
    /// second `$PGM`. A program given to a definition that declares no `$PGM` is refused
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
                VariableInput::Pattern(pattern)
                    if name.strip_prefix('$').unwrap_or(name) == "PGM" =>
                {
                    assembler.program_pattern(pattern.clone())
                }
                VariableInput::Pattern(pattern) => assembler.bind_pattern(name, pattern.clone()),
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
    if undecided_parse(&error) {
        return InputError::InferenceDisagreement(message);
    }
    match error {
        ConfigurationError::Program(_) | ConfigurationError::Parse { .. } => {
            InputError::Parse(message)
        }
        ConfigurationError::Parser(_) => InputError::Grammar(message),
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

/// Whether a parse attempt `error` records is k-rust's checked-inference disagreement
/// ([`InputError::InferenceDisagreement`]): the program text's failure or a variable's, its
/// syntax module's attempt, and the item attempt each of them records.
fn undecided_parse(error: &ConfigurationError) -> bool {
    fn undecided(error: &ProgramParseError) -> bool {
        matches!(*error.error, ParseError::InferenceEngineDisagreement { .. })
            || error.item_attempt.as_deref().is_some_and(undecided)
    }
    match error {
        ConfigurationError::Program(error) => undecided(error),
        ConfigurationError::Parse {
            error,
            syntax_attempt,
            ..
        } => undecided(error) || syntax_attempt.as_deref().is_some_and(undecided),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn attempt(error: ParseError, item_attempt: Option<ProgramParseError>) -> ProgramParseError {
        ProgramParseError {
            module: "SYNTAX".to_owned(),
            start_sort: Sort::new("Exp"),
            error: Box::new(error),
            item_attempt: item_attempt.map(Box::new),
        }
    }

    fn disagreement() -> ParseError {
        ParseError::InferenceEngineDisagreement {
            portable: Ok("term".to_owned()),
            z3: Err("no sort".to_owned()),
            ambiguous_parse: false,
        }
    }

    fn rejection() -> ParseError {
        ParseError::SortInference {
            message: "no sort".to_owned(),
        }
    }

    fn variable(
        error: ProgramParseError,
        syntax_attempt: Option<ProgramParseError>,
    ) -> ConfigurationError {
        ConfigurationError::Parse {
            variable: "$N".to_owned(),
            sort: Sort::new("Int"),
            error: Box::new(error),
            syntax_attempt: syntax_attempt.map(Box::new),
        }
    }

    /// PJ-34 (FX2): under k-rust's checked inference the two engines can disagree on a text.
    /// k-rust keeps that apart from a rejection (`ParseError::InferenceEngineDisagreement`), and
    /// so does kink: wherever the disagreement is among the attempts of a failure (the program
    /// text's, a variable's, its syntax module's attempt, an item attempt), the failure is not a
    /// parse rejection, so it meets no `rejected = "parse"` statement and kills no grammar
    /// mutant, and it is refused `inputs`/`inference-disagreement`. A rejection without one is
    /// still `InputError::Parse`.
    #[test]
    fn an_inference_disagreement_is_no_parse_rejection() {
        let undecided = [
            ConfigurationError::Program(attempt(disagreement(), None)),
            ConfigurationError::Program(attempt(rejection(), Some(attempt(disagreement(), None)))),
            variable(attempt(disagreement(), None), None),
            variable(
                attempt(rejection(), None),
                Some(attempt(disagreement(), None)),
            ),
            variable(
                attempt(rejection(), Some(attempt(disagreement(), None))),
                Some(attempt(rejection(), None)),
            ),
        ];
        for error in undecided {
            let read = input_error(error);
            assert!(
                matches!(read, InputError::InferenceDisagreement(_)),
                "{read:?}"
            );
            let refusal = crate::admission::input_refusal(read);
            assert_eq!(
                (refusal.stage.as_str(), refusal.reason.as_str()),
                ("inputs", "inference-disagreement")
            );
        }
        for error in [
            ConfigurationError::Program(attempt(rejection(), None)),
            variable(attempt(rejection(), None), Some(attempt(rejection(), None))),
        ] {
            assert!(matches!(input_error(error), InputError::Parse(_)));
        }
    }
}
