//! The portable front half of `krust krun`: from a compiled definition and a program's text to
//! the initial configuration krun runs, and to the backend krun runs it on.
//!
//! `krust krun` is this module plus what only a command line has: reading the program and the
//! standard input, loading a runnable artifact or compiling a source definition, phrasing errors
//! in terms of its arguments, building its run options, and timing each phase. A library caller
//! that assembles configurations through [`KrunAssembler::assemble`], builds its backend with
//! [`KrunDefinition::backend`] and prepares each configuration with [`with_initial_term_on`]
//! gets the configuration, the rewrite theory and the initial term krun gets for the same
//! definition and inputs, on a stack that holds them; what it then runs is its own choice
//! (krun runs [`Backend::run_cli`]).
//!
//! The reusable parts are built once per definition and serve every program:
//!
//! ```no_run
//! # use k_rust::{backend::BackendOptions, krun::{KrunDefinition, KrunInputs, ProgramText}};
//! # fn run(definition: KrunDefinition<'_>, programs: &[String]) -> Result<(), Box<dyn std::error::Error>> {
//! let grammar = definition.program_grammar()?;
//! let mut assembler = definition.assembler(&grammar);
//! let mut backend = definition.backend(BackendOptions::default())?;
//! let start_sort = k_rust::kast::parser::parse_sort("Pgm")?;
//! for program in programs {
//!     let initial = assembler.assemble(
//!         &KrunInputs {
//!             start_sort: &start_sort,
//!             program: Some(ProgramText::unnamed(program)),
//!             configuration_variables: &[],
//!             io: false,
//!         },
//!         || Ok::<_, k_rust::kompile::ConfigurationError>(Vec::new()),
//!     )?;
//!     k_rust::krun::with_initial_term_on(&mut backend, &initial, |backend, term| {
//!         // run `term.pattern` on `backend`, for example with `Backend::run_cli`
//! #       let _ = (backend, term);
//!         Ok(())
//!     })?;
//! }
//! # Ok(())
//! # }
//! ```

use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fmt,
    sync::Arc,
};

use k_rust_backend::{definition::BackendDefinition, nesting, rewrite};

use crate::{
    backend::{Backend, BackendError, BackendOptions},
    definition::Definition,
    inner::UNNAMED_PROGRAM,
    kast::Sort as KastSort,
    kompile::{ConfigurationAssembler, ConfigurationError, ProgramGrammar},
    kore::{
        ast::{Definition as KoreDefinition, Pattern},
        parser::{ParseError, parse_definition},
    },
};

/// The parts of a compiled definition krun reads to assemble and run a configuration.
///
/// A source compilation yields them as the loaded frontend definition
/// ([`crate::outer::LoadedDefinition::into_definition`]) and the fields of
/// [`crate::kompile::CompiledKoreArtifacts`] of the same names; a runnable artifact stores the
/// same parts.
#[derive(Clone, Copy, Debug)]
pub struct KrunDefinition<'a> {
    /// The module whose configuration is built and executed.
    pub main_module: &'a str,
    /// The module whose grammar parses the program.
    pub syntax_module: &'a str,
    /// The frontend definition, from which the program grammar is built.
    pub frontend_definition: &'a Definition,
    /// Each declared configuration variable, without its `$`, with its sort.
    pub configuration_variables: &'a BTreeMap<String, KastSort>,
    /// The executable rewrite precedence of the compilation that emitted `definition_kore`.
    pub execution_rewrite_order: &'a [String],
    /// The KORE text of the execution definition.
    pub definition_kore: &'a str,
}

impl<'a> KrunDefinition<'a> {
    /// The grammar programs and configuration values are parsed against.
    ///
    /// # Errors
    ///
    /// When the extended frontend definition does not resolve.
    pub fn program_grammar(&self) -> Result<ProgramGrammar, ConfigurationError> {
        ProgramGrammar::new(self.frontend_definition)
    }

    /// Whether `grammar` was built by [`Self::program_grammar`] from this definition's frontend
    /// definition, or from a clone of it.
    ///
    /// The grammar extends a clone of the frontend definition, whose sentences it shares, so the
    /// check is that each module has the same name and begins with the very same sentences: a
    /// grammar of another compilation, such as the other side of a differential, fails it even
    /// when its module names are the same. It costs one pointer comparison per sentence.
    #[must_use]
    pub fn grammar_matches(&self, grammar: &ProgramGrammar) -> bool {
        let frontend = &self.frontend_definition.modules;
        let extended = &grammar.definition().modules;
        frontend.len() == extended.len()
            && frontend.iter().zip(extended).all(|(module, extended)| {
                module.name == extended.name
                    && module.local_sentences.len() <= extended.local_sentences.len()
                    && module
                        .local_sentences
                        .iter()
                        .zip(&extended.local_sentences)
                        .all(|(sentence, extended)| Arc::ptr_eq(sentence, extended))
            })
    }

    /// An empty assembler for this definition's configurations, parsing with `grammar`, which
    /// must be [`Self::program_grammar`] of this definition ([`Self::grammar_matches`]; checked
    /// by a debug assertion). With a grammar of another definition, programs would be parsed
    /// with that definition's syntax and no error would say so.
    #[must_use]
    pub fn assembler<'g>(&self, grammar: &'g ProgramGrammar) -> KrunAssembler<'g>
    where
        'a: 'g,
    {
        debug_assert!(
            self.grammar_matches(grammar),
            "the program grammar was not built from this definition"
        );
        KrunAssembler::new(
            grammar,
            self.main_module,
            self.syntax_module,
            self.configuration_variables,
        )
    }

    /// Parse [`Self::definition_kore`].
    ///
    /// # Errors
    ///
    /// When the text is not a KORE definition.
    pub fn parse_kore(&self) -> Result<KoreDefinition, ParseError> {
        parse_definition(self.definition_kore)
    }

    /// Internalize the main module of `syntax`, which is [`Self::parse_kore`], for source
    /// execution: rewrite rules are tried in [`Self::execution_rewrite_order`], which selects the
    /// path a run that follows one path takes.
    ///
    /// # Errors
    ///
    /// When the backend refuses the definition.
    pub fn internalize(&self, syntax: &KoreDefinition) -> Result<BackendDefinition, BackendError> {
        Backend::internalize_source_definition(
            syntax,
            self.main_module,
            self.execution_rewrite_order,
        )
    }

    /// The backend krun runs configurations of this definition on: [`Self::parse_kore`], then
    /// [`Self::internalize`], then [`Backend::from_internalized`] with `options`.
    ///
    /// krun also prints the load-time findings of
    /// [`crate::backend::execution::value_claim_warnings`] of the internalized definition; a
    /// caller that wants them takes the three steps itself.
    ///
    /// # Errors
    ///
    /// When a step fails.
    pub fn backend(&self, options: BackendOptions) -> Result<Backend, KrunBackendError> {
        let syntax = self.parse_kore().map_err(KrunBackendError::Parse)?;
        let definition = self
            .internalize(&syntax)
            .map_err(KrunBackendError::Backend)?;
        Backend::from_internalized(definition, options).map_err(KrunBackendError::Backend)
    }
}

/// Why [`KrunDefinition::backend`] built no backend.
#[derive(Debug)]
#[non_exhaustive]
pub enum KrunBackendError {
    /// The definition's KORE text did not parse.
    Parse(ParseError),
    /// The backend refused the definition.
    Backend(BackendError),
}

impl fmt::Display for KrunBackendError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Parse(error) => error.fmt(formatter),
            Self::Backend(error) => error.fmt(formatter),
        }
    }
}

impl Error for KrunBackendError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Parse(error) => Some(error),
            Self::Backend(error) => Some(error),
        }
    }
}

/// A program's text with the file name its locations carry.
#[derive(Clone, Copy, Debug)]
pub struct ProgramText<'a> {
    /// The program's source text, parsed with the definition's syntax module.
    pub text: &'a str,
    /// [`UNNAMED_PROGRAM`] for an expression or standard input, otherwise the name krun gives a
    /// program file ([`crate::inner::program_file_name`]).
    pub file: &'a str,
    /// Whether the text is the process's standard input, which then holds nothing more for
    /// `$STDIN`.
    pub from_standard_input: bool,
}

impl<'a> ProgramText<'a> {
    /// A program given as text, read from no file: krun's `--expression`.
    #[must_use]
    pub fn unnamed(text: &'a str) -> Self {
        Self {
            text,
            file: UNNAMED_PROGRAM,
            from_standard_input: false,
        }
    }
}

/// The inputs of one configuration, as krun takes them from its arguments.
#[derive(Clone, Copy, Debug)]
pub struct KrunInputs<'a> {
    /// The sort the program is parsed at (krun's `--sort`).
    pub start_sort: &'a KastSort,
    /// The program, or `None` when none is passed. krun reads `$PGM` from standard input when
    /// none is passed and the definition declares `$PGM`; a library caller passes that text as a
    /// program with [`ProgramText::from_standard_input`] set.
    pub program: Option<ProgramText<'a>>,
    /// The configuration variables other than `$PGM`, each name with or without its `$`, in the
    /// order they are bound (krun's `-c NAME=VALUE`, in command-line order).
    pub configuration_variables: &'a [(&'a str, &'a str)],
    /// Whether the run has a console (krun's `--io`): `$IO` is bound to `on` or `off` after it,
    /// and with a console `$STDIN` is empty.
    pub io: bool,
}

/// [`ConfigurationAssembler`] with krun's binding order and stream defaults.
///
/// krun binds `$PGM` first, from the program; then the other configuration variables, in the
/// order given; then the unbound stream variables ([`Self::bind_stream_defaults`]); and assembles
/// the configuration. [`Self::assemble`] takes the four steps; krun takes them one by one so that
/// it can time the program apart from the configuration values.
///
/// A caller that takes the steps itself calls [`Self::clear`] after a step fails, before the next
/// configuration: a failed step leaves what was bound before it, so the next program would be
/// reported as a second `$PGM`. [`Self::assemble`] clears before it starts.
///
/// Parsers are built on first use and kept, so one assembler serves every configuration of its
/// definition.
pub struct KrunAssembler<'g> {
    assembler: ConfigurationAssembler<'g>,
    variables: &'g BTreeMap<String, KastSort>,
    program_from_standard_input: bool,
}

impl<'g> KrunAssembler<'g> {
    /// An empty assembler from only the parts assembly reads: the grammar
    /// ([`KrunDefinition::program_grammar`]), the main module, the syntax module and the declared
    /// configuration variables with their sorts, each without its `$`.
    /// [`KrunDefinition::assembler`] is this with a definition's fields, and also checks that
    /// the grammar is that definition's; a caller of this constructor ensures it.
    #[must_use]
    pub fn new(
        grammar: &'g ProgramGrammar,
        main_module: &str,
        syntax_module: &str,
        configuration_variables: &'g BTreeMap<String, KastSort>,
    ) -> Self {
        Self {
            assembler: ConfigurationAssembler::new(
                grammar,
                main_module,
                syntax_module,
                configuration_variables,
            ),
            variables: configuration_variables,
            program_from_standard_input: false,
        }
    }

    /// Whether a configuration binds `$PGM`: when a program is supplied, which is parsed and
    /// checked whether or not the definition declares `$PGM`, or when the definition declares
    /// it. A definition that declares no `$PGM` and is given no program runs from its
    /// configuration variables alone, and reads no program.
    #[must_use]
    pub fn binds_program(&self, program_supplied: bool) -> bool {
        program_supplied || self.variables.contains_key("PGM")
    }

    /// Bind `$PGM` to `program`, parsed with the syntax module at `start_sort`.
    ///
    /// # Errors
    ///
    /// When `$PGM` is already bound or the program does not parse, sort and convert.
    pub fn program(
        &mut self,
        start_sort: &KastSort,
        program: &ProgramText<'_>,
    ) -> Result<(), ConfigurationError> {
        self.assembler
            .program_file(start_sort, program.text, program.file)?;
        self.program_from_standard_input = program.from_standard_input;
        Ok(())
    }

    /// Bind the configuration variable `name` (with or without its `$`) to `text`
    /// ([`ConfigurationAssembler::bind`]).
    ///
    /// # Errors
    ///
    /// As [`ConfigurationAssembler::bind`].
    pub fn bind(&mut self, name: &str, text: &str) -> Result<(), ConfigurationError> {
        self.assembler.bind(name, text)
    }

    /// Bind each declared `String`-sorted stream variable that is still unbound: `$IO` to `on`
    /// or `off` after `io`, and `$STDIN` to krun's buffered text of what `read_standard_input`
    /// returns (its trailing newlines replaced by exactly one; `"\n"` for no input), or to the
    /// empty string when `io` is on or the program was read from standard input
    /// ([`ConfigurationAssembler::bind_stream_defaults`]).
    /// `read_standard_input` runs only when its result is used.
    ///
    /// # Errors
    ///
    /// When a default does not bind, or `read_standard_input` fails.
    pub fn bind_stream_defaults<E: From<ConfigurationError>>(
        &mut self,
        io: bool,
        read_standard_input: impl FnOnce() -> Result<Vec<u8>, E>,
    ) -> Result<(), E> {
        self.assembler
            .bind_stream_defaults(io, self.program_from_standard_input, || {
                read_standard_input().map(buffered_stdin_bytes)
            })
    }

    /// Assemble the configuration ([`ConfigurationAssembler::finish`]), leaving the assembler
    /// empty for the next one.
    ///
    /// # Errors
    ///
    /// When a declared variable is unbound; nothing changes then.
    pub fn finish(&mut self) -> Result<Pattern, ConfigurationError> {
        let initial = self.assembler.finish()?;
        self.program_from_standard_input = false;
        Ok(initial)
    }

    /// Discard the program and every binding without assembling them.
    pub fn clear(&mut self) {
        self.assembler.clear();
        self.program_from_standard_input = false;
    }

    /// The initial configuration krun builds from `inputs`, with `read_standard_input` as its
    /// standard input: the program when it binds `$PGM` ([`Self::binds_program`]), then each
    /// configuration variable in order, then the stream defaults, then the assembly.
    ///
    /// When the definition declares `$PGM` and `inputs.program` is `None`, the configuration is
    /// missing `$PGM`. The assembler is cleared first, so whatever an earlier failed step or an
    /// unwound panic left in it is discarded; on an error it is left empty, as after a success.
    ///
    /// # Errors
    ///
    /// The first error of a step.
    pub fn assemble<E: From<ConfigurationError>>(
        &mut self,
        inputs: &KrunInputs<'_>,
        read_standard_input: impl FnOnce() -> Result<Vec<u8>, E>,
    ) -> Result<Pattern, E> {
        self.clear();
        let assembled = self.assemble_steps(inputs, read_standard_input);
        if assembled.is_err() {
            self.clear();
        }
        assembled
    }

    fn assemble_steps<E: From<ConfigurationError>>(
        &mut self,
        inputs: &KrunInputs<'_>,
        read_standard_input: impl FnOnce() -> Result<Vec<u8>, E>,
    ) -> Result<Pattern, E> {
        // krun takes the same steps in the same order in `krun` (`crates/k-rust/src/main.rs`),
        // one by one, around its timing phases and its own `NAME=VALUE` split: a change of the
        // order or a new step is made in both.
        // A supplied program always binds `$PGM` (`Self::binds_program`).
        if let Some(program) = &inputs.program {
            self.program(inputs.start_sort, program)?;
        }
        for &(name, text) in inputs.configuration_variables {
            self.bind(name, text)?;
        }
        self.bind_stream_defaults(inputs.io, read_standard_input)?;
        Ok(self.finish()?)
    }
}

/// An initial configuration prepared as krun prepares it, to be run on the backend it was
/// prepared for.
#[derive(Debug, PartialEq, Eq)]
pub struct InitialTerm {
    /// The internalized configuration, with no constraints.
    pub pattern: rewrite::Pattern,
    /// The definition's function symbols ([`BackendDefinition::function_symbol_names`]), which a
    /// run takes in [`crate::backend::execution::BackendRunOptions::function_symbols`].
    pub function_symbols: BTreeSet<String>,
}

/// krun's preparation of `initial`: the function symbols, the check that it is an executable
/// pattern (no macro or alias), and its unverified admission and internalization. The assembler
/// built it from parsed and sorted inputs, so it is not verified again as a standalone pattern.
fn prepare_initial(
    definition: &BackendDefinition,
    initial: &Pattern,
) -> Result<InitialTerm, Box<dyn Error>> {
    let function_symbols = definition.function_symbol_names();
    definition.validate_executable_pattern(initial)?;
    let term = definition
        .admit_unverified(initial, &[])
        .internalize_term()?;
    Ok(InitialTerm {
        pattern: rewrite::Pattern {
            term,
            constraints: Vec::new(),
        },
        function_symbols,
    })
}

/// Run `work` on a stack that holds an initial configuration and the passes over it.
///
/// The initial configuration is as deep as the program and the configuration values, which
/// nothing bounds: validating, internalizing and executing it recurse over it, and so do the
/// drops of the internal terms built from it. All of it runs on a stack the backend measures from
/// the configuration and the definition (`BackendDefinition::with_stack_for`), which refuses a
/// configuration too deep for any stack it provides.
/// `zone` is [`BackendDefinition::operation_depth`] of the initial configuration.
fn on_initial_stack<T>(
    zone: usize,
    work: impl FnOnce() -> Result<T, Box<dyn Error>>,
) -> Result<T, Box<dyn Error>> {
    nesting::with_stack(zone, work).map_err(|error| {
        format!("the initial configuration is too deep for the backend: {error}")
    })?
}

/// krun's route from an internalized definition and an assembled initial configuration to a run:
/// on the stack the backend measures for `initial`, prepare it ([`InitialTerm`]) and call `run`
/// with the definition and the prepared term. krun builds its [`Backend`] from the definition
/// inside `run` ([`Backend::from_internalized`]) and runs it there.
///
/// # Errors
///
/// When the configuration is too deep for any stack, is not executable, or does not
/// internalize; or `run`'s error.
pub fn with_initial_term<T>(
    definition: BackendDefinition,
    initial: &Pattern,
    run: impl FnOnce(BackendDefinition, InitialTerm) -> Result<T, Box<dyn Error>>,
) -> Result<T, Box<dyn Error>> {
    let zone = definition.operation_depth(&[initial]);
    on_initial_stack(zone, || {
        let term = prepare_initial(&definition, initial)?;
        run(definition, term)
    })
}

/// [`with_initial_term`] on a backend built once ([`KrunDefinition::backend`]) and reused for
/// every configuration: the same stack and the same preparation, against the backend's
/// definition of its main module, then `run` with the backend and the prepared term.
///
/// krun prepares the term before it builds its backend; the preparation reads only the
/// definition, so the term is the same.
///
/// # Errors
///
/// As [`with_initial_term`], and when the backend has no definition selected.
pub fn with_initial_term_on<T>(
    backend: &mut Backend,
    initial: &Pattern,
    run: impl FnOnce(&mut Backend, InitialTerm) -> Result<T, Box<dyn Error>>,
) -> Result<T, Box<dyn Error>> {
    let definition = backend.select_definition(None)?;
    let zone = definition.operation_depth(&[initial]);
    on_initial_stack(zone, || {
        let term = prepare_initial(&definition, initial)?;
        run(backend, term)
    })
}

/// The text `--io off` gives `$STDIN` (`docs/compatibility.md`, "Backend scope"): standard input
/// with its trailing newlines replaced by exactly one, also when it is empty (`#buffer("\n")`);
/// interior newlines and every other byte are kept.
/// With the console off nothing extends the `stdin` stream's buffer, so a parse rule reads a token
/// only when a delimiter already follows it there. The one newline ends the input's last line
/// whether or not standard input ended it, so its last token is read like every other where the
/// newline is a requested delimiter. The further trailing newlines are empty lines that hold no
/// token; kept, two of them would leave a buffer that begins with two delimiters after the last
/// token, which `stdinParseInt` reads as the undefined `String2Int("")` where the input has
/// simply ended.
#[must_use]
pub(crate) fn buffered_stdin_bytes(mut input: Vec<u8>) -> Vec<u8> {
    let trimmed = input
        .iter()
        .rposition(|byte| *byte != b'\n')
        .map_or(0, |index| index + 1);
    input.truncate(trimmed);
    input.push(b'\n');
    input
}

#[cfg(test)]
mod tests {
    use super::buffered_stdin_bytes;

    #[test]
    fn buffered_stdin_ends_in_exactly_one_newline() {
        assert_eq!(buffered_stdin_bytes(Vec::new()), b"\n");
        assert_eq!(buffered_stdin_bytes(b"ab".to_vec()), b"ab\n");
        assert_eq!(buffered_stdin_bytes(b"ab\n".to_vec()), b"ab\n");
        assert_eq!(buffered_stdin_bytes(b"ab\n\n\n".to_vec()), b"ab\n");
        assert_eq!(buffered_stdin_bytes(b"\n\n".to_vec()), b"\n");
        assert_eq!(
            buffered_stdin_bytes(b"a\r\n\nb\r\n".to_vec()),
            b"a\r\n\nb\r\n"
        );
        assert_eq!(buffered_stdin_bytes(vec![b'x', 0x80]), [b'x', 0x80, b'\n']);
    }
}
