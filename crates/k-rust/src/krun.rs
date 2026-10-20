//! The portable front half of `krust krun`: from a compiled definition and a program's text to
//! the initial configuration krun runs, and to the backend krun runs it on.
//!
//! `krust krun` is this module plus what only a command line has: reading the program and the
//! standard input, loading a runnable artifact or compiling a source definition, phrasing errors
//! in terms of its arguments, and timing each phase. A library caller that assembles
//! configurations through [`KrunAssembler::assemble`] and builds its backend with
//! [`KrunDefinition::backend`] gets the configuration and the rewrite theory krun gets for the
//! same definition and inputs.
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
//!     // execute `initial` on `backend`
//! #   let _ = (&initial, &mut backend);
//! }
//! # Ok(())
//! # }
//! ```

use std::{collections::BTreeMap, error::Error, fmt};

use k_rust_backend::definition::BackendDefinition;

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

    /// An empty assembler for this definition's configurations, parsing with `grammar`, which
    /// must be [`Self::program_grammar`] of this definition.
    #[must_use]
    pub fn assembler<'g>(&self, grammar: &'g ProgramGrammar) -> KrunAssembler<'g>
    where
        'a: 'g,
    {
        KrunAssembler {
            assembler: ConfigurationAssembler::new(
                grammar,
                self.main_module,
                self.syntax_module,
                self.configuration_variables,
            ),
            variables: self.configuration_variables,
            program_from_standard_input: false,
        }
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
    pub configuration_variables: &'a [(String, String)],
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
/// Parsers are built on first use and kept, so one assembler serves every configuration of its
/// definition.
pub struct KrunAssembler<'g> {
    assembler: ConfigurationAssembler<'g>,
    variables: &'g BTreeMap<String, KastSort>,
    program_from_standard_input: bool,
}

impl KrunAssembler<'_> {
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
    /// or `off` after `io`, and `$STDIN` to [`buffered_stdin_bytes`] of what
    /// `read_standard_input` returns, or to the empty string when `io` is on or the program was
    /// read from standard input ([`ConfigurationAssembler::bind_stream_defaults`]).
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
    /// missing `$PGM`. On an error the assembler is left empty, as after a success.
    ///
    /// # Errors
    ///
    /// The first error of a step.
    pub fn assemble<E: From<ConfigurationError>>(
        &mut self,
        inputs: &KrunInputs<'_>,
        read_standard_input: impl FnOnce() -> Result<Vec<u8>, E>,
    ) -> Result<Pattern, E> {
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
        // A supplied program always binds `$PGM` (`Self::binds_program`).
        if let Some(program) = &inputs.program {
            self.program(inputs.start_sort, program)?;
        }
        for (name, text) in inputs.configuration_variables {
            self.bind(name, text)?;
        }
        self.bind_stream_defaults(inputs.io, read_standard_input)?;
        Ok(self.finish()?)
    }
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
pub fn buffered_stdin_bytes(mut input: Vec<u8>) -> Vec<u8> {
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
