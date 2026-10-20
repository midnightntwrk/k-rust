//! Assembly of an instantiated program into a configuration exactly as krun does, and backend
//! construction on the route a [`CompiledDefinition`] names (ARCHITECTURE 2.3, 5.4; T-6, T-7).
//! Owner: FZ-02.
//!
//! krun's order is: the program (`program_file` at the start sort), then the `--config-var`
//! bindings in order, then `bind_stream_defaults(io = false, program_uses_stdin = false, …)`
//! with the standard input buffered as krun buffers it, then `finish`
//! (`crates/k-rust/src/main.rs:2508-2552` at `b322de1ab`). A campaign runs with `--io off` and
//! an empty standard input: a case reads nothing from the process, so its configuration is a
//! function of the program text and the bindings alone (ARCHITECTURE 5.1, 5.4).
//!
//! FZ-G15 is extracting krun's portable front half (program grammar, `ConfigurationAssembler`
//! with krun's binding order, stream defaults, backend construction) into a non-`cli` module of
//! the facade. Every piece of code it replaces is marked "FZ-G15" below; integration round 1
//! switches them.
//!
//! # Lifetimes (interface question 2)
//!
//! `ConfigurationAssembler<'g>` borrows the program grammar and the configuration-variable
//! sorts, and keeps its configuration-variable parsers, macro expander and sort injector across
//! configurations. A [`ProgramAssembly`] owns the grammar, so it cannot also hold an assembler
//! that borrows it. The two are therefore split:
//!
//! - [`ProgramAssembly`] owns the grammar, built once per campaign and definition;
//! - [`CaseAssembler`] borrows it and the definition, and keeps the assembler's caches across
//!   the cases it assembles. The engine creates one for the duration of a run.
//!
//! [`ProgramAssembly::assemble`] is the one-shot form (a fresh [`CaseAssembler`] per call), for
//! callers that assemble once, such as confirmation (ARCHITECTURE 7). Both give the same
//! configuration: the assembler's caches depend on the grammar alone.

use k_rust::{
    backend::{Backend, BackendOptions},
    kast::parser::parse_sort,
    kompile::{ConfigurationAssembler, ConfigurationError, ProgramGrammar},
    kore::ast::Pattern as KorePattern,
};

use crate::{
    error::CampaignError,
    holes::InstantiatedProgram,
    spec::{BackendRoute, CompiledDefinition, ProgramText},
};

/// Why an instantiated program did not assemble; the case is `rejected` (ARCHITECTURE 5.3).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct AssembleError {
    /// The parser's or assembler's message.
    pub(crate) message: String,
}

impl From<ConfigurationError> for AssembleError {
    fn from(error: ConfigurationError) -> Self {
        Self {
            message: error.to_string(),
        }
    }
}

/// The per-definition state of assembly: the resolved program grammar, built once per campaign
/// and definition and reused by every case (ARCHITECTURE 2.3). Confirmation builds a fresh one
/// (ARCHITECTURE 7).
pub(crate) struct ProgramAssembly {
    grammar: ProgramGrammar,
}

impl ProgramAssembly {
    /// Resolve the program grammar of `definition` (`ProgramGrammar::new` over its frontend
    /// definition).
    ///
    /// # Errors
    ///
    /// [`CampaignError::Definition`] when the grammar does not resolve.
    pub(crate) fn new(definition: &CompiledDefinition) -> Result<Self, CampaignError> {
        // FZ-G15: `KrunDefinition::program_grammar`.
        let grammar = ProgramGrammar::new(&definition.frontend_definition).map_err(|error| {
            CampaignError::Definition {
                message: format!("the program grammar does not resolve: {error}"),
            }
        })?;
        Ok(Self { grammar })
    }

    /// The resolved program grammar, which also parses surface patterns
    /// (`compile_search_pattern`'s parsing definition, as krun uses it).
    pub(crate) fn grammar(&self) -> &ProgramGrammar {
        &self.grammar
    }

    /// An assembler for `definition`, which must be the definition this assembly was built
    /// from. It keeps its parsers across the configurations it assembles, so one should serve
    /// every case of a run.
    pub(crate) fn assembler<'a>(&'a self, definition: &'a CompiledDefinition) -> CaseAssembler<'a> {
        CaseAssembler {
            // FZ-G15: `KrunDefinition::assembler(&self.grammar)`, or a constructor of
            // `KrunAssembler` from these four parts (workers/interfaces.md, FZ-02 notes).
            assembler: ConfigurationAssembler::new(
                &self.grammar,
                definition.main_module.as_str(),
                definition.syntax_module.as_str(),
                &definition.configuration_variables,
            ),
        }
    }

    /// Assemble `program` into the KORE initial configuration krun would build for it, with a
    /// fresh [`CaseAssembler`] ([`CaseAssembler::assemble`]). `definition` must be the
    /// definition this assembly was built from.
    ///
    /// # Errors
    ///
    /// [`AssembleError`] when the program or a binding does not parse or the configuration does
    /// not assemble.
    pub(crate) fn assemble(
        &self,
        definition: &CompiledDefinition,
        program: &InstantiatedProgram,
    ) -> Result<KorePattern, AssembleError> {
        self.assembler(definition).assemble(program)
    }
}

/// An assembler of one definition's configurations, reused across cases (see the module
/// documentation).
pub(crate) struct CaseAssembler<'a> {
    // FZ-G15: `KrunAssembler<'a>`.
    assembler: ConfigurationAssembler<'a>,
}

impl CaseAssembler<'_> {
    /// Assemble `program` into the KORE initial configuration krun would build for it: the
    /// `initGeneratedTopCell` application with `$PGM` first, then the configuration variables in
    /// binding order, then `$IO` bound to `off` and `$STDIN` to an empty standard input as krun
    /// buffers it (`"\n"`), unless bound. A KORE template is returned as substituted. The
    /// configuration is not yet validated by the backend.
    ///
    /// On an error the assembler is left empty, as after a success.
    ///
    /// # Errors
    ///
    /// [`AssembleError`] when the program or a binding does not parse or the configuration does
    /// not assemble.
    pub(crate) fn assemble(
        &mut self,
        program: &InstantiatedProgram,
    ) -> Result<KorePattern, AssembleError> {
        match program {
            InstantiatedProgram::Kore(pattern) => Ok(pattern.clone()),
            InstantiatedProgram::Source {
                program,
                config_vars,
            } => {
                let assembled = self.assemble_source(program.as_ref(), config_vars);
                if assembled.is_err() {
                    self.assembler.clear();
                }
                assembled
            }
        }
    }

    // FZ-G15: this body becomes `KrunAssembler::assemble(&KrunInputs { start_sort, program:
    // program.map(|p| ProgramText { text, file: name, from_standard_input: false }),
    // configuration_variables: &pairs, io: false }, || Ok(Vec::new()))`, with `pairs` the
    // bindings as a `Vec<(&str, &str)>`.
    fn assemble_source(
        &mut self,
        program: Option<&ProgramText>,
        config_vars: &[(String, String)],
    ) -> Result<KorePattern, AssembleError> {
        // krun parses and checks a supplied program whether or not the definition declares
        // `$PGM`. The program text is never standard input here, so `$STDIN` keeps its default.
        if let Some(program) = program {
            let start_sort = parse_sort(&program.start_sort).map_err(|error| AssembleError {
                message: format!("start sort `{}`: {error}", program.start_sort),
            })?;
            self.assembler
                .program_file(&start_sort, &program.text, &program.name)?;
        }
        for (name, text) in config_vars {
            self.assembler.bind(name, text)?;
        }
        self.assembler.bind_stream_defaults(false, false, || {
            Ok::<_, ConfigurationError>(buffered_stdin_bytes(Vec::new()))
        })?;
        Ok(self.assembler.finish()?)
    }
}

/// The `$STDIN` text krun gives a run with `--io off` from standard input `input`: its trailing
/// newlines replaced by exactly one, also when it is empty. A campaign's standard input is
/// empty, so `$STDIN` is `"\n"`, as `krun --io off < /dev/null` binds it.
///
/// FZ-G15: a copy of the private `buffered_stdin_bytes` of `crates/k-rust/src/main.rs` at
/// `b322de1ab`. `KrunAssembler::assemble` applies krun's own to what the reader returns, so the
/// copy goes with the switch and the reader returns the empty input.
fn buffered_stdin_bytes(mut input: Vec<u8>) -> Vec<u8> {
    let trimmed = input
        .iter()
        .rposition(|byte| *byte != b'\n')
        .map_or(0, |index| index + 1);
    input.truncate(trimmed);
    input.push(b'\n');
    input
}

/// A fresh backend over `definition` on the route it names (ARCHITECTURE 5.4, T-6):
/// `Backend::internalize_source_definition(&kore, main, &order)` then
/// `Backend::from_internalized` for [`BackendRoute::SourceExecution`], and
/// `Backend::from_definition` for [`BackendRoute::FromDefinition`]; `options` are the
/// backend's solver options.
///
/// # Errors
///
/// [`CampaignError::Definition`] when the backend cannot be built.
pub(crate) fn build_backend(
    definition: &CompiledDefinition,
    options: BackendOptions,
) -> Result<Backend, CampaignError> {
    let refused = |error: &dyn std::fmt::Display| CampaignError::Definition {
        message: format!(
            "the backend refuses definition `{}`: {error}",
            definition.main_module
        ),
    };
    match &definition.route {
        BackendRoute::SourceExecution {
            execution_rewrite_order,
        } => {
            // FZ-G15: `KrunDefinition::internalize`, krun's route (main.rs:2606-2610).
            let internalized = Backend::internalize_source_definition(
                &definition.kore,
                &definition.main_module,
                execution_rewrite_order,
            )
            .map_err(|error| refused(&error))?;
            Backend::from_internalized(internalized, options).map_err(|error| refused(&error))
        }
        BackendRoute::FromDefinition => Backend::from_definition(
            definition.kore.clone(),
            definition.main_module.as_str(),
            options,
        )
        .map_err(|error| refused(&error)),
    }
}

#[cfg(test)]
mod tests {
    use super::buffered_stdin_bytes;

    #[test]
    fn an_empty_standard_input_is_one_newline() {
        assert_eq!(buffered_stdin_bytes(Vec::new()), b"\n");
        assert_eq!(buffered_stdin_bytes(b"a\n\n".to_vec()), b"a\n");
    }
}
