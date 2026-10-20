//! Assembly of an instantiated program into a configuration exactly as krun does, and backend
//! construction on the route a [`CompiledDefinition`] names (ARCHITECTURE 2.3, 5.4; T-6, T-7).
//! Owner: FZ-02.
//!
//! Assembly is krun's own, through `k_rust::krun::KrunAssembler`: the program (at the start
//! sort), then the `--config-var` bindings in order, then the stream defaults, then `finish`.
//! A campaign runs with `--io off` and an empty standard input, which krun buffers to one
//! newline for `$STDIN`: a case reads nothing from the process, so its configuration is a
//! function of the program text and the bindings alone (ARCHITECTURE 5.1, 5.4). Execution
//! stays with the public `Backend::execute` (FZ-04, D20).
//!
//! # Lifetimes (interface question 2)
//!
//! `KrunAssembler<'g>` borrows the program grammar and the configuration-variable sorts, and
//! keeps its parsers, macro expander and sort injector across configurations. A
//! [`ProgramAssembly`] owns the grammar, so it cannot also hold an assembler that borrows it.
//! The two are therefore split:
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
    kast::{Sort as KastSort, parser::parse_sort},
    kompile::{ConfigurationError, ProgramGrammar},
    kore::ast::Pattern as KorePattern,
    krun::{KrunAssembler, KrunInputs, ProgramText as KrunProgramText},
};

use crate::{
    error::CampaignError,
    holes::InstantiatedProgram,
    spec::{BackendRoute, CompiledDefinition},
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
        // `KrunDefinition::program_grammar` is this call.
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
            assembler: KrunAssembler::new(
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
    assembler: KrunAssembler<'a>,
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
        let (program, config_vars) = match program {
            InstantiatedProgram::Kore(pattern) => return Ok(pattern.clone()),
            InstantiatedProgram::Source {
                program,
                config_vars,
            } => (program.as_ref(), config_vars),
        };
        let start_sort = program
            .map(|program| {
                parse_sort(&program.start_sort).map_err(|error| AssembleError {
                    message: format!("start sort `{}`: {error}", program.start_sort),
                })
            })
            .transpose()?;
        let pairs = config_vars
            .iter()
            .map(|(name, text)| (name.as_str(), text.as_str()))
            .collect::<Vec<_>>();
        // Without a program the start sort is never read.
        let no_start = KastSort::new("Pgm");
        let inputs = KrunInputs {
            start_sort: start_sort.as_ref().unwrap_or(&no_start),
            // krun parses and checks a supplied program whether or not the definition declares
            // `$PGM`. The text is never standard input here, so `$STDIN` keeps its default.
            program: program.map(|program| KrunProgramText {
                text: &program.text,
                file: &program.name,
                from_standard_input: false,
            }),
            configuration_variables: &pairs,
            io: false,
        };
        Ok(self
            .assembler
            .assemble(&inputs, || Ok::<_, ConfigurationError>(Vec::new()))?)
    }
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
            // krun's route: `KrunDefinition::internalize` is this call.
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
