//! Assembly of an instantiated program into a configuration exactly as krun does, and backend
//! construction on the route a [`CompiledDefinition`] names (ARCHITECTURE 2.3, 5.4; T-6, T-7).
//! Owner: FZ-02.
//!
//! This is a thin adapter: FZ-G15 is extracting krun's portable front half (program grammar,
//! `ConfigurationAssembler` with krun's binding order, stream defaults, backend construction)
//! into a non-`cli` module of the facade, and integration round 1 switches these bodies to it.
//! krun's order is: the program (`program_file` at the start sort), then the `--config-var`
//! bindings in order, then `bind_stream_defaults(io = false, program_uses_stdin = false, …)`,
//! then `finish` (`crates/k-rust/src/main.rs:2508-2552`).

use k_rust::{
    backend::{Backend, BackendOptions},
    kompile::ProgramGrammar,
    kore::ast::Pattern as KorePattern,
};

use crate::{error::CampaignError, holes::InstantiatedProgram, spec::CompiledDefinition};

/// Why an instantiated program did not assemble; the case is `rejected` (ARCHITECTURE 5.3).
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct AssembleError {
    /// The parser's or assembler's message.
    pub(crate) message: String,
}

/// The per-definition state of assembly: the resolved program grammar and the configuration
/// variable sorts, built once per campaign and definition and reused by every case
/// (ARCHITECTURE 2.3). Confirmation builds a fresh one (ARCHITECTURE 7).
pub(crate) struct ProgramAssembly {
    grammar: ProgramGrammar,
    main_module: String,
    syntax_module: String,
}

impl ProgramAssembly {
    /// Resolve the program grammar of `definition` (`ProgramGrammar::new` over its frontend
    /// definition).
    ///
    /// # Errors
    ///
    /// [`CampaignError::Definition`] when the grammar does not resolve.
    pub(crate) fn new(definition: &CompiledDefinition) -> Result<Self, CampaignError> {
        unimplemented!("FZ-02")
    }

    /// The resolved program grammar, which also parses surface patterns
    /// (`compile_search_pattern`'s parsing definition, as krun uses it).
    pub(crate) fn grammar(&self) -> &ProgramGrammar {
        &self.grammar
    }

    /// Assemble `program` into the KORE initial configuration krun would build for it: the
    /// `initGeneratedTopCell` application with `$PGM` first, then the configuration variables in
    /// binding order, `$IO` off and `$STDIN` empty unless bound. A KORE template is returned as
    /// substituted. The configuration is not yet validated by the backend.
    ///
    /// # Errors
    ///
    /// [`AssembleError`] when the program or a binding does not parse or the configuration does
    /// not assemble.
    pub(crate) fn assemble(
        &mut self,
        definition: &CompiledDefinition,
        program: &InstantiatedProgram,
    ) -> Result<KorePattern, AssembleError> {
        unimplemented!("FZ-02")
    }
}

/// A fresh backend over `definition` on the route it names (ARCHITECTURE 5.4, T-6):
/// `Backend::internalize_source_definition(&kore, main, &order)` then
/// `Backend::from_internalized` for [`crate::BackendRoute::SourceExecution`], and
/// `Backend::from_definition` for [`crate::BackendRoute::FromDefinition`]; `options` are the
/// backend's solver options.
///
/// # Errors
///
/// [`CampaignError::Definition`] when the backend cannot be built.
pub(crate) fn build_backend(
    definition: &CompiledDefinition,
    options: BackendOptions,
) -> Result<Backend, CampaignError> {
    unimplemented!("FZ-02")
}
