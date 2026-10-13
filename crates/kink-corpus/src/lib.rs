//! Root-relative corpus sources and concrete program inputs.

pub mod admission;
pub mod cli;
pub mod input;
pub mod manifest;
pub mod resolver;
pub mod runner;
pub mod store;
pub mod summary;

pub use input::{InputError, ProgramSource, TestInputSpec, assemble_input};
pub use resolver::{CorpusSource, LoadError, LoadedSource, SourceFile, load_source};

pub use runner::{DefinitionOutcome, run_definition};
pub use store::{Store, StoreError};
