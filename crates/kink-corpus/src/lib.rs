//! Root-relative corpus sources and concrete program inputs.

pub mod admission;
pub mod input;
pub mod manifest;
pub mod resolver;

pub use input::{InputError, ProgramSource, TestInputSpec, assemble_input};
pub use resolver::{CorpusSource, LoadError, LoadedSource, SourceFile, load_source};
