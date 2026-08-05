//! K definition syntax and KAST JSON interchange.

pub mod ast;
pub mod json;
pub mod ordering;
pub mod resolve;

pub use ast::{
    Associativity, Attributes, Definition, FlatImport, FlatModule, Location, ProductionItem,
    Sentence,
};
pub use ordering::{
    Error as OrderingError, compare_attributes, compare_sentences, compare_terms,
    sentence_equivalent, sort_sentences,
};
pub use resolve::{Error as ResolveError, ImportRef, ModuleId, ResolvedDefinition, ResolvedModule};
