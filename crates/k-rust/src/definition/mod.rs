//! K definition syntax and KAST JSON interchange.

pub mod ast;
pub mod json;
pub mod ordering;
pub mod partial_order;
pub mod relations;
pub mod resolve;

pub use ast::{
    Associativity, Attributes, Definition, FlatImport, FlatModule, Location, ProductionItem,
    Sentence,
};
pub use ordering::{
    Error as OrderingError, compare_attributes, compare_sentences, compare_terms,
    sentence_equivalent, sort_sentences,
};
pub use partial_order::{Cycle as PartialOrderCycle, PartialOrder};
pub use relations::{
    Error as RelationError, OverloadOrder, ProductionId, compute_overloads, compute_subsorts,
};
pub use resolve::{Error as ResolveError, ImportRef, ModuleId, ResolvedDefinition, ResolvedModule};
