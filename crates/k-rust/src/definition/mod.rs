//! K definition syntax and KAST JSON interchange.

pub mod ast;
pub mod catalog;
pub mod json;
pub mod ordering;
pub mod partial_order;
pub mod relations;
pub mod resolve;

pub use ast::{
    Associativity, Attributes, Definition, FlatImport, FlatModule, Location, ProductionItem,
    Sentence,
};
pub use catalog::{LabelHead, ProductionCatalog, ProductionId, ProductionSignature, SortHead};
pub use ordering::{
    Error as OrderingError, compare_attributes, compare_sentences, compare_terms,
    sentence_equivalent, sort_sentences,
};
pub use partial_order::{Cycle as PartialOrderCycle, PartialOrder};
pub use relations::{
    AssociativityRelations, Error as RelationError, OverloadOrder, compute_associativities,
    compute_overloads, compute_priorities, compute_subsorts,
};
pub use resolve::{Error as ResolveError, ImportRef, ModuleId, ResolvedDefinition, ResolvedModule};
