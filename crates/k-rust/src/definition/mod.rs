//! K definition syntax and KAST JSON interchange.

pub mod ast;
pub mod catalog;
pub mod checks;
pub mod json;
pub mod ordering;
pub mod partial_order;
pub mod relations;
pub mod resolve;
pub mod rule_catalog;
pub mod sort_catalog;

pub use ast::{
    Associativity, Attributes, Definition, FlatImport, FlatModule, LOCATION_ATTRIBUTE, Location,
    ProductionItem, SOURCE_ATTRIBUTE, Sentence,
};
pub use catalog::{
    FreshGeneratorError, LabelHead, ProductionCatalog, ProductionId, ProductionSignature, SortHead,
};
pub use checks::{
    Error as CheckError, check_anonymous_variables, check_associativity, check_duplicate_labels,
    check_k_terms, check_module, check_rewrites, check_sort_top_uniqueness, check_syntax_groups,
    check_tokens,
};
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
pub use rule_catalog::{ClaimId, ContextId, RuleCatalog, RuleId, match_rule_label};
pub use sort_catalog::SortCatalog;
