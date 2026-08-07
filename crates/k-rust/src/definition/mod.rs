//! K definition syntax and KAST JSON interchange.

pub mod ast;
pub mod catalog;
pub mod checks;
pub mod configuration;
pub mod json;
pub mod ordering;
pub mod partial_order;
pub mod regex;
pub mod relations;
pub mod resolve;
pub mod rule_catalog;
pub mod sort_catalog;
pub mod synonyms;

pub use ast::{
    Associativity, Attributes, Definition, FlatImport, FlatModule, LOCATION_ATTRIBUTE, Location,
    ProductionItem, SOURCE_ATTRIBUTE, Sentence,
};
pub use catalog::{
    FreshGeneratorError, LabelHead, ProductionCatalog, ProductionId, ProductionSignature, SortHead,
};
pub use checks::{
    Error as CheckError, StructuralCheckBackend, StructuralCheckOptions, check_anonymous_variables,
    check_associativity, check_attribute_semantics, check_attributes, check_configuration_cells,
    check_definition, check_definition_with_options, check_duplicate_klabels,
    check_duplicate_labels, check_function_rule_attributes, check_functions, check_holes,
    check_k_terms, check_klabels, check_module, check_module_with_options, check_regexes,
    check_rewrites, check_rhs_variables, check_smt_lemmas, check_sort_top_uniqueness,
    check_streams, check_syntax_groups, check_tokens,
};
pub use configuration::{ConfigurationError, expand_configurations};
pub use ordering::{
    Error as OrderingError, compare_attributes, compare_sentences, compare_terms,
    sentence_equivalent, sort_sentences,
};
pub use partial_order::{Cycle as PartialOrderCycle, PartialOrder};
pub use regex::{
    CharClass as RegexCharClass, ParseError as RegexParseError, Regex, RegexBody,
    parse as parse_regex,
};
pub use relations::{
    AssociativityRelations, Error as RelationError, OverloadOrder, compute_associativities,
    compute_overloads, compute_priorities, compute_subsorts,
};
pub use resolve::{Error as ResolveError, ImportRef, ModuleId, ResolvedDefinition, ResolvedModule};
pub use rule_catalog::{ClaimId, ContextId, RuleCatalog, RuleId, match_rule_label};
pub use sort_catalog::SortCatalog;
pub use synonyms::apply_sort_synonyms;
