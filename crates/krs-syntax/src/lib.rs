//! Shared, span-preserving parsers for compiler-owned KRS syntax islands.
//!
//! This is an ordinary library rather than a procedural-macro crate. Both the
//! The macro facade and the collector's source-reparsing provenance pass use these
//! ASTs, validation rules, and [`ProvenanceRole`] values. Global Rust/K name
//! resolution and semantic IR construction deliberately live elsewhere.

mod attribute;
mod configuration;
mod enum_constructor;
mod error;
mod grammar;
mod initializer;
mod item;
mod provenance;
mod range;
mod rule;
mod sorts;
mod state_macro;
mod state_rule;
pub mod surface;
mod term;
pub mod trivia;

pub use attribute::{
    AliasAttribute, CellAttributePayload, ClaimAttribute, ClaimBinder, ClaimModality,
    ConfigurationAttribute, ConstructorAttribute, ConstructorsAttribute, ContextAliasAttribute,
    EquationAttribute, ExistsAttribute, FunctionAttribute, FunctionTotality, InitAttribute,
    PriorityAttribute, RuleAttribute, SimplificationAttribute, SortAttribute, SubsortAttribute,
    SymbolAttribute, VariantSyntaxAttribute, parse_alias_attribute, parse_alias_attribute_source,
    parse_cell_attribute, parse_cell_attribute_source, parse_claim_attribute,
    parse_claim_attribute_source, parse_configuration_attribute,
    parse_configuration_attribute_source, parse_constructor_attribute,
    parse_constructor_attribute_source, parse_constructors_attribute,
    parse_constructors_attribute_source, parse_context_alias_attribute,
    parse_context_alias_attribute_source, parse_equation_attribute,
    parse_equation_attribute_source, parse_exists_attribute, parse_exists_attribute_source,
    parse_function_attribute, parse_function_attribute_source, parse_init_attribute,
    parse_init_attribute_source, parse_priority_attribute, parse_priority_attribute_source,
    parse_rule_attribute, parse_rule_attribute_source, parse_simplification_attribute,
    parse_simplification_attribute_source, parse_sort_attribute, parse_sort_attribute_source,
    parse_subsort_attribute, parse_subsort_attribute_source, parse_symbol_attribute,
    parse_symbol_attribute_source, parse_variant_syntax_attribute,
    parse_variant_syntax_attribute_source,
};
pub use configuration::{
    ComputationCellField, ConfigurationCellContent, ConfigurationDeclaration,
    ConfigurationReferenceCandidate, FixedCellField, parse_configuration_declaration,
    parse_configuration_declaration_source,
};
pub use enum_constructor::{
    EnumConstructorDeclaration, EnumConstructorVariant, EnumPrecedenceGroup,
    parse_enum_constructor_declaration, parse_enum_constructor_declaration_source,
};
pub use error::{SyntaxError, SyntaxErrorKind};
pub use grammar::{
    AssociativityDeclaration, AssociativitySentence, BracketAttribute, GroupAssociativity,
    PrecedenceChain, PrecedenceDeclaration, PrecedenceEdge, StrictnessAttribute, StrictnessKind,
    StructuredFormat, StructuredFormatFragment, SubsortDeclaration, SyntaxTemplate,
    SyntaxTemplateItem, TokenAttribute, TokenDeclaration, parse_associativity_declaration,
    parse_associativity_declaration_source, parse_bracket_attribute,
    parse_bracket_attribute_source, parse_precedence_declaration,
    parse_precedence_declaration_source, parse_seqstrict_attribute,
    parse_seqstrict_attribute_source, parse_strict_attribute, parse_strict_attribute_source,
    parse_subsort_declaration, parse_subsort_declaration_source, parse_token_attribute,
    parse_token_attribute_source, parse_token_declaration, parse_token_declaration_source,
};
pub use initializer::{
    ComputationCellInitializer, ConfigurationVariable, ConfigurationVariableAttribute,
    FixedCellInitializer, InitializerCellContent, InitializerFunction,
    InitializerReferenceCandidate, parse_initializer_function, parse_initializer_function_source,
};
pub use item::{
    ConstructorDeclaration, ConstructorField, ProductionDocumentation, SortDeclaration,
    parse_constructor_declaration, parse_constructor_declaration_source, parse_sort_declaration,
    parse_sort_declaration_source,
};
pub use provenance::{ProvenanceAnchor, ProvenanceRole, RuleRole, RuleSide, role_tokens};
pub use range::TokenRange;
pub use rule::{
    RuleBlock, RuleClause, RuleCondition, RuleExtra, RuleHeadResult, RuleImport, RuleItem,
    RuleNarrowing, RuleParameter, RulePattern, RuleReferenceCandidate, RuleTermReferenceCandidate,
    TermSort, parse_rule_block, parse_rule_block_source, parse_rule_block_source_with_trivia,
    parse_rule_item, parse_rule_item_source,
};
pub use sorts::{
    SortsDeclaration, SortsEntry, SortsMembership, SortsSort, parse_sorts_declaration,
    parse_sorts_declaration_source,
};
pub use state_macro::{
    CellsEntry, CellsExpression, KSequence, KSequenceNotation, MapBody, MapExpression, MapItem,
    StateMacroContext, StateMacroRemainder, StateTerm, parse_cells_expression,
    parse_cells_expression_source, parse_cells_expression_source_with_trivia, parse_cells_pattern,
    parse_cells_pattern_source, parse_cells_pattern_source_with_trivia,
    parse_k_sequence_expression, parse_k_sequence_expression_source, parse_k_sequence_pattern,
    parse_k_sequence_pattern_source, parse_map_expression, parse_map_expression_source,
    parse_map_expression_source_with_trivia, parse_map_pattern, parse_map_pattern_source,
    parse_map_pattern_source_with_trivia, state_path_spelling,
};
pub use state_rule::{
    ClaimEnsures, ClaimSortCandidate, StateClaimItem, StateContextAliasItem, StateRuleBinding,
    StateRuleBindingKind, StateRuleItem, StateRuleReferenceCandidate, StateRuleReferenceKind,
    parse_state_claim_item, parse_state_claim_item_source, parse_state_context_alias_item,
    parse_state_context_alias_item_source, parse_state_rule_item, parse_state_rule_item_source,
};
pub use term::{
    CellTerm, TermApplication, TermArguments, TermExpression, TermLiteral, TermNamedArgument,
    TermNode, TermRootKind, TermSymbol, TermSymbolKind, TermTree, parse_term_expression,
    parse_term_expression_source,
};
pub use trivia::{
    BlockCommentTrivia, DocCommentStyle, LineCommentTrivia, SourceRange, Trivia, TriviaAttachment,
    TriviaKind, TriviaTable, WhitespaceTrivia, lex_gaps,
};
