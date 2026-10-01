//! Shared, span-preserving parsers for compiler-owned KRS syntax islands.
//!
//! This is an ordinary library rather than a procedural-macro crate.
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
pub mod keyword;
pub mod parse;
mod provenance;
mod range;
mod rule;
mod sorts;
mod state_macro;
mod state_rule;
pub mod surface;
mod term;
mod term_sort;
pub mod trivia;

pub use attribute::{
    AliasAttribute, CellAttributePayload, ClaimAttribute, ClaimBinder, ClaimModality,
    ConfigurationAttribute, ConstructorAttribute, ConstructorsAttribute, ContextAliasAttribute,
    EquationAttribute, ExistsAttribute, FunctionAttribute, FunctionTotality, InitAttribute,
    PriorityAttribute, RuleAttribute, SimplificationAttribute, SortAttribute, SubsortAttribute,
    SymbolAttribute, VariantSyntaxAttribute,
};
pub use configuration::{
    ComputationCellField, ConfigurationCellContent, ConfigurationDeclaration, FixedCellField,
};
pub use enum_constructor::{
    EnumConstructorDeclaration, EnumConstructorVariant, EnumPrecedenceGroup,
};
pub use error::{SyntaxError, SyntaxErrorKind};
pub use grammar::{
    AssociativityDeclaration, AssociativitySentence, BracketAttribute, GroupAssociativity,
    PrecedenceChain, PrecedenceDeclaration, PrecedenceEdge, StrictnessAttribute, StrictnessKind,
    StructuredFormat, StructuredFormatFragment, SubsortDeclaration, SyntaxTemplate,
    SyntaxTemplateItem, TokenAttribute, TokenDeclaration, parse_seqstrict_attribute,
    parse_strict_attribute,
};
pub use initializer::{
    ComputationCellInitializer, ConfigurationVariable, ConfigurationVariableAttribute,
    FixedCellInitializer, InitializerCellContent, InitializerFunction,
};
pub use item::{
    ConstructorDeclaration, ConstructorField, ProductionDocumentation, SortDeclaration,
};
pub use parse::{KrsSyntax, ReferenceCandidate};
pub use provenance::{ProvenanceAnchor, ProvenanceRole, RuleRole, RuleSide, role_tokens};
pub use range::TokenRange;
pub use rule::{
    RuleBlock, RuleClause, RuleClauseLayout, RuleCondition, RuleExtra, RuleHeadResult, RuleImport,
    RuleItem, RuleNarrowing, RuleParameter, RulePattern, parse_rule_block_source_with_trivia,
};
pub use sorts::{SortsDeclaration, SortsEntry, SortsMembership, SortsSort};
pub use state_macro::{
    CellsEntry, CellsExpression, KSequence, KSequenceNotation, MapBody, MapExpression, MapItem,
    StateMacroContext, StateMacroRemainder, StateTerm, parse_cells_expression,
    parse_cells_expression_source_with_trivia, parse_cells_pattern,
    parse_cells_pattern_source_with_trivia, parse_k_sequence_expression, parse_k_sequence_pattern,
    parse_map_expression, parse_map_expression_source_with_trivia, parse_map_pattern,
    parse_map_pattern_source_with_trivia,
};
pub use state_rule::{
    ClaimEnsures, ClaimSortCandidate, StateClaimItem, StateContextAliasItem, StateRuleBinding,
    StateRuleBindingKind, StateRuleItem, StateRuleReferenceKind, parse_state_context_alias_item,
};
pub use term::{
    CellTerm, TermApplication, TermArguments, TermExpression, TermLiteral, TermNamedArgument,
    TermNode, TermRootKind, TermSymbol, TermSymbolKind, TermTree,
};
pub use term_sort::TermSort;
pub use trivia::{
    BlockCommentTrivia, DocCommentStyle, LineCommentTrivia, SourceRange, Trivia, TriviaAttachment,
    TriviaKind, TriviaTable, WhitespaceTrivia, lex_gaps,
};
