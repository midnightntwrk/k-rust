use krs_ir::ProvenanceKey;
use proc_macro2::TokenStream;
use quote::ToTokens;

use crate::TokenRange;

/// Parser-owned semantic roles used by both anchor producers and reparsers.
///
/// The string mapping is a protocol seam: callers must use this catalog rather
/// than spelling roles themselves. Ordinals are zero-based occurrences in AST
/// order within one attribute or macro invocation.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[non_exhaustive]
pub enum ProvenanceRole {
    /// Exact string literal in an explicit stable-symbol override.
    StableSymbol,
    /// Name of an attributed sort trait.
    SortDeclaration,
    /// Direct super-sort path, in source order.
    SortParent,
    /// Name of an attributed explicit subsort implementation.
    SubsortDeclaration,
    /// Super-sort trait path in an explicit subsort implementation.
    SubsortSuperSort,
    /// Sub-sort self-type path in an explicit subsort implementation.
    SubsortSubSort,
    /// Required `sort` path in a constructor attribute.
    ConstructorSort,
    /// Optional `syntax` literal in a constructor attribute.
    ConstructorSyntax,
    /// Name of an attributed constructor struct.
    ConstructorDeclaration,
    /// Object-language sort path of a constructor record field, in field order.
    ConstructorFieldSort,
    /// Name of a constructor field, in declaration order.
    ConstructorFieldDeclaration,
    /// One ordered item in a checked constructor syntax template.
    ConstructorSyntaxItem,
    /// A named field placeholder in a constructor syntax template.
    ConstructorSyntaxFieldReference,
    /// Production-group reference in a constructor attribute.
    ConstructorGroup,
    /// Typed `avoid` flag in a constructor attribute.
    ConstructorAvoid,
    /// Structured format literal in a constructor attribute.
    ConstructorFormat,
    /// One fragment in a structured constructor format.
    ConstructorFormatFragment,
    /// One literal rustdoc line carried by a constructor production.
    ConstructorDocumentation,
    /// Name of a functional constructor declaration.
    FunctionDeclaration,
    /// Bare `total` marker on a function declaration.
    FunctionTotal,
    /// Bare `partial` marker on a function declaration.
    FunctionPartial,
    /// Closed backend-hook selector on a function declaration.
    FunctionHook,
    /// Static alias marker on a constructor production.
    AliasProduction,
    /// Restricted alias clause, anchored to its function identifier.
    AliasClause,
    /// Explicit equation-priority integer.
    EquationPriority,
    /// Bare ordered-fallback marker on a transition rule.
    RuleOwise,
    /// Simplification marker, anchored to the attributed function identifier.
    SimplificationMarker,
    /// Optional simplification-priority integer.
    SimplificationPriority,
    /// Name of an attributed token newtype.
    TokenDeclaration,
    /// Token regular-expression literal.
    TokenRegex,
    /// Optional token lexical-precedence value.
    TokenLexicalPrecedence,
    /// Syntax-only bracket declaration on a sort.
    BracketDeclaration,
    /// One ordered bracket-template item.
    BracketSyntaxItem,
    /// The same-sort `{value}` placeholder in a bracket template.
    BracketValueReference,
    /// Strictness or sequential-strictness declaration.
    StrictnessDeclaration,
    /// Optional named context-alias selected by strictness metadata.
    StrictnessContextAliasReference,
    /// Named strictness field reference in authored order.
    StrictnessFieldReference,
    /// Explicit result-predicate sort path on strictness metadata.
    StrictnessResultSort,
    /// Complete precedence macro declaration.
    PrecedenceDeclaration,
    /// One unrelated precedence chain.
    PrecedenceChain,
    /// One production-group reference in precedence source order.
    PrecedenceGroupReference,
    /// Complete group-associativity macro declaration.
    AssociativityDeclaration,
    /// One typed group-associativity sentence.
    AssociativitySentence,
    /// One production-group reference in associativity source order.
    AssociativityGroupReference,
    /// Named root literal in a configuration attribute.
    ConfigurationRoot,
    /// Name of an attributed configuration struct.
    ConfigurationDeclaration,
    /// The fixed computation-cell field name.
    ConfigurationField,
    /// `KCell` wrapper path in the computation-cell field type.
    ConfigurationCellWrapper,
    /// `KSequence` content path in the computation-cell field type.
    ConfigurationCellContent,
    /// One generic object-sort argument of a fixed leaf cell's content type.
    ConfigurationCellContentArgument,
    /// Explicit emitted name literal on a fixed cell field.
    ConfigurationCellName,
    /// Classified color literal on a fixed cell field.
    ConfigurationCellColor,
    /// Classified multiplicity literal on a fixed cell field.
    ConfigurationCellMultiplicity,
    /// Classified collection-type literal on a repeated cell field.
    ConfigurationCellType,
    /// Name of an attributed initializer associated function.
    InitializerDeclaration,
    /// Initializer return type.
    InitializerResultType,
    /// One configuration-variable parameter binding.
    ConfigurationVariable,
    /// External K variable name literal on a parameter.
    ConfigurationVariableName,
    /// Configuration-variable Rust type.
    ConfigurationVariableType,
    /// Optional `main` marker on a configuration variable.
    ConfigurationVariableMain,
    /// Complete declarative initializer body expression.
    InitializerBody,
    /// Required computation-cell initializer field.
    InitializerField,
    /// `KCell::new` constructor path.
    InitializerCellConstructor,
    /// Complete single-item `k!` payload.
    InitializerTerm,
    /// Named path in the initializer term, in preorder.
    InitializerTermPath,
    /// One node in the declarative initializer cell tree.
    InitializerCell,
    /// Rust struct path used to initialize a nested cell group.
    InitializerNestedConstructor,
    /// Complete `cells!` macro payload.
    CellsPayload,
    /// Selected cell field name in a `cells!` payload.
    CellsField,
    /// Cell wrapper path in a `cells!` entry.
    CellsWrapper,
    /// Configuration remainder/frame marker in a `cells!` payload.
    CellsRemainder,
    /// Complete `k!` K-sequence payload.
    KSequencePayload,
    /// One K-sequence item in source order.
    KSequenceItem,
    /// K-sequence tail or exact `.K` marker.
    KSequenceTail,
    /// Complete `map!` payload.
    MapPayload,
    /// One map-item key in source order.
    MapKey,
    /// One map-item value in source order.
    MapValue,
    /// Associative map-remainder marker.
    MapRemainder,
    /// Base map term of a functional update.
    MapUpdateBase,
    /// Complete `cells!` payload in a configuration-rule subject.
    RuleLeftCellsPayload,
    /// Selected cell field in a configuration-rule subject.
    RuleLeftCellsField,
    /// Cell wrapper path in a configuration-rule subject.
    RuleLeftCellsWrapper,
    /// Configuration frame in a configuration-rule subject.
    RuleLeftCellsRemainder,
    /// Complete K-sequence payload in a configuration-rule subject.
    RuleLeftKSequencePayload,
    /// One K item in a configuration-rule subject.
    RuleLeftKSequenceItem,
    /// K-sequence tail in a configuration-rule subject.
    RuleLeftKSequenceTail,
    /// Complete map payload in a configuration-rule subject.
    RuleLeftMapPayload,
    /// Map key in a configuration-rule subject.
    RuleLeftMapKey,
    /// Map value in a configuration-rule subject.
    RuleLeftMapValue,
    /// Map remainder in a configuration-rule subject.
    RuleLeftMapRemainder,
    /// Map-update base in a configuration-rule subject.
    RuleLeftMapUpdateBase,
    /// Complete `cells!` payload in a configuration-rule result.
    RuleRightCellsPayload,
    /// Selected cell field in a configuration-rule result.
    RuleRightCellsField,
    /// Cell wrapper path in a configuration-rule result.
    RuleRightCellsWrapper,
    /// Configuration frame in a configuration-rule result.
    RuleRightCellsRemainder,
    /// Complete K-sequence payload in a configuration-rule result.
    RuleRightKSequencePayload,
    /// One K item in a configuration-rule result.
    RuleRightKSequenceItem,
    /// K-sequence tail in a configuration-rule result.
    RuleRightKSequenceTail,
    /// Complete map payload in a configuration-rule result.
    RuleRightMapPayload,
    /// Map key in a configuration-rule result.
    RuleRightMapKey,
    /// Map value in a configuration-rule result.
    RuleRightMapValue,
    /// Map remainder in a configuration-rule result.
    RuleRightMapRemainder,
    /// Map-update base in a configuration-rule result.
    RuleRightMapUpdateBase,
    /// Rule function name.
    RuleDeclaration,
    /// Context-alias function name.
    ContextAliasDeclaration,
    /// Explicit shared context-alias name.
    ContextAliasName,
    /// Binding designated as `HERE` by a context alias.
    ContextAliasHere,
    /// Claim function name; the stable declaration anchor.
    ClaimDeclaration,
    /// Explicit claim-label string literal.
    ClaimLabel,
    /// `all_paths` or `one_path` claim modality token.
    ClaimModality,
    /// Optional claim circularity marker.
    ClaimCircularity,
    /// One universal claim binder declaration.
    ClaimUniversalBinder,
    /// One existential claim binder declaration.
    ClaimExistentialBinder,
    /// Exact claim binder name.
    ClaimBinderName,
    /// Exact claim binder sort.
    ClaimBinderSort,
    /// Complete object-language Boolean postcondition.
    ClaimEnsures,
    /// Named path in a postcondition, in preorder.
    ClaimEnsuresPath,
    /// Named application head in a postcondition.
    ClaimEnsuresApplicationHead,
    /// Bare reference in a postcondition.
    ClaimEnsuresReference,
    /// Literal in a postcondition.
    ClaimEnsuresLiteral,
    /// Named record field in a postcondition.
    ClaimEnsuresRecordFieldName,
    /// Concrete compiler-owned builtin Id literal.
    ClaimIdToken,
    /// Concrete compiler-owned builtin Bytes literal.
    ClaimBytesToken,
    /// Complete fresh anonymous occurrence.
    ClaimAnonymous,
    /// Sort path in an anonymous occurrence.
    ClaimAnonymousSort,
    /// Display spelling in an anonymous occurrence.
    ClaimAnonymousSpelling,
    /// Complete object-Bool disjunction macro.
    ClaimOrBool,
    /// Explicit emitted K rule-label literal.
    RuleLabel,
    /// Complete object-language Boolean condition in `#[k::requires(...)]`.
    RuleRequires,
    /// Named path in a rule condition, in preorder.
    RuleRequiresPath,
    /// Named application head in a rule condition, in preorder.
    RuleRequiresApplicationHead,
    /// Bare reference in a rule condition, in preorder.
    RuleRequiresReference,
    /// Integer or Boolean literal in a rule condition, in preorder.
    RuleRequiresLiteral,
    /// Named record field in a rule condition, in structural preorder.
    RuleRequiresRecordFieldName,
    /// Explicit `Term<Sort>` type of a configuration-rule binding parameter.
    RuleBindingType,
    /// Complete refutable subject pattern.
    RulePattern,
    /// Rule parameter type.
    RuleType,
    /// Rule return type.
    RuleResultType,
    /// Complete right-hand term expression.
    RuleResult,
    /// Named path in the rule subject, in preorder.
    RuleLeftPath,
    /// Named path in the rule result, in preorder.
    RuleRightPath,
    /// Complete standalone `term!` payload.
    TermPayload,
    /// Named path in a standalone term payload, in preorder.
    TermPath,
    /// Named application head in a standalone term, in preorder.
    TermApplicationHead,
    /// Bare reference in a standalone term, in preorder.
    TermReference,
    /// Integer or Boolean literal in a standalone term, in preorder.
    TermLiteral,
    /// Named record field in a standalone term, in structural preorder.
    TermRecordFieldName,
    /// Named application head in a rule subject, in preorder.
    RuleLeftApplicationHead,
    /// Bare reference in a rule subject, in preorder.
    RuleLeftReference,
    /// Integer or Boolean literal in a rule subject, in preorder.
    RuleLeftLiteral,
    /// Named record field in a rule subject, in structural preorder.
    RuleLeftRecordFieldName,
    /// Native Rust wildcard in a rule subject, in structural preorder.
    RuleLeftWildcard,
    /// Named application head in a rule result, in preorder.
    RuleRightApplicationHead,
    /// Bare reference in a rule result, in preorder.
    RuleRightReference,
    /// Integer or Boolean literal in a rule result, in preorder.
    RuleRightLiteral,
    /// Named record field in a rule result, in structural preorder.
    RuleRightRecordFieldName,
}

impl ProvenanceRole {
    /// Returns the stable role spelling stored in [`ProvenanceKey`].
    #[must_use]
    #[allow(clippy::too_many_lines)] // One exhaustive catalog makes protocol spelling drift impossible.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::StableSymbol => "stable_symbol",
            Self::SortDeclaration => "sort_declaration",
            Self::SortParent => "sort_parent",
            Self::SubsortDeclaration => "subsort_declaration",
            Self::SubsortSuperSort => "subsort_super_sort",
            Self::SubsortSubSort => "subsort_sub_sort",
            Self::ConstructorSort => "constructor_sort",
            Self::ConstructorSyntax => "constructor_syntax",
            Self::ConstructorDeclaration => "constructor_declaration",
            Self::ConstructorFieldSort => "constructor_field_sort",
            Self::ConstructorFieldDeclaration => "constructor_field_declaration",
            Self::ConstructorSyntaxItem => "constructor_syntax_item",
            Self::ConstructorSyntaxFieldReference => "constructor_syntax_field_reference",
            Self::ConstructorGroup => "constructor_group",
            Self::ConstructorAvoid => "constructor_avoid",
            Self::ConstructorFormat => "constructor_format",
            Self::ConstructorFormatFragment => "constructor_format_fragment",
            Self::ConstructorDocumentation => "constructor_documentation",
            Self::FunctionDeclaration => "function_declaration",
            Self::FunctionTotal => "function_total",
            Self::FunctionPartial => "function_partial",
            Self::FunctionHook => "function_hook",
            Self::AliasProduction => "alias_production",
            Self::AliasClause => "alias_clause",
            Self::EquationPriority => "equation_priority",
            Self::RuleOwise => "rule_owise",
            Self::SimplificationMarker => "simplification_marker",
            Self::SimplificationPriority => "simplification_priority",
            Self::TokenDeclaration => "token_declaration",
            Self::TokenRegex => "token_regex",
            Self::TokenLexicalPrecedence => "token_lexical_precedence",
            Self::BracketDeclaration => "bracket_declaration",
            Self::BracketSyntaxItem => "bracket_syntax_item",
            Self::BracketValueReference => "bracket_value_reference",
            Self::StrictnessDeclaration => "strictness_declaration",
            Self::StrictnessContextAliasReference => "strictness_context_alias_reference",
            Self::StrictnessFieldReference => "strictness_field_reference",
            Self::StrictnessResultSort => "strictness_result_sort",
            Self::PrecedenceDeclaration => "precedence_declaration",
            Self::PrecedenceChain => "precedence_chain",
            Self::PrecedenceGroupReference => "precedence_group_reference",
            Self::AssociativityDeclaration => "associativity_declaration",
            Self::AssociativitySentence => "associativity_sentence",
            Self::AssociativityGroupReference => "associativity_group_reference",
            Self::ConfigurationRoot => "configuration_root",
            Self::ConfigurationDeclaration => "configuration_declaration",
            Self::ConfigurationField => "configuration_field",
            Self::ConfigurationCellWrapper => "configuration_cell_wrapper",
            Self::ConfigurationCellContent => "configuration_cell_content",
            Self::ConfigurationCellContentArgument => "configuration_cell_content_argument",
            Self::ConfigurationCellName => "configuration_cell_name",
            Self::ConfigurationCellColor => "configuration_cell_color",
            Self::ConfigurationCellMultiplicity => "configuration_cell_multiplicity",
            Self::ConfigurationCellType => "configuration_cell_type",
            Self::InitializerDeclaration => "initializer_declaration",
            Self::InitializerResultType => "initializer_result_type",
            Self::ConfigurationVariable => "configuration_variable",
            Self::ConfigurationVariableName => "configuration_variable_name",
            Self::ConfigurationVariableType => "configuration_variable_type",
            Self::ConfigurationVariableMain => "configuration_variable_main",
            Self::InitializerBody => "initializer_body",
            Self::InitializerField => "initializer_field",
            Self::InitializerCellConstructor => "initializer_cell_constructor",
            Self::InitializerTerm => "initializer_term",
            Self::InitializerTermPath => "initializer_term_path",
            Self::InitializerCell => "initializer_cell",
            Self::InitializerNestedConstructor => "initializer_nested_constructor",
            Self::CellsPayload => "cells_payload",
            Self::CellsField => "cells_field",
            Self::CellsWrapper => "cells_wrapper",
            Self::CellsRemainder => "cells_remainder",
            Self::KSequencePayload => "k_sequence_payload",
            Self::KSequenceItem => "k_sequence_item",
            Self::KSequenceTail => "k_sequence_tail",
            Self::MapPayload => "map_payload",
            Self::MapKey => "map_key",
            Self::MapValue => "map_value",
            Self::MapRemainder => "map_remainder",
            Self::MapUpdateBase => "map_update_base",
            Self::RuleLeftCellsPayload => "rule_left_cells_payload",
            Self::RuleLeftCellsField => "rule_left_cells_field",
            Self::RuleLeftCellsWrapper => "rule_left_cells_wrapper",
            Self::RuleLeftCellsRemainder => "rule_left_cells_remainder",
            Self::RuleLeftKSequencePayload => "rule_left_k_sequence_payload",
            Self::RuleLeftKSequenceItem => "rule_left_k_sequence_item",
            Self::RuleLeftKSequenceTail => "rule_left_k_sequence_tail",
            Self::RuleLeftMapPayload => "rule_left_map_payload",
            Self::RuleLeftMapKey => "rule_left_map_key",
            Self::RuleLeftMapValue => "rule_left_map_value",
            Self::RuleLeftMapRemainder => "rule_left_map_remainder",
            Self::RuleLeftMapUpdateBase => "rule_left_map_update_base",
            Self::RuleRightCellsPayload => "rule_right_cells_payload",
            Self::RuleRightCellsField => "rule_right_cells_field",
            Self::RuleRightCellsWrapper => "rule_right_cells_wrapper",
            Self::RuleRightCellsRemainder => "rule_right_cells_remainder",
            Self::RuleRightKSequencePayload => "rule_right_k_sequence_payload",
            Self::RuleRightKSequenceItem => "rule_right_k_sequence_item",
            Self::RuleRightKSequenceTail => "rule_right_k_sequence_tail",
            Self::RuleRightMapPayload => "rule_right_map_payload",
            Self::RuleRightMapKey => "rule_right_map_key",
            Self::RuleRightMapValue => "rule_right_map_value",
            Self::RuleRightMapRemainder => "rule_right_map_remainder",
            Self::RuleRightMapUpdateBase => "rule_right_map_update_base",
            Self::RuleDeclaration => "rule_declaration",
            Self::ContextAliasDeclaration => "context_alias_declaration",
            Self::ContextAliasName => "context_alias_name",
            Self::ContextAliasHere => "context_alias_here",
            Self::ClaimDeclaration => "claim_declaration",
            Self::ClaimLabel => "claim_label",
            Self::ClaimModality => "claim_modality",
            Self::ClaimCircularity => "claim_circularity",
            Self::ClaimUniversalBinder => "claim_universal_binder",
            Self::ClaimExistentialBinder => "claim_existential_binder",
            Self::ClaimBinderName => "claim_binder_name",
            Self::ClaimBinderSort => "claim_binder_sort",
            Self::ClaimEnsures => "claim_ensures",
            Self::ClaimEnsuresPath => "claim_ensures_path",
            Self::ClaimEnsuresApplicationHead => "claim_ensures_application_head",
            Self::ClaimEnsuresReference => "claim_ensures_reference",
            Self::ClaimEnsuresLiteral => "claim_ensures_literal",
            Self::ClaimEnsuresRecordFieldName => "claim_ensures_record_field_name",
            Self::ClaimIdToken => "claim_id_token",
            Self::ClaimBytesToken => "claim_bytes_token",
            Self::ClaimAnonymous => "claim_anonymous",
            Self::ClaimAnonymousSort => "claim_anonymous_sort",
            Self::ClaimAnonymousSpelling => "claim_anonymous_spelling",
            Self::ClaimOrBool => "claim_or_bool",
            Self::RuleLabel => "rule_label",
            Self::RuleRequires => "rule_requires",
            Self::RuleRequiresPath => "rule_requires_path",
            Self::RuleRequiresApplicationHead => "rule_requires_application_head",
            Self::RuleRequiresReference => "rule_requires_reference",
            Self::RuleRequiresLiteral => "rule_requires_literal",
            Self::RuleRequiresRecordFieldName => "rule_requires_record_field_name",
            Self::RuleBindingType => "rule_binding_type",
            Self::RulePattern => "rule_pattern",
            Self::RuleType => "rule_type",
            Self::RuleResultType => "rule_result_type",
            Self::RuleResult => "rule_result",
            Self::RuleLeftPath => "rule_left_path",
            Self::RuleRightPath => "rule_right_path",
            Self::TermPayload => "term_payload",
            Self::TermPath => "term_path",
            Self::TermApplicationHead => "term_application_head",
            Self::TermReference => "term_reference",
            Self::TermLiteral => "term_literal",
            Self::TermRecordFieldName => "term_record_field_name",
            Self::RuleLeftApplicationHead => "rule_left_application_head",
            Self::RuleLeftReference => "rule_left_reference",
            Self::RuleLeftLiteral => "rule_left_literal",
            Self::RuleLeftRecordFieldName => "rule_left_record_field_name",
            Self::RuleLeftWildcard => "rule_left_wildcard",
            Self::RuleRightApplicationHead => "rule_right_application_head",
            Self::RuleRightReference => "rule_right_reference",
            Self::RuleRightLiteral => "rule_right_literal",
            Self::RuleRightRecordFieldName => "rule_right_record_field_name",
        }
    }

    /// Creates the canonical IR key for one occurrence.
    ///
    /// # Errors
    ///
    /// This catalog only contains nonempty roles, so an error indicates a
    /// violated internal contract in the IR key type.
    pub fn key(self, ordinal: u32) -> Result<ProvenanceKey, krs_ir::HostProvenanceError> {
        ProvenanceKey::new(self.as_str(), ordinal)
    }
}

impl ToTokens for ProvenanceRole {
    /// Emits the role spelling as a string literal, the role argument of
    /// `ProvenanceKey::new` in generated code.
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.as_str().to_tokens(tokens);
    }
}

/// One side of a configuration rule or claim.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum RuleSide {
    /// The subject.
    Left,
    /// The result.
    Right,
}

impl ProvenanceRole {
    /// The role that a `cells!`, `k!`, or `map!` node with the standalone
    /// role `self` takes on `side` of a configuration rule; `None` when
    /// `self` is not a standalone state-macro role.
    #[must_use]
    pub const fn on_rule_side(self, side: RuleSide) -> Option<Self> {
        Some(match (side, self) {
            (RuleSide::Left, Self::CellsPayload) => Self::RuleLeftCellsPayload,
            (RuleSide::Left, Self::CellsField) => Self::RuleLeftCellsField,
            (RuleSide::Left, Self::CellsWrapper) => Self::RuleLeftCellsWrapper,
            (RuleSide::Left, Self::CellsRemainder) => Self::RuleLeftCellsRemainder,
            (RuleSide::Left, Self::KSequencePayload) => Self::RuleLeftKSequencePayload,
            (RuleSide::Left, Self::KSequenceItem) => Self::RuleLeftKSequenceItem,
            (RuleSide::Left, Self::KSequenceTail) => Self::RuleLeftKSequenceTail,
            (RuleSide::Left, Self::MapPayload) => Self::RuleLeftMapPayload,
            (RuleSide::Left, Self::MapKey) => Self::RuleLeftMapKey,
            (RuleSide::Left, Self::MapValue) => Self::RuleLeftMapValue,
            (RuleSide::Left, Self::MapRemainder) => Self::RuleLeftMapRemainder,
            (RuleSide::Left, Self::MapUpdateBase) => Self::RuleLeftMapUpdateBase,
            (RuleSide::Right, Self::CellsPayload) => Self::RuleRightCellsPayload,
            (RuleSide::Right, Self::CellsField) => Self::RuleRightCellsField,
            (RuleSide::Right, Self::CellsWrapper) => Self::RuleRightCellsWrapper,
            (RuleSide::Right, Self::CellsRemainder) => Self::RuleRightCellsRemainder,
            (RuleSide::Right, Self::KSequencePayload) => Self::RuleRightKSequencePayload,
            (RuleSide::Right, Self::KSequenceItem) => Self::RuleRightKSequenceItem,
            (RuleSide::Right, Self::KSequenceTail) => Self::RuleRightKSequenceTail,
            (RuleSide::Right, Self::MapPayload) => Self::RuleRightMapPayload,
            (RuleSide::Right, Self::MapKey) => Self::RuleRightMapKey,
            (RuleSide::Right, Self::MapValue) => Self::RuleRightMapValue,
            (RuleSide::Right, Self::MapRemainder) => Self::RuleRightMapRemainder,
            (RuleSide::Right, Self::MapUpdateBase) => Self::RuleRightMapUpdateBase,
            _ => return None,
        })
    }
}

/// One canonical semantic key paired with its authored token endpoints.
#[derive(Clone, Debug)]
pub struct ProvenanceAnchor {
    role: ProvenanceRole,
    ordinal: u32,
    range: TokenRange,
}

impl ProvenanceAnchor {
    /// Creates an anchor from a parser-owned role, occurrence, and range.
    #[must_use]
    pub const fn new(role: ProvenanceRole, ordinal: u32, range: TokenRange) -> Self {
        Self {
            role,
            ordinal,
            range,
        }
    }

    /// Returns the parser-owned role.
    #[must_use]
    pub const fn role(&self) -> ProvenanceRole {
        self.role
    }

    /// Returns the zero-based role occurrence.
    #[must_use]
    pub const fn ordinal(&self) -> u32 {
        self.ordinal
    }

    /// Returns the exact token endpoints.
    #[must_use]
    pub const fn range(&self) -> TokenRange {
        self.range
    }

    /// Returns the IR key a producer and reparser must use for this node.
    ///
    /// # Errors
    ///
    /// This catalog only contains nonempty roles, so an error indicates a
    /// violated internal contract in the IR key type.
    pub fn key(&self) -> Result<ProvenanceKey, krs_ir::HostProvenanceError> {
        self.role.key(self.ordinal)
    }
}
