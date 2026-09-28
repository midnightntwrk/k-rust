//! Parser-owned semantic roles used by anchors and reparsers.

use serde::{Deserialize, Deserializer, Serialize, Serializer};

macro_rules! provenance_roles {
    ($( $(#[$doc:meta])* $variant:ident => $spelling:literal, )*) => {
        /// Parser-owned semantic roles used by both anchor producers and reparsers.
        ///
        /// The string mapping is a protocol seam: callers must use this catalog rather
        /// than spelling roles themselves. Ordinals are zero-based occurrences in AST
        /// order within one attribute or macro invocation.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        #[non_exhaustive]
        pub enum ProvenanceRole {
            $( $(#[$doc])* $variant, )*
        }

        impl ProvenanceRole {
            /// All provenance roles in catalog declaration order.
            pub const ALL: &'static [Self] = &[$(Self::$variant,)*];

            /// Returns the stable role spelling stored in a provenance key.
            #[must_use]
            pub const fn as_str(self) -> &'static str {
                match self { $( Self::$variant => $spelling, )* }
            }

            /// Parses a stable role spelling.
            #[must_use]
            pub fn from_spelling(spelling: &str) -> Option<Self> {
                match spelling { $( $spelling => Some(Self::$variant), )* _ => None }
            }

            /// Returns the Rust variant identifier for generated collector code.
            #[must_use]
            pub const fn variant_ident(self) -> &'static str {
                match self { $( Self::$variant => stringify!($variant), )* }
            }
        }
    };
}

provenance_roles! {
    /// Exact string literal in an explicit stable-symbol override.
    StableSymbol => "stable_symbol",
    /// Name of an attributed sort trait.
    SortDeclaration => "sort_declaration",
    /// Direct super-sort path, in source order.
    SortParent => "sort_parent",
    /// Name of an attributed explicit subsort implementation.
    SubsortDeclaration => "subsort_declaration",
    /// Super-sort trait path in an explicit subsort implementation.
    SubsortSuperSort => "subsort_super_sort",
    /// Sub-sort self-type path in an explicit subsort implementation.
    SubsortSubSort => "subsort_sub_sort",
    /// Required `sort` path in a constructor attribute.
    ConstructorSort => "constructor_sort",
    /// Optional `syntax` literal in a constructor attribute.
    ConstructorSyntax => "constructor_syntax",
    /// Name of an attributed constructor struct.
    ConstructorDeclaration => "constructor_declaration",
    /// Object-language sort path of a constructor record field, in field order.
    ConstructorFieldSort => "constructor_field_sort",
    /// Name of a constructor field, in declaration order.
    ConstructorFieldDeclaration => "constructor_field_declaration",
    /// One ordered item in a checked constructor syntax template.
    ConstructorSyntaxItem => "constructor_syntax_item",
    /// A named field placeholder in a constructor syntax template.
    ConstructorSyntaxFieldReference => "constructor_syntax_field_reference",
    /// Production-group reference in a constructor attribute.
    ConstructorGroup => "constructor_group",
    /// Typed `avoid` flag in a constructor attribute.
    ConstructorAvoid => "constructor_avoid",
    /// Structured format literal in a constructor attribute.
    ConstructorFormat => "constructor_format",
    /// One fragment in a structured constructor format.
    ConstructorFormatFragment => "constructor_format_fragment",
    /// One literal rustdoc line carried by a constructor production.
    ConstructorDocumentation => "constructor_documentation",
    /// Name of a functional constructor declaration.
    FunctionDeclaration => "function_declaration",
    /// Bare `total` marker on a function declaration.
    FunctionTotal => "function_total",
    /// Bare `partial` marker on a function declaration.
    FunctionPartial => "function_partial",
    /// Closed backend-hook selector on a function declaration.
    FunctionHook => "function_hook",
    /// Static alias marker on a constructor production.
    AliasProduction => "alias_production",
    /// Restricted alias clause, anchored to its function identifier.
    AliasClause => "alias_clause",
    /// Explicit equation-priority integer.
    EquationPriority => "equation_priority",
    /// Bare ordered-fallback marker on a transition rule.
    RuleOwise => "rule_owise",
    /// Simplification marker, anchored to the attributed function identifier.
    SimplificationMarker => "simplification_marker",
    /// Optional simplification-priority integer.
    SimplificationPriority => "simplification_priority",
    /// Name of an attributed token newtype.
    TokenDeclaration => "token_declaration",
    /// Token regular-expression literal.
    TokenRegex => "token_regex",
    /// Optional token lexical-precedence value.
    TokenLexicalPrecedence => "token_lexical_precedence",
    /// Syntax-only bracket declaration on a sort.
    BracketDeclaration => "bracket_declaration",
    /// One ordered bracket-template item.
    BracketSyntaxItem => "bracket_syntax_item",
    /// The same-sort `{value}` placeholder in a bracket template.
    BracketValueReference => "bracket_value_reference",
    /// Strictness or sequential-strictness declaration.
    StrictnessDeclaration => "strictness_declaration",
    /// Optional named context-alias selected by strictness metadata.
    StrictnessContextAliasReference => "strictness_context_alias_reference",
    /// Named strictness field reference in authored order.
    StrictnessFieldReference => "strictness_field_reference",
    /// Explicit result-predicate sort path on strictness metadata.
    StrictnessResultSort => "strictness_result_sort",
    /// Complete precedence macro declaration.
    PrecedenceDeclaration => "precedence_declaration",
    /// One unrelated precedence chain.
    PrecedenceChain => "precedence_chain",
    /// One production-group reference in precedence source order.
    PrecedenceGroupReference => "precedence_group_reference",
    /// Complete group-associativity macro declaration.
    AssociativityDeclaration => "associativity_declaration",
    /// One typed group-associativity sentence.
    AssociativitySentence => "associativity_sentence",
    /// One production-group reference in associativity source order.
    AssociativityGroupReference => "associativity_group_reference",
    /// Named root literal in a configuration attribute.
    ConfigurationRoot => "configuration_root",
    /// Name of an attributed configuration struct.
    ConfigurationDeclaration => "configuration_declaration",
    /// The fixed computation-cell field name.
    ConfigurationField => "configuration_field",
    /// `KCell` wrapper path in the computation-cell field type.
    ConfigurationCellWrapper => "configuration_cell_wrapper",
    /// `KSequence` content path in the computation-cell field type.
    ConfigurationCellContent => "configuration_cell_content",
    /// One generic object-sort argument of a fixed leaf cell's content type.
    ConfigurationCellContentArgument => "configuration_cell_content_argument",
    /// Explicit emitted name literal on a fixed cell field.
    ConfigurationCellName => "configuration_cell_name",
    /// Classified color literal on a fixed cell field.
    ConfigurationCellColor => "configuration_cell_color",
    /// Classified multiplicity literal on a fixed cell field.
    ConfigurationCellMultiplicity => "configuration_cell_multiplicity",
    /// Classified collection-type literal on a repeated cell field.
    ConfigurationCellType => "configuration_cell_type",
    /// Name of an attributed initializer associated function.
    InitializerDeclaration => "initializer_declaration",
    /// Initializer return type.
    InitializerResultType => "initializer_result_type",
    /// One configuration-variable parameter binding.
    ConfigurationVariable => "configuration_variable",
    /// External K variable name literal on a parameter.
    ConfigurationVariableName => "configuration_variable_name",
    /// Configuration-variable Rust type.
    ConfigurationVariableType => "configuration_variable_type",
    /// Optional `main` marker on a configuration variable.
    ConfigurationVariableMain => "configuration_variable_main",
    /// Complete declarative initializer body expression.
    InitializerBody => "initializer_body",
    /// Required computation-cell initializer field.
    InitializerField => "initializer_field",
    /// `KCell::new` constructor path.
    InitializerCellConstructor => "initializer_cell_constructor",
    /// Complete single-item `k!` payload.
    InitializerTerm => "initializer_term",
    /// Named path in the initializer term, in preorder.
    InitializerTermPath => "initializer_term_path",
    /// One node in the declarative initializer cell tree.
    InitializerCell => "initializer_cell",
    /// Rust struct path used to initialize a nested cell group.
    InitializerNestedConstructor => "initializer_nested_constructor",
    /// Complete `cells!` macro payload.
    CellsPayload => "cells_payload",
    /// Selected cell field name in a `cells!` payload.
    CellsField => "cells_field",
    /// Cell wrapper path in a `cells!` entry.
    CellsWrapper => "cells_wrapper",
    /// Configuration remainder/frame marker in a `cells!` payload.
    CellsRemainder => "cells_remainder",
    /// Complete `k!` K-sequence payload.
    KSequencePayload => "k_sequence_payload",
    /// One K-sequence item in source order.
    KSequenceItem => "k_sequence_item",
    /// K-sequence tail or exact `.K` marker.
    KSequenceTail => "k_sequence_tail",
    /// Complete `map!` payload.
    MapPayload => "map_payload",
    /// One map-item key in source order.
    MapKey => "map_key",
    /// One map-item value in source order.
    MapValue => "map_value",
    /// Associative map-remainder marker.
    MapRemainder => "map_remainder",
    /// Base map term of a functional update.
    MapUpdateBase => "map_update_base",
    /// Complete `cells!` payload in a configuration-rule subject.
    RuleLeftCellsPayload => "rule_left_cells_payload",
    /// Selected cell field in a configuration-rule subject.
    RuleLeftCellsField => "rule_left_cells_field",
    /// Cell wrapper path in a configuration-rule subject.
    RuleLeftCellsWrapper => "rule_left_cells_wrapper",
    /// Configuration frame in a configuration-rule subject.
    RuleLeftCellsRemainder => "rule_left_cells_remainder",
    /// Complete K-sequence payload in a configuration-rule subject.
    RuleLeftKSequencePayload => "rule_left_k_sequence_payload",
    /// One K item in a configuration-rule subject.
    RuleLeftKSequenceItem => "rule_left_k_sequence_item",
    /// K-sequence tail in a configuration-rule subject.
    RuleLeftKSequenceTail => "rule_left_k_sequence_tail",
    /// Complete map payload in a configuration-rule subject.
    RuleLeftMapPayload => "rule_left_map_payload",
    /// Map key in a configuration-rule subject.
    RuleLeftMapKey => "rule_left_map_key",
    /// Map value in a configuration-rule subject.
    RuleLeftMapValue => "rule_left_map_value",
    /// Map remainder in a configuration-rule subject.
    RuleLeftMapRemainder => "rule_left_map_remainder",
    /// Map-update base in a configuration-rule subject.
    RuleLeftMapUpdateBase => "rule_left_map_update_base",
    /// Complete `cells!` payload in a configuration-rule result.
    RuleRightCellsPayload => "rule_right_cells_payload",
    /// Selected cell field in a configuration-rule result.
    RuleRightCellsField => "rule_right_cells_field",
    /// Cell wrapper path in a configuration-rule result.
    RuleRightCellsWrapper => "rule_right_cells_wrapper",
    /// Configuration frame in a configuration-rule result.
    RuleRightCellsRemainder => "rule_right_cells_remainder",
    /// Complete K-sequence payload in a configuration-rule result.
    RuleRightKSequencePayload => "rule_right_k_sequence_payload",
    /// One K item in a configuration-rule result.
    RuleRightKSequenceItem => "rule_right_k_sequence_item",
    /// K-sequence tail in a configuration-rule result.
    RuleRightKSequenceTail => "rule_right_k_sequence_tail",
    /// Complete map payload in a configuration-rule result.
    RuleRightMapPayload => "rule_right_map_payload",
    /// Map key in a configuration-rule result.
    RuleRightMapKey => "rule_right_map_key",
    /// Map value in a configuration-rule result.
    RuleRightMapValue => "rule_right_map_value",
    /// Map remainder in a configuration-rule result.
    RuleRightMapRemainder => "rule_right_map_remainder",
    /// Map-update base in a configuration-rule result.
    RuleRightMapUpdateBase => "rule_right_map_update_base",
    /// Rule function name.
    RuleDeclaration => "rule_declaration",
    /// Context-alias function name.
    ContextAliasDeclaration => "context_alias_declaration",
    /// Explicit shared context-alias name.
    ContextAliasName => "context_alias_name",
    /// Binding designated as `HERE` by a context alias.
    ContextAliasHere => "context_alias_here",
    /// Claim function name; the stable declaration anchor.
    ClaimDeclaration => "claim_declaration",
    /// Explicit claim-label string literal.
    ClaimLabel => "claim_label",
    /// `all_paths` or `one_path` claim modality token.
    ClaimModality => "claim_modality",
    /// Optional claim circularity marker.
    ClaimCircularity => "claim_circularity",
    /// One universal claim binder declaration.
    ClaimUniversalBinder => "claim_universal_binder",
    /// One existential claim binder declaration.
    ClaimExistentialBinder => "claim_existential_binder",
    /// Exact claim binder name.
    ClaimBinderName => "claim_binder_name",
    /// Exact claim binder sort.
    ClaimBinderSort => "claim_binder_sort",
    /// Complete object-language Boolean postcondition.
    ClaimEnsures => "claim_ensures",
    /// Named path in a postcondition, in preorder.
    ClaimEnsuresPath => "claim_ensures_path",
    /// Named application head in a postcondition.
    ClaimEnsuresApplicationHead => "claim_ensures_application_head",
    /// Bare reference in a postcondition.
    ClaimEnsuresReference => "claim_ensures_reference",
    /// Literal in a postcondition.
    ClaimEnsuresLiteral => "claim_ensures_literal",
    /// Named record field in a postcondition.
    ClaimEnsuresRecordFieldName => "claim_ensures_record_field_name",
    /// Concrete compiler-owned builtin Id literal.
    ClaimIdToken => "claim_id_token",
    /// Concrete compiler-owned builtin Bytes literal.
    ClaimBytesToken => "claim_bytes_token",
    /// Complete fresh anonymous occurrence.
    ClaimAnonymous => "claim_anonymous",
    /// Sort path in an anonymous occurrence.
    ClaimAnonymousSort => "claim_anonymous_sort",
    /// Display spelling in an anonymous occurrence.
    ClaimAnonymousSpelling => "claim_anonymous_spelling",
    /// Complete object-Bool disjunction macro.
    ClaimOrBool => "claim_or_bool",
    /// Explicit emitted K rule-label literal.
    RuleLabel => "rule_label",
    /// Complete object-language Boolean condition in `#[k::requires(...)]`.
    RuleRequires => "rule_requires",
    /// Named path in a rule condition, in preorder.
    RuleRequiresPath => "rule_requires_path",
    /// Named application head in a rule condition, in preorder.
    RuleRequiresApplicationHead => "rule_requires_application_head",
    /// Bare reference in a rule condition, in preorder.
    RuleRequiresReference => "rule_requires_reference",
    /// Integer or Boolean literal in a rule condition, in preorder.
    RuleRequiresLiteral => "rule_requires_literal",
    /// Named record field in a rule condition, in structural preorder.
    RuleRequiresRecordFieldName => "rule_requires_record_field_name",
    /// Explicit `Term<Sort>` type of a configuration-rule binding parameter.
    RuleBindingType => "rule_binding_type",
    /// Complete refutable subject pattern.
    RulePattern => "rule_pattern",
    /// Rule parameter type.
    RuleType => "rule_type",
    /// Rule return type.
    RuleResultType => "rule_result_type",
    /// Complete right-hand term expression.
    RuleResult => "rule_result",
    /// Named path in the rule subject, in preorder.
    RuleLeftPath => "rule_left_path",
    /// Named path in the rule result, in preorder.
    RuleRightPath => "rule_right_path",
    /// Complete standalone `term!` payload.
    TermPayload => "term_payload",
    /// Named path in a standalone term payload, in preorder.
    TermPath => "term_path",
    /// Named application head in a standalone term, in preorder.
    TermApplicationHead => "term_application_head",
    /// Bare reference in a standalone term, in preorder.
    TermReference => "term_reference",
    /// Integer or Boolean literal in a standalone term, in preorder.
    TermLiteral => "term_literal",
    /// Named record field in a standalone term, in structural preorder.
    TermRecordFieldName => "term_record_field_name",
    /// Named application head in a rule subject, in preorder.
    RuleLeftApplicationHead => "rule_left_application_head",
    /// Bare reference in a rule subject, in preorder.
    RuleLeftReference => "rule_left_reference",
    /// Integer or Boolean literal in a rule subject, in preorder.
    RuleLeftLiteral => "rule_left_literal",
    /// Named record field in a rule subject, in structural preorder.
    RuleLeftRecordFieldName => "rule_left_record_field_name",
    /// Native Rust wildcard in a rule subject, in structural preorder.
    RuleLeftWildcard => "rule_left_wildcard",
    /// Named application head in a rule result, in preorder.
    RuleRightApplicationHead => "rule_right_application_head",
    /// Bare reference in a rule result, in preorder.
    RuleRightReference => "rule_right_reference",
    /// Integer or Boolean literal in a rule result, in preorder.
    RuleRightLiteral => "rule_right_literal",
    /// Named record field in a rule result, in structural preorder.
    RuleRightRecordFieldName => "rule_right_record_field_name",
}

impl Serialize for ProvenanceRole {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(self.as_str())
    }
}

impl<'de> Deserialize<'de> for ProvenanceRole {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let spelling = String::deserialize(deserializer)?;
        Self::from_spelling(&spelling).ok_or_else(|| {
            serde::de::Error::custom(format!("unknown provenance role `{spelling}`"))
        })
    }
}

impl ProvenanceRole {
    /// Creates the canonical IR key for one occurrence.
    #[must_use]
    pub const fn key(self, ordinal: u32) -> crate::ProvenanceKey {
        crate::ProvenanceKey::new(self, ordinal)
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

/// A standalone state-macro role that can appear on either rule side.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RuleRole {
    /// The `CellsPayload` standalone role.
    CellsPayload,
    /// The `CellsField` standalone role.
    CellsField,
    /// The `CellsWrapper` standalone role.
    CellsWrapper,
    /// The `CellsRemainder` standalone role.
    CellsRemainder,
    /// The `KSequencePayload` standalone role.
    KSequencePayload,
    /// The `KSequenceItem` standalone role.
    KSequenceItem,
    /// The `KSequenceTail` standalone role.
    KSequenceTail,
    /// The `MapPayload` standalone role.
    MapPayload,
    /// The `MapKey` standalone role.
    MapKey,
    /// The `MapValue` standalone role.
    MapValue,
    /// The `MapRemainder` standalone role.
    MapRemainder,
    /// The `MapUpdateBase` standalone role.
    MapUpdateBase,
}

impl RuleRole {
    /// Recognizes state-macro roles; unrelated provenance roles are ignored.
    #[must_use]
    pub const fn from_standalone(role: ProvenanceRole) -> Option<Self> {
        match role {
            ProvenanceRole::CellsPayload => Some(Self::CellsPayload),
            ProvenanceRole::CellsField => Some(Self::CellsField),
            ProvenanceRole::CellsWrapper => Some(Self::CellsWrapper),
            ProvenanceRole::CellsRemainder => Some(Self::CellsRemainder),
            ProvenanceRole::KSequencePayload => Some(Self::KSequencePayload),
            ProvenanceRole::KSequenceItem => Some(Self::KSequenceItem),
            ProvenanceRole::KSequenceTail => Some(Self::KSequenceTail),
            ProvenanceRole::MapPayload => Some(Self::MapPayload),
            ProvenanceRole::MapKey => Some(Self::MapKey),
            ProvenanceRole::MapValue => Some(Self::MapValue),
            ProvenanceRole::MapRemainder => Some(Self::MapRemainder),
            ProvenanceRole::MapUpdateBase => Some(Self::MapUpdateBase),
            _ => None,
        }
    }

    /// Returns the rule-side role for a standalone state-macro role.
    #[must_use]
    pub const fn on_side(self, side: RuleSide) -> ProvenanceRole {
        match (side, self) {
            (RuleSide::Left, Self::CellsPayload) => ProvenanceRole::RuleLeftCellsPayload,
            (RuleSide::Left, Self::CellsField) => ProvenanceRole::RuleLeftCellsField,
            (RuleSide::Left, Self::CellsWrapper) => ProvenanceRole::RuleLeftCellsWrapper,
            (RuleSide::Left, Self::CellsRemainder) => ProvenanceRole::RuleLeftCellsRemainder,
            (RuleSide::Left, Self::KSequencePayload) => ProvenanceRole::RuleLeftKSequencePayload,
            (RuleSide::Left, Self::KSequenceItem) => ProvenanceRole::RuleLeftKSequenceItem,
            (RuleSide::Left, Self::KSequenceTail) => ProvenanceRole::RuleLeftKSequenceTail,
            (RuleSide::Left, Self::MapPayload) => ProvenanceRole::RuleLeftMapPayload,
            (RuleSide::Left, Self::MapKey) => ProvenanceRole::RuleLeftMapKey,
            (RuleSide::Left, Self::MapValue) => ProvenanceRole::RuleLeftMapValue,
            (RuleSide::Left, Self::MapRemainder) => ProvenanceRole::RuleLeftMapRemainder,
            (RuleSide::Left, Self::MapUpdateBase) => ProvenanceRole::RuleLeftMapUpdateBase,
            (RuleSide::Right, Self::CellsPayload) => ProvenanceRole::RuleRightCellsPayload,
            (RuleSide::Right, Self::CellsField) => ProvenanceRole::RuleRightCellsField,
            (RuleSide::Right, Self::CellsWrapper) => ProvenanceRole::RuleRightCellsWrapper,
            (RuleSide::Right, Self::CellsRemainder) => ProvenanceRole::RuleRightCellsRemainder,
            (RuleSide::Right, Self::KSequencePayload) => ProvenanceRole::RuleRightKSequencePayload,
            (RuleSide::Right, Self::KSequenceItem) => ProvenanceRole::RuleRightKSequenceItem,
            (RuleSide::Right, Self::KSequenceTail) => ProvenanceRole::RuleRightKSequenceTail,
            (RuleSide::Right, Self::MapPayload) => ProvenanceRole::RuleRightMapPayload,
            (RuleSide::Right, Self::MapKey) => ProvenanceRole::RuleRightMapKey,
            (RuleSide::Right, Self::MapValue) => ProvenanceRole::RuleRightMapValue,
            (RuleSide::Right, Self::MapRemainder) => ProvenanceRole::RuleRightMapRemainder,
            (RuleSide::Right, Self::MapUpdateBase) => ProvenanceRole::RuleRightMapUpdateBase,
        }
    }
}

impl std::fmt::Display for ProvenanceRole {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(self.as_str())
    }
}
