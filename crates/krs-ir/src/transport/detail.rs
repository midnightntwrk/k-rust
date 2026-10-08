//! Closed details for transport validation errors.

use crate::detail_macros::details;

details! {
    /// A transport field identified by local validation.
    TransportField {
        RustFieldIdentity => "Rust field identity",
        AssociativityGroups => "associativity groups",
        AssociativitySentences => "associativity sentences",
        CellColor => "cell color",
        CellContentSort => "cell content sort",
        CellDeclaration => "cell declaration",
        CellIdentityOwner => "cell identity owner",
        CellSortArgumentDiagnosticPath => "cell sort argument diagnostic path",
        ConfigurationDescriptor => "configuration descriptor",
        ConfigurationRootName => "configuration root name",
        ConfigurationRuleDescriptor => "configuration rule descriptor",
        ConfigurationRuleType => "configuration rule type",
        ConfigurationVariableBindings => "configuration variable bindings",
        ContextAliasDescriptor => "context alias descriptor",
        ContextAliasNameHere => "context alias name/here",
        ContextAliasBindings => "context-alias bindings",
        EmittedCellName => "emitted cell name",
        EmittedSiblingCellNames => "emitted sibling cell names",
        ExternalConfigurationVariableName => "external configuration variable name",
        ExternalConfigurationVariableNames => "external configuration variable names",
        FixedCellFields => "fixed cell fields",
        FormatFragments => "format fragments",
        HeadAnchoredRuleDescriptor => "head-anchored rule descriptor",
        HeadRuleBindings => "head-rule bindings",
        HeadRuleConfiguration => "head-rule configuration",
        HeadRuleExtraCells => "head-rule extra cells",
        HeadRuleSelectedCells => "head-rule selected cells",
        InitializerCellFields => "initializer cell fields",
        NestedCellDeclaration => "nested cell declaration",
        NestedCellDiagnosticPath => "nested cell diagnostic path",
        NestedInitializerChildren => "nested initializer children",
        PrecedenceChains => "precedence chains",
        PrecedenceGroups => "precedence groups",
        ProductionAttributeFamilies => "production attribute families",
        ProductionItems => "production items",
        ProductionRegex => "production regex",
        RuleApplicationRecordFields => "rule application record fields",
        RuleBindingSort => "rule binding sort",
        RuleBindings => "rule bindings",
        RuleLabel => "rule label",
        SelectedRuleCells => "selected rule cells",
        StrictnessFields => "strictness fields",
        Terminal => "terminal",
        FixedConfigurationDescriptor => "fixed configuration descriptor",
        NestedCellDescriptor => "nested cell descriptor",
        RequiredGrammarPrimaryProvenanceKey => "required grammar primary provenance key",
        Color => "production color",
        Colors => "production colors",
    }
}

details! {
    /// An expected stable namespace for a transport reference.
    TransportItemKind {
        Cell => "Cell",
        Claim => "Claim",
        Configuration => "Configuration",
        ConfigurationOrCell => "Configuration or Cell",
        ContextAlias => "ContextAlias",
        Equation => "Equation",
        Rule => "Rule",
        Sort => "Sort",
        SortOrBuiltin => "Sort or builtin",
        SentenceMatchingRelationalItem => "sentence-matching relational item",
    }
}

details! {
    /// A state cell content validation failure.
    StateCellContentReason {
        DotKMissingProvenance => ".K is missing exact provenance",
        KCellSortMismatch => "KCell content sort must be builtin KSequence",
        EmptyMapPayloadProvenanceMismatch => "empty map payload provenance disagrees with notation",
        EmptyMapProvenanceMismatch => "empty map provenance disagrees with notation",
        InvalidKSequenceShell => "invalid K-sequence shell",
        InvalidExactKSequenceShell => "invalid exact K-sequence shell",
        InvalidVariableSort => "invalid variable sort",
        EmptyMapItemPayload => "map item form requires a nonempty payload",
        MapItemContentOrPayloadProvenance => "map items require content or a frame and payload provenance",
        MapUpdateRequiresPayloadProvenance => "map update requires payload provenance",
        MapUpdateSideOrPayloadProvenance => "map updates are result-only and require payload provenance",
        ProvenanceOrdinalExceedsU32 => "provenance ordinal exceeds u32",
        RuleSubjectAndResultConfigurationsDiffer => "rule subject and result configurations differ",
        RuleWrapperAndStateFamilyDisagree => "rule wrapper and state family disagree",
        InvalidStandaloneDotKShell => "standalone .K has an invalid shell",
        InvalidStandaloneDotKPayload => "standalone .K must be empty and have payload provenance",
        WrapperAndInitializerStateFamilyDisagree => "wrapper and initializer state family disagree",
        MissingConfigurationHostOwner => "fixed configuration lacks a nominal host owner",
        MissingNestedCellHostOwner => "nested cell declaration lacks a nominal host owner",
    }
}

details! {
    /// A state term validation failure.
    StateTermReason {
        OneSidedAliasReusesResultFrame => "a one-sided context alias cannot reuse a result frame",
        UnexpectedAnonymousOccurrence => "anonymous occurrences are claim-subject-only",
        InvalidApplicationPathOrHeadClass => "application path keys or head class are invalid",
        BindingCatalogOrder => "binding catalog is not subject first-occurrence preorder",
        CellTypeRequiresRepeatedMultiplicity => "cell type requires repeated multiplicity",
        CircularityRequiresAnAllPathClaim => "circularity requires an all-path claim",
        UnexpectedClaimMetadata => "claim metadata is valid only on claims",
        InitializerClaimTerm => "claim-only terms are not allowed in initializers",
        MissingClaimMetadataOrLabel => "claims require typed metadata and an explicit label",
        ConfigurationRuleOrderedFallbackPriority => "configuration-rule ordered fallback priority",
        RuleTermKeyMismatch => "configuration-rule term path and semantic keys disagree",
        AliasHereContentOccurrence => "context alias HERE binding must occur exactly once in cell content",
        AliasHereBindingCount => "context alias must select exactly one ordinary HERE binding",
        AliasFrameBindingMismatch => "context-alias frame binding has the wrong structural kind or occurrence",
        AliasProvenanceNotClosed => "context-alias provenance is not closed",
        AliasBindingCatalogMismatch => "context-alias structural binding catalog does not match its frames",
        DuplicateAliasBinding => "duplicate context-alias binding",
        DuplicateFragmentChildField => "fragment! child field occurs more than once",
        EmptyOrNonNominalFragment => "fragment! requires a nonempty nominal cell declaration",
        EmptyFragment => "fragment! requires at least one child field",
        InitializerFragment => "fragment! terms are not allowed in initializers",
        FrameFormIsInvalidOnThisRuleSide => "frame form is invalid on this rule side",
        UndeclaredHeadRuleExtraBinding => "head-rule extra references an undeclared binding",
        HeadRuleHeaderOwnership => "head-rule header ownership",
        HeadRuleOrderedFallbackPriority => "head-rule ordered fallback priority",
        InvalidNondetGroup => "nondet group outside a transition or with an invalid identifier",
        HeadRuleRequiresProvenanceKey => "head-rule requires provenance key",
        HeadRuleStructuralProvenanceKey => "head-rule structural provenance key",
        InitializerRecordFieldProvenance => "initializer syntax has no exact record-field provenance",
        NonCanonicalIntegerLiteral => "integer literal is not canonical unsigned decimal",
        InvalidAnonymousSort => "invalid anonymous sort",
        InvalidApplicationTarget => "invalid application target",
        InvalidCellSortArgument => "invalid cell sort argument",
        InvalidClaimBinderSort => "invalid claim binder sort",
        InvalidCompilerOwnedBuiltinToken => "invalid compiler-owned builtin token",
        InvalidClaimBinderCatalog => "invalid, duplicate, or uncatalogued claim binder",
        MapReadCellProvenanceKey => "map read cell provenance key",
        MapUpdateCellProvenanceKey => "map update cell provenance key",
        OrdinaryCellRewriteProvenanceKey => "ordinary cell rewrite provenance key",
        ResultFrameBindingKind => "result frame binding has the wrong structural kind",
        InvalidRuleApplicationKeysOrHeadClass => "rule application keys or head class are invalid",
        RuleProvenanceOrdinalExceedsU32 => "rule provenance ordinal exceeds u32",
        RuleVariableBindingIsNotATerm => "rule variable binding is not a term",
        ConfigurationSimplification => "simplifications cannot have configuration rewrite bodies",
        ConfigurationStaticAlias => "static aliases cannot have configuration rewrite bodies",
        SubjectFrameBindingKind => "subject frame binding has the wrong structural kind",
        TooManyClaimBinders => "too many claim binders",
        TooManyClaimNodes => "too many claim nodes",
        UnsupportedCellMultiplicity => "unsupported cell multiplicity",
        UnsupportedRepeatedCellCollection => "unsupported repeated-cell collection type",
        VariableKeyOrBindingMismatch => "variable keys disagree or the binding is undeclared",
        WildcardsAreAllowedOnlyInRuleSubjects => "wildcards are allowed only in rule subjects",
        WildcardsAreNotAllowedInInitializers => "wildcards are not allowed in initializers",
        AliasPrimaryProvenanceMismatch => "wrong context-alias primary provenance",
    }
}

details! {
    /// A grammar production validation failure.
    GrammarProductionReason {
        AliasFunctionMetadata => "alias metadata cannot be combined with function metadata",
        InternalProgramMetadata => "`internal` cannot be combined with `program`",
        BracketConstructorField => "bracket nonterminal cannot claim a constructor field",
        BracketFieldName => "bracket nonterminal field must be `value`",
        BracketOwnerResultSortMismatch => "bracket owner and result sorts must be identical",
        BracketOwnerShape => "bracket owner requires bracket metadata and one nonterminal",
        BracketSortMismatch => "bracket owner, result, and value sorts must be identical",
        BracketRegexItem => "bracket production cannot contain regex items",
        BracketConstructorTemplate => "bracket production cannot have a constructor-template key",
        BracketMetadataShape => "bracket production must contain only bracket metadata",
        DuplicateConstructorFieldOrdinal => "constructor field declaration ordinals must be unique",
        SparseConstructorFieldOrdinals => "constructor field declaration ordinals must form a dense permutation",
        ConstructorHasTokenOrBracketMetadata => "constructor has token or bracket metadata",
        MissingConstructorFieldKey => "constructor nonterminal lacks its field declaration key",
        ConstructorOwnerMetadata => "constructor owner cannot carry token or bracket metadata",
        ConstructorRegexItem => "constructor production cannot contain a regex item",
        FormatWithoutConstructorSyntax => "format metadata requires explicit constructor syntax",
        HookWithoutTotalFunction => "hook metadata requires a total function production",
        NominalTokenRegexGuards => "nominal token regex cannot carry precede/follow guards",
        ShortPrecedenceChain => "precedence chain requires at least two groups",
        ProvenanceOrdinalExceedsU32 => "provenance ordinal exceeds u32",
        TokenOrBracketOwnerKind => "token and bracket owners must be authored sorts",
        TokenOwnerShape => "token owner requires one regex item and token metadata",
        TokenSyntaxTemplate => "token production cannot have a syntax-template key",
        TokenRegexItemCount => "token production must contain exactly one regex item",
        TokenMetadataShape => "token production must contain only token metadata",
        TotalWithoutFunction => "total metadata requires function metadata",
    }
}

details! {
    /// A grammar application validation failure.
    GrammarApplicationReason {
        ListOperationHasInvalidArity => "List operation has invalid arity",
        ListOperationsAcceptPositionalArgumentsOnly => "List operations accept positional arguments only",
        MapOperationHasInvalidArity => "Map operation has invalid arity",
        MapOperationsAcceptPositionalArgumentsOnly => "Map operations accept positional arguments only",
        SetOperationHasInvalidArity => "Set operation has invalid arity",
        SetOperationsAcceptPositionalArgumentsOnly => "Set operations accept positional arguments only",
        UnappliedListOperation => "a List operation must be an applied term head",
        UnappliedMapOperation => "a Map operation must be an applied term head",
        UnappliedSetOperation => "a Set operation must be an applied term head",
        BareConstructorArguments => "a bare-reference constructor must have no arguments",
        DuplicateNamedField => "named field occurs more than once",
        StructuralMapApplication => "structural-only Map operation used as an application head",
    }
}

details! {
    /// A grammar term validation failure.
    GrammarTermReason {
        UnexpectedClaimTerm => "claim-only term used outside a whole-configuration claim",
        CompleteCellTermsRequireConfigurationRules => "complete cell terms require configuration rules",
        InvalidExplicitRuleLabel => "invalid explicit rule label",
        InvalidPriorityKind => "priority must be an equation priority or transition ordered fallback",
        InvalidNondetGroup => "nondet group outside a transition or with an invalid identifier",
        UnexpectedSimplificationMetadata => "simplification metadata is supported only on simplifications",
        MissingSimplificationMetadata => "simplification sentence lacks simplification metadata",
        StaticAliasRequires => "static alias clauses cannot carry requires conditions",
        WildcardsAreAllowedOnlyInRuleSubjects => "wildcards are allowed only in rule subjects",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{GrammarTransportError, ItemKind, StateTransportError};

    #[test]
    fn field_and_expected_namespace_displays_are_stable() {
        assert_eq!(
            StateTransportError::ItemKind {
                field: TransportField::CellIdentityOwner,
                expected: TransportItemKind::ConfigurationOrCell,
                actual: ItemKind::Sort,
            }
            .to_string(),
            "cell identity owner item kind mismatch: expected Configuration or Cell, found sort"
        );
        assert_eq!(
            GrammarTransportError::DuplicateValue(TransportField::RuleBindings).to_string(),
            "rule bindings contains a duplicate"
        );
    }

    #[test]
    fn state_reason_displays_are_stable() {
        assert_eq!(
            StateTransportError::InvalidCellContent(StateCellContentReason::KCellSortMismatch)
                .to_string(),
            "invalid cell content: KCell content sort must be builtin KSequence"
        );
        assert_eq!(
            StateTransportError::InvalidTerm(StateTermReason::InvalidAnonymousSort).to_string(),
            "invalid initializer term: invalid anonymous sort"
        );
    }

    #[test]
    fn grammar_reason_displays_are_stable() {
        assert_eq!(
            GrammarTransportError::InvalidProduction(
                GrammarProductionReason::SparseConstructorFieldOrdinals
            )
            .to_string(),
            "invalid production: constructor field declaration ordinals must form a dense permutation"
        );
        assert_eq!(
            GrammarTransportError::InvalidApplication(
                GrammarApplicationReason::DuplicateNamedField
            )
            .to_string(),
            "invalid application: named field occurs more than once"
        );
        assert_eq!(
            GrammarTransportError::InvalidTerm(GrammarTermReason::UnexpectedClaimTerm).to_string(),
            "invalid term: claim-only term used outside a whole-configuration claim"
        );
    }
}
