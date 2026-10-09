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
        LexicalEntries => "lexical entries",
        LexicalName => "lexical name",
        LayoutRegexes => "layout regexes",
        RawSentenceText => "raw K sentence text",
        SpecModuleName => "spec module name",
        SpecModuleImport => "spec module import",
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
        InvalidGroupCellEntry => "a nested cell entry is a binder, `_`, or fragment!",
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
        NonCanonicalIntegerLiteral => "integer literal is not a canonical signed decimal",
        InvalidAnonymousSort => "invalid anonymous sort",
        InvalidLexemeSort => "invalid lexeme sort",
        EmptyLexemeText => "lexeme text must not be empty",
        InitializerLexeme => "lexeme! terms are not allowed in initializers",
        InvalidSortTestSort => "invalid is! or project! sort",
        InitializerSortTest => "is! and project! terms are not allowed in initializers",
        InvalidApplicationTarget => "invalid application target",
        InvalidCellSortArgument => "invalid cell sort argument",
        InvalidClaimBinderSort => "invalid claim binder sort",
        InvalidCompilerOwnedBuiltinToken => "invalid compiler-owned builtin token",
        InvalidClaimBinderCatalog => "invalid, duplicate, or uncatalogued claim binder",
        InvalidRuleExistential => "existential binders and ensures conditions are allowed only on transitions and claims, with distinct names that do not shadow a subject binding",
        InvalidRuleFresh => "fresh binders are allowed only on transitions, with distinct names that do not shadow a subject binding or an existential",
        MapReadCellProvenanceKey => "map read cell provenance key",
        MapUpdateCellProvenanceKey => "map update cell provenance key",
        OrdinaryCellRewriteProvenanceKey => "ordinary cell rewrite provenance key",
        ResultFrameBindingKind => "result frame binding has the wrong structural kind",
        InvalidRuleApplicationKeysOrHeadClass => "rule application keys or head class are invalid",
        RuleProvenanceOrdinalExceedsU32 => "rule provenance ordinal exceeds u32",
        RuleVariableBindingIsNotATerm => "rule variable binding is not a term",
        ConfigurationSimplification => "simplifications cannot have configuration rewrite bodies",
        ConfigurationStaticAlias => "static alias and desugar clauses cannot have configuration rewrite bodies",
        SubjectFrameBindingKind => "subject frame binding has the wrong structural kind",
        TooManyClaimBinders => "too many claim binders",
        TooManyClaimNodes => "too many claim nodes",
        UnsupportedCellMultiplicity => "unsupported cell multiplicity",
        UnsupportedRepeatedCellCollection => "unsupported repeated-cell collection type",
        VariableKeyOrBindingMismatch => "variable keys disagree or the binding is undeclared",
        WildcardsAreAllowedOnlyInRuleSubjects => "wildcards are allowed only in rule subjects",
        WildcardsAreNotAllowedInInitializers => "wildcards are not allowed in initializers",
        AliasPrimaryProvenanceMismatch => "wrong context-alias primary provenance",
        TrustedClaimWithCircularity => "a trusted claim cannot also be a circularity",
        PatternAsOutsideLeftHandSide => "`name @ pattern` (#as) is allowed only in left-hand sides",
        InitializerPatternAs => "`name @ pattern` (#as) is not allowed in initializers",
        PatternOrOutsideLeftHandSide => "`A | B` or-patterns (#Or) are allowed only in left-hand sides",
        InitializerPatternOr => "`A | B` or-patterns (#Or) are not allowed in initializers",
        MatchesInPattern => "`k::matches!` (:=K) is a Bool test, allowed only in results and conditions",
        InitializerMatches => "`k::matches!` (:=K) is not allowed in initializers",
        LetInPattern => "a `let` block (#let) is a term, allowed only in results and conditions",
        InitializerLet => "a `let` block (#let) is not allowed in initializers",
        InitializerApplicationInstance => "a turbofish instance (`Choose::<Int> { .. }`) is not allowed in initializers",
        ClosureInPattern => "an `ml::exists` closure (#Exists) is a predicate, allowed only in conditions and predicate simplifications",
        InitializerClosure => "an `ml::exists` closure (#Exists) is not allowed in initializers",
        RewriteOutsideSingleBodyRule => "`k::rewrite!` (K's local =>) is allowed only in the subject of a single-body rule",
        NestedRewrite => "`k::rewrite!` cannot occur inside another rewrite",
        EmptyRewriteOutsideKSequence => "`()` (.K) is the right side of a `k::rewrite!` only as a whole K-sequence item",
        SingleBodyRuleWithoutRewrite => "a single-body rule has no result and must contain a `k::rewrite!`",
    }
}

details! {
    /// A grammar production validation failure.
    GrammarProductionReason {
        AliasFunctionMetadata => "alias and desugar metadata cannot be combined with function metadata",
        InternalProgramMetadata => "`internal` cannot be combined with `program`",
        PreferAvoidMetadata => "`prefer` cannot be combined with `avoid`",
        MemoWithoutFunction => "`memo` requires function metadata",
        FreshGeneratorWithoutFunction => "`fresh_generator` requires function metadata",
        SmtWithoutFunction => "`smtlib` and `smt_hook` require function metadata",
        InvalidSmtlibSymbol => "an `smtlib` symbol is an SMT-LIB simple symbol",
        InvalidSmtTemplate => "an `smt_hook` template is nonempty text and placeholders that name nonterminal fields",
        ListMetadata => "syntactic-list metadata belongs on a constructor production without function, token, bracket, alias, or desugar metadata",
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
        TokenOwnerShape => "token owner requires one regex or terminal item and token metadata",
        TokenSyntaxTemplate => "token production cannot have a syntax-template key",
        TokenRegexItemCount => "token production must contain exactly one regex or terminal item",
        TokenMetadataShape => "token production must contain only token metadata",
        TokenOutsideCarrier => "token productions travel only in a token carrier",
        TokenCarrierOwner => "every production of a token carrier must be a token production of one sort",
        TerminalTokenPrecedence => "`prec` applies only to regex token productions",
        TotalWithoutFunction => "total metadata requires function metadata",
        AliasDesugarMetadata => "a production is an alias or a desugar, not both",
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
        InvalidAnywhereRule => "anywhere marker outside a transition, or beside a priority or nondet group",
        InvalidRuleExistential => "existential binders and ensures conditions are allowed only on transitions and claims, with distinct non-empty binder names",
        InvalidRuleFresh => "fresh binders are allowed only on transitions that are not anywhere rules, with distinct non-empty binder names",
        UnexpectedSimplificationMetadata => "simplification metadata is supported only on simplifications",
        MissingSimplificationMetadata => "simplification sentence lacks simplification metadata",
        StaticAliasRequires => "static alias and desugar clauses cannot carry requires conditions",
        WildcardsAreAllowedOnlyInRuleSubjects => "wildcards are allowed only in rule subjects",
        EmptyLexemeText => "lexeme text must not be empty",
        InvalidMatchRestriction => "concrete, symbolic, and smt_lemma keys are allowed only on equations and simplifications, once each, with distinct non-empty binder names",
        InvalidUnboundVariables => "unbound_variables is allowed only on desugar clauses, listing distinct names the subject does not bind and the result uses, or `_` for the result's wildcards",
        PatternAsOutsideLeftHandSide => "`name @ pattern` (#as) is allowed only in left-hand sides",
        PatternOrOutsideLeftHandSide => "`A | B` or-patterns (#Or) are allowed only in left-hand sides",
        MatchesInPattern => "`k::matches!` (:=K) is a Bool test, allowed only in results and conditions",
        LetInPattern => "a `let` block (#let) is a term, allowed only in results and conditions",
        InvalidFunctionContext => "a function context is allowed only on an equation that declares every binder, framed by an anonymous configuration remainder, with distinct context binders",
        ClosureInPattern => "an `ml::exists` closure (#Exists) is a predicate, allowed only in conditions and predicate simplifications",
        InvalidPredicateRule => "a predicate rule (`ml::Predicate` subject and result) is allowed only on a simplification",
        RewriteOutsideSingleBodyRule => "`k::rewrite!` (K's local =>) is allowed only in the subject of a single-body rule",
        NestedRewrite => "`k::rewrite!` cannot occur inside another rewrite",
        EmptyRewriteOutsideKSequence => "`()` (.K) is the right side of a `k::rewrite!` only as a whole K-sequence item",
        SingleBodyRuleWithoutRewrite => "a single-body rule has no result and must contain a `k::rewrite!`",
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
