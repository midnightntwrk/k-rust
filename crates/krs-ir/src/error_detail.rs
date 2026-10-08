//! Closed fields and reasons for target-neutral IR validation errors.

use crate::detail_macros::details;

details! {
    /// A required stable-identity component.
    IdentityComponent {
        CargoName => "cargo_name",
        CargoSource => "cargo_source",
        CargoVersion => "cargo_version",
        ItemName => "item_name",
        KNamespace => "k_namespace",
        ModulePath => "module_path",
    }
}

details! {
    /// A path-free IR identity namespace.
    IrIdentityKind {
        LabelId => "label_id",
        ModuleId => "module_id",
        ProductionFieldId => "production_field_id",
        ProductionGroupId => "production_group_id",
        SemanticId => "semantic_id",
        SourceMapKey => "source_map_key",
        SymbolId => "symbol_id",
    }
}

details! {
    /// A target-neutral IR field or collection named by local validation.
    IrField {
        CellColor => "cell color",
        CellName => "cell name",
        ConfigurationPatternCells => "configuration pattern cells",
        ConfigurationRewriteClauses => "configuration rewrite clauses",
        ConfigurationRoot => "configuration root",
        ConfigurationVariableName => "configuration variable name",
        ContextAliasIdentity => "context alias identity",
        ContextAliasNameHere => "context alias name/HERE",
        DuplicateExternalConfigurationVariable => "duplicate external configuration variable",
        FollowRegex => "follow regex",
        InitializerChildren => "initializer children",
        LabelName => "label name",
        MultipleMainConfigurationVariables => "multiple main configuration variables",
        NestedCellChildren => "nested cell children",
        PrecedeRegex => "precede regex",
        ProductionGroupName => "production group name",
        ProductionRegex => "production regex",
        ProductionTerminal => "production terminal",
        StrictnessContextAliasReference => "strictness context alias reference",
        SymbolName => "symbol name",
        TokenValue => "token value",
        TopLevelCells => "top-level cells",
    }
}

details! {
    /// A semantic identity namespace that must not contain duplicates.
    SemanticIdentityKind {
        Cell => "cell",
        Configuration => "configuration",
        Declaration => "declaration",
        Initializer => "initializer",
        Module => "module",
    }
}

details! {
    /// A production attribute family that must not occur twice.
    ProductionAttributeFamily {
        Alias => "alias",
        Avoid => "avoid",
        Bracket => "bracket",
        Format => "format",
        Function => "function",
        Group => "group",
        Hook => "hook",
        Strictness => "strictness",
        Token => "token",
        Total => "total",
        Internal => "internal",
        Program => "program",
        Color => "color",
        Prefer => "prefer",
    }
}

details! {
    /// A constructor signature required by a BN128 hook.
    Bn128PointSignature {
        G1 => "G1Point(Int, Int)",
        G2 => "G2Point(Int, Int, Int, Int)",
    }
}

impl Bn128PointSignature {
    /// Returns the required declared sort name.
    #[must_use]
    pub const fn sort_name(self) -> &'static str {
        match self {
            Self::G1 => "G1Point",
            Self::G2 => "G2Point",
        }
    }

    /// Returns the number of integer coordinates in the constructor.
    #[must_use]
    pub const fn arity(self) -> usize {
        match self {
            Self::G1 => 2,
            Self::G2 => 4,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{GrammarShapeError, IdentityError, IrIdentityError, StateShapeError};

    #[test]
    fn identity_detail_displays_are_stable() {
        assert_eq!(
            IdentityError::EmptyComponent(IdentityComponent::CargoName).to_string(),
            "identity component `cargo_name` is empty",
        );
        assert_eq!(
            IrIdentityError::Empty(IrIdentityKind::SourceMapKey).to_string(),
            "source_map_key must not be empty",
        );
    }

    #[test]
    fn field_and_namespace_displays_are_stable() {
        assert_eq!(
            StateShapeError::EmptyCollection(IrField::ConfigurationRewriteClauses).to_string(),
            "configuration rewrite clauses must not be empty",
        );
        assert_eq!(
            GrammarShapeError::EmptyText(IrField::ProductionRegex).to_string(),
            "production regex must not be empty",
        );
    }

    #[test]
    fn attribute_and_signature_displays_are_stable() {
        assert_eq!(Bn128PointSignature::G1.to_string(), "G1Point(Int, Int)");
        assert_eq!(
            Bn128PointSignature::G2.to_string(),
            "G2Point(Int, Int, Int, Int)"
        );
    }
}
