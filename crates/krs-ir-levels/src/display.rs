//! Author-facing spellings of Semantic and Definition IR identities.

use std::fmt;

use crate::{IrSortRef, LabelId, SymbolId, SymbolKind};

impl<D: fmt::Display> fmt::Display for IrSortRef<D> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Declared(id) => id.fmt(formatter),
            Self::Builtin(sort) => sort.fmt(formatter),
        }
    }
}

impl fmt::Display for SymbolId {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}

impl fmt::Display for LabelId {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}

impl fmt::Display for SymbolKind {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Sort => "sort",
            Self::Production => "production",
            Self::Cell => "cell",
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        DefinitionSortRef, DefinitionValidationError, SemanticSortRef, SemanticValidationError,
    };
    use krs_ir::{
        BuiltinSort, IrField, ItemKind, PackageId, ProductionAttributeFamily, SemanticIdentityKind,
        StableItemId,
    };

    #[test]
    fn sort_ref_display_text() {
        let package = PackageId::new("EXAMPLE", "example", "1.0.0", "workspace").unwrap();
        let item =
            StableItemId::new(package, ["math", "integer"], "Number", ItemKind::Sort, "").unwrap();
        assert_eq!(
            SemanticSortRef::Declared(item.clone()).to_string(),
            "EXAMPLE::math::integer::Number (sort)"
        );
        assert_eq!(
            SemanticSortRef::Builtin(BuiltinSort::Int).to_string(),
            "Int"
        );
        assert_eq!(
            DefinitionSortRef::Builtin(BuiltinSort::KSequence).to_string(),
            "K"
        );
        assert_eq!(
            DefinitionSortRef::Declared(SymbolId::new("NumberSymbol").unwrap()).to_string(),
            "NumberSymbol"
        );
    }

    #[test]
    fn validation_error_displays_are_stable() {
        assert_eq!(
            SemanticValidationError::DuplicateId {
                kind: SemanticIdentityKind::Cell,
                id: "same".to_owned(),
            }
            .to_string(),
            "duplicate cell ID same",
        );
        assert_eq!(
            DefinitionValidationError::AdapterSpecificValue(IrField::SymbolName).to_string(),
            "symbol name must be target-neutral and path-free",
        );
        assert_eq!(
            DefinitionValidationError::DuplicateProductionAttribute(
                ProductionAttributeFamily::Function
            )
            .to_string(),
            "production repeats function metadata",
        );
    }
}
