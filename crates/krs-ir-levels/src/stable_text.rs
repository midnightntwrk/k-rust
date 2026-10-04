//! Frozen spellings of Semantic and Definition IR sort references.

use std::borrow::Cow;

use krs_ir::StableText;

use crate::{DefinitionSortRef, SemanticSortRef, SymbolId};

impl StableText for SemanticSortRef {
    fn stable_text(&self) -> Cow<'static, str> {
        Cow::Owned(match self {
            Self::Declared(id) => format!("Declared({})", id.stable_text()),
            Self::Builtin(sort) => format!("Builtin({})", sort.stable_text()),
        })
    }
}

impl StableText for SymbolId {
    fn stable_text(&self) -> Cow<'static, str> {
        Cow::Owned(format!("SymbolId({:?})", self.as_str()))
    }
}

impl StableText for DefinitionSortRef {
    fn stable_text(&self) -> Cow<'static, str> {
        Cow::Owned(match self {
            Self::Declared(id) => format!("Declared({})", id.stable_text()),
            Self::Builtin(sort) => format!("Builtin({})", sort.stable_text()),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use krs_ir::{BuiltinSort, ItemKind, PackageId, StableItemId};

    #[test]
    fn sort_ref_spellings_are_frozen() {
        let id = StableItemId::new(
            PackageId::new("EXAMPLE", "example", "1.0.0", "workspace").unwrap(),
            ["syntax"],
            "Expr",
            ItemKind::Sort,
            "",
        )
        .unwrap();
        let declared = SemanticSortRef::Declared(id);
        assert_eq!(
            declared.stable_text(),
            "Declared(StableItemId { package: PackageId { k_namespace: \"EXAMPLE\", cargo_name: \"example\", cargo_version: \"1.0.0\", cargo_source: \"workspace\" }, module_path: [\"syntax\"], item_name: \"Expr\", item_kind: Sort, disambiguator: \"\" })"
        );
        assert_eq!(
            SemanticSortRef::Builtin(BuiltinSort::Int).stable_text(),
            "Builtin(Int)"
        );
        assert_eq!(
            DefinitionSortRef::Declared(SymbolId::new("sortExpr").unwrap()).stable_text(),
            "Declared(SymbolId(\"sortExpr\"))"
        );
        assert_eq!(
            DefinitionSortRef::Builtin(BuiltinSort::Bool).stable_text(),
            "Builtin(Bool)"
        );
    }
}
