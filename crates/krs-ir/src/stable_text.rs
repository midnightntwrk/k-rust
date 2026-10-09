//! Frozen spellings used by generated identities and ordering keys.

use std::borrow::Cow;

use crate::{BuiltinSort, ItemKind, PackageId, SourceMapKey, StableItemId};

/// Supplies text whose spelling is part of a generated identity or order.
pub trait StableText {
    /// Returns the frozen spelling of this value.
    fn stable_text(&self) -> Cow<'static, str>;
}

impl StableText for ItemKind {
    fn stable_text(&self) -> Cow<'static, str> {
        Cow::Borrowed(match self {
            Self::Sort => "Sort",
            Self::Constructor => "Constructor",
            Self::Grammar => "Grammar",
            Self::Configuration => "Configuration",
            Self::Cell => "Cell",
            Self::Rule => "Rule",
            Self::Equation => "Equation",
            Self::Simplification => "Simplification",
            Self::Alias => "Alias",
            Self::ContextAlias => "ContextAlias",
            Self::Claim => "Claim",
            Self::Desugar => "Desugar",
        })
    }
}

impl StableText for BuiltinSort {
    fn stable_text(&self) -> Cow<'static, str> {
        Cow::Borrowed(self.spec().marker_name)
    }
}

impl StableText for PackageId {
    fn stable_text(&self) -> Cow<'static, str> {
        Cow::Owned(format!(
            "PackageId {{ k_namespace: {:?}, cargo_name: {:?}, cargo_version: {:?}, cargo_source: {:?} }}",
            self.k_namespace(),
            self.cargo_name(),
            self.cargo_version(),
            self.cargo_source()
        ))
    }
}

impl StableText for StableItemId {
    fn stable_text(&self) -> Cow<'static, str> {
        Cow::Owned(format!(
            "StableItemId {{ package: {}, module_path: {:?}, item_name: {:?}, item_kind: {}, disambiguator: {:?} }}",
            self.package().stable_text(),
            self.module_path(),
            self.item_name(),
            self.item_kind().stable_text(),
            self.disambiguator()
        ))
    }
}

impl StableText for SourceMapKey {
    fn stable_text(&self) -> Cow<'static, str> {
        Cow::Owned(format!("SourceMapKey({:?})", self.as_str()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ITEM_KINDS: [ItemKind; 12] = [
        ItemKind::Sort,
        ItemKind::Constructor,
        ItemKind::Grammar,
        ItemKind::Configuration,
        ItemKind::Cell,
        ItemKind::Rule,
        ItemKind::Equation,
        ItemKind::Simplification,
        ItemKind::Alias,
        ItemKind::ContextAlias,
        ItemKind::Claim,
        ItemKind::Desugar,
    ];

    /// Pins one spelling per variant; a new variant fails to compile here.
    fn frozen_item_kind(kind: ItemKind) -> &'static str {
        match kind {
            ItemKind::Sort => "Sort",
            ItemKind::Constructor => "Constructor",
            ItemKind::Grammar => "Grammar",
            ItemKind::Configuration => "Configuration",
            ItemKind::Cell => "Cell",
            ItemKind::Rule => "Rule",
            ItemKind::Equation => "Equation",
            ItemKind::Simplification => "Simplification",
            ItemKind::Alias => "Alias",
            ItemKind::ContextAlias => "ContextAlias",
            ItemKind::Claim => "Claim",
            ItemKind::Desugar => "Desugar",
        }
    }

    /// Pins one spelling per variant; a new variant fails to compile here.
    fn frozen_builtin_sort(sort: BuiltinSort) -> &'static str {
        match sort {
            BuiltinSort::KSequence => "KSequence",
            BuiltinSort::Int => "Int",
            BuiltinSort::Bool => "Bool",
            BuiltinSort::Map => "Map",
            BuiltinSort::Id => "Id",
            BuiltinSort::Bytes => "Bytes",
            BuiltinSort::String => "String",
            BuiltinSort::List => "List",
            BuiltinSort::Set => "Set",
            BuiltinSort::Endianness => "Endianness",
            BuiltinSort::Signedness => "Signedness",
            BuiltinSort::Float => "Float",
        }
    }

    #[test]
    fn item_kind_spellings_are_frozen() {
        for kind in ITEM_KINDS {
            assert_eq!(kind.stable_text(), frozen_item_kind(kind));
        }
    }

    #[test]
    fn builtin_sort_spellings_are_frozen() {
        for sort in BuiltinSort::ALL {
            assert_eq!(sort.stable_text(), frozen_builtin_sort(sort));
        }
    }

    #[test]
    fn closed_catalog_spelling_sets_are_frozen() {
        let item_kinds = ITEM_KINDS
            .iter()
            .map(StableText::stable_text)
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(
            item_kinds.into_iter().collect::<Vec<_>>(),
            [
                "Alias",
                "Cell",
                "Claim",
                "Configuration",
                "Constructor",
                "ContextAlias",
                "Desugar",
                "Equation",
                "Grammar",
                "Rule",
                "Simplification",
                "Sort",
            ]
        );
        let builtin_sorts = BuiltinSort::ALL
            .iter()
            .map(StableText::stable_text)
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(
            builtin_sorts.into_iter().collect::<Vec<_>>(),
            [
                "Bool",
                "Bytes",
                "Endianness",
                "Float",
                "Id",
                "Int",
                "KSequence",
                "List",
                "Map",
                "Set",
                "Signedness",
                "String",
            ]
        );
    }

    #[test]
    fn source_map_key_spelling_is_frozen() {
        assert_eq!(
            SourceMapKey::new("key\"suffix").unwrap().stable_text(),
            "SourceMapKey(\"key\\\"suffix\")"
        );
    }
}
