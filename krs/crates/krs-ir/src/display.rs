//! Author-facing spellings of IR identities and closed catalogs.

use std::fmt;

use crate::{
    BuiltinOperation, BuiltinSort, ExplicitSymbol, HookOperation, ItemKind, ListOperation,
    MapOperation, ModuleId, PackageId, ProductionFieldId, ProductionGroupId, SemanticId,
    SetOperation, Sha256Digest, SourceMapKey, StableItemId, TermMapOperation,
};

impl fmt::Display for ItemKind {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Sort => "sort",
            Self::Constructor => "constructor",
            Self::Grammar => "grammar",
            Self::Configuration => "configuration",
            Self::Cell => "cell",
            Self::Rule => "rule",
            Self::Equation => "equation",
            Self::Simplification => "simplification",
            Self::Alias => "alias",
            Self::ContextAlias => "context alias",
            Self::Claim => "claim",
            Self::Desugar => "desugar",
            Self::Context => "context",
        })
    }
}

impl fmt::Display for StableItemId {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.package().k_namespace())?;
        for segment in self.module_path() {
            write!(formatter, "::{segment}")?;
        }
        write!(formatter, "::{} ({}", self.item_name(), self.item_kind())?;
        if !self.disambiguator().is_empty() {
            write!(formatter, " {}", self.disambiguator())?;
        }
        formatter.write_str(")")
    }
}

impl fmt::Display for PackageId {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.cargo_name())
    }
}

impl fmt::Display for BuiltinSort {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.k_name())
    }
}

macro_rules! display_inner {
    ($($type:ty),+ $(,)?) => {
        $(impl fmt::Display for $type {
            fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str(self.as_str())
            }
        })+
    };
}

display_inner!(
    ExplicitSymbol,
    Sha256Digest,
    SourceMapKey,
    ModuleId,
    SemanticId,
    ProductionGroupId,
    ProductionFieldId,
);

impl fmt::Display for BuiltinOperation {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.spec().description)
    }
}

impl fmt::Display for HookOperation {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.spec().k_hook)
    }
}

impl fmt::Display for MapOperation {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.spec().description)
    }
}

impl fmt::Display for TermMapOperation {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.spec().description)
    }
}

impl fmt::Display for ListOperation {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.spec().description)
    }
}

impl fmt::Display for SetOperation {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.spec().description)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn author_facing_id_and_sort_text() {
        let package = PackageId::new("EXAMPLE", "example", "1.0.0", "workspace").unwrap();
        let item =
            StableItemId::new(package, ["math", "integer"], "Number", ItemKind::Sort, "").unwrap();
        assert_eq!(item.to_string(), "EXAMPLE::math::integer::Number (sort)");
        let generated = StableItemId::new(
            item.package().clone(),
            ["math"],
            "Number",
            ItemKind::Constructor,
            "variant-0",
        )
        .unwrap();
        assert_eq!(
            generated.to_string(),
            "EXAMPLE::math::Number (constructor variant-0)"
        );
        assert_eq!(ItemKind::ContextAlias.to_string(), "context alias");
        assert_eq!(
            SourceMapKey::new("source.key").unwrap().to_string(),
            "source.key"
        );
    }
}
