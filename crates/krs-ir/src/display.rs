//! Author-facing spellings of IR identities and closed catalogs.

use std::fmt;

use crate::{
    BuiltinOperation, BuiltinSort, DefinitionSortRef, ExplicitSymbol, HookOperation, ItemKind,
    LabelId, ListOperation, MapOperation, ModuleId, PackageId, ProductionFieldId,
    ProductionGroupId, SemanticId, SemanticSortRef, SetOperation, Sha256Digest, SourceMapKey,
    StableItemId, SymbolId, SymbolKind,
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
        })
    }
}

impl fmt::Display for StableItemId {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}", self.package().cargo_name())?;
        for segment in self.module_path() {
            write!(formatter, "::{segment}")?;
        }
        write!(formatter, "::{}", self.item_name())?;
        if !self.disambiguator().is_empty() {
            write!(formatter, " [{}]", self.disambiguator())?;
        }
        Ok(())
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

impl fmt::Display for SemanticSortRef {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Declared(id) => id.fmt(formatter),
            Self::Builtin(sort) => sort.fmt(formatter),
        }
    }
}

impl fmt::Display for DefinitionSortRef {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Declared(id) => id.fmt(formatter),
            Self::Builtin(sort) => sort.fmt(formatter),
        }
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
    SymbolId,
    LabelId,
    ProductionGroupId,
    ProductionFieldId,
);

impl fmt::Display for SymbolKind {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Sort => "sort",
            Self::Production => "production",
            Self::Cell => "cell",
        })
    }
}

impl fmt::Display for BuiltinOperation {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::IntAdd => "integer addition",
            Self::IntSub => "integer subtraction",
            Self::IntMul => "integer multiplication",
            Self::IntTDiv => "integer truncating division",
            Self::IntMod => "integer modulus",
            Self::IntPowMod => "integer modular exponentiation",
            Self::IntLog2 => "integer base-two logarithm",
            Self::IntShiftRight => "integer right shift",
            Self::IntShiftLeft => "integer left shift",
            Self::IntBitAnd => "integer bitwise conjunction",
            Self::IntBitXor => "integer bitwise exclusive disjunction",
            Self::IntBitOr => "integer bitwise inclusive disjunction",
            Self::IntGreaterEqual => "integer greater-than-or-equal comparison",
            Self::IntGreater => "integer greater-than comparison",
            Self::IntLessEqual => "integer less-than-or-equal comparison",
            Self::IntLess => "integer less-than comparison",
            Self::IntEqual => "integer equality",
            Self::IntNotEqual => "integer inequality",
            Self::BoolNot => "Boolean negation",
            Self::BoolEqual => "Boolean equality",
            Self::BoolNotEqual => "Boolean inequality",
            Self::BoolAnd => "Boolean conjunction",
            Self::BoolOr => "Boolean disjunction",
            Self::BytesLength => "byte-string length",
            Self::BytesGet => "byte lookup",
            Self::BytesEmpty => "empty byte string",
            Self::BytesUpdate => "byte update",
            Self::BytesPadRight => "byte-string right padding",
            Self::BytesSubstring => "byte substring",
        })
    }
}

impl fmt::Display for HookOperation {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::KryptoKeccak256Raw => "KRYPTO.keccak256raw",
            Self::KryptoSha256Raw => "KRYPTO.sha256raw",
            Self::KryptoRipemd160Raw => "KRYPTO.ripemd160raw",
            Self::KryptoEcdsaRecover => "KRYPTO.ecdsaRecover",
            Self::KryptoBn128Valid => "KRYPTO.bn128valid",
            Self::KryptoBn128Add => "KRYPTO.bn128add",
            Self::KryptoBn128Mul => "KRYPTO.bn128mul",
            Self::KryptoBn128G2Valid => "KRYPTO.bn128g2valid",
            Self::KryptoBn128Ate => "KRYPTO.bn128ate",
        })
    }
}

impl fmt::Display for MapOperation {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Empty => "empty Map",
            Self::Item => "Map item",
            Self::Update => "Map update",
            Self::Get => "Map lookup",
            Self::InKeys => "Map key membership",
        })
    }
}

impl fmt::Display for ListOperation {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Empty => "empty List",
            Self::Item => "List item",
            Self::Concat => "List concatenation",
            Self::Get => "List lookup",
            Self::Update => "List update",
            Self::Size => "List size",
            Self::Make => "List repetition",
            Self::Range => "List range",
            Self::UpdateAll => "List range update",
        })
    }
}

impl fmt::Display for SetOperation {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Empty => "empty Set",
            Self::Item => "Set item",
            Self::Concat => "Set concatenation",
            Self::Union => "Set union",
            Self::Contains => "Set membership",
        })
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
        assert_eq!(item.to_string(), "example::math::integer::Number");
        assert_eq!(
            SemanticSortRef::Declared(item.clone()).to_string(),
            "example::math::integer::Number"
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
        let generated = StableItemId::new(
            item.package().clone(),
            ["math"],
            "Number",
            ItemKind::Constructor,
            "variant-0",
        )
        .unwrap();
        assert_eq!(generated.to_string(), "example::math::Number [variant-0]");
        assert_eq!(ItemKind::ContextAlias.to_string(), "context alias");
        assert_eq!(
            SourceMapKey::new("source.key").unwrap().to_string(),
            "source.key"
        );
    }
}
