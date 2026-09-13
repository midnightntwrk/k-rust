//! Well-known KORE identities the frontend emits and the backend reads.
//!
//! Spellings live here once; every crate compares through the predicates below.
//! Nothing is interned: the enums are the vocabulary, the representations keep their strings.
//! The identifier prefixes (`Sort`, `Lbl`, `Var`) are not here: only the frontend applies and
//! strips them, so they live with its encoder.

use crate::kore::ast::{Sort, Symbol};

/// Symbols every compiled definition contains regardless of the user's modules.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum WellKnownSymbol {
    /// `inj{From, To}(From) : To [sortInjection{}()]`, the prelude's polymorphic injection.
    Inj,
    /// `kseq{}(KItem, K) : K`, the K-sequence cons.
    KSeq,
    /// `dotk{}() : K`, the empty K sequence.
    DotK,
    /// `append{}(K, K) : K`.
    Append,
    /// `rawTerm{}(KItem)`, the LLVM backend's wrapper around a top-level injected term.
    RawTerm,
}

impl WellKnownSymbol {
    pub const ALL: [Self; 5] = [
        Self::Inj,
        Self::KSeq,
        Self::DotK,
        Self::Append,
        Self::RawTerm,
    ];

    /// The KORE symbol name.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Inj => "inj",
            Self::KSeq => "kseq",
            Self::DotK => "dotk",
            Self::Append => "append",
            Self::RawTerm => "rawTerm",
        }
    }
}

/// Sorts of the KORE prelude and of the generated configuration that two crates test for.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum BuiltinSort {
    K,
    KItem,
    Bool,
    Int,
    String,
    Bytes,
    Float,
    Map,
    Set,
    List,
    KConfigVar,
    GeneratedTopCell,
    GeneratedCounterCell,
}

impl BuiltinSort {
    pub const ALL: [Self; 13] = [
        Self::K,
        Self::KItem,
        Self::Bool,
        Self::Int,
        Self::String,
        Self::Bytes,
        Self::Float,
        Self::Map,
        Self::Set,
        Self::List,
        Self::KConfigVar,
        Self::GeneratedTopCell,
        Self::GeneratedCounterCell,
    ];

    /// The KORE spelling (`"SortK"`, `"SortKItem"`, …).
    pub const fn kore_name(self) -> &'static str {
        match self {
            Self::K => "SortK",
            Self::KItem => "SortKItem",
            Self::Bool => "SortBool",
            Self::Int => "SortInt",
            Self::String => "SortString",
            Self::Bytes => "SortBytes",
            Self::Float => "SortFloat",
            Self::Map => "SortMap",
            Self::Set => "SortSet",
            Self::List => "SortList",
            Self::KConfigVar => "SortKConfigVar",
            Self::GeneratedTopCell => "SortGeneratedTopCell",
            Self::GeneratedCounterCell => "SortGeneratedCounterCell",
        }
    }

    /// The K spelling (`"K"`, `"KItem"`, …); `kore_name` is `"Sort"` followed by it for every
    /// variant.
    pub const fn k_name(self) -> &'static str {
        match self {
            Self::K => "K",
            Self::KItem => "KItem",
            Self::Bool => "Bool",
            Self::Int => "Int",
            Self::String => "String",
            Self::Bytes => "Bytes",
            Self::Float => "Float",
            Self::Map => "Map",
            Self::Set => "Set",
            Self::List => "List",
            Self::KConfigVar => "KConfigVar",
            Self::GeneratedTopCell => "GeneratedTopCell",
            Self::GeneratedCounterCell => "GeneratedCounterCell",
        }
    }
}

impl Symbol {
    /// True when the symbol's name is the well-known symbol's spelling.
    pub fn is(&self, symbol: WellKnownSymbol) -> bool {
        self.name == symbol.as_str()
    }
}

impl Sort {
    /// True for the nullary application of the builtin's KORE name.
    pub fn is_builtin(&self, sort: BuiltinSort) -> bool {
        matches!(
            self,
            Self::Application { name, arguments }
                if arguments.is_empty() && name == sort.kore_name()
        )
    }

    /// The nullary application of the builtin's KORE name.
    pub fn builtin(sort: BuiltinSort) -> Self {
        Self::Application {
            name: sort.kore_name().to_owned(),
            arguments: Vec::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kore::lexical::symbol_problems;

    #[test]
    fn kore_name_is_sort_followed_by_k_name() {
        for sort in BuiltinSort::ALL {
            assert_eq!(
                sort.kore_name(),
                format!("Sort{}", sort.k_name()),
                "{sort:?}"
            );
            assert!(Sort::builtin(sort).is_builtin(sort), "{sort:?}");
        }
    }

    #[test]
    fn well_known_symbol_spellings_are_distinct_kore_symbols() {
        let spellings: Vec<_> = WellKnownSymbol::ALL
            .iter()
            .map(|symbol| symbol.as_str())
            .collect();
        for (index, spelling) in spellings.iter().enumerate() {
            assert!(symbol_problems(spelling).is_empty(), "{spelling}");
            assert!(!spellings[index + 1..].contains(spelling), "{spelling}");
        }
        let symbol = Symbol {
            name: "inj".into(),
            sort_parameters: Vec::new(),
        };
        assert!(symbol.is(WellKnownSymbol::Inj));
        assert!(!symbol.is(WellKnownSymbol::KSeq));
    }

    #[test]
    fn is_builtin_rejects_a_parametric_application_of_the_same_name() {
        let parametric = Sort::Application {
            name: BuiltinSort::Map.kore_name().to_owned(),
            arguments: vec![Sort::builtin(BuiltinSort::K)],
        };
        assert!(!parametric.is_builtin(BuiltinSort::Map));
        assert!(!Sort::Variable("SortMap".into()).is_builtin(BuiltinSort::Map));
        assert!(!Sort::builtin(BuiltinSort::Set).is_builtin(BuiltinSort::Map));
    }
}
