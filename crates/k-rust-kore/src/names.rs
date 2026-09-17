//! Well-known KORE identities the frontend emits and the backend reads.
//!
//! Spellings live here once; every crate compares through the predicates below.
//! Nothing is interned: the enums are the vocabulary, the representations keep their strings.
//! The identifier prefixes (`Sort`, `Lbl`, `Var`) are not here: only the frontend applies and
//! strips them, so they live with its encoder.

use crate::kore::ast::{Attributes, Pattern, Sort, Symbol};

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

/// Attribute symbols the frontend emits into `definition.kore` and the backend reads.
///
/// `as_str` is the KORE identifier as written, including Java `ModuleToKORE`'s encoding of
/// keywords and punctuation (`alias'Kywd'`, `symbol'Kywd'`, `UNIQUE'Unds'ID`,
/// `org'Stop'kframework'Stop'attributes'Stop'Source`; `-` is an identifier character and
/// stays); the K key each one comes from is the frontend's business
/// (`k_rust::definition::AttributeKey`).
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum KoreAttribute {
    // The emitted K keys, in the order of the frontend's key table.
    Label,
    Concrete,
    Symbolic,
    Token,
    Hook,
    Comm,
    Priority,
    Circularity,
    Trusted,
    Depends,
    Cool,
    NonExecutable,
    Owise,
    PreservesDefinedness,
    SmtLemma,
    Anywhere,
    Simplification,
    Syntactic,
    Colors,
    Element,
    Format,
    Klabel,
    Smtlib,
    SmtHook,
    Unit,
    Update,
    Symbol,
    Alias,
    AliasRec,
    Assoc,
    Binder,
    Bracket,
    Cell,
    Constructor,
    Deprecated,
    FreshGenerator,
    Function,
    Functional,
    Idem,
    Impure,
    Injective,
    Macro,
    MacroRec,
    Memo,
    NoEvaluators,
    Total,
    Concat,
    CoolLike,
    HasDomainValues,
    Nat,
    Priorities,
    Source,
    Location,
    SymbolOverload,
    Terminals,
    UniqueId,
    // Markers the emitter or the prelude writes that are not K keys of a sentence.
    SortInjection,
    Subsort,
    TopCellInitializer,
    /// Java K's spelling of `symbol-overload` in older generated definitions; the backend reads
    /// it beside `SymbolOverload`, the emitter never writes it.
    Overload,
}

impl KoreAttribute {
    pub const ALL: [Self; 60] = [
        Self::Label,
        Self::Concrete,
        Self::Symbolic,
        Self::Token,
        Self::Hook,
        Self::Comm,
        Self::Priority,
        Self::Circularity,
        Self::Trusted,
        Self::Depends,
        Self::Cool,
        Self::NonExecutable,
        Self::Owise,
        Self::PreservesDefinedness,
        Self::SmtLemma,
        Self::Anywhere,
        Self::Simplification,
        Self::Syntactic,
        Self::Colors,
        Self::Element,
        Self::Format,
        Self::Klabel,
        Self::Smtlib,
        Self::SmtHook,
        Self::Unit,
        Self::Update,
        Self::Symbol,
        Self::Alias,
        Self::AliasRec,
        Self::Assoc,
        Self::Binder,
        Self::Bracket,
        Self::Cell,
        Self::Constructor,
        Self::Deprecated,
        Self::FreshGenerator,
        Self::Function,
        Self::Functional,
        Self::Idem,
        Self::Impure,
        Self::Injective,
        Self::Macro,
        Self::MacroRec,
        Self::Memo,
        Self::NoEvaluators,
        Self::Total,
        Self::Concat,
        Self::CoolLike,
        Self::HasDomainValues,
        Self::Nat,
        Self::Priorities,
        Self::Source,
        Self::Location,
        Self::SymbolOverload,
        Self::Terminals,
        Self::UniqueId,
        Self::SortInjection,
        Self::Subsort,
        Self::TopCellInitializer,
        Self::Overload,
    ];

    /// The variants no K attribute key produces: the three markers the emitter or the prelude
    /// writes by hand, and the legacy `overload` the backend only reads.
    pub const WITHOUT_KEY: [Self; 4] = [
        Self::SortInjection,
        Self::Subsort,
        Self::TopCellInitializer,
        Self::Overload,
    ];

    /// The KORE identifier as written in `definition.kore`.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Label => "label",
            Self::Concrete => "concrete",
            Self::Symbolic => "symbolic",
            Self::Token => "token",
            Self::Hook => "hook",
            Self::Comm => "comm",
            Self::Priority => "priority",
            Self::Circularity => "circularity",
            Self::Trusted => "trusted",
            Self::Depends => "depends",
            Self::Cool => "cool",
            Self::NonExecutable => "non-executable",
            Self::Owise => "owise",
            Self::PreservesDefinedness => "preserves-definedness",
            Self::SmtLemma => "smt-lemma",
            Self::Anywhere => "anywhere",
            Self::Simplification => "simplification",
            Self::Syntactic => "syntactic",
            Self::Colors => "colors",
            Self::Element => "element",
            Self::Format => "format",
            Self::Klabel => "klabel",
            Self::Smtlib => "smtlib",
            Self::SmtHook => "smt-hook",
            Self::Unit => "unit",
            Self::Update => "update",
            Self::Symbol => "symbol'Kywd'",
            Self::Alias => "alias'Kywd'",
            Self::AliasRec => "alias-rec",
            Self::Assoc => "assoc",
            Self::Binder => "binder",
            Self::Bracket => "bracket",
            Self::Cell => "cell",
            Self::Constructor => "constructor",
            Self::Deprecated => "deprecated",
            Self::FreshGenerator => "freshGenerator",
            Self::Function => "function",
            Self::Functional => "functional",
            Self::Idem => "idem",
            Self::Impure => "impure",
            Self::Injective => "injective",
            Self::Macro => "macro",
            Self::MacroRec => "macro-rec",
            Self::Memo => "memo",
            Self::NoEvaluators => "no-evaluators",
            Self::Total => "total",
            Self::Concat => "concat",
            Self::CoolLike => "cool-like",
            Self::HasDomainValues => "hasDomainValues",
            Self::Nat => "nat",
            Self::Priorities => "priorities",
            Self::Source => "org'Stop'kframework'Stop'attributes'Stop'Source",
            Self::Location => "org'Stop'kframework'Stop'attributes'Stop'Location",
            Self::SymbolOverload => "symbol-overload",
            Self::Terminals => "terminals",
            Self::UniqueId => "UNIQUE'Unds'ID",
            Self::SortInjection => "sortInjection",
            Self::Subsort => "subsort",
            Self::TopCellInitializer => "topCellInitializer",
            Self::Overload => "overload",
        }
    }
}

/// One attribute's arguments failed the shape the reader expects.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MalformedAttribute {
    pub attribute: KoreAttribute,
    /// `"one string"` or `"one nullary symbol"`.
    pub expected: &'static str,
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

impl Attributes {
    /// The symbol and arguments of the first application of `attribute`, whatever its
    /// arguments and sort parameters (`subsort{Sub, Sup}()` carries its payload in the sort
    /// parameters).
    pub fn application(&self, attribute: KoreAttribute) -> Option<(&Symbol, &[Pattern])> {
        self.0.iter().find_map(|pattern| match pattern {
            Pattern::Application { symbol, arguments } if symbol.name == attribute.as_str() => {
                Some((symbol, arguments.as_slice()))
            }
            _ => None,
        })
    }

    /// True when some application of `attribute` is present; arguments are ignored.
    pub fn has(&self, attribute: KoreAttribute) -> bool {
        self.application(attribute).is_some()
    }

    /// The arguments of the first application of `attribute`.
    pub fn arguments(&self, attribute: KoreAttribute) -> Option<&[Pattern]> {
        self.application(attribute).map(|(_, arguments)| arguments)
    }

    /// `[String(s)]` → `Some(s)`; absent → `None`; any other shape → error.
    pub fn string(&self, attribute: KoreAttribute) -> Result<Option<&str>, MalformedAttribute> {
        match self.arguments(attribute) {
            None => Ok(None),
            Some([Pattern::String(value)]) => Ok(Some(value)),
            Some(_) => Err(MalformedAttribute {
                attribute,
                expected: "one string",
            }),
        }
    }

    /// As `string`, and `[]` → `Some("")` (`simplification` without a priority).
    pub fn string_or_empty(
        &self,
        attribute: KoreAttribute,
    ) -> Result<Option<&str>, MalformedAttribute> {
        match self.arguments(attribute) {
            Some([]) => Ok(Some("")),
            _ => self.string(attribute),
        }
    }

    /// `[Application { symbol, arguments: [] }]` → `Some(&symbol.name)`; absent → `None`; any
    /// other shape → error.
    pub fn nullary_symbol(
        &self,
        attribute: KoreAttribute,
    ) -> Result<Option<&str>, MalformedAttribute> {
        match self.arguments(attribute) {
            None => Ok(None),
            Some([Pattern::Application { symbol, arguments }]) if arguments.is_empty() => {
                Ok(Some(&symbol.name))
            }
            Some(_) => Err(MalformedAttribute {
                attribute,
                expected: "one nullary symbol",
            }),
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

    #[test]
    fn kore_attribute_spellings_are_distinct_kore_identifiers() {
        let spellings: Vec<_> = KoreAttribute::ALL
            .iter()
            .map(|attribute| attribute.as_str())
            .collect();
        for (index, spelling) in spellings.iter().enumerate() {
            assert!(symbol_problems(spelling).is_empty(), "{spelling}");
            assert!(!spellings[index + 1..].contains(spelling), "{spelling}");
        }
        for marker in KoreAttribute::WITHOUT_KEY {
            assert!(KoreAttribute::ALL.contains(&marker));
        }
    }

    #[test]
    fn attribute_predicates_read_the_first_application_by_shape() {
        let application = |name: &str, arguments: Vec<Pattern>| Pattern::Application {
            symbol: Symbol {
                name: name.into(),
                sort_parameters: Vec::new(),
            },
            arguments,
        };
        let attributes = Attributes(vec![
            application("simplification", Vec::new()),
            application("priority", vec![Pattern::String("50".into())]),
            application("element", vec![application("Lblelt", Vec::new())]),
            application("hook", vec![application("Lblnot", Vec::new())]),
        ]);
        assert!(attributes.has(KoreAttribute::Simplification));
        assert!(!attributes.has(KoreAttribute::Owise));
        assert!(
            attributes
                .arguments(KoreAttribute::Simplification)
                .is_some_and(<[Pattern]>::is_empty)
        );
        assert!(attributes.arguments(KoreAttribute::Owise).is_none());
        assert_eq!(
            attributes.string_or_empty(KoreAttribute::Simplification),
            Ok(Some(""))
        );
        assert_eq!(
            attributes.string(KoreAttribute::Simplification),
            Err(MalformedAttribute {
                attribute: KoreAttribute::Simplification,
                expected: "one string",
            })
        );
        assert_eq!(attributes.string(KoreAttribute::Priority), Ok(Some("50")));
        assert_eq!(attributes.string(KoreAttribute::Owise), Ok(None));
        assert_eq!(
            attributes.nullary_symbol(KoreAttribute::Element),
            Ok(Some("Lblelt"))
        );
        assert_eq!(
            attributes.string(KoreAttribute::Hook),
            Err(MalformedAttribute {
                attribute: KoreAttribute::Hook,
                expected: "one string",
            })
        );
        assert_eq!(attributes.nullary_symbol(KoreAttribute::Owise), Ok(None));
        assert_eq!(
            attributes.nullary_symbol(KoreAttribute::Priority),
            Err(MalformedAttribute {
                attribute: KoreAttribute::Priority,
                expected: "one nullary symbol",
            })
        );
    }
}
