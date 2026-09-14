//! Every well-known K attribute key, declared once with the facts K keeps per key.
//!
//! The definition model's `Attributes` map stays `String`-keyed: unrecognized user keys are
//! data until `check_attribute_map` reports them, and KAST JSON round-trips them.
//! This enum is the closed set of keys the compiler itself reads or writes: K's built-in keys
//! (user-visible, with their parameter rule and sentence targets), K's internal keys (written by
//! the compiler, an error in user source), and the markers krust mints.
//! The `emits` column is K's `KeyRange::WholePipeline`: the key reaches `definition.kore`.

pub(crate) const MODULE: u16 = 1 << 0;
pub(crate) const SYNTAX_SORT: u16 = 1 << 1;
pub(crate) const SORT_SYNONYM: u16 = 1 << 2;
pub(crate) const SYNTAX_LEXICAL: u16 = 1 << 3;
pub(crate) const PRODUCTION: u16 = 1 << 4;
pub(crate) const SYNTAX_ASSOCIATIVITY: u16 = 1 << 5;
pub(crate) const SYNTAX_PRIORITY: u16 = 1 << 6;
pub(crate) const CONTEXT_ALIAS: u16 = 1 << 7;
pub(crate) const CONTEXT: u16 = 1 << 8;
pub(crate) const RULE: u16 = 1 << 9;
pub(crate) const CLAIM: u16 = 1 << 10;
pub(crate) const CONFIGURATION: u16 = 1 << 11;
pub(crate) const BUBBLE: u16 = 1 << 12;
const ALL_SENTENCES: u16 = !MODULE;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum KeyParameter {
    Required,
    Optional,
    Forbidden,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct BuiltinKey {
    pub(crate) parameter: KeyParameter,
    pub(crate) targets: u16,
}

/// Which of K's two key tables a key belongs to, or that krust minted it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum KeyClass {
    /// May appear in user source; the parameter rule and the sentence kinds it may target.
    Builtin {
        parameter: KeyParameter,
        targets: u16,
    },
    /// Written by the compiler; an error in user source.
    Internal,
    /// Written by krust only; treated as `Internal` by both attribute checks.
    Krust,
}

const fn builtin(parameter: KeyParameter, targets: u16) -> KeyClass {
    KeyClass::Builtin { parameter, targets }
}

macro_rules! attribute_keys {
    ($($variant:ident = $spelling:literal ($class:expr, $emits:literal)),+ $(,)?) => {
        /// A well-known attribute key; `as_str` is its spelling in K source, KAST JSON, and the
        /// `Attributes` map.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum AttributeKey {
            $($variant),+
        }

        impl AttributeKey {
            const COUNT: usize = 0 $(+ { let _ = stringify!($variant); 1 })+;

            /// Every key, in declaration order.
            pub const ALL: [Self; Self::COUNT] = [$(Self::$variant),+];

            /// The spelling in K source, KAST JSON, and the `Attributes` map.
            pub const fn as_str(self) -> &'static str {
                match self {
                    $(Self::$variant => $spelling),+
                }
            }

            pub const fn class(self) -> KeyClass {
                match self {
                    $(Self::$variant => $class),+
                }
            }

            /// K `KeyRange::WholePipeline`: the key is emitted to `definition.kore`.
            pub const fn emits(self) -> bool {
                match self {
                    $(Self::$variant => $emits),+
                }
            }

            /// The one string-to-key lookup; `None` for unrecognized keys.
            pub fn from_name(name: &str) -> Option<Self> {
                match name {
                    $($spelling => Some(Self::$variant),)+
                    _ => None,
                }
            }
        }
    };
}

use KeyClass::{Internal, Krust};
use KeyParameter::{Forbidden, Optional, Required};

attribute_keys! {
    // K built-in keys (user-visible), declaration order of Java `Att` at base.
    Group = "group" (builtin(Required, ALL_SENTENCES), false),
    Label = "label" (builtin(Required, ALL_SENTENCES), true),
    AllPath = "all-path" (builtin(Forbidden, CLAIM | MODULE), false),
    OnePath = "one-path" (builtin(Forbidden, CLAIM | MODULE), false),
    Concrete = "concrete" (builtin(Optional, MODULE | PRODUCTION | RULE), true),
    Symbolic = "symbolic" (builtin(Optional, MODULE | PRODUCTION | RULE), true),
    CellCollection = "cellCollection" (builtin(Forbidden, PRODUCTION | SYNTAX_SORT), false),
    Token = "token" (builtin(Forbidden, PRODUCTION | SYNTAX_SORT), true),
    Hook = "hook" (builtin(Required, PRODUCTION | SYNTAX_SORT), true),
    Comm = "comm" (builtin(Forbidden, PRODUCTION | RULE), true),
    Initializer = "initializer" (builtin(Forbidden, PRODUCTION | RULE), false),
    Priority = "priority" (builtin(Required, CONTEXT | CONTEXT_ALIAS | PRODUCTION | RULE), true),
    Result = "result" (builtin(Required, CONTEXT | CONTEXT_ALIAS | PRODUCTION | RULE), false),
    Private = "private" (builtin(Forbidden, MODULE | PRODUCTION), false),
    Public = "public" (builtin(Forbidden, MODULE | PRODUCTION), false),
    Stream = "stream" (builtin(Optional, PRODUCTION | RULE), false),
    UnboundVariables = "unboundVariables" (
        builtin(Required, CONTEXT | CONTEXT_ALIAS | PRODUCTION | RULE | CLAIM),
        false
    ),
    Circularity = "circularity" (builtin(Forbidden, CLAIM), true),
    Trusted = "trusted" (builtin(Forbidden, CLAIM), true),
    Depends = "depends" (builtin(Required, CLAIM), true),
    Context = "context" (builtin(Required, CONTEXT_ALIAS), false),
    Cool = "cool" (builtin(Forbidden, RULE), true),
    Heat = "heat" (builtin(Forbidden, RULE), false),
    NonExecutable = "non-executable" (builtin(Forbidden, RULE), true),
    Owise = "owise" (builtin(Forbidden, RULE), true),
    PreservesDefinedness = "preserves-definedness" (builtin(Forbidden, RULE), true),
    SmtLemma = "smt-lemma" (builtin(Forbidden, RULE), true),
    Anywhere = "anywhere" (builtin(Forbidden, RULE), true),
    Simplification = "simplification" (builtin(Optional, RULE), true),
    Syntactic = "syntactic" (builtin(Required, RULE), true),
    Haskell = "haskell" (builtin(Forbidden, MODULE), false),
    NotLr1 = "not-lr1" (builtin(Forbidden, MODULE), false),
    Locations = "locations" (builtin(Forbidden, SYNTAX_SORT), false),
    ApplyPriority = "applyPriority" (builtin(Required, PRODUCTION), false),
    CellName = "cellName" (builtin(Required, PRODUCTION), false),
    Color = "color" (builtin(Required, PRODUCTION), false),
    Colors = "colors" (builtin(Required, PRODUCTION), true),
    Element = "element" (builtin(Required, PRODUCTION), true),
    Format = "format" (builtin(Required, PRODUCTION), true),
    Index = "index" (builtin(Required, PRODUCTION), false),
    Klabel = "klabel" (builtin(Required, PRODUCTION), true),
    Latex = "latex" (builtin(Required, PRODUCTION), false),
    Multiplicity = "multiplicity" (builtin(Required, PRODUCTION), false),
    Overload = "overload" (builtin(Required, PRODUCTION), false),
    Parser = "parser" (builtin(Required, PRODUCTION), false),
    Prec = "prec" (builtin(Required, PRODUCTION), false),
    Smtlib = "smtlib" (builtin(Required, PRODUCTION), true),
    SmtHook = "smt-hook" (builtin(Required, PRODUCTION), true),
    TerminatorSymbol = "terminator-symbol" (builtin(Required, PRODUCTION), false),
    Type = "type" (builtin(Required, PRODUCTION), false),
    Unit = "unit" (builtin(Required, PRODUCTION), true),
    Update = "update" (builtin(Required, PRODUCTION), true),
    WrapElement = "wrapElement" (builtin(Required, PRODUCTION), false),
    Hybrid = "hybrid" (builtin(Optional, PRODUCTION), false),
    Seqstrict = "seqstrict" (builtin(Optional, PRODUCTION), false),
    Strict = "strict" (builtin(Optional, PRODUCTION), false),
    Symbol = "symbol" (builtin(Optional, PRODUCTION), true),
    Alias = "alias" (builtin(Forbidden, PRODUCTION), true),
    AliasRec = "alias-rec" (builtin(Forbidden, PRODUCTION), true),
    Assoc = "assoc" (builtin(Forbidden, PRODUCTION), true),
    Avoid = "avoid" (builtin(Forbidden, PRODUCTION), false),
    Bag = "bag" (builtin(Forbidden, PRODUCTION), false),
    Binder = "binder" (builtin(Forbidden, PRODUCTION), true),
    Bracket = "bracket" (builtin(Forbidden, PRODUCTION), true),
    Cell = "cell" (builtin(Forbidden, PRODUCTION), true),
    Constructor = "constructor" (builtin(Forbidden, PRODUCTION), true),
    Deprecated = "deprecated" (builtin(Forbidden, PRODUCTION), true),
    Exit = "exit" (builtin(Forbidden, PRODUCTION), false),
    FreshGenerator = "freshGenerator" (builtin(Forbidden, PRODUCTION), true),
    Function = "function" (builtin(Forbidden, PRODUCTION), true),
    Functional = "functional" (builtin(Forbidden, PRODUCTION), true),
    Idem = "idem" (builtin(Forbidden, PRODUCTION), true),
    Impure = "impure" (builtin(Forbidden, PRODUCTION), true),
    Initial = "initial" (builtin(Forbidden, PRODUCTION), false),
    Injective = "injective" (builtin(Forbidden, PRODUCTION), true),
    Internal = "internal" (builtin(Forbidden, PRODUCTION), false),
    // K declares `left` and `right` in both tables; `is_internal_key` keeps that.
    Left = "left" (builtin(Forbidden, PRODUCTION), false),
    Macro = "macro" (builtin(Forbidden, PRODUCTION), true),
    MacroRec = "macro-rec" (builtin(Forbidden, PRODUCTION), true),
    Maincell = "maincell" (builtin(Forbidden, PRODUCTION), false),
    Memo = "memo" (builtin(Forbidden, PRODUCTION), true),
    MlBinder = "mlBinder" (builtin(Forbidden, PRODUCTION), false),
    MlOp = "mlOp" (builtin(Forbidden, PRODUCTION), false),
    NonAssoc = "non-assoc" (builtin(Forbidden, PRODUCTION), false),
    NoEvaluators = "no-evaluators" (builtin(Forbidden, PRODUCTION), true),
    Prefer = "prefer" (builtin(Forbidden, PRODUCTION), false),
    ReturnsUnit = "returnsUnit" (builtin(Forbidden, PRODUCTION), false),
    Right = "right" (builtin(Forbidden, PRODUCTION), false),
    Total = "total" (builtin(Forbidden, PRODUCTION), true),
    UnparseAvoid = "unparseAvoid" (builtin(Forbidden, PRODUCTION), false),
    Unused = "unused" (builtin(Forbidden, PRODUCTION), false),
    // K internal keys, declaration order of Java `Att` at base.
    Anonymous = "anonymous" (Internal, false),
    BracketLabel = "bracketLabel" (Internal, false),
    CellFragment = "cellFragment" (Internal, false),
    CellOptAbsent = "cellOptAbsent" (Internal, false),
    CellSort = "cellSort" (Internal, false),
    Concat = "concat" (Internal, true),
    ContentStartColumn = "contentStartColumn" (Internal, false),
    ContentStartLine = "contentStartLine" (Internal, false),
    ContentStartOffset = "contentStartOffset" (Internal, false),
    CoolLike = "cool-like" (Internal, true),
    Denormal = "denormal" (Internal, false),
    Digest = "digest" (Internal, false),
    DummyCell = "dummy_cell" (Internal, false),
    FilterElement = "filterElement" (Internal, false),
    Fresh = "fresh" (Internal, false),
    HasDomainValues = "hasDomainValues" (Internal, true),
    Nat = "nat" (Internal, true),
    NotInjection = "notInjection" (Internal, false),
    NotLr1Modules = "not-lr1-modules" (Internal, false),
    OriginalPrd = "originalPrd" (Internal, false),
    Predicate = "predicate" (Internal, false),
    PrettyPrintWithSortAnnotation = "prettyPrintWithSortAnnotation" (Internal, false),
    Priorities = "priorities" (Internal, true),
    ProductionClass = "org.kframework.definition.Production" (Internal, false),
    Projection = "projection" (Internal, false),
    RecordPrd = "recordPrd" (Internal, false),
    RecordPrdZero = "recordPrd-zero" (Internal, false),
    RecordPrdOne = "recordPrd-one" (Internal, false),
    RecordPrdMain = "recordPrd-main" (Internal, false),
    RecordPrdEmpty = "recordPrd-empty" (Internal, false),
    RecordPrdSubsort = "recordPrd-subsort" (Internal, false),
    RecordPrdRepeat = "recordPrd-repeat" (Internal, false),
    RecordPrdItem = "recordPrd-item" (Internal, false),
    Refreshed = "refreshed" (Internal, false),
    SmtPrelude = "smt-prelude" (Internal, false),
    SortClass = "org.kframework.kore.Sort" (Internal, false),
    SortParams = "sortParams" (Internal, false),
    Source = "org.kframework.attributes.Source" (Internal, true),
    SourceId = "org.kframework.attributes.SourceId" (Internal, false),
    Location = "org.kframework.attributes.Location" (Internal, true),
    SymbolOverload = "symbol-overload" (Internal, true),
    SyntaxModule = "syntaxModule" (Internal, false),
    TemporaryCellSortDecl = "temporary-cell-sort-decl" (Internal, false),
    Terminals = "terminals" (Internal, true),
    UniqueId = "UNIQUE_ID" (Internal, true),
    UserList = "userList" (Internal, false),
    UserListTerminator = "userListTerminator" (Internal, false),
    WithConfig = "withConfig" (Internal, false),
    // Keys krust mints.
    Origin = "org.krust.provenance.Origin" (Krust, false),
    SentenceStartOffset = "org.krust.provenance.SentenceStartOffset" (Krust, false),
    SentenceEndOffset = "org.krust.provenance.SentenceEndOffset" (Krust, false),
    GeneratedRuleSyntax = "generatedRuleSyntax" (Krust, false),
    BisonParsingOnlySubsort = "#bisonParsingOnlySubsort" (Krust, false),
}

impl AttributeKey {
    /// The keys that make a production or rule macro-like.
    pub const MACRO_LIKE: [Self; 4] = [Self::Macro, Self::MacroRec, Self::Alias, Self::AliasRec];

    /// Keys krust writes for its own provenance and never reports as semantic content.
    pub(crate) const fn is_provenance_only(self) -> bool {
        matches!(
            self,
            Self::Origin | Self::SentenceStartOffset | Self::SentenceEndOffset
        )
    }
}

/// The parameter rule and sentence targets of a K built-in key; `None` for every other name.
pub(crate) fn builtin_key(key: &str) -> Option<BuiltinKey> {
    match AttributeKey::from_name(key)?.class() {
        KeyClass::Builtin { parameter, targets } => Some(BuiltinKey { parameter, targets }),
        KeyClass::Internal | KeyClass::Krust => None,
    }
}

/// Whether a name is a key the compiler writes and user source may not spell.
///
/// `left` and `right` are in both of K's tables, so they answer `true` here as well.
pub(crate) fn is_internal_key(key: &str) -> bool {
    AttributeKey::from_name(key).is_some_and(|key| {
        matches!(key.class(), KeyClass::Internal | KeyClass::Krust)
            || matches!(key, AttributeKey::Left | AttributeKey::Right)
    })
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::*;

    #[test]
    fn every_key_round_trips_through_its_spelling() {
        for key in AttributeKey::ALL {
            assert_eq!(AttributeKey::from_name(key.as_str()), Some(key), "{key:?}");
        }
    }

    #[test]
    fn spellings_are_distinct() {
        let spellings = AttributeKey::ALL
            .iter()
            .map(|key| key.as_str())
            .collect::<BTreeSet<_>>();
        assert_eq!(spellings.len(), AttributeKey::ALL.len());
    }

    /// The set emitted to `definition.kore` at the base of this registry; a row that starts or
    /// stops emitting is a visible edit of this list.
    #[test]
    fn emitted_keys_are_frozen() {
        let emitted = AttributeKey::ALL
            .iter()
            .filter(|key| key.emits())
            .map(|key| key.as_str())
            .collect::<Vec<_>>();
        let expected = [
            "label",
            "concrete",
            "symbolic",
            "token",
            "hook",
            "comm",
            "priority",
            "circularity",
            "trusted",
            "depends",
            "cool",
            "non-executable",
            "owise",
            "preserves-definedness",
            "smt-lemma",
            "anywhere",
            "simplification",
            "syntactic",
            "colors",
            "element",
            "format",
            "klabel",
            "smtlib",
            "smt-hook",
            "unit",
            "update",
            "symbol",
            "alias",
            "alias-rec",
            "assoc",
            "binder",
            "bracket",
            "cell",
            "constructor",
            "deprecated",
            "freshGenerator",
            "function",
            "functional",
            "idem",
            "impure",
            "injective",
            "macro",
            "macro-rec",
            "memo",
            "no-evaluators",
            "total",
            "concat",
            "cool-like",
            "hasDomainValues",
            "nat",
            "priorities",
            "org.kframework.attributes.Source",
            "org.kframework.attributes.Location",
            "symbol-overload",
            "terminals",
            "UNIQUE_ID",
        ];
        assert_eq!(emitted, expected);
    }
}
