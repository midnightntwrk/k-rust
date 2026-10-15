//! This definition-layer algorithm scans or transforms its model in deterministic declaration order.
//! Cost is linear in visited syntax unless its local documentation states another bound; no dedicated counter.
//!
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

/// The shape of a builtin attribute parameter that names sorts.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SortValues {
    /// The whole parameter names one sort.
    One,
    /// A comma-separated list of sort spellings, with each element trimmed.
    List,
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

/// What an attribute key's value records ([`AttributeKey::record`]).
///
/// A `SourcePosition` or `Provenance` value is written by the loader or the compiler, never by
/// user source, and never changes what the sentence that carries it means; two loads of one
/// definition from texts that differ only in the position of its sentences differ only in these
/// keys.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum KeyRecord {
    /// Part of what the sentence, module or definition says.
    Content,
    /// A position in the text the loader read: the file, its identity, the span, or the start
    /// of the sentence's content. The value moves when text before it moves.
    SourcePosition,
    /// krust's own record of how the sentence was built: its origin receipt, its offsets in the
    /// input, and the input sentences it derives from.
    Provenance,
}

const fn builtin(parameter: KeyParameter, targets: u16) -> KeyClass {
    KeyClass::Builtin { parameter, targets }
}

macro_rules! attribute_keys {
    ($($variant:ident = $spelling:literal ($class:expr, $emits:literal, $record:ident $(, sorts = $sorts:ident)?)),+ $(,)?) => {
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

            /// What the key's value records: the sentence's content, the position in the text
            /// the loader read it from, or krust's construction history ([`KeyRecord`]).
            /// The column is mandatory, so a key cannot be added without a record.
            pub const fn record(self) -> KeyRecord {
                match self {
                    $(Self::$variant => KeyRecord::$record),+
                }
            }

            /// K `KeyRange::WholePipeline`: the key is emitted to `definition.kore`.
            pub const fn emits(self) -> bool {
                match self {
                    $(Self::$variant => $emits),+
                }
            }

            /// Only builtin keys whose parameter names sorts carry this column.
            /// The cell `type` attribute selects a collection kind, a keyword rather than a sort.
            /// Internal keys (`predicate`, `sortParams`, `cellSort`) are written by the compiler from applied sorts.
            pub const fn sort_values(self) -> Option<SortValues> {
                match self {
                    $(Self::$variant => attribute_keys!(@sorts $($sorts)?)),+
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
    (@sorts $sorts:ident) => { Some(SortValues::$sorts) };
    (@sorts) => { None };
}

use KeyClass::{Internal, Krust};
use KeyParameter::{Forbidden, Optional, Required};

attribute_keys! {
    // K built-in keys (user-visible).
    Group = "group" (builtin(Required, ALL_SENTENCES), false, Content),
    Label = "label" (builtin(Required, ALL_SENTENCES), true, Content),
    AllPath = "all-path" (builtin(Forbidden, CLAIM | MODULE), false, Content),
    OnePath = "one-path" (builtin(Forbidden, CLAIM | MODULE), false, Content),
    Concrete = "concrete" (builtin(Optional, MODULE | PRODUCTION | RULE), true, Content),
    Symbolic = "symbolic" (builtin(Optional, MODULE | PRODUCTION | RULE), true, Content),
    CellCollection = "cellCollection" (builtin(Forbidden, PRODUCTION | SYNTAX_SORT), false, Content),
    Token = "token" (builtin(Forbidden, PRODUCTION | SYNTAX_SORT), true, Content),
    Hook = "hook" (builtin(Required, PRODUCTION | SYNTAX_SORT), true, Content),
    Comm = "comm" (builtin(Forbidden, PRODUCTION | RULE), true, Content),
    Initializer = "initializer" (builtin(Forbidden, PRODUCTION | RULE), false, Content),
    Priority = "priority" (builtin(Required, CONTEXT | CONTEXT_ALIAS | PRODUCTION | RULE), true, Content),
    Result = "result" (builtin(Required, CONTEXT | CONTEXT_ALIAS | PRODUCTION | RULE), false, Content, sorts = One),
    Private = "private" (builtin(Forbidden, MODULE | PRODUCTION), false, Content),
    Public = "public" (builtin(Forbidden, MODULE | PRODUCTION), false, Content),
    Stream = "stream" (builtin(Optional, PRODUCTION | RULE), false, Content),
    UnboundVariables = "unboundVariables" (
        builtin(Required, CONTEXT | CONTEXT_ALIAS | PRODUCTION | RULE | CLAIM),
        false,
        Content
    ),
    Circularity = "circularity" (builtin(Forbidden, CLAIM), true, Content),
    Trusted = "trusted" (builtin(Forbidden, CLAIM), true, Content),
    Depends = "depends" (builtin(Required, CLAIM), true, Content),
    Context = "context" (builtin(Required, CONTEXT_ALIAS), false, Content),
    Cool = "cool" (builtin(Forbidden, RULE), true, Content),
    Heat = "heat" (builtin(Forbidden, RULE), false, Content),
    NonExecutable = "non-executable" (builtin(Forbidden, RULE), true, Content),
    Owise = "owise" (builtin(Forbidden, RULE), true, Content),
    PreservesDefinedness = "preserves-definedness" (builtin(Forbidden, RULE), true, Content),
    SmtLemma = "smt-lemma" (builtin(Forbidden, RULE), true, Content),
    Anywhere = "anywhere" (builtin(Forbidden, RULE), true, Content),
    Simplification = "simplification" (builtin(Optional, RULE), true, Content),
    Syntactic = "syntactic" (builtin(Required, RULE), true, Content),
    Haskell = "haskell" (builtin(Forbidden, MODULE), false, Content),
    NotLr1 = "not-lr1" (builtin(Forbidden, MODULE), false, Content),
    Locations = "locations" (builtin(Forbidden, SYNTAX_SORT), false, Content),
    ApplyPriority = "applyPriority" (builtin(Required, PRODUCTION), false, Content),
    CellName = "cellName" (builtin(Required, PRODUCTION), false, Content),
    Color = "color" (builtin(Required, PRODUCTION), false, Content),
    Colors = "colors" (builtin(Required, PRODUCTION), true, Content),
    Element = "element" (builtin(Required, PRODUCTION), true, Content),
    Format = "format" (builtin(Required, PRODUCTION), true, Content),
    Index = "index" (builtin(Required, PRODUCTION), false, Content),
    Klabel = "klabel" (builtin(Required, PRODUCTION), true, Content),
    Latex = "latex" (builtin(Required, PRODUCTION), false, Content),
    Multiplicity = "multiplicity" (builtin(Required, PRODUCTION), false, Content),
    Overload = "overload" (builtin(Required, PRODUCTION), false, Content),
    Parser = "parser" (builtin(Required, PRODUCTION), false, Content),
    Prec = "prec" (builtin(Required, PRODUCTION), false, Content),
    Smtlib = "smtlib" (builtin(Required, PRODUCTION), true, Content),
    SmtHook = "smt-hook" (builtin(Required, PRODUCTION), true, Content),
    TerminatorSymbol = "terminator-symbol" (builtin(Required, PRODUCTION), false, Content),
    Type = "type" (builtin(Required, PRODUCTION), false, Content),
    Unit = "unit" (builtin(Required, PRODUCTION), true, Content),
    Update = "update" (builtin(Required, PRODUCTION), true, Content),
    WrapElement = "wrapElement" (builtin(Required, PRODUCTION), false, Content),
    Hybrid = "hybrid" (builtin(Optional, PRODUCTION), false, Content, sorts = List),
    Seqstrict = "seqstrict" (builtin(Optional, PRODUCTION), false, Content),
    Strict = "strict" (builtin(Optional, PRODUCTION), false, Content),
    Symbol = "symbol" (builtin(Optional, PRODUCTION), true, Content),
    Alias = "alias" (builtin(Forbidden, PRODUCTION), true, Content),
    AliasRec = "alias-rec" (builtin(Forbidden, PRODUCTION), true, Content),
    Assoc = "assoc" (builtin(Forbidden, PRODUCTION), true, Content),
    Avoid = "avoid" (builtin(Forbidden, PRODUCTION), false, Content),
    Bag = "bag" (builtin(Forbidden, PRODUCTION), false, Content),
    Binder = "binder" (builtin(Forbidden, PRODUCTION), true, Content),
    Bracket = "bracket" (builtin(Forbidden, PRODUCTION), true, Content),
    Cell = "cell" (builtin(Forbidden, PRODUCTION), true, Content),
    Constructor = "constructor" (builtin(Forbidden, PRODUCTION), true, Content),
    Deprecated = "deprecated" (builtin(Forbidden, PRODUCTION), true, Content),
    Exit = "exit" (builtin(Forbidden, PRODUCTION), false, Content),
    FreshGenerator = "freshGenerator" (builtin(Forbidden, PRODUCTION), true, Content),
    Function = "function" (builtin(Forbidden, PRODUCTION), true, Content),
    Functional = "functional" (builtin(Forbidden, PRODUCTION), true, Content),
    Idem = "idem" (builtin(Forbidden, PRODUCTION), true, Content),
    Impure = "impure" (builtin(Forbidden, PRODUCTION), true, Content),
    Initial = "initial" (builtin(Forbidden, PRODUCTION), false, Content),
    Injective = "injective" (builtin(Forbidden, PRODUCTION), true, Content),
    Internal = "internal" (builtin(Forbidden, PRODUCTION), false, Content),
    // K declares `left` and `right` in both tables; `is_internal_key` keeps that.
    Left = "left" (builtin(Forbidden, PRODUCTION), false, Content),
    Macro = "macro" (builtin(Forbidden, PRODUCTION), true, Content),
    MacroRec = "macro-rec" (builtin(Forbidden, PRODUCTION), true, Content),
    Maincell = "maincell" (builtin(Forbidden, PRODUCTION), false, Content),
    Memo = "memo" (builtin(Forbidden, PRODUCTION), true, Content),
    MlBinder = "mlBinder" (builtin(Forbidden, PRODUCTION), false, Content),
    MlOp = "mlOp" (builtin(Forbidden, PRODUCTION), false, Content),
    NonAssoc = "non-assoc" (builtin(Forbidden, PRODUCTION), false, Content),
    NoEvaluators = "no-evaluators" (builtin(Forbidden, PRODUCTION), true, Content),
    Prefer = "prefer" (builtin(Forbidden, PRODUCTION), false, Content),
    ReturnsUnit = "returnsUnit" (builtin(Forbidden, PRODUCTION), false, Content),
    Right = "right" (builtin(Forbidden, PRODUCTION), false, Content),
    Total = "total" (builtin(Forbidden, PRODUCTION), true, Content),
    UnparseAvoid = "unparseAvoid" (builtin(Forbidden, PRODUCTION), false, Content),
    Unused = "unused" (builtin(Forbidden, PRODUCTION), false, Content),
    // K internal keys.
    Anonymous = "anonymous" (Internal, false, Content),
    BracketLabel = "bracketLabel" (Internal, false, Content),
    CellFragment = "cellFragment" (Internal, false, Content),
    CellOptAbsent = "cellOptAbsent" (Internal, false, Content),
    CellSort = "cellSort" (Internal, false, Content),
    Concat = "concat" (Internal, true, Content),
    ContentStartColumn = "contentStartColumn" (Internal, false, SourcePosition),
    ContentStartLine = "contentStartLine" (Internal, false, SourcePosition),
    ContentStartOffset = "contentStartOffset" (Internal, false, SourcePosition),
    CoolLike = "cool-like" (Internal, true, Content),
    Denormal = "denormal" (Internal, false, Content),
    Digest = "digest" (Internal, false, Content),
    DummyCell = "dummy_cell" (Internal, false, Content),
    FilterElement = "filterElement" (Internal, false, Content),
    Fresh = "fresh" (Internal, false, Content),
    HasDomainValues = "hasDomainValues" (Internal, true, Content),
    Nat = "nat" (Internal, true, Content),
    NotInjection = "notInjection" (Internal, false, Content),
    NotLr1Modules = "not-lr1-modules" (Internal, false, Content),
    OriginalPrd = "originalPrd" (Internal, false, Content),
    Predicate = "predicate" (Internal, false, Content),
    PrettyPrintWithSortAnnotation = "prettyPrintWithSortAnnotation" (Internal, false, Content),
    Priorities = "priorities" (Internal, true, Content),
    ProductionClass = "org.kframework.definition.Production" (Internal, false, Content),
    Projection = "projection" (Internal, false, Content),
    RecordPrd = "recordPrd" (Internal, false, Content),
    RecordPrdZero = "recordPrd-zero" (Internal, false, Content),
    RecordPrdOne = "recordPrd-one" (Internal, false, Content),
    RecordPrdMain = "recordPrd-main" (Internal, false, Content),
    RecordPrdEmpty = "recordPrd-empty" (Internal, false, Content),
    RecordPrdSubsort = "recordPrd-subsort" (Internal, false, Content),
    RecordPrdRepeat = "recordPrd-repeat" (Internal, false, Content),
    RecordPrdItem = "recordPrd-item" (Internal, false, Content),
    Refreshed = "refreshed" (Internal, false, Content),
    SmtPrelude = "smt-prelude" (Internal, false, Content),
    SortClass = "org.kframework.kore.Sort" (Internal, false, Content),
    SortParams = "sortParams" (Internal, false, Content),
    Source = "org.kframework.attributes.Source" (Internal, true, SourcePosition),
    SourceId = "org.kframework.attributes.SourceId" (Internal, false, SourcePosition),
    Location = "org.kframework.attributes.Location" (Internal, true, SourcePosition),
    SymbolOverload = "symbol-overload" (Internal, true, Content),
    SyntaxModule = "syntaxModule" (Internal, false, Content),
    TemporaryCellSortDecl = "temporary-cell-sort-decl" (Internal, false, Content),
    Terminals = "terminals" (Internal, true, Content),
    UniqueId = "UNIQUE_ID" (Internal, true, Content),
    UserList = "userList" (Internal, false, Content),
    UserListTerminator = "userListTerminator" (Internal, false, Content),
    WithConfig = "withConfig" (Internal, false, Content),
    // Keys krust mints.
    Origin = "org.krust.provenance.Origin" (Krust, false, Provenance),
    SentenceStartOffset = "org.krust.provenance.SentenceStartOffset" (Krust, false, Provenance),
    SentenceEndOffset = "org.krust.provenance.SentenceEndOffset" (Krust, false, Provenance),
    InputAddresses = "org.krust.provenance.InputAddresses" (Krust, false, Provenance),
    GeneratedRuleSyntax = "generatedRuleSyntax" (Krust, false, Content),
    BisonParsingOnlySubsort = "#bisonParsingOnlySubsort" (Krust, false, Content),
    // The `owise` equation local-function lowering adds to make a lambda `\bottom` off its
    // pattern; the LLVM target leaves it out.
    LambdaRefutation = "org.krust.LambdaRefutation" (Krust, false, Content),
}

impl AttributeKey {
    pub(crate) const fn is_emission_claim(self) -> bool {
        matches!(
            self,
            Self::Total | Self::Functional | Self::Constructor | Self::Injective
        )
    }
}

impl AttributeKey {
    /// The keys that make a production or rule macro-like.
    pub const MACRO_LIKE: [Self; 4] = [Self::Macro, Self::MacroRec, Self::Alias, Self::AliasRec];

    /// Keys krust writes for its own provenance and never reports as semantic content
    /// ([`KeyRecord::Provenance`]). `Attributes` equality ignores exactly these keys.
    pub const fn is_provenance_only(self) -> bool {
        matches!(self.record(), KeyRecord::Provenance)
    }

    /// Keys whose value is a position in the text the loader read
    /// ([`KeyRecord::SourcePosition`]). `Attributes` equality keeps them: a sentence's identity
    /// within k-rust includes where it was read.
    pub const fn is_source_position(self) -> bool {
        matches!(self.record(), KeyRecord::SourcePosition)
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
    fn sort_valued_keys_are_result_and_hybrid() {
        let keys = AttributeKey::ALL
            .into_iter()
            .filter_map(|key| key.sort_values().map(|values| (key, values)))
            .collect::<Vec<_>>();
        assert_eq!(
            keys,
            vec![
                (AttributeKey::Result, SortValues::One),
                (AttributeKey::Hybrid, SortValues::List),
            ]
        );
    }

    /// The keys that record where the loader read a sentence, and the keys that record krust's
    /// construction history; every other key is content.
    #[test]
    fn source_position_and_provenance_keys_are_frozen() {
        let positions = AttributeKey::ALL
            .into_iter()
            .filter(|key| key.is_source_position())
            .collect::<Vec<_>>();
        assert_eq!(
            positions,
            [
                AttributeKey::ContentStartColumn,
                AttributeKey::ContentStartLine,
                AttributeKey::ContentStartOffset,
                AttributeKey::Source,
                AttributeKey::SourceId,
                AttributeKey::Location,
            ]
        );
        let provenance = AttributeKey::ALL
            .into_iter()
            .filter(|key| key.is_provenance_only())
            .collect::<Vec<_>>();
        assert_eq!(
            provenance,
            [
                AttributeKey::Origin,
                AttributeKey::SentenceStartOffset,
                AttributeKey::SentenceEndOffset,
                AttributeKey::InputAddresses,
            ]
        );
        for key in AttributeKey::ALL {
            let expected = if positions.contains(&key) {
                KeyRecord::SourcePosition
            } else if provenance.contains(&key) {
                KeyRecord::Provenance
            } else {
                KeyRecord::Content
            };
            assert_eq!(key.record(), expected, "{key:?}");
            assert!(
                !(key.is_source_position() && key.is_provenance_only()),
                "{key:?}"
            );
        }
    }

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
