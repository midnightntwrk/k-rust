//! Where a term case's construct stands, and what its spelling contains: the data the oracle
//! ([`super::oracle`]) reads.
//!
//! A [`Position`] is a value: the sentence [`Form`], the [`Slot`] of the form, the [`Kind`] of the
//! position (what a term there means), the [`PatternRoot`] of a pattern's root, and the
//! [`Nesting`] the position lies in below the slot's root. A slot template declares the
//! [`Opening`]s from its slot's root to its hole ([`Position::at`]), and a spelling declares its
//! [`Node`]s, each with the openings from the hole to it, so every node's position is derived by
//! [`Position::enter`], never read from a case's text or ID.
//!
//! The model is the generator's own: it shares nothing with `krs_syntax::positions`, the
//! product's position table, which `tests/positions.rs` compares with the oracle case by case.
//! A new position is one more path (a slot's root is the empty one, a position a construct opens
//! a longer one), a new form one more [`Form`] with its traits, and a new construct one more
//! [`Construct`] with its oracle entry.

/// The sentence form a term is written in.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Form {
    /// A clause of a readable `k::rules!` block over a configuration (`for Machine`).
    ReadableRule,
    /// A clause of a readable `k::claims!` block.
    ReadableClaim,
    /// A clause of a `k::rules!` block over a sort (`for Stmt`).
    SortRule,
    /// A row of a `k::equations!` table.
    EquationTable,
    /// A `#[k::rule]` fn with a result.
    RuleFn,
    /// A single-body `#[k::rule]` fn, whose subject's `k::rewrite!` islands say what changes.
    LocalRule,
    /// A `#[k::equation]` fn, and the equation a function shorthand's body defines.
    EquationFn,
    /// A `#[k::simplification]` fn.
    Simplification,
    /// A `cells!` rule with a result.
    CellsRule,
    /// A `#[k::init]` initializer.
    Initializer,
    /// A `#[k::constant]`.
    Constant,
}

impl Form {
    /// Whether the form is a claim: its sides describe symbolic states, which the prover reaches.
    #[must_use]
    pub const fn is_claim(self) -> bool {
        matches!(self, Self::ReadableClaim)
    }

    /// Whether the form writes its cell values in the `cells!` reference notation, which names
    /// every field of every record.
    #[must_use]
    pub const fn writes_cells(self) -> bool {
        matches!(self, Self::CellsRule)
    }

    /// Whether the form's subject, outside its `k::rewrite!` islands, is both what the sentence
    /// matches and what it keeps: a single-body rule's.
    #[must_use]
    pub const fn keeps_subject(self) -> bool {
        matches!(self, Self::LocalRule)
    }

    /// Whether `k::rewrite!` marks what changes inside the form's subject.
    #[must_use]
    pub const fn marks_rewrites(self) -> bool {
        matches!(self, Self::LocalRule)
    }

    /// Whether the form rewrites its subject in place as the one term it matched: a single-body
    /// rule and a simplification.
    #[must_use]
    pub const fn rewrites_one_term(self) -> bool {
        matches!(self, Self::LocalRule | Self::Simplification)
    }

    /// Whether the form's subject matches terms whose functions are evaluated: a rewrite rule's
    /// and an equation's, but not a simplification's (it rewrites unevaluated applications) or a
    /// claim's (its states are symbolic).
    #[must_use]
    pub const fn matches_evaluated_terms(self) -> bool {
        matches!(
            self,
            Self::ReadableRule
                | Self::SortRule
                | Self::EquationTable
                | Self::RuleFn
                | Self::LocalRule
                | Self::EquationFn
                | Self::CellsRule
        )
    }

    /// Whether the root of the form's subject is a function's application: an equation's, which
    /// defines the function, and a simplification's, which rewrites its unevaluated application.
    #[must_use]
    pub const fn subject_root_applies_function(self) -> bool {
        matches!(
            self,
            Self::EquationFn | Self::EquationTable | Self::Simplification
        )
    }

    /// Whether a matching-logic predicate may be the form's condition: a claim's, and a
    /// simplification's, which holds of symbolic terms.
    #[must_use]
    pub const fn admits_predicate_conditions(self) -> bool {
        matches!(self, Self::ReadableClaim | Self::Simplification)
    }

    /// The role of the form's subject root, `None` for a form with no subject.
    #[must_use]
    pub const fn subject_root(self) -> Option<PatternRoot> {
        match self {
            Self::RuleFn
            | Self::LocalRule
            | Self::EquationFn
            | Self::EquationTable
            | Self::Simplification => Some(PatternRoot::Subject),
            Self::SortRule => Some(PatternRoot::Clause),
            Self::ReadableRule | Self::ReadableClaim | Self::CellsRule => Some(PatternRoot::Value),
            Self::Initializer | Self::Constant => None,
        }
    }
}

/// The part of a form a term fills.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Slot {
    /// The subject: what the sentence matches (a rule's left side, a claim's start state, a
    /// function's arguments).
    Subject,
    /// The result: what the sentence builds.
    Result,
    /// The `#[k::requires]` condition.
    Requires,
    /// An initializer's or a constant's value.
    Value,
}

/// What a term at a position means.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Kind {
    /// A shape that already-evaluated values are compared against: a subject, a local pattern,
    /// a collection element in a pattern.
    Matched,
    /// The key a map read in a pattern finds its entry by: matched against the map's keys where
    /// it is a pattern, computed and looked up where it is computed.
    Evaluated,
    /// A value to construct: a result, a rewrite's right side, an initializer's or a constant's
    /// value, the operands of a function or a test.
    Built,
    /// A Bool to compute: a condition.
    Guard,
}

/// The root of a pattern, whose role decides what may stand for the whole of it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum PatternRoot {
    /// The subject of a fn or a table row: the constructor or function application the sentence
    /// matches.
    Subject,
    /// The subject of a `for Sort` clause: the constructor the clause matches, or a bare name for
    /// the whole subject.
    Clause,
    /// A readable or `cells!` record's cell value, which is no sentence's root.
    Value,
}

/// A collection entry a position lies in.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Entry {
    /// A map read's key.
    MapKey,
    /// A list's element.
    ListElement,
}

/// A pattern a construct opens inside a term.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum LocalPattern {
    /// A `let` statement's pattern.
    Let,
    /// A `k::matches!` pattern.
    Matches,
}

/// A side of a `k::rewrite!`.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RewriteSide {
    /// The matched side.
    Left,
    /// The side the matched term becomes.
    Right,
}

/// What lies between the slot's root and a position: the innermost entry, local pattern and
/// rewrite side it lies in.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct Nesting {
    /// The innermost collection entry entered.
    pub entry: Option<Entry>,
    /// The innermost local pattern entered.
    pub local: Option<LocalPattern>,
    /// The `k::rewrite!` side entered.
    pub rewrite: Option<RewriteSide>,
    /// Whether the position is inside a matching-logic predicate.
    pub in_predicate: bool,
}

/// A step from a construct to a position it opens, or from a slot's root into a collection.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Opening {
    /// An argument of a constructor application.
    Argument,
    /// An argument of a function application.
    FunctionArgument,
    /// The pattern of `name @ pattern`.
    AsBody,
    /// One alternative of `A | B`.
    OrBranch,
    /// A `let` statement's pattern.
    LetPattern,
    /// A `let` statement's value.
    LetValue,
    /// A `let` block's result.
    LetBody,
    /// The term a `k::matches!` tests.
    MatchesSubject,
    /// A `k::matches!` pattern.
    MatchesPattern,
    /// A `k::rewrite!`'s left side.
    RewriteLeft,
    /// A `k::rewrite!`'s right side.
    RewriteRight,
    /// The operand of `k::is!` or `k::project!`.
    SortTestOperand,
    /// An operand of `k::or_bool!`.
    OrBoolOperand,
    /// A field of a `k::fragment!` cell term.
    FragmentField,
    /// The body of a matching-logic predicate (a quantifier's closure).
    PredicateBody,
    /// A term operand of a matching-logic predicate (`k::ml::equals`).
    PredicateOperand,
    /// A field a record update lists.
    UpdateField,
    /// A record update's base.
    UpdateBase,
    /// The key of a map read's entry.
    MapKey,
    /// An element of a list read or written.
    ListElement,
}

/// Where a construct stands.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Position {
    /// The sentence form.
    pub form: Form,
    /// The part of the form.
    pub slot: Slot,
    /// What a term here means.
    pub kind: Kind,
    /// The pattern root this position is, if it is one.
    pub root: Option<PatternRoot>,
    /// What lies between the slot's root and here.
    pub nesting: Nesting,
}

impl Position {
    /// The root of `slot` in `form`: a subject's is matched and has the form's root role, a
    /// result and a value are built, and a condition is a guard.
    #[must_use]
    pub const fn root(form: Form, slot: Slot) -> Self {
        let (kind, root) = match slot {
            Slot::Subject => (Kind::Matched, form.subject_root()),
            Slot::Result | Slot::Value => (Kind::Built, None),
            Slot::Requires => (Kind::Guard, None),
        };
        Self {
            form,
            slot,
            kind,
            root,
            nesting: Nesting {
                entry: None,
                local: None,
                rewrite: None,
                in_predicate: false,
            },
        }
    }

    /// The position `path` opens from the root of `slot` in `form`.
    #[must_use]
    pub const fn at(form: Form, slot: Slot, path: &[Opening]) -> Self {
        Self::root(form, slot).enter_all(path)
    }

    /// The position `path` opens from this one.
    #[must_use]
    pub const fn enter_all(self, path: &[Opening]) -> Self {
        let mut position = self;
        let mut index = 0;
        while index < path.len() {
            position = position.enter(path[index]);
            index += 1;
        }
        position
    }

    /// The position `opening` opens from this one. Only the two sides of `name @ pattern`,
    /// `A | B` and `k::rewrite!` stay at a pattern's root.
    #[must_use]
    pub const fn enter(self, opening: Opening) -> Self {
        let mut position = self;
        position.root = None;
        match opening {
            // A constructor's arguments mean what the constructor does: a key's constructor
            // pattern binds its names as the key does.
            Opening::Argument | Opening::FragmentField => {}
            // A function's arguments are matched where the function is (a simplification's or a
            // claim's subject), and otherwise computed.
            Opening::FunctionArgument => {
                if !matches!(self.kind, Kind::Matched) {
                    position.kind = Kind::Built;
                }
            }
            Opening::AsBody | Opening::OrBranch => position.root = self.root,
            Opening::RewriteLeft => {
                position.root = self.root;
                position.nesting.rewrite = Some(RewriteSide::Left);
            }
            Opening::RewriteRight => {
                position.root = self.root;
                position.nesting.rewrite = Some(RewriteSide::Right);
                position.kind = Kind::Built;
            }
            Opening::LetPattern => {
                position.kind = Kind::Matched;
                position.nesting.local = Some(LocalPattern::Let);
            }
            Opening::MatchesPattern => {
                position.kind = Kind::Matched;
                position.nesting.local = Some(LocalPattern::Matches);
            }
            // A block's result is the block's value: a condition in a condition, built elsewhere.
            Opening::LetBody => {
                if !matches!(self.kind, Kind::Guard) {
                    position.kind = Kind::Built;
                }
            }
            Opening::LetValue
            | Opening::MatchesSubject
            | Opening::SortTestOperand
            | Opening::UpdateField
            | Opening::UpdateBase
            | Opening::PredicateOperand => position.kind = Kind::Built,
            Opening::OrBoolOperand => position.kind = Kind::Guard,
            Opening::PredicateBody => {
                position.kind = Kind::Guard;
                position.nesting.in_predicate = true;
            }
            Opening::MapKey => {
                position.kind = Kind::Evaluated;
                position.nesting.entry = Some(Entry::MapKey);
            }
            Opening::ListElement => position.nesting.entry = Some(Entry::ListElement),
        }
        position
    }
}

/// A term construct, as the oracle tells them apart.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Construct {
    /// A bare name: a binder, or a unit constructor at a fn subject's root.
    Reference,
    /// A constructor application, a unit constructor's path included.
    Constructor,
    /// A literal: Int (a negative one included), Bool, String, Float.
    Literal,
    /// An application of a function the definition declares.
    FunctionApplication,
    /// An application of a builtin operation (`k::builtin::int::add(..)`), a function no
    /// equation defines.
    BuiltinApplication,
    /// `_`.
    Wildcard,
    /// `name @ pattern`.
    As,
    /// `A | B`.
    Or,
    /// `k::matches!(term, pattern)`.
    Matches,
    /// A `let` block.
    Let,
    /// A matching-logic predicate (`k::ml::exists`, `k::ml::equals`).
    MlPredicate,
    /// `k::rewrite!(from => to)`.
    Rewrite,
    /// `k::is!` or `k::project!`.
    SortTest,
    /// `k::anonymous!`.
    Anonymous,
    /// `k::or_bool!`.
    OrBool,
    /// `k::fragment![..]`.
    Fragment,
    /// A record update, `Ctor { f: e, ..base }`.
    RecordUpdate,
    /// `k::id!`.
    IdToken,
    /// `k::bytes!`.
    BytesToken,
    /// `k::lexeme!`.
    Lexeme,
}

/// One construct of a spelling and where it stands: the openings from the hole to it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Node {
    /// The construct.
    pub construct: Construct,
    /// The openings from the hole to the construct; empty for the construct at the hole.
    pub path: &'static [Opening],
}

/// A node of `construct` at `path` below the hole.
#[must_use]
pub const fn node(construct: Construct, path: &'static [Opening]) -> Node {
    Node { construct, path }
}

/// A construct's spelling and its nodes, in the walker's order (preorder, in source order).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Spelling {
    /// The text written in the hole.
    pub text: &'static str,
    /// Every construct the text holds.
    pub nodes: &'static [Node],
}

/// A term case's position and its construct's nodes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TermCase {
    /// Where the hole stands.
    pub position: Position,
    /// The constructs the hole holds.
    pub nodes: &'static [Node],
}
