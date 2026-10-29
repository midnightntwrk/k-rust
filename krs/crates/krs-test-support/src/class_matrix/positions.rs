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
    /// A `#[k::context]` fn: its subject is the context, and its one `k::rewrite!` rewrites the
    /// hole.
    Context,
    /// A `#[k::alias]` clause, which expands a production marked `#[k::alias]` and runs backwards
    /// when a result is printed.
    Alias,
    /// A `#[k::desugar]` clause, which expands a production marked `#[k::desugar]` once, before
    /// anything runs.
    Desugar,
    /// A `cells!` rule with a result.
    CellsRule,
    /// A single-body `cells!` rule.
    CellsLocalRule,
    /// A `#[k::claim]` fn over `cells!` terms.
    CellsClaim,
    /// A `#[k::context_alias]`, a named configuration context.
    ContextAlias,
    /// A `#[k::init]` initializer.
    Initializer,
    /// A `#[k::constant]`.
    Constant,
}

impl Form {
    /// Every form.
    pub const ALL: [Self; 17] = [
        Self::ReadableRule,
        Self::ReadableClaim,
        Self::SortRule,
        Self::EquationTable,
        Self::RuleFn,
        Self::LocalRule,
        Self::EquationFn,
        Self::Simplification,
        Self::Context,
        Self::Alias,
        Self::Desugar,
        Self::CellsRule,
        Self::CellsLocalRule,
        Self::CellsClaim,
        Self::ContextAlias,
        Self::Initializer,
        Self::Constant,
    ];

    /// The slots the form has.
    #[must_use]
    pub const fn slots(self) -> &'static [Slot] {
        match self {
            Self::ReadableRule
            | Self::ReadableClaim
            | Self::SortRule
            | Self::EquationTable
            | Self::RuleFn
            | Self::EquationFn
            | Self::Simplification
            | Self::CellsRule
            | Self::CellsClaim => &[Slot::Subject, Slot::Result, Slot::Requires],
            Self::LocalRule | Self::CellsLocalRule | Self::Context => {
                &[Slot::Subject, Slot::Requires]
            }
            Self::Alias | Self::Desugar => &[Slot::Subject, Slot::Result],
            Self::ContextAlias => &[Slot::Subject],
            Self::Initializer | Self::Constant => &[Slot::Value],
        }
    }

    /// Whether the form is a claim: its sides describe symbolic states, which the prover reaches.
    #[must_use]
    pub const fn is_claim(self) -> bool {
        matches!(self, Self::ReadableClaim | Self::CellsClaim)
    }

    /// Whether the form writes its cell values in the `cells!` reference notation, which names
    /// every field of every record.
    #[must_use]
    pub const fn writes_cells(self) -> bool {
        matches!(
            self,
            Self::CellsRule | Self::CellsLocalRule | Self::CellsClaim | Self::ContextAlias
        )
    }

    /// Whether the form's subject, outside its `k::rewrite!` islands, is both what the sentence
    /// matches and what it keeps: a single-body rule's.
    #[must_use]
    pub const fn keeps_subject(self) -> bool {
        matches!(self, Self::LocalRule | Self::CellsLocalRule)
    }

    /// Whether `k::rewrite!` marks what changes inside the form's subject: a single-body rule's,
    /// and a context's, which rewrites its hole.
    #[must_use]
    pub const fn marks_rewrites(self) -> bool {
        matches!(self, Self::LocalRule | Self::CellsLocalRule | Self::Context)
    }

    /// Whether the form rewrites its subject in place as the one term it matched: a single-body
    /// rule and a simplification.
    #[must_use]
    pub const fn rewrites_one_term(self) -> bool {
        matches!(
            self,
            Self::LocalRule | Self::CellsLocalRule | Self::Simplification
        )
    }

    /// Whether the form's subject matches terms whose functions are evaluated: a rewrite rule's,
    /// an equation's and a context's, which match the configuration a computation reached, but
    /// not a simplification's (it rewrites unevaluated applications), a claim's (its states are
    /// symbolic) or a static clause's (it expands program and rule terms as written, before
    /// anything runs).
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
                | Self::Context
                | Self::CellsRule
                | Self::CellsLocalRule
                | Self::ContextAlias
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

    /// Whether the root of the form's subject is the production the clause expands: a static
    /// clause's, a production marked as the clause is.
    #[must_use]
    pub const fn subject_root_expands_production(self) -> bool {
        matches!(self, Self::Alias | Self::Desugar)
    }

    /// Whether a matching-logic predicate may be the form's condition: a claim's, and a
    /// simplification's, which holds of symbolic terms.
    #[must_use]
    pub const fn admits_predicate_conditions(self) -> bool {
        matches!(
            self,
            Self::ReadableClaim | Self::CellsClaim | Self::Simplification
        )
    }

    /// The role of the form's subject root, `None` for a form with no subject.
    #[must_use]
    pub const fn subject_root(self) -> Option<PatternRoot> {
        match self {
            Self::RuleFn
            | Self::LocalRule
            | Self::EquationFn
            | Self::EquationTable
            | Self::Simplification
            | Self::Context
            | Self::Alias
            | Self::Desugar => Some(PatternRoot::Subject),
            Self::SortRule => Some(PatternRoot::Clause),
            Self::ReadableRule
            | Self::ReadableClaim
            | Self::CellsRule
            | Self::CellsLocalRule
            | Self::CellsClaim
            | Self::ContextAlias => Some(PatternRoot::Value),
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
    /// a collection's element or value in a pattern.
    Matched,
    /// The key a map read in a pattern finds its entry by, or the element a set in a pattern is
    /// looked up by (a set is looked up by its elements as a map by its keys), which reads two
    /// ways. A pattern-only
    /// construct (`_`, `@`, `|`), or a name nothing else in the pattern binds, selects an entry by
    /// matching the map's keys, which are evaluated values: a choice among the entries. A
    /// computed term (an application, an operator, a `let` block, ..) is computed from names
    /// bound elsewhere and looked up. A value (a constructor, a literal) reads either way. The
    /// positions below a key follow the reading its construct gives: those a pattern-only
    /// construct opens are matched, those a computed one opens are built ([`Position::enter`]).
    Evaluated,
    /// A value to construct: a result, a rewrite's right side, an initializer's or a constant's
    /// value, the operands of a function or a test, and the key of a map or the element of a set
    /// that is built.
    Built,
    /// A Bool to compute: a condition.
    Guard,
}

/// The root of a pattern, whose role decides what may stand for the whole of it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum PatternRoot {
    /// The subject of a fn, a table row, a context or a static clause: the constructor or
    /// function application the sentence matches.
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
    /// An item of the computation cell's sequence.
    ComputationItem,
    /// A list's element.
    ListElement,
    /// A map's key.
    MapKey,
    /// A map's value.
    MapValue,
    /// A set's element.
    SetElement,
    /// A cell collection's instance, matched against the instances the collection holds.
    Instance,
}

impl Entry {
    const fn same(self, other: Self) -> bool {
        self as u8 == other as u8
    }
}

/// The collection entries a position lies in, outermost first: a list element inside a map key
/// keeps the key.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct Entries {
    chain: [Option<Entry>; Self::DEPTH],
}

impl Entries {
    /// The most entries a position lies in.
    pub const DEPTH: usize = 4;

    /// No entry.
    pub const NONE: Self = Self {
        chain: [None; Self::DEPTH],
    };

    /// These entries, with `entry` entered inside the innermost.
    ///
    /// # Panics
    ///
    /// Panics when the chain already holds [`Self::DEPTH`] entries.
    #[must_use]
    pub const fn push(self, entry: Entry) -> Self {
        let mut entries = self;
        let mut index = 0;
        while index < Self::DEPTH {
            if entries.chain[index].is_none() {
                entries.chain[index] = Some(entry);
                return entries;
            }
            index += 1;
        }
        panic!("a position lies in at most four entries")
    }

    /// The innermost entry.
    #[must_use]
    pub const fn innermost(self) -> Option<Entry> {
        let mut index = Self::DEPTH;
        while index > 0 {
            index -= 1;
            if let Some(entry) = self.chain[index] {
                return Some(entry);
            }
        }
        None
    }

    /// Whether `entry` is one of the entries.
    #[must_use]
    pub const fn contains(self, entry: Entry) -> bool {
        let mut index = 0;
        while index < Self::DEPTH {
            if let Some(held) = self.chain[index]
                && held.same(entry)
            {
                return true;
            }
            index += 1;
        }
        false
    }

    /// The entries, outermost first.
    pub fn iter(self) -> impl Iterator<Item = Entry> {
        self.chain.into_iter().flatten()
    }
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

/// What lies between the slot's root and a position: the entries it lies in, and the innermost
/// local pattern and rewrite side.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct Nesting {
    /// The collection entries entered, outermost first.
    pub entries: Entries,
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
    /// An item of the computation cell, `k: [item, ..]`, `KCell(item, ..)`, `k::k![.., item]`.
    ComputationItem,
    /// The key of a map's entry.
    MapKey,
    /// The value of a map's entry.
    MapValue,
    /// The element of a set's singleton, `set::item(element)`.
    SetElement,
    /// An element of a list read or written.
    ListElement,
    /// A Map or List collection's instance in a pattern, which the collection holds as a value or
    /// an element: matched. A Set collection's instance is its element ([`Self::SetElement`]).
    Instance,
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
                entries: Entries::NONE,
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
            // claim's subject), and otherwise computed. A sort test applies the sort's generated
            // predicate or projection, so its operand is a function's argument.
            Opening::FunctionArgument | Opening::SortTestOperand => {
                if !matches!(self.kind, Kind::Matched) {
                    position.kind = Kind::Built;
                }
            }
            // Alternatives and an alias's pattern match what the construct does; in a key, they
            // select an entry by matching the map's keys.
            Opening::AsBody | Opening::OrBranch => {
                position.root = self.root;
                if matches!(self.kind, Kind::Evaluated) {
                    position.kind = Kind::Matched;
                }
            }
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
            // A block's result is the value the block computes, an object term even in a
            // condition: a predicate there is an operand of the block.
            Opening::LetBody
            | Opening::LetValue
            | Opening::MatchesSubject
            | Opening::UpdateField
            | Opening::UpdateBase
            | Opening::PredicateOperand => position.kind = Kind::Built,
            // `k::or_bool!` applies the Bool disjunction: its operands are matched where the
            // application is, as a function's are, and are conditions elsewhere.
            Opening::OrBoolOperand => {
                if !matches!(self.kind, Kind::Matched) {
                    position.kind = Kind::Guard;
                }
            }
            Opening::PredicateBody => {
                position.kind = Kind::Guard;
                position.nesting.in_predicate = true;
            }
            // A map read in a pattern finds its entry by its key, and a set by its element; a
            // map or a set that is built has its keys and elements built.
            Opening::MapKey | Opening::SetElement => {
                position.kind = match self.kind {
                    Kind::Matched | Kind::Evaluated => Kind::Evaluated,
                    Kind::Built | Kind::Guard => Kind::Built,
                };
                let entry = if matches!(opening, Opening::MapKey) {
                    Entry::MapKey
                } else {
                    Entry::SetElement
                };
                position.nesting.entries = self.nesting.entries.push(entry);
            }
            Opening::MapValue => {
                position.nesting.entries = self.nesting.entries.push(Entry::MapValue);
            }
            Opening::ListElement => {
                position.nesting.entries = self.nesting.entries.push(Entry::ListElement);
            }
            Opening::Instance => {
                position.nesting.entries = self.nesting.entries.push(Entry::Instance);
            }
            Opening::ComputationItem => {
                position.nesting.entries = self.nesting.entries.push(Entry::ComputationItem);
            }
        }
        position
    }
}

/// A notation form of `krs_syntax::notation`: notation for one builtin call.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Notation {
    /// `a + b`, `a - b`, `a * b`, `a / b`, `a % b`.
    Arithmetic,
    /// `a & b`, `a ^ b`.
    Bitwise,
    /// `a | b` over operands an operator's domain takes, `x | 1`; where a pattern is read the
    /// same spelling is alternatives. `A | B` over constructor patterns is [`Construct::Or`].
    BitwiseOr,
    /// `a << b`, `a >> b`.
    Shift,
    /// `a < b`, `a <= b`, `a > b`, `a >= b`.
    Comparison,
    /// `a == b`, `a != b`.
    Equality,
    /// `a && b`, `bool::and_then`.
    AndThen,
    /// `a || b`, `bool::or_else`.
    OrElse,
    /// `!a`.
    Not,
    /// `-a` on anything but a literal.
    Negation,
    /// `recv.op::<D>(args..)`.
    Method,
}

impl Notation {
    /// Every notation form.
    pub const ALL: [Self; 11] = [
        Self::Arithmetic,
        Self::Bitwise,
        Self::BitwiseOr,
        Self::Shift,
        Self::Comparison,
        Self::Equality,
        Self::AndThen,
        Self::OrElse,
        Self::Not,
        Self::Negation,
        Self::Method,
    ];
}

/// A term construct, as the oracle tells them apart.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Construct {
    /// A bare name: a binder, or a unit constructor at a fn subject's root.
    Reference,
    /// A binder the case's pattern binds nowhere else: in a key or a set's element, where it is
    /// matched, it selects the entries whose key matches.
    Fresh,
    /// A constructor application, a unit constructor's path included.
    Constructor,
    /// A constructor application whose turbofish names its parametric production's instance,
    /// `Wrap::<KItem>(x)`.
    Turbofish,
    /// A literal: Int (a negative one included), Bool, String, Float.
    Literal,
    /// An application of a function the definition declares.
    FunctionApplication,
    /// An application of a builtin operation (`k::builtin::int::add(..)`), a function no
    /// equation defines.
    BuiltinApplication,
    /// A notation form, which denotes a builtin operation's application.
    Notation(Notation),
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
    /// An open record, `Ctor { f: e, .. }`.
    OpenRecord,
    /// A map literal, `k::map![k -> v]` or `map![k -> v]`.
    MapLiteral,
    /// List brackets, `[x, ..]`.
    ListBrackets,
    /// An anonymous rest, the `..` of `[x, ..]`.
    Rest,
    /// `k::id!`.
    IdToken,
    /// `k::bytes!`.
    BytesToken,
    /// `k::lexeme!`.
    Lexeme,
}

impl Construct {
    /// Every construct, each notation form apart.
    pub const ALL: [Self; 37] = [
        Self::Reference,
        Self::Fresh,
        Self::Constructor,
        Self::Turbofish,
        Self::Literal,
        Self::FunctionApplication,
        Self::BuiltinApplication,
        Self::Notation(Notation::Arithmetic),
        Self::Notation(Notation::Bitwise),
        Self::Notation(Notation::BitwiseOr),
        Self::Notation(Notation::Shift),
        Self::Notation(Notation::Comparison),
        Self::Notation(Notation::Equality),
        Self::Notation(Notation::AndThen),
        Self::Notation(Notation::OrElse),
        Self::Notation(Notation::Not),
        Self::Notation(Notation::Negation),
        Self::Notation(Notation::Method),
        Self::Wildcard,
        Self::As,
        Self::Or,
        Self::Matches,
        Self::Let,
        Self::MlPredicate,
        Self::Rewrite,
        Self::SortTest,
        Self::Anonymous,
        Self::OrBool,
        Self::Fragment,
        Self::RecordUpdate,
        Self::OpenRecord,
        Self::MapLiteral,
        Self::ListBrackets,
        Self::Rest,
        Self::IdToken,
        Self::BytesToken,
        Self::Lexeme,
    ];

    /// Whether the construct is a compiler-owned island: a macro the compiler reads as a term of
    /// its own.
    #[must_use]
    pub const fn is_island(self) -> bool {
        matches!(
            self,
            Self::Matches
                | Self::Rewrite
                | Self::SortTest
                | Self::Anonymous
                | Self::OrBool
                | Self::Fragment
                | Self::IdToken
                | Self::BytesToken
                | Self::Lexeme
        )
    }
}

/// One construct of a spelling and where it stands: the openings from the hole to it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Node {
    /// The construct.
    pub construct: Construct,
    /// The openings from the hole to the construct; empty for the construct at the hole.
    pub path: Vec<Opening>,
    /// Whether the node is the outer construct's, whose opening the case's construct stands in
    /// (depth 2), rather than the case's construct's.
    pub outer: bool,
}

/// A node of `construct` at `path` below the hole.
#[must_use]
pub fn node(construct: Construct, path: &[Opening]) -> Node {
    Node {
        construct,
        path: path.to_vec(),
        outer: false,
    }
}

impl Node {
    /// The node, standing below `prefix`: the openings from an outer hole to this node's hole.
    #[must_use]
    pub fn below(&self, prefix: &[Opening]) -> Self {
        let mut path = prefix.to_vec();
        path.extend_from_slice(&self.path);
        Self {
            construct: self.construct,
            path,
            outer: self.outer,
        }
    }

    /// The node, as the outer construct's.
    #[must_use]
    pub fn outer(self) -> Self {
        Self {
            outer: true,
            ..self
        }
    }
}

/// A term case's position and its construct's nodes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TermCase {
    /// Where the slot's hole stands; for a construct inside another construct's opening (depth
    /// 2), where the outer construct stands.
    pub position: Position,
    /// The openings from the slot's root to `position`.
    pub path: Vec<Opening>,
    /// The constructs the hole holds, the outer construct's included, in the walker's order
    /// (preorder, in source order).
    pub nodes: Vec<Node>,
}
