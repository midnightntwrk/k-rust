//! The position table: whether a term construct may stand at a position of a sentence form.
//!
//! A term is written at a [`Position`]: a [`Slot`] of a [`Form`] (a `#[k::rule]` fn's subject,
//! a readable claim's result, an initializer's value) and the [`Nesting`] the walk has entered
//! below the slot's root (a `k::matches!` pattern, a `let` pattern, a `k::rewrite!`, a
//! collection's entry). [`admits`] answers, for one [`Construct`] at one position, from what the
//! construct means there:
//!
//! - [`Admission::Admit`]: the construct may stand there, and what is left to judge is the term's
//!   sort, which the compiler judges for every term alike (`condition-sort`, `content-sort`, a
//!   `let` whose result has no Bool sort in a guard), and its names (`unbound-name`).
//! - [`Admission::Refuse`]: the construct means nothing there, or something the position cannot
//!   hold. The position alone settles it, so the term walker refuses it before rustc runs, with
//!   the class's one [`Code`], at the construct's own range, outermost construct first.
//! - [`Admission::After`]: the answer needs what only the compiler knows, a declaration a path
//!   resolves to or an operand's sort ([`Rule`]). The walker admits the construct, and the
//!   compiler refuses it or not.
//!
//! The table is data plus [`admits`]; it says nothing about a construct's own shape (a
//! `k::matches!` with an `if` guard, a `let` with no result, `name @ ..`), which the parser
//! judges, nor about a cell entry's spelling against its cell's kind, which the configuration
//! judges.
//!
//! **The classes are the class tests' classes.** [`Class`] is this crate's copy of the `[class]`
//! section of `krs/tests/class-matrix/expected.toml`, each class with its one registered code,
//! and [`Rule`] names the classes an [`Admission::After`] row leaves to the compiler. A test in
//! `krs-test-support` (`tests/positions.rs`) checks that every class here exists there with the
//! same code, that every position class there exists here, and that the table decides every
//! generated term case as the expected outcomes do.
//!
//! **Positions.** A pattern is where a sentence matches terms: a subject, a `k::matches!`
//! pattern, a `let` pattern. Everywhere else a term is built: a result, a condition, an
//! initializer's value, a constant's value. A single-body rule (`#[k::rule]` fn returning `()`,
//! or the `cells!` one) and a simplification rewrite their subject as one term, in place; a
//! single-body rule's subject is matched and kept, except inside its `k::rewrite!` islands. A
//! `k::rewrite!`'s left side matches, as the subject around it does; its right side is what the
//! matched term becomes, a term built in place, so it is judged as a result is
//! ([`Position::rewrite_right`]). An alias clause's subject is matched and also built: the
//! clause runs backwards when a result is printed, each term its result matches printed as its
//! subject built from the match's bindings, so a construct that only matches has no meaning there
//! ([`Position::is_built_backwards`]).
//!
//! **Keys.** A map's key in a pattern is what the map is looked up by, and reads by what stands
//! at its root: a name or a pattern-only construct (`_`, `@`, `|`) selects an entry by matching
//! the map's keys, which are evaluated values, so the positions below it are matched
//! ([`Nesting::in_selected_key`]); a computed construct (a sort test, a record update, an
//! operator or a method) computes the value looked up, so the positions below it are built
//! ([`Nesting::in_computed_key`]). A constructor's fields read as the key does. A key of a map
//! that is built is built with it. A `let` block and `k::matches!` compute too, each a function of
//! the names it reads, and a computed key holds them as it holds a function's application.
//!
//! **Collection instances.** Braces write a Set collection's instances, which a pattern looks
//! the collection up by as by its elements, and a Map collection's, which it matches; only the
//! cell's declared type tells them apart, which resolution gives. So in a braced instance of a
//! pattern over evaluated terms ([`Nesting::in_braced_instance`]) a sort test and a record update
//! are the compiler's to decide, as a function's application is.

use std::fmt;

use krs_diagnostic::{Code, codes};

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
    /// A single-body `#[k::rule]` fn (one that returns `()`): its subject's `k::rewrite!` islands
    /// say what changes.
    LocalRule,
    /// A `#[k::equation]` fn, and an equation a function shorthand's body defines.
    EquationFn,
    /// A `#[k::simplification]` fn.
    Simplification,
    /// A `#[k::context]` fn, whose subject rewrites its hole.
    Context,
    /// A `#[k::alias]` fn, which expands its production as a desugar clause does and runs
    /// backwards when a result is printed.
    Alias,
    /// A `#[k::desugar]` clause.
    Desugar,
    /// A `cells!` rule with a result.
    CellsRule,
    /// A single-body `cells!` rule.
    CellsLocalRule,
    /// A `cells!` claim.
    CellsClaim,
    /// A `#[k::context_alias]`.
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

    /// Whether the form is a claim, whose states are symbolic.
    #[must_use]
    pub const fn is_claim(self) -> bool {
        matches!(self, Self::ReadableClaim | Self::CellsClaim)
    }

    /// Whether the form writes its sides as `cells!` terms, the reference notation, which names
    /// every field of every record.
    #[must_use]
    pub const fn writes_cells(self) -> bool {
        matches!(
            self,
            Self::CellsRule | Self::CellsLocalRule | Self::CellsClaim | Self::ContextAlias
        )
    }

    /// Whether the form's subject is also built: an alias clause runs backwards when a result
    /// is printed, and each term its result matches is printed as its subject, built from what
    /// the result's match bound.
    const fn builds_subject_backwards(self) -> bool {
        matches!(self, Self::Alias)
    }

    /// Whether the form's subject is matched against a program's terms as they are written: a
    /// static clause's, which static expansion matches before anything evaluates.
    const fn matches_terms_as_written(self) -> bool {
        matches!(self, Self::Alias | Self::Desugar)
    }

    /// Whether the form's result writes a configuration record, which creates cell instances:
    /// a readable rule's and a readable claim's.
    const fn creates_instances(self) -> bool {
        matches!(self, Self::ReadableRule | Self::ReadableClaim)
    }

    /// Whether the form's subject is kept as it is outside its `k::rewrite!` islands: a
    /// single-body rule's; a context's, whose heating and cooling rewrite only its hole, so the
    /// term around the hole is matched and written back; and a context alias's, the term around
    /// `here` of every context it makes.
    const fn keeps_subject(self) -> bool {
        matches!(
            self,
            Self::LocalRule | Self::CellsLocalRule | Self::Context | Self::ContextAlias
        )
    }

    /// Whether the form's subject is rewritten in place as one term: a single-body rule's, a
    /// simplification's, and a context's and a context alias's, which heating and cooling
    /// rewrite around their hole.
    const fn rewrites_one_term(self) -> bool {
        matches!(
            self,
            Self::LocalRule
                | Self::CellsLocalRule
                | Self::Simplification
                | Self::Context
                | Self::ContextAlias
        )
    }

    /// Whether a collection literal that writes entries (`map![k -> v]`, `set![a, b]`, either
    /// with a rest) may stand for the form's whole subject. A simplification rewrites a
    /// function's unevaluated application, and the literal writes the collection it builds, a
    /// value, however KRS builds it: its subject spells the update or the union as a call.
    #[must_use]
    pub const fn admits_collection_literal_root(self) -> bool {
        !matches!(self, Self::Simplification)
    }

    /// Whether the form's subject marks what changes with `k::rewrite!`: a single-body rule's,
    /// and a context's, which rewrites its hole.
    const fn rewrites_inside_subject(self) -> bool {
        matches!(self, Self::LocalRule | Self::CellsLocalRule | Self::Context)
    }

    /// Whether the form's subject is the pattern of a rewrite rule, an equation or a context,
    /// which every term it applies to matches with its functions evaluated: a context matches the
    /// configuration's terms as a rule does. A simplification's and a claim's subjects hold
    /// symbolic terms, and a static clause's the program as written, before anything runs.
    const fn matches_evaluated_terms(self) -> bool {
        matches!(
            self,
            Self::ReadableRule
                | Self::SortRule
                | Self::RuleFn
                | Self::LocalRule
                | Self::CellsRule
                | Self::CellsLocalRule
                | Self::EquationFn
                | Self::EquationTable
                | Self::Context
                | Self::ContextAlias
        )
    }

    /// Whether a matching-logic predicate may be the form's whole condition: a claim's and a
    /// simplification's.
    const fn admits_predicate_conditions(self) -> bool {
        matches!(
            self,
            Self::ReadableClaim | Self::CellsClaim | Self::Simplification
        )
    }

    const fn noun(self) -> &'static str {
        match self {
            Self::ReadableRule => "a readable rule",
            Self::ReadableClaim => "a readable claim",
            Self::SortRule => "a `k::rules!` sort rule",
            Self::EquationTable => "a `k::equations!` row",
            Self::RuleFn => "a `#[k::rule]` fn",
            Self::LocalRule => "a single-body `#[k::rule]` fn",
            Self::EquationFn => "an equation",
            Self::Simplification => "a `#[k::simplification]` fn",
            Self::Context => "a `#[k::context]` fn",
            Self::Alias => "a `#[k::alias]` fn",
            Self::Desugar => "a `#[k::desugar]` clause",
            Self::CellsRule => "a `cells!` rule",
            Self::CellsLocalRule => "a single-body `cells!` rule",
            Self::CellsClaim => "a `cells!` claim",
            Self::ContextAlias => "a `#[k::context_alias]`",
            Self::Initializer => "an initializer",
            Self::Constant => "a `#[k::constant]`",
        }
    }
}

/// The part of a form a term fills.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Slot {
    /// The subject: the pattern a sentence matches (a rule's left-hand side, a claim's start).
    Subject,
    /// The result: the term a sentence builds.
    Result,
    /// The `requires` condition.
    Requires,
    /// The `ensures` condition.
    Ensures,
    /// An initializer's value.
    InitializerValue,
    /// A constant's value.
    ConstantValue,
}

impl Slot {
    const fn noun(self) -> &'static str {
        match self {
            Self::Subject => "the subject",
            Self::Result => "the result",
            Self::Requires => "the `requires` condition",
            Self::Ensures => "the `ensures` condition",
            Self::InitializerValue | Self::ConstantValue => "the value",
        }
    }
}

/// What the walk has entered between the slot's root and the construct.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
#[expect(
    clippy::struct_excessive_bools,
    reason = "Each flag records one independent enclosing construct of the walk."
)]
pub struct Nesting {
    /// Inside the pattern of a `k::matches!`.
    pub in_matches_pattern: bool,
    /// Inside the pattern of a `let` statement.
    pub in_let_pattern: bool,
    /// Inside a `k::rewrite!`: its left side, in the slot of the rewrite, or its right side, in
    /// [`Slot::Result`] ([`Position::rewrite_right`]).
    pub in_rewrite: bool,
    /// Inside a map's key, which the map is looked up by, or a set's element in a pattern, which
    /// the set is looked up by as a map by its keys ([`Self::in_set_element`]).
    pub in_map_key: bool,
    /// Inside a set's element `set::item(e)` in a pattern: a key, told apart only to name it.
    pub in_set_element: bool,
    /// Inside a key a pattern looks up, below a construct that computes it (a sort test, a record
    /// update, an operator or a method): a term built to be looked up.
    pub in_computed_key: bool,
    /// Inside a key a pattern looks up, below a pattern-only construct (`name @ pattern`, `A |
    /// B`), which selects an entry by matching the map's keys: matched.
    pub in_selected_key: bool,
    /// Inside a cell of a collection's instance written in braces (`{ Decl { cell: .. }, .. }`):
    /// a Set collection's, which a pattern looks up by an instance as by an element, or a Map
    /// collection's, which it matches.
    pub in_braced_instance: bool,
}

/// Where a construct stands.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Position {
    /// The sentence form.
    pub form: Form,
    /// The part of the form.
    pub slot: Slot,
    /// What the walk has entered below the slot's root.
    pub nesting: Nesting,
}

impl Position {
    /// The root of `slot` in `form`.
    #[must_use]
    pub const fn root(form: Form, slot: Slot) -> Self {
        Self {
            form,
            slot,
            nesting: Nesting {
                in_matches_pattern: false,
                in_let_pattern: false,
                in_rewrite: false,
                in_map_key: false,
                in_set_element: false,
                in_computed_key: false,
                in_selected_key: false,
                in_braced_instance: false,
            },
        }
    }

    /// The position of the left side of a `k::rewrite!` standing at `self`: a pattern, matched
    /// where the rewrite stands.
    #[must_use]
    pub const fn rewrite_left(self) -> Self {
        let mut position = self;
        position.nesting.in_rewrite = true;
        position
    }

    /// The position of the right side of a `k::rewrite!` standing at `self`: what the term the
    /// left side matched becomes, which the rule builds in its place. It matches nothing, so it
    /// is a result, inside the rewrite: an alias or `_` names no term there, and a `let`, a
    /// `k::matches!` test or a sort test computes from the subject's bindings as in any result.
    #[must_use]
    pub const fn rewrite_right(self) -> Self {
        let mut position = self.rewrite_left();
        position.slot = Slot::Result;
        position
    }

    /// Whether the construct is matched against a term: the form's subject, but below a
    /// construct a key computes, or a local pattern.
    #[must_use]
    pub const fn is_pattern(self) -> bool {
        (matches!(self.slot, Slot::Subject) && !self.nesting.in_computed_key)
            || self.in_local_pattern()
    }

    /// Whether the construct stands where a pattern looks a map up: a key of a map the subject
    /// matches, at the reading its own construct gives, which a computed construct may give.
    #[must_use]
    pub const fn is_looked_up(self) -> bool {
        matches!(self.slot, Slot::Subject)
            && self.nesting.in_map_key
            && !self.nesting.in_computed_key
            && !self.nesting.in_selected_key
            && !self.in_local_pattern()
    }

    /// Whether the construct is matched against terms whose functions are evaluated: the subject
    /// of a rewrite rule, an equation or a context, outside a key or where a key selects an entry
    /// by matching, or a local pattern, which matches a value a rule computed.
    #[must_use]
    pub const fn matches_evaluated_terms(self) -> bool {
        (matches!(self.slot, Slot::Subject)
            && self.form.matches_evaluated_terms()
            && (!self.nesting.in_map_key || self.nesting.in_selected_key))
            || self.in_local_pattern()
    }

    /// Whether the construct is matched against a program's terms as they are written: in a
    /// static clause's subject, which static expansion matches before anything evaluates. A
    /// construct that computes would match only its own spelling there (`Foo(x + 1)` the program
    /// `foo(y + 1)`, not `foo(1 + y)`), where everywhere else it denotes its value.
    #[must_use]
    pub const fn matches_terms_as_written(self) -> bool {
        matches!(self.slot, Slot::Subject)
            && self.form.matches_terms_as_written()
            && !self.in_local_pattern()
    }

    /// Whether the construct stands in a braced collection instance of a pattern over evaluated
    /// terms, outside a key: looked up when the collection is a Set and the instance is computed,
    /// matched otherwise, which the collection's declared type and the instance's names decide.
    #[must_use]
    pub const fn reads_by_collection_type(self) -> bool {
        matches!(self.slot, Slot::Subject)
            && self.nesting.in_braced_instance
            && !self.nesting.in_map_key
            && !self.in_local_pattern()
            && self.form.matches_evaluated_terms()
    }

    /// Whether the construct is matched and also built: in an alias clause's subject, which is
    /// printed backwards, built from the bindings of what the clause's result matched. A
    /// construct that only matches (`_`, `name @ pattern`, `A | B`, an open record, a list's
    /// anonymous rest) has no meaning there: printing cannot build it.
    #[must_use]
    pub const fn is_built_backwards(self) -> bool {
        self.form.builds_subject_backwards() && self.is_pattern() && !self.in_local_pattern()
    }

    /// Whether the construct is inside a `k::matches!` or `let` pattern.
    const fn in_local_pattern(self) -> bool {
        self.nesting.in_matches_pattern || self.nesting.in_let_pattern
    }
}

impl fmt::Display for Position {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.nesting.in_matches_pattern {
            formatter.write_str("a `k::matches!` pattern in ")?;
        } else if self.nesting.in_let_pattern {
            formatter.write_str("a `let` pattern in ")?;
        } else if self.nesting.in_set_element {
            formatter.write_str("a set's element in ")?;
        } else if self.nesting.in_map_key {
            formatter.write_str("a map key in ")?;
        } else if self.nesting.in_rewrite {
            // Only a rewrite in a subject is walked into, so a result inside one is its right
            // side.
            if matches!(self.slot, Slot::Result) {
                return write!(
                    formatter,
                    "the right side of a `k::rewrite!`, a term built in place, in the subject of {}",
                    self.form.noun()
                );
            }
            formatter.write_str("a `k::rewrite!` in ")?;
        }
        write!(formatter, "{} of {}", self.slot.noun(), self.form.noun())
    }
}

/// What the root of a subject is, which the pattern reader applies where it reads a subject's
/// root: the one rule of a pattern that needs the root rather than a construct's position below
/// it, because it decides what a bare name at the root means.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum PatternRoot {
    /// The subject of a fn, a table row, a desugar clause or a context: its root is the
    /// constructor or function the sentence matches. A bare name there names a unit constructor,
    /// and an alias, `_` or a compiler-owned island cannot stand for the whole subject; each
    /// alternative of a root `A | B` is a whole subject.
    Subject,
    /// The subject of a `for Sort` clause: its root is the constructor the clause matches, as a
    /// [`Self::Subject`]'s, or else any term of the clause's sort, which the clause's root states
    /// without the fn subject's parameter: a bare name binds the whole subject, `_` is that term
    /// unnamed, and an alias or an island stands at the root as it does below a constructor.
    Clause,
    /// A readable record's value, which is no sentence's root: the whole pattern, `|` and
    /// parentheses at its root included, reads as below a constructor.
    Value,
}

impl PatternRoot {
    /// The policy the reader applies to `pattern` at this root, by what the root holds:
    /// [`Self::Subject`] or [`Self::Value`], since a [`Self::Clause`]'s root reads a bare name,
    /// `_`, an alias or an island as a value and anything else as a subject.
    #[must_use]
    pub const fn at(self, holds_whole_term: bool) -> Self {
        match self {
            Self::Clause if holds_whole_term => Self::Value,
            Self::Clause | Self::Subject => Self::Subject,
            Self::Value => Self::Value,
        }
    }

    /// Whether a bare name at the root names a unit constructor rather than binding.
    #[must_use]
    pub const fn names_constructor(self) -> bool {
        matches!(self, Self::Subject)
    }

    /// Whether `construct` may stand for the whole subject at this root. Alternatives and every
    /// other term may; an alias, `_` and an island stand below a subject's root.
    #[must_use]
    pub const fn admits(self, construct: RootConstruct) -> bool {
        match construct {
            RootConstruct::As | RootConstruct::Wildcard | RootConstruct::Island => {
                matches!(self, Self::Value)
            }
        }
    }
}

/// A construct whose admission at a pattern's root [`PatternRoot`] decides.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum RootConstruct {
    /// `name @ pattern`.
    As,
    /// `_`.
    Wildcard,
    /// A compiler-owned island (`k::fragment!`, `k::bytes!`, `k::rewrite!`, ..) or any macro.
    Island,
}

/// A term construct whose legality depends on where it stands. Every other term (a binder, a
/// path, a constructor application) may stand wherever a term may.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Construct {
    /// `_`.
    Wildcard,
    /// `name @ pattern` (K's `#as`).
    As,
    /// `A | B`, pattern alternatives (K's `#Or`).
    Or,
    /// `k::matches!(subject, pattern)` (K's `:=K`).
    Matches,
    /// A `let` block (K's `#let`).
    Let,
    /// A matching-logic predicate the walker recognizes by its shape: the closure of an
    /// `ml::exists`.
    MlPredicate,
    /// `k::rewrite!(from => to)` (K's local `=>`).
    Rewrite,
    /// `k::is!` or `k::project!`.
    SortTest,
    /// `k::anonymous!`, a claim's symbolic value.
    Anonymous,
    /// `k::or_bool!`, a claim's disjunction.
    OrBool,
    /// `k::fragment![..]`, a nested cell term.
    Fragment,
    /// A record update `Ctor { f: e, ..t }`.
    RecordUpdate,
    /// An open record `Ctor { f: e, .. }`.
    OpenRecord,
    /// An open group record `k::fragment![G { c: e, .. }]`, a nested cell term that leaves the
    /// group's other children open.
    OpenFragment,
    /// A list pattern's anonymous rest `[e, ..]`, the elements it leaves unnamed; a term built
    /// outside a pattern holds none, which the list notation's parser refuses.
    Rest,
    /// A turbofish instance on an application head, `Choose::<Int> { .. }`.
    Turbofish,
    /// `k::id!`.
    IdToken,
    /// `k::bytes!`.
    BytesToken,
    /// `k::lexeme!`.
    Lexeme,
    /// A literal: Int, Bool, String, Float.
    Literal,
    /// An application of a function, which only the declaration its head resolves to tells
    /// apart from a constructor's: never decided by the walker.
    FunctionApplication,
}

impl Construct {
    /// Every construct.
    pub const ALL: [Self; 21] = [
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
        Self::OpenFragment,
        Self::Rest,
        Self::Turbofish,
        Self::IdToken,
        Self::BytesToken,
        Self::Lexeme,
        Self::Literal,
        Self::FunctionApplication,
    ];
}

/// The answer of [`admits`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Admission {
    /// The construct may stand there.
    Admit,
    /// The construct may not stand there; the walker refuses it with the class's code.
    Refuse(Class),
    /// The compiler decides, by a declaration or a sort the walker cannot see.
    After(Rule),
}

/// A mistake the position alone settles, with its one registered code: the class-test class of
/// the same name.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Class {
    /// `alias-in-alias-subject`.
    AliasInAliasSubject,
    /// `alias-in-let-pattern`.
    AliasInLetPattern,
    /// `alias-outside-pattern`.
    AliasOutsidePattern,
    /// `alternatives-in-alias-subject`.
    AlternativesInAliasSubject,
    /// `alternatives-in-let-pattern`.
    AlternativesInLetPattern,
    /// `alternatives-in-one-term-rewrite`.
    AlternativesInOneTermRewrite,
    /// `claim-only-term`.
    ClaimOnlyTerm,
    /// `claim-subject-only-term`.
    ClaimSubjectOnlyTerm,
    /// `constant-not-ground`.
    ConstantNotGround,
    /// `fragment-in-initializer`.
    FragmentInInitializer,
    /// `let-outside-term`.
    LetOutsideTerm,
    /// `matches-outside-condition`.
    MatchesOutsideCondition,
    /// `open-record-in-alias-subject`.
    OpenRecordInAliasSubject,
    /// `open-record-outside-pattern`.
    OpenRecordOutsidePattern,
    /// `ml-in-initializer`.
    MlInInitializer,
    /// `ml-predicate-as-term`.
    MlPredicateAsTerm,
    /// `record-remainder-in-cells-term`.
    RecordRemainderInCellsTerm,
    /// `record-remainder-in-initializer`.
    RecordRemainderInInitializer,
    /// `record-update-in-pattern`.
    RecordUpdateInPattern,
    /// `rest-in-alias-subject`.
    RestInAliasSubject,
    /// `rewrite-in-map-key`.
    RewriteInMapKey,
    /// `rewrite-outside-local-rule`.
    RewriteOutsideLocalRule,
    /// `sort-test-in-pattern`.
    SortTestInPattern,
    /// `wildcard-in-alias-subject`.
    WildcardInAliasSubject,
    /// `wildcard-outside-pattern`.
    WildcardOutsidePattern,
}

impl Class {
    /// Every class.
    pub const ALL: [Self; 25] = [
        Self::AliasInAliasSubject,
        Self::AliasInLetPattern,
        Self::AliasOutsidePattern,
        Self::AlternativesInAliasSubject,
        Self::AlternativesInLetPattern,
        Self::AlternativesInOneTermRewrite,
        Self::ClaimOnlyTerm,
        Self::ClaimSubjectOnlyTerm,
        Self::ConstantNotGround,
        Self::FragmentInInitializer,
        Self::LetOutsideTerm,
        Self::MatchesOutsideCondition,
        Self::OpenRecordInAliasSubject,
        Self::OpenRecordOutsidePattern,
        Self::MlInInitializer,
        Self::MlPredicateAsTerm,
        Self::RecordRemainderInCellsTerm,
        Self::RecordRemainderInInitializer,
        Self::RecordUpdateInPattern,
        Self::RestInAliasSubject,
        Self::RewriteInMapKey,
        Self::RewriteOutsideLocalRule,
        Self::SortTestInPattern,
        Self::WildcardInAliasSubject,
        Self::WildcardOutsidePattern,
    ];

    /// The class's name in `expected.toml`.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::AliasInAliasSubject => "alias-in-alias-subject",
            Self::AliasInLetPattern => "alias-in-let-pattern",
            Self::AliasOutsidePattern => "alias-outside-pattern",
            Self::AlternativesInAliasSubject => "alternatives-in-alias-subject",
            Self::AlternativesInLetPattern => "alternatives-in-let-pattern",
            Self::AlternativesInOneTermRewrite => "alternatives-in-one-term-rewrite",
            Self::ClaimOnlyTerm => "claim-only-term",
            Self::ClaimSubjectOnlyTerm => "claim-subject-only-term",
            Self::ConstantNotGround => "constant-not-ground",
            Self::FragmentInInitializer => "fragment-in-initializer",
            Self::LetOutsideTerm => "let-outside-term",
            Self::MatchesOutsideCondition => "matches-outside-condition",
            Self::OpenRecordInAliasSubject => "open-record-in-alias-subject",
            Self::OpenRecordOutsidePattern => "open-record-outside-pattern",
            Self::MlInInitializer => "ml-in-initializer",
            Self::MlPredicateAsTerm => "ml-predicate-as-term",
            Self::RecordRemainderInCellsTerm => "record-remainder-in-cells-term",
            Self::RecordRemainderInInitializer => "record-remainder-in-initializer",
            Self::RecordUpdateInPattern => "record-update-in-pattern",
            Self::RestInAliasSubject => "rest-in-alias-subject",
            Self::RewriteInMapKey => "rewrite-in-map-key",
            Self::RewriteOutsideLocalRule => "rewrite-outside-local-rule",
            Self::SortTestInPattern => "sort-test-in-pattern",
            Self::WildcardInAliasSubject => "wildcard-in-alias-subject",
            Self::WildcardOutsidePattern => "wildcard-outside-pattern",
        }
    }

    /// The class's one registered code.
    #[must_use]
    pub const fn code(self) -> Code {
        match self {
            Self::AliasInAliasSubject
            | Self::AlternativesInAliasSubject
            | Self::OpenRecordInAliasSubject
            | Self::RestInAliasSubject
            | Self::WildcardInAliasSubject => codes::expand::IRREVERSIBLE_ALIAS,
            Self::AliasInLetPattern | Self::AlternativesInLetPattern => codes::syntax::INVALID_LET,
            Self::AliasOutsidePattern => codes::syntax::INVALID_PATTERN_AS,
            Self::AlternativesInOneTermRewrite => codes::analysis::INVALID_PATTERN_OR,
            Self::ClaimOnlyTerm => codes::expand::CLAIM_ONLY_TERM,
            Self::ClaimSubjectOnlyTerm => codes::expand::CLAIM_SUBJECT_ONLY_TERM,
            Self::ConstantNotGround => codes::syntax::INVALID_CONSTANT,
            Self::FragmentInInitializer => codes::expand::INITIALIZER_FRAGMENT,
            Self::LetOutsideTerm => codes::expand::LET_OUTSIDE_TERM,
            Self::MatchesOutsideCondition => codes::expand::MATCHES_OUTSIDE_CONDITION,
            Self::MlInInitializer => codes::expand::ML_PLACEMENT,
            Self::MlPredicateAsTerm => codes::analysis::INVALID_ML_PREDICATE,
            Self::RecordRemainderInCellsTerm => codes::analysis::INVALID_RECORD_UPDATE,
            Self::RecordRemainderInInitializer => codes::expand::INITIALIZER_RECORD_UPDATE,
            Self::RecordUpdateInPattern | Self::OpenRecordOutsidePattern => {
                codes::syntax::INVALID_RECORD_UPDATE
            }
            Self::RewriteInMapKey | Self::RewriteOutsideLocalRule => {
                codes::syntax::INVALID_LOCAL_REWRITE
            }
            Self::SortTestInPattern => codes::analysis::INVALID_SORT_TEST,
            Self::WildcardOutsidePattern => codes::syntax::UNSUPPORTED_TERM_EXPRESSION,
        }
    }

    /// What the construct means, which is why the position cannot hold it; a refusal's message
    /// is this followed by the position.
    #[must_use]
    pub const fn summary(self) -> &'static str {
        match self {
            Self::AliasInAliasSubject => {
                "an alias clause also runs backwards: when a result is printed, each term its result matches prints as its subject, built from what the match bound, and `name @ pattern` (K's #as) is a test of the term's shape, which building cannot make: it prints as the conjunction `term #And pattern`, no term, and for a term the pattern does not match, as an alias that does not expand back to it; write `#[k::desugar]` for an expansion that runs one way"
            }
            Self::AliasInLetPattern => {
                "a `let` pattern destructures one value, which a bare name already names whole: write `let p = e; let P = p;` for `p @ P`"
            }
            Self::AliasOutsidePattern => {
                "`name @ pattern` (K's #as) names the term a pattern matched, so it stands only where a sentence matches: a subject, or a `k::matches!` pattern in a condition; a single-body rule's subject outside its `k::rewrite!` islands is kept as it is, as a context's and a context alias's are around their hole, and a result only builds"
            }
            Self::AlternativesInAliasSubject => {
                "an alias clause also runs backwards: when a result is printed, each term its result matches prints as its subject, built from what the match bound, and `A | B` (K's #Or) denotes no one term: it prints as the disjunction `A #Or B`; write one alias clause per alternative, each with the result, or `#[k::desugar]` for an expansion that runs one way"
            }
            Self::AlternativesInLetPattern => {
                "a `let` reads its value by one pattern, whose names the rest of its block uses: test which shape a value has with `k::matches!`, or match each shape in a sentence of its own"
            }
            Self::AlternativesInOneTermRewrite => {
                "`A | B` (K's #Or) matches one of several terms, and a subject rewritten as one term in place stands for the one term it matched: write one sentence per alternative"
            }
            Self::ClaimOnlyTerm => {
                "`k::or_bool!` joins a claim's symbolic conditions, so it stands only in a claim"
            }
            Self::ClaimSubjectOnlyTerm => {
                "`k::anonymous!` is a value nothing determines, which only a claim's start state may hold"
            }
            Self::ConstantNotGround => {
                "a constant's value is a ground constructor term, a value a pattern can match and nothing about it depends on evaluation or a match"
            }
            Self::FragmentInInitializer => {
                "`k::fragment!` names a nested cell term, and an initializer builds its nested cells with their structs"
            }
            Self::LetOutsideTerm => {
                "a `let` block (K's #let) computes a term, the application `#fun(P => B)(E)` of a function generated for that block, and no term a pattern meets is an application of it, so a pattern holding one never matches: it stands where a term is built or a condition computed, in a claim's start state, which is a term, and in a key, a set's element or a Set collection's instance that a pattern over evaluated terms computes from names it binds elsewhere and looks up, never where a key selects an entry by matching; write the block in a rule's or an equation's result or condition, a fn body, or an initializer"
            }
            Self::MatchesOutsideCondition => {
                "`k::matches!` (K's :=K) computes a Bool by matching a term, the application of a function generated for that test, and no term a pattern meets is an application of it, so a pattern holding one never matches: it stands where a term is built or a condition computed, in a claim's start state, which is a term, and in a key, a set's element or a Set collection's instance that a pattern over evaluated terms computes from names it binds elsewhere and looks up, never where a key selects an entry by matching; write the test in a rule's or an equation's result or condition, a fn body, or an initializer"
            }
            Self::MlInInitializer => {
                "a matching-logic predicate states a property of a symbolic state, and an initializer builds one concrete state"
            }
            Self::MlPredicateAsTerm => {
                "a matching-logic predicate is a formula about terms, no term itself, so a pattern cannot match it"
            }
            Self::OpenRecordInAliasSubject => {
                "an alias clause also runs backwards: when a result is printed, each term its result matches prints as its subject, built from what the match bound, and the fields `..` leaves open have no value from that match: they print as variables (`_Krs_Wildcard0`); name every field and use it in the result, or write `#[k::desugar]` for an expansion that runs one way"
            }
            Self::OpenRecordOutsidePattern => {
                "`..` stands only in a pattern, where it leaves the fields the record does not name unconstrained; a built term names every field of the record it builds, so it holds no `..`, even with every field named"
            }
            Self::RecordRemainderInCellsTerm => {
                "a `cells!` term, the reference notation, names every field of a record, `_` for one a pattern leaves unconstrained, and only a pattern's group record leaves its other children open (`k::fragment![G { c: e, .. }]`); `..base` and `..` are readable-record notation"
            }
            Self::RecordRemainderInInitializer => {
                "`..` leaves a record's other fields open, which only a pattern can: an initializer builds its record, which has no value for them, so name every field, or write `..base` to take them from the record `base`"
            }
            Self::RecordUpdateInPattern => {
                "`..base` builds a record whose unlisted fields are those of the record the alias `base` matched, which only a term a sentence builds can say; a pattern denotes no record by it, and leaves out the fields it does not constrain with `..`"
            }
            Self::RestInAliasSubject => {
                "an alias clause also runs backwards: when a result is printed, each term its result matches prints as its subject, built from what the match bound, and the elements an anonymous `..` leaves unnamed have no value from that match: they print as a variable (`_Krs_Wildcard0`); a list of an element and a rest is moreover one spelling of the list, which static expansion matches as written: name the whole list and use the name in the result"
            }
            Self::RewriteInMapKey => {
                "a map key is what the map is looked up by, as a set's element is what the set is, and a rewrite there would move the entry to another key, or replace the element by another, a removal and an insertion that may meet a key or an element the collection already holds: a rewrite in a map changes a value, `key -> k::rewrite!(old => new)`, and a rule with a result moves an entry with `map::remove` and `map::update`"
            }
            Self::RewriteOutsideLocalRule => {
                "`k::rewrite!` (K's local =>) marks what changes inside the subject of a single-body rule or the hole of a context, once and outside any local pattern"
            }
            Self::SortTestInPattern => {
                "`k::is!` and `k::project!` compute from a term, and a pattern matches terms as they are: restrict a binder's sort with a typed parameter or `where x: Sort` instead"
            }
            Self::WildcardInAliasSubject => {
                "an alias clause also runs backwards: when a result is printed, each term its result matches prints as its subject, built from what the match bound, and `_` names no term the match gives a value: it prints as a variable (`_Krs_Wildcard0`) where the term stood; name the term and use the name in the result, or write `#[k::desugar]` for an expansion that runs one way"
            }
            Self::WildcardOutsidePattern => {
                "`_` matches any term, so it stands only in a pattern; a result, a condition and an initializer build a term, which `_` does not name"
            }
        }
    }

    /// The message of a refusal of this class at `position`.
    #[must_use]
    pub fn message(self, position: Position) -> String {
        let summary = match (self, position.form, position.slot) {
            // A context's subject is matched by heating, and so `y` would name a term its guard
            // can read; what refuses `#as` is the way back, the frame cooling builds.
            (Self::AliasOutsidePattern, Form::Context, Slot::Subject) => {
                "`name @ pattern` (K's #as) names the term a pattern matched, but a context's subject is the frame that heating matches and cooling puts back around the hole, and `#as` cannot stand in the term cooling builds, so the name has no term to stand for there; write the term as a bare name and its shape as a test in the context's guard: `#[k::requires(k::matches!(y, P))]`"
            }
            (Self::AliasOutsidePattern, Form::ContextAlias, Slot::Subject) => {
                "`name @ pattern` (K's #as) names the term a pattern matched, but a context alias's pattern is the frame of every context it makes, which heating matches and cooling puts back around `here`, and `#as` cannot stand in the term cooling builds, so the name has no term to stand for there; an alias states no guard, and its pattern alone matches the same terms"
            }
            _ => self.summary(),
        };
        format!("{summary}; here it stands in {position}")
    }
}

/// A decision the compiler makes after resolution or sort inference: the class-test class of
/// the same name.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Rule {
    /// `alternatives-outside-pattern`: outside a pattern, `A | B` is the bitwise operator, whose
    /// operand sorts choose its domain.
    AlternativesOutsidePattern,
    /// `constant-applies-function`: whether an application in a constant's value applies a
    /// function.
    ConstantAppliesFunction,
    /// `let-outside-term`: whether a key a pattern computes that holds a `let` block selects an
    /// entry instead, by a name nothing else binds, and whether a braced instance's cell holding
    /// one is a Map collection's, which the pattern matches, rather than a Set collection's,
    /// which it looks up.
    LetOutsideTerm,
    /// `matches-outside-condition`: [`Self::LetOutsideTerm`]'s decision for `k::matches!`.
    MatchesOutsideCondition,
    /// `function-in-pattern`: whether an application where a pattern matches a term applies a
    /// function, and, at an equation's slot root, whether that root is the subject's. In a
    /// static clause's subject the compiler also tells a collection of two or more parts by its
    /// head (`collection-in-static-subject`), which static expansion matches in one spelling,
    /// and an application of a static production its expansion cannot rewrite
    /// (`unexpandable-static-application`).
    FunctionInPattern,
    /// `ml-in-condition`: a matching-logic predicate in the condition of a transition or an
    /// equation, which the compiler recognizes for every connective alike.
    MlInCondition,
    /// `ml-predicate-as-term`: whether a predicate in a built term is an operand of an object
    /// term.
    MlPredicateAsTerm,
    /// `record-update-in-pattern`: whether a record update in a braced collection instance
    /// stands in a Set collection's instance a pattern looks up.
    RecordUpdateInPattern,
    /// `record-remainder-in-cells-term`: whether a record's `..` or `..base` in a `cells!` value
    /// closes a group record, a cell's entry, which the entry's admission judges as it judges a
    /// fragment's, or a constructor's record, which a `cells!` term writes whole.
    RecordRemainderInCellsTerm,
    /// `sort-test-in-pattern`: whether a sort test in a key over evaluated terms stands in a key
    /// that selects an entry by matching, and one in a braced collection instance in a Set
    /// collection's instance a pattern looks up.
    SortTestInPattern,
}

impl Rule {
    /// Every rule.
    pub const ALL: [Self; 10] = [
        Self::AlternativesOutsidePattern,
        Self::ConstantAppliesFunction,
        Self::LetOutsideTerm,
        Self::MatchesOutsideCondition,
        Self::FunctionInPattern,
        Self::MlInCondition,
        Self::MlPredicateAsTerm,
        Self::RecordUpdateInPattern,
        Self::RecordRemainderInCellsTerm,
        Self::SortTestInPattern,
    ];

    /// The class's name in `expected.toml`.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::AlternativesOutsidePattern => "alternatives-outside-pattern",
            Self::ConstantAppliesFunction => "constant-applies-function",
            Self::LetOutsideTerm => "let-outside-term",
            Self::MatchesOutsideCondition => "matches-outside-condition",
            Self::FunctionInPattern => "function-in-pattern",
            Self::MlInCondition => "ml-in-condition",
            Self::MlPredicateAsTerm => "ml-predicate-as-term",
            Self::RecordUpdateInPattern => "record-update-in-pattern",
            Self::RecordRemainderInCellsTerm => "record-remainder-in-cells-term",
            Self::SortTestInPattern => "sort-test-in-pattern",
        }
    }
}

/// Whether `construct` may stand at `position`.
#[must_use]
#[expect(
    clippy::too_many_lines,
    reason = "One match over the closed construct set; each arm is the construct's rows."
)]
pub const fn admits(position: Position, construct: Construct) -> Admission {
    use Admission::{Admit, After, Refuse};
    match position.form {
        Form::Constant => return constant_value(construct),
        Form::Initializer => {
            if let Some(admission) = initializer_value(position, construct) {
                return admission;
            }
        }
        _ => {}
    }
    let form = position.form;
    let nesting = position.nesting;
    let pattern = position.is_pattern();
    let looked_up = position.is_looked_up();
    let in_pattern_key = matches!(position.slot, Slot::Subject) && nesting.in_map_key;
    // An alias clause's subject is also built, from what the clause's result matched in a
    // printed term: what only matches cannot be built there.
    let built_backwards = position.is_built_backwards();
    match construct {
        // `_` names no term; a desugar clause's result lists it in `unbound_variables`, where it
        // is K's anonymous variable of the rewritten program.
        Construct::Wildcard => {
            if built_backwards {
                Refuse(Class::WildcardInAliasSubject)
            } else if pattern || matches!((form, position.slot), (Form::Desugar, Slot::Result)) {
                Admit
            } else {
                Refuse(Class::WildcardOutsidePattern)
            }
        }
        Construct::As => {
            if nesting.in_matches_pattern {
                // A `k::matches!` in a condition is part of the matching that decides whether
                // the sentence applies; in a result or an initializer it is a test of the built
                // term. In a key a pattern computes, the test is a function of the names the key
                // reads, whose equations state it in their conditions, where `name @ pattern`
                // means what it means in any condition.
                if matches!(position.slot, Slot::Result | Slot::InitializerValue) {
                    Refuse(Class::AliasOutsidePattern)
                } else {
                    Admit
                }
            } else if nesting.in_let_pattern {
                Refuse(Class::AliasInLetPattern)
            } else if built_backwards {
                Refuse(Class::AliasInAliasSubject)
            } else if pattern {
                if form.keeps_subject() && !nesting.in_rewrite {
                    Refuse(Class::AliasOutsidePattern)
                } else {
                    Admit
                }
            } else {
                Refuse(Class::AliasOutsidePattern)
            }
        }
        // Alternatives match one of several terms; a subject rewritten in place as one term
        // stands for the one term it matched, an alias's subject is built as one term, and a
        // `let` reads its value by one shape. Outside a pattern `A | B` is the bitwise operator.
        Construct::Or => {
            if built_backwards {
                Refuse(Class::AlternativesInAliasSubject)
            } else if pattern && !position.in_local_pattern() && form.rewrites_one_term() {
                Refuse(Class::AlternativesInOneTermRewrite)
            } else if nesting.in_let_pattern {
                Refuse(Class::AlternativesInLetPattern)
            } else if pattern {
                Admit
            } else {
                After(Rule::AlternativesOutsidePattern)
            }
        }
        // `k::matches!` tests and `let` computes, each by applying a function generated for it
        // alone, which no term holds: a pattern, which matches terms as they are, never meets
        // one. A claim's states hold applications, which denote their values, so its start state
        // holds either, as its end state and conditions do; KRS lifts a claim's into functions the
        // definition declares, since the provers lower them only in a definition's sentences
        // (NT-15). Both notations write the same sentences, so a `cells!` cell value holds what
        // the same place of a readable sentence does: a result's is built, a claim's start
        // state is a term, and a Set collection's instance a pattern looks up is computed as a
        // key is; every other place of a `cells!` subject is a pattern. A key a pattern over
        // evaluated terms looks up is computed from names the pattern binds elsewhere and looked
        // up, so it holds either, as it holds a function's application: the value is a function
        // of those names, which KRS lifts into a function of its own and applies there, so no
        // binder of the construct stands in the sentence's left side. Below `@` or `|` a key
        // selects an entry by matching the map's keys, which are evaluated values, and holds
        // neither; a pattern that meets unevaluated terms (a simplification's, a static clause's)
        // would match a key that is the generated function's application, which no term holds.
        Construct::Matches | Construct::Let => {
            let outside = if matches!(construct, Construct::Matches) {
                Class::MatchesOutsideCondition
            } else {
                Class::LetOutsideTerm
            };
            let key_computed = in_pattern_key
                && !nesting.in_selected_key
                && (form.matches_evaluated_terms() || form.is_claim());
            // A braced instance's cell is looked up in a Set collection, as a key is, and matched
            // in a Map collection's, which only the cell's declared type tells: the compiler
            // refuses one in a matched instance.
            let after = if matches!(construct, Construct::Matches) {
                Rule::MatchesOutsideCondition
            } else {
                Rule::LetOutsideTerm
            };
            if position.in_local_pattern()
                || (in_pattern_key && !key_computed)
                || (pattern
                    && !form.is_claim()
                    && !key_computed
                    && !position.reads_by_collection_type())
            {
                Refuse(outside)
            } else if (key_computed && form.matches_evaluated_terms())
                || position.reads_by_collection_type()
            {
                After(after)
            } else {
                Admit
            }
        }
        // A predicate is a formula about terms. A pattern matches terms, so it holds none; in a
        // built term or a condition, whether the predicate is the condition or an operand of an
        // object term is the compiler's to see, since it recognizes every connective alike.
        Construct::MlPredicate => match position.slot {
            _ if pattern => Refuse(Class::MlPredicateAsTerm),
            Slot::Requires | Slot::Ensures if !form.admits_predicate_conditions() => {
                After(Rule::MlInCondition)
            }
            _ => After(Rule::MlPredicateAsTerm),
        },
        // A rewrite marks what changes inside a single-body rule's subject, where a map changes
        // values: its keys are what it is looked up by, and so are a set's elements.
        Construct::Rewrite => {
            if !matches!(position.slot, Slot::Subject)
                || !form.rewrites_inside_subject()
                || nesting.in_rewrite
                || position.in_local_pattern()
            {
                Refuse(Class::RewriteOutsideLocalRule)
            } else if nesting.in_map_key {
                Refuse(Class::RewriteInMapKey)
            } else {
                Admit
            }
        }
        // A sort test applies the sort's generated predicate or projection, a function: a pattern
        // over evaluated terms never meets it, a static clause's subject would match its spelling
        // rather than its value, while a simplification's and a claim's subjects hold
        // applications, and a key computes it.
        // In a key over evaluated terms, whether the whole key is computed or selects an entry
        // by matching takes its names: the compiler decides. So does a braced collection
        // instance's type and names.
        Construct::SortTest => {
            if position.reads_by_collection_type() {
                After(Rule::SortTestInPattern)
            } else if position.matches_terms_as_written()
                || (position.matches_evaluated_terms() && !looked_up)
            {
                Refuse(Class::SortTestInPattern)
            } else if in_pattern_key && form.matches_evaluated_terms() {
                After(Rule::SortTestInPattern)
            } else {
                Admit
            }
        }
        // A claim's start state may hold values nothing determines, and its conditions may be
        // disjunctions of symbolic conditions; no other sentence quantifies over its state.
        Construct::Anonymous => {
            if form.is_claim() && matches!(position.slot, Slot::Subject) && !nesting.in_computed_key
            {
                Admit
            } else {
                Refuse(Class::ClaimSubjectOnlyTerm)
            }
        }
        Construct::OrBool => {
            if form.is_claim() {
                Admit
            } else {
                Refuse(Class::ClaimOnlyTerm)
            }
        }
        // `..base` takes the fields an update leaves out from a matched record, which a built
        // term can do and a pattern cannot: it matches records and leaves fields out with `..`.
        // A Set collection's instance a pattern looks up computes it, as a key does. Where a
        // `cells!` value is built, only the record's head tells a group record, a cell's entry
        // (ruling R4) whose update the entry's admission judges, from a constructor's record,
        // which a `cells!` term writes whole ([`Rule::RecordRemainderInCellsTerm`]); where it
        // matches, `..base` denotes no record of either, so the head is not needed.
        Construct::RecordUpdate => {
            if cells_value(position)
                && matches!(position.slot, Slot::Result)
                && !position.in_local_pattern()
            {
                After(Rule::RecordRemainderInCellsTerm)
            } else if cells_value(position) {
                Refuse(Class::RecordRemainderInCellsTerm)
            } else if position.reads_by_collection_type() {
                After(Rule::RecordUpdateInPattern)
            } else if pattern && !looked_up {
                Refuse(Class::RecordUpdateInPattern)
            } else {
                Admit
            }
        }
        // Outside a pattern the record is built, and `..` names no value for the fields it
        // leaves open: a condition, a result, a rewrite's right side, and below a construct a key
        // computes; so is an alias's subject, from a match that gives them none. A readable
        // record's result also creates cell instances, whose `..` gives the other cells their
        // defaults, and only resolution tells an instance's record from a constructor's there.
        // A group record's `..` in a `cells!` pattern leaves the group's other children
        // unconstrained, as a pattern's open record leaves its other fields (records follow
        // Rust): its children are the group's entries, and K frames the ones it leaves out. A
        // `cells!` result builds the group, which has no value for them; elsewhere it is an open
        // record. A record `G { c: e, .. }` written inside a `cells!` value without `k::fragment!`
        // is a group record when its head is a group's struct, and then a cell's entry as a
        // fragment's child is (ruling R4), which the entry's admission judges by the group's
        // children; only resolution tells it from a constructor's record, which a `cells!` term
        // writes whole ([`Rule::RecordRemainderInCellsTerm`]).
        Construct::OpenFragment if cells_value(position) && pattern => Admit,
        Construct::OpenRecord if cells_value(position) => After(Rule::RecordRemainderInCellsTerm),
        Construct::OpenRecord | Construct::OpenFragment => {
            if cells_value(position) {
                Refuse(Class::RecordRemainderInCellsTerm)
            } else if built_backwards {
                Refuse(Class::OpenRecordInAliasSubject)
            } else if pattern || (matches!(position.slot, Slot::Result) && form.creates_instances())
            {
                Admit
            } else {
                Refuse(Class::OpenRecordOutsidePattern)
            }
        }
        // A list pattern's anonymous rest stands for the elements it leaves unnamed, which an
        // alias's subject, built from what its result matched, has no value for.
        Construct::Rest => {
            if built_backwards {
                Refuse(Class::RestInAliasSubject)
            } else {
                Admit
            }
        }
        // A rule's, an equation's and a context's pattern matches terms with their functions
        // evaluated, and so does a local pattern, which matches a value a rule computed: an
        // application where a pattern matches a term, at a slot's root as below it, in a map's
        // value or a list's element as in a constructor's field, matches only if it is a
        // constructor's, which resolution decides. The root of an equation's subject is the
        // function it defines, which the compiler tells from the root of a function-context cell;
        // a simplification's and a claim's subjects hold unevaluated applications. A key is
        // computed and looked up, and the application with it, when nothing in it outside the
        // constructs that compute selects an entry by matching (a name nothing else binds, `_`, an
        // alias, alternatives, an open record); otherwise it is matched: that takes the key's
        // names, and a set's element is told by its head, so the compiler decides both. A static
        // clause's subject is matched against a program as written, where a function's
        // application would stand for its spelling, a key's or a set element's too, since nothing
        // is looked up there (decision NT-11-5); the compiler tells a function from a
        // constructor, and a collection of two or more parts, which static expansion matches in
        // one of its spellings, by its head.
        Construct::FunctionApplication => {
            if position.matches_evaluated_terms()
                || position.matches_terms_as_written()
                || (in_pattern_key && form.matches_evaluated_terms())
            {
                After(Rule::FunctionInPattern)
            } else {
                Admit
            }
        }
        Construct::Fragment
        | Construct::Turbofish
        | Construct::IdToken
        | Construct::BytesToken
        | Construct::Lexeme
        | Construct::Literal => Admit,
    }
}

/// Whether `position` is a `cells!` cell value, the reference notation, outside its conditions.
const fn cells_value(position: Position) -> bool {
    position.form.writes_cells() && matches!(position.slot, Slot::Subject | Slot::Result)
}

/// A constant's value: a ground constructor term, with literals and the token islands, each of
/// which denotes one constant of its sort.
const fn constant_value(construct: Construct) -> Admission {
    match construct {
        Construct::Literal
        | Construct::IdToken
        | Construct::BytesToken
        | Construct::Lexeme
        | Construct::Turbofish => Admission::Admit,
        Construct::FunctionApplication => Admission::After(Rule::ConstantAppliesFunction),
        Construct::Wildcard
        | Construct::As
        | Construct::Or
        | Construct::Matches
        | Construct::Let
        | Construct::MlPredicate
        | Construct::Rewrite
        | Construct::SortTest
        | Construct::Anonymous
        | Construct::OrBool
        | Construct::Fragment
        | Construct::RecordUpdate
        | Construct::OpenRecord
        | Construct::OpenFragment
        | Construct::Rest => Admission::Refuse(Class::ConstantNotGround),
    }
}

/// An initializer's value: the concrete initial content of a cell, built from constants and
/// configuration variables, its functions evaluated when the configuration is built. It is a
/// built term as a result is, read by the same rows, `let` blocks, `k::matches!`, sort tests,
/// turbofish instances and record updates included, with three exceptions: a matching-logic
/// predicate states a property of a symbolic state, where an initializer builds one concrete
/// state; `k::fragment!` names a nested cell term, where an initializer builds nested cells
/// with their structs; and an open record leaves fields open, which only a pattern can, so it
/// is refused outside a local pattern.
const fn initializer_value(position: Position, construct: Construct) -> Option<Admission> {
    use Admission::Refuse;
    match construct {
        Construct::Fragment => Some(Refuse(Class::FragmentInInitializer)),
        Construct::MlPredicate if !position.in_local_pattern() => {
            Some(Refuse(Class::MlInInitializer))
        }
        Construct::OpenRecord | Construct::OpenFragment if !position.in_local_pattern() => {
            Some(Refuse(Class::RecordRemainderInInitializer))
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests;
