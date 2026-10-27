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
//! single-body rule's subject is matched and kept, except inside its `k::rewrite!` islands.

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
    /// A `#[k::alias]` fn.
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

    /// Whether the form is a single-body rule, whose subject is kept as it is outside its
    /// `k::rewrite!` islands.
    const fn is_single_body(self) -> bool {
        matches!(self, Self::LocalRule | Self::CellsLocalRule)
    }

    /// Whether the form's subject is rewritten in place as one term: a single-body rule's and a
    /// simplification's.
    const fn rewrites_one_term(self) -> bool {
        matches!(
            self,
            Self::LocalRule | Self::CellsLocalRule | Self::Simplification
        )
    }

    /// Whether the form's subject marks what changes with `k::rewrite!`: a single-body rule's,
    /// and a context's, which rewrites its hole.
    const fn rewrites_inside_subject(self) -> bool {
        matches!(self, Self::LocalRule | Self::CellsLocalRule | Self::Context)
    }

    /// Whether the form's subject is the pattern of a rewrite rule or an equation, which every
    /// term it applies to matches with its functions evaluated.
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
    /// The construct is below the slot's root term.
    pub below_root: bool,
    /// Inside the pattern of a `k::matches!`.
    pub in_matches_pattern: bool,
    /// Inside the pattern of a `let` statement.
    pub in_let_pattern: bool,
    /// Inside a `k::rewrite!`.
    pub in_rewrite: bool,
    /// Inside a key, value or element of a collection (a readable map read's key, a List cell's
    /// element).
    pub in_collection_entry: bool,
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
                below_root: false,
                in_matches_pattern: false,
                in_let_pattern: false,
                in_rewrite: false,
                in_collection_entry: false,
            },
        }
    }

    /// Whether the construct is matched against a term: the form's subject, or a local pattern.
    #[must_use]
    pub const fn is_pattern(self) -> bool {
        matches!(self.slot, Slot::Subject) || self.in_local_pattern()
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
        } else if self.nesting.in_rewrite {
            formatter.write_str("a `k::rewrite!` in ")?;
        }
        write!(formatter, "{} of {}", self.slot.noun(), self.form.noun())
    }
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
    pub const ALL: [Self; 19] = [
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
    /// `alias-outside-pattern`.
    AliasOutsidePattern,
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
    /// `ml-in-initializer`.
    MlInInitializer,
    /// `ml-predicate-as-term`.
    MlPredicateAsTerm,
    /// `record-remainder-in-cells-term`.
    RecordRemainderInCellsTerm,
    /// `record-remainder-in-initializer`.
    RecordRemainderInInitializer,
    /// `rewrite-outside-local-rule`.
    RewriteOutsideLocalRule,
    /// `rule-term-in-initializer`.
    RuleTermInInitializer,
    /// `sort-test-in-pattern`.
    SortTestInPattern,
    /// `turbofish-in-initializer`.
    TurbofishInInitializer,
    /// `wildcard-outside-pattern`.
    WildcardOutsidePattern,
}

impl Class {
    /// Every class.
    pub const ALL: [Self; 17] = [
        Self::AliasOutsidePattern,
        Self::AlternativesInOneTermRewrite,
        Self::ClaimOnlyTerm,
        Self::ClaimSubjectOnlyTerm,
        Self::ConstantNotGround,
        Self::FragmentInInitializer,
        Self::LetOutsideTerm,
        Self::MatchesOutsideCondition,
        Self::MlInInitializer,
        Self::MlPredicateAsTerm,
        Self::RecordRemainderInCellsTerm,
        Self::RecordRemainderInInitializer,
        Self::RewriteOutsideLocalRule,
        Self::RuleTermInInitializer,
        Self::SortTestInPattern,
        Self::TurbofishInInitializer,
        Self::WildcardOutsidePattern,
    ];

    /// The class's name in `expected.toml`.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::AliasOutsidePattern => "alias-outside-pattern",
            Self::AlternativesInOneTermRewrite => "alternatives-in-one-term-rewrite",
            Self::ClaimOnlyTerm => "claim-only-term",
            Self::ClaimSubjectOnlyTerm => "claim-subject-only-term",
            Self::ConstantNotGround => "constant-not-ground",
            Self::FragmentInInitializer => "fragment-in-initializer",
            Self::LetOutsideTerm => "let-outside-term",
            Self::MatchesOutsideCondition => "matches-outside-condition",
            Self::MlInInitializer => "ml-in-initializer",
            Self::MlPredicateAsTerm => "ml-predicate-as-term",
            Self::RecordRemainderInCellsTerm => "record-remainder-in-cells-term",
            Self::RecordRemainderInInitializer => "record-remainder-in-initializer",
            Self::RewriteOutsideLocalRule => "rewrite-outside-local-rule",
            Self::RuleTermInInitializer => "rule-term-in-initializer",
            Self::SortTestInPattern => "sort-test-in-pattern",
            Self::TurbofishInInitializer => "turbofish-in-initializer",
            Self::WildcardOutsidePattern => "wildcard-outside-pattern",
        }
    }

    /// The class's one registered code.
    #[must_use]
    pub const fn code(self) -> Code {
        match self {
            Self::AliasOutsidePattern => codes::syntax::INVALID_PATTERN_AS,
            Self::AlternativesInOneTermRewrite => codes::analysis::INVALID_PATTERN_OR,
            Self::ClaimOnlyTerm | Self::RuleTermInInitializer => codes::expand::CLAIM_ONLY_TERM,
            Self::ClaimSubjectOnlyTerm => codes::expand::CLAIM_SUBJECT_ONLY_TERM,
            Self::ConstantNotGround => codes::syntax::INVALID_CONSTANT,
            Self::FragmentInInitializer => codes::expand::INITIALIZER_FRAGMENT,
            Self::LetOutsideTerm => codes::expand::LET_OUTSIDE_TERM,
            Self::MatchesOutsideCondition => codes::expand::MATCHES_OUTSIDE_CONDITION,
            Self::MlInInitializer => codes::expand::ML_PLACEMENT,
            Self::MlPredicateAsTerm => codes::analysis::INVALID_ML_PREDICATE,
            Self::RecordRemainderInCellsTerm => codes::analysis::INVALID_RECORD_UPDATE,
            Self::RecordRemainderInInitializer => codes::expand::INITIALIZER_RECORD_UPDATE,
            Self::RewriteOutsideLocalRule => codes::syntax::INVALID_LOCAL_REWRITE,
            Self::SortTestInPattern => codes::analysis::INVALID_SORT_TEST,
            Self::TurbofishInInitializer => codes::expand::TURBOFISH_PLACEMENT,
            Self::WildcardOutsidePattern => codes::syntax::UNSUPPORTED_TERM_EXPRESSION,
        }
    }

    /// What the construct means, which is why the position cannot hold it; a refusal's message
    /// is this followed by the position.
    #[must_use]
    pub const fn summary(self) -> &'static str {
        match self {
            Self::AliasOutsidePattern => {
                "`name @ pattern` (K's #as) names the term a pattern matched, so it stands only where a sentence matches: a subject, a `let` pattern, or a `k::matches!` pattern in a condition; a single-body rule's subject outside its `k::rewrite!` islands is kept as it is, and a result only builds"
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
                "a `let` block (K's #let) computes a term from values the sentence has bound, so it stands in a result or a condition of a rule, never in a pattern, an initializer or a claim"
            }
            Self::MatchesOutsideCondition => {
                "`k::matches!` (K's :=K) is a Bool test of a bound term, so it stands in a result or a condition of a rule, never in a pattern, an initializer or a claim"
            }
            Self::MlInInitializer => {
                "a matching-logic predicate states a property of a symbolic state, and an initializer builds one concrete state"
            }
            Self::MlPredicateAsTerm => {
                "a matching-logic predicate is a formula about terms, no term itself, so a pattern cannot match it"
            }
            Self::RecordRemainderInCellsTerm => {
                "a `cells!` term, the reference notation, names every field of a record; `..base` and `..` are readable-record notation"
            }
            Self::RecordRemainderInInitializer => {
                "an initializer term names every field of a record: `..base` takes fields from a matched record and `..` leaves them open, and an initializer matches nothing"
            }
            Self::RewriteOutsideLocalRule => {
                "`k::rewrite!` (K's local =>) marks what changes inside the subject of a single-body rule or the hole of a context, once and outside any local pattern"
            }
            Self::RuleTermInInitializer => {
                "`k::is!` and `k::project!` test and narrow a term a rule or claim matched, and an initializer matches nothing"
            }
            Self::SortTestInPattern => {
                "`k::is!` and `k::project!` compute from a term, and a pattern matches terms as they are: restrict a binder's sort with a typed parameter or `where x: Sort` instead"
            }
            Self::TurbofishInInitializer => {
                "a turbofish instance chooses a parametric production's instance, and an initializer builds concrete values, whose syntax numbers no instance"
            }
            Self::WildcardOutsidePattern => {
                "`_` matches any term, so it stands only in a pattern; a result, a condition and an initializer build a term, which `_` does not name"
            }
        }
    }

    /// The message of a refusal of this class at `position`.
    #[must_use]
    pub fn message(self, position: Position) -> String {
        format!("{}; here it stands in {position}", self.summary())
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
    /// `function-in-pattern`: whether an application below a pattern's root applies a function.
    FunctionInPattern,
    /// `ml-in-condition`: a matching-logic predicate in the condition of a transition or an
    /// equation, which the compiler recognizes for every connective alike.
    MlInCondition,
    /// `ml-predicate-as-term`: whether a predicate in a built term is an operand of an object
    /// term.
    MlPredicateAsTerm,
}

impl Rule {
    /// Every rule.
    pub const ALL: [Self; 5] = [
        Self::AlternativesOutsidePattern,
        Self::ConstantAppliesFunction,
        Self::FunctionInPattern,
        Self::MlInCondition,
        Self::MlPredicateAsTerm,
    ];

    /// The class's name in `expected.toml`.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::AlternativesOutsidePattern => "alternatives-outside-pattern",
            Self::ConstantAppliesFunction => "constant-applies-function",
            Self::FunctionInPattern => "function-in-pattern",
            Self::MlInCondition => "ml-in-condition",
            Self::MlPredicateAsTerm => "ml-predicate-as-term",
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
        Form::Initializer => return initializer_value(construct),
        _ => {}
    }
    let form = position.form;
    let nesting = position.nesting;
    let pattern = position.is_pattern();
    match construct {
        // `_` names no term; a desugar clause's result lists it in `unbound_variables`, where it
        // is K's anonymous variable of the rewritten program.
        Construct::Wildcard => {
            if pattern || matches!((form, position.slot), (Form::Desugar, Slot::Result)) {
                Admit
            } else {
                Refuse(Class::WildcardOutsidePattern)
            }
        }
        Construct::As => {
            if nesting.in_matches_pattern {
                // A `k::matches!` in a condition is part of the matching that decides whether
                // the sentence applies; in a result it is a test of the built term.
                if matches!(position.slot, Slot::Result) {
                    Refuse(Class::AliasOutsidePattern)
                } else {
                    Admit
                }
            } else if nesting.in_let_pattern {
                Admit
            } else if matches!(position.slot, Slot::Subject) {
                if form.is_single_body() && !nesting.in_rewrite {
                    Refuse(Class::AliasOutsidePattern)
                } else {
                    Admit
                }
            } else {
                Refuse(Class::AliasOutsidePattern)
            }
        }
        // Alternatives match one of several terms; a subject rewritten in place as one term
        // stands for the one term it matched. Outside a pattern `A | B` is the bitwise operator.
        Construct::Or => {
            if matches!(position.slot, Slot::Subject)
                && !position.in_local_pattern()
                && form.rewrites_one_term()
            {
                Refuse(Class::AlternativesInOneTermRewrite)
            } else if pattern {
                Admit
            } else {
                After(Rule::AlternativesOutsidePattern)
            }
        }
        // `k::matches!` tests and `let` computes from terms a match has bound, so neither stands
        // in a pattern; a claim's sides and conditions describe symbolic states the prover
        // reaches rather than compute from one match, and a `cells!` value is a cell's content
        // (S6 decides whether that changes for readable rules written as `cells!` rules).
        Construct::Matches => {
            if pattern || form.is_claim() || cells_value(position) {
                Refuse(Class::MatchesOutsideCondition)
            } else {
                Admit
            }
        }
        Construct::Let => {
            if pattern || form.is_claim() || cells_value(position) {
                Refuse(Class::LetOutsideTerm)
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
        Construct::Rewrite => {
            if matches!(position.slot, Slot::Subject)
                && form.rewrites_inside_subject()
                && !nesting.in_rewrite
                && !position.in_local_pattern()
            {
                Admit
            } else {
                Refuse(Class::RewriteOutsideLocalRule)
            }
        }
        Construct::SortTest => {
            if pattern {
                Refuse(Class::SortTestInPattern)
            } else {
                Admit
            }
        }
        // A claim's start state may hold values nothing determines, and its conditions may be
        // disjunctions of symbolic conditions; no other sentence quantifies over its state.
        Construct::Anonymous => {
            if form.is_claim() && matches!(position.slot, Slot::Subject) {
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
        Construct::RecordUpdate | Construct::OpenRecord => {
            if cells_value(position) {
                Refuse(Class::RecordRemainderInCellsTerm)
            } else {
                Admit
            }
        }
        // A pattern matches terms with their functions evaluated, so an application below its
        // root matches only if it is a constructor's, which resolution decides. The root of an
        // equation is the function it defines; a simplification's and a claim's subjects hold
        // unevaluated applications; a collection lookup evaluates its key.
        Construct::FunctionApplication => {
            if matches!(position.slot, Slot::Subject)
                && form.matches_evaluated_terms()
                && nesting.below_root
                && !nesting.in_collection_entry
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
        | Construct::OpenRecord => Admission::Refuse(Class::ConstantNotGround),
    }
}

/// An initializer's value: the concrete initial content of a cell, built from constants and
/// configuration variables. Outside a pattern `A | B` is the bitwise operator, whose operand
/// sorts the compiler judges.
const fn initializer_value(construct: Construct) -> Admission {
    use Admission::{Admit, After, Refuse};
    match construct {
        Construct::Literal
        | Construct::IdToken
        | Construct::BytesToken
        | Construct::Lexeme
        | Construct::FunctionApplication => Admit,
        Construct::Or => After(Rule::AlternativesOutsidePattern),
        Construct::Wildcard => Refuse(Class::WildcardOutsidePattern),
        Construct::As => Refuse(Class::AliasOutsidePattern),
        Construct::Matches => Refuse(Class::MatchesOutsideCondition),
        Construct::Let => Refuse(Class::LetOutsideTerm),
        Construct::MlPredicate => Refuse(Class::MlInInitializer),
        Construct::Rewrite => Refuse(Class::RewriteOutsideLocalRule),
        Construct::SortTest => Refuse(Class::RuleTermInInitializer),
        Construct::Anonymous => Refuse(Class::ClaimSubjectOnlyTerm),
        Construct::OrBool => Refuse(Class::ClaimOnlyTerm),
        Construct::Fragment => Refuse(Class::FragmentInInitializer),
        Construct::RecordUpdate | Construct::OpenRecord => {
            Refuse(Class::RecordRemainderInInitializer)
        }
        Construct::Turbofish => Refuse(Class::TurbofishInInitializer),
    }
}

#[cfg(test)]
mod tests;
