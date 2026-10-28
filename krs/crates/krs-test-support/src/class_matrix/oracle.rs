//! The oracle of the term families: whether a term case is accepted, and the class of its
//! mistake when it is not, derived from what each construct means where it stands.
//!
//! [`expected`] walks a case's [`Node`]s in preorder, each at the [`Position`] its path opens
//! from the hole, and asks [`admits`]. [`admits`] is written per construct, not per position: for
//! each construct it states where the construct means something, in terms of the position's
//! [`Kind`], its root role, the form's traits and the nesting, and which class it is otherwise. A
//! position's kind says what a term there is: matched (a shape values are compared against),
//! evaluated (a map key, found by matching or by lookup), built (a value to construct) or a guard
//! (a Bool to compute). From it, and from what each construct denotes:
//!
//! - a pattern-only construct (`_`, `name @ P`, `A | B` as alternatives) means something only
//!   where a term is matched;
//! - a computed construct (a function application, a `let` block, `k::matches!`, a sort test, a
//!   record update) means something only where a term is computed: in a matched position it
//!   describes a term that never occurs among evaluated values;
//! - a value (a binder, a constructor application, a literal, a token island) may stand
//!   anywhere, except for the whole subject of an equation or a simplification, which is a
//!   function's application; what may stand for the whole subject of a fn rule or a `for Sort`
//!   clause (`_`, an alias, an island) is still open (NT-F5, NT-2), and the oracle admits it;
//! - a construct with a home (`k::rewrite!` in a single-body rule's subject, a matching-logic
//!   predicate in a condition, `k::anonymous!` in a claim's start state, ..) is stated with it.
//!
//! **Product boundaries.** Three entries keep a refusal that no meaning of the construct
//! supports, as boundaries of the product kept pending a decision, each marked with its id:
//! `let` and `k::matches!` in a claim (NT-Q1) and in an initializer (NT-Q2), and a sort test in
//! an initializer (NT-Q3). The `cells!` cell value's boundary for `let` and `k::matches!` is
//! finding S0-17's, owned by S6.
//!
//! **Stages.** A refusal's [`Stage`] says what the mistake is told by. A [`Stage::Placement`]
//! refusal is told by the spelling and its position alone, before any name is resolved. A
//! [`Stage::Resolution`] refusal needs what a path resolves to (a function rather than a
//! constructor, a predicate rather than an object term) or an operand's sort, so a name that
//! resolves to nothing or a sort mistake is met first. [`expected`] answers with the outermost
//! placement refusal, or else the outermost resolution refusal; the table decides between the
//! latter and its own name and sort rules (`table`'s precedence).
//!
//! The oracle does not judge a term's sort or names (`condition-sort`, `let-sort`,
//! `unbound-name`, `record-update-base`), which the compiler judges for every admitted term alike
//! and the table's refusal rules state; nor a construct's own shape, which the parser judges. It
//! shares nothing with the product's position table, `krs_syntax::positions::admits`, which is
//! written per position: `tests/positions.rs` compares the two case by case.

use super::positions::{
    Construct, Entry, Form, Kind, LocalPattern, Node, PatternRoot, Position, RewriteSide, Slot,
};

/// A mistake class the oracle answers with: a `[class]` entry of `expected.toml`, which holds
/// its code.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Class {
    /// `alias-in-let-pattern`.
    AliasInLetPattern,
    /// `alias-outside-pattern`.
    AliasOutsidePattern,
    /// `alternatives-in-let-pattern`.
    AlternativesInLetPattern,
    /// `alternatives-in-one-term-rewrite`.
    AlternativesInOneTermRewrite,
    /// `alternatives-outside-pattern`.
    AlternativesOutsidePattern,
    /// `claim-only-term`.
    ClaimOnlyTerm,
    /// `claim-subject-only-term`.
    ClaimSubjectOnlyTerm,
    /// `constant-applies-function`.
    ConstantAppliesFunction,
    /// `constant-not-ground`.
    ConstantNotGround,
    /// `equation-root-not-function`.
    EquationRootNotFunction,
    /// `fragment-in-initializer`.
    FragmentInInitializer,
    /// `function-in-pattern`.
    FunctionInPattern,
    /// `let-outside-term`.
    LetOutsideTerm,
    /// `matches-outside-condition`.
    MatchesOutsideCondition,
    /// `ml-in-condition`.
    MlInCondition,
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
    /// `rewrite-in-map-key`.
    RewriteInMapKey,
    /// `rewrite-outside-local-rule`.
    RewriteOutsideLocalRule,
    /// `rule-term-in-initializer`.
    RuleTermInInitializer,
    /// `simplification-root-not-function`.
    SimplificationRootNotFunction,
    /// `sort-test-in-pattern`.
    SortTestInPattern,
    /// `wildcard-outside-pattern`.
    WildcardOutsidePattern,
}

impl Class {
    /// Every class.
    pub const ALL: [Self; 26] = [
        Self::AliasInLetPattern,
        Self::AliasOutsidePattern,
        Self::AlternativesInLetPattern,
        Self::AlternativesInOneTermRewrite,
        Self::AlternativesOutsidePattern,
        Self::ClaimOnlyTerm,
        Self::ClaimSubjectOnlyTerm,
        Self::ConstantAppliesFunction,
        Self::ConstantNotGround,
        Self::EquationRootNotFunction,
        Self::FragmentInInitializer,
        Self::FunctionInPattern,
        Self::LetOutsideTerm,
        Self::MatchesOutsideCondition,
        Self::MlInCondition,
        Self::MlInInitializer,
        Self::MlPredicateAsTerm,
        Self::RecordRemainderInCellsTerm,
        Self::RecordRemainderInInitializer,
        Self::RecordUpdateInPattern,
        Self::RewriteInMapKey,
        Self::RewriteOutsideLocalRule,
        Self::RuleTermInInitializer,
        Self::SimplificationRootNotFunction,
        Self::SortTestInPattern,
        Self::WildcardOutsidePattern,
    ];

    /// The class's name in `expected.toml`.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::AliasInLetPattern => "alias-in-let-pattern",
            Self::AliasOutsidePattern => "alias-outside-pattern",
            Self::AlternativesInLetPattern => "alternatives-in-let-pattern",
            Self::AlternativesInOneTermRewrite => "alternatives-in-one-term-rewrite",
            Self::AlternativesOutsidePattern => "alternatives-outside-pattern",
            Self::ClaimOnlyTerm => "claim-only-term",
            Self::ClaimSubjectOnlyTerm => "claim-subject-only-term",
            Self::ConstantAppliesFunction => "constant-applies-function",
            Self::ConstantNotGround => "constant-not-ground",
            Self::EquationRootNotFunction => "equation-root-not-function",
            Self::FragmentInInitializer => "fragment-in-initializer",
            Self::FunctionInPattern => "function-in-pattern",
            Self::LetOutsideTerm => "let-outside-term",
            Self::MatchesOutsideCondition => "matches-outside-condition",
            Self::MlInCondition => "ml-in-condition",
            Self::MlInInitializer => "ml-in-initializer",
            Self::MlPredicateAsTerm => "ml-predicate-as-term",
            Self::RecordRemainderInCellsTerm => "record-remainder-in-cells-term",
            Self::RecordRemainderInInitializer => "record-remainder-in-initializer",
            Self::RecordUpdateInPattern => "record-update-in-pattern",
            Self::RewriteInMapKey => "rewrite-in-map-key",
            Self::RewriteOutsideLocalRule => "rewrite-outside-local-rule",
            Self::RuleTermInInitializer => "rule-term-in-initializer",
            Self::SimplificationRootNotFunction => "simplification-root-not-function",
            Self::SortTestInPattern => "sort-test-in-pattern",
            Self::WildcardOutsidePattern => "wildcard-outside-pattern",
        }
    }
}

/// What a refusal is told by.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Stage {
    /// The spelling and its position alone.
    Placement,
    /// What a path resolves to, or an operand's sort.
    Resolution,
}

/// One refusal: its class and what it is told by.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Refusal {
    /// The mistake class.
    pub class: Class,
    /// What the mistake is told by.
    pub stage: Stage,
}

/// The oracle's answer for a case.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Outcome {
    /// Every construct means something where it stands.
    Accept,
    /// The deciding refusal: the outermost placement refusal, or else the outermost resolution
    /// refusal.
    Refuse(Refusal),
}

/// The oracle's answer for `nodes` at `hole`.
#[must_use]
pub fn expected(hole: Position, nodes: &[Node]) -> Outcome {
    let mut resolution = None;
    for node in nodes {
        match admits(node.construct, hole.enter_all(node.path)) {
            None => {}
            Some(
                refusal @ Refusal {
                    stage: Stage::Placement,
                    ..
                },
            ) => return Outcome::Refuse(refusal),
            Some(refusal) => {
                resolution.get_or_insert(refusal);
            }
        }
    }
    resolution.map_or(Outcome::Accept, Outcome::Refuse)
}

const fn placement(class: Class) -> Refusal {
    Refusal {
        class,
        stage: Stage::Placement,
    }
}

const fn resolution(class: Class) -> Refusal {
    Refusal {
        class,
        stage: Stage::Resolution,
    }
}

/// Whether `position` lies in a constant's value, which is a ground constructor term: a value a
/// pattern can match, which nothing about evaluation or a match decides.
const fn in_constant(position: Position) -> bool {
    matches!(position.form, Form::Constant)
}

/// Whether a matched `position` meets only evaluated terms: a rule's or an equation's pattern, and
/// a local pattern, which reads a computed value. A simplification's and a claim's subjects hold
/// unevaluated applications.
const fn meets_evaluated_terms(position: Position) -> bool {
    position.nesting.local.is_some() || position.form.matches_evaluated_terms()
}

/// Whether `position` lies in a `cells!` cell value, the reference notation of a cell's content.
const fn in_cells_value(position: Position) -> bool {
    position.form.writes_cells() && matches!(position.slot, Slot::Subject | Slot::Result)
}

/// Whether `construct` may stand at `position`: `None` when it means something there, and the
/// refusal otherwise.
#[must_use]
#[expect(
    clippy::too_many_lines,
    reason = "One match over the closed construct set; each arm is the construct's entry."
)]
pub const fn admits(construct: Construct, position: Position) -> Option<Refusal> {
    let form = position.form;
    let kind = position.kind;
    let nesting = position.nesting;
    match construct {
        // A value denotes itself wherever a term stands, but the whole subject of an equation or
        // a simplification is the application of the function it defines or simplifies, which a
        // value is not.
        Construct::Reference
        | Construct::Constructor
        | Construct::Literal
        | Construct::IdToken
        | Construct::BytesToken
        | Construct::Lexeme => {
            if matches!(position.root, Some(PatternRoot::Subject))
                && form.subject_root_applies_function()
            {
                if matches!(form, Form::Simplification) {
                    Some(resolution(Class::SimplificationRootNotFunction))
                } else {
                    Some(resolution(Class::EquationRootNotFunction))
                }
            } else {
                None
            }
        }
        // An application denotes the function's value. A pattern over evaluated terms never
        // meets an unevaluated application, except at an equation's subject root, which is the
        // function it defines, and a builtin operation is no function an equation defines; a
        // simplification may rewrite a builtin's application as any other. A constant's value is
        // ground. Telling a function from a constructor needs its head.
        Construct::FunctionApplication | Construct::BuiltinApplication => match kind {
            Kind::Matched => {
                if matches!(position.root, Some(PatternRoot::Subject))
                    && form.subject_root_applies_function()
                {
                    if matches!(construct, Construct::BuiltinApplication)
                        && !matches!(form, Form::Simplification)
                    {
                        Some(resolution(Class::EquationRootNotFunction))
                    } else {
                        None
                    }
                } else if meets_evaluated_terms(position) {
                    Some(resolution(Class::FunctionInPattern))
                } else {
                    None
                }
            }
            Kind::Built if in_constant(position) => {
                Some(resolution(Class::ConstantAppliesFunction))
            }
            Kind::Evaluated | Kind::Built | Kind::Guard => None,
        },
        // `_` matches any term. A map key finds an entry by matching as well as by lookup, so `_`
        // there is any entry; a built term or a condition is computed, and `_` names no term.
        Construct::Wildcard => {
            if in_constant(position) {
                Some(placement(Class::ConstantNotGround))
            } else if matches!(kind, Kind::Matched | Kind::Evaluated) {
                None
            } else {
                Some(placement(Class::WildcardOutsidePattern))
            }
        }
        // `name @ P` names the term a pattern matched. A `let` reads one value, which a bare
        // name already names whole. A `k::matches!` in a condition matches as part of the
        // sentence; in a built term it is a test whose names nothing uses. Outside its rewrite
        // islands a single-body rule's subject is also what it keeps, where `@` builds nothing.
        Construct::As => {
            if in_constant(position) {
                Some(placement(Class::ConstantNotGround))
            } else if matches!(nesting.local, Some(LocalPattern::Let)) {
                Some(placement(Class::AliasInLetPattern))
            } else if matches!(nesting.local, Some(LocalPattern::Matches)) {
                if matches!(position.slot, Slot::Requires) {
                    None
                } else {
                    Some(placement(Class::AliasOutsidePattern))
                }
            } else {
                match kind {
                    Kind::Matched
                        if form.keeps_subject()
                            && !matches!(nesting.rewrite, Some(RewriteSide::Left)) =>
                    {
                        Some(placement(Class::AliasOutsidePattern))
                    }
                    Kind::Matched | Kind::Evaluated => None,
                    Kind::Built | Kind::Guard => Some(placement(Class::AliasOutsidePattern)),
                }
            }
        }
        // `A | B` matches one of several terms. A `let` reads its value by one shape, and a
        // subject rewritten in place as one term stands for the one term it matched. Where a term
        // is computed, `|` is the bitwise operator, whose domain its operands' sorts choose.
        Construct::Or => {
            if in_constant(position) {
                Some(placement(Class::ConstantNotGround))
            } else {
                match kind {
                    Kind::Matched if matches!(nesting.local, Some(LocalPattern::Let)) => {
                        Some(placement(Class::AlternativesInLetPattern))
                    }
                    Kind::Matched
                        if nesting.local.is_none()
                            && matches!(position.slot, Slot::Subject)
                            && form.rewrites_one_term() =>
                    {
                        Some(placement(Class::AlternativesInOneTermRewrite))
                    }
                    Kind::Matched | Kind::Evaluated => None,
                    Kind::Built | Kind::Guard => {
                        Some(resolution(Class::AlternativesOutsidePattern))
                    }
                }
            }
        }
        // `k::matches!` is a Bool computed by matching a term a rule or equation bound, and a
        // `let` block a term computed from them (K's `:=K` and `#let`). Neither describes a
        // matched term. A claim (NT-Q1) and an initializer (NT-Q2) refuse them as product
        // boundaries kept pending a decision: both lower to `:=K` and `#let` nodes as in a rule,
        // and no meaning excludes them there. A `cells!` cell value's boundary is S0-17's (S6).
        Construct::Matches => {
            if in_constant(position) {
                Some(placement(Class::ConstantNotGround))
            } else if matches!(kind, Kind::Matched)
                || form.is_claim()
                || matches!(form, Form::Initializer)
                || in_cells_value(position)
            {
                Some(placement(Class::MatchesOutsideCondition))
            } else {
                None
            }
        }
        Construct::Let => {
            if in_constant(position) {
                Some(placement(Class::ConstantNotGround))
            } else if matches!(kind, Kind::Matched)
                || form.is_claim()
                || matches!(form, Form::Initializer)
                || in_cells_value(position)
            {
                Some(placement(Class::LetOutsideTerm))
            } else {
                None
            }
        }
        // A predicate is a formula about terms, no term: a pattern or a key cannot match it, and
        // an initializer builds one concrete state. It may be the condition of a sentence over
        // symbolic states (a claim, a simplification), and an operand of another predicate. As
        // an operand of an object term, or the condition of a transition or an equation, it is
        // told from an object term by what its head resolves to.
        Construct::MlPredicate => {
            if in_constant(position) {
                Some(placement(Class::ConstantNotGround))
            } else if nesting.in_predicate {
                None
            } else {
                match kind {
                    Kind::Matched | Kind::Evaluated => Some(placement(Class::MlPredicateAsTerm)),
                    Kind::Built if matches!(form, Form::Initializer) => {
                        Some(placement(Class::MlInInitializer))
                    }
                    Kind::Built => Some(resolution(Class::MlPredicateAsTerm)),
                    Kind::Guard if form.admits_predicate_conditions() => None,
                    Kind::Guard => Some(resolution(Class::MlInCondition)),
                }
            }
        }
        // A rewrite marks what changes inside a single-body rule's subject, once and outside any
        // local pattern or predicate. A map changes values there: its keys are what it is looked
        // up by, and re-keying an entry may meet a key it holds.
        Construct::Rewrite => {
            if in_constant(position) {
                Some(placement(Class::ConstantNotGround))
            } else if !(form.marks_rewrites()
                && matches!(position.slot, Slot::Subject)
                && nesting.rewrite.is_none()
                && nesting.local.is_none()
                && !nesting.in_predicate)
            {
                Some(placement(Class::RewriteOutsideLocalRule))
            } else if matches!(nesting.entry, Some(Entry::MapKey)) {
                Some(placement(Class::RewriteInMapKey))
            } else {
                None
            }
        }
        // `k::is!` and `k::project!` apply the sort's generated predicate or projection, so they
        // mean what an application does: a pattern over evaluated terms never meets one, and a
        // simplification's or a claim's subject may hold one. An initializer refuses them as a
        // product boundary kept pending a decision (NT-Q3), though it admits an application.
        Construct::SortTest => {
            if in_constant(position) {
                Some(placement(Class::ConstantNotGround))
            } else if matches!(kind, Kind::Matched) && meets_evaluated_terms(position) {
                Some(placement(Class::SortTestInPattern))
            } else if matches!(form, Form::Initializer) {
                Some(placement(Class::RuleTermInInitializer))
            } else {
                None
            }
        }
        // A value nothing determines: only a claim's start state, which the claim quantifies
        // over, may hold one.
        Construct::Anonymous => {
            if in_constant(position) {
                Some(placement(Class::ConstantNotGround))
            } else if form.is_claim()
                && matches!(position.slot, Slot::Subject)
                && !matches!(kind, Kind::Built)
            {
                None
            } else {
                Some(placement(Class::ClaimSubjectOnlyTerm))
            }
        }
        // A disjunction of a claim's symbolic conditions: only a claim has them.
        Construct::OrBool => {
            if in_constant(position) {
                Some(placement(Class::ConstantNotGround))
            } else if form.is_claim() {
                None
            } else {
                Some(placement(Class::ClaimOnlyTerm))
            }
        }
        // A nested cell term, in a sentence's terms; an initializer builds nested cells with
        // their structs, and a constant's value is no cell term.
        Construct::Fragment => {
            if in_constant(position) {
                Some(placement(Class::ConstantNotGround))
            } else if matches!(form, Form::Initializer) {
                Some(placement(Class::FragmentInInitializer))
            } else {
                None
            }
        }
        // `..base` builds a record whose unlisted fields are those of the record `base` matched.
        // A `cells!` term names every field, a pattern denotes no record by it, and an
        // initializer matches no record to take fields from.
        Construct::RecordUpdate => {
            if in_constant(position) {
                Some(placement(Class::ConstantNotGround))
            } else if in_cells_value(position) {
                Some(placement(Class::RecordRemainderInCellsTerm))
            } else if matches!(kind, Kind::Matched) {
                Some(placement(Class::RecordUpdateInPattern))
            } else if matches!(form, Form::Initializer) {
                Some(placement(Class::RecordRemainderInInitializer))
            } else {
                None
            }
        }
    }
}
