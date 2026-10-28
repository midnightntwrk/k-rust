//! The oracle of the term families: whether a term case is accepted, and the class of its
//! mistake when it is not, derived from what each construct means where it stands.
//!
//! [`expected`] walks a case's [`Node`]s in preorder, each at the [`Position`] its path opens
//! from the hole, and asks [`admits`]. [`admits`] is written per construct, not per position: for
//! each construct it states where the construct means something, in terms of the position's
//! [`Kind`], its root role, the form's traits and the nesting, and which class it is otherwise. A
//! position's kind says what a term there is: matched (a shape values are compared against),
//! evaluated (a map key in a pattern, found by matching or by lookup), built (a value to
//! construct) or a guard (a Bool to compute). From it, and from what each construct denotes:
//!
//! - a pattern-only construct (`_`, `name @ P`, `A | B` as alternatives, an open record, a list's
//!   anonymous rest) means something only where a term is matched;
//! - a computed construct (a function application, a notation form, a `let` block,
//!   `k::matches!`, a sort test, a record update) means something only where a term is computed:
//!   in a matched position over evaluated terms it describes a term that never occurs; a
//!   notation form is moreover no pattern, so a matched position refuses it by its spelling;
//! - a value (a binder, a constructor application, a literal, a token island) may stand
//!   anywhere, except for the whole subject of an equation or a simplification, which is a
//!   function's application, and of a static clause, which is the production it expands;
//! - the whole subject of a fn, a table row, a context or a static clause names the production
//!   the sentence is written for, which `_`, an alias and a compiler-owned island do not
//!   (decision D3); a `for Sort` clause's root reads as below a constructor, and a bare name
//!   there binds the whole subject;
//! - a construct with a home (`k::rewrite!` in a single-body rule's subject, a matching-logic
//!   predicate in a condition, `k::anonymous!` in a claim's start state, ..) is stated with it.
//!
//! **Product boundaries.** Five entries keep a refusal that no meaning of the construct
//! supports, as boundaries of the product kept pending a decision, each marked with its id:
//! `let` and `k::matches!` in a claim (NT-Q1) and in an initializer (NT-Q2), a sort test in an
//! initializer (NT-Q3), a turbofish in an initializer (NT-Q4), and a map literal at a term
//! position, which NT-6 (plan item M2) makes a built term. The `cells!` cell value's boundary for
//! `let` and `k::matches!` is finding S0-17's, owned by S6.
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
//! `unbound-name`, `record-update-base`, ..), which the compiler judges for every admitted term
//! alike and the table's refusal rules state; nor a construct's own shape, which the parser
//! judges. It shares nothing with the product's position table, `krs_syntax::positions::admits`,
//! which is written per position: `tests/positions.rs` compares the two case by case.

use super::positions::{
    Construct, Entry, Form, Kind, LocalPattern, Node, PatternRoot, Position, RewriteSide, Slot,
};

/// Declares [`Class`]: each variant with its name in `expected.toml`.
macro_rules! classes {
    ($($variant:ident => $name:literal,)*) => {
        /// A mistake class the oracle answers with: a `[class]` entry of `expected.toml`, which
        /// holds its code.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Class {
            $(#[doc = concat!("`", $name, "`.")] $variant,)*
        }

        impl Class {
            /// Every class.
            pub const ALL: [Self; [$($name),*].len()] = [$(Self::$variant),*];

            /// The class's name in `expected.toml`.
            #[must_use]
            pub const fn name(self) -> &'static str {
                match self {
                    $(Self::$variant => $name,)*
                }
            }
        }
    };
}

classes! {
    AliasAtSubjectRoot => "alias-at-subject-root",
    AliasInLetPattern => "alias-in-let-pattern",
    AliasOutsidePattern => "alias-outside-pattern",
    AlternativesInLetPattern => "alternatives-in-let-pattern",
    AlternativesInOneTermRewrite => "alternatives-in-one-term-rewrite",
    AlternativesOutsidePattern => "alternatives-outside-pattern",
    ClaimOnlyTerm => "claim-only-term",
    ClaimSubjectOnlyTerm => "claim-subject-only-term",
    ConstantAppliesFunction => "constant-applies-function",
    ConstantNotGround => "constant-not-ground",
    EquationRootNotFunction => "equation-root-not-function",
    FragmentInInitializer => "fragment-in-initializer",
    FunctionInPattern => "function-in-pattern",
    IslandAtSubjectRoot => "island-at-subject-root",
    LetOutsideTerm => "let-outside-term",
    MapLiteralInTerm => "map-literal-in-term",
    MapReadValueBinder => "map-read-value-binder",
    MatchesOutsideCondition => "matches-outside-condition",
    MlInCondition => "ml-in-condition",
    MlInInitializer => "ml-in-initializer",
    MlPredicateAsTerm => "ml-predicate-as-term",
    NotationInPattern => "notation-in-pattern",
    OpenRecordOutsidePattern => "open-record-outside-pattern",
    RecordRemainderInCellsTerm => "record-remainder-in-cells-term",
    RecordRemainderInInitializer => "record-remainder-in-initializer",
    RecordUpdateInPattern => "record-update-in-pattern",
    RestOutsidePattern => "rest-outside-pattern",
    RewriteInMapKey => "rewrite-in-map-key",
    RewriteOutsideLocalRule => "rewrite-outside-local-rule",
    RuleTermInInitializer => "rule-term-in-initializer",
    SimplificationRootNotFunction => "simplification-root-not-function",
    SortTestInPattern => "sort-test-in-pattern",
    StaticClauseRootNotMarked => "static-clause-root-not-marked",
    TurbofishInInitializer => "turbofish-in-initializer",
    WildcardAtSubjectRoot => "wildcard-at-subject-root",
    WildcardOutsidePattern => "wildcard-outside-pattern",
}

/// What a refusal is told by.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Stage {
    /// The spelling and its position alone.
    Placement,
    /// What a path resolves to, or an operand's sort.
    Resolution,
}

/// One refusal: its class, what it is told by, and whether the construct that makes it is the
/// case's own or the one whose opening the case's construct stands in (depth 2).
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Refusal {
    /// The mistake class.
    pub class: Class,
    /// What the mistake is told by.
    pub stage: Stage,
    /// Whether the refused construct is the outer one, whose text holds the case's construct.
    pub outer: bool,
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
        match admits(node.construct, hole.enter_all(&node.path)) {
            None => {}
            Some(refusal) => {
                let refusal = Refusal {
                    outer: node.outer,
                    ..refusal
                };
                if refusal.stage == Stage::Placement {
                    return Outcome::Refuse(refusal);
                }
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
        outer: false,
    }
}

const fn resolution(class: Class) -> Refusal {
    Refusal {
        class,
        stage: Stage::Resolution,
        outer: false,
    }
}

/// Whether `position` lies in a constant's value, which is a ground constructor term: a value a
/// pattern can match, which nothing about evaluation or a match decides.
const fn in_constant(position: Position) -> bool {
    matches!(position.form, Form::Constant)
}

/// Whether a matched `position` meets only evaluated terms: a rule's, an equation's or a
/// context's pattern, and a local pattern, which reads a computed value. A simplification's and a
/// claim's subjects hold unevaluated applications, and a static clause's program terms as
/// written.
const fn meets_evaluated_terms(position: Position) -> bool {
    position.nesting.local.is_some() || position.form.matches_evaluated_terms()
}

/// Whether `position` lies in a `cells!` cell value, the reference notation of a cell's content.
const fn in_cells_value(position: Position) -> bool {
    position.form.writes_cells() && matches!(position.slot, Slot::Subject | Slot::Result)
}

/// Whether `position` is the whole subject of a fn, a table row, a context or a static clause.
const fn at_subject_root(position: Position) -> bool {
    matches!(position.root, Some(PatternRoot::Subject))
}

/// Whether `position` is the value of a readable map read, `{ key -> value, .. }`.
const fn in_readable_read_value(position: Position) -> bool {
    matches!(position.form, Form::ReadableRule | Form::ReadableClaim)
        && matches!(position.kind, Kind::Matched)
        && matches!(position.nesting.entries.innermost(), Some(Entry::MapValue))
}

/// The refusal of a value at the root of a subject whose root is a function's application or the
/// production a static clause expands: a value defines, simplifies and expands nothing. Telling
/// it needs what its head resolves to.
const fn value_at_root(position: Position) -> Option<Refusal> {
    let form = position.form;
    if !at_subject_root(position) {
        None
    } else if form.subject_root_applies_function() {
        if matches!(form, Form::Simplification) {
            Some(resolution(Class::SimplificationRootNotFunction))
        } else {
            Some(resolution(Class::EquationRootNotFunction))
        }
    } else if form.subject_root_expands_production() {
        Some(resolution(Class::StaticClauseRootNotMarked))
    } else {
        None
    }
}

/// Whether `construct` may stand at `position`: `None` when it means something there, and the
/// refusal otherwise.
#[must_use]
pub const fn admits(construct: Construct, position: Position) -> Option<Refusal> {
    // A readable map read binds the value its key maps to: the value is the name the read
    // introduces, or `_` for a value it does not name; a shape the value must have is a test of
    // that name.
    if in_readable_read_value(position)
        && !matches!(construct, Construct::Reference | Construct::Wildcard)
    {
        return Some(placement(Class::MapReadValueBinder));
    }
    // The whole subject of a fn, a table row, a context or a static clause names the production
    // the sentence is written for, its head. A compiler-owned island stands for a term the
    // compiler makes, no head an author names (D3).
    if at_subject_root(position) && construct.is_island() {
        return Some(placement(Class::IslandAtSubjectRoot));
    }
    match construct {
        // A value denotes itself wherever a term stands, but at a root that is a function's
        // application or a static clause's production ([`value_at_root`]).
        Construct::Reference
        | Construct::Constructor
        | Construct::Literal
        | Construct::IdToken
        | Construct::BytesToken
        | Construct::Lexeme => value_at_root(position),
        // A turbofish names the instance of a parametric constructor's application, a value as
        // any constructor's. An initializer refuses it as a product boundary kept pending a
        // decision (NT-Q4): no meaning of an instance's name excludes it from a value built once.
        Construct::Turbofish => {
            if matches!(position.form, Form::Initializer) {
                Some(placement(Class::TurbofishInInitializer))
            } else {
                value_at_root(position)
            }
        }
        Construct::FunctionApplication | Construct::BuiltinApplication => {
            application(construct, position)
        }
        // A notation form is notation for the builtin application it denotes, and means what
        // the application does. It is no pattern, though: where a pattern is read, it is refused
        // by its spelling, before anything resolves (a pattern spells the call); and its spelling
        // alone says it applies an operation, which a constant's ground value does not.
        Construct::Notation(_) => {
            if matches!(position.kind, Kind::Matched) {
                Some(placement(Class::NotationInPattern))
            } else if in_constant(position) {
                Some(placement(Class::ConstantNotGround))
            } else {
                application(Construct::BuiltinApplication, position)
            }
        }
        Construct::Wildcard => wildcard(position),
        Construct::As => alias(position),
        Construct::Or => alternatives(position),
        Construct::Matches | Construct::Let => local_term(construct, position),
        Construct::MlPredicate => predicate(position),
        Construct::Rewrite => rewrite(position),
        Construct::SortTest => sort_test(position),
        Construct::Anonymous | Construct::OrBool | Construct::Fragment => {
            island(construct, position)
        }
        Construct::RecordUpdate | Construct::OpenRecord => record(construct, position),
        Construct::MapLiteral | Construct::ListBrackets | Construct::Rest => {
            collection(construct, position)
        }
    }
}

/// An application denotes the function's value. A pattern over evaluated terms never meets an
/// unevaluated application, except at an equation's subject root, which is the function it
/// defines, and a builtin operation is no function an equation defines; a simplification may
/// rewrite a builtin's application as any other. A static clause expands a production, which an
/// application is not. A constant's value is ground. A key computes and looks it up. Telling a
/// function from a constructor needs its head.
const fn application(construct: Construct, position: Position) -> Option<Refusal> {
    let form = position.form;
    match position.kind {
        Kind::Matched => {
            if at_subject_root(position) && form.subject_root_applies_function() {
                if matches!(construct, Construct::BuiltinApplication)
                    && !matches!(form, Form::Simplification)
                {
                    Some(resolution(Class::EquationRootNotFunction))
                } else {
                    None
                }
            } else if at_subject_root(position) && form.subject_root_expands_production() {
                Some(resolution(Class::StaticClauseRootNotMarked))
            } else if meets_evaluated_terms(position) {
                Some(resolution(Class::FunctionInPattern))
            } else {
                None
            }
        }
        Kind::Built if in_constant(position) => Some(resolution(Class::ConstantAppliesFunction)),
        Kind::Evaluated | Kind::Built | Kind::Guard => None,
    }
}

/// `_` matches any term. At a subject's root it names no production (D3); at a `for Sort`
/// clause's root it is any term of the sort, as a bare name is. A map key finds an entry by
/// matching as well as by lookup, so `_` there is any entry; a built term or a condition is
/// computed, and `_` names no term. A desugar's result is written into the rules that use the
/// production as well as into programs, so `_` there is the anonymous variable of the rule it
/// lands in, which the clause's `unbound_variables` declares (a names rule).
const fn wildcard(position: Position) -> Option<Refusal> {
    if in_constant(position) {
        Some(placement(Class::ConstantNotGround))
    } else if at_subject_root(position) {
        Some(placement(Class::WildcardAtSubjectRoot))
    } else if matches!(position.kind, Kind::Matched | Kind::Evaluated)
        || matches!(
            (position.form, position.slot),
            (Form::Desugar, Slot::Result)
        )
    {
        None
    } else {
        Some(placement(Class::WildcardOutsidePattern))
    }
}

/// `name @ P` names the term a pattern matched. The whole subject is the fn's parameter, which
/// names no production (D3). A `let` reads one value, which a bare name already names whole. A
/// `k::matches!` in a condition matches as part of the sentence; in a built term it is a test
/// whose names nothing uses. Outside its rewrite islands a single-body rule's subject is also
/// what it keeps, where `@` builds nothing.
const fn alias(position: Position) -> Option<Refusal> {
    let nesting = position.nesting;
    if in_constant(position) {
        Some(placement(Class::ConstantNotGround))
    } else if at_subject_root(position) {
        Some(placement(Class::AliasAtSubjectRoot))
    } else if matches!(nesting.local, Some(LocalPattern::Let)) {
        Some(placement(Class::AliasInLetPattern))
    } else if matches!(nesting.local, Some(LocalPattern::Matches)) {
        if matches!(position.slot, Slot::Requires) {
            None
        } else {
            Some(placement(Class::AliasOutsidePattern))
        }
    } else {
        match position.kind {
            Kind::Matched
                if position.form.keeps_subject()
                    && !matches!(nesting.rewrite, Some(RewriteSide::Left)) =>
            {
                Some(placement(Class::AliasOutsidePattern))
            }
            Kind::Matched | Kind::Evaluated => None,
            Kind::Built | Kind::Guard => Some(placement(Class::AliasOutsidePattern)),
        }
    }
}

/// `A | B` matches one of several terms. A `let` reads its value by one shape, and a subject
/// rewritten in place as one term stands for the one term it matched. Where a term is computed,
/// `|` is the bitwise operator, whose domain its operands' sorts choose.
const fn alternatives(position: Position) -> Option<Refusal> {
    if in_constant(position) {
        return Some(placement(Class::ConstantNotGround));
    }
    match position.kind {
        Kind::Matched if matches!(position.nesting.local, Some(LocalPattern::Let)) => {
            Some(placement(Class::AlternativesInLetPattern))
        }
        Kind::Matched
            if position.nesting.local.is_none()
                && matches!(position.slot, Slot::Subject)
                && position.form.rewrites_one_term() =>
        {
            Some(placement(Class::AlternativesInOneTermRewrite))
        }
        Kind::Matched | Kind::Evaluated => None,
        Kind::Built | Kind::Guard => Some(resolution(Class::AlternativesOutsidePattern)),
    }
}

/// `k::matches!` is a Bool computed by matching a term a rule or equation bound, and a `let`
/// block a term computed from them (K's `:=K` and `#let`). Neither describes a matched term. A
/// claim (NT-Q1) and an initializer (NT-Q2) refuse them as product boundaries kept pending a
/// decision: both lower to `:=K` and `#let` nodes as in a rule, and no meaning excludes them
/// there. A `cells!` cell value's boundary is S0-17's (S6).
const fn local_term(construct: Construct, position: Position) -> Option<Refusal> {
    let class = if matches!(construct, Construct::Matches) {
        Class::MatchesOutsideCondition
    } else {
        Class::LetOutsideTerm
    };
    if in_constant(position) {
        Some(placement(Class::ConstantNotGround))
    } else if matches!(position.kind, Kind::Matched)
        || position.form.is_claim()
        || matches!(position.form, Form::Initializer)
        || in_cells_value(position)
    {
        Some(placement(class))
    } else {
        None
    }
}

/// A predicate is a formula about terms, no term: a pattern or a key cannot match it, and an
/// initializer builds one concrete state. It may be the condition of a sentence over symbolic
/// states (a claim, a simplification), and an operand of another predicate. As an operand of an
/// object term, or the condition of a transition or an equation, it is told from an object term
/// by what its head resolves to.
const fn predicate(position: Position) -> Option<Refusal> {
    if in_constant(position) {
        Some(placement(Class::ConstantNotGround))
    } else if position.nesting.in_predicate {
        None
    } else {
        match position.kind {
            Kind::Matched | Kind::Evaluated => Some(placement(Class::MlPredicateAsTerm)),
            Kind::Built if matches!(position.form, Form::Initializer) => {
                Some(placement(Class::MlInInitializer))
            }
            Kind::Built => Some(resolution(Class::MlPredicateAsTerm)),
            Kind::Guard if position.form.admits_predicate_conditions() => None,
            Kind::Guard => Some(resolution(Class::MlInCondition)),
        }
    }
}

/// A rewrite marks what changes inside a single-body rule's subject, or a context's hole, once
/// and outside any local pattern or predicate. A map changes values there: its keys are what it
/// is looked up by, and re-keying an entry may meet a key it holds.
const fn rewrite(position: Position) -> Option<Refusal> {
    let nesting = position.nesting;
    if in_constant(position) {
        Some(placement(Class::ConstantNotGround))
    } else if !(position.form.marks_rewrites()
        && matches!(position.slot, Slot::Subject)
        && nesting.rewrite.is_none()
        && nesting.local.is_none()
        && !nesting.in_predicate)
    {
        Some(placement(Class::RewriteOutsideLocalRule))
    } else if nesting.entries.contains(Entry::MapKey) {
        Some(placement(Class::RewriteInMapKey))
    } else {
        None
    }
}

/// `k::is!` and `k::project!` apply the sort's generated predicate or projection, so they mean
/// what an application does: a pattern over evaluated terms never meets one, and a
/// simplification's or a claim's subject may hold one. An initializer refuses them as a product
/// boundary kept pending a decision (NT-Q3), though it admits an application.
const fn sort_test(position: Position) -> Option<Refusal> {
    if in_constant(position) {
        Some(placement(Class::ConstantNotGround))
    } else if matches!(position.kind, Kind::Matched) && meets_evaluated_terms(position) {
        Some(placement(Class::SortTestInPattern))
    } else if matches!(position.form, Form::Initializer) {
        Some(placement(Class::RuleTermInInitializer))
    } else {
        None
    }
}

/// `k::anonymous!` is a value nothing determines: only a claim's start state, which the claim
/// quantifies over, may hold one. `k::or_bool!` is a disjunction of a claim's symbolic
/// conditions: only a claim has them. `k::fragment!` is a nested cell term, in a sentence's
/// terms; an initializer builds nested cells with their structs. A constant's value is none of
/// them.
const fn island(construct: Construct, position: Position) -> Option<Refusal> {
    let form = position.form;
    if in_constant(position) {
        return Some(placement(Class::ConstantNotGround));
    }
    match construct {
        Construct::Anonymous => {
            if form.is_claim()
                && matches!(position.slot, Slot::Subject)
                && !matches!(position.kind, Kind::Built)
            {
                None
            } else {
                Some(placement(Class::ClaimSubjectOnlyTerm))
            }
        }
        Construct::OrBool => {
            if form.is_claim() {
                None
            } else {
                Some(placement(Class::ClaimOnlyTerm))
            }
        }
        _ => {
            if matches!(form, Form::Initializer) {
                Some(placement(Class::FragmentInInitializer))
            } else {
                None
            }
        }
    }
}

/// `..base` builds a record whose unlisted fields are those of the record `base` matched, and
/// `..` alone leaves a matched record's unlisted fields open. A `cells!` term names every field,
/// and an initializer matches no record to take fields from or leave open. A pattern denotes no
/// record by `..base`; a built term or a condition has no value for a field `..` leaves open. An
/// open record is a constructor's pattern, read at a root as a constructor is.
const fn record(construct: Construct, position: Position) -> Option<Refusal> {
    let update = matches!(construct, Construct::RecordUpdate);
    if in_constant(position) {
        Some(placement(Class::ConstantNotGround))
    } else if in_cells_value(position) {
        Some(placement(Class::RecordRemainderInCellsTerm))
    } else if matches!(position.form, Form::Initializer) {
        Some(placement(Class::RecordRemainderInInitializer))
    } else if update {
        if matches!(position.kind, Kind::Matched) {
            Some(placement(Class::RecordUpdateInPattern))
        } else {
            None
        }
    } else if matches!(position.kind, Kind::Matched | Kind::Evaluated) {
        value_at_root(position)
    } else {
        Some(placement(Class::OpenRecordOutsidePattern))
    }
}

/// A map literal builds a map, notation of a `cells!` cell's and an initializer's map today: at a
/// term position it is refused as a product boundary kept pending NT-6, which makes it a built
/// term; a constant's value is ground, which a built map is not. List brackets denote a list wherever the position's sort is one, which the compiler
/// judges. A list's anonymous rest `..` stands for the elements a pattern leaves unnamed: a built
/// term or a condition has nothing it keeps, and a constant's value is ground.
const fn collection(construct: Construct, position: Position) -> Option<Refusal> {
    match construct {
        Construct::MapLiteral if in_constant(position) => Some(placement(Class::ConstantNotGround)),
        Construct::MapLiteral => Some(placement(Class::MapLiteralInTerm)),
        Construct::ListBrackets => value_at_root(position),
        _ => {
            if in_constant(position) {
                Some(placement(Class::ConstantNotGround))
            } else if matches!(position.kind, Kind::Matched | Kind::Evaluated) {
                None
            } else {
                Some(placement(Class::RestOutsidePattern))
            }
        }
    }
}
