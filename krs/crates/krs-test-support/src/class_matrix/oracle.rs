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
//!   anonymous rest) means something only where a term is matched, and not where it is also
//!   built: an alias clause's subject is both, since the clause runs backwards when a result is
//!   printed, each term its result matches printed as its subject built from the match's
//!   bindings, and printing builds no test, choice or hole;
//! - a computed construct (a function application, a notation form, a `let` block,
//!   `k::matches!`, a sort test, a record update) means something only where a term is computed:
//!   in a matched position over evaluated terms it describes a term that never occurs, and in a
//!   static clause's subject, matched against a program as written, it would stand for its
//!   spelling rather than its value (decision NT-11-5); a notation form is moreover no pattern,
//!   so a matched position refuses it by its spelling;
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
//! **Meaning, not tools.** An entry states what the construct means where it stands, not
//! whether every tool that reads the emitted K takes it: `let` and `k::matches!` in a claim mean
//! what they mean in a rule, which KRS makes every prover read by lifting them into functions the
//! definition declares (NT-15). The `cells!` cell value's boundary for `let` and
//! `k::matches!` is finding S0-17's, owned by S6, and is kept here as a refusal.
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
    Construct, Entry, Form, Kind, LocalPattern, Node, Notation, Opening, PatternRoot, Position,
    RewriteSide, Slot,
};

/// Declares [`Class`]: each variant with its name in `expected.toml`. The attribute axis's oracle
/// ([`super::attributes`]) answers with the classes listed last.
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
    AliasInAliasSubject => "alias-in-alias-subject",
    AliasInLetPattern => "alias-in-let-pattern",
    AliasOutsidePattern => "alias-outside-pattern",
    AlternativesInAliasSubject => "alternatives-in-alias-subject",
    AlternativesInLetPattern => "alternatives-in-let-pattern",
    AlternativesInOneTermRewrite => "alternatives-in-one-term-rewrite",
    AlternativesOutsidePattern => "alternatives-outside-pattern",
    ClaimOnlyTerm => "claim-only-term",
    ClaimSubjectOnlyTerm => "claim-subject-only-term",
    CollectionInStaticSubject => "collection-in-static-subject",
    ConstantAppliesFunction => "constant-applies-function",
    ConstantNotGround => "constant-not-ground",
    EquationRootNotFunction => "equation-root-not-function",
    FragmentInInitializer => "fragment-in-initializer",
    FunctionInPattern => "function-in-pattern",
    IslandAtSubjectRoot => "island-at-subject-root",
    LetOutsideTerm => "let-outside-term",
    MapReadValueBinder => "map-read-value-binder",
    MatchesOutsideCondition => "matches-outside-condition",
    MlInCondition => "ml-in-condition",
    MlInInitializer => "ml-in-initializer",
    MlPredicateAsTerm => "ml-predicate-as-term",
    NotationInPattern => "notation-in-pattern",
    OpenRecordInAliasSubject => "open-record-in-alias-subject",
    OpenRecordOutsidePattern => "open-record-outside-pattern",
    RecordRemainderInCellsTerm => "record-remainder-in-cells-term",
    RecordRemainderInInitializer => "record-remainder-in-initializer",
    RecordUpdateInPattern => "record-update-in-pattern",
    RestInAliasSubject => "rest-in-alias-subject",
    RestOutsidePattern => "rest-outside-pattern",
    RewriteInMapKey => "rewrite-in-map-key",
    RewriteOutsideLocalRule => "rewrite-outside-local-rule",
    SimplificationRootNotFunction => "simplification-root-not-function",
    SortTestInPattern => "sort-test-in-pattern",
    StaticClauseRootNotMarked => "static-clause-root-not-marked",
    UnexpandableStaticApplication => "unexpandable-static-application",
    WildcardAtSubjectRoot => "wildcard-at-subject-root",
    WildcardInAliasSubject => "wildcard-in-alias-subject",
    WildcardOutsidePattern => "wildcard-outside-pattern",
    // The attribute axis's classes (`super::attributes`).
    AnywhereOutsideTermRule => "anywhere-outside-term-rule",
    ConditionOnStaticClause => "condition-on-static-clause",
    DuplicateKey => "duplicate-key",
    EvaluationKeyWithoutEvaluation => "evaluation-key-without-evaluation",
    ExistentialOutsideStep => "existential-outside-step",
    FreshOutsideStep => "fresh-outside-step",
    HelperOnConstant => "helper-on-constant",
    HelperOnContextAlias => "helper-on-context-alias",
    HelperOnInitializer => "helper-on-initializer",
    HelperOnShorthand => "helper-on-shorthand",
    HelperOnTableRow => "helper-on-table-row",
    KeyValueShape => "key-value-shape",
    KeysTogether => "keys-together",
    MissingKey => "missing-key",
    NondetOnFunction => "nondet-on-function",
    OrderOnUnorderedSentence => "order-on-unordered-sentence",
    OwiseOnSimplification => "owise-on-simplification",
    PriorityRange => "priority-range",
    RecursiveOutsideProduction => "recursive-outside-production",
    RestrictionBinder => "restriction-binder",
    RestrictionOutsideFunction => "restriction-outside-function",
    RestrictionShape => "restriction-shape",
    RetiredAttribute => "retired-attribute",
    SmtLemmaUntranslatable => "smt-lemma-untranslatable",
    UnboundVariablesOutsideDesugar => "unbound-variables-outside-desugar",
    UnboundVariablesShape => "unbound-variables-shape",
    UnknownKey => "unknown-key",
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

/// Whether `position` lies in the matched part of a key or a set's element in a pattern: not below
/// a construct that computes it, nor in a local pattern.
fn in_key_reading(position: Position) -> bool {
    (position.nesting.entries.contains(Entry::MapKey)
        || position.nesting.entries.contains(Entry::SetElement))
        && matches!(position.kind, Kind::Evaluated | Kind::Matched)
        && position.nesting.local.is_none()
}

/// Whether `position` lies in a Map collection's instance in a pattern over evaluated terms,
/// outside a key and a local pattern: matched, but written in the braces a Set collection's
/// instance is written in, which a pattern looks up instead. Only the cell's declared type tells
/// the two apart, so the instance's cells are read as a key is, the notation there the call it
/// denotes, and what a matched cell cannot hold is told by resolution.
const fn in_map_instance(position: Position) -> bool {
    position.nesting.entries.contains(Entry::Instance)
        && !position.nesting.entries.contains(Entry::SetElement)
        && !position.nesting.entries.contains(Entry::MapKey)
        && matches!(position.kind, Kind::Matched)
        && matches!(position.slot, Slot::Subject)
        && position.nesting.local.is_none()
        && position.form.matches_evaluated_terms()
}

/// Whether `construct` selects an entry by matching where a key reads it: a name nothing else
/// binds, `_`, an alias, alternatives (`x | 1` reads as alternatives there), an open record, a
/// list's rest.
const fn selects(construct: Construct) -> bool {
    matches!(
        construct,
        Construct::Fresh
            | Construct::Wildcard
            | Construct::As
            | Construct::Or
            | Construct::Notation(Notation::BitwiseOr)
            | Construct::OpenRecord
            | Construct::Rest
    )
}

/// What a construct that computes means in a key that is a selection: the key is matched against
/// the collection's evaluated keys, which no application, operator or sort test is, so it never
/// matches (told once the key's names are known); a `let` block and `k::matches!` are refused as in
/// any pattern.
const fn in_selection(construct: Construct) -> Option<Refusal> {
    match construct {
        Construct::FunctionApplication
        | Construct::BuiltinApplication
        | Construct::Notation(
            Notation::Arithmetic
            | Notation::Bitwise
            | Notation::Shift
            | Notation::Comparison
            | Notation::Equality
            | Notation::AndThen
            | Notation::OrElse
            | Notation::Not
            | Notation::Negation
            | Notation::Method
            | Notation::Index
            | Notation::CollectionMethod
            | Notation::MapLiteral
            | Notation::SetLiteral,
        ) => Some(resolution(Class::FunctionInPattern)),
        Construct::SortTest => Some(resolution(Class::SortTestInPattern)),
        Construct::Let => Some(placement(Class::LetOutsideTerm)),
        Construct::Matches => Some(placement(Class::MatchesOutsideCondition)),
        _ => None,
    }
}

/// Whether `node`, list brackets in `nodes`, writes two or more parts: elements, or an element
/// and a rest.
fn list_of_parts(node: &Node, nodes: &[Node]) -> bool {
    node.construct == Construct::ListBrackets
        && nodes
            .iter()
            .filter(|other| {
                other.path.len() == node.path.len() + 1
                    && other.path.starts_with(&node.path)
                    && other.path.last() == Some(&Opening::ListElement)
            })
            .count()
            >= 2
}

/// Each node's refusal at its position in `nodes` at `hole`, the node's own entry
/// ([`admits`]) read with its key's: a key that holds a selecting construct is a selection. A
/// list of two or more parts below a static subject's root is one spelling of the list
/// ([`concatenation`]), which its brackets' parts tell.
#[must_use]
pub fn refusals(hole: Position, nodes: &[Node]) -> Vec<Option<Refusal>> {
    let selection = nodes
        .iter()
        .any(|node| selects(node.construct) && in_key_reading(hole.enter_all(&node.path)));
    nodes
        .iter()
        .map(|node| {
            let position = hole.enter_all(&node.path);
            if list_of_parts(node, nodes)
                && matched_as_written(position)
                && !at_subject_root(position)
            {
                return admits(node.construct, position)
                    .or(Some(resolution(Class::CollectionInStaticSubject)));
            }
            match in_selection(node.construct) {
                // Below `@` or `|` the key is matched already, by the construct's own entry.
                Some(refusal)
                    if selection
                        && in_key_reading(position)
                        && position.kind == Kind::Evaluated =>
                {
                    Some(refusal)
                }
                _ => admits(node.construct, position),
            }
        })
        .collect()
}

/// The oracle's answer for `nodes` at `hole`.
///
/// A key or a set's element in a pattern reads two ways (`positions::Kind::Evaluated`): computed
/// and looked up when nothing in its matched part selects an entry, a selection otherwise. Each
/// construct's entry reads the first; a case whose key holds a selecting construct reads the
/// second, and a construct that computes there never matches.
#[must_use]
pub fn expected(hole: Position, nodes: &[Node]) -> Outcome {
    let mut resolution = None;
    for (node, refusal) in nodes.iter().zip(refusals(hole, nodes)) {
        match refusal {
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

/// Whether `position` is matched and also built: in an alias clause's subject, outside a local
/// pattern, which printing builds from the bindings of what the clause's result matched in a
/// printed term. A construct that only matches there (a test, a choice, a hole) is no term
/// printing can build: the printed alias would not denote the printed value.
const fn built_backwards(position: Position) -> bool {
    position.form.builds_subject_backwards()
        && matches!(position.slot, Slot::Subject)
        && matches!(position.kind, Kind::Matched | Kind::Evaluated)
        && position.nesting.local.is_none()
}

/// Whether `position` lies in a static clause's subject, outside a local pattern: an alias's or
/// a desugar's, which static expansion matches against a program's terms as they are written,
/// before anything evaluates. A computed construct there would match only its own spelling
/// (`Foo(x + 1)` the program `foo(y + 1)`, not `foo(1 + y)`), where everywhere else it denotes
/// its value (decision NT-11-5).
const fn matched_as_written(position: Position) -> bool {
    position.form.subject_root_expands_production()
        && matches!(position.slot, Slot::Subject)
        && matches!(position.kind, Kind::Matched | Kind::Evaluated)
        && position.nesting.local.is_none()
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
        && !matches!(
            construct,
            Construct::Reference | Construct::Fresh | Construct::Wildcard
        )
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
        // application or a static clause's production ([`value_at_root`]). A static production's
        // application denotes its expansion: the definition's expansion rewrites it in a rule's
        // pattern, and (decision NT-14) KRS writes it expanded below a desugar's or an alias's
        // subject root wherever the expansion needs no value, as a ground application's never
        // does, so it is a value too.
        // A collection literal
        // that denotes a value, the empty collection or a set's singleton, is one, as its call
        // `map::empty()` or `set::item(x)` is; and a turbofish names the instance of a parametric
        // constructor's application, a value as any constructor's, an initializer's too.
        Construct::Reference
        | Construct::Fresh
        | Construct::Constructor
        | Construct::StaticApplication
        | Construct::Literal
        | Construct::IdToken
        | Construct::BytesToken
        | Construct::Lexeme
        | Construct::Turbofish => value_at_root(position),
        Construct::CollectionValue | Construct::Notation(Notation::CollectionValue) => {
            collection_value(position)
        }
        Construct::FunctionApplication | Construct::BuiltinApplication => {
            application(construct, position)
        }
        // Below a static clause's subject root, a program's application of a static production
        // is expanded before the clause is tried, so the clause matches its expansion; where its
        // clauses give it none, or one that depends on what a program writes, the subject stands
        // for no one term (decision NT-14). Telling it needs the production's clauses, which
        // resolution reads. The spellings that write one stand in static subjects only.
        Construct::OpenStaticApplication => {
            if matched_as_written(position) && !at_subject_root(position) {
                Some(resolution(Class::UnexpandableStaticApplication))
            } else {
                value_at_root(position)
            }
        }
        Construct::Concatenation => concatenation(position),
        // An index, a collection method or a collection literal is the application of a
        // collection's function it denotes, decided as that application is wherever it stands: a
        // pattern holds it as it holds the call (`m[k]` is `map::get(m, k)`, `map![k -> v]` is
        // `map::update(map::empty(), k, v)`), and a function there never matches.
        Construct::Notation(notation) if notation.is_collection() => {
            application(Construct::BuiltinApplication, position)
        }
        // A notation form is notation for the builtin application it denotes, and means what
        // the application does. It is no pattern, though: where a pattern is read, it is refused
        // by its spelling, before anything resolves (a pattern spells the call); and its spelling
        // alone says it applies an operation, which a constant's ground value does not.
        // `a | b` where a pattern is read is the alternatives' spelling, and means what they do.
        Construct::Notation(Notation::BitwiseOr)
            if matches!(position.kind, Kind::Matched | Kind::Evaluated) =>
        {
            alternatives(position)
        }
        Construct::Notation(_) if in_map_instance(position) => {
            application(Construct::BuiltinApplication, position)
        }
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
        Construct::ListBrackets | Construct::Rest => collection(construct, position),
    }
}

/// An application denotes the function's value. A pattern over evaluated terms never meets an
/// unevaluated application, except at an equation's subject root, which is the function it
/// defines, and a builtin operation is no function an equation defines; a simplification may
/// rewrite a builtin's application as any other. A static clause expands a production, which an
/// application is not, and below its root its subject matches a program's terms as written,
/// where an application would stand for its spelling rather than its value (decision NT-11-5),
/// a key or a set's element too, since nothing is looked up there. A constant's value is
/// ground. A key computes and looks it up. Telling a function from a constructor needs its head.
const fn application(construct: Construct, position: Position) -> Option<Refusal> {
    let form = position.form;
    if matched_as_written(position) && !at_subject_root(position) {
        return Some(resolution(Class::FunctionInPattern));
    }
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

/// A collection's unit or singleton (`map![]`, `set![x]`, `[x, ..]`, their calls) is a value, a
/// pattern as a constructor is. At a rule's whole subject, the computation's first item, it
/// matches that item where it is the collection (decision NT-11-2); a context's subject root
/// names the production whose argument the context evaluates, which a collection is not, so a
/// collection there is refused with the class a function at a matched root has. Elsewhere a root
/// decides as a value's ([`value_at_root`]).
const fn collection_value(position: Position) -> Option<Refusal> {
    if at_subject_root(position) && position.form.subject_root_evaluates_argument() {
        Some(resolution(Class::FunctionInPattern))
    } else {
        value_at_root(position)
    }
}

/// A set's concatenation matches a set split into disjoint parts, a pattern as a constructor is
/// (at a root too, but a context's, as [`collection_value`]), and builds their union where the
/// parts are disjoint. Below a static clause's
/// subject root it is matched as written, and static expansion neither reorders a set's parts nor
/// regroups a list's (decision NT-14, finding S2 of its review: `[1, 2, 3]` misses
/// `list::concat([1, 2], [3])`), so a collection of two or more parts there is one of its
/// spellings, and stands for it rather than for the collection; the empty collection and one
/// element have one spelling. Telling a concatenation from another application takes its head.
/// A constant's value applies no function.
const fn concatenation(position: Position) -> Option<Refusal> {
    if matched_as_written(position) && !at_subject_root(position) {
        Some(resolution(Class::CollectionInStaticSubject))
    } else if in_constant(position) {
        Some(resolution(Class::ConstantAppliesFunction))
    } else if matches!(position.kind, Kind::Matched | Kind::Evaluated) {
        collection_value(position)
    } else {
        None
    }
}

/// `_` matches any term. At a subject's root it names no production (D3); at a `for Sort`
/// clause's root it is any term of the sort, as a bare name is. A map key finds an entry by
/// matching as well as by lookup, so `_` there is any entry; a built term or a condition is
/// computed, and `_` names no term. A desugar's result is written into the rules that use the
/// production as well as into programs, so `_` there is the anonymous variable of the rule it
/// lands in, which the clause's `unbound_variables` declares (a names rule). An alias's subject is
/// also built, and `_` there would print as a variable where a value stood.
const fn wildcard(position: Position) -> Option<Refusal> {
    if in_constant(position) {
        Some(placement(Class::ConstantNotGround))
    } else if at_subject_root(position) {
        Some(placement(Class::WildcardAtSubjectRoot))
    } else if built_backwards(position) {
        Some(placement(Class::WildcardInAliasSubject))
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
/// what it keeps, where `@` builds nothing. An alias clause's subject is also built, where `@`'s
/// test of the term's shape would print as a conjunction, no term.
const fn alias(position: Position) -> Option<Refusal> {
    let nesting = position.nesting;
    if in_constant(position) {
        Some(placement(Class::ConstantNotGround))
    } else if at_subject_root(position) {
        Some(placement(Class::AliasAtSubjectRoot))
    } else if built_backwards(position) {
        Some(placement(Class::AliasInAliasSubject))
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

/// `A | B` matches one of several terms. A `let` reads its value by one shape, a subject
/// rewritten in place as one term stands for the one term it matched, and an alias clause's
/// subject is also built as one term, where `A | B` would print as a disjunction. Where a term is
/// computed,
/// `|` is the bitwise operator, whose domain its operands' sorts choose: alternatives of
/// constructor patterns choose none (`x | 1`, over operands a domain takes, is
/// [`Notation::BitwiseOr`], the operator's application).
const fn alternatives(position: Position) -> Option<Refusal> {
    if in_constant(position) {
        return Some(placement(Class::ConstantNotGround));
    }
    if built_backwards(position) {
        return Some(placement(Class::AlternativesInAliasSubject));
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

/// `k::matches!` is a Bool computed by matching a term, and a `let` block a term computed from
/// others (K's `:=K` and `#let`), each the application of a function generated for it alone,
/// which no term holds: a pattern never meets one. Where a term is built or a condition computed
/// they mean their value: a result, a condition, an initializer (from its configuration
/// variables and constants, evaluated when the configuration is built), and a claim's states
/// and conditions, which are terms over the claim's variables as a rule's are; a claim's start
/// state holds applications, which denote their values there. A `cells!` cell value's boundary
/// is S0-17's (S6).
const fn local_term(construct: Construct, position: Position) -> Option<Refusal> {
    let class = if matches!(construct, Construct::Matches) {
        Class::MatchesOutsideCondition
    } else {
        Class::LetOutsideTerm
    };
    let claim_state = position.form.is_claim() && position.nesting.local.is_none();
    if in_constant(position) {
        Some(placement(Class::ConstantNotGround))
    } else if (matches!(position.kind, Kind::Matched) && !claim_state) || in_cells_value(position) {
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
/// what an application does: a pattern over evaluated terms never meets one, nor does a static
/// clause's subject, which would match its spelling (decision NT-11-5), and a simplification's
/// or a claim's subject may hold one, as a built term, an initializer's included, does.
const fn sort_test(position: Position) -> Option<Refusal> {
    if in_constant(position) {
        Some(placement(Class::ConstantNotGround))
    } else if in_map_instance(position) {
        Some(resolution(Class::SortTestInPattern))
    } else if matched_as_written(position)
        || (matches!(position.kind, Kind::Matched) && meets_evaluated_terms(position))
    {
        Some(placement(Class::SortTestInPattern))
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

/// `..base` builds the record `base` with the listed fields replaced, and `..` alone leaves a
/// matched record's unlisted fields open. A `cells!` term names every field. A pattern denotes
/// no record by `..base`; a built term or a condition, an initializer's included (whose base is a
/// value: a configuration variable or a constant), denotes that record; and a built term has no
/// value for a field `..` leaves open, an initializer's (its own class) as any other, and neither
/// has an alias clause's subject, built from what its result matched. An open record is a
/// constructor's pattern, read at a root as a constructor is.
const fn record(construct: Construct, position: Position) -> Option<Refusal> {
    let update = matches!(construct, Construct::RecordUpdate);
    if in_constant(position) {
        Some(placement(Class::ConstantNotGround))
    } else if in_cells_value(position) {
        Some(placement(Class::RecordRemainderInCellsTerm))
    } else if !update
        && matches!(position.form, Form::Initializer)
        && position.nesting.local.is_none()
    {
        Some(placement(Class::RecordRemainderInInitializer))
    } else if update {
        if in_map_instance(position) {
            Some(resolution(Class::RecordUpdateInPattern))
        } else if matches!(position.kind, Kind::Matched) {
            Some(placement(Class::RecordUpdateInPattern))
        } else {
            None
        }
    } else if built_backwards(position) {
        Some(placement(Class::OpenRecordInAliasSubject))
    } else if matches!(position.kind, Kind::Matched | Kind::Evaluated) {
        value_at_root(position)
    } else {
        Some(placement(Class::OpenRecordOutsidePattern))
    }
}

/// List brackets denote a list wherever the position's sort is one, which the compiler judges,
/// decided at a root as a collection's value ([`collection_value`]). A
/// list's anonymous rest `..` stands for the elements a pattern leaves unnamed: a built term or a
/// condition has nothing it keeps, an alias clause's subject, built from what its result matched,
/// has no value for them, and a constant's value is ground.
const fn collection(construct: Construct, position: Position) -> Option<Refusal> {
    match construct {
        Construct::ListBrackets => collection_value(position),
        _ => {
            if in_constant(position) {
                Some(placement(Class::ConstantNotGround))
            } else if built_backwards(position) {
                Some(placement(Class::RestInAliasSubject))
            } else if matches!(position.kind, Kind::Matched | Kind::Evaluated) {
                None
            } else {
                Some(placement(Class::RestOutsidePattern))
            }
        }
    }
}
