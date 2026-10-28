//! The position table (`krs_syntax::positions`) against the class tests' spec: the product's
//! classes are those of `krs/tests/class-matrix/expected.toml`, with the same codes; the
//! oracle's (`class_matrix::oracle`) are too, and cover the product's; and the product's table,
//! written per position, decides every generated term case as the oracle, written per
//! construct, does, from the case's own position and nodes. The cases on which the two disagree
//! are exactly the known findings ([`KNOWN`]), each on the red list (`pending.toml`) under its
//! finding, so the spec and the product cannot drift apart silently.

use std::collections::BTreeSet;
use std::path::Path;

use krs_syntax::positions::{
    Admission, Class, Construct, Form, Nesting, Position, Rule, Slot, admits,
};
use krs_test_support::class_matrix::oracle::{self, Stage};
use krs_test_support::class_matrix::pending::Pending;
use krs_test_support::class_matrix::positions::{self as model, Entry, LocalPattern, RewriteSide};
use krs_test_support::class_matrix::table::Table;
use krs_test_support::class_matrix::{self, Family};

/// The cases on which the product's table and the oracle disagree, and the finding of each.
const KNOWN: [(&str, &str); 13] = [
    ("terms/claim/subject/k::is!(Int, x)", "NT-1-3"),
    ("terms/claim/subject/k::project!(Int, x)", "NT-1-3"),
    ("terms/readable/list-element/Size(x)", "NT-1-2"),
    (
        "terms/readable/list-element/k::builtin::int::add(1, 2)",
        "NT-1-2",
    ),
    ("terms/readable/map-key/Cmd::Pair { a: x, ..x }", "NT-1-1"),
    ("terms/readable/map-key/k::is!(Int, x)", "NT-1-1"),
    (
        "terms/readable/map-key/k::matches!(x, Cmd::Hold(_))",
        "NT-1-1",
    ),
    ("terms/readable/map-key/k::project!(Int, x)", "NT-1-1"),
    (
        "terms/readable/map-key/{ let (Cmd::Go() | Cmd::Hold(_)) = x; x }",
        "NT-1-1",
    ),
    ("terms/readable/map-key/{ let y = x; y }", "NT-1-1"),
    (
        "terms/readable/map-key/{ let y @ Cmd::Hold(_) = x; y }",
        "NT-1-1",
    ),
    ("terms/simplification/subject/k::is!(Int, x)", "NT-1-3"),
    ("terms/simplification/subject/k::project!(Int, x)", "NT-1-3"),
];

/// The product's classes that no generated construct can make yet: the oracle has no entry for
/// a construct no spelling holds (a turbofish instance).
const NOT_SPELLED: [&str; 1] = ["turbofish-in-initializer"];

fn read_class_matrix(file: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/class-matrix")
        .join(file);
    std::fs::read_to_string(&path).unwrap_or_else(|error| panic!("{}: {error}", path.display()))
}

fn spec() -> Table {
    Table::parse(&read_class_matrix("expected.toml"))
        .unwrap_or_else(|errors| panic!("expected.toml: {errors:#?}"))
}

/// The names of every class the table refuses with or leaves to the compiler.
fn table_class_names() -> BTreeSet<&'static str> {
    Class::ALL
        .iter()
        .map(|class| class.name())
        .chain(Rule::ALL.iter().map(|rule| rule.name()))
        .collect()
}

#[test]
fn every_class_of_the_table_is_a_spec_class_with_its_code() {
    let spec = spec();
    let mut drift = Vec::new();
    for class in Class::ALL {
        match spec.classes.get(class.name()) {
            None => drift.push(format!("{} is no class of expected.toml", class.name())),
            Some(expected) if expected.code != class.code().as_str() => drift.push(format!(
                "{} has the code {} in the table and {} in expected.toml",
                class.name(),
                class.code().as_str(),
                expected.code
            )),
            Some(_) => {}
        }
    }
    for rule in Rule::ALL {
        if !spec.classes.contains_key(rule.name()) {
            drift.push(format!("{} is no class of expected.toml", rule.name()));
        }
    }
    assert!(drift.is_empty(), "{drift:#?}");
}

#[test]
fn every_class_of_the_oracle_is_a_spec_class_and_covers_the_table() {
    let spec = spec();
    let oracle = oracle::Class::ALL
        .iter()
        .map(|class| class.name())
        .collect::<BTreeSet<_>>();
    let undeclared = oracle
        .iter()
        .filter(|class| !spec.classes.contains_key(**class))
        .collect::<Vec<_>>();
    assert!(undeclared.is_empty(), "{undeclared:#?}");
    let uncovered = table_class_names()
        .into_iter()
        .filter(|class| !oracle.contains(class) && !NOT_SPELLED.contains(class))
        .collect::<Vec<_>>();
    assert!(uncovered.is_empty(), "{uncovered:#?}");
}

/// The product's position of a model position.
fn product_position(position: model::Position) -> Position {
    let form = match position.form {
        model::Form::ReadableRule => Form::ReadableRule,
        model::Form::ReadableClaim => Form::ReadableClaim,
        model::Form::SortRule => Form::SortRule,
        model::Form::EquationTable => Form::EquationTable,
        model::Form::RuleFn => Form::RuleFn,
        model::Form::LocalRule => Form::LocalRule,
        model::Form::EquationFn => Form::EquationFn,
        model::Form::Simplification => Form::Simplification,
        model::Form::CellsRule => Form::CellsRule,
        model::Form::Initializer => Form::Initializer,
        model::Form::Constant => Form::Constant,
    };
    let slot = match position.slot {
        model::Slot::Subject => Slot::Subject,
        model::Slot::Result => Slot::Result,
        model::Slot::Requires => Slot::Requires,
        model::Slot::Value if form == Form::Constant => Slot::ConstantValue,
        model::Slot::Value => Slot::InitializerValue,
    };
    let nesting = position.nesting;
    let product = Position {
        form,
        slot,
        nesting: Nesting {
            in_matches_pattern: nesting.local == Some(LocalPattern::Matches),
            in_let_pattern: nesting.local == Some(LocalPattern::Let),
            in_rewrite: nesting.rewrite.is_some(),
            in_collection_entry: nesting.entry.is_some(),
            in_map_key: nesting.entry == Some(Entry::MapKey),
        },
    };
    if nesting.rewrite == Some(RewriteSide::Right) {
        product.rewrite_right()
    } else {
        product
    }
}

/// The product's construct of a model construct; `None` for a binder or a constructor
/// application, for which the product's table has no row: below a pattern's root they stand
/// wherever a term does, and at a root the product's pattern reader judges them by the root's
/// role, not `admits` ([`product`] reports such a node instead of skipping it).
const fn product_construct(construct: model::Construct) -> Option<Construct> {
    use model::Construct as M;
    Some(match construct {
        M::Reference | M::Constructor => return None,
        M::Literal => Construct::Literal,
        M::FunctionApplication | M::BuiltinApplication => Construct::FunctionApplication,
        M::Wildcard => Construct::Wildcard,
        M::As => Construct::As,
        M::Or => Construct::Or,
        M::Matches => Construct::Matches,
        M::Let => Construct::Let,
        M::MlPredicate => Construct::MlPredicate,
        M::Rewrite => Construct::Rewrite,
        M::SortTest => Construct::SortTest,
        M::Anonymous => Construct::Anonymous,
        M::OrBool => Construct::OrBool,
        M::Fragment => Construct::Fragment,
        M::RecordUpdate => Construct::RecordUpdate,
        M::IdToken => Construct::IdToken,
        M::BytesToken => Construct::BytesToken,
        M::Lexeme => Construct::Lexeme,
    })
}

/// A table's answer for one case: the first refusal in preorder, the classes it leaves to the
/// compiler before it, and whether a node stands at a pattern's root.
#[derive(Debug, Default, Eq, PartialEq)]
struct Answer {
    refused: Option<&'static str>,
    after: BTreeSet<&'static str>,
    at_root: bool,
}

/// The product table's answer for `nodes` at `hole`. A binder or a constructor at a pattern's
/// root, which `admits` does not judge, is reported as a refusal of its own.
fn product(hole: model::Position, nodes: &[model::Node]) -> Answer {
    let mut answer = Answer::default();
    for node in nodes {
        let position = hole.enter_all(node.path);
        answer.at_root |= position.root.is_some();
        let Some(construct) = product_construct(node.construct) else {
            if position.root.is_some() {
                answer.refused = Some("a root admits() does not judge");
                break;
            }
            continue;
        };
        match admits(product_position(position), construct) {
            Admission::Admit => {}
            Admission::Refuse(class) => {
                answer.refused = Some(class.name());
                break;
            }
            Admission::After(rule) => {
                answer.after.insert(rule.name());
            }
        }
    }
    answer
}

/// The oracle's answer for `nodes` at `hole`, in the same shape: its first placement refusal,
/// and its resolution refusals before it.
fn oracle(hole: model::Position, nodes: &[model::Node]) -> Answer {
    let mut answer = Answer::default();
    for node in nodes {
        let position = hole.enter_all(node.path);
        answer.at_root |= position.root.is_some();
        match oracle::admits(node.construct, position) {
            None => {}
            Some(refusal) if refusal.stage == Stage::Placement => {
                answer.refused = Some(refusal.class.name());
                break;
            }
            Some(refusal) => {
                answer.after.insert(refusal.class.name());
            }
        }
    }
    answer
}

#[test]
fn the_table_decides_every_term_case_as_the_oracle_does() {
    let pending = Pending::parse(&read_class_matrix("pending.toml"))
        .unwrap_or_else(|errors| panic!("pending.toml: {errors:#?}"));
    let cases = class_matrix::cases();
    let mut disagreements = Vec::new();
    let mut judged = 0;
    for case in cases
        .iter()
        .filter(|case| matches!(case.family, Family::Terms | Family::Import))
    {
        let term = case.term.expect("a term case has a position");
        let product = product(term.position, term.nodes);
        let oracle = oracle(term.position, term.nodes);
        // The product refuses where the oracle tells a placement mistake, and leaves to the
        // compiler exactly what the oracle tells by resolution. At a pattern's root the product
        // leaves to the compiler what only the root's declaration settles (an equation's root
        // application), so there it may leave more than the oracle refuses.
        let after = if oracle.at_root {
            oracle.after.is_subset(&product.after)
        } else {
            oracle.after == product.after
        };
        if product.refused != oracle.refused || !after {
            disagreements.push((
                case.id.as_str(),
                format!("the table says {product:?}, the oracle says {oracle:?}"),
            ));
        }
        judged += 1;
    }
    assert!(judged > 800, "only {judged} term cases were judged");
    let unknown = disagreements
        .iter()
        .filter(|(id, _)| !KNOWN.iter().any(|(known, _)| known == id))
        .map(|(id, line)| format!("{id}: {line}"))
        .collect::<Vec<_>>();
    assert!(
        unknown.is_empty(),
        "{} disagreements:\n{}",
        unknown.len(),
        unknown.join("\n")
    );
    let found = disagreements
        .iter()
        .map(|(id, _)| *id)
        .collect::<BTreeSet<_>>();
    let gone = KNOWN
        .iter()
        .filter(|(id, _)| !found.contains(id))
        .collect::<Vec<_>>();
    assert!(
        gone.is_empty(),
        "known disagreements that agree now: {gone:?}"
    );
    for (id, finding) in KNOWN {
        let entry = pending.entries.get(id);
        assert_eq!(
            entry.map(|entry| entry.finding.as_str()),
            Some(finding),
            "{id} is pending under {finding}"
        );
    }
}
