//! The position table (`krs_syntax::positions`) against the class tests' spec
//! (`krs/tests/class-matrix/expected.toml`): the product's classes are the spec's, with the same
//! codes, every position class of the spec is in the table, and the table decides every
//! generated term case as the spec does. The spec and the product cannot drift apart silently.

use std::collections::BTreeSet;
use std::path::Path;

use krs_syntax::positions::{
    Admission, Class, Construct, Form, Nesting, Position, Rule, Slot, admits,
};
use krs_test_support::class_matrix::invariants::registry_kind;
use krs_test_support::class_matrix::table::{Expected, Table};
use krs_test_support::class_matrix::{self, Family};

/// The classes of the term families' rules that no position decides: a term's sort, which the
/// compiler judges for every admitted term (a guard that is no Bool term, a `let` whose result
/// is none), and a name nothing binds.
const NOT_POSITION_CLASSES: [&str; 3] = ["condition-sort", "let-sort", "unbound-name"];

fn spec() -> Table {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/class-matrix/expected.toml");
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("{}: {error}", path.display()));
    Table::parse(&text).unwrap_or_else(|errors| panic!("expected.toml: {errors:#?}"))
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
fn every_position_class_of_the_spec_is_in_the_table() {
    let spec = spec();
    let table = table_class_names();
    let missing = spec
        .refuse
        .iter()
        .filter(|rule| rule.pattern.starts_with("terms/") || rule.pattern.starts_with("import/"))
        .map(|rule| rule.class.as_str())
        .filter(|class| !NOT_POSITION_CLASSES.contains(class) && !table.contains(class))
        .collect::<BTreeSet<_>>();
    assert!(missing.is_empty(), "{missing:#?}");
}

/// Where a term case's hole stands, from its slot (`rule/subject`).
fn position(form: &str, slot: &str) -> Position {
    let entry = |form, slot| Position {
        nesting: Nesting {
            in_collection_entry: true,
            ..Nesting::default()
        },
        ..Position::root(form, slot)
    };
    let form_of = match form {
        "rule" => Form::RuleFn,
        "local-rule" => Form::LocalRule,
        "cells" => Form::CellsRule,
        "equation" | "shorthand" => Form::EquationFn,
        "table" => Form::EquationTable,
        "simplification" => Form::Simplification,
        "sort-rule" => Form::SortRule,
        "readable" => Form::ReadableRule,
        "claim" => Form::ReadableClaim,
        "init" => return Position::root(Form::Initializer, Slot::InitializerValue),
        "constant" => return Position::root(Form::Constant, Slot::ConstantValue),
        other => panic!("no form for the slot {other}/{slot}"),
    };
    match slot {
        // Every subject and result hole is an argument of a command or function, which the walk
        // reaches through no nesting.
        "subject" | "subject-depth-2" => Position::root(form_of, Slot::Subject),
        "result" => Position::root(form_of, Slot::Result),
        // A guard's hole is the whole condition.
        "guard" => Position::root(form_of, Slot::Requires),
        "map-key" | "list-element" => entry(form_of, Slot::Subject),
        "result-list-element" => entry(form_of, Slot::Result),
        other => panic!("no slot for {form}/{other}"),
    }
}

/// Where a node of a construct stands relative to the hole.
#[derive(Clone, Copy)]
enum Inner {
    Hole,
    MatchesPattern,
    LetPattern,
    RewriteLeft,
    RewriteRight,
}

/// The nodes of a construct the table judges, in the walker's order (preorder).
fn nodes(construct: &str) -> Vec<(Construct, Inner)> {
    use Construct as C;
    use Inner::{Hole, LetPattern, MatchesPattern, RewriteLeft, RewriteRight};
    match construct {
        "x" | "Cmd::Go" | "Cmd::Go()" | "Cmd::Hold(x)" | "Go()" | "Hold(x)" => Vec::new(),
        "k::builtin::int::add(1, 2)" => vec![
            (C::FunctionApplication, Hole),
            (C::Literal, Hole),
            (C::Literal, Hole),
        ],
        "Size(x)" => vec![(C::FunctionApplication, Hole)],
        "1" | "-1" | "true" | "\"s\"" | "1.5" => vec![(C::Literal, Hole)],
        "_" => vec![(C::Wildcard, Hole)],
        "k::id!(\"$x\")" => vec![(C::IdToken, Hole)],
        "k::bytes!(b\"ab\")" => vec![(C::BytesToken, Hole)],
        "k::anonymous!(Int, \"_V\")" => vec![(C::Anonymous, Hole)],
        "k::lexeme!(Word, \"word\")" => vec![(C::Lexeme, Hole)],
        "k::or_bool!(true, false)" => {
            vec![(C::OrBool, Hole), (C::Literal, Hole), (C::Literal, Hole)]
        }
        "k::fragment![crate::Frame { ret: 1 }]" => vec![(C::Fragment, Hole), (C::Literal, Hole)],
        "k::is!(Int, x)" | "k::project!(Int, x)" => vec![(C::SortTest, Hole)],
        "y @ Cmd::Hold(_)" => vec![(C::As, Hole), (C::Wildcard, Hole)],
        "Cmd::Go() | Cmd::Hold(_)" => vec![(C::Or, Hole), (C::Wildcard, Hole)],
        "k::matches!(x, Cmd::Hold(_))" => vec![(C::Matches, Hole), (C::Wildcard, MatchesPattern)],
        "{ let y = x; y }" => vec![(C::Let, Hole)],
        "{ let y @ Cmd::Hold(_) = x; y }" => vec![
            (C::Let, Hole),
            (C::As, LetPattern),
            (C::Wildcard, LetPattern),
        ],
        "{ let (Cmd::Go() | Cmd::Hold(_)) = x; x }" => vec![
            (C::Let, Hole),
            (C::Or, LetPattern),
            (C::Wildcard, LetPattern),
        ],
        "k::ml::exists(|v: Int| k::ml::equals(v, 0))" => vec![(C::MlPredicate, Hole)],
        "k::rewrite!(_ => 1)" => vec![
            (C::Rewrite, Hole),
            (C::Wildcard, RewriteLeft),
            (C::Literal, RewriteRight),
        ],
        other => panic!("no nodes for the construct {other}"),
    }
}

/// The table's answer for a construct at `hole`: the first refusal in preorder, and the rules it
/// leaves to the compiler before it.
fn decide(hole: Position, construct: &str) -> (Option<Class>, BTreeSet<&'static str>) {
    let mut after = BTreeSet::new();
    for (construct, inner) in nodes(construct) {
        let mut position = hole;
        match inner {
            Inner::Hole => {}
            Inner::MatchesPattern => position.nesting.in_matches_pattern = true,
            Inner::LetPattern => position.nesting.in_let_pattern = true,
            Inner::RewriteLeft => position = position.rewrite_left(),
            Inner::RewriteRight => position = position.rewrite_right(),
        }
        match admits(position, construct) {
            Admission::Admit => {}
            Admission::Refuse(class) => return (Some(class), after),
            Admission::After(rule) => {
                after.insert(rule.name());
            }
        }
    }
    (None, after)
}

#[test]
fn the_table_decides_every_term_case_as_the_spec_does() {
    let spec = spec();
    let cases = class_matrix::cases();
    let ids = cases
        .iter()
        .map(|case| case.id.as_str())
        .collect::<Vec<_>>();
    let resolution = spec.resolve(&ids, registry_kind);
    let table = table_class_names();
    let mut disagreements = Vec::new();
    let mut judged = 0;
    for case in cases
        .iter()
        .filter(|case| matches!(case.family, Family::Terms | Family::Import))
    {
        let mut parts = case.id.splitn(4, '/');
        let (_, form, slot) = (parts.next(), parts.next(), parts.next());
        let hole = position(
            form.expect("a term case names its form"),
            slot.expect("a term case names its slot"),
        );
        let (refused, after) = decide(hole, &case.construct);
        let expected = resolution
            .expected
            .get(&case.id)
            .unwrap_or_else(|| panic!("expected.toml decides {}", case.id));
        let spec_class = match expected {
            Expected::Accept(_) => None,
            Expected::Refuse { rule, .. } => Some(rule.class.as_str()),
        };
        let agrees = match (refused, spec_class) {
            (Some(class), spec_class) => spec_class == Some(class.name()),
            // Admitted by the table: the spec accepts, or refuses by a sort or a name, or by a
            // rule the table left to the compiler.
            (None, None) => true,
            (None, Some(spec_class)) => !table.contains(spec_class) || after.contains(spec_class),
        };
        if !agrees {
            disagreements.push(format!(
                "{}: the table says {}, expected.toml says {}",
                case.id,
                refused.map_or_else(
                    || format!("admit (after {after:?})"),
                    |class| class.name().to_owned()
                ),
                spec_class.unwrap_or("accept"),
            ));
        }
        judged += 1;
    }
    assert!(judged > 800, "only {judged} term cases were judged");
    assert!(
        disagreements.is_empty(),
        "{} disagreements:\n{}",
        disagreements.len(),
        disagreements.join("\n")
    );
}
