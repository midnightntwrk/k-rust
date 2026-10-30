//! K7's generator data: every spelling states what it matches and denotes, every slot has a
//! driver or says why not, every static production of the terms base has a spelling, and the
//! drivers write the programs and the cells their documentation describes.

use std::collections::BTreeMap;

use krs_test_support::class_matrix::k7::{Ground, K7, Meaning, SkipKind, Status};
use krs_test_support::class_matrix::{self, Base, Case, Family};

fn term_case(cases: &[Case], id: &str) -> Case {
    cases
        .iter()
        .find(|case| case.id == id)
        .unwrap_or_else(|| panic!("no case {id}"))
        .clone()
}

/// The spellings with no witness or no value, by reason: what K7 cannot run them on. A spelling
/// that states neither (the defaults) would show as `no witness is stated` or `no value is
/// stated`, which no spelling may keep.
#[test]
fn every_spelling_states_its_witness_and_its_value_or_why_not() {
    let mut missing = BTreeMap::<String, Vec<String>>::new();
    for meaning in class_matrix::spelling_meanings() {
        let family = meaning.family.name();
        if let Err(reason) = meaning.witness {
            missing
                .entry(format!("no witness: {reason}"))
                .or_default()
                .push(format!("{family} {}", meaning.text));
        }
        if let Meaning::Undefined(reason) | Meaning::Unstated(reason) = meaning.value {
            missing
                .entry(format!("no value: {reason}"))
                .or_default()
                .push(format!("{family} {}", meaning.text));
        }
    }
    for reason in [
        "no witness: no witness is stated",
        "no value: no value is stated",
    ] {
        assert!(
            !missing.contains_key(reason),
            "{reason}: {:?}",
            missing[reason]
        );
    }
    let listed = missing
        .iter()
        .map(|(reason, spellings)| format!("{reason}: {}", spellings.join(" | ")))
        .collect::<Vec<_>>();
    assert_eq!(listed, MISSING, "{listed:#?}");
}

const MISSING: &[&str] = &[
    "no value: a cell fragment, which no term of a KItem position is: terms k::fragment![crate::Frame { ret: 1 }]",
    "no value: a matching-logic predicate, which only a prover reads: terms k::ml::exists(|v: Int| k::ml::equals(v, 0))",
    "no value: a pattern, which names or tests a term and builds none: terms _ | terms y @ Cmd::Hold(_) | terms Cmd::Go() | Cmd::Hold(_) | terms Cmd::Pair { a: x, .. } | terms [x, ..]",
    "no value: an anonymous variable, which names no value: terms k::anonymous!(Int, \"_V\")",
    "no value: the empty map has no entry at 1: notation k::builtin::map::empty()[x] | notation k::builtin::map::get(k::builtin::map::empty(), x)",
    "no value: the let's pattern does not match x = 1: terms { let y @ Cmd::Hold(_) = x; y } | terms { let (Cmd::Go() | Cmd::Hold(_)) = x; x }",
    "no value: the update's base, x = 1, is no Pair: terms Cmd::Pair { a: x, ..x }",
    "no value: x = 1 is no Bool: terms x && true | terms x || true",
    "no witness: a cell fragment, which no term of a KItem position is: terms k::fragment![crate::Frame { ret: 1 }]",
    "no witness: a computed term, which no evaluated term is: terms k::builtin::int::add(1, 2) | terms Size(x) | terms k::or_bool!(true, false) | terms k::is!(Int, x) | terms k::project!(Int, x) | terms k::matches!(x, Cmd::Hold(_)) | terms { let y = x; y } | terms { let y @ Cmd::Hold(_) = x; y } | terms { let (Cmd::Go() | Cmd::Hold(_)) = x; x } | terms Cmd::Pair { a: x, ..x } | terms x + 1 | terms x & 1 | terms x << 1 | terms x < 1 | terms x == 1 | terms x && true | terms x || true | terms !(x < 1) | terms -(x + 1) | terms x.add::<Int>(1) | terms k::builtin::int::add(x, 1) | terms k::map![x -> 1] | terms map![x -> 1] | notation k::builtin::map::empty()[x] | notation k::builtin::map::get(k::builtin::map::empty(), x) | notation k::builtin::list::item(x)[0] | notation k::builtin::list::get(k::builtin::list::item(x), 0) | notation k::builtin::map::empty().update(x, 1) | notation k::builtin::map::update(k::builtin::map::empty(), x, 1) | notation k::builtin::list::item(x).len() | notation k::builtin::list::size(k::builtin::list::item(x)) | notation k::builtin::set::item(x).to_list() | notation k::builtin::set::to_list(k::builtin::set::item(x)) | notation k::builtin::map::empty().contains_key(x) | notation k::builtin::map::in_keys(x, k::builtin::map::empty()) | notation map![x -> 1, 2 -> 3] | notation k::builtin::map::update(k::builtin::map::update(k::builtin::map::empty(), x, 1), 2, 3) | notation map![x -> 1, ..k::builtin::map::empty()] | notation map![0 -> 1] | notation k::builtin::map::update(k::builtin::map::empty(), 0, 1) | notation set![x, 1] | notation k::builtin::set::union(k::builtin::set::item(x), k::builtin::set::item(1)) | notation set![x, ..k::builtin::set::empty()] | notation k::builtin::set::union(k::builtin::set::empty(), k::builtin::set::item(x))",
    "no witness: a matching-logic predicate, which only a prover reads: terms k::ml::exists(|v: Int| k::ml::equals(v, 0))",
];

/// The slots K7 runs no case of, by reason: the forms a run cannot exercise, and the one slot
/// whose hole a fixed binder value cannot drive. No slot falls through to "no driver is
/// written".
#[test]
fn every_slot_has_a_driver_or_says_why_not() {
    let cases = class_matrix::cases();
    let mut undriven = BTreeMap::<String, Vec<String>>::new();
    for case in cases.iter().filter(|case| case.term.is_some()) {
        if let K7::Skip(skip) = &case.k7
            && skip.kind == SkipKind::Form
        {
            let slot = case
                .id
                .rsplit_once('/')
                .map_or(case.id.as_str(), |(slot, _)| slot);
            let slot = slot
                .split_once('/')
                .map_or(slot, |(_, slot)| slot)
                .to_owned();
            let slots = undriven.entry(skip.reason.clone()).or_default();
            if !slots.contains(&slot) {
                slots.push(slot);
            }
        }
    }
    assert!(
        !undriven
            .keys()
            .any(|reason| reason.starts_with("no driver is written")),
        "{undriven:#?}"
    );
    let listed = undriven
        .iter()
        .map(|(reason, slots)| format!("{reason}: {}", slots.join(" | ")))
        .collect::<Vec<_>>();
    assert_eq!(listed, UNDRIVEN, "{listed:#?}");
}

const UNDRIVEN: &[&str] = &[
    "a claim is proved, not run, and needs a prover (L4 keeps claims in the fixture gates): cells-claim/guard | cells-claim/item-root | cells-claim/result-item-root | cells-claim/result | cells-claim/subject | claim/item-root | claim/result-item-root | claim/result | claim/subject | cells-claim/guard/closure-body",
    "a constant has no program syntax, and no base sentence can name the case's constant: constant/value-root | constant/value",
    "a context alias acts only through a production strict in it, and neither the base nor the case declares one: context-alias/item-root | context-alias/subject",
    "a simplification only rewrites what a prover simplifies, and needs a prover: simplification/guard | simplification/result-root | simplification/result | simplification/subject-root | simplification/subject",
    "the base applies no function but Probe and Size from a rule: equation/subject-root",
    "the function is internal: it has no program syntax, and no base sentence can name the case's function: shorthand/result-root | shorthand/result",
];

/// Each production of the terms base that a static clause expands (a `Cmd` variant marked
/// `#[k::desugar]` or `#[k::alias]`) is applied by a spelling, so a static production kind the
/// base gains without a spelling is named here.
#[test]
fn every_static_production_of_the_terms_base_has_a_spelling() {
    let base = Base::Terms.preamble();
    let cases = class_matrix::cases();
    let mut marked = Vec::new();
    for line in base.lines() {
        let line = line.trim();
        for marker in ["#[k::desugar]", "#[k::alias]"] {
            if line.starts_with("#[k::syntax(")
                && let Some((_, variant)) = line.split_once(marker)
            {
                let name = variant
                    .trim()
                    .split(|character: char| !character.is_alphanumeric())
                    .next()
                    .unwrap_or_default();
                marked.push((marker, name.to_owned()));
            }
        }
    }
    assert_eq!(
        marked,
        [
            ("#[k::desugar]", "Dz".to_owned()),
            ("#[k::alias]", "Az".to_owned())
        ],
        "the terms base's static productions"
    );
    for (marker, name) in marked {
        let application = format!("Cmd::{name}(");
        assert!(
            cases.iter().any(
                |case| case.family == Family::Terms && case.construct.starts_with(&application)
            ),
            "the production {name}, marked {marker}, has no spelling"
        );
    }
}

/// What a case's run program is and what the run must end with, for one case of each kind of
/// driver: a matched hole, a built one, a key set up before the command, a condition, an
/// equation applied from a rule, a static clause, and an initializer.
#[test]
fn the_drivers_write_their_programs_and_cells() {
    let cases = class_matrix::cases();
    let plan = |id: &str| {
        let case = term_case(&cases, id);
        let (terminal, path) = case.command().map_or_else(
            || ("NAME".to_owned(), "Cmd::NAME".to_owned()),
            |command| (command.terminal(), format!("Cmd::{}", command.name)),
        );
        match &case.k7 {
            K7::Run(run) => (
                run.program.replace(&terminal, "NAME"),
                run.steps,
                run.cells
                    .iter()
                    .map(|(cell, term)| format!("{cell} = {term}").replace(&path, "Cmd::NAME"))
                    .collect::<Vec<_>>()
                    .join(", "),
                run.status,
            ),
            K7::Skip(skip) => panic!("{id}: {skip:?}"),
        }
    };
    let k = |items: &str| format!("k = k[{items}]");
    assert_eq!(
        plan("terms/rule/subject/Cmd::Hold(x)"),
        (
            "NAME(1, hold(1))".to_owned(),
            1,
            k("Cmd::Hold(1)"),
            Status::Liveness
        )
    );
    assert_eq!(
        plan("terms/rule/result/x + 1"),
        ("NAME(1, 0)".to_owned(), 1, k("Cmd::Hold(2)"), Status::Value)
    );
    assert_eq!(
        plan("terms/readable/map-key/x + 1"),
        (
            "then(setenv(mput(memp, 2, 0)), NAME(1, 0))".to_owned(),
            3,
            k(""),
            Status::Value
        )
    );
    assert_eq!(
        plan("terms/rule/guard/x < 1"),
        (
            "NAME(1, 0)".to_owned(),
            0,
            k("Cmd::NAME(1, 0)"),
            Status::Value
        )
    );
    assert_eq!(
        plan("terms/equation/result/x + 1"),
        (
            "call(NAME, 1)".to_owned(),
            1,
            k("Cmd::Hold(size(2))"),
            Status::Value
        )
    );
    assert_eq!(
        plan("terms/desugar/subject/Cmd::Dz()"),
        (
            "NAME(1, pair(2, 3))".to_owned(),
            0,
            k("Cmd::Hold(1)"),
            Status::Liveness
        )
    );
    assert_eq!(
        plan("terms/sort-rule/result/matches-pattern/x"),
        (
            "NAME(1, 0)".to_owned(),
            1,
            k("Cmd::Hold(true)"),
            Status::Value
        )
    );
    assert_eq!(
        plan("terms/cells/result-map-framed/Cmd::Hold(x)"),
        (
            "then(setenv(mput(memp, 1, 0)), NAME(1, 0))".to_owned(),
            3,
            format!("{}, env = map{{1 -> Cmd::Hold(1)}}", k("")),
            Status::Value
        )
    );
    assert_eq!(
        plan("terms/init/variable-item/x + 1"),
        (
            "go".to_owned(),
            0,
            k("Cmd::Go(), 1, Cmd::Hold(2)"),
            Status::Value
        )
    );
}

/// A ground term's program and its agreement with what a run shows.
#[test]
fn ground_terms_are_written_and_compared_by_value() {
    let one = Ground::Int(1);
    let map = Ground::map(vec![
        (one.clone(), Ground::Int(2)),
        (one.clone(), Ground::Int(3)),
    ]);
    assert_eq!(map, Ground::Map(vec![(one.clone(), Ground::Int(3))]));
    assert_eq!(map.program().as_deref(), Some("mput(memp, 1, 3)"));
    assert_eq!(map.literal_program(), None);
    let set = Ground::set(vec![one.clone(), one.clone()]);
    assert_eq!(set, Ground::Set(vec![one.clone()]));
    assert_eq!(set.program().as_deref(), Some("sone(1)"));
    let held = Ground::ctor("Cmd::Hold", vec![Ground::Any]);
    assert!(held.agrees(&Ground::ctor("Cmd::Hold", vec![Ground::string("s")])));
    assert!(!held.agrees(&Ground::ctor("Cmd::Go", Vec::new())));
    assert!(Ground::ctor("Cmd::Go", Vec::new()).agrees(&Ground::ctor("pkg::Cmd::Go", Vec::new())));
    assert!(!Ground::ctor("Cmd::Go", Vec::new()).agrees(&Ground::ctor("XCmd::Go", Vec::new())));
    assert_eq!(
        Ground::ctor("Wrap", vec![one.clone()]).program().as_deref(),
        Some("wk(1)")
    );
    assert_eq!(Ground::ctor("Wrap", vec![one]).literal_program(), None);
    assert_eq!(Ground::float(1.5).program().as_deref(), Some("1.5"));
    assert_eq!(
        Ground::Bytes(b"ab".to_vec()).program().as_deref(),
        Some("b\"ab\"")
    );
}
