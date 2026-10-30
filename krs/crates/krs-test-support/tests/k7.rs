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
        if let Meaning::Undefined(reason) | Meaning::Unstated(reason) | Meaning::NoTerm(reason) =
            meaning.value
        {
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
    "no value: Size is partial and the base gives it no equation, so the definition names no value of its application: terms Size(x)",
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

/// Every case's K7 status, a skip by its kind and reason, with its count, and the cases that
/// run a counter-witness: a change that moves cases into a skip, or out of a counter run, fails
/// here, whatever reason the skip gives.
#[test]
fn every_cases_k7_status_is_counted() {
    let cases = class_matrix::cases();
    let mut statuses = BTreeMap::<String, usize>::new();
    for case in &cases {
        let status = match &case.k7 {
            K7::Run(run) => format!("runs, {}", run.status.name()),
            K7::Skip(skip) => format!("{}: {}", skip.kind.name(), skip.reason),
        };
        *statuses.entry(status).or_default() += 1;
        if case.k7_counter.is_some() {
            *statuses
                .entry("runs a counter-witness".to_owned())
                .or_default() += 1;
        }
    }
    let listed = statuses
        .iter()
        .map(|(status, count)| format!("{count} {status}"))
        .collect::<Vec<_>>();
    assert_eq!(listed, STATUSES, "{listed:#?}");
}

const STATUSES: &[&str] = &[
    "766 no driver: a claim is proved, not run, and needs a prover (L4 keeps claims in the fixture gates)",
    "152 no driver: a constant has no program syntax, and no base sentence can name the case's constant",
    "156 no driver: a context alias acts only through a production strict in it, and neither the base nor the case declares one",
    "382 no driver: a simplification only rewrites what a prover simplifies, and needs a prover",
    "75 no driver: the base applies no function but Probe and Size from a rule",
    "152 no driver: the function is internal: it has no program syntax, and no base sentence can name the case's function",
    "674 no driver: the readable, claim and `cells!` families read cells the machine and typed bases start at fixed values, and those bases have no driver commands to set them up (a claim needs a prover besides)",
    "5 no value: Size is partial and the base gives it no equation, so the definition names no value of its application",
    "33 no value: a cell fragment, which no term of a KItem position is",
    "107 no value: a matching-logic predicate, which only a prover reads",
    "170 no value: a pattern, which names or tests a term and builds none",
    "34 no value: an anonymous variable, which names no value",
    "5 no value: the condition's stated value, \"s\", is no Bool",
    "5 no value: the condition's stated value, $x, is no Bool",
    "5 no value: the condition's stated value, -1, is no Bool",
    "5 no value: the condition's stated value, -2, is no Bool",
    "55 no value: the condition's stated value, 1, is no Bool",
    "5 no value: the condition's stated value, 1.5, is no Bool",
    "20 no value: the condition's stated value, 2, is no Bool",
    "5 no value: the condition's stated value, 3, is no Bool",
    "14 no value: the condition's stated value, Cmd::Go(), is no Bool",
    "9 no value: the condition's stated value, Cmd::Hold(1), is no Bool",
    "5 no value: the condition's stated value, Wrap(1), is no Bool",
    "10 no value: the condition's stated value, [1], is no Bool",
    "5 no value: the condition's stated value, b\"ab\", is no Bool",
    "10 no value: the condition's stated value, map{0 -> 1}, is no Bool",
    "10 no value: the condition's stated value, map{1 -> 1, 2 -> 3}, is no Bool",
    "25 no value: the condition's stated value, map{1 -> 1}, is no Bool",
    "10 no value: the condition's stated value, map{}, is no Bool",
    "35 no value: the condition's stated value, set{1}, is no Bool",
    "10 no value: the condition's stated value, set{}, is no Bool",
    "5 no value: the condition's stated value, word, is no Bool",
    "56 no value: the empty map has no entry at 1",
    "194 no value: the let's pattern does not match x = 1",
    "28 no value: the update's base, x = 1, is no Pair",
    "56 no value: x = 1 is no Bool",
    "43 no witness: a cell fragment, which no term of a KItem position is",
    "1748 no witness: a computed term, which no evaluated term is",
    "43 no witness: a matching-logic predicate, which only a prover reads",
    "4 no witness: a program writes $x only through a maker, a function, which a static clause's expansion of the program meets unevaluated",
    "4 no witness: a program writes Wrap(1) only through a maker, a function, which a static clause's expansion of the program meets unevaluated",
    "4 no witness: a program writes [1] only through a maker, a function, which a static clause's expansion of the program meets unevaluated",
    "8 no witness: a program writes map{} only through a maker, a function, which a static clause's expansion of the program meets unevaluated",
    "1 no witness: a program writes set{1, Cmd::Hold(1)} only through a maker, a function, which a static clause's expansion of the program meets unevaluated",
    "14 no witness: a program writes set{1} only through a maker, a function, which a static clause's expansion of the program meets unevaluated",
    "8 no witness: a program writes set{} only through a maker, a function, which a static clause's expansion of the program meets unevaluated",
    "76 no witness: the context's hole is the construct's x, which K7 binds to 1, a KResult no context heats",
    "3 no witness: the program would hold a value the generator does not state",
    "1002 runs a counter-witness",
    "1252 runs, liveness",
    "2425 runs, value",
];

/// The pattern spellings (those with a witness) without a counter-witness, by reason; no pattern
/// spelling may keep the default, `no counter-witness is stated`.
#[test]
fn every_pattern_spelling_states_a_counter_witness_or_why_not() {
    let mut missing = BTreeMap::<String, Vec<String>>::new();
    for meaning in class_matrix::spelling_meanings() {
        if meaning.witness.is_err() {
            continue;
        }
        if let Err(reason) = meaning.counter {
            missing.entry(reason.to_owned()).or_default().push(format!(
                "{} {}",
                meaning.family.name(),
                meaning.text
            ));
        }
    }
    assert!(
        !missing.contains_key("no counter-witness is stated"),
        "{:?}",
        missing.get("no counter-witness is stated")
    );
    let listed = missing
        .iter()
        .map(|(reason, spellings)| format!("{reason}: {}", spellings.join(" | ")))
        .collect::<Vec<_>>();
    assert_eq!(listed, COUNTERLESS, "{listed:#?}");
}

const COUNTERLESS: &[&str] = &[
    "`_` matches every term: terms _",
    "a binder matches every term where it is the only occurrence of its name: terms x",
    "a program writes no Id but `$x`, through its maker: terms k::id!(\"$x\")",
    "its alternative `x` matches every term where the template does not bind `x`: terms x | 1",
    "its left side `_` matches every term: terms k::rewrite!(_ => 1)",
];

/// Each production of the terms base that a static clause expands (a `Cmd` variant marked
/// `#[k::desugar]` or `#[k::alias]`) is applied by a spelling, so a static production kind the
/// base gains without a spelling is named here.
#[test]
fn every_static_production_of_the_terms_base_has_a_spelling() {
    let base = Base::Terms.preamble();
    let cases = class_matrix::cases();
    // The variants of `Cmd` whose attributes mark them, read from the parsed base, so that a
    // marker's place among the variant's attributes does not matter.
    let file = syn::parse_file(&base).expect("the terms base parses");
    let mut marked = Vec::new();
    for item in &file.items {
        let syn::Item::Enum(family) = item else {
            continue;
        };
        if family.ident != "Cmd" {
            continue;
        }
        for variant in &family.variants {
            for attribute in &variant.attrs {
                let path = attribute.path();
                let segments = path
                    .segments
                    .iter()
                    .map(|segment| segment.ident.to_string())
                    .collect::<Vec<_>>();
                let attribute_name = match segments.as_slice() {
                    [facade, name] if facade == "k" && name == "desugar" => "#[k::desugar]",
                    [facade, name] if facade == "k" && name == "alias" => "#[k::alias]",
                    _ => continue,
                };
                marked.push((attribute_name, variant.ident.to_string()));
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
#[expect(
    clippy::too_many_lines,
    reason = "One pinned plan per driver kind, each a few lines."
)]
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
    // A computed set element is looked up by its value, as a key is (D2).
    assert_eq!(
        plan("terms/rule/subject/set-element/k::builtin::int::add(x, 1)"),
        (
            "NAME(1, sone(2))".to_owned(),
            1,
            k("Cmd::Hold(1)"),
            Status::Value
        )
    );
    assert_eq!(
        plan("terms/readable/set-instance-child/x + 1"),
        (
            "then(addtoken(hold(2)), NAME(1, 0))".to_owned(),
            3,
            k(""),
            Status::Value
        )
    );
    // A condition with no value at x = 1 does not hold: the rule must not apply.
    assert_eq!(
        plan("terms/rule/guard/let-pattern/Cmd::Hold(x)"),
        (
            "NAME(1, 0)".to_owned(),
            0,
            k("Cmd::NAME(1, 0)"),
            Status::Value
        )
    );
    // A counter-witness's run stops before the case's sentence.
    let case = term_case(&cases, "terms/rule/subject/Cmd::Hold(x)");
    let counter = case
        .k7_counter
        .as_ref()
        .expect("Cmd::Hold(x) has a counter-witness");
    let terminal = case
        .command()
        .expect("a rule case has a command")
        .terminal();
    assert_eq!(
        (
            counter.program.replace(&terminal, "NAME"),
            counter.depth,
            counter.steps
        ),
        ("NAME(1, pair(0, 0))".to_owned(), 1, 0)
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
