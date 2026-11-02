//! The cells oracle's checks (design S5, §3): the table's cell-entry rows against the principles
//! (checks 0, 1, 1r), the readable form against the `cells!` form it abbreviates (check 3), the
//! advice of a missing layer (check 4), and the generated coverage of the domain (check 5).
//!
//! Check 2, the product's `admit` and `pair` against the oracle, is the product's own: it needs
//! `krs_syntax::cell_entries`.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::sync::LazyLock;

use krs_test_support::class_matrix::cells_oracle::{
    CODES, ENTRY_CLASSES, EntryCase, Form, LINT_CLASSES, Layer, Mark, Notation, Order, Outcome,
    READABLE_ONLY, RULE_CLASSES, SORT_CLASSES, Spelling, Step, Template, abbreviate, advise, judge,
    mark, outcome, rule_outcome,
};
use krs_test_support::class_matrix::invariants::registry_kind;
use krs_test_support::class_matrix::table::{Expected, Glob, TERM_ACCEPTS_FILE, Table, twin};
use krs_test_support::class_matrix::{self, Case, Family, Side, entry_cases};

fn read_class_matrix(file: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/class-matrix")
        .join(file);
    std::fs::read_to_string(&path).unwrap_or_else(|error| panic!("{}: {error}", path.display()))
}

static CASES: LazyLock<Vec<Case>> = LazyLock::new(class_matrix::cases);

static TABLE: LazyLock<Table> = LazyLock::new(|| {
    Table::parse_with_term_accepts(
        &read_class_matrix("expected.toml"),
        &read_class_matrix(TERM_ACCEPTS_FILE),
    )
    .unwrap_or_else(|errors| panic!("expected.toml: {errors:#?}"))
});

/// The table's decision of every case, as `Table::resolve` resolves it.
static EXPECTED: LazyLock<BTreeMap<String, Expected<'static>>> = LazyLock::new(|| {
    let resolution = TABLE.resolve_cases(&CASES, registry_kind);
    assert!(resolution.errors.is_empty(), "{:#?}", resolution.errors);
    resolution.expected
});

/// Every cell-entry case with its entry.
static ENTRIES: LazyLock<Vec<(&'static Case, EntryCase)>> = LazyLock::new(|| {
    CASES
        .iter()
        .filter_map(|case| Some((case, case.cell_entry()?)))
        .collect()
});

/// Whether the oracle's `got` agrees with the table's `expected` (§3, check 1): a refusal with
/// a refusal of its class; an admission with an accept owing the same lint; `After` with an
/// accept owing none or a sort class's refusal; and any admission with a rule-level row, which
/// check 1r judges.
fn agrees(got: Outcome, expected: &Expected<'_>) -> bool {
    match expected {
        Expected::Refuse { name, .. } if RULE_CLASSES.contains(name) => got.admits(),
        Expected::Refuse { name, .. } => match got {
            Outcome::Refuse(class) => class == *name,
            Outcome::After => SORT_CLASSES.contains(name),
            Outcome::Admit { .. } => false,
        },
        Expected::Accept(accepted) => match got {
            Outcome::Admit { lint } => lint == accepted.lint.as_deref(),
            Outcome::After => accepted.lint.is_none(),
            Outcome::Refuse(_) => false,
        },
    }
}

fn shown(expected: &Expected<'_>) -> String {
    match expected {
        Expected::Refuse { name, .. } => format!("refuse {name}"),
        Expected::Accept(accepted) => accepted.lint.as_ref().map_or_else(
            || "accept".to_owned(),
            |lint| format!("accept, lint {lint}"),
        ),
    }
}

/// The exceptions whose glob matches `id` or its twin.
fn naming<'t>(id: &str, exceptions: &'t [(Glob, String, String)]) -> Vec<&'t str> {
    let twin = twin(id);
    exceptions
        .iter()
        .filter(|(glob, ..)| {
            glob.matches(id) || twin.as_deref().is_some_and(|twin| glob.matches(twin))
        })
        .map(|(_, pattern, _)| pattern.as_str())
        .collect()
}

/// Check 0: every class the oracle answers with is a class of the table with the oracle's code;
/// a proposed code is one its step registers, so it must not be registered yet, and a registered
/// one is an author code.
#[test]
fn check_0_every_class_of_the_oracle_is_the_tables_with_its_code() {
    let mut failures = Vec::new();
    let named = ENTRY_CLASSES
        .iter()
        .chain(&RULE_CLASSES)
        .chain(&LINT_CLASSES)
        .copied()
        .collect::<BTreeSet<_>>();
    let coded = CODES
        .iter()
        .map(|(class, _)| *class)
        .collect::<BTreeSet<_>>();
    assert_eq!(named, coded, "every class of the oracle states its code");
    for (class, code) in CODES {
        match TABLE.classes.get(class) {
            None => failures.push(format!("{class}: no class of expected.toml")),
            Some(declared) if declared.code != code => failures.push(format!(
                "{class}: expected.toml answers with {}, the oracle with {code}",
                declared.code
            )),
            Some(declared) => match (registry_kind(code), declared.proposed) {
                (Some(_), true) => failures.push(format!("{class}: {code} is registered")),
                (None, false) => failures.push(format!("{class}: {code} is not registered")),
                (Some(kind), false) if kind != krs_diagnostic::codes::CodeKind::Author => {
                    failures.push(format!("{class}: {code} is no author code"));
                }
                _ => {}
            },
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

/// Check 1: every cell-entry case's row agrees with the oracle (steps 1–3), or a
/// `[cell-exception]` names it with the principle it departs by; no exception is stale.
#[test]
fn check_1_every_cell_entry_row_agrees_with_the_principles() {
    let exceptions = TABLE
        .cell_exceptions
        .iter()
        .map(|exception| {
            let glob = Glob::parse(&exception.pattern).expect("a parsed table's globs parse");
            (glob, exception.pattern.clone(), exception.principle.clone())
        })
        .collect::<Vec<_>>();
    let mut failures = Vec::new();
    for (_, pattern, principle) in &exceptions {
        let stated = principle == "E1"
            || principle == "E3"
            || principle
                .strip_prefix("C-lim: ")
                .is_some_and(|reason| !reason.trim().is_empty());
        if !stated {
            failures.push(format!(
                "cell-exception {pattern:?}: the principle {principle:?} is not E1, E3 or `C-lim: REASON`"
            ));
        }
    }
    let mut hits = BTreeMap::<&str, usize>::new();
    let mut disagreements = 0;
    for (case, entry) in ENTRIES.iter() {
        let expected = &EXPECTED[&case.id];
        let got = entry.outcome();
        if agrees(got, expected) {
            continue;
        }
        disagreements += 1;
        let named = naming(&case.id, &exceptions);
        if named.is_empty() {
            failures.push(format!(
                "{}: the table says {}, the principles {got:?}",
                case.id,
                shown(expected)
            ));
        }
        for pattern in named {
            *hits.entry(pattern).or_default() += 1;
        }
    }
    for (_, pattern, _) in &exceptions {
        if !hits.contains_key(pattern.as_str()) {
            failures.push(format!(
                "cell-exception {pattern:?} names no disagreement: it is stale, remove it"
            ));
        }
    }
    println!(
        "{} cell-entry cases, {disagreements} disagree, {} named by {} exceptions",
        ENTRIES.len(),
        hits.values().sum::<usize>(),
        exceptions.len()
    );
    assert!(failures.is_empty(), "{failures:#?}");
}

/// Check 1r: where the entry is admitted, the rule-level judgement equals a rule-level row's
/// class, and is none on an accept.
#[test]
fn check_1r_every_rule_level_row_agrees_with_the_rule() {
    let mut failures = Vec::new();
    let mut judged = 0;
    for (case, entry) in ENTRIES.iter() {
        let got = entry.outcome();
        if !got.admits() {
            continue;
        }
        let rule = entry.rule_outcome(got);
        let row = match &EXPECTED[&case.id] {
            Expected::Refuse { name, .. } if RULE_CLASSES.contains(name) => Some(*name),
            Expected::Refuse { .. } => continue,
            Expected::Accept(_) => None,
        };
        if row.is_some() || rule.is_some() {
            judged += 1;
        }
        if row != rule {
            failures.push(format!(
                "{}: the table's rule-level row is {row:?}, the rule's {rule:?}",
                case.id
            ));
        }
    }
    println!("{judged} rule-level rows judged");
    assert!(failures.is_empty(), "{failures:#?}");
}

/// The template's entries abbreviated as `cells!` writes them.
fn abbreviated(template: &Template) -> Template {
    let mut template = template.clone();
    for entry in &mut template.entries {
        entry.spelling = abbreviate(&entry.stack, &entry.spelling);
    }
    template
}

/// A readable case's admission, the rule level included.
fn admitted(entry: &EntryCase, form: Form, spelling: &Spelling, template: &Template) -> Outcome {
    let mut context = entry.context.clone();
    if form == Form::Cells {
        context.other = context
            .other
            .map(|other| abbreviate(&entry.entry.stack, &other));
    }
    let got = outcome(
        form,
        entry.entry.side,
        &entry.entry.stack,
        spelling,
        &context,
    );
    let mut own = entry.entry.clone();
    own.spelling = spelling.clone();
    rule_outcome(template, &own, got).map_or(got, Outcome::Refuse)
}

fn accepted(id: &str) -> bool {
    matches!(EXPECTED.get(id), Some(Expected::Accept(_)))
}

/// Check 3 (P7): a readable entry is admitted exactly where the `cells!` entry it abbreviates
/// is, but for a listed readable-only refusal; and an accepted readable rule whose abbreviation
/// is a generated accepted case is linked to it by `same_k_as`.
#[test]
fn check_3_readable_abbreviates_cells() {
    let twins = ENTRIES
        .iter()
        .filter(|(case, _)| case.family == Family::Cells)
        .map(|(case, entry)| {
            (
                (
                    entry.entry.side,
                    entry.entry.cell.clone(),
                    entry.entry.spelling.clone(),
                ),
                case.id.as_str(),
            )
        })
        .collect::<Vec<_>>();
    let mut failures = Vec::new();
    let mut counts = BTreeMap::<String, usize>::new();
    for (case, entry) in ENTRIES.iter() {
        if !matches!(
            case.family,
            Family::Readable | Family::Claim | Family::ReadableRun
        ) {
            continue;
        }
        let readable = admitted(entry, entry.form, &entry.entry.spelling, &entry.template);
        let abbreviation = abbreviate(&entry.entry.stack, &entry.entry.spelling);
        let cells = admitted(
            entry,
            Form::Cells,
            &abbreviation,
            &abbreviated(&entry.template),
        );
        *counts
            .entry(format!(
                "{:?} readable {} cells {}",
                case.family,
                readable.admits(),
                cells.admits()
            ))
            .or_default() += 1;
        match (readable, cells.admits()) {
            (got, false) if got.admits() => failures.push(format!(
                "{}: admitted, but its `cells!` abbreviation {abbreviation:?} is {cells:?}",
                case.id
            )),
            (Outcome::Refuse(class), true) if !READABLE_ONLY.contains(&class) => {
                failures.push(format!(
                    "{}: refused as {class}, which is no readable-only class, while its `cells!` \
                     abbreviation is admitted",
                    case.id
                ));
            }
            _ => {}
        }
        if case.family != Family::Readable || !accepted(&case.id) {
            continue;
        }
        let Some((_, twin)) = twins.iter().find(|((side, cell, spelling), _)| {
            *side == entry.entry.side && *cell == entry.entry.cell && *spelling == abbreviation
        }) else {
            *counts
                .entry("readable accepted, no generated twin".to_owned())
                .or_default() += 1;
            continue;
        };
        if !accepted(twin) {
            continue;
        }
        let linked = |from: &str, to: &str| {
            TABLE
                .accept
                .get(from)
                .is_some_and(|accepted| accepted.same_k_as.iter().any(|other| other == to))
        };
        *counts
            .entry("readable accepted, twin accepted".to_owned())
            .or_default() += 1;
        if !linked(&case.id, twin) && !linked(twin, &case.id) {
            failures.push(format!(
                "{}: its `cells!` abbreviation {twin} is accepted and no `same_k_as` links them",
                case.id
            ));
        }
    }
    println!("{counts:#?}");
    assert!(failures.is_empty(), "{failures:#?}");
}

/// The classes whose advice adds the missing layer (P3 c).
const LAYER_CLASSES: [&str; 3] = [
    "cell-wrapper",
    "collection-without-instances",
    "optional-without-presence",
];

/// Check 4 (P3's reason): a refusal for a missing layer at the author's head has an advice, the
/// spelling with every missing layer added, and the advice is admitted at the head; and each
/// class's advised case is one the oracle admits.
#[test]
fn check_4_the_advice_of_a_missing_layer_is_admitted_at_the_head() {
    let mut failures = Vec::new();
    let mut counts = BTreeMap::<String, usize>::new();
    for (case, entry) in ENTRIES.iter() {
        let (form, side, stack, spelling) = (
            entry.form,
            entry.entry.side,
            &entry.entry.stack,
            &entry.entry.spelling,
        );
        let Err(refusal) = judge(form, side, stack, spelling, &entry.context) else {
            continue;
        };
        if refusal.step != Step::MissingLayer || refusal.depth != 0 {
            continue;
        }
        assert!(LAYER_CLASSES.contains(&refusal.class), "{}", case.id);
        let Some((advised, added)) =
            advise(form, side, stack, spelling, entry.context.other.as_ref())
        else {
            failures.push(format!(
                "{}: refused as {} for a missing layer, and no spelling adds the layers its \
                 head needs, so the advice would be refused again",
                case.id, refusal.class
            ));
            continue;
        };
        let verdict = match judge(form, side, stack, &advised, &entry.context) {
            Ok(_) => "admitted".to_owned(),
            Err(again) if again.depth == added => {
                failures.push(format!(
                    "{}: refused as {}, and the advice {advised:?} is refused again at the \
                     author's head as {}",
                    case.id, refusal.class, again.class
                ));
                "refused again".to_owned()
            }
            Err(again) => format!("deeper: {}", again.class),
        };
        *counts
            .entry(format!("{} {verdict}", refusal.class))
            .or_default() += 1;
    }
    let entries = ENTRIES
        .iter()
        .map(|(case, entry)| (case.id.as_str(), entry))
        .collect::<BTreeMap<_, _>>();
    for (name, class) in &TABLE.classes {
        for (case, entry) in ENTRIES.iter() {
            if !matches!(EXPECTED.get(&case.id), Some(Expected::Refuse { name: refused, .. }) if refused == name)
            {
                continue;
            }
            let _ = entry;
            for advised in class.advised_cases(&case.id) {
                if let Some(advised_entry) = entries.get(advised.as_str())
                    && !advised_entry.outcome().admits()
                {
                    failures.push(format!(
                        "{name}: advises {advised}, which the oracle refuses as {:?}",
                        advised_entry.outcome()
                    ));
                }
            }
        }
    }
    failures.sort();
    failures.dedup();
    println!("{counts:#?}");
    assert!(failures.is_empty(), "{failures:#?}");
}

/// The domain's stacks (§3, check 5): the computation, the leaves, a group, `?` over a leaf or a
/// group, `*` of each order, and a second computation.
const STACKS: [&str; 15] = [
    "computation",
    "leaf Int",
    "leaf List",
    "leaf Cons",
    "leaf Map",
    "leaf Set",
    "group",
    "? leaf Int",
    "? leaf List",
    "? leaf Map",
    "? group",
    "* List",
    "* Set",
    "* Map",
    "second computation",
];

/// The marks of the domain per form, as check 5 names them.
fn marks(form: Form) -> &'static [&'static str] {
    match form {
        Form::Readable | Form::Claim => &[
            "presence:some",
            "presence:none",
            "seq",
            "setinst",
            "map",
            "value:binder",
            "value:_",
            "value:literal",
            "value:record",
        ],
        Form::Cells => &[
            "presence:some",
            "presence:none",
            "leaf",
            "comp",
            "listinst",
            "setinst",
            "value:binder",
            "value:_",
            "value:fragment",
        ],
        Form::Init => &[
            "presence:some",
            "presence:absent",
            "presence:none",
            "comp",
            "seq",
            "map",
            "value:literal",
            "value:record",
            "value:call",
            "value:cfgvar",
        ],
    }
}

fn mark_name(form: Form, spelling: &Spelling) -> String {
    let readable = if form == Form::Claim {
        Form::Readable
    } else {
        form
    };
    match (mark(readable, spelling, false), spelling) {
        (Mark::Presence, Spelling::Present(_)) => "presence:some",
        (Mark::Presence, Spelling::Missing) => "presence:none",
        (Mark::Presence, _) => "presence:absent",
        (Mark::Seq, _) => "seq",
        (Mark::SetInst, _) => "setinst",
        (Mark::ListInst, _) => "listinst",
        (Mark::Map, _) => "map",
        (Mark::Leaf, _) => "leaf",
        (Mark::Comp, _) => "comp",
        (Mark::Value, Spelling::Binder(_) | Spelling::Alias(..)) => "value:binder",
        (Mark::Value, Spelling::Wild) => "value:_",
        (Mark::Value, Spelling::Literal | Spelling::MapLit(_)) => "value:literal",
        (Mark::Value, Spelling::Record(_)) => "value:record",
        (Mark::Value, Spelling::Fragment(_)) => "value:fragment",
        (Mark::Value, Spelling::Call(_)) => "value:call",
        (Mark::Value, Spelling::ConfigVar(_)) => "value:cfgvar",
        (Mark::Value, _) => "value:other",
    }
    .to_owned()
}

fn stack_name(cell: &str, stack: &[Layer]) -> String {
    let leaf = |notation: &Notation| match notation {
        Notation::Plain => "leaf Int",
        Notation::List => "leaf List",
        Notation::Cons => "leaf Cons",
        Notation::Map => "leaf Map",
        Notation::Set => "leaf Set",
    };
    match stack {
        [Layer::Computation] if cell == "code" => "second computation".to_owned(),
        [Layer::Computation] => "computation".to_owned(),
        [Layer::Leaf(notation)] => leaf(notation).to_owned(),
        [Layer::Group(_)] => "group".to_owned(),
        [Layer::Optional, Layer::Leaf(notation)] => format!("? {}", leaf(notation)),
        [Layer::Optional, Layer::Group(_)] => "? group".to_owned(),
        [Layer::Instances(order), ..] => format!(
            "* {}",
            match order {
                Order::List => "List",
                Order::Set => "Set",
                Order::Map => "Map",
            }
        ),
        other => format!("{other:?}"),
    }
}

/// The triples of the domain no generated case covers, which S5.0g adds: `(form, side, stack,
/// mark)`, each part a value or `*` for every value. 528 of the domain's 960 triples: the 8 stacks
/// the fixtures declare no cell of (`*` Set only on the run base's readable records and `cells!`
/// rules), and on every declared stack `cells!` instance braces and `_` in a `cells!` result.
const UNCOVERED: [(&str, &str, &str, &str); 10] = [
    ("*", "*", "leaf Cons", "*"),
    ("*", "*", "leaf Set", "*"),
    ("*", "*", "? leaf List", "*"),
    ("*", "*", "? leaf Map", "*"),
    ("*", "*", "? group", "*"),
    ("*", "*", "* Map", "*"),
    ("*", "*", "* Set", "*"),
    ("*", "*", "second computation", "*"),
    ("cells", "*", "*", "setinst"),
    ("cells", "result", "*", "value:_"),
];

fn form_name(form: Form) -> &'static str {
    match form {
        Form::Readable => "readable",
        Form::Claim => "claim",
        Form::Cells => "cells",
        Form::Init => "init",
    }
}

fn side_name(side: Side) -> &'static str {
    side.name()
}

/// Check 5: every (form × side × stack × mark) triple of the domain is some generated case's, or
/// is listed in [`UNCOVERED`]; and every entry of [`UNCOVERED`] lists some triple no case covers.
#[test]
fn check_5_the_generated_cases_cover_the_domain() {
    let mut covered = BTreeSet::new();
    for (case, entry) in ENTRIES.iter() {
        let declared = entry_cases::declared_stack(case, &entry.entry.cell);
        covered.insert((
            form_name(entry.form),
            side_name(entry.entry.side),
            stack_name(&entry.entry.cell, &declared),
            mark_name(entry.form, &entry.entry.spelling),
        ));
    }
    let mut uncovered = Vec::new();
    let mut domain = 0;
    for form in [Form::Readable, Form::Claim, Form::Cells, Form::Init] {
        let sides: &[Side] = if form == Form::Init {
            &[Side::Initializer]
        } else {
            &[Side::Subject, Side::Result]
        };
        for side in sides {
            for stack in STACKS {
                for mark in marks(form) {
                    domain += 1;
                    let triple = (
                        form_name(form),
                        side_name(*side),
                        stack.to_owned(),
                        (*mark).to_owned(),
                    );
                    if !covered.contains(&triple) {
                        uncovered.push(triple);
                    }
                }
            }
        }
    }
    let lists = |entry: &(&str, &str, &str, &str), triple: &(&str, &str, String, String)| {
        (entry.0 == "*" || entry.0 == triple.0)
            && (entry.1 == "*" || entry.1 == triple.1)
            && (entry.2 == "*" || entry.2 == triple.2)
            && (entry.3 == "*" || entry.3 == triple.3)
    };
    let mut failures = uncovered
        .iter()
        .filter(|triple| !UNCOVERED.iter().any(|entry| lists(entry, triple)))
        .map(|triple| format!("uncovered and not listed: {triple:?}"))
        .collect::<Vec<_>>();
    for entry in &UNCOVERED {
        if !uncovered.iter().any(|triple| lists(entry, triple)) {
            failures.push(format!(
                "UNCOVERED lists {entry:?}, which cases cover: remove it"
            ));
        }
    }
    println!(
        "domain {domain}, covered {}, uncovered {}",
        domain - uncovered.len(),
        uncovered.len()
    );
    assert!(
        failures.is_empty(),
        "{} failures: {failures:#?}",
        failures.len()
    );
}
