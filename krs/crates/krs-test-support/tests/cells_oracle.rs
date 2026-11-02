//! The cells oracle's checks (design S5, §3): the table's cell-entry rows against the principles
//! (checks 0, 1, 1r), the product's admission against the table (check 2), the readable form
//! against the `cells!` form it abbreviates (check 3), the advice of a missing layer (check 4),
//! and the generated coverage of the domain (check 5).

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::sync::LazyLock;

use krs_ir::cell_kind::{self, CellKind};
use krs_syntax::cell_entries::{self, EntrySide};
use krs_syntax::cell_entry::{
    EntryForm, EntryMap, EntryReading, EntryRecord, EntryRest, EntrySeq, EntrySpelling, RecordTail,
    RestPlace,
};
use krs_syntax::{ConfigurationCell, ConfigurationDeclaration};
use syn::parse::Parser;

use krs_test_support::class_matrix::cells_oracle::{
    CODES, ENTRY_CLASSES, Entries, EntryCase, Form, Group, LINT_CLASSES, Layer, Mark, Notation,
    Order, Outcome, READABLE_ONLY, RULE_CLASSES, Record, RecordRest, Rest, RestAt, SORT_CLASSES,
    Seq, Spelling, Step, Template, abbreviate, advise, judge, mark, outcome, rule_outcome,
};
use krs_test_support::class_matrix::invariants::registry_kind;
use krs_test_support::class_matrix::table::{Expected, Glob, TERM_ACCEPTS_FILE, Table, twin};
use krs_test_support::class_matrix::{self, Base, Case, Family, Side, entry_cases};

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
    let exceptions = exceptions();
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

/// The exceptions of the table, with their globs parsed.
fn exceptions() -> Vec<(Glob, String, String)> {
    TABLE
        .cell_exceptions
        .iter()
        .map(|exception| {
            let glob = Glob::parse(&exception.pattern).expect("a parsed table's globs parse");
            (glob, exception.pattern.clone(), exception.principle.clone())
        })
        .collect()
}

/// A base's configuration as `krs_syntax` parses it from the rendered source: the
/// `#[k::configuration]` struct and every `#[k::cell]` group, without rustc.
struct Configuration {
    root: String,
    declarations: Vec<ConfigurationDeclaration>,
}

impl Configuration {
    fn parse(source: &str) -> Option<Self> {
        let file = syn::parse_file(source).ok()?;
        let mut root = None;
        let mut declarations = Vec::new();
        for item in file.items {
            let syn::Item::Struct(item) = item else {
                continue;
            };
            let attribute = |name: &str| {
                item.attrs.iter().any(|attribute| {
                    attribute
                        .path()
                        .segments
                        .last()
                        .is_some_and(|segment| segment.ident == name)
                })
            };
            if attribute("configuration") {
                root = Some(item.ident.to_string());
            } else if !attribute("cell") {
                continue;
            }
            declarations.push(
                ConfigurationDeclaration::from_item(item)
                    .unwrap_or_else(|error| panic!("a fixture's cell struct parses: {error:?}")),
            );
        }
        Some(Self {
            root: root?,
            declarations,
        })
    }

    /// The cell `name` with the ancestors between the configuration's level and it, found
    /// depth first.
    fn find(&self, name: &str) -> Option<(Vec<ConfigurationCell<'_>>, ConfigurationCell<'_>)> {
        fn search<'c>(
            fields: Vec<ConfigurationCell<'c>>,
            name: &str,
            ancestors: &mut Vec<ConfigurationCell<'c>>,
        ) -> Option<ConfigurationCell<'c>> {
            for field in fields {
                if field.field().name() == name {
                    return Some(field);
                }
                ancestors.push(field);
                if let Some(found) = search(field.children(), name, ancestors) {
                    return Some(found);
                }
                ancestors.pop();
            }
            None
        }
        let root = self
            .declarations
            .iter()
            .find(|declaration| *declaration.name() == self.root)?;
        let fields = root
            .cells()
            .iter()
            .map(|field| ConfigurationCell::new(field, &self.declarations, &[]))
            .collect();
        let mut ancestors = Vec::new();
        let field = search(fields, name, &mut ancestors)?;
        Some((ancestors, field))
    }

    /// The stack an entry naming `cell` is judged against: `CellKind::{path, of}`.
    fn stack(&self, cell: &str) -> Vec<cell_kind::Layer> {
        let (ancestors, field) = self
            .find(cell)
            .unwrap_or_else(|| panic!("the configuration declares the cell `{cell}`"));
        CellKind::entry(&ancestors, &field).layers
    }
}

/// Every cell-entry base's configuration, parsed from the first of its cases whose rendered
/// source `syn` parses (syn's nodes hold spans, which a static cannot share between threads).
fn configurations() -> BTreeMap<Base, Configuration> {
    let mut configurations = BTreeMap::new();
    for (case, _) in ENTRIES.iter() {
        if configurations.contains_key(&case.base) {
            continue;
        }
        if let Some(configuration) = Configuration::parse(&case.render().source) {
            configurations.insert(case.base, configuration);
        }
    }
    configurations
}

/// The product's layer as the oracle writes it.
fn oracle_layer(layer: &cell_kind::Layer) -> Layer {
    let order = |order: cell_kind::Order| match order {
        cell_kind::Order::List => Order::List,
        cell_kind::Order::Set => Order::Set,
        cell_kind::Order::Map => Order::Map,
    };
    match layer {
        cell_kind::Layer::Optional => Layer::Optional,
        cell_kind::Layer::Instances(by) => Layer::Instances(order(*by)),
        cell_kind::Layer::Computation => Layer::Computation,
        cell_kind::Layer::Leaf(notation) => Layer::Leaf(match notation {
            cell_kind::Notation::Plain => Notation::Plain,
            cell_kind::Notation::List => Notation::List,
            cell_kind::Notation::Cons => Notation::Cons,
            cell_kind::Notation::Map => Notation::Map,
            cell_kind::Notation::Set => Notation::Set,
        }),
        cell_kind::Layer::Group(group) => Layer::Group(Group {
            name: group.name.clone(),
            children: group
                .children
                .iter()
                .map(|(name, kind)| (name.clone(), kind.layers.iter().map(oracle_layer).collect()))
                .collect(),
        }),
    }
}

/// The product's spelling as the oracle declares it: the marks and names, a literal's text
/// dropped.
fn declared_as(spelling: &EntrySpelling) -> Spelling {
    let seq = |seq: &EntrySeq| Seq {
        items: seq.items.iter().map(declared_as).collect(),
        rest: seq.rest.as_ref().map(|(rest, place)| {
            (
                rest_as(rest),
                match place {
                    RestPlace::Back => RestAt::Back,
                    RestPlace::Front => RestAt::Front,
                },
            )
        }),
    };
    let map = |map: &EntryMap| Entries {
        entries: map
            .entries
            .iter()
            .map(|(key, value)| (declared_as(key), declared_as(value)))
            .collect(),
        rest: map.rest.as_ref().map(rest_as),
    };
    let record = |record: &EntryRecord| Record {
        head: record.head.clone(),
        fields: record
            .fields
            .iter()
            .map(|(name, value)| (name.clone(), declared_as(value)))
            .collect(),
        rest: match &record.tail {
            RecordTail::Exact => RecordRest::Exact,
            RecordTail::Open => RecordRest::Open,
            RecordTail::Update(base) => RecordRest::Update(base.clone()),
        },
    };
    let boxed = |inner: &EntrySpelling| Box::new(declared_as(inner));
    match spelling {
        EntrySpelling::Wild => Spelling::Wild,
        EntrySpelling::Binder(name) => Spelling::Binder(name.clone()),
        EntrySpelling::Literal(_) => Spelling::Literal,
        EntrySpelling::Call(arguments) => {
            Spelling::Call(arguments.iter().map(declared_as).collect())
        }
        EntrySpelling::ConfigVar(name) => Spelling::ConfigVar(name.clone()),
        EntrySpelling::Present(inner) => Spelling::Present(boxed(inner)),
        EntrySpelling::Missing => Spelling::Missing,
        EntrySpelling::Absent(inner) => Spelling::Absent(boxed(inner)),
        EntrySpelling::Brackets(items) => Spelling::Brackets(seq(items)),
        EntrySpelling::Braces(items) => Spelling::Braces(seq(items)),
        EntrySpelling::MapRead(entries) => Spelling::MapRead(map(entries)),
        EntrySpelling::Record(fields) => Spelling::Record(record(fields)),
        EntrySpelling::Alias(name, inner) => Spelling::Alias(name.clone(), boxed(inner)),
        EntrySpelling::Cell(inner) => Spelling::Cell(boxed(inner)),
        EntrySpelling::KCell(items) => Spelling::KCell(seq(items)),
        EntrySpelling::Fragment(fields) => Spelling::Fragment(record(fields)),
        EntrySpelling::InstanceList(items) => Spelling::InstList(seq(items)),
        EntrySpelling::InstanceSet(items) => Spelling::InstSet(seq(items)),
        EntrySpelling::MapLiteral(entries) => Spelling::MapLit(map(entries)),
        EntrySpelling::KMacro(items) => Spelling::KMacro(seq(items)),
    }
}

fn rest_as(rest: &EntryRest) -> Rest {
    match rest {
        EntryRest::Anonymous => Rest::Anon,
        EntryRest::Named(name) => Rest::Named(name.clone()),
        EntryRest::Splice(name) => Rest::Splice(name.clone()),
    }
}

/// The oracle's declared spelling of a template's other side as the product reads spellings,
/// for pairing: only the marks and rests matter there.
fn product_of(spelling: &Spelling) -> EntrySpelling {
    let seq = |seq: &Seq| EntrySeq {
        items: seq.items.iter().map(product_of).collect(),
        rest: seq.rest.as_ref().map(|(rest, at)| {
            (
                product_rest(rest),
                match at {
                    RestAt::Back => RestPlace::Back,
                    RestAt::Front => RestPlace::Front,
                },
            )
        }),
    };
    let map = |entries: &Entries| EntryMap {
        entries: entries
            .entries
            .iter()
            .map(|(key, value)| (product_of(key), product_of(value)))
            .collect(),
        rest: entries.rest.as_ref().map(product_rest),
    };
    let record = |record: &Record| EntryRecord {
        head: record.head.clone(),
        fields: record
            .fields
            .iter()
            .map(|(name, value)| (name.clone(), product_of(value)))
            .collect(),
        tail: match &record.rest {
            RecordRest::Exact => RecordTail::Exact,
            RecordRest::Open => RecordTail::Open,
            RecordRest::Update(base) => RecordTail::Update(base.clone()),
        },
    };
    let boxed = |inner: &Spelling| Box::new(product_of(inner));
    match spelling {
        Spelling::Wild => EntrySpelling::Wild,
        Spelling::Binder(name) => EntrySpelling::Binder(name.clone()),
        Spelling::Literal => EntrySpelling::Literal("0".to_owned()),
        Spelling::Call(arguments) => {
            EntrySpelling::Call(arguments.iter().map(product_of).collect())
        }
        Spelling::ConfigVar(name) => EntrySpelling::ConfigVar(name.clone()),
        Spelling::Present(inner) => EntrySpelling::Present(boxed(inner)),
        Spelling::Missing => EntrySpelling::Missing,
        Spelling::Absent(inner) => EntrySpelling::Absent(boxed(inner)),
        Spelling::Brackets(items) => EntrySpelling::Brackets(seq(items)),
        Spelling::Braces(items) => EntrySpelling::Braces(seq(items)),
        Spelling::MapRead(entries) => EntrySpelling::MapRead(map(entries)),
        Spelling::Record(fields) => EntrySpelling::Record(record(fields)),
        Spelling::Alias(name, inner) => EntrySpelling::Alias(name.clone(), boxed(inner)),
        Spelling::Cell(inner) => EntrySpelling::Cell(boxed(inner)),
        Spelling::KCell(items) => EntrySpelling::KCell(seq(items)),
        Spelling::Fragment(fields) => EntrySpelling::Fragment(record(fields)),
        Spelling::InstList(items) => EntrySpelling::InstanceList(seq(items)),
        Spelling::InstSet(items) => EntrySpelling::InstanceSet(seq(items)),
        Spelling::MapLit(entries) => EntrySpelling::MapLiteral(map(entries)),
        Spelling::KMacro(items) => EntrySpelling::KMacro(seq(items)),
    }
}

fn product_rest(rest: &Rest) -> EntryRest {
    match rest {
        Rest::Anon => EntryRest::Anonymous,
        Rest::Named(name) => EntryRest::Named(name.clone()),
        Rest::Splice(name) => EntryRest::Splice(name.clone()),
    }
}

/// The case's entry as the product reads it from the rendered source: the entry's `key: value`
/// field, and below a plain group's record the field that names the cell.
fn parsed_entry(case: &Case, entry: &EntryCase) -> Result<EntrySpelling, String> {
    let rendered = case.render();
    let text = &rendered.source[rendered.cases[0].entry.clone()];
    let form = match entry.form {
        Form::Readable => EntryForm::Readable,
        Form::Claim => EntryForm::Claim,
        Form::Cells => EntryForm::Cells,
        Form::Init => EntryForm::Initializer,
    };
    let variables = entry
        .template
        .variables
        .iter()
        .map(|(name, _)| name.clone())
        .collect::<Vec<_>>();
    let reading = EntryReading::new(form, &variables);
    let (key, mut value) = (|input: syn::parse::ParseStream<'_>| reading.parse_field(input))
        .parse_str(text)
        .map_err(|error| format!("`{text}`: {error}"))?;
    let mut name = key
        .segments
        .last()
        .map(|segment| segment.ident.to_string())
        .unwrap_or_default();
    while name != entry.entry.cell {
        let EntrySpelling::Record(record) = value else {
            return Err(format!("`{text}` names no cell `{}`", entry.entry.cell));
        };
        let Some((field, inner)) = record.fields.into_iter().next() else {
            return Err(format!("`{text}` names no cell `{}`", entry.entry.cell));
        };
        (name, value) = (field, inner);
    }
    Ok(value)
}

const fn product_side(side: Side) -> EntrySide {
    match side {
        Side::Subject => EntrySide::Subject,
        Side::Result => EntrySide::Result,
        _ => EntrySide::Initializer,
    }
}

/// The product's judgement of a case's entry: `admit` (form and kind), then `pair`.
fn product_outcome(
    entry: &EntryCase,
    stack: &[cell_kind::Layer],
    spelling: &EntrySpelling,
) -> Outcome {
    let form = match entry.form {
        Form::Readable => EntryForm::Readable,
        Form::Claim => EntryForm::Claim,
        Form::Cells => EntryForm::Cells,
        Form::Init => EntryForm::Initializer,
    };
    let side = product_side(entry.entry.side);
    let bound = |name: &str| entry.context.bound.iter().any(|bound| bound == name);
    let admitted = match cell_entries::admit(form, side, stack, spelling, &bound) {
        Ok(admitted) => admitted,
        Err(refusal) => return Outcome::Refuse(refusal.class()),
    };
    let other = entry.context.other.as_ref().map(product_of);
    match cell_entries::pair(side, stack, spelling, other.as_ref(), entry.context.written) {
        Err(refusal) => Outcome::Refuse(refusal.class()),
        Ok(None) if admitted.sorted => Outcome::After,
        Ok(lint) => Outcome::Admit {
            lint: lint.map(cell_entries::Lint::class),
        },
    }
}

/// Check 2: the product against the table, steps 1–3. For every cell-entry case, the product
/// reads the entry from the rendered source (`krs_syntax::cell_entry`), reads the cell's stack
/// from the configuration `krs_syntax` parses (`krs_ir::cell_kind::CellKind::{path, of}`), and
/// judges it (`krs_syntax::cell_entries::{admit, pair}`). Its answer is the oracle's, or, on a
/// case a `[cell-exception]` names, the table's: the exception is a stated departure in which the
/// table is authoritative. There is no pending list.
///
/// Two agreements come first: the stack `CellKind` reads equals the test-side stack of every
/// fixture cell an entry names (kind agreement), and the spelling the product parses is the one
/// the generator declares (spelling agreement).
#[test]
fn check_2_the_product_admits_as_the_table_says() {
    let exceptions = exceptions();
    let configurations = configurations();
    let mut failures = Vec::new();
    let mut kinds = BTreeSet::new();
    let mut counts = BTreeMap::<String, usize>::new();
    for (case, entry) in ENTRIES.iter() {
        let Some(configuration) = configurations.get(&case.base) else {
            failures.push(format!(
                "{}: no rendered source of base {:?} parses",
                case.id, case.base
            ));
            continue;
        };
        let cell = &entry.entry.cell;
        let stack = configuration.stack(cell);
        let read = stack.iter().map(oracle_layer).collect::<Vec<_>>();
        if kinds.insert((case.base, cell.clone())) {
            let declared = entry_cases::declared_stack(case, cell);
            if read != declared {
                failures.push(format!(
                    "{:?}/{cell}: CellKind reads {read:?}, the fixture declares {declared:?}",
                    case.base
                ));
            }
        }
        let spelling = match parsed_entry(case, entry) {
            Ok(spelling) => spelling,
            Err(error) => {
                failures.push(format!(
                    "{}: the product does not read the entry: {error}",
                    case.id
                ));
                continue;
            }
        };
        if declared_as(&spelling) != entry.entry.spelling {
            failures.push(format!(
                "{}: the product reads {:?}, the generator declares {:?}",
                case.id,
                declared_as(&spelling),
                entry.entry.spelling
            ));
            continue;
        }
        let got = product_outcome(entry, &stack, &spelling);
        let excepted = !naming(&case.id, &exceptions).is_empty();
        let want = match &EXPECTED[&case.id] {
            Expected::Refuse { name, .. } if excepted => Outcome::Refuse(name),
            _ if excepted => {
                failures.push(format!("{}: an exception names an accepted case", case.id));
                continue;
            }
            _ => entry.outcome(),
        };
        *counts
            .entry(format!(
                "{} {}",
                if excepted { "excepted" } else { "oracle" },
                if got == want { "agree" } else { "disagree" }
            ))
            .or_default() += 1;
        if got != want {
            failures.push(format!(
                "{}: the product says {got:?}, the {} {want:?}",
                case.id,
                if excepted {
                    "table (an exception names it)"
                } else {
                    "principles"
                }
            ));
        }
    }
    println!("{} fixture cells' kinds compared; {counts:#?}", kinds.len());
    assert!(
        failures.is_empty(),
        "{} failures: {failures:#?}",
        failures.len()
    );
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
