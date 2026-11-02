//! The cells oracle's checks (design S5, §3): the table's cell-entry rows against the principles
//! (checks 0, 1, 1r), the product's admission against the table (check 2), the readable form
//! against the `cells!` form it abbreviates (check 3), the advice of a missing layer (check 4),
//! and the generated coverage of the domain (check 5).

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
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

/// Check 0: every class the oracle answers with is a class of the table with the oracle's code.
/// Whether that code is registered as the class's `proposed` says, and is an author code, is the
/// table's resolution's (`Table::resolve_cases`, `check_codes`), which every check reading
/// [`EXPECTED`] runs; check 0 does not restate it.
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
            Some(_) => {}
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

/// The rule-level classes no generated case's row has, so check 1r cannot see `rule_outcome`
/// miss them (it sees it answer them where no row does), with why; S5.0g generates them.
const RULE_UNCOVERED: [(&str, &str); 1] = [(
    "rule-changes-no-cell",
    "every generated rule writes a cell (its computation's, at least)",
)];

/// Check 1r: where the entry is admitted, the rule-level judgement equals a rule-level row's
/// class, and is none on an accept; and every rule-level class is some generated case's row, or
/// is listed in [`RULE_UNCOVERED`].
#[test]
fn check_1r_every_rule_level_row_agrees_with_the_rule() {
    let mut failures = Vec::new();
    let mut judged = 0;
    let mut rows = BTreeSet::new();
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
        rows.extend(row);
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
    for class in RULE_CLASSES {
        let listed = RULE_UNCOVERED.iter().any(|(listed, _)| *listed == class);
        match (rows.contains(class), listed) {
            (false, false) => failures.push(format!(
                "{class}: no generated case's row has it, so a rule_outcome that misses it \
                 passes; generate one or list it in RULE_UNCOVERED"
            )),
            (true, true) => failures.push(format!(
                "{class}: listed in RULE_UNCOVERED, and a generated case's row has it: remove it"
            )),
            _ => {}
        }
    }
    println!("{judged} rule-level rows judged, classes with rows {rows:?}");
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

    /// What an entry naming `cell` is judged against: `CellKind::{path, of}`, apart.
    fn kind(&self, cell: &str) -> cell_kind::EntryKind {
        let (ancestors, field) = self
            .find(cell)
            .unwrap_or_else(|| panic!("the configuration declares the cell `{cell}`"));
        CellKind::entry(&ancestors, &field)
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

/// The product's judgement of a case's entry: `admit` (form, path and kind), then `pair`.
fn product_outcome(
    entry: &EntryCase,
    kind: &cell_kind::EntryKind,
    spelling: &EntrySpelling,
) -> Outcome {
    let (path, stack) = (&kind.path.layers[..], &kind.own.layers[..]);
    let form = match entry.form {
        Form::Readable => EntryForm::Readable,
        Form::Claim => EntryForm::Claim,
        Form::Cells => EntryForm::Cells,
        Form::Init => EntryForm::Initializer,
    };
    let side = product_side(entry.entry.side);
    let bound = |name: &str| entry.context.bound.iter().any(|bound| bound == name);
    let admitted = match cell_entries::admit(form, side, path, stack, spelling, &bound) {
        Ok(admitted) => admitted,
        Err(refusal) => return Outcome::Refuse(refusal.class()),
    };
    let other = entry.context.other.as_ref().map(product_of);
    match cell_entries::pair(
        form,
        side,
        stack,
        spelling,
        other.as_ref(),
        entry.context.written,
    ) {
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
        let kind = configuration.kind(cell);
        let read = kind.own.layers.iter().map(oracle_layer).collect::<Vec<_>>();
        let path = kind
            .path
            .layers
            .iter()
            .map(oracle_layer)
            .collect::<Vec<_>>();
        if kinds.insert((case.base, cell.clone())) {
            let declared = entry_cases::declared_stack(case, cell);
            if read != declared || path != entry.entry.path {
                failures.push(format!(
                    "{:?}/{cell}: CellKind reads {path:?} then {read:?}, the fixture declares \
                     {:?} then {declared:?}",
                    case.base, entry.entry.path
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
        let got = product_outcome(entry, &kind, &spelling);
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
        &entry.entry.path,
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
/// spelling with every missing layer added, and the advice is admitted at the head.
///
/// That each class's `advice` case is one the oracle admits is not checked here: the table's
/// resolution refuses an advice that is no accepted case (`AdviceNotAccepted`), check 1 makes
/// every accepted case agree with the oracle unless an exception names it, and check 2 refuses an
/// exception that names an accepted case.
#[test]
fn check_4_the_advice_of_a_missing_layer_is_admitted_at_the_head() {
    let mut failures = Vec::new();
    let mut counts = BTreeMap::<String, usize>::new();
    for (case, entry) in ENTRIES.iter() {
        let (form, side, path, stack, spelling) = (
            entry.form,
            entry.entry.side,
            &entry.entry.path,
            &entry.entry.stack,
            &entry.entry.spelling,
        );
        let Err(refusal) = judge(form, side, path, stack, spelling, &entry.context) else {
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
        let verdict = match judge(form, side, path, stack, &advised, &entry.context) {
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

/// The tuples of the domain no generated case covers, which S5.0g adds: `(form, side, path,
/// stack, mark)`, each part a value or `*` for every value. On the cell's own level (path
/// `none`): the 8 stacks the fixtures declare no cell of (`*` Set only on the run base's readable
/// records and `cells!` rules), and on every declared stack `cells!` instance braces and `_` in a
/// `cells!` result; every result over a cell its subject does not match (Q1's overwrite, R2);
/// and every entry naming a cell below a `?` or `*` ancestor (S1 (b), R1).
const UNCOVERED: [(&str, &str, &str, &str, &str); 13] = [
    ("*", "*", "none", "leaf Cons", "*"),
    ("*", "*", "none", "leaf Set", "*"),
    ("*", "*", "none", "? leaf List", "*"),
    ("*", "*", "none", "? leaf Map", "*"),
    ("*", "*", "none", "? group", "*"),
    ("*", "*", "none", "* Map", "*"),
    ("*", "*", "none", "* Set", "*"),
    ("*", "*", "none", "second computation", "*"),
    ("cells", "*", "none", "*", "setinst"),
    ("cells", "result", "none", "*", "value:_"),
    ("*", "result-unmatched", "none", "*", "*"),
    ("*", "*", "below ?", "*", "*"),
    ("*", "*", "below *", "*", "*"),
];

fn form_name(form: Form) -> &'static str {
    match form {
        Form::Readable => "readable",
        Form::Claim => "claim",
        Form::Cells => "cells",
        Form::Init => "init",
    }
}

/// The side as check 5 names it: a result over a cell its subject does not match is
/// `result-unmatched`.
fn side_name(entry: &EntryCase) -> &'static str {
    match entry.entry.side {
        Side::Result if entry.context.other.is_none() => "result-unmatched",
        side => side.name(),
    }
}

/// The path as check 5 names it: the outermost marked ancestor's layer, if any.
fn path_name(path: &[Layer]) -> &'static str {
    match path.first() {
        None => "none",
        Some(Layer::Optional) => "below ?",
        Some(_) => "below *",
    }
}

/// Check 5: every (form × side × path × stack × mark) tuple of the domain is some generated
/// case's, or is listed in [`UNCOVERED`]; and every entry of [`UNCOVERED`] lists some tuple no
/// case covers. A rule form's sides are its subject, its result over a matched cell and over an
/// unmatched one; an initializer's is its value, which names no cell through a path (a struct
/// literal names its own fields only).
#[test]
fn check_5_the_generated_cases_cover_the_domain() {
    let mut covered = BTreeSet::new();
    for (case, entry) in ENTRIES.iter() {
        let declared = entry_cases::declared_stack(case, &entry.entry.cell);
        covered.insert((
            form_name(entry.form),
            side_name(entry),
            path_name(&entry.entry.path),
            stack_name(&entry.entry.cell, &declared),
            mark_name(entry.form, &entry.entry.spelling),
        ));
    }
    let mut uncovered = Vec::new();
    let mut domain = 0;
    for form in [Form::Readable, Form::Claim, Form::Cells, Form::Init] {
        let (sides, paths): (&[&str], &[&str]) = if form == Form::Init {
            (&["initializer"], &["none"])
        } else {
            (
                &["subject", "result", "result-unmatched"],
                &["none", "below ?", "below *"],
            )
        };
        for side in sides {
            for path in paths {
                for stack in STACKS {
                    for mark in marks(form) {
                        domain += 1;
                        let tuple = (
                            form_name(form),
                            *side,
                            *path,
                            stack.to_owned(),
                            (*mark).to_owned(),
                        );
                        if !covered.contains(&tuple) {
                            uncovered.push(tuple);
                        }
                    }
                }
            }
        }
    }
    let lists = |entry: &(&str, &str, &str, &str, &str),
                 tuple: &(&str, &str, &str, String, String)| {
        (entry.0 == "*" || entry.0 == tuple.0)
            && (entry.1 == "*" || entry.1 == tuple.1)
            && (entry.2 == "*" || entry.2 == tuple.2)
            && (entry.3 == "*" || entry.3 == tuple.3)
            && (entry.4 == "*" || entry.4 == tuple.4)
    };
    let mut failures = uncovered
        .iter()
        .filter(|tuple| !UNCOVERED.iter().any(|entry| lists(entry, tuple)))
        .map(|tuple| format!("uncovered and not listed: {tuple:?}"))
        .collect::<Vec<_>>();
    for entry in &UNCOVERED {
        if !uncovered.iter().any(|tuple| lists(entry, tuple)) {
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

/// The oracle's layer as the product writes it.
fn product_layer(layer: &Layer) -> cell_kind::Layer {
    let order = |order: Order| match order {
        Order::List => cell_kind::Order::List,
        Order::Set => cell_kind::Order::Set,
        Order::Map => cell_kind::Order::Map,
    };
    match layer {
        Layer::Optional => cell_kind::Layer::Optional,
        Layer::Instances(by) => cell_kind::Layer::Instances(order(*by)),
        Layer::Computation => cell_kind::Layer::Computation,
        Layer::Leaf(notation) => cell_kind::Layer::Leaf(match notation {
            Notation::Plain => cell_kind::Notation::Plain,
            Notation::List => cell_kind::Notation::List,
            Notation::Cons => cell_kind::Notation::Cons,
            Notation::Map => cell_kind::Notation::Map,
            Notation::Set => cell_kind::Notation::Set,
        }),
        Layer::Group(group) => cell_kind::Layer::Group(cell_kind::GroupKind {
            name: group.name.clone(),
            children: group
                .children
                .iter()
                .map(|(name, stack)| {
                    (
                        name.clone(),
                        CellKind {
                            layers: stack.iter().map(product_layer).collect(),
                        },
                    )
                })
                .collect(),
        }),
    }
}

const fn entry_form(form: Form) -> EntryForm {
    match form {
        Form::Readable => EntryForm::Readable,
        Form::Claim => EntryForm::Claim,
        Form::Cells => EntryForm::Cells,
        Form::Init => EntryForm::Initializer,
    }
}

/// One entry outside the generated cases: its form and side, its cell's path and own stack
/// (as the oracle writes them), its text, and its rule's other side and bound names.
struct Probe<'p> {
    form: Form,
    side: Side,
    path: &'p [Layer],
    stack: &'p [Layer],
    text: &'p str,
    /// For a result, the subject's entry of the cell, `None` where the subject does not match
    /// it; for a subject, unread.
    other: Option<&'p str>,
    /// For a subject, whether the result writes the cell.
    written: bool,
    bound: &'p [&'p str],
}

impl Probe<'_> {
    fn reading(&self) -> EntryReading<'static> {
        static VARIABLES: LazyLock<Vec<String>> = LazyLock::new(|| vec!["pgm".to_owned()]);
        EntryReading::new(entry_form(self.form), &VARIABLES)
    }

    fn read(&self, text: &str) -> EntrySpelling {
        self.reading()
            .value(
                text.parse()
                    .unwrap_or_else(|error| panic!("`{text}` lexes: {error}")),
            )
            .unwrap_or_else(|error| panic!("`{text}` reads: {error}"))
    }

    fn context(&self) -> class_matrix::cells_oracle::Context {
        class_matrix::cells_oracle::Context {
            bound: self.bound.iter().map(|name| (*name).to_owned()).collect(),
            other: self.other.map(|text| declared_as(&self.read(text))),
            written: self.written,
        }
    }

    /// The oracle's outcome.
    fn oracle(&self) -> Outcome {
        let stack = if self.side == Side::Initializer {
            match self.stack.split_first() {
                Some((Layer::Instances(_), template)) => template,
                _ => self.stack,
            }
        } else {
            self.stack
        };
        outcome(
            self.form,
            self.side,
            self.path,
            stack,
            &declared_as(&self.read(self.text)),
            &self.context(),
        )
    }

    /// The product's outcome, `admit` then `pair`, on the same entry.
    fn product(&self) -> Outcome {
        let form = entry_form(self.form);
        let side = product_side(self.side);
        let path = self.path.iter().map(product_layer).collect::<Vec<_>>();
        let stack = self.stack.iter().map(product_layer).collect::<Vec<_>>();
        let spelling = self.read(self.text);
        let bound = |name: &str| self.bound.contains(&name);
        let admitted = match cell_entries::admit(form, side, &path, &stack, &spelling, &bound) {
            Ok(admitted) => admitted,
            Err(refusal) => return Outcome::Refuse(refusal.class()),
        };
        let pair_stack = match (side, stack.split_first()) {
            (EntrySide::Initializer, Some((cell_kind::Layer::Instances(_), template))) => template,
            _ => &stack[..],
        };
        let other = self.other.map(|text| self.read(text));
        match cell_entries::pair(
            form,
            side,
            pair_stack,
            &spelling,
            other.as_ref(),
            self.written,
        ) {
            Err(refusal) => Outcome::Refuse(refusal.class()),
            Ok(None) if admitted.sorted => Outcome::After,
            Ok(lint) => Outcome::Admit {
                lint: lint.map(cell_entries::Lint::class),
            },
        }
    }
}

fn int() -> Vec<Layer> {
    vec![Layer::Leaf(Notation::Plain)]
}

/// The sweep's group `G`, two `Int` children (so a record naming one is not complete).
fn group_g() -> Layer {
    Layer::Group(Group {
        name: "G".to_owned(),
        children: vec![("a".to_owned(), int()), ("b".to_owned(), int())],
    })
}

/// The review's probes of S1 (b) and Q1's overwrite (R1, R2), outside every generated case: the
/// oracle and the product both refuse each, with the class the principles give.
#[test]
fn the_oracle_and_the_product_refuse_the_reviews_probes() {
    let optional = [Layer::Optional];
    let map = [Layer::Instances(Order::Map)];
    let list = [Layer::Instances(Order::List)];
    let int = int();
    let probe = |form, side, path, stack, text, other| Probe {
        form,
        side,
        path,
        stack,
        text,
        other,
        written: false,
        bound: &["x", "y"],
    };
    let (subject, result) = (Side::Subject, Side::Result);
    let probes = [
        // R1: an ancestor's mark spelled in the entry.
        (
            probe(Form::Readable, subject, &optional, &int, "Some(x)", None),
            "optional-without-presence",
        ),
        (
            probe(Form::Readable, subject, &map, &int, "{ .. }", None),
            "collection-without-instances",
        ),
        (
            probe(Form::Readable, subject, &list, &int, "[x, ..]", None),
            "collection-without-instances",
        ),
        (
            probe(Form::Cells, subject, &list, &int, "[x, ..]", None),
            "collection-without-instances",
        ),
        // R2: a result over a cell the subject does not match.
        (
            probe(
                Form::Readable,
                result,
                &[],
                &[Layer::Optional, Layer::Leaf(Notation::Plain)],
                "Some(1)",
                None,
            ),
            "unmatched-optional-result",
        ),
        (
            probe(
                Form::Readable,
                result,
                &[],
                &[Layer::Leaf(Notation::List)],
                "[x, ..]",
                None,
            ),
            "rest-mismatch",
        ),
        (
            probe(
                Form::Readable,
                result,
                &[],
                &[Layer::Computation],
                "[x, ..]",
                None,
            ),
            "continuation-in-readable",
        ),
    ];
    let mut failures = Vec::new();
    for (probe, class) in &probes {
        let want = Outcome::Refuse(class);
        for (who, got) in [("oracle", probe.oracle()), ("product", probe.product())] {
            if got != want {
                failures.push(format!(
                    "{:?} {:?} below {:?} on {:?}: `{}`: the {who} says {got:?}, the principles \
                     {want:?}",
                    probe.form, probe.side, probe.path, probe.stack, probe.text
                ));
            }
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

/// Where the sweep of [`outcome`] is kept, checked in so that a change to `outcome` shows as a
/// diff (`KRS_CELLS_SWEEP_RECORD=1` rewrites it).
const SWEEP_FILE: &str = "cells-outcome-sweep.tsv";

/// The sweep's short names of the classes (its legend).
const SWEEP_LEGEND: [(&str, &str); 20] = [
    ("absence-test-without-creation", "atc"),
    ("anonymous-rest-in-map-literal", "arm"),
    ("bracket-reading", "br"),
    ("cell-wrapper", "cw"),
    ("collection-without-instances", "cwi"),
    ("computation-back-item", "cbi"),
    ("continuation-in-readable", "cir"),
    ("initializer-remainder", "ir"),
    ("instance-list-shape", "ils"),
    ("instances-on-plain-cell", "iop"),
    ("map-notation-at-non-map", "mna"),
    ("map-read-in-result", "mrr"),
    ("map-read-value-binder", "mvb"),
    ("none-in-initializer", "nii"),
    ("optional-without-presence", "owp"),
    ("presence-on-plain-cell", "pop"),
    ("record-missing-children", "rmc"),
    ("rest-mismatch", "rm"),
    ("unmatched-optional-result", "uor"),
    ("wildcard-outside-pattern", "wop"),
];

fn sweep_name(outcome: Outcome) -> String {
    match outcome {
        Outcome::Admit { lint: None } => "ok".to_owned(),
        Outcome::Admit { lint: Some(lint) } => format!("ok+{lint}"),
        Outcome::After => "sort".to_owned(),
        Outcome::Refuse(class) => SWEEP_LEGEND
            .iter()
            .find(|(name, _)| *name == class)
            .map_or_else(|| class.to_owned(), |(_, short)| (*short).to_owned()),
    }
}

/// The sweep's own stacks: every kind the domain has (check 5's, but the second computation,
/// which differs from the first by its name only, P1), with `G` as the group and the
/// collections' instance group.
fn sweep_stacks() -> Vec<(&'static str, Vec<Layer>)> {
    let leaf = |notation| vec![Layer::Leaf(notation)];
    let optional = |mut stack: Vec<Layer>| {
        stack.insert(0, Layer::Optional);
        stack
    };
    let many = |order| vec![Layer::Instances(order), group_g()];
    vec![
        ("computation", vec![Layer::Computation]),
        ("leaf Int", leaf(Notation::Plain)),
        ("leaf List", leaf(Notation::List)),
        ("leaf Cons", leaf(Notation::Cons)),
        ("leaf Map", leaf(Notation::Map)),
        ("leaf Set", leaf(Notation::Set)),
        ("group G", vec![group_g()]),
        ("? leaf Int", optional(leaf(Notation::Plain))),
        ("? leaf List", optional(leaf(Notation::List))),
        ("? leaf Map", optional(leaf(Notation::Map))),
        ("? group G", optional(vec![group_g()])),
        ("* List of G", many(Order::List)),
        ("* Set of G", many(Order::Set)),
        ("* Map of G", many(Order::Map)),
    ]
}

/// The entry a matched result's subject writes in its cell: the cell's content with an
/// anonymous rest at its content root where it has one, else a binder.
fn sweep_subject(form: Form, stack: &[Layer]) -> String {
    let cells = form == Form::Cells;
    let inner = |text: &str| {
        if cells {
            format!("k::configuration::Cell({text})")
        } else {
            text.to_owned()
        }
    };
    match stack {
        [Layer::Optional, rest @ ..] => format!("Some({})", sweep_subject(form, rest)),
        [Layer::Computation] if cells => "k::configuration::KCell(y, ..)".to_owned(),
        [Layer::Computation] => "[y, ..]".to_owned(),
        [Layer::Leaf(Notation::List | Notation::Cons)] => inner("[y, ..]"),
        [Layer::Leaf(Notation::Map)] if cells => inner("k::map![z -> y, ..]"),
        [Layer::Leaf(Notation::Map)] => "{ z -> y, .. }".to_owned(),
        [Layer::Leaf(_)] => inner("old"),
        [Layer::Group(_)] if cells => "k::fragment![crate::G { a: y, .. }]".to_owned(),
        [Layer::Group(_)] => "G { a: y, .. }".to_owned(),
        [Layer::Instances(Order::List), ..] if cells => {
            "[k::fragment![crate::G { a: y, .. }], ..]".to_owned()
        }
        [Layer::Instances(_), ..] if cells => {
            "{ k::fragment![crate::G { a: y, .. }], .. }".to_owned()
        }
        [Layer::Instances(Order::List), ..] => "[G { a: y, .. }, ..]".to_owned(),
        [Layer::Instances(_), ..] => "{ G { a: y, .. }, .. }".to_owned(),
        other => panic!("no sweep subject for {other:?}"),
    }
}

/// The spellings the sweep writes in each form, one per column: each mark of the form, and the
/// rests and records that pairing and L4 read.
const fn sweep_spellings(form: Form) -> &'static [&'static str] {
    match form {
        Form::Readable | Form::Claim => &[
            "Some(x)",
            "None",
            "[x, ..]",
            "[x]",
            "[..]",
            "[.., x]",
            "[x, r @ ..]",
            "{ G { a: x, .. }, .. }",
            "{ y -> x, .. }",
            "x",
            "_",
            "0",
            "G { a: x, .. }",
            "G { a: x }",
        ],
        Form::Cells => &[
            "Some(k::configuration::Cell(x))",
            "None",
            "k::configuration::Cell(x)",
            "k::configuration::Cell([x, ..])",
            "k::configuration::Cell(k::map![y -> x, ..])",
            "k::configuration::KCell(x, ..)",
            "k::configuration::KCell(x)",
            "[k::fragment![crate::G { a: x, .. }], ..]",
            "{ k::fragment![crate::G { a: x, .. }], .. }",
            "x",
            "_",
            "k::fragment![crate::G { a: x, .. }]",
        ],
        Form::Init => &[
            "Some(0)",
            "k::absent!(0)",
            "None",
            "k::k![pgm]",
            "k::k![Cmd::Go(), ..]",
            "[0]",
            "[0, ..]",
            "k::map![0 -> 1]",
            "0",
            "G { a: 0, b: 0 }",
            "G { a: 0 }",
            "Cmd::Go()",
            "pgm",
        ],
    }
}

/// The sweep of [`outcome`] over form × side (a subject whose cell the result leaves or writes,
/// a result over a matched or an unmatched cell, an initializer) × path (none, below a `?`
/// ancestor, below a `*` ancestor) × stack × spelling, with the product's answer where it
/// differs.
fn outcome_sweep() -> String {
    let mut out = String::new();
    out.push_str(concat!(
        "# The cells oracle's `outcome` (steps 1-3) over the cell-entry domain: the review surface for\n",
        "# S5.0g, whose rows come from `outcome`. Generated by krs-test-support `--test cells_oracle`\n",
        "# (`the_outcome_sweep_is_the_golden`); rewrite with KRS_CELLS_SWEEP_RECORD=1.\n",
        "#\n",
        "# One table per form. A row is a side, a path and the cell's own stack; a column a spelling.\n",
        "# side: `subject` (the result leaves the cell), `subject, written` (the result writes it),\n",
        "#   `result, matched` (the subject matches the cell with the row's `other`: its content with\n",
        "#   an anonymous rest at the content root where it has one, else a binder), `result,\n",
        "#   unmatched` (the subject does not match the cell: Q1's overwrite), `init`.\n",
        "# path: `-` the cell is named at its record's level (or below plain groups only); `?` below a\n",
        "#   `?` ancestor; `*` below a `*` ancestor (S1 (b)). The stack is the cell's own.\n",
        "# Bound names: in a result, x, y, z, old (bound by the subject); in a subject, none; in an\n",
        "#   initializer, the configuration variable pgm. `G` is the group (children a, b: Int) of\n",
        "#   the group stacks and the collections' instances.\n",
        "# claim's steps 1-3 are readable's; both are printed so a change to either shows.\n",
        "#\n",
        "# A cell: ok (admitted), ok+LINT (admitted, owing the lint), sort (admitted, a value's sort\n",
        "#   left to the lattice, step 4), or the refusal's class by its short name below.\n",
        "#   `A|product:B` marks where the product (krs_syntax::cell_entries) answers B: each such\n",
        "#   cell is a [cell-exception] departure (E1, E3, a C-lim) or a disagreement to explain.\n",
        "#\n",
    ));
    for (class, short) in SWEEP_LEGEND {
        let _ = writeln!(out, "# {short}\t{class}");
    }
    let paths: [(&str, Vec<Layer>); 3] = [
        ("-", Vec::new()),
        ("?", vec![Layer::Optional]),
        ("*", vec![Layer::Instances(Order::List)]),
    ];
    for form in [Form::Readable, Form::Claim, Form::Cells, Form::Init] {
        let spellings = sweep_spellings(form);
        let _ = write!(out, "#\n## {}\nside\tpath\tstack\tother", form_name(form));
        for spelling in spellings {
            out.push('\t');
            out.push_str(spelling);
        }
        out.push('\n');
        let sides: &[(&str, Side, bool, bool)] = if form == Form::Init {
            &[("init", Side::Initializer, false, false)]
        } else {
            &[
                ("subject", Side::Subject, false, false),
                ("subject, written", Side::Subject, true, false),
                ("result, matched", Side::Result, false, true),
                ("result, unmatched", Side::Result, false, false),
            ]
        };
        for (side_name, side, written, matched) in sides {
            for (path_name, path) in &paths {
                for (stack_name, stack) in sweep_stacks() {
                    let other = matched.then(|| sweep_subject(form, &stack));
                    let bound: &[&str] = match side {
                        Side::Result => &["x", "y", "z", "old"],
                        Side::Initializer => &["pgm"],
                        _ => &[],
                    };
                    let _ = write!(
                        out,
                        "{side_name}\t{path_name}\t{stack_name}\t{}",
                        other.as_deref().unwrap_or("-")
                    );
                    for text in spellings {
                        let probe = Probe {
                            form,
                            side: *side,
                            path,
                            stack: &stack,
                            text,
                            other: other.as_deref(),
                            written: *written,
                            bound,
                        };
                        let (oracle, product) = (probe.oracle(), probe.product());
                        out.push('\t');
                        out.push_str(&sweep_name(oracle));
                        if product != oracle {
                            out.push_str("|product:");
                            out.push_str(&sweep_name(product));
                        }
                    }
                    out.push('\n');
                }
            }
        }
    }
    out
}

/// The sweep of `outcome` is the checked-in one: a change to the oracle's answers, or to the
/// product's departures from them, shows as a diff of `cells-outcome-sweep.tsv`.
#[test]
fn the_outcome_sweep_is_the_golden() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/class-matrix")
        .join(SWEEP_FILE);
    let sweep = outcome_sweep();
    if std::env::var_os("KRS_CELLS_SWEEP_RECORD").is_some() {
        std::fs::write(&path, &sweep).unwrap_or_else(|error| panic!("{}: {error}", path.display()));
        return;
    }
    let golden = std::fs::read_to_string(&path).unwrap_or_default();
    if golden != sweep {
        let line = golden
            .lines()
            .zip(sweep.lines())
            .position(|(was, is)| was != is)
            .unwrap_or_else(|| golden.lines().count().min(sweep.lines().count()));
        panic!(
            "{SWEEP_FILE} differs from `outcome`'s sweep from line {}: was {:?}, is {:?}; \
             review the change and record it with KRS_CELLS_SWEEP_RECORD=1",
            line + 1,
            golden.lines().nth(line),
            sweep.lines().nth(line)
        );
    }
}
