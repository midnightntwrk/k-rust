//! The cells oracle's checks (design S5, §3): the table's cell-entry rows against the principles
//! (checks 0, 1, 1r), the product's admission against the table, with the test-side templates
//! against the rendered sentences (check 2), the readable form against the `cells!` form it
//! abbreviates (check 3), the advice of a missing layer (check 4), the generated coverage of the
//! domain (check 5), and the recorded K's frames against P6 (check 6). Outside the generated
//! cases: the review's probes, and the sweep of `outcome` over the whole domain, checked in as
//! `cells-outcome-sweep.tsv`, with its row patterns and their principles in
//! `cells-outcome-patterns.tsv`.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::Path;
use std::sync::LazyLock;

use krs_ir::cell_kind::{self, CellKind};
use krs_syntax::cell_entries::{self, Bound, EntrySide};
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
    sentence_outcome,
};
use krs_test_support::class_matrix::invariants::registry_kind;
use krs_test_support::class_matrix::pending::{self, Pending};
use krs_test_support::class_matrix::sweep;
use krs_test_support::class_matrix::sweep::{
    CHILDREN as CHILDREN_SWEEP, CHILDREN_UNBASED as CHILDREN_UNBASED_SWEEP,
    FRAGMENT_CHILD as FRAGMENT_CHILD_SWEEP, INITIALIZER_CHILDREN as INITIALIZER_CHILDREN_SWEEP,
    back_spellings as sweep_back_spellings, children_stack, form_name, group_g,
    group_of as sweep_group, main_tables as sweep_main_tables,
    more_spellings as sweep_more_spellings, nested_collection_stack, spellings as sweep_spellings,
    stack_name, stacks as sweep_stacks, subject as sweep_subject, untexted,
};
use krs_test_support::class_matrix::table::{At, Expected, Glob, TERM_ACCEPTS_FILE, Table, twin};
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

/// Each case's answer by P4's steps over its whole sentence ([`sentence_outcome`], ruling 1 of
/// S5.3 part 2): the sentence's answer, and whether it is about the case's own entry. A case's
/// row is its sentence's answer (ruling 2).
static ANSWERS: LazyLock<BTreeMap<String, (Outcome, bool)>> = LazyLock::new(|| {
    ENTRIES
        .iter()
        .map(|(case, entry)| {
            let (sentence, own) = ordered_sentence(case, entry)
                .unwrap_or_else(|error| panic!("{}: the sentence is not read: {error}", case.id));
            let (about, answer) = sentence_outcome(entry.form, &sentence, own);
            (case.id.clone(), (answer, about == own))
        })
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
        let stated = ["E1", "E3"].iter().any(|named| {
            principle == named
                || principle
                    .strip_prefix(named)
                    .and_then(|tail| tail.strip_prefix(": "))
                    .is_some_and(|reason| !reason.trim().is_empty())
        }) || principle
            .strip_prefix("C-lim: ")
            .is_some_and(|reason| !reason.trim().is_empty());
        if !stated {
            failures.push(format!(
                "cell-exception {pattern:?}: the principle {principle:?} is not E1, E3 (each with an optional `: REASON`) or `C-lim: REASON`"
            ));
        }
    }
    let mut hits = BTreeMap::<&str, usize>::new();
    let mut disagreements = 0;
    for (case, _) in ENTRIES.iter() {
        let expected = &EXPECTED[&case.id];
        let (got, own) = ANSWERS[&case.id];
        // A refusal of another entry is met outside the case's own entry, in its item.
        if !own
            && let Expected::Refuse { at, .. } = expected
            && *at != At::Item
        {
            failures.push(format!(
                "{}: the sentence's answer {got:?} is another entry's, so the row's site is the \
                 item, not the {at:?}",
                case.id
            ));
        }
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
const RULE_UNCOVERED: [(&str, &str); 0] = [];

/// Check 1r: where the entry is admitted, the rule-level judgement equals a rule-level row's
/// class, and is none on an accept; and every rule-level class is some generated case's row, or
/// is listed in [`RULE_UNCOVERED`].
#[test]
fn check_1r_every_rule_level_row_agrees_with_the_rule() {
    let mut failures = Vec::new();
    let mut judged = 0;
    let mut rows = BTreeSet::new();
    for (case, entry) in ENTRIES.iter() {
        // The rule-level classes judge a sentence whose every entry is admitted.
        let (got, _) = ANSWERS[&case.id];
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
    /// The sorts of the source's `#[k::cons_list]` constructor enums: a cell of one is a cons
    /// leaf.
    cons_lists: Vec<String>,
}

impl Configuration {
    fn parse(source: &str) -> Option<Self> {
        let file = syn::parse_file(source).ok()?;
        let mut root = None;
        let mut declarations = Vec::new();
        let mut cons_lists = Vec::new();
        for item in file.items {
            let item = match item {
                syn::Item::Struct(item) => item,
                syn::Item::Enum(item) => {
                    cons_lists.extend(cons_list_sort(&item));
                    continue;
                }
                _ => continue,
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
            cons_lists,
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
            .map(|field| ConfigurationCell::new(field, &self.declarations, &self.cons_lists))
            .collect();
        let mut ancestors = Vec::new();
        let field = search(fields, name, &mut ancestors)?;
        Some((ancestors, field))
    }

    /// The configuration's groups, at any depth, as `CellKind` reads its cells: what the
    /// product reads a term's record by.
    fn groups(&self) -> Vec<cell_kind::GroupKind> {
        let mut groups = Vec::new();
        let Some(root) = self
            .declarations
            .iter()
            .find(|declaration| *declaration.name() == self.root)
        else {
            return groups;
        };
        for field in root.cells() {
            let cell = ConfigurationCell::new(field, &self.declarations, &self.cons_lists);
            cell_entries::collect_groups(&CellKind::of(&cell).layers, &mut groups);
        }
        groups
    }

    /// What an entry naming `cell` is judged against: `CellKind::{path, of}`, apart.
    fn kind(&self, cell: &str) -> cell_kind::EntryKind {
        let (ancestors, field) = self
            .find(cell)
            .unwrap_or_else(|| panic!("the configuration declares the cell `{cell}`"));
        CellKind::entry(&ancestors, &field)
    }
}

/// The sort of a `#[k::cons_list]` constructors enum: its `#[k::constructors(sort = S, ..)]`.
fn cons_list_sort(item: &syn::ItemEnum) -> Option<String> {
    let named = |attribute: &syn::Attribute, name: &str| {
        attribute
            .path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == name)
    };
    if !item
        .attrs
        .iter()
        .any(|attribute| named(attribute, "cons_list"))
    {
        return None;
    }
    let constructors = item
        .attrs
        .iter()
        .find(|attribute| named(attribute, "constructors"))?;
    let mut sort = None;
    let _ = constructors.parse_nested_meta(|meta| {
        if meta.path.is_ident("sort") {
            sort = Some(meta.value()?.parse::<syn::Path>()?);
        } else if meta.input.peek(syn::Token![=]) {
            let _ = meta.value()?.parse::<syn::Expr>()?;
        }
        Ok(())
    });
    sort.and_then(|path| {
        path.segments
            .last()
            .map(|segment| segment.ident.to_string())
    })
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
/// dropped (the generator declares a literal without it, [`build::lit`]).
fn declared_as(spelling: &EntrySpelling) -> Spelling {
    read_as(spelling, false)
}

/// The product's spelling as a probe gives it to the oracle: its literals' texts kept, so the
/// oracle can tell two literals apart (R9's key written back).
fn probed_as(spelling: &EntrySpelling) -> Spelling {
    read_as(spelling, true)
}

fn read_as(spelling: &EntrySpelling, texts: bool) -> Spelling {
    let read = |spelling: &EntrySpelling| read_as(spelling, texts);
    let seq = |seq: &EntrySeq| Seq {
        items: seq.items.iter().map(read).collect(),
        rest: seq.rest.as_ref().map(|(rest, place)| {
            (
                rest_as(rest),
                match place {
                    RestPlace::Back => RestAt::Back,
                    RestPlace::Before(_) => RestAt::Front,
                },
            )
        }),
    };
    let map = |map: &EntryMap| Entries {
        entries: map
            .entries
            .iter()
            .map(|(key, value)| (read(key), read(value)))
            .collect(),
        rest: map.rest.as_ref().map(rest_as),
    };
    let record = |record: &EntryRecord| Record {
        head: record.head.clone(),
        fields: record
            .fields
            .iter()
            .map(|(name, value)| (name.clone(), read(value)))
            .collect(),
        rest: match &record.tail {
            RecordTail::Exact => RecordRest::Exact,
            RecordTail::Open => RecordRest::Open,
            RecordTail::Update(base) => RecordRest::Update(base.clone()),
        },
    };
    let boxed = |inner: &EntrySpelling| Box::new(read(inner));
    match spelling {
        EntrySpelling::Wild => Spelling::Wild,
        EntrySpelling::Binder(name) => Spelling::Binder(name.clone()),
        EntrySpelling::Literal(text) => Spelling::Literal(texts.then(|| text.clone())),
        EntrySpelling::Call(arguments) => Spelling::Call(arguments.iter().map(read).collect()),
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
                    // The oracle states only that an item follows the rest; every other side
                    // it declares with one writes the rest first (`[.., x]`).
                    RestAt::Front => RestPlace::Before(0),
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
        Spelling::Literal(text) => {
            EntrySpelling::Literal(text.clone().unwrap_or_else(|| "0".to_owned()))
        }
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

/// A rendered sentence as the product reads it, independently of the test-side template: its
/// entries (each `key: value` field, a plain group's record read as its children's entries),
/// the names its parameters bind, whether it states a guard, and an initializer's
/// configuration variables with whether each is the main one.
#[derive(Debug, Default)]
struct Rendered {
    sentence: Option<class_matrix::cells_oracle::Sentence>,
    /// Whether a sentence that keeps its pattern is a context, which is lowered as a rule's
    /// pattern is.
    context: bool,
    entries: Vec<(String, Side, EntrySpelling)>,
    parameters: BTreeSet<String>,
    guard: bool,
    variables: Vec<(String, bool)>,
}

/// What the rendered sentence does with its cells, as the product's judgement reads it: a
/// sentence that keeps its pattern as it matched it keeps every cell it names (a context lowered
/// as a rule's pattern is), one with a result entry pairs each entry with the other side's, and
/// one with none rewrites in place.
fn product_rewrite(rendered: &Rendered) -> cell_entries::Rewrite {
    if rendered.sentence == Some(class_matrix::cells_oracle::Sentence::Context) {
        cell_entries::Rewrite::Kept {
            as_rule: rendered.context,
        }
    } else if rendered
        .entries
        .iter()
        .any(|(_, side, _)| *side == Side::Result)
    {
        cell_entries::Rewrite::Result
    } else {
        cell_entries::Rewrite::InPlace
    }
}

/// Skips one token tree.
fn skip(input: syn::parse::ParseStream<'_>) -> syn::Result<()> {
    input.step(|cursor| {
        cursor
            .token_tree()
            .map(|(_, next)| ((), next))
            .ok_or_else(|| cursor.error("a token"))
    })
}

/// A record's or a `cells!` body's fields: `key: value`, and the frames `name @ ..`, `..name`
/// and `..`, which name no cell.
fn rendered_fields(
    reading: EntryReading<'_>,
    input: syn::parse::ParseStream<'_>,
    side: Side,
    out: &mut Vec<(String, Side, EntrySpelling)>,
) -> syn::Result<()> {
    while !input.is_empty() {
        if input.peek(syn::Token![..]) {
            input.parse::<syn::Token![..]>()?;
            if input.peek(syn::Ident) {
                input.parse::<syn::Ident>()?;
            }
        } else if input.peek(syn::Ident) && input.peek2(syn::Token![@]) {
            input.parse::<syn::Ident>()?;
            input.parse::<syn::Token![@]>()?;
            input.parse::<syn::Token![..]>()?;
        } else {
            let (key, value) = reading.parse_field(input)?;
            let cell = key
                .segments
                .last()
                .map(|segment| segment.ident.to_string())
                .unwrap_or_default();
            out.push((cell, side, value));
        }
        if !input.is_empty() {
            input.parse::<syn::Token![,]>()?;
        }
    }
    Ok(())
}

/// A readable rule or claim: `k::rules! { for M; use ..; #[..] label: { .. } => { .. }; }`.
fn rendered_readable(form: EntryForm, input: syn::parse::ParseStream<'_>) -> syn::Result<Rendered> {
    use class_matrix::cells_oracle::Sentence;
    let mut rendered = Rendered::default();
    let path = input.call(syn::Path::parse_mod_style)?;
    rendered.sentence = Some(
        if path
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "claims")
        {
            Sentence::Claim
        } else {
            Sentence::Rule
        },
    );
    input.parse::<syn::Token![!]>()?;
    let body;
    syn::braced!(body in input);
    let reading = EntryReading::new(form, &[]);
    while !body.is_empty() {
        if body.peek(syn::Token![for]) {
            while !body.peek(syn::Token![;]) {
                skip(&body)?;
            }
            body.parse::<syn::Token![;]>()?;
            continue;
        }
        if body.peek(syn::Token![use]) {
            body.parse::<syn::ItemUse>()?;
            continue;
        }
        body.call(syn::Attribute::parse_outer)?;
        body.parse::<syn::Ident>()?;
        body.parse::<syn::Token![:]>()?;
        let subject;
        syn::braced!(subject in body);
        rendered_fields(reading, &subject, Side::Subject, &mut rendered.entries)?;
        body.parse::<syn::Token![=>]>()?;
        let result;
        syn::braced!(result in body);
        rendered_fields(reading, &result, Side::Result, &mut rendered.entries)?;
        while !body.peek(syn::Token![;]) {
            rendered.guard = true;
            skip(&body)?;
        }
        body.parse::<syn::Token![;]>()?;
    }
    Ok(rendered)
}

/// A `cells!` rule: `#[k::rule(..)] pub fn f(x: T, .., k::cells! { .. }: M) -> M { k::cells! { .. } }`;
/// or a sentence that keeps its `cells!` pattern as it matched it (G6): an equation whose last
/// parameter is its function context, `#[k::equation] fn f(x: T, .., k::term![..]: S,
/// k::cells! { .., .. }: M) -> S { .. }`, after the struct of the function it defines, a
/// context alias, `#[k::context_alias(..)] fn f(x: T, .., k::cells! { .. }: M) {}`, and a
/// context, `#[k::context(hole = h)] fn f(h: T, .., k::cells! { .. }: M) {}`.
fn rendered_cells(input: syn::parse::ParseStream<'_>) -> syn::Result<Rendered> {
    use class_matrix::cells_oracle::Sentence;
    let mut rendered = Rendered {
        sentence: Some(Sentence::Rule),
        ..Rendered::default()
    };
    let reading = EntryReading::new(EntryForm::Cells, &[]);
    let attributes = input.call(syn::Attribute::parse_outer)?;
    let attributes = if input.fork().parse::<syn::ItemStruct>().is_ok() {
        input.parse::<syn::ItemStruct>()?;
        input.call(syn::Attribute::parse_outer)?
    } else {
        attributes
    };
    let marks = |name: &str| {
        attributes.iter().any(|attribute| {
            attribute
                .path()
                .segments
                .last()
                .is_some_and(|segment| segment.ident == name)
        })
    };
    if marks("equation") || marks("context_alias") || marks("context") {
        rendered.sentence = Some(Sentence::Context);
        rendered.context = marks("context");
    }
    input.parse::<syn::Visibility>()?;
    input.parse::<syn::Token![fn]>()?;
    input.parse::<syn::Ident>()?;
    let parameters;
    syn::parenthesized!(parameters in input);
    while !parameters.is_empty() {
        if parameters.peek(syn::Ident) && parameters.peek2(syn::Token![::]) {
            let path = parameters.call(syn::Path::parse_mod_style)?;
            parameters.parse::<syn::Token![!]>()?;
            if path
                .segments
                .last()
                .is_some_and(|segment| segment.ident == "cells")
            {
                let subject;
                syn::braced!(subject in parameters);
                rendered_fields(reading, &subject, Side::Subject, &mut rendered.entries)?;
            } else {
                // An equation's subject, `k::term![..]`, holds no cell entry.
                skip(&parameters)?;
            }
        } else {
            rendered
                .parameters
                .insert(parameters.parse::<syn::Ident>()?.to_string());
        }
        parameters.parse::<syn::Token![:]>()?;
        parameters.parse::<syn::Type>()?;
        if !parameters.is_empty() {
            parameters.parse::<syn::Token![,]>()?;
        }
    }
    if input.peek(syn::Token![->]) {
        input.parse::<syn::Token![->]>()?;
        input.parse::<syn::Type>()?;
    }
    let body;
    syn::braced!(body in input);
    if rendered.sentence == Some(Sentence::Context) {
        // An equation's body is its result term, a context alias's and a context's are empty:
        // none writes a cell.
        while !body.is_empty() {
            skip(&body)?;
        }
        return Ok(rendered);
    }
    body.call(syn::Path::parse_mod_style)?;
    body.parse::<syn::Token![!]>()?;
    let result;
    syn::braced!(result in body);
    rendered_fields(reading, &result, Side::Result, &mut rendered.entries)?;
    Ok(rendered)
}

/// An initializer: `impl M { #[k::init] pub fn init(#[k::config_var(..)] v: S, ..) -> Self {
/// Self { .. } } }`.
fn rendered_initializer(input: syn::parse::ParseStream<'_>) -> syn::Result<Rendered> {
    let mut rendered = Rendered {
        sentence: Some(class_matrix::cells_oracle::Sentence::Initializer),
        ..Rendered::default()
    };
    input.parse::<syn::Token![impl]>()?;
    input.parse::<syn::Type>()?;
    let item;
    syn::braced!(item in input);
    item.call(syn::Attribute::parse_outer)?;
    item.parse::<syn::Visibility>()?;
    item.parse::<syn::Token![fn]>()?;
    item.parse::<syn::Ident>()?;
    let parameters;
    syn::parenthesized!(parameters in item);
    while !parameters.is_empty() {
        let mut main = false;
        for attribute in parameters.call(syn::Attribute::parse_outer)? {
            attribute.parse_nested_meta(|meta| {
                if meta.path.is_ident("main") {
                    main = true;
                } else if meta.input.peek(syn::Token![=]) {
                    meta.value()?.parse::<syn::Lit>()?;
                }
                Ok(())
            })?;
        }
        let name = parameters.parse::<syn::Ident>()?.to_string();
        parameters.parse::<syn::Token![:]>()?;
        parameters.parse::<syn::Type>()?;
        rendered.parameters.insert(name.clone());
        rendered.variables.push((name, main));
        if !parameters.is_empty() {
            parameters.parse::<syn::Token![,]>()?;
        }
    }
    item.parse::<syn::Token![->]>()?;
    item.parse::<syn::Type>()?;
    let body;
    syn::braced!(body in item);
    body.parse::<syn::Token![Self]>()?;
    let fields;
    syn::braced!(fields in body);
    let variables = rendered
        .variables
        .iter()
        .map(|(name, _)| name.clone())
        .collect::<Vec<_>>();
    let reading = EntryReading::new(EntryForm::Initializer, &variables);
    rendered_fields(reading, &fields, Side::Initializer, &mut rendered.entries)?;
    Ok(rendered)
}

/// The case's whole sentence as the product reads it from the rendered source, a plain group's
/// record read as its children's entries.
fn rendered_sentence(case: &Case, entry: &EntryCase) -> Result<Rendered, String> {
    let rendered = case.render();
    let text = &rendered.source[rendered.cases[0].item.clone()];
    let form = entry_form(entry.form);
    let parsed = match entry.form {
        Form::Readable | Form::Claim => {
            (|input: syn::parse::ParseStream<'_>| rendered_readable(form, input)).parse_str(text)
        }
        Form::Cells => rendered_cells.parse_str(text),
        Form::Init => rendered_initializer.parse_str(text),
    };
    let mut sentence = parsed.map_err(|error| format!("`{text}`: {error}"))?;
    let mut flat = Vec::new();
    let mut pending = std::mem::take(&mut sentence.entries);
    while let Some((cell, side, value)) = pending.pop() {
        match value {
            EntrySpelling::Record(record) if !entry_cases::declares(case, &cell) => {
                pending.extend(
                    record
                        .fields
                        .into_iter()
                        .map(|(child, value)| (child, side, value)),
                );
            }
            value => flat.push((cell, side, value)),
        }
    }
    flat.reverse();
    sentence.entries = flat;
    Ok(sentence)
}

/// The case's sentence in source order, the rendered sentence's ([`rendered_sentence`]), each
/// entry with its context ([`EntryCase::sentence`]), and the index of the case's own entry.
fn ordered_sentence(
    case: &Case,
    entry: &EntryCase,
) -> Result<
    (
        Vec<(
            class_matrix::cells_oracle::Entry,
            class_matrix::cells_oracle::Context,
        )>,
        usize,
    ),
    String,
> {
    let rendered = rendered_sentence(case, entry)?;
    let mut sentence = entry
        .sentence()
        .into_iter()
        .enumerate()
        .map(|(index, judged)| {
            rendered
                .entries
                .iter()
                .position(|(cell, side, _)| *cell == judged.0.cell && *side == judged.0.side)
                .map(|at| (at, index, judged))
                .ok_or_else(|| "an entry the rendered sentence does not have".to_owned())
        })
        .collect::<Result<Vec<_>, String>>()?;
    sentence.sort_by_key(|(at, ..)| *at);
    let own = sentence
        .iter()
        .position(|(_, index, _)| *index == 0)
        .expect("the own entry is in the sentence");
    Ok((
        sentence.into_iter().map(|(.., judged)| judged).collect(),
        own,
    ))
}

/// The bases the updates of `spelling` name (`..me`), in first-occurrence order.
fn update_bases(spelling: &Spelling, out: &mut Vec<String>) {
    if let Spelling::Record(record) | Spelling::Fragment(record) = spelling
        && let RecordRest::Update(base) = &record.rest
        && !out.contains(base)
    {
        out.push(base.clone());
    }
    for inner in class_matrix::cells_oracle::children(spelling) {
        update_bases(inner, out);
    }
}

/// The names a spelling binds: its binders, its aliases' names and its named rests.
fn names(spelling: &Spelling, out: &mut BTreeSet<String>) {
    match spelling {
        Spelling::Binder(name) | Spelling::Alias(name, _) => {
            out.insert(name.clone());
        }
        _ => {}
    }
    let rest = match spelling {
        Spelling::Brackets(seq)
        | Spelling::Braces(seq)
        | Spelling::KCell(seq)
        | Spelling::InstList(seq)
        | Spelling::InstSet(seq)
        | Spelling::KMacro(seq) => seq.rest.as_ref().map(|(rest, _)| rest),
        Spelling::MapRead(entries) | Spelling::MapLit(entries) => entries.rest.as_ref(),
        _ => None,
    };
    if let Some(Rest::Named(name)) = rest {
        out.insert(name.clone());
    }
    for inner in class_matrix::cells_oracle::children(spelling) {
        names(inner, out);
    }
}

/// R9: the case's test-side template agrees with the rendered sentence, read independently: the
/// same other entries (cell, side, spelling, and the cell's stacks as `CellKind` reads them),
/// the same sentence, guard and configuration variables; for a subject, whether the result
/// writes its cell; for a result, whether and how the subject matches its cell; and, in a
/// readable form (the only one whose outcome reads them), for each name the entry holds, whether
/// the sentence binds it outside the entry.
fn template_agreement(
    case: &Case,
    entry: &EntryCase,
    configuration: &Configuration,
) -> Result<(), String> {
    let rendered = rendered_sentence(case, entry)?;
    let (cell, side) = (&entry.entry.cell, entry.entry.side);
    let mut others = rendered.entries.clone();
    let own = others
        .iter()
        .position(|(at, on, _)| at == cell && *on == side)
        .ok_or_else(|| format!("the rendered sentence has no {side:?} entry of `{cell}`"))?;
    others.remove(own);
    let shown = |entries: &mut Vec<(String, Side, Spelling)>| {
        entries.sort_by_key(|entry| format!("{entry:?}"));
        format!("{entries:?}")
    };
    let mut read = others
        .iter()
        .map(|(cell, side, value)| (cell.clone(), *side, declared_as(value)))
        .collect::<Vec<_>>();
    let mut written = entry
        .template
        .entries
        .iter()
        .map(|other| (other.cell.clone(), other.side, other.spelling.clone()))
        .collect::<Vec<_>>();
    let (read, written) = (shown(&mut read), shown(&mut written));
    if read != written {
        return Err(format!(
            "the template's other entries are {written}, the rendered sentence's {read}"
        ));
    }
    template_stacks_and_sentence(entry, &rendered, configuration)?;
    let on = |want: Side| {
        others
            .iter()
            .find(|(at, on, _)| at == cell && *on == want)
            .map(|(_, _, value)| declared_as(value))
    };
    match side {
        Side::Subject if entry.context.written != on(Side::Result).is_some() => {
            return Err(format!(
                "the template says the result writes `{cell}`: {}, the rendered sentence {}",
                entry.context.written,
                on(Side::Result).is_some()
            ));
        }
        Side::Result if entry.context.other.as_ref().map(untexted) != on(Side::Subject) => {
            return Err(format!(
                "the template's subject entry of `{cell}` is {:?}, the rendered sentence's {:?}",
                entry.context.other,
                on(Side::Subject)
            ));
        }
        Side::Subject
            if entry.context.other.is_some()
                && entry.context.other.as_ref().map(untexted) != on(Side::Result) =>
        {
            return Err(format!(
                "the template's result entry of `{cell}` is {:?}, the rendered sentence's {:?}",
                entry.context.other,
                on(Side::Result)
            ));
        }
        _ => {}
    }
    bases_agree(entry, &others)?;
    if matches!(entry.form, Form::Readable | Form::Claim) {
        let mut bound = rendered.parameters.clone();
        for (_, on, value) in &others {
            if *on == Side::Subject {
                names(&declared_as(value), &mut bound);
            }
        }
        let mut held = BTreeSet::new();
        names(&entry.entry.spelling, &mut held);
        for name in held {
            if entry.context.bound.contains(&name) != bound.contains(&name) {
                return Err(format!(
                    "the template says the sentence binds `{name}` outside the entry: {}, the \
                     rendered sentence {}",
                    entry.context.bound.contains(&name),
                    bound.contains(&name)
                ));
            }
        }
    }
    Ok(())
}

/// What each base an update of the entry names binds (S5.0g item 3b ruling 1): the record the
/// template says, and the one an alias of the rendered sentence's other subject entries binds
/// it to, agree.
fn bases_agree(entry: &EntryCase, others: &[(String, Side, EntrySpelling)]) -> Result<(), String> {
    let mut rendered_records = Vec::new();
    for (_, on, value) in others {
        if *on == Side::Subject {
            rendered_records.extend(sweep::records_by(&declared_as(value)));
        }
    }
    let mut bases = Vec::new();
    update_bases(&entry.entry.spelling, &mut bases);
    for base in bases {
        let head = |records: &[(String, String)]| {
            records
                .iter()
                .find(|(name, _)| *name == base)
                .map(|(_, head)| head.clone())
        };
        if head(&entry.context.records) != head(&rendered_records) {
            return Err(format!(
                "the template says the sentence binds the base `{base}` to a record of {:?}, the \
                 rendered sentence to one of {:?}",
                head(&entry.context.records),
                head(&rendered_records)
            ));
        }
    }
    Ok(())
}

/// The template's entries' stacks are the ones `CellKind` reads, and its sentence, guard and
/// configuration variables are the rendered sentence's.
fn template_stacks_and_sentence(
    entry: &EntryCase,
    rendered: &Rendered,
    configuration: &Configuration,
) -> Result<(), String> {
    for other in &entry.template.entries {
        let kind = configuration.kind(&other.cell);
        let mut own = kind.own.layers.iter().map(oracle_layer).collect::<Vec<_>>();
        if other.side == Side::Initializer && matches!(own.first(), Some(Layer::Instances(_))) {
            own.remove(0);
        }
        let path = kind
            .path
            .layers
            .iter()
            .map(oracle_layer)
            .collect::<Vec<_>>();
        if own != other.stack || path != other.path {
            return Err(format!(
                "the template's entry of `{}` has the stacks {:?} then {:?}, CellKind reads {path:?} \
                 then {own:?}",
                other.cell, other.path, other.stack
            ));
        }
    }
    if rendered.sentence != Some(entry.template.sentence) || rendered.guard != entry.template.guard
    {
        return Err(format!(
            "the template is a {:?} with guard {}, the rendered sentence a {:?} with guard {}",
            entry.template.sentence, entry.template.guard, rendered.sentence, rendered.guard
        ));
    }
    if rendered.variables != entry.template.variables {
        return Err(format!(
            "the template's configuration variables are {:?}, the rendered initializer's {:?}",
            entry.template.variables, rendered.variables
        ));
    }
    Ok(())
}

/// What the product reads `name` as binding, from the oracle's context: `None` where the sentence
/// binds it nowhere outside the entry.
fn product_bound(context: &class_matrix::cells_oracle::Context, name: &str) -> Option<Bound> {
    context.bound.iter().any(|bound| bound == name).then(|| {
        context
            .records
            .iter()
            .find(|(bound, _)| bound == name)
            .map_or(Bound::Value, |(_, head)| Bound::Record(head.clone()))
    })
}

const fn product_side(side: Side) -> EntrySide {
    match side {
        Side::Subject => EntrySide::Subject,
        Side::Result => EntrySide::Result,
        _ => EntrySide::Initializer,
    }
}

/// The product's judgement of a case's entry: `admit` (form, path and kind), then `pair`, or
/// `pair_kept` in a sentence that keeps its pattern as it matched it (the rendered sentence's
/// [`product_rewrite`]).
fn product_outcome(
    case: &Case,
    entry: &EntryCase,
    kind: &cell_kind::EntryKind,
    spelling: &EntrySpelling,
    groups: &[cell_kind::GroupKind],
) -> Outcome {
    let rewrite = rendered_sentence(case, entry)
        .map_or(cell_entries::Rewrite::Result, |rendered| {
            product_rewrite(&rendered)
        });
    let (path, stack) = (&kind.path.layers[..], &kind.own.layers[..]);
    let form = match entry.form {
        Form::Readable => EntryForm::Readable,
        Form::Claim => EntryForm::Claim,
        Form::Cells => EntryForm::Cells,
        Form::Init => EntryForm::Initializer,
    };
    let side = product_side(entry.entry.side);
    let bound = |name: &str| product_bound(&entry.context, name);
    let admitted = match cell_entries::admit(form, side, path, stack, spelling, &bound, groups) {
        Ok(admitted) => admitted,
        Err(refusal) => return Outcome::Refuse(refusal.class()),
    };
    let other = entry.context.other.as_ref().map(product_of);
    let paired = match rewrite {
        cell_entries::Rewrite::Kept { as_rule } => {
            cell_entries::pair_kept(form, stack, spelling, as_rule, &bound)
        }
        _ => cell_entries::pair(
            form,
            side,
            stack,
            spelling,
            other.as_ref(),
            entry.context.written,
            &bound,
        ),
    };
    match paired {
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
/// Three agreements come first: the stack `CellKind` reads equals the test-side stack of every
/// fixture cell an entry names (kind agreement); the case's template (its other entries, what the
/// result writes, whether the subject matches the cell, the names bound) is the rendered
/// sentence's, read by the product's reader (template agreement, [`template_agreement`]); and the
/// spelling the product parses is the one the generator declares (spelling agreement).
#[test]
fn check_2_the_product_admits_as_the_table_says() {
    let exceptions = exceptions();
    let configurations = configurations();
    let groups = configurations
        .iter()
        .map(|(base, configuration)| (*base, configuration.groups()))
        .collect::<BTreeMap<_, _>>();
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
        match template_agreement(case, entry, configuration) {
            Ok(()) => *counts.entry("template agrees".to_owned()).or_default() += 1,
            Err(error) => failures.push(format!(
                "{}: the template and the rendered sentence disagree: {error}",
                case.id
            )),
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
        if declared_as(&spelling) != untexted(&entry.entry.spelling) {
            failures.push(format!(
                "{}: the product reads {:?}, the generator declares {:?}",
                case.id,
                declared_as(&spelling),
                entry.entry.spelling
            ));
            continue;
        }
        let got = product_outcome(case, entry, &kind, &spelling, &groups[&case.base]);
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

/// Check 2s (S5.3 part 2; readable records and claims, S5.2 part a): the product's judgement of a
/// whole `cells!`, readable or claim sentence against the oracle's, as the collector judges each
/// before the compile path reads it. For every generated case of those forms, the product reads
/// every entry of the rendered
/// sentence (`krs_syntax::cell_entry`) and its cell's kind, and judges the sentence as the
/// collector does ([`krs_syntax::cell_entries::Sentence::judge`]); its answer, the refused entry
/// and its class or an admission, is [`sentence_outcome`]'s over the case's sentence. Check 2
/// compares one entry at a time, so it does not see a template entry the product refuses, or the
/// order the product meets the refusals of two entries in. A case an exception names is the
/// table's on its own entry, which the oracle does not state; it is left to check 2.
#[test]
fn check_2s_the_product_judges_a_sentence_as_the_table_says() {
    let exceptions = exceptions();
    let configurations = configurations();
    let mut failures = Vec::new();
    let mut counts = BTreeMap::<&str, usize>::new();
    for (case, entry) in ENTRIES.iter() {
        if !matches!(entry.form, Form::Cells | Form::Readable | Form::Claim) {
            continue;
        }
        if !naming(&case.id, &exceptions).is_empty() {
            *counts.entry("excepted").or_default() += 1;
            continue;
        }
        let Some(configuration) = configurations.get(&case.base) else {
            failures.push(format!(
                "{}: no rendered source of its base parses",
                case.id
            ));
            continue;
        };
        let rendered = match rendered_sentence(case, entry) {
            Ok(rendered) => rendered,
            Err(error) => {
                failures.push(format!(
                    "{}: the product does not read the sentence: {error}",
                    case.id
                ));
                continue;
            }
        };
        let kinds = rendered
            .entries
            .iter()
            .map(|(cell, ..)| configuration.kind(cell))
            .collect::<Vec<_>>();
        let entries = rendered
            .entries
            .iter()
            .zip(&kinds)
            .map(
                |((cell, side, spelling), kind)| cell_entries::SentenceEntry {
                    side: product_side(*side),
                    cell: cell.as_str(),
                    kind,
                    spelling: Some(spelling),
                },
            )
            .collect::<Vec<_>>();
        let parameters = rendered.parameters.iter().cloned().collect::<Vec<_>>();
        let groups = configuration.groups();
        let got = cell_entries::Sentence {
            form: entry_form(entry.form),
            entries: &entries,
            rewrite: product_rewrite(&rendered),
            parameters: &parameters,
            groups: &groups,
        }
        .judge()
        .err()
        .map(|(at, refusal)| {
            let (cell, side, _) = &rendered.entries[at];
            (cell.clone(), *side, refusal.class())
        });
        let (sentence, own) = match ordered_sentence(case, entry) {
            Ok(sentence) => sentence,
            Err(error) => {
                failures.push(format!("{}: {error}", case.id));
                continue;
            }
        };
        let (about, answer) = sentence_outcome(entry.form, &sentence, own);
        let want = match answer {
            Outcome::Refuse(class) => Some((
                sentence[about].0.cell.clone(),
                sentence[about].0.side,
                class,
            )),
            _ => None,
        };
        *counts
            .entry(if got == want { "agree" } else { "disagree" })
            .or_default() += 1;
        if got != want {
            failures.push(format!(
                "{}: the product's sentence answers {got:?}, the principles {want:?}",
                case.id
            ));
        }
    }
    println!("{counts:?}");
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

/// The sentence a kinds-base case's entry stands in, by its ID's second segment (its side, or
/// the name of its group's sentence, `class_matrix::kinds::groups`), so that a readable case's
/// `cells!` twin is the entry of the same sentence; other bases write one sentence per side.
fn sentence_of(case: &Case) -> &str {
    if case.base == Base::Kinds {
        case.id.split('/').nth(1).unwrap_or_default()
    } else {
        ""
    }
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
                    case.base,
                    sentence_of(case),
                    side_name(entry),
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
        let Some((_, twin)) = twins
            .iter()
            .find(|((base, sentence, side, cell, spelling), _)| {
                *base == case.base
                    && *sentence == sentence_of(case)
                    && *side == side_name(entry)
                    && *cell == entry.entry.cell
                    && *spelling == abbreviation
            })
        else {
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

/// Why check 4 lets a missing-instances advice on a Set or Map collection be refused again as
/// `instance-list-shape` (S5.0g, open for the orchestrator): [`advise`] wraps the value in the
/// collection's braces, a value item, which Q2 refuses in unordered braces (an unordered
/// instance is chosen by a written record). The advice the design states for such a cell is the
/// instance record (§2.3's S1 (b) row, `{ Account { child: v, .. }, .. }`), which no wrapping of
/// a value builds; check 4 first met an unordered collection with S5.0g's kinds base.
/// Check 4's one exemption (ruled at S5.0g): a value on a Set or Map collection is refused
/// `collection-without-instances`, and its wrapping in braces is Q2's value item, refused again
/// as `instance-list-shape`. The advice for such a cell is the instance record (§2.3's S1 (b)
/// row, `{ G { .. }, .. }`), a template no mechanical wrap of a value builds.
const UNORDERED_ADVICE: &str = "a value wrapped in unordered braces is Q2's value item; the advice is an instance record, which wrapping cannot build";

/// Check 4 (P3's reason, at every depth: S5.0g pattern review P-R5): a refusal for a missing
/// layer at the author's head has an advice, the spelling with every missing layer added, and
/// the advice passes form and kind, at its head and below it (pairing and sorts come next, and
/// the author meets them on the advised spelling). A refusal
/// for a marked ancestor (S1 (b)) advises the entry inside the ancestor's mark, so the entry
/// must be admitted by its own cell's layers (S5.0g review R3).
///
/// That each class's `advice` case is one the oracle admits is not checked here: the table's
/// resolution refuses an advice that is no accepted case (`AdviceNotAccepted`), check 1 makes
/// every accepted case agree with the oracle unless an exception names it, and check 2 refuses an
/// exception that names an accepted case.
#[test]
fn check_4_the_advice_of_a_missing_layer_passes_form_and_kind() {
    let mut failures = Vec::new();
    let mut unordered_advice = 0;
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
        // S1 (b) (S5.0g review R3): a path refusal's advice writes the author's entry inside
        // the ancestor's mark, at the ancestor's level, so the entry must be one the cell's own
        // layers admit there: judged without the path, steps 1 and 2 refuse nothing. Its
        // pairing is the ancestor entry's, against the ancestor's other side, which the advice
        // writes anew.
        if refusal.step == Step::Path {
            let verdict = match judge(form, side, &[], stack, spelling, &entry.context) {
                Err(again) if again.step != Step::Pairing => {
                    failures.push(format!(
                        "{}: refused as {} for its ancestor, and the advice, the entry inside \
                         the ancestor's mark, is refused again at the author's head as {}",
                        case.id, refusal.class, again.class
                    ));
                    "path, refused again"
                }
                _ => "path, admitted at the head",
            };
            *counts
                .entry(format!("{} {verdict}", refusal.class))
                .or_default() += 1;
            continue;
        }
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
        // P3's reason at every depth (S5.0g pattern review P-R5): the advice passes form and
        // kind, at its head and below it; its pairing and its sorts are later steps, which the
        // author meets next. The path is the ancestor's, judged above.
        let verdict = match judge(form, side, &[], stack, &advised, &entry.context) {
            Ok(_) => "admitted".to_owned(),
            Err(again) if again.step == Step::Pairing => "admitted, pairing next".to_owned(),
            Err(again)
                if again.depth == added
                    && refusal.class == "collection-without-instances"
                    && again.class == "instance-list-shape"
                    && matches!(
                        stack.first(),
                        Some(Layer::Instances(Order::Set | Order::Map))
                    ) =>
            {
                unordered_advice += 1;
                "refused again, unordered (UNORDERED_ADVICE)".to_owned()
            }
            Err(again) => {
                failures.push(format!(
                    "{}: refused as {}, and the advice {advised:?} is refused again as {} \
                     ({:?}, depth {})",
                    case.id, refusal.class, again.class, again.step, again.depth
                ));
                "refused again".to_owned()
            }
        };
        *counts
            .entry(format!("{} {verdict}", refusal.class))
            .or_default() += 1;
    }
    if unordered_advice == 0 {
        failures.push(format!(
            "no advice on an unordered collection is refused again: remove UNORDERED_ADVICE \
             ({UNORDERED_ADVICE})"
        ));
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
        (Mark::Value, Spelling::Literal(_) | Spelling::MapLit(_)) => "value:literal",
        (Mark::Value, Spelling::Record(_)) => "value:record",
        (Mark::Value, Spelling::Fragment(_)) => "value:fragment",
        (Mark::Value, Spelling::Call(_)) => "value:call",
        (Mark::Value, Spelling::ConfigVar(_)) => "value:cfgvar",
        (Mark::Value, _) => "value:other",
    }
    .to_owned()
}

/// The reason of an [`UNCOVERED`] entry whose tuples no case covers because the sweep golden
/// prints `outcome` at each of them, and the row's pattern in [`PATTERNS_FILE`] states the
/// principle that gives it, for review (the coverage ruling: cases cover every pair of the
/// domain's dimensions; interactions of more than two are the sweep's).
const SWEEP: &str = "judged by the sweep row's reviewed pattern in cells-outcome-patterns.tsv";

/// The tuples of the domain no generated case covers: `(form, side, path, stack, mark, reason)`,
/// each part a value or `*` for every value. An entry with the [`SWEEP`] reason leaves its tuples
/// to the sweep golden, which must print `outcome` at each; check 5 still requires every pair of
/// the domain's dimensions to be some case's, unless an entry with another reason names it.
const UNCOVERED: [(&str, &str, &str, &str, &str, &str); 3] = [
    ("*", "*", "*", "*", "*", SWEEP),
    ("*", "result", "below ?", "*", "*", MATCHED_BELOW),
    ("*", "result", "below *", "*", "*", MATCHED_BELOW),
];

/// Why no case has a matched result on a cell below a marked ancestor: a subject entry naming
/// the cell is refused for the ancestor whatever it spells (S1 (b)), at the kind step, so it
/// would be the sentence's answer before the result's (P4 over a sentence); a case's subject
/// matches the cell through the ancestor instead, which the context states as no subject entry
/// of the cell. The two are one point there: a result entry below the ancestor is refused at the
/// kind step too, before any pairing reads its other side.
const MATCHED_BELOW: &str = "a result below a marked ancestor is refused before its pairing";

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

/// A tuple of check 5's domain: form, side, path, stack and mark.
type Tuple = (&'static str, &'static str, &'static str, String, String);

/// The domain of check 5, in order.
fn domain() -> Vec<Tuple> {
    let mut domain = Vec::new();
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
                        domain.push((
                            form_name(form),
                            *side,
                            *path,
                            stack.to_owned(),
                            (*mark).to_owned(),
                        ));
                    }
                }
            }
        }
    }
    domain
}

/// The tuple's value at dimension `at` (0 form, 1 side, 2 path, 3 stack, 4 mark).
fn part(tuple: &Tuple, at: usize) -> &str {
    match at {
        0 => tuple.0,
        1 => tuple.1,
        2 => tuple.2,
        3 => &tuple.3,
        _ => &tuple.4,
    }
}

/// The pairs a tuple holds, as check 5 requires them: for each two of its dimensions, their
/// values, within the tuple's form (a form's marks are its own, and so are its sides).
fn pairs(tuple: &Tuple) -> Vec<(String, usize, String, usize, String)> {
    let mut pairs = Vec::new();
    for first in 0..5 {
        for second in first + 1..5 {
            pairs.push((
                tuple.0.to_owned(),
                first,
                part(tuple, first).to_owned(),
                second,
                part(tuple, second).to_owned(),
            ));
        }
    }
    pairs
}

/// The paths the sweep prints a form's rows at: every one for a rule or claim form, and none
/// but the record's level for an initializer, a struct literal of the configuration, which
/// names no cell by a path (S1 (b) is the rule forms').
fn sweep_paths<T>(form: Form, paths: &[T]) -> &[T] {
    if form == Form::Init {
        &paths[..1]
    } else {
        paths
    }
}

/// The tuples at which the sweep golden prints `outcome`: its form, side, path and stack by row,
/// its mark by column. The second computation differs from the first by its name only (P1), so
/// the computation's rows are its.
fn sweep_tuples() -> BTreeSet<Tuple> {
    let mut tuples = BTreeSet::new();
    let paths: [(&str, Vec<Layer>); 3] = [
        ("none", Vec::new()),
        ("below ?", vec![Layer::Optional]),
        ("below *", vec![Layer::Instances(Order::List)]),
    ];
    for form in [Form::Readable, Form::Claim, Form::Cells, Form::Init] {
        let sides: &[&str] = if form == Form::Init {
            &["initializer"]
        } else {
            &["subject", "result", "result-unmatched"]
        };
        for (_, stack) in sweep_stacks() {
            let mut names = vec![stack_name("", &stack)];
            if stack == [Layer::Computation] {
                names.push("second computation".to_owned());
            }
            for text in sweep_spellings(form)
                .iter()
                .chain(sweep_more_spellings(form))
                .chain(sweep_back_spellings(form))
            {
                let probe = Probe {
                    form,
                    side: Side::Subject,
                    path: &[],
                    stack: &stack,
                    text,
                    other: None,
                    written: false,
                    bound: &[],
                    records: &[],
                    elsewhere: false,
                };
                let mark = mark_name(form, &declared_as(&probe.read(text)));
                for side in sides {
                    for (path, _) in sweep_paths(form, &paths) {
                        for name in &names {
                            tuples.insert((
                                form_name(form),
                                *side,
                                *path,
                                name.clone(),
                                mark.clone(),
                            ));
                        }
                    }
                }
            }
        }
    }
    tuples
}

/// Check 5: every pair of the domain's dimensions (form, side, path, stack and mark; matched or
/// unmatched is the side's) is some generated case's, within its form, so each mark of a form
/// is met on every stack: the coverage ruling. A tuple no case covers is listed in
/// [`UNCOVERED`]; one listed with the [`SWEEP`] reason must be a tuple the sweep golden prints
/// `outcome` at, and a missing pair fails unless an entry with another reason names it. Every
/// entry lists some tuple no case covers. A rule form's sides are its subject, its result over a
/// matched cell and over an unmatched one; an initializer's is its value, which names no cell
/// through a path (a struct literal names its own fields only).
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
    let domain = domain();
    let uncovered = domain
        .iter()
        .filter(|tuple| !covered.contains(*tuple))
        .collect::<Vec<_>>();
    let lists = |entry: &(&str, &str, &str, &str, &str, &str), tuple: &Tuple| {
        (0..5).all(|at| {
            let value = [entry.0, entry.1, entry.2, entry.3, entry.4][at];
            value == "*" || value == part(tuple, at)
        })
    };
    let mut failures = Vec::new();
    let sweep = sweep_tuples();
    for tuple in &uncovered {
        let listing = UNCOVERED
            .iter()
            .filter(|entry| lists(entry, tuple))
            .collect::<Vec<_>>();
        if listing.is_empty() {
            failures.push(format!("uncovered and not listed: {tuple:?}"));
        } else if listing.iter().all(|entry| entry.5 == SWEEP) && !sweep.contains(*tuple) {
            failures.push(format!(
                "left to the sweep, which prints no outcome at it: {tuple:?}"
            ));
        }
    }
    for entry in &UNCOVERED {
        if !uncovered.iter().any(|tuple| lists(entry, tuple)) {
            failures.push(format!(
                "UNCOVERED lists {entry:?}, which cases cover: remove it"
            ));
        }
    }
    let have = covered.iter().flat_map(pairs).collect::<BTreeSet<_>>();
    let names = |pair: &(String, usize, String, usize, String),
                 entry: &(&str, &str, &str, &str, &str, &str)| {
        let values = [entry.0, entry.1, entry.2, entry.3, entry.4];
        (values[0] == "*" || values[0] == pair.0)
            && (values[pair.1] == "*" || values[pair.1] == pair.2)
            && (values[pair.3] == "*" || values[pair.3] == pair.4)
    };
    let dimension = ["form", "side", "path", "stack", "mark"];
    let mut missing = 0;
    let mut excused = BTreeSet::new();
    for pair in domain.iter().flat_map(pairs).collect::<BTreeSet<_>>() {
        if have.contains(&pair) {
            continue;
        }
        missing += 1;
        let by = UNCOVERED
            .iter()
            .position(|entry| entry.5 != SWEEP && names(&pair, entry));
        if let Some(by) = by {
            excused.insert(by);
        } else {
            failures.push(format!(
                "{}: no case has {} {:?} with {} {:?}",
                pair.0, dimension[pair.1], pair.2, dimension[pair.3], pair.4
            ));
        }
    }
    for (at, entry) in UNCOVERED.iter().enumerate() {
        if entry.5 != SWEEP && !excused.contains(&at) {
            failures.push(format!(
                "UNCOVERED {entry:?} names no missing pair: give it the sweep reason"
            ));
        }
    }
    println!(
        "domain {}, covered {}, uncovered {}, pairs missing {missing}",
        domain.len(),
        domain.len() - uncovered.len(),
        uncovered.len()
    );
    assert!(
        failures.is_empty(),
        "{} failures: {:#?}",
        failures.len(),
        failures.iter().take(60).collect::<Vec<_>>()
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
    /// it; for a subject, the result's entry of the cell, where the probe states one.
    other: Option<&'p str>,
    /// For a subject, whether the result writes the cell.
    written: bool,
    bound: &'p [&'p str],
    /// The bound names an alias binds to a record, with the record's head constructor.
    records: &'p [(&'p str, &'p str)],
    /// Whether each bound name an update `..name` names binds, besides, a record of that
    /// update's own constructor matched elsewhere (the children sweep's reading of `me`,
    /// [`sweep::update_records`]).
    elsewhere: bool,
}

impl Probe<'_> {
    fn reading(&self) -> EntryReading<'static> {
        static VARIABLES: LazyLock<Vec<String>> = LazyLock::new(|| {
            ["pgm", "env", "base"]
                .into_iter()
                .map(str::to_owned)
                .collect()
        });
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

    /// The names the probe binds to a record, with their heads: its `records`, then, with
    /// `elsewhere`, its updates' bases.
    fn records(&self) -> Vec<(String, String)> {
        let mut records = self
            .records
            .iter()
            .map(|(name, head)| ((*name).to_owned(), (*head).to_owned()))
            .collect::<Vec<_>>();
        if self.elsewhere {
            for found in sweep::update_records(self.bound, &probed_as(&self.read(self.text))) {
                if !records.iter().any(|(known, _)| *known == found.0) {
                    records.push(found);
                }
            }
        }
        records
    }

    fn context(&self) -> class_matrix::cells_oracle::Context {
        class_matrix::cells_oracle::Context {
            bound: self.bound.iter().map(|name| (*name).to_owned()).collect(),
            records: self.records(),
            other: self.other.map(|text| probed_as(&self.read(text))),
            written: self.written,
            groups: self.groups(),
        }
    }

    /// The groups of the probe's configuration: those of its path and stack, and `G` (a, b:
    /// Int), the group a term's record names.
    fn groups(&self) -> Vec<Group> {
        let mut groups = Vec::new();
        for layers in [self.path, self.stack, &[group_g()][..]] {
            class_matrix::cells_oracle::collect_groups(layers, &mut groups);
        }
        groups
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
            &probed_as(&self.read(self.text)),
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
        let records = self.records();
        let bound = |name: &str| {
            self.bound.contains(&name).then(|| {
                records
                    .iter()
                    .find(|(bound, _)| bound == name)
                    .map_or(Bound::Value, |(_, head)| Bound::Record(head.clone()))
            })
        };
        let groups = self
            .groups()
            .iter()
            .map(|group| match product_layer(&Layer::Group(group.clone())) {
                cell_kind::Layer::Group(group) => group,
                other => unreachable!("a group's layer is {other:?}"),
            })
            .collect::<Vec<_>>();
        let admitted =
            match cell_entries::admit(form, side, &path, &stack, &spelling, &bound, &groups) {
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
            &bound,
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
        records: &[],
        elsewhere: false,
    };
    let (subject, result) = (Side::Subject, Side::Result);
    let probes = [
        // R1: an ancestor's mark spelled in the entry admits nothing. It is no mark of the
        // cell's own layers, which refuse it first (S5.0g review R3, P3's reason: the path's
        // advice, the entry inside the ancestor's mark, would be refused again).
        (
            probe(Form::Readable, subject, &optional, &int, "Some(x)", None),
            "presence-on-plain-cell",
        ),
        (
            probe(Form::Readable, subject, &map, &int, "{ .. }", None),
            "instances-on-plain-cell",
        ),
        (
            probe(Form::Readable, subject, &list, &int, "[x, ..]", None),
            "bracket-reading",
        ),
        (
            probe(Form::Cells, subject, &list, &int, "[x, ..]", None),
            "instances-on-plain-cell",
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

/// S5.0g review R3 (P3's reason): the cell's own kind is judged before its path (S1 (b)), since
/// the path's advice writes the entry inside the ancestor's mark: a spelling the cell's own
/// layers admit is refused for its ancestor, and one they refuse, by (b) or (c), is refused by
/// them.
#[test]
fn a_cell_below_a_marked_ancestor_is_judged_on_its_own_layers_first() {
    let optional = [Layer::Optional];
    let map = [Layer::Instances(Order::Map)];
    let list = [Layer::Instances(Order::List)];
    let int = int();
    let jobs = [Layer::Instances(Order::List), group_g()];
    let probe = |form, path, stack, text| Probe {
        form,
        side: Side::Subject,
        path,
        stack,
        text,
        other: None,
        written: false,
        bound: &[],
        records: &[],
        elsewhere: false,
    };
    probes_agree(&[
        // A spelling the cell's own layers admit is refused for its ancestor (S1 (b)).
        (
            probe(Form::Readable, &optional, &int, "x"),
            Outcome::Refuse("optional-without-presence"),
        ),
        (
            probe(Form::Readable, &map, &int, "x"),
            Outcome::Refuse("collection-without-instances"),
        ),
        (
            probe(
                Form::Readable,
                &list,
                &[Layer::Optional, Layer::Leaf(Notation::Plain)],
                "Some(x)",
            ),
            Outcome::Refuse("collection-without-instances"),
        ),
        (
            probe(Form::Cells, &optional, &int, "k::configuration::Cell(x)"),
            Outcome::Refuse("optional-without-presence"),
        ),
        // The cell's own P3 (c) comes first too: a value on its own `?` layer below a `*`.
        (
            probe(
                Form::Readable,
                &list,
                &[Layer::Optional, Layer::Leaf(Notation::Plain)],
                "x",
            ),
            Outcome::Refuse("optional-without-presence"),
        ),
        (
            probe(Form::Readable, &optional, &jobs, "x"),
            Outcome::Refuse("collection-without-instances"),
        ),
    ]);
}

/// Each probe's outcome, from the oracle and from the product alike, against `want`.
fn probes_agree(probes: &[(Probe<'_>, Outcome)]) {
    let mut failures = Vec::new();
    for (probe, want) in probes {
        for (who, got) in [("oracle", probe.oracle()), ("product", probe.product())] {
            if got != *want {
                failures.push(format!(
                    "{:?} {:?} below {:?} on {:?}: `{}` over {:?}: the {who} says {got:?}, the \
                     principles {want:?}",
                    probe.form, probe.side, probe.path, probe.stack, probe.text, probe.other
                ));
            }
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

const fn result_probe<'p>(
    form: Form,
    stack: &'p [Layer],
    text: &'p str,
    other: Option<&'p str>,
) -> Probe<'p> {
    Probe {
        form,
        side: Side::Result,
        path: &[],
        stack,
        text,
        other,
        written: false,
        bound: &["x", "y", "z"],
        records: &[],
        elsewhere: false,
    }
}

/// S5.0g pattern review P-R2 (P4, P6): a `cells!` result's `Cell(k::map![.., ..])` is the leaf's
/// content root, lexically (the direct argument of `Cell(..)`), so the form step refuses nothing
/// in it: its kind judges it, and pairing judges its `..` against the subject's map at the same
/// cell, which keeps it where the subject framed its rest (P6 at the map's content root, M3) and
/// refuses it as `rest-mismatch` where the subject wrote no rest, bound the map whole, matched
/// nothing (Q1's overwrite) or `None` (a created cell). A readable `map![..]` is a literal
/// everywhere (readable writes `{ k -> v, .. }`). The product refuses every such `cells!` result
/// still, `anonymous-rest-in-map-literal`: the stated M3 limitation.
#[test]
fn a_cells_result_map_with_a_rest_at_its_leaf_root_is_judged_by_kind_and_pairing() {
    let arm = Outcome::Refuse("anonymous-rest-in-map-literal");
    let rm = Outcome::Refuse("rest-mismatch");
    let map = [Layer::Leaf(Notation::Map)];
    let optional_map = [Layer::Optional, Layer::Leaf(Notation::Map)];
    let cell = "k::configuration::Cell(k::map![y -> x, ..])";
    let framing = "k::configuration::Cell(k::map![z -> y, ..])";
    let probes = [
        (
            result_probe(Form::Cells, &map, cell, Some(framing)),
            Outcome::After,
            arm,
        ),
        (
            result_probe(
                Form::Cells,
                &map,
                cell,
                Some("k::configuration::Cell(k::map![z -> y])"),
            ),
            rm,
            arm,
        ),
        (
            result_probe(Form::Cells, &map, cell, Some("k::configuration::Cell(old)")),
            rm,
            arm,
        ),
        (result_probe(Form::Cells, &map, cell, None), rm, arm),
        (
            result_probe(
                Form::Cells,
                &[Layer::Leaf(Notation::Plain)],
                cell,
                Some("k::configuration::Cell(old)"),
            ),
            Outcome::Refuse("map-notation-at-non-map"),
            arm,
        ),
        (
            result_probe(
                Form::Cells,
                &optional_map,
                cell,
                Some("Some(k::configuration::Cell(k::map![z -> y, ..]))"),
            ),
            Outcome::Refuse("optional-without-presence"),
            arm,
        ),
        (
            result_probe(
                Form::Cells,
                &optional_map,
                "Some(k::configuration::Cell(k::map![y -> x, ..]))",
                Some("Some(k::configuration::Cell(k::map![z -> y, ..]))"),
            ),
            Outcome::After,
            arm,
        ),
        (
            result_probe(
                Form::Cells,
                &optional_map,
                "Some(k::configuration::Cell(k::map![y -> x, ..]))",
                Some("None"),
            ),
            rm,
            arm,
        ),
        (
            result_probe(
                Form::Readable,
                &map,
                "map![y -> x, ..]",
                Some("{ z -> y, .. }"),
            ),
            arm,
            arm,
        ),
    ];
    oracle_and_product(&probes);
}

/// The same lexical reading at a record's child (the S5.0g fixes review's F-1, ruled): P1 makes
/// a record's child an entry, so the direct value of a field of a group record, an instance
/// record or a fragment at a configuration position is its child cell's content, a content root
/// (P6) exactly as `Cell(..)`'s argument is: a fragment's Map child `m: k::map![y -> x, ..]` is
/// judged by kind and pairing against the subject's same child, as the readable record it
/// abbreviates is (P7), and the product's `arm` there is the stated M3 limitation, as its
/// `map-read-in-result` is for the readable record's map read (S5.0g item 3a fixes, F-8). Below that,
/// inside a term (a list's element, a constructor's argument), and at an entry's head without its
/// leaf's `Cell(..)`, the literal stays `anonymous-rest-in-map-literal` (P6: below a root,
/// notation is a term's).
#[test]
fn a_cells_result_map_with_a_rest_at_a_records_child_is_judged_by_pairing() {
    let arm = Outcome::Refuse("anonymous-rest-in-map-literal");
    let rm = Outcome::Refuse("rest-mismatch");
    let int = Layer::Leaf(Notation::Plain);
    let group = [sweep_group(
        "B",
        &[("m", Layer::Leaf(Notation::Map)), ("n", int.clone())],
    )];
    let keyed = [
        Layer::Instances(Order::Map),
        sweep_group("A", &[("id", int), ("m", Layer::Leaf(Notation::Map))]),
    ];
    let probes = [
        (
            result_probe(
                Form::Cells,
                &group,
                "k::fragment![crate::B { m: k::map![y -> x, ..], n: 0 }]",
                Some("k::fragment![crate::B { m: k::map![z -> y, ..], .. }]"),
            ),
            Outcome::After,
            arm,
        ),
        (
            result_probe(
                Form::Readable,
                &group,
                "B { m: { y -> x, .. }, n: 0 }",
                Some("B { m: { z -> y, .. }, .. }"),
            ),
            Outcome::After,
            Outcome::Refuse("map-read-in-result"),
        ),
        (
            result_probe(
                Form::Cells,
                &group,
                "k::fragment![crate::B { m: k::map![y -> x, ..], n: 0 }]",
                Some("k::fragment![crate::B { m: k::map![z -> y], .. }]"),
            ),
            rm,
            arm,
        ),
        (
            result_probe(
                Form::Cells,
                &group,
                "k::fragment![crate::B { m: k::map![y -> x, ..], n: 0 }]",
                Some("k::fragment![crate::B { n: z, .. }]"),
            ),
            rm,
            arm,
        ),
        (
            Probe {
                bound: &["x", "y", "z", "me"],
                records: &[],
                elsewhere: false,
                ..result_probe(
                    Form::Cells,
                    &keyed,
                    "{ k::fragment![crate::A { m: k::map![y -> x, ..], ..me }], .. }",
                    Some("{ me @ k::fragment![crate::A { id: z, m: k::map![z -> y, ..] }], .. }"),
                )
            },
            Outcome::After,
            arm,
        ),
        (
            result_probe(
                Form::Cells,
                &[Layer::Leaf(Notation::Map)],
                "k::map![y -> x, ..]",
                Some("k::configuration::Cell(k::map![z -> y, ..])"),
            ),
            arm,
            arm,
        ),
    ];
    oracle_and_product(&probes);
}

/// Below a content root, inside a term (a list's element, a constructor's argument), a
/// `cells!` result's `k::map![.., ..]` is a literal, `anonymous-rest-in-map-literal`, in the
/// oracle and the product alike (P6: below a root, notation is a term's; S5.0g fixes review
/// F-1).
#[test]
fn a_cells_result_map_with_a_rest_inside_a_term_is_a_literal() {
    let arm = Outcome::Refuse("anonymous-rest-in-map-literal");
    let int = Layer::Leaf(Notation::Plain);
    let group = [sweep_group(
        "B",
        &[("m", Layer::Leaf(Notation::Map)), ("n", int.clone())],
    )];
    let list = [sweep_group(
        "H",
        &[("l", Layer::Leaf(Notation::List)), ("b", int)],
    )];
    let probes = [
        (
            result_probe(
                Form::Cells,
                &list,
                "k::fragment![crate::H { l: [k::map![y -> x, ..]], b: 0 }]",
                Some("k::fragment![crate::H { l: [y, ..], .. }]"),
            ),
            arm,
            arm,
        ),
        (
            result_probe(
                Form::Cells,
                &group,
                "k::fragment![crate::B { m: Cmd::Hold(k::map![y -> x, ..]), n: 0 }]",
                Some("k::fragment![crate::B { m: k::map![z -> y, ..], .. }]"),
            ),
            arm,
            arm,
        ),
    ];
    oracle_and_product(&probes);
}

/// S5.0g pattern review P-R1 (P0, P2): a cons list is built from its front, so an item after its
/// rest lowers to no K, in a subject and in a result, readable and `cells!` alike:
/// `cons-list-back-item`, a refusal inside the leaf's mark, which stands under a path and comes
/// before pairing. The builtin List is matched at either end.
#[test]
fn a_cons_lists_back_item_is_refused_inside_its_mark() {
    let cons = [Layer::Leaf(Notation::Cons)];
    let list = [Layer::Leaf(Notation::List)];
    let optional = [Layer::Optional];
    let back = Outcome::Refuse("cons-list-back-item");
    let subject = |form, path, stack, text| Probe {
        form,
        side: Side::Subject,
        path,
        stack,
        text,
        other: None,
        written: false,
        bound: &[],
        records: &[],
        elsewhere: false,
    };
    probes_agree(&[
        (subject(Form::Readable, &[], &cons, "[.., x]"), back),
        (subject(Form::Readable, &[], &cons, "[x, .., y]"), back),
        (subject(Form::Readable, &optional, &cons, "[.., x]"), back),
        (
            subject(Form::Cells, &[], &cons, "k::configuration::Cell([.., x])"),
            back,
        ),
        (
            subject(Form::Readable, &[], &list, "[.., x]"),
            Outcome::Admit { lint: None },
        ),
        (
            subject(Form::Readable, &[], &cons, "[x, ..]"),
            Outcome::Admit { lint: None },
        ),
        (result_probe(Form::Readable, &cons, "[.., x]", None), back),
        (
            result_probe(Form::Readable, &cons, "[.., x]", Some("[y, ..]")),
            back,
        ),
        (
            result_probe(Form::Readable, &cons, "[..r, x]", Some("[y, r @ ..]")),
            back,
        ),
    ]);
}

/// S5.0g pattern review P-R4 (P2, P3b): brackets on a Set or Map collection are its instance mark
/// of the wrong order, `instance-list-shape`, whatever they hold; on a cell with no instance
/// layer they denote nothing, `bracket-reading`.
#[test]
fn brackets_on_an_unordered_collection_are_its_instance_mark_of_the_wrong_order() {
    let set = [Layer::Instances(Order::Set), group_g()];
    let map = [Layer::Instances(Order::Map), group_g()];
    let shape = Outcome::Refuse("instance-list-shape");
    let subject = |stack, text| Probe {
        form: Form::Readable,
        side: Side::Subject,
        path: &[],
        stack,
        text,
        other: None,
        written: false,
        bound: &[],
        records: &[],
        elsewhere: false,
    };
    let int = int();
    probes_agree(&[
        (subject(&set, "[x, ..]"), shape),
        (subject(&set, "[..]"), shape),
        (subject(&map, "[G { a: x, .. }, ..]"), shape),
        (subject(&map, "[x]"), shape),
        (subject(&int, "[x, ..]"), Outcome::Refuse("bracket-reading")),
    ]);
}

/// S5.0g pattern review P-R5 (P3's reason at every depth): an entry is refused for a missing
/// outer layer only where its inside passes form and kind against the deeper layers; otherwise
/// the inside's own refusal is named, since the advice would be refused again there.
#[test]
fn a_missing_layer_is_named_only_where_its_inside_passes() {
    let optional_int = [Layer::Optional, Layer::Leaf(Notation::Plain)];
    let optional_group = [Layer::Optional, group_g()];
    let set = [Layer::Instances(Order::Set), group_g()];
    let probe = |form, stack, text| Probe {
        form,
        side: Side::Subject,
        path: &[],
        stack,
        text,
        other: None,
        written: false,
        bound: &[],
        records: &[],
        elsewhere: false,
    };
    probes_agree(&[
        (
            probe(
                Form::Cells,
                &optional_int,
                "k::configuration::Cell([x, ..])",
            ),
            Outcome::Refuse("bracket-reading"),
        ),
        (
            probe(
                Form::Cells,
                &optional_int,
                "k::configuration::Cell(k::map![y -> x, ..])",
            ),
            Outcome::Refuse("map-notation-at-non-map"),
        ),
        (
            probe(Form::Cells, &optional_int, "k::configuration::Cell(x)"),
            Outcome::Refuse("optional-without-presence"),
        ),
        (
            probe(Form::Cells, &optional_int, "x"),
            Outcome::Refuse("optional-without-presence"),
        ),
        (
            probe(Form::Readable, &optional_group, "G { a: x }"),
            Outcome::Refuse("record-missing-children"),
        ),
        (
            probe(Form::Readable, &optional_group, "G { a: x, .. }"),
            Outcome::Refuse("optional-without-presence"),
        ),
        (
            probe(Form::Readable, &set, "G { a: x }"),
            Outcome::Refuse("record-missing-children"),
        ),
        (
            probe(Form::Cells, &set, "k::fragment![crate::G { a: x }]"),
            Outcome::Refuse("record-missing-children"),
        ),
        // The inside passes against the instance's group, so the missing instances are named,
        // though wrapping the value in braces would be Q2's value item (check 4's exemption).
        (
            probe(Form::Readable, &set, "x"),
            Outcome::Refuse("collection-without-instances"),
        ),
    ]);
}

/// Each probe's oracle and product answers against the ones given for each.
fn oracle_and_product(probes: &[(Probe<'_>, Outcome, Outcome)]) {
    let mut failures = Vec::new();
    for (probe, oracle, product) in probes {
        for (who, got, want) in [
            ("oracle", probe.oracle(), oracle),
            ("product", probe.product(), product),
        ] {
            if got != *want {
                failures.push(format!(
                    "{:?} on {:?}: `{}` over {:?}: the {who} says {got:?}, not {want:?}",
                    probe.form, probe.stack, probe.text, probe.other
                ));
            }
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

/// F1: a result `None` over a `?` cell the subject matches present removes the cell, and with it
/// all its content, its rest included (P5); it writes no content root, so P6 pairs no rest.
#[test]
fn a_result_none_over_a_matched_optional_cell_pairs_no_rest() {
    let list = [Layer::Optional, Layer::Leaf(Notation::List)];
    let map = [Layer::Optional, Layer::Leaf(Notation::Map)];
    let ok = Outcome::Admit { lint: None };
    probes_agree(&[
        (
            result_probe(Form::Readable, &list, "None", Some("Some([y, ..])")),
            ok,
        ),
        (
            result_probe(Form::Claim, &map, "None", Some("Some({ z -> y, .. })")),
            ok,
        ),
        (
            result_probe(
                Form::Cells,
                &list,
                "None",
                Some("Some(k::configuration::Cell([y, ..]))"),
            ),
            ok,
        ),
        (
            result_probe(
                Form::Cells,
                &map,
                "None",
                Some("Some(k::configuration::Cell(k::map![z -> y, ..]))"),
            ),
            ok,
        ),
        // A result that writes the content pairs its rest with the subject's.
        (
            result_probe(Form::Readable, &list, "Some(x)", Some("Some([y, ..])")),
            Outcome::Refuse("rest-mismatch"),
        ),
        (
            result_probe(Form::Readable, &list, "None", None),
            Outcome::Refuse("unmatched-optional-result"),
        ),
    ]);
}

/// F2: `name @ P` stands in a pattern only (§2.3 step 1), and a rest is no exception: a result
/// writes `..` or `..name` (P6), at every content root, before the path is judged.
#[test]
fn a_named_rest_in_a_result_is_refused_at_the_form() {
    let refused = Outcome::Refuse("alias-outside-pattern");
    let list = [Layer::Leaf(Notation::List)];
    let map = [Layer::Leaf(Notation::Map)];
    let computation = [Layer::Computation];
    let instances = [Layer::Instances(Order::List), group_g()];
    let mut below = result_probe(Form::Readable, &list, "[x, r @ ..]", Some("[y, ..]"));
    below.path = &[Layer::Optional];
    probes_agree(&[
        (
            result_probe(Form::Readable, &list, "[x, r @ ..]", Some("[y, ..]")),
            refused,
        ),
        (
            result_probe(Form::Readable, &list, "[x, r @ ..]", None),
            refused,
        ),
        (
            result_probe(Form::Claim, &computation, "[x, r @ ..]", Some("[y, ..]")),
            refused,
        ),
        (
            result_probe(Form::Readable, &map, "{ y -> x, r @ .. }", None),
            refused,
        ),
        (
            result_probe(
                Form::Cells,
                &computation,
                "k::configuration::KCell(x, r @ ..)",
                Some("k::configuration::KCell(y, ..)"),
            ),
            refused,
        ),
        (
            result_probe(
                Form::Cells,
                &list,
                "k::configuration::Cell([x, r @ ..])",
                None,
            ),
            refused,
        ),
        (
            result_probe(
                Form::Cells,
                &instances,
                "[k::fragment![crate::G { a: x, .. }], r @ ..]",
                Some("[k::fragment![crate::G { a: y, .. }], ..]"),
            ),
            refused,
        ),
        (below, refused),
    ]);
}

/// R4 under the vacuous-rest ruling (P6, P0): a bare `..` in a built record is Rust's default
/// fields, so it is refused exactly where it leaves a declared field unnamed; here the record of
/// a group that exists, and a child's record inside it. A `..` after every field defaults none:
/// Rust and K read the same exact record.
#[test]
fn a_bare_rest_in_a_built_record_is_refused_where_it_leaves_a_field_open() {
    let open = Outcome::Refuse("open-record-outside-pattern");
    let group = [group_g()];
    let w = children_stack("group W");
    let frame = [sweep_group(
        "Frame",
        &[("ret", Layer::Leaf(Notation::Plain))],
    )];
    probes_agree(&[
        // The record of a group that exists: open on `G { a, b }` without `b`, exact with it.
        (
            result_probe(
                Form::Readable,
                &group,
                "G { a: x, .. }",
                Some("G { a: y, .. }"),
            ),
            open,
        ),
        (
            result_probe(
                Form::Readable,
                &group,
                "G { a: x, b: y, .. }",
                Some("G { a: y, .. }"),
            ),
            Outcome::After,
        ),
        (
            result_probe(Form::Claim, &group, "G { a: x, b: y, .. }", None),
            Outcome::After,
        ),
        (
            result_probe(
                Form::Cells,
                &group,
                "k::fragment![crate::G { a: x, b: y, .. }]",
                Some("k::fragment![crate::G { a: y, .. }]"),
            ),
            Outcome::After,
        ),
        (
            result_probe(
                Form::Cells,
                &frame,
                "k::fragment![crate::Frame { ret: x, .. }]",
                Some("k::fragment![crate::Frame { ret: y, .. }]"),
            ),
            Outcome::After,
        ),
        // A child's record inside a record.
        (
            result_probe(Form::Readable, &w, "W { g: G { a: x, .. }, n: 0 }", None),
            open,
        ),
        (
            result_probe(
                Form::Readable,
                &w,
                "W { g: G { a: x, b: y, .. }, n: 0 }",
                None,
            ),
            Outcome::After,
        ),
    ]);
}

/// R4 under the vacuous-rest ruling, on a term: a record a result's value writes at a leaf, or
/// where the missing layer's advice puts it, is refused where its bare `..` leaves a field open,
/// and judged as the value it is otherwise (P6, P0, P3's reason). A record whose head names no
/// group of the configuration has no fields it is known to name, so its `..` is open.
#[test]
fn a_bare_rest_in_a_term_is_refused_where_it_leaves_a_field_open() {
    let open = Outcome::Refuse("open-record-outside-pattern");
    let set = [Layer::Leaf(Notation::Set)];
    let code = [Layer::Computation];
    let optional_list = [Layer::Optional, Layer::Leaf(Notation::List)];
    probes_agree(&[
        (
            result_probe(Form::Readable, &set, "G { a: x, .. }", Some("old")),
            open,
        ),
        (
            result_probe(Form::Readable, &set, "G { a: x, b: y, .. }", Some("old")),
            Outcome::After,
        ),
        (
            result_probe(Form::Readable, &code, "G { a: x, .. }", Some("[y, ..]")),
            open,
        ),
        (
            result_probe(
                Form::Readable,
                &code,
                "G { a: x, b: y, .. }",
                Some("[y, ..]"),
            ),
            Outcome::Refuse("cell-wrapper"),
        ),
        (
            result_probe(
                Form::Readable,
                &optional_list,
                "G { a: x, .. }",
                Some("Some([y, ..])"),
            ),
            open,
        ),
        (
            result_probe(
                Form::Readable,
                &optional_list,
                "G { a: x, b: y, .. }",
                Some("Some([y, ..])"),
            ),
            Outcome::Refuse("optional-without-presence"),
        ),
        (
            result_probe(
                Form::Cells,
                &set,
                "k::configuration::Cell(k::fragment![crate::G { a: x, b: y, .. }])",
                Some("k::configuration::Cell(old)"),
            ),
            Outcome::After,
        ),
        (
            result_probe(
                Form::Cells,
                &set,
                "k::configuration::Cell(k::fragment![crate::G { a: x, .. }])",
                Some("k::configuration::Cell(old)"),
            ),
            open,
        ),
        // A head no group names.
        (
            result_probe(Form::Readable, &set, "Q { a: x, .. }", Some("old")),
            open,
        ),
    ]);
}

/// F3: a bare `..` in a result is Rust's default fields, which only a created instance has (its
/// template, P6): refused on a group the subject matches, admitted on an instance record.
#[test]
fn a_result_group_record_with_a_bare_rest_is_refused_over_a_matched_group() {
    let refused = Outcome::Refuse("open-record-outside-pattern");
    let group = [group_g()];
    let optional = [Layer::Optional, group_g()];
    let set = [Layer::Instances(Order::Set), group_g()];
    probes_agree(&[
        (
            result_probe(
                Form::Readable,
                &group,
                "G { a: x, .. }",
                Some("G { a: y, .. }"),
            ),
            refused,
        ),
        (
            result_probe(
                Form::Claim,
                &group,
                "G { a: x, .. }",
                Some("G { a: y, .. }"),
            ),
            refused,
        ),
        (
            result_probe(
                Form::Readable,
                &optional,
                "Some(G { a: x, .. })",
                Some("Some(G { a: y, .. })"),
            ),
            refused,
        ),
        (
            result_probe(
                Form::Readable,
                &group,
                "G { a: x, b: 0 }",
                Some("G { a: y, .. }"),
            ),
            Outcome::After,
        ),
        (
            result_probe(
                Form::Readable,
                &set,
                "{ G { a: x, .. }, .. }",
                Some("{ G { a: y, .. }, .. }"),
            ),
            Outcome::After,
        ),
    ]);
}

/// Ruling 1 on F3: a result over a group the subject does not match overwrites a group that
/// exists already, so a bare `..` there has no default fields to give (P6); only a created
/// instance, or a `?` cell created over a subject `None`, has its template's.
#[test]
fn a_result_group_record_with_a_bare_rest_is_refused_over_an_overwritten_group() {
    let refused = Outcome::Refuse("open-record-outside-pattern");
    let group = [group_g()];
    let optional = [Layer::Optional, group_g()];
    let set = [Layer::Instances(Order::Set), group_g()];
    probes_agree(&[
        (
            result_probe(Form::Readable, &group, "G { a: x, .. }", None),
            refused,
        ),
        (
            result_probe(Form::Claim, &group, "G { a: x, .. }", None),
            refused,
        ),
        (
            result_probe(Form::Readable, &group, "G { a: x, b: 0 }", None),
            Outcome::After,
        ),
        (
            result_probe(Form::Readable, &optional, "Some(G { a: x, .. })", None),
            Outcome::Refuse("unmatched-optional-result"),
        ),
        (
            result_probe(
                Form::Readable,
                &optional,
                "Some(G { a: x, .. })",
                Some("None"),
            ),
            Outcome::After,
        ),
        (
            result_probe(Form::Readable, &set, "{ G { a: x, .. } }", None),
            Outcome::After,
        ),
    ]);
}

/// D-3 (S5.0g): `k::fragment![crate::G { a: x, .. }]` is the record readable `G { a: x, .. }`
/// abbreviates (P7), so its bare `..` in a result is Rust's default fields too, which a group that
/// exists, matched or overwritten, does not have (P6, ruling 1); a `?` cell created over a
/// subject `None` and a created instance have their template's.
#[test]
fn a_result_group_fragment_with_a_bare_rest_is_refused_over_an_existing_group() {
    let refused = Outcome::Refuse("open-record-outside-pattern");
    let group = [group_g()];
    let optional = [Layer::Optional, group_g()];
    let list = [Layer::Instances(Order::List), group_g()];
    let open = "k::fragment![crate::G { a: x, .. }]";
    let open_present = "Some(k::fragment![crate::G { a: x, .. }])";
    probes_agree(&[
        (
            result_probe(
                Form::Cells,
                &group,
                open,
                Some("k::fragment![crate::G { a: y, .. }]"),
            ),
            refused,
        ),
        (result_probe(Form::Cells, &group, open, None), refused),
        (
            result_probe(
                Form::Cells,
                &optional,
                open_present,
                Some("Some(k::fragment![crate::G { a: y, .. }])"),
            ),
            refused,
        ),
        (
            result_probe(Form::Cells, &optional, open_present, Some("None")),
            Outcome::After,
        ),
        (
            result_probe(
                Form::Cells,
                &group,
                "k::fragment![crate::G { a: x, b: 0 }]",
                None,
            ),
            Outcome::After,
        ),
        (
            result_probe(
                Form::Cells,
                &list,
                "[k::fragment![crate::G { a: x, .. }], ..]",
                Some("[k::fragment![crate::G { a: y, .. }], ..]"),
            ),
            Outcome::After,
        ),
    ]);
}

/// D-4 (L4, P6, P7): a `cells!` fragment of the position's group without `..` names every child,
/// as the readable record it abbreviates does: records follow Rust, in a pattern and in a built
/// term alike, at a group's position and as a collection's instance.
#[test]
fn a_group_fragment_without_a_rest_names_every_child() {
    let missing = Outcome::Refuse("record-missing-children");
    let group = [group_g()];
    let list = [Layer::Instances(Order::List), group_g()];
    let set = [Layer::Instances(Order::Set), group_g()];
    let probe = |side, stack, text, other| Probe {
        form: Form::Cells,
        side,
        path: &[],
        stack,
        text,
        other,
        written: false,
        bound: &["x", "y", "z"],
        records: &[],
        elsewhere: false,
    };
    let (subject, result) = (Side::Subject, Side::Result);
    let exact = "k::fragment![crate::G { a: x }]";
    probes_agree(&[
        (probe(subject, &group, exact, None), missing),
        (probe(result, &group, exact, None), missing),
        (
            probe(
                result,
                &group,
                exact,
                Some("k::fragment![crate::G { a: y, .. }]"),
            ),
            missing,
        ),
        (
            probe(
                subject,
                &list,
                "[k::fragment![crate::G { a: x }], ..]",
                None,
            ),
            missing,
        ),
        (
            probe(
                subject,
                &set,
                "{ k::fragment![crate::G { a: x }], .. }",
                None,
            ),
            missing,
        ),
        (
            probe(subject, &group, "k::fragment![crate::G { a: x, .. }]", None),
            Outcome::After,
        ),
        (
            probe(
                result,
                &group,
                "k::fragment![crate::G { a: x, b: y }]",
                None,
            ),
            Outcome::After,
        ),
        (
            probe(
                subject,
                &list,
                "[k::fragment![crate::G { a: x, b: y }], ..]",
                None,
            ),
            Outcome::After,
        ),
    ]);
}

/// D-5 (P5): an initializer's value for a `*` cell is one instance's template at every depth, so a
/// collection child of a template record, or of a plain group's record, takes its own instance's
/// template; brackets there are no instance list.
#[test]
fn an_initializers_collection_child_takes_its_instance_template() {
    let probe = |stack, text| Probe {
        form: Form::Init,
        side: Side::Initializer,
        path: &[],
        stack,
        text,
        other: None,
        written: false,
        bound: &["pgm"],
        records: &[],
        elsewhere: false,
    };
    let (map, group) = (
        nested_collection_stack("* Map of Q"),
        nested_collection_stack("group P"),
    );
    probes_agree(&[
        (probe(&map, "Q { id: 0, js: J { p: 0 } }"), Outcome::After),
        (probe(&group, "P { js: J { p: 0 } }"), Outcome::After),
        (
            probe(&map, "Q { id: 0, js: [J { p: 0 }] }"),
            Outcome::Refuse("bracket-reading"),
        ),
        (
            probe(&group, "P { js: Some(J { p: 0 }) }"),
            Outcome::Refuse("presence-on-plain-cell"),
        ),
    ]);
}

/// D-1's thread collection, `* List of T { k: KSequence, n: Int }`, and group
/// `H { l: List, b: Int }`, each with a child whose content has a root (P6).
fn d1_stacks() -> (Vec<Layer>, Layer) {
    let int = Layer::Leaf(Notation::Plain);
    let threads = vec![
        Layer::Instances(Order::List),
        Layer::Group(Group {
            name: "T".to_owned(),
            children: vec![
                ("k".to_owned(), vec![Layer::Computation]),
                ("n".to_owned(), vec![int.clone()]),
            ],
        }),
    ];
    let h = Layer::Group(Group {
        name: "H".to_owned(),
        children: vec![
            ("l".to_owned(), vec![Layer::Leaf(Notation::List)]),
            ("b".to_owned(), vec![int]),
        ],
    });
    (threads, h)
}

/// A result probe of D-1 and D-2, binding `x`, `y`, `z` and `me`.
const fn child_probe<'p>(
    form: Form,
    stack: &'p [Layer],
    text: &'p str,
    other: Option<&'p str>,
) -> Probe<'p> {
    Probe {
        form,
        side: Side::Result,
        path: &[],
        stack,
        text,
        other,
        written: false,
        bound: &["x", "y", "z", "me"],
        records: &[],
        elsewhere: true,
    }
}

/// D-1 (S5.0g): a group or instance record's children are entries of their own cells (P1), and
/// rests pair at each content root (P6). In an instance update a child's other side is the same
/// child of the subject instance the update labels (R10), an unmatched child where that instance
/// does not name it (Q1, Q3); a created instance's child has none (R2). The first two are the
/// S5.0g stop's instance probes.
#[test]
fn an_instance_records_children_pair_their_rests_at_their_own_content_roots() {
    let (threads, _) = d1_stacks();
    let rm = Outcome::Refuse("rest-mismatch");
    let me = Some("[me @ T { k: [y, ..], .. }, ..]");
    let me_cells = Some("[me @ k::fragment![crate::T { k: [y, ..], .. }], ..]");
    let probe = |form, text, other| child_probe(form, &threads, text, other);
    probes_agree(&[
        (probe(Form::Readable, "[T { k: [x], ..me }, ..]", me), rm),
        (
            probe(Form::Readable, "[T { k: [x, ..], n: 1 }, ..]", Some("[..]")),
            rm,
        ),
        // The update that keeps the rest, and a created instance's exact computation.
        (
            probe(Form::Readable, "[T { k: [x, ..], ..me }, ..]", me),
            Outcome::After,
        ),
        (
            probe(Form::Readable, "[T { k: [x], n: 1 }, ..]", Some("[..]")),
            Outcome::After,
        ),
        // Their `cells!` forms.
        (
            probe(
                Form::Cells,
                "[k::fragment![crate::T { k: [x], ..me }], ..]",
                me_cells,
            ),
            rm,
        ),
        (
            probe(
                Form::Cells,
                "[k::fragment![crate::T { k: [x, ..], ..me }], ..]",
                me_cells,
            ),
            Outcome::After,
        ),
        // A child the labelled instance does not name is overwritten (Q1): a readable rule does
        // not drop a continuation it did not match (Q3); `cells!` may.
        (
            probe(
                Form::Readable,
                "[T { k: [x], ..me }, ..]",
                Some("[me @ T { n: y, .. }, ..]"),
            ),
            Outcome::Refuse("continuation-in-readable"),
        ),
        (
            probe(
                Form::Cells,
                "[k::fragment![crate::T { k: [x], ..me }], ..]",
                Some("[me @ k::fragment![crate::T { n: y, .. }], ..]"),
            ),
            Outcome::After,
        ),
    ]);
}

/// D-1 (S5.0g), for groups: a matched group's child pairs with the subject record's same child,
/// one the subject does not name is overwritten (Q1), and an overwritten group's child is
/// unmatched; a `?` cell created over a subject `None` creates its group's children (R2). The
/// first two are the S5.0g stop's group probes.
#[test]
fn a_group_records_children_pair_their_rests_at_their_own_content_roots() {
    let (_, h) = d1_stacks();
    let group = [h.clone()];
    let optional = [Layer::Optional, h];
    let rm = Outcome::Refuse("rest-mismatch");
    let subject = Some("H { l: [y, ..], .. }");
    probes_agree(&[
        (
            child_probe(Form::Readable, &group, "H { l: [x], b: 1 }", subject),
            rm,
        ),
        (
            child_probe(Form::Readable, &group, "H { l: [x, ..], b: 1 }", None),
            rm,
        ),
        (
            child_probe(Form::Readable, &group, "H { l: [x, ..], b: 1 }", subject),
            Outcome::After,
        ),
        (
            child_probe(
                Form::Readable,
                &group,
                "H { l: [x], b: 1 }",
                Some("H { b: y, .. }"),
            ),
            Outcome::After,
        ),
        (
            child_probe(
                Form::Cells,
                &group,
                "k::fragment![crate::H { l: [x], b: 1 }]",
                Some("k::fragment![crate::H { l: [y, ..], .. }]"),
            ),
            rm,
        ),
        (
            child_probe(
                Form::Readable,
                &optional,
                "Some(H { l: [x, ..], b: 1 })",
                Some("None"),
            ),
            rm,
        ),
        (
            child_probe(
                Form::Readable,
                &optional,
                "Some(H { l: [x], b: 1 })",
                Some("Some(H { l: [y, ..], .. })"),
            ),
            rm,
        ),
    ]);
}

/// R1 (S5.0g review): an overwritten group's children are unmatched, not created (Q1): a
/// readable rule does not drop the computation child's continuation it never matched (Q3), the
/// `?` child's presence is unknown (P5), and the group child exists, so a bare `..` on it is
/// Rust's default fields (P6).
#[test]
fn an_overwritten_records_children_are_unmatched_not_created() {
    let int = || vec![Layer::Leaf(Notation::Plain)];
    let group = |name: &str, children: Vec<(&str, Vec<Layer>)>| {
        [Layer::Group(Group {
            name: name.to_owned(),
            children: children
                .into_iter()
                .map(|(child, stack)| (child.to_owned(), stack))
                .collect(),
        })]
    };
    let c = group("C", vec![("c", vec![Layer::Computation]), ("n", int())]);
    let o = group(
        "O",
        vec![
            ("o", vec![Layer::Optional, Layer::Leaf(Notation::Plain)]),
            ("n", int()),
        ],
    );
    let w = group("W", vec![("g", vec![group_g()]), ("n", int())]);
    let uor = Outcome::Refuse("unmatched-optional-result");
    let open = Outcome::Refuse("open-record-outside-pattern");
    probes_agree(&[
        (
            child_probe(Form::Readable, &c, "C { c: [x], n: 0 }", None),
            Outcome::Refuse("continuation-in-readable"),
        ),
        (
            child_probe(Form::Readable, &o, "O { o: Some(1), n: 0 }", None),
            uor,
        ),
        (
            child_probe(Form::Readable, &o, "O { o: None, n: 0 }", None),
            uor,
        ),
        (
            child_probe(
                Form::Cells,
                &o,
                "k::fragment![crate::O { o: Some(1), n: 0 }]",
                None,
            ),
            uor,
        ),
        (
            child_probe(Form::Readable, &w, "W { g: G { a: x, .. }, n: 0 }", None),
            open,
        ),
        (
            child_probe(
                Form::Cells,
                &w,
                "k::fragment![crate::W { g: G { a: x, .. }, n: 0 }]",
                None,
            ),
            open,
        ),
        // A matched record that does not name `g`: `g` exists and is overwritten.
        (
            child_probe(
                Form::Readable,
                &w,
                "W { g: G { a: x, .. }, n: 0 }",
                Some("W { n: y, .. }"),
            ),
            open,
        ),
        (
            child_probe(Form::Readable, &w, "W { g: G { a: x, b: y }, n: 0 }", None),
            Outcome::After,
        ),
    ]);
}

/// S5.0g pattern review P-R3 (P0): an update `T { .., ..me }` whose label names no instance the
/// subject matches is no in-place rewrite, since K rewrites in place only an instance its left
/// side matched. Where the sentence binds `me` elsewhere (a value saved in another cell), the
/// record is a new term with `me`'s fields: a created instance, whose children are created
/// (`k: [x]` exact, `k: [x, ..]` a `..` with nothing to keep, a `?` child written over no
/// cell). Where it binds `me` nowhere, the update has no base: `record-update-base`. An update
/// whose label the subject shows is the in-place one (R10).
#[test]
fn an_update_whose_label_the_subject_does_not_show_is_created_or_has_no_base() {
    let (threads, _) = d1_stacks();
    let keyed = [
        Layer::Instances(Order::Map),
        sweep_group(
            "A",
            &[
                ("id", Layer::Leaf(Notation::Plain)),
                ("l", Layer::Leaf(Notation::List)),
            ],
        ),
    ];
    let elsewhere = |form, stack, text| child_probe(form, stack, text, Some("[..]"));
    let nowhere = |form, stack, text, other| Probe {
        bound: &["x", "y", "z"],
        records: &[],
        elsewhere: false,
        ..child_probe(form, stack, text, Some(other))
    };
    let rm = Outcome::Refuse("rest-mismatch");
    let base = Outcome::Refuse("record-update-base");
    probes_agree(&[
        (
            elsewhere(Form::Readable, &threads, "[T { k: [x], ..me }, ..]"),
            Outcome::After,
        ),
        (
            elsewhere(Form::Readable, &threads, "[T { k: [x, ..], ..me }, ..]"),
            rm,
        ),
        (
            elsewhere(
                Form::Cells,
                &threads,
                "[k::fragment![crate::T { k: [x, ..], ..me }], ..]",
            ),
            rm,
        ),
        (
            child_probe(
                Form::Readable,
                &keyed,
                "{ A { id: 5, ..me }, .. }",
                Some("{ .. }"),
            ),
            Outcome::After,
        ),
        (
            nowhere(Form::Readable, &threads, "[T { k: [x], ..me }, ..]", "[..]"),
            base,
        ),
        (
            nowhere(
                Form::Cells,
                &threads,
                "[k::fragment![crate::T { k: [x], ..me }], ..]",
                "[..]",
            ),
            base,
        ),
        (
            nowhere(
                Form::Readable,
                &keyed,
                "{ A { l: [x], ..me }, .. }",
                "{ .. }",
            ),
            base,
        ),
        // The subject shows `me`: the in-place update, paired with the matched instance.
        (
            nowhere(
                Form::Readable,
                &threads,
                "[T { k: [x, ..], ..me }, ..]",
                "[me @ T { k: [y, ..], .. }, ..]",
            ),
            Outcome::After,
        ),
    ]);
}

/// D-2 (S5.0g), narrowed by ruling 2 (P0): an update (`..me`) changes the instance in place, and
/// a Map collection's instance is keyed by its first child, its identity (design §2.3, §7). An
/// update that writes the key as the binder its subject matched it with means the same instance,
/// admitted; any other key value (a literal, another name, a computed value), or a key the
/// labelled instance does not name, is `map-collection-key`. An update's unnamed non-key child
/// is Q1's overwrite; a Set collection keys none.
/// R9 (S5.0g review, P0): an update writing a Map collection's key as the same literal its
/// subject matched it with writes provably the matched key, so the instance's identity is
/// unchanged; another literal, or the literal another instance matched, is another key.
#[test]
fn an_update_writing_the_literal_its_subject_matched_keeps_the_key() {
    let map = vec![
        Layer::Instances(Order::Map),
        Layer::Group(Group {
            name: "A".to_owned(),
            children: vec![("id".to_owned(), int()), ("bal".to_owned(), int())],
        }),
    ];
    let refused = Outcome::Refuse("map-collection-key");
    probes_agree(&[
        (
            child_probe(
                Form::Readable,
                &map,
                "{ A { id: 5, ..me }, .. }",
                Some("{ me @ A { id: 5, .. }, .. }"),
            ),
            Outcome::After,
        ),
        (
            child_probe(
                Form::Readable,
                &map,
                "{ A { id: 5, ..me }, .. }",
                Some("{ me @ A { id: k @ 5, .. }, .. }"),
            ),
            Outcome::After,
        ),
        (
            child_probe(
                Form::Cells,
                &map,
                "{ k::fragment![crate::A { id: 5, ..me }], .. }",
                Some("{ me @ k::fragment![crate::A { id: 5, .. }], .. }"),
            ),
            Outcome::After,
        ),
        (
            child_probe(
                Form::Readable,
                &map,
                "{ A { id: 6, ..me }, .. }",
                Some("{ me @ A { id: 5, .. }, .. }"),
            ),
            refused,
        ),
        (
            child_probe(
                Form::Readable,
                &map,
                "{ A { id: 5, ..me }, .. }",
                Some("{ me @ A { id: z, .. }, other @ A { id: 5, .. }, .. }"),
            ),
            refused,
        ),
    ]);
}

#[test]
fn an_update_of_a_map_collections_instance_that_writes_its_key_is_refused() {
    let account = |order| {
        vec![
            Layer::Instances(order),
            Layer::Group(Group {
                name: "A".to_owned(),
                children: vec![("id".to_owned(), int()), ("bal".to_owned(), int())],
            }),
        ]
    };
    let (map, set) = (account(Order::Map), account(Order::Set));
    let refused = Outcome::Refuse("map-collection-key");
    let me = Some("{ me @ A { id: z, .. }, .. }");
    probes_agree(&[
        (
            child_probe(Form::Readable, &map, "{ A { id: 5, ..me }, .. }", me),
            refused,
        ),
        (
            child_probe(Form::Claim, &map, "{ A { id: z, ..me }, .. }", me),
            Outcome::After,
        ),
        (
            child_probe(
                Form::Cells,
                &map,
                "{ k::fragment![crate::A { id: z, ..me }], .. }",
                Some("{ me @ k::fragment![crate::A { id: z, .. }], .. }"),
            ),
            Outcome::After,
        ),
        (
            child_probe(Form::Readable, &map, "{ A { id: y, ..me }, .. }", me),
            refused,
        ),
        (
            child_probe(
                Form::Readable,
                &map,
                "{ A { id: k::builtin::int::add(z, 1), ..me }, .. }",
                me,
            ),
            refused,
        ),
        (
            child_probe(
                Form::Readable,
                &map,
                "{ A { id: z, ..me }, .. }",
                Some("{ me @ A { id: y, .. }, other @ A { id: z, .. }, .. }"),
            ),
            refused,
        ),
        (
            child_probe(
                Form::Readable,
                &map,
                "{ A { id: 5, ..me }, .. }",
                Some("{ me @ A { bal: y, .. }, .. }"),
            ),
            refused,
        ),
        (
            child_probe(
                Form::Cells,
                &map,
                "{ k::fragment![crate::A { id: 5, ..me }], .. }",
                Some("{ me @ k::fragment![crate::A { id: z, .. }], .. }"),
            ),
            refused,
        ),
        (
            child_probe(Form::Readable, &map, "{ A { bal: 5, ..me }, .. }", me),
            Outcome::After,
        ),
        (
            child_probe(
                Form::Readable,
                &map,
                "{ A { id: 5, bal: 0 }, .. }",
                Some("{ .. }"),
            ),
            Outcome::After,
        ),
        (
            child_probe(
                Form::Cells,
                &map,
                "{ k::fragment![crate::A { id: 5, bal: 0 }], .. }",
                Some("{ .. }"),
            ),
            Outcome::After,
        ),
        (
            child_probe(Form::Readable, &set, "{ A { id: 5, ..me }, .. }", me),
            Outcome::After,
        ),
    ]);
}

/// `group-and-descendant` (design §2.3, an unchanged class, extended to instances): P1 makes an
/// entry denote the content of one cell, so a rule or claim whose entries name a cell and a cell
/// below it, on either side, names that cell twice. The compiler refuses it today with
/// `krs::analysis::group-and-descendant` (`semantic/rules.rs` `check_group_descendants`, the
/// `configuration-cells` fixture `group-and-leaf`); the oracle answers it at step 5, first.
/// R6 (S5.0g review): an initializer's program in a computation cell other than `k` while a
/// `k` computation exists is `main-cell-not-k` when no `k` cell holds the program, whatever the
/// order of the entries; the program in `k` and in a second computation (S5-M1's rows, P0, P1)
/// is no such refusal in either order.
#[test]
fn the_main_cell_rule_reads_the_entries_as_a_set() {
    use class_matrix::cells_oracle::build::seq;
    use class_matrix::cells_oracle::{Entry, Sentence};
    let kmac = |items| Spelling::KMacro(seq(items, None));
    let entry = |cell: &str, spelling| Entry {
        cell: cell.to_owned(),
        side: Side::Initializer,
        path: Vec::new(),
        stack: vec![Layer::Computation],
        spelling,
    };
    let pgm = || kmac(vec![Spelling::ConfigVar("pgm".to_owned())]);
    let empty = || kmac(Vec::new());
    let init = |entries| Template {
        sentence: Sentence::Initializer,
        entries,
        guard: false,
        variables: vec![("pgm".to_owned(), true)],
    };
    let admitted = Outcome::Admit { lint: None };
    let judged = |template: &Template, own: &Entry| rule_outcome(template, own, admitted);
    let (k_pgm, prog_pgm) = (entry("k", pgm()), entry("prog", pgm()));
    let (k_empty, prog_empty) = (entry("k", empty()), entry("prog", empty()));
    // The program in `prog` alone, `k` empty: refused, with either entry first.
    assert_eq!(
        judged(&init(vec![k_empty.clone()]), &prog_pgm),
        Some("main-cell-not-k")
    );
    assert_eq!(
        judged(&init(vec![prog_pgm.clone()]), &k_empty),
        Some("main-cell-not-k")
    );
    // The program in `k` and in `prog`: `k` holds it, in either order.
    assert_eq!(judged(&init(vec![k_pgm.clone()]), &prog_pgm), None);
    assert_eq!(judged(&init(vec![prog_pgm.clone()]), &k_pgm), None);
    // The program in `k` alone.
    assert_eq!(judged(&init(vec![prog_empty.clone()]), &k_pgm), None);
    assert_eq!(judged(&init(vec![k_pgm]), &prog_empty), None);
}

/// S5.0g item 3a fixes, ruling 2 (P5, D2 #8): a value's base `..name` uses the configuration
/// variable `name` exactly as an item `name` would, so an initializer whose only use of a
/// variable is a map's, list's, computation's or instance sequence's base, or a record update's,
/// uses it; a base of another name does not.
#[test]
fn an_initializer_uses_a_configuration_variable_it_writes_as_a_base() {
    use class_matrix::cells_oracle::build::{lit, seq};
    use class_matrix::cells_oracle::{Entry, Sentence};
    let entry = |cell: &str, stack: Vec<Layer>, spelling| Entry {
        cell: cell.to_owned(),
        side: Side::Initializer,
        path: Vec::new(),
        stack,
        spelling,
    };
    let init = |variable: &str| Template {
        sentence: Sentence::Initializer,
        entries: Vec::new(),
        guard: false,
        variables: vec![(variable.to_owned(), false)],
    };
    let splice = |name: &str| Some((Rest::Splice(name.to_owned()), RestAt::Back));
    let group = Layer::Group(Group {
        name: "G".to_owned(),
        children: vec![("a".to_owned(), int()), ("b".to_owned(), int())],
    });
    let bases = |name: &str| {
        vec![
            entry(
                "env",
                vec![Layer::Leaf(Notation::Map)],
                Spelling::MapLit(Entries {
                    entries: vec![(lit(), lit())],
                    rest: Some(Rest::Splice(name.to_owned())),
                }),
            ),
            entry(
                "stack",
                vec![Layer::Leaf(Notation::List)],
                Spelling::Brackets(seq(vec![lit()], splice(name))),
            ),
            entry(
                "k",
                vec![Layer::Computation],
                Spelling::KMacro(seq(vec![lit()], splice(name))),
            ),
            entry(
                "jobs",
                vec![Layer::Instances(Order::List), group.clone()],
                Spelling::InstList(seq(Vec::new(), splice(name))),
            ),
            entry(
                "frame",
                vec![group.clone()],
                Spelling::Record(Record {
                    head: "G".to_owned(),
                    fields: vec![("a".to_owned(), lit())],
                    rest: RecordRest::Update(name.to_owned()),
                }),
            ),
        ]
    };
    let admitted = Outcome::Admit { lint: None };
    for (used, unused) in bases("base").into_iter().zip(bases("other")) {
        assert_eq!(
            rule_outcome(&init("base"), &used, admitted),
            None,
            "{used:?}"
        );
        assert_eq!(
            rule_outcome(&init("base"), &unused, admitted),
            Some("unused-configuration-variable"),
            "{unused:?}"
        );
    }
}

#[test]
fn a_rule_naming_a_group_and_a_cell_below_it_is_refused_on_the_whole_rule() {
    use class_matrix::cells_oracle::build::{bind, lit, open, seq};
    use class_matrix::cells_oracle::{Entry, Sentence};
    let entry = |cell: &str, side, stack: Vec<Layer>, spelling| Entry {
        cell: cell.to_owned(),
        side,
        path: Vec::new(),
        stack,
        spelling,
    };
    let frame = |children: Vec<(&str, Vec<Layer>)>| {
        Layer::Group(Group {
            name: "Frame".to_owned(),
            children: children
                .into_iter()
                .map(|(name, stack)| (name.to_owned(), stack))
                .collect(),
        })
    };
    let flat = frame(vec![("pc", int()), ("gas", int())]);
    let k = entry(
        "k",
        Side::Subject,
        vec![Layer::Computation],
        Spelling::Brackets(seq(vec![bind("x")], open())),
    );
    let pc = |side| entry("pc", side, int(), bind("p"));
    let whole = |side, stack: &Layer| entry("frame", side, vec![stack.clone()], bind("f"));
    let next = entry(
        "pc",
        Side::Result,
        int(),
        Spelling::Call(vec![bind("p"), lit()]),
    );
    let rule = |sentence, entries| Template {
        sentence,
        entries,
        guard: false,
        variables: Vec::new(),
    };
    let admitted = Outcome::Admit { lint: None };
    let descendant = Some("group-and-descendant");
    // The fixture's `peek`: `frame: f, pc: p` => `pc: p + 1`.
    let peek = rule(
        Sentence::Rule,
        vec![k.clone(), whole(Side::Subject, &flat), next.clone()],
    );
    assert_eq!(
        rule_outcome(&peek, &pc(Side::Subject), admitted),
        descendant
    );
    // The group and the cell below it on the result side only, and in a claim.
    let written = rule(Sentence::Rule, vec![k.clone(), whole(Side::Result, &flat)]);
    assert_eq!(rule_outcome(&written, &next, admitted), descendant);
    let claim = rule(
        Sentence::Claim,
        vec![k.clone(), whole(Side::Subject, &flat)],
    );
    assert_eq!(
        rule_outcome(&claim, &pc(Side::Subject), admitted),
        descendant
    );
    // A cell at any depth below, through a nested group or a collection's instances.
    let nested = frame(vec![(
        "inner",
        vec![Layer::Group(Group {
            name: "Inner".to_owned(),
            children: vec![("pc".to_owned(), int())],
        })],
    )]);
    let deep = rule(
        Sentence::Rule,
        vec![k.clone(), whole(Side::Subject, &nested), next.clone()],
    );
    assert_eq!(
        rule_outcome(&deep, &pc(Side::Subject), admitted),
        descendant
    );
    let jobs = entry(
        "jobs",
        Side::Subject,
        vec![Layer::Instances(Order::List), frame(vec![("pc", int())])],
        Spelling::Brackets(seq(Vec::new(), open())),
    );
    let collection = rule(Sentence::Rule, vec![k.clone(), jobs, next.clone()]);
    assert_eq!(
        rule_outcome(&collection, &pc(Side::Subject), admitted),
        descendant
    );
    // The cell alone, or a group that holds no such cell, is no overlap.
    let alone = rule(Sentence::Rule, vec![k.clone(), next.clone()]);
    assert_eq!(rule_outcome(&alone, &pc(Side::Subject), admitted), None);
    let other = frame(vec![("ret", int())]);
    let apart = rule(Sentence::Rule, vec![k, whole(Side::Subject, &other), next]);
    assert_eq!(rule_outcome(&apart, &pc(Side::Subject), admitted), None);
    // A refused entry has no rule-level row.
    assert_eq!(
        rule_outcome(&peek, &pc(Side::Subject), Outcome::Refuse("cell-wrapper")),
        None
    );
}

/// Key ruling 3 (P5, §7): a Map collection's instance is keyed by its first child, its identity,
/// written at creation and never changed by an update. A created instance that does not write it
/// (a bare `..` takes the template's fields, which state no identity) is `map-collection-key`; a
/// Set or List collection has no key, and an update that leaves the key out keeps it.
#[test]
fn a_created_map_collection_instance_that_does_not_write_its_key_is_refused() {
    let account = |order| {
        vec![
            Layer::Instances(order),
            Layer::Group(Group {
                name: "A".to_owned(),
                children: vec![("id".to_owned(), int()), ("bal".to_owned(), int())],
            }),
        ]
    };
    let (map, set, list) = (
        account(Order::Map),
        account(Order::Set),
        account(Order::List),
    );
    let refused = Outcome::Refuse("map-collection-key");
    let any = Some("{ .. }");
    probes_agree(&[
        (
            child_probe(Form::Readable, &map, "{ A { bal: 0, .. }, .. }", any),
            refused,
        ),
        (
            child_probe(Form::Claim, &map, "{ A { bal: 0, .. }, .. }", any),
            refused,
        ),
        (
            child_probe(
                Form::Cells,
                &map,
                "{ k::fragment![crate::A { bal: 0, .. }], .. }",
                any,
            ),
            refused,
        ),
        (
            child_probe(Form::Readable, &map, "{ A { bal: 0, .. } }", None),
            refused,
        ),
        (
            child_probe(Form::Readable, &map, "{ A { id: 5, .. }, .. }", any),
            Outcome::After,
        ),
        (
            child_probe(Form::Readable, &set, "{ A { bal: 0, .. }, .. }", any),
            Outcome::After,
        ),
        (
            child_probe(
                Form::Readable,
                &list,
                "[A { bal: 0, .. }, ..]",
                Some("[..]"),
            ),
            Outcome::After,
        ),
        (
            child_probe(
                Form::Readable,
                &map,
                "{ A { bal: 0, ..me }, .. }",
                Some("{ me @ A { id: z, .. }, .. }"),
            ),
            Outcome::After,
        ),
    ]);
}

/// Ruling 3 on F2: `name @ P` names what a pattern matched, so a result holds none, at any depth
/// (§2.3 step 1), before the path is judged.
#[test]
fn an_alias_in_a_result_is_refused_at_the_form() {
    let refused = Outcome::Refuse("alias-outside-pattern");
    let int = int();
    let list = [Layer::Leaf(Notation::List)];
    let optional = [Layer::Optional, Layer::Leaf(Notation::Plain)];
    let group = [group_g()];
    let instances = [Layer::Instances(Order::List), group_g()];
    let mut below = result_probe(Form::Readable, &int, "x @ 1", None);
    below.path = &[Layer::Optional];
    probes_agree(&[
        (
            result_probe(Form::Readable, &int, "x @ 1", Some("old")),
            refused,
        ),
        (
            result_probe(Form::Claim, &list, "[x @ 1, ..]", Some("[y, ..]")),
            refused,
        ),
        (
            result_probe(Form::Readable, &optional, "Some(x @ 1)", Some("Some(old)")),
            refused,
        ),
        (
            result_probe(Form::Readable, &group, "G { a: x @ 1, b: 0 }", None),
            refused,
        ),
        (
            result_probe(
                Form::Cells,
                &int,
                "k::configuration::Cell(x @ 1)",
                Some("k::configuration::Cell(old)"),
            ),
            refused,
        ),
        (
            result_probe(
                Form::Cells,
                &instances,
                "[f @ k::fragment![crate::G { a: x, b: 0 }], ..]",
                Some("[k::fragment![crate::G { a: y, .. }], ..]"),
            ),
            refused,
        ),
        (below, refused),
    ]);
}

/// Ruling 4 on F2: an initializer is a result with no subject (P5), so nothing in it is a
/// pattern: a named rest and `name @ P` are refused at the form, and `..base` updates.
#[test]
fn an_alias_or_a_named_rest_in_an_initializer_is_refused_at_the_form() {
    let refused = Outcome::Refuse("alias-outside-pattern");
    let probe = |stack, text| Probe {
        form: Form::Init,
        side: Side::Initializer,
        path: &[],
        stack,
        text,
        other: None,
        written: false,
        bound: &["pgm"],
        records: &[],
        elsewhere: false,
    };
    let list = [Layer::Leaf(Notation::List)];
    let map = [Layer::Leaf(Notation::Map)];
    let computation = [Layer::Computation];
    let int = int();
    probes_agree(&[
        (probe(&list, "[0, r @ ..]"), refused),
        (probe(&computation, "k::k![Cmd::Go(), r @ ..]"), refused),
        (probe(&map, "k::map![0 -> 1, r @ ..]"), refused),
        (probe(&int, "x @ 0"), refused),
        (probe(&list, "[0, ..base]"), Outcome::After),
    ]);
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
        "#   `?` ancestor; `*` below a `*` ancestor (S1 (b), the rule forms'; an initializer, a struct\n",
        "#   literal of the configuration, names no cell by a path, so its rows are `-` only). The\n",
        "#   stack is the cell's own.\n",
        "# Bound names: in a result, x, y, z, old (bound by the subject); in a subject, none; in an\n",
        "#   initializer, the configuration variable pgm. `G` is the group (children a, b: Int) of\n",
        "#   the group stacks and the collections' instances.\n",
        "# claim's steps 1-3 are readable's; both are printed so a change to either shows.\n",
        "#\n",
        "# A cell: ok (admitted), ok+LINT (admitted, owing the lint), sort (admitted, a value's sort\n",
        "#   left to the lattice, step 4), or the refusal's class by its short name below.\n",
        "#   `A|product:B` marks where the product (krs_syntax::cell_entries) answers B: each such\n",
        "#   cell is a [cell-exception] departure (E3, a C-lim) or a disagreement to explain.\n",
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
    for (table, form, spellings) in sweep_main_tables() {
        let _ = write!(out, "#\n## {table}\nside\tpath\tstack\tother");
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
            for (path_name, path) in sweep_paths(form, &paths) {
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
                            records: &[],
                            elsewhere: false,
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
    children_sweep(&mut out);
    out
}

/// The fragment-child sweep (the S5.0g fixes review's F-1): a group record's Map, List or
/// computation child at its own content root, in readable, claim and `cells!`, so that a
/// `cells!` fragment's child and the readable record's child it abbreviates (P7) show side by
/// side.
fn fragment_child_sweep(out: &mut String) {
    out.push_str(concat!(
        "#\n",
        "## children, fragment child: a group record's Map, List or computation child, in a subject and a result\n",
        "# Each row is a side, the group, the subject's entry of the cell (`-`: none, or a subject's\n",
        "#   own row) and the entry. Groups: M (m: Map, n: Int), H (l: List, b: Int), C (c: a\n",
        "#   computation, n: Int). Bound names: in a result x, y, z; in a subject none. The `cells!`\n",
        "#   rows write each record as its fragment, whose child is the child's entry, unwrapped (P1):\n",
        "#   the field's direct value is the child's content root (P6).\n",
        "form\tside\tstack\tother\tentry\toutcome\n",
    ));
    for form in [Form::Readable, Form::Claim, Form::Cells] {
        let spelled = usize::from(form == Form::Cells);
        for (side_name, stack_name, other, entry) in &FRAGMENT_CHILD_SWEEP {
            let stack = children_stack(stack_name);
            let other = (other[spelled] != "-").then_some(other[spelled]);
            let (side, bound): (Side, &[&str]) = if *side_name == "subject" {
                (Side::Subject, &[])
            } else {
                (Side::Result, &["x", "y", "z"])
            };
            let probe = Probe {
                form,
                side,
                path: &[],
                stack: &stack,
                text: entry[spelled],
                other,
                written: false,
                bound,
                records: &[],
                elsewhere: false,
            };
            let (oracle, product) = (probe.oracle(), probe.product());
            let _ = write!(
                out,
                "{}\t{side_name}\t{stack_name}\t{}\t{}\t{}",
                form_name(form),
                other.unwrap_or("-"),
                entry[spelled],
                sweep_name(oracle)
            );
            if product != oracle {
                let _ = write!(out, "|product:{}", sweep_name(product));
            }
            out.push('\n');
        }
    }
}

/// The sweep of a result's children (P1: a group or instance record's children are entries of
/// their own cells): each child's content root against its own other side (P6, R10), and a
/// Map collection's key written in an instance update (§7).
fn children_sweep(out: &mut String) {
    out.push_str(concat!(
        "#\n",
        "## children: a result's group and instance records, each child at its own content root\n",
        "# Each row is a result over its cell; `other` is the subject's entry of the cell (`-`: the\n",
        "#   subject does not match it). Bound names: x, y, z, me. `me` is bound: an update `..me`\n",
        "#   whose subject shows no instance labelled `me` reads a value the sentence matches\n",
        "#   elsewhere, which creates an instance (P-R3); the next table is the reading where\n",
        "#   nothing binds `me`. Groups: H (l: List, b: Int), T (k: a computation, n: Int), A (id:\n",
        "#   Int, l: List; a Map collection is keyed by its first child, id), C (c: a computation,\n",
        "#   n: Int), O (o: ? Int, n: Int), W (g: G, n: Int), G (a, b: Int).\n",
        "#   The `cells!` rows write each record as its fragment.\n",
        "form\tstack\tother\tresult\toutcome\n",
    ));
    children_rows(out, &CHILDREN_SWEEP, &["x", "y", "z", "me"]);
    out.push_str(concat!(
        "#\n",
        "## children, base matched nowhere: an update whose label nothing in the sentence binds\n",
        "# As the children table, with the bound names x, y, z: no subject instance is labelled `me`\n",
        "#   and nothing else binds it (P-R3).\n",
        "form\tstack\tother\tresult\toutcome\n",
    ));
    children_rows(out, &CHILDREN_UNBASED_SWEEP, &["x", "y", "z"]);
    fragment_child_sweep(out);
    initializer_children_sweep(out);
}

/// The children sweep's rows of `rows`, in readable, claim and `cells!`, with the names `bound`.
fn children_rows(out: &mut String, rows: &[(&str, [&str; 2], [&str; 2])], bound: &[&str]) {
    for form in [Form::Readable, Form::Claim, Form::Cells] {
        let spelled = usize::from(form == Form::Cells);
        for (stack_name, other, result) in rows {
            let stack = children_stack(stack_name);
            let other = (other[spelled] != "-").then_some(other[spelled]);
            let probe = Probe {
                form,
                side: Side::Result,
                path: &[],
                stack: &stack,
                text: result[spelled],
                other,
                written: false,
                bound,
                records: &[],
                elsewhere: true,
            };
            let (oracle, product) = (probe.oracle(), probe.product());
            let _ = write!(
                out,
                "{}\t{stack_name}\t{}\t{}\t{}",
                form_name(form),
                other.unwrap_or("-"),
                result[spelled],
                sweep_name(oracle)
            );
            if product != oracle {
                let _ = write!(out, "|product:{}", sweep_name(product));
            }
            out.push('\n');
        }
    }
}

fn initializer_children_sweep(out: &mut String) {
    out.push_str(concat!(
        "#\n",
        "## children, init: a template record with a collection or a `?` child (P5 at every depth)\n",
        "# Groups: Q (id: Int, js: * List of J), P (js: * List of J), J (p: Int), O (o: ? Int, n:\n",
        "#   Int), A (id: Int, l: List; a Map collection is keyed by its first child, id). Bound: pgm.\n",
        "form\tstack\tother\tvalue\toutcome\n",
    ));
    for (stack_name, text) in INITIALIZER_CHILDREN_SWEEP {
        let stack = nested_collection_stack(stack_name);
        let probe = Probe {
            form: Form::Init,
            side: Side::Initializer,
            path: &[],
            stack: &stack,
            text,
            other: None,
            written: false,
            bound: &["pgm"],
            records: &[],
            elsewhere: false,
        };
        let (oracle, product) = (probe.oracle(), probe.product());
        let _ = write!(out, "init\t{stack_name}\t-\t{text}\t{}", sweep_name(oracle));
        if product != oracle {
            let _ = write!(out, "|product:{}", sweep_name(product));
        }
        out.push('\n');
    }
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

/// The forms a [`Scope`] names.
const EVERY_FORM: &[&str] = &["readable", "claim", "cells", "init"];
const RULE_FORMS: &[&str] = &["readable", "claim", "cells"];
const READABLE_FORMS: &[&str] = &["readable", "claim"];
const CELLS_FORM: &[&str] = &["cells"];
const INIT_FORM: &[&str] = &["init"];

/// Where a registry ID can decide a cell (the S5.0g fixes review's F-4, ruled): the forms its
/// statement is of, and the stacks, by a word of the stack's sweep name (`?`, `*`, `computation`,
/// `group`, `* Map`, ..), none for every stack. Coarse by intent: a line that cites an ID for a
/// pattern none of whose members it reaches cites a ruling that does not cover the cell.
#[derive(Clone, Copy)]
struct Scope {
    forms: &'static [&'static str],
    stacks: &'static [&'static str],
}

impl Scope {
    fn holds(&self, form: &str, stack: &str) -> bool {
        self.forms.contains(&form)
            && (self.stacks.is_empty() || self.stacks.iter().any(|word| stack.contains(word)))
    }

    fn shown(&self) -> String {
        let forms = if self.forms == EVERY_FORM {
            "every form".to_owned()
        } else {
            self.forms.join(", ")
        };
        if self.stacks.is_empty() {
            format!("{forms}; any stack")
        } else {
            format!("{forms}; stacks with {}", self.stacks.join(" or "))
        }
    }
}

/// The citation registry of the principle lines (S5.0g pattern review P-R11): every line cites
/// its principles and rulings by these IDs, each with a one-line statement, its source and its
/// [`Scope`].
const CITATIONS: [(&str, &str, &str, Scope); 50] = [
    (
        "P0",
        "an entry means the K configuration it lowers to; a spelling Rust reads otherwise is refused",
        "S5-principles.md §1 P0",
        Scope {
            forms: EVERY_FORM,
            stacks: &[],
        },
    ),
    (
        "P1",
        "an entry denotes the content of one cell at any depth; the declaration fixes its stack: ?, *, then a computation, a leaf or a group",
        "S5-principles.md §1 P1",
        Scope {
            forms: EVERY_FORM,
            stacks: &[],
        },
    ),
    (
        "P2",
        "each layer has one mark per form, read lexically; a cons list's brackets end in their rest",
        "S5-principles.md §1 P2",
        Scope {
            forms: EVERY_FORM,
            stacks: &[],
        },
    ),
    (
        "P3",
        "one judgement in every form, the entry's head against the whole stack: (a), (b), (c); a missing outer layer is named only where the inside passes form and kind",
        "S5-principles.md §1 P3",
        Scope {
            forms: EVERY_FORM,
            stacks: &[],
        },
    ),
    (
        "P3a",
        "the outermost layer's mark admits the entry, and its inside is judged against the next layer",
        "S5-principles.md §1 P3 (a)",
        Scope {
            forms: EVERY_FORM,
            stacks: &[],
        },
    ),
    (
        "P3b",
        "a mark of a layer the cell has nowhere gives that mark's class",
        "S5-principles.md §1 P3 (b)",
        Scope {
            forms: EVERY_FORM,
            stacks: &[],
        },
    ),
    (
        "P3c",
        "a deeper layer's mark, or a value where the outermost layer has a mark, gives the missing outer layer's class",
        "S5-principles.md §1 P3 (c)",
        Scope {
            forms: EVERY_FORM,
            stacks: &[],
        },
    ),
    (
        "P4",
        "form, then kind (P3), then pairing, then sorts (the lattice), each answered by the first layer that can know it",
        "S5-principles.md §1 P4",
        Scope {
            forms: EVERY_FORM,
            stacks: &[],
        },
    ),
    (
        "P5",
        "a subject constrains and binds; a result is the new content; None tests absence by creation; an initializer is a complete result, a * cell's value one instance's template",
        "S5-principles.md §1 P5",
        Scope {
            forms: EVERY_FORM,
            stacks: &[],
        },
    ),
    (
        "P6",
        "at a content root .. is K's ...: a subject matches the rest, a result keeps it with .. or puts a named one back with ..name; records follow Rust, a bare .. in a result being the template of a created instance or of a ? cell created over None",
        "S5-principles.md §1 P6",
        Scope {
            forms: EVERY_FORM,
            stacks: &[],
        },
    ),
    (
        "P7",
        "readable abbreviates cells!: a readable entry is admitted exactly where the cells! entry it abbreviates is",
        "S5-principles.md §1 P7",
        Scope {
            forms: RULE_FORMS,
            stacks: &[],
        },
    ),
    (
        "E1",
        "the computation is read from its front: .. ends it (computation-back-item, a stated exception of every form, S5.0g:F-6)",
        "S5-principles.md §1, the exceptions",
        Scope {
            forms: EVERY_FORM,
            stacks: &["computation"],
        },
    ),
    (
        "E2",
        "the continuation has no readable value spelling (now Q3)",
        "S5-principles.md §1, the exceptions",
        Scope {
            forms: READABLE_FORMS,
            stacks: &["computation"],
        },
    ),
    (
        "E3",
        "an initializer's k![..] takes no ..pgm (a stated exception)",
        "S5-principles.md §1, the exceptions",
        Scope {
            forms: INIT_FORM,
            stacks: &[],
        },
    ),
    (
        "Q1",
        "a subject entry that constrains nothing is a lint; a result over an unmatched cell is an overwrite",
        "S5-cell-kinds.md rev. 4, decisions in force",
        Scope {
            forms: RULE_FORMS,
            stacks: &[],
        },
    ),
    (
        "Q2",
        "one collection instance is a value only in an ordered collection; an unordered one's instance is chosen by a written record",
        "S5-cell-kinds.md rev. 4, decisions in force",
        Scope {
            forms: RULE_FORMS,
            stacks: &["*"],
        },
    ),
    (
        "Q3",
        "a readable rule never drops or captures the continuation",
        "S5-cell-kinds.md rev. 4, decisions in force",
        Scope {
            forms: READABLE_FORMS,
            stacks: &[],
        },
    ),
    (
        "L1",
        "presence is lexical",
        "S5-cell-kinds.md rev. 4, decisions in force (D3)",
        Scope {
            forms: EVERY_FORM,
            stacks: &[],
        },
    ),
    (
        "L3",
        "initializer brackets on a ? cell with no List layer give bracket-reading (as S5.0g:R7 words it)",
        "S5-cell-kinds.md rev. 4, decisions in force (D3)",
        Scope {
            forms: INIT_FORM,
            stacks: &["?"],
        },
    ),
    (
        "L4",
        "a group record at a configuration position names every child or writes ..",
        "S5-cell-kinds.md rev. 4, decisions in force (D3)",
        Scope {
            forms: EVERY_FORM,
            stacks: &["group", "*"],
        },
    ),
    (
        "design:S1b",
        "an entry naming a cell below a ? or * ancestor is refused for the outermost such ancestor (owp, cwi), the rule forms'",
        "S5-cell-kinds.md rev. 4 §2.3, rows changed in revision 4",
        Scope {
            forms: RULE_FORMS,
            stacks: &[],
        },
    ),
    (
        "design:R3",
        "Some(e) admits e by the underlying kind (the design's ruling 3)",
        "S5-principles.md §2 row 55",
        Scope {
            forms: EVERY_FORM,
            stacks: &["?"],
        },
    ),
    (
        "design:R4",
        "braces on a Set leaf are instances-on-plain-cell (the design's ruling 4)",
        "S5-principles.md §2 row 56",
        Scope {
            forms: READABLE_FORMS,
            stacks: &["leaf Set"],
        },
    ),
    (
        "design:R6",
        "cells! judges the outermost layer first, withdrawn: one order for every form, a cells! wrapper on a ? or * cell is cell-wrapper",
        "S5-principles.md §3 item 1 (A)",
        Scope {
            forms: CELLS_FORM,
            stacks: &["?", "*"],
        },
    ),
    (
        "design:M3",
        "a map read has no result side until M3: readable { k -> v, .. } in a result is map-read-in-result and a cells! result's k::map![.., ..] at a content root (Cell(..)'s argument, a record field's value) the product's arm, both stated limitations",
        "S5-cell-kinds.md rev. 4 §2.3, the C-lims",
        Scope {
            forms: RULE_FORMS,
            stacks: &[],
        },
    ),
    (
        "design:rev4-R10",
        "an instance child's other side is the labelled subject instance's same child (..me); a created instance's child has none",
        "S5-cell-kinds.md rev. 4, revision 4 table, R10",
        Scope {
            forms: RULE_FORMS,
            stacks: &["*"],
        },
    ),
    (
        "S5.0:F1",
        "None over a matched ? cell removes it with its rest, admitted",
        "README.md §12 lane 3, S5.0 rulings",
        Scope {
            forms: RULE_FORMS,
            stacks: &["?"],
        },
    ),
    (
        "S5.0:F2",
        "a named rest in a result is alias-outside-pattern",
        "README.md §12 lane 3, S5.0 rulings",
        Scope {
            forms: RULE_FORMS,
            stacks: &[],
        },
    ),
    (
        "S5.0:F3",
        "with ruling 1: a bare .. on a result group record of a group that exists, matched or overwritten, is open-record-outside-pattern; only a created instance has defaults",
        "README.md §12 lane 3, S5.0 rulings",
        Scope {
            forms: RULE_FORMS,
            stacks: &["group"],
        },
    ),
    (
        "S5.0:R3",
        "any @ in a result is refused (S5.0's ruling 3)",
        "README.md §12 lane 3, S5.0 rulings",
        Scope {
            forms: RULE_FORMS,
            stacks: &[],
        },
    ),
    (
        "S5.0:R4",
        "any @ in an initializer is refused (S5.0's ruling 4)",
        "README.md §12 lane 3, S5.0 rulings",
        Scope {
            forms: INIT_FORM,
            stacks: &[],
        },
    ),
    (
        "S5.0g:D-1",
        "a result pairs its rests at every content root, a group or instance record's children included",
        "README.md §12 lane 3, S5.0g D-1",
        Scope {
            forms: RULE_FORMS,
            stacks: &["group", "*"],
        },
    ),
    (
        "S5.0g:D-2",
        "a Map collection's instance is keyed by its first child; an update writes the key, if at all, as its subject's key binder (with S5.0g's ruling 2), else map-collection-key",
        "README.md §12 lane 3, S5.0g D-2 and \"ruled next\"",
        Scope {
            forms: RULE_FORMS,
            stacks: &["* Map"],
        },
    ),
    (
        "S5.0g:D-3",
        "a fragment of the position's group is read as its record, for pairing and Q1's lint",
        "README.md §12 lane 3, S5.0g D-3",
        Scope {
            forms: RULE_FORMS,
            stacks: &["group", "*"],
        },
    ),
    (
        "S5.0g:D-4",
        "k::fragment![crate::G { a: x }] is record-missing-children, as its readable form",
        "README.md §12 lane 3, S5.0g D-4",
        Scope {
            forms: RULE_FORMS,
            stacks: &["group", "*"],
        },
    ),
    (
        "S5.0g:D-5",
        "a * value is one instance's template at every depth",
        "README.md §12 lane 3, S5.0g D-5",
        Scope {
            forms: INIT_FORM,
            stacks: &[],
        },
    ),
    (
        "S5.0g:key",
        "a created Map instance must write its key",
        "README.md §12 lane 3, S5.0g \"ruled next\"",
        Scope {
            forms: RULE_FORMS,
            stacks: &["* Map"],
        },
    ),
    (
        "S5.0g:R3",
        "the cell's own form, mark and kind refusals come before the path refusal, which replaces only what they admit and pairing",
        "README.md §12 lane 3, S5.0g part (a) review R3",
        Scope {
            forms: RULE_FORMS,
            stacks: &[],
        },
    ),
    (
        "S5.0g:R4",
        "a bare .. on a built record that is not a created instance is open-record-outside-pattern where it leaves a field open; after every field it defaults none",
        "README.md §12 lane 3, S5.0g R4 and the vacuous-rest ruling",
        Scope {
            forms: RULE_FORMS,
            stacks: &[],
        },
    ),
    (
        "S5.0g:R7",
        "L3 holds on a ? cell with no List layer; on a ? List the brackets are its leaf's mark (P3c)",
        "tickets/S5-0g-review-a.md R7",
        Scope {
            forms: EVERY_FORM,
            stacks: &["?"],
        },
    ),
    (
        "S5.0g:R9",
        "an update writing a Map key as the same literal its subject matched keeps it",
        "README.md §12 lane 3, S5.0g part (a) review R9",
        Scope {
            forms: RULE_FORMS,
            stacks: &["* Map"],
        },
    ),
    (
        "S5.0g:P-R1",
        "a cons list's back lowers to no K: cons-list-back-item, a kind refusal inside the leaf's mark",
        "tickets/S5-0g-b-review-fixes.md ruling 1",
        Scope {
            forms: EVERY_FORM,
            stacks: &["Cons"],
        },
    ),
    (
        "S5.0g:P-R2",
        "a cells! result's Cell(k::map![.., ..]) is a content root, judged by kind and pairing; arm only where the literal is no content root, a readable map! everywhere",
        "tickets/S5-0g-b-review-fixes.md ruling 2",
        Scope {
            forms: RULE_FORMS,
            stacks: &[],
        },
    ),
    (
        "S5.0g:P-R3",
        "an update whose label names no subject instance creates an instance where the sentence binds the label elsewhere, and is record-update-base where it binds it nowhere",
        "tickets/S5-0g-b-review-fixes.md ruling 3",
        Scope {
            forms: RULE_FORMS,
            stacks: &["*"],
        },
    ),
    (
        "S5.0g:P-R4",
        "brackets on a Set or Map collection are instance-list-shape, whatever they hold",
        "tickets/S5-0g-b-review-fixes.md ruling 4",
        Scope {
            forms: RULE_FORMS,
            stacks: &["* Set", "* Map"],
        },
    ),
    (
        "S5.0g:P-R5",
        "a missing outer layer is named only where the inside passes form and kind against the deeper layers",
        "tickets/S5-0g-b-review-fixes.md ruling 5",
        Scope {
            forms: EVERY_FORM,
            stacks: &[],
        },
    ),
    (
        "S5.0g:P-R12",
        "under a path, an ancestor's own pairing decides whether a group is created, so F3's refusal is pairing and the path class replaces it",
        "tickets/S5-0g-b-review-fixes.md ruling 7",
        Scope {
            forms: RULE_FORMS,
            stacks: &["group"],
        },
    ),
    (
        "S5.0g:P-R13",
        "a ? cell created over None has a template (the initializer's k::absent!(v)), so its bare .. is admitted",
        "tickets/S5-0g-b-review-fixes.md ruling 7, P6 as amended",
        Scope {
            forms: RULE_FORMS,
            stacks: &["?"],
        },
    ),
    (
        "S5.0g:F-1",
        "a field's direct value in a group record, an instance record or a fragment at a configuration position is its child's entry and content root, as Cell(..)'s argument is: a cells! fragment's k::map![.., ..] child is judged by kind and pairing; deeper, in a term, it stays arm",
        "tickets/S5-0g-b-review-fixes-2.md ruling 1",
        Scope {
            forms: RULE_FORMS,
            stacks: &["group", "*"],
        },
    ),
    (
        "S5.0g:F-6",
        "E1 holds in every form: the computation is read from its front, so cells! KCell(.., x) and KCell(x, .., y) are computation-back-item as readable [.., x] is",
        "tickets/S5-0g-b-review-fixes-2.md ruling 6",
        Scope {
            forms: EVERY_FORM,
            stacks: &["computation"],
        },
    ),
];

/// Where the sweep's row patterns are kept: each distinct pattern of `cells-outcome-sweep.tsv`
/// once, with the rows that share it and the principle that gives it, the reviewed state that
/// [`SWEEP`] points at (`KRS_CELLS_PATTERNS_RECORD=1` rewrites it).
const PATTERNS_FILE: &str = "cells-outcome-patterns.tsv";

/// The line of a pattern that holds its principle.
const PRINCIPLE: &str = "principle";

/// The header line that records which review signed the patterns off; kept on a rewrite.
const REVIEWED: &str = "# reviewed:";

/// One table of the sweep, as printed: its name (up to a `:`), its column header and its rows.
struct SweepTable<'s> {
    name: &'s str,
    header: Vec<&'s str>,
    rows: Vec<Vec<&'s str>>,
}

fn sweep_tables(sweep: &str) -> Vec<SweepTable<'_>> {
    let mut tables: Vec<SweepTable<'_>> = Vec::new();
    for line in sweep.lines() {
        if let Some(title) = line.strip_prefix("## ") {
            tables.push(SweepTable {
                name: title.split(':').next().unwrap_or(title),
                header: Vec::new(),
                rows: Vec::new(),
            });
        } else if !line.starts_with('#')
            && let Some(table) = tables.last_mut()
        {
            let cells = line.split('\t').collect();
            if table.header.is_empty() {
                table.header = cells;
            } else {
                table.rows.push(cells);
            }
        }
    }
    tables
}

/// A row pattern: its answer lines (a label and the answers across the table's columns) and the
/// row groups that have exactly those answers.
struct Pattern {
    lines: Vec<(String, Vec<String>)>,
    members: Vec<Vec<String>>,
}

/// A table of the patterns golden: its name, the prefix of its patterns' IDs, its columns, and
/// its patterns in the order their first member is printed in the sweep.
struct PatternTable {
    name: &'static str,
    prefix: &'static str,
    columns: Vec<String>,
    patterns: Vec<Pattern>,
}

impl PatternTable {
    fn add(&mut self, lines: Vec<(String, Vec<String>)>, member: Vec<String>) {
        match self
            .patterns
            .iter_mut()
            .find(|pattern| pattern.lines == lines)
        {
            Some(pattern) => pattern.members.push(member),
            None => self.patterns.push(Pattern {
                lines,
                members: vec![member],
            }),
        }
    }
}

fn owned(cells: &[&str]) -> Vec<String> {
    cells.iter().map(|cell| (*cell).to_owned()).collect()
}

/// A main table's patterns: a row group is a side and a stack, its pattern the answers of its
/// rows, one per path its table prints (`-`, `?` and `*`; an initializer's `-` only). The forms given share their columns, so they share patterns,
/// and a member names the forms whose row group it is.
fn main_patterns(
    tables: &[SweepTable<'_>],
    name: &'static str,
    prefix: &'static str,
    forms: &[&str],
) -> PatternTable {
    let table = |form: &str| {
        tables
            .iter()
            .find(|table| table.name == form)
            .unwrap_or_else(|| panic!("the sweep has no table {form}"))
    };
    let columns = &table(forms[0]).header[4..];
    let mut out = PatternTable {
        name,
        prefix,
        columns: owned(columns),
        patterns: Vec::new(),
    };
    for form in forms {
        let table = table(form);
        assert_eq!(
            &table.header[4..],
            columns,
            "{form}'s columns are {}'s",
            forms[0]
        );
        let mut groups: Vec<(&str, &str)> = Vec::new();
        let mut paths: Vec<&str> = Vec::new();
        let mut rows = BTreeMap::new();
        for row in &table.rows {
            let (side, path, stack) = (row[0], row[1], row[2]);
            if !groups.contains(&(side, stack)) {
                groups.push((side, stack));
            }
            if !paths.contains(&path) {
                paths.push(path);
            }
            rows.insert((side, path, stack), &row[4..]);
        }
        for (side, stack) in groups {
            let lines = paths
                .iter()
                .map(|path| {
                    let row = rows
                        .get(&(side, *path, stack))
                        .unwrap_or_else(|| panic!("{form}: no row {side} {path} {stack}"));
                    ((*path).to_owned(), owned(row))
                })
                .collect::<Vec<_>>();
            let pattern = out
                .patterns
                .iter()
                .position(|pattern| pattern.lines == lines);
            let member = pattern.and_then(|at| {
                out.patterns[at]
                    .members
                    .iter_mut()
                    .find(|member| member[1] == side && member[2] == stack)
            });
            match member {
                Some(member) => {
                    member[0].push_str(", ");
                    member[0].push_str(form);
                }
                None => out.add(lines, owned(&[form, side, stack])),
            }
        }
    }
    out
}

/// The children sections' patterns: a row group is one result (its answers in readable, claim
/// and `cells!`, whose rows follow in that order) or one initializer value (its one answer).
fn children_patterns(tables: &[SweepTable<'_>]) -> [PatternTable; 4] {
    [
        result_patterns(tables, "children", "ch"),
        result_patterns(tables, "children, base matched nowhere", "cn"),
        result_patterns(tables, "children, fragment child", "cf"),
        initializer_patterns(tables),
    ]
}

/// The patterns of a children table of entries, `name`: one entry's answers in readable, claim
/// and `cells!` (its row's last cell), its member the row's other cells but the form.
fn result_patterns(
    tables: &[SweepTable<'_>],
    name: &'static str,
    prefix: &'static str,
) -> PatternTable {
    let children = tables
        .iter()
        .find(|table| table.name == name)
        .unwrap_or_else(|| panic!("the sweep has a {name} table"));
    let forms = ["readable", "claim", "cells"];
    let per_form = children.rows.len() / forms.len();
    let mut table = PatternTable {
        name,
        prefix,
        columns: owned(&forms),
        patterns: Vec::new(),
    };
    for at in 0..per_form {
        let rows = (0..forms.len())
            .map(|form| &children.rows[form * per_form + at])
            .collect::<Vec<_>>();
        for (row, form) in rows.iter().zip(forms) {
            assert_eq!((row[0], row[1]), (form, rows[0][1]), "children row {at}");
        }
        let last = rows[0].len() - 1;
        let answers = rows.iter().map(|row| row[last].to_owned()).collect();
        table.add(
            vec![("answers".to_owned(), answers)],
            owned(&rows[0][1..last]),
        );
    }
    table
}

/// The patterns of the children table of initializer values: one value's answer.
fn initializer_patterns(tables: &[SweepTable<'_>]) -> PatternTable {
    let init = tables
        .iter()
        .find(|table| table.name == "children, init")
        .expect("the sweep has a children, init table");
    let mut table = PatternTable {
        name: "children, init",
        prefix: "ci",
        columns: owned(&["init"]),
        patterns: Vec::new(),
    };
    for row in &init.rows {
        table.add(
            vec![("answer".to_owned(), owned(&[row[4]]))],
            owned(&[row[1], row[3]]),
        );
    }
    table
}

/// The principles of the checked-in patterns file, by table and answer lines, and its review line.
fn golden_principles(golden: &str) -> (BTreeMap<(String, String), String>, String) {
    let mut principles = BTreeMap::new();
    let mut reviewed = format!("{REVIEWED} not yet (S5.0g part (b), item 2)");
    let mut section = String::new();
    let mut answers = BTreeMap::<String, String>::new();
    for line in golden.lines() {
        if line.starts_with(REVIEWED) {
            line.clone_into(&mut reviewed);
        } else if let Some(name) = line.strip_prefix("## ") {
            name.clone_into(&mut section);
        } else if !line.starts_with('#') {
            let mut cells = line.splitn(3, '\t');
            let (Some(id), Some(label)) = (cells.next(), cells.next()) else {
                continue;
            };
            let rest = cells.next().unwrap_or_default();
            if label == PRINCIPLE {
                let key = (section.clone(), answers.remove(id).unwrap_or_default());
                principles.insert(key, rest.to_owned());
            } else if label != "member" && label != "line" {
                let entry = answers.entry(id.to_owned()).or_default();
                let _ = writeln!(entry, "{label}\t{rest}");
            }
        }
    }
    (principles, reviewed)
}

/// The patterns of the sweep, rendered with each pattern's principle taken from `golden` (the
/// checked-in file) where `golden` has a pattern with the same table and answers, else empty.
fn sweep_patterns(sweep: &str, golden: &str) -> String {
    let tables = sweep_tables(sweep);
    let mut out = vec![
        main_patterns(&tables, "readable, claim", "rc", &["readable", "claim"]),
        main_patterns(&tables, "cells", "c", &["cells"]),
        main_patterns(&tables, "init", "i", &["init"]),
        main_patterns(
            &tables,
            "readable, claim more",
            "rx",
            &["readable more", "claim more"],
        ),
        main_patterns(&tables, "cells more", "cx", &["cells more"]),
        main_patterns(&tables, "cells back", "cb", &["cells back"]),
        main_patterns(&tables, "init more", "ix", &["init more"]),
    ];
    out.extend(children_patterns(&tables));
    let (principles, reviewed) = golden_principles(golden);
    let mut text = String::new();
    text.push_str(concat!(
        "# The row patterns of `cells-outcome-sweep.tsv`: each distinct pattern once, with the rows\n",
        "# that share it and the principle that gives it (P0-P7 and E1-E3 of S5-principles.md, the\n",
        "# design's S1 (b), L1-L5 and Q1-Q3, and the S5.0 and S5.0g rulings). It is the reviewed\n",
        "# judgement check 5's `SWEEP` reason names: the sweep's tuples no case covers are judged\n",
        "# here. Generated by krs-test-support `--test cells_oracle`\n",
        "# (`the_sweep_patterns_are_the_golden`) from the sweep; rewrite with\n",
        "# KRS_CELLS_PATTERNS_RECORD=1, which keeps the principle of every pattern whose answers are\n",
        "# unchanged and leaves a new one's empty: the test fails until it is written.\n",
        "#\n",
        "# A pattern is exact: a table and the answers, cell by cell, of one row group across the\n",
        "# table's columns (the sweep's short names and `|product:` marks).\n",
        "# - readable, claim; cells; init: a row group is a side and a stack, and its pattern is its\n",
        "#   rows, path `-`, `?` and `*` (init: `-` only), one line each. readable and claim have the same\n",
        "#   columns, so they share patterns; a member names its forms. A row's `other` is a\n",
        "#   function of its form, side and stack, so a member determines it.\n",
        "# - children: a row group is one result of the sweep's children section, its pattern the\n",
        "#   answers in readable, claim and cells! (whose row writes each record as its fragment); a\n",
        "#   member is its stack, `other` and result, in readable's spelling.\n",
        "# - children, init: a row group is one value, its pattern the one answer.\n",
        "# - the `more` tables (readable, claim more; cells more; init more) print each form's\n",
        "#   further single-entry spellings (the pattern review's gaps G7, G8, G9) as tables of their\n",
        "#   own, with the same rows, and cells back the computation's back items in cells! (E1 in\n",
        "#   every form, the fixes review's F-6); children, base matched nowhere is the children\n",
        "#   table's reading where nothing binds an update's label (S5.0g:P-R3); children, fragment\n",
        "#   child a group record's Map, List or computation child in a subject and a result (the\n",
        "#   fixes review's F-1), its member the row's side, stack, `other` and entry.\n",
        "# Lines: `ID  PATH|answers  ANSWERS..` (the pattern), `ID  member  ..` (each row group that\n",
        "# has it), `ID  principle  TEXT`. IDs number the patterns in the order their first member is\n",
        "# printed in the sweep.\n",
        "#\n",
        "# The path rule, S5.0g:R3 (each main pattern's `?` and `*` lines): an entry naming a cell\n",
        "#   below a `?` or `*` ancestor is judged on its own layers first (the form step, then P3\n",
        "#   against the cell's own stack, refusals inside its marks included) and those refusals\n",
        "#   stand; whatever they admit is then refused for the ancestor (design:S1b): `owp` below\n",
        "#   `?`, `cwi` below `*`. A pairing refusal of the `-` row (rm, uor, atc, Q3's overwrite cir,\n",
        "#   S5.0:F3's open record over an existing group, map-collection-key, record-update-base)\n",
        "#   comes after the path, so the path class replaces it (S5.0g:P-R12), as it does the\n",
        "#   product's List collection limitations at the pairing (both ends, a back instance kept\n",
        "#   in place: `ils`). The product's other departures (design:M3's readable `mrr` at the\n",
        "#   kind step, design:M3's `cells!` `arm` and E3's `ir` at the form step) come before the\n",
        "#   path and show through.\n",
        "#\n",
        "# Citations: every principle line cites the IDs of this registry, and only these (a test\n",
        "#   fails on a line that cites none, an unknown one, or a ruling by a bare number):\n",
    ));
    for (id, statement, source, scope) in CITATIONS {
        let _ = writeln!(
            text,
            "#   {id}: {statement} ({source}; scope: {})",
            scope.shown()
        );
    }
    text.push_str(&reviewed);
    text.push('\n');
    for table in &out {
        let _ = write!(
            text,
            "#\n## {}\npattern\tline\t{}\n",
            table.name,
            table.columns.join("\t")
        );
        for (at, pattern) in table.patterns.iter().enumerate() {
            let id = format!("{}{:02}", table.prefix, at + 1);
            let mut key = String::new();
            for (label, answers) in &pattern.lines {
                let answers = answers.join("\t");
                let _ = writeln!(text, "{id}\t{label}\t{answers}");
                let _ = writeln!(key, "{label}\t{answers}");
            }
            for member in &pattern.members {
                let _ = writeln!(text, "{id}\tmember\t{}", member.join("\t"));
            }
            let principle = principles
                .get(&(table.name.to_owned(), key))
                .map_or("", String::as_str);
            let _ = writeln!(text, "{id}\t{PRINCIPLE}\t{principle}");
        }
    }
    text
}

/// The sweep's patterns are the checked-in ones, each with a principle: a sweep row that moves
/// to another pattern, a new pattern, or a pattern whose rows change shows as a diff of
/// `cells-outcome-patterns.tsv`, and a pattern without a principle fails.
#[test]
fn the_sweep_patterns_are_the_golden() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/class-matrix")
        .join(PATTERNS_FILE);
    let golden = std::fs::read_to_string(&path).unwrap_or_default();
    let patterns = sweep_patterns(&outcome_sweep(), &golden);
    if std::env::var_os("KRS_CELLS_PATTERNS_RECORD").is_some() {
        std::fs::write(&path, &patterns)
            .unwrap_or_else(|error| panic!("{}: {error}", path.display()));
    } else if golden != patterns {
        let line = golden
            .lines()
            .zip(patterns.lines())
            .position(|(was, is)| was != is)
            .unwrap_or_else(|| golden.lines().count().min(patterns.lines().count()));
        panic!(
            "{PATTERNS_FILE} differs from the sweep's patterns from line {}: was {:?}, is {:?}; \
             a sweep row changed pattern, a pattern appeared or its rows changed: review it, \
             record it with KRS_CELLS_PATTERNS_RECORD=1 and write each new pattern's principle",
            line + 1,
            golden.lines().nth(line),
            patterns.lines().nth(line)
        );
    }
    let suffix = format!("\t{PRINCIPLE}\t");
    let unprincipled = patterns
        .lines()
        .filter_map(|line| line.strip_suffix(&suffix))
        .collect::<Vec<_>>();
    assert!(
        unprincipled.is_empty(),
        "{PATTERNS_FILE}: patterns without a principle: {unprincipled:?}"
    );
}

/// The citations a principle line makes: qualified IDs (`S5.0:R3`, `design:R3`), principle IDs
/// (`P3b`, `E1`, `Q1`, `L4`), and rulings cited by a bare number (`R3`, `F3`, `D-2`, `P-R5`,
/// `ruling 3`), which no reader can resolve (P-R11).
fn citations(line: &str) -> (Vec<&str>, Vec<String>) {
    let principle = |token: &str| {
        let mut chars = token.chars();
        match (chars.next(), chars.as_str()) {
            (Some('P'), rest) => {
                let rest = rest.strip_suffix(['a', 'b', 'c']).unwrap_or(rest);
                rest.len() == 1 && rest.chars().all(|c| c.is_ascii_digit())
            }
            (Some('E' | 'Q' | 'L'), rest) => {
                rest.len() == 1 && rest.chars().all(|c| c.is_ascii_digit())
            }
            _ => false,
        }
    };
    let numbered = |token: &str| {
        let digits = |rest: &str| !rest.is_empty() && rest.chars().all(|c| c.is_ascii_digit());
        ["R", "F", "D-", "P-R", "M"]
            .iter()
            .any(|prefix| token.strip_prefix(prefix).is_some_and(digits))
    };
    let mut cited = Vec::new();
    let mut bare = Vec::new();
    for token in line.split(|c: char| !(c.is_ascii_alphanumeric() || ".:-".contains(c))) {
        let token = token.trim_matches(|c: char| ".:-".contains(c));
        if token.is_empty() || token.contains("::") {
            continue;
        }
        if let Some((source, id)) = token.split_once(':')
            && source.starts_with(|c: char| c.is_ascii_alphabetic())
            && !id.is_empty()
            && !id.contains(':')
        {
            cited.push(token);
        } else if principle(token) {
            cited.push(token);
        } else if numbered(token) {
            bare.push(token.to_owned());
        }
    }
    let words = line.split_whitespace().collect::<Vec<_>>();
    for pair in words.windows(2) {
        if pair[0].eq_ignore_ascii_case("ruling")
            && pair[1].starts_with(|c: char| c.is_ascii_digit())
        {
            bare.push(format!("{} {}", pair[0], pair[1]));
        }
    }
    (cited, bare)
}

/// The members of each pattern of the patterns golden, as `(form, stack)`: a main table's
/// member names its forms (a `more` or `back` table's by its form) and its stack; a children
/// table's member is written in readable, claim and `cells!` (the init children's in the
/// initializer), its stack the member's own.
fn pattern_members(golden: &str) -> BTreeMap<&str, Vec<(String, String)>> {
    let mut members = BTreeMap::<&str, Vec<(String, String)>>::new();
    let mut section = "";
    for line in golden.lines() {
        if let Some(name) = line.strip_prefix("## ") {
            section = name;
            continue;
        }
        let cells = line.split('\t').collect::<Vec<_>>();
        if line.starts_with('#') || cells.get(1) != Some(&"member") {
            continue;
        }
        let entry = members.entry(cells[0]).or_default();
        let (forms, stack): (Vec<&str>, &str) = match section {
            "children, init" => (vec!["init"], cells[2]),
            "children, fragment child" => (RULE_FORMS.to_vec(), cells[3]),
            children if children.starts_with("children") => (RULE_FORMS.to_vec(), cells[2]),
            _ => (
                cells[2]
                    .split(", ")
                    .map(|form| form.split(' ').next().unwrap_or(form))
                    .collect(),
                cells[4],
            ),
        };
        for form in forms {
            entry.push((form.to_owned(), stack.to_owned()));
        }
    }
    members
}

/// Measure (c) of the S5.0g pattern review fixes (P-R11): every principle line cites the
/// registry ([`CITATIONS`]), and every ID it cites is the registry's; a ruling cited by a bare
/// number fails, since several rulings share each number. And (the fixes review's F-4, ruled) an
/// ID a line cites must reach some member of its pattern by its [`Scope`]: a line citing an ID
/// for cells no member is in (a `cells!` ruling for an initializer, a ruling on `?` and `*` cells
/// for a plain leaf) cites a ruling that does not cover them (P-R10's class).
#[test]
fn every_principle_line_cites_the_registry() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/class-matrix")
        .join(PATTERNS_FILE);
    let golden = std::fs::read_to_string(&path).unwrap_or_default();
    let known = CITATIONS
        .iter()
        .map(|(id, _, _, scope)| (*id, *scope))
        .collect::<BTreeMap<_, _>>();
    let members = pattern_members(&golden);
    let mut failures = Vec::new();
    let mut lines = 0;
    for line in golden.lines() {
        let Some((id, text)) = line.split_once(&format!("\t{PRINCIPLE}\t")) else {
            continue;
        };
        lines += 1;
        let (cited, bare) = citations(text);
        if cited.is_empty() {
            failures.push(format!("{id}: its principle cites no registry ID"));
        }
        let own = members.get(id).map_or(&[][..], Vec::as_slice);
        for cited in &cited {
            match known.get(cited) {
                None => failures.push(format!("{id}: cites {cited}, which the registry has not")),
                Some(scope) if !own.iter().any(|(form, stack)| scope.holds(form, stack)) => {
                    failures.push(format!(
                        "{id}: cites {cited}, whose scope ({}) holds none of its members {own:?}",
                        scope.shown()
                    ));
                }
                Some(_) => {}
            }
        }
        for bare in bare {
            failures.push(format!(
                "{id}: cites `{bare}` by a bare number; qualify it from the registry"
            ));
        }
    }
    assert!(lines > 0, "{PATTERNS_FILE} has no principle line");
    assert!(failures.is_empty(), "{failures:#?}");
}

/// Where the root sweep cells no compiled case witnesses are accounted for (measure (a)).
const WITNESSES_FILE: &str = "cells-outcome-witnesses.tsv";

/// The cases a pending entry names, by any test's key ([`pending::case_of`]): each is red on
/// some test, so its compiled verdict is not the one its row states.
fn pending_cases() -> BTreeMap<String, BTreeSet<String>> {
    let pending = Pending::parse(&read_class_matrix("pending.toml"))
        .unwrap_or_else(|errors| panic!("pending.toml: {errors:#?}"));
    let mut cases = BTreeMap::<String, BTreeSet<String>>::new();
    for (key, entry) in &pending.entries {
        if let Some(case) = pending::case_of(key) {
            cases
                .entry(case.to_owned())
                .or_default()
                .insert(entry.finding.clone());
        }
    }
    cases
}

/// The sweep cells measure (a) requires a witness of, keyed `(table, side, stack, column)`, as
/// the checked-in sweep prints them: one per main table's row at path `-` and column (the column
/// is the entry's spelling), and one per children row (its side is its form and side, over the
/// row's `other` where it has one; its column the entry). A path row (`?`, `*`) needs no witness
/// of its own: S5.0g:R3 judges it from the cell's own answer, its `-` row's, and check 4's path
/// step judges the advice there.
fn printed_root_cells(sweep: &str) -> BTreeSet<sweep::Key> {
    let mut cells = BTreeSet::new();
    for table in sweep_tables(sweep) {
        if table.name.starts_with("children") {
            let at = |name: &str| table.header.iter().position(|cell| *cell == name);
            let (stack, other) = (at("stack").expect("a stack column"), at("other"));
            let entry = table.header.len() - 2;
            for row in &table.rows {
                let written = at("side").map_or("result", |side| row[side]);
                let side = match other.map(|other| row[other]) {
                    _ if row[0] == "init" => "init".to_owned(),
                    Some("-") | None => format!("{} {written}", row[0]),
                    Some(other) => format!("{} {written} over {other}", row[0]),
                };
                cells.insert((
                    table.name.to_owned(),
                    side,
                    row[stack].to_owned(),
                    row[entry].to_owned(),
                ));
            }
            continue;
        }
        for row in table.rows.iter().filter(|row| row[1] == "-") {
            for column in &table.header[4..] {
                cells.insert((
                    table.name.to_owned(),
                    row[0].to_owned(),
                    row[2].to_owned(),
                    (*column).to_owned(),
                ));
            }
        }
    }
    cells
}

/// The sweep's answer at a root cell, as the sweep's probe gives it.
fn sweep_answer(cell: &sweep::Cell) -> Outcome {
    let stack = sweep::named_stack(cell.stack);
    Probe {
        form: cell.form,
        side: cell.side,
        path: &[],
        stack: &stack,
        text: cell.text,
        other: cell.other.as_deref(),
        written: cell.written,
        bound: cell.bound,
        records: &[],
        elsewhere: false,
    }
    .oracle()
}

/// Whether a case witnesses a root cell whose sweep answer is `answer`: its row agrees with
/// `outcome`, and so its compiled verdict, which conforms (no pending entry names it), is
/// `outcome`'s; it means the cell (its `outcome` is the cell's answer); and no
/// `[cell-exception]` names it (an excepted row departs from `outcome`, so its verdict witnesses
/// the departure, not `outcome`).
fn witnesses_cell(
    id: &str,
    entry: &EntryCase,
    answer: Outcome,
    exceptions: &[(Glob, String, String)],
    red: &BTreeMap<String, BTreeSet<String>>,
) -> bool {
    agrees(entry.outcome(), &EXPECTED[id])
        && entry.outcome() == answer
        && naming(id, exceptions).is_empty()
        && !red.contains_key(id)
}

/// Each root sweep cell no compiled case witnesses, with the reason, from the cases themselves:
/// `red: FINDINGS (ID)` where the cell's case is red (the compiler departs from `outcome` there,
/// under those findings), `excepted: PRINCIPLE (ID)` where an exception holds its row at the
/// product's answer, or the generator's `unbuilt:` reason where no case can be compiled; and
/// `no witness (IDS)` where a case exists and witnesses nothing for another reason (its row or
/// its answer disagrees), which is no reason and fails.
fn unwitnessed_cells() -> BTreeMap<sweep::Key, String> {
    let exceptions = exceptions();
    let red = pending_cases();
    let unbuilt = sweep::unbuilt();
    let mut by_key = BTreeMap::<sweep::Key, Vec<&(&Case, EntryCase)>>::new();
    let mut by_row = BTreeMap::<(String, String, String, String), Vec<&(&Case, EntryCase)>>::new();
    for generated in ENTRIES.iter() {
        let (case, entry) = generated;
        if let Some(key) = sweep::key_of(&case.id) {
            by_key.entry(key.clone()).or_default().push(generated);
        } else if entry.entry.path.is_empty() {
            let stack = entry_cases::declared_stack(case, &entry.entry.cell);
            by_row
                .entry(sweep::row_key(&stack, entry))
                .or_default()
                .push(generated);
        }
    }
    let mut out = BTreeMap::new();
    for cell in sweep::cells() {
        let answer = sweep_answer(&cell);
        let mut candidates = by_key.get(&cell.key).cloned().unwrap_or_default();
        candidates.extend(
            by_row
                .get(&sweep::main_key(&cell))
                .into_iter()
                .flatten()
                .copied(),
        );
        if candidates
            .iter()
            .any(|(case, entry)| witnesses_cell(&case.id, entry, answer, &exceptions, &red))
        {
            continue;
        }
        let reason = if let Some(reason) = unbuilt.get(&cell.key) {
            (*reason).to_owned()
        } else if let Some((case, _)) = candidates
            .iter()
            .find(|(case, _)| red.contains_key(&case.id))
        {
            let findings = red[&case.id].iter().cloned().collect::<Vec<_>>();
            format!("red: {} ({})", findings.join(", "), case.id)
        } else if let Some((case, _)) = candidates
            .iter()
            .find(|(case, _)| !naming(&case.id, &exceptions).is_empty())
        {
            let principle = exceptions
                .iter()
                .find(|(glob, ..)| glob.matches(&case.id))
                .map_or("", |(_, _, principle)| principle.as_str());
            format!("excepted: {principle} ({})", case.id)
        } else {
            let ids = candidates
                .iter()
                .map(|(case, _)| case.id.as_str())
                .collect::<Vec<_>>();
            format!("no witness ({})", ids.join(", "))
        };
        out.insert(cell.key, reason);
    }
    out
}

/// Measure (a) in the key of the S5.0g fixes review's ruling 2 (F-2): every root sweep cell
/// (form, side, stack, column at path `-`) is witnessed by a compiled case, the sweep's own
/// ([`sweep`], shard `sweep`) or another family's case of the same form, side, stack, spelling
/// and subject entry, whose row agrees with `outcome` there, with no `[cell-exception]` or
/// pending entry naming it ([`witnesses_cell`]). Otherwise [`WITNESSES_FILE`] lists the cell with
/// its reason, which the cases give ([`unwitnessed_cells`]): the file must equal it, so a new
/// unwitnessed cell, a stale entry and a changed reason each fail, and a cell with no reason
/// (`no witness`) fails whatever the file says. `KRS_CELLS_WITNESSES_RECORD=1` rewrites the file.
/// The generator's cells are the checked-in sweep's root cells, one for one.
///
/// This test reads the table and `pending.toml`, never a compiled verdict: a case counts as a
/// witness because its row says what the compiler must answer and no pending entry says it
/// answers otherwise. It is sound together with a green full `sweep` shard
/// (`scripts/krs-class.sh --shard sweep`), which compiles every case and fails on any verdict
/// its row and pending entry do not state; neither alone shows that the compiler agrees with
/// `outcome` (S5.0g item 3a fixes, F-7).
///
/// Path rows need no witness of their own: S5.0g:R3 and check 4's path step judge them from the
/// root's answer.
#[test]
fn every_root_sweep_cell_is_witnessed_by_a_compiled_case() {
    let printed = printed_root_cells(&outcome_sweep());
    let generated = sweep::cells()
        .into_iter()
        .map(|cell| cell.key)
        .collect::<BTreeSet<_>>();
    assert_eq!(
        printed.symmetric_difference(&generated).collect::<Vec<_>>(),
        Vec::<&sweep::Key>::new(),
        "the generator's root cells are not the sweep's"
    );
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/class-matrix")
        .join(WITNESSES_FILE);
    let missing = unwitnessed_cells();
    let mut text = String::from(concat!(
        "# The root sweep cells no compiled case witnesses (measure (a), in the S5.0g fixes review's\n",
        "# ruling 2 key): `TABLE  SIDE  STACK  COLUMN  REASON`, one line per sweep cell at path `-`\n",
        "# whose case is red (the compiler departs from `outcome`, under the findings named), excepted\n",
        "# (its row holds the product's answer, by the principle named), or cannot be compiled (the\n",
        "# generator's reason). Generated by krs-test-support `--test cells_oracle`\n",
        "# (`every_root_sweep_cell_is_witnessed_by_a_compiled_case`), which fails where the file\n",
        "# differs from the cases; rewrite with KRS_CELLS_WITNESSES_RECORD=1 and review the diff.\n",
    ));
    for (key, reason) in &missing {
        let _ = writeln!(text, "{}\t{}\t{}\t{}\t{reason}", key.0, key.1, key.2, key.3);
    }
    let mut counts = BTreeMap::<&str, usize>::new();
    for reason in missing.values() {
        *counts
            .entry(reason.split(':').next().unwrap_or(reason))
            .or_default() += 1;
    }
    println!(
        "{} root cells, {} unwitnessed: {counts:?}",
        generated.len(),
        missing.len()
    );
    if std::env::var_os("KRS_CELLS_WITNESSES_RECORD").is_some() {
        std::fs::write(&path, &text).unwrap_or_else(|error| panic!("{}: {error}", path.display()));
    }
    let failures = missing
        .iter()
        .filter(|(_, reason)| reason.starts_with("no witness"))
        .map(|(key, reason)| format!("{key:?}: {reason}"))
        .collect::<Vec<_>>();
    assert!(
        failures.is_empty(),
        "{} root cells have a case that witnesses nothing: {:#?}",
        failures.len(),
        failures.iter().take(40).collect::<Vec<_>>()
    );
    let golden = std::fs::read_to_string(&path).unwrap_or_default();
    if golden != text {
        let lines = |text: &str| text.lines().map(str::to_owned).collect::<BTreeSet<_>>();
        let (golden, text) = (lines(&golden), lines(&text));
        panic!(
            "{WITNESSES_FILE} differs from the cases (rewrite with KRS_CELLS_WITNESSES_RECORD=1): \
             listed, not computed {:#?}; computed, not listed {:#?}",
            golden.difference(&text).take(20).collect::<Vec<_>>(),
            text.difference(&golden).take(20).collect::<Vec<_>>()
        );
    }
}

/// A stack the sweep names: one of its main stacks, a children stack, or an initializer
/// children stack.
fn named_stack(name: &str) -> Vec<Layer> {
    const CHILDREN: [&str; 10] = [
        "group H",
        "group M",
        "? group H",
        "* List of T",
        "* Map of A",
        "group C",
        "group O",
        "group W",
        "? group G",
        "? leaf List",
    ];
    if let Some((_, stack)) = sweep_stacks().into_iter().find(|(stack, _)| *stack == name) {
        return stack;
    }
    if CHILDREN.contains(&name) {
        return children_stack(name);
    }
    nested_collection_stack(name)
}

/// Measure (b) of the S5.0g pattern review fixes: every cell-entry class `outcome` answers with
/// states its spellings as machine-read examples (`examples` in `expected.toml`, `FORM ; SIDE ;
/// PATH ; STACK ; ENTRY ; OTHER`), and `outcome` gives each example its class. A doc whose
/// spellings another class answers then fails here, as P-R4's two docs would have.
#[test]
fn every_cell_entry_class_doc_example_gives_its_class() {
    let mut failures = Vec::new();
    let mut judged = 0;
    for class in ENTRY_CLASSES.iter().chain(&LINT_CLASSES) {
        let Some(declared) = TABLE.classes.get(*class) else {
            failures.push(format!("{class}: no class of expected.toml"));
            continue;
        };
        if declared.examples.is_empty() {
            failures.push(format!(
                "{class}: its doc states no machine-read example (`examples`)"
            ));
        }
        for example in &declared.examples {
            let parts = example.split(" ; ").collect::<Vec<_>>();
            let [form, side, path, stack, entry, other] = parts[..] else {
                failures.push(format!(
                    "{class}: `{example}` is not FORM ; SIDE ; PATH ; STACK ; ENTRY ; OTHER"
                ));
                continue;
            };
            let form = match form {
                "readable" => Form::Readable,
                "claim" => Form::Claim,
                "cells" => Form::Cells,
                "init" => Form::Init,
                other => {
                    failures.push(format!("{class}: `{example}`: no form {other}"));
                    continue;
                }
            };
            let (side, written, bound): (Side, bool, &[&str]) = match side {
                "subject" => (Side::Subject, false, &[]),
                "subject, written" => (Side::Subject, true, &[]),
                "result" => (Side::Result, false, &["x", "y", "z", "old"]),
                "init" => (Side::Initializer, false, &["pgm"]),
                other => {
                    failures.push(format!("{class}: `{example}`: no side {other}"));
                    continue;
                }
            };
            let path = match path {
                "-" => Vec::new(),
                "?" => vec![Layer::Optional],
                "*" => vec![Layer::Instances(Order::List)],
                other => {
                    failures.push(format!("{class}: `{example}`: no path {other}"));
                    continue;
                }
            };
            let stack = named_stack(stack);
            let probe = Probe {
                form,
                side,
                path: &path,
                stack: &stack,
                text: entry,
                other: (other != "-").then_some(other),
                written,
                bound,
                records: &[],
                elsewhere: false,
            };
            let want = if LINT_CLASSES.contains(class) {
                Outcome::Admit { lint: Some(class) }
            } else {
                Outcome::Refuse(class)
            };
            judged += 1;
            let got = probe.oracle();
            if got != want {
                failures.push(format!(
                    "{class}: its doc's example `{example}` is {got:?} by `outcome`"
                ));
            }
        }
    }
    println!("{judged} doc examples judged");
    assert!(failures.is_empty(), "{failures:#?}");
}

/// Every content root an entry's spelling writes, with its cell's name: the entry's own content
/// where its cell's content is a computation or a list or map leaf (P6's content roots), below
/// presence, and the children of the group or instance records it writes, each judged as its
/// own cell's entry (P1). A collection's own instances are not looked at: K's configuration
/// abstraction leaves their frame implicit.
fn content_roots<'s>(
    cell: &str,
    stack: &[Layer],
    spelling: &'s Spelling,
    out: &mut Vec<(String, &'s Spelling)>,
) {
    let spelling = match spelling {
        Spelling::Alias(_, inner) => inner,
        other => other,
    };
    let records = |items: &'s [Spelling], group: &Group, out: &mut Vec<(String, &'s Spelling)>| {
        for item in items {
            let item = match item {
                Spelling::Alias(_, inner) => inner,
                other => other,
            };
            if let Spelling::Record(record) | Spelling::Fragment(record) = item
                && record.head == group.name
            {
                for (name, value) in &record.fields {
                    if let Some((_, child)) = group.children.iter().find(|(child, _)| child == name)
                    {
                        content_roots(name, child, value, out);
                    }
                }
            }
        }
    };
    match (stack, spelling) {
        ([Layer::Optional, rest @ ..], Spelling::Present(inner) | Spelling::Absent(inner)) => {
            content_roots(cell, rest, inner, out);
        }
        (
            [Layer::Instances(_), Layer::Group(group)],
            Spelling::Brackets(seq)
            | Spelling::Braces(seq)
            | Spelling::InstList(seq)
            | Spelling::InstSet(seq),
        ) => records(&seq.items, group, out),
        ([Layer::Group(group)], _) => records(std::slice::from_ref(spelling), group, out),
        (
            [Layer::Computation | Layer::Leaf(Notation::List | Notation::Cons | Notation::Map)],
            _,
        ) => {
            out.push((cell.to_owned(), spelling));
        }
        _ => {}
    }
}

/// The contents of every `<cell>` .. `</cell>` in a recorded K text, in order.
fn k_cells<'k>(k: &'k str, cell: &str) -> Vec<&'k str> {
    let (open, close) = (format!("<{cell}"), format!("</{cell}>"));
    let mut found = Vec::new();
    let mut at = 0;
    while let Some(start) = k[at..].find(&open).map(|start| start + at) {
        let after = &k[start + open.len()..];
        if !after.starts_with('>') && !after.starts_with(' ') {
            at = start + open.len();
            continue;
        }
        let Some(body) = after.find('>').map(|end| start + open.len() + end + 1) else {
            break;
        };
        let Some(end) = k[body..].find(&close).map(|end| end + body) else {
            break;
        };
        found.push(k[body..end].trim());
        at = end + close.len();
    }
    found
}

/// The tokens of a K text at its own top level, outside every parenthesis: `ListItem(V0:KItem)
/// V1:List` is `ListItem`, `V1:List`; a cons list `V0:Int : V1:Ints` is `V0:Int`, `:`, `V1:Ints`.
fn top_tokens(content: &str) -> Vec<&str> {
    let content = content.trim();
    let mut depth = 0_usize;
    let mut top = Vec::new();
    let mut start = None;
    for (at, c) in content.char_indices() {
        if c.is_whitespace() || matches!(c, '(' | ')' | ',') {
            if let Some(from) = start.take()
                && depth == 0
            {
                top.push(&content[from..at]);
            }
            match c {
                '(' => depth += 1,
                ')' => depth = depth.saturating_sub(1),
                _ => {}
            }
        } else if start.is_none() {
            start = Some(at);
        }
    }
    if let Some(from) = start
        && depth == 0
    {
        top.push(&content[from..]);
    }
    top
}

/// Every token of a K text, inside parentheses too.
fn all_tokens(k: &str) -> impl Iterator<Item = &str> {
    k.split(|c: char| c.is_whitespace() || matches!(c, '(' | ')' | ','))
        .filter(|token| !token.is_empty())
}

/// A K variable token's name: `V3` for `V3:Map` or `V3`.
fn variable_name(token: &str) -> Option<&str> {
    let name = token.split_once(':').map_or(token, |(name, _)| name);
    let number = name.strip_prefix('V')?;
    (!number.is_empty() && number.bytes().all(|byte| byte.is_ascii_digit())).then_some(name)
}

/// The variables of a K cell content that can stand for its rest: one of a collection's or a
/// computation's sort (`V3:Map`) at the content's top level, or a cons list's tail (the last
/// item, after a `:`).
fn rest_candidates(content: &str) -> Vec<&str> {
    let top = top_tokens(content);
    let last = top.len().saturating_sub(1);
    top.iter()
        .enumerate()
        .filter_map(|(at, token)| {
            let name = variable_name(token)?;
            match token.split_once(':').map(|(_, sort)| sort) {
                Some("List" | "Map" | "Set" | "K") => Some(name),
                _ if at == last && at > 0 && top[at - 1] == ":" => Some(name),
                _ => None,
            }
        })
        .collect()
}

/// How often a variable occurs in a K sentence.
fn occurrences(sentence: &str, name: &str) -> usize {
    all_tokens(sentence)
        .filter(|token| variable_name(token) == Some(name))
        .count()
}

/// Ruling 1 (b), as F-9 widens it: a rest variable of `subject` that stands at the same content
/// root in `result`, in any position (P6 makes a result's `..` the subject's rest of the same
/// cell, wherever the result puts it), and occurs nowhere else in `sentence` than at those
/// `places` (1 when the cell is not rewritten, so both sides are one text; 2 otherwise). A
/// variable that occurs again, a condition included, constrains the rest: it is a use, not a
/// frame.
fn kept_rest(subject: &str, result: &str, sentence: &str, places: usize) -> bool {
    rest_candidates(subject).into_iter().any(|name| {
        top_tokens(result)
            .iter()
            .any(|token| variable_name(token) == Some(name))
            && occurrences(sentence, name) == places
    })
}

/// Ruling 1 (c) by its meaning (P0): a subject's rest variable that occurs nowhere else in the
/// sentence matches the rest unconstrained, exactly as `_` there does.
fn unused_rest(subject: &str, sentence: &str) -> bool {
    rest_candidates(subject)
        .into_iter()
        .any(|name| occurrences(sentence, name) == 1)
}

/// A K text split at its own ` => `, outside every cell and parenthesis it holds; `None` where it
/// writes no rewrite of its own.
fn split_rewrite(text: &str) -> Option<(&str, &str)> {
    let (mut cells, mut parens) = (0_isize, 0_isize);
    let bytes = text.as_bytes();
    for (at, c) in text.char_indices() {
        match c {
            '(' => parens += 1,
            ')' => parens -= 1,
            '<' if text[at + 1..].starts_with('/') => cells -= 1,
            '<' if text[at + 1..].starts_with(|c: char| c.is_ascii_alphabetic()) => cells += 1,
            '=' if cells == 0
                && parens == 0
                && bytes.get(at + 1) == Some(&b'>')
                && at > 0
                && bytes[at - 1] == b' ' =>
            {
                return Some((text[..at].trim(), text[at + 2..].trim()));
            }
            _ => {}
        }
    }
    None
}

/// A whole-cell rewrite of a K sentence (ruling 1 (d)), `(<c> L </c> => <c> R </c>)`: its span
/// in the sentence, with both sides.
struct CellRewrite<'k> {
    span: std::ops::Range<usize>,
    cell: &'k str,
    subject: &'k str,
    result: &'k str,
}

/// One side of a whole-cell rewrite.
enum RewriteSide<'k> {
    /// The cell itself, `<name> .. </name>`.
    Cell(&'k str),
    /// A whole cell written otherwise: `.Bag` (no cell, a `?` cell absent) or one variable or
    /// `_` of its cell sort.
    Whole,
}

/// The side of a whole-cell rewrite `text` is, if it is one.
fn rewrite_side(text: &str) -> Option<RewriteSide<'_>> {
    match text.strip_prefix('<') {
        Some(tag) => {
            let name = tag
                .split(|c: char| c == '>' || c.is_whitespace())
                .next()
                .unwrap_or_default();
            text.ends_with(&format!("</{name}>"))
                .then_some(RewriteSide::Cell(name))
        }
        None => (!text.contains(char::is_whitespace)).then_some(RewriteSide::Whole),
    }
}

/// Every whole-cell rewrite a K sentence writes.
fn cell_rewrites(k: &str) -> Vec<CellRewrite<'_>> {
    let mut found = Vec::new();
    let mut at = 0;
    while let Some(open) = k[at..].find('(').map(|open| open + at) {
        let mut depth = 0_isize;
        let mut close = None;
        for (offset, c) in k[open..].char_indices() {
            match c {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        close = Some(open + offset);
                        break;
                    }
                }
                _ => {}
            }
        }
        let Some(close) = close else { break };
        let inner = &k[open + 1..close];
        let rewrite = split_rewrite(inner).and_then(|(subject, result)| {
            match (rewrite_side(subject)?, rewrite_side(result)?) {
                (RewriteSide::Cell(left), RewriteSide::Cell(right)) if left != right => None,
                (RewriteSide::Cell(cell), _) | (_, RewriteSide::Cell(cell)) => {
                    Some((cell, subject, result))
                }
                (RewriteSide::Whole, RewriteSide::Whole) => None,
            }
        });
        if let Some((cell, subject, result)) = rewrite {
            found.push(CellRewrite {
                span: open..close + 1,
                cell,
                subject,
                result,
            });
            at = close + 1;
        } else {
            at = open + 1;
        }
    }
    found
}

/// The K sentence as one side reads it: every whole-cell rewrite replaced by its subject's cell
/// or its result's (ruling 1 (d)).
fn side_view(k: &str, result: bool) -> String {
    let mut view = String::new();
    let mut at = 0;
    for rewrite in cell_rewrites(k) {
        view.push_str(&k[at..rewrite.span.start]);
        view.push_str(if result {
            rewrite.result
        } else {
            rewrite.subject
        });
        at = rewrite.span.end;
    }
    view.push_str(&k[at..]);
    view
}

/// The names of the cells directly inside a K cell's content, in order.
fn child_cells(content: &str) -> Vec<&str> {
    let mut children = Vec::new();
    let mut depth = 0_usize;
    let mut rest = content;
    while let Some(at) = rest.find('<') {
        let tag = &rest[at + 1..];
        if let Some(name) = tag.strip_prefix('/') {
            depth = depth.saturating_sub(1);
            rest = &name[name.find('>').map_or(name.len(), |end| end + 1)..];
            continue;
        }
        if !tag.starts_with(|c: char| c.is_ascii_alphabetic()) {
            rest = tag;
            continue;
        }
        let end = tag.find(['>', ' ']).unwrap_or(tag.len());
        if depth == 0 {
            children.push(&tag[..end]);
        }
        depth += 1;
        rest = &tag[end..];
    }
    children
}

/// The results of every rewrite a K sentence writes: each whole-cell rewrite's result and each
/// cell content's own ` => `'s right side.
fn rewrite_results(k: &str) -> Vec<String> {
    let mut results: Vec<String> = cell_rewrites(k)
        .iter()
        .map(|rewrite| rewrite.result.to_owned())
        .collect();
    let mut at = 0;
    while let Some(open) = k[at..].find('<').map(|open| open + at) {
        at = open + 1;
        let tag = &k[open + 1..];
        if !tag.starts_with(|c: char| c.is_ascii_alphabetic()) {
            continue;
        }
        let name = &tag[..tag.find(['>', ' ']).unwrap_or(tag.len())];
        for content in k_cells(&k[open..], name).into_iter().take(1) {
            if let Some((_, result)) = split_rewrite(content) {
                results.push(result.to_owned());
            }
        }
    }
    results
}

/// Ruling 1's checks on a recorded K sentence as a whole: `_` never in a result (c), and a
/// whole-cell rewrite (d) that keeps its cell's children, in order, and the subject's frame.
fn sentence_frames(k: &str) -> Vec<String> {
    let mut found = Vec::new();
    for result in rewrite_results(k) {
        if all_tokens(&result).any(|token| token == "_") {
            found.push(format!("a `_` in the result `{result}`"));
        }
    }
    for rewrite in cell_rewrites(k) {
        let inside = |side: &str| {
            k_cells(side, rewrite.cell)
                .first()
                .copied()
                .unwrap_or_default()
                .to_owned()
        };
        let cell = format!("<{}", rewrite.cell);
        if !rewrite.subject.starts_with(&cell) || !rewrite.result.starts_with(&cell) {
            continue;
        }
        let (subject, result) = (inside(rewrite.subject), inside(rewrite.result));
        if child_cells(&subject) != child_cells(&result) {
            found.push(format!(
                "a rewrite of `<{}>` whose result writes the children {:?}, its subject {:?}",
                rewrite.cell,
                child_cells(&result),
                child_cells(&subject)
            ));
        }
        if top_level_frame(&subject) && !top_level_frame(&result) {
            found.push(format!(
                "a rewrite of `<{}>` whose result drops its subject's frame",
                rewrite.cell
            ));
        }
    }
    found
}

/// Whether a K text writes the cell `cell`: its tag, or a variable or `_` of its cell sort
/// (`V0:OgroupCell`, `_:OgroupCell`).
fn writes_cell(k: &str, cell: &str) -> bool {
    let mut letters = cell.chars();
    let sort = letters.next().map_or_else(String::new, |first| {
        format!("{}{}Cell", first.to_uppercase(), letters.as_str())
    });
    k_cells(k, cell).len() + usize::from(container(k, cell).is_some()) > 0
        || all_tokens(k).any(|token| token.split_once(':').is_some_and(|(_, of)| of == sort))
}

/// The presence half of check 6 (S5.0g item 3a fixes, ruling 5; P5, P0): a subject's `Some(..)`
/// on a `?` cell tests that the cell is present, so its K writes the cell, or a variable or `_`
/// of the cell's sort, on the subject side; a bare untyped `_` there names no cell and tests
/// nothing. A subject's `None` tests that it is absent, so where the result writes the cell the
/// K creates it: the subject side writes no such cell.
fn presence_frame(entry: &EntryCase, subject: &str, result: &str) -> Option<String> {
    let entry = &entry.entry;
    if entry.side != Side::Subject || entry.stack.first() != Some(&Layer::Optional) {
        return None;
    }
    let spelling = match &entry.spelling {
        Spelling::Alias(_, inner) => inner,
        other => other,
    };
    let cell = entry.cell.as_str();
    match spelling {
        Spelling::Present(_) if !writes_cell(subject, cell) => Some(format!(
            "its subject `Some(..)` on the `?` cell `{cell}` writes no `<{cell}>` and no variable \
             of its sort, so the rule tests no presence"
        )),
        Spelling::Missing if writes_cell(result, cell) && writes_cell(subject, cell) => {
            Some(format!(
                "its subject `None` on the `?` cell `{cell}` writes the cell on the subject side, \
                 so the result does not create it"
            ))
        }
        _ => None,
    }
}

/// P6 read off one K content root for an entry's root on `side` (ruling 1): whether the K keeps a
/// frame exactly where the root keeps the rest. `content` is the cell's content as `side` reads
/// it, `subject` and `result` the content of each side of its rewrite, `places` how many texts
/// they are (1 for a cell no rewrite writes). A frame is `...` in the cell (a), which frames both
/// sides of a rewrite inside it, a kept rest variable (b), or on the subject a `_` at the
/// content's top level (c).
/// A subject's `..` or `name @ ..` matches the unwritten rest, so its side has a frame; an exact
/// subject has none. A result's `..` keeps the subject's rest, and `..name` keeps it only where
/// `name` is that rest (`own_rest`, [`puts_own_rest_back`]); any other `..name` moves a list in,
/// which replaces the content exactly, as an exact result does. An initializer's value is
/// complete.
fn frame_agrees(
    side: Side,
    root: &class_matrix::cells_oracle::Root,
    own_rest: impl Fn(&str) -> bool,
    content: &str,
    (subject, result): (&str, &str),
    sentence: &str,
    places: usize,
) -> Result<(), String> {
    use class_matrix::cells_oracle::Root;
    let dots = content.split_whitespace().any(|token| token == "...");
    let kept = kept_rest(subject, result, sentence, places);
    let framed = match side {
        Side::Subject => {
            dots || kept || top_tokens(subject).contains(&"_") || unused_rest(subject, sentence)
        }
        Side::Result => dots || kept,
        _ => dots,
    };
    let keeps = match (side, root) {
        (Side::Subject, Root::Rest(Rest::Anon | Rest::Named(_)))
        | (Side::Result, Root::Rest(Rest::Anon)) => true,
        (Side::Result, Root::Rest(Rest::Splice(name))) => own_rest(name),
        (Side::Initializer, _) | (_, Root::Rest(_) | Root::Exact) => false,
        // A whole binder that nothing reads matches every content, which K writes `...` alone;
        // otherwise a whole binder or a value writes no rest, and frames nothing.
        (Side::Subject, Root::Whole) if content.trim() == "..." => return Ok(()),
        (_, Root::Whole | Root::Value) => {
            return if dots {
                Err("a frame `...`".to_owned())
            } else {
                Ok(())
            };
        }
    };
    match (keeps, framed) {
        (true, false) => Err("no frame".to_owned()),
        (false, true) => Err("a frame".to_owned()),
        _ => Ok(()),
    }
}

/// P6 for a result's `..name` at `cell`'s content root: whether it puts back this cell's own
/// rest, the one `subject` (the subject's entry of the result's top cell, read by its `stack`)
/// names `name @ ..` at the same content root. Only then does the result keep the cell's rest,
/// and its K a frame there. A `..name` that names any other binding, another cell's rest
/// included, moves that list in: the cell's content is then replaced exactly.
fn puts_own_rest_back(
    cell: &str,
    (top, stack): (&str, &[Layer]),
    subject: Option<&Spelling>,
    name: &str,
) -> bool {
    use class_matrix::cells_oracle::{Root, root};
    let mut roots = Vec::new();
    if let Some(subject) = subject {
        content_roots(top, stack, subject, &mut roots);
    }
    roots
        .iter()
        .any(|(at, spelling)| at == cell && root(spelling) == Root::Rest(Rest::Named(name.into())))
}

/// Check 6 (P6 in the recorded K, independent of classes): every accepted cell-entry case with
/// recorded K keeps a frame in its K exactly where its entry's content roots keep the rest, and
/// exactly where its records and instance sequences keep the fields and instances they do not
/// name ([`record_frames_agree`], S5.0g review R8). The
/// K is the product's, recorded by `--record`; this judges it against the principle, so a
/// lowering that keeps a rest an exact entry does not write (S5-D2's) or drops one a `..` keeps
/// fails here, whatever the row's class.
///
/// An entry means the K it lowers to, so the frame is judged by that meaning, not its spelling
/// (S5.0g item 3a fixes, ruling 1, P0): at a content root, `...` (a), a rest variable kept at the
/// same place on both sides and used nowhere else (b), `_` in a subject (c), each read on the
/// side of a whole-cell rewrite `(<c> L </c> => <c> R </c>)` the entry is on (d). `_` in a result
/// and a whole-cell rewrite that drops a child or its subject's frame are refused
/// ([`sentence_frames`]).
#[test]
fn check_6_the_recorded_k_keeps_a_frame_exactly_where_p6_says() {
    use class_matrix::cells_oracle::root;
    let mut failures = Vec::new();
    let mut counts = BTreeMap::<&str, usize>::new();
    for (case, entry) in ENTRIES.iter() {
        let Some(Expected::Accept(accepted)) = EXPECTED.get(&case.id) else {
            continue;
        };
        let Some(k) = accepted.k.as_deref() else {
            *counts.entry("accepted, no K recorded").or_default() += 1;
            continue;
        };
        // The case's own sentence (or configuration) is the K text's first paragraph; the base's
        // sentences follow it.
        let k = k.trim_start().split("\n\n").next().unwrap_or_default();
        for found in sentence_frames(k) {
            failures.push(format!("{}: {found}", case.id));
        }
        let (subject_view, result_view) = (side_view(k, false), side_view(k, true));
        if let Some(found) = presence_frame(entry, &subject_view, &result_view) {
            failures.push(format!("{}: {found}", case.id));
        }
        let view = if entry.entry.side == Side::Result {
            &result_view
        } else {
            &subject_view
        };
        // Records are judged on the whole text, as before the views: a created instance's
        // `...` takes its template's defaults, which no side view reads.
        record_frames_agree(case, entry, k, &mut failures, &mut counts);
        let mut roots = Vec::new();
        content_roots(
            &entry.entry.cell,
            &entry.entry.stack,
            &entry.entry.spelling,
            &mut roots,
        );
        if roots.is_empty() {
            *counts.entry("accepted, no content root").or_default() += 1;
            continue;
        }
        let mut cells = BTreeMap::<&str, Vec<&Spelling>>::new();
        for (cell, spelling) in &roots {
            cells.entry(cell.as_str()).or_default().push(spelling);
        }
        for (cell, spellings) in cells {
            let contents = k_cells(view, cell);
            let (subjects, results) = (k_cells(&subject_view, cell), k_cells(&result_view, cell));
            if contents.len() != spellings.len() {
                failures.push(format!(
                    "{}: the entry writes {} content roots of `{cell}`, its K has {} cells \
                     `<{cell}>` on its side",
                    case.id,
                    spellings.len(),
                    contents.len(),
                ));
                continue;
            }
            // A cell a whole-cell rewrite creates (`.Bag => <c> .. </c>`) or deletes has one
            // side only; the other has no content.
            let paired = subjects.len() == results.len();
            // A cell no whole-cell rewrite holds is one text on both sides.
            let in_rewrite = k_cells(k, cell).len() != subjects.len();
            for (at, (spelling, content)) in spellings.into_iter().zip(contents).enumerate() {
                *counts.entry("content roots judged").or_default() += 1;
                let (subject, result) = if paired {
                    (subjects[at], results[at])
                } else if entry.entry.side == Side::Result {
                    ("", content)
                } else {
                    (content, "")
                };
                let subject = split_rewrite(subject).map_or(subject, |(left, _)| left);
                let result = split_rewrite(result).map_or(result, |(_, right)| right);
                let places = if in_rewrite || split_rewrite(content).is_some() {
                    2
                } else {
                    1
                };
                let top = (entry.entry.cell.as_str(), &entry.entry.stack[..]);
                let subject_of = entry.context.other.as_ref();
                if let Err(found) = frame_agrees(
                    entry.entry.side,
                    &root(spelling),
                    |name| puts_own_rest_back(cell, top, subject_of, name),
                    content,
                    (subject, result),
                    k,
                    places,
                ) {
                    failures.push(format!(
                        "{}: `<{cell}> {content} </{cell}>` has {found}, where P6 says the \
                         content root {:?} on the {:?} side {}",
                        case.id,
                        root(spelling),
                        entry.entry.side,
                        if found == "no frame" {
                            "keeps the rest"
                        } else {
                            "keeps none"
                        }
                    ));
                }
            }
        }
    }
    println!("{counts:#?}");
    assert!(failures.is_empty(), "{failures:#?}");
}

/// Check 6's reading of a result's `..name` (S5-N1, P6), on both shapes: the cell's own rest put
/// back keeps the rest, so its K needs a frame; another cell's rest moved in replaces the
/// content exactly, so its K has none, and `...` there is refused.
#[test]
fn a_result_splice_keeps_the_rest_only_where_it_names_the_cells_own() {
    use class_matrix::cells_oracle::root;
    let optional = [Layer::Optional, Layer::Leaf(Notation::List)];
    let read = |text: &str| {
        probed_as(
            &Probe {
                form: Form::Cells,
                side: Side::Result,
                path: &[],
                stack: &optional,
                text,
                other: None,
                written: false,
                bound: &[],
                records: &[],
                elsewhere: false,
            }
            .read(text),
        )
    };
    let result = read("Some(k::configuration::Cell([..r]))");
    let own = read("Some(k::configuration::Cell([x, r @ ..]))");
    let moved = read("Some(k::configuration::Cell(old))");
    let top = ("olist", &optional[..]);
    assert!(puts_own_rest_back("olist", top, Some(&own), "r"));
    assert!(!puts_own_rest_back("olist", top, Some(&moved), "r"));
    assert!(!puts_own_rest_back("olist", top, None, "r"));
    assert!(!puts_own_rest_back("olist", top, Some(&own), "s"));
    assert!(!puts_own_rest_back("stack", top, Some(&own), "r"));
    let judge = |subject: Option<&Spelling>, content: &str, sides: (&str, &str), k: &str| {
        frame_agrees(
            Side::Result,
            &root(&result),
            |name: &str| puts_own_rest_back("olist", top, subject, name),
            content,
            sides,
            k,
            2,
        )
    };
    // The own rest: `<olist> ListItem(V0) V1:List => V1:List </olist>` keeps `V1`; without it,
    // the K has no frame.
    let kept = "<olist> ListItem(V0) V1:List => V1:List </olist>";
    assert_eq!(
        judge(
            Some(&own),
            "ListItem(V0) V1:List => V1:List",
            ("ListItem(V0) V1:List", "V1:List"),
            kept
        ),
        Ok(())
    );
    assert_eq!(
        judge(
            Some(&own),
            "ListItem(V0) V1:List => .List",
            ("ListItem(V0) V1:List", ".List"),
            "<olist> ListItem(V0) V1:List => .List </olist>"
        ),
        Err("no frame".to_owned())
    );
    // Another cell's rest: `<olist> V2:List => V1:List </olist>` is exact; `...` is a frame.
    let moved_k = "<stack> ListItem(V0) V1:List => ListItem(V0) </stack> \
                   <olist> V2:List => V1:List </olist>";
    assert_eq!(
        judge(
            Some(&moved),
            "V2:List => V1:List",
            ("V2:List", "V1:List"),
            moved_k
        ),
        Ok(())
    );
    assert_eq!(
        judge(
            Some(&moved),
            "V2:List => V1:List ...",
            ("V2:List", "V1:List ..."),
            &moved_k.replace("V1:List </olist>", "V1:List ... </olist>")
        ),
        Err("a frame".to_owned())
    );
}

/// A record-level frame an entry writes (P6, records follow Rust): a group or instance record's
/// cell, whose K content keeps a top-level `...` exactly where the record keeps the rest, and an
/// instance sequence's collection, whose K keeps the other instances exactly where it writes a
/// rest.
#[derive(Debug)]
enum RecordFrame {
    /// A record of the group the cell holds (the cell's own group, or one instance's), with the
    /// children it does not name.
    Record {
        cell: String,
        keeps: bool,
        unnamed: Vec<String>,
    },
    /// The instances of a collection, of which `records` are records.
    Instances {
        cell: String,
        keeps: bool,
        records: usize,
    },
}

/// Every record frame an entry's spelling writes, below presence and through the children of
/// the records it writes. On a subject a record's `..` (or `..base`) matches the fields it does
/// not name; on a result an update `..label` keeps them and a created instance's `..` takes its
/// template's, K's `...` alike, while a bare `..` after every child keeps none (the exact
/// record); an initializer's value is complete, so it writes none.
fn record_frames(
    cell: &str,
    side: Side,
    stack: &[Layer],
    spelling: &Spelling,
    out: &mut Vec<RecordFrame>,
) {
    let spelling = match spelling {
        Spelling::Alias(_, inner) => inner,
        other => other,
    };
    let keeps = |rest: bool| rest && side != Side::Initializer;
    // A built record whose bare `..` follows every child keeps nothing: the `..` leaves no
    // field for Rust's defaults, and the record is the exact one (P6, P0).
    let record_keeps = |group: &Group, record: &Record| {
        let vacuous = side == Side::Result
            && record.rest == RecordRest::Open
            && record.fields.len() == group.children.len();
        !vacuous && keeps(record.rest != RecordRest::Exact)
    };
    let record = |group: &Group, item: &Spelling| match item {
        Spelling::Alias(_, inner) => match &**inner {
            Spelling::Record(record) | Spelling::Fragment(record) if record.head == group.name => {
                Some(record.clone())
            }
            _ => None,
        },
        Spelling::Record(record) | Spelling::Fragment(record) if record.head == group.name => {
            Some(record.clone())
        }
        _ => None,
    };
    let unnamed = |group: &Group, record: &Record| {
        group
            .children
            .iter()
            .filter(|(child, _)| !record.fields.iter().any(|(name, _)| name == child))
            .map(|(child, _)| child.clone())
            .collect()
    };
    let fields = |group: &Group, record: &Record, out: &mut Vec<RecordFrame>| {
        for (name, value) in &record.fields {
            if let Some((_, child)) = group.children.iter().find(|(child, _)| child == name) {
                record_frames(name, side, child, value, out);
            }
        }
    };
    match (stack, spelling) {
        ([Layer::Optional, rest @ ..], Spelling::Present(inner) | Spelling::Absent(inner)) => {
            record_frames(cell, side, rest, inner, out);
        }
        ([Layer::Group(group), ..], _) => {
            if let Some(found) = record(group, spelling) {
                out.push(RecordFrame::Record {
                    cell: cell.to_owned(),
                    keeps: record_keeps(group, &found),
                    unnamed: unnamed(group, &found),
                });
                fields(group, &found, out);
            }
        }
        (
            [Layer::Instances(_), Layer::Group(group), ..],
            Spelling::Brackets(seq)
            | Spelling::Braces(seq)
            | Spelling::InstList(seq)
            | Spelling::InstSet(seq),
        ) => {
            let mut records = 0;
            for item in &seq.items {
                if let Some(found) = record(group, item) {
                    records += 1;
                    out.push(RecordFrame::Record {
                        cell: cell.to_owned(),
                        keeps: record_keeps(group, &found),
                        unnamed: unnamed(group, &found),
                    });
                    fields(group, &found, out);
                }
            }
            out.push(RecordFrame::Instances {
                cell: cell.to_owned(),
                keeps: keeps(seq.rest.is_some()),
                records,
            });
        }
        _ => {}
    }
}

/// Whether a K cell content has `...` at its own top level, outside every cell nested in it.
fn top_level_frame(content: &str) -> bool {
    let mut depth = 0_usize;
    let mut top = String::new();
    let mut rest = content;
    while let Some(at) = rest.find('<') {
        let (before, tag) = rest.split_at(at);
        if depth == 0 {
            top.push_str(before);
            top.push(' ');
        }
        let closing = tag.starts_with("</");
        let opening = tag[1..].starts_with(|c: char| c.is_ascii_alphabetic());
        let Some(end) = tag.find('>').filter(|_| closing || opening) else {
            if depth == 0 {
                top.push('<');
            }
            rest = &tag[1..];
            continue;
        };
        if closing {
            depth = depth.saturating_sub(1);
        } else {
            depth += 1;
        }
        rest = &tag[end + 1..];
    }
    if depth == 0 {
        top.push_str(rest);
    }
    top.split(|c: char| c.is_whitespace() || matches!(c, '(' | ')'))
        .any(|token| token == "...")
}

/// The cell that holds the first `<cell>` of a K text, if the text writes it.
fn container<'k>(k: &'k str, cell: &str) -> Option<&'k str> {
    let open = format!("<{cell}");
    let at = k
        .match_indices(&open)
        .find(|(at, _)| k[at + open.len()..].starts_with(['>', ' ']))?
        .0;
    let mut stack = Vec::new();
    let mut rest = &k[..at];
    while let Some(start) = rest.find('<') {
        let tag = &rest[start + 1..];
        let Some(end) = tag.find(['>', ' ']) else {
            break;
        };
        match tag.strip_prefix('/') {
            Some(name) => {
                let name = &name[..name.find('>').unwrap_or(name.len())];
                if stack.last() == Some(&name) {
                    stack.pop();
                }
            }
            None if tag.starts_with(|c: char| c.is_ascii_alphabetic()) => stack.push(&tag[..end]),
            None => {}
        }
        rest = &tag[end..];
    }
    stack.last().copied()
}

/// Check 6's record half (S5.0g review R8): `failures` gains every record frame of `entry`
/// whose recorded K keeps a frame where P6 says none or none where it says one; `counts` the
/// judged and the unjudged (a cell the K writes more often than the entry, such as a result's
/// instance beside the subject's, or a collection with no instance record to find it by).
fn record_frames_agree(
    case: &Case,
    entry: &EntryCase,
    k: &str,
    failures: &mut Vec<String>,
    counts: &mut BTreeMap<&'static str, usize>,
) {
    let mut frames = Vec::new();
    record_frames(
        &entry.entry.cell,
        entry.entry.side,
        &entry.entry.stack,
        &entry.entry.spelling,
        &mut frames,
    );
    let mut records = BTreeMap::<&str, Vec<(bool, &[String])>>::new();
    for frame in &frames {
        match frame {
            RecordFrame::Record {
                cell,
                keeps,
                unnamed,
            } => {
                records
                    .entry(cell.as_str())
                    .or_default()
                    .push((*keeps, unnamed.as_slice()));
            }
            RecordFrame::Instances {
                cell,
                keeps,
                records,
            } => {
                if *records == 0 {
                    *counts
                        .entry("instance frames unjudged (no record)")
                        .or_default() += 1;
                    continue;
                }
                *counts.entry("instance frames judged").or_default() += 1;
                let holds_frame = match container(k, cell) {
                    Some(holder) => k_cells(k, holder)
                        .first()
                        .is_some_and(|content| top_level_frame(content)),
                    // Unwritten, the collection's other instances are framed by K's
                    // configuration abstraction.
                    None => true,
                };
                if holds_frame != *keeps {
                    failures.push(format!(
                        "{}: the instances of `{cell}` {} the other instances in K, where P6 says \
                         the instance sequence {}",
                        case.id,
                        if holds_frame { "frame" } else { "do not frame" },
                        if *keeps {
                            "keeps them"
                        } else {
                            "names every instance"
                        }
                    ));
                }
            }
        }
    }
    for (cell, wanted) in records {
        let contents = k_cells(k, cell);
        if contents.len() != wanted.len() {
            *counts
                .entry("record frames unjudged (K writes the cell more often)")
                .or_default() += wanted.len();
            continue;
        }
        for ((keeps, unnamed), content) in wanted.into_iter().zip(contents) {
            *counts.entry("record frames judged").or_default() += 1;
            // Ruling 1 (c): on a subject, a child the record does not name written `_` as its
            // whole content matches that child unconstrained; a record whose every unnamed child
            // is so written (none, where it names every child) keeps the rest it does not name.
            let has_frame = top_level_frame(content)
                || (keeps
                    && entry.entry.side == Side::Subject
                    && unnamed.iter().all(|child| {
                        let found = k_cells(content, child);
                        found.len() == 1 && found[0] == "_"
                    }));
            if has_frame != keeps {
                failures.push(format!(
                    "{}: `<{cell}> {content} </{cell}>` has {} at its top level, where P6 says \
                     the record {}",
                    case.id,
                    if has_frame {
                        "a frame `...`"
                    } else {
                        "no frame"
                    },
                    if keeps {
                        "keeps the fields it does not name"
                    } else {
                        "names every field"
                    }
                ));
            }
        }
    }
}

/// With `KRS_CELLS_ROWS=FILE`, write each kinds-base and sweep case's ID, its sentence's answer
/// ([`ANSWERS`]), its rule-level class, and where the answer is met (`entry`: the case's own
/// entry; `item`: another entry of the sentence) to FILE (S5.0g's rows come from the oracle, and
/// the generated table diff is reviewed).
#[test]
fn the_kinds_cases_outcomes_print_on_request() {
    let Some(file) = std::env::var_os("KRS_CELLS_ROWS") else {
        return;
    };
    let mut out = String::new();
    for (case, entry) in ENTRIES.iter() {
        if !matches!(case.base, Base::Kinds | Base::Sweep | Base::SweepPaths) {
            continue;
        }
        let (got, own) = ANSWERS[&case.id];
        let rule = if got.admits() {
            entry.rule_outcome(got)
        } else {
            None
        };
        let _ = writeln!(
            out,
            "{}\t{}\t{}\t{}",
            case.id,
            sweep_name(got),
            rule.unwrap_or("-"),
            if own { "entry" } else { "item" }
        );
    }
    std::fs::write(file, out).expect("the rows file is written");
}

/// With `KRS_CELLS_CASE=GLOB`, print the rendered item of each case the glob selects, for review.
#[test]
fn the_cases_items_print_on_request() {
    let Some(glob) = std::env::var_os("KRS_CELLS_CASE") else {
        return;
    };
    let glob = Glob::parse(&glob.to_string_lossy()).expect("KRS_CELLS_CASE is a glob");
    for case in CASES.iter().filter(|case| glob.matches(&case.id)) {
        println!("## {}\n{}", case.id, case.item());
    }
}

/// S5.0g item 3b ruling 1 (P6): `..base` updates a record, so its base is a record of the
/// update's own constructor matched by the sentence. Where the subject shows no instance
/// labelled `me`, a base the sentence binds elsewhere to a record of the update's constructor
/// creates an instance; one bound to no record (a list element, a leaf value) or to another
/// constructor's record has none (`record-update-base`). Ruling 2 (P5 with P1): a subject's
/// `None` on a `?` child of a group or instance record tests the child absent, which K does
/// only by creating it, so the result's same child must be present, at every depth.
#[test]
fn a_base_is_a_record_of_its_constructor_and_a_child_absence_test_needs_creation() {
    let threads = children_stack("* List of T");
    let group = children_stack("group O");
    let Layer::Group(o) = &group[0] else {
        unreachable!("`group O` is a group");
    };
    let accounts = [Layer::Instances(Order::Map), Layer::Group(o.clone())];
    let update = |form, text, records| Probe {
        form,
        side: Side::Result,
        path: &[],
        stack: &threads,
        text,
        other: Some("[..]"),
        written: false,
        bound: &["x", "me"],
        records,
        elsewhere: false,
    };
    let subject = |stack, text, other| Probe {
        form: Form::Readable,
        side: Side::Subject,
        path: &[],
        stack,
        text,
        other,
        written: other.is_some(),
        bound: &[],
        records: &[],
        elsewhere: false,
    };
    let admitted = Outcome::Admit { lint: None };
    let base = Outcome::Refuse("record-update-base");
    let absent = Outcome::Refuse("absence-test-without-creation");
    let readable = "[T { k: [x], ..me }, ..]";
    let cells = "[k::fragment![crate::T { k: [x], ..me }], ..]";
    probes_agree(&[
        (
            update(Form::Readable, readable, &[("me", "T")]),
            Outcome::After,
        ),
        (update(Form::Cells, cells, &[("me", "T")]), Outcome::After),
        (update(Form::Readable, readable, &[]), base),
        (update(Form::Cells, cells, &[]), base),
        (update(Form::Readable, readable, &[("me", "Job")]), base),
        (update(Form::Cells, cells, &[("me", "Job")]), base),
        (subject(&group, "O { o: None, n: x }", None), absent),
        (
            subject(&group, "O { o: None, n: x }", Some("O { o: None, n: x }")),
            absent,
        ),
        (
            subject(
                &group,
                "O { o: None, n: x }",
                Some("O { o: Some(1), n: x }"),
            ),
            admitted,
        ),
        (
            subject(&accounts, "{ O { n: x, o: None }, .. }", None),
            absent,
        ),
        (
            subject(
                &accounts,
                "{ O { n: x, o: None }, .. }",
                Some("{ O { n: x, o: Some(1) }, .. }"),
            ),
            absent,
        ),
        (
            subject(
                &accounts,
                "{ me @ O { n: x, o: None }, .. }",
                Some("{ O { o: Some(1), ..me }, .. }"),
            ),
            admitted,
        ),
        (
            subject(
                &accounts,
                "{ me @ O { n: x, o: None }, .. }",
                Some("{ O { n: 1, ..me }, .. }"),
            ),
            absent,
        ),
    ]);
}

/// P5 at a cell's own root as at a child (S5.3 part 3): a subject `None` the result writes over
/// with `None` creates nothing, so the absence test has no creation; only a result `Some(..)`
/// creates the cell. No generated case has the shape.
#[test]
fn a_root_absence_test_needs_the_result_to_create_the_cell() {
    let absent = Outcome::Refuse("absence-test-without-creation");
    let admitted = Outcome::Admit { lint: None };
    let optional = [Layer::Optional, Layer::Leaf(Notation::Plain)];
    let root = |form, text, other| Probe {
        form,
        side: Side::Subject,
        path: &[],
        stack: &optional,
        text,
        other: Some(other),
        written: true,
        bound: &[],
        records: &[],
        elsewhere: false,
    };
    probes_agree(&[
        (root(Form::Readable, "None", "None"), absent),
        (root(Form::Cells, "None", "None"), absent),
        (root(Form::Readable, "None", "Some(1)"), admitted),
        (
            root(Form::Cells, "None", "Some(k::configuration::Cell(1))"),
            admitted,
        ),
    ]);
}
