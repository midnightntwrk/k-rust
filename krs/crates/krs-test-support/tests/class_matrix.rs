//! The class-test generator: every base expands, every case's ranges name its construct, the
//! shipped table and red list parse, and the table, PENDING, and invariant rules decide as
//! documented.

use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;
use std::path::Path;

use krs_diagnostic::codes::CodeKind;
use krs_expand::whole_file::{self, ExpandDiagnostic, FileExpansion, FileRequest, Selection};
use krs_test_support::class_matrix::advice::{UNCHECKED, Unchecked, listed_forms, unchecked_drift};
use krs_test_support::class_matrix::attributes::Written;
use krs_test_support::class_matrix::findings::{
    FINDINGS_FILE, FindingKind, Findings, Owner, Red, RedKind, Summary, audit,
};
use krs_test_support::class_matrix::invariants::{
    FORWARDED_RUSTC, Observed, ObservedDiagnostic, Severity, Violation, front_stops_at_rustc_parse,
    registry_kind, signature, violations, without_rustc_parse_error,
};
use krs_test_support::class_matrix::oracle::{Class, Outcome, Refusal, Stage, admits};
use krs_test_support::class_matrix::pending::{
    Judgement, Observation, Pending, UNASSIGNED, case_of,
};
use krs_test_support::class_matrix::positions::{
    Construct, Entry, Form, Kind, Notation, Opening, Position, Slot as Part,
};
use krs_test_support::class_matrix::table::{
    self as table, Accepted, At, Expected, Glob, MistakeClass, TERM_ACCEPTS_FILE, Table, TableError,
};
use krs_test_support::class_matrix::{
    self, Base, Case, FRONT_CASE_CAP, Family, OwnReason, Packaging, Placed, entry_points, render,
};

fn expand(source: &str) -> Result<FileExpansion, Vec<ExpandDiagnostic>> {
    let module_path = vec!["krs_class_case".to_owned()];
    whole_file::expand_file(&FileRequest {
        display_file: "src/lib.rs",
        source,
        generated_file: "/work/expanded/class-case/src/lib.rs",
        facade_alias: "k",
        facade_path: syn::parse_str("::k").expect("the facade path parses"),
        module_path: &module_path,
        selection: &Selection::WholeFile,
    })
}

fn read_class_matrix(file: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/class-matrix")
        .join(file);
    std::fs::read_to_string(&path).unwrap_or_else(|error| panic!("{}: {error}", path.display()))
}

#[test]
fn every_base_preamble_expands() {
    for base in Base::ALL {
        let preamble = base.preamble();
        if let Err(diagnostics) = expand(&preamble) {
            panic!("the {base:?} base does not expand: {diagnostics:#?}\n{preamble}");
        }
    }
}

/// A single-body rule must rewrite something, so the `local-rule` template carries a rewrite of
/// its own: with a plain construct in the hole, the case is accepted, and a refusal can only be
/// about the construct.
#[test]
fn the_local_rule_template_is_accepted_around_a_plain_construct() {
    let cases = class_matrix::cases();
    for id in [
        "terms/local-rule/subject/x",
        "import/local-rule/subject/Go()",
    ] {
        let case = cases
            .iter()
            .find(|case| case.id == id)
            .unwrap_or_else(|| panic!("{id} is generated"));
        let rendered = case.render();
        if let Err(diagnostics) = expand(&rendered.source) {
            panic!("{id} does not expand: {diagnostics:#?}");
        }
    }
}

#[test]
fn the_case_count_per_family_is_pinned_and_capped() {
    let cases = class_matrix::cases();
    let mut counts = BTreeMap::new();
    for case in &cases {
        *counts.entry(case.family).or_insert(0) += 1;
    }
    assert_eq!(
        counts,
        BTreeMap::from([
            // 7 kinds × 13 spellings × 2 sides, 8 typed cells × 4 contents × 2 sides, the kinds
            // base's 15 stacks × 9 marks (S5.0g), and its listed cases: a group named with its
            // child, the 2-child group record written whole and naming one child on each side,
            // `Some(_)` in a result, and (readable only) a rule that writes no cell.
            (Family::Readable, 182 + 64 + 15 * 9 + 7),
            (Family::Claim, 182 + 64 + 15 * 9 + 6),
            // 7 kinds × (13 subject + 13 result spellings), the kinds base's 15 stacks × 9
            // marks, S5-F1's result fragment with a bare `..` (and its machine-base twin on the
            // one-child group), and the 2-child group's fragment naming one child on each side.
            (Family::Cells, 182 + 15 * 9 + 2 + 2),
            // 7 kinds × 19 values, the computation cell's remainder, 3 field orders and the
            // nested group's, the optional cell declared `initial` written present, the 4 main-cell
            // shapes × 3 forms of a sentence that names no cell, 8 typed cells × 4 contents, and
            // the typed `stmt` written after it starts, and the kinds base's 15 stacks × 10
            // initializer marks.
            (Family::Init, 133 + 1 + 3 + 1 + 1 + 4 * 3 + 32 + 1 + 15 * 10),
            // (81 positions of depth 1 + 25 positions constructs open) × 51 constructs, the alias
            // roots' slots each splitting their position's constructs with a twin by whether they
            // read `x`, 3 elements in each static subject's set concatenation, and 2 spellings
            // reading an initializer's configuration variable in a `let` body; the 2 static
            // productions' applications at the 35 matched slots of depth 1 below a subject's
            // root; the 2 values a framed `cells!` result map writes at one key twice, the 2 it
            // writes over a map the subject binds whole, and the 2 keys it writes over a framed
            // map's remainder; and in the static subjects (NT-14), each of the desugar's and the
            // alias's, the 17 spellings that stand there only, the 20 witnesses a rule of the
            // case's own writes, the 2 a typed parameter binds (the desugar's), the 8 spellings
            // at a constructor's argument and at an alias's pattern, and 5 at an alternative;
            // and the 8 keys an equation's function context and a context alias look up each, the
            // 2 conditions of a `cells!` rule that restates its cells, and the list brackets at a
            // fn's `List` subject (NT-18); and the 4 spellings a desugar's subject holds beside a
            // second clause of its production (NT-22: two names that overlap it, two terms that do
            // not); and the 2 Bool spellings a desugar's result holds below `Cmd::When`, whose
            // rule's condition reads it, and the 3 subjects of `k::matches!(HOLE, _)` there, in a
            // rule's guard and at a rule's result, the static result's twin (NT-42).
            (
                Family::Terms,
                106 * 51
                    + 3 * 2
                    + 2
                    + 35 * 2
                    + 2
                    + 2
                    + 2
                    + 2 * (17 + 20 + 2 * 8 + 5)
                    + 2
                    + 8 * 2
                    + 2
                    + 1
                    + 4
                    + 2
                    + 3 * 3,
            ),
            // 95 slots of depth 1 (an alias root's twin is a slot of its own, and a desugar's
            // subject beside a second clause one too) × 2 bare variants.
            (Family::Import, 95 * 2),
            // The term family's 106 positions × (6 collection notation forms and their calls, and
            // 8 collection literals and the 7 calls they denote apart from the method's), and a
            // set's singleton as the witness a rule of the case's own writes, at each static
            // subject.
            (Family::Notation, 106 * (12 + 15) + 2),
            // 18 forms × 26 attributes, 26 malformed attributes, 21 extra cases, and 4 pairs of a key
            // and a helper.
            (Family::Attributes, 18 * 26 + 26 + 21 + 4),
            // The readable records and the `cells!` rules on the run base, and the Set collection's
            // spellings: 7 subject (a map literal with an anonymous rest among them) and 5 result
            // spellings in a readable record, 6 and 5 in a `cells!` rule; and 8 map results over a
            // framed `cells!` subject (finding NT-9-1).
            (Family::ReadableRun, 182 + 7 + 5),
            (Family::CellsRun, 182 + 6 + 5 + 8),
            // The compiled sweep (S5.0g item 3a): the 4,008 root cells of the cells oracle's
            // sweep, less the 15 no case can be compiled for (`sweep::unbuilt`) and the 434
            // another family's case already writes in the same form, side, stack, spelling and
            // subject entry.
            (Family::Sweep, 4_008 - 15 - 434),
        ])
    );
    for shard in class_matrix::FRONT_SHARDS {
        let count = cases
            .iter()
            .filter(|case| shard.contains(&case.family))
            .count();
        assert!(count <= FRONT_CASE_CAP, "{shard:?}: {count}");
    }
}

/// The fast tier's shards partition the families: each family's cases run in exactly one test.
#[test]
fn every_family_is_in_exactly_one_shard_of_the_fast_tier() {
    for family in Family::ALL {
        let shards = class_matrix::FRONT_SHARDS
            .iter()
            .filter(|shard| shard.contains(&family))
            .count();
        assert_eq!(shards, 1, "{family:?} is in {shards} shards");
    }
}

#[test]
fn ids_are_spelled_from_the_axes_and_commands_are_unique() {
    let cases = class_matrix::cases();
    let mut commands = BTreeSet::new();
    for case in &cases {
        assert!(
            case.id.starts_with(&format!("{}/", case.family.name())),
            "{} does not start with its family",
            case.id
        );
        assert!(
            case.id.ends_with(&format!("/{}", case.construct)),
            "{} does not end with its construct",
            case.id
        );
        // A construct holds a `/` only as the division operator, spaced (`x / 2`), and an
        // opener's name holds no space: an ID's segments before its construct are read by
        // taking the construct off its end, never by splitting at its last `/`.
        assert!(
            !case.construct.replace(" / ", " ").contains('/'),
            "{} holds a `/` that is no spaced operator",
            case.id
        );
        if let Some(command) = case.command() {
            assert!(
                commands.insert(command.name.clone()),
                "{} repeats the command {}",
                case.id,
                command.name
            );
        }
        if let Packaging::Own(reason) = &case.packaging {
            assert_eq!(
                *reason == OwnReason::Initializer,
                case.replaces_initializer(),
                "{}",
                case.id
            );
        }
    }
}

/// Check a placed case's ranges: they nest, the item is the case's item, and the spelling is
/// the construct (an attribute's `TAG` written as the case's tag), except for a field-order case,
/// whose construct names the order and whose spelling is the whole field list, or the nested
/// group's.
fn assert_placed(source: &str, placed: &Placed<'_>) {
    let case = placed.case;
    assert_eq!(&source[placed.item.clone()], case.item(), "{}", case.id);
    assert!(
        placed.item.start <= placed.entry.start
            && placed.entry.start <= placed.spelling.start
            && placed.spelling.end <= placed.entry.end
            && placed.entry.end <= placed.item.end,
        "{}: the spelling, entry and item ranges do not nest",
        case.id
    );
    let written = &source[placed.spelling.clone()];
    if case.id.starts_with("init/order/") {
        let (separator, declared) = if case.base == Base::Nested {
            (", ", &["aux", "ret"][..])
        } else {
            (
                ",\n",
                &["counter", "env", "frame", "k", "pc", "queue", "stack"][..],
            )
        };
        let mut cells = written
            .split(separator)
            .map(|field| field.trim().split_once(':').expect("a field").0)
            .collect::<Vec<_>>();
        cells.sort_unstable();
        assert_eq!(cells, declared, "{}", case.id);
    } else if let Some(pair) = case.attribute {
        // A production's key is written on the case's command: its spelling is the clause's
        // marker.
        let spelled = match pair.written() {
            Written::Production(_) => format!("#[k::{}]", pair.form().marker),
            other => other.text().replace("TAG", &case.tag()),
        };
        assert_eq!(written, spelled, "{}", case.id);
    } else {
        assert_eq!(written, case.construct, "{}", case.id);
    }
    // The initial base's case writes its construct, `initial`, in a cell's declaration.
    if case.kind.is_some() && case.base != Base::Initial {
        let entry = &source[placed.entry.clone()];
        assert!(
            entry.ends_with(&format!(": {}", case.construct)),
            "{}: the entry {entry:?} is not `CELL: construct`",
            case.id
        );
    }
}

#[test]
fn every_case_alone_places_its_construct() {
    for case in &class_matrix::cases() {
        let rendered = case.render();
        assert_eq!(rendered.cases.len(), 1);
        assert_placed(&rendered.source, &rendered.cases[0]);
    }
}

#[test]
fn the_shared_cases_of_a_base_render_as_one_package() {
    let cases = class_matrix::cases();
    for base in Base::ALL {
        let shared = cases
            .iter()
            .filter(|case| case.base == base && matches!(case.packaging, Packaging::Shared(_)))
            .collect::<Vec<&Case>>();
        if matches!(
            base,
            Base::Nested | Base::Initial | Base::MainCell | Base::MainK
        ) {
            // Its only case is an initializer, rendered alone.
            assert!(shared.is_empty(), "{base:?} has no shared case");
            continue;
        }
        assert!(!shared.is_empty(), "{base:?} has shared cases");
        let rendered = render(&shared);
        assert_eq!(rendered.cases.len(), shared.len());
        for placed in &rendered.cases {
            assert_placed(&rendered.source, placed);
            let command = placed.case.command().expect("the case is shared");
            assert_eq!(
                rendered
                    .source
                    .matches(&format!("] {} ", command.name))
                    .count()
                    + rendered
                        .source
                        .matches(&format!("] {}()", command.name))
                        .count(),
                1,
                "{} declares its command once",
                placed.case.id
            );
        }
    }
}

#[test]
#[should_panic(expected = "a case that is not shared is rendered alone")]
fn a_computation_subject_case_is_never_batched() {
    let cases = class_matrix::cases();
    let own = cases
        .iter()
        .find(|case| case.packaging == Packaging::Own(OwnReason::ComputationSubject))
        .expect("a computation-subject case is generated");
    let other = cases
        .iter()
        .find(|case| case.base == own.base && matches!(case.packaging, Packaging::Shared(_)))
        .expect("a shared case is generated");
    let _ = render(&[own, other]);
}

/// The term cases a table rule decides before the oracle's resolution refusal, with the oracle's
/// class ([`the_shipped_table_and_red_list_parse`]).
/// The notation family's positions where a table rule decides every case before the oracle's
/// resolution refusal, with the oracle's class: each of the family's spellings (the collection
/// notation and the calls it denotes) that reads `x` and applies a function
/// ([`reads_x_and_applies`]), as `k::builtin::int::add(x, 1)` does at the term family's same
/// positions ([`OVERRIDDEN`]).
const OVERRIDDEN_POSITIONS: [(&str, &str); 7] = [
    ("notation/constant/value", "constant-applies-function"),
    ("notation/constant/value-root", "constant-applies-function"),
    ("notation/local-rule/subject-root", "function-in-pattern"),
    (
        "notation/readable/map-key/matches-pattern",
        "function-in-pattern",
    ),
    ("notation/rule/guard/matches-pattern", "function-in-pattern"),
    ("notation/rule/subject/or-branch", "function-in-pattern"),
    (
        "notation/sort-rule/result/matches-pattern",
        "function-in-pattern",
    ),
];

/// Whether a case's spelling reads the name `x` and applies a function at its root, as every
/// notation spelling but the values (`map![]`, `set![x]`, their calls) and the ground map
/// (`map![0 -> 1]`, whose overrides [`OVERRIDDEN`] lists) does ([`OVERRIDDEN_POSITIONS`]).
fn reads_x_and_applies(case: &Case) -> bool {
    let Some(term) = case.term.as_ref() else {
        return false;
    };
    // The case's own nodes: a depth-2 case's outer construct opens the position it stands in.
    let mut own = term.nodes.iter().filter(|node| !node.outer);
    let root = own.next();
    let reads_x = root
        .into_iter()
        .chain(own)
        .any(|node| node.construct == Construct::Reference);
    let value = root.is_some_and(|root| {
        matches!(
            root.construct,
            Construct::Constructor
                | Construct::CollectionValue
                | Construct::Notation(Notation::CollectionValue)
        )
    });
    reads_x && !value
}

const OVERRIDDEN: [(&str, &str); 76] = [
    (
        "import/alias/subject-root-binding/Go()",
        "static-clause-root-not-marked",
    ),
    (
        "import/alias/subject-root/Hold(x)",
        "static-clause-root-not-marked",
    ),
    (
        "notation/context/subject-root/k::builtin::map::update(k::builtin::map::empty(), 0, 1)",
        "function-in-pattern",
    ),
    (
        "notation/context/subject-root/map![0 -> 1]",
        "function-in-pattern",
    ),
    (
        "notation/local-rule/subject-root/k::builtin::map::update(k::builtin::map::empty(), 0, 1)",
        "function-in-pattern",
    ),
    (
        "notation/local-rule/subject-root/map![0 -> 1]",
        "function-in-pattern",
    ),
    (
        "terms/alias/subject-root-binding/x",
        "static-clause-root-not-marked",
    ),
    (
        "terms/cells-local/subject/k::builtin::int::add(x, 1)",
        "function-in-pattern",
    ),
    (
        "terms/cells/item-root/k::builtin::int::add(x, 1)",
        "function-in-pattern",
    ),
    (
        "terms/cells/map-key/beside-fresh/!(x < 1)",
        "function-in-pattern",
    ),
    (
        "terms/cells/map-key/beside-fresh/-(x + 1)",
        "function-in-pattern",
    ),
    (
        "terms/cells/map-key/beside-fresh/k::builtin::int::add(x, 1)",
        "function-in-pattern",
    ),
    (
        "terms/cells/map-key/beside-fresh/x % 2",
        "function-in-pattern",
    ),
    (
        "terms/cells/map-key/beside-fresh/x & 1",
        "function-in-pattern",
    ),
    (
        "terms/cells/map-key/beside-fresh/x && true",
        "function-in-pattern",
    ),
    (
        "terms/cells/map-key/beside-fresh/x + 1",
        "function-in-pattern",
    ),
    (
        "terms/cells/map-key/beside-fresh/x / 2",
        "function-in-pattern",
    ),
    (
        "terms/cells/map-key/beside-fresh/x < 1",
        "function-in-pattern",
    ),
    (
        "terms/cells/map-key/beside-fresh/x << 1",
        "function-in-pattern",
    ),
    (
        "terms/cells/map-key/beside-fresh/x == 1",
        "function-in-pattern",
    ),
    (
        "terms/cells/map-key/beside-fresh/x >> 1",
        "function-in-pattern",
    ),
    (
        "terms/cells/map-key/beside-fresh/x || true",
        "function-in-pattern",
    ),
    (
        "terms/cells/map-key/beside-fresh/x.add::<Int>(1)",
        "function-in-pattern",
    ),
    (
        "terms/cells/map-value/k::builtin::int::add(x, 1)",
        "function-in-pattern",
    ),
    (
        "terms/cells/subject/k::builtin::int::add(x, 1)",
        "function-in-pattern",
    ),
    (
        "terms/constant/value-root/Size(x)",
        "constant-applies-function",
    ),
    (
        "terms/constant/value-root/k::builtin::int::add(x, 1)",
        "constant-applies-function",
    ),
    (
        "terms/constant/value-root/k::map![x -> 1]",
        "constant-applies-function",
    ),
    (
        "terms/constant/value-root/map![x -> 1]",
        "constant-applies-function",
    ),
    ("terms/constant/value/Size(x)", "constant-applies-function"),
    (
        "terms/constant/value/k::builtin::int::add(x, 1)",
        "constant-applies-function",
    ),
    (
        "terms/constant/value/k::map![x -> 1]",
        "constant-applies-function",
    ),
    (
        "terms/constant/value/map![x -> 1]",
        "constant-applies-function",
    ),
    (
        "terms/context-alias/item-root/k::builtin::int::add(x, 1)",
        "function-in-pattern",
    ),
    (
        "terms/context-alias/subject/k::builtin::int::add(x, 1)",
        "function-in-pattern",
    ),
    (
        "terms/context/subject-root/k::builtin::int::add(1, 2)",
        "function-in-pattern",
    ),
    (
        "terms/desugar/result-root/Cmd::Go() | Cmd::Hold(_)",
        "alternatives-outside-pattern",
    ),
    (
        "terms/desugar/result/Cmd::Go() | Cmd::Hold(_)",
        "alternatives-outside-pattern",
    ),
    (
        "terms/desugar/subject-root/[x, ..]",
        "static-clause-root-not-marked",
    ),
    (
        "terms/desugar/subject-root/x",
        "static-clause-root-not-marked",
    ),
    (
        "terms/desugar/subject-root/x | 1",
        "static-clause-root-not-marked",
    ),
    (
        "terms/desugar/subject/[x, ..]",
        "collection-in-static-subject",
    ),
    (
        "terms/equation/subject-root/[x, ..]",
        "equation-root-not-function",
    ),
    (
        "terms/equation/subject-root/x",
        "equation-root-not-function",
    ),
    (
        "terms/equation/subject-root/x | 1",
        "equation-root-not-function",
    ),
    (
        "terms/local-rule/subject-root/Size(x)",
        "function-in-pattern",
    ),
    (
        "terms/local-rule/subject-root/k::builtin::int::add(1, 2)",
        "function-in-pattern",
    ),
    (
        "terms/local-rule/subject-root/k::builtin::int::add(x, 1)",
        "function-in-pattern",
    ),
    (
        "terms/local-rule/subject-root/k::map![x -> 1]",
        "function-in-pattern",
    ),
    (
        "terms/local-rule/subject-root/map![x -> 1]",
        "function-in-pattern",
    ),
    (
        "terms/readable/map-key-child/Cmd::Pair { a: x, ..x }",
        "record-update-in-pattern",
    ),
    (
        "terms/readable/map-value-child/Cmd::Pair { a: x, ..x }",
        "record-update-in-pattern",
    ),
    (
        "terms/readable/map-key/matches-pattern/Size(x)",
        "function-in-pattern",
    ),
    (
        "terms/readable/map-key/matches-pattern/k::builtin::int::add(x, 1)",
        "function-in-pattern",
    ),
    (
        "terms/readable/map-key/matches-pattern/k::map![x -> 1]",
        "function-in-pattern",
    ),
    (
        "terms/readable/map-key/matches-pattern/map![x -> 1]",
        "function-in-pattern",
    ),
    (
        "terms/rule/guard/closure-body/Cmd::Pair { a: x, ..x }",
        "ml-in-condition",
    ),
    (
        "terms/rule/guard/matches-pattern/Size(x)",
        "function-in-pattern",
    ),
    (
        "terms/rule/guard/matches-pattern/k::builtin::int::add(x, 1)",
        "function-in-pattern",
    ),
    (
        "terms/rule/guard/matches-pattern/k::map![x -> 1]",
        "function-in-pattern",
    ),
    (
        "terms/rule/guard/matches-pattern/map![x -> 1]",
        "function-in-pattern",
    ),
    (
        "terms/rule/subject/or-branch/Size(x)",
        "function-in-pattern",
    ),
    (
        "terms/rule/subject/or-branch/k::builtin::int::add(x, 1)",
        "function-in-pattern",
    ),
    (
        "terms/rule/subject/or-branch/k::map![x -> 1]",
        "function-in-pattern",
    ),
    (
        "terms/rule/subject/or-branch/map![x -> 1]",
        "function-in-pattern",
    ),
    (
        "terms/simplification/subject-root/[x, ..]",
        "simplification-root-not-function",
    ),
    (
        "terms/simplification/subject-root/x",
        "simplification-root-not-function",
    ),
    (
        "terms/sort-rule/result/matches-pattern/Size(x)",
        "function-in-pattern",
    ),
    (
        "terms/sort-rule/result/matches-pattern/k::builtin::int::add(x, 1)",
        "function-in-pattern",
    ),
    (
        "terms/sort-rule/result/matches-pattern/k::map![x -> 1]",
        "function-in-pattern",
    ),
    (
        "terms/sort-rule/result/matches-pattern/map![x -> 1]",
        "function-in-pattern",
    ), // A collection's value as a context's whole subject (decision NT-11-2), where the table
    // refuses the context whose hole the subject does not bind, or list brackets at a `KItem`
    // position, first.
    ("terms/context/subject-root/[x, ..]", "function-in-pattern"),
    (
        "notation/context/subject-root/k::builtin::map::empty()",
        "function-in-pattern",
    ),
    (
        "notation/context/subject-root/k::builtin::set::empty()",
        "function-in-pattern",
    ),
    (
        "notation/context/subject-root/map![]",
        "function-in-pattern",
    ),
    (
        "notation/context/subject-root/set![]",
        "function-in-pattern",
    ),
];

#[test]
fn the_shipped_table_and_red_list_parse() {
    let table = Table::parse_with_term_accepts(
        &read_class_matrix("expected.toml"),
        &read_class_matrix(TERM_ACCEPTS_FILE),
    )
    .unwrap_or_else(|errors| panic!("expected.toml: {errors:#?}"));
    let pending = Pending::parse(&read_class_matrix("pending.toml"))
        .unwrap_or_else(|errors| panic!("pending.toml: {errors:#?}"));
    let cases = class_matrix::cases();
    let ids = cases
        .iter()
        .map(|case| case.id.as_str())
        .collect::<Vec<_>>();
    let resolution = table.resolve_cases(&cases, registry_kind);
    // The table decides every case exactly once.
    assert!(resolution.errors.is_empty(), "{:#?}", resolution.errors);
    // A rule overrides the oracle's resolution refusal only where the case also makes a name or
    // sort mistake, which is met first: an unbound `x` (in a constant, at a root, where a bare
    // name names a unit constructor), a `k::matches!` pattern that rebinds `x`, alternatives that
    // bind other names, a `KItem` binder an operand sorts as `Int`, `_` in a desugar result
    // without `unbound_variables`, a record update's base, brackets at a `KItem` root, a name an
    // alias clause's subject binds and its result does not use.
    let positions = cases.iter().filter_map(|case| {
        let position = case.id.strip_suffix(&format!("/{}", case.construct))?;
        if case.family != Family::Notation || !reads_x_and_applies(case) {
            return None;
        }
        OVERRIDDEN_POSITIONS
            .iter()
            .find(|(overridden, _)| *overridden == position)
            .map(|(_, class)| (case.id.clone(), *class))
    });
    assert_eq!(
        resolution.overridden,
        OVERRIDDEN
            .into_iter()
            .map(|(id, class)| (id.to_owned(), class))
            .chain(positions)
            .collect::<BTreeMap<_, _>>()
    );
    assert_eq!(resolution.expected.len(), ids.len());
    // K5's entries name mutations, which are no cases of the table.
    let mutations = entry_points::mutations();
    let mut named = ids.clone();
    named.extend(mutations.iter().map(|mutation| mutation.id.as_str()));
    assert!(pending.stale(&named).is_empty());

    // Every red has a registered owner, and its computed kind is one its finding's kind admits.
    let findings = Findings::parse(&read_class_matrix(FINDINGS_FILE))
        .unwrap_or_else(|errors| panic!("{FINDINGS_FILE}: {errors:#?}"));
    let red = |key: &str, entry: &krs_test_support::class_matrix::pending::PendingEntry| {
        let expected = case_of(key).and_then(|case| resolution.expected.get(case));
        Red::of(key, &entry.deviation, expected, registry_kind)
    };
    let errors = audit(&findings, &pending, red);
    assert!(
        errors.is_empty(),
        "{FINDINGS_FILE} against pending.toml:\n{}",
        errors.join("\n")
    );
    let mut summary = Summary::default();
    for (key, entry) in &pending.entries {
        summary.add(
            red(key, entry),
            &entry.finding,
            &findings.owner_name(&entry.finding, key),
        );
    }
    eprintln!("pending.toml: {} reds, {summary}", pending.entries.len());
}

/// A red's kind is computed from its key, its deviation and the table's expectation of its case,
/// the internal flag from the codes its deviation names (in any of its errors), and the panic flag
/// from the panic it records (in any test); a finding's kind admits it or not.
#[test]
fn the_kind_of_a_red_is_computed_from_its_entry() {
    let (class, accepted) = expectations();
    let refuse = Expected::Refuse {
        name: "wrong-shape",
        class: &class,
        at: At::Spelling,
    };
    let accept = Expected::Accept(&accepted);
    let red = |key: &str, deviation: &str, expected: &Expected<'_>| {
        Red::of(key, deviation, Some(expected), registry_kind)
    };
    // The kinds, computed from the key, the deviation and the table's expectation.
    let internal = INTERNAL;
    // The flags of a red: whether its deviation names an internal code, and whether it panicked.
    let (none, coded) = ((false, false), (true, false));
    for (key, deviation, expected, kind, (is_internal, is_panic)) in [
        ("terms/a", "accepted", &refuse, RedKind::UnderRefusal, none),
        (
            "full/terms/a",
            "accepted",
            &refuse,
            RedKind::UnderRefusal,
            none,
        ),
        (
            "terms/a",
            "krs::analysis::invalid-term @ item",
            &refuse,
            RedKind::Diagnostic,
            none,
        ),
        // An internal code only in a second error is the case's still.
        (
            "terms/a",
            "krs::analysis::invalid-term @ spelling; krs::emit::unsupported-shape @ item",
            &refuse,
            RedKind::Diagnostic,
            coded,
        ),
        ("terms/a", internal, &accept, RedKind::OverRefusal, coded),
        ("terms/a", "accepted", &accept, RedKind::OtherK, none),
        (
            "terms/a",
            "accepted, without the lint no-effect-entry",
            &accept,
            RedKind::LintMissing,
            none,
        ),
        (
            "terms/a",
            "accepted, with the lint no-effect-entry, which the table does not owe",
            &accept,
            RedKind::LintUnowed,
            none,
        ),
        (
            "k3/terms/a",
            "printed surface refused: krs::emit::unsupported-shape @ unlocated",
            &accept,
            RedKind::K3,
            coded,
        ),
        ("k7/terms/a", "not applied", &accept, RedKind::K7, none),
        ("k8/terms/a", "advises", &refuse, RedKind::K8, none),
        (
            "lattice/class-x/a~b/c",
            "1 pairs",
            &accept,
            RedKind::K4,
            none,
        ),
        ("entry/k::rule", "2 errors", &accept, RedKind::K5, none),
    ] {
        assert_eq!(
            red(key, deviation, expected),
            Red {
                kind,
                internal: is_internal,
                panicked: is_panic,
                rust_syntax: false,
            },
            "{key}: {deviation}"
        );
    }

    let under = red("terms/a", "accepted", &refuse);
    assert_eq!(under.to_string(), "under-refusal");
    assert_eq!(
        red("terms/a", internal, &accept).to_string(),
        "over-refusal+internal"
    );
    assert!(under.admits(FindingKind::Bug) && !under.admits(FindingKind::Generator));
    assert!(!red("terms/a", internal, &refuse).admits(FindingKind::Diagnostic));
    assert!(!red("k7/terms/a", "d", &accept).admits(FindingKind::Diagnostic));
    assert!(red("k7/terms/a", "d", &accept).admits(FindingKind::Generator));
    assert!(red("k8/terms/a", "d", &refuse).admits(FindingKind::Diagnostic));
}

/// A K2 red that is a Rust parser's error, where the table's class for the case has another code
/// or the table accepts it, is tagged `+rust-syntax`, so the family is one count in a summary; a
/// class whose code is the parser's, and another test's red, are not.
#[test]
fn a_rust_parse_error_where_a_class_stands_is_tagged() {
    let (class, accepted) = expectations();
    let refuse = Expected::Refuse {
        name: "wrong-shape",
        class: &class,
        at: At::Spelling,
    };
    let parser_class = MistakeClass {
        code: "krs::syntax::rust-syntax".to_owned(),
        ..class.clone()
    };
    let refuse_by_parser = Expected::Refuse {
        name: "map-read-in-result",
        class: &parser_class,
        at: At::Spelling,
    };
    let accept = Expected::Accept(&accepted);
    let red = |key: &str, expected: &Expected<'_>| {
        Red::of(
            key,
            "krs::syntax::rust-syntax @ spelling",
            Some(expected),
            registry_kind,
        )
    };
    assert_eq!(
        red("terms/a", &refuse).to_string(),
        "diagnostic+rust-syntax"
    );
    assert_eq!(
        red("terms/a", &accept).to_string(),
        "over-refusal+rust-syntax"
    );
    assert_eq!(red("terms/a", &refuse_by_parser).to_string(), "diagnostic");
    assert_eq!(red("k8/terms/a", &refuse).to_string(), "k8");
    assert!(red("terms/a", &refuse).admits(FindingKind::Diagnostic));
}

/// A red that records a panic is a bug in every test: K2's signature writes it as its part
/// `panic`, after the errors or alone, and the other tests as `panic: MESSAGE` or `panicked`. A
/// K2 red of a case the table does not decide is the generator's.
#[test]
fn a_panic_is_a_bug_and_an_undecided_case_the_generators() {
    let (class, accepted) = expectations();
    let refuse = Expected::Refuse {
        name: "wrong-shape",
        class: &class,
        at: At::Spelling,
    };
    let accept = Expected::Accept(&accepted);
    for (key, deviation, expected, kind) in [
        (
            "terms/a",
            "krs::analysis::invalid-term @ spelling; panic",
            &refuse,
            RedKind::Diagnostic,
        ),
        ("terms/a", "panic", &accept, RedKind::OverRefusal),
        (
            "k3/terms/a",
            "printed surface refused: krs expand panicked: `r#_` cannot be a raw identifier",
            &accept,
            RedKind::K3,
        ),
        (
            "k6/terms/a",
            "uncoded: a check worker panicked",
            &accept,
            RedKind::K6,
        ),
        (
            "k7/terms/a",
            "counter-witness `go`: panic: a message",
            &accept,
            RedKind::K7,
        ),
        ("k8/terms/a", "panic: a message", &refuse, RedKind::K8),
    ] {
        let red = Red::of(key, deviation, Some(expected), registry_kind);
        assert_eq!(
            red,
            Red {
                kind,
                internal: false,
                panicked: true,
                rust_syntax: false,
            },
            "{key}: {deviation}"
        );
        assert!(
            red.admits(FindingKind::Bug)
                && [
                    FindingKind::Feature,
                    FindingKind::Diagnostic,
                    FindingKind::Generator
                ]
                .into_iter()
                .all(|kind| !red.admits(kind)),
            "{key}: {deviation}"
        );
    }
    assert_eq!(
        Red::of(
            "k8/terms/a",
            "panic: a message",
            Some(&refuse),
            registry_kind
        )
        .to_string(),
        "k8+panic"
    );
    let uncovered = Red::of("terms/a", "accepted", None, registry_kind);
    assert_eq!(uncovered.kind, RedKind::Uncovered);
    assert!(
        uncovered.admits(FindingKind::Generator)
            && !uncovered.admits(FindingKind::Bug)
            && !uncovered.admits(FindingKind::Diagnostic)
    );
}

/// An internal code, as a deviation names it.
const INTERNAL: &str = "krs::emit::unsupported-shape @ spelling";

/// A refusal's class and an accept entry, for the table's expectations of a red's case.
fn expectations() -> (MistakeClass, Accepted) {
    (
        MistakeClass {
            code: "krs::analysis::invalid-term".to_owned(),
            doc: String::new(),
            proposed: false,
            advice: Vec::new(),
            examples: Vec::new(),
        },
        Accepted {
            k: None,
            same_k_as: Vec::new(),
            lint: None,
        },
    )
}

/// A registry of three findings: a bug with an under-refusal's risk and a K3 owner of its own, a
/// diagnostic, and a kept limit.
const REGISTRY: &str = r#"
["A"]
owner = "NT-28"
kind = "bug"
what = "an under-refusal, with its risk"
risk = "KRS writes K the spelling does not say"
by_test = { k3 = "NT-30" }

["B"]
owner = "S5"
kind = "diagnostic"
what = "a misplaced site"

["C"]
owner = "kept: D4"
kind = "feature"
what = "a kept limit"
"#;

/// The audit of `pending` against [`REGISTRY`]: a key ending `refused` is a case the table
/// refuses, one ending `uncovered` a case it does not decide, any other a case it accepts.
fn audited(pending: &str) -> Vec<String> {
    let findings = Findings::parse(REGISTRY).unwrap_or_else(|errors| panic!("{errors:#?}"));
    let (class, accepted) = expectations();
    let refuse = Expected::Refuse {
        name: "wrong-shape",
        class: &class,
        at: At::Spelling,
    };
    let accept = Expected::Accept(&accepted);
    let pending = Pending::parse(pending).unwrap_or_else(|errors| panic!("{errors:#?}"));
    audit(&findings, &pending, |key, entry| {
        let expected = if key.ends_with("uncovered") {
            None
        } else if key.ends_with("refused") {
            Some(&refuse)
        } else {
            Some(&accept)
        };
        Red::of(key, &entry.deviation, expected, registry_kind)
    })
}

/// A pending entry's body.
fn entry(finding: &str, deviation: &str) -> String {
    format!("finding = \"{finding}\"\ndeviation = \"{deviation}\"\n")
}

/// A red list on which [`REGISTRY`] holds every finding, each with an entry of its kind.
fn sound() -> String {
    format!(
        "[\"terms/refused\"]\n{}\n[\"k3/terms/a\"]\n{}\n[\"terms/b/refused\"]\n{}\n[\"terms/c\"]\n{}",
        entry("A", "accepted"),
        entry("A", "printed surface refused"),
        entry("B", "krs::analysis::invalid-term @ item"),
        entry("C", "krs::analysis::invalid-term @ spelling"),
    )
}

/// Each `(pending, fragments)`: the audit of `pending` fails with every fragment.
fn assert_audit_fails(cases: &[(String, Vec<&str>)]) {
    for (pending, fragments) in cases {
        let errors = audited(pending);
        for fragment in fragments {
            assert!(
                errors.iter().any(|error| error.contains(fragment)),
                "{fragment:?} missing from {errors:#?}"
            );
        }
    }
}

/// The registry's audit fails on each way a red loses its owner or hides its kind: an
/// unregistered finding, a finding with no entry left (and a `by_test` owner with none), an
/// under-refusal or an internal code under a finding that is not a bug, a red of what KRS ran
/// under a diagnostic, and an under-refusal with no stated risk.
#[test]
fn the_findings_registry_owns_every_red_by_its_kind() {
    let sound = sound();
    // Every finding holds an entry of its kind: no failure.
    assert_eq!(audited(&sound), Vec::<String>::new());
    // Each failure, forced: its message names the fix.
    let stale = format!(
        "[\"terms/refused\"]\n{}\n[\"terms/b/refused\"]\n{}",
        entry("A", "accepted"),
        entry("B", "krs::analysis::invalid-term @ item"),
    );
    assert_audit_fails(&[
        (
            format!("{sound}\n[\"terms/d\"]\n{}", entry("D", "accepted")),
            vec!["terms/d: its finding \"D\" is not in findings.toml"],
        ),
        (
            stale,
            vec![
                "C: no pending entry is left under it: it is done",
                "A: by_test gives its k3 entries an owner, but none is left",
            ],
        ),
        (
            format!("{sound}\n[\"terms/e/refused\"]\n{}", entry("B", INTERNAL)),
            vec![
                "terms/e/refused: a red of kind diagnostic+internal under B, a diagnostic finding",
            ],
        ),
        (
            format!("{sound}\n[\"k7/terms/e\"]\n{}", entry("B", "not applied")),
            vec!["k7/terms/e: a red of kind k7 under B, a diagnostic finding"],
        ),
        (
            format!(
                "{sound}\n[\"terms/j\"]\n{}",
                entry("C", "accepted, with other K than recorded")
            ),
            vec!["C holds an under-refusal or other K than the table's: state its risk"],
        ),
        (
            format!("{sound}\n[\"terms/f/refused\"]\n{}", entry("C", "accepted")),
            vec![
                "terms/f/refused: a red of kind under-refusal under C, a feature finding",
                "C holds an under-refusal or other K than the table's: state its risk",
            ],
        ),
    ]);
}

/// The audit also sees a bug where it hides: an internal code in the second error only, and a
/// panic after an author code, under a diagnostic finding; an undecided case's red under any
/// kind but `generator`; and an owner's statements that no entry bears out: a finding whose
/// every entry `by_test` owns, and a risk on a finding that holds no under-refusal.
#[test]
fn the_findings_registry_sees_a_bug_where_it_hides() {
    let sound = sound();
    let through_by_test = format!(
        "[\"k3/terms/a\"]\n{}\n[\"terms/b/refused\"]\n{}\n[\"terms/c\"]\n{}",
        entry("A", "printed surface refused"),
        entry("B", "krs::analysis::invalid-term @ item"),
        entry("C", "krs::analysis::invalid-term @ spelling"),
    );
    assert_audit_fails(&[
        (
            format!(
                "{sound}\n[\"terms/g/refused\"]\n{}",
                entry(
                    "B",
                    "krs::analysis::invalid-term @ spelling; krs::emit::unsupported-shape @ item"
                )
            ),
            vec![
                "terms/g/refused: a red of kind diagnostic+internal under B, a diagnostic finding",
            ],
        ),
        (
            format!(
                "{sound}\n[\"terms/h/refused\"]\n{}",
                entry("B", "krs::analysis::invalid-term @ spelling; panic")
            ),
            vec!["terms/h/refused: a red of kind diagnostic+panic under B, a diagnostic finding"],
        ),
        (
            format!(
                "{sound}\n[\"k3/terms/h\"]\n{}",
                entry(
                    "B",
                    "printed surface refused: krs expand panicked: a message"
                )
            ),
            vec!["k3/terms/h: a red of kind k3+panic under B, a diagnostic finding"],
        ),
        (
            through_by_test,
            vec![
                "A: every entry left is owned through by_test: make NT-30 the finding's owner",
                "A states a risk but holds no under-refusal and no other K: remove the risk",
            ],
        ),
        (
            format!(
                "{sound}\n[\"terms/i/uncovered\"]\n{}",
                entry("C", "accepted")
            ),
            vec![
                "terms/i/uncovered: a red of kind uncovered under C, a feature finding: the table \
                 does not decide the case",
            ],
        ),
    ]);
}

/// K8's unchecked refusals against the reviewed entries: any run fails on advice no entry reviews
/// or one whose entry does not list the shard, however many refusals meet it; only a whole run
/// fails on an entry of the shard no refusal meets, since a filtered run sees a subset.
#[test]
fn a_run_fails_on_unchecked_advice_no_entry_reviews() {
    let reviewed = [
        Unchecked {
            class: "ml-in-condition",
            forms: &["`int::eq`"],
            shards: &["notation", "terms"],
            reason: "r",
        },
        Unchecked {
            class: "sort-test-in-pattern",
            forms: &["`where x: {Sort,Int}`"],
            shards: &["terms"],
            reason: "r",
        },
        Unchecked {
            class: "wildcard-at-subject-root",
            forms: &["`k::rules! \\{ case_*: k::term![*] => *; \\}`"],
            shards: &["terms"],
            reason: "r",
        },
        Unchecked {
            class: "configuration-variable-sort",
            forms: &[
                "`{x,pgm}: {Int,Map}`",
                r"`k::project!({Int,Map}\, {x,pgm})`",
            ],
            shards: &["init"],
            reason: "r",
        },
    ];
    let observed = |pairs: &[(&str, &str, usize)]| {
        pairs
            .iter()
            .map(|(class, forms, count)| (((*class).to_owned(), (*forms).to_owned()), *count))
            .collect::<BTreeMap<_, _>>()
    };
    let drift = |shard, pairs: &[(&str, &str, usize)], whole| {
        unchecked_drift(shard, &observed(pairs), &reviewed, whole)
    };
    let clause = "`k::rules! { case_1: k::term![_] => 1; }`";
    let every = [
        ("ml-in-condition", "`int::eq`", 41),
        ("sort-test-in-pattern", "`where x: Sort`", 70),
        ("sort-test-in-pattern", "`where x: Int`", 4),
        ("wildcard-at-subject-root", clause, 1),
    ];
    // Reviewed advice passes at any count, filtered or whole; a filtered run may see a subset.
    assert_eq!(drift("terms", &every, true), Vec::<String>::new());
    assert_eq!(drift("terms", &every[..1], false), Vec::<String>::new());
    assert_eq!(drift("terms", &[], false), Vec::<String>::new());
    assert_eq!(
        drift("terms", &[("ml-in-condition", "`int::eq`", 400)], false),
        Vec::<String>::new()
    );
    // Advice no entry reviews fails every run: a new class, or new forms of a reviewed class.
    for whole in [false, true] {
        let new = drift("terms", &[("content-sort", "`x: Int`", 1)], whole);
        assert!(
            new.iter().any(|failure| failure.contains(
                "1 refusals of content-sort in the shard terms advise `x: Int`, which no generated case writes and no entry of UNCHECKED"
            )),
            "{new:?}"
        );
        let other = drift("terms", &[("ml-in-condition", "`int::ne`", 2)], whole);
        assert!(
            other
                .iter()
                .any(|failure| failure.contains("advise `int::ne`")),
            "{other:?}"
        );
        // Reviewed advice in a shard its entry does not list.
        let elsewhere = drift(
            "init",
            &[("sort-test-in-pattern", "`where x: Int`", 1)],
            whole,
        );
        assert!(
            elsewhere
                .iter()
                .any(|failure| failure.contains("for the shards [\"terms\"] only: add init to it")),
            "{elsewhere:?}"
        );
    }
    // A whole run fails on an entry of the shard no refusal meets; a filtered run cannot tell.
    let stale = drift("terms", &every[1..], true);
    assert_eq!(
        stale,
        [
            "K8: the UNCHECKED entry of ml-in-condition for `int::eq` lists the shard terms, where no \
          refusal advises it now: drop terms from it, or the entry"
        ]
    );
    assert_eq!(drift("terms", &every[1..], false), Vec::<String>::new());
    assert_eq!(drift("attrs", &[], true), Vec::<String>::new());
}

/// An entry of [`UNCHECKED`] reviews a refusal whose every listed form one of its globs matches
/// alone: a form appended to reviewed advice, or one a glob would match only across a form's
/// backticks, is advice no entry reviews.
#[test]
fn a_reviewed_entry_matches_each_listed_form_alone() {
    let reviewed = [
        Unchecked {
            class: "configuration-variable-sort",
            forms: &[
                "`{x,pgm}: {Int,Map}`",
                r"`k::project!({Int,Map}\, {x,pgm})`",
            ],
            shards: &["init"],
            reason: "r",
        },
        Unchecked {
            class: "wildcard-at-subject-root",
            forms: &["`k::rules! \\{ case_*: k::term![*] => *; \\}`"],
            shards: &["terms"],
            reason: "r",
        },
    ];
    let drift = |shard, pairs: &[(&str, &str, usize)], whole| {
        let observed = pairs
            .iter()
            .map(|(class, forms, count)| (((*class).to_owned(), (*forms).to_owned()), *count))
            .collect::<BTreeMap<_, _>>();
        unchecked_drift(shard, &observed, &reviewed, whole)
    };
    let clause = "`k::rules! { case_1: k::term![_] => 1; }`";
    let narrowed = [
        ("configuration-variable-sort", "`pgm: Map`", 1),
        (
            "configuration-variable-sort",
            "`x: Int`, `k::project!(Int, x)`",
            1,
        ),
    ];
    assert_eq!(drift("init", &narrowed, false), Vec::<String>::new());
    for (class, forms, shard) in [
        (
            "configuration-variable-sort",
            "`x: Int`, `k::is!(Int, x)`",
            "init",
        ),
        (
            "configuration-variable-sort",
            "`drop x`, `pgm: Int`",
            "init",
        ),
        ("configuration-variable-sort", "`k::is!(x): Int`", "init"),
        (
            "wildcard-at-subject-root",
            "`k::rules! { case_1: k::term![_] => 1; }`, `k::absent!(..); }`",
            "terms",
        ),
    ] {
        let failures = drift(shard, &[(class, forms, 1)], false);
        assert!(
            failures
                .iter()
                .any(|failure| failure.contains("no entry of UNCHECKED")),
            "{class} {forms}: {failures:?}"
        );
    }
    assert_eq!(
        drift("terms", &[("wildcard-at-subject-root", clause, 1)], false),
        Vec::<String>::new()
    );
    assert_eq!(
        listed_forms("drop `x`, `k::project!(Int, x)`"),
        ["drop `x`", "`k::project!(Int, x)`"]
    );
    assert!(listed_forms("`x`,`y`").is_empty());
}

/// The reviewed unchecked advice ([`UNCHECKED`]) is well formed: one entry per class and forms,
/// sorted by class, each a class of the table, its forms a glob, its shards case shards, and a
/// reason.
#[test]
fn every_reviewed_unchecked_advice_names_a_class_its_shards_and_a_reason() {
    const CASE_SHARDS: [&str; 9] = [
        "attrs", "cells", "import", "init", "notation", "readable", "runs", "sweep", "terms",
    ];
    let table = Table::parse_with_term_accepts(
        &read_class_matrix("expected.toml"),
        &read_class_matrix(TERM_ACCEPTS_FILE),
    )
    .unwrap_or_else(|errors| panic!("expected.toml: {errors:#?}"));
    let classes = UNCHECKED
        .iter()
        .map(|entry| entry.class)
        .collect::<Vec<_>>();
    let mut sorted = classes.clone();
    sorted.sort_unstable();
    assert_eq!(classes, sorted, "UNCHECKED is sorted by class");
    for entry in UNCHECKED {
        assert!(
            table.classes.contains_key(entry.class),
            "UNCHECKED: {} is no class of expected.toml",
            entry.class
        );
        assert!(
            !entry.forms.is_empty(),
            "UNCHECKED {}: no forms",
            entry.class
        );
        for form in entry.forms {
            Glob::parse(form)
                .unwrap_or_else(|reason| panic!("UNCHECKED {}: {reason}", entry.class));
        }
        assert!(
            !entry.shards.is_empty()
                && entry.shards.iter().all(|shard| CASE_SHARDS.contains(shard))
                && entry.shards.is_sorted(),
            "UNCHECKED {}: {:?} are not sorted case shards (CASE_SHARDS here copies the shard \
             tests of krs-cli/tests/class_matrix.rs: a new shard is added to both)",
            entry.class,
            entry.shards
        );
        assert!(
            !entry.reason.is_empty(),
            "UNCHECKED {}: no reason",
            entry.class
        );
    }
}

/// The registry's own schema: an entry's owner by its test, sorted names, a known owner, kind and
/// test, no placeholder.
#[test]
fn the_findings_registry_follows_its_schema() {
    let findings = Findings::parse(REGISTRY).unwrap_or_else(|errors| panic!("{errors:#?}"));
    assert_eq!(
        findings.owner("A", "k3/terms/x"),
        Some(&Owner::Ticket("NT-30".to_owned()))
    );
    assert_eq!(
        findings.owner("A", "terms/x"),
        Some(&Owner::Ticket("NT-28".to_owned()))
    );
    assert_eq!(
        findings.owner("C", "terms/x"),
        Some(&Owner::Kept("D4".to_owned()))
    );
    let errors = Findings::parse(
        "[\"b\"]\nowner = \"NT-1\"\nkind = \"bug\"\nwhat = \"w\"\n\n\
         [\"a\"]\nowner = \"T9\"\nkind = \"cosmetic\"\nwhat = \"w\"\nby_test = { k9 = \"S5\" }\n\n\
         [\"unassigned\"]\nowner = \"S5\"\nkind = \"bug\"\n",
    )
    .expect_err("the registry is broken");
    for fragment in [
        "\"a\" follows \"b\": keep the findings sorted by name",
        "\"T9\" is no owner",
        "not one of bug, feature, diagnostic, generator",
        "by_test names \"k9\"",
        "the placeholder of a deviation no finding owns",
        "needs an owner, a kind and a what",
    ] {
        assert!(
            errors.iter().any(|error| error.contains(fragment)),
            "{fragment:?} missing from {errors:#?}"
        );
    }
}

/// A run family's case is judged as its twin, the machine-base case of the same slot and spelling,
/// is (`table::twin`): the table expects the same of both, accepted with the same lint and `same_k_as` pairs
/// between twins and the same K (the sentences the case adds, its command written `TAG`, so the run
/// base's driver commands and Set collection change no twin's K), or refused with the same class
/// at the same site.
#[test]
fn every_run_case_is_expected_what_its_twin_is() {
    let table = Table::parse_with_term_accepts(
        &read_class_matrix("expected.toml"),
        &read_class_matrix(TERM_ACCEPTS_FILE),
    )
    .unwrap_or_else(|errors| panic!("expected.toml: {errors:#?}"));
    let cases = class_matrix::cases();
    let resolution = table.resolve_cases(&cases, registry_kind);
    let shape = |expected: &Expected<'_>| match expected {
        Expected::Accept(accepted) => format!(
            "accepted, K {:?}, lint {:?}, same K as {:?}",
            accepted.k,
            accepted.lint,
            accepted
                .same_k_as
                .iter()
                .map(|other| table::twin(other).unwrap_or_else(|| other.clone()))
                .collect::<Vec<_>>()
        ),
        Expected::Refuse { name, at, .. } => format!("refused as {name} at the {at:?}"),
    };
    let mut twins = 0;
    for case in cases.iter().filter(|case| case.family.twin().is_some()) {
        let Some(twin) =
            table::twin(&case.id).filter(|twin| resolution.expected.contains_key(twin))
        else {
            continue;
        };
        twins += 1;
        assert_eq!(
            shape(&resolution.expected[&case.id]),
            shape(&resolution.expected[&twin]),
            "{} and its twin {twin}",
            case.id
        );
    }
    // Every readable record and `cells!` rule of the machine base has its twin.
    assert_eq!(twins, 182 + 182);
}

#[test]
fn each_mutation_breaks_one_header_of_the_base() {
    let mutations = entry_points::mutations();
    assert_eq!(mutations.len(), 53);
    let attributes = mutations
        .iter()
        .filter(|mutation| mutation.id.starts_with("entry/attribute/"))
        .count();
    assert_eq!(attributes, 29);
    for mutation in &mutations {
        assert_ne!(mutation.source, entry_points::BASE, "{}", mutation.id);
        let header = &mutation.source[mutation.header.clone()];
        assert!(
            !header.trim().is_empty(),
            "{}: the header is empty",
            mutation.id
        );
        let (before, after) = (
            &mutation.source[..mutation.header.start],
            &mutation.source[mutation.header.end..],
        );
        assert!(
            entry_points::BASE.starts_with(before) && entry_points::BASE.ends_with(after),
            "{}: the mutation changes only its header",
            mutation.id
        );
    }
    // The whole-file expander refuses the base's inline spec module, so the full tier checks
    // that the base passes `krs check` and `cargo check` cleanly before it judges a mutation.
}

fn table(text: &str) -> Table {
    Table::parse(text).unwrap_or_else(|errors| panic!("{errors:#?}"))
}

/// The full tier compares an accepted case's warnings inside its entry with the lint its row
/// owes both ways: an owed lint no warning reports is missing, and a lint class's warning the row
/// does not owe is unowed (S2: the lint follows its reason, so an over-lint is a red too).
#[test]
fn the_lint_a_case_owes_is_compared_with_its_warnings_both_ways() {
    let table = table(
        r#"
[class.no-effect-entry]
code = "krs::analysis::no-effect-entry"
proposed = true
doc = "a subject entry that constrains nothing"
advice = "none"

[accept."cells/subject/pc/k::configuration::Cell(_)"]
lint = "no-effect-entry"

[accept."cells/subject/pc/k::configuration::Cell(x)"]
"#,
    );
    let owed = &table.accept["cells/subject/pc/k::configuration::Cell(_)"];
    let none = &table.accept["cells/subject/pc/k::configuration::Cell(x)"];
    let entry = 10..20;
    let warned = |code: &str, range: Range<usize>| Observed {
        accepted: true,
        diagnostics: vec![ObservedDiagnostic {
            severity: Severity::Warning,
            code: Some(code.to_owned()),
            kind: None,
            range: Some(range),
            labels: Vec::new(),
            message: "warning".to_owned(),
            help: Vec::new(),
        }],
        panic: None,
    };
    let quiet = Observed {
        accepted: true,
        ..Observed::default()
    };
    let lint = "krs::analysis::no-effect-entry";
    assert_eq!(
        table.lint_deviation(owed, &quiet, &entry),
        Some(table::LintDeviation::Missing("no-effect-entry"))
    );
    assert_eq!(
        table.lint_deviation(owed, &warned(lint, 12..14), &entry),
        None
    );
    // A warning outside the entry is not the entry's.
    assert_eq!(
        table.lint_deviation(owed, &warned(lint, 30..34), &entry),
        Some(table::LintDeviation::Missing("no-effect-entry"))
    );
    assert_eq!(table.lint_deviation(none, &quiet, &entry), None);
    let unowed = table.lint_deviation(none, &warned(lint, 12..14), &entry);
    assert_eq!(
        unowed,
        Some(table::LintDeviation::Unowed("no-effect-entry"))
    );
    // A warning of no lint class's code is no lint.
    assert_eq!(
        table.lint_deviation(none, &warned("krs::analysis::other", 12..14), &entry),
        None
    );
    // The signatures are the deviations the red's kind is computed from.
    let (class, accepted) = expectations();
    let _ = class;
    let kind = |deviation: table::LintDeviation<'_>| {
        Red::of(
            "cells/a",
            &deviation.signature(),
            Some(&Expected::Accept(&accepted)),
            registry_kind,
        )
        .kind
    };
    assert_eq!(kind(unowed.expect("unowed")), RedKind::LintUnowed);
    assert_eq!(
        kind(table::LintDeviation::Missing("no-effect-entry")),
        RedKind::LintMissing
    );
}

const CLASSES: &str = r#"
[class.wrong-shape]
code = "krs::analysis::invalid-term"
doc = "a shape the position does not admit"
advice = "none"

[class.presence]
code = "krs::analysis::optional-presence"
doc = "`Some`/`None` on a plain cell"
advice = "none"
"#;

#[test]
fn globs_match_within_segments_with_alternatives_and_escapes() {
    let glob = |pattern: &str| Glob::parse(pattern).expect("the glob parses");
    assert!(glob("readable/*/pc/x").matches("readable/subject/pc/x"));
    assert!(!glob("readable/*/x").matches("readable/subject/pc/x"));
    assert!(glob("readable/*").matches("readable/"));
    let presence = glob("readable/{subject,result}/pc/{Some(x),None}");
    assert!(presence.matches("readable/result/pc/None"));
    assert!(!presence.matches("readable/guard/pc/None"));
    assert!(
        glob(r"readable/subject/env/\{ y -> x, .. \}")
            .matches("readable/subject/env/{ y -> x, .. }")
    );
    assert!(glob("a/{b,c{d,e}}/*").matches("a/ce/f"));
    assert!(glob("[x, ..]").matches("[x, ..]"));
    for broken in ["a/{b", "a/b}", "a\\"] {
        assert!(Glob::parse(broken).is_err(), "{broken} parses");
    }
}

#[test]
fn the_most_specific_entry_decides_and_ties_are_errors() {
    let ids = [
        "readable/subject/pc/x",
        "readable/subject/pc/Some(x)",
        "readable/result/pc/Some(x)",
        "readable/result/pc/x",
    ];
    let narrowed = table(&format!(
        r#"{CLASSES}
[[refuse]]
match = "readable/*/pc/*"
class = "wrong-shape"
at = "entry"

[[refuse]]
match = "readable/*/pc/Some(x)"
class = "presence"
at = "spelling"

[accept."readable/result/pc/x"]
k = "<pc> _ => X </pc>"
"#
    ));
    let resolution = narrowed.resolve(&ids, |_| None, registry_kind);
    assert!(resolution.errors.is_empty(), "{:#?}", resolution.errors);
    let decided = |id: &str| match resolution.expected[id] {
        Expected::Refuse { class, at, .. } => (class.code.as_str(), Some(at)),
        Expected::Accept(accepted) => (accepted.k.as_deref().unwrap_or_default(), None),
    };
    assert_eq!(
        decided("readable/subject/pc/x"),
        ("krs::analysis::invalid-term", Some(At::Entry))
    );
    assert_eq!(
        decided("readable/result/pc/Some(x)"),
        ("krs::analysis::optional-presence", Some(At::Spelling))
    );
    assert_eq!(decided("readable/result/pc/x"), ("<pc> _ => X </pc>", None));

    // Each glob covers a case the other does not: neither is more specific.
    let tied = table(&format!(
        r#"{CLASSES}
[[refuse]]
match = "readable/subject/*/x"
class = "wrong-shape"
at = "entry"

[[refuse]]
match = "readable/*/pc/x"
class = "presence"
at = "entry"
"#
    ));
    let resolution = tied.resolve(
        &[
            "readable/subject/pc/x",
            "readable/result/pc/x",
            "readable/subject/env/x",
        ],
        |_| None,
        registry_kind,
    );
    assert_eq!(
        resolution.errors,
        vec![TableError::Tie {
            id: "readable/subject/pc/x".to_owned(),
            entries: vec![
                "\"readable/subject/*/x\"".to_owned(),
                "\"readable/*/pc/x\"".to_owned()
            ],
        }]
    );
    assert_eq!(resolution.expected.len(), 2);
}

/// A term case is decided by the oracle's placement refusal, then the table's rules, then the
/// oracle's resolution refusal, then its accept entry; an accept entry never overrides a refusal.
#[test]
fn the_oracle_decides_term_cases_before_and_after_the_rules() {
    let terms = table(
        r#"
[class.wildcard-outside-pattern]
code = "krs::syntax::unsupported-term-expression"
doc = "`_` outside a pattern"
advice = "none"

[class.constant-applies-function]
code = "krs::analysis::invalid-constant"
doc = "a constant that applies a function"
advice = "none"

[class.unbound-name]
code = "krs::expand::unbound-name"
doc = "a name nothing binds"
advice = "none"

[[refuse]]
match = "terms/a/*"
class = "unbound-name"
at = "item"

[[refuse]]
match = "terms/b/z"
class = "wildcard-outside-pattern"
at = "spelling"

[[refuse]]
match = "terms/a/Size(x)"
class = "unbound-name"
at = "item"

[accept."terms/b/x"]
k = "rule X"

[accept."terms/b/z"]
k = "rule Z"
"#,
    );
    let refusal = |class, stage| {
        Some(Outcome::Refuse(Refusal {
            class,
            stage,
            outer: false,
        }))
    };
    let outcome = |id: &str| match id {
        "terms/a/_" | "terms/b/z" => refusal(Class::WildcardOutsidePattern, Stage::Placement),
        "terms/a/Size(x)" | "terms/b/add" => {
            refusal(Class::ConstantAppliesFunction, Stage::Resolution)
        }
        "terms/b/w" => refusal(Class::AliasOutsidePattern, Stage::Placement),
        _ => Some(Outcome::Accept),
    };
    let ids = [
        "terms/a/_",
        "terms/a/Size(x)",
        "terms/b/add",
        "terms/b/x",
        "terms/b/y",
        "terms/b/z",
        "terms/b/w",
    ];
    let resolution = terms.resolve(&ids, outcome, registry_kind);
    let decided = |id: &str| match resolution.expected.get(id) {
        Some(Expected::Refuse { name, at, .. }) => Some((*name, Some(*at))),
        Some(Expected::Accept(accepted)) => Some((accepted.k.as_deref().unwrap_or_default(), None)),
        None => None,
    };
    assert_eq!(
        decided("terms/a/_"),
        Some(("wildcard-outside-pattern", Some(At::Spelling)))
    );
    assert_eq!(
        decided("terms/a/Size(x)"),
        Some(("unbound-name", Some(At::Item)))
    );
    assert_eq!(
        decided("terms/b/add"),
        Some(("constant-applies-function", Some(At::Spelling)))
    );
    assert_eq!(decided("terms/b/x"), Some(("rule X", None)));
    assert_eq!(decided("terms/b/y"), None);
    assert_eq!(
        decided("terms/b/z"),
        Some(("wildcard-outside-pattern", Some(At::Spelling)))
    );
    assert_eq!(decided("terms/b/w"), None);
    assert_eq!(
        resolution.overridden,
        BTreeMap::from([("terms/a/Size(x)".to_owned(), "constant-applies-function")])
    );
    // A rule of an oracle class over a term case is a table error, and so is a rule that decides
    // nothing: `terms/a/*`, whose cases the oracle and a more specific rule decide, and the one
    // over `terms/b/z`, which the oracle refuses first.
    assert_eq!(
        resolution.errors,
        vec![
            TableError::OracleClassRule {
                pattern: "terms/b/z".to_owned(),
                class: "wildcard-outside-pattern".to_owned(),
            },
            TableError::Uncovered {
                id: "terms/b/y".to_owned()
            },
            TableError::AcceptsRefusedCase {
                id: "terms/b/z".to_owned(),
                class: "wildcard-outside-pattern".to_owned(),
            },
            TableError::UnknownOracleClass {
                id: "terms/b/w".to_owned(),
                class: "alias-outside-pattern".to_owned(),
            },
            TableError::ShadowedRule {
                pattern: "terms/a/*".to_owned(),
            },
            TableError::ShadowedRule {
                pattern: "terms/b/z".to_owned(),
            },
        ]
    );
}

/// The oracle reads a subject's root by the form's root role: an equation's and a
/// simplification's root is the function's application, which a value is not.
#[test]
fn the_oracle_reads_a_subject_root_by_its_role() {
    let root = |form| Position::root(form, Part::Subject);
    let refused = |construct, form| admits(construct, root(form)).map(|refusal| refusal.class);
    assert_eq!(
        refused(Construct::Constructor, Form::EquationFn),
        Some(Class::EquationRootNotFunction)
    );
    assert_eq!(
        refused(Construct::Literal, Form::Simplification),
        Some(Class::SimplificationRootNotFunction)
    );
    assert_eq!(
        refused(Construct::FunctionApplication, Form::EquationTable),
        None
    );
    // A builtin operation is no function an equation defines, but a simplification may rewrite
    // its application.
    for form in [Form::EquationFn, Form::EquationTable] {
        assert_eq!(
            refused(Construct::BuiltinApplication, form),
            Some(Class::EquationRootNotFunction)
        );
    }
    assert_eq!(
        refused(Construct::BuiltinApplication, Form::Simplification),
        None
    );
    assert_eq!(refused(Construct::Constructor, Form::RuleFn), None);
    assert_eq!(
        refused(Construct::FunctionApplication, Form::RuleFn),
        Some(Class::FunctionInPattern)
    );
    // Below the root, the same application is one the subject matches.
    let argument = root(Form::EquationFn).enter(Opening::FunctionArgument);
    assert_eq!(
        admits(Construct::FunctionApplication, argument).map(|refusal| refusal.class),
        Some(Class::FunctionInPattern)
    );
    assert_eq!(
        admits(Construct::BuiltinApplication, argument).map(|refusal| refusal.class),
        Some(Class::FunctionInPattern)
    );
    assert_eq!(admits(Construct::Constructor, argument), None);
    // The whole subject of a fn names the production the sentence is written for, which `_`, an
    // alias and an island do not (D3); a `for Sort` clause's root reads as below a constructor.
    for (construct, class) in [
        (Construct::Wildcard, Class::WildcardAtSubjectRoot),
        (Construct::As, Class::AliasAtSubjectRoot),
        (Construct::BytesToken, Class::IslandAtSubjectRoot),
        (Construct::SortTest, Class::IslandAtSubjectRoot),
    ] {
        assert_eq!(refused(construct, Form::RuleFn), Some(class));
        assert_eq!(refused(construct, Form::Context), Some(class));
    }
    for construct in [
        Construct::Reference,
        Construct::Wildcard,
        Construct::As,
        Construct::BytesToken,
    ] {
        assert_eq!(refused(construct, Form::SortRule), None);
    }
    // A static clause's root is the production it expands.
    for construct in [Construct::Constructor, Construct::FunctionApplication] {
        assert_eq!(
            refused(construct, Form::Desugar),
            Some(Class::StaticClauseRootNotMarked)
        );
    }
    // A static clause matches program terms as written, so an application below its root would
    // stand for its spelling rather than its value (decision NT-11-5), as would a sort test; a
    // static production's application stands for its expansion, a value.
    for form in [Form::Alias, Form::Desugar] {
        let below = root(form).enter(Opening::Argument);
        assert_eq!(
            admits(Construct::FunctionApplication, below).map(|refusal| refusal.class),
            Some(Class::FunctionInPattern)
        );
        assert_eq!(
            admits(Construct::SortTest, below).map(|refusal| refusal.class),
            Some(Class::SortTestInPattern)
        );
        assert_eq!(admits(Construct::StaticApplication, below), None);
    }
}

/// A map key reads by its parent's kind (D2): a key of a map in a pattern is evaluated, of a
/// map that is built is built; in an evaluated key a pattern-only construct selects an entry by
/// matching, so its openings are matched, and a computed one is looked up, so its openings are
/// built. The entries a position lies in are kept outermost first (D4).
#[test]
fn a_map_key_reads_by_its_parent_and_its_construct() {
    let pattern_key = Position::at(Form::CellsRule, Part::Subject, &[Opening::MapKey]);
    let built_key = Position::at(Form::CellsRule, Part::Result, &[Opening::MapKey]);
    assert_eq!(pattern_key.kind, Kind::Evaluated);
    assert_eq!(built_key.kind, Kind::Built);
    assert_eq!(pattern_key.enter(Opening::AsBody).kind, Kind::Matched);
    assert_eq!(pattern_key.enter(Opening::OrBranch).kind, Kind::Matched);
    assert_eq!(
        pattern_key.enter(Opening::FunctionArgument).kind,
        Kind::Built
    );
    assert_eq!(pattern_key.enter(Opening::Argument).kind, Kind::Evaluated);
    let refused = |construct, position| admits(construct, position).map(|refusal| refusal.class);
    // A function below an alias in a key would match the map's evaluated keys.
    assert_eq!(
        refused(
            Construct::FunctionApplication,
            Position::at(
                Form::ReadableRule,
                Part::Subject,
                &[Opening::MapKey, Opening::AsBody]
            )
        ),
        Some(Class::FunctionInPattern)
    );
    // `_` in a computed key's argument names no term.
    assert_eq!(
        refused(
            Construct::Wildcard,
            pattern_key.enter(Opening::FunctionArgument)
        ),
        Some(Class::WildcardOutsidePattern)
    );
    // A notation form in a key is the application it denotes, computed and looked up.
    assert_eq!(
        refused(
            Construct::Notation(krs_test_support::class_matrix::positions::Notation::Arithmetic),
            pattern_key
        ),
        None
    );
    let nested = Position::at(
        Form::ReadableRule,
        Part::Subject,
        &[
            Opening::ComputationItem,
            Opening::MapKey,
            Opening::ListElement,
        ],
    );
    assert_eq!(
        nested.nesting.entries.iter().collect::<Vec<_>>(),
        vec![Entry::ComputationItem, Entry::MapKey, Entry::ListElement]
    );
    assert!(nested.nesting.entries.contains(Entry::MapKey));
    assert_eq!(nested.nesting.entries.innermost(), Some(Entry::ListElement));
}

/// The term families' accept entries live in a file of their own, which holds nothing else and
/// no case of another family; `expected.toml` holds none of them.
#[test]
fn the_term_accepts_file_holds_only_term_accept_entries() {
    let main = "[class.wildcard-outside-pattern]\ncode = \"krs::syntax::unsupported-term-expression\"\ndoc = \"`_` outside a pattern\"\nadvice = \"none\"\n\n[accept.\"readable/result/pc/x\"]\n";
    let table = Table::parse_with_term_accepts(main, "[accept.\"terms/a/x\"]\nk = \"rule X\"\n")
        .expect("the two files parse as one table");
    assert_eq!(
        table.accept.keys().map(String::as_str).collect::<Vec<_>>(),
        ["readable/result/pc/x", "terms/a/x"]
    );
    let errors = Table::parse_with_term_accepts(
        main,
        "[accept.\"readable/result/pc/x\"]\n\n[[refuse]]\nmatch = \"terms/*\"\nclass = \"wildcard-outside-pattern\"\nat = \"spelling\"\n",
    )
    .expect_err("the term accepts file is checked");
    assert_eq!(
        errors,
        vec![
            TableError::Schema(format!(
                "{TERM_ACCEPTS_FILE} holds parts other than accept entries"
            )),
            TableError::Schema(format!(
                "{TERM_ACCEPTS_FILE} accepts \"readable/result/pc/x\", which is no term case"
            )),
        ]
    );
    let misplaced =
        Table::parse_with_term_accepts("[accept.\"terms/a/x\"]\n", "[accept.\"terms/a/y\"]\n")
            .expect_err("a term case's entry is in its own file");
    assert_eq!(
        misplaced,
        vec![TableError::Schema(format!(
            "expected.toml accepts the term case \"terms/a/x\", whose entry belongs in {TERM_ACCEPTS_FILE}"
        ))]
    );
}

/// The parts of a term case's ID: its form, its position, the construct whose opening it stands
/// in (depth 2), and its construct. An opener's name holds no space, and a construct that holds a
/// `/` holds one beside it (`x / 2`), so the segment after the position is an opener's exactly
/// where a `/` follows it and it holds no space.
fn id_parts(id: &str) -> Option<(&str, &str, Option<&str>, &str)> {
    let mut segments = id.splitn(4, '/');
    segments.next()?;
    let form = segments.next()?;
    let position = segments.next()?;
    let rest = segments.next()?;
    Some(match rest.split_once('/') {
        Some((opener, construct)) if !opener.is_empty() && !opener.contains(' ') => {
            (form, position, Some(opener), construct)
        }
        _ => (form, position, None, rest),
    })
}

/// The forms whose binders a `cells!` record declares, at the sort of the field each fills.
const DECLARED_BINDERS: [&str; 4] = ["cells", "cells-claim", "cells-local", "context-alias"];

/// The forms whose whole subject names the production the sentence is written for.
const FN_SUBJECTS: [&str; 7] = [
    "rule",
    "local-rule",
    "equation",
    "simplification",
    "context",
    "desugar",
    "alias",
];

/// The cases among which a name or sort rule's mistake is the same for one spelling: its
/// siblings. `None` for a case the class's mistake does not compare across.
fn sibling_scope(class: &str, id: &str) -> Option<&'static str> {
    let (form, position, opener, _) = id_parts(id)?;
    let free = matches!(form, "constant" | "init") && position != "variable-item";
    match class {
        // A sentence's `x` names the command's field and is never a record's alias, while an
        // initializer's update takes its base's fields by value; brackets at a `KItem` position
        // name no list.
        "record-update-base" if form != "init" && !free => Some("bound"),
        "list-notation-sort" if !free => Some("bound"),
        // `x` is no initializer's parameter (but the `variable-item` initializer's) nor a
        // constant's; a bare name at a fn subject's root names a unit constructor.
        "unbound-name" if free => Some("free"),
        "unbound-name" if position == "subject-root" && FN_SUBJECTS.contains(&form) => {
            Some("fn-root")
        }
        // The opener binds or reads its own names around the construct.
        "matches-pattern-binder" if opener == Some("matches-pattern") => Some("matches"),
        "alternatives-bind-unequally" if opener == Some("or-branch") => Some("or"),
        "binder-bound-twice" if opener == Some("as-body") => Some("as"),
        "object-term-as-predicate" if opener == Some("closure-body") => Some("closure"),
        // The construct is a condition's whole value.
        "condition-sort" | "let-sort" | "turbofish-instance-sort"
            if position == "guard" && matches!(opener, None | Some("let-body")) =>
        {
            Some("condition")
        }
        // A `cells!` record's binders have the sort the record declares, which a condition's
        // Bool or an operator's operand may not be.
        "binder-sort" if DECLARED_BINDERS.contains(&form) && position == "guard" => {
            Some("declared-condition")
        }
        "binder-sort" if DECLARED_BINDERS.contains(&form) => Some("declared"),
        "desugar-wildcard-undeclared"
            if form == "desugar" && matches!(position, "result" | "result-root") =>
        {
            Some("desugar-result")
        }
        _ => None,
    }
}

/// The name and sort rules of the term families: the classes no position decides.
const NAME_AND_SORT_CLASSES: [&str; 12] = [
    "alternatives-bind-unequally",
    "binder-bound-twice",
    "binder-sort",
    "condition-sort",
    "desugar-wildcard-undeclared",
    "let-sort",
    "list-notation-sort",
    "matches-pattern-binder",
    "object-term-as-predicate",
    "record-update-base",
    "turbofish-instance-sort",
    "unbound-name",
];

/// Why a readable key's alternative that reads `x` binds no name. A `k::matches!` pattern's names
/// are its own wherever the test stands, a key's too, so the test there rebinds `x` as in a
/// condition.
const KEY_READS_ITS_NAMES: &str = "in a readable map key a name the pattern binds elsewhere is looked up (D2), so an alternative that reads it binds nothing; in a subject's it binds";

/// The notation family's positions whose every case is a sibling exception, and why: each of the
/// family's spellings reads `x` as `k::builtin::int::add(x, 1)` does ([`SIBLING_EXCEPTIONS`]).
const SIBLING_EXCEPTION_POSITIONS: [(&str, &str, &str); 1] = [(
    "notation/readable/map-key/or-branch",
    "alternatives-bind-unequally",
    KEY_READS_ITS_NAMES,
)];

/// Sibling cases a name or sort rule does not decide though it decides the spelling at another
/// sibling, and why.
const SIBLING_EXCEPTIONS: [(&str, &str, &str); 10] = [
    (
        "terms/rule/subject-root-list/[x, ..]",
        "list-notation-sort",
        "the fn's whole subject is a `Term<List>`, a position of the sort list brackets denote, unlike its siblings' `KItem` (NT-18)",
    ),
    (
        "terms/readable/map-key/or-branch/Size(x)",
        "alternatives-bind-unequally",
        KEY_READS_ITS_NAMES,
    ),
    (
        "terms/readable/map-key/or-branch/k::builtin::int::add(x, 1)",
        "alternatives-bind-unequally",
        KEY_READS_ITS_NAMES,
    ),
    (
        "terms/readable/map-key/or-branch/Cmd::Hold(x)",
        "alternatives-bind-unequally",
        KEY_READS_ITS_NAMES,
    ),
    (
        "terms/readable/map-key/or-branch/Cmd::Pair { a: x, .. }",
        "alternatives-bind-unequally",
        KEY_READS_ITS_NAMES,
    ),
    (
        "terms/readable/map-key/or-branch/k::builtin::set::item(x)",
        "alternatives-bind-unequally",
        KEY_READS_ITS_NAMES,
    ),
    (
        "terms/readable/map-key/or-branch/k::map![x -> 1]",
        "alternatives-bind-unequally",
        KEY_READS_ITS_NAMES,
    ),
    (
        "terms/readable/map-key/or-branch/map![x -> 1]",
        "alternatives-bind-unequally",
        KEY_READS_ITS_NAMES,
    ),
    (
        "terms/readable/map-key/or-branch/x",
        "alternatives-bind-unequally",
        KEY_READS_ITS_NAMES,
    ),
    (
        "terms/readable/map-key/or-branch/x | 1",
        "alternatives-bind-unequally",
        KEY_READS_ITS_NAMES,
    ),
];

/// A spelling a name or sort rule refuses at one case is accepted at none of its siblings: an
/// observation of the full tier writes the rules, and a sibling whose product refuses it for
/// another reason (a finding) would otherwise be accepted by the table, so that fixing the finding
/// would record a wrong acceptance. A sibling refused for another mistake, the oracle's or
/// another rule's, makes that mistake first.
#[test]
fn a_name_or_sort_rule_refuses_a_spelling_at_every_sibling() {
    let table = Table::parse_with_term_accepts(
        &read_class_matrix("expected.toml"),
        &read_class_matrix(TERM_ACCEPTS_FILE),
    )
    .unwrap_or_else(|errors| panic!("expected.toml: {errors:#?}"));
    let cases = class_matrix::cases();
    let resolution = table.resolve_cases(&cases, registry_kind);
    let mut groups = BTreeMap::<(&str, &str, &str, &str), Vec<&Case>>::new();
    for case in &cases {
        let Some((_, _, _, construct)) = id_parts(&case.id) else {
            continue;
        };
        if case.term.is_none() {
            continue;
        }
        // A name nothing binds is unbound whatever construct reads it.
        let reads_a_name = case.term.as_ref().is_some_and(|term| {
            term.nodes
                .iter()
                .any(|node| node.construct == Construct::Reference)
        });
        for class in NAME_AND_SORT_CLASSES {
            if let Some(scope) = sibling_scope(class, &case.id) {
                let construct = if class == "unbound-name" && scope == "free" && reads_a_name {
                    "a construct that reads a name"
                } else {
                    construct
                };
                groups
                    .entry((class, scope, case.family.name(), construct))
                    .or_default()
                    .push(case);
            }
        }
    }
    let decided_by = |case: &Case| match resolution.expected.get(&case.id) {
        Some(Expected::Refuse { name, .. }) => Some(*name),
        _ => None,
    };
    // The table meets a name or sort mistake before the oracle's resolution refusal of the
    // case's own construct ([`OVERRIDDEN`]), so a sibling the oracle refuses only there, and no
    // name or sort rule decides, is as open to the rule as an accepted one. A refusal of the outer
    // construct is the opener's own mistake, which its siblings need not share.
    let open = |case: &Case| match resolution.expected.get(&case.id) {
        Some(Expected::Accept(_)) => Some("accepted"),
        Some(Expected::Refuse { name, .. }) if !NAME_AND_SORT_CLASSES.contains(name) => matches!(
            case.oracle(),
            Some(Outcome::Refuse(Refusal {
                stage: Stage::Resolution,
                outer: false,
                ..
            }))
        )
        .then_some("refused only at resolution"),
        _ => None,
    };
    let mut gaps = Vec::new();
    let mut excepted = BTreeSet::new();
    for ((class, _, _, _), members) in &groups {
        if !members.iter().any(|case| decided_by(case) == Some(*class)) {
            continue;
        }
        for case in members {
            let Some(how) = open(case) else {
                continue;
            };
            if SIBLING_EXCEPTION_POSITIONS
                .iter()
                .any(|(position, excepted_class, _)| {
                    case.id.starts_with(&format!("{position}/")) && excepted_class == class
                })
            {
                continue;
            }
            if SIBLING_EXCEPTIONS
                .iter()
                .any(|(id, excepted_class, _)| *id == case.id && excepted_class == class)
            {
                excepted.insert((case.id.as_str(), *class));
            } else {
                gaps.push(format!("{} is {how}, no {class}", case.id));
            }
        }
    }
    gaps.sort();
    gaps.dedup();
    assert!(gaps.is_empty(), "{} gaps:\n{}", gaps.len(), gaps.join("\n"));
    let stale = SIBLING_EXCEPTIONS
        .iter()
        .filter(|(id, class, _)| !excepted.contains(&(*id, *class)))
        .collect::<Vec<_>>();
    assert!(stale.is_empty(), "exceptions no rule needs: {stale:?}");
}

/// The term positions where the table accepts no construct, and why that is the position's own
/// fact rather than a generator's mistake.
const POSITIONS_WITHOUT_AN_ACCEPTED_CASE: [(&str, &str); 9] = [
    (
        "terms/alias/subject-root",
        "a static clause's whole subject is the production it expands, marked as the clause is, and no construct of the catalog is one (the base marks the command of the clause's other slots): the slot shows what each construct is refused for there",
    ),
    (
        "terms/alias/subject-root-binding",
        "a static clause's whole subject is the production it expands, marked as the clause is, and no construct of the catalog is one (the base marks the command of the clause's other slots): the slot shows what each construct that binds `x` is refused for there",
    ),
    (
        "terms/alias/subject/as-body",
        "`name @ pattern` in an alias clause's subject is refused (NT-8), whatever it aliases: the static applications show that it is told before them",
    ),
    (
        "terms/alias/subject/or-branch",
        "`A | B` in an alias clause's subject is refused (NT-8), whatever its alternatives: the static applications show that it is told before them",
    ),
    (
        "terms/alias/subject/set-concat",
        "a set's concatenation in a static clause's subject is refused by its head, whatever element it holds (NT-14: static expansion matches it in one order of its parts): the three elements show that it is told before them",
    ),
    (
        "terms/desugar/subject-root",
        "a static clause's whole subject is the production it expands, marked as the clause is, and no construct of the catalog is one (the base marks the command of the clause's other slots): the slot shows what each construct is refused for there",
    ),
    (
        "terms/desugar/subject/set-concat",
        "a set's concatenation in a static clause's subject is refused by its head, whatever element it holds (NT-14: static expansion matches it in one order of its parts): the three elements show that it is told before them",
    ),
    (
        "terms/local-rule/subject-root",
        "a single-body rule's whole subject holds its rewrite below its root: a construct holding none makes a rule that changes nothing, a whole-subject rewrite is an ordinary rule, and `_`, an alias and an island cannot be a subject's root (D3)",
    ),
    (
        "terms/rule/guard/closure-body",
        "a matching-logic predicate is refused in a rule's condition (`ml-in-condition`), so every case is; the host shows which mistakes inside the predicate come first, and a claim's condition is the closure's accepting host",
    ),
];

/// A term position where no construct is accepted is listed with its reason: a position whose
/// template makes every case fail for the same unrelated reason would otherwise go unnoticed.
#[test]
fn every_position_without_an_accepted_case_is_listed() {
    let table = Table::parse_with_term_accepts(
        &read_class_matrix("expected.toml"),
        &read_class_matrix(TERM_ACCEPTS_FILE),
    )
    .unwrap_or_else(|errors| panic!("expected.toml: {errors:#?}"));
    let cases = class_matrix::cases();
    let resolution = table.resolve_cases(&cases, registry_kind);
    let mut accepted = BTreeMap::<&str, bool>::new();
    for case in cases.iter().filter(|case| case.family == Family::Terms) {
        let position = case
            .id
            .strip_suffix(case.construct.as_str())
            .and_then(|position| position.strip_suffix('/'))
            .expect("a case ID ends with its construct");
        let accepts = matches!(resolution.expected.get(&case.id), Some(Expected::Accept(_)));
        *accepted.entry(position).or_default() |= accepts;
    }
    let without = accepted
        .into_iter()
        .filter(|(_, accepts)| !accepts)
        .map(|(position, _)| position)
        .collect::<Vec<_>>();
    assert_eq!(
        without,
        POSITIONS_WITHOUT_AN_ACCEPTED_CASE
            .iter()
            .map(|(position, _)| *position)
            .collect::<Vec<_>>()
    );
}

#[test]
fn table_defects_are_reported() {
    let defective = table(&format!(
        r#"{CLASSES}
[class.internal]
code = "krs::analysis::invalid-semantic-theory"
doc = "an internal code as an answer"
advice = "none"

[class.environment]
code = "krs::collect::host-io"
doc = "an environment code as an answer"
advice = "none"

[class.unknown-code]
code = "krs::nowhere::nothing"
doc = "a code the registry lacks"
advice = "none"

[class.proposed-code]
code = "krs::nowhere::proposed"
doc = "a code its step will register"
advice = "none"
proposed = true

[class.proposed-but-registered]
code = "krs::analysis::invalid-term"
doc = "a proposed code the registry already has"
advice = "none"
proposed = true

[[refuse]]
match = "claim/*"
class = "wrong-shape"
at = "entry"

[[refuse]]
match = "readable/subject/pc/x"
class = "no-such-class"
at = "entry"

[accept."readable/result/pc/x"]
k = ""
same_k_as = ["readable/subject/pc/x", "readable/gone"]

[accept."readable/gone"]
"#
    ));
    let errors = defective
        .resolve(
            &["readable/subject/pc/x", "readable/result/pc/x"],
            |_| None,
            registry_kind,
        )
        .errors;
    for expected in [
        TableError::NonAuthorClassCode {
            class: "internal".to_owned(),
            code: "krs::analysis::invalid-semantic-theory".to_owned(),
            kind: CodeKind::Internal,
        },
        TableError::NonAuthorClassCode {
            class: "environment".to_owned(),
            code: "krs::collect::host-io".to_owned(),
            kind: CodeKind::Environment,
        },
        TableError::Unregistered {
            owner: "class \"unknown-code\"".to_owned(),
            code: "krs::nowhere::nothing".to_owned(),
        },
        TableError::ProposedRegistered {
            class: "proposed-but-registered".to_owned(),
            code: "krs::analysis::invalid-term".to_owned(),
        },
        TableError::UnusedRule {
            pattern: "claim/*".to_owned(),
        },
        TableError::UnknownClass {
            pattern: "readable/subject/pc/x".to_owned(),
            class: "no-such-class".to_owned(),
        },
        TableError::SameKNotAccepted {
            id: "readable/result/pc/x".to_owned(),
            other: "readable/subject/pc/x".to_owned(),
        },
        TableError::UnknownCase {
            owner: "same_k_as of \"readable/result/pc/x\"".to_owned(),
            id: "readable/gone".to_owned(),
        },
        TableError::UnknownCase {
            owner: "an accept entry".to_owned(),
            id: "readable/gone".to_owned(),
        },
        TableError::Uncovered {
            id: "readable/subject/pc/x".to_owned(),
        },
    ] {
        assert!(
            errors.contains(&expected),
            "{expected:?} missing from {errors:#?}"
        );
    }
    assert!(
        !errors
            .iter()
            .any(|error| matches!(error, TableError::Unregistered { owner, .. } if owner.contains("proposed-code"))),
        "a proposed code may be unregistered: {errors:#?}"
    );

    let schema = Table::parse(
        "[[refuse]]\nmatch = \"a/{b\"\nclass = \"c\"\nat = \"somewhere\"\nextra = 1\n\n[other]\n",
    )
    .expect_err("the schema is broken");
    let messages = schema.iter().map(ToString::to_string).collect::<Vec<_>>();
    for fragment in [
        "unknown part \"other\"",
        "unknown key \"extra\"",
        "not entry, spelling",
        "is not closed",
    ] {
        assert!(
            messages.iter().any(|message| message.contains(fragment)),
            "{fragment:?} missing from {messages:#?}"
        );
    }
}

#[test]
fn pending_cases_follow_the_pending_rules() {
    let pending = Pending::parse(
        r#"
["readable/result/pc/Some(x)"]
finding = "unassigned"
deviation = "E0277 @ item"

["init/k/k::k![]"]
finding = "F1"
deviation = "uncoded @ unlocated"

["lattice/machine/catalog~coverage/s-kitem"]
finding = "F2"
deviation = "1 pairs only catalog holds; 0 pairs only coverage holds"
"#,
    )
    .unwrap_or_else(|errors| panic!("{errors:#?}"));
    let id = "readable/result/pc/Some(x)";
    let other = "readable/subject/pc/x";
    assert_eq!(
        pending.judge(other, Observation::Conforms),
        Judgement::Conforms
    );
    assert_eq!(
        pending.judge(id, Observation::Deviates("E0277 @ item")),
        Judgement::Red
    );
    assert_eq!(
        pending.judge(id, Observation::Conforms),
        Judgement::NowConforms
    );
    assert_eq!(
        pending.judge(
            id,
            Observation::Deviates("krs::analysis::optional-presence @ entry")
        ),
        Judgement::DeviationChanged {
            recorded: "E0277 @ item".to_owned(),
            observed: "krs::analysis::optional-presence @ entry".to_owned(),
        }
    );
    assert_eq!(
        pending.judge(other, Observation::Deviates("panic")),
        Judgement::Unexpected {
            observed: "panic".to_owned()
        }
    );
    assert!(Judgement::Red.passes() && Judgement::Conforms.passes());
    assert!(!Judgement::NowConforms.passes());
    // A sort-judge disagreement names no case, so it is never stale here.
    assert_eq!(pending.stale(&[id]), vec!["init/k/k::k![]"]);
    let tally = pending.tally([id, "init/k/k::k![]"]);
    assert_eq!(
        tally.by_finding,
        BTreeMap::from([("F1".to_owned(), 1), (UNASSIGNED.to_owned(), 1)])
    );

    // The full tier's prefixed entries name their case; a lattice entry names none.
    let prefixed = Pending::parse(
        "[\"k1/a\"]\nfinding = \"F\"\ndeviation = \"d\"\n\n\
         [\"full/b\"]\nfinding = \"F\"\ndeviation = \"d\"\n\n\
         [\"k6/e\"]\nfinding = \"F\"\ndeviation = \"d\"\n\n\
         [\"lattice/c\"]\nfinding = \"F\"\ndeviation = \"d\"\n",
    )
    .expect("the entries parse");
    assert_eq!(prefixed.stale(&["a"]), vec!["full/b", "k6/e"]);
    assert_eq!(
        ["k1/a", "full/b", "k6/e", "lattice/c", "d"].map(case_of),
        [Some("a"), Some("b"), Some("e"), None, Some("d")]
    );

    let errors = Pending::parse(
        "[\"a\"]\nfinding = \"\"\n\n[\"b\"]\nfinding = \"F\"\ndeviation = \"d\"\nstep = \"S5\"\nnote = 1\n",
    )
    .expect_err("the entries are broken");
    for fragment in [
        "needs a finding and a deviation",
        "a step owns a finding, not an entry",
        "unknown key \"note\"",
        "not a non-empty string",
    ] {
        assert!(
            errors.iter().any(|error| error.contains(fragment)),
            "{fragment:?} missing from {errors:#?}"
        );
    }
}

fn error(code: Option<&str>, range: Option<Range<usize>>, message: &str) -> ObservedDiagnostic {
    ObservedDiagnostic {
        severity: Severity::Error,
        code: code.map(str::to_owned),
        // A KRS code's kind is the registry's; a forwarded code states its own (below).
        kind: code.and_then(registry_kind),
        range,
        labels: Vec::new(),
        message: message.to_owned(),
        help: Vec::new(),
    }
}

#[test]
fn the_site_is_the_tables_and_a_forwarded_rustc_error_is_no_krs_code() {
    let cases = class_matrix::cases();
    let case = cases
        .iter()
        .find(|case| case.id == "init/k/k::k![]")
        .expect("the case is generated");
    let rendered = case.render();
    let placed = &rendered.cases[0];

    // A mistake outside the entry (an unused parameter) lies in the site a class widens it to.
    let at_parameter = Observed {
        accepted: false,
        diagnostics: vec![error(
            Some("krs::analysis::optional-presence"),
            Some(placed.item.start..placed.item.start + 4),
            "an unused configuration variable",
        )],
        panic: None,
    };
    assert_eq!(
        violations(&at_parameter, &placed.entry, registry_kind),
        vec![Violation::OutsideSite {
            range: placed.item.start..placed.item.start + 4
        }]
    );
    assert!(violations(&at_parameter, &placed.item, registry_kind).is_empty());

    // A diagnostic that relates two places is located at either: a binder's declaration as the
    // primary, outside the entry, and the occurrence as a label, inside it.
    let mut at_declaration = at_parameter.clone();
    at_declaration.diagnostics[0].labels = vec![placed.entry.clone()];
    assert!(violations(&at_declaration, &placed.entry, registry_kind).is_empty());

    // A rustc error forwarded under a registered code is still no KRS diagnosis.
    let forwarded = Observed {
        accepted: false,
        diagnostics: vec![error(
            Some(FORWARDED_RUSTC),
            Some(placed.spelling.clone()),
            "expected one of `!`, `)`, `,`, found `@`",
        )],
        panic: None,
    };
    assert_eq!(
        violations(&forwarded, &placed.entry, registry_kind),
        vec![Violation::NoRegisteredCode]
    );
}

/// The slots rustc parses as Rust before a KRS macro reads them: fn bodies an attribute macro
/// takes, and a `const` value. Nothing inside a macro's own tokens is one.
#[test]
fn rustc_parses_exactly_the_fn_bodies_and_the_constant_value() {
    let slots = class_matrix::cases()
        .iter()
        .filter(|case| case.rustc_parses)
        .map(|case| {
            let mut segments = case.id.split('/');
            let family = segments.next().unwrap_or_default();
            let form = segments.next().unwrap_or_default();
            let position = segments.next().unwrap_or_default();
            assert!(
                matches!(
                    case.family,
                    Family::Terms | Family::Import | Family::Notation
                ),
                "{} is no term position",
                case.id
            );
            assert!(matches!(family, "terms" | "import" | "notation"));
            format!("{form}/{position}")
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(
        slots,
        BTreeSet::from(
            [
                "alias/result",
                "alias/result-root",
                "alias/result-root-ground",
                "constant/value",
                "constant/value-root",
                "desugar/result",
                "desugar/result-guarded",
                "desugar/result-root",
                "equation/result",
                "rule/result",
                "rule/result-root",
                "shorthand/result",
                "shorthand/result-root",
                "simplification/result",
                "simplification/result-root",
            ]
            .map(str::to_owned)
        )
    );
}

/// K2's one exception: at a position rustc parses, rustc's parse error beside KRS's one error,
/// both inside the construct, leaves KRS's error to be judged; anywhere else, or with the errors
/// elsewhere, the observation is judged whole.
#[test]
fn rustcs_parse_error_is_admitted_beside_krss_error_where_rustc_parses() {
    let cases = class_matrix::cases();
    let placed_case = |id: &str| {
        cases
            .iter()
            .find(|case| case.id == id)
            .unwrap_or_else(|| panic!("{id} is generated"))
            .render()
    };
    let parsed = placed_case("terms/equation/result/y @ Cmd::Hold(_)");
    let parsed = &parsed.cases[0];
    let owned = placed_case("terms/table/result/y @ Cmd::Hold(_)");
    let owned = &owned.cases[0];
    let pair = |placed: &Placed<'_>, rustc_at: Range<usize>| Observed {
        accepted: false,
        diagnostics: vec![
            error(
                Some(FORWARDED_RUSTC),
                Some(rustc_at),
                "expected one of `)`, `,`, found `@`",
            ),
            error(
                Some("krs::syntax::invalid-pattern-as"),
                Some(placed.spelling.clone()),
                "`@` stands only in a pattern",
            ),
        ],
        panic: None,
    };
    let at_sign = |placed: &Placed<'_>| placed.spelling.start + 2..placed.spelling.start + 3;

    let admitted = pair(parsed, at_sign(parsed));
    let judged = without_rustc_parse_error(&admitted, parsed);
    assert_eq!(judged.errors().count(), 1);
    assert_eq!(
        judged
            .errors()
            .next()
            .and_then(|error| error.code.as_deref()),
        Some("krs::syntax::invalid-pattern-as")
    );
    assert!(violations(&judged, &parsed.spelling, registry_kind).is_empty());
    assert_eq!(
        signature(&admitted, parsed),
        "krs::rust-expansion::uncoded-error @ spelling; krs::syntax::invalid-pattern-as @ spelling",
        "the signature still names rustc's error"
    );

    // In a macro's own tokens rustc parses nothing: the same pair is two errors.
    let in_macro = pair(owned, at_sign(owned));
    assert_eq!(
        without_rustc_parse_error(&in_macro, owned).errors().count(),
        2
    );
    // rustc's error outside the construct, a second KRS error, no rustc error, or a panic:
    // judged whole.
    let elsewhere = pair(parsed, parsed.item.clone());
    assert_eq!(
        without_rustc_parse_error(&elsewhere, parsed)
            .errors()
            .count(),
        2
    );
    let mut two_krs = pair(parsed, at_sign(parsed));
    two_krs.diagnostics.push(error(
        Some("krs::syntax::rust-syntax"),
        Some(parsed.spelling.clone()),
        "expected an expression",
    ));
    assert_eq!(
        without_rustc_parse_error(&two_krs, parsed).errors().count(),
        3
    );
    let mut no_rustc = pair(parsed, at_sign(parsed));
    no_rustc.diagnostics[0].code = Some("krs::syntax::rust-syntax".to_owned());
    assert_eq!(
        without_rustc_parse_error(&no_rustc, parsed)
            .errors()
            .count(),
        2
    );
    let mut panicked = pair(parsed, at_sign(parsed));
    panicked.panic = Some("boom".to_owned());
    assert_eq!(
        without_rustc_parse_error(&panicked, parsed)
            .errors()
            .count(),
        2
    );

    // The front stops at the same parse error there, and only there.
    let front = Observed {
        accepted: false,
        diagnostics: vec![error(
            Some("krs::expand::parse"),
            Some(at_sign(parsed)),
            "expected one of `)`, `,`, found `@`",
        )],
        panic: None,
    };
    assert!(front_stops_at_rustc_parse(&front, parsed));
    let mut front_in_macro = front.clone();
    front_in_macro.diagnostics[0].range = Some(at_sign(owned));
    assert!(!front_stops_at_rustc_parse(&front_in_macro, owned));
    let mut front_elsewhere = front;
    front_elsewhere.diagnostics[0].range = Some(parsed.item.clone());
    assert!(!front_stops_at_rustc_parse(&front_elsewhere, parsed));
}

#[test]
fn the_table_free_invariants_judge_a_refusal_without_the_table() {
    let cases = class_matrix::cases();
    let case = cases
        .iter()
        .find(|case| case.id == "readable/result/pc/Some(x)")
        .expect("the case is generated");
    let rendered = case.render();
    let placed = &rendered.cases[0];
    let judge = |observed: &Observed| violations(observed, &placed.entry, registry_kind);

    let accepted = Observed {
        accepted: true,
        ..Observed::default()
    };
    assert!(judge(&accepted).is_empty());
    assert_eq!(signature(&accepted, placed), "accepted");

    let located = Observed {
        accepted: false,
        diagnostics: vec![
            error(
                Some("krs::analysis::optional-presence"),
                Some(placed.spelling.clone()),
                "an optional cell's result is `Some(..)` or `None`",
            ),
            ObservedDiagnostic {
                severity: Severity::Warning,
                code: Some("unused_imports".to_owned()),
                kind: Some(CodeKind::Author),
                range: None,
                labels: Vec::new(),
                message: "unused import".to_owned(),
                help: Vec::new(),
            },
        ],
        panic: None,
    };
    assert!(judge(&located).is_empty());
    assert_eq!(
        signature(&located, placed),
        "krs::analysis::optional-presence @ spelling"
    );

    // rustc judges the authored Rust.
    let rustc = Observed {
        accepted: false,
        diagnostics: vec![ObservedDiagnostic {
            kind: Some(CodeKind::Author),
            ..error(
                Some("E0277"),
                Some(placed.item.clone()),
                "the trait bound is not satisfied",
            )
        }],
        panic: None,
    };
    assert_eq!(
        judge(&rustc),
        vec![
            Violation::NoRegisteredCode,
            Violation::OutsideSite {
                range: placed.item.clone()
            }
        ]
    );
    assert_eq!(signature(&rustc, placed), "E0277 @ item");

    let internal_failure = Observed {
        accepted: false,
        diagnostics: vec![
            error(
                Some("krs::analysis::invalid-semantic-theory"),
                None,
                "declared variables must exactly match sentence uses",
            ),
            error(None, None, "internal error: no framework KItem sort"),
        ],
        panic: Some("index out of bounds".to_owned()),
    };
    assert_eq!(
        judge(&internal_failure),
        vec![
            Violation::Unlocated,
            Violation::ErrorCount(2),
            Violation::NonAuthorCode {
                code: "krs::analysis::invalid-semantic-theory".to_owned(),
                kind: CodeKind::Internal,
            },
            Violation::Panic("index out of bounds".to_owned()),
            Violation::InternalErrorText("internal error: no framework KItem sort".to_owned()),
        ]
    );
    assert_eq!(
        signature(&internal_failure, placed),
        "krs::analysis::invalid-semantic-theory @ unlocated; uncoded @ unlocated; panic"
    );

    let silent = Observed::default();
    assert_eq!(
        judge(&silent),
        vec![
            Violation::NoRegisteredCode,
            Violation::Unlocated,
            Violation::ErrorCount(0)
        ]
    );
    assert_eq!(signature(&silent, placed), "refused without an error");
}

#[test]
fn invariant_four_reads_the_kind_an_error_was_reported_with() {
    let cases = class_matrix::cases();
    let case = cases
        .iter()
        .find(|case| case.id == "readable/result/pc/Some(x)")
        .expect("the case is generated");
    let rendered = case.render();
    let placed = &rendered.cases[0];
    let judge = |observed: &Observed| violations(observed, &placed.entry, registry_kind);

    // A native code is in no registry: its kind is the one it was reported with, internal at a
    // sentence KRS lowered.
    let native = Observed {
        accepted: false,
        diagnostics: vec![ObservedDiagnostic {
            kind: Some(CodeKind::Internal),
            ..error(
                Some("UnboundVariable"),
                Some(placed.spelling.clone()),
                "variable x is unbound",
            )
        }],
        panic: None,
    };
    assert_eq!(
        judge(&native),
        vec![
            Violation::NoRegisteredCode,
            Violation::NonAuthorCode {
                code: "UnboundVariable".to_owned(),
                kind: CodeKind::Internal,
            }
        ]
    );

    // The same spelling about a `raw_k!` text is the author's.
    let mut raw = native;
    raw.diagnostics[0].kind = Some(CodeKind::Author);
    assert_eq!(judge(&raw), vec![Violation::NoRegisteredCode]);
}

/// The notation family's name rules (`unbound-name`, `alternatives-bind-unequally`,
/// `matches-pattern-binder` in `expected.toml`) select the spellings that read the name `x` by the
/// glob `*x*`, its letter; so each case they decide must read a name, and a spelling that holds an
/// `x` but reads none (a method such as `.extend(..)` over ground operands) fails here rather than
/// being refused silently.
#[test]
fn the_notation_familys_name_rules_decide_only_spellings_that_read_a_name() {
    let table = Table::parse_with_term_accepts(
        &read_class_matrix("expected.toml"),
        &read_class_matrix(TERM_ACCEPTS_FILE),
    )
    .unwrap_or_else(|errors| panic!("expected.toml: {errors:#?}"));
    let cases = class_matrix::cases();
    let resolution = table.resolve_cases(&cases, registry_kind);
    let captured = cases
        .iter()
        .filter(|case| case.family == Family::Notation)
        .filter(|case| {
            matches!(
                resolution.expected.get(&case.id),
                Some(Expected::Refuse { name, .. })
                    if ["unbound-name", "alternatives-bind-unequally", "matches-pattern-binder"]
                        .contains(name)
            )
        })
        .filter(|case| {
            !case.term.as_ref().is_some_and(|term| {
                term.nodes
                    .iter()
                    .any(|node| node.construct == Construct::Reference)
            })
        })
        .map(|case| case.id.as_str())
        .collect::<Vec<_>>();
    assert!(
        captured.is_empty(),
        "decided by a name rule, reading no name: {captured:#?}"
    );
}

/// A run that a filter narrows judges the pending entries of the cases it selects as a whole run
/// does, every prefix alike: an entry of a selected case that names no verdict of its test (its
/// case conforms now, say a `k8/` entry of a refusal that turned into an accept) fails it; an
/// entry of a case the filter leaves out, or of a test the run does not run, does not.
#[test]
fn a_filtered_run_fails_on_a_stale_entry_of_any_prefix() {
    let entry = |key: &str| format!("[{key:?}]\nfinding = \"F\"\ndeviation = \"d\"\n\n");
    let keys = [
        "k8/terms/a/x",
        "k8/terms/b/x",
        "k3/terms/a/x",
        "k6/terms/a/x",
        "k7/terms/a/y",
        "terms/a/y",
        "full/terms/a/z",
        "lattice/c",
    ];
    let pending = Pending::parse(&keys.map(entry).concat()).expect("the entries parse");
    let filter = Glob::parse("terms/a/*").expect("the filter parses");
    let covers = |_: &str, case: &str| filter.matches(case);
    // The run judged `terms/a/x` by K2, K3 and K7 and found it accepted, so it has no K8
    // verdict; `terms/a/y` deviates at K2 and K7, as recorded; `terms/a/z` is no case.
    let judged = BTreeMap::from([
        ("k2", BTreeSet::from(["terms/a/x", "terms/a/y"])),
        ("k3", BTreeSet::from(["terms/a/x"])),
        ("k7", BTreeSet::from(["terms/a/y"])),
    ]);
    let ran = BTreeSet::from(["k1", "k2", "k3", "k7", "k8"]);
    assert_eq!(
        pending.unjudged(&ran, &judged, covers),
        vec![("full/terms/a/z", "k2"), ("k8/terms/a/x", "k8")],
        "the stale K8 entry of a selected case fails; `k8/terms/b/x` is outside the filter, and \
         K6 did not run"
    );
    // The same entries in a whole run: every case is covered.
    assert_eq!(
        pending.unjudged(&ran, &judged, |_, _| true),
        vec![
            ("full/terms/a/z", "k2"),
            ("k8/terms/a/x", "k8"),
            ("k8/terms/b/x", "k8"),
        ]
    );
    // With K6 run, its entry of a case it judged no definition of fails too.
    let with_k6 = BTreeSet::from(["k1", "k2", "k3", "k6", "k7", "k8"]);
    assert!(
        pending
            .unjudged(&with_k6, &judged, covers)
            .contains(&("k6/terms/a/x", "k6"))
    );
}

/// A case whose K2 entry says its K differs from the table's holds the principled K, which record
/// mode keeps: [`Pending::holds_other_k`] sees the entry under the case's ID and under `full/`,
/// and no other deviation.
#[test]
fn record_mode_keeps_a_principled_k_held_against_the_product() {
    let pending = Pending::parse(&format!(
        "[\"terms/a\"]\n{}\n[\"full/terms/b\"]\n{}\n[\"terms/c\"]\n{}",
        entry("A", krs_test_support::class_matrix::pending::OTHER_K),
        entry("A", krs_test_support::class_matrix::pending::OTHER_K),
        entry("A", "accepted"),
    ))
    .unwrap_or_else(|errors| panic!("{errors:#?}"));
    assert!(pending.holds_other_k("terms/a"));
    assert!(pending.holds_other_k("terms/b"));
    assert!(!pending.holds_other_k("terms/c"));
    assert!(!pending.holds_other_k("terms/d"));
}
