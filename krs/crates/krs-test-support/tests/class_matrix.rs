//! The class-test generator: every base expands, every case's ranges name its construct, the
//! shipped table and red list parse, and the table, PENDING, and invariant rules decide as
//! documented.

use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;
use std::path::Path;

use krs_diagnostic::Code;
use krs_expand::whole_file::{self, ExpandDiagnostic, FileExpansion, FileRequest, Selection};
use krs_test_support::class_matrix::invariants::{
    Observed, ObservedDiagnostic, Severity, Violation, signature, violations,
};
use krs_test_support::class_matrix::pending::{Judgement, Observation, Pending, UNASSIGNED};
use krs_test_support::class_matrix::table::{At, Expected, Glob, Table, TableError};
use krs_test_support::class_matrix::{
    self, Base, Case, FRONT_CASE_CAP, Family, OwnReason, Packaging, Placed, render,
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

fn registered(code: &str) -> bool {
    Code::registered_spelling(code).is_some()
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
            // 7 kinds × 13 spellings × 2 sides, and 8 typed cells × 4 contents × 2 sides.
            (Family::Readable, 182 + 64),
            (Family::Claim, 182 + 64),
            // 7 kinds × (13 subject + 11 result spellings).
            (Family::Cells, 168),
            // 7 kinds × 16 values, 3 field orders, and 8 typed cells × 4 contents.
            (Family::Init, 112 + 3 + 32),
            // 29 term positions × 26 constructs.
            (Family::Terms, 754),
            // 29 term positions × 2 bare variants.
            (Family::Import, 58),
        ])
    );
    assert!(cases.len() <= FRONT_CASE_CAP);
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
        assert!(!case.construct.contains('/'), "{} holds a `/`", case.id);
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
/// the construct, except for a field-order case, whose construct names the order and whose
/// spelling is the whole field list.
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
        let mut cells = written
            .split(",\n")
            .map(|field| field.trim().split_once(':').expect("a field").0)
            .collect::<Vec<_>>();
        cells.sort_unstable();
        assert_eq!(
            cells,
            ["counter", "env", "frame", "k", "pc", "queue", "stack"],
            "{}",
            case.id
        );
    } else {
        assert_eq!(written, case.construct, "{}", case.id);
    }
    if case.kind.is_some() {
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
            .filter(|case| case.base == base && case.command().is_some())
            .collect::<Vec<&Case>>();
        assert!(!shared.is_empty(), "{base:?} has shared cases");
        let rendered = render(&shared);
        assert_eq!(rendered.cases.len(), shared.len());
        for placed in &rendered.cases {
            assert_placed(&rendered.source, placed);
            let command = placed.case.command().expect("the case is shared");
            assert_eq!(
                rendered
                    .source
                    .matches(&format!(")] {} ", command.name))
                    .count()
                    + rendered
                        .source
                        .matches(&format!(")] {}()", command.name))
                        .count(),
                1,
                "{} declares its command once",
                placed.case.id
            );
        }
    }
}

#[test]
#[should_panic(expected = "a case without a command is rendered alone")]
fn a_computation_subject_case_is_never_batched() {
    let cases = class_matrix::cases();
    let own = cases
        .iter()
        .find(|case| case.packaging == Packaging::Own(OwnReason::ComputationSubject))
        .expect("a computation-subject case is generated");
    let other = cases
        .iter()
        .find(|case| case.base == own.base && case.command().is_some())
        .expect("a shared case is generated");
    let _ = render(&[own, other]);
}

#[test]
fn the_shipped_table_and_red_list_parse() {
    let table = Table::parse(&read_class_matrix("expected.toml"))
        .unwrap_or_else(|errors| panic!("expected.toml: {errors:#?}"));
    let pending = Pending::parse(&read_class_matrix("pending.toml"))
        .unwrap_or_else(|errors| panic!("pending.toml: {errors:#?}"));
    let cases = class_matrix::cases();
    let ids = cases
        .iter()
        .map(|case| case.id.as_str())
        .collect::<Vec<_>>();
    let resolution = table.resolve(&ids, registered);
    // The refusal rules and the accepted K are written when the table is populated; until
    // then the table may only leave cases uncovered.
    let defects = resolution
        .errors
        .iter()
        .filter(|error| !matches!(error, TableError::Uncovered { .. }))
        .collect::<Vec<_>>();
    assert!(defects.is_empty(), "{defects:#?}");
    assert!(!table.internal.is_empty());
    assert!(pending.stale(&ids).is_empty());
}

fn table(text: &str) -> Table {
    Table::parse(text).unwrap_or_else(|errors| panic!("{errors:#?}"))
}

const CLASSES: &str = r#"
[class.wrong-shape]
code = "krs::analysis::invalid-term"
doc = "a shape the position does not admit"

[class.presence]
code = "krs::analysis::optional-presence"
doc = "`Some`/`None` on a plain cell"
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
    let resolution = narrowed.resolve(&ids, registered);
    assert!(resolution.errors.is_empty(), "{:#?}", resolution.errors);
    let decided = |id: &str| match resolution.expected[id] {
        Expected::Refuse { class, rule } => (class.code.as_str(), Some(rule.at)),
        Expected::Accept(accepted) => (accepted.k.as_str(), None),
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
        registered,
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

#[test]
fn table_defects_are_reported() {
    let defective = table(&format!(
        r#"{CLASSES}
[class.internal]
code = "krs::analysis::invalid-semantic-theory"
doc = "an internal code as an answer"

[class.unknown-code]
code = "krs::nowhere::nothing"
doc = "a code the registry lacks"

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
k = ""

[internal]
codes = ["krs::analysis::invalid-semantic-theory"]
"#
    ));
    let errors = defective
        .resolve(
            &["readable/subject/pc/x", "readable/result/pc/x"],
            registered,
        )
        .errors;
    for expected in [
        TableError::InternalClassCode {
            class: "internal".to_owned(),
            code: "krs::analysis::invalid-semantic-theory".to_owned(),
        },
        TableError::Unregistered {
            owner: "class \"unknown-code\"".to_owned(),
            code: "krs::nowhere::nothing".to_owned(),
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
step = "S5"

["init/k/k::k![]"]
finding = "F1"
deviation = "uncoded @ unlocated"
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
    assert_eq!(pending.stale(&[id]), vec!["init/k/k::k![]"]);
    let tally = pending.tally([id, "init/k/k::k![]"]);
    assert_eq!(
        tally.by_finding,
        BTreeMap::from([("F1".to_owned(), 1), (UNASSIGNED.to_owned(), 1)])
    );
    assert_eq!(
        tally.by_step,
        BTreeMap::from([("S5".to_owned(), 1), ("no step".to_owned(), 1)])
    );

    let errors = Pending::parse(
        "[\"a\"]\nfinding = \"\"\n\n[\"b\"]\nfinding = \"F\"\ndeviation = \"d\"\nstep = \"S9\"\nnote = 1\n",
    )
    .expect_err("the entries are broken");
    for fragment in [
        "needs a finding and a deviation",
        "not one of S1 to S6",
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
        range,
        message: message.to_owned(),
    }
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
    let internal = vec!["krs::analysis::invalid-semantic-theory".to_owned()];
    let judge = |observed: &Observed| violations(observed, &placed.entry, &internal, registered);

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
                range: None,
                message: "unused import".to_owned(),
            },
        ],
        panic: None,
    };
    assert!(judge(&located).is_empty());
    assert_eq!(
        signature(&located, placed),
        "krs::analysis::optional-presence @ spelling"
    );

    let rustc = Observed {
        accepted: false,
        diagnostics: vec![error(
            Some("E0277"),
            Some(placed.item.clone()),
            "the trait bound is not satisfied",
        )],
        panic: None,
    };
    assert_eq!(
        judge(&rustc),
        vec![
            Violation::NoRegisteredCode,
            Violation::OutsideEntry {
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
            Violation::InternalCode("krs::analysis::invalid-semantic-theory".to_owned()),
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
