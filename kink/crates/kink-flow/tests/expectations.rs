//! A mutation's expectation (`expect = "survive"` or `"kill"`): the verdict its author claims the
//! corpus gives it, checked against its row's status on every run (`report::mutation_expectation`).
//!
//! - Every status against each expectation gives one verdict, `met`, `unmet` or `inconclusive`,
//!   and the run's exit status joins it: unmet 1, inconclusive 3, beside the row's own status,
//!   across rows as within one; a mutation stating one that has no row is `unchecked`.
//! - A fuzz witness of a mutation expected to survive refutes it only when kink confirmed it and
//!   it needs no premise the flow lacks.
//! - The binary, on the calc fixture: an unmet or inconclusive expectation fails `run` with or
//!   without `--full` and `--locked`, the same verdicts under both schedules, cold and warm (from
//!   the outcome cache), and `report` exits as the run did; each such expectation has one stderr
//!   line naming the mutation; changing the expectations re-checks them on the cached verdicts;
//!   a list whose expectations are met exits 0, and its lock is the lock of the same list without
//!   them.

mod flow_support;

use kink_flow::{
    MutationList,
    cli::{
        EXIT_NO, EXIT_UNANSWERED, EXIT_UNASKED, EXIT_YES, fuzz_status, mutation_exit_status,
        run_status,
    },
    report::{EXPECTED_SURVIVOR_ACTION, check_expectations, expectation_lines},
    search::{STATUSES, UNKILLABLE},
};
use serde_json::{Value, json};
use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

/// The verdict each status gives each expectation, as the module documentation of
/// `report::mutation_expectation` argues it.
fn expected(status: &str, expect: &str) -> &'static str {
    match (status, expect) {
        ("killed", "kill") | ("survived" | "equivalent" | UNKILLABLE, "survive") => "met",
        ("killed", "survive") | ("survived" | "equivalent" | UNKILLABLE, "kill") => "unmet",
        _ => "inconclusive",
    }
}

/// A row of `status` whose mutation `id` expects `expect` (`None`: states nothing).
fn row(id: &str, status: &str, expect: Option<&str>) -> Value {
    json!({"id": id, "status": status, "expect": expect, "reason": null})
}

/// The run document of `rows`, its expectations checked as the run checks them.
fn document(mut rows: Vec<Value>) -> Value {
    let expectations = check_expectations(&mut rows, &[]);
    json!({
        "spec": {"outcome": "admitted"},
        "programs": [],
        "mutations": rows,
        "expectations": expectations,
        "mismatches": [],
    })
}

/// Every status against each expectation, and the exit status a run of that one row gives: the
/// row's own ([`mutation_exit_status`]) joined with the expectation's.
#[test]
fn every_status_meets_fails_or_leaves_open_each_expectation() {
    for status in STATUSES {
        for expect in ["survive", "kill"] {
            let verdict = expected(status, expect);
            let document = document(vec![row("m", status, Some(expect))]);
            let checked = &document["mutations"][0]["expectation"];
            assert_eq!(checked["verdict"], verdict, "{status} {expect}: {checked}");
            let own = mutation_exit_status(status, None);
            let expectation = match verdict {
                "unmet" => EXIT_NO,
                "inconclusive" => EXIT_UNANSWERED,
                _ => EXIT_YES,
            };
            assert_eq!(
                run_status(&document),
                kink_flow::cli::exit_join(own, expectation),
                "{status} {expect}"
            );
            assert_eq!(
                document["expectations"][verdict],
                json!(["m"]),
                "{status} {expect}"
            );
            // A line names the mutation exactly when the expectation fails or stays open.
            let lines = expectation_lines(&document);
            if verdict == "met" {
                assert!(lines.is_empty(), "{status} {expect}: {lines:?}");
            } else {
                assert_eq!(lines.len(), 1, "{status} {expect}: {lines:?}");
                assert!(
                    lines[0].starts_with("mutation m: expected to "),
                    "{lines:?}"
                );
            }
        }
        // A row without `expect` has no expectation, and its run exits by its status alone.
        let document = document(vec![row("m", status, None)]);
        assert_eq!(document["mutations"][0]["expectation"], Value::Null);
        assert_eq!(run_status(&document), mutation_exit_status(status, None));
        assert!(expectation_lines(&document).is_empty());
    }
}

/// The details: a broken control names its killers (every one of `killed_by` under `--full`, the
/// killer under first-kill), an undecided one each program left undecided with its cause, and a
/// met control on a mutant no program can kill says it is vacuous; a `survived` row of a met
/// control asks nothing, and every other row keeps its action.
#[test]
fn an_expectation_says_what_the_row_shows_against_it() {
    let mut first = row("first", "killed", Some("survive"));
    first["killer"] = json!("add");
    let mut full = row("full", "killed", Some("survive"));
    full["killer"] = json!("add");
    full["killed_by"] = json!(["add", "nested"]);
    let mut unknown = row("open", "unknown", Some("survive"));
    unknown["executed"] = json!([
        {"program": "add", "outcome": "agree", "cause": null},
        {"program": "nested", "outcome": "unknown", "cause": "an undecided branch"},
        {"program": "sub", "outcome": "timeout", "cause": null},
    ]);
    let mut refused = row("refused", "not-admitted", Some("kill"));
    refused["reason"] = json!("rejected");
    let mut control = row("control", "survived", Some("survive"));
    control["action"] = json!("write a program");
    let mut gap = row("gap", "survived", Some("kill"));
    gap["action"] = json!("write a program");
    let mut horizon = row("horizon", "survived", Some("survive"));
    horizon["action"] = json!("raise the bound");
    horizon["horizon"] = json!([
        {"program": "add", "horizon": {"out": {"elements": 2, "opening": "bound"}}},
    ]);
    let mut hidden = row("hidden", "survived", Some("survive"));
    hidden["action"] = json!("stop after the rule");
    hidden["stop_hides_edit"] = json!(["the stop stops before add"]);
    let document = document(vec![
        horizon,
        hidden,
        first,
        full,
        unknown,
        refused,
        control,
        gap,
        row("vacuous", "equivalent", Some("survive")),
        row("impossible", UNKILLABLE, Some("kill")),
    ]);
    assert_eq!(
        expectation_lines(&document),
        [
            "mutation first: expected to survive, killed by add",
            "mutation full: expected to survive, killed by add, nested",
            "mutation open: expected to survive, unknown (nested: an undecided branch; sub: \
             timeout): not confirmed",
            "mutation refused: expected to be killed, but it has no verdict: not-admitted \
             (rejected)",
            "mutation gap: expected to be killed, survived",
            "mutation impossible: expected to be killed, unkillable: no program of any corpus can \
             kill it",
        ]
    );
    assert_eq!(
        document["expectations"],
        json!({
            "met": ["horizon", "hidden", "control", "vacuous"],
            "unmet": ["first", "full", "gap", "impossible"],
            "inconclusive": ["open", "refused"],
            "unchecked": [],
        })
    );
    let rows = document["mutations"].as_array().unwrap();
    let by_id = |id: &str| rows.iter().find(|row| row["id"] == id).unwrap();
    assert!(
        by_id("vacuous")["expectation"]["detail"]
            .as_str()
            .unwrap()
            .starts_with("vacuous: "),
        "{}",
        by_id("vacuous")
    );
    assert_eq!(by_id("control")["expectation"]["detail"], Value::Null);
    assert_eq!(by_id("control")["action"], EXPECTED_SURVIVOR_ACTION);
    assert_eq!(by_id("gap")["action"], "write a program");
    // A survival up to a horizon, or behind a stop that hides the edit, is weaker than survival:
    // met, said so, and the row keeps the action that would observe more.
    assert_eq!(
        by_id("horizon")["expectation"]["detail"],
        "met only within what the runs observed: add agreed only up to the horizon of a \
         baseline's observation channel (horizon), and the mutant may differ past it; the row's \
         action says what would observe more"
    );
    assert_eq!(by_id("horizon")["action"], "raise the bound");
    assert_eq!(
        by_id("hidden")["expectation"]["detail"],
        "met only within what the runs observed: the stop hides the edit from every program \
         (stop_hides_edit), so no run shows what it changes; the row's action says what would \
         observe more"
    );
    assert_eq!(by_id("hidden")["action"], "stop after the rule");
    // The unmet expectations make the run a finding; the refused row's own status comes first.
    assert_eq!(run_status(&document), EXIT_UNASKED);
}

/// The run joins the expectations of all its rows as it joins their statuses: an unmet one (1)
/// comes before an inconclusive one (3) of another row, and before an unrelated row's own
/// `unknown` (3); a refused row's own 2 comes before both.
#[test]
fn the_run_joins_expectations_across_rows() {
    let unmet = row("gap", "survived", Some("kill"));
    let open = row("open", "unknown", Some("survive"));
    assert_eq!(
        run_status(&document(vec![unmet.clone(), open.clone()])),
        EXIT_NO
    );
    assert_eq!(
        run_status(&document(vec![open.clone(), unmet.clone()])),
        EXIT_NO
    );
    assert_eq!(
        run_status(&document(vec![
            row("plain", "unknown", None),
            row("broken", "killed", Some("survive")),
        ])),
        EXIT_NO
    );
    assert_eq!(
        run_status(&document(vec![
            open.clone(),
            row("met", "killed", Some("kill"))
        ])),
        EXIT_UNANSWERED
    );
    assert_eq!(
        run_status(&document(vec![
            unmet,
            open,
            row("bad", "invalid-mutation", None)
        ])),
        EXIT_UNASKED
    );
}

/// A mutation of the list that states an expectation and has no row (a run stopped before it, or
/// `--only` left it out) is `unchecked`, in list order, and is no verdict: the exit status is the
/// rows' alone.
#[test]
fn an_expectation_without_a_row_is_unchecked() {
    let list = MutationList::decode(
        r#"
[[mutation]]
id = "ran"
misunderstanding = "a"
expect = "survive"
  [[mutation.edit]]
  rule = "add"
  find = "x"
  replace = "y"

[[mutation]]
id = "left-out"
misunderstanding = "b"
expect = "kill"
  [[mutation.edit]]
  rule = "add"
  find = "x"
  replace = "y"

[[mutation]]
id = "states-nothing"
misunderstanding = "c"
  [[mutation.edit]]
  rule = "add"
  find = "x"
  replace = "y"

[[mutation]]
id = "also-left-out"
misunderstanding = "d"
expect = "survive"
  [[mutation.edit]]
  rule = "add"
  find = "x"
  replace = "y"
"#,
    )
    .unwrap();
    let mut rows = vec![row("ran", "survived", Some("survive"))];
    let expectations = check_expectations(&mut rows, &list.mutations);
    assert_eq!(
        expectations,
        json!({
            "met": ["ran"],
            "unmet": [],
            "inconclusive": [],
            "unchecked": ["left-out", "also-left-out"],
        })
    );
    let document = json!({
        "spec": {"outcome": "admitted"},
        "programs": [],
        "mutations": rows,
        "expectations": expectations,
        "mismatches": [],
    });
    assert_eq!(run_status(&document), EXIT_YES);
    assert!(expectation_lines(&document).is_empty());
}

/// A fuzz witness of a mutation expected to survive refutes the expectation (1) only when kink's
/// own run confirmed the kill and every premise it rests on is in the flow; unconfirmed
/// (`--no-confirm`) or resting on a premise `FLOW.toml` lacks, it is a candidate (3). A witness
/// of any other kill job answers it (0).
#[test]
fn a_fuzz_witness_refutes_a_control_only_when_confirmed_on_the_flow() {
    let witness = |expect: Value, confirmed: bool, in_flow: &[bool]| {
        json!({
            "stopped": null,
            "job": {"kind": "kill", "expect": expect},
            "program": {
                "confirmed": confirmed,
                "premises": in_flow
                    .iter()
                    .map(|in_flow| json!({"name": "p", "in_flow": in_flow}))
                    .collect::<Vec<_>>(),
            },
        })
    };
    let survive = || json!("survive");
    assert_eq!(fuzz_status(&witness(survive(), true, &[])), EXIT_NO);
    assert_eq!(fuzz_status(&witness(survive(), true, &[true])), EXIT_NO);
    assert_eq!(
        fuzz_status(&witness(survive(), false, &[])),
        EXIT_UNANSWERED
    );
    assert_eq!(
        fuzz_status(&witness(survive(), true, &[true, false])),
        EXIT_UNANSWERED
    );
    assert_eq!(
        fuzz_status(&witness(survive(), false, &[false])),
        EXIT_UNANSWERED
    );
    for expect in [json!("kill"), Value::Null] {
        assert_eq!(
            fuzz_status(&witness(expect.clone(), false, &[false])),
            EXIT_YES
        );
        assert_eq!(fuzz_status(&witness(expect, true, &[])), EXIT_YES);
    }
}

// ---------------------------------------------------------------------------------------------
// The binary on calc.

/// A private copy of the calc fixture, without its cache.
fn calc(test: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-expectations-{}", std::process::id()))
        .join(test);
    let _ = fs::remove_dir_all(&dir);
    flow_support::copy_dir(&flow_support::flow("calc"), &dir);
    dir
}

/// The four judged mutations of calc's status list, each with `expect` set to the value its id
/// is paired with (`None`: no `expect`).
fn list(expects: [(&str, Option<&str>); 4]) -> String {
    let edit = |find: &str, replace: &str| {
        format!(
            "  [[mutation.edit]]\n  rule = \"add\"\n  find = \"{find}\"\n  replace = \"{replace}\"\n"
        )
    };
    let edits = [
        ("add-becomes-sub", edit("I1 +Int I2", "I1 -Int I2")),
        ("add-commutes", edit("I1 +Int I2", "I2 +Int I1")),
        (
            "add-in-a-group",
            edit("I1 +Int I2", "I1 +Int I2 [group(arith)]"),
        ),
        ("add-unbound", edit("I1 +Int I2", "I1 +Int I3")),
    ];
    edits
        .iter()
        .zip(expects)
        .map(|((id, edit), (named, expect))| {
            assert_eq!(*id, named);
            let expect = expect.map_or(String::new(), |expect| format!("expect = \"{expect}\"\n"));
            format!("[[mutation]]\nid = \"{id}\"\nmisunderstanding = \"a test mutation\"\n{expect}\n{edit}\n")
        })
        .collect()
}

/// `kink-flow VERB FLOW.toml ARGS` in `dir`: its exit status, document and stderr.
fn binary(dir: &Path, verb: &str, args: &[&str]) -> (Option<i32>, Value, String, Vec<u8>) {
    let output = Command::new(env!("CARGO_BIN_EXE_kink-flow"))
        .arg(verb)
        .arg(dir.join("FLOW.toml"))
        .args(args)
        .current_dir(dir)
        .output()
        .unwrap();
    let document = serde_json::from_slice(&output.stdout).unwrap();
    (
        output.status.code(),
        document,
        String::from_utf8(output.stderr).unwrap(),
        output.stdout,
    )
}

fn code(status: u8) -> Option<i32> {
    Some(i32::from(status))
}

/// Every expectation of the list is wrong: a killed mutation expected to survive, a survivor and
/// an equivalent mutation expected to be killed, each unmet; `run` exits 1 and names each, the
/// same cold and warm (decided from the outcome cache), first-kill and `--full`, and `report`
/// exits as the last run did. A lock written by such a run is current, and `--locked` still exits
/// 1 on the expectations, which it checks from the rows, not the lock. Changing the expectations
/// to the verdicts re-checks them on the cached verdicts, which nothing invalidates: the run
/// exits 0 under `--locked` with the lock unchanged (a run of the three mutations that compile,
/// since a run under `--only` writes no lock). The mutation `--only` leaves out is unchecked. A mutation that does not compile has no verdict: its expectation is inconclusive,
/// and its own status (2) is the run's.
#[test]
#[ignore = "kink"]
fn an_unmet_expectation_fails_run_under_either_schedule() {
    let dir = calc("unmet");
    fs::write(
        dir.join("EXPECT.toml"),
        list([
            ("add-becomes-sub", Some("survive")),
            ("add-commutes", Some("kill")),
            ("add-in-a-group", Some("kill")),
            ("add-unbound", Some("kill")),
        ]),
    )
    .unwrap();
    let judged = [
        "EXPECT.toml",
        "--only",
        "add-becomes-sub",
        "--only",
        "add-commutes",
        "--only",
        "add-in-a-group",
    ];
    let mut documents = Vec::new();
    for (round, full) in [("cold", false), ("warm", false), ("full", true)] {
        let args = [&judged[..], if full { &["--full"][..] } else { &[] }].concat();
        let (status, document, stderr, stdout) = binary(&dir, "run", &args);
        assert_eq!(status, code(EXIT_NO), "{round}: {stderr}");
        let lines = stderr
            .lines()
            .filter(|line| line.starts_with("kink-flow: mutation "))
            .collect::<Vec<_>>();
        assert_eq!(lines.len(), 3, "{round}: {stderr}");
        assert!(
            lines[0].starts_with(
                "kink-flow: mutation add-becomes-sub: expected to survive, killed by "
            ),
            "{round}: {lines:?}"
        );
        assert_eq!(
            lines[1..],
            [
                "kink-flow: mutation add-commutes: expected to be killed, survived",
                "kink-flow: mutation add-in-a-group: expected to be killed, equivalent: no \
                 program of any corpus can kill it",
            ],
            "{round}"
        );
        assert_eq!(
            document["expectations"],
            json!({
                "met": [],
                "unmet": ["add-becomes-sub", "add-commutes", "add-in-a-group"],
                "inconclusive": [],
                "unchecked": ["add-unbound"],
            }),
            "{round}"
        );
        if round == "warm" {
            // The killed and the surviving mutation are decided from the outcome cache.
            assert_eq!(
                document["outcome_cache"]["mutations_from_cache"], 2,
                "{:#}",
                document["outcome_cache"]
            );
        }
        documents.push((document, stdout));
    }
    // The verdicts are the row statuses', which no schedule moves.
    let verdicts = |document: &Value| {
        document["mutations"]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| {
                (
                    row["id"].clone(),
                    row["status"].clone(),
                    row["expectation"]["verdict"].clone(),
                )
            })
            .collect::<Vec<_>>()
    };
    for (document, _) in &documents[1..] {
        assert_eq!(verdicts(document), verdicts(&documents[0].0));
    }
    let (status, _, stderr, stdout) = binary(&dir, "report", &[]);
    assert_eq!(status, code(EXIT_NO), "{stderr}");
    assert_eq!(stdout, documents[2].1);
    assert_eq!(
        stderr
            .lines()
            .filter(|line| line.starts_with("kink-flow: mutation "))
            .count(),
        3,
        "{stderr}"
    );
    // A lock written by a run that fails on its expectations is the lock of its verdicts, and
    // `--locked` on it fails on the same expectations, the lock unchanged. A run under `--only`
    // writes no lock, so these runs judge a list of the three mutations that compile.
    let three = |expects: [(&str, Option<&str>); 3]| {
        let text = list([expects[0], expects[1], expects[2], ("add-unbound", None)]);
        text[..text.find("[[mutation]]\nid = \"add-unbound\"").unwrap()].to_owned()
    };
    fs::write(
        dir.join("THREE.toml"),
        three([
            ("add-becomes-sub", Some("survive")),
            ("add-commutes", Some("kill")),
            ("add-in-a-group", Some("kill")),
        ]),
    )
    .unwrap();
    let locked = ["THREE.toml", "--lock", "expect.lock"];
    let (status, document, stderr, _) = binary(&dir, "run", &locked);
    assert_eq!(status, code(EXIT_NO), "{stderr}");
    assert_eq!(
        document["lock"]["status"], "created",
        "{:#}",
        document["lock"]
    );
    let locked = [&locked[..], &["--locked"][..]].concat();
    let (status, document, stderr, _) = binary(&dir, "run", &locked);
    assert_eq!(status, code(EXIT_NO), "{stderr}");
    assert_eq!(
        document["lock"]["status"], "unchanged",
        "{:#}",
        document["lock"]
    );
    assert_eq!(
        document["expectations"]["unmet"],
        json!(["add-becomes-sub", "add-commutes", "add-in-a-group"])
    );
    assert_eq!(
        stderr
            .lines()
            .filter(|line| line.starts_with("kink-flow: mutation "))
            .count(),
        3,
        "{stderr}"
    );
    let lock = fs::read(dir.join("expect.lock")).unwrap();
    // The expectations changed to the verdicts: checked again on the cached verdicts, all met.
    fs::write(
        dir.join("THREE.toml"),
        three([
            ("add-becomes-sub", Some("kill")),
            ("add-commutes", Some("survive")),
            ("add-in-a-group", Some("survive")),
        ]),
    )
    .unwrap();
    let (status, document, stderr, _) = binary(&dir, "run", &locked);
    assert_eq!(status, code(EXIT_YES), "{stderr}");
    assert!(!stderr.contains("kink-flow: mutation "), "{stderr}");
    assert_eq!(
        document["expectations"],
        json!({
            "met": ["add-becomes-sub", "add-commutes", "add-in-a-group"],
            "unmet": [],
            "inconclusive": [],
            "unchecked": [],
        })
    );
    let statuses = |document: &Value| {
        verdicts(document)
            .into_iter()
            .map(|(id, status, _)| (id, status))
            .collect::<Vec<_>>()
    };
    assert_eq!(statuses(&document), statuses(&documents[0].0));
    assert_eq!(document["outcome_cache"]["mutations_from_cache"], 2);
    assert_eq!(document["outcome_cache"]["records_written"], 0);
    assert_eq!(document["lock"]["status"], "unchanged");
    assert_eq!(fs::read(dir.join("expect.lock")).unwrap(), lock);
    // No verdict to check: inconclusive, and the row's own status is the run's.
    let (status, document, stderr, _) =
        binary(&dir, "run", &["EXPECT.toml", "--only", "add-unbound"]);
    assert_eq!(status, code(EXIT_UNASKED), "{stderr}");
    assert_eq!(
        document["expectations"]["inconclusive"],
        json!(["add-unbound"])
    );
    assert_eq!(
        document["expectations"]["unchecked"],
        json!(["add-becomes-sub", "add-commutes", "add-in-a-group"])
    );
    assert!(
        stderr.contains(
            "kink-flow: mutation add-unbound: expected to be killed, but it has no verdict: \
             not-admitted (rejected)"
        ),
        "{stderr}"
    );
}

/// Every expectation of the list is right: `run` exits 0 and prints no expectation line, the
/// control's `survived` row asks nothing, the equivalent control is met and vacuous, and the lock
/// is byte for byte the lock of the same list without any `expect`.
#[test]
#[ignore = "kink"]
fn met_expectations_leave_the_run_and_its_lock_unchanged() {
    let dir = calc("met");
    let expects = [
        ("add-becomes-sub", Some("kill")),
        ("add-commutes", Some("survive")),
        ("add-in-a-group", Some("survive")),
    ];
    let three = |expects: [(&str, Option<&str>); 3]| {
        let text = list([expects[0], expects[1], expects[2], ("add-unbound", None)]);
        // The fourth mutation does not compile; the lock is of the three judged ones.
        text[..text.find("[[mutation]]\nid = \"add-unbound\"").unwrap()].to_owned()
    };
    fs::write(dir.join("EXPECT.toml"), three(expects)).unwrap();
    fs::write(
        dir.join("PLAIN.toml"),
        three(expects.map(|(id, _)| (id, None))),
    )
    .unwrap();
    let (status, document, stderr, _) =
        binary(&dir, "run", &["EXPECT.toml", "--lock", "expect.lock"]);
    assert_eq!(status, code(EXIT_YES), "{stderr}");
    assert!(!stderr.contains("kink-flow: mutation "), "{stderr}");
    assert_eq!(
        document["expectations"],
        json!({
            "met": ["add-becomes-sub", "add-commutes", "add-in-a-group"],
            "unmet": [],
            "inconclusive": [],
            "unchecked": [],
        })
    );
    let rows = document["mutations"].as_array().unwrap();
    assert_eq!(rows[1]["status"], "survived");
    assert_eq!(rows[1]["action"], EXPECTED_SURVIVOR_ACTION);
    assert_eq!(rows[2]["status"], "equivalent");
    assert!(
        rows[2]["expectation"]["detail"]
            .as_str()
            .unwrap()
            .starts_with("vacuous: "),
        "{}",
        rows[2]
    );
    let (status, document, stderr, _) =
        binary(&dir, "run", &["PLAIN.toml", "--lock", "plain.lock"]);
    assert_eq!(status, code(EXIT_YES), "{stderr}");
    assert_eq!(document["mutations"][1]["expectation"], Value::Null);
    assert_eq!(
        fs::read(dir.join("expect.lock")).unwrap(),
        fs::read(dir.join("plain.lock")).unwrap()
    );
}
