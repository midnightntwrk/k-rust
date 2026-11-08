//! The runner's mutant statuses have one name in kink-campaign's reports, kink-corpus's harness
//! summary and kink-flow's documents; kink-flow's only other statuses are its own. Each status
//! gives one exit status, and parts' exit statuses join in one order.

use kink_campaign::{MutantStatus, Tally, report_status_name, report_tally};
use kink_corpus::summary::TALLY_KEYS;
use kink_flow::cli::{
    EXIT_NO, EXIT_UNANSWERED, EXIT_UNASKED, EXIT_YES, coverage_status, exit_join, fuzz_status,
    mutation_exit_status, query_status, run_status,
};
use kink_flow::results::RESULT_CACHE_NO_BUILD;
use kink_flow::search::{INVALID_MUTATION, STATUSES, UNKILLABLE, status_name};
use serde_json::json;
use std::collections::BTreeSet;

/// Every runner status; [`listed`]'s match makes a new variant a compile error here.
const RUNNER: [MutantStatus; 7] = [
    MutantStatus::Killed,
    MutantStatus::Survived,
    MutantStatus::Equivalent,
    MutantStatus::NotAdmitted,
    MutantStatus::Timeout,
    MutantStatus::Unknown,
    MutantStatus::Error,
];

const fn listed(status: MutantStatus) -> usize {
    match status {
        MutantStatus::Killed => 0,
        MutantStatus::Survived => 1,
        MutantStatus::Equivalent => 2,
        MutantStatus::NotAdmitted => 3,
        MutantStatus::Timeout => 4,
        MutantStatus::Unknown => 5,
        MutantStatus::Error => 6,
    }
}

/// The field of `tally` that counts `status`.
fn count(tally: &mut Tally, status: MutantStatus) -> &mut u64 {
    match status {
        MutantStatus::Killed => &mut tally.killed,
        MutantStatus::Survived => &mut tally.survived,
        MutantStatus::Equivalent => &mut tally.equivalent,
        MutantStatus::NotAdmitted => &mut tally.not_admitted,
        MutantStatus::Timeout => &mut tally.timeout,
        MutantStatus::Unknown => &mut tally.unknown,
        MutantStatus::Error => &mut tally.error,
    }
}

#[test]
fn every_document_names_a_runner_status_alike() {
    for (index, status) in RUNNER.into_iter().enumerate() {
        assert_eq!(listed(status), index);
    }
    let runner: BTreeSet<&str> = RUNNER.into_iter().map(status_name).collect();
    assert_eq!(
        runner.len(),
        RUNNER.len(),
        "two runner statuses share a name"
    );

    // kink-campaign's report names each status as kink-flow's documents do, in a mutant's
    // `status` and as the tally key that counts it.
    let mut tally = Tally::default();
    for (count_of, status) in (1..).zip(RUNNER) {
        assert_eq!(
            report_status_name(status),
            status_name(status),
            "a campaign report names {status:?} otherwise"
        );
        *count(&mut tally, status) = count_of;
    }
    let rejected_origins = 1 + RUNNER.len() as u64;
    tally.rejected_origins = rejected_origins;
    let rendered = report_tally(tally);
    let rendered = rendered.as_object().expect("a tally is an object");
    for (count_of, status) in (1..).zip(RUNNER) {
        assert_eq!(
            rendered[status_name(status)],
            count_of,
            "a campaign report's tally counts {status:?} under another key"
        );
    }
    assert_eq!(rendered["rejected_origins"], rejected_origins);

    // kink-corpus's summary reads a report's tally under exactly the report's keys.
    let report_keys: BTreeSet<&str> = rendered.keys().map(String::as_str).collect();
    let harness: BTreeSet<&str> = TALLY_KEYS.into_iter().collect();
    assert_eq!(harness.len(), TALLY_KEYS.len(), "two tally keys coincide");
    assert_eq!(
        harness, report_keys,
        "the harness summary reads a tally key a campaign report does not write"
    );

    let user: BTreeSet<&str> = STATUSES.into_iter().collect();
    assert_eq!(user.len(), STATUSES.len(), "two user statuses share a name");
    assert!(runner.is_subset(&user));
    assert_eq!(
        user.difference(&runner).copied().collect::<BTreeSet<_>>(),
        BTreeSet::from([UNKILLABLE, INVALID_MUTATION]),
    );
}

/// Every status of a run document gives the exit status of what the caller does next: a verdict
/// is an answer, `timeout` and `unknown` are none, a mutation its author must fix could not be
/// asked, and an `error` is a finding only when it reports a `--verify` mismatch.
#[test]
fn every_mutation_status_gives_one_exit_status() {
    let expected = |status: &str| match status {
        "killed" | "survived" | "equivalent" | UNKILLABLE => EXIT_YES,
        "timeout" | "unknown" => EXIT_UNANSWERED,
        "not-admitted" | "error" | INVALID_MUTATION => EXIT_UNASKED,
        other => panic!("a status with no exit status: {other}"),
    };
    for status in STATUSES {
        assert_eq!(
            mutation_exit_status(status, None),
            expected(status),
            "{status}"
        );
    }
    assert_eq!(
        mutation_exit_status("error", Some("outcome-mismatch:p")),
        EXIT_NO
    );
    assert_eq!(
        mutation_exit_status("error", Some("resolution-mismatch")),
        EXIT_NO
    );
    assert_eq!(
        mutation_exit_status("error", Some("baseline-mismatch:p")),
        EXIT_UNASKED
    );
    assert_eq!(
        mutation_exit_status("error", Some("no-comparable-program")),
        EXIT_UNASKED
    );
}

/// Parts join as 2 > 1 > 3 > 0, and a status that is none of the four counts as 2.
#[test]
fn exit_statuses_join_unasked_then_no_then_unanswered_then_yes() {
    let order = [EXIT_UNASKED, EXIT_NO, EXIT_UNANSWERED, EXIT_YES];
    for (i, left) in order.into_iter().enumerate() {
        for (j, right) in order.into_iter().enumerate() {
            assert_eq!(exit_join(left, right), order[i.min(j)], "{left} {right}");
        }
        assert_eq!(exit_join(left, 7), EXIT_UNASKED);
    }
}

/// Each command's document decides its exit status from what the command asks.
#[test]
fn documents_give_their_exit_statuses() {
    let admitted = json!({"outcome": "admitted"});
    // results: a program's class and its expectation.
    let results = |programs: serde_json::Value, mismatches: serde_json::Value| json!({"spec": admitted, "programs": programs, "mismatches": mismatches});
    assert_eq!(
        coverage_status(&results(json!([{"class": "comparable"}]), json!([]))),
        EXIT_YES
    );
    assert_eq!(
        coverage_status(&results(
            json!([{"class": "comparable", "expectation": {"verdict": "unmet"}}, {"class": "timeout"}]),
            json!([])
        )),
        EXIT_NO
    );
    assert_eq!(
        coverage_status(&results(json!([{"class": "unknown"}]), json!([]))),
        EXIT_UNANSWERED
    );
    assert_eq!(
        coverage_status(&results(json!([{"class": "refused"}]), json!([{}]))),
        EXIT_UNASKED
    );
    assert_eq!(
        coverage_status(&results(json!([{"class": "comparable"}]), json!([{}]))),
        EXIT_NO
    );
    assert_eq!(
        coverage_status(&json!({"spec": {"outcome": "refused"}, "programs": []})),
        EXIT_UNASKED
    );
    // A result record the command could not write fails it, a finding included; a record it does
    // not write because kink's build identity is unknown does not.
    assert_eq!(
        coverage_status(&results(
            json!([{"class": "comparable", "expectation": {"verdict": "unmet"}}, {"class": "comparable", "cache_error": "cannot write the result record: x"}]),
            json!([])
        )),
        EXIT_UNASKED
    );
    assert_eq!(
        coverage_status(&results(
            json!([{"class": "comparable", "cache_error": RESULT_CACHE_NO_BUILD}]),
            json!([])
        )),
        EXIT_YES
    );
    // run: the mutations' verdicts; a baseline timeout only cannot kill.
    let run = |programs: serde_json::Value, mutations: serde_json::Value| json!({"spec": admitted, "programs": programs, "mutations": mutations, "mismatches": []});
    assert_eq!(
        run_status(&run(
            json!([{"class": "timeout"}]),
            json!([{"status": "killed"}, {"status": "survived"}])
        )),
        EXIT_YES
    );
    assert_eq!(
        run_status(&run(
            json!([]),
            json!([{"status": "unknown"}, {"status": "killed"}])
        )),
        EXIT_UNANSWERED
    );
    assert_eq!(
        run_status(&run(
            json!([]),
            json!([{"status": "unknown"}, {"status": INVALID_MUTATION}])
        )),
        EXIT_UNASKED
    );
    assert_eq!(
        run_status(&run(
            json!([{"class": "error"}]),
            json!([{"status": "killed"}])
        )),
        EXIT_UNASKED
    );
    assert_eq!(
        run_status(&run(
            json!([]),
            json!([{"status": "killed", "cache_error": "x"}])
        )),
        EXIT_UNASKED
    );
    // query: a refuted claim is a finding, an unanswered pair no answer.
    let query = |rows: serde_json::Value| json!({"spec": admitted, "programs": [], "rows": rows, "mismatches": []});
    assert_eq!(
        query_status(&query(
            json!([{"answer": "hit"}, {"answer": "no", "claim": null}])
        )),
        EXIT_YES
    );
    assert_eq!(
        query_status(&query(
            json!([{"answer": "no", "claim": "refuted"}, {"answer": "unknown"}])
        )),
        EXIT_NO
    );
    assert_eq!(
        query_status(&query(json!([{"answer": "unknown"}]))),
        EXIT_UNANSWERED
    );
    assert_eq!(
        query_status(&query(json!([{"answer": "invalid-pattern"}]))),
        EXIT_UNASKED
    );
    // A pattern record or a result record the command could not write fails it, beside a refuted
    // claim too.
    assert_eq!(
        query_status(&query(json!([
            {"answer": "no", "claim": "refuted"},
            {"answer": "hit", "cache_error": "cannot write the answer's record: x"}
        ]))),
        EXIT_UNASKED
    );
    assert_eq!(
        query_status(&json!({
            "spec": admitted,
            "programs": [{"class": "comparable", "cache_error": "cannot write the result record: x"}],
            "rows": [{"answer": "no", "claim": "refuted"}],
            "mismatches": []
        })),
        EXIT_UNASKED
    );
    // fuzz: by why it stopped.
    for (stopped, status) in [
        (json!(null), EXIT_YES),
        (json!("equivalent"), EXIT_YES),
        (json!("budget"), EXIT_UNANSWERED),
        (json!("domain-exhausted"), EXIT_UNANSWERED),
        (json!("client-refused"), EXIT_UNANSWERED),
        (json!("unconfirmed"), EXIT_UNANSWERED),
        (json!("assembly-mismatch"), EXIT_UNANSWERED),
        (json!("time-limit"), EXIT_UNANSWERED),
        (json!("cancelled"), EXIT_UNANSWERED),
        (json!("rejected-out"), EXIT_UNASKED),
        (json!("refused"), EXIT_UNASKED),
        (json!("not-comparable"), EXIT_UNASKED),
        (json!("aborted"), EXIT_UNASKED),
    ] {
        assert_eq!(
            fuzz_status(&json!({"stopped": stopped})),
            status,
            "{stopped}"
        );
    }
}
