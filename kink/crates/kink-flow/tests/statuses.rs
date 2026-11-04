//! The runner's mutant statuses have one name in kink-campaign's reports, kink-corpus's harness
//! summary and kink-flow's documents; kink-flow's only other statuses are its own.

use kink_campaign::{MutantStatus, Tally, report_status_name, report_tally};
use kink_corpus::summary::TALLY_KEYS;
use kink_flow::search::{INVALID_MUTATION, STATUSES, UNKILLABLE, status_name};
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
