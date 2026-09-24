//! Corpus fold truth table (P9), ported from the former `corpus-vectors.json`.
//! Rows use Rust's explicit-exhaustion rule: absence is reported only when the
//! caller supplies an empty-search decision.

use kink_pattern::{
    CorpusComponent, CorpusSkip, EmptySearchDecision, PatternFailureKind, PatternOutcome,
    aggregate_corpus,
};

use CorpusComponent::{Evaluated, Skipped};
use PatternOutcome::{Error, Match, NoMatch, Unknown};

struct Row {
    id: &'static str,
    components: &'static [CorpusComponent],
    shared_setup_failed: bool,
    early_stop_after_match: bool,
    exhausted: bool,
    outcome: PatternOutcome,
    complete_coverage: bool,
    matching_tests: &'static [usize],
    cause: Option<usize>,
}

const ROWS: &[Row] = &[
    Row {
        id: "complete-corpus-absence",
        components: &[Evaluated(NoMatch), Evaluated(NoMatch)],
        shared_setup_failed: false,
        early_stop_after_match: false,
        exhausted: true,
        outcome: NoMatch,
        complete_coverage: true,
        matching_tests: &[],
        cause: None,
    },
    Row {
        id: "corpus-unknown-retained",
        components: &[Evaluated(NoMatch), Evaluated(Unknown)],
        shared_setup_failed: false,
        early_stop_after_match: false,
        exhausted: true,
        outcome: Unknown,
        complete_coverage: false,
        matching_tests: &[],
        cause: Some(1),
    },
    Row {
        id: "match-dominates-local-unknown",
        components: &[Evaluated(Unknown), Evaluated(Match)],
        shared_setup_failed: false,
        early_stop_after_match: false,
        exhausted: true,
        outcome: Match,
        complete_coverage: false,
        matching_tests: &[1],
        cause: None,
    },
    Row {
        id: "local-error-is-incomplete-not-global",
        components: &[Evaluated(NoMatch), Evaluated(Error)],
        shared_setup_failed: false,
        early_stop_after_match: false,
        exhausted: true,
        outcome: Unknown,
        complete_coverage: false,
        matching_tests: &[],
        cause: Some(1),
    },
    Row {
        id: "invalid-shared-setup-is-global-error",
        components: &[
            Skipped(CorpusSkip::SharedSetupFailed),
            Skipped(CorpusSkip::SharedSetupFailed),
        ],
        shared_setup_failed: true,
        early_stop_after_match: false,
        exhausted: true,
        outcome: Error,
        complete_coverage: false,
        matching_tests: &[],
        cause: None,
    },
    Row {
        id: "early-match-retains-skipped-tests",
        components: &[
            Evaluated(Match),
            Skipped(CorpusSkip::MatchFound),
            Skipped(CorpusSkip::MatchFound),
        ],
        shared_setup_failed: false,
        early_stop_after_match: true,
        exhausted: false,
        outcome: Match,
        complete_coverage: false,
        matching_tests: &[0],
        cause: None,
    },
    Row {
        id: "collect-all-after-match-by-default",
        components: &[Evaluated(Match), Evaluated(NoMatch), Evaluated(Unknown)],
        shared_setup_failed: false,
        early_stop_after_match: false,
        exhausted: false,
        outcome: Match,
        complete_coverage: false,
        matching_tests: &[0],
        cause: None,
    },
    // Shared-setup failure under early stop still skips every test as setup-failed.
    Row {
        id: "shared-setup-failure-precedes-early-stop",
        components: &[
            Skipped(CorpusSkip::SharedSetupFailed),
            Skipped(CorpusSkip::SharedSetupFailed),
        ],
        shared_setup_failed: true,
        early_stop_after_match: true,
        exhausted: false,
        outcome: Error,
        complete_coverage: false,
        matching_tests: &[],
        cause: None,
    },
    // The first failing test in manifest order is the cause, not a later one.
    Row {
        id: "first-failing-test-is-the-cause",
        components: &[Evaluated(NoMatch), Evaluated(Unknown), Evaluated(Unknown)],
        shared_setup_failed: false,
        early_stop_after_match: false,
        exhausted: true,
        outcome: Unknown,
        complete_coverage: false,
        matching_tests: &[],
        cause: Some(1),
    },
    // Rust rule: clean exhaustion without an empty-search decision is not absence.
    Row {
        id: "absence-without-exhaustion-evidence",
        components: &[Evaluated(NoMatch), Evaluated(NoMatch)],
        shared_setup_failed: false,
        early_stop_after_match: false,
        exhausted: false,
        outcome: Unknown,
        complete_coverage: false,
        matching_tests: &[],
        cause: None,
    },
    // Early stop is only a permission: a match on the last test skips nothing.
    Row {
        id: "early-stop-on-last-test-is-complete",
        components: &[Evaluated(NoMatch), Evaluated(Match)],
        shared_setup_failed: false,
        early_stop_after_match: true,
        exhausted: false,
        outcome: Match,
        complete_coverage: true,
        matching_tests: &[1],
        cause: None,
    },
    // Only shared-setup failure is a corpus-scoped Error; test-scoped errors leave the
    // corpus Unknown, as a path-local error stop leaves `evaluate` Unknown. The former
    // BAG-16 fold ranked test errors first and reported Error here.
    Row {
        id: "all-local-errors-are-unknown",
        components: &[Evaluated(Error), Evaluated(Error)],
        shared_setup_failed: false,
        early_stop_after_match: false,
        exhausted: true,
        outcome: Unknown,
        complete_coverage: false,
        matching_tests: &[],
        cause: Some(0),
    },
    // An infrastructure error is the cause even behind an earlier unknown.
    Row {
        id: "local-error-outranks-earlier-unknown-as-cause",
        components: &[Evaluated(Unknown), Evaluated(Error)],
        shared_setup_failed: false,
        early_stop_after_match: false,
        exhausted: true,
        outcome: Unknown,
        complete_coverage: false,
        matching_tests: &[],
        cause: Some(1),
    },
    Row {
        id: "local-error-does-not-override-match",
        components: &[Evaluated(Error), Evaluated(Match)],
        shared_setup_failed: false,
        early_stop_after_match: false,
        exhausted: true,
        outcome: Match,
        complete_coverage: false,
        matching_tests: &[1],
        cause: None,
    },
];

#[test]
fn corpus_fold_matches_the_truth_table() {
    for row in ROWS {
        let folded = aggregate_corpus(
            row.components,
            row.shared_setup_failed,
            row.early_stop_after_match,
            row.exhausted.then_some(EmptySearchDecision),
        )
        .unwrap_or_else(|failure| panic!("{}: {failure}", row.id));
        assert_eq!(folded.outcome, row.outcome, "{}: outcome", row.id);
        assert_eq!(
            folded.complete_coverage, row.complete_coverage,
            "{}: coverage",
            row.id
        );
        assert_eq!(
            folded.matching_tests, row.matching_tests,
            "{}: matching tests",
            row.id
        );
        assert_eq!(folded.cause, row.cause, "{}: cause", row.id);
    }
}

#[test]
fn corpus_fold_rejects_unjustified_schedules() {
    let rejected: &[(&str, &[CorpusComponent], bool, bool)] = &[
        ("empty corpus", &[], false, false),
        (
            "shared-setup failure retained an executed result",
            &[Evaluated(Match), Skipped(CorpusSkip::SharedSetupFailed)],
            true,
            false,
        ),
        (
            "shared-setup skip without a setup failure",
            &[Skipped(CorpusSkip::SharedSetupFailed), Evaluated(NoMatch)],
            false,
            false,
        ),
        (
            "skip without early stop",
            &[Evaluated(Match), Skipped(CorpusSkip::MatchFound)],
            false,
            false,
        ),
        (
            "early stop skipped a test before the first match",
            &[Skipped(CorpusSkip::MatchFound), Evaluated(Match)],
            false,
            true,
        ),
        (
            "early stop kept evaluating after the first match",
            &[
                Evaluated(Match),
                Skipped(CorpusSkip::MatchFound),
                Evaluated(NoMatch),
            ],
            false,
            true,
        ),
        (
            "early stop skipped without any match",
            &[Evaluated(NoMatch), Skipped(CorpusSkip::MatchFound)],
            false,
            true,
        ),
        (
            "early stop suffix labelled as setup failure",
            &[Evaluated(Match), Skipped(CorpusSkip::SharedSetupFailed)],
            false,
            true,
        ),
    ];
    for (label, components, shared_setup_failed, early_stop) in rejected {
        let failure = aggregate_corpus(
            components,
            *shared_setup_failed,
            *early_stop,
            Some(EmptySearchDecision),
        )
        .expect_err(label);
        assert_eq!(failure.kind(), PatternFailureKind::InvalidCorpus, "{label}");
    }
}
