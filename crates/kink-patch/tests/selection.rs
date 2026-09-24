//! Site derivation, selection policies and candidate folding over
//! `testdata/k/memory.k`.
//!
//! The selection rows are the former `selectionCases` of
//! `mutation-selection-vectors.json`, with their IDs kept. Sites are the
//! bodies of the `write`, `load` and `free` rules; tuples that
//! `derive_sites` does not produce (joined, repeated, or from a
//! non-exhaustive discovery) are built by hand from those sites.

#[path = "../../../testdata/k/support.rs"]
mod support;

use k_rust::kast::Term;
use kink_patch::{
    Baseline, Bindings, CandidateDisposition, CandidateFailureKind, Completeness, Discovery,
    DiscoveryTuple, Edit, Patch, PatchFailureKind, PatchOrigin, SelectionPolicy, Site,
    SiteSelector, TermRef, derive_sites, select,
};

const NAMES: [&str; 3] = ["write", "load", "free"];

struct Memory {
    baseline: Baseline,
}

impl Memory {
    fn new() -> Self {
        Self {
            baseline: support::load("memory.k"),
        }
    }

    /// The body of rule `name`.
    fn site(&self, name: &str) -> TermRef {
        TermRef::new(
            support::rule(&self.baseline, &format!("MEMORY.{name}")),
            [0],
        )
    }

    fn name(&self, at: &TermRef) -> &'static str {
        NAMES
            .into_iter()
            .find(|name| self.site(name) == *at)
            .unwrap_or_else(|| panic!("{at:?} is not a rule body"))
    }

    fn tuple(&self, names: &[&str]) -> DiscoveryTuple {
        DiscoveryTuple {
            sites: names
                .iter()
                .map(|name| Site {
                    role: if *name == "write" { "left" } else { "right" }.to_owned(),
                    at: self.site(name),
                })
                .collect(),
            bindings: Bindings::default(),
        }
    }

    /// Replaces the right-hand side of the rewrite at `body` by its left-hand side.
    fn rhs_to_lhs(&self, body: &TermRef) -> Edit {
        let side = |step| {
            let mut path = body.path.0.clone();
            path.push(step);
            TermRef::new(body.sentence.clone(), path)
        };
        let term = |at: &TermRef| -> Term { self.baseline.term(at).expect("term").clone() };
        Edit::ReplaceTerm {
            at: side(1),
            expected: term(&side(1)),
            replacement: term(&side(0)),
        }
    }

    /// One edit per site of the origin.
    fn patch(&self, origin: &PatchOrigin) -> Patch {
        Patch::new(
            origin
                .site_tuple
                .iter()
                .map(|at| self.rhs_to_lhs(at))
                .collect(),
        )
        .expect("nonempty origin")
    }
}

enum Expected {
    /// `select` publishes no generation.
    Rejected(CandidateFailureKind),
    Generated {
        complete: bool,
        failure: Option<CandidateFailureKind>,
        site_tuples: &'static [&'static [&'static str]],
        /// Discovery tuples kept across all origins, when the row names it.
        retained: Option<usize>,
    },
}

struct Row {
    id: &'static str,
    policy: SelectionPolicy,
    supplied: &'static [&'static [&'static str]],
    tuple_symmetric: bool,
    exhaustive: bool,
    cap: usize,
    /// Every origin builds the same patch.
    same_patch: bool,
    expected: Expected,
}

const EXACT_ONE: SelectionPolicy = SelectionPolicy::Exact {
    expected_tuple_count: 1,
    expected_tuple_arity: 1,
};

const EXACT_PAIR: SelectionPolicy = SelectionPolicy::Exact {
    expected_tuple_count: 1,
    expected_tuple_arity: 2,
};

const fn row(
    id: &'static str,
    policy: SelectionPolicy,
    supplied: &'static [&'static [&'static str]],
    expected: Expected,
) -> Row {
    Row {
        id,
        policy,
        supplied,
        tuple_symmetric: false,
        exhaustive: true,
        cap: 4,
        same_patch: false,
        expected,
    }
}

const fn complete(site_tuples: &'static [&'static [&'static str]]) -> Expected {
    Expected::Generated {
        complete: true,
        failure: None,
        site_tuples,
        retained: None,
    }
}

const fn failed(failure: CandidateFailureKind) -> Expected {
    Expected::Generated {
        complete: true,
        failure: Some(failure),
        site_tuples: &[],
        retained: None,
    }
}

const ROWS: &[Row] = &[
    row(
        "exact-one",
        EXACT_ONE,
        &[&["write"]],
        complete(&[&["write"]]),
    ),
    row(
        "exact-zero",
        EXACT_ONE,
        &[],
        failed(CandidateFailureKind::CardinalityMismatch),
    ),
    row(
        "exact-excessive",
        EXACT_ONE,
        &[&["write"], &["load"]],
        failed(CandidateFailureKind::CardinalityMismatch),
    ),
    row(
        "exact-coupled-tuple",
        EXACT_PAIR,
        &[&["write", "load"]],
        complete(&[&["write", "load"]]),
    ),
    row(
        "exact-wrong-tuple-arity",
        EXACT_PAIR,
        &[&["write"]],
        failed(CandidateFailureKind::InvalidJoin),
    ),
    row(
        "each-canonical-order",
        SelectionPolicy::Each,
        &[&["free"], &["write"], &["load"]],
        complete(&[&["write"], &["load"], &["free"]]),
    ),
    // The host builds no cartesian product: only the supplied joins appear.
    row(
        "tuple-each-uses-only-supplied-joins",
        SelectionPolicy::TupleEach,
        &[&["write", "load"], &["write", "free"]],
        complete(&[&["write", "load"], &["write", "free"]]),
    ),
    Row {
        tuple_symmetric: true,
        ..row(
            "tuple-each-symmetric-dedup",
            SelectionPolicy::TupleEach,
            &[&["load", "write"], &["write", "load"]],
            Expected::Generated {
                complete: true,
                failure: None,
                site_tuples: &[&["write", "load"]],
                retained: Some(2),
            },
        )
    },
    // One atomic instance, hence one mutant.
    row(
        "all-matches-one-atomic-instance",
        SelectionPolicy::AllMatches,
        &[&["free"], &["write"], &["load"]],
        complete(&[&["write", "load", "free"]]),
    ),
    Row {
        exhaustive: false,
        cap: 2,
        ..row(
            "candidate-cap-is-incomplete",
            SelectionPolicy::Each,
            &[&["write"], &["load"], &["free"]],
            Expected::Generated {
                complete: false,
                failure: Some(CandidateFailureKind::IncompleteGeneration),
                site_tuples: &[&["write"], &["load"]],
                retained: None,
            },
        )
    },
    Row {
        same_patch: true,
        ..row(
            "identical-patch-dedup-retains-origins",
            SelectionPolicy::Each,
            &[&["write"], &["load"]],
            Expected::Generated {
                complete: true,
                failure: None,
                site_tuples: &[&["write"], &["load"]],
                retained: Some(2),
            },
        )
    },
    row(
        "duplicate-site-rejected",
        SelectionPolicy::Each,
        &[&["write"], &["write"]],
        Expected::Rejected(CandidateFailureKind::DuplicateSite),
    ),
];

#[test]
fn selection_rows_fold_discovered_tuples() {
    let memory = Memory::new();
    for row in ROWS {
        let id = row.id;
        let tuples = row
            .supplied
            .iter()
            .map(|names| memory.tuple(names))
            .collect::<Vec<_>>();
        let discovery = Discovery {
            joined: row.policy == SelectionPolicy::TupleEach
                || tuples.iter().any(|tuple| tuple.sites.len() > 1),
            tuples,
            exhaustive: row.exhaustive,
            tuple_symmetric: row.tuple_symmetric,
        };
        let selection = select(&discovery, row.policy, row.cap);
        let (complete, failure, site_tuples, retained) = match row.expected {
            Expected::Rejected(kind) => {
                assert_eq!(
                    selection.expect_err("no generation is published").kind(),
                    kind,
                    "{id}"
                );
                continue;
            }
            Expected::Generated {
                complete,
                failure,
                site_tuples,
                retained,
            } => (complete, failure, site_tuples, retained),
        };
        let generation = selection.unwrap_or_else(|error| panic!("{id}: {error}"));
        assert_eq!(
            generation.completeness == Completeness::CompleteFinite,
            complete,
            "{id}"
        );
        assert_eq!(generation.failure, failure, "{id}");
        assert_eq!(generation.scored, failure.is_none(), "{id}");
        let actual = generation
            .selected_origins
            .iter()
            .map(|origin| {
                origin
                    .site_tuple
                    .iter()
                    .map(|at| memory.name(at))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        assert_eq!(actual, site_tuples, "{id}");
        if let Some(retained) = retained {
            assert_eq!(
                generation
                    .selected_origins
                    .iter()
                    .map(|origin| origin.discovery_tuples.len())
                    .sum::<usize>(),
                retained,
                "{id}"
            );
        }

        let origins = generation.selected_origins.clone();
        let same = origins.first().map(|origin| memory.patch(origin));
        let (folded, dispositions) = generation.fold(&memory.baseline, "rhs-to-lhs", |origin| {
            if row.same_patch {
                same.clone().expect("an origin exists")
            } else {
                memory.patch(origin)
            }
        });
        let expected_candidates = if row.same_patch {
            origins.len().min(1)
        } else {
            origins.len()
        };
        assert_eq!(folded.candidates.len(), expected_candidates, "{id}");
        assert_eq!(
            folded
                .candidates
                .iter()
                .flat_map(|candidate| candidate.origins.iter().cloned())
                .collect::<Vec<_>>(),
            origins,
            "{id}: every origin is kept, in order"
        );
        assert!(
            dispositions
                .iter()
                .all(|disposition| matches!(disposition, CandidateDisposition::Mutant(_))),
            "{id}: {dispositions:?}"
        );
    }
}

/// Formerly the `binding-order-normalized` row: bindings compare equal
/// whatever order they were supplied in.
#[test]
fn bindings_are_name_sorted_by_construction() {
    let address = Term::apply("addr", vec![Term::apply("z", vec![])]);
    let value = Term::apply("s", vec![Term::apply("z", vec![])]);
    let supplied = Bindings::new(vec![
        ("V".to_owned(), value.clone()),
        ("A".to_owned(), address.clone()),
    ])
    .expect("valid bindings");
    let sorted = Bindings::new(vec![
        ("A".to_owned(), address.clone()),
        ("V".to_owned(), value.clone()),
    ])
    .expect("valid bindings");
    assert_eq!(supplied, sorted);
    assert_eq!(
        supplied
            .as_slice()
            .iter()
            .map(|(name, _)| name.as_str())
            .collect::<Vec<_>>(),
        ["A", "V"]
    );
    for invalid in [
        vec![("A".to_owned(), address.clone()), ("A".to_owned(), value)],
        vec![("a".to_owned(), address)],
    ] {
        assert_eq!(
            Bindings::new(invalid).expect_err("invalid bindings").kind(),
            CandidateFailureKind::InvalidBinding
        );
    }
}

#[test]
fn cap_is_applied_before_patch_deduplication() {
    let memory = Memory::new();
    let discovery = Discovery {
        tuples: vec![memory.tuple(&["write"]), memory.tuple(&["load"])],
        exhaustive: true,
        joined: false,
        tuple_symmetric: false,
    };
    let selected = select(&discovery, SelectionPolicy::Each, 1).expect("selection");
    assert_eq!(selected.selected_origins.len(), 1);
    assert_eq!(
        selected.failure,
        Some(CandidateFailureKind::IncompleteGeneration)
    );
    assert!(!selected.scored);
    let same = memory.patch(&selected.selected_origins[0]);
    let (folded, _) = selected.fold(&memory.baseline, "rhs-to-lhs", |_| same.clone());
    assert_eq!(folded.candidates.len(), 1);
    assert_eq!(
        folded.candidates[0].origins.len(),
        1,
        "the capped origin never reaches the fold"
    );
}

#[test]
fn sites_are_derived_in_definition_order_from_memory_k() {
    let memory = Memory::new();
    let bodies = derive_sites(&memory.baseline, "body", &[SiteSelector::Root(0)]);
    assert!(bodies.exhaustive && !bodies.joined && !bodies.tuple_symmetric);
    assert_eq!(
        bodies
            .tuples
            .iter()
            .map(|tuple| {
                assert_eq!(tuple.bindings, Bindings::default());
                let [site] = tuple.sites.as_slice() else {
                    panic!("derived tuples are unary");
                };
                assert_eq!(site.role, "body");
                memory.name(&site.at)
            })
            .collect::<Vec<_>>(),
        NAMES
    );

    let load = derive_sites(
        &memory.baseline,
        "body",
        &[
            SiteSelector::RuleLabel("MEMORY.load".to_owned()),
            SiteSelector::Root(0),
        ],
    );
    assert_eq!(
        load.tuples,
        [DiscoveryTuple {
            sites: vec![Site {
                role: "body".to_owned(),
                at: memory.site("load"),
            }],
            bindings: Bindings::default(),
        }]
    );

    // Head clauses match at any depth: `s(L)` on the left and `s(N)` on the
    // right of `increment`.
    let counter = support::load("counter.k");
    let increment = support::rule(&counter, "COUNTER.increment");
    let successors = derive_sites(
        &counter,
        "successor",
        &[SiteSelector::Head {
            label: "s".to_owned(),
        }],
    );
    assert_eq!(
        successors
            .tuples
            .iter()
            .map(|tuple| tuple.sites[0].at.clone())
            .collect::<Vec<_>>(),
        [
            TermRef::new(increment.clone(), [0, 0, 1]),
            TermRef::new(increment, [0, 1, 0]),
        ]
    );
}

/// S5 row 1: a candidate whose patch does not apply, such as a no-change
/// patch, is a rejected disposition and never a mutant.
#[test]
fn no_change_patch_is_a_rejected_disposition_never_a_mutant() {
    let memory = Memory::new();
    let discovery = derive_sites(&memory.baseline, "body", &[SiteSelector::Root(0)]);
    let generation = select(&discovery, SelectionPolicy::Each, 4).expect("selection");
    let write = memory.site("write");
    let (folded, dispositions) = generation.fold(&memory.baseline, "rhs-to-lhs", |origin| {
        if origin.site_tuple == [write.clone()] {
            let at = TermRef::new(write.sentence.clone(), [0, 1]);
            let current = memory.baseline.term(&at).expect("term").clone();
            Patch::new(vec![Edit::ReplaceTerm {
                at,
                expected: current.clone(),
                replacement: current,
            }])
            .expect("one edit")
        } else {
            memory.patch(origin)
        }
    });
    let [write_disposition, load, free] = dispositions.as_slice() else {
        panic!("one disposition per origin: {dispositions:?}");
    };
    match write_disposition {
        CandidateDisposition::Rejected(failure) => {
            assert_eq!(failure.kind(), PatchFailureKind::NoChange);
        }
        other => panic!("expected a rejection, got {other:?}"),
    }
    assert_eq!(
        [load, free],
        [
            &CandidateDisposition::Mutant(0),
            &CandidateDisposition::Mutant(1)
        ]
    );
    assert_eq!(
        folded
            .candidates
            .iter()
            .map(|candidate| memory.name(&candidate.origins[0].site_tuple[0]))
            .collect::<Vec<_>>(),
        ["load", "free"]
    );
    assert!(
        folded
            .candidates
            .iter()
            .all(|candidate| candidate.operator == "rhs-to-lhs")
    );
}
