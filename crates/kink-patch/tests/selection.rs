//! Site derivation, selection policies and candidate folding over
//! `testdata/k/memory.k`.
//!
//! The selection rows are the former `selectionCases` of
//! `mutation-selection-vectors.json`, with their IDs kept. Sites are the
//! bodies of the `write`, `load` and `free` rules and `write`'s right-hand
//! side. An exhaustive row's discovery is derived: every authored position,
//! narrowed to the named sites, and joined with itself for pairs. Tuples no
//! derivation produces (repeated, or from a non-exhaustive discovery) are
//! supplied by hand, which is never exhaustive.

#[path = "../../../testdata/k/support.rs"]
mod support;

use k_rust::kast::Term;
use kink_patch::{
    Baseline, Bindings, CandidateDisposition, CandidateFailureKind, CandidateGeneration,
    Completeness, Discovery, DiscoveryTuple, Edit, InsertPosition, Patch, PatchFailureKind,
    PatchOrigin, SelectionPolicy, SentenceRef, Site, SiteSelector, TermRef, derive_sites, select,
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

    /// The body of rule `name`, or its right-hand side for `write.rhs`.
    fn site(&self, name: &str) -> TermRef {
        let (rule, path): (_, &[u32]) = match name.strip_suffix(".rhs") {
            Some(rule) => (rule, &[0, 1]),
            None => (name, &[0]),
        };
        TermRef::new(
            support::rule(&self.baseline, &format!("MEMORY.{rule}")),
            path,
        )
    }

    fn named(&self, at: &TermRef) -> Option<&'static str> {
        NAMES
            .into_iter()
            .chain(["write.rhs"])
            .find(|name| self.site(name) == *at)
    }

    fn name(&self, at: &TermRef) -> &'static str {
        self.named(at)
            .unwrap_or_else(|| panic!("{at:?} is not a named site"))
    }

    /// The named sites of an exhaustive derivation, as unary tuples of `role`.
    fn derived(&self, role: &str) -> Discovery<'_> {
        derive_sites(&self.baseline, role, &[])
            .filter(|tuple| self.named(&tuple.sites[0].at).is_some())
    }

    /// An exhaustive discovery of exactly the `supplied` tuples: the named
    /// sites, or their pairs when `joined`. Each tuple is unary, or a pair
    /// when joined.
    fn discovery(
        &self,
        supplied: &[&[&str]],
        joined: bool,
        tuple_symmetric: bool,
    ) -> Discovery<'_> {
        let names = |tuple: &DiscoveryTuple| {
            tuple
                .sites
                .iter()
                .map(|site| self.name(&site.at))
                .collect::<Vec<_>>()
        };
        if !joined {
            return self
                .derived("site")
                .filter(|tuple| supplied.iter().any(|wanted| *wanted == names(tuple)));
        }
        self.derived("left")
            .join(&self.derived("right"), tuple_symmetric, |left, right| {
                let pair = [names(left), names(right)].concat();
                supplied.iter().any(|wanted| *wanted == pair)
            })
            .expect("one baseline, no bindings")
    }

    /// A hand-supplied tuple, for a non-exhaustive discovery.
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

    /// Selects under `policy` and folds with [`Self::patch`].
    fn fold<'b>(
        &self,
        discovery: &Discovery<'b>,
        policy: SelectionPolicy,
    ) -> CandidateGeneration<'b> {
        select(discovery, policy, 4)
            .expect("selection")
            .fold("rhs-to-lhs", |origin| self.patch(origin))
            .expect("every origin edits its own rule")
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
    /// Derived when true, supplied by hand (never exhaustive) otherwise.
    exhaustive: bool,
    cap: usize,
    /// Every origin builds the first origin's patch; the fold's sentence
    /// check requires the origins to share that sentence.
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
    // A derivation is already in canonical order; the supplied reversal of
    // `discovery_authority_adversaries_publish_no_scored_generation` is not.
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
    // Two sites of one rule, since an origin may only edit its own sentences.
    Row {
        same_patch: true,
        ..row(
            "identical-patch-dedup-retains-origins",
            SelectionPolicy::Each,
            &[&["write"], &["write.rhs"]],
            Expected::Generated {
                complete: true,
                failure: None,
                site_tuples: &[&["write"], &["write.rhs"]],
                retained: Some(2),
            },
        )
    },
    // No derivation repeats a tuple, so this one is supplied.
    Row {
        exhaustive: false,
        ..row(
            "duplicate-site-rejected",
            SelectionPolicy::Each,
            &[&["write"], &["write"]],
            Expected::Rejected(CandidateFailureKind::DuplicateSite),
        )
    },
];

#[test]
fn selection_rows_fold_discovered_tuples() {
    let memory = Memory::new();
    for row in ROWS {
        let id = row.id;
        let joined = row.policy == SelectionPolicy::TupleEach
            || row.supplied.iter().any(|names| names.len() > 1);
        let discovery = if row.exhaustive {
            memory.discovery(row.supplied, joined, row.tuple_symmetric)
        } else {
            let tuples = row.supplied.iter().map(|names| memory.tuple(names));
            Discovery::supplied(
                &memory.baseline,
                tuples.collect(),
                joined,
                row.tuple_symmetric,
            )
            .unwrap_or_else(|error| panic!("{id}: {error}"))
        };
        assert_eq!(discovery.exhaustive(), row.exhaustive, "{id}");
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
            generation.completeness() == Completeness::CompleteFinite,
            complete,
            "{id}"
        );
        assert_eq!(generation.failure(), failure, "{id}");
        let actual = generation
            .selected_origins()
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
                    .selected_origins()
                    .iter()
                    .map(|origin| origin.discovery_tuples.len())
                    .sum::<usize>(),
                retained,
                "{id}"
            );
        }

        let origins = generation.selected_origins().to_vec();
        let same = origins.first().map(|origin| memory.patch(origin));
        let folded = generation
            .fold("rhs-to-lhs", |origin| {
                if row.same_patch {
                    same.clone().expect("an origin exists")
                } else {
                    memory.patch(origin)
                }
            })
            .unwrap_or_else(|error| panic!("{id}: {error}"));
        let expected_candidates = if row.same_patch {
            origins.len().min(1)
        } else {
            origins.len()
        };
        assert_eq!(folded.candidates().len(), expected_candidates, "{id}");
        assert_eq!(folded.scored(), failure.is_none(), "{id}");
        assert_eq!(
            folded.completeness() == Completeness::CompleteFinite,
            complete,
            "{id}"
        );
        assert_eq!(folded.failure(), failure, "{id}");
        assert_eq!(
            folded
                .candidates()
                .iter()
                .flat_map(|candidate| candidate.origins.iter().cloned())
                .collect::<Vec<_>>(),
            origins,
            "{id}: every origin is kept, in order"
        );
        let dispositions = folded.dispositions();
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
    let discovery = memory.discovery(&[&["write"], &["load"]], false, false);
    let selected = select(&discovery, SelectionPolicy::Each, 1).expect("selection");
    assert_eq!(selected.selected_origins().len(), 1);
    assert_eq!(
        selected.failure(),
        Some(CandidateFailureKind::IncompleteGeneration)
    );
    let same = memory.patch(&selected.selected_origins()[0]);
    let folded = selected
        .fold("rhs-to-lhs", |_| same.clone())
        .expect("the one origin builds its own patch");
    assert!(!folded.scored());
    assert_eq!(folded.candidates().len(), 1);
    assert_eq!(
        folded.candidates()[0].origins.len(),
        1,
        "the capped origin never reaches the fold"
    );
}

#[test]
fn sites_are_derived_in_definition_order_from_memory_k() {
    let memory = Memory::new();
    let bodies = derive_sites(&memory.baseline, "body", &[SiteSelector::Root(0)]);
    assert!(bodies.exhaustive() && !bodies.joined() && !bodies.tuple_symmetric());
    assert_eq!(
        bodies
            .tuples()
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
        load.tuples(),
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
            .tuples()
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
    let folded = generation
        .fold("rhs-to-lhs", |origin| {
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
        })
        .expect("every origin edits its own rule");
    let dispositions = folded.dispositions();
    let [write_disposition, load, free] = dispositions else {
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
            .candidates()
            .iter()
            .map(|candidate| memory.name(&candidate.origins[0].site_tuple[0]))
            .collect::<Vec<_>>(),
        ["load", "free"]
    );
    assert!(
        folded
            .candidates()
            .iter()
            .all(|candidate| candidate.operator == "rhs-to-lhs")
    );
}

/// Plan row S2 (edit authorization), the edit-receipt half of the former
/// `discovery_authority_and_edit_receipt_adversaries_publish_nothing`: every
/// edit must target a sentence of the origin it was built from, and one
/// foreign edit publishes no generation at all. The discovery-authority half
/// is `discovery_authority_adversaries_publish_no_scored_generation`.
#[test]
fn edits_outside_their_origin_publish_nothing() {
    let memory = Memory::new();
    let write = memory.site("write").sentence;
    let free = memory.baseline.sentence(&memory.site("free").sentence);
    let free = free.expect("free").clone();
    let insert = |position| Edit::InsertSentence {
        position,
        ordinal: 0,
        sentence: free.clone(),
    };
    let attribute = |at: &str| Edit::AddAttribute {
        at: memory.site(at).sentence,
        key: "priority".to_owned(),
        value: serde_json::Value::String("40".to_owned()),
    };
    // (id, origin sites, edits, authorized)
    #[rustfmt::skip]
    let rows: Vec<(&str, &[&str], Vec<Edit>, bool)> = vec![
        ("term-in-origin-rule", &["write"], vec![memory.rhs_to_lhs(&memory.site("write"))], true),
        ("term-in-origin-rule-from-a-nested-site", &["write.rhs"], vec![memory.rhs_to_lhs(&memory.site("write"))], true),
        ("term-in-another-rule", &["load"], vec![memory.rhs_to_lhs(&memory.site("write"))], false),
        ("one-foreign-edit-among-authorized-ones", &["write"], vec![memory.rhs_to_lhs(&memory.site("write")), memory.rhs_to_lhs(&memory.site("load"))], false),
        ("joined-origin-authorizes-each-member", &["write", "load"], vec![memory.rhs_to_lhs(&memory.site("write")), memory.rhs_to_lhs(&memory.site("load"))], true),
        ("attribute-of-origin-rule", &["write"], vec![attribute("write")], true),
        ("attribute-of-another-rule", &["write"], vec![attribute("load")], false),
        ("delete-another-rule", &["write"], vec![Edit::DeleteSentence { at: memory.site("load").sentence }], false),
        ("insert-after-origin-rule", &["write"], vec![insert(InsertPosition::After(write.clone()))], true),
        ("insert-before-another-rule", &["write"], vec![insert(InsertPosition::Before(memory.site("load").sentence))], false),
        ("insert-at-origin-module-end", &["write"], vec![insert(InsertPosition::ModuleEnd("MEMORY".to_owned()))], true),
        ("insert-at-another-module-start", &["write"], vec![insert(InsertPosition::ModuleStart("MEMORY-SYNTAX".to_owned()))], false),
    ];
    for (id, sites, edits, authorized) in rows {
        let discovery = memory.discovery(&[sites], sites.len() > 1, false);
        let policy = if sites.len() > 1 {
            SelectionPolicy::TupleEach
        } else {
            SelectionPolicy::Each
        };
        let generation = select(&discovery, policy, 4).expect("selection");
        let patch = Patch::new(edits).expect("nonempty");
        let folded = generation.fold("adversary", |_| patch.clone());
        if authorized {
            // The patch may still be rejected by `apply`; only the fold's
            // authorization is under test.
            let folded = folded.unwrap_or_else(|error| panic!("{id}: {error}"));
            assert_eq!(folded.dispositions().len(), 1, "{id}");
        } else {
            assert_eq!(
                folded.expect_err(id).kind(),
                CandidateFailureKind::UnauthorizedEdit,
                "{id}"
            );
        }
    }

    // A later foreign edit withdraws the earlier origins' candidates too.
    let discovery = memory.discovery(&[&["write"], &["load"]], false, false);
    let generation = select(&discovery, SelectionPolicy::Each, 4).expect("selection");
    let write_patch = memory.patch(&generation.selected_origins()[0]);
    assert_eq!(
        generation
            .fold("adversary", |_| write_patch.clone())
            .expect_err("load's origin edits write")
            .kind(),
        CandidateFailureKind::UnauthorizedEdit
    );
}

/// The discovery-authority half of the former
/// `discovery_authority_and_edit_receipt_adversaries_publish_nothing`. The
/// registry digests are gone, so each adversary becomes a typing rule: a
/// claimant's tuple order is replaced by canonical order, a hand-supplied
/// discovery (forged, or missing a member) is never exhaustive and so never
/// scored, a stale site is rejected, and discoveries of another baseline do
/// not join.
#[test]
fn discovery_authority_adversaries_publish_no_scored_generation() {
    let memory = Memory::new();
    let supplied = |names: &[&[&str]]| {
        Discovery::supplied(
            &memory.baseline,
            names.iter().map(|names| memory.tuple(names)).collect(),
            false,
            false,
        )
    };

    // Claimant tuple order is replaced by canonical order, and the supplied
    // set is not complete even when it is every site the operator selects.
    let reversed = supplied(&[&["load"], &["write"]]).expect("known sites");
    assert!(!reversed.exhaustive());
    let generation = memory.fold(&reversed, SelectionPolicy::Each);
    assert_eq!(
        generation
            .selected_origins()
            .iter()
            .map(|origin| memory.name(&origin.site_tuple[0]))
            .collect::<Vec<_>>(),
        ["write", "load"]
    );
    assert_eq!(generation.completeness(), Completeness::Incomplete);
    assert!(!generation.scored());

    // A forged complete registry: the supplied tuple is exactly the derived
    // one, and the exact policy still refuses to count it.
    let exact = SelectionPolicy::Exact {
        expected_tuple_count: 1,
        expected_tuple_arity: 1,
    };
    let derived = memory.fold(&memory.discovery(&[&["write"]], false, false), exact);
    assert!(derived.scored());
    let forged = memory.fold(&supplied(&[&["write"]]).expect("known site"), exact);
    assert_eq!(
        forged.failure(),
        Some(CandidateFailureKind::IncompleteGeneration)
    );
    assert!(forged.selected_origins().is_empty() && !forged.scored());

    // Stale site metadata: a position the baseline does not have.
    let write = memory.site("write").sentence;
    for (id, at) in [
        ("path-past-a-leaf", TermRef::new(write.clone(), [0, 9])),
        ("unknown-field", TermRef::new(write.clone(), [3])),
        (
            "sentence-past-the-module",
            TermRef::new(SentenceRef::new("MEMORY", 999), [0]),
        ),
        (
            "unknown-module",
            TermRef::new(SentenceRef::new("NOWHERE", write.index), [0]),
        ),
    ] {
        let tuple = DiscoveryTuple {
            sites: vec![Site {
                role: "site".to_owned(),
                at,
            }],
            bindings: Bindings::default(),
        };
        assert_eq!(
            Discovery::supplied(&memory.baseline, vec![tuple], false, false)
                .expect_err(id)
                .kind(),
            CandidateFailureKind::UnknownSite,
            "{id}"
        );
    }

    // Stale registry identity: an equal baseline loaded again is another
    // baseline, and a generation records which one it was derived from.
    let other = Memory::new();
    assert_eq!(
        memory
            .derived("left")
            .join(&other.derived("right"), false, |_, _| true)
            .expect_err("two baselines")
            .kind(),
        CandidateFailureKind::InvalidJoin
    );
    assert!(derived.derived_from(&memory.baseline));
    assert!(!derived.derived_from(&other.baseline));
}

/// An empty generation is not scored, whether nothing was selected or every
/// origin was rejected; the two stay apart in the dispositions.
#[test]
fn empty_generations_are_not_scored() {
    let memory = Memory::new();
    let nothing = derive_sites(
        &memory.baseline,
        "body",
        &[SiteSelector::RuleLabel("MEMORY.nothing".to_owned())],
    );
    let write = memory.discovery(&[&["write"]], false, false);
    let no_change = |origin: &PatchOrigin| {
        let at = origin.site_tuple[0].clone();
        let current = memory.baseline.term(&at).expect("term").clone();
        Patch::new(vec![Edit::ReplaceTerm {
            at,
            expected: current.clone(),
            replacement: current,
        }])
        .expect("one edit")
    };
    // (id, discovery, no-change patch, dispositions, scored)
    #[rustfmt::skip]
    let rows: [(&str, &Discovery<'_>, bool, usize, bool); 3] = [
        ("nothing-selected", &nothing, false, 0, false),
        ("every-origin-rejected", &write, true, 1, false),
        ("one-candidate", &write, false, 1, true),
    ];
    for (id, discovery, rejected, dispositions, scored) in rows {
        let generation = select(discovery, SelectionPolicy::Each, 4)
            .expect("selection")
            .fold("rhs-to-lhs", |origin| {
                if rejected {
                    no_change(origin)
                } else {
                    memory.patch(origin)
                }
            })
            .unwrap_or_else(|error| panic!("{id}: {error}"));
        assert_eq!(
            (generation.completeness(), generation.failure()),
            (Completeness::CompleteFinite, None),
            "{id}"
        );
        assert_eq!(generation.dispositions().len(), dispositions, "{id}");
        assert_eq!(
            generation.candidates().is_empty(),
            !scored,
            "{id}: {:?}",
            generation.dispositions()
        );
        assert_eq!(generation.scored(), scored, "{id}");
    }
}
