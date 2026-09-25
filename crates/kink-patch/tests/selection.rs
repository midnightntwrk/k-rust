//! Site derivation, selection policies and candidate folding over
//! `testdata/k/memory.k`.
//!
//! The selection rows are the former `selectionCases` of
//! `mutation-selection-vectors.json`, with their IDs kept. Sites are the
//! bodies of the `write`, `load` and `free` rules and `write`'s right-hand
//! side. An exhaustive row's discovery is derived by clauses: each named
//! site's rule label and path, joined for pairs, and the tuples united.
//! Tuples no derivation produces (repeated, or from a non-exhaustive
//! discovery) are supplied by hand, which is never exhaustive.
//!
//! The site-derivation rows are the former selector registries
//! (`counter-mutation-site-registry.json`, `mutation-site-registry.json`)
//! over `testdata/k`, and the operators are the two those registries fed:
//! `counter-plus-one-site` and `coupled-memory-representation`.

#[path = "../../../testdata/k/support.rs"]
mod support;

use k_rust::definition::sentence_mut;
use k_rust::kast::{Sort, Term};
use kink_patch::{
    Baseline, Bindings, CandidateDisposition, CandidateFailureKind, CandidateGeneration,
    Completeness, Discovery, DiscoveryTuple, Edit, InsertPosition, Patch, PatchFailureKind,
    PatchOrigin, SelectionPolicy, SentenceRef, Site, SiteSelector, TermRef, apply, derive_sites,
    select,
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

    /// The label of the rule of site `name`, and the site's path in it: the
    /// rule's body, or its right-hand side for `write.rhs`.
    fn located(name: &str) -> (String, &'static [u32]) {
        match name.strip_suffix(".rhs") {
            Some(rule) => (format!("MEMORY.{rule}"), &[0, 1]),
            None => (format!("MEMORY.{name}"), &[0]),
        }
    }

    fn site(&self, name: &str) -> TermRef {
        let (rule, path) = Self::located(name);
        TermRef::new(support::rule(&self.baseline, &rule), path)
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

    /// The exhaustive derivation of site `name` alone, by its rule label and
    /// path clauses, as a unary tuple of `role`.
    fn derived(&self, role: &str, name: &str) -> Discovery<'_> {
        let (rule, at) = Self::located(name);
        derive_sites(&self.baseline, role, &[label(&rule), path(at)]).expect("no bindings")
    }

    /// An exhaustive discovery of exactly the `supplied` tuples, declared by
    /// clauses: the union of each named site's derivation, or of each pair's
    /// join when `joined`. Each tuple is unary, or a pair when joined.
    fn discovery(
        &self,
        supplied: &[&[&str]],
        joined: bool,
        tuple_symmetric: bool,
    ) -> Discovery<'_> {
        let nothing = Discovery::empty(&self.baseline, joined, tuple_symmetric);
        supplied
            .iter()
            .map(|names| match (joined, names) {
                (false, [name]) => self.derived("site", name),
                (true, [left, right]) => self
                    .derived("left", left)
                    .join(&self.derived("right", right), tuple_symmetric)
                    .expect("one baseline, no bindings"),
                _ => panic!("{names:?} is not a tuple of this shape"),
            })
            .fold(nothing, |all, next| {
                all.union(&next).expect("one baseline and shape")
            })
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
    // `forged_or_foreign_discoveries_publish_no_scored_generation` is not.
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

#[test]
fn union_keeps_exhaustiveness_and_shape() {
    let memory = Memory::new();
    let write = memory.derived("site", "write");
    let load = memory.derived("site", "load");
    let supplied = Discovery::supplied(&memory.baseline, write.tuples().to_vec(), false, false)
        .expect("known site");
    let filtered = write.clone().filter(|_| true);
    let other_role = memory.derived("other", "write");
    #[rustfmt::skip]
    let rows = [
        ("both-exhaustive", &write, &load, true, vec![write.tuples()[0].clone(), load.tuples()[0].clone()]),
        ("supplied-input", &supplied, &load, false, vec![supplied.tuples()[0].clone(), load.tuples()[0].clone()]),
        ("supplied-input-reversed", &load, &supplied, false, vec![load.tuples()[0].clone(), supplied.tuples()[0].clone()]),
        ("filtered-input", &write, &filtered, false, write.tuples().to_vec()),
        ("identical-tuples-once", &write, &write, true, write.tuples().to_vec()),
        ("same-site-two-roles", &write, &other_role, true, vec![write.tuples()[0].clone(), other_role.tuples()[0].clone()]),
    ];
    for (id, left, right, exhaustive, expected) in rows {
        let union = left
            .union(right)
            .unwrap_or_else(|error| panic!("{id}: {error}"));
        assert_eq!(union.tuples(), expected, "{id}");
        assert_eq!(union.exhaustive(), exhaustive, "{id}");
        if id == "same-site-two-roles" {
            assert_eq!(
                select(&union, SelectionPolicy::Each, 4)
                    .expect_err(id)
                    .kind(),
                CandidateFailureKind::DuplicateSite,
                "{id}"
            );
        }
    }

    let joined = write.join(&load, false).expect("one baseline");
    let symmetric = write.join(&load, true).expect("one baseline");
    #[rustfmt::skip]
    let incompatible = [
        ("joined-with-unjoined", &joined, &write),
        ("symmetric-with-asymmetric", &symmetric, &joined),
    ];
    for (id, left, right) in incompatible {
        assert_eq!(
            left.union(right).expect_err(id).kind(),
            CandidateFailureKind::InvalidJoin,
            "{id}"
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
    let bodies = derive_sites(&memory.baseline, "body", &[SiteSelector::Path(vec![0])])
        .expect("no bindings");
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
            SiteSelector::Path(vec![0]),
        ],
    )
    .expect("no bindings");
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
    )
    .expect("no bindings");
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
    let discovery = derive_sites(&memory.baseline, "body", &[SiteSelector::Path(vec![0])])
        .expect("no bindings");
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

/// Plan row S2: every edit must target a sentence of its origin, and one
/// foreign edit prevents the entire generation from being published.
/// Discovery authority is covered by
/// `forged_or_foreign_discoveries_publish_no_scored_generation`.
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

/// Supplied tuple order is replaced by canonical order. A hand-supplied
/// discovery is never exhaustive and cannot be scored, even when it includes
/// every derived site. A closure-narrowed discovery is also never exhaustive.
/// Stale sites are rejected, and discoveries of another baseline cannot join
/// or unite with this baseline's discoveries.
#[test]
fn forged_or_foreign_discoveries_publish_no_scored_generation() {
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

    // A member dropped by code rather than by a declared selector: a closure
    // narrowing an exhaustive derivation is never exhaustive, so leaving out
    // `load` is never scored. The same sites declared by clauses are.
    let bodies = derive_sites(&memory.baseline, "site", &[path(&[0])]).expect("no bindings");
    assert!(bodies.exhaustive());
    let narrowed = bodies.filter(|tuple| memory.name(&tuple.sites[0].at) != "load");
    assert!(!narrowed.exhaustive());
    let declared = memory.discovery(&[&["write"], &["free"]], false, false);
    assert!(declared.exhaustive());
    for (id, discovery, scored) in [("closure", &narrowed, false), ("clauses", &declared, true)] {
        let generation = memory.fold(discovery, SelectionPolicy::Each);
        assert_eq!(
            generation
                .selected_origins()
                .iter()
                .map(|origin| memory.name(&origin.site_tuple[0]))
                .collect::<Vec<_>>(),
            ["write", "free"],
            "{id}"
        );
        assert_eq!(generation.candidates().len(), 2, "{id}");
        assert_eq!(generation.scored(), scored, "{id}");
    }

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
            .derived("left", "write")
            .join(&other.derived("right", "load"), false)
            .expect_err("two baselines")
            .kind(),
        CandidateFailureKind::InvalidJoin
    );
    assert_eq!(
        memory
            .derived("site", "write")
            .union(&other.derived("site", "load"))
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
    let nothing = Discovery::empty(&memory.baseline, false, false);
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

fn label(label: &str) -> SiteSelector {
    SiteSelector::RuleLabel(label.to_owned())
}

fn path(path: &[u32]) -> SiteSelector {
    SiteSelector::Path(path.to_vec())
}

fn sort(name: &str) -> SiteSelector {
    SiteSelector::Sort(Sort::new(name))
}

fn head(label: &str) -> SiteSelector {
    SiteSelector::Head {
        label: label.to_owned(),
    }
}

fn bind(name: &str) -> SiteSelector {
    SiteSelector::Bind(name.to_owned())
}

#[test]
fn selector_references_must_resolve() {
    let memory = Memory::new();
    let counter = support::load("counter.k");
    let derived = memory.derived("site", "write");
    #[rustfmt::skip]
    let rows = [
        ("unknown-label", &memory.baseline, vec![label("MEMORY.nothing")]),
        ("typo-in-a-union-member", &memory.baseline, vec![label("MEMORY.wirte"), path(&[0])]),
        ("label-with-a-path-past-a-leaf", &counter, vec![label("COUNTER.branch"), path(&[0, 1, 99])]),
    ];
    for (id, baseline, selector) in rows {
        let result = derive_sites(baseline, "site", &selector);
        let result = if id == "typo-in-a-union-member" {
            result.and_then(|member| derived.union(&member))
        } else {
            result
        };
        assert_eq!(
            result.expect_err(id).kind(),
            CandidateFailureKind::UnknownSite,
            "{id}"
        );
    }

    let unmet = derive_sites(
        &counter,
        "site",
        &[label("COUNTER.branch"), path(&[0, 1]), sort("Bool")],
    )
    .expect("resolved selector");
    assert!(unmet.tuples().is_empty() && unmet.exhaustive());
    let invalid = derive_sites(
        &memory.baseline,
        "site",
        &[label("MEMORY.nothing"), bind("a"), bind("a")],
    );
    assert_eq!(
        invalid.expect_err("invalid bind names first").kind(),
        CandidateFailureKind::InvalidBinding
    );
    let fallback_requires = TermRef::new(support::rule(&counter, "COUNTER.fallback"), [1]);
    assert!(counter.term(&fallback_requires).is_some());
    let empty = Discovery::empty(&memory.baseline, false, false);
    let union = empty.union(&derived).expect("same shape");
    assert_eq!(union.tuples(), derived.tuples());
    assert!(union.exhaustive());
}

/// Expected sites as (rule label, path).
type Sites = &'static [(&'static str, &'static [u32])];

/// (id, baseline, selector, expected sites, bound names)
type DerivationRow<'a> = (
    &'static str,
    &'a Baseline,
    Vec<SiteSelector>,
    Sites,
    &'static [&'static str],
);

/// The derived sites as (rule label, path).
fn labelled_sites(baseline: &Baseline, discovery: &Discovery<'_>) -> Vec<(String, Vec<u32>)> {
    discovery
        .tuples()
        .iter()
        .flat_map(|tuple| &tuple.sites)
        .map(|site| {
            let rule = baseline.sentence(&site.at.sentence).expect("sentence");
            let label = rule
                .attributes()
                .string(k_rust::definition::AttributeKey::Label)
                .expect("labelled rule");
            (label.to_owned(), site.at.path.0.clone())
        })
        .collect()
}

/// Plan row S4: sites are derived from the definition by conjunctive clauses
/// (label, term path, sort, head), in site order, and each binds its term to
/// the selector's `Bind` names.
#[test]
fn sites_are_derived_from_selector_clauses_with_bindings() {
    let counter = support::load("counter.k");
    let memory = support::load("memory.k");
    #[rustfmt::skip]
    let rows: [DerivationRow<'_>; 10] = [
        // The counter increment site is the `s(N)` argument of `counter`.
        ("counter-increment-expression", &counter, vec![path(&[0, 1, 0]), sort("Nat"), head("s"), bind("E")], &[("COUNTER.increment", &[0, 1, 0])], &["E"]),
        // Without a label clause, labelled rules match too.
        ("no-label-clause-matches-labelled-rules", &counter, vec![path(&[0, 1]), sort("Control")], &[("COUNTER.branch", &[0, 1]), ("COUNTER.fallback", &[0, 1])], &[]),
        ("label-clause-narrows", &counter, vec![label("COUNTER.branch"), path(&[0, 1]), sort("Control")], &[("COUNTER.branch", &[0, 1])], &[]),
        ("sort-clauses-are-conjunctive", &counter, vec![path(&[0, 1, 0]), sort("Nat"), sort("Bool")], &[], &[]),
        ("sort-is-exact-not-a-supersort", &counter, vec![path(&[0, 1, 0]), sort("KItem")], &[], &[]),
        ("wrong-head", &counter, vec![path(&[0, 1]), sort("Counter"), head("selected")], &[], &[]),
        ("path-past-a-leaf", &counter, vec![path(&[0, 1, 99]), sort("Nat")], &[], &[]),
        // A variable takes the sort of the cast the loader wraps it in; the
        // cast and the variable are two positions of that sort.
        ("variable-under-a-cast-has-the-cast-sort", &counter, vec![label("COUNTER.branch"), sort("Bool"), bind("B")], &[("COUNTER.branch", &[0, 0, 0]), ("COUNTER.branch", &[0, 0, 0, 0]), ("COUNTER.branch", &[0, 1, 0]), ("COUNTER.branch", &[0, 1, 0, 0]), ("COUNTER.branch", &[1]), ("COUNTER.branch", &[1, 0]), ("COUNTER.branch", &[2])], &["B"]),
        // The two clauses of the former `mutation-site-registry.json`.
        ("memory-write-address", &memory, vec![label("MEMORY.write"), path(&[0, 0, 0]), sort("Address"), bind("A")], &[("MEMORY.write", &[0, 0, 0])], &["A"]),
        ("memory-load-address", &memory, vec![label("MEMORY.load"), path(&[0, 0, 0]), sort("Address"), bind("A")], &[("MEMORY.load", &[0, 0, 0])], &["A"]),
    ];
    for (id, baseline, selector, expected, names) in rows {
        let discovery = derive_sites(baseline, "role", &selector)
            .unwrap_or_else(|error| panic!("{id}: {error}"));
        assert!(discovery.exhaustive() && !discovery.joined(), "{id}");
        let expected = expected
            .iter()
            .map(|(rule, path)| ((*rule).to_owned(), path.to_vec()))
            .collect::<Vec<_>>();
        assert_eq!(labelled_sites(baseline, &discovery), expected, "{id}");
        for tuple in discovery.tuples() {
            let term = baseline
                .term(&tuple.sites[0].at)
                .expect("a derived site resolves");
            assert_eq!(
                tuple.bindings.as_slice(),
                names
                    .iter()
                    .map(|name| ((*name).to_owned(), term.clone()))
                    .collect::<Vec<_>>(),
                "{id}: each name binds the site's own term"
            );
        }
    }
}

/// The former `ordered-shared-term` join: a name both roles bind is one
/// pattern variable, so only pairs that bind it to equal terms are tuples,
/// and each tuple binds it once.
#[test]
fn a_join_unifies_the_names_both_roles_bind() {
    let memory = support::load("memory.k");
    let role = |role: &str, rule: &str, at: &[u32], sort_name: &str, name: &str| {
        derive_sites(
            &memory,
            role,
            &[label(rule), path(at), sort(sort_name), bind(name)],
        )
        .expect("valid selector")
    };
    let write_address = role("write-address", "MEMORY.write", &[0, 0, 0], "Address", "A");
    let load_address = role("load-address", "MEMORY.load", &[0, 0, 0], "Address", "A");
    let shared = write_address
        .join(&load_address, false)
        .expect("one baseline");
    assert!(shared.exhaustive() && shared.joined());
    let [tuple] = shared.tuples() else {
        panic!("one pair: {:?}", shared.tuples());
    };
    assert_eq!(
        tuple
            .sites
            .iter()
            .map(|site| site.role.as_str())
            .collect::<Vec<_>>(),
        ["write-address", "load-address"]
    );
    let address = memory.term(&tuple.sites[0].at).expect("site").clone();
    assert_eq!(tuple.bindings.as_slice(), [("A".to_owned(), address)]);

    // `A` bound to `load`'s value `V` is another term: no pair, and the join
    // still considered every pair.
    let load_value = role("load-value", "MEMORY.load", &[0, 0, 1], "Nat", "A");
    let mismatch = write_address
        .join(&load_value, false)
        .expect("one baseline");
    assert!(mismatch.tuples().is_empty() && mismatch.exhaustive());

    // Distinct names do not constrain each other.
    let value = role("load-value", "MEMORY.load", &[0, 0, 1], "Nat", "V");
    let distinct = write_address.join(&value, false).expect("one baseline");
    let [tuple] = distinct.tuples() else {
        panic!("one pair: {:?}", distinct.tuples());
    };
    assert_eq!(
        tuple
            .bindings
            .as_slice()
            .iter()
            .map(|(name, _)| name.as_str())
            .collect::<Vec<_>>(),
        ["A", "V"]
    );
}

/// The term at `path` below `term`, through rewrites and applications.
fn term_mut<'t>(term: &'t mut Term, path: &[u32]) -> &'t mut Term {
    let Some((step, rest)) = path.split_first() else {
        return term;
    };
    let step = usize::try_from(*step).expect("step");
    let child = match term {
        Term::Annotated { term, .. } => return term_mut(term, path),
        Term::Rewrite { left, right } => [left, right].into_iter().nth(step).expect("side"),
        Term::Apply { arguments, .. } => arguments.get_mut(step).expect("argument"),
        other => panic!("{other} has no children"),
    };
    term_mut(child, rest)
}

/// An edited copy of either written rule's body in `annotated.k`.
fn written(annotated: &Baseline, rule_label: &str, edit: impl FnOnce(&mut Term)) -> Baseline {
    let rule = support::rule(annotated, rule_label);
    let mut loaded = annotated.loaded().clone();
    let module = loaded
        .definition
        .modules
        .iter_mut()
        .find(|module| module.name == rule.module)
        .expect("module");
    let slot = &mut module.local_sentences[usize::try_from(rule.index).expect("index")];
    let k_rust::definition::Sentence::Rule { body, .. } = sentence_mut(slot) else {
        panic!("{rule_label} is a rule");
    };
    edit(body);
    Baseline::new(loaded)
}

fn nat_variable(name: &str) -> Term {
    Term::Variable {
        name: name.to_owned(),
        sort: Some(Sort::new("Nat")),
    }
}

/// (id, baseline, put's site, get's site (a path, or every `Nat` position),
/// pairs as (put path, get path), exhaustive)
type UnificationRow<'a> = (
    &'static str,
    &'a Baseline,
    Option<&'static [u32]>,
    Option<&'static [u32]>,
    &'static [(&'static [u32], &'static [u32])],
    bool,
);

/// A join compares the terms a name binds modulo how a variable's sort is
/// written, and never drops a pair it cannot decide in silence. In
/// `annotated.k`, `put(A:Nat)` and `get(A)` load alike: a `Nat` cast
/// (`[0, 0, 0]`) over the variable (`[0, 0, 0, 0]`). Two casts over `A` are
/// one term. A cast against the variable under it, or two bare variables
/// whose sorts come from outside the bound terms, would need the baseline's
/// typing, so the pair is left out and the join is not exhaustive; a
/// sort-only selector meets both kinds of position. A structured input that
/// writes `get`'s `A` with an explicit `Nat` sort instead of a cast unifies
/// with `put`'s cast, and one with another sort is undecided.
#[test]
fn a_join_decides_unification_modulo_variable_sorts_or_is_not_exhaustive() {
    let annotated = support::load("annotated.k");
    // `get`'s left-hand argument becomes `A` written with `sort`.
    let get_with_sort = |sort: &str| {
        written(&annotated, "ANNOTATED.get", |body| {
            *term_mut(body, &[0, 0]) = Term::Variable {
                name: "A".to_owned(),
                sort: Some(Sort::new(sort)),
            };
        })
    };
    let nat = get_with_sort("Nat");
    let int = get_with_sort("Int");
    let bind_a = |baseline, role: &str, rule: &str, at: Option<&[u32]>| {
        let mut selector = vec![label(rule), bind("A")];
        selector.extend(at.map(path));
        if at.is_none() {
            selector.push(sort("Nat"));
        }
        derive_sites(baseline, role, &selector).expect("valid selector")
    };
    const CAST: Option<&[u32]> = Some(&[0, 0, 0]);
    const VARIABLE: Option<&[u32]> = Some(&[0, 0, 0, 0]);
    #[rustfmt::skip]
    let rows: [UnificationRow<'_>; 6] = [
        ("casts-over-one-variable-unify", &annotated, CAST, CAST, &[(&[0, 0, 0], &[0, 0, 0])], true),
        ("a-cast-against-its-variable-is-undecided", &annotated, CAST, VARIABLE, &[], false),
        ("bare-variables-are-sorted-from-outside", &annotated, VARIABLE, VARIABLE, &[], false),
        // Every `Nat` position: the two casts and two variables of each rule.
        ("a-sort-only-selector-keeps-only-decided-pairs", &annotated, None, None, &[(&[0, 0, 0], &[0, 0, 0]), (&[0, 0, 0], &[0, 1, 0]), (&[0, 1, 0], &[0, 0, 0]), (&[0, 1, 0], &[0, 1, 0])], false),
        ("an-annotation-unifies-with-a-cast-of-its-sort", &nat, CAST, CAST, &[(&[0, 0, 0], &[0, 0, 0])], true),
        ("an-annotation-of-another-sort-is-undecided", &int, CAST, CAST, &[], false),
    ];
    for (id, baseline, put_site, get_site, pairs, exhaustive) in rows {
        let put = bind_a(baseline, "put", "ANNOTATED.put", put_site);
        let got = bind_a(baseline, "get", "ANNOTATED.get", get_site);
        assert!(put.exhaustive() && got.exhaustive(), "{id}");
        let joined = put.join(&got, false).expect("one baseline");
        assert_eq!(joined.exhaustive(), exhaustive, "{id}");
        assert_eq!(
            joined
                .tuples()
                .iter()
                .map(|tuple| {
                    let [left, right] = tuple.sites.as_slice() else {
                        panic!("{id}: pairs");
                    };
                    (left.at.path.0.clone(), right.at.path.0.clone())
                })
                .collect::<Vec<_>>(),
            pairs
                .iter()
                .map(|(left, right)| (left.to_vec(), right.to_vec()))
                .collect::<Vec<_>>(),
            "{id}"
        );
        let selection = select(&joined, SelectionPolicy::TupleEach, 16).expect("selection");
        assert_eq!(
            selection.completeness() == Completeness::CompleteFinite,
            exhaustive,
            "{id}: an undecided pair is never scored"
        );
    }
}

#[test]
fn a_join_unifies_structurally() {
    let annotated = support::load("annotated.k");
    let get_different_name = written(&annotated, "ANNOTATED.get", |body| {
        *term_mut(body, &[0, 0]) = nat_variable("B");
    });
    let put_body = annotated
        .term(&TermRef::new(
            support::rule(&annotated, "ANNOTATED.put"),
            [0],
        ))
        .expect("put body")
        .clone();
    // The two rewrites have the same structure, with `A:Nat` written as a
    // cast in `put` and an annotated variable in `get`.
    let equal_rewrites = written(&annotated, "ANNOTATED.get", |body| {
        *body = put_body.clone();
        *term_mut(body, &[0, 0]) = nat_variable("A");
    });
    let got_rhs = annotated
        .term(&TermRef::new(
            support::rule(&annotated, "ANNOTATED.get"),
            [0, 1],
        ))
        .expect("get right-hand side")
        .clone();
    let differing_rewrites = written(&equal_rewrites, "ANNOTATED.put", |body| {
        *term_mut(body, &[1]) = got_rhs.clone();
    });
    let put_argument = annotated
        .term(&TermRef::new(
            support::rule(&annotated, "ANNOTATED.put"),
            [0, 0, 0],
        ))
        .expect("put argument")
        .clone();
    // The as-patterns likewise write their pattern variable in two forms.
    let as_argument = |pattern| Term::As {
        pattern: Box::new(pattern),
        alias: Box::new(nat_variable("C")),
    };
    let put_as = written(&annotated, "ANNOTATED.put", |body| {
        *term_mut(body, &[0, 0]) = as_argument(put_argument.clone());
    });
    let both_as = written(&put_as, "ANNOTATED.get", |body| {
        *term_mut(body, &[0, 0]) = as_argument(nat_variable("A"));
    });
    let put_sequence = written(&annotated, "ANNOTATED.put", |body| {
        *term_mut(body, &[0, 0]) = Term::Sequence(vec![nat_variable("A")]);
    });
    let different_sequences = written(&put_sequence, "ANNOTATED.get", |body| {
        *term_mut(body, &[0, 0]) = Term::Sequence(vec![nat_variable("A"), nat_variable("C")]);
    });
    #[rustfmt::skip]
    let rows = [
        ("different-names-mismatch", &get_different_name, &[0, 0, 0][..], &[0, 0, 0][..], 0),
        ("equal-rewrites-unify", &equal_rewrites, &[0][..], &[0][..], 1),
        ("rewrites-differing-on-one-side", &differing_rewrites, &[0][..], &[0][..], 0),
        ("as-patterns-unify-componentwise", &both_as, &[0, 0, 0][..], &[0, 0, 0][..], 1),
        ("sequences-of-different-lengths", &different_sequences, &[0, 0, 0][..], &[0, 0, 0][..], 0),
    ];
    for (id, baseline, put_path, get_path, pair_count) in rows {
        let bind_at = |role, rule, at| {
            derive_sites(baseline, role, &[label(rule), path(at), bind("X")])
                .unwrap_or_else(|error| panic!("{id}: {error}"))
        };
        let put = bind_at("put", "ANNOTATED.put", put_path);
        let get = bind_at("get", "ANNOTATED.get", get_path);
        assert_eq!((put.tuples().len(), get.tuples().len()), (1, 1), "{id}");
        let joined = put.join(&get, false).expect("one baseline");
        assert!(joined.exhaustive(), "{id}");
        assert_eq!(joined.tuples().len(), pair_count, "{id}");
        for tuple in joined.tuples() {
            assert_eq!(tuple.sites[0].at.path.0, put_path, "{id}");
            assert_eq!(tuple.sites[1].at.path.0, get_path, "{id}");
            assert_eq!(tuple.bindings.as_slice().len(), 1, "{id}");
        }
    }
}

#[test]
fn bind_clauses_must_name_unique_k_variables() {
    let memory = support::load("memory.k");
    for (id, names) in [
        ("lower-case", &["a"][..]),
        ("repeated", &["A", "A"]),
        ("empty", &[""]),
    ] {
        // Rejected whether or not any position matches.
        for selector in [vec![], vec![label("MEMORY.nothing")]] {
            let selector = selector
                .into_iter()
                .chain(names.iter().map(|name| bind(name)))
                .collect::<Vec<_>>();
            assert_eq!(
                derive_sites(&memory, "role", &selector)
                    .expect_err(id)
                    .kind(),
                CandidateFailureKind::InvalidBinding,
                "{id}"
            );
        }
    }
}

/// A position whose sort cannot be decided is neither a site nor a non-site:
/// the discovery is not exhaustive, so its generation is never scored. A
/// selector that never asks for that position's sort is unaffected.
#[test]
fn an_undecided_sort_makes_the_discovery_incomplete() {
    let counter = support::load("counter.k");
    let increment = support::rule(&counter, "COUNTER.increment");
    // `increment`'s `requires` becomes a variable without a sort or cast.
    let mut loaded = counter.loaded().clone();
    let module = loaded
        .definition
        .modules
        .iter_mut()
        .find(|module| module.name == increment.module)
        .expect("module");
    let slot = &mut module.local_sentences[usize::try_from(increment.index).expect("index")];
    let k_rust::definition::Sentence::Rule { requires, .. } = sentence_mut(slot) else {
        panic!("increment is a rule");
    };
    *requires = Term::Variable {
        name: "B".to_owned(),
        sort: None,
    };
    let unsorted = Baseline::new(loaded);

    let requires =
        derive_sites(&unsorted, "requires", &[path(&[1]), sort("Bool")]).expect("valid selector");
    assert!(!requires.exhaustive());
    assert_eq!(
        labelled_sites(&unsorted, &requires),
        [
            ("COUNTER.branch".to_owned(), vec![1]),
            ("COUNTER.fallback".to_owned(), vec![1])
        ]
    );
    let generation = select(&requires, SelectionPolicy::Each, 4)
        .expect("selection")
        .fold("unused", |origin| {
            let at = origin.site_tuple[0].clone();
            let current = unsorted.term(&at).expect("term").clone();
            Patch::new(vec![Edit::ReplaceTerm {
                at,
                expected: current,
                replacement: Term::Token {
                    token: "false".to_owned(),
                    sort: Sort::new("Bool"),
                },
            }])
            .expect("one edit")
        })
        .expect("each origin edits its own rule");
    assert_eq!(generation.completeness(), Completeness::Incomplete);
    assert!(!generation.scored());

    let ensures =
        derive_sites(&unsorted, "ensures", &[path(&[2]), sort("Bool")]).expect("valid selector");
    assert!(ensures.exhaustive());
    assert_eq!(ensures.tuples().len(), 3);
}

/// The two operators of the former selector registries, now built from
/// derived sites and their bindings. Each yields one scored candidate whose
/// mutant k-rust compiles.
#[test]
fn operators_build_their_patches_from_bound_terms() {
    // `counter-plus-one-site`: each `s(E')` on a right-hand side's first
    // argument loses its successor, `E` becoming its argument.
    let counter = support::load("counter.k");
    let increments = derive_sites(
        &counter,
        "increment-expression",
        &[path(&[0, 1, 0]), sort("Nat"), head("s"), bind("E")],
    )
    .expect("valid selector");
    let generation = select(&increments, SelectionPolicy::Each, 16)
        .expect("selection")
        .fold("counter-plus-one-site", |origin| {
            let tuple = &origin.discovery_tuples[0];
            let Term::Apply { arguments, .. } =
                tuple.bindings.get("E").expect("bound").unannotated()
            else {
                panic!("E is an application of s");
            };
            let at = tuple.sites[0].at.clone();
            Patch::new(vec![Edit::ReplaceTerm {
                expected: counter.term(&at).expect("term").clone(),
                at,
                replacement: arguments[0].clone(),
            }])
            .expect("one edit")
        })
        .expect("each origin edits its own rule");
    assert!(generation.scored());
    let [candidate] = generation.candidates() else {
        panic!("one candidate: {generation:?}");
    };
    let increment = support::rule(&counter, "COUNTER.increment");
    let at = |path: &[u32]| TermRef::new(increment.clone(), path);
    let term = |path: &[u32]| counter.term(&at(path)).expect("term").clone();
    assert_eq!(
        candidate.patch,
        Patch::new(vec![Edit::ReplaceTerm {
            at: at(&[0, 1, 0]),
            expected: term(&[0, 1, 0]),
            replacement: term(&[0, 1, 0, 0]),
        }])
        .expect("one edit"),
        "the hand-built increment mutant of the validator tests"
    );
    let mutant = apply(&counter, &candidate.patch).expect("applies");
    support::compile(&mutant.to_loaded(&counter)).expect("the mutant compiles");

    // `coupled-memory-representation`: the value `write` stores and the value
    // `load` reads change representation together, as one mutant. Exactly
    // one pair shares `V`; each site becomes `s(V)`.
    let memory = support::load("memory.k");
    let value = |role: &str, rule: &str| {
        derive_sites(
            &memory,
            role,
            &[label(rule), path(&[0, 0, 1]), sort("Nat"), bind("V")],
        )
        .expect("valid selector")
    };
    let coupled = value("write-value", "MEMORY.write")
        .join(&value("load-value", "MEMORY.load"), false)
        .expect("one baseline");
    let generation = select(&coupled, EXACT_PAIR, 8)
        .expect("selection")
        .fold("coupled-memory-representation", |origin| {
            let tuple = &origin.discovery_tuples[0];
            let bound = tuple.bindings.get("V").expect("bound");
            Patch::new(
                tuple
                    .sites
                    .iter()
                    .map(|site| Edit::ReplaceTerm {
                        at: site.at.clone(),
                        expected: memory.term(&site.at).expect("term").clone(),
                        replacement: Term::apply("s", vec![bound.clone()]),
                    })
                    .collect(),
            )
            .expect("two edits")
        })
        .expect("the origin holds both rules");
    assert!(generation.scored());
    let [candidate] = generation.candidates() else {
        panic!("one candidate: {generation:?}");
    };
    assert_eq!(candidate.patch.edits().len(), 2);
    let mutant = apply(&memory, &candidate.patch).expect("applies");
    for rule in ["MEMORY.write", "MEMORY.load"] {
        let at = TermRef::new(support::rule(&memory, rule), [0, 0, 1]);
        assert_eq!(
            kink_patch::term_at(
                mutant.definition(),
                &at.sentence.module,
                at.sentence.index,
                &at.path.0
            ),
            Some(&Term::apply(
                "s",
                vec![memory.term(&at).expect("term").clone()]
            )),
            "{rule}"
        );
    }
    support::compile(&mutant.to_loaded(&memory)).expect("the mutant compiles");
}
