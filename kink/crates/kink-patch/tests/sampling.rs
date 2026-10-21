//! Population identities and deterministic sampling before candidate folding.

#[path = "../../../testdata/k/support.rs"]
mod support;

use k_rust::{builtin, kast::Sort, outer::ResolvedSource};
use kink_patch::{
    Action, Baseline, CandidateFailureKind, Clause, Completeness, Discovery, OperatorSpec,
    PatchOrigin, SelectionPolicy, Sha256Digest, SiteSelector, Universe, canonical_json,
    derive_sites_in, generate, payload_digest, resolve_universe, select,
};
use serde_json::json;
use std::collections::BTreeSet;

fn baseline() -> Baseline {
    let mut resolver = |_: &str, name: &str| {
        builtin::embedded(name).ok_or_else(|| format!("{name} is not embedded"))
    };
    Baseline::load(
        ResolvedSource::new(
            "sampling.k",
            r#"
module SAMPLING
 imports INT
 imports BASIC-K
 syntax Int ::= pair(Int, Int) [symbol(pair)]
 rule [first]: pair(1, 2) => 3
 rule [second]: pair(4, 5) => 6
endmodule
"#,
        ),
        "SAMPLING",
        None,
        &mut resolver,
        &support::options(),
    )
    .expect("sampling fixture loads")
}

fn spec(offset: i64) -> OperatorSpec {
    OperatorSpec::new(
        "int-literal",
        offset.to_string(),
        1,
        vec![Clause::TokenOfSort {
            sort: Sort::new("Int"),
        }],
        Action::IntOffset(offset),
    )
    .expect("valid operator")
}

fn rank(seed: &[u8], origin: &PatchOrigin) -> (Sha256Digest, String) {
    let value = json!(
        origin
            .site_tuple
            .iter()
            .map(|at| {
                json!({"module":at.sentence.module,"index":at.sentence.index,"path":at.path.0})
            })
            .collect::<Vec<_>>()
    );
    let text = canonical_json(&value);
    let bytes = [seed, text.as_bytes()].concat();
    (payload_digest("kink/sample/v1", &bytes), text)
}

fn expected_subset(origins: &[PatchOrigin], seed: &[u8], size: usize) -> Vec<PatchOrigin> {
    let mut ranked = origins
        .iter()
        .enumerate()
        .map(|(index, origin)| {
            let (digest, text) = rank(seed, origin);
            (digest, text, index)
        })
        .collect::<Vec<_>>();
    ranked.sort();
    let kept = ranked
        .into_iter()
        .take(size)
        .map(|(_, _, index)| index)
        .collect::<BTreeSet<_>>();
    origins
        .iter()
        .enumerate()
        .filter(|(index, _)| kept.contains(index))
        .map(|(_, origin)| origin.clone())
        .collect()
}

#[test]
fn populations_precede_all_bounds_and_sample_is_identical_across_loads() {
    let first = baseline();
    let second = baseline();
    let operator = spec(1);
    let seed = [0x00, 0xfe, 0x17];
    let mut samples = Vec::new();
    let mut populations = Vec::new();
    for baseline in [&first, &second] {
        let universe = resolve_universe(baseline, &Universe::v1());
        let full = generate(baseline, &universe, &operator, usize::MAX).expect("full generation");
        let origins = full.selected_origins();
        assert_eq!(origins.len(), 6);
        let value = json!(
            origins
                .iter()
                .map(OperatorSpec::origin_value)
                .collect::<Vec<_>>()
        );
        let population = operator
            .population(baseline, &universe)
            .expect("population");
        assert_eq!(population.0, 6);
        assert_eq!(
            population.1,
            payload_digest("kink/population/v1", canonical_json(&value).as_bytes())
        );
        let sampled =
            OperatorSpec::generate_all(baseline, &universe, &[(&operator, 5)], Some((3, 2, &seed)))
                .expect("sampled generation");
        assert_eq!(
            sampled[0].selected_origins(),
            expected_subset(origins, &seed, 2)
        );
        assert_eq!(sampled[0].completeness(), Completeness::Incomplete);
        assert_eq!(sampled[0].failure(), Some(CandidateFailureKind::Sampled));
        assert!(!sampled[0].scored());
        assert_eq!(sampled[0].candidates().len(), 2);
        samples.push(sampled[0].candidates().to_vec());
        populations.push(population);
    }
    assert_eq!(samples[0], samples[1]);
    assert_eq!(populations[0], populations[1]);
}

#[test]
fn supplied_discovery_iteration_order_cannot_change_hash_sample_or_origin_order() {
    let baseline = baseline();
    let universe = resolve_universe(&baseline, &Universe::v1());
    let derived = derive_sites_in(
        &baseline,
        &universe,
        &[SiteSelector::TokenOfSort {
            sort: Sort::new("Int"),
        }],
    )
    .expect("discovery");
    let full = select(&derived, SelectionPolicy::Each, usize::MAX).expect("selection");
    let origins = full.selected_origins();
    let seed = b"iteration-test";
    let expected = expected_subset(origins, seed, 3);
    let mut tuples = origins
        .iter()
        .flat_map(|origin| origin.discovery_tuples.clone())
        .collect::<Vec<_>>();
    let mut samples = Vec::new();
    for _ in 0..2 {
        let discovery =
            Discovery::supplied(&baseline, tuples.clone(), false, false).expect("supplied");
        let selection =
            select(&discovery, SelectionPolicy::Each, usize::MAX).expect("canonical selection");
        let sampled = selection.sample(|origin| expected.contains(origin));
        assert_eq!(sampled.selected_origins(), expected);
        assert_eq!(sampled.failure(), Some(CandidateFailureKind::Sampled));
        samples.push(sampled.selected_origins().to_vec());
        tuples.reverse();
    }
    assert_eq!(samples[0], samples[1]);
    assert!(
        samples[0]
            .windows(2)
            .all(|pair| pair[0].site_tuple < pair[1].site_tuple)
    );
}

#[test]
fn per_spec_cut_and_global_cut_use_hash_rank_with_canonical_ties() {
    let baseline = baseline();
    let universe = resolve_universe(&baseline, &Universe::v1());
    let plus = spec(1);
    let minus = spec(-1);
    let specs = [(&plus, 6), (&minus, 6)];
    let seed = b"two-stages";
    let full = generate(&baseline, &universe, &plus, usize::MAX).expect("full");
    let per_spec = expected_subset(full.selected_origins(), seed, 3);
    let mut ranked = specs
        .iter()
        .enumerate()
        .flat_map(|(spec_index, (spec, _))| {
            per_spec
                .iter()
                .enumerate()
                .map(move |(origin_index, origin)| {
                    let (digest, text) = rank(seed, origin);
                    (digest, text, spec.digest(), spec_index, origin_index)
                })
        })
        .collect::<Vec<_>>();
    ranked.sort();
    let kept = ranked
        .into_iter()
        .take(3)
        .map(|(_, _, _, spec_index, origin_index)| (spec_index, origin_index))
        .collect::<BTreeSet<_>>();
    let sampled = OperatorSpec::generate_all(&baseline, &universe, &specs, Some((3, 3, seed)))
        .expect("sample");
    for (spec_index, generation) in sampled.iter().enumerate() {
        let expected = per_spec
            .iter()
            .enumerate()
            .filter(|(origin_index, _)| kept.contains(&(spec_index, *origin_index)))
            .map(|(_, origin)| origin.clone())
            .collect::<Vec<_>>();
        assert_eq!(generation.selected_origins(), expected);
        assert_eq!(generation.failure(), Some(CandidateFailureKind::Sampled));
        assert!(!generation.scored());
    }
    assert_eq!(
        sampled
            .iter()
            .map(|generation| generation.selected_origins().len())
            .sum::<usize>(),
        3
    );
    let reversed = OperatorSpec::generate_all(
        &baseline,
        &universe,
        &[(&minus, 6), (&plus, 6)],
        Some((3, 3, seed)),
    )
    .expect("reverse spec order");
    assert_eq!(
        sampled[0].selected_origins(),
        reversed[1].selected_origins()
    );
    assert_eq!(
        sampled[1].selected_origins(),
        reversed[0].selected_origins()
    );
}

#[test]
fn no_budget_preserves_ordinary_generation_and_noncutting_budget_preserves_score() {
    let baseline = baseline();
    let universe = resolve_universe(&baseline, &Universe::v1());
    let operator = spec(1);
    let ordinary = generate(&baseline, &universe, &operator, 2).expect("capped");
    let without = OperatorSpec::generate_all(&baseline, &universe, &[(&operator, 2)], None)
        .expect("without budget");
    assert_eq!(ordinary.candidates(), without[0].candidates());
    assert_eq!(ordinary.selected_origins(), without[0].selected_origins());
    assert_eq!(ordinary.dispositions(), without[0].dispositions());
    assert_eq!(ordinary.completeness(), without[0].completeness());
    assert_eq!(
        without[0].failure(),
        Some(CandidateFailureKind::IncompleteGeneration)
    );
    let full = OperatorSpec::generate_all(
        &baseline,
        &universe,
        &[(&operator, 6)],
        Some((u64::MAX, u64::MAX, b"")),
    )
    .expect("no cuts");
    assert_eq!(full[0].completeness(), Completeness::CompleteFinite);
    assert_eq!(full[0].failure(), None);
    assert!(full[0].scored());
    let cap = OperatorSpec::generate_all(
        &baseline,
        &universe,
        &[(&operator, 2)],
        Some((6, 6, b"cap")),
    )
    .expect("cap cut");
    assert_eq!(cap[0].selected_origins().len(), 2);
    assert_eq!(cap[0].failure(), Some(CandidateFailureKind::Sampled));
    assert!(!cap[0].scored());
}

#[test]
fn zero_budgets_publish_empty_sampled_unscored_generations() {
    let baseline = baseline();
    let universe = resolve_universe(&baseline, &Universe::v1());
    let operator = spec(1);
    for (per_spec, total) in [(0, 6), (6, 0), (0, 0)] {
        let sampled = OperatorSpec::generate_all(
            &baseline,
            &universe,
            &[(&operator, 6)],
            Some((per_spec, total, b"zero")),
        )
        .expect("zero budget");
        assert!(sampled[0].selected_origins().is_empty());
        assert!(sampled[0].candidates().is_empty());
        assert_eq!(sampled[0].failure(), Some(CandidateFailureKind::Sampled));
        assert_eq!(sampled[0].completeness(), Completeness::Incomplete);
        assert!(!sampled[0].scored());
    }
}

#[test]
fn sample_noop_preserves_earlier_failure_and_actual_cut_replaces_incomplete_generation() {
    let baseline = baseline();
    let universe = resolve_universe(&baseline, &Universe::v1());
    let discovery = derive_sites_in(
        &baseline,
        &universe,
        &[SiteSelector::TokenOfSort {
            sort: Sort::new("Int"),
        }],
    )
    .expect("discovery");
    let failed = select(
        &discovery,
        SelectionPolicy::Exact {
            expected_tuple_count: 99,
            expected_tuple_arity: 1,
        },
        6,
    )
    .expect("failed selection");
    let failed = failed.sample(|_| false);
    assert_eq!(
        failed.failure(),
        Some(CandidateFailureKind::CardinalityMismatch)
    );
    assert_eq!(failed.completeness(), Completeness::CompleteFinite);
    let capped = select(&discovery, SelectionPolicy::Each, 2).expect("capped");
    assert_eq!(
        capped.clone().sample(|_| true).failure(),
        Some(CandidateFailureKind::IncompleteGeneration)
    );
    let sampled = capped.sample(|_| false);
    assert_eq!(sampled.failure(), Some(CandidateFailureKind::Sampled));
    assert_eq!(sampled.completeness(), Completeness::Incomplete);
}
