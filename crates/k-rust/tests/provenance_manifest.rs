use std::collections::{BTreeMap, BTreeSet};

use k_rust::{
    kast::{Sort, Term},
    provenance::{DECLARED_ORIGIN_FREE_NODE_KINDS, GeneratingPass, declared_origin_free},
};
use regex::Regex;
use serde::Deserialize;

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ProvenanceCoverageManifest {
    version: u32,
    origin_free_node_kinds: Vec<String>,
    pipeline: Vec<PipelineStage>,
    boundary_generator: Vec<BoundaryGenerator>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct PipelineStage {
    call: String,
    occurrences: usize,
    behavior: String,
    #[serde(default)]
    generating_passes: Vec<String>,
    reason: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct BoundaryGenerator {
    call: String,
    generating_pass: String,
    boundary: String,
    reason: String,
}

#[test]
fn provenance_manifest_classifies_the_compile_pipeline_and_origin_free_nodes() {
    let manifest: ProvenanceCoverageManifest =
        toml::from_str(include_str!("fixtures/provenance-coverage.toml"))
            .expect("provenance coverage manifest must be valid TOML");
    assert_eq!(manifest.version, 1, "unsupported manifest version");

    let declared_origin_free_kinds = manifest
        .origin_free_node_kinds
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    assert_eq!(
        declared_origin_free_kinds,
        DECLARED_ORIGIN_FREE_NODE_KINDS.into_iter().collect()
    );
    for kind in &manifest.origin_free_node_kinds {
        let term = match kind.as_str() {
            "primitive-token" => Term::Token {
                token: "0".into(),
                sort: Sort::new("Int"),
            },
            "structural-dot" => Term::apply("#dots", Vec::new()),
            "truth-value" => Term::Token {
                token: "true".into(),
                sort: Sort::new("Bool"),
            },
            unknown => panic!("unknown declared-origin-free node kind {unknown:?}"),
        };
        assert!(declared_origin_free(&term), "{kind} is not origin-free");
    }
    assert!(!declared_origin_free(&Term::variable("X")));

    let mut declared_pipeline = BTreeMap::new();
    let mut classified_generators = BTreeSet::new();
    for stage in &manifest.pipeline {
        assert!(
            declared_pipeline
                .insert(stage.call.clone(), stage.occurrences)
                .is_none(),
            "duplicate pipeline classification for {:?}",
            stage.call
        );
        assert!(
            !stage.reason.trim().is_empty(),
            "{} needs a reason",
            stage.call
        );
        match stage.behavior.as_str() {
            "generating" => assert!(
                !stage.generating_passes.is_empty(),
                "generating stage {} needs a generating pass",
                stage.call
            ),
            "identity" | "metadata-only" | "structural-origin-free" | "validation" => assert!(
                stage.generating_passes.is_empty(),
                "non-generating stage {} names a generating pass",
                stage.call
            ),
            behavior => panic!("unknown provenance behavior {behavior:?}"),
        }
        for pass in &stage.generating_passes {
            classified_generators.insert(pass.as_str());
        }
    }

    let compile_source = include_str!("../src/kompile/compile.rs");
    let pipeline_source = compile_source
        .split_once("fn transform_loaded_definition(")
        .unwrap()
        .1
        .split_once("fn with_newline(")
        .unwrap()
        .0;
    let call_pattern = Regex::new(
        r"([A-Za-z_][A-Za-z0-9_]*)\(\s*(?:&loaded\.definition|&resolved|&definition)\s*(?:,|\))",
    )
    .unwrap();
    let mut actual_pipeline = BTreeMap::new();
    for captures in call_pattern.captures_iter(pipeline_source) {
        *actual_pipeline.entry(captures[1].to_owned()).or_insert(0) += 1;
    }
    assert_eq!(declared_pipeline, actual_pipeline);

    let boundary_source = include_str!("../src/kompile/module_to_kore.rs");
    for boundary in &manifest.boundary_generator {
        assert_eq!(boundary.boundary, "k-to-kore");
        assert!(!boundary.reason.trim().is_empty());
        let pass = GeneratingPass::from_name(&boundary.generating_pass)
            .expect("boundary generator must name a generating pass");
        assert!(
            boundary_source.contains(&format!("fn {}(", boundary.call)),
            "boundary generator {:?} is absent",
            boundary.call
        );
        assert!(
            boundary_source.contains(&format!("GeneratingPass::{pass:?}")),
            "boundary generator {:?} does not emit {:?}",
            boundary.call,
            boundary.generating_pass
        );
        classified_generators.insert(boundary.generating_pass.as_str());
    }

    let expected_generators = GeneratingPass::ALL
        .into_iter()
        .map(GeneratingPass::as_str)
        .collect::<BTreeSet<_>>();
    assert_eq!(classified_generators, expected_generators);
}
