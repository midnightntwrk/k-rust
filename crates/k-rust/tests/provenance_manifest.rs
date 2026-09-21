use std::collections::{BTreeMap, BTreeSet};

use k_rust::{
    kast::{Sort, Term},
    kompile::pipeline::{pipeline_checkpoint, prologue_descriptions, stage_descriptions},
    provenance::{DECLARED_ORIGIN_FREE_NODE_KINDS, GeneratingPass, declared_origin_free},
};
use serde::Deserialize;

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ProvenanceCoverageManifest {
    version: u32,
    origin_free_node_kinds: Vec<String>,
    pipeline: Vec<PipelineStage>,
    pipeline_checkpoint: Vec<PipelineCheckpoint>,
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
struct PipelineCheckpoint {
    binding: String,
    source: String,
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
fn pipeline_description_accessors_cover_both_tables_and_the_checkpoint() {
    let stages = stage_descriptions();
    assert_eq!(stages.len(), 34);
    assert_eq!(stages.first().unwrap().call, "resolve_comm");
    assert_eq!(stages.last().unwrap().call, "minimize_term_construction");
    assert_eq!(
        pipeline_checkpoint(),
        ("execution_definition", "definition")
    );
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
                .insert(
                    stage.call.clone(),
                    (
                        stage.occurrences,
                        stage.behavior.clone(),
                        stage
                            .generating_passes
                            .iter()
                            .cloned()
                            .collect::<BTreeSet<_>>(),
                    ),
                )
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

    let mut actual_pipeline = BTreeMap::<String, (usize, String, BTreeSet<String>)>::new();
    for stage in prologue_descriptions()
        .into_iter()
        .chain(stage_descriptions())
    {
        let entry = actual_pipeline.entry(stage.call.into()).or_insert_with(|| {
            (
                0,
                stage.behavior.into(),
                stage
                    .generating_passes
                    .iter()
                    .map(|pass| (*pass).to_owned())
                    .collect(),
            )
        });
        assert_eq!(entry.1, stage.behavior);
        assert_eq!(
            entry.2,
            stage
                .generating_passes
                .iter()
                .map(|pass| (*pass).to_owned())
                .collect()
        );
        entry.0 += 1;
    }
    assert_eq!(declared_pipeline, actual_pipeline);
    let declared_checkpoints = manifest
        .pipeline_checkpoint
        .iter()
        .map(|checkpoint| {
            assert!(
                !checkpoint.reason.trim().is_empty(),
                "pipeline checkpoint {} needs a reason",
                checkpoint.binding
            );
            (checkpoint.binding.clone(), checkpoint.source.clone())
        })
        .collect::<BTreeMap<_, _>>();
    let checkpoint = pipeline_checkpoint();
    assert_eq!(
        declared_checkpoints,
        BTreeMap::from([(checkpoint.0.to_owned(), checkpoint.1.to_owned())])
    );

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
