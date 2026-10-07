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
    assert_eq!(stages.len(), 35);
    assert_eq!(stages.first().unwrap().call, "resolve_comm");
    assert_eq!(stages.first().unwrap().table, "TRANSFORM_STAGES");
    assert_eq!(stages.last().unwrap().call, "minimize_term_construction");
    assert_eq!(stages.last().unwrap().table, "EMISSION_STAGES");
    assert!(
        prologue_descriptions()
            .iter()
            .all(|stage| stage.table == "prologue_descriptions")
    );
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

    for boundary in &manifest.boundary_generator {
        // The generator is defined in the boundary's source. A load-boundary generator runs
        // before compilation receives the definition, so the loader must call it.
        let boundary_source = match boundary.boundary.as_str() {
            "k-to-kore" => include_str!("../src/kompile/module_to_kore.rs"),
            "load" => {
                // Load-boundary generators currently only expand configurations.
                assert!(
                    include_str!("../src/outer/loader.rs").contains(&format!("{}(", boundary.call)),
                    "load-boundary generator {:?} is not called by the loader",
                    boundary.call
                );
                include_str!("../src/definition/configuration.rs")
            }
            other => panic!("unknown generator boundary {other:?}"),
        };
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

/// The environment variable that makes [`deep_annotation_child`] run, in the child process of
/// [`a_deep_generated_term_is_annotated_in_linear_memory`].
const DEEP_ANNOTATION_CHILD: &str = "K_RUST_TEST_DEEP_ANNOTATION_CHILD";

/// The work of [`a_deep_generated_term_is_annotated_in_linear_memory`]; it does
/// nothing unless that test runs it in its child process.
#[test]
fn deep_annotation_child() {
    use k_rust::definition::{Attributes, Sentence};
    use k_rust::kast::{Label, Sort, Term};
    if std::env::var_os(DEEP_ANNOTATION_CHILD).is_none() {
        return;
    }
    const DEPTH: usize = 100_000;
    let application = |label: &str, arguments| Term::Apply {
        label: Label::new(label),
        arguments,
    };
    let truth = || Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    };
    let rule = |leaf: &str| {
        let deep = (0..DEPTH).fold(application(leaf, Vec::new()), |term, _| {
            application("s", vec![term])
        });
        std::sync::Arc::new(Sentence::Rule {
            body: Term::Rewrite {
                left: Box::new(application("go", Vec::new())),
                right: Box::new(application("done", vec![deep])),
            },
            requires: truth(),
            ensures: truth(),
            attributes: Attributes::default(),
        })
    };
    let parsed = k_rust::outer::parse(
        "deep.k",
        "module MAIN\n syntax Nat ::= \"z\" | \"y\" | s(Nat)\n syntax KItem ::= \"go\" | done(Nat)\nendmodule\n",
    )
    .unwrap();
    let mut before = k_rust::outer::lower(&parsed, "MAIN").unwrap();
    before.modules[0].local_sentences.push(rule("z"));
    let mut after = before.clone();
    *after.modules[0].local_sentences.last_mut().unwrap() = rule("y");
    // `record_generated_origins` compares each sentence with its counterpart by `Term` equality,
    // which recurses per level (the documented bound of the KAST term traits), hence 64 MiB.
    let bottom_path = std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(move || {
            let annotated = k_rust::provenance::record_generated_origins(
                &before,
                after,
                k_rust::provenance::GeneratingPass::ResolveFun,
            );
            let Sentence::Rule { body, .. } =
                &**annotated.modules[0].local_sentences.last().unwrap()
            else {
                unreachable!("the rule stays a rule")
            };
            let Term::Rewrite { right, .. } = body.unannotated() else {
                unreachable!("the body stays a rewrite")
            };
            let mut term = &**right;
            let mut depth = 0;
            while let Term::Apply { arguments, .. } = term.unannotated() {
                match arguments.first() {
                    Some(argument) => {
                        term = argument;
                        depth += 1;
                    }
                    None => break,
                }
            }
            assert_eq!(depth, DEPTH + 1, "done and the s");
            let path = term
                .metadata()
                .and_then(|metadata| metadata.origin.as_deref())
                .and_then(|origin| origin.destination.as_ref())
                .expect("the changed leaf carries a receipt")
                .path
                .clone();
            (path.len(), annotated)
        })
        .expect("the worker should spawn")
        .join()
        .expect("the annotation should finish");
    // The body field, the rewrite's right side, `done`'s argument and one step per `s`.
    assert_eq!(bottom_path.0, DEPTH + 3);
    std::mem::forget(bottom_path.1);
}

/// A pass that changes the bottom of a deep term changes every node above it, and recording
/// the pass's origins annotates each of them with a receipt naming its path: a rule whose right
/// side is 100,000 levels deep, changed at its leaf, is annotated in a child process limited to
/// 1 GiB of address space, with receipts whose paths share their parents' (the leaf's path has
/// the 100,003 steps of its position). The annotation once compared the node with its
/// counterpart (a walk of the whole subtree) at every level and copied the whole path into
/// every receipt: O(N x h) time and memory, 308 MB at 8,000 levels and about 20 GB at 100,000;
/// it now also continues on fresh stack segments rather than recursing on the caller's stack.
#[cfg(target_os = "linux")]
#[test]
fn a_deep_generated_term_is_annotated_in_linear_memory() {
    let output = std::process::Command::new("sh")
        .arg("-c")
        .arg(r#"ulimit -v 1048576 && exec "$0" "$@""#)
        .arg(std::env::current_exe().unwrap())
        .args(["--exact", "deep_annotation_child", "--nocapture"])
        .args(["--test-threads", "1"])
        .env(DEEP_ANNOTATION_CHILD, "1")
        .output()
        .expect("the test binary re-runs itself");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success() && stdout.contains("1 passed"),
        "the annotation of a deep generated term failed under 1 GiB of address space ({}):\n{stdout}\n{}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
}
