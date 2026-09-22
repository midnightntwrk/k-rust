use algo_graph::{build_graph, canonical_toml, workspace_root};

#[test]
fn workspace_algorithm_graph_is_fresh() {
    let build = build_graph(&workspace_root()).expect("the workspace graph should build");

    for finding in &build.report {
        eprintln!("algo-graph report: {finding}");
    }

    assert!(
        build.failures.is_empty(),
        "algorithm graph freshness failures:\n{}",
        build.failures.join("\n")
    );

    let canonical = canonical_toml(&build.graph).expect("the workspace graph should serialize");
    let mut settings = insta::Settings::clone_current();
    settings.set_prepend_module_to_snapshot(false);
    settings.bind(|| insta::assert_snapshot!("graph.toml", canonical));
}
