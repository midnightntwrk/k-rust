//! The workspace freshness gate: the source cards satisfy their contract, the canonical graph
//! equals its snapshot, and the checked-in algorithm map equals the map rendered from the graph.
//!
//! Both tests read the graph built from the checkout. Under `cargo test` they share one build;
//! under `cargo nextest`, which runs each test in its own process, each test builds it.

use std::{io::Write, sync::OnceLock};

use algo_graph::{
    Build, MAP_COMMAND, MAP_PATH, build_graph, canonical_toml, render_map, workspace_root,
    write_report,
};

fn build() -> &'static Build {
    static BUILD: OnceLock<Build> = OnceLock::new();
    BUILD.get_or_init(|| build_graph(&workspace_root()).expect("the workspace graph should build"))
}

#[test]
fn workspace_algorithm_graph_is_fresh() {
    let build = build();

    // The advisory report never fails the gate. Its summary line goes to the process's standard
    // error directly, not through `eprintln!`, which libtest captures, so that a passing
    // `cargo test` run shows it too.
    let summary = write_report(&workspace_root(), build).expect("the report should be written");
    let _ = writeln!(std::io::stderr(), "{summary}");

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

/// The map is a checked-in document rather than an insta snapshot, so that an agent reading the
/// repository finds it at docs/algorithm-map.md.
#[test]
fn workspace_algorithm_map_is_fresh() {
    let map = render_map(&build().graph);
    let checked_in = std::fs::read_to_string(workspace_root().join(MAP_PATH)).unwrap_or_default();
    assert!(
        checked_in == map,
        "{MAP_PATH} differs from the map rendered from the current graph; regenerate it with `{MAP_COMMAND}`"
    );
}
