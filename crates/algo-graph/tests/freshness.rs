//! The workspace freshness gate. It runs without the libtest harness (`harness = false` in
//! Cargo.toml) so that its report summary is printed by a plain `cargo test`; a failure panics
//! and exits nonzero.

use algo_graph::{build_graph, canonical_toml, workspace_root, write_report};

fn main() {
    let root = workspace_root();
    let build = build_graph(&root).expect("the workspace graph should build");

    println!(
        "{}",
        write_report(&root, &build).expect("the report should be written")
    );

    assert!(
        build.failures.is_empty(),
        "algorithm graph freshness failures:\n{}",
        build.failures.join("\n")
    );

    let canonical = canonical_toml(&build.graph).expect("the workspace graph should serialize");
    let mut settings = insta::Settings::clone_current();
    settings.set_prepend_module_to_snapshot(false);
    settings.bind(|| insta::assert_snapshot!("graph.toml", canonical));
    println!("workspace_algorithm_graph_is_fresh ... ok");
}
