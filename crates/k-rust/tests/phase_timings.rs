//! The ordered phase list recorded by the timed load and compile entry points.
//!
//! The public phase tables are the kompile pipeline's documented stage order for a source
//! definition. A pass reorder or a new stage edits those tables deliberately.

#![cfg(feature = "z3-inference")]

use std::{fs, path::Path};

use k_rust::{
    builtin::embedded,
    kompile::{
        CompilationBackend, CompileOptions, compile_loaded_definition_timed,
        pipeline::{EMISSION_PHASES, LOAD_PHASES, prologue_descriptions, stage_descriptions},
    },
    outer::{LoadOptions, ResolvedSource, load_for_compilation_timed},
    timings::PhaseTimings,
};

/// Load and compile `examples/rewrite.k` for the Rust backend, returning the load and compile
/// timings separately.
fn time_rewrite_example() -> (PhaseTimings, PhaseTimings) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/rewrite.k");
    let source = fs::read_to_string(&path).expect("examples/rewrite.k should be readable");
    let prelude = embedded("prelude.md").expect("embedded prelude should exist");
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let (loaded, syntax_module, load_timings) = load_for_compilation_timed(
        ResolvedSource::new("rewrite.k", &source),
        "REWRITE",
        None,
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![prelude],
            excluded_module_attributes: vec![
                CompilationBackend::Rust.excluded_module_attribute().into(),
            ],
            ..LoadOptions::default()
        },
    )
    .expect("examples/rewrite.k should load");
    assert_eq!(syntax_module, "REWRITE");
    let (_, compile_timings) = compile_loaded_definition_timed(&loaded, CompileOptions::default())
        .expect("examples/rewrite.k should compile");
    (load_timings, compile_timings)
}

#[test]
fn load_and_compile_phases_follow_the_public_table_order() {
    let (load_timings, compile_timings) = time_rewrite_example();
    let load_names_and_depths = load_timings
        .phases
        .iter()
        .map(|phase| (phase.name, phase.depth))
        .collect::<Vec<_>>();
    let load_names = load_timings
        .phases
        .iter()
        .map(|phase| phase.name)
        .collect::<Vec<_>>();
    // The library entry point starts after the two mutually exclusive CLI entry phases.
    assert_eq!(load_names, &LOAD_PHASES[2..]);
    let rule_bubbles = load_names
        .iter()
        .position(|name| *name == "resolve rule bubbles")
        .expect("rule-bubble parent phase should be recorded");
    assert_eq!(
        &load_names[rule_bubbles..rule_bubbles + 3],
        &[
            "resolve rule bubbles",
            "resolve rule bubbles / grammars",
            "resolve rule bubbles / parse",
        ]
    );
    assert_eq!(
        &load_names_and_depths[rule_bubbles..rule_bubbles + 3],
        &[
            ("resolve rule bubbles", 0),
            ("resolve rule bubbles / grammars", 1),
            ("resolve rule bubbles / parse", 1),
        ]
    );
    assert_eq!(
        load_names
            .iter()
            .filter(|name| **name == "resolve rule bubbles / grammars")
            .count(),
        1
    );
    assert_eq!(
        load_names
            .iter()
            .filter(|name| **name == "resolve rule bubbles / parse")
            .count(),
        1
    );
    let compile_names = compile_timings
        .phases
        .iter()
        .map(|phase| phase.name)
        .collect::<Vec<_>>();
    let expected_compile_names = prologue_descriptions()
        .into_iter()
        .chain(stage_descriptions())
        .map(|description| description.name)
        // The library entry point stops before the optional Bison and artifact-write phases.
        .chain(EMISSION_PHASES[..EMISSION_PHASES.len() - 2].iter().copied())
        .collect::<Vec<_>>();
    assert_eq!(compile_names, expected_compile_names);
}

#[test]
fn phase_timings_are_non_negative_and_sum_by_prefix() {
    let (load_timings, compile_timings) = time_rewrite_example();
    let mut timings = load_timings;
    let compile_total = compile_timings.total_seconds();
    let print_total = compile_timings
        .phases
        .iter()
        .filter(|phase| phase.name.starts_with("print "))
        .map(|phase| phase.seconds)
        .sum::<f64>();
    let load_total = timings.total_seconds();
    let rule_parent = timings
        .phases
        .iter()
        .find(|phase| phase.name == "resolve rule bubbles")
        .expect("rule-bubble parent phase should be recorded")
        .seconds;
    let rule_children = timings
        .children_of("resolve rule bubbles")
        .map(|phase| phase.seconds)
        .sum::<f64>();
    assert!(
        rule_children <= rule_parent + 1e-9,
        "rule-bubble child phases must be contained by parent: {rule_children} > {rule_parent}"
    );
    timings.extend(compile_timings);
    let expected_phase_count = LOAD_PHASES.len() - 2
        + prologue_descriptions().len()
        + stage_descriptions().len()
        + EMISSION_PHASES.len()
        - 2;
    assert!(timings.phases.len() >= expected_phase_count);
    assert!(
        timings.phases.iter().all(|phase| phase.seconds >= 0.0),
        "{timings:?}"
    );
    assert!(
        (timings.total_seconds() - (load_total + compile_total)).abs() < 1e-9,
        "{timings:?}"
    );
    assert_eq!(timings.seconds_of("print "), print_total);
    assert_eq!(timings.seconds_of("no such phase"), 0.0);
}

#[test]
fn sequential_nested_phases_keep_one_child_depth() {
    let mut timings = PhaseTimings::default();
    timings.time_nested("first", |children| {
        children.time("first child", || ());
    });
    timings.time_nested("second", |children| {
        children.time("second child", || ());
    });
    assert_eq!(
        timings
            .phases
            .iter()
            .map(|phase| (phase.name, phase.depth))
            .collect::<Vec<_>>(),
        vec![
            ("first", 0),
            ("first child", 1),
            ("second", 0),
            ("second child", 1),
        ]
    );
}
