//! The ordered phase list recorded by the timed load and compile entry points.
//!
//! The pinned list below is the kompile pipeline's documented stage order for a source
//! definition. A pass reorder or a new stage edits this list deliberately.

#![cfg(feature = "z3-inference")]

use std::{fs, path::Path};

use k_rust::{
    builtin::embedded,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition_timed},
    outer::{LoadOptions, ResolvedSource, load_for_compilation_timed},
    timings::PhaseTimings,
};

const LOAD_PHASES: &[&str] = &[
    "parse sources",
    "select source files",
    "lower files",
    "apply sort synonyms",
    "resolve outer definition",
    "check outer modules",
    "select modules",
    "resolve configuration bubbles",
    "expand configurations",
    "resolve and check sorts",
    "resolve rule bubbles",
    "resolve loaded definition",
];

const COMPILE_PHASES: &[&str] = &[
    "expand structured configurations",
    "resolve structured configurations",
    "definition checks",
    "resolve commutative rules",
    "resolve I/O streams",
    "resolve local functions",
    "seed sort predicate syntax",
    "resolve function configuration",
    "resolve strictness",
    "resolve anonymous variables",
    "resolve contexts",
    "number sentences",
    "resolve heat/cool attributes",
    "resolve semantic casts",
    "add KItem subsorts",
    "constant folding",
    "propagate macro attributes",
    "guard or-patterns",
    "resolve fresh configuration constants",
    "generate sort predicate syntax",
    "generate sort projections",
    "expand macros",
    "add implicit computation cell",
    "resolve fresh constants",
    "regenerate sort predicate syntax",
    "regenerate sort projections",
    "check simplification rules",
    "finalize KItem subsorts",
    "concretize cells",
    "add semantics module",
    "resolve configuration variables",
    "add cool-like attributes",
    "generate sort predicate rules",
    "number sentences (final)",
    "add sort injections",
    "remove units",
    "minimize term construction",
    "collect execution rewrite order",
    "resolve transformed definition",
    "singleton overload checks",
    "collect configuration variables",
    "hook namespace checks",
    "emit KORE",
    "print definition.kore",
    "print syntaxDefinition.kore",
    "print macros.kore",
];

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
fn load_and_compile_phases_follow_the_pinned_pipeline_order() {
    let (load_timings, compile_timings) = time_rewrite_example();
    let load_names = load_timings
        .phases
        .iter()
        .map(|phase| phase.name)
        .collect::<Vec<_>>();
    assert_eq!(load_names, LOAD_PHASES);
    let compile_names = compile_timings
        .phases
        .iter()
        .map(|phase| phase.name)
        .collect::<Vec<_>>();
    assert_eq!(compile_names, COMPILE_PHASES);
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
    timings.extend(compile_timings);
    assert_eq!(
        timings.phases.len(),
        LOAD_PHASES.len() + COMPILE_PHASES.len()
    );
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
