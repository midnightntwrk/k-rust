//! The ordered phase list recorded by the timed load and compile entry points.
//!
//! The public phase tables are the kompile pipeline's documented stage order for a source
//! definition. A pass reorder or a new stage edits those tables deliberately.

#![cfg(feature = "z3-inference")]

use std::{fs, path::Path};

use k_rust::{
    builtin::embedded,
    diagnostic::DiagnosticPolicy,
    kompile::{
        CompilationBackend, CompileOptions, compile_loaded_definition_timed,
        compile_loaded_definition_with_timings,
        pipeline::{EMISSION_PHASES, LOAD_PHASES, prologue_descriptions, stage_descriptions},
    },
    outer::{LoadOptions, LoadedDefinition, ResolvedSource, load_for_compilation_timed},
    timings::PhaseTimings,
};

/// Load and compile `examples/rewrite.k` for the Rust backend, returning the load and compile
/// timings separately.
fn time_rewrite_example() -> (PhaseTimings, PhaseTimings) {
    let (loaded, load_timings) = load_rewrite_example();
    let (_, compile_timings) = compile_loaded_definition_timed(&loaded, CompileOptions::default())
        .expect("examples/rewrite.k should compile");
    (load_timings, compile_timings)
}

/// The phases a successful library compile of a source definition records, in order: the
/// prologue, the transformation stages, and the emission phases before the optional Bison and
/// artifact-write phases.
fn expected_compile_names() -> Vec<&'static str> {
    prologue_descriptions()
        .into_iter()
        .chain(stage_descriptions())
        .map(|description| description.name)
        // The library entry point stops before the optional Bison and artifact-write phases.
        .chain(EMISSION_PHASES[..EMISSION_PHASES.len() - 2].iter().copied())
        .collect()
}

/// The names of the top-level phases of `timings`, in order.
fn top_level_names(timings: &PhaseTimings) -> Vec<&'static str> {
    timings
        .phases
        .iter()
        .filter(|phase| phase.depth == 0)
        .map(|phase| phase.name)
        .collect()
}

/// The prefix of [`expected_compile_names`] that ends at the first phase named `last`.
fn expected_compile_names_through(last: &str) -> Vec<&'static str> {
    let expected = expected_compile_names();
    let end = expected
        .iter()
        .position(|name| *name == last)
        .unwrap_or_else(|| panic!("{last:?} should be a compile phase: {expected:?}"));
    expected[..=end].to_vec()
}

/// Load an in-memory source definition for the Rust backend.
fn load_source(file: &str, source: &str, main_module: &str) -> LoadedDefinition {
    let prelude = embedded("prelude.md").expect("embedded prelude should exist");
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let (loaded, _, _) = load_for_compilation_timed(
        ResolvedSource::new(file, source),
        main_module,
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
    .unwrap_or_else(|error| panic!("{file} should load: {error:?}"));
    loaded
}

/// Load `examples/rewrite.k` for the Rust backend with its load timings.
fn load_rewrite_example() -> (LoadedDefinition, PhaseTimings) {
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
    (loaded, load_timings)
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
    assert_eq!(compile_names, expected_compile_names());
}

/// A definition that loads and passes every transformation stage, and whose compile fails late,
/// at the hook namespace check, once its unadmitted hook namespace is promoted to an error.
const LATE_FAILURE: &str = r#"
module LATE-SYNTAX
endmodule
module LATE
  imports INT
  syntax Int ::= nope(Int) [function, hook(NOPE.nope)]
  rule nope(_) => 0
endmodule
"#;

fn warnings_to_errors() -> CompileOptions {
    CompileOptions {
        diagnostics: DiagnosticPolicy {
            warnings_to_errors: true,
            ..DiagnosticPolicy::default()
        },
        ..CompileOptions::default()
    }
}

#[test]
fn a_failed_compile_keeps_the_timings_of_the_stages_that_ran() {
    let loaded = load_source("late-failure.k", LATE_FAILURE, "LATE");
    let mut timings = PhaseTimings::default();
    let error = timings
        .span(|timings| {
            compile_loaded_definition_with_timings(&loaded, warnings_to_errors(), timings)
        })
        .expect_err("the unadmitted hook namespace should fail the compile");
    assert_eq!(error.stage, "hook namespace checks", "{error}");
    assert_eq!(
        error,
        compile_loaded_definition_timed(&loaded, warnings_to_errors())
            .expect_err("the timed compile should fail the same way")
    );
    assert_eq!(
        top_level_names(&timings),
        expected_compile_names_through("hook namespace checks")
    );
    assert!(
        timings.measured_span_seconds() >= timings.total_seconds(),
        "{timings:?}"
    );
}

#[test]
fn a_failed_transform_stage_is_the_last_recorded_phase() {
    // `[strict, result(8)]` names a result sort without a sort predicate; the heat/cool stage
    // rejects it.
    let source = r#"
module MAIN
  imports BOOL
  syntax 8
  syntax KResult
  syntax Exp ::= foo(Exp) [strict, result(8)] | "e"
endmodule
"#;
    let loaded = load_source("res8.k", source, "MAIN");
    let mut timings = PhaseTimings::default();
    let error =
        compile_loaded_definition_with_timings(&loaded, CompileOptions::default(), &mut timings)
            .expect_err("the heat/cool stage should reject the definition");
    assert_eq!(error.stage, "resolve heat/cool attributes", "{error}");
    let names = top_level_names(&timings);
    assert_eq!(
        names.last(),
        Some(&"resolve heat/cool attributes"),
        "{names:?}"
    );
    assert_eq!(
        names,
        expected_compile_names_through("resolve heat/cool attributes")
    );
}

#[test]
fn the_out_parameter_keeps_earlier_entries_and_span() {
    let (loaded, load_timings) = load_rewrite_example();
    let load_names_and_depths = load_timings
        .phases
        .iter()
        .map(|phase| (phase.name, phase.depth))
        .collect::<Vec<_>>();
    let load_span = load_timings.measured_span_seconds();
    let mut accumulated = load_timings;
    compile_loaded_definition_with_timings(&loaded, CompileOptions::default(), &mut accumulated)
        .expect("examples/rewrite.k should compile");
    let (earlier, appended) = accumulated.phases.split_at(load_names_and_depths.len());
    assert_eq!(
        earlier
            .iter()
            .map(|phase| (phase.name, phase.depth))
            .collect::<Vec<_>>(),
        load_names_and_depths
    );
    // The appended compile phases leave the load group's span alone.
    assert_eq!(accumulated.measured_span_seconds(), load_span);

    let (_, timed) = compile_loaded_definition_timed(&loaded, CompileOptions::default())
        .expect("examples/rewrite.k should compile");
    let timed_names_and_depths = timed
        .phases
        .iter()
        .map(|phase| (phase.name, phase.depth))
        .collect::<Vec<_>>();
    assert_eq!(
        appended
            .iter()
            .map(|phase| (phase.name, phase.depth))
            .collect::<Vec<_>>(),
        timed_names_and_depths
    );
    assert_eq!(top_level_names(&timed), expected_compile_names());
    assert!(
        timed.measured_span_seconds() >= timed.total_seconds(),
        "{timed:?}"
    );

    // Inside a caller's nested phase, every compile phase is recorded one level deeper.
    let mut outer = PhaseTimings::default();
    outer
        .time_nested("compile", |timings| {
            compile_loaded_definition_with_timings(&loaded, CompileOptions::default(), timings)
        })
        .expect("examples/rewrite.k should compile");
    assert_eq!(
        outer
            .phases
            .iter()
            .map(|phase| (phase.name, phase.depth))
            .collect::<Vec<_>>(),
        std::iter::once(("compile", 0))
            .chain(
                timed_names_and_depths
                    .iter()
                    .map(|(name, depth)| (*name, depth + 1))
            )
            .collect::<Vec<_>>()
    );
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
