//! Test support: the input and output of one compilation stage, as the pipeline produces them.
//!
//! A pass is a function from the definition the earlier stages produce to a new definition. A test
//! that builds that input by hand, or by calling a few passes in an order of its choosing, checks
//! the pass on an input the pipeline may never give it: the earlier stages add sort predicates,
//! number sentences, lower strictness and contexts, and so on. [`run_to_stage`] instead loads a
//! source as `kcompile --no-prelude` does, runs the prologue checks and every stage before the
//! named one exactly as [`compile_loaded_definition`](super::compile_loaded_definition) runs them,
//! and then runs the named stage alone. A test asserts on the stage's own output, with the input
//! beside it to state what the stage changed, so a failure names the stage that broke its
//! contract instead of a difference in the emitted KORE that any later stage could have caused.
//!
//! The sources are small and import no prelude: a test declares the syntax it needs, and a stub
//! module (`module BOOL endmodule`) where a stage only needs a module to be present. In builds
//! with debug assertions the pipeline's stage-boundary checks run on every stage here too.

use crate::{
    definition::{Definition, FlatModule, Sentence},
    outer::{LoadOptions, ResolvedSource, load_for_compilation},
    timings::PhaseTimings,
};

use super::{
    CompileError, CompileOptions,
    compile::checked_input,
    pipeline::{
        EMISSION_STAGES, PipelineState, Stage, TRANSFORM_STAGES, run_stages_seeded_with_resolved,
    },
};

/// The definition one stage receives in the pipeline, and what the stage makes of it.
pub(crate) struct StageRun {
    pub input: Definition,
    pub output: Result<Definition, CompileError>,
}

impl StageRun {
    /// The stage's output; panics with the stage's error when it failed.
    #[track_caller]
    pub fn output(&self) -> &Definition {
        self.output
            .as_ref()
            .unwrap_or_else(|error| panic!("the stage failed: {error:?}"))
    }
}

/// Load `source` (main and syntax module `MAIN`, no prelude, no `requires`), compile it with the
/// default options up to the stage named `stage` (a [`Stage::name`] of the transformation or
/// emission table), and run that stage, carrying the pipeline state the earlier stages left.
///
/// Panics when the source does not load, when an earlier stage fails, or when no stage has that
/// name: those are faults of the test, not of the stage.
#[track_caller]
pub(crate) fn run_to_stage(source: &str, stage: &str) -> StageRun {
    let options = CompileOptions::default();
    let (table, index) = locate(stage);
    let mut resolver = |_: &str, required: &str| Err(format!("unexpected require {required}"));
    let (loaded, _) = load_for_compilation(
        ResolvedSource::new("definition.k", source),
        "MAIN",
        Some("MAIN"),
        &mut resolver,
        &LoadOptions::default(),
    )
    .unwrap_or_else(|error| panic!("the source should load: {error:?}"));
    let mut timings = PhaseTimings::default();
    let (definition, resolved, _) = checked_input(&loaded, &options, &mut timings)
        .unwrap_or_else(|error| panic!("the definition checks should pass: {error:?}"));
    let mut state = PipelineState::default();
    let before = |stages: &[Stage], definition, resolved, state: &mut PipelineState| {
        run_stages_seeded_with_resolved(
            stages,
            definition,
            state,
            &options,
            &mut PhaseTimings::default(),
            resolved,
        )
        .unwrap_or_else(|error| panic!("the stages before {stage:?} should succeed: {error:?}"))
    };
    let (definition, resolved) = if table == Table::Emission {
        let (definition, resolved) = before(TRANSFORM_STAGES, definition, resolved, &mut state);
        before(&EMISSION_STAGES[..index], definition, resolved, &mut state)
    } else {
        before(&TRANSFORM_STAGES[..index], definition, resolved, &mut state)
    };
    let stages = match table {
        Table::Transform => &TRANSFORM_STAGES[index..=index],
        Table::Emission => &EMISSION_STAGES[index..=index],
    };
    let output = run_stages_seeded_with_resolved(
        stages,
        definition.clone(),
        &mut state,
        &options,
        &mut timings,
        resolved,
    )
    .map(|(output, _)| output);
    StageRun {
        input: definition,
        output,
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Table {
    Transform,
    Emission,
}

fn locate(stage: &str) -> (Table, usize) {
    let found = [
        (Table::Transform, TRANSFORM_STAGES),
        (Table::Emission, EMISSION_STAGES),
    ]
    .into_iter()
    .flat_map(|(table, stages)| {
        stages
            .iter()
            .enumerate()
            .filter(move |(_, candidate)| candidate.name == stage)
            .map(move |(index, _)| (table, index))
    })
    .collect::<Vec<_>>();
    match found.as_slice() {
        [found] => *found,
        _ => panic!(
            "{stage:?} names {} stages; the stages are {:?}",
            found.len(),
            TRANSFORM_STAGES
                .iter()
                .chain(EMISSION_STAGES)
                .map(|stage| stage.name)
                .collect::<Vec<_>>()
        ),
    }
}

/// The module `name` of `definition`.
#[track_caller]
pub(crate) fn module<'a>(definition: &'a Definition, name: &str) -> &'a FlatModule {
    definition
        .modules
        .iter()
        .find(|module| module.name == name)
        .unwrap_or_else(|| panic!("no module {name}"))
}

/// The sentences of module `name` in `definition` that carry `label(<label>)`.
pub(crate) fn labelled<'a>(
    definition: &'a Definition,
    name: &str,
    label: &str,
) -> Vec<&'a Sentence> {
    module(definition, name)
        .local_sentences
        .iter()
        .map(|sentence| &**sentence)
        .filter(|sentence| sentence.attributes().get_str("label") == Some(label))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    const SOURCE: &str = r#"
module MAIN
  syntax K
  syntax Exp ::= "a" [symbol(a)] | "b" [symbol(b)]
  configuration <k> a </k>
  rule <k> a => b </k> [label(step)]
endmodule
"#;

    /// The harness hands a stage what the stages before it produced: `number sentences` gives
    /// the rule its `UNIQUE_ID`, so the input of a later stage carries it and the input of the
    /// numbering stage does not.
    #[test]
    fn a_stage_receives_what_the_earlier_stages_produced() {
        let numbering = run_to_stage(SOURCE, "number sentences");
        let unique_id = |definition: &Definition| {
            labelled(definition, "MAIN", "step")[0]
                .attributes()
                .get_str("UNIQUE_ID")
                .map(str::to_owned)
        };
        assert_eq!(unique_id(&numbering.input), None);
        let numbered = unique_id(numbering.output()).expect("the stage numbers the rule");

        let later = run_to_stage(SOURCE, "resolve heat/cool attributes");
        assert_eq!(unique_id(&later.input), Some(numbered.clone()));
        let emission = run_to_stage(SOURCE, "remove units");
        assert_eq!(unique_id(&emission.input), Some(numbered));
    }

    #[test]
    #[should_panic(expected = "names 0 stages")]
    fn an_unknown_stage_name_is_a_test_fault() {
        let _ = run_to_stage(SOURCE, "no such stage");
    }

    /// A stage name selects one stage (`locate` panics otherwise), so a harness test names
    /// the stage it is about.
    #[test]
    fn every_stage_has_its_own_name() {
        for (table, stages) in [
            (Table::Transform, TRANSFORM_STAGES),
            (Table::Emission, EMISSION_STAGES),
        ] {
            for (index, stage) in stages.iter().enumerate() {
                assert_eq!(locate(stage.name), (table, index), "{}", stage.name);
            }
        }
    }
}
