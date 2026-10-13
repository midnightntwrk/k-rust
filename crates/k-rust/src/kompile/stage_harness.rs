//! Test support: the input and output of one compilation stage, as the pipeline produces them.
//!
//! A pass is a function from the definition the earlier stages produce to a new definition. A test
//! that builds that input by hand, or by calling a few passes in an order of its choosing, checks
//! the pass on an input the pipeline may never give it: the earlier stages add sort predicates,
//! number sentences, lower strictness and contexts, and so on. [`run_to_stage`] instead loads a
//! source with the options `kcompile --no-prelude` loads it with, compiles it with
//! [`compile_loaded_definition`](super::compile_loaded_definition)'s own driver, and reports what
//! the named stage received and produced in that compile. A test asserts on the stage's own
//! output, with the input beside it to state what the stage changed, so a failure names the stage
//! that broke its contract instead of a difference in the emitted KORE that any later stage could
//! have caused.
//!
//! The sources are small and import no prelude: a test declares the syntax it needs, and the
//! productions of `BOOL` or `INT` that the stages generate terms of (`_andBool_`, `_+Int_`, ...).
//! Each source is a definition krust compiles in full, so the stage output a test checks is one
//! the rest of the compile accepts. In builds with debug assertions the pipeline's stage-boundary
//! checks run on every stage here too.

use crate::{
    definition::{Definition, FlatModule, Sentence},
    outer::{ResolvedSource, load_for_compilation},
    timings::PhaseTimings,
};

use super::{
    CompileError, CompileOptions,
    compile::compile_loaded_definition_observed,
    pipeline::{EMISSION_STAGES, TRANSFORM_STAGES},
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

    /// The stage's error; panics when the stage succeeded.
    #[track_caller]
    pub fn error(&self) -> &CompileError {
        self.output
            .as_ref()
            .expect_err("the stage should have failed")
    }
}

/// Load `source` (main and syntax module `MAIN`, no prelude, no `requires`) as `kcompile
/// --no-prelude` loads it for the default backend, compile it with the default options, and
/// return what the stage named `stage` (a [`Stage::name`](super::pipeline::Stage) of the
/// transformation or emission table) received and produced in that compile.
///
/// Panics when no stage has that name, when the source does not load, when the compile stops
/// before the stage, or when the stage succeeds and the rest of the compile rejects the
/// definition: those are faults of the test's source, not of the stage.
#[track_caller]
pub(crate) fn run_to_stage(source: &str, stage: &str) -> StageRun {
    locate(stage);
    let options = CompileOptions::default();
    let mut resolver = |_: &str, required: &str| Err(format!("unexpected require {required}"));
    let (loaded, _) = load_for_compilation(
        ResolvedSource::new("definition.k", source),
        "MAIN",
        Some("MAIN"),
        &mut resolver,
        &options.backend.load_options(),
    )
    .unwrap_or_else(|error| panic!("the source should load: {error:?}"));
    let mut observed = None;
    let compiled = compile_loaded_definition_observed(
        &loaded,
        options,
        &mut PhaseTimings::default(),
        &mut |ran, input, output| {
            if ran.name == stage {
                observed = Some(StageRun {
                    input: input.clone(),
                    output: output.cloned().map_err(CompileError::clone),
                });
            }
        },
    );
    let Some(run) = observed else {
        panic!("the compile stopped before {stage:?}: {:?}", compiled.err());
    };
    if run.output.is_ok()
        && let Err(error) = compiled
    {
        panic!("{stage:?} succeeded and the rest of the compile rejects the source: {error:?}");
    }
    run
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

/// Sentences of a definition, each with the name of its module.
pub(crate) type ModuleSentences<'a> = Vec<(&'a str, &'a Sentence)>;

/// Every sentence of `after` that is not a sentence of `before`, by module, with the sentences of
/// `before` that `after` no longer has: the change a stage made, up to sentence order.
pub(crate) fn sentence_changes<'a>(
    before: &'a Definition,
    after: &'a Definition,
) -> (ModuleSentences<'a>, ModuleSentences<'a>) {
    let sentences = |definition: &'a Definition| {
        definition
            .modules
            .iter()
            .flat_map(|module| {
                module
                    .local_sentences
                    .iter()
                    .map(move |sentence| (module.name.as_str(), &**sentence))
            })
            .collect::<Vec<_>>()
    };
    let (before, after) = (sentences(before), sentences(after));
    let added = after
        .iter()
        .filter(|sentence| !before.contains(sentence))
        .copied()
        .collect();
    let removed = before
        .iter()
        .filter(|sentence| !after.contains(sentence))
        .copied()
        .collect();
    (added, removed)
}

/// A one-line rendering of `sentence` for assertions and failure messages: rules, claims and
/// contexts as their terms, productions as label, sort and arguments.
pub(crate) fn render(sentence: &Sentence) -> String {
    match sentence {
        Sentence::Rule {
            body,
            requires,
            ensures,
            ..
        } => format!("rule {body} requires {requires} ensures {ensures}"),
        Sentence::Claim {
            body,
            requires,
            ensures,
            ..
        } => format!("claim {body} requires {requires} ensures {ensures}"),
        Sentence::Context { body, requires, .. } => format!("context {body} requires {requires}"),
        Sentence::ContextAlias { body, requires, .. } => {
            format!("context alias {body} requires {requires}")
        }
        Sentence::Production {
            label, sort, items, ..
        } => format!(
            "syntax {sort} ::= {}({})",
            label.as_ref().map_or("", |label| label.name.as_str()),
            items
                .iter()
                .filter_map(|item| match item {
                    crate::definition::ProductionItem::NonTerminal { sort, .. } => {
                        Some(sort.to_string())
                    }
                    crate::definition::ProductionItem::Terminal(_)
                    | crate::definition::ProductionItem::RegexTerminal { .. } => None,
                })
                .collect::<Vec<_>>()
                .join(", ")
        ),
        other @ (Sentence::SyntaxSort { .. }
        | Sentence::SortSynonym { .. }
        | Sentence::SyntaxLexical { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::Configuration { .. }
        | Sentence::Bubble { .. }) => format!("{other:?}"),
    }
}

/// [`sentence_changes`] of a successful stage, each sentence [`render`]ed: what the stage added
/// and what it removed.
#[track_caller]
pub(crate) fn rendered_changes(run: &StageRun) -> (Vec<String>, Vec<String>) {
    let (added, removed) = sentence_changes(&run.input, run.output());
    let render_all = |sentences: ModuleSentences<'_>| {
        sentences
            .into_iter()
            .map(|(_, sentence)| render(sentence))
            .collect::<Vec<_>>()
    };
    (render_all(added), render_all(removed))
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

    /// The stage under test receives what the pipeline's earlier stages make of the source; a
    /// source that only stubs the modules the compiler generates terms of (`module BOOL
    /// endmodule` where a later stage generates `_andBool_`) leaves unchecked whether the tested
    /// stage's output is something the rest of the compile accepts, and nothing would flag it
    /// when a stage starts to depend on the declarations the stub omits. So every source a stage
    /// test hands to [`run_to_stage`] and expects to pass its stage compiles in full, as
    /// `kcompile --no-prelude` compiles it. [`run_to_stage`] asserts this of each source it is
    /// given; this test reads the sources from the stage tests themselves (each raw string
    /// holding `module MAIN` in a file that calls `run_to_stage`; a source whose test reads the
    /// stage's error is expected to fail somewhere and is skipped), so it holds of every source
    /// whichever stage tests a run selects.
    #[test]
    fn every_stage_harness_source_compiles_in_full() {
        fn sources(directory: &std::path::Path, found: &mut Vec<std::path::PathBuf>) {
            for entry in std::fs::read_dir(directory).expect("read the kompile sources") {
                let path = entry.expect("directory entry").path();
                if path.is_dir() {
                    sources(&path, found);
                } else if path.extension().is_some_and(|extension| extension == "rs") {
                    found.push(path);
                }
            }
        }
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/kompile");
        let mut files = Vec::new();
        sources(&root, &mut files);
        files.sort();
        let literal = regex::Regex::new(r##"(?s)r#"(.*?)"#"##).unwrap();
        let expects_error = regex::Regex::new(r"\.error\(\)|expect_err|is_err").unwrap();
        let mut checked = 0;
        let mut failures = Vec::new();
        for file in files {
            let text = std::fs::read_to_string(&file).unwrap();
            if !text.contains("run_to_stage(") || file.ends_with("stage_harness.rs") {
                continue;
            }
            for found in literal.captures_iter(&text) {
                let whole = found.get(0).unwrap();
                let source = &found[1];
                if !source.contains("module MAIN") {
                    continue;
                }
                let rest = &text[whole.end()..];
                let test_rest = rest.split("#[test]").next().unwrap_or(rest);
                if expects_error.is_match(test_rest) {
                    continue;
                }
                let line = text[..whole.start()].lines().count() + 1;
                let name = format!(
                    "{}:{line}",
                    file.strip_prefix(&root).unwrap_or(&file).display()
                );
                checked += 1;
                let mut resolver =
                    |_: &str, required: &str| Err(format!("unexpected require {required}"));
                let loaded = load_for_compilation(
                    ResolvedSource::new("definition.k", source),
                    "MAIN",
                    Some("MAIN"),
                    &mut resolver,
                    &CompileOptions::default().backend.load_options(),
                );
                let outcome = match loaded {
                    Err(error) => Err(format!("does not load: {error:?}")),
                    Ok((loaded, _)) => {
                        super::super::compile_loaded_definition(&loaded, CompileOptions::default())
                            .map(|_| ())
                            .map_err(|error| format!("does not compile: {error:?}"))
                    }
                };
                if let Err(message) = outcome {
                    let message = message.chars().take(300).collect::<String>();
                    failures.push(format!("{name}: {message}"));
                }
            }
        }
        assert!(checked > 0, "found no stage-harness sources");
        assert!(
            failures.is_empty(),
            "{} of {checked} stage-harness sources do not compile in full:\n{}",
            failures.len(),
            failures.join("\n")
        );
    }

    /// A stage test's source is a definition krust compiles: when the named stage succeeds and
    /// a later stage rejects the definition, the source is at fault and the harness says so.
    /// Here the source declares no `_andBool_`, which context lowering generates for the
    /// strictness the stage adds, so the compile fails after the stage.
    #[test]
    #[should_panic(expected = "the rest of the compile rejects the source")]
    fn a_source_a_later_stage_rejects_is_a_test_fault() {
        let _ = run_to_stage(
            r#"
module BOOL
endmodule
module MAIN
  syntax K
  syntax KResult
  syntax Val ::= "v" [symbol(v)]
  syntax KResult ::= Val
  syntax Exp ::= Val | plus(Exp, Exp) [strict, symbol(plus)]
  configuration <k> v </k>
endmodule
"#,
            "resolve strictness",
        );
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
