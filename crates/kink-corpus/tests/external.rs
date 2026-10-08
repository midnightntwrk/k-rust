//! Read-only admission measurements; enabled explicitly with KINK_WORKSPACE and --ignored.
//! Timings and process-lifetime RSS are measurement logs, never artifact inputs.

use std::{fmt::Debug, path::PathBuf, sync::Mutex, time::Instant};

use k_rust::{
    backend::{Backend, BackendOptions},
    definition::{AttributeKey, Sentence},
    kast::identifier::encode,
    kompile::CompileOptions,
    kore::parser::parse_definition,
};
use kink_corpus::{
    CorpusSource, LoadedSource, ProgramSource, TestInputSpec, assemble_input, load_source,
};
use kink_native::{
    NativeValidator, ValidatedDefinition,
    bridge::validate_test_initial_state,
    census::{DeclarationCensus, declaration_census},
    representation::validate_representation,
};
use kink_patch::SemanticInput;
use serde_json::{Value, json};

const REGRESSION: &str = "inspirations/runtimeverification/k/k-distribution/tests/regression-new";
const STACK_BYTES: usize = 256 * 1024 * 1024;
// The test harness may schedule ignored tests concurrently; large targets stay serial.
static MEASUREMENT_LOCK: Mutex<()> = Mutex::new(());

#[derive(Clone, Copy)]
enum Target {
    Panopticon,
    Imp,
    Issue4142,
    WithConfig,
    #[cfg(feature = "z3")]
    Kmir,
    #[cfg(feature = "z3")]
    Kevm,
}

impl Target {
    const fn name(self) -> &'static str {
        match self {
            Self::Panopticon => "panopticon",
            Self::Imp => "imp-lesson4",
            Self::Issue4142 => "issue-4142",
            Self::WithConfig => "withConfig",
            #[cfg(feature = "z3")]
            Self::Kmir => "kmir",
            #[cfg(feature = "z3")]
            Self::Kevm => "kevm",
        }
    }

    fn source(self, workspace: PathBuf) -> CorpusSource {
        let (root, entry, includes, main, syntax, selector) = match self {
            Self::Panopticon => (
                "panopticon/K/spec".to_owned(),
                "panopticon-semantics.md",
                vec![],
                "PANOPTICON-SEMANTICS",
                "PANOPTICON-SYNTAX",
                "k",
            ),
            Self::Imp => (
                format!("{REGRESSION}/pl-tutorial/1_k/2_imp/lesson_4"),
                "imp.k",
                vec![],
                "IMP",
                "IMP-SYNTAX",
                "k",
            ),
            Self::Issue4142 => (
                format!("{REGRESSION}/issue-4142-no-symbol-overload"),
                "test.k",
                vec![],
                "TEST",
                "TEST",
                "k",
            ),
            Self::WithConfig => (
                format!("{REGRESSION}/withConfig"),
                "test.k",
                vec![],
                "TEST",
                "TEST",
                "k",
            ),
            #[cfg(feature = "z3")]
            Self::Kmir => (
                "inspirations/runtimeverification/mir-semantics/kmir/src/kmir/kdist".to_owned(),
                "mir-semantics/kmir.md",
                vec![""],
                "KMIR",
                "KMIR-AST",
                "k & ! concrete",
            ),
            #[cfg(feature = "z3")]
            Self::Kevm => (
                "inspirations/runtimeverification/evm-semantics/kevm-pyk/src/kevm_pyk/kproj"
                    .to_owned(),
                "evm-semantics/edsl.md",
                vec!["evm-semantics", "plugin"],
                "EDSL",
                "EDSL",
                "k & ! concrete",
            ),
        };
        CorpusSource {
            root: workspace.join(root),
            entry: entry.to_owned(),
            include_dirs: includes.into_iter().map(str::to_owned).collect(),
            main_module: main.to_owned(),
            syntax_module: Some(syntax.to_owned()),
            md_selector: Some(selector.to_owned()),
        }
    }

    fn inputs(self) -> Vec<(&'static str, TestInputSpec)> {
        let spec = |program, sort: &str| TestInputSpec {
            program,
            start_sort: Some(sort.to_owned()),
            variables: vec![],
        };
        match self {
            Self::Panopticon => [
                ("let1", "let x : int = 1 ; x"),
                ("shadow", "let x : int = 1 ; let x : bool = true ; x"),
                ("const", "42"),
            ]
            .into_iter()
            .map(|(id, text)| (id, spec(ProgramSource::Text(text.to_owned()), "Pgm")))
            .collect(),
            Self::Issue4142 => ["exps", "rvals", "vals"]
                .into_iter()
                .map(|id| (id, spec(ProgramSource::File(format!("{id}.test")), "Exps")))
                .collect(),
            Self::WithConfig => ["1", "2", "3", "4", "5"]
                .into_iter()
                .map(|id| (id, spec(ProgramSource::File(format!("{id}.test")), "KItem")))
                .collect(),
            _ => vec![],
        }
    }
}

fn peak_rss_kib() -> Option<u64> {
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    status.lines().find_map(|line| {
        line.strip_prefix("VmHWM:")?
            .split_whitespace()
            .next()?
            .parse()
            .ok()
    })
}

fn record(target: Target, stage: &str, start: Instant, outcome: &str, detail: Value) {
    eprintln!(
        "CS02_EXTERNAL {}",
        json!({
            "target": target.name(),
            "profile": if cfg!(feature = "z3") { "z3" } else { "no-z3" },
            "stage": stage,
            "outcome": outcome,
            "elapsed_us": start.elapsed().as_micros(),
            "peak_rss_kib": peak_rss_kib(),
            "rss_scope": "process-lifetime-high-water-mark",
            "detail": detail,
        })
    );
}

fn measure<T, E: Debug>(target: Target, stage: &str, action: impl FnOnce() -> Result<T, E>) -> T {
    let start = Instant::now();
    match action() {
        Ok(value) => {
            record(target, stage, start, "ok", Value::Null);
            value
        }
        Err(error) => {
            record(
                target,
                stage,
                start,
                "error",
                json!({"error": format!("{error:?}")}),
            );
            panic!("{} {stage}: {error:?}", target.name());
        }
    }
}

fn no_absolute_path(text: &str, source: &CorpusSource) {
    assert!(!text.contains(source.root.to_str().expect("UTF-8 root")));
    assert!(!text.contains("/home/"), "absolute home path in artifact");
    assert!(!text.contains("/tmp/"), "absolute temp path in artifact");
}

fn inputs(target: Target, loaded: &LoadedSource, compiled: &ValidatedDefinition) {
    let tests = target.inputs();
    if tests.is_empty() {
        return;
    }
    let mut backend = measure(target, "input-backend", || {
        let syntax =
            parse_definition(&compiled.artifacts().definition_kore).expect("compiled KORE parses");
        Backend::from_definition(
            syntax,
            encode(&compiled.definition().main_module),
            BackendOptions::default(),
        )
    });
    for (id, spec) in &tests {
        let state = measure(target, &format!("assemble-input:{id}"), || {
            assemble_input(loaded, spec)
        });
        measure(target, &format!("input-gate:{id}"), || {
            validate_test_initial_state(&mut backend, &state)
        });
    }
    record(
        target,
        "inputs-summary",
        Instant::now(),
        "ok",
        json!({"assembled": tests.len(), "input_gate_passed": tests.len()}),
    );
}

fn generated_maps(compiled: &ValidatedDefinition, census: &DeclarationCensus) -> Vec<Value> {
    let mut maps = vec![];
    for module in &compiled.artifacts().execution_definition.modules {
        for sentence in &module.local_sentences {
            let Sentence::Production {
                label: Some(label),
                attributes,
                sort,
                ..
            } = sentence.as_ref()
            else {
                continue;
            };
            let Some(hook) = attributes.string(AttributeKey::Hook) else {
                continue;
            };
            if !hook.starts_with("MAP.") || attributes.string(AttributeKey::Source).is_some() {
                continue;
            }
            let symbol = format!("Lbl{}", encode(&label.name));
            maps.push(json!({
                "symbol": symbol,
                "hook": hook,
                "result_sort": sort.to_string(),
                "natural": !census.findings().iter().any(|finding| finding.symbol == symbol),
            }));
        }
    }
    maps.sort_by_key(Value::to_string);
    maps
}

fn run(target: Target) {
    let Some(workspace) = std::env::var_os("KINK_WORKSPACE") else {
        record(
            target,
            "measurement",
            Instant::now(),
            "skipped",
            json!({"reason": "KINK_WORKSPACE unset"}),
        );
        return;
    };
    let _measurement_guard = MEASUREMENT_LOCK
        .lock()
        .expect("prior measurement did not fail");
    std::thread::Builder::new()
        .name(format!("cs02-{}", target.name()))
        .stack_size(STACK_BYTES)
        .spawn(move || {
            let source = target.source(PathBuf::from(workspace));
            let loaded = measure(target, "load", || load_source(&source));
            let files: Vec<_> = loaded.files.iter().map(|file| {
                assert!(!std::path::Path::new(&file.name).is_absolute());
                json!({"name": file.name, "sha256": file.sha256.to_string()})
            }).collect();
            let authored_rules = loaded.baseline.authored_sentences()
                .filter(|(_, sentence)| matches!(sentence, Sentence::Rule { .. })).count();
            record(target, "source-summary", Instant::now(), "ok", json!({
                "files": files,
                "modules": loaded.baseline.definition().modules.len(),
                "authored_rules": authored_rules,
                "load_diagnostics": loaded.baseline.loaded().diagnostics().len(),
            }));
            let input = measure(target, "semantic-input", || SemanticInput::of(&loaded.baseline));
            no_absolute_path(input.text(), &source);
            let (again, baseline) = measure(target, "semantic-input-read", || SemanticInput::read(input.text()));
            assert_eq!(again, input, "canonical SemanticInput fixed point");
            record(target, "semantic-input-summary", Instant::now(), "ok", json!({
                "bytes": input.text().len(), "sha256": input.digest().to_string(), "canonical": true,
            }));
            let validator = NativeValidator::bind(baseline, CompileOptions::default());
            let compiled = measure(target, "compile", || validator.compile_baseline());
            let artifacts = compiled.artifacts();
            no_absolute_path(&artifacts.definition_kore, &source);
            no_absolute_path(&artifacts.macros_kore, &source);
            no_absolute_path(&artifacts.syntax_definition_kore, &source);
            record(target, "compile-summary", Instant::now(), "ok", json!({
                "kore_sha256": compiled.kore_sha256().to_string(),
                "kore_bytes": artifacts.definition_kore.len(),
                "rewrite_rules": artifacts.execution_rewrite_order.len(),
                "compile_diagnostics": artifacts.diagnostics.len(),
                "configuration_variables": format!("{:?}", artifacts.configuration_variables),
            }));
            let start = Instant::now();
            let representation = validate_representation(&compiled);
            record(target, "representation", start,
                if representation.is_ok() { "admitted" } else { "refused" },
                json!({"error": representation.as_ref().err().map(ToString::to_string)}));
            let census = measure(target, "declaration-census", || declaration_census(&compiled));
            no_absolute_path(&census.text(), &source);
            record(target, "census-summary", Instant::now(), "ok", json!({
                "census": census.value(),
                "finding_classes": census.findings().iter().map(|finding| format!("{:?}", finding.class)).collect::<Vec<_>>(),
                "inert_hooks": census.inert().iter().map(|inert| &inert.hook).collect::<Vec<_>>(),
                "generated_map_declarations": generated_maps(&compiled, &census),
            }));
            // Census differences are recorded deviations for admission work, not
            // failures of this ignored measurement (CS-02 deliverable 5).
            inputs(target, &loaded, &compiled);
            // Emit the census even if the earlier representation stage was refused.
            representation.expect("representation admission must hold after TB-03M");
        })
        .expect("measurement thread starts")
        .join()
        .unwrap_or_else(|panic| std::panic::resume_unwind(panic));
}

#[test]
#[ignore = "external read-only measurement; requires KINK_WORKSPACE"]
fn panopticon() {
    run(Target::Panopticon);
}

#[test]
#[ignore = "external read-only measurement; requires KINK_WORKSPACE"]
fn imp_lesson4() {
    run(Target::Imp);
}

#[test]
#[ignore = "external read-only measurement; requires KINK_WORKSPACE"]
fn issue4142() {
    run(Target::Issue4142);
}

#[test]
#[ignore = "external read-only measurement; requires KINK_WORKSPACE"]
fn with_config() {
    run(Target::WithConfig);
}

#[cfg(feature = "z3")]
#[test]
#[ignore = "large external read-only Z3 measurement; requires KINK_WORKSPACE"]
fn kmir() {
    run(Target::Kmir);
}

#[cfg(feature = "z3")]
#[test]
#[ignore = "large external read-only Z3 measurement; requires KINK_WORKSPACE"]
fn kevm() {
    run(Target::Kevm);
}
