//! CS-16 A1-A5: corpus admission of natural ground collection terminals.

use k_rust::{
    backend::{Backend, BackendOptions},
    kompile::CompileOptions,
    kore::{ast::Pattern, codec::from_value, parser::parse_definition},
};
use kink_campaign::{
    Campaign, CampaignOptions, CrashPolicy, OracleDeclaration, Projection, ScheduleMode,
    StateProjection, TestCase, run_campaign_multi,
};
use kink_corpus::{
    CorpusSource, ProgramSource, TestInputSpec,
    admission::{AdmissionRecord, AdmissionResult, admit_definition, compile_definition},
    assemble_input, load_source,
    manifest::CorpusManifest,
    runner::all_normal,
};
use kink_native::{
    CensusVerdict, NativeValidator,
    bridge::{BridgeContext, paths_from_execution_values},
    execution::{ExecutionAdapter, ExecutionBudget, SolverProfile},
    feasibility::TestInitialState,
    step_events::ObservationDecider,
};
use kink_patch::{Discovery, SelectionPolicy, canonical_json, select, sha256};
use kink_pattern::SymbolSorts;
use serde_json::{Value, json};
use std::{
    path::{Path, PathBuf},
    sync::Mutex,
    time::Duration,
};

fn workspace() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .unwrap()
}
fn with_stack(body: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(body)
        .unwrap()
        .join()
        .unwrap_or_else(|panic| std::panic::resume_unwind(panic));
}
fn admission(
    root: &str,
    file: &str,
    main: &str,
    syntax: Option<&str>,
    programs: &[&str],
    depth: u64,
) -> AdmissionResult {
    let workspace = workspace();
    let mut v: Value = serde_json::from_str(include_str!(
        "../../../testdata/corpus/admission-v1/clean.json"
    ))
    .unwrap();
    let d = &mut v["definitions"][0];
    d["root"]["path"] = json!(root);
    d["entry"] = json!(file);
    d["main_module"] = json!(main);
    d["syntax_module"] = json!(syntax);
    d["files"] = json!([{"name":file,"sha256":sha256(&std::fs::read(workspace.join(root).join(file)).unwrap()).to_string()}]);
    let template = d["tests"][0].clone();
    d["tests"] = json!(
        programs
            .iter()
            .enumerate()
            .map(|(i, text)| {
                let mut test = template.clone();
                test["id"] = json!(format!("p{i}"));
                test["input"]["program"]["text"] = json!(text);
                test
            })
            .collect::<Vec<_>>()
    );
    v["campaign"]["budget"]["max_depth"] = json!(depth);
    let manifest = CorpusManifest::from_canonical_json(&canonical_json(&v)).unwrap();
    admit_definition(&manifest, "clean", &workspace)
}
fn admitted(result: AdmissionResult, count: usize) {
    assert!(result.record.refusal.is_none(), "{}", result.record.text());
    assert_eq!(
        result.record.census.as_ref().unwrap().verdict(),
        CensusVerdict::Natural
    );
    assert_eq!(result.admitted.expect("admitted").tests.len(), count);
}
#[test]
fn a1_a4_local_admission_rows() {
    with_stack(|| {
        admitted(
            admission(
                "testdata/corpus/admission-v1",
                "map-unit.k",
                "CS12-MAP-UNIT",
                None,
                &["true", "false"],
                20,
            ),
            2,
        );
        let bytes = admission(
            "testdata/corpus/admission-v1",
            "map.k",
            "CS12-MAP",
            None,
            &["true", "false"],
            20,
        );
        assert!(bytes.admitted.is_none());
        let refusal = bytes.record.refusal.unwrap();
        assert_eq!(
            (&*refusal.stage, &*refusal.reason),
            ("baseline", "baseline-oracle-failed")
        );
        admitted(
            admission(
                "testdata/k",
                "collimp.k",
                "COLLIMP",
                Some("COLLIMP-SYNTAX"),
                &["var x ; var y ; x = 1 + 2 ; y = x + x ;", "var x ; var x ;"],
                200,
            ),
            2,
        );
        admitted(
            admission(
                "testdata/k",
                "collenv.k",
                "COLLENV",
                Some("COLLENV-SYNTAX"),
                &["let x = 1 ; x", "42"],
                200,
            ),
            2,
        );
    });
}
fn oracles() -> Vec<OracleDeclaration> {
    [
        StateProjection::ExitStop {
            exit_code_cell: None,
        },
        StateProjection::WholeTerm,
    ]
    .into_iter()
    .map(|p| OracleDeclaration::new(CrashPolicy::Reject, Projection::State(p)).unwrap())
    .collect()
}
static EXTERNAL_LOCK: Mutex<()> = Mutex::new(());

/// Run the CS-12 compile stage and baseline-only campaigns on read-only external sources.
fn external(imp: bool) {
    let Some(root) = std::env::var_os("KINK_WORKSPACE") else {
        println!("CS16-A5 skipped: KINK_WORKSPACE unset");
        return;
    };
    let _lock = EXTERNAL_LOCK.lock().unwrap();
    with_stack(move || {
        let name = if imp { "imp-lesson4" } else { "panopticon" };
        let (root_path, entry, main, syntax, depth, programs): (_, _, _, _, _, Vec<(&str, &str)>) =
            if imp {
                (
                    "inspirations/runtimeverification/k/k-distribution/tests/regression-new/pl-tutorial/1_k/2_imp/lesson_4",
                    "imp.k",
                    "IMP",
                    "IMP-SYNTAX",
                    1000,
                    vec![(
                        "sum3",
                        "int n, sum; n = 3; sum = 0; while (!(n <= 0)) { sum = sum + n; n = n + -1; }",
                    )],
                )
            } else {
                (
                    "panopticon/K/spec",
                    "panopticon-semantics.md",
                    "PANOPTICON-SEMANTICS",
                    "PANOPTICON-SYNTAX",
                    100,
                    vec![
                        ("let1", "let x : int = 1 ; x"),
                        ("shadow", "let x : int = 1 ; let x : bool = true ; x"),
                        ("const", "42"),
                    ],
                )
            };
        let loaded = load_source(&CorpusSource {
            root: PathBuf::from(root).join(root_path),
            entry: entry.into(),
            include_dirs: vec![],
            main_module: main.into(),
            syntax_module: Some(syntax.into()),
            md_selector: Some("k".into()),
        })
        .unwrap();
        let validator = NativeValidator::bind(loaded.baseline.clone(), CompileOptions::default());
        let mut record = AdmissionRecord::new(name);
        let compiled = compile_definition(&validator, &mut record).unwrap();
        assert_eq!(
            record.census.as_ref().unwrap().verdict(),
            CensusVerdict::Natural
        );
        let module = k_rust::kast::identifier::encode(main);
        let definition = parse_definition(&compiled.artifacts().definition_kore).unwrap();
        let sorts = SymbolSorts::from_definition(&definition);
        let mut backend =
            Backend::from_definition(definition, &module, BackendOptions::default()).unwrap();
        let budget = ExecutionBudget {
            time: Duration::from_secs(120),
            max_simplification_iterations: 10_000,
            max_depth: Some(depth),
            max_breadth: None,
        };
        for (id, text) in programs {
            let initial_state = assemble_input(
                &loaded,
                &TestInputSpec {
                    program: ProgramSource::Text(text.into()),
                    start_sort: Some("Pgm".into()),
                    variables: vec![],
                },
            )
            .unwrap();
            let execution = ExecutionAdapter::with_profile(SolverProfile::BUILD)
                .execute(&mut backend, &initial_state, budget)
                .unwrap();
            assert!(!execution.timed_out(), "{name} {id}");
            let distinct: std::collections::BTreeSet<Pattern> = execution
                .leaves()
                .iter()
                .map(|leaf| from_value(&leaf.branch.state).unwrap())
                .collect();
            let bridged = backend
                .with_solver(None, |definition, solver| {
                    let decider = ObservationDecider::new(
                        definition,
                        solver,
                        TestInitialState::of_test(&initial_state),
                    );
                    for term in &distinct {
                        assert_eq!(
                            decider.terminal_value(term),
                            Some(term.clone()),
                            "{name} {id}"
                        );
                    }
                    Ok::<_, k_rust::backend::BackendError>(paths_from_execution_values(
                        &execution,
                        &BridgeContext {
                            test_id: id,
                            classify: &all_normal,
                            sorts: &sorts,
                        },
                        &|term| decider.terminal_value(term),
                    ))
                })
                .unwrap()
                .unwrap();
            assert!(
                bridged.paths.iter().all(|path| path.complete),
                "{name} {id}"
            );
            if imp {
                assert_eq!(execution.leaves().len(), 64);
                assert_eq!(bridged.paths.len(), 64);
                assert_eq!(distinct.len(), 1);
            }
            let tests = [TestCase {
                id: id.into(),
                initial_state,
                oracles: oracles(),
            }];
            let discovery = Discovery::empty(validator.baseline(), false, false);
            let generation = select(&discovery, SelectionPolicy::Each, 1)
                .unwrap()
                .fold("cs16/baseline-only", |_| unreachable!())
                .unwrap();
            let campaign = Campaign {
                validator: &validator,
                module: &module,
                observation: &[],
                classify: &all_normal,
                tests: &tests,
                budget,
            };
            for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
                let options = CampaignOptions {
                    schedule,
                    selection: kink_campaign::SelectionPolicy::None,
                    share_evidence: true,
                };
                let run =
                    run_campaign_multi(&campaign, std::slice::from_ref(&generation), &options)
                        .unwrap();
                assert!(run.mutants.is_empty());
                println!(
                    "CS16-A5|{:?}|{name}|{id}|{schedule:?}|admitted|leaves={}|paths={}|distinct={}",
                    SolverProfile::BUILD,
                    execution.leaves().len(),
                    bridged.paths.len(),
                    distinct.len()
                );
            }
        }
    });
}
#[test]
#[ignore = "external read-only collection admission; requires KINK_WORKSPACE"]
fn a5_panopticon() {
    external(false);
}
#[test]
#[ignore = "external read-only collection admission; requires KINK_WORKSPACE"]
fn a5_imp_lesson4() {
    external(true);
}
