//! Multi-operator scheduling, data replay and record-only declaration census.
#[path = "../../../testdata/k/step_support.rs"]
mod step_support;
#[path = "../../../testdata/k/support.rs"]
mod support;
use k_rust::{builtin, kompile::CompileOptions, kore::ast::Pattern, outer::ResolvedSource};
use kink_campaign::*;
use kink_native::{
    NativeValidator, declaration_census, execution::ExecutionBudget, step_events::StepObservation,
};
use kink_patch::{
    Action, Baseline, CAMPAIGN_MANIFEST_DOMAIN, CandidateFailure, CandidateGeneration,
    ClaimSupport, Clause, Edit, OperatorSpec, Patch, SiteSelector, Universe, canonical_json,
    catalogue_v1, derive_sites, generate, payload_digest, resolve_universe, select,
};
use kink_pattern::{Atom, ExecutionTerminalKind, PatternArm, PatternPlan};
use serde_json::{Value, json};
use std::{path::Path, time::Duration};
const BUDGET: ExecutionBudget = ExecutionBudget {
    time: Duration::from_secs(30),
    max_simplification_iterations: 1000,
    max_depth: Some(32),
    max_breadth: None,
};
fn normal(_: &Pattern) -> ExecutionTerminalKind {
    ExecutionTerminalKind::Normal
}
fn with_stack(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap();
}
fn code(b: &Baseline) -> Result<CandidateGeneration<'_>, CandidateFailure> {
    let discovery = derive_sites(
        b,
        "site",
        &[
            SiteSelector::RuleLabel("COUNTER.increment".into()),
            SiteSelector::Path(vec![0]),
        ],
    )?;
    select(&discovery, kink_patch::SelectionPolicy::Each, 1)?.fold("code", |_| {
        Patch::new(vec![Edit::AddAttribute {
            at: support::rule(b, "COUNTER.increment"),
            key: "foo".into(),
            value: json!(""),
        }])
        .unwrap()
    })
}
fn code_id() -> ManifestOperator<'static> {
    ManifestOperator::Code(OperatorId {
        id: "code",
        version: 1,
        policy: kink_patch::SelectionPolicy::Each,
    })
}
fn counter_tests(events: &[kink_native::step_events::StepEventSpec]) -> Vec<TestCase> {
    let vocabulary = StepObservation::vocabulary_of(events).unwrap();
    let pattern = |name: &str| {
        OracleDeclaration::new(
            CrashPolicy::CompareIdentity,
            Projection::Pattern {
                plan: PatternPlan::new(
                    &vocabulary,
                    vec![],
                    vec![PatternArm {
                        atoms: vec![Atom {
                            constructor: name.into(),
                            payload: vec![],
                        }],
                        relations: vec![],
                    }],
                    None,
                )
                .unwrap(),
                with_bindings: false,
            },
        )
        .unwrap()
    };
    let z = || support::app("Lblz", vec![]);
    let s = |x| support::app("Lbls", vec![x]);
    vec![
        TestCase {
            id: "counter".into(),
            initial_state: support::initial_state(
                support::app("Lblcounter", vec![z(), s(s(s(z())))]),
                "SortCounter",
            ),
            oracles: vec![pattern("increment")],
        },
        TestCase {
            id: "choose".into(),
            initial_state: support::initial_state(
                support::app(
                    "Lblchoose",
                    vec![Pattern::DomainValue {
                        sort: k_rust::kompile::initial_configuration::kore_sort("SortBool"),
                        value: "true".into(),
                    }],
                ),
                "SortControl",
            ),
            oracles: vec![pattern("branchTaken")],
        },
    ]
}
fn census_baseline(value: &Value) {
    for mutant in value["mutants"].as_array().unwrap() {
        assert_eq!(
            mutant["census"],
            if mutant["validation"]["outcome"] == "compiled" {
                json!("baseline")
            } else {
                Value::Null
            },
            "STOP: compiled declaration census differs: {mutant}"
        );
    }
}
fn no_timeout(value: &Value) {
    match value {
        Value::String(s) => assert!(
            !matches!(s.as_str(), "timeout" | "time-limit"),
            "STOP: time bound fired"
        ),
        Value::Array(a) => a.iter().for_each(no_timeout),
        Value::Object(o) => o.values().for_each(no_timeout),
        _ => (),
    }
}
/// Mixed generations (three catalogue specs and a code operator over counter.k) in `schedule`:
/// the multi-generation run is scored with ids in order, its manifest is natural with the
/// baseline census, and its report fires no time bound; with `replay_rows`, the report replays
/// and each of five declaration tampers is refused; for each generation index of `singles`, the
/// generation run alone gives each mutant the multi run's status and killing tests, and its
/// single report's score is the multi report's per-operator score (and the single-generation
/// multi report's bytes). The kink tier runs Full in parts that run in parallel, the heavy tier
/// FirstKill (test-gate TG-C; until then one test ran both schedules).
fn mixed_generations(schedule: ScheduleMode, replay_rows: bool, singles: &'static [usize]) {
    with_stack(move || {
        let validator =
            NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
        let events = step_support::counter(true);
        let tests = counter_tests(&events);
        let campaign = Campaign {
            validator: &validator,
            module: "COUNTER",
            observation: &events,
            classify: &normal,
            tests: &tests,
            budget: BUDGET,
        };
        let universe = resolve_universe(validator.baseline(), &Universe::v1());
        let specs: Vec<_> = catalogue_v1()
            .into_iter()
            .filter(|s| matches!(s.id(), "cond-true" | "cond-false" | "delete-rule"))
            .collect();
        assert_eq!(specs.len(), 3);
        let mut generations: Vec<_> = specs
            .iter()
            .map(|s| generate(validator.baseline(), &universe, s, usize::MAX).unwrap())
            .collect();
        generations.push(code(validator.baseline()).unwrap());
        let mut operators: Vec<_> = specs.iter().map(ManifestOperator::Spec).collect();
        operators.push(code_id());
        {
            let options = CampaignOptions {
                schedule,
                selection: SelectionPolicy::None,
                share_evidence: true,
                run: kink_campaign::RunOptions::default(),
                compile_workers: 1,
            };
            let run = run_campaign_multi(&campaign, &generations, &options).unwrap();
            assert!(generations.iter().all(CandidateGeneration::scored));
            assert!(run.score.is_some());
            for (id, mutant) in run.mutants.iter().enumerate() {
                assert_eq!(mutant.report.mutant_id, MutantId(id));
            }
            let manifest = campaign_manifest_multi(&MultiManifestInput {
                campaign: &campaign,
                generations: &generations,
                operators: &operators,
                universe: Some(&universe),
                schedule,
                selection: SelectionPolicy::None,
                classifier: "normal",
            })
            .unwrap();
            assert_eq!(manifest.value()["admission"]["verdict"], "natural");
            census_baseline(manifest.value());
            let report = campaign_report_multi(&manifest, &campaign, &generations, &run).unwrap();
            no_timeout(report.value());
            let mut offset = 0;
            for (index, generation) in generations.iter().enumerate() {
                if !singles.contains(&index) {
                    offset += generation.candidates().len();
                    continue;
                }
                let alone = run_campaign(&campaign, generation, schedule).unwrap();
                for (local, mutant) in alone.mutants.iter().enumerate() {
                    let multi = &run.mutants[offset + local];
                    assert_eq!(
                        multi.report.status, mutant.report.status,
                        "STOP: multi status differs"
                    );
                    assert_eq!(
                        multi.report.killing_test_ids, mutant.report.killing_test_ids,
                        "STOP: multi killing tests differ"
                    );
                }
                assert_eq!(report.value()["summary"]["per_operator"][index]["score"], {
                    let single_manifest = campaign_manifest(&ManifestInput {
                        campaign: &campaign,
                        generation,
                        schedule,
                        selection: SelectionPolicy::None,
                        operators: &operators[index..index + 1],
                        classifier: "normal",
                    })
                    .unwrap();
                    let single =
                        campaign_report(&single_manifest, &campaign, generation, &alone).unwrap();
                    let singleton_run =
                        run_campaign_multi(&campaign, std::slice::from_ref(generation), &options)
                            .unwrap();
                    let multi_single = campaign_report_multi(
                        &single_manifest,
                        &campaign,
                        std::slice::from_ref(generation),
                        &singleton_run,
                    )
                    .unwrap();
                    assert_eq!(single.text(), multi_single.text());
                    single.value()["summary"]["score"].clone()
                });
                offset += generation.candidates().len();
            }
            if schedule == ScheduleMode::Full && replay_rows {
                println!("CS09_EXAMPLE_MANIFEST {}", manifest.text());
            }
            if !replay_rows {
                return;
            }
            let decoded: Vec<_> = manifest.value()["operators"].as_array().unwrap()[..3]
                .iter()
                .map(|op| OperatorSpec::from_canonical_json(&canonical_json(&op["spec"])).unwrap())
                .collect();
            let mut replay_ops: Vec<_> = decoded
                .iter()
                .map(|spec| ReplayOperator::Spec {
                    spec,
                    cap: usize::MAX,
                })
                .collect();
            replay_ops.push(ReplayOperator::Code {
                id: "code",
                version: 1,
                policy: kink_patch::SelectionPolicy::Each,
                select: &code,
            });
            let declaration = ReplayDeclaration {
                module: "COUNTER",
                observation: &events,
                classify: &normal,
                classifier: "normal",
                tests: &tests,
                budget: BUDGET,
                schedule,
                selection: SelectionPolicy::None,
                operators: &replay_ops,
            };
            assert_eq!(
                replay(
                    &report.text(),
                    manifest.baseline_input().text(),
                    &declaration
                ),
                ReplayOutcome::Reproduced,
                "STOP: untampered replay"
            );
            for row in 0..5 {
                let mut changed = report.value().clone();
                match row {
                    0 => changed["manifest"]["operators"][0]["spec"]["version"] = json!(2),
                    1 => changed["manifest"]["universe"]["excluded"]
                        .as_array_mut()
                        .unwrap()
                        .push(json!({"module":"COUNTER","index":0,"reason":"untyped"})),
                    2 => {
                        changed["manifest"]["admission"]["declarations"]["verdict"] =
                            json!("flagged")
                    }
                    3 => changed["manifest"]["mutants"][0]["operator"] = json!(3),
                    _ => changed["manifest"]["operators"]
                        .as_array_mut()
                        .unwrap()
                        .swap(0, 1),
                }
                changed["manifest_sha256"] = json!(
                    payload_digest(
                        CAMPAIGN_MANIFEST_DOMAIN,
                        canonical_json(&changed["manifest"]).as_bytes()
                    )
                    .to_string()
                );
                assert_eq!(
                    replay(
                        &canonical_json(&changed),
                        manifest.baseline_input().text(),
                        &declaration
                    ),
                    ReplayOutcome::Refused(ReplayRefusal::Declaration),
                    "tamper row {row}"
                );
            }
        }
    });
}

/// Builds the manifest of every catalogue mutant of fixture `name` in each schedule of
/// `schedules` (each compiles every mutant) and requires every compiled mutant's census to be the
/// baseline's; returns how many compiled, counted in Full.
fn catalogue_census_for_fixture(
    name: &str,
    specs: &[OperatorSpec],
    schedules: &[ScheduleMode],
) -> usize {
    let mut compiled = 0;
    let text = std::fs::read_to_string(Path::new(support::DIR).join(name)).unwrap();
    let module = text
        .lines()
        .filter_map(|l| l.trim().strip_prefix("module "))
        .next_back()
        .unwrap()
        .split_whitespace()
        .next()
        .unwrap()
        .to_owned();
    let mut resolver = |_: &str, required: &str| {
        builtin::embedded(required).ok_or_else(|| format!("{required} is not embedded"))
    };
    let baseline = Baseline::load(
        ResolvedSource::new(name, text),
        &module,
        None,
        &mut resolver,
        &support::options(),
    )
    .unwrap_or_else(|error| panic!("CS-08 fixture {name} did not load: {error}"));
    let validator = NativeValidator::bind(baseline, CompileOptions::default());
    let Ok(baseline) = validator.compile_baseline() else {
        return 0;
    };
    let _ = declaration_census(&baseline).unwrap();
    let universe = resolve_universe(validator.baseline(), &Universe::v1());
    let generations = specs
        .iter()
        .map(|spec| generate(validator.baseline(), &universe, spec, usize::MAX).unwrap())
        .collect::<Vec<_>>();
    let operators = specs.iter().map(ManifestOperator::Spec).collect::<Vec<_>>();
    let campaign = Campaign {
        validator: &validator,
        module: &module,
        observation: &[],
        classify: &normal,
        tests: &[],
        budget: BUDGET,
    };
    for &schedule in schedules {
        let manifest = campaign_manifest_multi(&MultiManifestInput {
            campaign: &campaign,
            generations: &generations,
            operators: &operators,
            universe: Some(&universe),
            schedule,
            selection: SelectionPolicy::None,
            classifier: "normal",
        })
        .unwrap();
        census_baseline(manifest.value());
        if schedule == ScheduleMode::Full {
            compiled += manifest.value()["mutants"]
                .as_array()
                .unwrap()
                .iter()
                .filter(|m| m["validation"]["outcome"] == "compiled")
                .count();
        }
    }
    println!("CS09_SWEEP_DEFINITION {name}");
    compiled
}

mod heavy {
    use super::*;

    /// `kink_tier::mixed_generations_*_in_full` in FirstKill, every part in one test.
    #[test]
    #[ignore = "heavy"]
    fn mixed_generations_equal_single_runs_and_replay_manifest_specs_in_first_kill() {
        mixed_generations(ScheduleMode::FirstKill, true, &[0, 1, 2, 3]);
    }

    /// Heavy tier (README, Gate): the mutants of every catalogue spec of `part` of `parts` (the
    /// specs whose catalogue index is `part` modulo `parts`) of fixture `name` of `testdata/k`,
    /// compiled in each schedule of `schedules` with the baseline's census. One test per fixture,
    /// so that they run in parallel, and for t12probe.k, whose sweep alone takes longer than
    /// nextest allows one test, one per schedule and quarter of the catalogue (test-gate TG-C;
    /// until then one test swept every fixture on four threads). A named fixture of the kink
    /// tier's sweep must compile some mutant in Full, as there.
    fn catalogue_sweep_of(
        name: &'static str,
        schedules: &'static [ScheduleMode],
        part: usize,
        parts: usize,
    ) {
        with_stack(move || {
            let specs = catalogue_v1()
                .into_iter()
                .enumerate()
                .filter(|(index, _)| index % parts == part)
                .map(|(_, spec)| spec)
                .collect::<Vec<_>>();
            let compiled = catalogue_census_for_fixture(name, &specs, schedules);
            if NAMED_SWEEP_FIXTURES.contains(&name) && schedules.contains(&ScheduleMode::Full) {
                assert!(compiled > 0, "{name} compiles no catalogue mutant");
            }
            println!("CS09_SWEEP_COMPILED {name} {schedules:?} {part}/{parts} {compiled}");
        });
    }

    const BOTH: &[ScheduleMode] = &[ScheduleMode::Full, ScheduleMode::FirstKill];
    const FULL: &[ScheduleMode] = &[ScheduleMode::Full];
    const FIRST_KILL: &[ScheduleMode] = &[ScheduleMode::FirstKill];

    /// One heavy test per fixture, and the list they sweep.
    macro_rules! catalogue_sweep {
        ($($test:ident: $name:literal $schedules:ident $part:literal / $parts:literal,)*) => {
            /// The fixtures the heavy sweep runs, in name order, with the schedules and the part
            /// of the catalogue of each test.
            const SWEPT_FIXTURES: &[(&str, &[ScheduleMode], usize, usize)] =
                &[$(($name, $schedules, $part, $parts)),*];

            $(
                #[test]
                #[ignore = "heavy"]
                fn $test() {
                    catalogue_sweep_of($name, $schedules, $part, $parts);
                }
            )*
        };
    }

    catalogue_sweep! {
    compiled_catalogue_sweep_of_annotated: "annotated.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_b1coll: "b1coll.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_cellmap: "cellmap.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_claims: "claims.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_collenv: "collenv.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_collimp: "collimp.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_collstore: "collstore.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_conflate: "conflate.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_conflate2: "conflate2.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_conflate3: "conflate3.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_conflatem: "conflatem.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_counter: "counter.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_counter_bytwo: "counter_bytwo.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_duplicate_unlabelled: "duplicate_unlabelled.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_effectmem: "effectmem.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_equation_ensures_support: "equation-ensures-support.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_floatzero: "floatzero.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_freshgen: "freshgen.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_guardeddiv: "guardeddiv.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_guardedeq: "guardedeq.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_guardedmem: "guardedmem.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_memory: "memory.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_nd: "nd.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_nextgap: "nextgap.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_opaquemem: "opaquemem.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_partialreq: "partialreq.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_partialstep: "partialstep.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_residue: "residue.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_rulecondfail: "rulecondfail.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_scopeforge: "scopeforge.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_strictheat: "strictheat.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_subsort_steps: "subsort_steps.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_symbolic_claim_mutation: "symbolic-claim-mutation.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_symbolic_claim_survivor: "symbolic-claim-survivor.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_symbolic_equation_ensures: "symbolic-equation-ensures.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_symbottom: "symbottom.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_symensures: "symensures.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_symmem: "symmem.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_symmem_existential: "symmem_existential.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_symmem_release: "symmem_release.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_symnarrow: "symnarrow.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_symowise: "symowise.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_sympartial: "sympartial.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_symwrap: "symwrap.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_symwraptotal: "symwraptotal.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_t12fold: "t12fold.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_t12hook: "t12hook.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_t12int: "t12int.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_t12macro: "t12macro.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_t12probe_in_full_0: "t12probe.k" FULL 0 / 4,
    compiled_catalogue_sweep_of_t12probe_in_full_1: "t12probe.k" FULL 1 / 4,
    compiled_catalogue_sweep_of_t12probe_in_full_2: "t12probe.k" FULL 2 / 4,
    compiled_catalogue_sweep_of_t12probe_in_full_3: "t12probe.k" FULL 3 / 4,
    compiled_catalogue_sweep_of_t12probe_in_first_kill_0: "t12probe.k" FIRST_KILL 0 / 4,
    compiled_catalogue_sweep_of_t12probe_in_first_kill_1: "t12probe.k" FIRST_KILL 1 / 4,
    compiled_catalogue_sweep_of_t12probe_in_first_kill_2: "t12probe.k" FIRST_KILL 2 / 4,
    compiled_catalogue_sweep_of_t12probe_in_first_kill_3: "t12probe.k" FIRST_KILL 3 / 4,
    compiled_catalogue_sweep_of_t12token: "t12token.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_t12unev: "t12unev.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_t13implemented: "t13implemented.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_t13inert: "t13inert.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_t13ite: "t13ite.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_t13natural: "t13natural.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_t13owk: "t13owk.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_t13role: "t13role.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_t13tok: "t13tok.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_t13typedlist: "t13typedlist.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_tb02bytes: "tb02bytes.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_tb02bytestoken: "tb02bytestoken.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_tb02float: "tb02float.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_tb02input: "tb02input.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_tb02string: "tb02string.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_tb02stringtoken: "tb02stringtoken.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_tb02token: "tb02token.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_unbound: "unbound.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_undecided: "undecided.k" BOTH 0 / 1,
    compiled_catalogue_sweep_of_unlabelled: "unlabelled.k" BOTH 0 / 1,
    }

    /// The heavy sweep runs every top-level fixture of `testdata/k` over the whole catalogue in
    /// both schedules, the named fixtures among them: a fixture added to the directory fails this
    /// test until it gets its sweep test.
    #[test]
    #[ignore = "heavy"]
    fn compiled_catalogue_sweep_covers_every_fixture() {
        let mut names: Vec<_> = std::fs::read_dir(support::DIR)
            .unwrap()
            .map(|e| e.unwrap().file_name().into_string().unwrap())
            .filter(|n| n.ends_with(".k"))
            .collect();
        names.sort();
        println!("CS09_SWEEP_FIXTURES {}", names.len());
        let mut swept =
            std::collections::BTreeMap::<&str, Vec<(ScheduleMode, usize, usize)>>::new();
        for (name, schedules, part, parts) in SWEPT_FIXTURES {
            for schedule in *schedules {
                swept
                    .entry(name)
                    .or_default()
                    .push((*schedule, *part, *parts));
            }
        }
        assert_eq!(
            names,
            swept
                .keys()
                .map(|name| name.to_string())
                .collect::<Vec<_>>()
        );
        for (name, tests) in &mut swept {
            tests.sort_by_key(|(schedule, part, _)| (*schedule != ScheduleMode::Full, *part));
            let parts = tests[0].2;
            let every = BOTH
                .iter()
                .flat_map(|schedule| (0..parts).map(move |part| (*schedule, part, parts)))
                .collect::<Vec<_>>();
            assert_eq!(
                *tests, every,
                "{name}: every part of the catalogue swept in both schedules once"
            );
        }
        assert!(
            NAMED_SWEEP_FIXTURES
                .iter()
                .all(|name| swept.contains_key(name))
        );
    }
}

/// The fixtures of the per-commit catalogue sweep (flow F-01): counter.k (EI-D2=b),
/// guardedmem.k (G) and symmem.k, the coupled-capable store-and-load fixture whose
/// release-after-access mutant (K) writes two rules.
const NAMED_SWEEP_FIXTURES: [&str; 3] = ["counter.k", "guardedmem.k", "symmem.k"];

/// The per-commit variant of the heavy sweep: the full catalogue over one named fixture, whose
/// Full manifest must compile some mutant and give each compiled one the baseline's census.
/// (Each schedule's manifest compiles every mutant again; the heavy sweep builds both.)
fn named_catalogue_sweep(name: &'static str) {
    with_stack(move || {
        let count = catalogue_census_for_fixture(name, &catalogue_v1(), &[ScheduleMode::Full]);
        assert!(count > 0, "{name} compiles no catalogue mutant");
        println!("CS09_SWEEP_NAMED_COMPILED {name} {count}");
    });
}

mod kink_tier {
    use super::*;

    #[test]
    #[ignore = "kink"]
    fn mixed_generations_replay_manifest_specs_in_full() {
        mixed_generations(ScheduleMode::Full, true, &[]);
    }

    #[test]
    #[ignore = "kink"]
    fn mixed_generations_equal_single_runs_of_cond_true_in_full() {
        mixed_generations(ScheduleMode::Full, false, &[0]);
    }

    #[test]
    #[ignore = "kink"]
    fn mixed_generations_equal_single_runs_of_cond_false_in_full() {
        mixed_generations(ScheduleMode::Full, false, &[1]);
    }

    #[test]
    #[ignore = "kink"]
    fn mixed_generations_equal_single_runs_of_delete_rule_and_code_in_full() {
        mixed_generations(ScheduleMode::Full, false, &[2, 3]);
    }

    // FirstKill's multi-equals-single comparison, in two parts (review of TG-C); the heavy test
    // adds FirstKill's manifest replay rows.
    #[test]
    #[ignore = "kink"]
    fn mixed_generations_equal_single_runs_of_cond_true_and_cond_false_in_first_kill() {
        mixed_generations(ScheduleMode::FirstKill, false, &[0, 1]);
    }

    #[test]
    #[ignore = "kink"]
    fn mixed_generations_equal_single_runs_of_delete_rule_and_code_in_first_kill() {
        mixed_generations(ScheduleMode::FirstKill, false, &[2, 3]);
    }

    #[test]
    #[ignore = "kink"]
    fn compiled_catalogue_sweep_of_counter_preserves_the_baseline_declaration_census() {
        named_catalogue_sweep(NAMED_SWEEP_FIXTURES[0]);
    }

    #[test]
    #[ignore = "kink"]
    fn compiled_catalogue_sweep_of_guardedmem_preserves_the_baseline_declaration_census() {
        named_catalogue_sweep(NAMED_SWEEP_FIXTURES[1]);
    }

    #[test]
    #[ignore = "kink"]
    fn compiled_catalogue_sweep_of_symmem_preserves_the_baseline_declaration_census() {
        named_catalogue_sweep(NAMED_SWEEP_FIXTURES[2]);
    }

    #[test]
    #[ignore = "kink"]
    fn empty_capped_and_foreign_generations_do_not_claim_global_scores() {
        with_stack(|| {
            let validator =
                NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
            let events = step_support::counter(true);
            let tests = counter_tests(&events);
            let campaign = Campaign {
                validator: &validator,
                module: "COUNTER",
                observation: &events,
                classify: &normal,
                tests: &tests,
                budget: BUDGET,
            };
            let universe = resolve_universe(validator.baseline(), &Universe::v1());
            let delete = catalogue_v1()
                .into_iter()
                .find(|s| s.id() == "delete-rule")
                .unwrap();
            let empty = OperatorSpec::new(
                "empty",
                "1",
                1,
                vec![Clause::Head {
                    label: "absent".into(),
                }],
                Action::DeleteRule,
            )
            .unwrap();
            for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
                let options = CampaignOptions {
                    schedule,
                    selection: SelectionPolicy::None,
                    share_evidence: true,
                    run: kink_campaign::RunOptions::default(),
                    compile_workers: 1,
                };
                for extra in [
                    generate(validator.baseline(), &universe, &empty, usize::MAX).unwrap(),
                    generate(validator.baseline(), &universe, &delete, 1).unwrap(),
                ] {
                    let generations = [code(validator.baseline()).unwrap(), extra];
                    assert!(
                        run_campaign_multi(&campaign, &generations, &options)
                            .unwrap()
                            .score
                            .is_none()
                    );
                }
                let foreign = support::load("counter.k");
                let generation = code(&foreign).unwrap();
                assert_eq!(
                    run_campaign_multi(&campaign, &[generation], &options)
                        .unwrap_err()
                        .kind(),
                    CampaignFailureKind::ForeignGeneration
                );
            }
        });
    }

    #[test]
    #[ignore = "kink"]
    fn flagged_census_records_without_refusing_the_campaign() {
        with_stack(|| {
            let validator =
                NativeValidator::bind(support::load("t13owk.k"), CompileOptions::default());
            let tests = [TestCase {
                id: "start".into(),
                initial_state: support::initial_state(
                    support::app("Lblstart", vec![support::int(1)]),
                    "SortProg",
                ),
                oracles: vec![
                    OracleDeclaration::new(
                        CrashPolicy::CompareIdentity,
                        Projection::State(StateProjection::WholeTerm),
                    )
                    .unwrap(),
                ],
            }];
            let campaign = Campaign {
                validator: &validator,
                module: "T13OWK",
                observation: &[],
                classify: &normal,
                tests: &tests,
                budget: BUDGET,
            };
            let universe = resolve_universe(validator.baseline(), &Universe::v1());
            let spec = catalogue_v1()
                .into_iter()
                .find(|s| s.id() == "drop-owise")
                .unwrap();
            let generations =
                [generate(validator.baseline(), &universe, &spec, usize::MAX).unwrap()];
            for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
                let manifest = campaign_manifest_multi(&MultiManifestInput {
                    campaign: &campaign,
                    generations: &generations,
                    operators: &[ManifestOperator::Spec(&spec)],
                    universe: Some(&universe),
                    schedule,
                    selection: SelectionPolicy::None,
                    classifier: "normal",
                })
                .unwrap();
                assert_eq!(manifest.value()["admission"]["verdict"], "flagged");
                census_baseline(manifest.value());
                // Re-pin R0a (finding E-13): at 927b9ce6 the flagged baseline ran (`addB`, INT.add
                // declared with result Bool, evaluated to Stuck `done(7)`) and the campaign was
                // reported. At 501f18b9 k-rust leaves an ill-sorted hook result unevaluated
                // (UnsupportedHookUnevaluated INT.add), so the baseline leaf is Indeterminate and the
                // baseline oracle refuses the campaign. The census still records without refusing:
                // the refusal is the baseline oracle's, not the census's.
                let refused = run_campaign_multi(
                    &campaign,
                    &generations,
                    &CampaignOptions {
                        schedule,
                        selection: SelectionPolicy::None,
                        share_evidence: true,
                        run: kink_campaign::RunOptions::default(),
                        compile_workers: 1,
                    },
                )
                .expect_err("the baseline oracle refuses the undefined baseline");
                assert_eq!(
                    refused.kind(),
                    CampaignFailureKind::BaselineOracleFailed,
                    "{schedule:?}"
                );
            }
        });
    }

    #[test]
    #[ignore = "kink"]
    fn claim_withdrawn_side_is_recorded_as_baseline_census() {
        with_stack(|| {
            let validator = NativeValidator::bind(
                support::load_path(
                    &Path::new(support::DIR).join("symbolic-claim-mutation.k"),
                    "SYMPARTIAL",
                ),
                CompileOptions::default(),
            );
            let tests = [TestCase {
                id: "symbolic".into(),
                initial_state: support::initial_state(
                    support::app(
                        "Lblseq",
                        vec![
                            support::app("Lblhalf", vec![support::var("X", "SortNat")]),
                            support::app("Lblhalt", vec![]),
                        ],
                    ),
                    "SortProg",
                ),
                oracles: vec![
                    OracleDeclaration::new(
                        CrashPolicy::CompareIdentity,
                        Projection::State(StateProjection::WholeTerm),
                    )
                    .unwrap(),
                ],
            }];
            let campaign = Campaign {
                validator: &validator,
                module: "SYMPARTIAL",
                observation: &[],
                classify: &normal,
                tests: &tests,
                budget: BUDGET,
            };
            let universe = resolve_universe(validator.baseline(), &Universe::v1());
            let spec = OperatorSpec::new(
                "claim",
                "offset",
                1,
                vec![
                    Clause::RuleLabel("SYMPARTIAL.d".into()),
                    Clause::TokenOfSort {
                        sort: k_rust::kast::Sort::new("Int"),
                    },
                ],
                Action::IntOffset(1),
            )
            .unwrap();
            let generation = generate(validator.baseline(), &universe, &spec, usize::MAX).unwrap();
            assert!(!generation.candidates().is_empty());
            let support = ClaimSupport::new(validator.baseline());
            for candidate in generation.candidates() {
                let withdrawal = support
                    .withdraw(validator.baseline(), &candidate.patch)
                    .unwrap();
                assert!(withdrawal.trusted());
                assert!(!withdrawal.withdrawn.is_empty());
                let side = validator.validate(withdrawal.patch().unwrap()).unwrap();
                assert_eq!(
                    declaration_census(&side).unwrap(),
                    declaration_census(&validator.compile_baseline().unwrap()).unwrap()
                );
            }
            for schedule in [ScheduleMode::Full, ScheduleMode::FirstKill] {
                let manifest = campaign_manifest_multi(&MultiManifestInput {
                    campaign: &campaign,
                    generations: std::slice::from_ref(&generation),
                    operators: &[ManifestOperator::Spec(&spec)],
                    universe: Some(&universe),
                    schedule,
                    selection: SelectionPolicy::None,
                    classifier: "normal",
                })
                .unwrap();
                census_baseline(manifest.value());
            }
        });
    }
}
