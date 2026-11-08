//! krs-exec's observations ([`krs_exec::observations`]) over a compiled definition: their
//! resolution, their recording along a run's path, and the comparison of two records. These are
//! library tests of krs-exec; they live here because only krs-cli builds a definition from KRS
//! source.
//!
//! The fixture (`fixtures/observations`) is a free-running machine: each step adds 1 to `n`, and
//! every third step (`emit`) appends `out(n)` to the `out` log. Its observer
//! (`fixtures/observations-observe`) depends on it and holds the views, components, filters and
//! element functions.

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;
use std::sync::OnceLock;

use k_rust::backend::{ExecuteRequest, ExecutionStrategy, InProcess};
use krs_exec::{
    ChannelKind, Closure, CompiledStage, Component, ConfigInputs, ConfigValue, ExecError, Filter,
    LogChannel, ObservationOracle, ObservationSpec, Observations, Observed, Observers, PointClass,
    RunOptions, Semantics, State, StopCriterion, StopRules, Stutter, Value, first_difference,
};
use krs_ir::measure::Timings;
use krs_ir_levels::DefinitionIr;
use krs_test_support::{
    SharedFixtureTarget, TempDir, fixture_build_env, krs_command, shared_fixture_target, temp_dir,
};
use serde_json::json;

const FIXTURE: &str = include_str!("fixtures/observations/src/lib.rs");
const PACKAGE: &str = "krs-observations-fixture";
const OBSERVER: &str = include_str!("fixtures/observations-observe/src/lib.rs");
const OBSERVER_PACKAGE: &str = "krs-observations-observe-fixture";

/// A package manifest of `name` in KRS namespace `namespace`, with `dependencies`.
fn manifest(name: &str, namespace: &str, dependencies: &str) -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    let krs_literal = serde_json::to_string(krs.to_str().unwrap()).unwrap();
    format!(
        "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {krs_literal} }}\n{dependencies}\n[package.metadata.krs]\nk-namespace = \"{namespace}\"\n\n[package.metadata.krs.definitions.main]\n"
    )
}

/// The machine and its observer in one workspace, and the fixture target `krs` builds in.
struct Workspace {
    directory: TempDir,
    target: SharedFixtureTarget,
}

impl Workspace {
    fn new() -> Self {
        let directory = temp_dir();
        let root = directory.path();
        for (member, source, manifest) in [
            (
                "machine",
                FIXTURE,
                manifest(PACKAGE, "ORG-KRS-OBSERVATIONS", ""),
            ),
            (
                "observe",
                OBSERVER,
                manifest(
                    OBSERVER_PACKAGE,
                    "ORG-KRS-OBSERVATIONS-OBSERVE",
                    &format!("machine = {{ package = \"{PACKAGE}\", path = \"../machine\" }}\n"),
                ),
            ),
        ] {
            fs::create_dir_all(root.join(member).join("src")).unwrap();
            fs::write(root.join(member).join("src/lib.rs"), source).unwrap();
            fs::write(root.join(member).join("Cargo.toml"), manifest).unwrap();
        }
        fs::write(
            root.join("Cargo.toml"),
            "[workspace]\nmembers = [\"machine\", \"observe\"]\nresolver = \"3\"\n",
        )
        .unwrap();
        Self {
            directory,
            target: shared_fixture_target(),
        }
    }

    fn path(&self, name: &str) -> std::path::PathBuf {
        self.directory.path().join(name)
    }
}

/// The machine's and the observer's Definition IR and compiled stages, built once.
fn compiled() -> &'static [(DefinitionIr, CompiledStage); 2] {
    static COMPILED: OnceLock<[(DefinitionIr, CompiledStage); 2]> = OnceLock::new();
    COMPILED.get_or_init(|| {
        let workspace = Workspace::new();
        let emit = |member: &str, package: &str, extra: &[&str]| {
            let emitted = workspace.path(&format!("emitted-{package}"));
            let mut process = krs_command!();
            fixture_build_env(&mut process, workspace.target.path());
            let output = process
                .current_dir(workspace.path(member))
                .args([
                    "emit-k",
                    "--ir",
                    "--package",
                    package,
                    "--definition",
                    "main",
                ])
                .args(extra)
                .arg("--output")
                .arg(&emitted)
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            let definition: DefinitionIr =
                serde_json::from_slice(&fs::read(emitted.join("definition-ir.json")).unwrap())
                    .unwrap();
            let stage = CompiledStage::compile(&definition, &mut Timings::disabled()).unwrap();
            (definition, stage)
        };
        [
            emit("machine", PACKAGE, &[]),
            emit(
                "observe",
                OBSERVER_PACKAGE,
                &["--dependency", &format!("{PACKAGE}:main")],
            ),
        ]
    })
}

fn semantics((definition, stage): &(DefinitionIr, CompiledStage)) -> Semantics {
    Semantics::from_stage(definition, stage.clone(), None, &mut Timings::disabled()).unwrap()
}

/// The machine, a second copy of it (an observer of its own definition) and the observer
/// package's definition, given to `test` on a thread with the stack the run commands give their
/// worker.
fn with_definitions(test: impl FnOnce(&mut Semantics, &mut Semantics, &mut Semantics) + Send) {
    let [machine, observer] = compiled();
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(256 << 20)
            .spawn_scoped(scope, || {
                let mut subject = semantics(machine);
                let mut twin = semantics(machine);
                let mut observer = semantics(observer);
                test(&mut subject, &mut twin, &mut observer);
            })
            .unwrap()
            .join()
            .unwrap();
    });
}

/// The machine's start from `n = start`, its `hole` holding `0`.
fn start(semantics: &mut Semantics, start: i64) -> State {
    configured(semantics, start, "0".into())
}

fn configured(semantics: &mut Semantics, start: i64, hole: ConfigValue) -> State {
    let text = start.to_string();
    semantics
        .configure(&ConfigInputs {
            variables: vec![
                ("start".to_owned(), text.as_str().into()),
                ("hole".to_owned(), hole),
            ],
            ..ConfigInputs::default()
        })
        .unwrap()
}

/// A class of `stutter` at the before side of both rules, reading `cells`.
fn class(name: &str, stutter: Stutter, cells: &[&str]) -> PointClass {
    PointClass {
        name: name.to_owned(),
        before: vec!["tick".to_owned(), "emit".to_owned()],
        after: Vec::new(),
        stutter,
        cells: cells.iter().map(|cell| (*cell).to_owned()).collect(),
        views: BTreeMap::default(),
        components: Vec::new(),
        when: None,
    }
}

fn points(points: Vec<PointClass>) -> ObservationSpec {
    ObservationSpec {
        points,
        ..ObservationSpec::default()
    }
}

/// A run of `depth` steps from `state` under `spec`, its functions evaluated in `observer`,
/// each evaluation within `budget` polls.
fn observe(
    subject: &mut Semantics,
    observer: Option<&mut Semantics>,
    state: &State,
    spec: ObservationSpec,
    depth: u64,
    budget: Option<u64>,
) -> Result<Observations, ExecError> {
    let report = subject.run_with(
        state,
        RunOptions {
            depth: Some(depth),
            observe: Some(spec),
            condition_budget: budget,
            ..RunOptions::default()
        },
        Observers {
            condition: None,
            observations: observer,
        },
    )?;
    Ok(report
        .observations
        .expect("a run with observations reports them"))
}

/// The values of a channel's elements.
fn values(observations: &Observations, channel: usize) -> Vec<serde_json::Value> {
    observations.channels[channel]
        .elements
        .iter()
        .map(|element| element.value.clone().unwrap())
        .collect()
}

/// Under `collapse` the bookkeeping `phase`, which no rule rewrites, is one element however many
/// points there are; under `count` it is one element per point. Both channels are open at the
/// depth bound, which is no end of the path.
#[test]
fn collapse_drops_equal_consecutive_contents_and_count_keeps_them() {
    with_definitions(|subject, _, _| {
        let state = start(subject, 0);
        let spec = points(vec![
            class("collapsed", Stutter::Collapse, &["phase"]),
            class("counted", Stutter::Count, &["phase"]),
            class("n", Stutter::Collapse, &["n"]),
        ]);
        let observations = observe(subject, None, &state, spec, 9, None).unwrap();
        assert_eq!(values(&observations, 0), [json!({"phase": 7})]);
        assert_eq!(observations.channels[1].elements.len(), 9);
        assert_eq!(
            values(&observations, 2),
            (0..9).map(|n| json!({"n": n})).collect::<Vec<_>>()
        );
        // The before points of the first nine steps, at depths 0 to 8, each named by its rule.
        let counted = &observations.channels[1].elements;
        assert_eq!(
            counted
                .iter()
                .map(|element| element.depth)
                .collect::<Vec<_>>(),
            (0..9).collect::<Vec<_>>()
        );
        assert_eq!(counted[2].rule.as_deref(), Some("crate::emit"));
        for channel in &observations.channels {
            assert_eq!(channel.closed, None);
            let open = channel.open.as_ref().unwrap();
            assert_eq!(open.index, channel.elements.len() as u64);
            assert!(open.reason.contains("depth-bound"), "{}", open.reason);
        }
    });
}

/// A filter emits only the points where it is decided true; a view replaces a cell's component
/// and a component reads several cells, each evaluated in the observer.
#[test]
fn a_filter_emits_only_where_it_holds() {
    with_definitions(|subject, _, observer| {
        let state = start(subject, 0);
        let mut filtered = class("even", Stutter::Count, &["n"]);
        filtered.views.insert("n".to_owned(), "Twice".to_owned());
        filtered.components.push(Component {
            name: "gap".to_owned(),
            cells: vec!["n".to_owned(), "phase".to_owned()],
            function: "Gap".to_owned(),
        });
        filtered.when = Some(Filter {
            function: "Even".to_owned(),
            cells: vec!["n".to_owned()],
        });
        let observations = observe(
            subject,
            Some(observer),
            &state,
            points(vec![filtered]),
            6,
            None,
        )
        .unwrap();
        assert_eq!(
            values(&observations, 0),
            [
                json!({"n": 0, "gap": -7}),
                json!({"n": 4, "gap": -5}),
                json!({"n": 8, "gap": -3}),
            ]
        );
    });
}

/// A log reads the items appended since its last read, through its element function, and at the
/// path's end; a cell that does not only grow by appending is refused.
#[test]
fn a_log_reads_appended_items_and_refuses_a_rewritten_one() {
    with_definitions(|subject, _, observer| {
        let state = start(subject, 0);
        let log = |name: &str, cell: &str, element: Option<&str>, at: &[&str]| LogChannel {
            name: name.to_owned(),
            cell: cell.to_owned(),
            element: element.map(str::to_owned),
            at: at.iter().map(|at| (*at).to_owned()).collect(),
        };
        let spec = ObservationSpec {
            points: vec![class("steps", Stutter::Count, &[])],
            logs: vec![
                log("out", "out", None, &["steps"]),
                log("twins", "out", Some("Twin"), &[]),
            ],
            observer: None,
        };
        let observations = observe(subject, Some(observer), &state, spec, 9, None).unwrap();
        let out = |n: i64| json!({"Out": {"n": n}});
        assert_eq!(observations.channels[1].kind, ChannelKind::Log);
        assert_eq!(values(&observations, 1), [out(2), out(5), out(8)]);
        // Read at the step after `emit` appended `out(2)`, the before point at depth 3; the last
        // item is appended by the ninth step and read at the path's end.
        let elements = &observations.channels[1].elements;
        assert_eq!(
            (elements[0].depth, elements[0].rule.as_deref()),
            (3, Some("crate::tick"))
        );
        assert_eq!((elements[2].depth, elements[2].rule.as_deref()), (9, None));
        assert_eq!(
            values(&observations, 2),
            [out(2), out(2), out(5), out(5), out(8), out(8)]
        );
        let ring = ObservationSpec {
            points: vec![class("steps", Stutter::Count, &[])],
            logs: vec![log("ring", "ring", None, &["steps"])],
            observer: None,
        };
        let error = observe(subject, None, &state, ring, 9, None).unwrap_err();
        let ExecError::Observation {
            channel,
            reason,
            steps,
            ..
        } = &error
        else {
            panic!("expected an observation refusal: {error}");
        };
        assert_eq!((channel.as_str(), *steps), ("ring", 6), "{error}");
        assert!(reason.starts_with("log-not-appended"), "{reason}");
    });
}

/// An element with no value refuses the run, naming the point, its rule, the steps and the cell
/// or the function; a read cell that holds no data has no value.
#[test]
fn no_value_refuses_naming_the_point_rule_depth_and_cell() {
    with_definitions(|subject, _, observer| {
        let state = start(subject, 0);
        let mut small = class("small", Stutter::Count, &[]);
        small.components.push(Component {
            name: "small".to_owned(),
            cells: vec!["n".to_owned()],
            function: "Small".to_owned(),
        });
        let error = observe(
            subject,
            Some(observer),
            &state,
            points(vec![small]),
            9,
            None,
        )
        .unwrap_err();
        let text = error.to_string();
        assert!(
            text.starts_with(
                "the observation `small` has no value at the before point of `crate::tick` after 3 steps: the component `small`"
            ),
            "{text}"
        );
        let hole = subject
            .values()
            .call("Natural", [("n", Value::Int((-1).into()))])
            .unwrap();
        let state = configured(subject, 0, ConfigValue::Value(hole));
        let error = observe(
            subject,
            None,
            &state,
            points(vec![class("hole", Stutter::Count, &["hole"])]),
            9,
            None,
        )
        .unwrap_err();
        let text = error.to_string();
        assert!(
            text.starts_with(
                "the observation `hole` has no value at the before point of `crate::tick` after 0 steps: the component `hole`: the cell `hole` holds"
            ),
            "{text}"
        );
    });
}

/// An evaluation that spends its budget leaves its element undecided: under `count` that element
/// is unknown and the later ones are kept, under `collapse` the channel opens there; either way
/// the record does not answer what the observation is.
#[test]
fn undecided_is_inconclusive() {
    with_definitions(|subject, _, observer| {
        let state = start(subject, 0);
        let climbing = |name: &str, stutter: Stutter| {
            let mut class = class(name, stutter, &[]);
            class.components.push(Component {
                name: "climb".to_owned(),
                cells: vec!["n".to_owned()],
                function: "Climb".to_owned(),
            });
            class
        };
        let observations = observe(
            subject,
            Some(observer),
            &state,
            points(vec![
                climbing("counted", Stutter::Count),
                climbing("collapsed", Stutter::Collapse),
            ]),
            3,
            Some(50),
        )
        .unwrap();
        assert!(observations.undecided());
        let counted = &observations.channels[0];
        assert_eq!(counted.elements.len(), 3);
        assert!(
            counted
                .elements
                .iter()
                .all(|element| element.undecided.is_some())
        );
        let collapsed = &observations.channels[1];
        let open = collapsed.open.as_ref().unwrap();
        assert_eq!(
            (collapsed.elements.len(), open.index, open.undecided),
            (0, 0, true)
        );
    });
}

/// Every declaration that cannot be recorded is refused before the run, naming the channel and
/// the cause.
#[test]
fn each_resolution_refusal_names_its_cause() {
    with_definitions(|subject, _, observer| {
        let refused = |spec: ObservationSpec, expected: &str| {
            let error = subject.observations(observer, &spec).unwrap_err();
            assert!(matches!(error, ExecError::Observe(_)), "{error:?}");
            let text = error.to_string();
            assert!(text.contains(expected), "{expected:?} not in {text:?}");
        };
        let with = |edit: &dyn Fn(&mut PointClass)| {
            let mut class = class("c", Stutter::Count, &["n"]);
            edit(&mut class);
            points(vec![class])
        };
        refused(
            with(&|class| class.before = vec!["nope".to_owned()]),
            "the point class `c`:",
        );
        refused(
            with(&|class| class.before = vec!["crate::Natural".to_owned()]),
            "the point class `c`:",
        );
        refused(
            with(&|class| {
                class.before.clear();
            }),
            "names no rule",
        );
        refused(with(&|class| class.cells = vec!["nope".to_owned()]), "nope");
        refused(
            with(&|class| class.cells = vec!["hidden".to_owned()]),
            "hidden",
        );
        refused(
            with(&|class| class.cells = vec!["cpu".to_owned()]),
            "is a group cell; an observation reads leaf cells",
        );
        refused(
            with(&|class| class.cells = vec!["timer".to_owned()]),
            "is or is below the optional cell `timer`",
        );
        refused(
            with(&|class| class.cells = vec!["n".to_owned(), "n".to_owned()]),
            "reads the cell `n` twice",
        );
        refused(
            with(&|class| {
                class.views.insert("n".to_owned(), "Gap".to_owned());
            }),
            "takes 2 parameters, but the view reads 1 cell",
        );
        refused(
            with(&|class| {
                class.views.insert("n".to_owned(), "Flag".to_owned());
            }),
            "does not admit the sort Int of the cell `n`",
        );
        refused(
            with(&|class| {
                class.views.insert("phase".to_owned(), "Twice".to_owned());
            }),
            "has a view of the cell `phase`, which it does not read",
        );
        refused(
            with(&|class| {
                class.when = Some(Filter {
                    function: "Twice".to_owned(),
                    cells: vec!["n".to_owned()],
                });
            }),
            "does not return Bool; a filter holds or does not at a state",
        );
        refused(
            with(&|class| {
                class.components.push(Component {
                    name: "n".to_owned(),
                    cells: vec!["n".to_owned()],
                    function: "Twice".to_owned(),
                });
            }),
            "has two components named `n`",
        );
        refused(
            points(vec![
                class("c", Stutter::Count, &[]),
                class("c", Stutter::Count, &[]),
            ]),
            "the observation channel `c` is declared twice",
        );
    });
}

/// Every log declaration that cannot be recorded is refused before the run, naming the log and
/// the cause.
#[test]
fn each_log_resolution_refusal_names_its_cause() {
    with_definitions(|subject, _, observer| {
        let refused = |spec: ObservationSpec, expected: &str| {
            let error = subject.observations(observer, &spec).unwrap_err();
            let text = error.to_string();
            assert!(text.starts_with("the log `l`: "), "{text}");
            assert!(text.contains(expected), "{expected:?} not in {text:?}");
        };
        let log = |cell: &str, element: Option<&str>, at: &[&str]| ObservationSpec {
            points: vec![class("c", Stutter::Count, &[])],
            logs: vec![LogChannel {
                name: "l".to_owned(),
                cell: cell.to_owned(),
                element: element.map(str::to_owned),
                at: at.iter().map(|at| (*at).to_owned()).collect(),
            }],
            observer: None,
        };
        refused(log("n", None, &[]), "is of sort Int, not a List");
        refused(log("out", Some("Number"), &[]), "does not return a List");
        refused(
            log("out", Some("Twice"), &[]),
            "does not admit the log's items",
        );
        refused(log("out", None, &["nope"]), "is read at `nope`");
    });
}

/// The functions are resolved and evaluated in the observer package: the machine's own
/// definition does not declare `Twice`, and a run evaluates it in the observer it is given, and
/// in no other.
#[test]
fn evaluated_in_the_observer_package() {
    with_definitions(|subject, twin, observer| {
        let mut viewed = class("n", Stutter::Count, &["n"]);
        viewed.views.insert("n".to_owned(), "Twice".to_owned());
        let spec = points(vec![viewed]);
        assert!(subject.observations(subject, &spec).is_err());
        assert!(subject.observations(observer, &spec).is_ok());
        let state = start(subject, 1);
        let observations = observe(subject, Some(observer), &state, spec.clone(), 2, None).unwrap();
        assert_eq!(values(&observations, 0), [json!({"n": 2}), json!({"n": 4})]);
        // In another observer, a copy of the machine's definition, `Twice` names no function.
        let error = observe(subject, Some(twin), &state, spec, 2, None).unwrap_err();
        assert!(matches!(error, ExecError::Observe(_)), "{error}");
        // A function of the machine's own definition resolves in it, and is still evaluated in
        // an observer, never in the definition being run: with none, the run is refused.
        let mut own = class("n", Stutter::Count, &["n"]);
        own.views.insert("n".to_owned(), "Natural".to_owned());
        let error = observe(subject, None, &state, points(vec![own]), 2, None).unwrap_err();
        assert!(error.to_string().contains("none was given"), "{error}");
    });
}

/// The first difference of two recorded runs is the first channel element both decided and
/// unequal, with the path inside the values; an end against an element is a difference, and a
/// bound never is.
#[test]
fn first_difference_of_two_recorded_runs() {
    with_definitions(|subject, _, _| {
        let spec = || {
            points(vec![
                class("n", Stutter::Count, &["n"]),
                class("phase", Stutter::Collapse, &["phase"]),
            ])
        };
        let from_zero = start(subject, 0);
        let from_one = start(subject, 1);
        let zero = observe(subject, None, &from_zero, spec(), 4, None).unwrap();
        let again = observe(subject, None, &from_zero, spec(), 4, None).unwrap();
        let one = observe(subject, None, &from_one, spec(), 4, None).unwrap();
        assert_eq!(first_difference(&zero, &again), None);
        let difference = first_difference(&zero, &one).unwrap();
        assert_eq!((difference.channel.as_str(), difference.index), ("n", 0));
        assert_eq!(difference.path.as_deref(), Some("n"));
        // A longer run agrees with a shorter one on its prefix: the bound ends what is known.
        let longer = observe(subject, None, &from_zero, spec(), 8, None).unwrap();
        assert_eq!(first_difference(&zero, &longer), None);
        // A run that ends at a stop closes its channels: against a run that goes on, its end
        // differs from the other run's next element.
        let stopped = subject
            .run_with(
                &from_zero,
                RunOptions {
                    stop: StopCriterion::Rules {
                        rules: StopRules {
                            before: vec!["emit".to_owned()],
                            ..StopRules::default()
                        },
                        count: std::num::NonZeroU64::MIN,
                        when: None,
                    },
                    observe: Some(spec()),
                    ..RunOptions::default()
                },
                Observers::default(),
            )
            .unwrap()
            .observations
            .unwrap();
        assert_eq!(stopped.channels[0].closed, Some(Closure::End));
        assert_eq!(stopped.channels[0].elements.len(), 2);
        let difference = first_difference(&stopped, &longer).unwrap();
        assert_eq!((difference.channel.as_str(), difference.index), ("n", 2));
        assert_eq!(difference.left, Observed::End);
    });
}

/// A cell the backend did not rewrite keeps its term node, so the record converts it once
/// however many points read it.
#[test]
fn a_cell_whose_handle_is_reused_converts_once() {
    with_definitions(|subject, _, _| {
        let state = start(subject, 0);
        let observations = observe(
            subject,
            None,
            &state,
            points(vec![class("phase", Stutter::Count, &["phase"])]),
            20,
            None,
        )
        .unwrap();
        assert_eq!(observations.channels[0].elements.len(), 20);
        assert_eq!(observations.conversions, 1);
    });
}

/// A comparing oracle ends the request at the first element that differs from a recorded
/// baseline's (`probe-difference`), and a run that agrees at the baseline's horizon, where the
/// baseline did not end, ends there (`probe-done`).
#[test]
fn a_comparison_stops_at_the_difference_or_the_horizon() {
    with_definitions(|subject, _, _| {
        let spec = points(vec![class("n", Stutter::Count, &["n"])]);
        let from_zero = start(subject, 0);
        let from_one = start(subject, 1);
        let baseline = observe(subject, None, &from_zero, spec.clone(), 4, None).unwrap();
        let resolved = subject.observations(subject, &spec).unwrap();
        let mut run = |state: &State| {
            let mut oracle = ObservationOracle::compare(&resolved, None, &baseline, None).unwrap();
            let mut request = ExecuteRequest::new(state.kore().clone());
            request.max_depth = Some(50);
            request.strategy = ExecutionStrategy::Any;
            let rules = oracle.probe_rules();
            let result = subject
                .backend_mut()
                .execute_kore_with_probe(
                    request,
                    rules,
                    InProcess {
                        probe: Some(&mut oracle),
                        ..InProcess::default()
                    },
                )
                .unwrap();
            let difference = oracle.difference().map(str::to_owned);
            let [leaf] = result.leaves.as_slice() else {
                panic!("one leaf");
            };
            (leaf.reason, leaf.depth, difference)
        };
        let (reason, depth, difference) = run(&from_zero);
        assert_eq!(
            (reason, depth, difference),
            (k_rust::backend::HaltReasonOutput::ProbeDone, 4, None)
        );
        let (reason, depth, difference) = run(&from_one);
        assert_eq!(
            (reason, depth),
            (k_rust::backend::HaltReasonOutput::ProbeDifference, 0)
        );
        assert!(difference.unwrap().contains("element 0"));
    });
}
