//! `krs-exec` configures a state whose bus log holds a million entries on an 8 MiB thread, a main
//! thread's default on Linux, and reads back there the end of a run from a state whose log holds
//! 200,000.
//! The run itself is made on a larger stack, and the test that also runs on 8 MiB is ignored:
//! the run holds the backend's results as `serde_json::Value`, which serializing and dropping walk
//! one stack frame per level, and the backend sizes the stack of one operation from the depth of
//! its request, which it refuses beyond about 700,000 levels in the `dev` profile.
//!
//! The fixture has the shape of a machine that logs its bus: a builtin `List` cell to which every
//! step appends one cycle, as Foldiboy's SM83 logs one entry per machine cycle.
//! A list is a chain one level per element in the KORE and KAST terms that carry it, so each walk
//! of a state, a result or a reading of its condition takes stack in proportion to the log's
//! length unless it keeps its work on a stack of its own; at about 2 KiB per level, a recursive
//! walk overflows 8 MiB at about 4,000 entries.
//! Here the log is given as a value, so that the run takes three steps however long the log is.
//!
//! A failure here is a stack overflow, which aborts the process; these tests live in their own
//! binary so that the abort takes down only this file's tests.

use std::fs;
use std::path::Path;
use std::sync::OnceLock;

use krs_exec::{
    CompiledStage, ConfigInputs, ConfigValue, Halt, RunOptions, Semantics, Value, View,
};
use krs_ir::measure::Timings;
use krs_ir_levels::DefinitionIr;
use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const FIXTURE: &str = r##"
use k::builtin::{Int, KSequence, List};
use k::KItem;

k::sorts! {
    BusCycle;
    Op: KItem;
}

/// One machine cycle as seen on the bus.
#[k::constructors(sort = BusCycle, result = k::KResult)]
pub enum Cycle {
    #[k::syntax("read({addr}, {value})")]
    Read { addr: Int, value: Int },
    #[k::syntax("write({addr}, {old}, {new})")]
    Write { addr: Int, old: Int, new: Int },
    #[k::syntax("internal")]
    Internal,
}

#[k::constructors(sort = Op, result = k::KResult)]
pub enum Step {
    /// One machine cycle: a read at `pc`, logged on the bus.
    #[k::syntax("#tick")]
    Tick,
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub pc: Int,
    /// Bus activity, one entry per machine cycle.
    #[k::cell]
    pub bus: List<BusCycle>,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PC")] pc: Int,
        #[k::config_var(name = "BUS")] bus: List<BusCycle>,
    ) -> Self {
        Self {
            k: k::k![Step::Tick],
            pc,
            bus,
        }
    }
}

k::rules! {
    for Machine;

    #[k::requires(pc < 3)]
    tick: {
        k: [Step::Tick, ..],
        pc,
        bus: log,
    } => {
        k: [Step::Tick, ..],
        pc: pc + 1,
        bus: [..log, Cycle::Read { addr: pc, value: 0 }],
    };
}
"##;
const PACKAGE: &str = "krs-exec-deep-log-fixture";

/// The bus log's length, `default` unless `KRS_DEEP_LOG_ENTRIES` sets another, to locate a
/// failure.
fn entries(default: usize) -> usize {
    std::env::var("KRS_DEEP_LOG_ENTRIES")
        .ok()
        .map_or(default, |entries| entries.parse().unwrap())
}

/// The fixture's Definition IR and compiled stage, built once per test process.
fn compiled() -> &'static (DefinitionIr, CompiledStage) {
    static COMPILED: OnceLock<(DefinitionIr, CompiledStage)> = OnceLock::new();
    COMPILED.get_or_init(|| {
        let target = shared_fixture_target();
        let temporary = temp_dir();
        let project = temporary.path().join("language");
        fs::create_dir_all(project.join("src")).unwrap();
        fs::write(project.join("src/lib.rs"), FIXTURE).unwrap();
        let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../krs")
            .canonicalize()
            .unwrap();
        let krs_literal = serde_json::to_string(krs.to_str().unwrap()).unwrap();
        fs::write(
            project.join("Cargo.toml"),
            format!(
                "[package]\nname = \"{PACKAGE}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {krs_literal} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-EXEC-DEEP-LOG\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\n"
            ),
        )
        .unwrap();
        let emitted = temporary.path().join("emitted");
        let mut process = krs_command!();
        fixture_build_env(&mut process, target.path());
        let output = process
            .current_dir(&project)
            .args(["emit-k", "--ir", "--manifest-path"])
            .arg(project.join("Cargo.toml"))
            .args(["--package", PACKAGE, "--definition", "main", "--output"])
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
    })
}

/// The `index`th entry of the given log: reads, writes and internal cycles in turn.
fn cycle(semantics: &Semantics, index: usize) -> Value {
    let values = semantics.values();
    let addr = i64::try_from(index % 65_536).unwrap();
    match index % 3 {
        0 => values
            .ctor("Cycle::Read", [("addr", addr.into()), ("value", 1.into())])
            .unwrap(),
        1 => values
            .ctor(
                "Cycle::Write",
                [("addr", addr.into()), ("old", 1.into()), ("new", 2.into())],
            )
            .unwrap(),
        _ => values.ctor("Cycle::Internal", []).unwrap(),
    }
}

/// The semantics of the fixture's compiled definition.
fn semantics_of((definition, stage): &(DefinitionIr, CompiledStage)) -> Semantics {
    Semantics::from_stage(definition, stage.clone(), None, &mut Timings::disabled()).unwrap()
}

/// The fixture's semantics, on a thread of 8 MiB, a main thread's default on Linux, given to
/// `test` with a log of `entries` entries.
fn on_an_8_mib_thread(
    entries: usize,
    test: impl FnOnce(&mut Semantics, Value, usize) + Send + 'static,
) {
    // Built on a large stack: building the fixture is not what is tested.
    let compiled = std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(compiled)
        .unwrap()
        .join()
        .unwrap();
    std::thread::Builder::new()
        .stack_size(8 << 20)
        .spawn(move || {
            let mut semantics = semantics_of(compiled);
            let log = Value::list((0..entries).map(|index| cycle(&semantics, index)));
            test(&mut semantics, log, entries);
        })
        .unwrap()
        .join()
        .unwrap();
}

/// The initial state with `log` on the bus and the program counter at 0.
fn configure(semantics: &mut Semantics, log: Value) -> krs_exec::State {
    semantics
        .configure(&ConfigInputs {
            variables: vec![
                ("PC".to_owned(), ConfigValue::Value(0.into())),
                ("BUS".to_owned(), ConfigValue::Value(log)),
            ],
            ..ConfigInputs::default()
        })
        .unwrap()
}

/// Configuring converts the log to KAST and to KORE and checks its entries against the cell's
/// declared element sort.
#[test]
fn a_million_entry_log_configures_on_an_8_mib_thread() {
    on_an_8_mib_thread(entries(1_000_000), |semantics, log, _| {
        let state = configure(semantics, log);
        let k_rust::kore::ast::Pattern::Application { symbol, .. } = state.kore() else {
            panic!("an initial state applies initGeneratedTopCell");
        };
        assert_eq!(symbol.name, "LblinitGeneratedTopCell");
    });
}

/// The end of a run from a state whose log holds 200,000 entries reads back on an 8 MiB thread:
/// its conversion to KAST and the view of its cells read the log there.
///
/// That is fifty times the length at which a walk taking 2 KiB per level overflows 8 MiB, and
/// leaves 42 bytes of the thread's stack per level, about what a call's return address and saved
/// registers take, so a walk that recursed per level would overflow here; the run that makes the
/// end takes about 40 s and 4 GiB of memory at that length.
/// The run is made by a semantics of its own on a thread with a stack of 4 GiB, of which it touches
/// what it uses, because the run is not bounded on 8 MiB
/// ([`a_million_entry_log_runs_and_reads_back_on_an_8_mib_thread`]).
#[test]
fn the_end_of_a_run_from_a_long_log_reads_back_on_an_8_mib_thread() {
    on_an_8_mib_thread(entries(200_000), |semantics, log, entries| {
        let state = configure(semantics, log);
        let report = std::thread::scope(|scope| {
            std::thread::Builder::new()
                .stack_size(4 << 30)
                .spawn_scoped(scope, || {
                    semantics_of(compiled())
                        .run(&state, RunOptions::default())
                        .unwrap()
                })
                .unwrap()
                .join()
                .unwrap()
        });
        drop(state);
        assert_eq!(report.halt, Halt::Stuck);
        assert_eq!(report.steps, 3);
        assert!(report.valueless.is_empty());
        let end = semantics.term(report.state.kore().clone()).unwrap();
        drop(report);
        assert_read_back(semantics, &end, entries);
    });
}

/// The view of `end`, the end of a run from the state with a log of `entries` entries: the
/// program counter at 3 and the log with the three cycles the run logged after its entries.
fn assert_read_back(semantics: &Semantics, end: &krs_exec::Term, entries: usize) {
    let View::State(view) = semantics.view(end).unwrap() else {
        panic!("the run's end is defined");
    };
    assert_eq!(view.value("pc").unwrap(), 3.into());
    let bus = view.value("bus").unwrap();
    let bus = bus.as_list().unwrap();
    assert_eq!(bus.len(), entries + 3);
    for index in [0, 1, 2, entries - 1] {
        assert_eq!(bus[index], cycle(semantics, index), "entry {index}");
    }
    let values = semantics.values();
    for (offset, pc) in (0_i64..3).enumerate() {
        assert_eq!(
            bus[entries + offset],
            values
                .ctor("Cycle::Read", [("addr", pc.into()), ("value", 0.into())])
                .unwrap(),
            "the cycle logged at pc {pc}"
        );
    }
}

/// A run from a state whose log holds a million entries, and the view of its end, on an 8 MiB
/// thread: the run reads the log in the backend's result and in the reading of its condition, and
/// converts its end to KAST.
///
/// It is ignored for two reasons.
/// The run holds the backend's results as `serde_json::Value`, which serializing and dropping walk
/// one stack frame per level: at 200,000 entries the run overflows 8 MiB while encoding the end as
/// text to decode it.
/// And the backend sizes the stack of one operation from its request's depth, 6 KiB per level in
/// the `dev` profile under a 4 GiB segment: it refuses a request a million levels deep as too deep
/// for it, on any thread.
#[test]
#[ignore = "the run is not bounded on 8 MiB (it holds the backend's results as `serde_json::Value`), and the backend refuses a request a million levels deep in the `dev` profile"]
fn a_million_entry_log_runs_and_reads_back_on_an_8_mib_thread() {
    on_an_8_mib_thread(entries(1_000_000), |semantics, log, entries| {
        let state = configure(semantics, log);
        let report = semantics.run(&state, RunOptions::default()).unwrap();
        assert_eq!(report.halt, Halt::Stuck);
        assert_eq!(report.steps, 3);
        assert!(report.valueless.is_empty());
        assert_read_back(semantics, &report.state, entries);
    });
}
