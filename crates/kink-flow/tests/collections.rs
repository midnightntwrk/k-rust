//! CS-16 R1-R26: collection mutations through flow resolution and the campaign runner.

use std::path::{Path, PathBuf};

use kink_campaign::{
    Campaign, CampaignFailureKind, MutantStatus, OracleOutcome, ScheduleMode, TestRun, run_campaign,
};
use kink_corpus::runner::all_normal;
use kink_flow::{
    admit::admit,
    manifest::FlowManifest,
    mutation::{MutationList, resolve},
    results::{execution_budget, fixed_oracles},
};

#[derive(Clone, Copy)]
struct Row {
    id: &'static str,
    mutation: &'static str,
    program: &'static str,
    status: Option<MutantStatus>,
    slots: [OracleOutcome; 2],
}

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../testdata/flow")
        .join(name)
}

fn check(name: &'static str, rows: &'static [Row]) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(move || campaigns(name, rows))
        .unwrap()
        .join()
        .unwrap_or_else(|panic| std::panic::resume_unwind(panic));
}

fn campaigns(name: &str, rows: &[Row]) {
    let manifest = FlowManifest::read(&fixture(name).join("FLOW.toml")).unwrap();
    let mutations = MutationList::read(&fixture(name).join("MUTATIONS.toml")).unwrap();
    let admission = admit(&manifest);
    let spec = admission.spec.as_ref().expect("spec admitted");
    let module = k_rust::kast::identifier::encode(&manifest.spec.main_module);
    for row in rows {
        let mutation = mutations
            .mutations
            .iter()
            .find(|m| m.id == row.mutation)
            .unwrap();
        let generation = resolve(&manifest, &spec.loaded, mutation)
            .unwrap()
            .generation(spec.validator.baseline())
            .unwrap();
        let mut test = admission
            .programs
            .iter()
            .find(|p| p.id == row.program)
            .unwrap()
            .outcome
            .clone()
            .expect("program admitted");
        test.oracles = fixed_oracles();
        let tests = [test];
        let campaign = Campaign {
            validator: &spec.validator,
            module: &module,
            observation: &[],
            classify: &all_normal,
            tests: &tests,
            budget: execution_budget(manifest.budget),
        };
        for mode in [ScheduleMode::Full, ScheduleMode::FirstKill] {
            let result = run_campaign(&campaign, &generation, mode);
            let Some(status) = row.status else {
                assert_eq!(
                    result.unwrap_err().kind(),
                    CampaignFailureKind::BaselineOracleFailed,
                    "{} {mode:?}",
                    row.id
                );
                continue;
            };
            let run = result.unwrap_or_else(|failure| panic!("{} {mode:?}: {failure:?}", row.id));
            let [mutant] = run.mutants.as_slice() else {
                panic!("one mutant")
            };
            assert_eq!(mutant.report.status, status, "{} {mode:?}", row.id);
            let [test] = mutant.plan.tests.as_slice() else {
                panic!("one test")
            };
            assert_eq!(
                test.run,
                TestRun::Compared(row.slots.to_vec()),
                "{} {mode:?}",
                row.id
            );
            if status == MutantStatus::Killed {
                assert_eq!(
                    mutant.report.killing_test_ids,
                    [row.program],
                    "{} {mode:?}",
                    row.id
                );
            } else {
                assert!(
                    mutant.report.killing_test_ids.is_empty(),
                    "{} {mode:?}",
                    row.id
                );
            }
        }
    }
}

use MutantStatus::{Killed, Survived, Unknown};
use OracleOutcome::{Agree, Distinguish, Unknown as Undecided};

#[test]
fn map_store_r1_r4() {
    check(
        "map-store",
        &[
            Row {
                id: "R1",
                mutation: "value-plus-one",
                program: "store",
                status: Some(Killed),
                slots: [Agree, Distinguish],
            },
            Row {
                id: "R2",
                mutation: "key-value-swap",
                program: "store",
                status: Some(Killed),
                slots: [Agree, Distinguish],
            },
            Row {
                id: "R3",
                mutation: "update-as-concat",
                program: "store",
                status: Some(Survived),
                slots: [Agree, Agree],
            },
            Row {
                id: "R4",
                mutation: "update-dropped",
                program: "store",
                status: Some(Killed),
                slots: [Agree, Distinguish],
            },
        ],
    );
}

#[test]
fn map_set_list_and_residue_r5_r15() {
    check(
        "collections/collstore",
        &[
            Row {
                id: "R5",
                mutation: "putTwo-order",
                program: "two",
                status: Some(Survived),
                slots: [Agree, Agree],
            },
            Row {
                id: "R6",
                mutation: "putTwo-values-swapped",
                program: "two",
                status: Some(Killed),
                slots: [Agree, Distinguish],
            },
            Row {
                id: "R7",
                mutation: "union-as-concat",
                program: "set11",
                status: Some(Killed),
                slots: [Distinguish, Distinguish],
            },
            Row {
                id: "R8",
                mutation: "union-as-concat",
                program: "set12",
                status: Some(Survived),
                slots: [Agree, Agree],
            },
            Row {
                id: "R9",
                mutation: "append-as-prepend",
                program: "list12",
                status: Some(Killed),
                slots: [Agree, Distinguish],
            },
            Row {
                id: "R10",
                mutation: "f0-deleted",
                program: "fkey0",
                status: Some(Unknown),
                slots: [Undecided, Undecided],
            },
            Row {
                id: "R11",
                mutation: "f0-value",
                program: "fkey0",
                status: Some(Killed),
                slots: [Agree, Distinguish],
            },
            Row {
                id: "R12",
                mutation: "bytes-key-doubled",
                program: "byteskey",
                status: None,
                slots: [Undecided, Undecided],
            },
            Row {
                id: "R13",
                mutation: "nest-value",
                program: "nest",
                status: Some(Killed),
                slots: [Agree, Distinguish],
            },
            Row {
                id: "R14",
                mutation: "clear-noop",
                program: "clear",
                status: Some(Killed),
                slots: [Agree, Distinguish],
            },
            Row {
                id: "R15",
                mutation: "clear-noop",
                program: "halt",
                status: Some(Survived),
                slots: [Agree, Agree],
            },
        ],
    );
}

#[test]
fn generated_cell_maps_r16_r17() {
    check(
        "collections/cellmap",
        &[
            Row {
                id: "R16",
                mutation: "balance-plus-one",
                program: "open21",
                status: Some(Killed),
                slots: [Agree, Distinguish],
            },
            Row {
                id: "R17",
                mutation: "seq-swapped",
                program: "open12",
                status: Some(Survived),
                slots: [Agree, Agree],
            },
        ],
    );
}

#[test]
fn imp_environment_r18_r22() {
    check(
        "collections/collimp",
        &[
            Row {
                id: "R18",
                mutation: "plus-as-minus",
                program: "sum",
                status: Some(Killed),
                slots: [Agree, Distinguish],
            },
            Row {
                id: "R19",
                mutation: "decl-guard-dropped",
                program: "dup",
                status: Some(Killed),
                slots: [Distinguish, Agree],
            },
            Row {
                id: "R20",
                mutation: "decl-guard-dropped",
                program: "sum",
                status: Some(Survived),
                slots: [Agree, Agree],
            },
            Row {
                id: "R21",
                mutation: "decl-initial-value",
                program: "sum",
                status: Some(Survived),
                slots: [Agree, Agree],
            },
            Row {
                id: "R22",
                mutation: "decl-initial-value",
                program: "dup",
                status: Some(Killed),
                slots: [Agree, Distinguish],
            },
        ],
    );
}

#[test]
fn lexical_environment_r23_r26() {
    check(
        "collections/collenv",
        &[
            Row {
                id: "R23",
                mutation: "binding-dropped",
                program: "let1",
                status: Some(Killed),
                slots: [Agree, Distinguish],
            },
            Row {
                id: "R24",
                mutation: "update-as-concat",
                program: "let1",
                status: Some(Survived),
                slots: [Agree, Agree],
            },
            Row {
                id: "R25",
                mutation: "update-as-concat",
                program: "shadow",
                status: Some(Killed),
                slots: [Distinguish, Distinguish],
            },
            Row {
                id: "R26",
                mutation: "binding-dropped",
                program: "const",
                status: Some(Survived),
                slots: [Agree, Agree],
            },
        ],
    );
}
