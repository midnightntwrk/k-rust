//! A case states the instances a run starts with (`instances`, krs-exec's `inputs` module,
//! "Instances"): `krs run --case`, `krs search --case`, `krs cases` and a case side of
//! `krs compare` build the initial configuration with them.
//!
//! The definition is the configuration-cells gate's `group-harts/smp`: harts as the instances of a
//! Map collection keyed by `id`, each running the program its template starts it with (`$PGM`),
//! with the library `group-harts/hart`'s rules as local steps of one hart, and the definition's
//! `read` and `write` answering a hart's bus items from one shared memory.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Output;
use std::sync::{Arc, Mutex, Weak};

use krs_test_support::{
    SharedFixtureTarget, TempDir, fixture_build_env, krs_command, shared_fixture_target, temp_dir,
};
use serde_json::{Value, json};

const HART: &str =
    include_str!("../../../tests/configuration-cells/packages/group-harts/hart/src/lib.rs");
const SMP: &str =
    include_str!("../../../tests/configuration-cells/packages/group-harts/smp/src/lib.rs");

/// The library's package, which the definition composes.
const HART_PACKAGE: &str = "krs-configuration-cells-group-harts-hart";
const SMP_PACKAGE: &str = "krs-configuration-cells-group-harts-smp";

/// The workspace of the two packages, shared by the tests that overlap in this process, which run
/// `krs` on it one at a time.
struct Workspace {
    directory: TempDir,
    _target: SharedFixtureTarget,
    target: PathBuf,
    turn: Mutex<()>,
}

impl Workspace {
    fn shared() -> Arc<Self> {
        static SLOT: Mutex<Weak<Workspace>> = Mutex::new(Weak::new());
        let mut slot = SLOT
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if let Some(workspace) = slot.upgrade() {
            return workspace;
        }
        let target = shared_fixture_target();
        let directory = temp_dir();
        let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../krs")
            .canonicalize()
            .unwrap();
        let krs_literal = serde_json::to_string(krs.to_str().unwrap()).unwrap();
        let write = |relative: &str, contents: &str| {
            let path = directory.path().join(relative);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, contents).unwrap();
        };
        for (name, source, dependency) in [
            ("hart", HART, String::new()),
            (
                "smp",
                SMP,
                format!("hart = {{ package = \"{HART_PACKAGE}\", path = \"../hart\" }}\n"),
            ),
        ] {
            write(&format!("{name}/src/lib.rs"), source);
            write(
                &format!("{name}/Cargo.toml"),
                &format!(
                    "[package]\nname = \"krs-configuration-cells-group-harts-{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {krs_literal} }}\n{dependency}\n[package.metadata.krs]\nk-namespace = \"KRS-GROUP-HARTS-{}\"\n\n[package.metadata.krs.definitions.main]\n",
                    name.to_ascii_uppercase()
                ),
            );
        }
        write(
            "Cargo.toml",
            "[workspace]\nmembers = [\"hart\", \"smp\"]\nresolver = \"3\"\n",
        );
        let workspace = Arc::new(Self {
            directory,
            target: target.path().to_path_buf(),
            _target: target,
            turn: Mutex::new(()),
        });
        *slot = Arc::downgrade(&workspace);
        workspace
    }

    /// Write `contents` at `relative` inside the definition's package directory.
    fn write(&self, relative: &str, contents: &str) {
        fs::write(self.directory.path().join("smp").join(relative), contents).unwrap();
    }

    /// `krs VERB ARGUMENTS` on the definition, composed with the library's, from its package
    /// directory.
    fn krs(&self, verb: &str, arguments: &[&str]) -> Output {
        let _turn = self
            .turn
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let mut process = krs_command!();
        fixture_build_env(&mut process, &self.target);
        process
            .current_dir(self.directory.path().join("smp"))
            .arg(verb)
            .args(["--package", SMP_PACKAGE, "--definition", "main"])
            .args(["--dependency", &format!("{HART_PACKAGE}:main")])
            .args(arguments)
            .env("NO_COLOR", "1");
        process.output().unwrap()
    }
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn json(output: &Output) -> Value {
    serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
        panic!(
            "stdout is not JSON ({error}):\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            stderr(output)
        )
    })
}

/// Two harts at depth 0: the end states both, each with the cells its instance states (a
/// register of a group cell, a present optional cell, a job of the hart's own Map collection, a
/// program as K text) and every other cell as the template starts it under the case's inputs,
/// `k` the program `pgm` binds included. `krs compare` reads the case's run as a side, and the
/// end it reads is that end.
#[test]
fn a_case_starts_a_run_with_the_instances_it_states() {
    let workspace = Workspace::shared();
    workspace.write(
        "two.toml",
        r#"inputs.pgm = { "$text" = "inc ; inc" }
run.depth = 0

[[instances.harts.hart]]
id = 0
pc = 4096

[[instances.harts.hart]]
id = 1
pc = 8192
k = { "$text" = "inc" }
regs = { a = 5 }
reservation = [7]
jobs.job = [{ jid = 2, payload = 3 }]
"#,
    );
    let hart = |id: i64, k: Value, pc: i64, a: i64, reservation: Value, job: Value| {
        json!({
            "id": id,
            "k": {"$seq": [k]},
            "pc": pc,
            "regs": {"a": a, "b": 2},
            "reservation": reservation,
            "jobs": {"job": job},
        })
    };
    let end = json!({
        "halt": "depth-bound",
        "cells": {
            "harts": {"hart": [
                hart(0, json!({"Then": {"head": "Inc", "tail": "Inc"}}), 4096, 1, json!([]), json!([])),
                hart(1, json!({"Inc": []}), 8192, 5, json!([7]), json!([{"jid": 2, "payload": 3}])),
            ]},
            "mem": {},
            "next_id": 1,
        },
    });
    let run = workspace.krs("run", &["--case", "two.toml", "--output", "end"]);
    assert_eq!(run.status.code(), Some(0), "{}", stderr(&run));
    assert_eq!(json(&run), end);
    workspace.write("two-end.json", &end.to_string());
    let compare = workspace.krs("compare", &["two.toml", "two-end.json"]);
    assert_eq!(compare.status.code(), Some(0), "{}", stderr(&compare));
}

/// Two harts that store their own id at one address race: a search from the case's two harts
/// reaches both orders of their `write` steps, so an expectation of either value is unmet by the
/// other end. `krs cases` runs a case's instances as `krs run --case` does: one hart keyed 3
/// counts from the program counter its instance states.
#[test]
fn a_search_from_two_stated_harts_reaches_both_interleavings() {
    let workspace = Workspace::shared();
    let race = |value: i64| {
        format!(
            "inputs.pgm = {{ \"$text\" = \"store ( 7 )\" }}\ninstances.harts.hart = [{{ id = 0 }}, {{ id = 1 }}]\n\n[expect]\nhalt = \"stuck\"\ncompare = [\"mem\"]\ncells = {{ mem = {{ \"7\" = {value} }} }}\n"
        )
    };
    for (value, other) in [(0, 1), (1, 0)] {
        workspace.write("race.toml", &race(value));
        let search = workspace.krs("search", &["--case", "race.toml"]);
        assert_eq!(search.status.code(), Some(1), "{}", stderr(&search));
        assert!(
            stderr(&search).ends_with(&format!(
                "krs search: 2 solutions\nkrs search: expectation unmet at `mem[7]`\n  expected: {value}\n  actual:   {other}\n  (one of the 2 actual ends; the expectation holds of every end or is unmet)\n"
            )),
            "{}",
            stderr(&search)
        );
    }
    workspace.write(
        "count.toml",
        "inputs.pgm = { \"$text\" = \"inc\" }\ninstances.harts.hart = [{ id = 3, pc = 10 }]\n\n[expect]\nhalt = \"stuck\"\ncompare = [\"harts.hart.id\", \"harts.hart.pc\"]\ncells = { harts = { hart = [{ id = 3, pc = 11 }] } }\n",
    );
    let cases = workspace.krs("cases", &["count.toml", "--output", "json"]);
    assert_eq!(cases.status.code(), Some(0), "{}", stderr(&cases));
    let records = String::from_utf8_lossy(&cases.stdout).into_owned();
    assert!(records.contains("\"verdict\":\"met\""), "{records}");
}

/// A case that states a fixed cell, or two instances with one key, is refused before the run,
/// naming the position.
#[test]
fn a_case_that_states_no_instances_of_the_configuration_is_refused() {
    let workspace = Workspace::shared();
    for (name, instances, refusal) in [
        (
            "fixed.toml",
            "instances.mem = { \"0\" = 1 }\n",
            "error[krs::exec::case]: case `fixed.toml`: `instances.mem`: `mem` is a fixed cell: the initializer states its start from the inputs, and a case states only the instances of optional and repeated cells (here `harts.hart`); bind other inputs to start it otherwise",
        ),
        (
            "twice.toml",
            "instances.harts.hart = [{ id = 0 }, { id = 0, pc = 1 }]\n",
            "error[krs::exec::case]: case `twice.toml`: `instances.harts.hart[1]`: the instance has the key 0 of the instance at [0]: a Map collection holds one instance per key, its first cell `id`",
        ),
    ] {
        workspace.write(
            name,
            &format!("inputs.pgm = {{ \"$text\" = \"inc\" }}\n{instances}"),
        );
        let run = workspace.krs("run", &["--case", name]);
        assert_eq!(run.status.code(), Some(2), "{}", stderr(&run));
        assert!(stderr(&run).contains(refusal), "{}", stderr(&run));
    }
}
