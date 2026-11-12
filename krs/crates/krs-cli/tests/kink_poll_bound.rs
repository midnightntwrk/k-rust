//! FB45-KINK: a flip whose mutant never ends is `unknown` by kink's work budget, a bound of polls,
//! whatever the clock.
//!
//! The package's `Reach(n)` climbs to the first value at least 10 (`if n >= 10 { n } else {
//! Reach(n + 1) }`), and `Hold(n)` returns `n` from 10 on and applies itself to the same `n`
//! below (`if n >= 10 { n } else { Hold(n) }`). The corpus runs `climb 20` and `keep 20`, which
//! the baseline answers at once. The flip of `n >= 10` in `Reach` sends `Reach(20)` up for ever
//! with a growing argument, inside one step: no exact cycle, so only a bound inside the step ends
//! it, and the work budget (`[budget] work_factor`, default 5: `max(5 × P, P_max)` polls) does, at
//! the same poll on every host. The flip is `unknown` with a cause naming the polls and the bound,
//! cached and locked like any verdict, so a second command under another `time_ms` (both far
//! above the run) reads it from the cache and writes the same lock. The flip of `n >= 10` in
//! `Hold` makes `Hold(20)` apply itself to the same argument: an exact cycle, which the backend
//! decides without the bound.

#![cfg(feature = "kink")]

use std::fmt::Write as _;
use std::fs;
use std::path::Path;
use std::process::Output;

use krs_test_support::{
    SharedFixtureTarget, TempDir, fixture_build_env, krs_command, shared_fixture_target, temp_dir,
};
use serde_json::Value;

const NAME: &str = "krs-cli-kink-poll-bound";

const LIBRARY: &str = r#"
use k::builtin::{Int, KSequence};
use k::{KItem, KResult, Term};

k::sorts! {
    Cmd: KItem;
}

#[k::constructors(sort = Cmd, result = KResult)]
pub enum CmdSyntax {
    #[k::syntax("climb {n}")]
    Climb { n: Int },
    #[k::syntax("keep {n}")]
    Keep { n: Int },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub acc: Int,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Cmd) -> Self {
        Self {
            k: k::k![pgm],
            acc: 0,
        }
    }
}

/// The first value at least 10 from `n` up.
#[k::function(total, internal)]
pub fn Reach(n: Term<Int>) -> Term<Int> {
    if n >= 10 { n } else { Reach(n + 1) }
}

/// `n` from 10 on; below, itself again.
#[k::function(partial, internal)]
pub fn Hold(n: Term<Int>) -> Term<Int> {
    if n >= 10 { n } else { Hold(n) }
}

k::rules! {
    for Machine;
    use CmdSyntax::*;

    climb: { k: [Climb(n), ..], acc: _ } => { k: [..], acc: crate::Reach(n) };
    keep: { k: [Keep(n), ..], acc: _ } => { k: [..], acc: crate::Hold(n) };
}
"#;

/// The corpus: each case's id and program, in `FLOW.toml` order.
const CASES: [(&str, &str); 2] = [("climb", "climb 20"), ("keep", "keep 20")];

/// The package with its corpus, in a fresh directory.
struct Package {
    directory: TempDir,
    target: SharedFixtureTarget,
}

impl Package {
    fn new() -> Self {
        let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../krs")
            .canonicalize()
            .unwrap();
        let directory = temp_dir();
        let root = directory.path();
        fs::create_dir_all(root.join("src")).unwrap();
        fs::create_dir_all(root.join("kink/cases")).unwrap();
        fs::write(root.join("src/lib.rs"), LIBRARY).unwrap();
        for (id, program) in CASES {
            fs::write(
                root.join(format!("kink/cases/{id}.g")),
                format!("{program}\n"),
            )
            .unwrap();
        }
        fs::write(
            root.join("Cargo.toml"),
            format!(
                "[package]\nname = \"{NAME}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"POLLS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
                serde_json::to_string(krs.to_str().unwrap()).unwrap(),
            ),
        )
        .unwrap();
        let package = Self {
            directory,
            target: shared_fixture_target(),
        };
        package.set_clock(600_000);
        package
    }

    /// `FLOW.toml` with `[budget] time_ms = time_ms` and the default work budget.
    fn set_clock(&self, time_ms: u64) {
        let mut flow = format!(
            "[spec]\nkrs = {{ package = \"{NAME}\", definition = \"main\" }}\n\n[budget]\ntime_ms = {time_ms}\n"
        );
        for (id, _) in CASES {
            writeln!(
                flow,
                "\n[[program]]\nid = \"{id}\"\nfile = \"cases/{id}.g\""
            )
            .unwrap();
        }
        fs::write(self.directory.path().join("kink/FLOW.toml"), flow).unwrap();
    }

    fn lock(&self) -> String {
        fs::read_to_string(self.directory.path().join("kink/kink.lock")).unwrap()
    }

    /// `krs kink VERB ARGUMENTS` with this package selected, from its directory.
    fn kink(&self, verb: &str, arguments: &[&str]) -> Output {
        let mut process = krs_command!();
        fixture_build_env(&mut process, self.target.path());
        process
            .current_dir(self.directory.path())
            .args(["kink", verb])
            .args(arguments)
            .args(["--package", NAME, "--definition", "main"])
            .output()
            .unwrap()
    }

    /// The coverage document of `krs kink coverage ARGUMENTS` and its exit status.
    fn coverage(&self, arguments: &[&str]) -> (Option<i32>, Value) {
        let output = self.kink("coverage", arguments);
        let document = serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
            panic!(
                "stdout is not JSON ({error}):\n{}\nstderr:\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            )
        });
        (output.status.code(), document)
    }
}

/// The flip that negates `n >= 10` in the function `function`.
fn flip<'d>(document: &'d Value, function: &str) -> &'d Value {
    let items = document["families"]["flips"]["items"].as_array().unwrap();
    items
        .iter()
        .find(|item| {
            item["id"]
                .as_str()
                .is_some_and(|id| id.to_lowercase().contains(&function.to_lowercase()))
        })
        .unwrap_or_else(|| panic!("no flip of {function}: {items:#?}"))
}

/// What the test asserts of a flip, for a message.
fn summary(item: &Value) -> Value {
    serde_json::json!({
        "id": item["id"],
        "status": item["status"],
        "kink_status": item["kink_status"],
        "reason": item["reason"],
        "killer": item["killer"],
        "causes": item["causes"],
        "live_runs": item["live_runs"],
        "calls": item["calls"],
    })
}

/// The flip of `Reach`'s base case is `unknown` by the poll bound, cached and locked; the flip of
/// `Hold`'s is `unknown` too, decided by the backend without the bound: the mutant's run of `keep`
/// ends with `Hold(20)` left unevaluated (the backend detects the exact self-application), an open
/// application of the edited function, which is no value kink compares. Both are answers no
/// clock decides, so another `time_ms` changes neither, and both come from the cache. The command
/// exits 3 (no answer), as for any `unknown` flip; under `--locked` the lock is current.
#[test]
fn a_flip_whose_recursion_grows_for_ever_is_unknown_by_the_poll_bound_whatever_the_clock() {
    let package = Package::new();
    let (status, first) = package.coverage(&[]);
    assert_eq!(status, Some(3), "{:#}", first["lock"]);
    let climbing = flip(&first, "reach");
    assert_eq!(climbing["status"], "unknown", "{:#}", summary(climbing));
    // Every program the flip left undecided was cut by the work budget: the row's reason.
    assert_eq!(climbing["reason"], "work-budget", "{:#}", summary(climbing));
    let [cause] = climbing["causes"].as_array().unwrap().as_slice() else {
        panic!("one program's cause: {:#}", summary(climbing))
    };
    assert_eq!(cause["program"], "climb", "{:#}", summary(climbing));
    let polls = |document: &Value, id: &str| {
        document["programs"]
            .as_array()
            .unwrap()
            .iter()
            .find(|program| program["id"] == id)
            .and_then(|program| program["polls"].as_u64())
            .expect("the baseline's polls")
    };
    // The bound is `max(5 × P, P_max)`: the corpus's two baselines cost about the same, so it is
    // `5 × P` here.
    let (climb, keep) = (polls(&first, "climb"), polls(&first, "keep"));
    assert!(5 * climb >= keep, "{climb} {keep}");
    let text = cause["cause"].as_str().unwrap();
    assert!(
        text.starts_with(&format!(
            "the mutant's run used more than 5 × the baseline's {climb} polls ({}), its work \
             budget ([budget] work_factor), so it is no complete run; ",
            5 * climb
        )),
        "{text}"
    );
    assert!(text.contains("(poll-bound 1)"), "{text}");
    let lock = package.lock();
    assert!(lock.contains("\nwork_factor = 5\n"), "{lock}");
    assert!(
        lock.contains("id = \"flip--reach_1+reach_2--IntGreaterEqual\""),
        "{lock}"
    );

    // The exact self-application: the backend decides it without the bound.
    let holding = flip(&first, "hold");
    assert_eq!(
        (&holding["status"], &holding["reason"]),
        (&Value::from("unknown"), &Value::from("open-application")),
        "{:#}",
        summary(holding)
    );
    let [held] = holding["causes"].as_array().unwrap().as_slice() else {
        panic!("one program's cause: {:#}", summary(holding))
    };
    let held = held["cause"].as_str().unwrap();
    assert!(
        held.contains("hold ( 20 )") && !held.contains("poll"),
        "{held}"
    );

    // Another clock, still far above every run: the same verdicts, from the cache, and the same
    // lock, which `--locked` then finds current.
    package.set_clock(60_000);
    let (second_status, second) = package.coverage(&[]);
    assert_eq!(second_status, status);
    for function in ["reach", "hold"] {
        let (before, after) = (flip(&first, function), flip(&second, function));
        assert_eq!(after["status"], before["status"], "{:#}", summary(after));
        assert_eq!(after["causes"], before["causes"], "{:#}", summary(after));
        assert_eq!(after["live_runs"], 0, "{:#}", summary(after));
        assert_eq!(after["calls"], 0, "{:#}", summary(after));
    }
    assert_eq!(package.lock(), lock);
    let (locked, document) = package.coverage(&["--locked"]);
    assert_eq!(locked, Some(3), "{:#}", document["lock"]);
    assert_eq!(
        document["lock"]["changes"],
        serde_json::json!([]),
        "{:#}",
        document["lock"]
    );
    assert_eq!(package.lock(), lock);
}
