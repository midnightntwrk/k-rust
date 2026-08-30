use std::{
    fs,
    os::unix::fs::PermissionsExt,
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

use toml::Value;

struct Fixture {
    root: PathBuf,
    k_checkout: PathBuf,
    wasm_checkout: PathBuf,
    fake_krust: PathBuf,
    args: PathBuf,
    limit: PathBuf,
    log: PathBuf,
}

impl Fixture {
    fn new() -> Self {
        static NEXT_FIXTURE: AtomicU64 = AtomicU64::new(0);
        let nonce = NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir().join(format!(
            "k-rust-wasm-ratchet-{}-{nonce}",
            std::process::id()
        ));
        let k_checkout = root.join("k");
        let wasm_checkout = root.join("wasm");
        let builtin = k_checkout.join("k-distribution/include/kframework/builtin");
        let semantics = wasm_checkout.join("pykwasm/src/pykwasm/kdist/wasm-semantics/test.md");
        fs::create_dir_all(&builtin).unwrap();
        fs::create_dir_all(semantics.parent().unwrap()).unwrap();
        fs::write(builtin.join("prelude.md"), "module PRELUDE endmodule\n").unwrap();
        fs::write(&semantics, "module WASM-TEST endmodule\n").unwrap();

        let fake_krust = root.join("fake-krust");
        fs::write(
            &fake_krust,
            r#"#!/usr/bin/env bash
set -euo pipefail
printf '%s\n' "$@" > "$FAKE_ARGS"
ulimit -v > "$FAKE_LIMIT"
sleep "${FAKE_SLEEP_SECONDS:-0}"
for line in $(seq -w 1 35); do
  printf 'diagnostic-%s\n' "$line" >&2
done
exit "${FAKE_EXIT_CODE:-17}"
"#,
        )
        .unwrap();
        let mut permissions = fs::metadata(&fake_krust).unwrap().permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(&fake_krust, permissions).unwrap();

        Self {
            args: root.join("args"),
            limit: root.join("limit"),
            log: root.join("ratchet.toml"),
            root,
            k_checkout,
            wasm_checkout,
            fake_krust,
        }
    }

    fn command(&self, label: &str, stage: &str, depth: u64) -> Command {
        let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let mut command = Command::new("bash");
        command
            .arg(workspace.join("scripts/wasm-ratchet.sh"))
            .args([
                "--label",
                label,
                "--stage",
                stage,
                "--depth",
                &depth.to_string(),
                "--log",
                self.log.to_str().unwrap(),
            ])
            .env("K_CHECKOUT", &self.k_checkout)
            .env("WASM_SEMANTICS_CHECKOUT", &self.wasm_checkout)
            .env("WASM_RATCHET_KRUST", &self.fake_krust)
            .env("WASM_RATCHET_TIMEOUT_SECONDS", "5")
            .env("WASM_RATCHET_MEMORY_KIB", "6291456")
            .env("REFERENCE_DIFFERENTIAL_ALLOW_UNPINNED", "1")
            .env("FAKE_ARGS", &self.args)
            .env("FAKE_LIMIT", &self.limit)
            .env("FAKE_EXIT_CODE", "17");
        command
    }

    fn run(&self, label: &str, stage: &str, depth: u64) -> std::process::Output {
        self.command(label, stage, depth).output().unwrap()
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.root).unwrap();
    }
}

#[test]
fn wasm_ratchet_records_probe_evidence_and_flags_regressions() {
    let fixture = Fixture::new();

    let baseline = fixture.run("baseline", "rule-parse", 20);
    assert!(
        baseline.status.success(),
        "{}",
        String::from_utf8_lossy(&baseline.stderr)
    );

    let invocation = fs::read_to_string(&fixture.args).unwrap();
    let expected_source = fixture
        .wasm_checkout
        .join("pykwasm/src/pykwasm/kdist/wasm-semantics/test.md");
    let expected_builtin = fixture
        .k_checkout
        .join("k-distribution/include/kframework/builtin");
    assert!(invocation.starts_with(&format!(
        "kcompile\n{}\n--main-module\nWASM-TEST\n--backend\nllvm\n",
        expected_source.display()
    )));
    assert!(invocation.contains("--emit-json\n"));
    assert!(invocation.ends_with(&format!(
        "--builtin-directory\n{}\n",
        expected_builtin.display()
    )));
    assert_eq!(fs::read_to_string(&fixture.limit).unwrap(), "6291456\n");

    let baseline_log = fs::read_to_string(&fixture.log).unwrap();
    let document = baseline_log.parse::<Value>().unwrap();
    let runs = document["run"].as_array().unwrap();
    assert_eq!(runs.len(), 1);
    assert_eq!(runs[0]["sequence"].as_integer(), Some(0));
    assert_eq!(runs[0]["label"].as_str(), Some("baseline"));
    assert_eq!(runs[0]["stage"].as_str(), Some("rule-parse"));
    assert_eq!(runs[0]["stage_rank"].as_integer(), Some(2));
    assert_eq!(runs[0]["depth"].as_integer(), Some(20));
    assert_eq!(runs[0]["exit_code"].as_integer(), Some(17));
    assert_eq!(runs[0]["regression"].as_bool(), Some(false));
    assert_eq!(runs[0]["stderr_sha256"].as_str().unwrap().len(), 64);
    let stderr_tail = runs[0]["stderr_tail"].as_str().unwrap();
    assert!(!stderr_tail.contains("diagnostic-05\n"));
    assert!(stderr_tail.starts_with("diagnostic-06\n"));
    assert!(stderr_tail.ends_with("diagnostic-35\n"));

    let depth_regression = fixture.run("depth-regression", "rule-parse", 19);
    assert_eq!(depth_regression.status.code(), Some(3));
    assert!(String::from_utf8_lossy(&depth_regression.stderr).contains("ratchet regression"));

    let stage_regression = fixture.run("stage-regression", "configuration-parse", 200);
    assert_eq!(stage_regression.status.code(), Some(3));
    assert!(String::from_utf8_lossy(&stage_regression.stderr).contains("ratchet regression"));

    let regression_log = fs::read_to_string(&fixture.log).unwrap();
    let document = regression_log.parse::<Value>().unwrap();
    let runs = document["run"].as_array().unwrap();
    assert_eq!(runs.len(), 3);
    assert_eq!(runs[1]["sequence"].as_integer(), Some(1));
    assert_eq!(runs[1]["regression"].as_bool(), Some(true));
    assert_eq!(runs[1]["previous_stage_rank"].as_integer(), Some(2));
    assert_eq!(runs[1]["previous_depth"].as_integer(), Some(20));
    assert_eq!(runs[2]["sequence"].as_integer(), Some(2));
    assert_eq!(runs[2]["regression"].as_bool(), Some(true));
    assert_eq!(runs[2]["previous_stage_rank"].as_integer(), Some(2));
    assert_eq!(runs[2]["previous_depth"].as_integer(), Some(20));
}

#[test]
fn wasm_ratchet_records_timeouts_and_returns_timeout_status() {
    let fixture = Fixture::new();
    let output = fixture
        .command("timeout", "rule-parse", 20)
        .env("WASM_RATCHET_TIMEOUT_SECONDS", "1")
        .env("FAKE_SLEEP_SECONDS", "2")
        .output()
        .unwrap();

    assert_eq!(output.status.code(), Some(124));
    assert!(String::from_utf8_lossy(&output.stderr).contains("WASM probe timed out"));
    let document = fs::read_to_string(&fixture.log)
        .unwrap()
        .parse::<Value>()
        .unwrap();
    let run = &document["run"].as_array().unwrap()[0];
    assert_eq!(run["timed_out"].as_bool(), Some(true));
    assert_eq!(run["regression"].as_bool(), Some(false));
    assert_eq!(run["exit_code"].as_integer(), Some(124));
}

#[test]
fn wasm_ratchet_preflight_failures_do_not_change_the_log() {
    let fixture = Fixture::new();
    fs::remove_file(
        fixture
            .wasm_checkout
            .join("pykwasm/src/pykwasm/kdist/wasm-semantics/test.md"),
    )
    .unwrap();

    let output = fixture.run("missing-source", "outer-parse", 0);
    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&output.stderr).contains("missing WASM source"));
    assert!(!fixture.log.exists());
}
