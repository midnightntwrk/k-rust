//! Sandbox scaling probes for module graphs that expose import-closure costs.
//!
//! These tests are intentionally ignored in the ordinary workspace run. They launch a release
//! `krust` child through `measure.py`, so the run records wall time, peak RSS, and the CQ-15a
//! timing residual together. CQ-15's structural update was dropped after its RSS gate failed;
//! consequently this harness does not claim a resolve-update sentence-visit counter. That work
//! is unavailable on the fallback tree and must be measured by a future ownership redesign.

#![cfg(feature = "cli")]

use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

use serde_json::Value;
use toml::Value as TomlValue;

mod support;
use support::chain::{Shape, definition, main_module};

const CHAIN_MODULES: usize = 40;
const FAN_IN_MODULES: usize = 24;
// Blow-up detectors allow headroom over the restored design while staying below the
// previously measured regression peak.
const CHAIN_PEAK_RSS_BLOWUP_DETECTOR_KIB: u64 = 850 * 1024;
const FAN_IN_PEAK_RSS_BLOWUP_DETECTOR_KIB: u64 = 850 * 1024;

struct Workspace {
    root: PathBuf,
}

impl Workspace {
    fn new(label: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let nonce = NEXT.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir().join(format!(
            "k-rust-kompile-scaling-{label}-{}-{nonce}",
            std::process::id()
        ));
        fs::create_dir_all(root.join("output")).unwrap();
        Self { root }
    }
}

impl Drop for Workspace {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

fn integer(metrics: &TomlValue, key: &str) -> u64 {
    metrics[key]
        .as_integer()
        .unwrap_or_else(|| panic!("measurement helper recorded no integer {key}"))
        .try_into()
        .unwrap_or_else(|_| panic!("measurement helper recorded negative {key}"))
}

fn number(report: &Value, key: &str) -> f64 {
    report[key]
        .as_f64()
        .unwrap_or_else(|| panic!("timing report recorded no number {key}"))
}

fn run_scaling_case(label: &str, modules: usize, shape: Shape, peak_limit_kib: u64) {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let workspace = Workspace::new(label);
    let source = workspace.root.join("definition.k");
    let timings = workspace.root.join("timings.json");
    let counters = workspace.root.join("counters.json");
    let log = workspace.root.join("measure");
    fs::write(&source, definition(modules, shape)).unwrap();

    let krust = std::env::var_os("KRUST_SCALING_BIN")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(env!("CARGO_BIN_EXE_krust")));
    let output = Command::new("python3")
        .arg(repository.join("scripts/conformance/measure.py"))
        .arg("--log")
        .arg(&log)
        .args(["--timeout", "900", "--"])
        .arg(&krust)
        .args(["kcompile", source.to_str().unwrap()])
        .args(["--main-module", &main_module(modules)])
        .args(["--backend", "llvm"])
        .arg("--output-directory")
        .arg(workspace.root.join("output"))
        .args(["--timings", timings.to_str().unwrap()])
        .env("KRUST_COUNTERS", &counters)
        .output()
        .unwrap();
    let stderr = fs::read_to_string(workspace.root.join("measure.stderr")).unwrap_or_default();
    assert!(
        output.status.success(),
        "{label} kcompile failed under the measurement helper: {}\n{stderr}",
        String::from_utf8_lossy(&output.stderr)
    );

    let metrics = fs::read_to_string(workspace.root.join("measure.meta.toml"))
        .unwrap()
        .parse::<TomlValue>()
        .unwrap();
    assert_eq!(integer(&metrics, "exit_code"), 0);
    let peak = integer(&metrics, "peak_rss_kib");
    assert!(
        peak <= peak_limit_kib,
        "{label} peaked at {} MiB, above {} MiB",
        peak / 1024,
        peak_limit_kib / 1024
    );

    let report: Value = serde_json::from_str(&fs::read_to_string(timings).unwrap()).unwrap();
    let residual = [
        "load_unattributed_seconds",
        "compile_unattributed_seconds",
        "write_unattributed_seconds",
    ]
    .into_iter()
    .map(|key| number(&report, key))
    .sum::<f64>();
    let total_wall = number(&report, "total_wall_seconds");
    assert!(
        residual <= 0.1 * total_wall + 0.25,
        "{label} timing residual {residual:.3}s exceeds 10% of {total_wall:.3}s"
    );
}

#[test]
#[ignore = "sandbox scaling gate; CQ-15 structural update was dropped"]
fn chain_40_scaling_stays_within_the_fallback_envelope() {
    run_scaling_case(
        "chain-40",
        CHAIN_MODULES,
        Shape::Chain,
        CHAIN_PEAK_RSS_BLOWUP_DETECTOR_KIB,
    );
}

#[test]
#[ignore = "sandbox scaling gate; CQ-15 structural update was dropped"]
fn fan_in_24_scaling_stays_within_the_fallback_envelope() {
    run_scaling_case(
        "fanin-24",
        FAN_IN_MODULES,
        Shape::FanIn,
        FAN_IN_PEAK_RSS_BLOWUP_DETECTOR_KIB,
    );
}
