//! Peak resident memory pins for `krust kcompile` on reduced reproductions of the
//! real-semantics memory regressions.
//!
//! The pinned WASM definition needs minutes and gigabytes, so the pins here compile a
//! synthetic definition that has the same shape: a chain of modules in which every module
//! sees every sort declared before it, so that each generating kompile pass (KItem subsorts,
//! sort predicates, sort projections, sort injections) adds one sentence per visible sort per
//! module, and each of those sentences carries a module-wide provenance receipt.
//! Peak RSS is measured by `scripts/conformance/measure.py` on the child process, the same
//! helper the WASM ratchet uses.

use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

use toml::Value;

mod support;
use support::chain::{Shape, definition as generated_definition, main_module};

/// Number of chained modules in the reduced memory pin.
const MODULES: usize = 10;
/// Peak RSS ceiling for the chain compile.
const PEAK_RSS_LIMIT_KIB: u64 = 400 * 1024;

struct Workspace {
    root: PathBuf,
}

impl Workspace {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let nonce = NEXT.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir().join(format!(
            "k-rust-kompile-memory-{}-{nonce}",
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

fn measured_value(metrics: &Value, key: &str) -> i64 {
    metrics[key]
        .as_integer()
        .unwrap_or_else(|| panic!("measurement helper recorded no integer {key}"))
}

#[test]
fn module_chain_compile_stays_under_the_pre_regression_peak_rss() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let measure = repository.join("scripts/conformance/measure.py");
    let workspace = Workspace::new();
    let definition = workspace.root.join("chain.k");
    fs::write(&definition, generated_definition(MODULES, Shape::Chain)).unwrap();
    let log = workspace.root.join("measure");

    let output = Command::new("python3")
        .arg(&measure)
        .arg("--log")
        .arg(&log)
        .args(["--timeout", "900", "--"])
        .arg(env!("CARGO_BIN_EXE_krust"))
        .arg("kcompile")
        .arg(&definition)
        .args(["--main-module", &main_module(MODULES)])
        .args(["--backend", "llvm"])
        .arg("--output-directory")
        .arg(workspace.root.join("output"))
        .output()
        .unwrap();
    let stderr = fs::read_to_string(workspace.root.join("measure.stderr")).unwrap_or_default();
    assert!(
        output.status.success(),
        "kcompile failed under the measurement helper: {}\n{stderr}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        workspace.root.join("output/definition.kore").is_file(),
        "kcompile produced no definition.kore"
    );

    let metrics = fs::read_to_string(workspace.root.join("measure.meta.toml"))
        .unwrap()
        .parse::<Value>()
        .unwrap();
    assert_eq!(measured_value(&metrics, "exit_code"), 0);
    let peak_rss_kib = u64::try_from(measured_value(&metrics, "peak_rss_kib")).unwrap();
    assert!(
        peak_rss_kib <= PEAK_RSS_LIMIT_KIB,
        "kcompile of the {MODULES}-module chain peaked at {peak_rss_kib} KiB ({} MiB), above the \
         {PEAK_RSS_LIMIT_KIB} KiB ({} MiB) pre-regression ceiling",
        peak_rss_kib / 1024,
        PEAK_RSS_LIMIT_KIB / 1024,
    );
}
