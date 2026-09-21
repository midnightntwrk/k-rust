//! The phase timing report must account for nearly all of a sandbox compile.
//!
//! This pin is ignored on the CQ-15a base because the carried resolved-state update is
//! intentionally still expensive there. CQ-15 removes that work; the orchestrator then
//! enables this test.

#![cfg(feature = "cli")]

use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

use serde_json::Value;

const MODULES: usize = 10;
const SORTS_PER_MODULE: usize = 8;
const RULES_PER_MODULE: usize = 12;

fn chain_definition() -> String {
    let mut text = String::new();
    for module in 0..MODULES {
        text.push_str(&format!("module CHAIN-{module}\n"));
        if module == 0 {
            text.push_str("  imports INT\n");
            text.push_str("  syntax Pgm ::= \"start\"\n");
            text.push_str("  configuration <k> $PGM:Pgm </k> <n> 0 </n>\n");
        } else {
            text.push_str(&format!("  imports CHAIN-{}\n", module - 1));
        }
        for sort in 0..SORTS_PER_MODULE {
            text.push_str(&format!(
                "  syntax S{module}x{sort} ::= \"c{module}x{sort}\" | f{module}x{sort}(S{module}x{sort}, Int) [function]\n"
            ));
        }
        for rule in 0..RULES_PER_MODULE {
            let sort = rule % SORTS_PER_MODULE;
            text.push_str(&format!(
                "  rule f{module}x{sort}(c{module}x{sort}, N:Int) => c{module}x{sort} requires N ==Int {rule}\n"
            ));
        }
        text.push_str("endmodule\n\n");
    }
    text
}

struct Workspace {
    root: PathBuf,
}

impl Workspace {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let nonce = NEXT.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir().join(format!(
            "k-rust-timings-residual-{}-{nonce}",
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

fn assert_residual(definition: &Path, main_module: &str, workspace: &Workspace) {
    let timings = workspace.root.join("timings.json");
    let log = workspace.root.join("measure");
    let output = Command::new("python3")
        .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("../../scripts/conformance/measure.py"))
        .arg("--log")
        .arg(&log)
        .args(["--timeout", "900", "--"])
        .arg(env!("CARGO_BIN_EXE_krust"))
        .args(["kcompile", definition.to_str().unwrap()])
        .args(["--main-module", main_module, "--backend", "llvm"])
        .arg("--output-directory")
        .arg(workspace.root.join("output"))
        .args(["--timings", timings.to_str().unwrap()])
        .output()
        .unwrap();
    let stderr = fs::read_to_string(workspace.root.join("measure.stderr")).unwrap_or_default();
    assert!(
        output.status.success(),
        "kcompile failed under the measurement helper: {}\n{stderr}",
        String::from_utf8_lossy(&output.stderr)
    );
    let report: Value = serde_json::from_str(&fs::read_to_string(timings).unwrap()).unwrap();
    let residual = [
        "load_unattributed_seconds",
        "compile_unattributed_seconds",
        "write_unattributed_seconds",
    ]
    .into_iter()
    .map(|key| report[key].as_f64().unwrap())
    .sum::<f64>();
    let total_wall = report["total_wall_seconds"].as_f64().unwrap();
    assert!(
        residual <= 0.1 * total_wall + 0.25,
        "timing residual {residual:.3}s exceeds 10% of {total_wall:.3}s"
    );
}

#[test]
fn compile_timing_residual_stays_below_ten_percent() {
    let repository = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");

    let rewrite = Workspace::new();
    assert_residual(&repository.join("examples/rewrite.k"), "REWRITE", &rewrite);

    let chain = Workspace::new();
    let definition = chain.root.join("chain.k");
    fs::write(&definition, chain_definition()).unwrap();
    assert_residual(&definition, &format!("CHAIN-{}", MODULES - 1), &chain);
}
