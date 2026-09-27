//! Deterministic work bounds for a checked-in, medium synthetic definition.

use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

// Baselines: many-small-rules n=24 from tests/perf/synth.py. Bundle byte
// headroom is 10%, rounded up to the next hundred bytes; zero pins the
// fixture's structural counts.
const BOUNDS: &[(&str, u64, u64)] = &[
    ("bundle.bytes", 575_009, 57_600),
    ("bundle.other_bytes", 76_773, 7_700),
    ("bundle.provenance_bytes", 498_236, 49_900),
    ("collector.host_descriptors", 34, 4),
    ("declarations.total", 34, 4),
    ("definition.modules", 2, 0),
    ("definition.sentences", 33, 4),
    ("definition.sentences.configuration", 1, 0),
    ("definition.sentences.production", 3, 0),
    ("definition.sentences.rule", 24, 0),
    ("definition.sentences.subsort", 2, 0),
    ("definition.sentences.syntax_sort", 3, 0),
    ("definition.source_map_entries", 273, 28),
    ("definition.symbols", 33, 4),
    ("descriptors.kind.Configuration", 1, 0),
    ("descriptors.kind.Constructor", 3, 0),
    ("descriptors.kind.Grammar", 3, 0),
    ("descriptors.kind.Rule", 24, 0),
    ("descriptors.kind.Sort", 3, 0),
    ("descriptors.total", 34, 4),
    ("provenance.anchors", 385, 0),
    ("provenance.origin_frames", 1_155, 116),
    ("semantic.modules", 2, 0),
];

struct Scratch(PathBuf);

impl Scratch {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "krs-measure-ratchet-{}-{nanos}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn run_check(
    manifest: &Path,
    target: &Path,
    wrapper: &Path,
    log: &Path,
    counters: &Path,
) -> Output {
    Command::new(env!("CARGO_BIN_EXE_krs"))
        .args(["check", "--manifest-path"])
        .arg(manifest)
        .args([
            "--package",
            "krs-perf-synth",
            "--definition",
            "main",
            "--counters",
        ])
        .arg(counters)
        .env("CARGO_TARGET_DIR", target)
        .env("CARGO_NET_OFFLINE", "true")
        .env("RUSTUP_TOOLCHAIN", "stable")
        .env("RUSTC_WRAPPER", wrapper)
        .env("KRS_RATCHET_RUSTC_LOG", log)
        .env_remove("RUSTC_WORKSPACE_WRAPPER")
        .output()
        .unwrap()
}

fn assert_success(output: &Output) {
    assert!(
        output.status.success(),
        "krs check failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn medium_definition_counters_and_second_check_are_stable() {
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/perf/fixtures/ratchet-medium/Cargo.toml")
        .canonicalize()
        .unwrap();
    let scratch = Scratch::new();
    let target = scratch.0.join("target");
    let wrapper = scratch.0.join("rustc-wrapper");
    let log = scratch.0.join("rustc.log");
    let counters = scratch.0.join("counters.json");
    fs::write(
        &wrapper,
        "#!/bin/sh\nprintf '%s\\n' \"$*\" >> \"$KRS_RATCHET_RUSTC_LOG\"\nexec \"$@\"\n",
    )
    .unwrap();
    fs::set_permissions(&wrapper, fs::Permissions::from_mode(0o755)).unwrap();

    assert_success(&run_check(&fixture, &target, &wrapper, &log, &counters));
    let first_invocations = fs::read_to_string(&log).unwrap();
    assert!(first_invocations.contains("--crate-name krs_perf_synth"));
    assert!(first_invocations.contains("--crate-name krs_generated_collector_"));

    let document: serde_json::Value =
        serde_json::from_slice(&fs::read(&counters).unwrap()).unwrap();
    assert_eq!(document["schema"], "krs-counters/1");
    assert_eq!(document["status"], "ok");
    let measured = &document["counters"];
    for &(key, baseline, headroom) in BOUNDS {
        let actual = measured[key]
            .as_u64()
            .unwrap_or_else(|| panic!("missing counter {key}"));
        assert!(
            actual <= baseline + headroom,
            "{key}: observed {actual} exceeds {} (baseline {baseline} + headroom {headroom})",
            baseline + headroom
        );
    }

    fs::write(&log, "").unwrap();
    assert_success(&run_check(&fixture, &target, &wrapper, &log, &counters));
    let second_invocations = fs::read_to_string(&log).unwrap();
    assert!(
        !second_invocations
            .lines()
            .any(|line| line.contains("--crate-name krs_perf_synth")
                || line.contains("--crate-name krs_generated_collector_")),
        "unchanged check invoked rustc for the fixture or collector:\n{second_invocations}"
    );
}
