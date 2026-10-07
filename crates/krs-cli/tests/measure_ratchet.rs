//! Deterministic work bounds for a checked-in, medium synthetic definition.

use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::Path;
use std::process::Output;

use krs_test_support::{krs_command, temp_dir};

// Baselines: many-small-rules n=24 from tests/perf/synth.py. Bundle byte
// headroom is 10%, rounded up to the next hundred bytes; zero pins the
// fixture's structural counts.
const BOUNDS: &[(&str, u64, u64)] = &[
    ("bundle.bytes", 143_598, 14_400),
    ("bundle.other_bytes", 84_660, 8_500),
    ("bundle.provenance_bytes", 58_938, 5_900),
    ("collector.host_descriptors", 34, 4),
    ("declarations.total", 34, 4),
    ("definition.modules", 3, 0),
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

fn run_check(
    manifest: &Path,
    target: &Path,
    wrapper: &Path,
    log: &Path,
    counters: &Path,
) -> Output {
    krs_command!()
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
    let scratch = temp_dir();
    // The first check must invoke rustc for both the fixture and collector.
    let target = scratch.path().join("target");
    let wrapper = scratch.path().join("rustc-wrapper");
    let log = scratch.path().join("rustc.log");
    let counters = scratch.path().join("counters.json");
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
    assert_eq!(measured["result.reused"], 0);
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
    let second: serde_json::Value = serde_json::from_slice(&fs::read(&counters).unwrap()).unwrap();
    assert_eq!(second["status"], "ok");
    assert_eq!(second["counters"]["result.reused"], 1);
    for &(key, _, _) in BOUNDS {
        assert_eq!(second["counters"][key], measured[key], "{key}");
    }
}
