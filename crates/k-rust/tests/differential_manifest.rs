use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
    process::Command,
    time::{SystemTime, UNIX_EPOCH},
};

use toml::Value;

const MANIFEST: &str = include_str!("../../../scripts/reference-differential.toml");
const COMPILE_SCRIPT: &str = include_str!("../../../scripts/reference-differential.sh");
const KAST_SCRIPT: &str = include_str!("../../../scripts/reference-kast-differential.sh");
const SECTIONS: [&str; 5] = ["compile", "kast", "execution", "proof", "rpc"];

#[test]
fn differential_manifest_is_complete_and_unambiguous() {
    let manifest = MANIFEST.parse::<Value>().expect("valid differential TOML");
    assert_eq!(manifest["version"].as_integer(), Some(1));

    let reference = manifest["reference"].as_table().expect("reference pins");
    for pin in [
        "k",
        "imp",
        "wasm",
        "evm-equivalence",
        "kevm",
        "kevm-plugin",
        "mir",
    ] {
        let revision = reference[pin]["revision"]
            .as_str()
            .expect("revision string");
        assert_eq!(revision.len(), 40, "{pin} must use a full Git revision");
        assert!(
            revision.bytes().all(|byte| byte.is_ascii_hexdigit()),
            "{pin} must use a hexadecimal Git revision"
        );
    }
    assert!(
        reference["k"]["version"]
            .as_str()
            .is_some_and(|version| !version.is_empty()),
        "K must have a pinned release version"
    );

    let allowed_requirements = BTreeSet::from(["reference-toolchain"]);
    for section in SECTIONS {
        let entries = manifest[section].as_array().expect("coverage array");
        assert!(!entries.is_empty(), "{section} coverage must not be empty");
        let mut names = BTreeSet::new();
        for entry in entries {
            let name = entry["name"].as_str().expect("coverage name");
            assert!(names.insert(name), "duplicate {section} case {name}");
            let requirements = entry["requires"].as_array().expect("case requirements");
            assert!(
                !requirements.is_empty(),
                "{section} case {name} has no requirement"
            );
            for requirement in requirements {
                let requirement = requirement.as_str().expect("string requirement");
                assert!(
                    allowed_requirements.contains(requirement),
                    "unknown requirement {requirement} on {section} case {name}"
                );
            }
            assert!(
                entry["constructs"].as_array().is_some(),
                "{section} case {name} has no construct classification"
            );
        }
    }

    for entry in manifest["compile"].as_array().unwrap() {
        assert!(
            entry["comparisons"]
                .as_array()
                .is_some_and(|comparisons| !comparisons.is_empty()),
            "every compile case must declare compared artifacts"
        );
    }

    let mut paths = BTreeSet::new();
    collect_workspace_paths(&manifest, &mut paths);
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    for relative in paths {
        let path = workspace.join(&relative);
        assert!(
            path.exists(),
            "workspace fixture does not exist: {}",
            path.display()
        );
    }

    let mut constructs = BTreeSet::new();
    for section in SECTIONS {
        for entry in manifest[section].as_array().unwrap() {
            let blocked = entry["requires"]
                .as_array()
                .unwrap()
                .iter()
                .any(|requirement| requirement.as_str() == Some("semantics-support"));
            if !blocked {
                constructs.extend(
                    entry["constructs"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .map(|construct| construct.as_str().expect("string construct")),
                );
            }
        }
    }
    let required_constructs = BTreeSet::from([
        "bounded-search",
        "collections",
        "crypto-hook",
        "deep-term",
        "macro-runtime",
        "owise",
        "star-cell-variable",
    ]);
    let missing = required_constructs
        .difference(&constructs)
        .copied()
        .collect::<Vec<_>>();
    assert!(
        missing.is_empty(),
        "missing runnable corpus constructs: {missing:?}"
    );
}

#[test]
fn excluded_cases_have_complete_oracle_dispositions() {
    let manifest = MANIFEST.parse::<Value>().expect("valid differential TOML");
    let excluded = manifest["excluded"].as_array().expect("excluded cases");
    assert_eq!(
        excluded.len(),
        6,
        "the six audited exclusions must stay explicit"
    );

    let allowed_dispositions =
        BTreeSet::from(["alternative-oracle", "comparison-impossible", "local-gate"]);
    let expected_names = BTreeSet::from([
        "ecdsa-invalid-execution",
        "evm-execution",
        "fresh-constants-execution",
        "mir-execution",
        "proof-counterexample-artifact",
        "wasm-execution",
    ]);
    let mut names = BTreeSet::new();

    for entry in excluded {
        let table = entry.as_table().expect("excluded case table");
        let name = table["name"].as_str().expect("excluded case name");
        assert!(names.insert(name), "duplicate excluded case {name}");
        assert_eq!(
            table.keys().map(String::as_str).collect::<BTreeSet<_>>(),
            BTreeSet::from([
                "disposition",
                "local_gate",
                "name",
                "reason",
                "section",
                "source",
            ]),
            "excluded case {name} must use the complete canonical schema",
        );
        let disposition = table["disposition"].as_str().expect("excluded disposition");
        assert!(
            allowed_dispositions.contains(disposition),
            "unknown disposition {disposition} on excluded case {name}",
        );
        let expected_disposition = match name {
            "ecdsa-invalid-execution" | "evm-execution" => "local-gate",
            "fresh-constants-execution" => "comparison-impossible",
            "mir-execution" | "proof-counterexample-artifact" | "wasm-execution" => {
                "alternative-oracle"
            }
            _ => unreachable!("the exact excluded name set is checked below"),
        };
        assert_eq!(
            disposition, expected_disposition,
            "excluded case {name} changed its adjudicated disposition",
        );
        assert!(
            table["local_gate"]
                .as_str()
                .is_some_and(|gate| !gate.trim().is_empty()),
            "excluded case {name} must name its green local gate",
        );
        let reason = table["reason"].as_str().expect("excluded reason");
        assert!(
            !reason.trim().is_empty(),
            "excluded case {name} has no reason"
        );
        assert!(
            reason.contains("pinned") || disposition == "comparison-impossible",
            "excluded case {name} must identify the pinned oracle limitation",
        );
        for capability_gap in [
            "k-rust cannot",
            "k-rust does not",
            "k-rust lacks",
            "not implemented by k-rust",
            "unimplemented in k-rust",
        ] {
            assert!(
                !reason.contains(capability_gap),
                "excluded case {name} records a k-rust capability gap instead of an oracle limitation",
            );
        }

        let source = table["source"].as_str().expect("excluded source");
        assert!(
            source.starts_with("${workspace}/")
                || source.starts_with("${wasm}/")
                || source.starts_with("${evm}/")
                || source.starts_with("${mir}/"),
            "excluded case {name} must use a pinned checkout or workspace source",
        );
        if let Some(relative) = source.strip_prefix("${workspace}/") {
            let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
            assert!(
                workspace.join(relative).exists(),
                "excluded case {name} references missing workspace source {source}",
            );
        }
    }

    assert_eq!(names, expected_names, "the audited exclusion set changed");
}

#[test]
fn manual_certification_protocol_names_all_imp_families() {
    for command in [
        "# scripts/reference-non-imp-execution-differential.sh imp",
        "# scripts/reference-proof-differential.sh imp",
        "# scripts/reference-rpc-differential.sh imp",
    ] {
        assert!(
            MANIFEST.lines().any(|line| line == command),
            "manual certification protocol must name `{command}`",
        );
    }
}

#[test]
fn frontend_differentials_guard_rust_resident_memory_without_constraining_the_reference_jvm() {
    for script in [COMPILE_SCRIPT, KAST_SCRIPT] {
        assert!(
            script.contains("reference_memory_kib=${REFERENCE_DIFFERENTIAL_MEMORY_KIB:-}"),
            "the reference JVM must retain its independently optional virtual-memory ceiling",
        );
        assert!(
            script.contains("source \"$workspace/scripts/reference-memory-guard.sh\""),
            "the Rust frontend must use the shared resident-memory guard",
        );
        assert_eq!(
            script
                .matches("reference_run_rust_frontend cargo run")
                .count(),
            1,
            "each frontend script must route its one Rust process through the guard",
        );
        assert!(
            !script.contains("ulimit -v \"$rust_memory_kib\""),
            "the Rust frontend must not confuse virtual address space with resident memory",
        );
    }

    assert_eq!(
        COMPILE_SCRIPT
            .matches("ulimit -v \"$reference_memory_kib\"")
            .count(),
        1,
        "the reference compile must use only the reference ceiling",
    );
    assert_eq!(
        KAST_SCRIPT
            .matches("ulimit -v \"$reference_memory_kib\"")
            .count(),
        3,
        "reference compile, acceptance, and rejection checks must use the reference ceiling",
    );

    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let guard_path = workspace.join("scripts/reference-memory-guard.sh");
    let guard = fs::read_to_string(&guard_path).expect("shared resident-memory guard");
    for contract in [
        "RUST_DIFFERENTIAL_MEMORY_HIGH_KIB:-6291456",
        "RUST_DIFFERENTIAL_MEMORY_MAX_KIB:-8388608",
        "RUST_DIFFERENTIAL_FALLBACK_VIRTUAL_MEMORY_KIB:-12582912",
        "MemoryHigh=${rust_memory_high_kib}K",
        "MemoryMax=${rust_memory_max_kib}K",
        "MemorySwapMax=0",
        "ulimit -v \"$rust_fallback_virtual_memory_kib\"",
    ] {
        assert!(
            guard.contains(contract),
            "memory guard is missing `{contract}`"
        );
    }

    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time after Unix epoch")
        .as_nanos();
    let fixture = std::env::temp_dir().join(format!(
        "k-rust-memory-guard-{}-{unique}",
        std::process::id()
    ));
    fs::create_dir(&fixture).expect("create guard fixture");
    let fake_systemd_run = fixture.join("systemd-run");
    fs::write(
        &fake_systemd_run,
        r#"#!/usr/bin/env bash
printf '%s\n' "$*" >>"$GUARD_CALLS"
if [[ "${*: -1}" == true ]]; then
  exit "$SYSTEMD_PROBE_STATUS"
fi
while (($#)) && [[ "$1" != -- ]]; do
  shift
done
shift
exec "$@"
"#,
    )
    .expect("write fake systemd-run");
    let mut permissions = fs::metadata(&fake_systemd_run)
        .expect("fake systemd-run metadata")
        .permissions();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        permissions.set_mode(0o755);
    }
    fs::set_permissions(&fake_systemd_run, permissions).expect("make fake systemd-run executable");
    let calls = fixture.join("calls");
    let path = format!(
        "{}:{}",
        fixture.display(),
        std::env::var("PATH").expect("PATH")
    );

    let scoped = Command::new("bash")
        .arg("-c")
        .arg("source \"$1\"; shift; reference_run_rust_frontend \"$@\"")
        .arg("guard-test")
        .arg(&guard_path)
        .arg("bash")
        .arg("-c")
        .arg("printf scoped-out; printf scoped-err >&2; exit 23")
        .env("PATH", &path)
        .env("GUARD_CALLS", &calls)
        .env("SYSTEMD_PROBE_STATUS", "0")
        .output()
        .expect("run scoped guard fixture");
    assert_eq!(
        scoped.status.code(),
        Some(23),
        "preserve scoped exit status"
    );
    assert_eq!(scoped.stdout, b"scoped-out", "preserve scoped stdout");
    assert_eq!(scoped.stderr, b"scoped-err", "preserve scoped stderr");
    let scoped_calls = fs::read_to_string(&calls).expect("scoped call log");
    assert!(scoped_calls.contains("MemoryHigh=6291456K"));
    assert!(scoped_calls.contains("MemoryMax=8388608K"));
    assert!(scoped_calls.contains("MemorySwapMax=0"));
    assert_eq!(
        scoped_calls.lines().count(),
        2,
        "probe once and execute once"
    );

    fs::write(&calls, "").expect("clear call log");
    let fallback = Command::new("bash")
        .arg("-c")
        .arg("source \"$1\"; shift; reference_run_rust_frontend \"$@\"")
        .arg("guard-test")
        .arg(&guard_path)
        .arg("bash")
        .arg("-c")
        .arg("ulimit -v; printf fallback-err >&2; exit 29")
        .env("PATH", &path)
        .env("GUARD_CALLS", &calls)
        .env("SYSTEMD_PROBE_STATUS", "1")
        .env("RUST_DIFFERENTIAL_FALLBACK_VIRTUAL_MEMORY_KIB", "10485760")
        .output()
        .expect("run fallback guard fixture");
    assert_eq!(
        fallback.status.code(),
        Some(29),
        "preserve fallback exit status"
    );
    assert_eq!(fallback.stdout, b"10485760\n", "apply fallback ulimit");
    assert!(
        fallback.stderr.ends_with(b"fallback-err"),
        "preserve fallback stderr"
    );
    assert_eq!(
        fs::read_to_string(&calls)
            .expect("fallback call log")
            .lines()
            .count(),
        1,
        "an unavailable scope must probe once and execute only through the fallback",
    );

    fs::remove_dir_all(fixture).expect("remove guard fixture");
}

fn collect_workspace_paths(value: &Value, output: &mut BTreeSet<PathBuf>) {
    match value {
        Value::String(value) => {
            if let Some(relative) = value.strip_prefix("${workspace}/") {
                output.insert(PathBuf::from(relative));
            }
        }
        Value::Array(values) => {
            for value in values {
                collect_workspace_paths(value, output);
            }
        }
        Value::Table(values) => {
            for value in values.values() {
                collect_workspace_paths(value, output);
            }
        }
        Value::Integer(_) | Value::Float(_) | Value::Boolean(_) | Value::Datetime(_) => {}
    }
}
