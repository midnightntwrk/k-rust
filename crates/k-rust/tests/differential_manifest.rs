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
const EXECUTION_SCRIPT: &str =
    include_str!("../../../scripts/reference-non-imp-execution-differential.sh");
const PROOF_SCRIPT: &str = include_str!("../../../scripts/reference-proof-differential.sh");
const RPC_SCRIPT: &str = include_str!("../../../scripts/reference-rpc-differential.sh");
const MIR_EXECUTION_SCRIPT: &str =
    include_str!("../../../scripts/reference-mir-execution-differential.sh");
const SECTIONS: [&str; 5] = ["compile", "kast", "execution", "proof", "rpc"];
const JAVA_BACKED_DIFFERENTIAL_SCRIPTS: [&str; 6] = [
    COMPILE_SCRIPT,
    KAST_SCRIPT,
    EXECUTION_SCRIPT,
    PROOF_SCRIPT,
    RPC_SCRIPT,
    MIR_EXECUTION_SCRIPT,
];

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
fn java_backed_differentials_guard_the_whole_job_without_nested_sibling_scopes() {
    for script in JAVA_BACKED_DIFFERENTIAL_SCRIPTS {
        let source = script
            .find("source \"$workspace/scripts/reference-memory-guard.sh\"")
            .expect("every Java-backed differential must source the shared guard");
        let enter = script
            .find("reference_enter_whole_job \"$@\"")
            .expect("every Java-backed differential must enter one whole-job guard");
        assert!(
            source < enter,
            "the shared guard must be sourced before entering it",
        );
        assert!(
            enter
                < script
                    .find("source \"$workspace/scripts/reference-pins.sh\"")
                    .unwrap(),
            "the whole-job guard must be entered before manifest and pin processing",
        );
    }

    for script in [COMPILE_SCRIPT, KAST_SCRIPT] {
        assert!(
            script.contains("reference_memory_kib=${REFERENCE_DIFFERENTIAL_MEMORY_KIB:-}"),
            "the reference JVM must retain its independently optional virtual-memory ceiling",
        );
        assert_eq!(
            script
                .matches("reference_run_rust_frontend cargo run")
                .count(),
            1,
            "each frontend script must route its one Rust process through the aggregate-aware helper",
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
    let guard = fs::read_to_string(&guard_path).expect("shared whole-job memory guard");
    for contract in [
        "REFERENCE_DIFFERENTIAL_JOB_MEMORY_HIGH_KIB:-8388608",
        "REFERENCE_DIFFERENTIAL_JOB_MEMORY_MAX_KIB:-8388608",
        "REFERENCE_DIFFERENTIAL_JOB_FALLBACK_VIRTUAL_MEMORY_KIB:-12582912",
        "MemoryHigh=${reference_job_memory_high_kib}K",
        "MemoryMax=${reference_job_memory_max_kib}K",
        "MemorySwapMax=0",
        "ulimit -v \"$reference_job_fallback_virtual_memory_kib\"",
        // The virtual-address fallback must bound the reference JVM itself:
        // default ergonomics on a many-core host exceed the RLIMIT_AS ceiling.
        "if [[ -z \"${REFERENCE_DIFFERENTIAL_K_OPTS:-}\" ]]; then",
        "export REFERENCE_DIFFERENTIAL_K_OPTS='-Xmx2048m -Xss1m -XX:+UseSerialGC",
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
    let fixture_script = fixture.join("whole-job-fixture.sh");
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
    fs::write(
        &fixture_script,
        r#"#!/usr/bin/env bash
set -euo pipefail
source "$REFERENCE_GUARD_PATH"
reference_enter_whole_job "$@"
reference_run_rust_frontend bash -c '
  printf x >>"$PAYLOAD_RUNS"
  printf "%s\n" "$REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND"
  if [[ "$REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND" == rlimit-as ]]; then
    ulimit -v
  fi
  printf payload-err >&2
  exit "$PAYLOAD_STATUS"
'
"#,
    )
    .expect("write whole-job fixture");
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
    let payload_runs = fixture.join("payload-runs");
    let path = format!(
        "{}:{}",
        fixture.display(),
        std::env::var("PATH").expect("PATH")
    );

    let scoped = Command::new("bash")
        .arg(&fixture_script)
        .env("PATH", &path)
        .env("GUARD_CALLS", &calls)
        .env("PAYLOAD_RUNS", &payload_runs)
        .env("PAYLOAD_STATUS", "23")
        .env("REFERENCE_GUARD_PATH", &guard_path)
        .env("SYSTEMD_PROBE_STATUS", "0")
        .env_remove("REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND")
        .output()
        .expect("run scoped guard fixture");
    assert_eq!(
        scoped.status.code(),
        Some(23),
        "preserve whole-job scoped exit status"
    );
    assert_eq!(scoped.stdout, b"systemd-scope\n", "preserve scoped stdout",);
    assert_eq!(scoped.stderr, b"payload-err", "preserve scoped stderr");
    let scoped_calls = fs::read_to_string(&calls).expect("scoped call log");
    assert!(scoped_calls.contains("MemoryHigh=8388608K"));
    assert!(scoped_calls.contains("MemoryMax=8388608K"));
    assert!(scoped_calls.contains("MemorySwapMax=0"));
    assert_eq!(
        scoped_calls.lines().count(),
        2,
        "probe once and execute the whole job once without an inner sibling scope"
    );
    assert_eq!(
        fs::read_to_string(&payload_runs).expect("scoped payload runs"),
        "x",
        "a nonzero child must never be retried",
    );

    fs::write(&calls, "").expect("clear call log");
    fs::write(&payload_runs, "").expect("clear payload run log");
    let fallback = Command::new("bash")
        .arg(&fixture_script)
        .env("PATH", &path)
        .env("GUARD_CALLS", &calls)
        .env("PAYLOAD_RUNS", &payload_runs)
        .env("PAYLOAD_STATUS", "29")
        .env("REFERENCE_GUARD_PATH", &guard_path)
        .env("SYSTEMD_PROBE_STATUS", "1")
        .env(
            "REFERENCE_DIFFERENTIAL_JOB_FALLBACK_VIRTUAL_MEMORY_KIB",
            "10485760",
        )
        .env_remove("REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND")
        .output()
        .expect("run fallback guard fixture");
    assert_eq!(
        fallback.status.code(),
        Some(29),
        "preserve whole-job fallback exit status"
    );
    assert_eq!(
        fallback.stdout, b"rlimit-as\n10485760\n",
        "apply the fallback virtual-address limit to the entire job",
    );
    assert_eq!(
        fallback.stderr,
        b"warning: user systemd scopes unavailable; applying the 10485760 KiB whole-job virtual-address fallback (RLIMIT_AS), not a resident-memory limit\n\
          warning: bounding the reference JVM with REFERENCE_DIFFERENTIAL_K_OPTS=-Xmx2048m -Xss1m -XX:+UseSerialGC -XX:CompressedClassSpaceSize=128m -XX:MaxMetaspaceSize=256m -XX:ReservedCodeCacheSize=128m under the virtual-address fallback\n\
          payload-err",
        "identify the fallback semantics, bound the reference JVM, and otherwise preserve stderr exactly",
    );

    // A caller-provided JVM bound is respected: the fallback must neither
    // override it nor announce a default it did not apply.
    fs::write(&calls, "").expect("clear call log");
    fs::write(&payload_runs, "").expect("clear payload run log");
    let bounded = Command::new("bash")
        .arg(&fixture_script)
        .env("PATH", &path)
        .env("GUARD_CALLS", &calls)
        .env("PAYLOAD_RUNS", &payload_runs)
        .env("PAYLOAD_STATUS", "29")
        .env("REFERENCE_GUARD_PATH", &guard_path)
        .env("SYSTEMD_PROBE_STATUS", "1")
        .env(
            "REFERENCE_DIFFERENTIAL_JOB_FALLBACK_VIRTUAL_MEMORY_KIB",
            "10485760",
        )
        .env("REFERENCE_DIFFERENTIAL_K_OPTS", "-Xmx1g")
        .env_remove("REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND")
        .output()
        .expect("run fallback guard fixture with a caller-bounded JVM");
    assert_eq!(bounded.status.code(), Some(29));
    assert_eq!(
        bounded.stderr,
        b"warning: user systemd scopes unavailable; applying the 10485760 KiB whole-job virtual-address fallback (RLIMIT_AS), not a resident-memory limit\npayload-err",
        "a caller-provided REFERENCE_DIFFERENTIAL_K_OPTS is kept without a default announcement",
    );
    assert_eq!(
        fs::read_to_string(&calls)
            .expect("fallback call log")
            .lines()
            .count(),
        1,
        "an unavailable scope must probe once and execute only through the fallback",
    );
    assert_eq!(
        fs::read_to_string(&payload_runs).expect("fallback payload runs"),
        "x",
        "a nonzero fallback child must never be retried",
    );

    fs::write(&calls, "").expect("clear call log");
    fs::write(&payload_runs, "").expect("clear payload run log");
    let invalid = Command::new("bash")
        .arg(&fixture_script)
        .env("PATH", &path)
        .env("GUARD_CALLS", &calls)
        .env("PAYLOAD_RUNS", &payload_runs)
        .env("PAYLOAD_STATUS", "0")
        .env("REFERENCE_GUARD_PATH", &guard_path)
        .env("SYSTEMD_PROBE_STATUS", "0")
        .env("REFERENCE_DIFFERENTIAL_JOB_MEMORY_MAX_KIB", "eight-gib")
        .env_remove("REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND")
        .output()
        .expect("run invalid guard configuration");
    assert_eq!(invalid.status.code(), Some(2));
    assert_eq!(
        invalid.stderr,
        b"error: REFERENCE_DIFFERENTIAL_JOB_MEMORY_MAX_KIB must be a positive KiB integer\n",
    );
    assert_eq!(
        fs::read_to_string(&calls).expect("invalid call log"),
        "",
        "invalid configuration must fail before probing",
    );
    assert_eq!(
        fs::read_to_string(&payload_runs).expect("invalid payload runs"),
        "",
        "invalid configuration must fail before executing the job",
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
