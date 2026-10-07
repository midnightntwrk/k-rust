use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
    process::Command,
    time::{SystemTime, UNIX_EPOCH},
};

use toml::Value;

const MANIFEST: &str = include_str!("../../../scripts/reference-differential.toml");
const NORMALISATIONS: &str = include_str!("../../../scripts/reference-normalisations.toml");
const COMPILE_SCRIPT: &str = include_str!("../../../scripts/reference-differential.sh");
const KAST_SCRIPT: &str = include_str!("../../../scripts/reference-kast-differential.sh");
const EXECUTION_SCRIPT: &str =
    include_str!("../../../scripts/reference-non-imp-execution-differential.sh");
const PROOF_SCRIPT: &str = include_str!("../../../scripts/reference-proof-differential.sh");
const RPC_SCRIPT: &str = include_str!("../../../scripts/reference-rpc-differential.sh");
const MIR_EXECUTION_SCRIPT: &str =
    include_str!("../../../scripts/reference-mir-execution-differential.sh");
const SYMBOLIC_EXECUTION_SCRIPT_PATH: &str = "scripts/reference-symbolic-execution-differential.sh";
const DIFFERENTIAL_WORKFLOW: &str = include_str!("../../../.github/workflows/differential.yml");
const SECTIONS: [&str; 6] = ["compile", "kast", "execution", "proof", "rpc", "symbolic"];
const JAVA_BACKED_DIFFERENTIAL_SCRIPTS: [&str; 6] = [
    COMPILE_SCRIPT,
    KAST_SCRIPT,
    EXECUTION_SCRIPT,
    PROOF_SCRIPT,
    RPC_SCRIPT,
    MIR_EXECUTION_SCRIPT,
];

/// The command that starts at `start`: its line and every line a trailing backslash continues.
fn shell_command_at(script: &str, start: usize) -> &str {
    let mut end = start;
    loop {
        let line_end = script[end..]
            .find('\n')
            .map_or(script.len(), |offset| end + offset);
        if !script[end..line_end].trim_end().ends_with('\\') || line_end == script.len() {
            return &script[start..line_end];
        }
        end = line_end + 1;
    }
}

/// The kompile invariant checkers exist in a release binary only under the
/// `kompile-invariant-checks` feature, so every gate that builds or runs `krust` must pass the
/// gate cargo arguments of `reference-memory-guard.sh`: the feature, and a target directory of
/// its own so the checked binary never replaces the `target/release/krust` that
/// `scripts/benchmark.sh` measures. A gate that builds `krust` executes the binary those
/// arguments write, never one under `CARGO_TARGET_DIR`.
#[test]
fn every_gate_builds_krust_with_the_gate_cargo_arguments() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let guard = fs::read_to_string(workspace.join("scripts/reference-memory-guard.sh"))
        .expect("read the memory guard");
    assert!(guard.contains("krust_gate_cargo_args+=(--features kompile-invariant-checks)"));
    assert!(guard.contains("/target/gates\"}"));
    for script in [
        "scripts/conformance-ratchet.sh",
        "scripts/reference-differential.sh",
        "scripts/reference-kast-differential.sh",
        "scripts/reference-non-imp-execution-differential.sh",
        "scripts/reference-proof-differential.sh",
        "scripts/reference-rpc-differential.sh",
        "scripts/reference-mir-execution-differential.sh",
        SYMBOLIC_EXECUTION_SCRIPT_PATH,
    ] {
        let text = fs::read_to_string(workspace.join(script)).expect("read gate script");
        let mut krust_commands = 0;
        for subcommand in ["cargo run ", "cargo build "] {
            for (start, _) in text.match_indices(subcommand) {
                let command = shell_command_at(&text, start);
                if !command.contains("--bin krust") {
                    continue;
                }
                krust_commands += 1;
                assert!(
                    command.contains("--release \"${krust_gate_cargo_args[@]}\""),
                    "{script} builds krust without the gate cargo arguments:\n{command}"
                );
                if subcommand == "cargo build " {
                    assert!(
                        text.contains("$krust_gate_binary"),
                        "{script} builds the gate krust but does not execute it"
                    );
                }
            }
        }
        assert!(krust_commands > 0, "{script} no longer builds krust");
        assert!(
            !text.contains("/release/krust"),
            "{script} executes a krust outside the gate target directory"
        );
    }
}

/// `KRUST_GATE_Z3` selects how Z3 is acquired for every Rust build a gate makes, so the
/// comparator builds carry the guard's Z3 arguments as the krust builds do (through
/// `krust_gate_cargo_args`, checked above): `reference_build_comparator` receives
/// `krust_gate_z3_args` or the whole `krust_gate_cargo_args`, and a direct `cargo test` names
/// `krust_gate_z3_args`.
#[test]
fn every_gate_builds_the_comparator_with_the_gate_z3_selection() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut comparator_builds = 0;
    for script in [
        "scripts/conformance-ratchet.sh",
        "scripts/reference-differential.sh",
        "scripts/reference-kast-differential.sh",
        "scripts/reference-non-imp-execution-differential.sh",
        "scripts/reference-proof-differential.sh",
        "scripts/reference-rpc-differential.sh",
        "scripts/reference-mir-execution-differential.sh",
        SYMBOLIC_EXECUTION_SCRIPT_PATH,
    ] {
        let text = fs::read_to_string(workspace.join(script)).expect("read gate script");
        for needle in ["reference_build_comparator \"$workspace\"", "cargo test "] {
            for (start, _) in text.match_indices(needle) {
                let command = shell_command_at(&text, start);
                comparator_builds += 1;
                assert!(
                    command.contains("\"${krust_gate_z3_args[@]}\"")
                        || command.contains("\"${krust_gate_cargo_args[@]}\""),
                    "{script} builds the comparator without the gate's Z3 selection:\n{command}"
                );
            }
        }
    }
    assert!(
        comparator_builds >= 6,
        "the gates no longer build the comparator"
    );
}

/// Every reference tool a gate runs for its results (kompile, krun, kprove, kast, kore-exec,
/// kore-parser) goes through the reference-output cache (`scripts/reference-cache.sh`), which
/// keys each call on what its result depends on, and each gate opens the cache after its pin
/// checks and closes it with the summary that fails on a verify mismatch. The RPC server sessions
/// stay outside it: the RPC gate's oracle session (the whole session, both servers and every
/// request included, costs under two CPU seconds) and the execution gate's one-request reference
/// simplifier session (N41).
#[test]
fn every_reference_tool_call_of_a_gate_goes_through_the_cache() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let symbolic = fs::read_to_string(workspace.join(SYMBOLIC_EXECUTION_SCRIPT_PATH))
        .expect("symbolic differential script");
    let tools = [
        "\"$kompile\"",
        "\"$krun\"",
        "\"$kprove\"",
        "\"$kast\"",
        "\"$kore_exec\"",
        "\"$kore_parser\"",
    ];
    let mut cached_calls = 0;
    for script in JAVA_BACKED_DIFFERENTIAL_SCRIPTS
        .iter()
        .copied()
        .chain([symbolic.as_str()])
    {
        let name = script
            .lines()
            .rev()
            .find(|line| line.contains(" passed\""))
            .unwrap_or_default();
        for needle in [
            "source \"$workspace/scripts/reference-cache.sh\"",
            "reference_cache_begin \"$work\"",
            "reference_cache_finish",
        ] {
            assert!(script.contains(needle), "gate without {needle}: {name}");
        }
        let lines = script.lines().collect::<Vec<_>>();
        for (index, line) in lines.iter().enumerate() {
            let call = line.trim_start();
            if !tools.iter().any(|tool| call.starts_with(tool)) {
                continue;
            }
            let mut start = index;
            while start > 0 && lines[start - 1].trim_end().ends_with('\\') {
                start -= 1;
            }
            assert!(
                lines[start..=index]
                    .iter()
                    .any(|line| line.contains("reference_cached ")),
                "a gate runs a reference tool outside the cache:\n{}",
                lines[start..=index].join("\n")
            );
            cached_calls += 1;
        }
    }
    assert!(
        cached_calls >= 20,
        "only {cached_calls} reference calls found"
    );
}

/// Run `script` (case arguments `cases`) against fake reference tools and a fake `cargo` that
/// records its arguments, with `KRUST_GATE_Z3` set to `selection` (unset for `None`); returns the
/// exit status, the recorded cargo argument lines and the standard error.
fn gate_cargo_calls(
    script: &str,
    cases: &[&str],
    selection: Option<&str>,
) -> (Option<i32>, Vec<String>, String) {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let fixture = environment_fixture("gate-z3");
    let k_checkout = fake_k_checkout(&fixture, &[]);
    let calls = fixture.join("calls");
    let cargo_calls = fixture.join("cargo-calls");
    for tool in ["kompile", "kore-parser", "kore-exec", "krun", "kmir-python"] {
        let prologue = match tool {
            "kompile" => FAKE_KOMPILE_PROLOGUE,
            "kmir-python" => ": >\"$4\"\n",
            _ => "",
        };
        write_environment_probe(&fixture.join(tool), tool, prologue);
    }
    let target = fake_gate_rust_toolchain(&fixture, "", "");
    let comparator = fixture.join("comparator");
    write_environment_probe(
        &fixture.join("cargo"),
        "cargo",
        &format!(
            r#"
printf '%s\n' "$*" >>{cargo_calls:?}
if [[ "$1" == test && " $* " == *" --no-run "* ]]; then
  printf '{{"reason":"compiler-artifact","target":{{"name":"reference_differential"}},"profile":{{"test":true}},"executable":"%s"}}\n' {comparator:?}
fi
"#
        ),
    );
    let mir_checkout = fixture.join("mir-semantics");
    for pinned in [
        "kmir/src/kmir/kdist/mir-semantics/kmir.md",
        "kmir/src/tests/integration/data/exec-smir/main-a-b-c/main-a-b-c.smir.json",
    ] {
        let path = mir_checkout.join(pinned);
        fs::create_dir_all(path.parent().unwrap()).expect("create fake MIR checkout");
        fs::write(path, "").expect("write fake MIR input");
    }
    let path = format!(
        "{}:{}",
        fixture.display(),
        std::env::var("PATH").expect("PATH")
    );
    let mut command = Command::new("bash");
    command
        .arg(workspace.join(script))
        .args(cases)
        .env("PATH", &path)
        .env("ENVIRONMENT_CALLS", &calls)
        .env("K_CHECKOUT", &k_checkout)
        .env("K_KOMPILE", fixture.join("kompile"))
        .env("K_KORE_PARSER", fixture.join("kore-parser"))
        .env("K_KORE_EXEC", fixture.join("kore-exec"))
        .env("K_KRUN", fixture.join("krun"))
        .env("KMIR_PYTHON", fixture.join("kmir-python"))
        .env("MIR_SEMANTICS_CHECKOUT", &mir_checkout)
        .env("KRUST_GATE_TARGET_DIR", &target)
        .env("REFERENCE_DIFFERENTIAL_ALLOW_UNPINNED", "1")
        .env("REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND", "rlimit-as");
    match selection {
        Some(value) => command.env("KRUST_GATE_Z3", value),
        None => command.env_remove("KRUST_GATE_Z3"),
    };
    let output = command.output().expect("run gate fixture");
    let recorded = fs::read_to_string(&cargo_calls)
        .unwrap_or_default()
        .lines()
        .map(str::to_owned)
        .collect();
    fs::remove_dir_all(fixture).expect("remove gate fixture");
    (
        output.status.code(),
        recorded,
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

/// `KRUST_GATE_Z3=system` gives every cargo call of a gate `--no-default-features --features
/// cli`, the default features without z3-sys's release download; unset, the gates build Cargo's
/// default features as CI does; any other value is refused before any build.
#[test]
fn gate_cargo_calls_follow_the_z3_selection() {
    for (script, cases, calls) in [
        (SYMBOLIC_EXECUTION_SCRIPT_PATH, &["symbolic-owise"][..], 2),
        (
            "scripts/reference-mir-execution-differential.sh",
            &[][..],
            3,
        ),
    ] {
        let (status, system, stderr) = gate_cargo_calls(script, cases, Some("system"));
        assert_eq!(
            status,
            Some(0),
            "{script} with KRUST_GATE_Z3=system: {stderr}"
        );
        assert_eq!(system.len(), calls, "{script}: {system:#?}");
        for call in &system {
            assert_eq!(
                call.matches("--no-default-features --features cli").count(),
                1,
                "{script} cargo call without the system Z3 selection: {call}"
            );
        }

        for selection in [None, Some("gh-release")] {
            let (status, default, stderr) = gate_cargo_calls(script, cases, selection);
            assert_eq!(status, Some(0), "{script} with {selection:?}: {stderr}");
            assert_eq!(default.len(), calls, "{script}: {default:#?}");
            for call in &default {
                assert!(
                    !call.contains("--no-default-features"),
                    "{script} with {selection:?} must build the default features: {call}"
                );
            }
        }

        let (status, rejected, stderr) = gate_cargo_calls(script, cases, Some("download"));
        assert_eq!(status, Some(2), "{script}: {stderr}");
        assert!(
            stderr.contains("KRUST_GATE_Z3 must be gh-release or system"),
            "{script}: {stderr}"
        );
        assert!(
            rejected.is_empty(),
            "{script} built before refusing: {rejected:#?}"
        );
    }
}

#[test]
fn differential_manifest_schema_is_complete() {
    let manifest = MANIFEST.parse::<Value>().expect("valid differential TOML");
    assert!(
        manifest["normalisations"].get("ignore_unique_id").is_none(),
        "compile comparison must not globally ignore UNIQUE_ID"
    );

    let allowed_pairings = BTreeSet::from(["kore/llvm", "haskell/rust"]);
    for entry in manifest["compile"].as_array().expect("compile cases") {
        let name = entry["name"].as_str().expect("compile name");
        let pairings = entry
            .get("pairings")
            .and_then(Value::as_array)
            .map(|values| values.as_slice())
            .unwrap_or(&[]);
        let effective_pairings = if pairings.is_empty() {
            vec!["kore/llvm", "haskell/rust"]
        } else {
            pairings
                .iter()
                .map(|value| value.as_str().expect("pairing string"))
                .collect()
        };
        assert!(!effective_pairings.is_empty(), "{name} has no pairing");
        for pairing in &effective_pairings {
            assert!(
                allowed_pairings.contains(pairing),
                "unknown pairing {pairing} on {name}"
            );
        }
        let expect = entry
            .get("expect")
            .and_then(Value::as_str)
            .unwrap_or("accept");
        assert!(matches!(expect, "accept" | "reject" | "port-accepts"));
        let reason = entry.get("reason").and_then(Value::as_str);
        if expect == "port-accepts" {
            assert!(
                reason.is_some_and(|reason| !reason.trim().is_empty()),
                "port-accepts case {name} must state why k-rust accepts what the reference rejects"
            );
            assert!(
                entry
                    .get("reference-error")
                    .and_then(Value::as_str)
                    .is_some_and(|diagnostic| !diagnostic.trim().is_empty()),
                "port-accepts case {name} must pin the reference diagnostic it diverges on"
            );
            assert!(
                entry
                    .get("comparisons")
                    .and_then(Value::as_array)
                    .is_none_or(Vec::is_empty),
                "port-accepts case {name} has no reference artifact to compare"
            );
            continue;
        }
        assert!(
            entry.get("reason").is_none(),
            "reason on {expect} case {name} is only read for port-accepts"
        );
        assert!(
            entry.get("reference-error").is_none(),
            "reference-error on {expect} case {name} is only read for port-accepts"
        );
        if expect == "reject" {
            assert!(
                entry
                    .get("comparisons")
                    .and_then(Value::as_array)
                    .is_none_or(Vec::is_empty),
                "reject case {name} must not compare artifacts"
            );
            continue;
        }
        assert!(
            entry.get("unique-id-divergence-ceilings").is_none(),
            "strict UNIQUE_ID parity makes the old ceiling on {name} obsolete"
        );
    }

    for required in [
        "fresh-name-collision",
        "concrete-rw2",
        "parametric",
        "assoc-strict",
        "exists-anon",
        "undefined-sort",
        "cast-inner",
        "let-list-binder",
    ] {
        assert!(
            manifest["compile"]
                .as_array()
                .unwrap()
                .iter()
                .any(|entry| entry["name"].as_str() == Some(required)),
            "missing designed compile case {required}"
        );
    }

    let compile_case = |name: &str| {
        manifest["compile"]
            .as_array()
            .expect("compile cases")
            .iter()
            .find(|entry| entry["name"].as_str() == Some(name))
            .unwrap_or_else(|| panic!("missing compile case {name}"))
    };
    assert_eq!(
        compile_case("exists-anon")["pairings"]
            .as_array()
            .expect("exists-anon pairings")
            .iter()
            .map(|pairing| pairing.as_str().expect("pairing string"))
            .collect::<Vec<_>>(),
        ["haskell/rust"],
        "K accepts an anonymous binder in requires only for its Haskell backend",
    );
    assert!(
        compile_case("assoc-strict")["requires"]
            .as_array()
            .expect("assoc-strict requirements")
            .iter()
            .all(|requirement| requirement.as_str() == Some("reference-toolchain")),
        "assoc-strict must run in the default protocol when the reference toolchain is available",
    );
}

#[test]
fn differential_special_case_schema_is_complete() {
    let manifest = MANIFEST.parse::<Value>().expect("valid differential TOML");
    let case = |section: &str, name: &str| {
        manifest[section]
            .as_array()
            .unwrap_or_else(|| panic!("missing {section} section"))
            .iter()
            .find(|entry| entry["name"].as_str() == Some(name))
            .unwrap_or_else(|| panic!("missing {section} case {name}"))
            .clone()
    };
    // The three symbolic collection and injection cases compare one rewrite step against kore-exec. The reference's
    // `--depth N` output lists the leaves that are stuck within N steps and drops the leaves that
    // merely reached the limit whenever a stuck leaf exists (GraphTraversal.checkLeftUnproven:
    // GotStuck wins over Stopped), so `--depth 1` prints only the unrewritten remainder and the
    // rewritten branches are observable from `--depth 2` on.
    for name in [
        "symbolic-collection-frames",
        "collection-and-injection-narrowing",
        "injected-variable-narrowing",
    ] {
        let entry = case("symbolic", name);
        for pattern in entry["pattern"].as_array().expect("symbolic patterns") {
            assert_eq!(
                pattern["depth"].as_integer(),
                Some(2),
                "{name}:{} must pin the depth at which kore-exec prints the stuck rewritten branches",
                pattern["name"].as_str().unwrap_or("?")
            );
            assert_eq!(pattern["mode"].as_str(), Some("exec"));
        }
    }
    for entry in manifest["proof"].as_array().expect("proof cases") {
        let name = entry["name"].as_str().expect("proof name");
        assert!(
            entry["claims"].as_array().is_some(),
            "{name} claims must be an array"
        );
        assert!(
            entry["failure-claim"]
                .as_str()
                .is_some_and(|claim| !claim.trim().is_empty()),
            "{name} must declare a failure claim"
        );
        let verdict = entry
            .get("failure-verdict")
            .map(|verdict| verdict.as_str().expect("failure-verdict string"))
            .unwrap_or("disproved");
        let reason = entry
            .get("failure-verdict-reason")
            .map(|reason| reason.as_str().expect("failure-verdict-reason string"));
        match verdict {
            "disproved" => assert!(
                reason.is_none(),
                "{name} gives a failure-verdict-reason for the default disproved verdict"
            ),
            "failed" => assert!(
                reason.is_some_and(|reason| !reason.trim().is_empty()),
                "{name} expects failed and must say why its failure claim is not refuted"
            ),
            other => panic!("{name} has unknown failure-verdict {other}"),
        }
    }
    // TRIVIAL-SPEC.ct2 starts from `t1`, which `rule t1 => t2 ensures false` makes empty: the
    // claim is vacuous, so the gate must not demand a refutation for it.
    assert_eq!(
        case("proof", "trivial-proof")["failure-verdict"].as_str(),
        Some("failed")
    );
    assert!(
        PROOF_SCRIPT.contains(r#".["failure-verdict"] // "disproved""#),
        "the proof gate must read each case's expected failure verdict"
    );

    for name in ["imp", "bounded-search", "trivial-result-rpc"] {
        let entry = manifest["rpc"]
            .as_array()
            .unwrap()
            .iter()
            .find(|entry| entry["name"].as_str() == Some(name))
            .unwrap_or_else(|| panic!("missing RPC case {name}"));
        assert_eq!(entry["oracle"].as_str(), Some("kore-rpc-booster"));
        if name == "trivial-result-rpc" {
            assert_eq!(
                entry["state-depth"].as_integer(),
                Some(0),
                "the trivial-result RPC probe must send the initial state, not Kore's post-step bottom",
            );
        }
    }

    let exit = manifest["execution"]
        .as_array()
        .expect("execution cases")
        .iter()
        .find(|entry| entry["name"].as_str() == Some("exit"))
        .expect("nonzero exit-code execution case");
    assert_eq!(exit["exit-code"].as_integer(), Some(7));

    let hook_exceptions = manifest["execution"]
        .as_array()
        .unwrap()
        .iter()
        .flat_map(|entry| {
            entry
                .get("oracle-exception")
                .and_then(Value::as_array)
                .into_iter()
                .flatten()
        })
        .collect::<Vec<_>>();
    assert_eq!(
        hook_exceptions.len(),
        2,
        "STRING.find and BYTES.replaceAt exceptions"
    );
    for exception in hook_exceptions {
        for field in ["program", "expected", "reference", "reason"] {
            assert!(
                exception[field]
                    .as_str()
                    .is_some_and(|value| !value.trim().is_empty()),
                "execution oracle exception lacks {field}"
            );
        }
        assert_ne!(exception["expected"], exception["reference"]);
    }

    let rpc_exceptions = manifest["rpc"]
        .as_array()
        .unwrap()
        .iter()
        .flat_map(|entry| {
            entry
                .get("oracle-exception")
                .and_then(Value::as_array)
                .into_iter()
                .flatten()
                .map(move |exception| (entry, exception))
        })
        .collect::<Vec<_>>();
    let mut adjudicated = rpc_exceptions
        .iter()
        .map(|(entry, exception)| {
            (
                entry["name"].as_str().unwrap_or_default(),
                exception["response"].as_str().unwrap_or_default(),
            )
        })
        .collect::<Vec<_>>();
    adjudicated.sort_unstable();
    assert_eq!(
        adjudicated,
        [
            ("bounded-search", "implies-consequent-universal"),
            ("bounded-search", "model-unsat"),
            ("imp", "implies"),
            ("trivial-result-rpc", "execute-trivial-configuration"),
        ],
        "the IMP implication payload, the consequent-only universal, the constructor-distinct model query and the trivial-rule result are the adjudicated RPC differences",
    );
    for (entry, exception) in rpc_exceptions {
        let name = entry["name"].as_str().unwrap_or_default();
        assert!(
            entry["responses"]
                .as_array()
                .is_some_and(|responses| responses.contains(&exception["response"])),
            "RPC oracle exception on {name} names a response its case does not request",
        );
        for field in ["oracle", "response", "expected", "reference", "reason"] {
            assert!(
                exception[field]
                    .as_str()
                    .is_some_and(|value| !value.trim().is_empty()),
                "RPC oracle exception on {name} lacks {field}"
            );
        }
        assert_ne!(exception["expected"], exception["reference"]);
        assert_eq!(exception["oracle"].as_str(), Some("kore-rpc-booster"));
        if exception["response"].as_str() == Some("implies") {
            // N19: the payload is claimed equal to the oracle's, so the gate must check that claim
            // by simplifying both payloads instead of pinning only the port's response.
            assert_eq!(
                exception["equivalence"].as_str(),
                Some("simplified-implication"),
                "the IMP implication exception must declare the equivalence the gate checks"
            );
        }
    }
    for needle in [
        "compare_simplified_implication",
        "simplified-implication",
        "kore-simplify",
    ] {
        assert!(RPC_SCRIPT.contains(needle), "RPC gate lacks {needle}");
    }
    let trivial_rpc = manifest["rpc"]
        .as_array()
        .unwrap()
        .iter()
        .find(|entry| entry["name"].as_str() == Some("trivial-result-rpc"))
        .expect("trivial-result RPC case");
    assert!(
        trivial_rpc["configuration-state"]
            .as_str()
            .is_some_and(|path| path.ends_with("rpc/trivial-result-configuration.json")),
        "the excluded trivial-rule response must send an evaluated configuration Booster rewrites itself",
    );
    assert!(
        trivial_rpc["oracle-exception"][0]["reason"]
            .as_str()
            .is_some_and(|reason| reason.starts_with("docs/compatibility.md#trivial-rule-results")),
        "the trivial-rule exception must cite its compatibility decision",
    );

    for entry in manifest["symbolic"].as_array().expect("symbolic cases") {
        let name = entry["name"].as_str().expect("symbolic name");
        assert!(matches!(
            entry["definition"].as_str(),
            Some("reference" | "rust" | "both")
        ));
        let patterns = entry["pattern"].as_array().expect("symbolic patterns");
        assert!(!patterns.is_empty(), "symbolic case {name} has no patterns");
        for pattern in patterns {
            let mode = pattern["mode"].as_str().expect("symbolic mode");
            assert!(matches!(
                mode,
                "exec"
                    | "search-final"
                    | "search-all"
                    | "search-one-step"
                    | "search-one-or-more-steps"
            ));
            if pattern["oracle-exclusion"].as_str() == Some("gotstuck") {
                assert_eq!(mode, "exec");
                assert!(pattern["depth"].as_integer().is_some());
            }
        }
    }
}

#[test]
fn compile_comparison_requires_strict_unique_id_parity() {
    let manifest = MANIFEST.parse::<Value>().expect("valid differential TOML");
    assert!(
        manifest["compile"]
            .as_array()
            .expect("compile cases")
            .iter()
            .all(|entry| entry.get("unique-id-divergence-ceilings").is_none())
    );
}

#[test]
fn differential_gate_scripts_wire_the_runtime_contract() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let symbolic = fs::read_to_string(workspace.join(SYMBOLIC_EXECUTION_SCRIPT_PATH))
        .expect("symbolic differential script");

    for script in [
        COMPILE_SCRIPT,
        KAST_SCRIPT,
        EXECUTION_SCRIPT,
        PROOF_SCRIPT,
        RPC_SCRIPT,
        &symbolic,
    ] {
        assert!(script.contains("reference-manifest.py"));
        assert!(script.contains("reference_require_k_version"));
        assert!(script.contains("reference_require_git_pin"));
        assert!(script.contains("semantics-support"));
    }
    for needle in [
        "REFERENCE_DIFFERENTIAL_PAIRINGS",
        "haskell/rust",
        "kore/llvm",
        "kore_parser",
        "verifying reference definition.kore",
        "verifying k-rust definition.kore",
    ] {
        assert!(
            COMPILE_SCRIPT.contains(needle),
            "compile gate lacks {needle}"
        );
    }
    for obsolete in [
        "K_DIFFERENTIAL_IGNORE_UNIQUE_ID",
        "ignore_unique_id_ticket",
        "unique-id-divergence-ceilings",
    ] {
        assert!(
            !COMPILE_SCRIPT.contains(obsolete),
            "compile comparison must reject the general UNIQUE_ID escape hatch: {obsolete}"
        );
    }
    for script in [EXECUTION_SCRIPT, MIR_EXECUTION_SCRIPT, &symbolic] {
        assert!(script.contains("K_DIFFERENTIAL_DEFINITION"));
        assert!(script.contains("K_DIFFERENTIAL_MODULE"));
    }
    // N4: the symbolic and MIR gates start from a pattern file, so the comparator can tell the
    // initial pattern's variables from the engine-chosen rule and remainder names.
    for script in [MIR_EXECUTION_SCRIPT, &symbolic] {
        assert!(
            script.contains("K_DIFFERENTIAL_INITIAL_PATTERN="),
            "pattern-driven execution gates must hand the initial pattern to the comparator"
        );
    }
    assert!(EXECUTION_SCRIPT.contains("oracle-exception"));
    assert!(EXECUTION_SCRIPT.contains("expected_exit_code"));
    assert!(EXECUTION_SCRIPT.contains("rust_status != expected_exit_code"));
    assert!(PROOF_SCRIPT.contains("if ((${#proven_claims[@]})); then"));
    for needle in [
        "--no-smt",
        "rpc_flavour",
        "REFERENCE_RPC_ORACLE",
        "oracle-exception",
        "configuration-state",
        "execute-trivial-configuration",
    ] {
        assert!(RPC_SCRIPT.contains(needle), "RPC gate lacks {needle}");
    }
    for needle in ["kore-exec", "--stop-leaves", "gotstuck", "--searchType"] {
        assert!(symbolic.contains(needle), "symbolic gate lacks {needle}");
    }
}

/// Every `krust krun` invocation of the execution gate, from `krun "$source"` to the redirect
/// that captures its output.
fn execution_gate_krust_krun_invocations(script: &str) -> Vec<&str> {
    script
        .match_indices("krun \"$source\"")
        .map(|(start, _)| {
            let rest = &script[start..];
            let end = rest
                .find(">\"$work/")
                .expect("krust krun invocation redirects its output under $work");
            &rest[..end]
        })
        .collect()
}

/// The execution gate pairs krust with the reference Haskell backend: `kompile --backend
/// haskell`, then the reference `krun`, which runs kore-exec in its default `--strategy all`
/// and prints every successor of a branching configuration (branching-execution: `rule a => b` and
/// `rule a => c` give `\or(b, c)` at depth 1). Plain `krust krun` follows one successor per
/// step (`--strategy any`; docs/compatibility.md#search-results), so a Haskell-paired execution
/// comparison must ask krust for the Haskell-equivalent branching: the krust side of every
/// `[[execution]]` program and search passes `--strategy all`, and the reference side keeps
/// kore-exec's default. The `[[execution.any]]` rows are the one exception: krust keeps its
/// krun default there and the comparator checks membership in the reference set (N26,
/// `K_DIFFERENTIAL_STRATEGY=any`).
#[test]
fn execution_gate_asks_krust_for_the_haskell_backend_branching_strategy() {
    assert!(
        EXECUTION_SCRIPT.contains("--backend haskell"),
        "the execution gate compiles the reference definition with the Haskell backend"
    );
    let invocations = execution_gate_krust_krun_invocations(EXECUTION_SCRIPT);
    let [programs, searches, any_runs] = invocations.as_slice() else {
        panic!(
            "one krust krun invocation each for the programs, the searches, and the any runs: {invocations:#?}"
        );
    };
    for invocation in [programs, searches] {
        assert!(
            invocation.contains("--strategy all"),
            "a Haskell-paired krust krun must explore every applicable rule:\n{invocation}"
        );
    }
    assert!(
        programs.contains("--io off"),
        "ordinary all-strategy execution must buffer I/O instead of selecting live output from alternatives:\n{programs}"
    );
    assert!(
        !any_runs.contains("--strategy"),
        "an [[execution.any]] run keeps krust's krun default:\n{any_runs}"
    );
    let any_loop = &EXECUTION_SCRIPT[EXECUTION_SCRIPT
        .find(any_runs)
        .expect("the any run is part of the script")..];
    let any_comparison = any_loop
        .find("compare_execution_any ")
        .expect("the any run is compared through compare_execution_any");
    assert!(
        !any_loop[..any_comparison].contains("compare_execution "),
        "the any run must not reach the exact comparator"
    );
    assert!(
        EXECUTION_SCRIPT.contains("K_DIFFERENTIAL_STRATEGY=any \\\n"),
        "compare_execution_any selects the N26 membership comparator"
    );
    let reference_invocations = EXECUTION_SCRIPT
        .split("run_reference_krun ")
        .skip(1)
        .map(|call| {
            let end = call
                .find("--output kore")
                .expect("reference krun invocation ends with --output kore");
            &call[..end]
        })
        .collect::<Vec<_>>();
    assert_eq!(
        reference_invocations.len(),
        3,
        "one reference krun invocation each for the programs, the searches, and the any runs"
    );
    for invocation in reference_invocations {
        assert!(
            !invocation.contains("--strategy"),
            "the reference krun keeps kore-exec's default strategy:\n{invocation}"
        );
    }
}

/// The I/O mode and the standard input are part of the initial configuration of a definition
/// that declares `$IO` or `$STDIN`, so the two sides of an execution comparison are comparable
/// only from the same values, and with real I/O a result would depend on the process's
/// streams. Every run of the execution gate, program, search and any alike, therefore gives
/// both krust and the reference krun `--io off` and an empty standard input (`</dev/null`).
#[test]
fn execution_gate_runs_both_sides_with_io_off_on_empty_input() {
    let krust_invocations = execution_gate_krust_krun_invocations(EXECUTION_SCRIPT);
    assert_eq!(
        krust_invocations.len(),
        3,
        "one krust krun invocation each for the programs, the searches, and the any runs"
    );
    for invocation in krust_invocations {
        assert!(
            invocation.contains("--io off") && invocation.trim_end().ends_with("</dev/null"),
            "a krust run of the execution gate must start with I/O off on empty input:\n{invocation}"
        );
    }
    let reference_invocations = EXECUTION_SCRIPT
        .split("run_reference_krun ")
        .skip(1)
        .filter_map(|call| {
            let end = call.find("--output kore")?;
            let rest = &call[end + "--output kore".len()..];
            Some((&call[..end], rest.lines().next().unwrap_or_default()))
        })
        .collect::<Vec<_>>();
    assert_eq!(
        reference_invocations.len(),
        3,
        "one reference krun invocation each for the programs, the searches, and the any runs"
    );
    for (invocation, redirection) in reference_invocations {
        assert!(
            invocation.contains("--io off") && redirection.trim() == "</dev/null",
            "a reference run of the execution gate must start with I/O off on empty input:\n{invocation}--output kore{redirection}"
        );
    }
}

#[test]
fn every_gate_rejects_unknown_cases_before_validating_reference_tools() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let missing = environment_fixture("missing-reference-tools").join("kompile");
    for (script, supported) in [
        ("scripts/reference-differential.sh", "append"),
        ("scripts/reference-kast-differential.sh", "imp"),
        (
            "scripts/reference-non-imp-execution-differential.sh",
            "collections",
        ),
        ("scripts/reference-proof-differential.sh", "mini-proof"),
        ("scripts/reference-rpc-differential.sh", "imp"),
        (SYMBOLIC_EXECUTION_SCRIPT_PATH, "symbolic-depth-bound"),
    ] {
        for (case, diagnostic) in [
            ("unknown-fixture-case", "error: unknown"),
            (supported, "error: set K_KOMPILE"),
        ] {
            let output = Command::new("bash")
                .arg(workspace.join(script))
                .arg(case)
                .env("K_KOMPILE", &missing)
                .env("REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND", "rlimit-as")
                .output()
                .expect("run gate preflight");
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert_eq!(output.status.code(), Some(2), "{script}: {stderr}");
            assert!(stderr.contains(diagnostic), "{script}: {stderr}");
            assert!(!String::from_utf8_lossy(&output.stdout).contains("corpus passed"));
        }
    }
    fs::remove_dir_all(missing.parent().unwrap()).unwrap();
}

#[test]
fn differential_manifest_rejects_prerequisites_the_gates_cannot_enforce() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let fixture = environment_fixture("manifest-prerequisites");
    let helper = fixture.join("reference-manifest.py");
    fs::copy(workspace.join("scripts/reference-manifest.py"), &helper).unwrap();
    for (requirements, valid) in [
        (r#"["reference-toolchain"]"#, true),
        (r#"["reference-toolchain", "semantics-support"]"#, true),
        (
            r#"["reference-toolchain", "ticket:historical-owner"]"#,
            false,
        ),
        (r#"["unknown-capability"]"#, false),
        (r#"[]"#, false),
        (r#""reference-toolchain""#, false),
    ] {
        fs::write(
            fixture.join("reference-differential.toml"),
            format!("[[compile]]\nname = \"fixture\"\nrequires = {requirements}\n"),
        )
        .unwrap();
        for args in [vec![], vec!["--validate"]] {
            let output = Command::new("python3")
                .arg(&helper)
                .args(args)
                .output()
                .unwrap();
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert_eq!(
                output.status.code(),
                Some(if valid { 0 } else { 2 }),
                "{requirements}: {stderr}"
            );
            if !valid {
                assert!(
                    output.stdout.is_empty(),
                    "invalid prerequisites must not reach gates"
                );
                assert!(stderr.contains("invalid differential manifest"), "{stderr}");
            }
        }
    }
    fs::remove_dir_all(fixture).unwrap();
}

/// N42: options that change the reference definition an execution case compares against are
/// sound only for programs that cannot reach what they change, so each case that carries them
/// states why (`reference-kompile-options-reason`); only the execution gate reads them.
#[test]
fn reference_kompile_options_need_a_reason_and_an_execution_case() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let fixture = environment_fixture("manifest-reference-options");
    let helper = fixture.join("reference-manifest.py");
    fs::copy(workspace.join("scripts/reference-manifest.py"), &helper).unwrap();
    let case = |section: &str, extra: &str| {
        format!("[[{section}]]\nname = \"fixture\"\nrequires = [\"reference-toolchain\"]\n{extra}")
    };
    let reason = "reference-kompile-options-reason = \"no program reaches the removed rule\"\n";
    for (manifest, valid) in [
        (case("execution", ""), true),
        (
            case(
                "execution",
                &format!("reference-kompile-options = [\"--allow-anywhere-haskell\"]\n{reason}"),
            ),
            true,
        ),
        (
            case(
                "execution",
                "reference-kompile-options = [\"--allow-anywhere-haskell\"]\n",
            ),
            false,
        ),
        (
            case(
                "execution",
                "reference-kompile-options = [\"--allow-anywhere-haskell\"]\nreference-kompile-options-reason = \" \"\n",
            ),
            false,
        ),
        (case("execution", reason), false),
        (
            case(
                "execution",
                &format!("reference-kompile-options = []\n{reason}"),
            ),
            false,
        ),
        (
            case(
                "execution",
                &format!("reference-kompile-options = [\"allow-anywhere-haskell\"]\n{reason}"),
            ),
            false,
        ),
        (
            case(
                "compile",
                &format!("reference-kompile-options = [\"--allow-anywhere-haskell\"]\n{reason}"),
            ),
            false,
        ),
    ] {
        fs::write(fixture.join("reference-differential.toml"), &manifest).unwrap();
        let output = Command::new("python3")
            .arg(&helper)
            .arg("--validate")
            .output()
            .unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            output.status.code(),
            Some(if valid { 0 } else { 2 }),
            "{manifest}: {stderr}"
        );
    }
    fs::remove_dir_all(fixture).unwrap();

    let manifest = MANIFEST.parse::<Value>().expect("valid differential TOML");
    let with_options = manifest["execution"]
        .as_array()
        .expect("execution cases")
        .iter()
        .filter(|entry| entry.get("reference-kompile-options").is_some())
        .map(|entry| entry["name"].as_str().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(with_options, ["star-cell-heating-set"]);

    // The options reach the reference kompile and nothing else.
    let uses = EXECUTION_SCRIPT
        .match_indices("\"${reference_kompile_options[@]}\"")
        .map(|(index, _)| index)
        .collect::<Vec<_>>();
    let [use_index] = uses.as_slice() else {
        panic!("the execution gate passes the reference options once: {uses:?}");
    };
    let kompile = EXECUTION_SCRIPT[..*use_index]
        .rfind("reference_cached kompile ")
        .expect("the options are passed to the reference kompile");
    assert!(
        !EXECUTION_SCRIPT[kompile..*use_index].contains(')'),
        "the options are arguments of the reference kompile command"
    );
}

/// N41: `reference-result-simplification-reason` is a written reason on an `[[execution]]` case
/// with programs and without search, any or oracle-exception runs; the renderer refuses anything
/// else, and only `star-cell-heating-set` carries it.
#[test]
fn reference_result_simplification_needs_a_reason_and_program_results() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let fixture = environment_fixture("manifest-reference-simplification");
    let helper = fixture.join("reference-manifest.py");
    fs::copy(workspace.join("scripts/reference-manifest.py"), &helper).unwrap();
    let case = |section: &str, extra: &str| {
        format!("[[{section}]]\nname = \"fixture\"\nrequires = [\"reference-toolchain\"]\n{extra}")
    };
    let reason = "reference-result-simplification-reason = \"the reference leaves branches it did not refute\"\n";
    let programs = "programs = [\"a.pgm\"]\n";
    for (manifest, valid) in [
        (case("execution", &format!("{programs}{reason}")), true),
        (case("execution", reason), false),
        (
            case(
                "execution",
                &format!("{programs}reference-result-simplification-reason = \" \"\n"),
            ),
            false,
        ),
        (
            case(
                "execution",
                &format!("{programs}reference-result-simplification-reason = true\n"),
            ),
            false,
        ),
        (
            case(
                "execution",
                &format!("{programs}{reason}[[execution.search]]\nname = \"s\"\n"),
            ),
            false,
        ),
        (
            case(
                "execution",
                &format!("{programs}{reason}[[execution.any]]\nname = \"a\"\n"),
            ),
            false,
        ),
        (
            case(
                "execution",
                &format!("{programs}{reason}[[execution.oracle-exception]]\nprogram = \"a.pgm\"\n"),
            ),
            false,
        ),
        (case("symbolic", reason), false),
    ] {
        fs::write(fixture.join("reference-differential.toml"), &manifest).unwrap();
        let output = Command::new("python3")
            .arg(&helper)
            .arg("--validate")
            .output()
            .unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            output.status.code(),
            Some(if valid { 0 } else { 2 }),
            "{manifest}: {stderr}"
        );
    }
    fs::remove_dir_all(fixture).unwrap();

    let manifest = MANIFEST.parse::<Value>().expect("valid differential TOML");
    let with_simplification = manifest["execution"]
        .as_array()
        .expect("execution cases")
        .iter()
        .filter(|entry| {
            entry
                .get("reference-result-simplification-reason")
                .is_some()
        })
        .map(|entry| entry["name"].as_str().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(with_simplification, ["star-cell-heating-set"]);
}

/// N45: `lifted-cells` is a non-empty array of `{rule, cell}` tables on an accepted
/// `[[compile]]` case with a written `lifted-cells-reason`; the renderer refuses anything else,
/// only `mir` carries it, and the compile gate passes it to the semantic KORE comparison only.
#[test]
fn lifted_cells_need_a_reason_and_an_accepted_compile_case() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let fixture = environment_fixture("manifest-lifted-cells");
    let helper = fixture.join("reference-manifest.py");
    fs::copy(workspace.join("scripts/reference-manifest.py"), &helper).unwrap();
    let case = |section: &str, extra: &str| {
        format!("[[{section}]]\nname = \"fixture\"\nrequires = [\"reference-toolchain\"]\n{extra}")
    };
    let entry = "lifted-cells = [{ rule = \"TEST.probe\", cell = \"stack\" }]\n";
    let reason = "lifted-cells-reason = \"probe writes <stack> inside <frame>\"\n";
    for (manifest, valid) in [
        (case("compile", &format!("{entry}{reason}")), true),
        (case("compile", entry), false),
        (case("compile", reason), false),
        (
            case("compile", &format!("{entry}lifted-cells-reason = \" \"\n")),
            false,
        ),
        (
            case("compile", &format!("lifted-cells = []\n{reason}")),
            false,
        ),
        (
            case(
                "compile",
                &format!("lifted-cells = [{{ rule = \"TEST.probe\" }}]\n{reason}"),
            ),
            false,
        ),
        (
            case(
                "compile",
                &format!(
                    "lifted-cells = [{{ rule = \"TEST.probe\", cell = \"<stack>\" }}]\n{reason}"
                ),
            ),
            false,
        ),
        (
            case(
                "compile",
                &format!(
                    "lifted-cells = [{{ rule = \"TEST.probe\", cell = \"stack\", why = \"x\" }}]\n{reason}"
                ),
            ),
            false,
        ),
        (
            case(
                "compile",
                &format!(
                    "lifted-cells = [{{ rule = \"TEST.probe\", cell = \"stack\" }}, {{ rule = \"TEST.probe\", cell = \"stack\" }}]\n{reason}"
                ),
            ),
            false,
        ),
        (
            case("compile", &format!("expect = \"reject\"\n{entry}{reason}")),
            false,
        ),
        (case("execution", &format!("{entry}{reason}")), false),
    ] {
        fs::write(fixture.join("reference-differential.toml"), &manifest).unwrap();
        let output = Command::new("python3")
            .arg(&helper)
            .arg("--validate")
            .output()
            .unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            output.status.code(),
            Some(if valid { 0 } else { 2 }),
            "{manifest}: {stderr}"
        );
    }
    fs::remove_dir_all(fixture).unwrap();

    let manifest = MANIFEST.parse::<Value>().expect("valid differential TOML");
    let with_lifted_cells = manifest["compile"]
        .as_array()
        .expect("compile cases")
        .iter()
        .filter(|entry| entry.get("lifted-cells").is_some())
        .map(|entry| entry["name"].as_str().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(with_lifted_cells, ["mir"]);

    // The entries reach the semantic KORE comparison and no other.
    let uses = COMPILE_SCRIPT
        .match_indices("K_DIFFERENTIAL_LIFTED_CELLS=")
        .map(|(index, _)| index)
        .collect::<Vec<_>>();
    let [use_index] = uses.as_slice() else {
        panic!("the compile gate passes the lifted cells once: {uses:?}");
    };
    let rest = &COMPILE_SCRIPT[*use_index..];
    assert!(
        rest.starts_with("K_DIFFERENTIAL_LIFTED_CELLS=\"$lifted_cells\" \\\n"),
        "the lifted cells are passed as the manifest renders them"
    );
    let command = &rest[..rest.find("); then").expect("the comparison is a condition")];
    assert!(
        command.contains("compare_artifacts emitted_kore_matches_the_reference_frontend"),
        "the lifted cells are an environment entry of the comparison command"
    );
    let section = &COMPILE_SCRIPT[..*use_index];
    let start = section
        .rfind("comparing semantic KORE")
        .expect("the semantic KORE comparison precedes the lifted cells");
    assert!(
        !section[start..].contains("compare_artifacts"),
        "the lifted cells belong to the semantic KORE comparison"
    );
}

/// Run the execution gate on `case` against fake reference tools, a fake reference RPC server
/// that only listens, a fake RPC client that answers `simplify` with `\bottom` (or with an error
/// when `FAKE_RPC_ERROR=1`), and a fake comparator that records which reference result it got
/// and fails on the raw one unless `FAKE_RAW_STATUS` says otherwise (and on the simplified one
/// with `FAKE_SIMPLIFIED_STATUS`). The gate chooses the server's port unless `environment` sets
/// `REFERENCE_SIMPLIFIER_PORT`; the fake server records the port it bound (`kore-rpc-bound`).
/// Returns the exit status, the call log, standard output and standard error, and whether a
/// fake server still listened after the gate exited.
fn execution_gate_with_reference_simplifier(
    case: &str,
    environment: &[(&str, &str)],
) -> (Option<i32>, String, String, String, bool) {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let fixture = environment_fixture("execution-simplifier");
    let k_checkout = fake_k_checkout(&fixture, &[]);
    let calls = fixture.join("calls");
    write_environment_probe(&fixture.join("kompile"), "kompile", FAKE_KOMPILE_PROLOGUE);
    write_environment_probe(
        &fixture.join("krun"),
        "krun",
        r#"printf '%s\n' '\or{S{}}(a{}(), b{}())'"#,
    );
    write_environment_probe(&fixture.join("kast"), "kast", "");
    write_environment_probe(
        &fixture.join("kore-parser"),
        "kore-parser $*",
        r#"printf '%s\n' '{"format":"KORE","version":1,"term":{"tag":"Top","sort":{"tag":"SortApp","name":"S","args":[]}}}'"#,
    );
    write_environment_probe(
        &fixture.join("kore-rpc"),
        "kore-rpc",
        r#"
printf 'kore-rpc %s|\n' "$*" >>"$ENVIRONMENT_CALLS"
while (($#)); do [[ $1 == --server-port ]] && port=$2; shift; done
exec python3 -c 'import os, socket, sys, time
s = socket.socket()
s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
s.bind(("127.0.0.1", int(sys.argv[1])))
s.listen(8)
with open(os.environ["ENVIRONMENT_CALLS"], "a") as calls:
    calls.write("kore-rpc-bound %d|\n" % s.getsockname()[1])
time.sleep(600)' "$port"
"#,
    );
    write_environment_probe(
        &fixture.join("kore-rpc-client"),
        "kore-rpc-client-done",
        r#"
printf 'kore-rpc-client %s|\n' "$*" >>"$ENVIRONMENT_CALLS"
while (($#)); do [[ $1 == -o ]] && out=$2; shift; done
if [[ ${FAKE_RPC_ERROR:-0} == 1 ]]; then
  printf '%s\n' '{"jsonrpc":"2.0","id":1,"error":{"code":-32002,"message":"Could not verify pattern"}}' >"$out"
else
  printf '%s\n' '{"jsonrpc":"2.0","id":1,"result":{"state":{"format":"KORE","version":1,"term":{"tag":"Bottom","sort":{"tag":"SortApp","name":"S","args":[]}}}}}' >"$out"
fi
"#,
    );
    let target = fake_gate_rust_toolchain(
        &fixture,
        "",
        r#"
printf 'comparator %s|\n' "$(basename "$K_REFERENCE_EXECUTION")" >>"$ENVIRONMENT_CALLS"
case $K_REFERENCE_EXECUTION in
  *.json) exit "${FAKE_SIMPLIFIED_STATUS:-0}" ;;
  *) exit "${FAKE_RAW_STATUS:-101}" ;;
esac
"#,
    );
    let path = format!(
        "{}:{}",
        fixture.display(),
        std::env::var("PATH").expect("PATH")
    );
    let mut command = Command::new("bash");
    command
        .arg(workspace.join("scripts/reference-non-imp-execution-differential.sh"))
        .arg(case)
        .env("PATH", &path)
        .env("ENVIRONMENT_CALLS", &calls)
        .env("K_CHECKOUT", &k_checkout)
        .env("K_KOMPILE", fixture.join("kompile"))
        .env_remove("K_KRUN")
        .env_remove("K_KAST")
        .env_remove("K_KORE_PARSER")
        .env_remove("K_KORE_RPC_CLIENT")
        .env_remove("REFERENCE_SIMPLIFIER_PORT")
        .env("KRUST_GATE_TARGET_DIR", &target)
        .env("REFERENCE_DIFFERENTIAL_ALLOW_UNPINNED", "1")
        .env("REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND", "rlimit-as")
        .stdin(std::process::Stdio::null());
    for (name, value) in environment {
        command.env(name, value);
    }
    let output = command.output().expect("run execution gate fixture");
    let log = fs::read_to_string(&calls).unwrap_or_default();
    let still_listening = bound_simplifier_ports(&log)
        .into_iter()
        .any(|port| std::net::TcpStream::connect(("127.0.0.1", port)).is_ok());
    fs::remove_dir_all(fixture).expect("remove execution gate fixture");
    (
        output.status.code(),
        log,
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
        still_listening,
    )
}

/// The ports the fake reference simplifiers of [`execution_gate_with_reference_simplifier`]
/// bound, in start order.
fn bound_simplifier_ports(log: &str) -> Vec<u16> {
    log.lines()
        .filter_map(|line| line.strip_prefix("kore-rpc-bound "))
        .map(|port| port.trim_end_matches('|').parse().expect("a bound port"))
        .collect()
}

/// The `--port` of every `simplify` request the fake RPC client of
/// [`execution_gate_with_reference_simplifier`] received, in order.
fn simplify_request_ports(log: &str) -> Vec<u16> {
    log.lines()
        .filter(|line| line.starts_with("kore-rpc-client ") && line.contains(" simplify "))
        .map(|line| {
            let mut words = line.split_whitespace();
            words.find(|word| *word == "--port");
            words
                .next()
                .and_then(|port| port.parse().ok())
                .unwrap_or_else(|| panic!("a simplify request without a port: {line}"))
        })
        .collect()
}

/// The execution gate never assumes a fixed port for the reference simplifier: by default it
/// starts the server on port 0, so the kernel assigns a free port at the server's own bind and
/// concurrent gate runs cannot collide, and it sends the request to the port the server it
/// started actually listens on. A port pinned with `REFERENCE_SIMPLIFIER_PORT` is used as given.
#[test]
fn execution_gate_sends_simplify_requests_to_the_port_its_own_server_bound() {
    let (status, log, stdout, stderr, _) =
        execution_gate_with_reference_simplifier("star-cell-heating-set", &[]);
    assert_eq!(status, Some(0), "{stdout}{stderr}");
    let servers = log
        .lines()
        .filter(|line| line.starts_with("kore-rpc "))
        .collect::<Vec<_>>();
    assert_eq!(servers.len(), 2, "{log}");
    for server in servers {
        assert!(server.ends_with("--server-port 0|"), "{server}");
    }
    let bound = bound_simplifier_ports(&log);
    assert_eq!(bound.len(), 2, "{log}");
    assert!(bound.iter().all(|port| *port != 0), "{log}");
    assert_eq!(simplify_request_ports(&log), bound, "{log}");

    let pinned = std::net::TcpListener::bind("127.0.0.1:0")
        .and_then(|listener| listener.local_addr())
        .expect("a free port")
        .port()
        .to_string();
    let (status, log, stdout, stderr, _) = execution_gate_with_reference_simplifier(
        "star-cell-heating-set",
        &[("REFERENCE_SIMPLIFIER_PORT", &pinned)],
    );
    assert_eq!(status, Some(0), "{stdout}{stderr}");
    for server in log.lines().filter(|line| line.starts_with("kore-rpc ")) {
        assert!(
            server.ends_with(&format!("--server-port {pinned}|")),
            "{server}"
        );
    }
    let pinned = pinned.parse::<u16>().unwrap();
    assert_eq!(bound_simplifier_ports(&log), [pinned, pinned], "{log}");
    assert_eq!(simplify_request_ports(&log), [pinned, pinned], "{log}");
}

/// N41: for a case with `reference-result-simplification-reason` the execution gate first
/// requires the raw reference result to differ from the port's, then compares the port's result
/// against the state the reference's Haskell backend RPC server (`kore-rpc`, on the case's
/// reference definition and main module, without SMT) answers to one `simplify` request, prints
/// the reason with the N41 label, and stops the server. A simplified result that differs, an RPC
/// error, or a raw result that already compares equal fails the gate; a case without the key
/// never starts the server.
#[test]
fn execution_gate_compares_against_the_reference_simplifier_only_for_opted_in_cases() {
    let (status, log, stdout, stderr, listening) =
        execution_gate_with_reference_simplifier("star-cell-heating-set", &[]);
    assert_eq!(status, Some(0), "{stdout}{stderr}");
    assert!(!listening, "the gate left the reference simplifier running");
    let comparisons = log
        .lines()
        .filter_map(|line| line.strip_prefix("comparator "))
        .collect::<Vec<_>>();
    assert_eq!(
        comparisons,
        [
            "star-cell-heating-set-two.pgm.reference.kore|",
            "star-cell-heating-set-two.pgm.reference.simplified.json|",
            "star-cell-heating-set-two-late.pgm.reference.kore|",
            "star-cell-heating-set-two-late.pgm.reference.simplified.json|",
        ],
        "{log}"
    );
    let servers = log
        .lines()
        .filter(|line| line.starts_with("kore-rpc "))
        .collect::<Vec<_>>();
    assert_eq!(servers.len(), 2, "one server per program result: {log}");
    for server in servers {
        assert!(
            server.contains("star-cell-heating-set-kompiled/definition.kore --module STAR-CELL-HEATING-SET --smt none --no-bug-report --server-port"),
            "{server}"
        );
    }
    assert_eq!(
        log.lines()
            .filter(|line| line.starts_with("kore-rpc-client ") && line.contains(" simplify "))
            .count(),
        2,
        "{log}"
    );
    assert_eq!(
        stdout
            .lines()
            .filter(|line| line.contains("N41: comparing with the reference result as the reference simplifies it: Without SMT"))
            .count(),
        2,
        "{stdout}"
    );

    let (status, log, _, stderr, _) = execution_gate_with_reference_simplifier(
        "star-cell-heating-set",
        &[("FAKE_SIMPLIFIED_STATUS", "101")],
    );
    assert_ne!(
        status,
        Some(0),
        "a simplified result that differs must fail: {log}"
    );
    assert!(!stderr.contains("no longer needed"), "{stderr}");

    let (status, log, _, stderr, listening) = execution_gate_with_reference_simplifier(
        "star-cell-heating-set",
        &[("FAKE_RPC_ERROR", "1")],
    );
    assert_eq!(status, Some(1), "{log}{stderr}");
    assert!(
        stderr.contains("the reference simplifier returned no state"),
        "{stderr}"
    );
    assert!(!listening, "the gate left the reference simplifier running");

    let (status, log, _, stderr, _) = execution_gate_with_reference_simplifier(
        "star-cell-heating-set",
        &[("FAKE_RAW_STATUS", "0")],
    );
    assert_eq!(status, Some(1), "{log}{stderr}");
    assert!(
        stderr.contains(
            "reference result simplification for star-cell-heating-set:two.pgm is no longer needed"
        ),
        "{stderr}"
    );
    assert!(!log.contains("kore-rpc"), "{log}");

    let (status, log, stdout, stderr, _) = execution_gate_with_reference_simplifier(
        "star-cell-map-nested-set",
        &[("FAKE_RAW_STATUS", "0")],
    );
    assert_eq!(status, Some(0), "{stdout}{stderr}");
    assert!(!log.contains("kore-rpc"), "{log}");
    assert!(!log.contains(".json"), "{log}");
}

#[test]
fn every_gate_normalisation_is_registered() {
    let register = NORMALISATIONS
        .parse::<Value>()
        .expect("valid normalisation register TOML");
    assert_eq!(register["version"].as_integer(), Some(1));
    let rows = register["normalisation"]
        .as_array()
        .expect("normalisation rows");
    let ids = rows
        .iter()
        .map(|row| row["id"].as_str().expect("normalisation id"))
        .collect::<BTreeSet<_>>();
    let expected = (1..=28)
        .filter(|id| *id != 2)
        .chain([
            30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45,
        ])
        .map(|id| format!("N{id}"))
        .collect::<BTreeSet<_>>();
    assert_eq!(
        ids.into_iter().map(str::to_owned).collect::<BTreeSet<_>>(),
        expected,
        "the gate register must contain N1, N3 through N28, and N30 through N45 (N29 is reserved); global UNIQUE_ID exclusion N2 is retired"
    );
    let row = |id: &str| {
        rows.iter()
            .find(|row| row["id"].as_str() == Some(id))
            .unwrap_or_else(|| panic!("missing normalisation {id}"))
    };
    // N4 covers every engine-chosen name the execution gates meet: the frontend's
    // Var'Unds'<stem>N, the NewUnifier's VarAC<n>'Unds'N remainder, the port's externalized
    // Ex/Eq/Rule marker names, and, given the initial pattern, every variable that is not free in it.
    for needle in ["VarAC", "Ex", "K_DIFFERENTIAL_INITIAL_PATTERN", "sort"] {
        assert!(
            row("N4")["rule"].as_str().unwrap().contains(needle),
            "N4 must describe the {needle} case"
        );
    }
    assert_eq!(
        row("N21")["anchor_symbol"].as_str(),
        Some("normalize_conjunctions")
    );
    assert_eq!(
        row("N22")["anchor_symbol"].as_str(),
        Some("canonicalize_remainder_existentials")
    );
    // N23 limits generated `#lambda` suffix normalization to documented multi-suffix families.
    assert_eq!(
        row("N23")["anchor_symbol"].as_str(),
        Some("strip_multi_suffix_lambda_ids")
    );
    for needle in [
        "#lambda",
        "multi-suffix",
        "docs/compatibility.md#comparison-contract",
    ] {
        assert!(
            row("N23")["justification"]
                .as_str()
                .unwrap()
                .contains(needle)
                || row("N23")["rule"].as_str().unwrap().contains(needle),
            "N23 must cite {needle}"
        );
    }
    for needle in [
        "manifest row explicitly classified as ambiguous",
        "complete KORE patterns",
        "same-sort binary Lblamb",
        "retain duplicate alternatives",
        "unambiguous parser output must remain byte-identical",
    ] {
        assert!(
            row("N25")["rule"].as_str().unwrap().contains(needle),
            "N25 must constrain {needle}"
        );
    }
    for needle in ["test-only", "generated scanner and grammar source bytes"] {
        assert!(
            row("N25")["justification"]
                .as_str()
                .unwrap()
                .contains(needle),
            "N25 must document {needle}"
        );
    }
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut registered_symbols = BTreeSet::new();
    for row in rows {
        let id = row["id"].as_str().unwrap();
        for field in ["gate", "anchor", "anchor_symbol", "rule", "justification"] {
            assert!(
                row[field]
                    .as_str()
                    .is_some_and(|value| !value.trim().is_empty()),
                "{id} must provide a non-empty {field}"
            );
        }
        let anchor = row["anchor"].as_str().unwrap();
        let anchor_path = anchor.split_once(':').map_or(anchor, |(path, _)| path);
        let source = fs::read_to_string(workspace.join(anchor_path)).unwrap_or_else(|error| {
            panic!("{id} anchor file {anchor_path} is unavailable: {error}")
        });
        let anchor_symbol = row["anchor_symbol"].as_str().unwrap();
        assert!(
            source.contains(anchor_symbol),
            "{id} anchor symbol {anchor_symbol:?} is absent from {anchor_path}"
        );
        registered_symbols.insert(anchor_symbol);
        if let Some(helpers) = row.get("anchor_helpers").and_then(Value::as_array) {
            for helper in helpers {
                let helper = helper.as_str().expect("anchor helper string");
                assert!(
                    source.contains(helper),
                    "{id} anchor helper {helper:?} is absent from {anchor_path}"
                );
                registered_symbols.insert(helper);
            }
        }
    }

    let harness =
        fs::read_to_string(workspace.join("crates/k-rust/tests/reference_differential.rs"))
            .expect("reference differential harness");
    for line in harness.lines() {
        let Some(signature) = line.trim_start().strip_prefix("fn ") else {
            continue;
        };
        let Some((name, _)) = signature.split_once('(') else {
            continue;
        };
        if [
            "normalize_",
            "canonical_",
            "canonicalize_",
            "canonicalized_",
            "strip_",
        ]
        .iter()
        .any(|prefix| name.starts_with(prefix))
        {
            assert!(
                registered_symbols.contains(name),
                "normalisation helper {name} has no register anchor or anchor_helpers entry"
            );
        }
    }
}

#[test]
fn every_conformance_normalisation_is_registered() {
    let register = NORMALISATIONS
        .parse::<Value>()
        .expect("valid normalisation register TOML");
    let rows = register["conformance"]
        .as_array()
        .expect("conformance rows");
    let ids = rows
        .iter()
        .map(|row| row["id"].as_str().expect("conformance id").to_owned())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        ids,
        (1..=9).map(|id| format!("C{id}")).collect::<BTreeSet<_>>(),
        "the conformance register must contain C1 through C9"
    );
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    for row in rows {
        let id = row["id"].as_str().unwrap();
        for field in ["rule", "justification"] {
            assert!(
                row[field]
                    .as_str()
                    .is_some_and(|value| !value.trim().is_empty()),
                "{id} must provide a non-empty {field}"
            );
        }
        // A conformance row anchored in the driver names a symbol that exists there, exactly
        // like the gate rows; unanchored rows describe driver policy rather than one function.
        let (anchor, anchor_symbol) = match (row.get("anchor"), row.get("anchor_symbol")) {
            (None, None) => {
                assert!(
                    row.get("anchor_helpers").is_none(),
                    "{id} lists anchor_helpers without an anchor"
                );
                continue;
            }
            (Some(anchor), Some(symbol)) => (
                anchor.as_str().expect("anchor string"),
                symbol.as_str().expect("anchor symbol string"),
            ),
            _ => panic!("{id} must provide anchor and anchor_symbol together"),
        };
        let anchor_path = anchor.split_once(':').map_or(anchor, |(path, _)| path);
        let source = fs::read_to_string(workspace.join(anchor_path)).unwrap_or_else(|error| {
            panic!("{id} anchor file {anchor_path} is unavailable: {error}")
        });
        assert!(
            source.contains(anchor_symbol),
            "{id} anchor symbol {anchor_symbol:?} is absent from {anchor_path}"
        );
        for helper in row
            .get("anchor_helpers")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
        {
            let helper = helper.as_str().expect("anchor helper string");
            assert!(
                source.contains(helper),
                "{id} anchor helper {helper:?} is absent from {anchor_path}"
            );
        }
    }
    // C7 is the driver's text-level reading of N4: `?Name:Sort` tokens are engine-named, the
    // pattern's own variables are not, and the renaming happens before the C1 sort.
    let c7 = rows
        .iter()
        .find(|row| row["id"].as_str() == Some("C7"))
        .expect("C7 row");
    assert_eq!(c7["anchor_symbol"].as_str(), Some("rename_existentials"));
    for needle in [
        "sort-preserving",
        "`?Name:Sort`",
        "first occurrence",
        "before the C1 sort",
        "--pattern",
    ] {
        assert!(
            c7["rule"].as_str().unwrap().contains(needle),
            "C7 must state {needle}"
        );
    }
    for needle in ["N4", "docs/compatibility.md#comparison-contract"] {
        assert!(
            c7["justification"].as_str().unwrap().contains(needle),
            "C7 must cite {needle}"
        );
    }
    // C8 escalates a failed C7 text comparison to the structural comparator over both results
    // simplified by the port: the reference is re-run with --output kore, both patterns go through
    // `krust kore-simplify`, N4 applies and N15 does not, and the .out stays the oracle.
    let c8 = rows
        .iter()
        .find(|row| row["id"].as_str() == Some("C8"))
        .expect("C8 row");
    assert_eq!(
        c8["anchor_symbol"].as_str(),
        Some("compare_simplified_kore")
    );
    for needle in [
        "C7 text comparison",
        "--output kore",
        "`krust kore-simplify`",
        "reference kompiled definition and main module",
        "executed_kore_matches_the_reference_backend",
        "without K_DIFFERENTIAL_DEFINITION",
        "N4 renaming applies and N15 does not",
        "distinct comparison label",
        ".out stays the oracle",
        "leaves the text mismatch in place",
    ] {
        assert!(
            c8["rule"].as_str().unwrap().contains(needle),
            "C8 must state {needle}"
        );
    }
    for needle in [
        "supplementary",
        "N15",
        "docs/compatibility.md#comparison-contract",
        "docs/testing.md#comparator-evidence",
    ] {
        assert!(
            c8["justification"].as_str().unwrap().contains(needle),
            "C8 must cite {needle}"
        );
    }
    let c9 = rows
        .iter()
        .find(|row| row["id"].as_str() == Some("C9"))
        .expect("C9 row");
    assert_eq!(c9["anchor_symbol"].as_str(), Some("compare_stdout_buffer"));
    for needle in [
        "--output none",
        "--io off",
        "exactly one execution leaf in total",
        "Any constrained residual leaf",
        "#ostream(1)",
        "#buffer(S)",
        "exact bytes",
        "explicit --io on",
        "pre-buffered --io on --output none",
    ] {
        assert!(
            c9["rule"].as_str().unwrap().contains(needle),
            "C9 must state {needle}"
        );
    }
    for needle in [
        "domains.md:2805-2846",
        "krun:442-448",
        "docs/compatibility.md#comparison-contract",
    ] {
        assert!(
            c9["justification"].as_str().unwrap().contains(needle),
            "C9 must cite {needle}"
        );
    }
}

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

    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let allowed_requirements = BTreeSet::from(["reference-toolchain", "semantics-support"]);
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
        if matches!(
            entry.get("expect").and_then(Value::as_str),
            Some("reject" | "port-accepts")
        ) {
            continue;
        }
        assert!(
            entry["comparisons"]
                .as_array()
                .is_some_and(|comparisons| !comparisons.is_empty()),
            "every compile case must declare compared artifacts"
        );
    }

    let mut paths = BTreeSet::new();
    collect_workspace_paths(&manifest, &mut paths);
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
            "excluded case {name} changed its documented disposition",
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
fn port_accepts_cases_are_the_adjudicated_divergences() {
    let manifest = MANIFEST.parse::<Value>().expect("valid differential TOML");
    let compatibility = fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../docs/compatibility.md"),
    )
    .expect("docs/compatibility.md");
    let mut names = BTreeSet::new();
    for entry in manifest["compile"].as_array().expect("compile cases") {
        if entry.get("expect").and_then(Value::as_str) != Some("port-accepts") {
            continue;
        }
        let name = entry["name"].as_str().expect("compile name");
        names.insert(name);
        let reason = entry["reason"].as_str().expect("port-accepts reason");
        let anchor = reason
            .split_whitespace()
            .find_map(|word| word.strip_prefix("docs/compatibility.md#"))
            .map(|anchor| anchor.trim_end_matches('.'))
            .unwrap_or_else(|| {
                panic!("port-accepts case {name} must link its compatibility section")
            });
        let heading = compatibility
            .lines()
            .filter_map(|line| line.strip_prefix("## "))
            .find(|heading| heading.to_lowercase().replace(' ', "-") == anchor)
            .unwrap_or_else(|| panic!("docs/compatibility.md has no section #{anchor} for {name}"));
        let section = compatibility
            .split(&format!("## {heading}\n"))
            .nth(1)
            .and_then(|rest| rest.split("\n## ").next())
            .expect("compatibility section body");
        assert!(
            section.contains(&format!("`{name}`")) && section.contains("port-accepts"),
            "docs/compatibility.md#{anchor} must record {name} as a port-accepts divergence",
        );
    }
    assert_eq!(
        names,
        BTreeSet::from(["semcast3", "semcast4"]),
        "the adjudicated port-accepts set changed",
    );
}

#[test]
fn differential_manifest_requires_a_reason_for_port_accepts() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let fixture = environment_fixture("manifest-outcomes");
    let helper = fixture.join("reference-manifest.py");
    fs::copy(workspace.join("scripts/reference-manifest.py"), &helper).unwrap();
    for (fields, valid) in [
        ("", true),
        ("expect = \"reject\"\n", true),
        (
            "expect = \"port-accepts\"\nreason = \"the manual's rule\"\nreference-error = \"Unexpected sort\"\n",
            true,
        ),
        (
            "expect = \"port-accepts\"\nreference-error = \"Unexpected sort\"\n",
            false,
        ),
        (
            "expect = \"port-accepts\"\nreason = \"  \"\nreference-error = \"Unexpected sort\"\n",
            false,
        ),
        ("expect = \"port-accepts\"\nreason = \"why\"\n", false),
        (
            "expect = \"port-accepts\"\nreason = \"why\"\nreference-error = \" \"\n",
            false,
        ),
        (
            "expect = \"port-accepts\"\nreason = \"why\"\nreference-error = \"Unexpected sort\"\ncomparisons = [\"semantic-kore\"]\n",
            false,
        ),
        ("expect = \"reject\"\nreason = \"why\"\n", false),
        (
            "expect = \"reject\"\nreference-error = \"Unexpected sort\"\n",
            false,
        ),
        ("reference-error = \"Unexpected sort\"\n", false),
        ("expect = \"port-rejects\"\n", false),
    ] {
        fs::write(
            fixture.join("reference-differential.toml"),
            format!(
                "[[compile]]\nname = \"fixture\"\nrequires = [\"reference-toolchain\"]\n{fields}"
            ),
        )
        .unwrap();
        let output = Command::new("python3")
            .arg(&helper)
            .arg("--validate")
            .output()
            .unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            output.status.code(),
            Some(if valid { 0 } else { 2 }),
            "{fields}: {stderr}"
        );
        if !valid {
            assert!(stderr.contains("invalid differential manifest"), "{stderr}");
        }
    }
    fs::remove_dir_all(fixture).unwrap();
}

#[test]
fn compile_gate_fails_when_either_side_of_a_port_accepts_case_moves() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let fixture = environment_fixture("port-accepts-gate");
    let k_checkout = fake_k_checkout(&fixture, &[]);
    let fake_kompile = fixture.join("kompile");
    let fake_kore_parser = fixture.join("kore-parser");
    fs::write(
        &fake_kompile,
        "#!/usr/bin/env bash\necho \"$FAKE_KOMPILE_MESSAGE\"\nexit \"$FAKE_KOMPILE_STATUS\"\n",
    )
    .unwrap();
    fs::write(
        &fake_kore_parser,
        "#!/usr/bin/env bash\nexit \"$FAKE_PARSER_STATUS\"\n",
    )
    .unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        for executable in [&fake_kompile, &fake_kore_parser] {
            fs::set_permissions(executable, fs::Permissions::from_mode(0o755)).unwrap();
        }
    }
    let gate_target = fake_gate_rust_toolchain(&fixture, "exit \"$FAKE_KRUST_STATUS\"", "");
    let calls = fixture.join("calls");
    let path = format!(
        "{}:{}",
        fixture.display(),
        std::env::var("PATH").expect("PATH")
    );
    let script = workspace.join("scripts/reference-differential.sh");
    const PINNED: &str =
        "[Error] Inner Parser: Unexpected sort Big for variable X. Expected: Small";
    let run = |reference: u8, message: &str, krust: u8, parser: u8| {
        let output = Command::new("bash")
            .arg(&script)
            .arg("semcast3")
            .env("PATH", &path)
            .env("K_CHECKOUT", &k_checkout)
            .env("K_KOMPILE", &fake_kompile)
            .env("K_KORE_PARSER", &fake_kore_parser)
            .env("FAKE_KOMPILE_STATUS", reference.to_string())
            .env("FAKE_KOMPILE_MESSAGE", message)
            .env("FAKE_KRUST_STATUS", krust.to_string())
            .env("FAKE_PARSER_STATUS", parser.to_string())
            .env("KRUST_GATE_TARGET_DIR", &gate_target)
            .env("ENVIRONMENT_CALLS", &calls)
            .env("REFERENCE_DIFFERENTIAL_ALLOW_UNPINNED", "1")
            .env("REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND", "rlimit-as")
            .output()
            .expect("run port-accepts gate fixture");
        (
            output.status.code(),
            String::from_utf8_lossy(&output.stdout).into_owned(),
            String::from_utf8_lossy(&output.stderr).into_owned(),
        )
    };

    let (status, stdout, stderr) = run(1, PINNED, 0, 0);
    assert_eq!(
        status,
        Some(0),
        "recorded divergence holds: {stdout}\n{stderr}"
    );
    assert!(
        stdout.contains("recorded divergence: The K user manual"),
        "{stdout}"
    );
    assert!(
        stdout.contains("reference rejection: [Error] Inner Parser: Unexpected sort Big"),
        "{stdout}"
    );
    assert!(
        stdout.contains("verifying k-rust definition.kore"),
        "{stdout}"
    );
    assert!(stdout.contains("corpus passed"), "{stdout}");

    for (reference, message, krust, parser, diagnostic) in [
        (
            0,
            PINNED,
            0,
            0,
            "reference frontend accepted port-accepts case semcast3",
        ),
        (
            1,
            "Error: Could not reserve enough space for object heap",
            0,
            0,
            "reference frontend rejection of port-accepts case semcast3 for haskell/rust changed",
        ),
        (
            1,
            "[Error] Inner Parser: Parse error: unexpected token 'a'",
            0,
            0,
            "lacks the recorded reference-error \"Unexpected sort Big for variable X\"",
        ),
        (
            1,
            PINNED,
            1,
            0,
            "k-rust rejected port-accepts case semcast3",
        ),
        (1, PINNED, 0, 1, "k-rust definition rejected by kore-parser"),
    ] {
        let (status, stdout, stderr) = run(reference, message, krust, parser);
        assert_eq!(status, Some(1), "{diagnostic}: {stdout}\n{stderr}");
        assert!(stderr.contains(diagnostic), "{stderr}");
        assert!(!stdout.contains("corpus passed"), "{stdout}");
    }
    fs::remove_dir_all(fixture).unwrap();
}

#[test]
fn llvm_verification_normalisation_is_exact_and_refuses_existing_claims() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let fixture = environment_fixture("llvm-verification-normalisation");
    let input = fixture.join("input.kore");
    let copy = fixture.join("verification.kore");
    let helper = workspace.join("scripts/reference-llvm-verification.py");
    let source = r#"[]
module A
  // symbol fake{}():SortS{} [value-production{}()]
  /* symbol fake2{}():SortS{} [value-production{}()] */
  symbol Lblfoo{}(SortS{}):SortS{} [anywhere{}(), value-production{}()]
  hooked-symbol Lblbar{}():SortS{}
    [value-production { } ( ), note{}("functional{}(), ] \\\""), nested{}(value-production{}())]
  symbol Lblfree{}():SortS{} [functional{}()]
  symbol Lblnested{}():SortS{} [nested{}(value-production{}())]
  symbol Lblparameter{}():SortS{} [value-production{SortS{}}()]
  axiom{} Lblfoo{}(X:SortS{}) [value-production{}()]
  axiom{} symbol:SortS{} [value-production{}()]
endmodule [value-production{}()]
"#;
    fs::write(&input, source).unwrap();
    let run = || {
        Command::new("python3")
            .arg(&helper)
            .arg(&input)
            .arg(&copy)
            .output()
            .expect("run LLVM verification normalisation")
    };
    let output = run();
    assert!(output.status.success(), "{output:?}");
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "N38 LLVM verification value-production declarations: 2\n"
    );
    let expected = source
        .replace(
            "[anywhere{}(), value-production{}()]",
            "[anywhere{}(), value-production{}(), function{}()]",
        )
        .replace(
            "nested{}(value-production{}())]\n  symbol Lblfree",
            "nested{}(value-production{}()), function{}()]\n  symbol Lblfree",
        );
    assert_eq!(fs::read_to_string(&copy).unwrap(), expected);
    assert_eq!(fs::read_to_string(&input).unwrap(), source);

    for claim in ["function", "functional"] {
        let invalid = format!(
            "symbol Lblvalid{{}}():SortS{{}} [value-production{{}}()]\n\
             symbol Lblinvalid{{}}():SortS{{}} [value-production{{}}(), {claim}{{}}()]\n"
        );
        fs::write(&input, &invalid).unwrap();
        fs::write(&copy, "untouched destination").unwrap();
        let output = run();
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert!(
            String::from_utf8_lossy(&output.stderr)
                .contains("Lblinvalid already carries function or functional"),
            "{output:?}"
        );
        assert_eq!(fs::read_to_string(&input).unwrap(), invalid);
        assert_eq!(fs::read_to_string(&copy).unwrap(), "untouched destination");
    }
    let output = Command::new("python3")
        .arg(&helper)
        .arg(&input)
        .arg(&input)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&output.stderr).contains("must use a separate copy"));
    fs::remove_dir_all(fixture).unwrap();
}

#[test]
fn compile_gate_normalises_only_the_llvm_verification_copy() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let fixture = environment_fixture("llvm-verification-routing");
    let k_checkout = fake_k_checkout(
        &fixture,
        &["k-distribution/tests/regression-new/append/test.k"],
    );
    let calls = fixture.join("calls");
    let fake_kompile = fixture.join("kompile");
    let fake_kore_parser = fixture.join("kore-parser");
    write_environment_probe(&fake_kompile, "kompile", "");
    write_environment_probe(
        &fake_kore_parser,
        "parser",
        r#"
if [[ "$1" == */rust/* ]]; then
  if [[ "$TEST_PAIRING" == kore/llvm ]]; then
    [[ "$1" == */definition.verify.kore ]]
  else
    [[ "$1" == */definition.kore ]]
  fi
  grep -qF 'value-production{}(), function{}()' "$1"
fi
"#,
    );
    let gate_target = fake_gate_rust_toolchain(
        &fixture,
        r#"
if [[ "$1" == kcompile ]]; then
  args=("$@")
  for ((i=0; i<${#args[@]}; i++)); do
    if [[ "${args[i]}" == --output-directory ]]; then
      output=${args[i+1]}
    fi
  done
  attributes='value-production{}()'
  if [[ "$TEST_PAIRING" == haskell/rust ]]; then
    attributes+=', function{}()'
  fi
  printf 'symbol Lblfoo{}():SortS{} [%s]\n' "$attributes" >"$output/definition.kore"
fi
"#,
        r#"
if [[ -n "${K_RUST_KORE:-}" ]]; then
  [[ "$K_RUST_KORE" != */definition.verify.kore ]]
  if [[ "$K_RUST_KORE" == */definition.kore ]]; then
    if [[ "$TEST_PAIRING" == kore/llvm ]]; then
      ! grep -qF 'function{}()' "$K_RUST_KORE"
    else
      grep -qF 'function{}()' "$K_RUST_KORE"
    fi
  fi
fi
"#,
    );
    let path = format!("{}:{}", fixture.display(), std::env::var("PATH").unwrap());
    for pairing in ["kore/llvm", "haskell/rust"] {
        let output = Command::new("bash")
            .arg(workspace.join("scripts/reference-differential.sh"))
            .arg("append")
            .env("PATH", &path)
            .env("ENVIRONMENT_CALLS", &calls)
            .env("TEST_PAIRING", pairing)
            .env("KRUST_GATE_TARGET_DIR", &gate_target)
            .env("K_CHECKOUT", &k_checkout)
            .env("K_KOMPILE", &fake_kompile)
            .env("K_KORE_PARSER", &fake_kore_parser)
            .env("REFERENCE_DIFFERENTIAL_ALLOW_UNPINNED", "1")
            .env("REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND", "rlimit-as")
            .env("REFERENCE_DIFFERENTIAL_PAIRINGS", pairing)
            .output()
            .unwrap();
        assert!(output.status.success(), "{pairing}: {output:?}");
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert_eq!(
            stdout.contains("N38 LLVM verification value-production declarations: 1"),
            pairing == "kore/llvm",
            "{stdout}"
        );
        assert!(stdout.contains("corpus passed"), "{stdout}");
    }
    fs::remove_dir_all(fixture).unwrap();
}

#[test]
fn manual_certification_protocol_names_required_gates() {
    let manifest = MANIFEST.parse::<Value>().expect("valid differential TOML");
    let certification = manifest["gate"]
        .as_array()
        .expect("gate sets")
        .iter()
        .filter(|gate| gate["run"].as_str() == Some("certification"))
        .map(|gate| gate["command"].as_str().expect("gate command"))
        .collect::<BTreeSet<_>>();
    for command in [
        "scripts/reference-differential.sh append ambiguous-rewrite casts cell-map fresh-variables list-set macro-rewrite parametric-semantic-cast hooked-namespaces star-cell-config overload-constructors owise-functions owise-competitors owise concrete-rw2 cast-inner",
        "scripts/reference-differential.sh fun-int-list-config",
        "scripts/reference-differential.sh imp fresh-name-collision parametric assoc-strict undefined-sort semcast2 semcast3 semcast4",
        "REFERENCE_DIFFERENTIAL_PAIRINGS=haskell/rust scripts/reference-differential.sh wasm mir evm-equivalence",
        "scripts/reference-kast-differential.sh wasm mir evm-equivalence",
        "scripts/reference-non-imp-execution-differential.sh imp collections hook-boundaries",
        "scripts/reference-non-imp-execution-differential.sh depth-bounded-search branching-execution concrete-symbolic-rules trivial-result-execution",
        "scripts/reference-proof-differential.sh mini-proof",
        "scripts/reference-proof-differential.sh split-proof trusted-lemma-proof trivial-proof",
        "scripts/reference-rpc-differential.sh imp",
        "scripts/reference-rpc-differential.sh bounded-search",
        "scripts/reference-rpc-differential.sh trivial-result-rpc",
        "scripts/reference-mir-execution-differential.sh",
        "scripts/reference-symbolic-execution-differential.sh symbolic-depth-bound symbolic-owise",
        "scripts/conformance-ratchet.sh --label change --cases append --log target/conformance/ratchet.toml --runs-dir target/conformance/runs",
    ] {
        assert!(
            certification.contains(command),
            "manual certification protocol must name `{command}`",
        );
    }

    for requirement in [
        r#"# Run the command of every [[gate]] below whose run is "certification" after a change to frontend, definition, kompile, or KORE emission behavior."#,
        "# PR description (any change under crates/k-rust/src/{inner,kompile,outer,definition}, crates/k-rust-backend, scripts/reference-*, scripts/conformance/):",
        "#   1. the certification gate commands below that apply, one row each: case, pass/fail, wall s, peak RSS MiB (scripts/conformance/measure.py)",
        "#   2. the ratchet block printed by `scripts/conformance-ratchet.sh --label change --cases <affected cases> --log target/conformance/ratchet.toml --runs-dir target/conformance/runs` (or --all for full certification)",
        "#   3. the permanent multi-alias oracle-exclusion count printed by scripts/reference-differential.sh",
    ] {
        assert!(
            MANIFEST.lines().any(|line| line == requirement),
            "manual certification protocol must require `{requirement}`",
        );
    }
}

/// The gate scripts that take manifest case names as arguments, and the section they read them
/// from. Without arguments a script runs every runnable case of its section.
const CASE_SCRIPTS: [(&str, &str); 6] = [
    ("scripts/reference-differential.sh", "compile"),
    ("scripts/reference-kast-differential.sh", "kast"),
    (
        "scripts/reference-non-imp-execution-differential.sh",
        "execution",
    ),
    ("scripts/reference-proof-differential.sh", "proof"),
    ("scripts/reference-rpc-differential.sh", "rpc"),
    (
        "scripts/reference-symbolic-execution-differential.sh",
        "symbolic",
    ),
];

/// A runnable case is one whose requirements the gates can satisfy: a `semantics-support`
/// requirement withholds the case from every script's default selection and rejects it by name.
fn is_runnable_case(entry: &Value) -> bool {
    !entry["requires"].as_array().is_some_and(|requirements| {
        requirements
            .iter()
            .any(|requirement| requirement.as_str() == Some("semantics-support"))
    })
}

/// Every inconsistency between the manifest's `[[gate]]` sets and its cases.
///
/// A gate command is `[NAME=value ...] script [argument ...]`, run from the workspace root. For a
/// script of `CASE_SCRIPTS` the arguments are case names of its section, every one of which must
/// be runnable there (the script refuses any other name before it does work), and no arguments
/// select every runnable case. A runnable case must be selected by some gate or carry
/// `manual = "<reason>"`; a case that some gate selects must not also claim to be manual.
fn gate_model_failures(manifest: &Value, workspace: &Path) -> Vec<String> {
    let mut failures = Vec::new();
    let mut gated = BTreeSet::<(&str, &str)>::new();
    let mut names = BTreeSet::new();
    let Some(gates) = manifest.get("gate").and_then(Value::as_array) else {
        return vec!["the manifest has no [[gate]] sets".into()];
    };
    for gate in gates {
        let Some(table) = gate.as_table() else {
            failures.push("a [[gate]] entry is not a table".into());
            continue;
        };
        let name = table.get("name").and_then(Value::as_str).unwrap_or("");
        if name.is_empty() || !names.insert(name) {
            failures.push(format!("gate name `{name}` is empty or not unique"));
        }
        let keys = table.keys().map(String::as_str).collect::<BTreeSet<_>>();
        if keys != BTreeSet::from(["command", "name", "run"]) {
            failures.push(format!(
                "gate {name} has keys {keys:?}, not command, name and run"
            ));
        }
        let run = table.get("run").and_then(Value::as_str).unwrap_or("");
        if !matches!(run, "certification" | "weekly") {
            failures.push(format!(
                "gate {name} has run `{run}`, not certification or weekly"
            ));
        }
        let command = table.get("command").and_then(Value::as_str).unwrap_or("");
        let mut words = command
            .split_whitespace()
            .skip_while(|word| {
                word.split_once('=').is_some_and(|(variable, _)| {
                    !variable.is_empty()
                        && variable
                            .bytes()
                            .all(|byte| byte.is_ascii_uppercase() || byte == b'_')
                })
            })
            .peekable();
        let Some(script) = words.next() else {
            failures.push(format!("gate {name} has no command"));
            continue;
        };
        if !script.starts_with("scripts/") || !workspace.join(script).is_file() {
            failures.push(format!(
                "gate {name} runs `{script}`, which is not a workspace script"
            ));
        }
        let Some(&(_, section)) = CASE_SCRIPTS.iter().find(|(path, _)| *path == script) else {
            continue;
        };
        let runnable = manifest
            .get(section)
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .filter(|entry| is_runnable_case(entry))
            .filter_map(|entry| entry["name"].as_str())
            .collect::<BTreeSet<_>>();
        if words.peek().is_none() {
            gated.extend(runnable.iter().map(|case| (section, *case)));
        }
        for case in words {
            if runnable.contains(case) {
                gated.insert((section, case));
            } else {
                failures.push(format!(
                    "gate {name} names `{case}`, which is not a runnable {section} case"
                ));
            }
        }
    }

    for section in SECTIONS {
        for entry in manifest
            .get(section)
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
        {
            let name = entry["name"].as_str().unwrap_or("");
            let manual = entry.get("manual");
            if manual.is_some_and(|reason| {
                reason
                    .as_str()
                    .is_none_or(|reason| reason.trim().is_empty())
            }) {
                failures.push(format!("{section} case {name} has an empty manual reason"));
            }
            match (gated.contains(&(section, name)), manual.is_some()) {
                (true, true) => failures.push(format!(
                    "{section} case {name} is run by a gate but carries a manual reason"
                )),
                (false, false) if is_runnable_case(entry) => failures.push(format!(
                    "{section} case {name} is in no [[gate]] and carries no manual reason"
                )),
                _ => {}
            }
        }
    }
    failures
}

/// A case that no gate runs rots unnoticed: nothing executes it until someone reads the
/// manifest. So every runnable case is in a named gate set or says why it is run by hand.
#[test]
fn every_runnable_case_belongs_to_a_gate_or_is_manual() {
    let manifest = MANIFEST.parse::<Value>().expect("valid differential TOML");
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let failures = gate_model_failures(&manifest, &workspace);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn gate_model_rejects_unlisted_misnamed_and_falsely_manual_cases() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let manifest = MANIFEST.parse::<Value>().expect("valid differential TOML");

    let mut unlisted = manifest.clone();
    let mut probe = unlisted["compile"][0].clone();
    probe["name"] = Value::String("unlisted-probe".into());
    unlisted["compile"]
        .as_array_mut()
        .unwrap()
        .push(probe.clone());
    assert_eq!(
        gate_model_failures(&unlisted, &workspace),
        ["compile case unlisted-probe is in no [[gate]] and carries no manual reason"],
    );

    let mut manual = unlisted.clone();
    let entries = manual["compile"].as_array_mut().unwrap();
    entries.last_mut().unwrap().as_table_mut().unwrap().insert(
        "manual".into(),
        Value::String("the probe is run by hand".into()),
    );
    assert!(gate_model_failures(&manual, &workspace).is_empty());

    let mut blocked = unlisted.clone();
    blocked["compile"]
        .as_array_mut()
        .unwrap()
        .last_mut()
        .unwrap()["requires"] = Value::Array(vec![Value::String("semantics-support".into())]);
    assert!(
        gate_model_failures(&blocked, &workspace).is_empty(),
        "a case no script can run needs no gate"
    );

    let mut falsely_manual = manifest.clone();
    falsely_manual["compile"][0]
        .as_table_mut()
        .unwrap()
        .insert("manual".into(), Value::String("stale".into()));
    let first = manifest["compile"][0]["name"].as_str().unwrap();
    assert_eq!(
        gate_model_failures(&falsely_manual, &workspace),
        [format!(
            "compile case {first} is run by a gate but carries a manual reason"
        )],
    );

    let mut misnamed = manifest.clone();
    let gate = misnamed["gate"]
        .as_array_mut()
        .unwrap()
        .first_mut()
        .unwrap();
    let command = format!("{} no-such-case", gate["command"].as_str().unwrap());
    gate["command"] = Value::String(command);
    let gate_name = manifest["gate"][0]["name"].as_str().unwrap();
    assert_eq!(
        gate_model_failures(&misnamed, &workspace),
        [format!(
            "gate {gate_name} names `no-such-case`, which is not a runnable compile case"
        )],
    );

    let mut all_cases = unlisted.clone();
    all_cases["gate"].as_array_mut().unwrap().push(Value::Table(
        [
            ("name".to_owned(), Value::String("compile-all".into())),
            ("run".to_owned(), Value::String("certification".into())),
            (
                "command".to_owned(),
                Value::String("scripts/reference-differential.sh".into()),
            ),
        ]
        .into_iter()
        .collect(),
    ));
    assert!(
        gate_model_failures(&all_cases, &workspace).is_empty(),
        "a case script without arguments runs every runnable case of its section"
    );
}

/// The `scripts/` commands of a GitHub workflow's `run:` steps, each with its whitespace collapsed:
/// a plain `run: command` line, or the lines of a `run: >-` folded block, which YAML joins with
/// spaces. Literal `run: |` blocks are shell scripts, not gate commands, and are skipped.
fn workflow_script_commands(workflow: &str) -> Vec<String> {
    let mut commands = Vec::new();
    let mut lines = workflow.lines().peekable();
    while let Some(line) = lines.next() {
        let Some((indent, value)) = line.split_once("run:") else {
            continue;
        };
        if !indent.trim().is_empty() && indent.trim() != "-" {
            continue;
        }
        let value = value.trim();
        let command = if value == ">-" {
            let mut folded = Vec::new();
            let step_indent = indent.len();
            while let Some(next) = lines.peek() {
                let next_indent = next.len() - next.trim_start().len();
                if next.trim().is_empty() || next_indent <= step_indent {
                    break;
                }
                folded.push(next.trim());
                lines.next();
            }
            folded.join(" ")
        } else {
            value.to_owned()
        };
        if command.starts_with("scripts/") {
            commands.push(command.split_whitespace().collect::<Vec<_>>().join(" "));
        }
    }
    commands
}

/// The weekly gate sets are the differential workflow's gate steps, so the manifest stays the one
/// record of which case runs where until the workflow reads its case lists from the manifest.
#[test]
fn weekly_gates_are_the_differential_workflow_steps() {
    let manifest = MANIFEST.parse::<Value>().expect("valid differential TOML");
    let mut weekly = manifest["gate"]
        .as_array()
        .expect("gate sets")
        .iter()
        .filter(|gate| gate["run"].as_str() == Some("weekly"))
        .map(|gate| gate["command"].as_str().expect("gate command").to_owned())
        .collect::<Vec<_>>();
    let mut workflow = workflow_script_commands(DIFFERENTIAL_WORKFLOW);
    assert!(
        !workflow.is_empty(),
        "the differential workflow runs no gate script"
    );
    weekly.sort();
    workflow.sort();
    assert_eq!(
        workflow, weekly,
        "every gate step of .github/workflows/differential.yml must be a weekly [[gate]] with the same command, and every weekly gate a step"
    );
}

#[test]
fn workflow_script_commands_reads_folded_and_plain_steps() {
    let workflow = "jobs:\n  local:\n    steps:\n      - name: Build\n        run: cargo build\n\n      - name: Compile\n        run: >-\n          scripts/reference-differential.sh\n          append casts\n\n      - name: Install\n        run: |\n          scripts/not-a-gate.sh\n          other\n\n      - name: Proof\n        run: scripts/reference-proof-differential.sh mini-proof\n";
    assert_eq!(
        workflow_script_commands(workflow),
        [
            "scripts/reference-differential.sh append casts",
            "scripts/reference-proof-differential.sh mini-proof",
        ]
    );
}

/// N10: the RPC gate refuses an oracle exception whose committed k-rust expectation and recorded
/// oracle response are the same JSON document, because then the two engines agree and the
/// exception excuses nothing. That depends only on committed files, so it is checked on every
/// push, not only when the gate runs against a live oracle.
#[test]
fn committed_rpc_oracle_exceptions_record_different_responses() {
    let manifest = MANIFEST.parse::<Value>().expect("valid differential TOML");
    let mut checked = 0;
    for entry in manifest["rpc"].as_array().expect("rpc cases") {
        let name = entry["name"].as_str().expect("rpc case name");
        for exception in entry
            .get("oracle-exception")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
        {
            let response = exception["response"].as_str().expect("exception response");
            let read = |field: &str| {
                let path = workspace_file(exception[field].as_str().expect("exception file"));
                let source = fs::read_to_string(&path).unwrap_or_else(|error| {
                    panic!(
                        "RPC oracle exception for {name}:{response} needs its committed {field} file {}: {error}",
                        path.display()
                    )
                });
                serde_json::from_str::<serde_json::Value>(&source)
                    .unwrap_or_else(|error| panic!("{} is not JSON: {error}", path.display()))
            };
            let (expected, reference) = (read("expected"), read("reference"));
            assert!(
                !same_json(&expected, &reference),
                "committed RPC oracle exception expectations for {name}:{response} are equal"
            );
            checked += 1;
        }
    }
    assert!(checked > 0, "no RPC oracle exception was checked");
}

/// JSON equality as `jq -S .` output compares it: object member order is irrelevant, and numbers
/// are equal when their values are, whatever their spelling.
fn same_json(left: &serde_json::Value, right: &serde_json::Value) -> bool {
    use serde_json::Value as Json;
    match (left, right) {
        (Json::Number(left), Json::Number(right)) => {
            left == right
                || left
                    .as_f64()
                    .is_some_and(|value| right.as_f64() == Some(value))
        }
        (Json::Array(left), Json::Array(right)) => {
            left.len() == right.len()
                && left
                    .iter()
                    .zip(right)
                    .all(|(left, right)| same_json(left, right))
        }
        (Json::Object(left), Json::Object(right)) => {
            left.len() == right.len()
                && left
                    .iter()
                    .all(|(key, value)| right.get(key).is_some_and(|other| same_json(value, other)))
        }
        _ => left == right,
    }
}

#[test]
fn same_json_ignores_member_order_and_number_spelling_only() {
    let parse = |source: &str| serde_json::from_str::<serde_json::Value>(source).unwrap();
    assert!(same_json(
        &parse(r#"{"a": 1, "b": [2.0, "x"]}"#),
        &parse(r#"{"b": [2, "x"], "a": 1e0}"#)
    ));
    assert!(!same_json(&parse(r#"{"a": 1}"#), &parse(r#"{"a": 2}"#)));
    assert!(!same_json(
        &parse(r#"{"a": 1}"#),
        &parse(r#"{"a": 1, "b": 1}"#)
    ));
    assert!(!same_json(&parse(r#"[1, 2]"#), &parse(r#"[2, 1]"#)));
    assert!(!same_json(&parse(r#""1""#), &parse("1")));
}

/// The workspace path of a manifest `${workspace}/...` file.
fn workspace_file(value: &str) -> PathBuf {
    let relative = value
        .strip_prefix("${workspace}/")
        .unwrap_or_else(|| panic!("{value} is not a workspace file"));
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(relative)
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
        for rust_process in [
            "reference_run_rust_frontend cargo build",
            "reference_run_rust_frontend \"$krust_gate_binary\"",
        ] {
            assert_eq!(
                script.matches(rust_process).count(),
                1,
                "each frontend script must route its one krust build and its one krust run through the aggregate-aware helper",
            );
        }
        assert!(
            !script.contains("cargo run"),
            "the gate runs the krust binary it built once",
        );
    }

    for script in JAVA_BACKED_DIFFERENTIAL_SCRIPTS {
        assert!(
            script.contains(
                "reference_k_opts=${REFERENCE_DIFFERENTIAL_K_OPTS:-$reference_default_k_opts}",
            ),
            "every Java-backed differential must consume the shared JVM default",
        );
        assert_eq!(
            script.matches("-Xmx2048m").count(),
            0,
            "JVM defaults must be declared only by reference-memory-guard.sh",
        );
    }
    assert_eq!(
        MIR_EXECUTION_SCRIPT
            .matches("export K_OPTS=\"$reference_k_opts\"")
            .count(),
        2,
        "MIR reference kompile and krun must both receive the bounded JVM options",
    );

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
        "REFERENCE_DIFFERENTIAL_JOB_MEMORY_HIGH_KIB:-16777216",
        "REFERENCE_DIFFERENTIAL_JOB_MEMORY_MAX_KIB:-16777216",
        "REFERENCE_DIFFERENTIAL_JOB_FALLBACK_VIRTUAL_MEMORY_KIB:-25165824",
        "MemoryHigh=${reference_job_memory_high_kib}K",
        "MemoryMax=${reference_job_memory_max_kib}K",
        "MemorySwapMax=0",
        "ulimit -v \"$reference_job_fallback_virtual_memory_kib\"",
        // The virtual-address fallback must bound the reference JVM itself:
        // default ergonomics on a many-core host exceed the RLIMIT_AS ceiling.
        "reference_default_k_opts='-Xmx2048m -Xss1m -XX:+UseSerialGC",
        "-Dscala.concurrent.context.numThreads=2 -Dscala.concurrent.context.maxThreads=2",
        "if [[ -z \"${REFERENCE_DIFFERENTIAL_K_OPTS:-}\" ]]; then",
        "export REFERENCE_DIFFERENTIAL_K_OPTS=\"$reference_default_k_opts\"",
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

    let fixture_command = || {
        let mut command = Command::new("bash");
        command
            .arg(&fixture_script)
            .env("PATH", &path)
            .env("GUARD_CALLS", &calls)
            .env("PAYLOAD_RUNS", &payload_runs)
            .env("REFERENCE_GUARD_PATH", &guard_path);
        // Each scenario owns the guard inputs, including the absence of an
        // override. CI and callers may set these in the parent environment.
        for name in [
            "REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND",
            "REFERENCE_DIFFERENTIAL_JOB_MEMORY_HIGH_KIB",
            "REFERENCE_DIFFERENTIAL_JOB_MEMORY_MAX_KIB",
            "REFERENCE_DIFFERENTIAL_JOB_FALLBACK_VIRTUAL_MEMORY_KIB",
            "REFERENCE_DIFFERENTIAL_K_OPTS",
        ] {
            command.env_remove(name);
        }
        command
    };

    let scoped = fixture_command()
        .env("PAYLOAD_STATUS", "23")
        .env("SYSTEMD_PROBE_STATUS", "0")
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
    assert!(scoped_calls.contains("MemoryHigh=16777216K"));
    assert!(scoped_calls.contains("MemoryMax=16777216K"));
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
    let fallback = fixture_command()
        .env("PAYLOAD_STATUS", "29")
        .env("SYSTEMD_PROBE_STATUS", "1")
        .env(
            "REFERENCE_DIFFERENTIAL_JOB_FALLBACK_VIRTUAL_MEMORY_KIB",
            "10485760",
        )
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
          warning: bounding the reference JVM with REFERENCE_DIFFERENTIAL_K_OPTS=-Xmx2048m -Xss1m -XX:+UseSerialGC -XX:CompressedClassSpaceSize=128m -XX:MaxMetaspaceSize=256m -XX:ReservedCodeCacheSize=128m -Dscala.concurrent.context.numThreads=2 -Dscala.concurrent.context.maxThreads=2 under the virtual-address fallback\n\
          payload-err",
        "identify the fallback semantics, bound the reference JVM, and otherwise preserve stderr exactly",
    );

    // A caller-provided JVM bound is respected: the fallback must neither
    // override it nor announce a default it did not apply.
    fs::write(&calls, "").expect("clear call log");
    fs::write(&payload_runs, "").expect("clear payload run log");
    let bounded = fixture_command()
        .env("PAYLOAD_STATUS", "29")
        .env("SYSTEMD_PROBE_STATUS", "1")
        .env(
            "REFERENCE_DIFFERENTIAL_JOB_FALLBACK_VIRTUAL_MEMORY_KIB",
            "10485760",
        )
        .env("REFERENCE_DIFFERENTIAL_K_OPTS", "-Xmx1g")
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
    let invalid = fixture_command()
        .env("PAYLOAD_STATUS", "0")
        .env("SYSTEMD_PROBE_STATUS", "0")
        .env("REFERENCE_DIFFERENTIAL_JOB_MEMORY_MAX_KIB", "eight-gib")
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

#[test]
fn compile_gate_scopes_haskell_runtime_options_to_the_reference_backend() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time after Unix epoch")
        .as_nanos();
    let fixture = std::env::temp_dir().join(format!(
        "k-rust-reference-environment-{}-{unique}",
        std::process::id()
    ));
    fs::create_dir(&fixture).expect("create environment fixture");
    let k_checkout = fake_k_checkout(
        &fixture,
        &["k-distribution/tests/regression-new/append/test.k"],
    );
    let calls = fixture.join("calls");
    let fake_kompile = fixture.join("kompile");
    let fake_kore_parser = fixture.join("kore-parser");
    let environment_state = r#"
if [[ ${GHCRTS+x} != x ]]; then
  ghcrts_state='<unset>'
elif [[ -z "$GHCRTS" ]]; then
  ghcrts_state='<empty>'
else
  ghcrts_state=$GHCRTS
fi
"#;
    fs::write(
        &fake_kompile,
        format!(
            r#"#!/usr/bin/env bash
set -euo pipefail
{environment_state}
printf 'kompile|%s\n' "$ghcrts_state" >>"$ENVIRONMENT_CALLS"
"#
        ),
    )
    .expect("write fake kompile");
    fs::write(
        &fake_kore_parser,
        format!(
            r#"#!/usr/bin/env bash
set -euo pipefail
{environment_state}
printf 'parser|%s\n' "$ghcrts_state" >>"$ENVIRONMENT_CALLS"
"#
        ),
    )
    .expect("write fake kore-parser");
    let gate_target = fake_gate_rust_toolchain(
        &fixture,
        r#"
if [[ "$1" == kcompile ]]; then
  args=("$@")
  for ((i = 0; i < ${#args[@]}; i++)); do
    if [[ "${args[i]}" == --output-directory ]]; then
      : >"${args[i+1]}/definition.kore"
    fi
  done
fi
"#,
        "",
    );
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        for executable in [&fake_kompile, &fake_kore_parser] {
            let mut permissions = fs::metadata(executable)
                .expect("fake executable metadata")
                .permissions();
            permissions.set_mode(0o755);
            fs::set_permissions(executable, permissions).expect("make fixture executable");
        }
    }
    let path = format!(
        "{}:{}",
        fixture.display(),
        std::env::var("PATH").expect("PATH")
    );
    let script = workspace.join("scripts/reference-differential.sh");
    let run = |pairing: &str, ghcrts: Option<&str>| {
        fs::write(&calls, "").expect("clear environment call log");
        let mut command = Command::new("bash");
        command
            .arg(&script)
            .arg("append")
            .env("PATH", &path)
            .env("ENVIRONMENT_CALLS", &calls)
            .env("K_CHECKOUT", &k_checkout)
            .env("K_KOMPILE", &fake_kompile)
            .env("K_KORE_PARSER", &fake_kore_parser)
            .env("KRUST_GATE_TARGET_DIR", &gate_target)
            .env("REFERENCE_DIFFERENTIAL_ALLOW_UNPINNED", "1")
            .env("REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND", "rlimit-as")
            .env("REFERENCE_DIFFERENTIAL_PAIRINGS", pairing);
        match ghcrts {
            Some(value) => {
                command.env("GHCRTS", value);
            }
            None => {
                command.env_remove("GHCRTS");
            }
        }
        let output = command.output().expect("run compile environment fixture");
        assert!(
            output.status.success(),
            "fixture control failed for {pairing} with GHCRTS={ghcrts:?}: status={}\nstdout:\n{}\nstderr:\n{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
        fs::read_to_string(&calls).expect("environment call log")
    };

    let default_haskell = run("haskell/rust", None);
    let overridden_haskell = run("haskell/rust", Some("-N3"));
    let non_haskell = run("kore/llvm", None);

    assert_eq!(
        default_haskell,
        "cargo-build|<unset>\ncargo-test|<unset>\nkompile|-N1\nkrust-kcompile|<unset>\nparser|<empty>\nparser|<empty>\ncomparator|<unset>\n",
        "the default must make only the reference Haskell frontend single-capability",
    );
    assert_eq!(
        overridden_haskell,
        "cargo-build|-N3\ncargo-test|-N3\nkompile|-N3\nkrust-kcompile|-N3\nparser|<empty>\nparser|<empty>\ncomparator|-N3\n",
        "a caller Haskell override must reach kompile while parsers remain compatible",
    );
    assert!(
        non_haskell.starts_with(
            "cargo-build|<unset>\ncargo-test|<unset>\nkompile|<unset>\nkrust-kcompile|<unset>\n"
        ),
        "the default must not reach the non-Haskell reference frontend: {non_haskell}",
    );
    assert_eq!(
        non_haskell.matches("parser|<empty>\n").count(),
        2,
        "both non-Haskell definition verifications must clear Haskell RTS options",
    );
    assert!(
        !non_haskell.contains("|-N1"),
        "the default Haskell runtime option leaked to a non-Haskell command: {non_haskell}",
    );

    fs::remove_dir_all(fixture).expect("remove environment fixture");
}

/// Write a fake executable that appends `label|<GHCRTS state>` to `$ENVIRONMENT_CALLS`.
///
/// `label` is expanded by the shell, so `cargo-${1:-missing}` records the cargo subcommand.
/// `prologue` runs before the record and may create the artifacts the script expects.
fn write_environment_probe(path: &Path, label: &str, prologue: &str) {
    fs::write(
        path,
        format!(
            r#"#!/usr/bin/env bash
set -euo pipefail
if [[ ${{GHCRTS+x}} != x ]]; then
  ghcrts_state='<unset>'
elif [[ -z "$GHCRTS" ]]; then
  ghcrts_state='<empty>'
else
  ghcrts_state=$GHCRTS
fi
{prologue}
printf '%s|%s\n' "{label}" "$ghcrts_state" >>"$ENVIRONMENT_CALLS"
"#
        ),
    )
    .unwrap_or_else(|error| panic!("write {}: {error}", path.display()));
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mut permissions = fs::metadata(path)
            .expect("fake executable metadata")
            .permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(path, permissions).expect("make fixture executable");
    }
}

/// Fake the Rust side of a gate: `cargo build` and `cargo test --no-run` (which reports the
/// comparator executable as a compiler artifact) succeed without building, the gate's krust
/// (under the returned `KRUST_GATE_TARGET_DIR`) runs `krust_prologue`, and the comparator runs
/// `comparator_prologue`. Each records `krust-<subcommand>`, `comparator` or `cargo-<subcommand>`
/// with its GHCRTS state in `$ENVIRONMENT_CALLS`.
fn fake_gate_rust_toolchain(
    fixture: &Path,
    krust_prologue: &str,
    comparator_prologue: &str,
) -> PathBuf {
    let target = fixture.join("gates");
    let krust = target.join("release/krust");
    fs::create_dir_all(krust.parent().unwrap()).expect("create fake gate target directory");
    let comparator = fixture.join("comparator");
    write_environment_probe(&krust, "krust-${1:-missing}", krust_prologue);
    write_environment_probe(&comparator, "comparator", comparator_prologue);
    write_environment_probe(
        &fixture.join("cargo"),
        "cargo-${1:-missing}",
        &format!(
            r#"
if [[ "$1" == test ]]; then
  printf '{{"reason":"compiler-artifact","target":{{"name":"reference_differential"}},"profile":{{"test":true}},"executable":"%s"}}\n' {comparator:?}
fi
"#
        ),
    );
    target
}

/// A fake `kompile` prologue: create the requested output definition like the real frontend.
const FAKE_KOMPILE_PROLOGUE: &str = r#"
while (($#)); do
  if [[ "$1" == --output-definition ]]; then
    mkdir -p "$2"
    : >"$2/definition.kore"
    shift 2
  else
    shift
  fi
done
"#;

fn environment_fixture(name: &str) -> PathBuf {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("time after Unix epoch")
        .as_nanos();
    let fixture =
        std::env::temp_dir().join(format!("k-rust-{name}-{}-{unique}", std::process::id()));
    fs::create_dir(&fixture).expect("create environment fixture");
    fixture
}

/// Supply the filesystem inputs checked by the gates even with mocked tools.
/// The probes do not parse K sources; no external checkout or builtin contents
/// are needed to test how the scripts pass runtime options to their children.
fn fake_k_checkout(fixture: &Path, sources: &[&str]) -> PathBuf {
    let checkout = fixture.join("k");
    fs::create_dir_all(checkout.join("k-distribution/include/kframework/builtin"))
        .expect("create fake K builtin directory");
    for source in sources {
        let path = checkout.join(source);
        fs::create_dir_all(path.parent().unwrap()).expect("create fake K source directory");
        fs::write(path, "").expect("write fake K source");
    }
    checkout
}

#[test]
fn symbolic_gate_scopes_haskell_runtime_options_to_the_reference_backend() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let fixture = environment_fixture("symbolic-environment");
    let k_checkout = fake_k_checkout(&fixture, &[]);
    let calls = fixture.join("calls");
    let fake_kompile = fixture.join("kompile");
    let fake_kore_parser = fixture.join("kore-parser");
    let fake_kore_exec = fixture.join("kore-exec");
    write_environment_probe(&fake_kompile, "kompile", FAKE_KOMPILE_PROLOGUE);
    write_environment_probe(&fake_kore_parser, "parser", "");
    write_environment_probe(&fake_kore_exec, "kore-exec", "");
    let target = fake_gate_rust_toolchain(&fixture, "", "");
    let path = format!(
        "{}:{}",
        fixture.display(),
        std::env::var("PATH").expect("PATH")
    );
    let script = workspace.join(SYMBOLIC_EXECUTION_SCRIPT_PATH);
    let run = |ghcrts: Option<&str>| {
        fs::write(&calls, "").expect("clear environment call log");
        let mut command = Command::new("bash");
        command
            .arg(&script)
            .arg("symbolic-owise")
            .env("PATH", &path)
            .env("ENVIRONMENT_CALLS", &calls)
            .env("K_CHECKOUT", &k_checkout)
            .env("K_KOMPILE", &fake_kompile)
            .env("K_KORE_PARSER", &fake_kore_parser)
            .env("K_KORE_EXEC", &fake_kore_exec)
            .env("KRUST_GATE_TARGET_DIR", &target)
            .env("REFERENCE_DIFFERENTIAL_ALLOW_UNPINNED", "1")
            .env("REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND", "rlimit-as");
        match ghcrts {
            Some(value) => {
                command.env("GHCRTS", value);
            }
            None => {
                command.env_remove("GHCRTS");
            }
        }
        let output = command.output().expect("run symbolic environment fixture");
        assert!(
            output.status.success(),
            "fixture control failed with GHCRTS={ghcrts:?}: status={}\nstdout:\n{}\nstderr:\n{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
        fs::read_to_string(&calls).expect("environment call log")
    };

    let default = run(None);
    let overridden = run(Some("-N3"));

    assert_eq!(
        default,
        "cargo-build|<unset>\ncargo-test|<unset>\nkompile|-N1\nparser|<empty>\nparser|<empty>\nkore-exec|-N1\nkrust-kore-exec|<unset>\ncomparator|<unset>\n",
        "the default must make the reference Haskell frontend and backend single-capability and leave the parsers and Rust side alone",
    );
    assert_eq!(
        overridden,
        "cargo-build|-N3\ncargo-test|-N3\nkompile|-N3\nparser|<empty>\nparser|<empty>\nkore-exec|-N3\nkrust-kore-exec|-N3\ncomparator|-N3\n",
        "a caller Haskell override must reach kompile and kore-exec while parsers remain compatible",
    );

    fs::remove_dir_all(fixture).expect("remove symbolic environment fixture");
}

#[test]
fn mir_execution_gate_scopes_haskell_runtime_options_to_the_reference_backend() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let fixture = environment_fixture("mir-environment");
    let k_checkout = fake_k_checkout(&fixture, &[]);
    let calls = fixture.join("calls");
    let fake_kompile = fixture.join("kompile");
    let fake_krun = fixture.join("krun");
    let fake_cargo = fixture.join("cargo");
    let fake_kmir_python = fixture.join("kmir-python");
    let mir_checkout = fixture.join("mir-semantics");
    let source = mir_checkout.join("kmir/src/kmir/kdist/mir-semantics/kmir.md");
    let smir = mir_checkout
        .join("kmir/src/tests/integration/data/exec-smir/main-a-b-c/main-a-b-c.smir.json");
    for pinned in [&source, &smir] {
        fs::create_dir_all(pinned.parent().unwrap()).expect("create fake MIR checkout");
        fs::write(pinned, "").expect("write fake MIR input");
    }
    write_environment_probe(&fake_kompile, "kompile", FAKE_KOMPILE_PROLOGUE);
    write_environment_probe(&fake_krun, "krun", "");
    write_environment_probe(&fake_cargo, "cargo-${1:-missing}", "");
    // reference-mir-initial.py receives (definition, smir, initial); the fake writes the pattern.
    write_environment_probe(&fake_kmir_python, "kmir-python", ": >\"$4\"\n");
    let path = format!(
        "{}:{}",
        fixture.display(),
        std::env::var("PATH").expect("PATH")
    );
    let script = workspace.join("scripts/reference-mir-execution-differential.sh");
    let run = |ghcrts: Option<&str>| {
        fs::write(&calls, "").expect("clear environment call log");
        let mut command = Command::new("bash");
        command
            .arg(&script)
            .env("PATH", &path)
            .env("ENVIRONMENT_CALLS", &calls)
            .env("K_CHECKOUT", &k_checkout)
            .env("K_KOMPILE", &fake_kompile)
            .env("K_KRUN", &fake_krun)
            .env("KMIR_PYTHON", &fake_kmir_python)
            .env("MIR_SEMANTICS_CHECKOUT", &mir_checkout)
            .env("REFERENCE_DIFFERENTIAL_ALLOW_UNPINNED", "1")
            .env("REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND", "rlimit-as");
        match ghcrts {
            Some(value) => {
                command.env("GHCRTS", value);
            }
            None => {
                command.env_remove("GHCRTS");
            }
        }
        let output = command.output().expect("run MIR environment fixture");
        assert!(
            output.status.success(),
            "fixture control failed with GHCRTS={ghcrts:?}: status={}\nstdout:\n{}\nstderr:\n{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
        fs::read_to_string(&calls).expect("environment call log")
    };

    let default = run(None);
    let overridden = run(Some("-N3"));

    assert_eq!(
        default,
        "kompile|-N1\ncargo-run|<unset>\nkmir-python|<unset>\nkrun|-N1\ncargo-run|<unset>\ncargo-test|<unset>\n",
        "the default must make the reference Haskell kompile and krun single-capability and leave the Rust side alone",
    );
    assert_eq!(
        overridden,
        "kompile|-N3\ncargo-run|-N3\nkmir-python|-N3\nkrun|-N3\ncargo-run|-N3\ncargo-test|-N3\n",
        "a caller Haskell override must reach the reference kompile and krun",
    );

    fs::remove_dir_all(fixture).expect("remove MIR environment fixture");
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

/// `scripts/reference-server-port.sh` reads the port a gate's server listens on from that
/// server's own listening socket, so a server told to bind port 0 (a free port the kernel assigns
/// at its bind) is found on that port, also behind a wrapper that forks it, and a server pinned
/// to a port another process holds is reported as failed instead of the gate talking to the
/// other process.
#[test]
fn the_gates_read_a_server_port_from_the_server_they_started() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let fixture = environment_fixture("server-port");
    let other = std::net::TcpListener::bind("127.0.0.1:0").expect("a listener of another process");
    let taken = other.local_addr().expect("its address").port();
    let script = r#"
set -u
source "$WORKSPACE/scripts/reference-server-port.sh"
server='import os, socket, sys, time
s = socket.socket()
s.bind(("127.0.0.1", int(sys.argv[1])))
s.listen()
with open(sys.argv[2], "w") as out:
    out.write("%d %d\n" % (s.getsockname()[1], os.getpid()))
time.sleep(60)'
started() {
  until [[ -s "$1" ]]; do sleep 0.05; done
  read -r bound pid <"$1"
}
python3 -c "$server" 0 "$FIXTURE/direct" 2>"$FIXTURE/direct.log" &
reference_wait_for_server_port $! "$FIXTURE/direct.log" 0
started "$FIXTURE/direct"
echo "direct $reference_listening_port $bound"
kill "$pid"
(python3 -c "$server" 0 "$FIXTURE/forked" 2>"$FIXTURE/forked.log"; true) &
reference_wait_for_server_port $! "$FIXTURE/forked.log" 0
started "$FIXTURE/forked"
echo "forked $reference_listening_port $bound"
kill "$pid"
python3 -c "$server" "$TAKEN" "$FIXTURE/taken" 2>"$FIXTURE/taken.log" &
if reference_wait_for_server_port $! "$FIXTURE/taken.log" "$TAKEN" 2>/dev/null; then
  echo "taken accepted"
else
  echo "taken refused"
fi
wait
"#;
    let output = Command::new("bash")
        .arg("-c")
        .arg(script)
        .env("WORKSPACE", &workspace)
        .env("FIXTURE", &fixture)
        .env("TAKEN", taken.to_string())
        .stdin(std::process::Stdio::null())
        .output()
        .expect("run the server-port helper");
    drop(other);
    fs::remove_dir_all(&fixture).expect("remove server-port fixture");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let lines = stdout.lines().collect::<Vec<_>>();
    assert_eq!(lines.len(), 3, "{stdout}{stderr}");
    for (line, label) in lines.iter().zip(["direct", "forked"]) {
        let words = line.split_whitespace().collect::<Vec<_>>();
        assert_eq!(words.len(), 3, "{stdout}{stderr}");
        assert_eq!(words[0], label, "{stdout}{stderr}");
        assert_ne!(words[1], "0", "{stdout}{stderr}");
        assert_eq!(
            words[1], words[2],
            "the helper found another port: {stdout}{stderr}"
        );
    }
    assert_eq!(lines[2], "taken refused", "{stdout}{stderr}");
}

/// The RPC gate starts both of its servers on a kernel-assigned port unless the caller pins one,
/// and sends every request to the port the server it started listens on
/// (`scripts/reference-server-port.sh`), so concurrent runs never share or steal a server.
#[test]
fn rpc_gate_reads_each_server_port_from_the_server_it_started() {
    for needle in [
        "source \"$workspace/scripts/reference-server-port.sh\"",
        "reference_port=${REFERENCE_RPC_PORT:-0}",
        "rust_port=${RUST_RPC_PORT:-0}",
        "reference_wait_for_server_port \"$server_pid\" \"$server_log\"",
    ] {
        assert!(RPC_SCRIPT.contains(needle), "RPC gate lacks {needle}");
    }
    let requests = RPC_SCRIPT
        .lines()
        .filter(|line| line.trim_start().starts_with("collect_responses \""))
        .collect::<Vec<_>>();
    assert_eq!(requests.len(), 2, "one session per server kind");
    for request in requests {
        assert!(
            request.contains("collect_responses \"$server_port\""),
            "a session not addressed to its own server's port: {request}"
        );
    }
}

/// The RPC gate's request states are functions of the case's program and definition, so its
/// reference `krun` calls run on an empty standard input, the reference-output cache's default
/// without `--stdin`, rather than reading (or, for a terminal or an open pipe, blocking on and
/// running uncached with) the caller's.
#[test]
fn rpc_gate_request_states_do_not_read_the_callers_standard_input() {
    let calls = RPC_SCRIPT
        .match_indices("reference_cached krun")
        .map(|(index, _)| {
            let start = RPC_SCRIPT[..index].rfind('\n').map_or(0, |line| line + 1);
            shell_command_at(RPC_SCRIPT, start)
        })
        .collect::<Vec<_>>();
    assert_eq!(calls.len(), 2, "run_reference_krun and generate_state");
    for call in calls {
        assert!(!call.contains("--stdin"), "{call}");
    }
}

/// `scripts/backend-smoke.sh`, when it builds krust itself (no `KRUST_BIN`), acquires Z3 as
/// `KRUST_GATE_Z3` selects for the gates: `system` builds the same `cli` features without the
/// release download, and the default keeps Cargo's default features.
#[test]
fn backend_smoke_builds_krust_with_the_gates_z3_selection() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    for (selection, without_download) in [
        (Some("system"), true),
        (Some("gh-release"), false),
        (None, false),
    ] {
        let fixture = environment_fixture("backend-smoke");
        let calls = fixture.join("calls");
        write_environment_probe(
            &fixture.join("cargo"),
            "cargo",
            r#"printf 'cargo %s\n' "$*" >>"$ENVIRONMENT_CALLS"; exit 3"#,
        );
        let path = format!(
            "{}:{}",
            fixture.display(),
            std::env::var("PATH").expect("PATH")
        );
        let mut command = Command::new("bash");
        command
            .arg(workspace.join("scripts/backend-smoke.sh"))
            .env("PATH", &path)
            .env("ENVIRONMENT_CALLS", &calls)
            .env_remove("KRUST_BIN")
            .env_remove("KRUST_GATE_Z3")
            .stdin(std::process::Stdio::null());
        if let Some(selection) = selection {
            command.env("KRUST_GATE_Z3", selection);
        }
        let output = command.output().expect("run backend smoke fixture");
        let log = fs::read_to_string(&calls).unwrap_or_default();
        fs::remove_dir_all(&fixture).expect("remove backend smoke fixture");
        assert_ne!(output.status.code(), Some(0), "the stand-in cargo fails");
        let cargo = log
            .lines()
            .find(|line| line.starts_with("cargo run "))
            .unwrap_or_else(|| panic!("{selection:?}: no cargo run: {log}"));
        assert_eq!(
            cargo.contains(" --no-default-features --features cli "),
            without_download,
            "{selection:?}: {cargo}"
        );
        assert!(
            cargo.contains(" -p k-rust --bin krust -- kcompile "),
            "{cargo}"
        );
    }
}
