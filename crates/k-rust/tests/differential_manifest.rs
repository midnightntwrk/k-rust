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
const CI_WORKFLOW: &str = include_str!("../../../.github/workflows/ci.yml");
const GATES: &str = include_str!("../../../scripts/gates.toml");
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
        .env("REFERENCE_DIFFERENTIAL_ALLOW_UNPINNED", "1");
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

    let exceptions_of = |name: &str| {
        manifest["execution"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|entry| entry["name"].as_str() == Some(name))
            .flat_map(|entry| {
                entry
                    .get("oracle-exception")
                    .and_then(Value::as_array)
                    .into_iter()
                    .flatten()
            })
            .collect::<Vec<_>>()
    };
    let hook_exceptions = exceptions_of("hook-boundaries");
    assert_eq!(
        hook_exceptions.len(),
        2,
        "STRING.find and BYTES.replaceAt exceptions"
    );
    let list_exceptions = exceptions_of("list-cell-positions");
    assert_eq!(
        list_exceptions
            .iter()
            .map(|exception| exception["program"].as_str().unwrap_or_default())
            .map(|program| program.rsplit('/').next().unwrap_or_default())
            .collect::<Vec<_>>(),
        ["last.pgm", "drop-last.pgm", "mk-last-get.pgm"],
        "a leading ... in a type=\"List\" collection reads, removes and adds at the back"
    );
    for exception in hook_exceptions.into_iter().chain(list_exceptions) {
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
/// fake server still listened after the gate exited. `GHCRTS` is removed unless `environment`
/// sets it. Three switches change the fakes, all off by default:
/// - `FAKE_GHC_RUNTIME_CHECK=1`: the fake `kore-parser` and `kore-rpc-client`, which stand for
///   binaries of the non-threaded GHC runtime, refuse to start under a `GHCRTS` holding `-N`, as
///   the pinned ones do;
/// - `FAKE_REFERENCE_RESULT`: what the fake reference `krun` prints;
/// - `FAKE_ECHO_REFERENCE=1`: the fake `kore-parser` answers with a digest of the pattern file it
///   read, the fake client answers `simplify` with the term it was sent, and the comparator logs
///   `comparator-reference NAME DIGEST` for the reference input it received, so the log shows
///   which result reached the comparison.
fn execution_gate_with_reference_simplifier(
    case: &str,
    environment: &[(&str, &str)],
) -> (Option<i32>, String, String, String, bool) {
    execution_gate_with_reference_simplifier_under(case, environment, &[])
}

/// [`execution_gate_with_reference_simplifier`] started through `caller`, a command that execs
/// its arguments (`bash GATE CASE`).
fn execution_gate_with_reference_simplifier_under(
    case: &str,
    environment: &[(&str, &str)],
    caller: &[&str],
) -> (Option<i32>, String, String, String, bool) {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let fixture = environment_fixture("execution-simplifier");
    let k_checkout = fake_k_checkout(&fixture, &[]);
    let calls = fixture.join("calls");
    write_environment_probe(&fixture.join("kompile"), "kompile", FAKE_KOMPILE_PROLOGUE);
    write_environment_probe(
        &fixture.join("krun"),
        "krun",
        r#"
if [[ -n ${FAKE_REFERENCE_RESULT:-} ]]; then
  printf '%s\n' "$FAKE_REFERENCE_RESULT"
else
  printf '%s\n' '\or{S{}}(a{}(), b{}())'
fi
"#,
    );
    write_environment_probe(&fixture.join("kast"), "kast", "");
    write_environment_probe(
        &fixture.join("kore-parser"),
        "kore-parser $*",
        &format!(
            "{FAKE_NON_THREADED_GHC_RUNTIME}{}",
            r#"
pattern=
for ((i = 1; i <= $#; i++)); do
  if [[ ${!i} == --pattern ]]; then j=$((i + 1)); pattern=${!j}; fi
done
if [[ ${FAKE_ECHO_REFERENCE:-0} == 1 ]]; then
  printf '{"format":"KORE","version":1,"term":{"tag":"DV","sort":{"tag":"SortApp","name":"S","args":[]},"value":"%s"}}\n' \
    "$(cksum <"$pattern" | cut -d' ' -f1)"
else
  printf '%s\n' '{"format":"KORE","version":1,"term":{"tag":"Top","sort":{"tag":"SortApp","name":"S","args":[]}}}'
fi
"#
        ),
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
        &format!(
            "{FAKE_NON_THREADED_GHC_RUNTIME}{}",
            r#"
printf 'kore-rpc-client %s|\n' "$*" >>"$ENVIRONMENT_CALLS"
while (($#)); do [[ $1 == -o ]] && out=$2; [[ $1 == simplify ]] && request=$2; shift; done
if [[ ${FAKE_ECHO_REFERENCE:-0} == 1 ]]; then
  printf '{"jsonrpc":"2.0","id":1,"result":{"state":%s}}\n' "$(cat "$request")" >"$out"
elif [[ ${FAKE_RPC_ERROR:-0} == 1 ]]; then
  printf '%s\n' '{"jsonrpc":"2.0","id":1,"error":{"code":-32002,"message":"Could not verify pattern"}}' >"$out"
else
  printf '%s\n' '{"jsonrpc":"2.0","id":1,"result":{"state":{"format":"KORE","version":1,"term":{"tag":"Bottom","sort":{"tag":"SortApp","name":"S","args":[]}}}}}' >"$out"
fi
"#
        ),
    );
    let target = fake_gate_rust_toolchain(
        &fixture,
        "",
        r#"
printf 'comparator %s|\n' "$(basename "$K_REFERENCE_EXECUTION")" >>"$ENVIRONMENT_CALLS"
if [[ ${FAKE_ECHO_REFERENCE:-0} == 1 ]]; then
  printf 'comparator-reference %s %s|\n' "$(basename "$K_REFERENCE_EXECUTION")" \
    "$(cksum <"$K_REFERENCE_EXECUTION" | cut -d' ' -f1)" >>"$ENVIRONMENT_CALLS"
fi
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
    let mut command = match caller {
        [] => Command::new("bash"),
        [program, arguments @ ..] => {
            let mut command = Command::new(program);
            command.args(arguments).arg("bash");
            command
        }
    };
    command
        .arg(workspace.join("scripts/reference-non-imp-execution-differential.sh"))
        .arg(case)
        .env_remove("GHCRTS")
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

/// The prologue of a fake binary of the non-threaded GHC runtime under `FAKE_GHC_RUNTIME_CHECK=1`:
/// like the pinned `kore-parser` and `kore-rpc-client`, it refuses runtime options that need the
/// threaded runtime.
const FAKE_NON_THREADED_GHC_RUNTIME: &str = r#"
if [[ ${FAKE_GHC_RUNTIME_CHECK:-0} == 1 && ${GHCRTS:-} == *-N* ]]; then
  echo "the flag ${GHCRTS} requires the program to be built with -threaded" >&2
  exit 1
fi
"#;

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
            .filter(|line| line.contains("N41: comparing with the reference result as the reference simplifies it: The pinned krun reports heating branches"))
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

/// N41 compares the port's result with the reference result as the reference simplifies it, so
/// the simplified result is a function of the reference result: two runs whose reference results
/// differ, and nothing else, hand the comparison two different simplified results. A gate that
/// simplified any other file (the port's own result, which makes the comparison a
/// self-comparison) hands it the same one twice.
#[test]
fn execution_gate_simplifies_the_reference_result_it_received() {
    let digests = |reference: &str| {
        let (status, log, stdout, stderr, _) = execution_gate_with_reference_simplifier(
            "star-cell-heating-set",
            &[
                ("FAKE_ECHO_REFERENCE", "1"),
                ("FAKE_REFERENCE_RESULT", reference),
                ("REFERENCE_CACHE", "off"),
            ],
        );
        assert_eq!(status, Some(0), "{stdout}{stderr}");
        let digests = log
            .lines()
            .filter_map(|line| line.strip_prefix("comparator-reference "))
            .filter(|line| line.contains(".json "))
            .map(str::to_owned)
            .collect::<Vec<_>>();
        assert_eq!(
            digests.len(),
            2,
            "one simplified comparison per program: {log}"
        );
        digests
    };
    let first = digests(r"\or{S{}}(a{}(), b{}())");
    let second = digests(r"\or{S{}}(c{}(), d{}())");
    for (first, second) in first.iter().zip(&second) {
        assert_ne!(
            first, second,
            "the simplified result did not change with the reference result"
        );
    }
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
            30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
        ])
        .map(|id| format!("N{id}"))
        .collect::<BTreeSet<_>>();
    assert_eq!(
        ids.into_iter().map(str::to_owned).collect::<BTreeSet<_>>(),
        expected,
        "the gate register must contain N1, N3 through N28, and N30 through N47 (N29 is reserved); global UNIQUE_ID exclusion N2 is retired"
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
        (1..=10).map(|id| format!("C{id}")).collect::<BTreeSet<_>>(),
        "the conformance register must contain C1 through C10"
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
    // C10 is N4's reading of a checked-in KORE output: every `?` variable that neither the
    // recipe's --pattern nor the request names is a rule existential, renamed bijectively and
    // sort-preservingly per disjunct.
    let c10 = rows
        .iter()
        .find(|row| row["id"].as_str() == Some("C10"))
        .expect("C10 row");
    assert_eq!(
        c10["anchor_symbol"].as_str(),
        Some("kore_output_comparison_environment")
    );
    for needle in [
        "--output kore",
        "executed_kore_matches_the_reference_backend",
        "K_DIFFERENTIAL_PATTERN_EXISTENTIALS",
        "bijective, sort-preserving renaming per disjunct",
        "--pattern",
        "request variable",
    ] {
        assert!(
            c10["rule"].as_str().unwrap().contains(needle),
            "C10 must state {needle}"
        );
    }
    for needle in [
        "docs/compatibility.md#result-variables",
        "docs/compatibility.md#variable-names",
        "docs/compatibility.md#comparison-contract",
    ] {
        assert!(
            c10["justification"].as_str().unwrap().contains(needle),
            "C10 must cite {needle}"
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

/// A recorded divergence from the reference is adjudicated: its reason links the
/// docs/compatibility.md section that argues it, and that section names it and its kind. A
/// compile case is named by its case name, a kast entry by `case:entry`.
#[test]
fn recorded_divergences_are_the_adjudicated_ones() {
    let manifest = MANIFEST.parse::<Value>().expect("valid differential TOML");
    let compatibility = fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../docs/compatibility.md"),
    )
    .expect("docs/compatibility.md");
    let mut divergences = Vec::new();
    for entry in manifest["compile"].as_array().expect("compile cases") {
        if entry.get("expect").and_then(Value::as_str) == Some("port-accepts") {
            let name = entry["name"].as_str().expect("compile name");
            divergences.push((name.to_owned(), "port-accepts", entry));
        }
    }
    for case in manifest["kast"].as_array().expect("kast cases") {
        let case_name = case["name"].as_str().expect("kast name");
        for kind in ["port-accepts", "port-rejects"] {
            for entry in case
                .get(kind)
                .and_then(Value::as_array)
                .into_iter()
                .flatten()
            {
                let entry_name = entry["name"].as_str().expect("kast entry name");
                divergences.push((format!("{case_name}:{entry_name}"), kind, entry));
            }
        }
    }
    let mut names = BTreeSet::new();
    for (name, kind, entry) in divergences {
        let reason = entry["reason"].as_str().expect("divergence reason");
        let anchor = reason
            .split_whitespace()
            .find_map(|word| word.strip_prefix("docs/compatibility.md#"))
            .map(|anchor| anchor.trim_end_matches('.'))
            .unwrap_or_else(|| panic!("{kind} {name} must link its compatibility section"));
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
            section.contains(&format!("`{name}`")) && section.contains(kind),
            "docs/compatibility.md#{anchor} must record {name} as a {kind} divergence",
        );
        names.insert(name);
    }
    assert_eq!(
        names,
        BTreeSet::from(
            [
                "semcast3",
                "semcast4",
                "regex-anchor-local:end-anchor-at-the-end-of-the-text",
                "regex-anchor-local:start-anchor-at-the-end-of-the-text",
            ]
            .map(String::from)
        ),
        "the adjudicated divergence set changed",
    );
}

#[test]
fn differential_manifest_requires_a_reason_for_a_kast_divergence() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let fixture = environment_fixture("manifest-kast-entries");
    let helper = fixture.join("reference-manifest.py");
    fs::copy(workspace.join("scripts/reference-manifest.py"), &helper).unwrap();
    for (entry, valid) in [
        ("[[kast.accept]]\nname = \"e\"\n", true),
        ("[[kast.reject]]\nname = \"e\"\n", true),
        (
            "[[kast.port-rejects]]\nname = \"e\"\nreason = \"why\"\n",
            true,
        ),
        (
            "[[kast.port-accepts]]\nname = \"e\"\nreason = \"why\"\nreference-error = \"Scanner error\"\n",
            true,
        ),
        ("[[kast.port-rejects]]\nname = \"e\"\n", false),
        (
            "[[kast.port-rejects]]\nname = \"e\"\nreason = \" \"\n",
            false,
        ),
        (
            "[[kast.port-rejects]]\nname = \"e\"\nreason = \"why\"\nreference-error = \"Scanner error\"\n",
            false,
        ),
        (
            "[[kast.port-accepts]]\nname = \"e\"\nreason = \"why\"\n",
            false,
        ),
        (
            "[[kast.port-accepts]]\nname = \"e\"\nreference-error = \"Scanner error\"\n",
            false,
        ),
        ("[[kast.accept]]\nname = \"e\"\nreason = \"why\"\n", false),
        (
            "[[kast.reject]]\nname = \"e\"\nreference-error = \"Scanner error\"\n",
            false,
        ),
        (
            "[[kast.port-accept]]\nname = \"e\"\nreason = \"why\"\n",
            false,
        ),
    ] {
        fs::write(
            fixture.join("reference-differential.toml"),
            format!(
                "[[kast]]\nname = \"fixture\"\nrequires = [\"reference-toolchain\"]\n\n{entry}"
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
            "{entry}: {stderr}"
        );
        if !valid {
            assert!(stderr.contains("invalid differential manifest"), "{stderr}");
        }
    }
    fs::remove_dir_all(fixture).unwrap();
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
fn kast_gate_fails_when_either_side_of_a_recorded_divergence_moves() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let fixture = environment_fixture("kast-divergence-gate");
    let k_checkout = fake_k_checkout(&fixture, &[]);
    let fake_kompile = fixture.join("kompile");
    write_environment_probe(&fake_kompile, "kompile", FAKE_KOMPILE_PROLOGUE);
    // The pinned kast of the regex-anchor-local case: the agreed entries answer as recorded, and
    // the two divergent texts answer as the environment says. Any other text, including an
    // agreed one that lost its line end on the way, is an error.
    let fake_kast = fixture.join("kast");
    write_environment_probe(
        &fake_kast,
        "kast",
        r#"
while (($#)); do
  if [[ "$1" == --expression ]]; then expression=$2; fi
  shift
done
case "$expression" in
  $'a\n' | $'b\n') echo '{}' ;;
  $' b\n') echo "[Error] Inner Parser: Scanner error: unexpected character sequence 'b'." >&2; exit 113 ;;
  a) echo '{}'; exit "$FAKE_KAST_A_STATUS" ;;
  b) echo "$FAKE_KAST_B_MESSAGE" >&2; exit "$FAKE_KAST_B_STATUS" ;;
  *) echo "unexpected expression $(printf %q "$expression")" >&2; exit 3 ;;
esac
"#,
    );
    let krust_arguments = fixture.join("krust-arguments");
    let gate_target = fake_gate_rust_toolchain(
        &fixture,
        r#"printf '%s\0' "$@" >"$FAKE_KRUST_ARGUMENTS"; exit "$FAKE_KRUST_STATUS""#,
        "",
    );
    let calls = fixture.join("calls");
    let path = format!(
        "{}:{}",
        fixture.display(),
        std::env::var("PATH").expect("PATH")
    );
    let script = workspace.join("scripts/reference-kast-differential.sh");
    const PINNED: &str = "[Error] Inner Parser: Scanner error: unexpected character sequence 'b'.";
    let run = |a: u8, b: u8, message: &str, krust: u8| {
        let output = Command::new("bash")
            .arg(&script)
            .arg("regex-anchor-local")
            .env("PATH", &path)
            .env("K_CHECKOUT", &k_checkout)
            .env("K_KOMPILE", &fake_kompile)
            .env("K_KAST", &fake_kast)
            .env("FAKE_KAST_A_STATUS", a.to_string())
            .env("FAKE_KAST_B_STATUS", b.to_string())
            .env("FAKE_KAST_B_MESSAGE", message)
            .env("FAKE_KRUST_STATUS", krust.to_string())
            .env("FAKE_KRUST_ARGUMENTS", &krust_arguments)
            .env("KRUST_GATE_TARGET_DIR", &gate_target)
            .env("ENVIRONMENT_CALLS", &calls)
            .env("REFERENCE_DIFFERENTIAL_ALLOW_UNPINNED", "1")
            .output()
            .expect("run kast divergence gate fixture");
        (
            output.status.code(),
            String::from_utf8_lossy(&output.stdout).into_owned(),
            String::from_utf8_lossy(&output.stderr).into_owned(),
        )
    };

    let (status, stdout, stderr) = run(0, 113, PINNED, 0);
    assert_eq!(
        status,
        Some(0),
        "recorded divergences hold: {stdout}\n{stderr}"
    );
    for line in [
        "[regex-anchor-local:start-anchor-at-the-end-of-the-text] recorded divergence: A token regex with a start anchor",
        "[regex-anchor-local:start-anchor-at-the-end-of-the-text] reference rejection: [Error] Inner Parser: Scanner error",
        "[regex-anchor-local:end-anchor-at-the-end-of-the-text] recorded divergence: A token regex with an end anchor",
        "corpus passed",
    ] {
        assert!(stdout.contains(line), "{line}: {stdout}");
    }
    // krust is asked to accept the agreed and the port-accepts texts and to reject the agreed
    // rejection and the port-rejects text, each with its line ends.
    let arguments = fs::read(&krust_arguments).expect("krust arguments");
    let arguments = arguments
        .split(|byte| *byte == 0)
        .map(|argument| String::from_utf8_lossy(argument).into_owned())
        .collect::<Vec<_>>();
    for expected in [
        ["--batch-case", "end-anchor-before-a-newline", "Foo", "a\n"],
        [
            "--batch-case",
            "start-anchor-at-the-start-before-a-newline",
            "Bar",
            "b\n",
        ],
        [
            "--batch-case",
            "start-anchor-at-the-end-of-the-text",
            "Bar",
            "b",
        ],
        [
            "--batch-reject-case",
            "start-anchor-after-a-space",
            "Bar",
            " b\n",
        ],
        [
            "--batch-reject-case",
            "end-anchor-at-the-end-of-the-text",
            "Foo",
            "a",
        ],
    ] {
        assert!(
            arguments.windows(4).any(|window| window == expected),
            "krust was not given {expected:?}: {arguments:?}"
        );
    }

    for (a, b, message, krust, diagnostic) in [
        (
            0,
            0,
            PINNED,
            0,
            "reference kast accepted port-accepts case regex-anchor-local:start-anchor-at-the-end-of-the-text",
        ),
        (
            0,
            1,
            "Error: Could not reserve enough space for object heap",
            0,
            "lacks the recorded reference-error \"Scanner error: unexpected character sequence 'b'\"",
        ),
        (
            1,
            113,
            PINNED,
            0,
            "reference kast rejected port-rejects case regex-anchor-local:end-anchor-at-the-end-of-the-text",
        ),
    ] {
        let (status, stdout, stderr) = run(a, b, message, krust);
        assert_eq!(status, Some(1), "{diagnostic}: {stdout}\n{stderr}");
        assert!(stderr.contains(diagnostic), "{stderr}");
        assert!(!stdout.contains("corpus passed"), "{stdout}");
    }
    // krust's side is its batch session, which fails when a port-accepts text is rejected or a
    // port-rejects text accepted.
    let (status, stdout, stderr) = run(0, 113, PINNED, 1);
    assert_ne!(status, Some(0), "{stdout}\n{stderr}");
    assert!(!stdout.contains("corpus passed"), "{stdout}");
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
    let registry = GATES.parse::<Value>().expect("valid gate registry TOML");
    let certification = registry["gate"]
        .as_array()
        .expect("gate entries")
        .iter()
        .filter(|gate| matches!(gate["run"].as_str(), Some("certification" | "heavy")))
        .map(|gate| gate["command"].as_str().expect("gate command"))
        .collect::<BTreeSet<_>>();
    for command in [
        "scripts/reference-differential.sh append ambiguous-rewrite casts cell-map fresh-variables list-set macro-rewrite parametric-semantic-cast hooked-namespaces star-cell-config overload-constructors owise-functions owise-competitors owise concrete-rw2 cast-inner",
        "scripts/reference-differential.sh fun-int-list-config",
        "scripts/reference-differential.sh imp fresh-name-collision parametric assoc-strict undefined-sort semcast2 semcast3 semcast4",
        "REFERENCE_DIFFERENTIAL_PAIRINGS=haskell/rust scripts/reference-differential.sh wasm mir evm-equivalence",
        "scripts/reference-kast-differential.sh wasm mir evm-equivalence",
        "scripts/reference-non-imp-execution-differential.sh imp collections hook-boundaries",
        "scripts/reference-non-imp-execution-differential.sh depth-bounded-search branching-execution concrete-symbolic-rules trivial-result-execution list-cell-positions",
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
        r#"# Run `scripts/run-gates.sh --changed BASE..HEAD` after a change; it runs every entry the change owes, and lists the host = "human-uid" ones as not run under an agent-N user."#,
        "# The heavy driver runs `scripts/run-gates.sh --run heavy --changed BASE..HEAD` at a host UID on each integration head.",
        "# PR description (any change that owes a certification or heavy entry):",
        "#   1. the summary of `scripts/run-gates.sh --changed BASE..HEAD`, one row per entry: pass/fail, wall s, peak RSS MiB (scripts/conformance/measure.py), and the cases each entry ran",
        "#   2. the ratchet block printed by `scripts/conformance-ratchet.sh --label change --cases <affected cases> --log target/conformance/ratchet.toml --runs-dir target/conformance/runs` (or --all for full certification)",
        "#   3. the permanent multi-alias oracle-exclusion count printed by scripts/reference-differential.sh",
    ] {
        assert!(
            GATES.lines().any(|line| line == requirement),
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

/// Every inconsistency between the `[[gate]]` entries of the registry (`scripts/gates.toml`) and
/// the manifest's cases. The registry's own keys, kinds and path patterns are checked by
/// `scripts/run-gates.sh --check` (`the_gate_registry_is_valid_against_the_workspace`).
///
/// A gate command is `[NAME=value ...] script [argument ...]`, run from the workspace root. For a
/// script of `CASE_SCRIPTS` the arguments are case names of its section, every one of which must
/// be runnable there (the script refuses any other name before it does work), and no arguments
/// select every runnable case. A runnable case must be selected by some gate or carry
/// `manual = "<reason>"`; a case that some gate selects must not also claim to be manual.
fn gate_model_failures(registry: &Value, manifest: &Value, workspace: &Path) -> Vec<String> {
    let mut failures = Vec::new();
    let mut gated = BTreeSet::<(&str, &str)>::new();
    let mut names = BTreeSet::new();
    let Some(gates) = registry.get("gate").and_then(Value::as_array) else {
        return vec!["the registry has no [[gate]] entries".into()];
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
    let registry = GATES.parse::<Value>().expect("valid gate registry TOML");
    let failures = gate_model_failures(&registry, &manifest, &workspace);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn gate_model_rejects_unlisted_misnamed_and_falsely_manual_cases() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let manifest = MANIFEST.parse::<Value>().expect("valid differential TOML");
    let registry = GATES.parse::<Value>().expect("valid gate registry TOML");

    let mut unlisted = manifest.clone();
    let mut probe = unlisted["compile"][0].clone();
    probe["name"] = Value::String("unlisted-probe".into());
    unlisted["compile"]
        .as_array_mut()
        .unwrap()
        .push(probe.clone());
    assert_eq!(
        gate_model_failures(&registry, &unlisted, &workspace),
        ["compile case unlisted-probe is in no [[gate]] and carries no manual reason"],
    );

    let mut manual = unlisted.clone();
    let entries = manual["compile"].as_array_mut().unwrap();
    entries.last_mut().unwrap().as_table_mut().unwrap().insert(
        "manual".into(),
        Value::String("the probe is run by hand".into()),
    );
    assert!(gate_model_failures(&registry, &manual, &workspace).is_empty());

    let mut blocked = unlisted.clone();
    blocked["compile"]
        .as_array_mut()
        .unwrap()
        .last_mut()
        .unwrap()["requires"] = Value::Array(vec![Value::String("semantics-support".into())]);
    assert!(
        gate_model_failures(&registry, &blocked, &workspace).is_empty(),
        "a case no script can run needs no gate"
    );

    let mut falsely_manual = manifest.clone();
    falsely_manual["compile"][0]
        .as_table_mut()
        .unwrap()
        .insert("manual".into(), Value::String("stale".into()));
    let first = manifest["compile"][0]["name"].as_str().unwrap();
    assert_eq!(
        gate_model_failures(&registry, &falsely_manual, &workspace),
        [format!(
            "compile case {first} is run by a gate but carries a manual reason"
        )],
    );

    let mut misnamed = registry.clone();
    let gate = misnamed["gate"]
        .as_array_mut()
        .unwrap()
        .first_mut()
        .unwrap();
    let command = format!("{} no-such-case", gate["command"].as_str().unwrap());
    gate["command"] = Value::String(command);
    let gate_name = registry["gate"][0]["name"].as_str().unwrap();
    assert_eq!(
        gate_model_failures(&misnamed, &manifest, &workspace),
        [format!(
            "gate {gate_name} names `no-such-case`, which is not a runnable compile case"
        )],
    );

    let mut all_cases = registry.clone();
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
        gate_model_failures(&all_cases, &unlisted, &workspace).is_empty(),
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

/// The weekly entries of the gate registry are the differential workflow's gate steps, so the
/// registry stays the one record of which case runs where until the workflow reads its case lists
/// from it.
#[test]
fn weekly_gates_are_the_differential_workflow_steps() {
    let registry = GATES.parse::<Value>().expect("valid gate registry TOML");
    let mut weekly = registry["gate"]
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

/// A `ci` entry of the gate registry is a step of the CI workflow with the same command, so the
/// registry's record of what runs on every push is what runs.
#[test]
fn ci_gates_are_ci_workflow_steps() {
    let registry = GATES.parse::<Value>().expect("valid gate registry TOML");
    let workflow = workflow_script_commands(CI_WORKFLOW);
    let ci = registry["gate"]
        .as_array()
        .expect("gate entries")
        .iter()
        .filter(|gate| gate["run"].as_str() == Some("ci"))
        .map(|gate| gate["command"].as_str().expect("gate command"))
        .collect::<Vec<_>>();
    assert!(!ci.is_empty(), "the registry has no ci entry");
    for command in ci {
        assert!(
            workflow.iter().any(|step| step == command),
            "the ci entry `{command}` is not a step of .github/workflows/ci.yml: {workflow:?}"
        );
    }
}

/// `scripts/run-gates.sh` with the given arguments, from the workspace root: its exit code and
/// standard output and error.
fn run_gates(arguments: &[&str]) -> (Option<i32>, String, String) {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let output = Command::new("bash")
        .arg(workspace.join("scripts/run-gates.sh"))
        .args(arguments)
        .current_dir(&workspace)
        .output()
        .expect("run scripts/run-gates.sh");
    (
        output.status.code(),
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

/// The registry's keys, kinds and patterns are well formed, every pattern matches a tracked file,
/// and every command runs a tracked program. Since a certification or heavy entry must name
/// `paths`, every such entry is owed by some change to a tracked file: none is reachable only by
/// someone remembering its name.
#[test]
fn the_gate_registry_is_valid_against_the_workspace() {
    let (code, stdout, stderr) = run_gates(&["--check"]);
    assert_eq!(code, Some(0), "{stdout}{stderr}");
}

/// An owed entry whose patterns match no tracked file is owed by no change, so `--check` refuses
/// it, as it refuses an owed entry without patterns.
#[test]
fn the_gate_registry_check_refuses_an_owed_entry_no_tracked_path_selects() {
    let directory = std::env::temp_dir().join(format!(
        "k-rust-gates-{}-{}",
        std::process::id(),
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    fs::create_dir_all(&directory).unwrap();
    let unmatched = directory.join("unmatched.toml");
    fs::write(
        &unmatched,
        "[[gate]]\nname = \"orphan\"\nrun = \"certification\"\ncommand = \"scripts/run-gates.sh\"\npaths = ['^no/such/directory/']\n",
    )
    .unwrap();
    let (code, _, stderr) = run_gates(&["--check", "--registry", unmatched.to_str().unwrap()]);
    assert_eq!(code, Some(1), "{stderr}");
    assert!(
        stderr.contains("gate orphan: pattern '^no/such/directory/' matches no tracked file"),
        "{stderr}"
    );
    let pathless = directory.join("pathless.toml");
    fs::write(
        &pathless,
        "[[gate]]\nname = \"orphan\"\nrun = \"heavy\"\ncommand = \"scripts/run-gates.sh\"\n",
    )
    .unwrap();
    let (code, _, stderr) = run_gates(&["--check", "--registry", pathless.to_str().unwrap()]);
    assert_eq!(code, Some(2), "{stderr}");
    assert!(
        stderr.contains("gate orphan: a heavy entry needs `paths`"),
        "{stderr}"
    );
    fs::remove_dir_all(directory).unwrap();
}

/// A change to the inner parser owes the gate that compares krust's parses of the real semantics
/// with the reference's: what the protocol requires of such a change is what the runner selects.
#[test]
fn a_change_to_the_inner_parser_owes_kast_real_semantics() {
    let (code, stdout, stderr) =
        run_gates(&["--list", "--touched", "crates/k-rust/src/inner/parser.rs"]);
    assert_eq!(code, Some(0), "{stderr}");
    let selected = stdout
        .lines()
        .filter(|line| !line.starts_with(' '))
        .filter_map(|line| line.split_whitespace().next())
        .collect::<BTreeSet<_>>();
    for gate in ["kast-real-semantics", "kast-imp", "compile-light"] {
        assert!(selected.contains(gate), "{gate} not selected: {stdout}");
    }
    assert!(
        !selected.contains("weekly-kast") && !selected.contains("coverage"),
        "a change owes no scheduled or on-demand entry: {stdout}"
    );
    let (code, _, stderr) = run_gates(&["--list", "kast-real-semantic"]);
    assert_eq!(code, Some(2), "an unknown name fails");
    assert!(
        stderr.contains("unknown gate kast-real-semantic"),
        "{stderr}"
    );
}

/// The two builds of k-rust can compile a definition differently only through code that one of
/// them compiles and the other does not, or through the forests both engines are given. So a
/// change to any source with a `z3-inference` cfg, to the native-only inference module, or to the
/// rule grammar and parser owes the entry that compares the builds.
#[test]
fn a_change_to_code_compiled_in_one_build_only_owes_build_agreement() {
    fn sources(directory: &Path, found: &mut Vec<PathBuf>) {
        for entry in fs::read_dir(directory).expect("read source directory") {
            let path = entry.expect("directory entry").path();
            if path.is_dir() {
                sources(&path, found);
            } else if path.extension().is_some_and(|extension| extension == "rs") {
                found.push(path);
            }
        }
    }
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut found = Vec::new();
    sources(&workspace.join("crates/k-rust/src"), &mut found);
    let mut owing = found
        .into_iter()
        .filter(|path| {
            fs::read_to_string(path)
                .expect("read source")
                .contains("feature = \"z3-inference\"")
        })
        .map(|path| {
            path.strip_prefix(&workspace)
                .expect("a workspace source")
                .display()
                .to_string()
        })
        .collect::<Vec<_>>();
    assert!(!owing.is_empty(), "no source has a z3-inference cfg");
    owing.extend([
        "crates/k-rust/src/inner/parser/z3_inference.rs".to_owned(),
        "crates/k-rust/src/inner/parser/chart.rs".to_owned(),
        "crates/k-rust/Cargo.toml".to_owned(),
    ]);
    for path in &owing {
        let (code, stdout, stderr) = run_gates(&["--list", "--touched", path]);
        assert_eq!(code, Some(0), "{stderr}");
        assert!(
            stdout
                .lines()
                .any(|line| line.starts_with("build-agreement ")),
            "a change to {path} does not owe build-agreement: {stdout}"
        );
    }
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

/// Every script under `scripts/` is run by something that runs: the command of a `[[gate]]` entry
/// of the registry, a workflow step, or another script those reach (a sourced helper, an imported
/// module, a called tool). A gate or tool that nothing reaches runs only when someone remembers
/// it, so a change it exists to check merges unchecked. The test takes the registry commands, the
/// workflows and the lines of crate tests that execute a command as roots, and follows every
/// mention of a script's file name (or, for a Python module, its import) to a fixed point.
///
/// This is an inventory, not a record of runs: a script named by a registry entry counts as
/// reached whether or not anything executes that entry. That every certification and heavy entry
/// is owed by some change, and so selected by `scripts/run-gates.sh --changed`, is
/// `the_gate_registry_is_valid_against_the_workspace`.
#[test]
fn every_script_is_reached_from_the_gate_registry_or_a_workflow() {
    fn files(directory: &Path, found: &mut Vec<PathBuf>) {
        for entry in fs::read_dir(directory).expect("read scripts directory") {
            let path = entry.expect("directory entry").path();
            if path.is_dir() {
                if path.file_name().is_some_and(|name| name != "__pycache__") {
                    files(&path, found);
                }
            } else if path
                .extension()
                .is_some_and(|extension| extension == "sh" || extension == "py")
            {
                found.push(path);
            }
        }
    }
    fn rust_sources(directory: &Path, found: &mut Vec<PathBuf>) {
        for entry in fs::read_dir(directory).expect("read tests directory") {
            let path = entry.expect("directory entry").path();
            if path.is_dir() {
                rust_sources(&path, found);
            } else if path.extension().is_some_and(|extension| extension == "rs") {
                found.push(path);
            }
        }
    }
    fn mentions(text: &str, word: &str) -> bool {
        let is_word = |c: char| c.is_ascii_alphanumeric() || c == '_' || c == '-';
        text.match_indices(word).any(|(at, _)| {
            !text[..at].chars().next_back().is_some_and(is_word)
                && !text[at + word.len()..].chars().next().is_some_and(is_word)
        })
    }
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let registry = GATES.parse::<Value>().expect("valid gate registry TOML");
    let mut reached_text = registry["gate"]
        .as_array()
        .expect("gate entries")
        .iter()
        .map(|gate| gate["command"].as_str().expect("gate command").to_owned())
        .collect::<Vec<_>>()
        .join("\n");
    for workflow in fs::read_dir(workspace.join(".github/workflows")).expect("workflows") {
        reached_text.push('\n');
        reached_text.push_str(&fs::read_to_string(workflow.unwrap().path()).unwrap());
    }
    // The workflows run every crate's tests, so a script a test executes is reached too (even
    // when the test runs it against fake tools: that is generous, never strict).
    for crate_directory in fs::read_dir(workspace.join("crates")).expect("crates") {
        let tests = crate_directory.unwrap().path().join("tests");
        let mut sources = Vec::new();
        if tests.is_dir() {
            rust_sources(&tests, &mut sources);
        }
        for source in sources {
            for line in fs::read_to_string(&source).unwrap().lines() {
                if line.contains(".arg(") || line.contains("Command::new") {
                    reached_text.push('\n');
                    reached_text.push_str(line);
                }
            }
        }
    }
    let mut scripts = Vec::new();
    files(&workspace.join("scripts"), &mut scripts);
    scripts.sort();
    let mut reached = BTreeSet::new();
    loop {
        let before = reached.len();
        for script in &scripts {
            if reached.contains(script) {
                continue;
            }
            let name = script.file_name().unwrap().to_str().unwrap();
            let stem = script.file_stem().unwrap().to_str().unwrap();
            let imported = script
                .extension()
                .is_some_and(|extension| extension == "py")
                && (mentions(&reached_text, &format!("import {stem}"))
                    || mentions(&reached_text, &format!("from {stem} import")));
            // A unittest discovery over the scripts' directories runs every test module there.
            let discovered = stem.starts_with("test_")
                && reached_text.contains("python3 -m unittest discover")
                && reached_text.contains("-name 'test_*.py'");
            if mentions(&reached_text, name) || imported || discovered {
                reached.insert(script.clone());
                reached_text.push('\n');
                reached_text.push_str(&fs::read_to_string(script).unwrap());
            }
        }
        if reached.len() == before {
            break;
        }
    }
    let unreached = scripts
        .iter()
        .filter(|script| !reached.contains(*script))
        .map(|script| {
            script
                .strip_prefix(&workspace)
                .unwrap_or(script)
                .display()
                .to_string()
        })
        .collect::<Vec<_>>();
    assert!(
        unreached.is_empty(),
        "scripts no [[gate]] entry, workflow or reached script runs: {unreached:#?}"
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
        2,
        "the reference compile and every reference parse must use the reference ceiling",
    );

    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let guard_path = workspace.join("scripts/reference-memory-guard.sh");
    let guard = fs::read_to_string(&guard_path).expect("shared whole-job memory guard");
    for contract in [
        "REFERENCE_DIFFERENTIAL_JOB_MEMORY_HIGH_KIB:-16777216",
        "REFERENCE_DIFFERENTIAL_JOB_MEMORY_MAX_KIB:-16777216",
        "REFERENCE_DIFFERENTIAL_JOB_FALLBACK_VIRTUAL_MEMORY_KIB:-25165824",
        "MemoryHigh=${memory_high_kib}K",
        "MemoryMax=${memory_max_kib}K",
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
            "REFERENCE_DIFFERENTIAL_JOB_GUARD_PROCESS",
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
    // The guard's 16 GiB defaults, or less under a caller already bounded more tightly
    // (the_memory_guard_keeps_a_gate_inside_its_callers_resource_envelope).
    let property = |name: &str| -> u64 {
        let prefix = format!("{name}=");
        scoped_calls
            .split_whitespace()
            .find_map(|word| word.strip_prefix(prefix.as_str()))
            .and_then(|value| value.strip_suffix('K'))
            .and_then(|value| value.parse().ok())
            .unwrap_or_else(|| panic!("no {name} in {scoped_calls}"))
    };
    assert!(property("MemoryMax") <= 16_777_216, "{scoped_calls}");
    assert!(
        property("MemoryHigh") <= property("MemoryMax"),
        "{scoped_calls}"
    );
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

    // A caller's tighter address-space limit is a bound the guard must not loosen: the fallback
    // keeps it, even when only the soft limit is set (the hard limit would allow raising it).
    fs::write(&calls, "").expect("clear call log");
    fs::write(&payload_runs, "").expect("clear payload run log");
    let base = fixture_command();
    let mut tighter = Command::new("bash");
    tighter
        .args(["-c", r#"ulimit -S -v 1048576; exec bash "$@""#, "caller"])
        .arg(&fixture_script);
    for (name, value) in base.get_envs() {
        match value {
            Some(value) => tighter.env(name, value),
            None => tighter.env_remove(name),
        };
    }
    let tighter = tighter
        .env("PAYLOAD_STATUS", "0")
        .env("SYSTEMD_PROBE_STATUS", "1")
        .output()
        .expect("run fallback guard fixture under a tighter caller limit");
    assert_eq!(tighter.status.code(), Some(0));
    assert_eq!(
        tighter.stdout, b"rlimit-as\n1048576\n",
        "keep the caller's tighter soft virtual-address limit for the entire job",
    );
    assert!(
        String::from_utf8_lossy(&tighter.stderr).starts_with(
            "warning: user systemd scopes unavailable; keeping the caller's tighter 1048576 KiB virtual-address limit (RLIMIT_AS) as the whole-job fallback, not a resident-memory limit\n"
        ),
        "announce that the caller's tighter limit is kept: {}",
        String::from_utf8_lossy(&tighter.stderr)
    );

    // What a guarded caller exports names the caller's guard, not this job's: the job still
    // enters its own scope, and runs once.
    fs::write(&calls, "").expect("clear call log");
    fs::write(&payload_runs, "").expect("clear payload run log");
    let leaked = fixture_command()
        .env("PAYLOAD_STATUS", "0")
        .env("SYSTEMD_PROBE_STATUS", "0")
        .env("REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND", "systemd-scope")
        .env("REFERENCE_DIFFERENTIAL_JOB_GUARD_PROCESS", "1")
        .output()
        .expect("run guard fixture under a guarded caller's environment");
    assert_eq!(leaked.status.code(), Some(0), "{leaked:?}");
    assert_eq!(leaked.stdout, b"systemd-scope\n");
    assert_eq!(
        fs::read_to_string(&calls)
            .expect("leaked call log")
            .lines()
            .count(),
        2,
        "a caller's guard markers must not skip the probe and the job's own scope",
    );
    assert_eq!(
        fs::read_to_string(&payload_runs).expect("leaked payload runs"),
        "x"
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
    let run = |pairing: &str, ghcrts: Option<&str>, reference_ghcrts: Option<&str>| {
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
            .env("REFERENCE_DIFFERENTIAL_PAIRINGS", pairing);
        match ghcrts {
            Some(value) => {
                command.env("GHCRTS", value);
            }
            None => {
                command.env_remove("GHCRTS");
            }
        }
        match reference_ghcrts {
            Some(value) => {
                command.env("REFERENCE_GHCRTS", value);
            }
            None => {
                command.env_remove("REFERENCE_GHCRTS");
            }
        }
        let output = command.output().expect("run compile environment fixture");
        assert!(
            output.status.success(),
            "fixture control failed for {pairing} with GHCRTS={ghcrts:?}, REFERENCE_GHCRTS={reference_ghcrts:?}: status={}\nstdout:\n{}\nstderr:\n{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
        fs::read_to_string(&calls).expect("environment call log")
    };

    let default_haskell = run("haskell/rust", None, None);
    let caller_haskell = run("haskell/rust", Some("-N3"), None);
    let overridden_haskell = run("haskell/rust", None, Some("-N3"));
    let non_haskell = run("kore/llvm", None, None);

    assert_eq!(
        default_haskell,
        "cargo-build|<unset>\ncargo-test|<unset>\nkompile|-N1\nkrust-kcompile|<unset>\nparser|<empty>\nparser|<empty>\ncomparator|<unset>\n",
        "the default must make only the reference Haskell frontend single-capability",
    );
    assert_eq!(
        caller_haskell, default_haskell,
        "the caller's GHCRTS must reach no process of the gate",
    );
    assert_eq!(
        overridden_haskell,
        "cargo-build|<unset>\ncargo-test|<unset>\nkompile|-N3\nkrust-kcompile|<unset>\nparser|<empty>\nparser|<empty>\ncomparator|<unset>\n",
        "REFERENCE_GHCRTS must replace the threaded reference tools' default and reach nothing else",
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
    let run = |ghcrts: Option<&str>, reference_ghcrts: Option<&str>| {
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
            .env("REFERENCE_DIFFERENTIAL_ALLOW_UNPINNED", "1");
        match ghcrts {
            Some(value) => {
                command.env("GHCRTS", value);
            }
            None => {
                command.env_remove("GHCRTS");
            }
        }
        match reference_ghcrts {
            Some(value) => {
                command.env("REFERENCE_GHCRTS", value);
            }
            None => {
                command.env_remove("REFERENCE_GHCRTS");
            }
        }
        let output = command.output().expect("run symbolic environment fixture");
        assert!(
            output.status.success(),
            "fixture control failed with GHCRTS={ghcrts:?}, REFERENCE_GHCRTS={reference_ghcrts:?}: status={}\nstdout:\n{}\nstderr:\n{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
        fs::read_to_string(&calls).expect("environment call log")
    };

    let default = run(None, None);
    let caller = run(Some("-N3"), None);
    let overridden = run(None, Some("-N3"));

    assert_eq!(
        default,
        "cargo-build|<unset>\ncargo-test|<unset>\nkompile|-N1\nparser|<empty>\nparser|<empty>\nkore-exec|-N1\nkrust-kore-exec|<unset>\ncomparator|<unset>\n",
        "the default must make the reference Haskell frontend and backend single-capability and leave the parsers and Rust side alone",
    );
    assert_eq!(
        caller, default,
        "the caller's GHCRTS must reach no process of the gate"
    );
    assert_eq!(
        overridden,
        "cargo-build|<unset>\ncargo-test|<unset>\nkompile|-N3\nparser|<empty>\nparser|<empty>\nkore-exec|-N3\nkrust-kore-exec|<unset>\ncomparator|<unset>\n",
        "REFERENCE_GHCRTS must replace the default of kompile and kore-exec and reach nothing else",
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
    let run = |ghcrts: Option<&str>, reference_ghcrts: Option<&str>| {
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
            .env("REFERENCE_DIFFERENTIAL_ALLOW_UNPINNED", "1");
        match ghcrts {
            Some(value) => {
                command.env("GHCRTS", value);
            }
            None => {
                command.env_remove("GHCRTS");
            }
        }
        match reference_ghcrts {
            Some(value) => {
                command.env("REFERENCE_GHCRTS", value);
            }
            None => {
                command.env_remove("REFERENCE_GHCRTS");
            }
        }
        let output = command.output().expect("run MIR environment fixture");
        assert!(
            output.status.success(),
            "fixture control failed with GHCRTS={ghcrts:?}, REFERENCE_GHCRTS={reference_ghcrts:?}: status={}\nstdout:\n{}\nstderr:\n{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
        fs::read_to_string(&calls).expect("environment call log")
    };

    let default = run(None, None);
    let caller = run(Some("-N3"), None);
    let overridden = run(None, Some("-N3"));

    assert_eq!(
        default,
        "kompile|-N1\ncargo-run|<unset>\nkmir-python|<unset>\nkrun|-N1\ncargo-run|<unset>\ncargo-test|<unset>\n",
        "the default must make the reference Haskell kompile and krun single-capability and leave the Rust side alone",
    );
    assert_eq!(
        caller, default,
        "the caller's GHCRTS must reach no process of the gate"
    );
    assert_eq!(
        overridden,
        "kompile|-N3\ncargo-run|<unset>\nkmir-python|<unset>\nkrun|-N3\ncargo-run|<unset>\ncargo-test|<unset>\n",
        "REFERENCE_GHCRTS must replace the default of the reference kompile and krun and reach nothing else",
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

/// The WASM execution gate's manifest step (`report` in `scripts/wasm-execution-gate.sh`), run in
/// `mode` on `manifest` with the measured outputs `work` (file name suffix and content per case,
/// written where the gate's run step writes them) for `cases`. Returns the exit status, standard
/// output and standard error, and the manifest afterwards.
fn wasm_gate_report_step(
    mode: &str,
    manifest: &str,
    work: &[(&str, &str)],
    cases: &[&str],
) -> (Option<i32>, String, String, String) {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let gate = fs::read_to_string(workspace.join("scripts/wasm-execution-gate.sh"))
        .expect("read the WASM execution gate");
    let report = gate
        .split_once("python3 - \"$manifest\" \"$success_configuration\"")
        .and_then(|(_, rest)| rest.split_once("<<'EOF'"))
        .and_then(|(_, rest)| rest.split_once('\n'))
        .and_then(|(_, rest)| rest.split_once("\nEOF\n"))
        .map(|(body, _)| body.to_owned())
        .expect("the gate's report step");
    let fixture = environment_fixture("wasm-report");
    let manifest_path = fixture.join("manifest.toml");
    fs::write(&manifest_path, manifest).unwrap();
    fs::write(fixture.join("success.kore"), "success\n").unwrap();
    let work_directory = fixture.join("work");
    fs::create_dir(&work_directory).unwrap();
    for (name, content) in work {
        fs::write(work_directory.join(name), content).unwrap();
    }
    let output = Command::new("python3")
        .args(["-I", "-c", &report])
        .arg(&manifest_path)
        .arg(fixture.join("success.kore"))
        .arg(&work_directory)
        .arg(mode)
        .args(cases)
        .output()
        .expect("run the gate's report step");
    let after = fs::read_to_string(&manifest_path).unwrap();
    fs::remove_dir_all(&fixture).expect("remove the report fixture");
    (
        output.status.code(),
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
        after,
    )
}

/// The WASM execution gate reports every difference of a recorded case and exits 3. A proof
/// recorded as failed (exit 1, with the digest of its output under `stdout`) that now passes has
/// no measured `stdout`, a key the case still records: that is a difference to report like any
/// other, not a reason for the report to stop. The test runs the gate's report step on such a
/// case, with the measured outputs written where the gate's run step writes them.
#[test]
fn wasm_execution_gate_reports_a_recorded_key_that_is_no_longer_measured() {
    let (status, stdout, stderr, _) = wasm_gate_report_step(
        "compare",
        r#"# header

[[program]]
name = "simple/unused"
exit = 0
stderr = ""
stdout = "success"

[[proof]]
name = "proofs/x"
module = "X-SPEC"
definition_module = "X"
known_failure = "a reason"
exit = 1
stderr = ""
verdict = """
claim a: failed
"""
stdout = "sha256:00 (1 bytes)"
"#,
        &[
            ("proofs-x.stdout", "claim a: proven\n"),
            ("proofs-x.exit", "0\n"),
            ("proofs-x.stderr", ""),
            ("proofs-x.milliseconds", "1000\n"),
        ],
        &["proofs/x"],
    );
    assert_eq!(status, Some(3), "{stdout}{stderr}");
    assert!(stdout.contains("proofs/x: DIFFERS"), "{stdout}{stderr}");
    assert!(stdout.contains("stdout"), "{stdout}{stderr}");
    assert!(
        stdout.contains("recorded as a known failure: a reason"),
        "{stdout}{stderr}"
    );
}

/// A pinned result other than success states why it is not one (`known_failure`), so that a
/// defect cannot look like an upstream-known failure; a success has nothing to explain and
/// carries no reason. A program succeeds when it exits 0 with the configuration upstream's passing
/// tests reach (`success`), a proof when it exits 0. The gate checks the recorded manifest before
/// it compiles anything, and `--update` keeps the rule: it drops the reason of a case that now
/// succeeds and fails on a case that no longer does until a reason is written.
#[test]
fn wasm_execution_gate_requires_a_reason_exactly_on_a_result_other_than_success() {
    let manifest = |program: &str, proof: &str| {
        format!(
            r#"# header

[[program]]
name = "simple/p"
{program}stderr = ""

[[proof]]
name = "proofs/q"
module = "Q-SPEC"
definition_module = "Q"
{proof}stderr = ""
verdict = """
claim a: failed
"""
"#
        )
    };
    let success = "exit = 0\nstdout = \"success\"\n";
    let digest = "exit = 0\nstdout = \"sha256:00 (1 bytes)\"\n";
    let failed = "exit = 1\n";
    let reason = "known_failure = \"upstream tests/failing.simple\"\n";
    let check = |manifest: &str| {
        let (status, _, stderr, _) = wasm_gate_report_step("check", manifest, &[], &[]);
        (status, stderr)
    };
    let mut failures = Vec::new();
    for (description, program, proof, expected) in [
        (
            "both with their reasons",
            format!("{reason}{digest}"),
            format!("{reason}{failed}"),
            None,
        ),
        (
            "a success without one",
            success.to_owned(),
            format!("{reason}{failed}"),
            None,
        ),
        (
            "a program output other than success without a reason",
            digest.to_owned(),
            format!("{reason}{failed}"),
            Some("simple/p: records a result other than success"),
        ),
        (
            "a failed proof without a reason",
            format!("{reason}{digest}"),
            failed.to_owned(),
            Some("proofs/q: records a result other than success"),
        ),
        (
            "an empty reason",
            format!("known_failure = \" \"\n{digest}"),
            format!("{reason}{failed}"),
            Some("simple/p: records a result other than success"),
        ),
        (
            "a success with a reason",
            format!("{reason}{success}"),
            format!("{reason}{failed}"),
            Some("simple/p: records success, so it carries no known_failure"),
        ),
    ] {
        let (status, stderr) = check(&manifest(&program, &proof));
        let ok = match expected {
            None => status == Some(0) && stderr.is_empty(),
            Some(error) => status == Some(2) && stderr.contains(error),
        };
        if !ok {
            failures.push(format!("{description}: exit {status:?}: {stderr}"));
        }
    }
    let gate_manifest = fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../scripts/wasm-execution-gate.toml"),
    )
    .expect("read the WASM gate manifest");
    let (status, stderr) = check(&gate_manifest);
    if status != Some(0) {
        failures.push(format!(
            "the gate's own manifest: exit {status:?}: {stderr}"
        ));
    }
    assert!(failures.is_empty(), "{failures:#?}");

    // --update: the program now succeeds, so its reason goes; the proof now fails without one.
    let measured = [
        ("simple-p.stdout", "success\n"),
        ("simple-p.exit", "0\n"),
        ("simple-p.stderr", ""),
        ("simple-p.milliseconds", "10\n"),
        ("proofs-q.stdout", "claim a: failed\n"),
        ("proofs-q.exit", "1\n"),
        ("proofs-q.stderr", ""),
        ("proofs-q.milliseconds", "10\n"),
    ];
    let (status, stdout, stderr, after) = wasm_gate_report_step(
        "update",
        &manifest(&format!("{reason}{digest}"), "exit = 0\n"),
        &measured,
        &[],
    );
    assert_eq!(status, Some(2), "{stdout}{stderr}");
    assert!(
        stdout.contains("simple/p: now success; dropped known_failure"),
        "{stdout}"
    );
    assert!(
        stderr.contains("proofs/q: records a result other than success"),
        "{stderr}"
    );
    let rewritten = after.parse::<Value>().expect("the rewritten manifest");
    assert!(
        rewritten["program"][0].get("known_failure").is_none(),
        "{after}"
    );
    assert_eq!(rewritten["program"][0]["stdout"].as_str(), Some("success"));
    assert_eq!(rewritten["proof"][0]["exit"].as_integer(), Some(1));
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

/// Every request of an RPC session goes through the pinned `kore-rpc-client` or a raw socket,
/// whichever server answers, so the session is a reference call like the gate's others: its
/// function body is one subshell that applies the reference memory bound before any request.
#[test]
fn rpc_gate_sessions_run_under_the_reference_memory_bound() {
    let start = RPC_SCRIPT
        .find("\ncollect_responses() (\n")
        .expect("the RPC session is a function whose body is a subshell");
    let body = &RPC_SCRIPT[start + 1..];
    let end = body.find("\n)\n").expect("the session subshell ends");
    let body = &body[..end];
    let bound = body
        .find("ulimit -v \"$reference_memory_kib\"")
        .expect("the session applies the reference memory bound");
    let first_request = body
        .find("\"$rpc_client\"")
        .expect("the session sends requests through the reference client");
    assert!(
        bound < first_request,
        "the bound must precede every request"
    );
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

/// The reference simplifier's client, `kore-rpc-client`, is not built with the threaded GHC
/// runtime, so it refuses to start under runtime options such as `-N1`: the GHC runtime options
/// of the gate's caller must not reach it, as they reach none of the gate's other reference calls.
/// With `GHCRTS=-N1` exported, the N41 case must still compare, and the client must run with
/// `GHCRTS` unset or empty.
#[test]
fn execution_gate_runs_the_reference_simplifier_client_without_the_callers_ghcrts() {
    let (status, log, stdout, stderr, listening) =
        execution_gate_with_reference_simplifier("star-cell-heating-set", &[("GHCRTS", "-N1")]);
    assert_eq!(status, Some(0), "{stdout}{stderr}");
    assert!(!listening, "the gate left the reference simplifier running");
    let clients = log
        .lines()
        .filter(|line| line.starts_with("kore-rpc-client-done|"))
        .collect::<Vec<_>>();
    assert_eq!(
        clients.len(),
        2,
        "one simplify request per program result: {log}"
    );
    for client in clients {
        assert!(
            matches!(
                client,
                "kore-rpc-client-done|<empty>" | "kore-rpc-client-done|<unset>"
            ),
            "the simplifier client ran with the caller's GHCRTS: {client}"
        );
    }
}

/// A listening socket the gate's caller opened without close-on-exec is inherited by every
/// server the gate starts, but it is not that server's bind: the helper must not report its port.
/// Here the "server" (`sleep`) never listens, so the helper must give up rather than hand the gate
/// the caller's port, which would make both RPC sessions talk to one foreign process.
#[test]
fn the_server_port_helper_ignores_a_listening_socket_inherited_from_the_caller() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let caller = r#"
import os, socket, sys
listener = socket.socket()
listener.bind(("127.0.0.1", 0))
listener.listen()
listener.set_inheritable(True)
print("caller", listener.getsockname()[1], flush=True)
os.execvp("bash", ["bash", "-c", sys.argv[1]])
"#;
    let gate = r#"
set -u
source "$WORKSPACE/scripts/reference-server-port.sh"
log=$(mktemp)
sleep 30 &
server=$!
status=0
reference_wait_for_server_port "$server" "$log" 0 20 2>/dev/null || status=$?
echo "helper $status ${reference_listening_port:-none}"
kill "$server"
rm -f "$log"
"#;
    let output = Command::new("python3")
        .args(["-I", "-c", caller, gate])
        .env("WORKSPACE", &workspace)
        .stdin(std::process::Stdio::null())
        .output()
        .expect("run the server-port helper under a caller holding a listener");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let lines = stdout.lines().collect::<Vec<_>>();
    assert_eq!(lines.len(), 2, "{stdout}{stderr}");
    assert!(lines[0].starts_with("caller "), "{stdout}{stderr}");
    assert_eq!(
        lines[1], "helper 1 none",
        "the helper reported the caller's listener as the server's port: {stdout}{stderr}"
    );
}

/// `scripts/benchmark.sh` measures the reference under the GHC runtime options its recorded
/// canonical figures carry, so those options are part of the measurement: they come from the
/// benchmark's own `REFERENCE_GHCRTS` (empty by default), and a caller's `GHCRTS` never reaches
/// the reference it times.
#[test]
fn benchmark_gives_the_reference_its_own_ghc_runtime_options_not_the_callers() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let fixture = environment_fixture("benchmark-ghcrts");
    let kompile = fixture.join("kompile");
    write_environment_probe(&kompile, "kompile", "");
    let work = fixture.join("work");
    fs::create_dir(&work).expect("create benchmark work directory");
    let calls = fixture.join("calls");
    let mut failures = Vec::new();
    for (description, stated, expected) in [
        ("no REFERENCE_GHCRTS", None, "kompile|<empty>"),
        ("REFERENCE_GHCRTS=-N2", Some("-N2"), "kompile|-N2"),
    ] {
        fs::write(&calls, "").expect("clear call log");
        let mut command = Command::new("bash");
        command
            .arg(workspace.join("scripts/benchmark.sh"))
            .args(["__run", "compile", "canonical-haskell", "imp"])
            .arg(&work)
            .env("GHCRTS", "-N4")
            .env("ENVIRONMENT_CALLS", &calls)
            .env("BENCHMARK_WORK_ROOT", &fixture)
            .env("K_KOMPILE", &kompile)
            .env("IMP_SEMANTICS_CHECKOUT", fixture.join("imp-semantics"))
            .env_remove("REFERENCE_GHCRTS")
            .stdin(std::process::Stdio::null());
        if let Some(stated) = stated {
            command.env("REFERENCE_GHCRTS", stated);
        }
        let output = command
            .output()
            .expect("run the benchmark's reference compile");
        let log = fs::read_to_string(&calls).unwrap_or_default();
        if !output.status.success() || log.trim_end() != expected {
            failures.push(format!(
                "{description}, caller GHCRTS=-N4: exit {:?}, reference saw {log:?}, not {expected:?}: {}",
                output.status.code(),
                String::from_utf8_lossy(&output.stderr)
            ));
        }
    }
    fs::remove_dir_all(&fixture).expect("remove benchmark fixture");
    assert!(failures.is_empty(), "{failures:#?}");
}

/// A caller that leaks into what a gate starts: it exports `GHCRTS` and holds a listening socket
/// without close-on-exec, then execs its arguments.
const LEAKING_CALLER: &str = r#"
import os, socket, sys
listener = socket.socket()
listener.bind(("127.0.0.1", 0))
listener.listen()
listener.set_inheritable(True)
os.execvp(sys.argv[1], sys.argv[1:])
"#;

/// A gate's verdict is a function of its inputs (krust, the pinned reference, the case), not of
/// the process it was started from: whatever its caller exports or holds open, the same case
/// compares the same results and reaches the same verdict. The N41 case runs every kind of
/// reference process a gate starts (non-threaded GHC tools, a server whose port the gate reads
/// from the server, the comparator), once from a clean environment and then from callers that
/// export `GHCRTS=-N1` (which the non-threaded tools refuse; a caller states the threaded tools'
/// options as `REFERENCE_GHCRTS`) and hold an inherited listening socket; in every run the
/// requests go to the servers the gate started.
#[test]
fn a_gate_reaches_the_same_verdict_whatever_its_caller_leaks() {
    let check = ("FAKE_GHC_RUNTIME_CHECK", "1");
    let comparisons = |log: &str| {
        log.lines()
            .filter(|line| line.starts_with("comparator "))
            .map(str::to_owned)
            .collect::<Vec<_>>()
    };
    let (status, log, stdout, stderr, _) =
        execution_gate_with_reference_simplifier_under("star-cell-heating-set", &[check], &[]);
    assert_eq!(status, Some(0), "clean caller: {stdout}{stderr}");
    let clean = comparisons(&log);
    assert!(!clean.is_empty(), "{log}");
    let mut failures = Vec::new();
    for (description, environment, caller) in [
        (
            "a caller exporting GHCRTS=-N1",
            vec![check, ("GHCRTS", "-N1")],
            vec![],
        ),
        (
            "a caller holding an inheritable listening socket",
            vec![check],
            vec!["python3", "-I", "-c", LEAKING_CALLER],
        ),
    ] {
        let (status, log, _, stderr, listening) = execution_gate_with_reference_simplifier_under(
            "star-cell-heating-set",
            &environment,
            &caller,
        );
        if status != Some(0) || comparisons(&log) != clean {
            let last = stderr.lines().last().unwrap_or_default();
            failures.push(format!(
                "{description}: exit {status:?} and {} comparisons, not exit 0 and {}: {last}",
                comparisons(&log).len(),
                clean.len()
            ));
        }
        if simplify_request_ports(&log) != bound_simplifier_ports(&log) {
            failures.push(format!(
                "{description}: simplify requests went to ports {:?}, the servers the gate started bound {:?}",
                simplify_request_ports(&log),
                bound_simplifier_ports(&log)
            ));
        }
        if listening {
            failures.push(format!("{description}: the gate left a server running"));
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

/// The guard sets a gate's process state before anything runs, whatever its caller leaves it:
/// standard input is `/dev/null`, no descriptor above 2 is open but the shell's own script
/// descriptor (255), and `GHCRTS` is unset. That is what the gate's children inherit, so it holds
/// in both of the guard's paths (a scope, and the address-space fallback), from a caller that
/// pipes standard input, holds an inheritable listening socket and exports `GHCRTS`.
#[test]
fn the_guard_starts_a_gate_without_its_callers_input_descriptors_or_ghcrts() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let fixture = environment_fixture("guard-process-state");
    let fake_systemd_run = fixture.join("systemd-run");
    fs::write(
        &fake_systemd_run,
        r#"#!/usr/bin/env bash
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
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(&fake_systemd_run, fs::Permissions::from_mode(0o755))
            .expect("make fake systemd-run executable");
    }
    let gate = fixture.join("gate.sh");
    fs::write(
        &gate,
        format!(
            r#"#!/usr/bin/env bash
set -euo pipefail
source {guard:?}
reference_enter_whole_job "$@"
# A simple command with its own redirection: in a substitution or a pipeline the shell would hold
# a pipe open while the listing runs.
listing=${{BASH_SOURCE[0]%/*}}/descriptors
ls /proc/$$/fd >"$listing"
echo "descriptors $(sort -n "$listing" | tr '\n' ' ')"
echo "input $(readlink /proc/$$/fd/0)"
echo "ghcrts ${{GHCRTS-unset}}"
"#,
            guard = workspace.join("scripts/reference-memory-guard.sh"),
        ),
    )
    .unwrap();
    let path = format!(
        "{}:{}",
        fixture.display(),
        std::env::var("PATH").expect("PATH")
    );
    let mut failures = Vec::new();
    for (description, probe) in [("a scope", "0"), ("the address-space fallback", "1")] {
        let output = Command::new("python3")
            .args(["-I", "-c", LEAKING_CALLER, "bash"])
            .arg(&gate)
            .env("PATH", &path)
            .env("SYSTEMD_PROBE_STATUS", probe)
            .env("GHCRTS", "-N1")
            .env_remove("REFERENCE_DIFFERENTIAL_JOB_GUARD_PROCESS")
            .stdin(std::process::Stdio::piped())
            .output()
            .expect("run the guard from a leaking caller");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let expected = "descriptors 0 1 2 255 \ninput /dev/null\nghcrts unset\n";
        if !output.status.success() || stdout != expected {
            failures.push(format!(
                "{description}: exit {:?}, printed {stdout:?}, not {expected:?}: {}",
                output.status.code(),
                String::from_utf8_lossy(&output.stderr)
            ));
        }
    }
    fs::remove_dir_all(&fixture).expect("remove guard fixture");
    assert!(failures.is_empty(), "{failures:#?}");
}

/// The whole-job memory guard bounds a gate's memory; it must not loosen a bound the gate's
/// caller already set, so after the guard the gate still runs inside its caller's slice and
/// under a memory limit no larger than the caller's. That holds however the caller starts the
/// gate: through another process (`timeout`) or as the outer scope's own process. Needs a user
/// systemd manager; without one the guard takes its RLIMIT_AS fallback and the test has nothing
/// to check.
#[test]
fn the_memory_guard_keeps_a_gate_inside_its_callers_resource_envelope() {
    let manager = Command::new("systemd-run")
        .args(["--user", "--scope", "--quiet", "--", "true"])
        .stdin(std::process::Stdio::null())
        .status()
        .is_ok_and(|status| status.success());
    if !manager {
        eprintln!("no user systemd manager: the guard uses its RLIMIT_AS fallback");
        return;
    }
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let fixture = environment_fixture("guard-envelope");
    let gate = fixture.join("gate.sh");
    fs::write(
        &gate,
        format!(
            r#"#!/usr/bin/env bash
set -euo pipefail
source {guard:?}
reference_enter_whole_job "$@"
cgroup=$(sed -n 's/^0:://p' /proc/self/cgroup)
limit=max
directory=/sys/fs/cgroup$cgroup
while [[ $directory == /sys/fs/cgroup/* ]]; do
  if [[ -r $directory/memory.max ]]; then
    value=$(<"$directory/memory.max")
    if [[ $value != max ]] && [[ $limit == max || $value -lt $limit ]]; then limit=$value; fi
  fi
  directory=${{directory%/*}}
done
echo "guard $REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND cgroup $cgroup limit $limit"
"#,
            guard = workspace.join("scripts/reference-memory-guard.sh"),
        ),
    )
    .unwrap();
    // No dash in the name: systemd reads each dash of a slice name as a parent slice and loads the
    // whole chain, so a dashed name would leave its parents loaded after the stop below.
    let slice = format!("krustguardtest{}.slice", std::process::id());
    let caller_limit: u64 = 1 << 30;
    let mut failures = Vec::new();
    for (description, between) in [
        ("started through timeout", vec!["timeout", "60"]),
        ("the outer scope's own process", vec![]),
    ] {
        let output = Command::new("systemd-run")
            .args(["--user", "--scope", "--quiet"])
            .arg(format!("--slice={slice}"))
            .arg(format!("--property=MemoryMax={caller_limit}"))
            .args(["--"])
            .args(&between)
            .arg("bash")
            .arg(&gate)
            .env_remove("REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND")
            .stdin(std::process::Stdio::null())
            .output()
            .expect("run the guard under an outer scope");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let line = stdout.lines().find(|line| line.starts_with("guard "));
        let Some(line) = line else {
            failures.push(format!(
                "{description}: the gate did not run: {stdout}{stderr}"
            ));
            continue;
        };
        let words = line.split_whitespace().collect::<Vec<_>>();
        let (cgroup, limit) = (words[3], words[5]);
        if !cgroup.contains(&format!("/{slice}/")) {
            failures.push(format!(
                "{description}: the gate left its caller's slice {slice}: {cgroup}"
            ));
        }
        if limit
            .parse::<u64>()
            .map_or(true, |limit| limit > caller_limit)
        {
            failures.push(format!(
                "{description}: the gate's memory limit {limit} exceeds its caller's {caller_limit}"
            ));
        }
    }
    fs::remove_dir_all(&fixture).expect("remove guard fixture");
    // A slice stays loaded once its last scope ends; stop the one this test created, which has no
    // parent slice of its own.
    let _ = Command::new("systemctl")
        .args(["--user", "stop", &slice])
        .stdin(std::process::Stdio::null())
        .status();
    assert!(failures.is_empty(), "{failures:#?}");
}
