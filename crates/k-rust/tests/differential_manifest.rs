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
const SECTIONS: [&str; 6] = ["compile", "kast", "execution", "proof", "rpc", "symbolic"];
const JAVA_BACKED_DIFFERENTIAL_SCRIPTS: [&str; 6] = [
    COMPILE_SCRIPT,
    KAST_SCRIPT,
    EXECUTION_SCRIPT,
    PROOF_SCRIPT,
    RPC_SCRIPT,
    MIR_EXECUTION_SCRIPT,
];

#[test]
fn part_b_manifest_schema_is_complete() {
    let manifest = MANIFEST.parse::<Value>().expect("valid differential TOML");
    assert!(
        manifest["normalisations"].get("ignore_unique_id").is_none(),
        "B2-03 removes the temporary UNIQUE_ID escape hatch"
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
        assert!(matches!(expect, "accept" | "reject"));
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
        compile_case("exists-anon")["requires"]
            .as_array()
            .expect("exists-anon requirements")
            .iter()
            .all(|requirement| requirement.as_str() != Some("ticket:B2-02")),
        "I1-07 and A3-07 make the B2-02 integration fixture directly runnable",
    );
    assert!(
        compile_case("assoc-strict")["requires"]
            .as_array()
            .expect("assoc-strict requirements")
            .iter()
            .all(|requirement| requirement.as_str() == Some("reference-toolchain")),
        "A3-06 and I1-06 are verified, so assoc-strict runs in the default protocol",
    );
}

#[test]
fn part_b_pending_and_special_case_schema_is_complete() {
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
    let ticket_requirements = |entry: &Value| {
        entry["requires"]
            .as_array()
            .unwrap()
            .iter()
            .filter_map(|requirement| {
                requirement
                    .as_str()
                    .and_then(|value| value.strip_prefix("ticket:"))
                    .map(str::to_owned)
            })
            .collect::<Vec<_>>()
    };
    // The three symbolic C1 cases stay pending on C1-01: the fresh remainder names now externalize
    // as KORE identifiers (`ExFrame0:SortMap{}`), but the comparison still fails on harness shape
    // (kore-exec's depth counting, `\not(\exists ...)` constraints, generated-name canonicalization;
    // see the manifest comment above the c1-map case).
    for name in ["c1-map", "c1-t2", "c1-t3"] {
        assert_eq!(
            ticket_requirements(&case("symbolic", name)),
            ["C1-01"],
            "symbolic case {name} must stay pending on the fresh-name owner C1-01"
        );
    }
    // Every case whose owning tickets are verified and which passed the opt-in stage-12 run
    // must run in the default protocol: no ticket: requirement may remain.
    let expected_unblocked = [
        ("compile", "fresh-name-collision"),
        ("compile", "imp"),
        ("compile", "parametric"),
        ("compile", "assoc-strict"),
        ("compile", "undefined-sort"),
        ("compile", "semcast2"),
        ("execution", "c3-search"),
        ("execution", "c3-br"),
        ("execution", "c3-co"),
        ("execution", "c3-tr"),
        ("proof", "c4-split"),
        ("proof", "c4-lemma"),
        ("proof", "c4-trivial"),
        ("rpc", "c3-tr-rpc"),
    ];
    for (section, name) in expected_unblocked {
        assert_eq!(
            ticket_requirements(&case(section, name)),
            Vec::<String>::new(),
            "{section} case {name} carries a stale ticket: requirement"
        );
    }
    let still_pending = SECTIONS
        .iter()
        .flat_map(|&section| {
            manifest[section]
                .as_array()
                .unwrap()
                .iter()
                .filter(|entry| !ticket_requirements(entry).is_empty())
                .map(move |entry| format!("{section}/{}", entry["name"].as_str().unwrap()))
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(
        still_pending,
        BTreeSet::from([
            "symbolic/c1-map".to_owned(),
            "symbolic/c1-t2".to_owned(),
            "symbolic/c1-t3".to_owned(),
        ]),
        "only the C1-01 symbolic cases may stay ticket-gated"
    );

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
    }

    for name in ["imp", "bounded-search", "c3-tr-rpc"] {
        let entry = manifest["rpc"]
            .as_array()
            .unwrap()
            .iter()
            .find(|entry| entry["name"].as_str() == Some(name))
            .unwrap_or_else(|| panic!("missing RPC case {name}"));
        assert_eq!(entry["oracle"].as_str(), Some("kore-rpc-booster"));
        if name == "c3-tr-rpc" {
            assert_eq!(
                entry["state-depth"].as_integer(),
                Some(0),
                "the C3-05 RPC probe must send the initial state, not Kore's post-step bottom",
            );
        }
    }

    let exit = manifest["execution"]
        .as_array()
        .expect("execution cases")
        .iter()
        .find(|entry| entry["name"].as_str() == Some("exit"))
        .expect("D1-01 exit execution case");
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
        for field in ["program", "expected", "reference", "reason", "ticket"] {
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
        })
        .collect::<Vec<_>>();
    assert_eq!(
        rpc_exceptions.len(),
        1,
        "only the measured IMP implication payload diverges from Booster",
    );
    for exception in rpc_exceptions {
        for field in ["oracle", "response", "expected", "reason", "ticket"] {
            assert!(
                exception[field]
                    .as_str()
                    .is_some_and(|value| !value.trim().is_empty()),
                "RPC oracle exception lacks {field}"
            );
        }
        assert_eq!(exception["oracle"].as_str(), Some("kore-rpc-booster"));
        assert_eq!(exception["response"].as_str(), Some("implies"));
        assert_eq!(exception["ticket"].as_str(), Some("D1-08"));
    }

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
fn b2_03_removes_measured_compile_divergence_ceilings() {
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
fn part_b_gate_scripts_wire_the_runtime_contract() {
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
        assert!(script.contains("REFERENCE_DIFFERENTIAL_PENDING"));
        assert!(script.contains("pending: blocked by"));
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
            "B2-03 must remove the general UNIQUE_ID escape hatch: {obsolete}"
        );
    }
    for script in [EXECUTION_SCRIPT, MIR_EXECUTION_SCRIPT, &symbolic] {
        assert!(script.contains("K_DIFFERENTIAL_DEFINITION"));
        assert!(script.contains("K_DIFFERENTIAL_MODULE"));
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
    ] {
        assert!(RPC_SCRIPT.contains(needle), "RPC gate lacks {needle}");
    }
    for needle in ["kore-exec", "--stop-leaves", "gotstuck", "--searchType"] {
        assert!(symbolic.contains(needle), "symbolic gate lacks {needle}");
    }
}

#[test]
fn pending_only_selection_does_not_require_reference_tools() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let manifest = MANIFEST.parse::<Value>().expect("valid differential TOML");
    // Every ticket-gated case of each section, so the check follows the manifest as
    // requirements are dropped when their tickets land.
    let mut exercised = 0;
    for (section, script_path) in [
        ("compile", "scripts/reference-differential.sh"),
        (
            "execution",
            "scripts/reference-non-imp-execution-differential.sh",
        ),
        ("proof", "scripts/reference-proof-differential.sh"),
        ("rpc", "scripts/reference-rpc-differential.sh"),
        (
            "symbolic",
            "scripts/reference-symbolic-execution-differential.sh",
        ),
    ] {
        for entry in manifest[section].as_array().expect("section cases") {
            let tickets = entry["requires"]
                .as_array()
                .unwrap()
                .iter()
                .filter_map(|requirement| {
                    requirement
                        .as_str()
                        .and_then(|value| value.strip_prefix("ticket:"))
                })
                .collect::<Vec<_>>();
            if tickets.is_empty() {
                continue;
            }
            exercised += 1;
            let case_name = entry["name"].as_str().expect("case name");
            let script_path = workspace.join(script_path);
            let output = Command::new("bash")
                .arg(&script_path)
                .arg(case_name)
                .env("REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND", "rlimit-as")
                .env("K_KOMPILE", workspace.join("missing-reference-kompile"))
                .output()
                .unwrap_or_else(|error| panic!("run {}: {error}", script_path.display()));
            assert!(
                output.status.success(),
                "{} validated unavailable reference tools before skipping {case_name}: {}",
                script_path.display(),
                String::from_utf8_lossy(&output.stderr),
            );
            let expected = format!("[{case_name}] pending: blocked by {}", tickets.join(", "));
            assert!(
                String::from_utf8_lossy(&output.stdout).contains(&expected),
                "{} did not name the blocking ticket(s) `{expected}`: {}",
                script_path.display(),
                String::from_utf8_lossy(&output.stdout),
            );
        }
    }
    assert!(
        exercised > 0,
        "the manifest must keep at least one ticket-gated case to exercise the skip path"
    );

    let compile_validation = "if [[ -z \"$kompile\" ]]";
    assert!(
        KAST_SCRIPT.find("pending: blocked by").unwrap()
            < KAST_SCRIPT.find(compile_validation).unwrap(),
        "the KAST gate must select and skip pending cases before validating reference tools",
    );
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
    let expected = (1..=20)
        .filter(|id| *id != 2)
        .map(|id| format!("N{id}"))
        .collect::<BTreeSet<_>>();
    assert_eq!(
        ids.into_iter().map(str::to_owned).collect::<BTreeSet<_>>(),
        expected,
        "the gate register must contain N1 and N3 through N20 after B2-03 deletes N2"
    );
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut registered_symbols = BTreeSet::new();
    for row in rows {
        let id = row["id"].as_str().unwrap();
        for field in [
            "gate",
            "anchor",
            "anchor_symbol",
            "rule",
            "justification",
            "fate",
        ] {
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
    let status_path = workspace.join("draft/fable51-review/implementation-status.toml");
    let known_tickets = status_path.exists().then(|| {
        let status = fs::read_to_string(&status_path).expect("read implementation-status ledger");
        let status = status
            .parse::<Value>()
            .expect("valid implementation-status TOML");
        status["ticket"]
            .as_array()
            .expect("implementation-status ticket rows")
            .iter()
            .map(|ticket| ticket["id"].as_str().expect("ticket id").to_owned())
            .collect::<BTreeSet<_>>()
    });
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
                if allowed_requirements.contains(requirement) {
                    continue;
                }
                let ticket = ticket_requirement(requirement).unwrap_or_else(|| {
                    panic!("unknown requirement {requirement} on {section} case {name}")
                });
                if let Some(known_tickets) = &known_tickets {
                    assert!(
                        known_tickets.contains(ticket),
                        "unknown ticket {ticket} on {section} case {name}"
                    );
                }
            }
            assert!(
                entry["constructs"].as_array().is_some(),
                "{section} case {name} has no construct classification"
            );
        }
    }

    for entry in manifest["compile"].as_array().unwrap() {
        if entry.get("expect").and_then(Value::as_str) == Some("reject") {
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

fn ticket_requirement(requirement: &str) -> Option<&str> {
    let ticket = requirement.strip_prefix("ticket:")?;
    let (area, number) = ticket.split_once('-')?;
    let mut area = area.bytes();
    if !area.next().is_some_and(|byte| byte.is_ascii_uppercase())
        || !area.all(|byte| byte.is_ascii_digit())
        || number.len() != 2
        || !number.bytes().all(|byte| byte.is_ascii_digit())
    {
        return None;
    }
    Some(ticket)
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
fn manual_certification_protocol_names_part_b_green_gates() {
    for command in [
        "# scripts/reference-differential.sh append ambiguous-rewrite casts cell-map fresh-variables list-set macro-rewrite parametric-semantic-cast hooked-namespaces star-cell-config overload-constructors owise-functions owise-competitors owise concrete-rw2 cast-inner",
        "# scripts/reference-differential.sh fun-int-list-config",
        "# scripts/reference-differential.sh imp fresh-name-collision parametric assoc-strict undefined-sort semcast2",
        "# REFERENCE_DIFFERENTIAL_PAIRINGS=haskell/rust scripts/reference-differential.sh wasm mir evm-equivalence",
        "# scripts/reference-kast-differential.sh wasm mir evm-equivalence",
        "# scripts/reference-non-imp-execution-differential.sh imp collections hooks-c2",
        "# scripts/reference-non-imp-execution-differential.sh c3-search c3-br c3-co c3-tr",
        "# scripts/reference-proof-differential.sh mini-proof",
        "# scripts/reference-proof-differential.sh c4-split c4-lemma c4-trivial",
        "# scripts/reference-rpc-differential.sh imp",
        "# scripts/reference-rpc-differential.sh bounded-search",
        "# scripts/reference-rpc-differential.sh c3-tr-rpc",
        "# scripts/reference-mir-execution-differential.sh",
        "# scripts/reference-symbolic-execution-differential.sh c3-sd-symbolic c3-sy",
        "# scripts/conformance-ratchet.sh --label <landing> --ticket <ticket>",
    ] {
        assert!(
            MANIFEST.lines().any(|line| line == command),
            "manual certification protocol must name `{command}`",
        );
    }

    for requirement in [
        "# PR description (any change under crates/k-rust/src/{inner,kompile,outer,definition}, crates/k-rust-backend, scripts/reference-*, scripts/conformance/):",
        "#   1. the gate lines above that apply, one row each: case, pass/fail, wall s, peak RSS MiB (scripts/conformance/measure.py)",
        "#   2. the ratchet block printed by `scripts/conformance-ratchet.sh --label <branch> --ticket <ids named in the PR>` (or --all at a milestone)",
        "#   3. the permanent multi-alias oracle-exclusion count printed by scripts/reference-differential.sh",
    ] {
        assert!(
            MANIFEST.lines().any(|line| line == requirement),
            "manual certification protocol must require `{requirement}`",
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
        "REFERENCE_DIFFERENTIAL_JOB_MEMORY_HIGH_KIB:-8388608",
        "REFERENCE_DIFFERENTIAL_JOB_MEMORY_MAX_KIB:-8388608",
        "REFERENCE_DIFFERENTIAL_JOB_FALLBACK_VIRTUAL_MEMORY_KIB:-12582912",
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
          warning: bounding the reference JVM with REFERENCE_DIFFERENTIAL_K_OPTS=-Xmx2048m -Xss1m -XX:+UseSerialGC -XX:CompressedClassSpaceSize=128m -XX:MaxMetaspaceSize=256m -XX:ReservedCodeCacheSize=128m -Dscala.concurrent.context.numThreads=2 -Dscala.concurrent.context.maxThreads=2 under the virtual-address fallback\n\
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
    let calls = fixture.join("calls");
    let fake_kompile = fixture.join("kompile");
    let fake_kore_parser = fixture.join("kore-parser");
    let fake_cargo = fixture.join("cargo");
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
    fs::write(
        &fake_cargo,
        format!(
            r#"#!/usr/bin/env bash
set -euo pipefail
{environment_state}
printf 'cargo-%s|%s\n' "${{1:-missing}}" "$ghcrts_state" >>"$ENVIRONMENT_CALLS"
"#
        ),
    )
    .expect("write fake cargo");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        for executable in [&fake_kompile, &fake_kore_parser, &fake_cargo] {
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
            .env("K_KOMPILE", &fake_kompile)
            .env("K_KORE_PARSER", &fake_kore_parser)
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
        "kompile|-N1\ncargo-run|<unset>\nparser|<empty>\nparser|<empty>\ncargo-test|<unset>\n",
        "the default must make only the reference Haskell frontend single-capability",
    );
    assert_eq!(
        overridden_haskell,
        "kompile|-N3\ncargo-run|-N3\nparser|<empty>\nparser|<empty>\ncargo-test|-N3\n",
        "a caller Haskell override must reach kompile while parsers remain compatible",
    );
    assert!(
        non_haskell.starts_with("kompile|<unset>\ncargo-run|<unset>\n"),
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

#[test]
fn symbolic_gate_scopes_haskell_runtime_options_to_the_reference_backend() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let fixture = environment_fixture("symbolic-environment");
    let calls = fixture.join("calls");
    let fake_kompile = fixture.join("kompile");
    let fake_kore_parser = fixture.join("kore-parser");
    let fake_kore_exec = fixture.join("kore-exec");
    let fake_cargo = fixture.join("cargo");
    let target = fixture.join("target");
    let fake_krust = target.join("release/krust");
    fs::create_dir_all(fake_krust.parent().unwrap()).expect("create fake release directory");
    write_environment_probe(&fake_kompile, "kompile", FAKE_KOMPILE_PROLOGUE);
    write_environment_probe(&fake_kore_parser, "parser", "");
    write_environment_probe(&fake_kore_exec, "kore-exec", "");
    write_environment_probe(&fake_cargo, "cargo-${1:-missing}", "");
    write_environment_probe(&fake_krust, "krust-${1:-missing}", "");
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
            .arg("c3-sy")
            .env("PATH", &path)
            .env("ENVIRONMENT_CALLS", &calls)
            .env("K_KOMPILE", &fake_kompile)
            .env("K_KORE_PARSER", &fake_kore_parser)
            .env("K_KORE_EXEC", &fake_kore_exec)
            .env("CARGO_TARGET_DIR", &target)
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
        "cargo-build|<unset>\nkompile|-N1\nparser|<empty>\nparser|<empty>\nkore-exec|-N1\nkrust-kore-exec|<unset>\ncargo-test|<unset>\n",
        "the default must make the reference Haskell frontend and backend single-capability and leave the parsers and Rust side alone",
    );
    assert_eq!(
        overridden,
        "cargo-build|-N3\nkompile|-N3\nparser|<empty>\nparser|<empty>\nkore-exec|-N3\nkrust-kore-exec|-N3\ncargo-test|-N3\n",
        "a caller Haskell override must reach kompile and kore-exec while parsers remain compatible",
    );

    fs::remove_dir_all(fixture).expect("remove symbolic environment fixture");
}

#[test]
fn mir_execution_gate_scopes_haskell_runtime_options_to_the_reference_backend() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let fixture = environment_fixture("mir-environment");
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
