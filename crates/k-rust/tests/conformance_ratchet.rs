use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    os::unix::fs::PermissionsExt,
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

use sha2::{Digest, Sha256};
use toml::Value;

const EXPECTATIONS: &str = include_str!("../../../scripts/conformance/expectations.toml");
const BISON_PARSERS: &str = include_str!("../../../scripts/conformance/bison-parsers.toml");

struct Fixture {
    root: PathBuf,
    log: PathBuf,
    runs: PathBuf,
    expectations: PathBuf,
    driver: PathBuf,
    fake_binary: PathBuf,
    args: PathBuf,
}

impl Fixture {
    fn new() -> Self {
        static NEXT_FIXTURE: AtomicU64 = AtomicU64::new(0);
        let nonce = NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir().join(format!(
            "k-rust-conformance-ratchet-{}-{nonce}",
            std::process::id()
        ));
        fs::create_dir(&root).unwrap();
        let log = root.join("ratchet.toml");
        let runs = root.join("runs");
        let expectations = root.join("expectations.toml");
        let driver = root.join("fake-driver");
        let fake_binary = root.join("fake-binary");
        let args = root.join("driver.args");

        fs::write(
            &expectations,
            r#"version = 1

[baseline]
timestamp_utc = "2026-09-02T08:17:59Z"
workspace_revision = "e12f1908f8e814b54f7eed11d9353241d30cadbe"
k_revision = "4a46d1231473b599c699160132fd6e76a5c46406"
artifacts = "baseline"

[[category]]
id = "fixture-exclusion"
decided_by = "test fixture"
meaning = "Exercise the exclusion contract."

[[case]]
name = "a"
baseline_verdict = "match"
baseline_stage = "krun"
exclusion = ""
reason = ""

[[case]]
name = "b"
baseline_verdict = "mismatch"
baseline_stage = "search"
exclusion = ""
reason = "measured mismatch"

[[case]]
name = "c"
baseline_verdict = "match"
baseline_stage = "kompile"
exclusion = "fixture-exclusion"
reason = "adjudicated fixture exclusion"

[[case]]
name = "d"
baseline_verdict = "krust-unsupported"
baseline_stage = "kast"
exclusion = ""
reason = ""
"#,
        )
        .unwrap();
        fs::write(
            &driver,
            r#"#!/usr/bin/env bash
set -euo pipefail
printf '%s\n' "$@" > "$FAKE_ARGS"
results=
logs=
while (($#)); do
  case "$1" in
    --results)
      results=$2
      shift 2
      ;;
    --logs)
      logs=$2
      shift 2
      ;;
    *)
      shift
      ;;
  esac
done
mkdir -p "$logs"
cp "$FAKE_RESULTS" "$results"
"#,
        )
        .unwrap();
        fs::write(&fake_binary, "#!/usr/bin/env bash\nexit 0\n").unwrap();
        make_executable(&driver);
        make_executable(&fake_binary);

        Self {
            root,
            log,
            runs,
            expectations,
            driver,
            fake_binary,
            args,
        }
    }

    fn results(&self, name: &str, cases: &[(&str, &str, &str)]) -> PathBuf {
        let path = self.root.join(format!("{name}.toml"));
        let mut body = String::new();
        for (case, verdict, stage) in cases {
            body.push_str(&format!(
                "[[case]]\nname = {case:?}\nkind = \"ktest\"\nbackend = \"llvm\"\nverdict = {verdict:?}\nstage = {stage:?}\nreason = \"fixture\"\nseconds = 0.1\nsteps = 1\n\n[[case.step]]\nstep = {stage:?}\nverdict = {verdict:?}\nstage = {stage:?}\n\n"
            ));
        }
        fs::write(&path, body).unwrap();
        path
    }

    fn wrapper(&self) -> Command {
        let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let mut command = Command::new("bash");
        command
            .arg(workspace.join("scripts/conformance-ratchet.sh"))
            .args(["--log", self.log.to_str().unwrap()])
            .args(["--runs-dir", self.runs.to_str().unwrap()])
            .args(["--expectations", self.expectations.to_str().unwrap()])
            .env("CONFORMANCE_DRIVER", &self.driver)
            .env("CONFORMANCE_KRUST", &self.fake_binary)
            .env("CONFORMANCE_TEST_BINARY", &self.fake_binary)
            .env("CONFORMANCE_DRIVER_VERSION", "fixture-driver-v1")
            .env("REFERENCE_DIFFERENTIAL_ALLOW_UNPINNED", "1")
            .env("REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND", "rlimit-as")
            .env("FAKE_ARGS", &self.args);
        command
    }

    fn seed(&self, results: &Path) -> Output {
        self.wrapper()
            .args(["--seed", results.to_str().unwrap()])
            .args(["--label", "baseline"])
            .output()
            .unwrap()
    }

    fn run(&self, label: &str, results: &Path, selection: &[&str]) -> Output {
        self.run_with_driver(label, results, selection, "fixture-driver-v1")
    }

    fn run_with_driver(
        &self,
        label: &str,
        results: &Path,
        selection: &[&str],
        driver_version: &str,
    ) -> Output {
        self.wrapper()
            .args(["--label", label])
            .args(selection)
            .env("FAKE_RESULTS", results)
            .env("CONFORMANCE_DRIVER_VERSION", driver_version)
            .output()
            .unwrap()
    }

    fn audit(&self) -> Output {
        self.wrapper().arg("--audit").output().unwrap()
    }

    fn document(&self) -> Value {
        fs::read_to_string(&self.log)
            .unwrap()
            .parse::<Value>()
            .unwrap()
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.root).unwrap();
    }
}

fn make_executable(path: &Path) {
    let mut permissions = fs::metadata(path).unwrap().permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(path, permissions).unwrap();
}

#[test]
fn conformance_driver_mirrors_the_ratchet_ranks() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    for (verdict, rank) in [
        ("reference-error", "-1"),
        ("krust-error", "0"),
        ("mismatch", "1"),
        ("krust-unsupported", "2"),
        ("skipped-with-reason", "2"),
        ("match", "3"),
    ] {
        let output = Command::new("python3")
            .arg(workspace.join("scripts/conformance/run.py"))
            .args(["--rank", verdict])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{verdict}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stdout).trim(),
            rank,
            "rank for {verdict}",
        );
    }
}

#[test]
fn measurement_metadata_preserves_command_arguments() {
    let fixture = Fixture::new();
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let prefix = fixture.root.join("measurement");
    let args = [
        "python3",
        "-c",
        "pass",
        "quotes: '\"",
        "slash: \\",
        "line\nbreak",
        "\u{7f}",
        "\u{1f980}",
    ];
    let output = Command::new("python3")
        .arg(workspace.join("scripts/conformance/measure.py"))
        .arg("--log")
        .arg(&prefix)
        .arg("--")
        .args(args)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let metadata: Value = fs::read_to_string(prefix.with_extension("meta.toml"))
        .unwrap()
        .parse()
        .unwrap();
    let recorded = metadata["command"]
        .as_array()
        .unwrap()
        .iter()
        .map(|value| value.as_str().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(recorded, args);
    assert_eq!(metadata["exit_code"].as_integer(), Some(0));
}

#[test]
fn conformance_driver_compares_expected_errors_and_program_statuses() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let output = Command::new("python3")
        .arg(workspace.join("crates/k-rust/tests/fixtures/conformance/expected_errors.py"))
        .arg(workspace.join("scripts/conformance"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

#[test]
fn conformance_driver_forwards_kompile_warning_flags_and_md_selectors() {
    // checkWarns requires `-w2e -w all`, and markdownSelectors requires that
    // krust's per-run recompilation receive the
    // kompile recipe's `--md-selector`. The translations are pure functions of the
    // recipe, so they are checked without the reference toolchain. The recipe is a
    // ktest-fail one: `-w2e` is forwarded only where the reference's rejection depends
    // on it (see conformance_driver_forwards_w2e_only_where_the_reference_rejects_on_it).
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import json, sys
sys.path.insert(0, sys.argv[1])
import run
case = run.Case("markdownSelectors")
recipe = run.split_recipe(
    "/kbin/kompile -w2e -w all --md-selector '(k|keep) & !discard' --backend haskell"
    " test.md --output-definition ./test-kompiled"
)
kompile, why, info = run.krust_kompile_args(case, recipe, expect_fail=True)
def call(name, *args):
    function = getattr(run, name, None)
    return function(*args) if function else None
print(json.dumps({
    "kompile": kompile,
    "why": why,
    "dropped": info["dropped"] if info else None,
    "krun": call("krust_krun_args", case, "1.test", None, ["--depth", "3"], "KItem", "TEST-SYNTAX"),
    "kast": call("krust_kast_args", case, "TEST-SYNTAX", "KItem", "kast", None, "1.test"),
}))
"#;
    let output = Command::new("python3")
        .env("K_KOMPILE", "/kbin/kompile")
        .env("CONFORMANCE_KRUST", "/krust")
        .args(["-c", script])
        .arg(workspace.join("scripts/conformance"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let translated: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    let words = |key: &str| -> Vec<String> {
        translated[key]
            .as_array()
            .unwrap_or_else(|| panic!("{key} is not translated: {translated}"))
            .iter()
            .map(|word| word.as_str().unwrap().to_owned())
            .collect()
    };
    let kompile = words("kompile");
    assert!(
        kompile.windows(2).any(|pair| pair == ["--warnings", "all"]),
        "kompile forwards -w all: {kompile:?}"
    );
    assert!(
        kompile.iter().any(|word| word == "--warnings-to-errors"),
        "kompile forwards -w2e: {kompile:?}"
    );
    assert_eq!(
        translated["dropped"],
        serde_json::Value::Array(Vec::new()),
        "no kompile flag is dropped: {translated}"
    );
    for tool in ["krun", "kast"] {
        let args = words(tool);
        assert!(
            args.windows(2)
                .any(|pair| pair == ["--md-selector", "(k|keep) & !discard"]),
            "{tool} carries the kompile md-selector: {args:?}"
        );
        assert_eq!(args[0], "/krust");
    }
    let krun = words("krun");
    assert!(
        krun.windows(2).any(|pair| pair == ["--depth", "3"]),
        "{krun:?}"
    );
    assert_eq!(krun[1..4], ["krun", "test.md", "1.test"], "{krun:?}");
}

#[test]
fn conformance_driver_forwards_w2e_only_where_the_reference_rejects_on_it() {
    // Dropping `-Wno` while forwarding `-w2e` promotes warnings the reference disabled
    // (werrorCategory); krust's UnadmittedHookNamespace extension warning can also turn
    // an accepted reference recipe into a krust-error (prelude-warnings). The
    // warning contract is forwarded whole or not at all: `-w2e` reaches krust only for a
    // ktest-fail recipe without `-W`/`-Wno`; every other form is dropped and recorded.
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import json, sys
sys.path.insert(0, sys.argv[1])
import run
def translate(recipe, expect_fail):
    case = run.Case("warnings")
    args, why, info = run.krust_kompile_args(case, run.split_recipe(recipe), expect_fail=expect_fail)
    return {"args": args, "why": why, "dropped": info["dropped"] if info else None}
tail = " --no-exc-wrap --type-inference-mode checked --backend llvm test.k --output-definition ./test-kompiled"
print(json.dumps({
    "werrorCategory": translate("/kbin/kompile -w2e -Wno missing-syntax-module" + tail, False),
    "prelude-warnings": translate("/kbin/kompile -w all -w2e" + tail, False),
    "checkWarns": translate("/kbin/kompile -w2e -w all" + tail, True),
    "fail-with-Wno": translate("/kbin/kompile -w2e -w all -Wno useless-rule" + tail, True),
}))
"#;
    let output = Command::new("python3")
        .env("K_KOMPILE", "/kbin/kompile")
        .env("CONFORMANCE_KRUST", "/krust")
        .args(["-c", script])
        .arg(workspace.join("scripts/conformance"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let translated: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    let strings = |recipe: &str, key: &str| -> Vec<String> {
        translated[recipe][key]
            .as_array()
            .unwrap_or_else(|| panic!("{recipe}.{key} is not translated: {translated}"))
            .iter()
            .map(|word| word.as_str().unwrap().to_owned())
            .collect()
    };
    let promotes = |recipe: &str| {
        strings(recipe, "args")
            .iter()
            .any(|w| w == "--warnings-to-errors")
    };
    let level = |recipe: &str, level: &str| {
        strings(recipe, "args")
            .windows(2)
            .any(|pair| pair == ["--warnings", level])
    };
    let drops = |recipe: &str, prefix: &str| {
        strings(recipe, "dropped")
            .iter()
            .any(|flag| flag == prefix || flag.starts_with(&format!("{prefix} ")))
    };

    // ktest-fail without a per-category flag: the reference rejects because of -w2e.
    assert!(promotes("checkWarns"), "{translated}");
    assert!(level("checkWarns", "all"), "{translated}");
    assert_eq!(
        strings("checkWarns", "dropped"),
        Vec::<String>::new(),
        "{translated}"
    );

    // ktest with a per-category disable krust cannot express: neither half is forwarded.
    assert!(!promotes("werrorCategory"), "{translated}");
    assert!(
        drops("werrorCategory", "-Wno missing-syntax-module"),
        "{translated}"
    );
    assert!(drops("werrorCategory", "-w2e"), "{translated}");

    // ktest that the reference accepts: the level is forwarded, the promotion is not.
    assert!(level("prelude-warnings", "all"), "{translated}");
    assert!(!promotes("prelude-warnings"), "{translated}");
    assert!(drops("prelude-warnings", "-w2e"), "{translated}");
    assert!(!drops("prelude-warnings", "-w"), "{translated}");

    // ktest-fail with a per-category disable: still not forwarded in part.
    assert!(!promotes("fail-with-Wno"), "{translated}");
    assert!(level("fail-with-Wno", "all"), "{translated}");
    assert!(drops("fail-with-Wno", "-Wno useless-rule"), "{translated}");
    assert!(drops("fail-with-Wno", "-w2e"), "{translated}");
}

#[test]
fn bison_parser_manifest_covers_the_reviewed_positive_corpus() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let regression = workspace.join("k/k-distribution/tests/regression-new");
    let document = BISON_PARSERS.parse::<Value>().unwrap();
    assert_eq!(document["schema"].as_integer(), Some(1));
    let rows = document["case"].as_array().unwrap();
    assert_eq!(rows.len(), 19);

    let mut names = BTreeSet::new();
    let mut executable = 0;
    let mut executable_inputs = 0;
    let mut libraries = 0;
    let mut reviewed_matrix = String::new();
    for value in rows {
        let row = value.as_table().unwrap();
        let name = row["name"].as_str().unwrap();
        assert!(names.insert(name), "duplicate case {name}");
        let name_path = Path::new(name);
        assert!(!name_path.is_absolute());
        assert!(
            name_path
                .components()
                .all(|part| matches!(part, std::path::Component::Normal(_)))
        );
        let artifact = row["artifact"].as_str().unwrap();
        let comparison = row
            .get("comparison")
            .and_then(Value::as_str)
            .unwrap_or("exact");
        assert!(matches!(comparison, "exact" | "amb"));
        let inputs = row["inputs"].as_array().unwrap();
        let strings = inputs
            .iter()
            .map(|item| item.as_str().unwrap())
            .collect::<Vec<_>>();
        use std::fmt::Write as _;
        writeln!(
            &mut reviewed_matrix,
            "{name}\t{artifact}\t{comparison}\t{}\t{}",
            row.get("makefile").and_then(Value::as_str).unwrap_or(""),
            strings.join("\t")
        )
        .unwrap();
        assert!(!strings.is_empty(), "{name}");
        assert!(
            strings.windows(2).all(|pair| pair[0] < pair[1]),
            "{name}: {strings:?}"
        );
        for input in &strings {
            let input_path = Path::new(input);
            assert!(!input_path.is_absolute(), "{name}/{input}");
            assert!(
                input_path
                    .components()
                    .all(|part| matches!(part, std::path::Component::Normal(_))),
                "{name}/{input}"
            );
            if regression.is_dir() {
                assert!(
                    regression.join(name).join(input).is_file(),
                    "missing {name}/{input}"
                );
            }
        }
        match artifact {
            "executable" => {
                executable += 1;
                executable_inputs += inputs.len();
            }
            "shared-library" => libraries += 1,
            other => panic!("unknown artifact {other}"),
        }
        if comparison == "amb" {
            assert_eq!(name, "parse-c", "ambiguity requires individual review");
        }
    }
    assert_eq!((executable, executable_inputs, libraries), (18, 37, 1));
    let matrix_digest = Sha256::digest(reviewed_matrix.as_bytes())
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    assert_eq!(
        matrix_digest,
        "67f65334366f36782f461d65670d84369da29d907bfaad25ae7e627882a7de59"
    );
}

#[test]
fn conformance_driver_forwards_bison_generator_options() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import json, sys
sys.path.insert(0, sys.argv[1])
import run
def translate(flags):
    case = run.Case("bison-glr-bug")
    recipe = run.split_recipe("/kbin/kompile " + flags + " --backend llvm test.k --output-definition ./test-kompiled")
    args, why, info = run.krust_kompile_args(case, recipe)
    return {"args": args, "why": why, "dropped": info["dropped"]}
print(json.dumps({
    "lr": translate("--gen-bison-parser"),
    "glr": translate("--gen-glr-bison-parser --bison-lists"),
    "both": translate("--gen-bison-parser --gen-glr-bison-parser"),
    "depth": translate("--gen-glr-bison-parser --bison-stack-max-depth 12000"),
}))
"#;
    let output = Command::new("python3")
        .env("K_KOMPILE", "/kbin/kompile")
        .env("CONFORMANCE_KRUST", "/krust")
        .args(["-c", script])
        .arg(workspace.join("scripts/conformance"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let translated: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    let args = |row: &str| {
        translated[row]["args"]
            .as_array()
            .unwrap()
            .iter()
            .map(|value| value.as_str().unwrap())
            .collect::<Vec<_>>()
    };
    assert!(args("lr").contains(&"--gen-bison-parser"));
    assert!(args("glr").contains(&"--gen-glr-bison-parser"));
    assert!(args("glr").contains(&"--bison-lists"));
    assert!(args("both").contains(&"--gen-bison-parser"));
    assert!(args("both").contains(&"--gen-glr-bison-parser"));
    assert!(
        args("depth")
            .windows(2)
            .any(|pair| pair == ["--bison-stack-max-depth", "12000"])
    );
    for row in ["lr", "glr", "both", "depth"] {
        assert_eq!(
            translated[row]["dropped"],
            serde_json::json!([]),
            "{row}: {translated}"
        );
    }
}

#[test]
fn conformance_driver_passes_parser_bytes_to_the_semantic_comparator() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import json, os, sys, tempfile
sys.path.insert(0, sys.argv[1])
import run
root = tempfile.mkdtemp()
case = run.Case("glr")
case.dir = root
case.log = os.path.join(root, "logs")
case.ref_kompiled = os.path.join(root, "reference-kompiled")
os.makedirs(case.ref_kompiled)
os.makedirs(os.path.join(root, "krust-kompiled"))
open(os.path.join(case.ref_kompiled, "parser_PGM"), "wb").close()
open(os.path.join(root, "krust-kompiled", "parser_PGM"), "wb").close()
open(os.path.join(root, "1.test"), "wb").close()
calls = []
comparison = {}
def fake_to_file(command, cwd, timeout, stdout_path, env=None):
    calls.append({"command": command, "cwd": cwd, "stdout": stdout_path})
    os.makedirs(os.path.dirname(stdout_path), exist_ok=True)
    with open(stdout_path, "wb") as output: output.write(b"a{}()\\n")
    return 0, "", 0.01, False
def fake_test(name, env, cwd, timeout=120):
    comparison.update(name=name, env=env, cwd=cwd, timeout=timeout)
    return 0, "bison-parser-comparison = 'exact'\nbison-parser-reference-ambiguity-nodes = 0\nbison-parser-reference-alternatives = 0\nbison-parser-krust-ambiguity-nodes = 0\nbison-parser-krust-alternatives = 0\n", ""
run.sh_to_file = fake_to_file
run.run_test_binary_result = lambda *args, **kwargs: (*fake_test(*args, **kwargs), False)
run.run_bison_parsers(case)
print(json.dumps({"calls": calls, "comparison": comparison, "steps": case.steps}))
"#;
    let output = Command::new("python3")
        .args(["-c", script])
        .arg(workspace.join("scripts/conformance"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let observed: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    let calls = observed["calls"].as_array().unwrap();
    assert_eq!(calls.len(), 2);
    for call in calls {
        assert_eq!(call["command"][1], "1.test");
        assert_eq!(call["cwd"], observed["comparison"]["cwd"]);
    }
    assert_eq!(
        observed["comparison"]["name"],
        "generated_bison_parser_outputs_match"
    );
    assert_eq!(
        observed["comparison"]["env"]["K_REFERENCE_BISON_PARSER_OUTPUT"],
        calls[0]["stdout"]
    );
    assert_eq!(
        observed["comparison"]["env"]["K_RUST_BISON_PARSER_OUTPUT"],
        calls[1]["stdout"]
    );
    assert_eq!(
        observed["comparison"]["env"]["K_BISON_PARSER_ALLOW_AMBIGUITY"],
        "0"
    );
    assert_eq!(observed["steps"][0]["verdict"], "match");
    assert_eq!(observed["steps"][0]["comparison_policy"], "exact");
}

#[test]
fn conformance_driver_selects_lesson_7_concrete_makefile_and_drives_custom_case() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import json, os, sys, tempfile
sys.path.insert(0, sys.argv[1])
import run
case = run.Case("pl-tutorial/1_k/4_imp++/lesson_7")
case.dir = "/case"
commands = []
def fake_sh(command, cwd, timeout, **kwargs):
    commands.append(command)
    return 0, "KOMPILE_BACKEND = llvm\n", "", 0.0, False
run.sh = fake_sh
run.make_vars(case)
run.make_recipes(case)

root = tempfile.mkdtemp()
run.WORK_TREE = root
run.REG = "regression"
run.LOGS = os.path.join(root, "logs")
os.makedirs(os.path.join(root, run.REG, case.name))
run.make_vars = lambda case: {}
run.make_recipes = lambda case: (0, [], "")
driven = []
run.run_bison_parsers = lambda case: driven.append(case.makefile)
result = run.run_case(case.name, "custom")
print(json.dumps({"commands": commands, "driven": driven, "verdict": result.verdict}))
"#;
    let output = Command::new("python3")
        .args(["-c", script])
        .arg(workspace.join("scripts/conformance"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let observed: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    for command in observed["commands"].as_array().unwrap() {
        let prefix = command.as_array().unwrap()[..3]
            .iter()
            .map(|value| value.as_str().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(prefix, ["make", "-f", "Makefile.concrete"]);
    }
    assert_eq!(observed["driven"], serde_json::json!(["Makefile.concrete"]));
}

#[test]
fn conformance_driver_classifies_generated_parser_failures() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import json, os, sys, tempfile
sys.path.insert(0, sys.argv[1])
import run
def probe(mode):
    root = tempfile.mkdtemp()
    case = run.Case("glr")
    case.dir = root
    case.log = os.path.join(root, "logs")
    case.ref_kompiled = os.path.join(root, "reference-kompiled")
    os.makedirs(case.ref_kompiled)
    os.makedirs(os.path.join(root, "krust-kompiled"))
    reference = os.path.join(case.ref_kompiled, "parser_PGM")
    krust = os.path.join(root, "krust-kompiled", "parser_PGM")
    if mode not in ("missing-reference", "expired-missing-reference"): open(reference, "wb").close()
    if mode not in ("missing-krust", "expired-missing-krust"): open(krust, "wb").close()
    if mode.startswith("expired-"): case.deadline = case.t0 - 1
    def fake(command, cwd, timeout, stdout_path, env=None):
        is_reference = command[0] == reference
        if mode == "reference-nonzero" and is_reference: return 7, "reference failed", 0.1, False
        if mode == "reference-timeout" and is_reference: return -9, "", 1.0, True
        if mode == "krust-nonzero" and not is_reference: return 8, "krust failed", 0.1, False
        if mode == "krust-timeout" and not is_reference: return -9, "", 1.0, True
        os.makedirs(os.path.dirname(stdout_path), exist_ok=True)
        with open(stdout_path, "wb") as output: output.write(b"a{}()\\n")
        return 0, "", 0.1, False
    run.sh_to_file = fake
    if mode == "comparator-timeout":
        run.run_test_binary_result = lambda *args, **kwargs: (-9, "", "", True)
    elif mode == "comparator-infrastructure":
        run.run_test_binary_result = lambda *args, **kwargs: (127, "", "missing comparator", False)
    elif mode == "comparator-mismatch":
        run.run_test_binary_result = lambda *args, **kwargs: (101, "", "semantic difference", False)
    else:
        run.run_test_binary_result = lambda *args, **kwargs: (0, "bison-parser-comparison = 'exact'\n", "", False)
    run.run_bison_parsers(case)
    return case.steps[0]["verdict"]
print(json.dumps({mode: probe(mode) for mode in [
    "missing-reference", "missing-krust", "expired-missing-reference",
    "expired-missing-krust", "reference-nonzero", "reference-timeout",
    "krust-nonzero", "krust-timeout", "comparator-timeout",
    "comparator-infrastructure", "comparator-mismatch",
]}))
"#;
    let output = Command::new("python3")
        .args(["-c", script])
        .arg(workspace.join("scripts/conformance"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let verdicts: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    for mode in [
        "missing-reference",
        "reference-nonzero",
        "reference-timeout",
        "expired-missing-reference",
    ] {
        assert_eq!(verdicts[mode], "reference-error", "{mode}: {verdicts}");
    }
    for mode in [
        "missing-krust",
        "krust-nonzero",
        "krust-timeout",
        "comparator-timeout",
        "comparator-infrastructure",
        "expired-missing-krust",
    ] {
        assert_eq!(verdicts[mode], "krust-error", "{mode}: {verdicts}");
    }
    assert_eq!(verdicts["comparator-mismatch"], "mismatch", "{verdicts}");
}

#[test]
fn conformance_driver_reports_missing_comparator_infrastructure() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import json, os, sys, tempfile
sys.path.insert(0, sys.argv[1])
import run
root = tempfile.mkdtemp()
run.KR = root
run.TEST_BINARY = None
missing_directory = run.run_test_binary_result("unused", {}, root)
os.makedirs(os.path.join(root, "target", "debug", "deps"))
missing_binary = run.run_test_binary_result("unused", {}, root)
print(json.dumps({"directory": missing_directory, "binary": missing_binary}))
"#;
    let output = Command::new("python3")
        .args(["-c", script])
        .arg(workspace.join("scripts/conformance"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let observed: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    for key in ["directory", "binary"] {
        let result = observed[key].as_array().unwrap();
        assert_eq!(result.len(), 4, "{key}: {observed}");
        assert_eq!(result[0], 1, "{key}: {observed}");
        assert_eq!(result[3], false, "{key}: {observed}");
        assert!(
            result[2]
                .as_str()
                .unwrap()
                .contains("no reference_differential test binary"),
            "{key}: {observed}"
        );
    }
}

#[test]
fn conformance_driver_bison_mode_skips_runtime_recipes_and_ranks_parser_steps() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import json, os, sys, tempfile
sys.path.insert(0, sys.argv[1])
import run
root = tempfile.mkdtemp()
run.WORK_TREE = root
run.REG = "regression"
run.LOGS = os.path.join(root, "logs")
run.BISON_PARSER_ONLY = True
case_dir = os.path.join(root, run.REG, "glr")
os.makedirs(case_dir)
run.make_vars = lambda case: {}
run.make_recipes = lambda case: (0, ["kompile", "krun"], "")
run.split_recipe = lambda line: {
    "tool": line,
    "args": ["test.k"] if line == "kompile" else ["1.test"],
    "raw": line,
    "out": None,
}
driven = []
def fake_kompile(case, recipe, expect_fail):
    driven.append(recipe["tool"])
    case.main_module = "TEST"
    run.step_record(case, step="kompile", stage="kompile", verdict="reference-error")
def fake_bison(case):
    driven.append("bison-parser")
    run.step_record(case, step="bison-parser", stage="bison-parser", verdict="match")
run.do_kompile = fake_kompile
run.run_bison_parsers = fake_bison
run.do_krun = lambda *args, **kwargs: driven.append("krun")
result = run.run_case("glr", "ktest")
print(json.dumps({"driven": driven, "verdict": result.verdict, "stage": result.stage}))
"#;
    let output = Command::new("python3")
        .args(["-c", script])
        .arg(workspace.join("scripts/conformance"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let observed: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(
        observed["driven"],
        serde_json::json!(["kompile", "bison-parser"])
    );
    assert_eq!(observed["verdict"], "match");
    assert_eq!(observed["stage"], "bison-parser");
}

#[test]
fn conformance_driver_classifies_a_kprove_compiler_rejection_by_its_diagnostic_lines() {
    // checkClaimError/rule-spec.k.out is `[Error] Compiler: Only claims and simplification
    // rules are allowed in proof modules.` followed by K's tab-indented Source, Location and
    // quoted source line (`6 |	    rule <k> doIt(foo) => doIt(0) ... </k>`). kprove_verdicts
    // searched the whole file for `<k>` and read the quoted rule as a not-proven
    // counterexample, so krust's matching Error[ProofModuleRule] rejection was recorded as
    // krust-error (host ratchet runs 3, 4 and 16). The verdict kinds are a pure function of
    // the .out text and krust's output, so they are checked without the reference toolchain.
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r##"
import json, sys
sys.path.insert(0, sys.argv[1])
import run
rejection = (
    "[Error] Compiler: Only claims and simplification rules are allowed in proof modules.\n"
    "\tSource(rule-spec.k)\n"
    "\tLocation(6,10,6,43)\n"
    "\t6 |\t    rule <k> doIt(foo) => doIt(0) ... </k>\n"
    "\t  .\t         ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n"
    "[Error] Compiler: Had 1 structural errors.\n"
)
krust_rejection = "rule-spec.krust-wrapped.k:7:5: Error[ProofModuleRule]: Only claims and simplification rules are allowed in proof modules.\n"
counterexample = (
    "[Error] Prover: the following claims could not be proved:\n"
    "#Not ( #Ceil ( doIt ( 0 ) ) )\n"
    "<generatedTop>\n"
    "  <k>\n"
    "    doIt ( 0 ) ~> .K\n"
    "  </k>\n"
    "</generatedTop>\n"
)
print(json.dumps({
    "rejection": run.kprove_verdicts(rejection, "", krust_rejection, 1)[:4],
    "rejection-proven": run.kprove_verdicts(rejection, "claim #1: proven (4 states, 0 unexplored)\n", "", 0)[:4],
    "counterexample": run.kprove_verdicts(counterexample, "", "1 claims were not proven\n", 1)[:4],
    "proven": run.kprove_verdicts("#Top\n", "claim #1: proven (4 states, 0 unexplored)\n", "", 0)[:4],
}))
"##;
    let output = Command::new("python3")
        .env("K_KOMPILE", "/kbin/kompile")
        .env("CONFORMANCE_KRUST", "/krust")
        .args(["-c", script])
        .arg(workspace.join("scripts/conformance"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let verdicts: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    let kinds = |name: &str| -> Vec<String> {
        verdicts[name]
            .as_array()
            .unwrap()
            .iter()
            .map(|value| value.as_str().unwrap().to_owned())
            .collect()
    };
    assert_eq!(
        kinds("rejection")[..3],
        ["error", "error", "match"],
        "{verdicts}"
    );
    assert_eq!(
        kinds("rejection-proven")[..3],
        ["error", "proven", "mismatch"],
        "{verdicts}"
    );
    assert_eq!(
        kinds("counterexample")[..3],
        ["not-proven", "not-proven", "match"],
        "{verdicts}"
    );
    assert_eq!(
        kinds("proven")[..3],
        ["proven", "proven", "match"],
        "{verdicts}"
    );
}

#[test]
fn conformance_driver_treats_a_default_kast_parser_script_as_the_default_program_parse() {
    // star-multiplicity's recipe is `krun 1.test --parser ./test-parser` where test-parser is
    // `cat "$1" | kast - --output kore`: K's own default program parser (krun invokes kparse
    // on the program file and reads KORE; kast without --sort or --module parses the program
    // at the $PGM sort with the main syntax module). krust's krun parses the program the same
    // way by default, so that flag has an exact equivalent; the driver recorded
    // krust-unsupported instead (host ratchet run 16, rank 2 above the kompile match). A
    // parser that is not the default parse (`cat`, a KORE program; a kast with --sort or
    // --module) stays unsupported.
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import json, os, sys, tempfile
sys.path.insert(0, sys.argv[1])
import run
case = run.Case("star-multiplicity")
case.dir = tempfile.mkdtemp()
def probe(name, text):
    if text is not None:
        with open(os.path.join(case.dir, name), "w") as f: f.write(text)
    return run.default_parser_script(case, name)
print(json.dumps({
    "cat-kast": probe("./test-parser", 'cat "$1" | kast - --output kore\n'),
    "shebang": probe("./with-shebang", '#!/bin/sh\n# parse the program\nkast "$1" -o kore\n'),
    "sorted": probe("./sorted", 'kast --sort Foo "$1" --output kore\n'),
    "module": probe("./module", 'cat "$1" | kast - --module OTHER --output kore\n'),
    "two-commands": probe("./two", 'kast "$1" --output kore\necho done\n'),
    "cat": probe("cat", None),
    "missing": probe("./missing", None),
}))
"#;
    let output = Command::new("python3")
        .env("K_KOMPILE", "/kbin/kompile")
        .env("CONFORMANCE_KRUST", "/krust")
        .args(["-c", script])
        .arg(workspace.join("scripts/conformance"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let translated: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    let equivalent = |name: &str| translated[name].as_str().map(str::to_owned);
    assert!(
        equivalent("cat-kast").is_some_and(|note| note.contains("kast")),
        "{translated}"
    );
    assert!(equivalent("shebang").is_some(), "{translated}");
    for other in ["sorted", "module", "two-commands", "cat", "missing"] {
        assert!(translated[other].is_null(), "{other}: {translated}");
    }
}

#[test]
fn conformance_driver_forwards_krun_pattern_projection() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import json, os, sys, tempfile
sys.path.insert(0, sys.argv[1])
import run

captured = []
def fake_run(case, kind, prog, stdin_path, extra, sort, syntax_module, step):
    args = run.krust_krun_args(case, prog, stdin_path, extra, sort, syntax_module)
    captured.append(args)
    return args, 0, "\\top{SortGeneratedTopCell{}}()", "", 0.0, False
run.run_krust_program = fake_run

def probe(arguments):
    root = tempfile.mkdtemp()
    case = run.Case("pattern-projection")
    case.dir = root
    case.log = os.path.join(root, "logs")
    case.ref_kompiled = os.path.join(root, "reference-kompiled")
    case.def_file = "test.k"
    case.main_module = "TEST"
    case.syntax_module = "TEST-SYNTAX"
    case.pgm_sort = "KItem"
    before = len(captured)
    recipe = run.split_recipe("/kbin/krun " + arguments)
    step = run.do_krun(case, recipe)
    return {
        "args": captured[-1] if len(captured) != before else None,
        "verdict": step["verdict"],
        "reason": step.get("reason"),
    }

pattern = "<tasks> $(echo must-not-run) ; .Bag </tasks>"
print(json.dumps({
    "plain": probe("program"),
    "pattern": probe("program --pattern " + repr(pattern)),
    "search": probe("program --search-final --pattern " + repr(pattern)),
    "repeated": probe("program --pattern first --pattern second"),
    "mixed": probe("program --search-final --pattern surface --search-pattern target.kore"),
    "pattern_value": pattern,
}))
"#;
    let output = Command::new("python3")
        .env("K_KOMPILE", "/kbin/kompile")
        .env("CONFORMANCE_KRUST", "/krust")
        .args(["-c", script])
        .arg(workspace.join("scripts/conformance"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let probes: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    let arguments = |name: &str| -> Vec<&str> {
        probes[name]["args"]
            .as_array()
            .unwrap_or_else(|| panic!("{name} did not invoke krust: {probes}"))
            .iter()
            .map(|argument| argument.as_str().unwrap())
            .collect()
    };
    let plain = arguments("plain");
    let pattern = arguments("pattern");
    assert_eq!(
        pattern[..plain.len()],
        plain,
        "--pattern must not change the base krust argv"
    );
    assert_eq!(
        &pattern[plain.len()..],
        ["--pattern", probes["pattern_value"].as_str().unwrap()]
    );
    let search = arguments("search");
    assert_eq!(
        &search[plain.len()..],
        [
            "--search-final",
            "--pattern",
            probes["pattern_value"].as_str().unwrap(),
        ]
    );
    for invalid in ["repeated", "mixed"] {
        assert!(probes[invalid]["args"].is_null(), "{invalid}: {probes}");
        assert_eq!(
            probes[invalid]["verdict"].as_str(),
            Some("krust-unsupported"),
            "{invalid}: {probes}"
        );
    }
}

fn baseline_cases() -> [(&'static str, &'static str, &'static str); 4] {
    [
        ("a", "match", "krun"),
        ("b", "mismatch", "search"),
        ("c", "match", "kompile"),
        ("d", "krust-unsupported", "kast"),
    ]
}

fn run_cases(run: &Value) -> BTreeMap<&str, &Value> {
    run["case"]
        .as_array()
        .unwrap()
        .iter()
        .map(|case| (case["name"].as_str().unwrap(), case))
        .collect()
}

#[test]
fn conformance_expectations_cover_the_baseline_and_classify_accepted_failures() {
    let document = EXPECTATIONS
        .parse::<Value>()
        .expect("valid conformance expectations TOML");
    assert_eq!(document["version"].as_integer(), Some(1));
    let categories = document["category"]
        .as_array()
        .expect("exclusion categories");
    let category_ids = categories
        .iter()
        .map(|category| {
            let decision = category["decided_by"]
                .as_str()
                .expect("compatibility decision");
            let (path, anchor) = decision.split_once('#').expect("decision section anchor");
            assert_eq!(path, "docs/compatibility.md");
            let compatibility = include_str!("../../../docs/compatibility.md");
            assert!(
                compatibility
                    .lines()
                    .filter_map(|line| line.strip_prefix("## "))
                    .any(|heading| heading.to_lowercase().replace(' ', "-") == anchor),
                "unresolved compatibility decision: {decision}"
            );
            category["id"].as_str().unwrap()
        })
        .collect::<BTreeSet<_>>();
    let cases = document["case"].as_array().expect("case expectations");
    assert_eq!(cases.len(), 256, "entry 0 has 256 regression-new leaves");
    assert_eq!(
        document["acceptance"]["case_count"].as_integer(),
        Some(cases.len() as i64)
    );
    let mut names = BTreeSet::new();
    let mut verdicts = BTreeMap::<&str, usize>::new();
    for case in cases {
        let name = case["name"].as_str().expect("case name");
        assert!(names.insert(name), "duplicate expectation for {name}");
        let verdict = case["baseline_verdict"].as_str().expect("baseline verdict");
        let accepted = case["accepted_verdict"].as_str().expect("accepted verdict");
        assert!(matches!(
            accepted,
            "match"
                | "mismatch"
                | "krust-error"
                | "krust-unsupported"
                | "skipped-with-reason"
                | "reference-error"
        ));
        assert!(
            !case["accepted_stage"]
                .as_str()
                .expect("accepted stage")
                .is_empty()
        );
        *verdicts.entry(verdict).or_default() += 1;
        assert!(case.get("tickets").is_none());
        let exclusion = case["exclusion"].as_str().expect("exclusion string");
        if !exclusion.is_empty() {
            assert!(
                category_ids.contains(exclusion),
                "unknown exclusion on {name}"
            );
            assert!(
                !case["reason"].as_str().unwrap_or_default().is_empty(),
                "excluded case {name} needs a reason"
            );
        }
        if matches!(accepted, "mismatch" | "krust-error") {
            assert!(
                !case["reason"].as_str().unwrap_or_default().is_empty(),
                "accepted failure {name} needs a measured-behavior explanation"
            );
        }
    }
    assert_eq!(
        verdicts,
        BTreeMap::from([
            ("krust-error", 99),
            ("krust-unsupported", 25),
            ("match", 86),
            ("mismatch", 36),
            ("skipped-with-reason", 10),
        ])
    );
}

#[test]
fn versioned_acceptance_survives_a_fresh_log_and_a_driver_change() {
    let fixture = Fixture::new();
    let source = fs::read_to_string(&fixture.expectations).unwrap();
    fs::write(
        &fixture.expectations,
        source.replace(
            "baseline_verdict = \"mismatch\"",
            "baseline_verdict = \"mismatch\"\naccepted_verdict = \"match\"\naccepted_stage = \"search\"",
        ),
    )
    .unwrap();
    // A fresh measurement log must not erase progress recorded in the repository.
    let old_baseline = fixture.results("old-baseline", &baseline_cases());
    assert_eq!(fixture.seed(&old_baseline).status.code(), Some(3));
    let unchanged = fixture.results("unchanged", &[("b", "mismatch", "search")]);
    let output = fixture.run_with_driver("new-driver", &unchanged, &["--cases", "b"], "v2");
    assert_eq!(output.status.code(), Some(3));
    assert_eq!(fixture.audit().status.code(), Some(3));
    let document = fixture.document();
    let run = document["run"].as_array().unwrap().last().unwrap();
    assert_eq!(run_cases(run)["b"]["floor_rank"].as_integer(), Some(3));
    let recovered = fixture.results("recovered", &[("b", "match", "search")]);
    assert!(
        fixture
            .run("recovered", &recovered, &["--cases", "b"])
            .status
            .success()
    );
    assert!(fixture.audit().status.success());
}

#[test]
fn versioned_acceptance_seeds_without_private_results_or_reference_tools() {
    let fixture = Fixture::new();
    fs::write(&fixture.expectations, EXPECTATIONS).unwrap();
    let output = fixture
        .wrapper()
        .args(["--seed-acceptance", "--label", "accepted"])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        !fixture.args.exists(),
        "seeding must not invoke the measurement driver"
    );
    let document = fixture.document();
    let run = &document["run"].as_array().unwrap()[0];
    assert_eq!(run["driver_version"].as_str(), Some("accepted-baseline"));
    assert_eq!(run["case"].as_array().unwrap().len(), 256);
    let expectations = EXPECTATIONS.parse::<Value>().unwrap();
    for expected in expectations["case"].as_array().unwrap() {
        let name = expected["name"].as_str().unwrap();
        assert_eq!(
            run_cases(run)[name]["verdict"],
            expected["accepted_verdict"]
        );
    }
    assert!(fixture.audit().status.success());
}

#[test]
fn conformance_ratchet_seeds_entry_zero_from_results() {
    let fixture = Fixture::new();
    let baseline = fixture.results("baseline", &baseline_cases());
    let output = fixture.seed(&baseline);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );

    let document = fixture.document();
    let runs = document["run"].as_array().unwrap();
    assert_eq!(runs.len(), 1);
    assert_eq!(runs[0]["sequence"].as_integer(), Some(0));
    assert_eq!(runs[0]["driver_version"].as_str(), Some("00-baseline"));
    assert_eq!(runs[0]["counts"]["match"].as_integer(), Some(2));
    assert_eq!(runs[0]["case"].as_array().unwrap().len(), 4);
    assert!(
        run_cases(&runs[0])
            .values()
            .all(|case| case["delta"].as_str() == Some("new"))
    );
}

#[test]
fn conformance_ratchet_records_improvements_and_fails_on_regression() {
    let fixture = Fixture::new();
    let baseline = fixture.results("baseline", &baseline_cases());
    assert!(fixture.seed(&baseline).status.success());
    let floor = fixture.results("floor", &baseline_cases());
    assert!(fixture.run("floor", &floor, &["--all"]).status.success());
    let changed = fixture.results(
        "changed",
        &[
            ("a", "mismatch", "krun"),
            ("b", "match", "search"),
            ("c", "match", "kompile"),
            ("d", "krust-unsupported", "kast"),
        ],
    );
    let output = fixture.run("changed", &changed, &["--all"]);
    assert_eq!(output.status.code(), Some(3));

    let document = fixture.document();
    let run = document["run"].as_array().unwrap().last().unwrap();
    assert_eq!(
        run["regressions"].as_array().unwrap()[0].as_str(),
        Some("a")
    );
    assert_eq!(
        run["improvements"].as_array().unwrap()[0].as_str(),
        Some("b")
    );
    assert_eq!(run_cases(run)["a"]["delta"].as_str(), Some("regression"));
    assert_eq!(run_cases(run)["b"]["delta"].as_str(), Some("improvement"));
}

#[test]
fn conformance_ratchet_reports_driver_deltas_above_the_floor_without_failing() {
    // Entry 0 is the initial measurement floor: a case that a later driver raised above it may fall back
    // to the floor under yet another driver version without failing the run.
    let fixture = Fixture::new();
    let baseline = fixture.results("baseline", &baseline_cases());
    assert!(fixture.seed(&baseline).status.success());
    let raised = fixture.results(
        "raised",
        &[
            ("a", "match", "krun"),
            ("b", "match", "search"),
            ("c", "match", "kompile"),
            ("d", "krust-unsupported", "kast"),
        ],
    );
    let output = fixture.run_with_driver("raised", &raised, &["--all"], "fixture-driver-v1");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let lowered = fixture.results("lowered", &baseline_cases());
    let output = fixture.run_with_driver("lowered", &lowered, &["--all"], "fixture-driver-v2");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let document = fixture.document();
    let run = document["run"].as_array().unwrap().last().unwrap();
    assert_eq!(run["regressions"].as_array().unwrap().len(), 0);
    assert_eq!(
        run["driver_deltas"].as_array().unwrap(),
        &[Value::from("b")],
        "only the case whose rank changed across driver versions is annotated"
    );
    let b = run_cases(run)["b"];
    assert_eq!(b["delta"].as_str(), Some("driver-delta"));
    assert_eq!(b["previous_rank"].as_integer(), Some(3));
    assert_eq!(b["floor_rank"].as_integer(), Some(1));
    assert_eq!(b["rank"].as_integer(), Some(1));
}

#[test]
fn conformance_ratchet_fails_below_the_initial_measurement_floor_across_driver_versions() {
    let fixture = Fixture::new();
    let baseline = fixture.results("baseline", &baseline_cases());
    assert!(fixture.seed(&baseline).status.success());
    let changed = fixture.results(
        "driver-change",
        &[
            ("a", "mismatch", "krun"),
            ("b", "mismatch", "search"),
            ("c", "match", "kompile"),
            ("d", "krust-unsupported", "kast"),
        ],
    );
    let output =
        fixture.run_with_driver("driver-change", &changed, &["--all"], "fixture-driver-v1");
    assert_eq!(
        output.status.code(),
        Some(3),
        "a rank below the entry-0 floor must fail even across driver versions: {}",
        String::from_utf8_lossy(&output.stdout)
    );
    let document = fixture.document();
    let run = document["run"].as_array().unwrap().last().unwrap();
    assert_eq!(run["regressions"].as_array().unwrap(), &[Value::from("a")]);
    assert_eq!(
        run["driver_deltas"].as_array().unwrap(),
        &[Value::from("a")],
        "the driver change still annotates the row"
    );
    let a = run_cases(run)["a"];
    assert_eq!(a["delta"].as_str(), Some("regression"));
    assert_eq!(a["previous_rank"].as_integer(), Some(3));
    assert_eq!(a["floor_rank"].as_integer(), Some(3));
    assert_eq!(a["rank"].as_integer(), Some(1));
}

#[test]
fn conformance_ratchet_counts_improvements_across_driver_versions() {
    let fixture = Fixture::new();
    let baseline = fixture.results("baseline", &baseline_cases());
    assert!(fixture.seed(&baseline).status.success());
    let improved = fixture.results(
        "improved",
        &[
            ("a", "match", "krun"),
            ("b", "match", "search"),
            ("c", "match", "kompile"),
            ("d", "krust-unsupported", "kast"),
        ],
    );
    let output = fixture.run_with_driver("improved", &improved, &["--all"], "fixture-driver-v1");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let document = fixture.document();
    let run = document["run"].as_array().unwrap().last().unwrap();
    assert_eq!(run["improvements"].as_array().unwrap(), &[Value::from("b")]);
    assert_eq!(
        run["driver_deltas"].as_array().unwrap(),
        &[Value::from("b")]
    );
    assert_eq!(run_cases(run)["b"]["delta"].as_str(), Some("improvement"));
}

#[test]
fn conformance_ratchet_never_fails_on_excluded_cases_across_driver_versions() {
    let fixture = Fixture::new();
    let baseline = fixture.results("baseline", &baseline_cases());
    assert!(fixture.seed(&baseline).status.success());
    let excluded_drop = fixture.results(
        "excluded-drop",
        &[
            ("a", "match", "krun"),
            ("b", "mismatch", "search"),
            ("c", "krust-error", "kompile"),
            ("d", "krust-unsupported", "kast"),
        ],
    );
    let output = fixture.run_with_driver(
        "excluded-drop",
        &excluded_drop,
        &["--all"],
        "fixture-driver-v1",
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let document = fixture.document();
    let run = document["run"].as_array().unwrap().last().unwrap();
    assert_eq!(run["regressions"].as_array().unwrap().len(), 0);
    assert_eq!(run["excluded"].as_array().unwrap(), &[Value::from("c")]);
    let c = run_cases(run)["c"];
    assert_eq!(c["delta"].as_str(), Some("regression"));
    assert_eq!(c["floor_rank"].as_integer(), Some(3));
}

#[test]
fn conformance_ratchet_fails_while_a_case_stays_below_the_initial_measurement_floor() {
    // The exit criterion is "no case below its initial measured rank": a case that already fell below
    // its floor keeps failing every run that measures it until it is raised, even when its
    // rank is unchanged against the previous measurement; excluded cases never count.
    let fixture = Fixture::new();
    let baseline = fixture.results("baseline", &baseline_cases());
    assert!(fixture.seed(&baseline).status.success());
    let dropped = fixture.results(
        "dropped",
        &[
            ("a", "mismatch", "krun"),
            ("b", "mismatch", "search"),
            ("c", "krust-error", "kompile"),
            ("d", "krust-unsupported", "kast"),
        ],
    );
    assert_eq!(
        fixture.run("dropped", &dropped, &["--all"]).status.code(),
        Some(3)
    );
    let unchanged = fixture.results("unchanged", &[("a", "mismatch", "krun")]);
    let output = fixture.run("unchanged", &unchanged, &["--cases", "a"]);
    assert_eq!(
        output.status.code(),
        Some(3),
        "a case still below its floor must fail the run: {}",
        String::from_utf8_lossy(&output.stdout)
    );
    let document = fixture.document();
    let run = document["run"].as_array().unwrap().last().unwrap();
    assert_eq!(run["regressions"].as_array().unwrap().len(), 0);
    assert_eq!(run["below_floor"].as_array().unwrap(), &[Value::from("a")]);
    assert_eq!(run_cases(run)["a"]["delta"].as_str(), Some("same"));
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("below required floor: [\"a\"]"),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );

    let excluded_only = fixture.results("excluded-only", &[("c", "krust-error", "kompile")]);
    let output = fixture.run("excluded-only", &excluded_only, &["--cases", "c"]);
    assert!(
        output.status.success(),
        "an excluded case below its floor never fails: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let document = fixture.document();
    let run = document["run"].as_array().unwrap().last().unwrap();
    assert_eq!(run["below_floor"].as_array().unwrap().len(), 0);
    assert_eq!(run["excluded"].as_array().unwrap(), &[Value::from("c")]);
}

#[test]
fn conformance_ratchet_audit_lists_cases_below_the_initial_measurement_floor() {
    let fixture = Fixture::new();
    let baseline = fixture.results("baseline", &baseline_cases());
    assert!(fixture.seed(&baseline).status.success());
    let clean = fixture.audit();
    assert!(
        clean.status.success(),
        "{}",
        String::from_utf8_lossy(&clean.stderr)
    );
    assert!(
        String::from_utf8_lossy(&clean.stdout).contains("below floor: 0"),
        "{}",
        String::from_utf8_lossy(&clean.stdout)
    );
    let changed = fixture.results(
        "driver-change",
        &[
            ("a", "mismatch", "krun"),
            ("b", "mismatch", "search"),
            ("c", "krust-error", "kompile"),
            ("d", "krust-unsupported", "kast"),
        ],
    );
    assert_eq!(
        fixture
            .run_with_driver("driver-change", &changed, &["--all"], "fixture-driver-v1")
            .status
            .code(),
        Some(3)
    );
    let output = fixture.audit();
    assert_eq!(output.status.code(), Some(3), "the audit fails like a run");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("| a | 3 | 1 | 1 | mismatch |  |"),
        "audit table lists the non-excluded case: {stdout}"
    );
    assert!(
        stdout.contains("| c | 3 | 0 | 1 | krust-error | fixture-exclusion |"),
        "audit table lists the excluded case with its exclusion: {stdout}"
    );
    assert!(!stdout.contains("| b |"), "b is at its floor: {stdout}");
    assert!(
        stdout.contains("below floor: 2 (1 non-excluded)"),
        "{stdout}"
    );
}

#[test]
fn conformance_ratchet_never_fails_on_excluded_cases() {
    let fixture = Fixture::new();
    let baseline = fixture.results("baseline", &baseline_cases());
    assert!(fixture.seed(&baseline).status.success());
    let floor = fixture.results("floor", &baseline_cases());
    assert!(fixture.run("floor", &floor, &["--all"]).status.success());
    let excluded_drop = fixture.results(
        "excluded-drop",
        &[
            ("a", "match", "krun"),
            ("b", "mismatch", "search"),
            ("c", "krust-error", "kompile"),
            ("d", "krust-unsupported", "kast"),
        ],
    );
    let output = fixture.run("excluded-drop", &excluded_drop, &["--all"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let document = fixture.document();
    let run = document["run"].as_array().unwrap().last().unwrap();
    assert_eq!(run["regressions"].as_array().unwrap().len(), 0);
    assert_eq!(run_cases(run)["c"]["delta"].as_str(), Some("regression"));
    assert_eq!(run["excluded"].as_array().unwrap()[0].as_str(), Some("c"));
}

#[test]
fn conformance_ratchet_reads_legacy_logs_without_weakening_the_floor() {
    let fixture = Fixture::new();
    let baseline = fixture.results("baseline", &baseline_cases());
    assert!(fixture.seed(&baseline).status.success());
    let legacy = fs::read_to_string(&fixture.log)
        .unwrap()
        .replace(
            "[[run.case]]",
            "[[run.case]]\ntickets = [\"historical-owner\"]",
        )
        .replace(
            "[[run]]",
            "[[run]]\noverdue = [\"b\"]\npromotion_candidates = []",
        );
    fs::write(&fixture.log, &legacy).unwrap();
    assert!(fixture.audit().status.success());
    let dropped = fixture.results("dropped", &[("a", "mismatch", "krun")]);
    let output = fixture.run("legacy-floor", &dropped, &["--cases", "a"]);
    assert_eq!(output.status.code(), Some(3));
    assert_eq!(fixture.audit().status.code(), Some(3));
    assert!(
        fs::read_to_string(&fixture.log)
            .unwrap()
            .starts_with(legacy.trim_end())
    );
    let document = fixture.document();
    let run = document["run"].as_array().unwrap().last().unwrap();
    assert_eq!(
        run["below_floor"].as_array().unwrap()[0].as_str(),
        Some("a")
    );
    for obsolete in ["overdue", "promotion_candidates"] {
        assert!(run.get(obsolete).is_none());
    }
    assert!(run_cases(run)["a"].get("tickets").is_none());
    assert!(!String::from_utf8_lossy(&output.stdout).contains("tickets"));
}

#[test]
fn conformance_ratchet_selects_cases_by_name_and_baseline_stage() {
    let fixture = Fixture::new();
    let baseline = fixture.results("baseline", &baseline_cases());
    assert!(fixture.seed(&baseline).status.success());
    for (label, selection, expected) in [
        ("case", vec!["--cases", "b"], vec!["b"]),
        ("stage", vec!["--stage", "krun"], vec!["a"]),
        (
            "union",
            vec!["--cases", "b", "--stage", "krun"],
            vec!["a", "b"],
        ),
    ] {
        let cases: Vec<_> = baseline_cases()
            .into_iter()
            .filter(|(name, _, _)| expected.contains(name))
            .collect();
        let results = fixture.results(label, &cases);
        let output = fixture.run(label, &results, &selection);
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let args = fs::read_to_string(&fixture.args).unwrap();
        let selected: Vec<_> = args
            .lines()
            .skip_while(|line| *line != "--cases")
            .skip(1)
            .collect();
        assert_eq!(selected, expected, "driver arguments: {args}");
        let document = fixture.document();
        let run = document["run"].as_array().unwrap().last().unwrap();
        assert_eq!(run_cases(run).keys().copied().collect::<Vec<_>>(), expected);
    }
}

#[test]
fn conformance_ratchet_preflight_failures_do_not_change_the_log() {
    let fixture = Fixture::new();
    let baseline = fixture.results("baseline", &baseline_cases());
    assert!(fixture.seed(&baseline).status.success());
    let before = fs::read(&fixture.log).unwrap();
    let output = fixture
        .wrapper()
        .args(["--label", "missing-driver", "--all"])
        .env("CONFORMANCE_DRIVER", fixture.root.join("missing-driver"))
        .env("FAKE_RESULTS", &baseline)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert_eq!(fs::read(&fixture.log).unwrap(), before);
}
