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
whole_case_reason = "the fixture case has no step that can be ranked"

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
            .env("CONFORMANCE_BACKLOG", "")
            .env("CONFORMANCE_VALUE_CONTRACT_GATE", &self.fake_binary)
            .env("FAKE_ARGS", &self.args);
        command
    }

    fn audit_with_backlog(&self, backlog: &Path) -> Output {
        self.wrapper()
            .args(["--audit", "--backlog", backlog.to_str().unwrap()])
            .output()
            .unwrap()
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

/// The critical-pair corpus gate (V12) reads the definitions the conformance driver compiles, so a
/// measurement runs it on the manifest cases that this run compiled (by their conformance case,
/// `issue-4114-overload-injection` for the gate's `issue-4114`), from the run's work tree, and a
/// difference it reports fails the ratchet.
#[test]
fn a_measurement_runs_the_critical_pair_corpus_gate_on_the_cases_it_compiled() {
    let fixture = Fixture::new();
    let mut expectations = fs::read_to_string(&fixture.expectations).unwrap();
    expectations.push_str(
        "\n[[case]]\nname = \"issue-4114-overload-injection\"\nbaseline_verdict = \"match\"\nbaseline_stage = \"krun\"\nexclusion = \"\"\nreason = \"\"\n",
    );
    fs::write(&fixture.expectations, expectations).unwrap();
    let gate = fixture.root.join("value-contract-gate");
    let calls = fixture.root.join("value-contract.calls");
    fs::write(
        &gate,
        format!(
            "#!/usr/bin/env bash\nprintf '%s\\n' \"$*\" >> {:?}\nexit \"$FAKE_GATE_STATUS\"\n",
            calls.to_str().unwrap()
        ),
    )
    .unwrap();
    make_executable(&gate);
    let results = fixture.results(
        "measured",
        &[
            ("issue-4114-overload-injection", "match", "krun"),
            ("a", "match", "krun"),
        ],
    );
    let seeded = fixture.seed(&results);
    assert!(seeded.status.success(), "{seeded:?}");
    for (status, expected) in [("0", Some(0)), ("3", Some(3))] {
        let output = fixture
            .wrapper()
            .args(["--label", &format!("gate-{status}")])
            .args(["--cases", "issue-4114-overload-injection", "a"])
            .env("FAKE_RESULTS", &results)
            .env("CONFORMANCE_VALUE_CONTRACT_GATE", &gate)
            .env("CONFORMANCE_WORK_TREE", "/fixture/work-tree")
            .env("FAKE_GATE_STATUS", status)
            .output()
            .unwrap();
        assert_eq!(
            output.status.code(),
            expected,
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    assert_eq!(
        fs::read_to_string(&calls).unwrap(),
        "--work-tree /fixture/work-tree issue-4114\n".repeat(2)
    );
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
fn c9_stdin_precondition_requires_diagnostic_and_definition_delimiter_run() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import importlib.util
import pathlib
import tempfile

workspace = pathlib.Path(__import__('os').environ['WORKSPACE'])
path = workspace / 'scripts/conformance/run.py'
spec = importlib.util.spec_from_file_location('conformance_run', path)
driver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(driver)
diagnostic = ('warning: execution ended with no successor at depth 8: '
              'rule STDIN-STREAM.stdinParseInt applied with an undefined result; '
              'refuted obligation \\ceil{SortInt{}, SortGeneratedTopCell{}}(String2Int(""))')
with tempfile.TemporaryDirectory() as root:
    root = pathlib.Path(root)
    definition = root / 'definition.kore'
    definition.write_text('''
      Lbl'Hash'parseInput'LParUndsCommUndsRParUnds'K-IO'Unds'Stream'Unds'String'Unds'String{}(
        \\dv{SortString{}}("Int"),
        \\dv{SortString{}}("|")
      )
    ''')
    repeated = root / 'repeated.in'
    repeated.write_text('2||4')
    single = root / 'single.in'
    single.write_text('2|4')
    assert driver.definition_stdin_delimiters(definition) == ['|']
    assert driver.c9_stdin_precondition_failure(diagnostic, repeated, definition)[0] == 'STDIN-STREAM.stdinParseInt'
    assert driver.c9_stdin_precondition_failure('', repeated, definition) is None
    assert driver.c9_stdin_precondition_failure(diagnostic, single, definition) is None
"#;
    let output = Command::new("python3")
        .args(["-c", script])
        .env("WORKSPACE", &workspace)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
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
    // compilation receive the recipe's `--md-selector`. krun reuses that artifact, while kast
    // still parses source and receives the selector. The translations are pure functions of the
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
    let kast = words("kast");
    assert!(
        kast.windows(2)
            .any(|pair| pair == ["--md-selector", "(k|keep) & !discard"]),
        "kast carries the kompile md-selector: {kast:?}"
    );
    let krun = words("krun");
    assert_eq!(krun[0], "/krust");
    assert!(
        krun.windows(2)
            .any(|pair| pair == ["--definition", "krust-kompiled"])
    );
    assert!(
        !krun
            .iter()
            .any(|arg| arg == "test.md" || arg == "--md-selector")
    );
    assert!(
        krun.windows(2).any(|pair| pair == ["--depth", "3"]),
        "{krun:?}"
    );
    assert_eq!(
        krun[1..4],
        ["krun", "--definition", "krust-kompiled"],
        "{krun:?}"
    );
}

#[test]
fn conformance_driver_reuses_one_rust_artifact_and_never_runs_an_llvm_payload() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import json, sys
sys.path.insert(0, sys.argv[1])
import run
case = run.Case("llvm-runtime")
case.needs_krust_runtime = True
compile_args, why, info = run.krust_kompile_args(
    case,
    run.split_recipe("/kbin/kompile --backend llvm test.k --main-module TEST --output-definition test-kompiled"),
)
runtime = run.krust_runtime_kompile_args(compile_args, info)
case.krust_runtime_definition = "krust-kompiled-runtime"
first = run.krust_krun_args(case, "one.test", None, [], "KItem", "TEST-SYNTAX")
second = run.krust_krun_args(case, "two.test", None, ["--search-final"], "KItem", "TEST-SYNTAX")
print(json.dumps({"runtime": runtime, "first": first, "second": second, "source": case.def_file, "why": why}))
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
    let words = |name: &str| {
        translated[name]
            .as_array()
            .unwrap()
            .iter()
            .map(|word| word.as_str().unwrap())
            .collect::<Vec<_>>()
    };
    let runtime = words("runtime");
    assert!(runtime.windows(2).any(|pair| pair == ["--backend", "rust"]));
    assert!(
        runtime
            .windows(2)
            .any(|pair| pair == ["--output-directory", "krust-kompiled-runtime"])
    );
    for name in ["first", "second"] {
        let run = words(name);
        assert!(
            run.windows(2)
                .any(|pair| pair == ["--definition", "krust-kompiled-runtime"])
        );
        assert!(
            !run.iter()
                .any(|word| *word == "test.k" || *word == "--main-module")
        );
    }
}

#[test]
fn conformance_driver_prepares_kprove_definitions_without_rewriting_specs() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import json, sys
sys.path.insert(0, sys.argv[1])
import run

markdown = run.Case("kprove-markdown")
kompile = run.split_recipe(
    "/kbin/kompile --backend haskell --main-module VERIFICATION"
    " --syntax-module SET-BALANCE verification.k --output-definition ./verification-kompiled"
)
proof_compile, compile_why, _ = run.krust_proof_kompile_args(markdown, kompile)
kprove = run.split_recipe(
    "/kbin/kprove set-balance-spec.md --md-selector 'keep&!(discard|k)'"
    " --definition ./verification-kompiled"
)
proof, proof_why, _ = run.krust_kprove_args(markdown, kprove)

plain = run.Case("plain-proof")
plain_compile = run.split_recipe(
    "/kbin/kompile --backend haskell plain.k --output-definition ./plain-kompiled"
)
run.krust_kompile_args(plain, plain_compile)
plain_proof, plain_why, _ = run.krust_kprove_args(
    plain,
    run.split_recipe("/kbin/kprove plain-spec.k --definition ./plain-kompiled"),
)

print(json.dumps({
    "proof_compile": proof_compile,
    "compile_why": compile_why,
    "proof": proof,
    "proof_why": proof_why,
    "plain_proof": plain_proof,
    "plain_why": plain_why,
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

    assert!(translated["compile_why"].is_null(), "{translated}");
    assert!(translated["proof_why"].is_null(), "{translated}");
    assert!(translated["plain_why"].is_null(), "{translated}");
    let proof_compile = words("proof_compile");
    assert!(proof_compile.iter().any(|arg| arg == "--for-proving"));
    assert!(
        proof_compile
            .windows(2)
            .any(|pair| pair == ["--backend", "rust"])
    );
    assert!(
        proof_compile
            .windows(2)
            .any(|pair| pair == ["--output-directory", "krust-kompiled-proof"])
    );
    assert!(
        !proof_compile.iter().any(|arg| arg == "--md-selector"),
        "the definition compile retains the kompile recipe's default `k` selector: {proof_compile:?}"
    );

    let proof = words("proof");
    assert_eq!(proof[2], "set-balance-spec.md", "{proof:?}");
    assert!(
        proof
            .windows(2)
            .any(|pair| pair == ["--compiled-definition", "krust-kompiled-proof"])
    );
    assert_eq!(
        proof
            .windows(2)
            .filter(|pair| pair[0] == "--md-selector")
            .map(|pair| pair[1].as_str())
            .collect::<Vec<_>>(),
        ["keep&!(discard|k)"]
    );
    assert!(!proof.iter().any(|arg| arg.contains(".krust-wrapped.")));

    let plain_proof = words("plain_proof");
    assert_eq!(plain_proof[2], "plain-spec.k");
    assert!(!plain_proof.iter().any(|arg| arg == "--md-selector"));
    assert!(
        !plain_proof
            .iter()
            .any(|arg| arg.contains(".krust-wrapped."))
    );
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
        assert!(matches!(comparison, "exact" | "amb" | "locations"));
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
            "shared-library" => {
                libraries += 1;
                assert_eq!(row["consumer"].as_str(), Some("test.c"));
                assert_eq!(row["library"].as_str(), Some("parser_KItem_TEST"));
            }
            other => panic!("unknown artifact {other}"),
        }
        if comparison == "amb" {
            assert_eq!(name, "parse-c", "ambiguity requires individual review");
        }
        if comparison == "locations" {
            assert!(
                matches!(
                    name,
                    "bison-parser-library" | "locations" | "locations2" | "locations3"
                ),
                "location normalization requires individual review: {name}"
            );
        }
    }
    assert_eq!((executable, executable_inputs, libraries), (18, 37, 1));
    let matrix_digest = Sha256::digest(reviewed_matrix.as_bytes())
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    assert_eq!(
        matrix_digest,
        "9e238cbf92217dcd9cd09fdd95a9e863422086e2288e5b5991c15a6abfb5d223"
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
    "library": translate("--gen-glr-bison-parser --bison-parser-library"),
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
    assert!(args("library").contains(&"--bison-parser-library"));
    assert!(
        args("depth")
            .windows(2)
            .any(|pair| pair == ["--bison-stack-max-depth", "12000"])
    );
    for row in ["lr", "glr", "both", "depth", "library"] {
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
        observed["comparison"]["env"]["K_BISON_PARSER_COMPARISON"],
        "exact"
    );
    assert_eq!(observed["steps"][0]["verdict"], "match");
    assert_eq!(observed["steps"][0]["comparison_policy"], "exact");
}

#[test]
fn conformance_driver_builds_the_shared_library_consumer_for_both_sides() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import json, os, sys, tempfile
sys.path.insert(0, sys.argv[1])
import run

def probe(mode):
    root = tempfile.mkdtemp()
    case = run.Case("bison-parser-library")
    case.dir = root
    case.log = os.path.join(root, "logs")
    case.ref_kompiled = os.path.join(root, "reference-kompiled")
    rust_kompiled = os.path.join(root, "krust-kompiled")
    os.makedirs(case.ref_kompiled)
    os.makedirs(rust_kompiled)
    os.makedirs(case.log)
    open(os.path.join(root, "test.c"), "wb").close()
    open(os.path.join(root, "test.in"), "wb").close()
    if mode != "missing-reference":
        open(os.path.join(case.ref_kompiled, "libparser_KItem_TEST.so"), "wb").close()
    if mode != "missing-krust":
        open(os.path.join(rust_kompiled, "libparser_KItem_TEST.so"), "wb").close()
    compile_calls = []
    parser_calls = []
    comparison = {}
    def fake_sh(command, cwd, timeout, **kwargs):
        compile_calls.append({"command": command, "cwd": cwd})
        with open(command[command.index("-o") + 1], "wb") as output:
            output.write(b"consumer")
        return 0, "", "", 0.01, False
    def fake_to_file(command, cwd, timeout, stdout_path, env=None):
        parser_calls.append({"command": command, "cwd": cwd, "env": env, "stdout": stdout_path})
        with open(stdout_path, "wb") as output:
            output.write(b"a{}()\n")
        return 0, "", 0.01, False
    def fake_compare(name, env, cwd, timeout):
        comparison.update(name=name, env=env, cwd=cwd)
        return 0, "bison-parser-comparison = 'exact'\n", "", False
    run.sh = fake_sh
    run.sh_to_file = fake_to_file
    run.run_test_binary_result = fake_compare
    run.run_bison_parsers(case)
    return {"compile": compile_calls, "parser": parser_calls,
            "comparison": comparison, "steps": case.steps}

print(json.dumps({mode: probe(mode) for mode in
                  ["success", "missing-reference", "missing-krust"]}))
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
    let success = &observed["success"];
    let compile = success["compile"].as_array().unwrap();
    assert_eq!(compile.len(), 2, "{success}");
    assert!(
        compile[0]["command"]
            .as_array()
            .unwrap()
            .iter()
            .any(|argument| argument.as_str().unwrap().contains("reference-kompiled"))
    );
    assert!(
        compile[1]["command"]
            .as_array()
            .unwrap()
            .iter()
            .any(|argument| argument.as_str().unwrap().contains("krust-kompiled"))
    );
    let parser = success["parser"].as_array().unwrap();
    assert_eq!(parser.len(), 2, "{success}");
    assert_eq!(parser[0]["command"][1], "test.in");
    assert_eq!(parser[1]["command"][1], "test.in");
    assert!(
        parser[0]["env"]
            .as_object()
            .unwrap()
            .values()
            .any(|value| { value.as_str().unwrap().ends_with("reference-kompiled") })
    );
    assert!(
        parser[1]["env"]
            .as_object()
            .unwrap()
            .values()
            .any(|value| { value.as_str().unwrap().ends_with("krust-kompiled") })
    );
    assert_eq!(success["steps"][0]["verdict"], "match");
    assert_eq!(
        success["comparison"]["env"]["K_REFERENCE_BISON_PARSER_OUTPUT"],
        parser[0]["stdout"]
    );
    assert_eq!(
        observed["missing-reference"]["steps"][0]["verdict"],
        "reference-error"
    );
    assert_eq!(
        observed["missing-krust"]["steps"][0]["verdict"],
        "krust-error"
    );
}

#[test]
fn conformance_driver_translates_kast_gen_parser_and_runs_the_generated_parsers() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import json, os, sys, tempfile
sys.path.insert(0, sys.argv[1])
import run

def probe(mode):
    root = tempfile.mkdtemp()
    case = run.Case("kast-bison")
    case.dir = root
    case.log = os.path.join(root, "logs")
    case.ref_kompiled = os.path.join(root, "kast-in-kompiled")
    case.def_file = "kast-in.k"
    case.syntax_module = "KAST-IN-SYNTAX"
    case.pgm_sort = "Pgm"
    os.makedirs(case.ref_kompiled)
    os.makedirs(case.log)
    open(os.path.join(root, "kast-in.k"), "wb").close()
    open(os.path.join(root, "1.kast-bison"), "wb").close()
    calls = []
    parser_calls = []
    comparison = {}
    def fake_sh(command, cwd, timeout, **kwargs):
        calls.append(command)
        if command[:2] == ["bash", "-c"]:
            if mode != "missing-reference":
                open(os.path.join(root, "bison_parser"), "wb").close()
            return 0, "", "", 0.01, False
        if mode == "krust-failure":
            return 8, "", "generation failed", 0.01, False
        open(command[-1], "wb").close()
        return 0, "", "", 0.01, False
    def fake_to_file(command, cwd, timeout, stdout_path, env=None):
        parser_calls.append({"command": command, "stdout": stdout_path})
        with open(stdout_path, "wb") as output:
            output.write(b"a{}()\n")
        return 0, "", 0.01, False
    def fake_compare(name, env, cwd, timeout):
        comparison.update(name=name, env=env)
        return 0, "bison-parser-comparison = 'exact'\n", "", False
    run.sh = fake_sh
    run.sh_to_file = fake_to_file
    run.run_test_binary_result = fake_compare
    recipe = run.split_recipe(
        "/kbin/kast --gen-parser --bison-stack-max-depth 12000 "
        "--definition ./kast-in-kompiled --module KAST-IN-SYNTAX --sort Pgm bison_parser")
    run.do_kast(case, recipe)
    run.run_kast_bison_parsers(case, ["1.kast-bison"])
    return {"calls": calls, "parser": parser_calls,
            "comparison": comparison, "steps": case.steps}

print(json.dumps({mode: probe(mode) for mode in
                  ["success", "missing-reference", "krust-failure"]}))
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
    let observed: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    let success = &observed["success"];
    assert_eq!(success["steps"][0]["verdict"], "match");
    assert_eq!(success["steps"][0]["stage"], "bison-parser");
    let krust = success["calls"][1].as_array().unwrap();
    assert!(krust.iter().any(|value| value == "--gen-parser"));
    assert!(
        krust
            .windows(2)
            .any(|pair| pair == ["--bison-stack-max-depth", "12000"])
    );
    assert!(
        krust
            .last()
            .unwrap()
            .as_str()
            .unwrap()
            .contains("/logs/kast-bison.krust-parser")
    );
    assert_eq!(success["parser"][0]["command"][1], "1.kast-bison");
    assert_eq!(success["parser"][1]["command"][1], "1.kast-bison");
    assert_eq!(success["steps"][1]["verdict"], "match");
    assert_eq!(
        success["comparison"]["env"]["K_RUST_BISON_PARSER_OUTPUT"],
        success["parser"][1]["stdout"]
    );
    assert_eq!(
        observed["missing-reference"]["steps"][0]["verdict"],
        "reference-error"
    );
    assert_eq!(
        observed["krust-failure"]["steps"][0]["verdict"],
        "krust-error"
    );
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
import tomllib
results = os.path.join(root, "results.toml")
run.write_results([result], results)
with open(results, "rb") as handle:
    recorded = tomllib.load(handle)["case"][0].get("bison_parsers_only")
print(json.dumps({"driven": driven, "verdict": result.verdict, "stage": result.stage, "recorded": recorded}))
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
    // The results say which steps ranked the case, for the ratchet to rank it alike.
    assert_eq!(observed["recorded"], true);
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

#[test]
fn conformance_driver_gives_a_search_recipe_exactly_one_search_flag() {
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

def probe(arguments, search_file):
    root = tempfile.mkdtemp()
    case = run.Case("search-flag")
    case.dir = root
    case.log = os.path.join(root, "logs")
    case.ref_kompiled = os.path.join(root, "reference-kompiled")
    case.def_file = "test.k"
    case.main_module = "TEST"
    case.syntax_module = "TEST-SYNTAX"
    case.pgm_sort = "KItem"
    before = len(captured)
    recipe = run.split_recipe("/kbin/krun " + arguments)
    step = run.do_krun(case, recipe, search_file=search_file)
    return {
        "args": captured[-1] if len(captured) != before else None,
        "verdict": step["verdict"],
        "stage": step.get("stage"),
        "reason": step.get("reason"),
    }

print(json.dumps({
    # KSEARCH is `krun --search-all` (k/k-distribution/include/kframework/ktest-common.mak:23),
    # so a .search recipe already carries the mode the driver would otherwise supply.
    "ksearch": probe("--search-all pgm.search", True),
    "bare": probe("pgm.search", True),
    "legacy": probe("--search pgm.search", True),
    "one_step": probe("--search-one-step pgm.search", True),
    "repeated": probe("--search-all --search-all pgm.search", True),
    "conflicting": probe("--search-all --search-one-step pgm.search", True),
    "unknown": probe("--not-a-krun-flag pgm.search", True),
    "plain": probe("pgm", False),
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
    let arguments = |name: &str| -> Vec<String> {
        probes[name]["args"]
            .as_array()
            .unwrap_or_else(|| panic!("{name} did not invoke krust: {probes}"))
            .iter()
            .map(|argument| argument.as_str().unwrap().to_string())
            .collect()
    };
    let plain = arguments("plain");
    assert!(
        !plain
            .iter()
            .any(|argument| argument.starts_with("--search")),
        "a non-search recipe must not select a search mode: {plain:?}"
    );
    for (name, mode) in [
        ("ksearch", "--search-all"),
        ("bare", "--search-all"),
        ("legacy", "--search-final"),
        ("one_step", "--search-one-step"),
        ("repeated", "--search-all"),
    ] {
        let args = arguments(name);
        let selected: Vec<&String> = args
            .iter()
            .filter(|argument| argument.starts_with("--search"))
            .collect();
        assert_eq!(
            selected,
            [&mode.to_string()],
            "{name}: a search step must carry exactly one search mode: {args:?}"
        );
        assert_eq!(
            probes[name]["stage"].as_str(),
            Some("search"),
            "{name}: {probes}"
        );
    }
    for invalid in ["conflicting", "unknown"] {
        assert!(probes[invalid]["args"].is_null(), "{invalid}: {probes}");
        assert_eq!(
            probes[invalid]["verdict"].as_str(),
            Some("krust-unsupported"),
            "{invalid}: {probes}"
        );
    }
    assert!(
        probes["unknown"]["reason"]
            .as_str()
            .unwrap()
            .contains("--not-a-krun-flag"),
        "an unrecognized krun flag must stay unsupported rather than be dropped: {probes}"
    );
}

#[test]
fn conformance_driver_compares_completion_only_stdout_without_hiding_bottom_or_residuals() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import json, os, sys, tempfile
sys.path.insert(0, sys.argv[1])
import run

captures = []
mode = None

def fake_run(case, kind, prog, stdin_path, extra, sort, syntax_module, step):
    captures.append({"extra": extra, "stdin": stdin_path})
    if mode == "bottom":
        return ["krust"], 0, "\\bottom{SortGeneratedTopCell{}}()", "", 0.1, False
    if mode == "explicit_on_halt":
        return ["krust"], 1, "", "in-process backend halted at depth 3: unsupported hook 'IO.write'", 0.1, False
    return ["krust"], 0, "cfg{}()", "", 0.1, False

def fake_run_bytes(case, prog, stdin_path, extra, sort, syntax_module, step):
    captures.append({"extra": extra, "stdin": stdin_path})
    if mode == "explicit_on_halt":
        return ["krust"], 1, b"", "in-process backend halted at depth 3: unsupported hook 'IO.write'", 0.1, False
    return ["krust"], 0, b"hello\n", "", 0.1, False

def fake_comparator(name, environment, cwd, timeout=120):
    assert name == "conformance_stdout_stream_buffers", name
    reports = {
        "match": {"leaves": [
            {"constraints": [], "buffers": [list(b"hello\n")]},
        ]},
        "residual": {"leaves": [
            {"constraints": [], "buffers": [list(b"hello\n")]},
            {"constraints": ["\\not{B{}}(p{}())"], "buffers": [list(b"partial")]},
        ]},
        "bytes_differ": {"leaves": [{"constraints": [], "buffers": [list(b"goodbye\n")]}]},
        "two_terminal": {"leaves": [
            {"constraints": [], "buffers": [list(b"hello\n")]},
            {"constraints": [], "buffers": [list(b"hello\n")]},
        ]},
        "no_buffer": {"leaves": [{"constraints": [], "buffers": []}]},
    }
    return 0, "c9-stdout-report = " + json.dumps(reports[mode]), "", False

run.run_krust_program = fake_run
run.run_krust_program_bytes = fake_run_bytes
run.run_test_binary_result = fake_comparator

def probe(selected, expected, explicit_io=False, stdin=False):
    global mode
    mode = selected
    root = tempfile.mkdtemp()
    case = run.Case("completion-stdout")
    case.dir = root
    case.log = os.path.join(root, "logs")
    case.ref_kompiled = os.path.join(root, "reference-kompiled")
    case.def_file = "test.k"
    case.main_module = "TEST"
    case.syntax_module = "TEST"
    case.pgm_sort = "KItem"
    with open(os.path.join(root, "program.out"), "w") as output:
        output.write(expected)
    if stdin:
        with open(os.path.join(root, "program.in"), "w") as input_file:
            input_file.write("input\n")
    command = "/kbin/krun program --output none"
    if explicit_io:
        command += " --io on"
    command += " | diff - program.out"
    recipe = run.split_recipe(command)
    if stdin:
        recipe["stdin"] = "program.in"
    before = len(captures)
    step = run.do_krun(case, recipe)
    return {
        "step": step,
        "capture": captures[-1] if len(captures) != before else None,
    }

print(json.dumps({
    "match": probe("match", "hello\n", stdin=True),
    "residual": probe("residual", "hello\n"),
    "bytes_differ": probe("bytes_differ", "hello\n"),
    "two_terminal": probe("two_terminal", "hello\n"),
    "no_buffer": probe("no_buffer", "hello\n"),
    "bottom_nonempty": probe("bottom", "hello\n"),
    "bottom_empty": probe("bottom", ""),
    "empty_completion": probe("empty_completion", ""),
    "explicit_on_match": probe("explicit_on_match", "hello\n", explicit_io=True),
    "explicit_on_halt": probe("explicit_on_halt", "hello\n", explicit_io=True),
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
    let step = |name: &str| &probes[name]["step"];
    assert_eq!(step("match")["verdict"], "match", "{probes}");
    assert!(
        step("match")["comparison"]
            .as_str()
            .unwrap()
            .starts_with("C9:"),
        "{probes}"
    );
    assert_eq!(step("match")["stdout_leaf_count"], 1, "{probes}");
    assert_eq!(step("match")["stdout_terminal_leaf_count"], 1, "{probes}");
    assert_eq!(step("match")["stdout_buffer_bytes"], 6, "{probes}");
    assert!(
        probes["match"]["capture"]["extra"]
            .as_array()
            .unwrap()
            .windows(2)
            .any(|pair| pair == ["--io", "off"]),
        "C9 must select the definition's buffered IO mode: {probes}"
    );
    assert!(
        probes["match"]["capture"]["stdin"]
            .as_str()
            .unwrap()
            .ends_with("program.in"),
        "C9 must retain recipe stdin: {probes}"
    );

    for name in ["residual", "bytes_differ", "two_terminal", "no_buffer"] {
        assert_eq!(step(name)["verdict"], "mismatch", "{name}: {probes}");
        assert!(
            step(name)["comparison"]
                .as_str()
                .unwrap()
                .starts_with("C9:"),
            "{name}: {probes}"
        );
    }
    assert!(
        step("residual")["divergence"]
            .as_str()
            .unwrap()
            .contains("constraints"),
        "{probes}"
    );
    assert!(
        step("bytes_differ")["divergence"]
            .as_str()
            .unwrap()
            .contains("offset"),
        "{probes}"
    );
    assert!(
        step("two_terminal")["divergence"]
            .as_str()
            .unwrap()
            .contains("buffers"),
        "{probes}"
    );

    for name in ["bottom_nonempty", "bottom_empty"] {
        assert_eq!(step(name)["verdict"], "krust-error", "{name}: {probes}");
        assert_eq!(step(name)["stage"], "krun", "{name}: {probes}");
        assert!(
            step(name)["reason"].as_str().unwrap().contains("bottom"),
            "{name}: {probes}"
        );
    }
    assert_eq!(step("empty_completion")["verdict"], "match", "{probes}");
    assert!(
        step("empty_completion")["comparison"]
            .as_str()
            .unwrap()
            .starts_with("completion only"),
        "{probes}"
    );
    assert_eq!(step("explicit_on_match")["verdict"], "match", "{probes}");
    assert!(
        step("explicit_on_match")["comparison"]
            .as_str()
            .unwrap()
            .contains("committed console stdout"),
        "{probes}"
    );
    assert_eq!(
        step("explicit_on_halt")["verdict"],
        "krust-error",
        "{probes}"
    );
    assert_eq!(step("explicit_on_halt")["stage"], "krun", "{probes}");
    assert_eq!(
        probes["explicit_on_halt"]["capture"]["extra"],
        serde_json::json!(["--io", "on", "--output", "none"]),
        "an explicit live IO recipe must retain live mode and suppress KORE rendering: {probes}"
    );
}

#[test]
fn conformance_driver_retries_only_a_proven_c9_stdin_precondition_in_live_mode() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import json, os, sys, tempfile
sys.path.insert(0, sys.argv[1])
import run

calls = []
diagnostic = ('warning: execution ended with no successor at depth 8: '
              'rule STDIN-STREAM.stdinParseInt applied with an undefined result; '
              'refuted obligation \\ceil{SortInt{}, SortGeneratedTopCell{}}(String2Int(""))')

def fake_run(case, kind, prog, stdin_path, extra, sort, syntax_module, step):
    calls.append(extra)
    return ["krust", "buffered"], 0, "\\bottom{SortGeneratedTopCell{}}()", diagnostic, 0.1, False

def fake_live(case, prog, stdin_path, extra, sort, syntax_module, step):
    calls.append(extra)
    return ["krust", "live"], 0, b"expected\n", "", 0.1, False

run.run_krust_program = fake_run
run.run_krust_program_bytes = fake_live

root = tempfile.mkdtemp()
case = run.Case("c9-live-fallback")
case.dir = root
case.log = os.path.join(root, "logs")
case.ref_kompiled = os.path.join(root, "reference-kompiled")
case.def_file = "test.k"
case.main_module = "TEST"
case.syntax_module = "TEST"
case.pgm_sort = "KItem"
os.makedirs(os.path.join(root, "krust-kompiled"))
with open(os.path.join(root, "krust-kompiled", "definition.kore"), "w") as definition:
    definition.write('''
      Lbl'Hash'parseInput{}(\\dv{SortString{}}("Int"), \\dv{SortString{}}("|"))
    ''')
with open(os.path.join(root, "program.in"), "w") as input_file:
    input_file.write("2||4")
with open(os.path.join(root, "program.out"), "wb") as output:
    output.write(b"expected\n")
recipe = run.split_recipe("/kbin/krun program --output none | diff - program.out")
recipe["stdin"] = "program.in"
step = run.do_krun(case, recipe)
print(json.dumps({"step": step, "calls": calls}))
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
    let probe: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(probe["step"]["verdict"], "match", "{probe}");
    assert!(
        probe["step"]["c9_stdin_precondition"]
            .as_str()
            .unwrap()
            .contains("STDIN-STREAM.stdinParseInt"),
        "{probe}"
    );
    assert_eq!(probe["calls"][0], serde_json::json!(["--io", "off"]));
    assert_eq!(
        probe["calls"][1],
        serde_json::json!(["--io", "on", "--output", "none"])
    );
}

#[test]
fn conformance_driver_caps_each_program_by_the_step_budget_inside_the_case_budget() {
    // Without a per-program ceiling, one divergent program consumes the whole case
    // budget and every program behind it is skipped. `step_budget` caps one execution's own CPU
    // time, so the verdict does not depend on what else the machine runs, and `step_wall_budget`
    // caps the wall time of a program that stops accruing CPU time. Either kill is reported as
    // that program's cost, the next program still runs, and the case budget still bounds both.
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import json, os, signal, sys, tempfile
sys.path.insert(0, sys.argv[1])
import run

calls = []
outcome = {"kill": "cpu"}

def fake_sh(cmd, cwd, timeout, stdin_path=None, env=None, shell=False):
    calls.append({"cmd": cmd, "timeout": round(timeout, 1)})
    # The fake program diverges or stalls: it only ever ends by being killed, by the CPU limit
    # when one applies and the probe says so, else by the wall-clock timeout.
    if outcome["kill"] == "cpu" and cmd[0] == "bash":
        return -signal.SIGXCPU, "", "", 1.0, False
    return -9, "", "", timeout, True

run.sh = fake_sh

def probe(step_budget, kill, remaining=None, wall_budget=None):
    outcome["kill"] = kill
    root = tempfile.mkdtemp()
    case = run.Case("step-budget")
    case.dir = root
    case.log = os.path.join(root, "logs")
    case.ref_kompiled = os.path.join(root, "reference-kompiled")
    case.def_file = "test.k"
    case.main_module = "TEST"
    case.syntax_module = "TEST"
    case.pgm_sort = "KItem"
    case.budget = 100.0
    case.deadline = case.t0 + case.budget
    case.step_budget = step_budget
    case.step_wall_budget = wall_budget
    if remaining is not None:
        case.deadline = run.time.monotonic() + remaining
    with open(os.path.join(root, "program.out"), "w") as output:
        output.write("hello\n")
    recipe = run.split_recipe("/kbin/krun program --output none | diff - program.out")
    first = run.do_krun(case, recipe)
    second = run.do_krun(case, recipe)
    return {"first": first, "second": second, "out_of_budget": case.out_of_budget()}

print(json.dumps({
    "capped": probe(5.0, "cpu", wall_budget=40.0),
    "stalled": probe(5.0, "wall", wall_budget=40.0),
    "uncapped": probe(None, "wall"),
    "case_budget_smaller": probe(50.0, "wall", remaining=20.0, wall_budget=60.0),
    "calls": calls,
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
    let capped = &probes["capped"];
    assert_eq!(capped["first"]["verdict"], "krust-error", "{probes}");
    assert_eq!(
        capped["first"]["reason"], "krust krun exceeded the step budget (5 CPU-s)",
        "{probes}"
    );
    assert_eq!(capped["first"]["step_budget"], 5.0, "{probes}");
    assert_eq!(capped["first"]["step_budget_exceeded"], true, "{probes}");
    assert_eq!(
        capped["second"]["reason"], "krust krun exceeded the step budget (5 CPU-s)",
        "the program after a killed one must still be measured: {probes}"
    );
    assert_eq!(
        capped["out_of_budget"], false,
        "two capped kills must not exhaust a 100 s case budget: {probes}"
    );
    let stalled = &probes["stalled"];
    assert_eq!(stalled["first"]["verdict"], "krust-error", "{probes}");
    assert_eq!(
        stalled["first"]["reason"], "krust krun exceeded the step wall budget (40 s)",
        "a program that accrues no CPU time is ended by the step wall budget: {probes}"
    );
    assert_eq!(stalled["first"]["step_wall_budget"], 40.0, "{probes}");
    assert_eq!(
        stalled["first"]["step_wall_budget_exceeded"], true,
        "{probes}"
    );
    assert!(
        stalled["first"].get("step_budget_exceeded").is_none(),
        "{probes}"
    );
    assert_eq!(
        stalled["second"]["reason"], "krust krun exceeded the step wall budget (40 s)",
        "the program after a stalled one must still be measured: {probes}"
    );
    let uncapped = &probes["uncapped"];
    assert_eq!(
        uncapped["first"]["reason"], "krust krun timed out",
        "without a step budget the kill is the case budget's: {probes}"
    );
    assert!(uncapped["first"].get("step_budget").is_none(), "{probes}");
    let smaller = &probes["case_budget_smaller"];
    assert_eq!(
        smaller["first"]["reason"], "krust krun timed out",
        "a wall-clock kill by the remaining case budget is not the step budget's: {probes}"
    );
    assert!(
        smaller["first"].get("step_budget_exceeded").is_none(),
        "{probes}"
    );
    assert!(
        smaller["first"].get("step_wall_budget_exceeded").is_none(),
        "{probes}"
    );
    let calls = probes["calls"].as_array().unwrap();
    // The step budget is the krust process's CPU limit: a SIGXCPU soft limit at the budget and a
    // SIGKILL hard limit a few seconds above it, set before krust is executed unchanged.
    let capped_command = calls[0]["cmd"].as_array().unwrap();
    let capped_command: Vec<_> = capped_command
        .iter()
        .map(|argument| argument.as_str().unwrap())
        .collect();
    assert_eq!(capped_command[0], "bash", "{probes}");
    assert!(
        capped_command[2].contains("ulimit -S -t \"$2\""),
        "{probes}"
    );
    assert_eq!(&capped_command[4..6], ["10", "5"], "{probes}");
    assert_eq!(capped_command[6], "/krust", "{probes}");
    for call in &calls[0..4] {
        assert_eq!(
            call["timeout"].as_f64().unwrap(),
            40.0,
            "a capped run's wall bound is the step wall budget inside the case budget: {probes}"
        );
    }
    assert_eq!(
        calls[4]["cmd"][0], "/krust",
        "an uncapped program runs unwrapped: {probes}"
    );
    assert!(
        calls[4]["timeout"].as_f64().unwrap() > 90.0,
        "the uncapped run gets the remaining case budget: {probes}"
    );
    assert!(
        calls[6]["timeout"].as_f64().unwrap() <= 20.0,
        "the capped run never exceeds the remaining case budget: {probes}"
    );
}

#[test]
fn conformance_driver_compares_execution_text_modulo_existential_renaming() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import json, os, sys, tempfile
sys.path.insert(0, sys.argv[1])
import run

PATTERN = "<tasks> <task> <k> T:Type </k> ...</task> </tasks>"
def eq(body): return "{\n  T:Type\n#Equals\n  " + body + "\n}\n"

def diff(expected, actual, pattern=PATTERN):
    d, compared_as_set, renamed = run.execution_text_diff(expected, actual, pattern)
    return {"match": d is None, "compared_as_set": compared_as_set, "renamed_existentials": renamed, "divergence": d}

# The pattern reaches compare_execution from do_krun; kprint is faked to return `actual` verbatim.
pretty = {}
run.kprint = lambda case, kore_path: (0, pretty["text"], "")
run.run_krust_program = lambda case, kind, prog, stdin_path, extra, sort, syntax_module, step: (
    ["krust"], 0, "\\top{SortGeneratedTopCell{}}()", "", 0.0, False)
run.confirm_oracle = lambda case, rec, step: None
def driver(expected, actual, pattern):
    root = tempfile.mkdtemp()
    case = run.Case("existential-renaming")
    case.dir = root; case.log = os.path.join(root, "logs")
    case.ref_kompiled = os.path.join(root, "reference-kompiled")
    case.def_file = "test.k"; case.main_module = "TEST"; case.syntax_module = "TEST-SYNTAX"; case.pgm_sort = "KItem"
    with open(os.path.join(root, "program.out"), "w") as f: f.write(expected)
    pretty["text"] = actual
    recipe = run.split_recipe("/kbin/krun program --search-final --pattern " + repr(pattern) + " | diff - program.out")
    assert recipe["out"] == "program.out", recipe
    step = run.do_krun(case, recipe)
    return {"verdict": step["verdict"], "comparison": step.get("comparison"),
            "renamed_existentials": step.get("renamed_existentials"), "divergence": step.get("divergence")}

xy_expected, xy_actual = "{ ?X:Int #Equals ?Y:Int }\n", "{ ?Y:Int #Equals ?X:Int }\n"
print(json.dumps({
    "composition": diff(
        eq("( ?Tx1:Type -> ?T3:Type ) -> ( ( ?T3:Type -> ?Te1:Type ) -> ( ?Tx1:Type -> ?Te1:Type ) )"),
        eq("( ?T3:Type -> ?T2:Type ) -> ( ( ?T2:Type -> ?Te1:Type ) -> ( ?T3:Type -> ?Te1:Type ) )")),
    "literal": diff(eq("int -> ?Tx1:Type"), eq("int -> ?Tx1:Type")),
    "disjunction": diff("  ?A:Type -> int\n#Or\n  ?B:Type -> bool\n", "  ?B:Type -> int\n#Or\n  ?A:Type -> bool\n"),
    "sharing": diff(eq("?A:Type -> ?A:Type"), eq("?A:Type -> ?B:Type")),
    "sort": diff(eq("?A:Type"), eq("?A:Int")),
    "pattern_variable": diff(eq("int"), eq("int").replace("T:Type", "U:Type")),
    "string_literal": diff(eq('"?A:Type"'), eq('"?B:Type"')),
    "pattern_existentials": diff(xy_expected, xy_actual, "<k> ?X:Int ?Y:Int </k>"),
    "free_existentials": diff(xy_expected, xy_actual, "<k> T:Int </k>"),
    "driver_fixed": driver(xy_expected, xy_actual, "<k> ?X:Int ?Y:Int </k>"),
    "driver_free": driver(xy_expected, xy_actual, "<k> T:Int </k>"),
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
    let probe = |name: &str| &probes[name];
    // Engine-chosen existential names match modulo renaming and are reported as renamed.
    for name in ["composition", "disjunction", "free_existentials"] {
        assert_eq!(probe(name)["match"], true, "{name}: {probes}");
        assert_eq!(
            probe(name)["renamed_existentials"],
            true,
            "{name}: {probes}"
        );
    }
    assert_eq!(probe("disjunction")["compared_as_set"], true, "{probes}");
    // Identical texts match without renaming.
    assert_eq!(probe("literal")["match"], true, "{probes}");
    assert_eq!(probe("literal")["renamed_existentials"], false, "{probes}");
    // Sharing loss, a sort change, a renamed non-existential pattern variable, a `?` inside a
    // string literal, and swapped pattern-declared `?` variables all stay mismatches.
    for name in [
        "sharing",
        "sort",
        "pattern_variable",
        "string_literal",
        "pattern_existentials",
    ] {
        assert_eq!(probe(name)["match"], false, "{name}: {probes}");
        assert_eq!(
            probe(name)["renamed_existentials"],
            false,
            "{name}: {probes}"
        );
    }
    // The mismatch diff is of the renamed texts: the true difference, not the spelling.
    let sharing = probe("sharing")["divergence"].as_str().unwrap();
    assert!(
        sharing.contains("?'KDiff0:Type -> ?'KDiff0:Type")
            && sharing.contains("?'KDiff0:Type -> ?'KDiff1:Type"),
        "{sharing}"
    );
    // do_krun threads the recipe's --pattern text into the comparison and labels it C7.
    assert_eq!(probe("driver_fixed")["verdict"], "mismatch", "{probes}");
    assert!(
        probe("driver_fixed")["renamed_existentials"].is_null(),
        "{probes}"
    );
    assert_eq!(probe("driver_free")["verdict"], "match", "{probes}");
    assert_eq!(
        probe("driver_free")["renamed_existentials"],
        true,
        "{probes}"
    );
    for name in ["driver_fixed", "driver_free"] {
        let comparison = probe(name)["comparison"].as_str().unwrap();
        assert!(
            comparison.contains("modulo C7 existential renaming"),
            "{name}: {comparison}"
        );
    }
}

#[test]
fn conformance_driver_compares_simplified_kore_when_the_execution_text_differs() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    // Every process boundary is faked: the krust krun, the reference krun re-run, kprint, the two
    // krust kore-simplify runs, the comparator test binary, and the oracle confirmation.
    let script = r#"
import json, os, sys, tempfile, time
sys.path.insert(0, sys.argv[1])
import run

EXPECTED = "<k>\n  false ~> .K\n</k>\n#And\n  { true #Equals size ( ListItem ( ?X:Int ) ?L:List ) >=Int -1 }\n"
KRUST_PRETTY = "<k>\n  false ~> .K\n</k>\n"
REFERENCE_KORE = "\\and{S{}}(cfg{}(), \\equals{B{}, S{}}(true{}(), c{}()))"
KRUST_KORE = "cfg{}()"
PLAIN = "/kbin/krun 1.test --no-exc-wrap --definition ./test-kompiled | diff - 1.test.out"

def driver(mode, recipe_text=PLAIN):
    root = tempfile.mkdtemp()
    case = run.Case("simplified-kore")
    case.dir = root; case.log = os.path.join(root, "logs")
    case.ref_kompiled = os.path.join(root, "test-kompiled")
    os.makedirs(case.ref_kompiled)
    with open(os.path.join(case.ref_kompiled, "definition.kore"), "w") as f: f.write("[]\n")
    case.def_file = "test.k"; case.main_module = "TEST"; case.syntax_module = "TEST"; case.pgm_sort = "KItem"
    with open(os.path.join(root, "1.test.out"), "w") as f: f.write(EXPECTED)
    if mode == "no_definition": os.remove(os.path.join(case.ref_kompiled, "definition.kore"))
    if mode == "no_module": case.main_module = None
    if mode == "budget_before_rerun": case.deadline = time.monotonic()
    calls = {"reference": [], "simplify": [], "comparator": [], "oracle": 0}
    def fake_sh(cmd, cwd, timeout, stdin_path=None, env=None, shell=False):
        tool = os.path.basename(cmd[0])
        if tool == "krust" and cmd[1] == "krun":
            return 0, KRUST_KORE, "", 0.1, False
        if tool == "krun":
            calls["reference"].append({"args": cmd[1:], "env": env})
            if mode == "reference_fails": return 1, "", "kore-exec: boom", 0.1, False
            if mode == "reference_timeout": return -9, "", "", 0.1, True
            if mode == "reference_empty": return 0, "", "", 0.1, False
            return 0, REFERENCE_KORE, "", 0.1, False
        if tool == "kprint":
            source = open(cmd[2]).read()
            if source == KRUST_KORE: return 0, EXPECTED if mode == "text_equal" else KRUST_PRETTY, "", 0.1, False
            assert source == REFERENCE_KORE, source
            if mode == "kprint_fails": return 1, "", "kprint: unparsable pattern", 0.1, False
            if mode == "budget_before_simplify_reference": case.deadline = time.monotonic()
            return 0, KRUST_PRETTY if mode == "stale_out" else EXPECTED, "", 0.1, False
        if tool == "krust" and cmd[1] == "kore-simplify":
            calls["simplify"].append(cmd[2:])
            source = cmd[cmd.index("--pattern") + 1]
            target = cmd[cmd.index("--output") + 1]
            if mode == "simplify_fails": return 1, "", "could not simplify KORE pattern: Smt(...)", 0.1, False
            if mode == "simplify_timeout": return -9, "", "", 0.1, True
            if mode == "simplify_no_output": return 0, "", "", 0.1, False
            if mode == "simplify_fails_krust" and source.endswith(".krust.kore"):
                return 1, "", "could not simplify KORE pattern: parse error", 0.1, False
            if mode == "budget_before_simplify_krust": case.deadline = time.monotonic()
            with open(target, "w") as f: f.write("simplified:" + open(source).read())
            return 0, "", "", 0.1, False
        raise AssertionError("unexpected command: " + " ".join(cmd))
    def fake_test(name, env, cwd, timeout=120):
        calls["comparator"].append({"name": name, "env": env,
            "sides": [open(env["K_REFERENCE_EXECUTION"]).read(), open(env["K_RUST_EXECUTION"]).read()]})
        if mode == "differ":
            return 1, "", "thread 'x' panicked at a.rs:1:1:\nunpaired disjunct: cfg{}()\nnote: run with RUST_BACKTRACE=1", False
        if mode == "comparator_timeout": return -9, "", "", True
        return 0, "ok", "", False
    run.sh = fake_sh
    run.run_test_binary_result = fake_test
    run.confirm_oracle = lambda case, rec, step: calls.__setitem__("oracle", calls["oracle"] + 1)
    step = run.do_krun(case, run.split_recipe(recipe_text))
    return {"verdict": step["verdict"], "comparison": step.get("comparison"),
            "reason": step.get("reason"),
            "simplified_kore_equal": step.get("simplified_kore_equal"), "divergence": step.get("divergence"),
            "text_divergence": step.get("text_divergence"),
            "simplified_kore_divergence": step.get("simplified_kore_divergence"),
            "reference_kore_error": step.get("reference_kore_error"),
            "reference_kore_reproduces_out": step.get("reference_kore_reproduces_out"),
            "reference_kore_rc": step.get("reference_kore_rc"), "calls": calls}

print(json.dumps({
    "equal": driver("equal"),
    "output_flag": driver("equal", "/kbin/krun 1.test --output pretty --definition ./test-kompiled | diff - 1.test.out"),
    "text_equal": driver("text_equal"),
    "differ": driver("differ"),
    "reference_fails": driver("reference_fails"),
    "simplify_fails": driver("simplify_fails"),
    "stale_out": driver("stale_out"),
    "expansion": driver("equal", "/kbin/krun $PGM --definition ./test-kompiled | diff - 1.test.out"),
    "no_definition": driver("no_definition"),
    "no_module": driver("no_module"),
    "budget_before_rerun": driver("budget_before_rerun"),
    "reference_timeout": driver("reference_timeout"),
    "reference_empty": driver("reference_empty"),
    "kprint_fails": driver("kprint_fails"),
    "budget_before_simplify_reference": driver("budget_before_simplify_reference"),
    "budget_before_simplify_krust": driver("budget_before_simplify_krust"),
    "simplify_timeout": driver("simplify_timeout"),
    "simplify_no_output": driver("simplify_no_output"),
    "simplify_fails_krust": driver("simplify_fails_krust"),
    "comparator_timeout": driver("comparator_timeout"),
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
    let probe = |name: &str| &probes[name];
    let calls = |name: &str| &probes[name]["calls"];
    // Equal after simplification: a match under the C8 label, never plain match text, with the
    // text difference retained, both sides simplified against the reference definition and main
    // module, and the comparator run without K_DIFFERENTIAL_DEFINITION.
    for name in ["equal", "output_flag"] {
        assert_eq!(probe(name)["verdict"], "match", "{name}: {probes}");
        let comparison = probe(name)["comparison"].as_str().unwrap();
        for needle in [
            "text differs",
            "C8",
            "krust kore-simplify",
            "--output kore",
            "without K_DIFFERENTIAL_DEFINITION",
        ] {
            assert!(comparison.contains(needle), "{name}: {comparison}");
        }
        assert_eq!(
            probe(name)["simplified_kore_equal"],
            true,
            "{name}: {probes}"
        );
        assert!(probe(name)["divergence"].is_null(), "{name}: {probes}");
        assert!(
            probe(name)["text_divergence"]
                .as_str()
                .unwrap()
                .contains("size ( ListItem"),
            "{name}: {probes}"
        );
        assert_eq!(
            probe(name)["reference_kore_reproduces_out"],
            true,
            "{name}: {probes}"
        );
        assert_eq!(calls(name)["oracle"], 0, "{name}: {probes}");
        let comparator = calls(name)["comparator"].as_array().unwrap();
        assert_eq!(comparator.len(), 1, "{name}: {probes}");
        assert_eq!(
            comparator[0]["name"],
            "executed_kore_matches_the_reference_backend"
        );
        assert!(
            comparator[0]["env"]
                .get("K_DIFFERENTIAL_DEFINITION")
                .is_none(),
            "{name}: {probes}"
        );
        assert_eq!(comparator[0]["env"]["K_DIFFERENTIAL_MODULE"], "TEST");
        assert_eq!(
            comparator[0]["sides"],
            serde_json::json!([
                "simplified:\\and{S{}}(cfg{}(), \\equals{B{}, S{}}(true{}(), c{}()))",
                "simplified:cfg{}()"
            ]),
            "{name}: {probes}"
        );
        let simplify = calls(name)["simplify"].as_array().unwrap();
        assert_eq!(simplify.len(), 2, "{name}: {probes}");
        for arguments in simplify {
            let arguments = arguments.as_array().unwrap();
            assert!(
                arguments[0]
                    .as_str()
                    .unwrap()
                    .ends_with("test-kompiled/definition.kore"),
                "{name}: {probes}"
            );
            assert_eq!(arguments[1], "--module");
            assert_eq!(arguments[2], "TEST");
        }
    }
    // The reference re-run replaces the recipe's output format by --output kore.
    assert_eq!(
        calls("equal")["reference"][0]["args"],
        serde_json::json!([
            "1.test",
            "--no-exc-wrap",
            "--definition",
            "./test-kompiled",
            "--output",
            "kore"
        ]),
        "{probes}"
    );
    assert_eq!(
        calls("output_flag")["reference"][0]["args"],
        serde_json::json!([
            "1.test",
            "--definition",
            "./test-kompiled",
            "--output",
            "kore"
        ]),
        "{probes}"
    );
    assert_eq!(calls("equal")["reference"][0]["env"]["GHCRTS"], "-N1");
    // Matching text never reaches C8.
    assert_eq!(probe("text_equal")["verdict"], "match", "{probes}");
    assert!(
        probe("text_equal")["comparison"]
            .as_str()
            .unwrap()
            .contains("modulo C7 existential renaming"),
        "{probes}"
    );
    assert_eq!(
        calls("text_equal")["reference"].as_array().unwrap().len(),
        0
    );
    assert_eq!(calls("text_equal")["simplify"].as_array().unwrap().len(), 0);
    // An unavailable simplification or comparison remains a mismatch that keeps the C7 label and
    // text diff. These are negative controls for the distinct reference-process failure below.
    for (name, reason) in [
        (
            "differ",
            "simplified KORE differ: unpaired disjunct: cfg{}()",
        ),
        (
            "simplify_fails",
            "not compared: krust kore-simplify failed on the reference KORE: exit 1",
        ),
        ("stale_out", "does not reproduce the checked-in .out"),
        ("expansion", "unsupported shell expansion or redirection"),
        (
            "no_definition",
            "not compared: no reference kompiled definition or main module",
        ),
        (
            "no_module",
            "not compared: no reference kompiled definition or main module",
        ),
        (
            "budget_before_rerun",
            "not compared: no remaining budget for the reference --output kore re-run",
        ),
        (
            "kprint_fails",
            "not compared: kprint failed on the reference --output kore result: kprint: unparsable pattern",
        ),
        (
            "budget_before_simplify_reference",
            "not compared: no remaining budget to simplify the reference KORE",
        ),
        (
            "budget_before_simplify_krust",
            "not compared: no remaining budget to simplify the krust KORE",
        ),
        (
            "simplify_timeout",
            "not compared: krust kore-simplify failed on the reference KORE: timed out",
        ),
        (
            "simplify_no_output",
            "not compared: krust kore-simplify failed on the reference KORE: exit 0",
        ),
        (
            "simplify_fails_krust",
            "not compared: krust kore-simplify failed on the krust KORE: exit 1",
        ),
        (
            "comparator_timeout",
            "simplified KORE not compared: the comparator timed out",
        ),
    ] {
        assert_eq!(probe(name)["verdict"], "mismatch", "{name}: {probes}");
        let comparison = probe(name)["comparison"].as_str().unwrap();
        assert!(
            comparison.contains("modulo C7 existential renaming") && !comparison.contains("C8"),
            "{name}: {comparison}"
        );
        assert!(
            probe(name)["simplified_kore_equal"].is_null(),
            "{name}: {probes}"
        );
        assert!(
            probe(name)["divergence"]
                .as_str()
                .unwrap()
                .contains("size ( ListItem"),
            "{name}: {probes}"
        );
        assert!(
            probe(name)["simplified_kore_divergence"]
                .as_str()
                .unwrap()
                .contains(reason),
            "{name}: {probes}"
        );
        assert_eq!(calls(name)["oracle"], 1, "{name}: {probes}");
    }
    for (name, outcome, error) in [
        ("reference_fails", "exit 1", "kore-exec: boom"),
        ("reference_timeout", "timed out", ""),
        ("reference_empty", "exit 0, empty stdout", ""),
    ] {
        assert_eq!(
            probe(name)["verdict"],
            "reference-error",
            "{name}: {probes}"
        );
        assert!(
            probe(name)["reason"].as_str().unwrap().contains(outcome),
            "{name}: {probes}"
        );
        assert!(
            probe(name)["reference_kore_error"]
                .as_str()
                .unwrap()
                .contains(error),
            "{name}: {probes}"
        );
        assert!(
            probe(name)["divergence"]
                .as_str()
                .unwrap()
                .contains("size ( ListItem"),
            "{name}: {probes}"
        );
        assert!(
            probe(name)["simplified_kore_divergence"]
                .as_str()
                .unwrap()
                .contains("reference --output kore re-run"),
            "{name}: {probes}"
        );
        assert_eq!(calls(name)["oracle"], 1, "{name}: {probes}");
        assert_eq!(calls(name)["simplify"].as_array().unwrap().len(), 0);
        assert_eq!(calls(name)["comparator"].as_array().unwrap().len(), 0);
    }
    assert_eq!(calls("differ")["comparator"].as_array().unwrap().len(), 1);
    assert_eq!(
        calls("reference_fails")["simplify"]
            .as_array()
            .unwrap()
            .len(),
        0
    );
    assert_eq!(
        calls("reference_fails")["comparator"]
            .as_array()
            .unwrap()
            .len(),
        0
    );
    assert_eq!(
        calls("simplify_fails")["comparator"]
            .as_array()
            .unwrap()
            .len(),
        0
    );
    assert_eq!(
        probe("stale_out")["reference_kore_reproduces_out"],
        false,
        "{probes}"
    );
    assert_eq!(calls("stale_out")["simplify"].as_array().unwrap().len(), 0);
    assert_eq!(calls("expansion")["reference"].as_array().unwrap().len(), 0);
    // Per-mode call counts: how far C8 got before it gave up.
    let count = |name: &str, stage: &str| calls(name)[stage].as_array().unwrap().len();
    for name in ["no_definition", "no_module", "budget_before_rerun"] {
        assert_eq!(count(name, "reference"), 0, "{name}: {probes}");
        assert_eq!(count(name, "simplify"), 0, "{name}: {probes}");
    }
    for name in [
        "reference_timeout",
        "reference_empty",
        "kprint_fails",
        "budget_before_simplify_reference",
    ] {
        assert_eq!(count(name, "reference"), 1, "{name}: {probes}");
        assert_eq!(count(name, "simplify"), 0, "{name}: {probes}");
    }
    assert_eq!(
        probe("reference_timeout")["reference_kore_rc"],
        -9,
        "{probes}"
    );
    assert_eq!(probe("reference_empty")["reference_kore_rc"], 0, "{probes}");
    assert!(
        probe("kprint_fails")["reference_kore_reproduces_out"].is_null(),
        "{probes}"
    );
    assert_eq!(
        probe("budget_before_simplify_reference")["reference_kore_reproduces_out"],
        true,
        "{probes}"
    );
    for name in [
        "budget_before_simplify_krust",
        "simplify_timeout",
        "simplify_no_output",
    ] {
        assert_eq!(count(name, "simplify"), 1, "{name}: {probes}");
    }
    assert_eq!(count("simplify_fails_krust", "simplify"), 2, "{probes}");
    assert!(
        calls("simplify_fails_krust")["simplify"][1][4]
            .as_str()
            .unwrap()
            .ends_with("1.test.krust.kore"),
        "{probes}"
    );
    assert_eq!(count("comparator_timeout", "simplify"), 2, "{probes}");
    assert_eq!(count("comparator_timeout", "comparator"), 1, "{probes}");
    for name in [
        "no_definition",
        "no_module",
        "budget_before_rerun",
        "reference_timeout",
        "reference_empty",
        "kprint_fails",
        "budget_before_simplify_reference",
        "budget_before_simplify_krust",
        "simplify_timeout",
        "simplify_no_output",
        "simplify_fails_krust",
    ] {
        assert_eq!(count(name, "comparator"), 0, "{name}: {probes}");
    }
}

#[test]
fn conformance_driver_refreshes_invalid_work_trees_and_cleans_nested_outputs() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import json, os, pathlib, sys, tempfile
sys.path.insert(0, sys.argv[1])
import run

root = pathlib.Path(tempfile.mkdtemp())
source = root / "source" / "k-distribution"
(source / "include/kframework").mkdir(parents=True)
(source / "include/kframework/ktest.mak").write_text("fixture\n")
(source / "tests/regression-new/example").mkdir(parents=True)
(source / "tests/regression-new/example/Makefile").write_text("include ktest.mak\n")
work = root / "work" / "k-distribution"
cases = [("example", "ktest")]

first = run.ensure_work_tree(work, source, cases)
sentinel = work / "valid-tree-is-reused"
sentinel.write_text("keep")
second = run.ensure_work_tree(work, source, cases)
valid_reused = sentinel.exists()

(work / "tests/regression-new/example/Makefile").unlink()
third = run.ensure_work_tree(work, source, cases)
missing_restored = (work / "tests/regression-new/example/Makefile").is_file()
invalid_replaced = not sentinel.exists()
stale_sentinel = work / "stale-tree-is-replaced"
stale_sentinel.write_text("remove")
marker = work / run.WORK_TREE_MARKER
marker_value = json.loads(marker.read_text())
marker_value["revision"] = "stale-revision"
marker.write_text(json.dumps(marker_value))
fourth = run.ensure_work_tree(work, source, cases)
stale_replaced = not stale_sentinel.exists()

case_dir = work / "tests/regression-new/example"
(case_dir / "top-kompiled").mkdir()
(case_dir / "concrete/imp-kompiled").mkdir(parents=True)
(case_dir / "concrete/keep").mkdir()
run.WORK_TREE = str(work)
run.LOGS = str(root / "logs")
observed = {}
def fake_vars(case):
    observed["nested_present_at_make"] = (case_dir / "concrete/imp-kompiled").exists()
    observed["control_present_at_make"] = (case_dir / "concrete/keep").exists()
    return {}
run.make_vars = fake_vars
run.make_recipes = lambda case: (2, [], "fixture make failure")
measured = run.run_case("example", "ktest")

print(json.dumps({
    "first": first,
    "second": second,
    "valid_reused": valid_reused,
    "third": third,
    "missing_restored": missing_restored,
    "invalid_replaced": invalid_replaced,
    "fourth": fourth,
    "stale_replaced": stale_replaced,
    "nested_present_at_make": observed["nested_present_at_make"],
    "control_present_at_make": observed["control_present_at_make"],
    "top_removed": not (case_dir / "top-kompiled").exists(),
    "verdict": measured.verdict,
    "reason": measured.reason,
}))
"#;
    let output = Command::new("python3")
        .env("K_KOMPILE", "/kbin/kompile")
        .args(["-c", script])
        .arg(workspace.join("scripts/conformance"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let probe: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert!(
        probe["first"].as_str().unwrap().contains("missing"),
        "{probe}"
    );
    assert!(probe["second"].is_null(), "{probe}");
    assert_eq!(probe["valid_reused"], true, "{probe}");
    assert!(
        probe["third"]
            .as_str()
            .unwrap()
            .contains("required files are missing"),
        "{probe}"
    );
    assert_eq!(probe["missing_restored"], true, "{probe}");
    assert_eq!(probe["invalid_replaced"], true, "{probe}");
    assert!(
        probe["fourth"].as_str().unwrap().contains("stale"),
        "{probe}"
    );
    assert_eq!(probe["stale_replaced"], true, "{probe}");
    assert_eq!(probe["nested_present_at_make"], false, "{probe}");
    assert_eq!(probe["top_removed"], true, "{probe}");
    assert_eq!(probe["control_present_at_make"], true, "{probe}");
    assert_eq!(probe["verdict"], "reference-error", "{probe}");
    assert!(
        probe["reason"]
            .as_str()
            .unwrap()
            .contains("could not enumerate")
    );
}

#[test]
fn conformance_driver_distinguishes_reference_crashes_from_stale_oracles() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import json, os, sys, tempfile
sys.path.insert(0, sys.argv[1])
import run
run.MEMORY_GUARD = "rlimit-as"

def probe(mode, incoming="mismatch", pattern=False, filtered=False):
    root = tempfile.mkdtemp()
    case = run.Case("oracle")
    case.dir = root
    with open(os.path.join(root, "program.out"), "w") as output:
        output.write("expected\n")
    pattern_arg = " --pattern '<k> V:K </k>'" if pattern else ""
    filter_arg = " | sed 's/value/value/'" if filtered else ""
    recipe = run.split_recipe("/kbin/krun program --definition ./test-kompiled" + pattern_arg + filter_arg + " | diff - program.out")
    calls = []
    def fake_sh(cmd, cwd, timeout, stdin_path=None, env=None, shell=False):
        calls.append({"cmd": cmd, "env": env})
        if mode == "crash":
            return 134, "", "mmap(): Cannot allocate memory\nBackend crashed during rewriting with exit code 134", 0.1, False
        if mode == "unavailable":
            return 127, "", "/kbin/krun: No such file or directory", 0.1, False
        if mode == "timeout":
            return -9, "", "", 60.0, True
        if mode == "stale":
            return 0, "different\n", "", 0.1, False
        if mode == "pipeline_refutation":
            return 1, "1c1\n< different\n---\n> expected\n", "", 0.1, False
        return 0, "expected\n", "", 0.1, False
    run.sh = fake_sh
    step = {
        "verdict": incoming,
        "reason": "C8 reference re-run failed" if incoming == "reference-error" else "text mismatch",
        "divergence": "krust produced different output",
    }
    run.confirm_oracle(case, recipe, step)
    step["call"] = calls[0]
    return step

def reference_environments():
    root = tempfile.mkdtemp()
    case = run.Case("environments")
    case.dir = root
    case.log = os.path.join(root, "logs")
    with open(os.path.join(root, "test.k"), "w") as source:
        source.write("module TEST endmodule\n")
    captured = {"kompile": None, "kore_parser": []}
    def fake_sh(cmd, cwd, timeout, stdin_path=None, env=None, shell=False):
        if cmd[:2] == ["bash", "-c"]:
            captured["kompile"] = env
            definition = os.path.join(root, "test-kompiled")
            os.makedirs(definition)
            for name, text in [
                ("mainModule.txt", "TEST\n"),
                ("mainSyntaxModule.txt", "TEST\n"),
                ("configVars.sh", ""),
                ("definition.kore", "[]\n"),
            ]:
                with open(os.path.join(definition, name), "w") as output:
                    output.write(text)
            return 0, "", "", 0.1, False
        if cmd[0] == "/krust":
            definition = os.path.join(root, "krust-kompiled")
            os.makedirs(definition)
            with open(os.path.join(definition, "definition.kore"), "w") as output:
                output.write("[]\n")
            return 0, "", "", 0.1, False
        if cmd[0] == run.KORE_PARSER:
            captured["kore_parser"].append(env)
            return 0, "", "", 0.1, False
        raise AssertionError(cmd)
    run.sh = fake_sh
    run.run_test_binary = lambda name, env, cwd: (0, "", "")
    run.KRUST = "/krust"
    run.KORE_PARSER = "/kbin/kore-parser"
    recipe = run.split_recipe(
        "/kbin/kompile --backend haskell test.k --output-definition ./test-kompiled"
    )
    run.do_kompile(case, recipe, False)
    return captured

print(json.dumps({
    "crash": probe("crash"),
    "crash_after_reference_error": probe("crash", "reference-error"),
    "unavailable": probe("unavailable"),
    "timeout": probe("timeout"),
    "stale": probe("stale"),
    "pipeline_refutation": probe("pipeline_refutation", filtered=True),
    "live_mismatch": probe("live"),
    "live_reference_error": probe("live", "reference-error"),
    "pattern": probe("live", pattern=True),
    "environments": reference_environments(),
}))
"#;
    let output = Command::new("python3")
        .env("K_KOMPILE", "/kbin/kompile")
        .env_remove("GHCRTS")
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
    let crash = &probes["crash"];
    assert_eq!(crash["verdict"], "reference-error", "{probes}");
    assert_eq!(
        crash["oracle_confirmed"], "not-run (reference crash)",
        "{probes}"
    );
    let crash_reason = crash["reason"].as_str().unwrap();
    for part in [
        "reference recipe failed to run",
        "exit 134",
        "reference crash",
        "mmap(): Cannot allocate memory",
        "under the rlimit-as memory guard",
    ] {
        assert!(crash_reason.contains(part), "{crash_reason}");
    }
    assert!(!crash_reason.contains("stale"), "{crash_reason}");
    assert!(
        crash["oracle_output"]
            .as_str()
            .unwrap()
            .contains("Backend crashed"),
        "{probes}"
    );
    assert_eq!(crash["call"]["env"]["GHCRTS"], "-N1", "{probes}");
    assert_eq!(
        crash["divergence"], "krust produced different output",
        "{probes}"
    );
    assert_eq!(
        probes["crash_after_reference_error"]["reason"], "C8 reference re-run failed",
        "{probes}"
    );
    assert_eq!(
        probes["crash_after_reference_error"]["oracle_confirmed"], "not-run (reference crash)",
        "{probes}"
    );
    for key in ["unavailable", "timeout"] {
        assert_eq!(probes[key]["verdict"], "reference-error", "{probes}");
        assert_eq!(
            probes[key]["oracle_confirmed"], "not-run (reference crash)",
            "{probes}"
        );
    }
    assert_eq!(probes["pattern"]["call"]["env"]["GHCRTS"], "", "{probes}");
    assert_eq!(probes["environments"]["kompile"]["GHCRTS"], "-N1");
    assert_eq!(
        probes["environments"]["kore_parser"],
        serde_json::json!([{ "GHCRTS": "" }, { "GHCRTS": "" }]),
        "{probes}"
    );

    let stale = &probes["stale"];
    assert_eq!(stale["verdict"], "reference-error", "{probes}");
    assert_eq!(stale["oracle_confirmed"], false, "{probes}");
    assert!(stale["reason"].as_str().unwrap().contains("stale oracle"));
    assert_eq!(stale["oracle_stale"], true, "{probes}");
    assert!(
        stale["oracle_output"]
            .as_str()
            .unwrap()
            .contains("different")
    );
    assert_eq!(
        probes["pipeline_refutation"]["oracle_confirmed"], false,
        "{probes}"
    );
    assert_eq!(
        probes["pipeline_refutation"]["oracle_stale"], true,
        "{probes}"
    );

    assert_eq!(probes["live_mismatch"]["oracle_confirmed"], true);
    assert_eq!(probes["live_mismatch"]["verdict"], "mismatch");
    assert_eq!(probes["live_reference_error"]["oracle_confirmed"], true);
    assert_eq!(probes["live_reference_error"]["verdict"], "reference-error");
    assert_eq!(
        probes["live_reference_error"]["reason"],
        "C8 reference re-run failed"
    );
}

#[test]
fn conformance_driver_ranks_a_verifier_rejection_after_every_step_and_never_excludes_it() {
    // A krust `kore-parser --verify` rejection is its own `kore-verify` step, recorded after the
    // program steps, and the definition.kore comparison still runs. The verifier reports one
    // rejected sentence at a time, so an exclusion of one diagnostic would hide every later one:
    // the expectations refuse a step exclusion of a `kore-verify` step, and the rejection ranks
    // the case.
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import json, os, sys, tempfile
sys.path.insert(0, sys.argv[1])
import run, ratchet

ANYWHERE = "Found invalid subterm in argument of function equation:"

def probe(diagnostic, comparison_rc, program_verdict):
    root = tempfile.mkdtemp()
    case = run.Case("verify")
    case.dir = root
    case.log = os.path.join(root, "logs")
    with open(os.path.join(root, "test.k"), "w") as source:
        source.write("module TEST endmodule\n")
    def fake_sh(cmd, cwd, timeout, stdin_path=None, env=None, shell=False):
        if cmd[:2] == ["bash", "-c"]:
            definition = os.path.join(root, "test-kompiled")
            os.makedirs(definition)
            for name, text in [("mainModule.txt", "TEST\n"), ("mainSyntaxModule.txt", "TEST\n"),
                               ("configVars.sh", ""), ("definition.kore", "[]\n")]:
                with open(os.path.join(definition, name), "w") as output:
                    output.write(text)
            return 0, "", "", 0.1, False
        if cmd[0] == "/krust":
            definition = os.path.join(root, "krust-kompiled")
            os.makedirs(definition)
            with open(os.path.join(definition, "definition.kore"), "w") as output:
                output.write("[]\n")
            return 0, "", "", 0.1, False
        if cmd[0] == run.KORE_PARSER:
            # An LLVM-target krust definition is verified through its N38 copy.
            if cmd[1].endswith("krust-kompiled/definition.verify.kore"):
                return 1, "", "Error:\n  module 'TEST':\n  axiom declaration:\n  (definition.kore 1:1):\n    " + diagnostic + "\n        f(X)\n", 0.1, False
            return 0, "", "", 0.1, False
        raise AssertionError(cmd)
    run.sh = fake_sh
    run.run_test_binary = lambda name, env, cwd: (comparison_rc, "", "")
    run.KRUST = "/krust"
    run.KORE_PARSER = "/kbin/kore-parser"
    recipe = run.split_recipe("/kbin/kompile --backend llvm test.k --output-definition ./test-kompiled")
    run.do_kompile(case, recipe, False)
    run.step_record(case, step="krun", test="p.test", stage="krun", verdict=program_verdict)
    run.finish(case)
    result = {"verdict": case.verdict, "step": case.steps}
    return {
        "steps": [[s["step"], s["verdict"], s.get("verify_error")] for s in case.steps],
        "verdict": case.verdict,
        "ranked": ratchet.ranked_case(result, {})[0],
    }

try:
    ratchet.expectation_map({"case": [{"name": "c", "step_exclusions": [
        {"step": "kore-verify", "exclusion": "x", "reason": "r"}]}]})
    refused = None
except ratchet.RatchetError as error:
    refused = str(error)

print(json.dumps({
    "refused": refused,
    "alone": probe(ANYWHERE, 0, "match"),
    "program": probe(ANYWHERE, 0, "mismatch"),
    "comparison": probe(ANYWHERE, 1, "match"),
    "other": probe("Expected function symbol, but found constructor symbol:", 0, "match"),
}))
"#;
    let output = Command::new("python3")
        .env("K_KOMPILE", "/kbin/kompile")
        .env_remove("GHCRTS")
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
    let anywhere = "Found invalid subterm in argument of function equation:";
    assert_eq!(
        probes["alone"]["steps"],
        serde_json::json!([
            ["kompile", "match", null],
            ["krun", "match", null],
            ["kore-verify", "mismatch", anywhere],
        ]),
        "{probes}"
    );
    assert_eq!(probes["alone"]["verdict"], "mismatch", "{probes}");
    assert!(
        probes["refused"]
            .as_str()
            .is_some_and(|error| error.contains("excludes a kore-verify step")),
        "{probes}"
    );
    for key in ["alone", "program", "comparison", "other"] {
        assert_eq!(probes[key]["verdict"], "mismatch", "{probes}");
        assert_eq!(probes[key]["ranked"], "mismatch", "{key}: {probes}");
    }
    assert_eq!(
        probes["other"]["steps"][2][2], "Expected function symbol, but found constructor symbol:",
        "{probes}"
    );
}

#[test]
fn conformance_driver_verifies_the_n38_copy_of_an_llvm_target_definition() {
    // The LLVM target emits a partial value production without `function`, which the verifier
    // requires of an equation head. The driver verifies a copy with `function{}()` added to the
    // marked declarations (N38) and leaves the compared definition unchanged; a Rust-target
    // definition (a Haskell-backend recipe) is verified as written.
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import json, os, sys, tempfile
sys.path.insert(0, sys.argv[1])
import run

DEFINITION = "[]\nmodule TEST\n  sort S{} []\n  symbol Lblwrap{}(S{}) : S{} [value-production{}()]\nendmodule []\n"

def probe(backend):
    root = tempfile.mkdtemp()
    case = run.Case("verify")
    case.dir = root
    case.log = os.path.join(root, "logs")
    with open(os.path.join(root, "test.k"), "w") as source:
        source.write("module TEST endmodule\n")
    verified = []
    def fake_sh(cmd, cwd, timeout, stdin_path=None, env=None, shell=False):
        if cmd[:2] == ["bash", "-c"]:
            definition = os.path.join(root, "test-kompiled")
            os.makedirs(definition)
            for name, text in [("mainModule.txt", "TEST\n"), ("mainSyntaxModule.txt", "TEST\n"),
                               ("configVars.sh", ""), ("definition.kore", "[]\n")]:
                with open(os.path.join(definition, name), "w") as output:
                    output.write(text)
            return 0, "", "", 0.1, False
        if cmd[0] == "/krust":
            definition = os.path.join(root, "krust-kompiled")
            os.makedirs(definition, exist_ok=True)
            with open(os.path.join(definition, "definition.kore"), "w") as output:
                output.write(DEFINITION)
            os.makedirs(os.path.join(root, "krust-kompiled-runtime"), exist_ok=True)
            return 0, "", "", 0.1, False
        if cmd[0] == run.KORE_PARSER:
            if "krust-kompiled" not in cmd[1]:
                return 0, "", "", 0.1, False
            verified.append(os.path.relpath(cmd[1], root))
            with open(cmd[1]) as handle:
                text = handle.read()
            if "value-production{}()]" in text:
                return 1, "", "Error:\n  module 'TEST':\n  axiom declaration:\n  (definition.kore 1:1):\n    Expected function symbol, but found constructor symbol:\n        Lblwrap{}\n", 0.1, False
            return 0, "", "", 0.1, False
        raise AssertionError(cmd)
    run.sh = fake_sh
    run.run_test_binary = lambda name, env, cwd: (0, "", "")
    run.KRUST = "/krust"
    run.KORE_PARSER = "/kbin/kore-parser"
    recipe = run.split_recipe(f"/kbin/kompile --backend {backend} test.k --output-definition ./test-kompiled")
    run.do_kompile(case, recipe, False)
    run.finish(case)
    with open(os.path.join(root, "krust-kompiled", "definition.kore")) as handle:
        compared = handle.read()
    copy = os.path.join(root, "krust-kompiled", "definition.verify.kore")
    return {
        "steps": [[s["step"], s["verdict"], s.get("verify_error")] for s in case.steps],
        "verified": verified,
        "compared_unchanged": compared == DEFINITION,
        "copy": open(copy).read() if os.path.exists(copy) else None,
    }

print(json.dumps({"llvm": probe("llvm"), "haskell": probe("haskell")}))
"#;
    let output = Command::new("python3")
        .env("K_KOMPILE", "/kbin/kompile")
        .env_remove("GHCRTS")
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
    assert_eq!(
        probes["llvm"]["verified"],
        serde_json::json!(["krust-kompiled/definition.verify.kore"]),
        "{probes}"
    );
    assert_eq!(
        probes["llvm"]["steps"],
        serde_json::json!([["kompile", "match", null]]),
        "{probes}"
    );
    assert_eq!(probes["llvm"]["compared_unchanged"], true, "{probes}");
    assert!(
        probes["llvm"]["copy"]
            .as_str()
            .is_some_and(|copy| copy.contains("value-production{}(), function{}()]")),
        "{probes}"
    );
    assert_eq!(
        probes["haskell"]["verified"],
        serde_json::json!(["krust-kompiled/definition.kore"]),
        "{probes}"
    );
    assert_eq!(
        probes["haskell"]["copy"],
        serde_json::Value::Null,
        "{probes}"
    );
    assert_eq!(
        probes["haskell"]["steps"],
        serde_json::json!([
            ["kompile", "match", null],
            [
                "kore-verify",
                "mismatch",
                "Expected function symbol, but found constructor symbol:"
            ],
        ]),
        "{probes}"
    );
}

#[test]
fn conformance_driver_verifies_a_copy_with_anywhere_heads_declared_injective() {
    // An anywhere head is emitted without `injective`, which its anywhere equations may falsify,
    // and the verifier admits it in an equation argument only when injective. The driver
    // verifies a copy with `injective{}()` added to exactly the `anywhere` declarations that
    // lack it (N47), for either target, and leaves the compared definition unchanged; any other
    // rejection of the copy still ranks the case.
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import json, os, sys, tempfile
sys.path.insert(0, sys.argv[1])
import run

DEFINITION = ("[]\nmodule TEST\n  sort S{} []\n"
              "  symbol Lblwrap{}(S{}) : S{} [anywhere{}()]\n"
              "  symbol Lblkept{}(S{}) : S{} [anywhere{}(), injective{}()]\n"
              "  symbol Lblfree{}(S{}) : S{} [constructor{}()]\nendmodule []\n")

def probe(backend, other_rejection):
    root = tempfile.mkdtemp()
    case = run.Case("verify")
    case.dir = root
    case.log = os.path.join(root, "logs")
    with open(os.path.join(root, "test.k"), "w") as source:
        source.write("module TEST endmodule\n")
    verified = []
    def fake_sh(cmd, cwd, timeout, stdin_path=None, env=None, shell=False):
        if cmd[:2] == ["bash", "-c"]:
            definition = os.path.join(root, "test-kompiled")
            os.makedirs(definition)
            for name, text in [("mainModule.txt", "TEST\n"), ("mainSyntaxModule.txt", "TEST\n"),
                               ("configVars.sh", ""), ("definition.kore", "[]\n")]:
                with open(os.path.join(definition, name), "w") as output:
                    output.write(text)
            return 0, "", "", 0.1, False
        if cmd[0] == "/krust":
            definition = os.path.join(root, "krust-kompiled")
            os.makedirs(definition, exist_ok=True)
            with open(os.path.join(definition, "definition.kore"), "w") as output:
                output.write(DEFINITION)
            os.makedirs(os.path.join(root, "krust-kompiled-runtime"), exist_ok=True)
            return 0, "", "", 0.1, False
        if cmd[0] == run.KORE_PARSER:
            if "krust-kompiled" not in cmd[1]:
                return 0, "", "", 0.1, False
            verified.append(os.path.relpath(cmd[1], root))
            with open(cmd[1]) as handle:
                text = handle.read()
            if "[anywhere{}()]" in text:
                return 1, "", "Error:\n    Found invalid subterm in argument of function equation:\n        Lblwrap{}\n", 0.1, False
            if other_rejection:
                return 1, "", "Error:\n    Expected function symbol, but found constructor symbol:\n        Lblfree{}\n", 0.1, False
            return 0, "", "", 0.1, False
        raise AssertionError(cmd)
    run.sh = fake_sh
    run.run_test_binary = lambda name, env, cwd: (0, "", "")
    run.KRUST = "/krust"
    run.KORE_PARSER = "/kbin/kore-parser"
    recipe = run.split_recipe(f"/kbin/kompile --backend {backend} test.k --output-definition ./test-kompiled")
    run.do_kompile(case, recipe, False)
    run.finish(case)
    with open(os.path.join(root, "krust-kompiled", "definition.kore")) as handle:
        compared = handle.read()
    copy = os.path.join(root, "krust-kompiled", "definition.verify.kore")
    with open(os.path.join(case.log, "kompile.krust-verify.log")) as handle:
        log = handle.read()
    return {
        "steps": [[s["step"], s["verdict"], s.get("verify_error")] for s in case.steps],
        "verified": verified,
        "compared_unchanged": compared == DEFINITION,
        "copy": open(copy).read() if os.path.exists(copy) else None,
        "log": log.splitlines()[:2],
    }

print(json.dumps({
    "haskell": probe("haskell", False),
    "llvm": probe("llvm", False),
    "other": probe("haskell", True),
}))
"#;
    let output = Command::new("python3")
        .env("K_KOMPILE", "/kbin/kompile")
        .env_remove("GHCRTS")
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
    let expected_copy = "[]\nmodule TEST\n  sort S{} []\n  symbol Lblwrap{}(S{}) : S{} [anywhere{}(), injective{}()]\n  symbol Lblkept{}(S{}) : S{} [anywhere{}(), injective{}()]\n  symbol Lblfree{}(S{}) : S{} [constructor{}()]\nendmodule []\n";
    for backend in ["haskell", "llvm"] {
        let probe = &probes[backend];
        assert_eq!(
            probe["verified"],
            serde_json::json!(["krust-kompiled/definition.verify.kore"]),
            "{backend}: {probes}"
        );
        assert_eq!(
            probe["steps"],
            serde_json::json!([["kompile", "match", null]]),
            "{backend}: {probes}"
        );
        assert_eq!(probe["compared_unchanged"], true, "{backend}: {probes}");
        assert_eq!(probe["copy"], expected_copy, "{backend}: {probes}");
    }
    assert_eq!(
        probes["haskell"]["log"][0], "N47 verification anywhere declarations made injective: 1",
        "{probes}"
    );
    assert_eq!(
        probes["llvm"]["log"],
        serde_json::json!([
            "N38 LLVM verification value-production declarations: 0",
            "N47 verification anywhere declarations made injective: 1",
        ]),
        "{probes}"
    );
    assert_eq!(
        probes["other"]["steps"],
        serde_json::json!([
            ["kompile", "match", null],
            [
                "kore-verify",
                "mismatch",
                "Expected function symbol, but found constructor symbol:"
            ],
        ]),
        "{probes}"
    );
}

#[test]
fn a_step_exclusion_ranks_a_case_by_the_steps_it_does_not_name() {
    // A step exclusion names one step's divergence. Every other step, before or after it and at
    // any verdict, keeps the case ranked, so the exclusion of one recipe of a many-recipe case
    // does not hide a divergence of another. A case exclusion leaves the case unranked, and a
    // case none of whose steps is excluded keeps the driver's own verdict.
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import json, sys
sys.path.insert(0, sys.argv[1])
import ratchet

EXCLUSION = {"step_exclusions": [{"step": "kompile", "out": "bad.k.out", "exclusion": "x", "reason": "r"}]}
bad = {"step": "kompile", "out": "bad.k.out", "verdict": "mismatch"}
other = {"step": "kompile", "out": "other.k.out", "verdict": "mismatch"}
program = {"step": "krun", "test": "p", "verdict": "match"}
error = {"step": "krun", "test": "p", "verdict": "krust-error"}

def ranked(verdict, steps, expectation=EXCLUSION):
    return ratchet.ranked_case({"verdict": verdict, "step": steps}, expectation)

print(json.dumps({
    "only": ranked("mismatch", [bad, program]),
    "later": ranked("mismatch", [bad, other]),
    "earlier": ranked("mismatch", [other, bad]),
    "worse": ranked("krust-error", [bad, error]),
    "all": ranked("mismatch", [bad]),
    "none": ranked("skipped-with-reason", [other], {}),
    "case": ranked("mismatch", [other], {"exclusion": "y"}),
}))
"#;
    let output = Command::new("python3")
        .args(["-I", "-c", script])
        .arg(workspace.join("scripts/conformance"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let probes: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(
        probes,
        serde_json::json!({
            "only": ["match", ["x"], ""],
            "later": ["mismatch", ["x"], ""],
            "earlier": ["mismatch", ["x"], ""],
            "worse": ["krust-error", ["x"], ""],
            "all": ["match", ["x"], ""],
            "none": ["skipped-with-reason", [], ""],
            "case": ["mismatch", [], "y"],
        })
    );
}

/// A step exclusion names one step's divergence, so any other step that does not match keeps the
/// case ranked, whatever its verdict: here the excluded recipe mismatches (the case's verdict)
/// and another recipe of the same case is `krust-unsupported`, ranked better than `mismatch` but
/// below a `match` floor. Excluding the case would hide that recipe's divergence.
#[test]
fn a_step_exclusion_keeps_the_case_ranked_when_another_step_fails_at_a_better_rank() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import json, sys
sys.path.insert(0, sys.argv[1])
import ratchet

EXCLUSION = {"step_exclusions": [{"step": "kompile", "out": "bad.k.out", "exclusion": "x", "reason": "r"}]}
bad = {"step": "kompile", "out": "bad.k.out", "verdict": "mismatch"}
for verdict in ("krust-unsupported", "skipped-with-reason"):
    other = {"step": "kompile", "out": "other.k.out", "verdict": verdict}
    print(json.dumps(ratchet.ranked_case({"verdict": "mismatch", "step": [bad, other]}, EXCLUSION)))
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
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "[\"krust-unsupported\", [\"x\"], \"\"]\n[\"skipped-with-reason\", [\"x\"], \"\"]\n"
    );
}

/// A step exclusion accepts the divergence of the steps it names, so excluding them must rank the
/// case exactly as if those steps had not been run: the case is flagged (a regression or below its
/// floor) when, and only when, the worst of its other steps would be. The property is checked on
/// random cases (one to four steps of random verdicts, a random subset excluded by `out`, a
/// random floor), comparing `build_run` on the case with its exclusions against `build_run` on the
/// same case with the excluded steps removed and its verdict recomputed from the rest.
#[test]
fn a_step_exclusion_ranks_a_case_as_if_its_named_steps_were_absent() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import json, random, sys
sys.path.insert(0, sys.argv[1])
import ratchet

VERDICTS = sorted(ratchet.RANK)

def worst(steps):
    return min((step["verdict"] for step in steps), key=ratchet.RANK.__getitem__) if steps else "match"

def flagged(result, expectation, floor):
    run = ratchet.build_run(
        sequence=1, label="t", workspace_revision="w", k_revision="k", driver_version="d",
        krust_sha256="", test_binary_sha256="", selection="all", jobs=1, wall_seconds=0.0,
        peak_rss_mib=0, artifacts="", results=[result], expectations={"c": expectation},
        previous_runs=[{"driver_version": "d", "case": [{"name": "c", "rank": ratchet.RANK[floor]}]}],
        timestamp_utc="2026-01-01T00:00:00Z",
    )
    return "c" in run["regressions"] or "c" in run["below_floor"]

rng = random.Random(20261010)
failures = []
for _ in range(3000):
    steps = [{"step": "kompile", "out": f"s{i}.out", "verdict": rng.choice(VERDICTS)}
             for i in range(rng.randint(1, 4))]
    named = [step for step in steps if rng.random() < 0.5]
    floor = rng.choice([verdict for verdict in VERDICTS if ratchet.RANK[verdict] >= 0])
    exclusions = [{"step": "kompile", "out": step["out"], "exclusion": "x", "reason": "r"} for step in named]
    rest = [step for step in steps if step not in named]
    with_exclusion = flagged({"name": "c", "verdict": worst(steps), "step": steps},
                             {"name": "c", "step_exclusions": exclusions}, floor)
    without_steps = flagged({"name": "c", "verdict": worst(rest), "step": rest}, {"name": "c"}, floor)
    if with_exclusion != without_steps:
        failures.append({"steps": steps, "excluded": [step["out"] for step in named], "floor": floor,
                         "flagged with the exclusion": with_exclusion,
                         "flagged without the steps": without_steps})
print(json.dumps({"failures": len(failures), "first": failures[:3]}, indent=1))
"#;
    let output = Command::new("python3")
        .args(["-I", "-c", script])
        .arg(workspace.join("scripts/conformance"))
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success(),
        "{stdout}{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(stdout.contains("\"failures\": 0,"), "{stdout}");
}

/// A rank logged before cases were ranked by their non-excluded steps counts an excluded step and
/// can be lower than the case's rank on the current scale, so it is a loose floor. The first rank
/// logged on the current scale re-establishes the floor without lowering it, and a measurement
/// compared against a run on the earlier scale is a driver change.
#[test]
fn the_first_residual_rank_re_establishes_a_floor_logged_on_an_earlier_scale() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import json, sys
sys.path.insert(0, sys.argv[1])
import ratchet

EXPECTATION = {"name": "c", "step_exclusions": [{"step": "kast", "exclusion": "x", "reason": "r"}]}

def measure(previous_runs, verdicts):
    steps = [{"step": step, "verdict": verdict} for step, verdict in verdicts]
    result = {"name": "c", "verdict": min((v for _, v in verdicts), key=ratchet.RANK.__getitem__), "step": steps}
    return ratchet.build_run(
        sequence=len(previous_runs), label="t", workspace_revision="w", k_revision="k",
        driver_version="d", krust_sha256="", test_binary_sha256="", selection="all", jobs=1,
        wall_seconds=0.0, peak_rss_mib=0, artifacts="", results=[result],
        expectations={"c": EXPECTATION}, previous_runs=previous_runs,
        timestamp_utc="2026-01-01T00:00:00Z",
    )

# Entry 0 on the earlier scale ranked the case by its excluded kast step.
legacy = {"driver_version": "d", "case": [{"name": "c", "verdict": "mismatch", "rank": 1}]}
first = measure([legacy], [("kompile", "match"), ("kast", "mismatch")])
second = measure([legacy, first], [("kompile", "krust-unsupported"), ("kast", "mismatch")])
row = lambda run: run["case"][0]
print(json.dumps({
    "first": [row(first)["ranked_verdict"], row(first)["rank"], row(first)["floor_rank"], row(first)["delta"], first["driver_deltas"], first["ranking"]],
    "second": [row(second)["ranked_verdict"], row(second)["floor_rank"], second["below_floor"], second["regressions"]],
}))
"#;
    let output = Command::new("python3")
        .args(["-I", "-c", script])
        .arg(workspace.join("scripts/conformance"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let probes: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(
        probes,
        serde_json::json!({
            "first": ["match", 3, 1, "improvement", ["c"], "residual-steps"],
            "second": ["krust-unsupported", 3, ["c"], ["c"]],
        })
    );
}

/// The ratchet refuses an expectations file whose exclusions do not say what they leave unranked:
/// a case exclusion removes every step, present and future, so it must state why no step can be
/// ranked; a `whole_case_reason` with nothing excluded justifies nothing; and a step exclusion
/// with no selector names no step. Each row is appended to an otherwise valid file and the
/// ratchet is run on it, so the refusal is the ratchet's, not a check of the committed file.
#[test]
fn the_ratchet_refuses_exclusions_that_do_not_name_what_they_leave_unranked() {
    let rows = [
        (
            "[[case]]\nname = \"e\"\nbaseline_verdict = \"mismatch\"\nbaseline_stage = \"krun\"\nexclusion = \"x\"\nreason = \"r\"\n",
            "whole_case_reason",
        ),
        (
            "[[case]]\nname = \"e\"\nbaseline_verdict = \"mismatch\"\nbaseline_stage = \"krun\"\nexclusion = \"\"\nreason = \"r\"\nwhole_case_reason = \"w\"\n",
            "but no exclusion",
        ),
        (
            "[[case]]\nname = \"e\"\nbaseline_verdict = \"mismatch\"\nbaseline_stage = \"krun\"\nexclusion = \"\"\nreason = \"r\"\nstep_exclusions = [\n  { exclusion = \"x\", reason = \"r\" },\n]\n",
            "without a selector",
        ),
    ];
    for (row, refusal) in rows {
        let fixture = Fixture::new();
        let mut expectations = fs::read_to_string(&fixture.expectations).unwrap();
        expectations.push('\n');
        expectations.push_str(row);
        fs::write(&fixture.expectations, expectations).unwrap();
        let results = fixture.results("results", &[("a", "match", "krun")]);
        let output = fixture.seed(&results);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(!output.status.success(), "{refusal}: accepted\n{stderr}");
        assert!(stderr.contains(refusal), "{refusal}: {stderr}");
        assert!(!fixture.log.exists(), "{refusal}: a log was written");
    }
}

/// A run that measures only the generated Bison parsers ranks a case by its `bison-parser` steps,
/// and records that it did; the ratchet, re-ranking a case after deleting its excluded steps,
/// selects the same steps, so the compilation that only produces the parsers ranks in neither.
/// The same result without the record is ranked from every remaining step.
#[test]
fn the_ratchet_ranks_a_bison_parser_run_by_the_steps_the_driver_ranks() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import json, sys
sys.path.insert(0, sys.argv[1])
import ratchet

EXCLUSION = {"step_exclusions": [{"step": "bison-parser", "out": "bad.out", "exclusion": "x", "reason": "r"}]}
steps = [
    {"step": "kompile", "verdict": "mismatch"},
    {"step": "bison-parser", "out": "bad.out", "verdict": "mismatch"},
    {"step": "bison-parser", "out": "good.out", "verdict": "match"},
]
print(json.dumps({
    "bison": ratchet.ranked_case({"verdict": "mismatch", "bison_parsers_only": True, "step": steps}, EXCLUSION)[0],
    "full": ratchet.ranked_case({"verdict": "mismatch", "step": steps}, EXCLUSION)[0],
}))
"#;
    let output = Command::new("python3")
        .args(["-I", "-c", script])
        .arg(workspace.join("scripts/conformance"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let probes: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(
        probes,
        serde_json::json!({"bison": "match", "full": "mismatch"})
    );
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
            assert!(
                !case["whole_case_reason"]
                    .as_str()
                    .unwrap_or_default()
                    .is_empty(),
                "case {name} is excluded as a whole and needs a whole_case_reason naming why no step can be ranked"
            );
        }
        if let Some(step_exclusions) = case.get("step_exclusions") {
            for step in step_exclusions.as_array().expect("step exclusions array") {
                assert!(
                    ["test", "out", "step"]
                        .iter()
                        .any(|selector| step.get(*selector).is_some()),
                    "step exclusion on {name} needs a selector"
                );
                let exclusion = step["exclusion"].as_str().expect("step exclusion category");
                assert!(
                    category_ids.contains(exclusion),
                    "unknown step exclusion on {name}: {exclusion}"
                );
                assert!(
                    !step["reason"].as_str().unwrap_or_default().is_empty(),
                    "step exclusion on {name} needs a reason"
                );
            }
        }
        if accepted != "match" {
            assert!(
                !case["reason"].as_str().unwrap_or_default().is_empty(),
                "accepted non-match {name} needs an inline justification (with an exclusion) or a measured reason (pending work)"
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
    let undriven = categories
        .iter()
        .find(|category| category["id"].as_str() == Some("undriven-recipe"))
        .expect("undriven-recipe category");
    assert!(
        undriven["meaning"]
            .as_str()
            .unwrap()
            .contains("individual step")
    );
    let simple = cases
        .iter()
        .find(|case| case["name"].as_str() == Some("pl-tutorial/2_languages/1_simple/1_untyped"))
        .expect("SIMPLE untyped expectation");
    assert_eq!(simple["accepted_verdict"].as_str(), Some("match"));
    assert!(simple.get("step_exclusions").is_none());
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

/// The driver learns the memory guard from the ratchet's command line, which states the guard the
/// ratchet's own shell entered; an exported guard kind could come from whatever started the
/// ratchet, so the driver does not read it.
#[test]
fn conformance_ratchet_states_the_memory_guard_it_entered_to_the_driver() {
    let fixture = Fixture::new();
    let baseline = fixture.results("baseline", &baseline_cases());
    assert!(fixture.seed(&baseline).status.success());
    let cases: Vec<_> = baseline_cases()
        .into_iter()
        .filter(|(name, _, _)| *name == "b")
        .collect();
    let results = fixture.results("guard", &cases);
    let output = fixture.run("guard", &results, &["--cases", "b"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let args = fs::read_to_string(&fixture.args).unwrap();
    let guard = args
        .lines()
        .skip_while(|line| *line != "--memory-guard")
        .nth(1);
    assert!(
        matches!(guard, Some("systemd-scope" | "rlimit-as")),
        "driver arguments: {args}"
    );
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

#[test]
fn conformance_audit_lists_pending_cases_without_an_open_backlog_ticket() {
    let fixture = Fixture::new();
    let baseline = fixture.results(
        "baseline",
        &[
            ("a", "match", "krun"),
            ("b", "mismatch", "search"),
            ("c", "mismatch", "kompile"),
            ("d", "krust-unsupported", "kast"),
        ],
    );
    assert!(fixture.seed(&baseline).status.success());

    // b is pending and owned; d is pending and unowned; c is excluded and needs no ticket;
    // the ticket on a names a matching case and is reported as closable.
    let backlog = fixture.root.join("backlog.toml");
    fs::write(
        &backlog,
        r#"version = 1

[[ticket]]
id = "T-01"
title = "b needs the search step"
state = "open"
cases = ["b"]

[[ticket]]
id = "T-02"
title = "a landed"
state = "open"
cases = ["a"]

[[ticket]]
id = "T-03"
title = "d was closed without landing"
state = "closed"
cases = ["d"]

[[ticket]]
id = "T-04"
title = "d is historical evidence, not owned"
state = "open"
case_role = "evidence"
cases = ["d"]
"#,
    )
    .unwrap();
    let output = fixture.audit_with_backlog(&backlog);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(output.status.code(), Some(3), "{stdout}");
    assert!(
        stdout.contains("### Conformance backlog audit (2 pending cases)"),
        "{stdout}"
    );
    assert!(stdout.contains("| b | 0 | mismatch | T-01 |"), "{stdout}");
    assert!(
        stdout.contains("| d | 0 | krust-unsupported | (none) |"),
        "{stdout}"
    );
    assert!(
        !stdout.contains("| c |"),
        "excluded cases are not pending: {stdout}"
    );
    assert!(
        stdout.contains("pending without an open ticket: 1"),
        "{stdout}"
    );
    assert!(
        stdout.contains("open tickets whose cases all match: [\"T-02\"]"),
        "{stdout}"
    );
    assert!(
        stdout.contains("open evidence-only tickets: [\"T-04\"]"),
        "{stdout}"
    );

    fs::write(
        &backlog,
        r#"version = 1

[[ticket]]
id = "T-01"
title = "b and d need work"
state = "open"
cases = ["b", "d"]
"#,
    )
    .unwrap();
    let output = fixture.audit_with_backlog(&backlog);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(output.status.success(), "{stdout}");
    assert!(
        stdout.contains("pending without an open ticket: 0"),
        "{stdout}"
    );

    // Without a backlog the audit keeps its floor-only contract.
    let output = fixture.audit();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert!(!String::from_utf8_lossy(&output.stdout).contains("backlog audit"));

    fs::write(&backlog, "version = 1\n\n[[ticket]]\nid = \"T-09\"\ntitle = \"unknown\"\nstate = \"open\"\ncases = [\"zz\"]\n").unwrap();
    let output = fixture.audit_with_backlog(&backlog);
    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&output.stderr).contains("names an unknown case: zz"));
}

/// Whether a GHC runtime option is valid is a property of the binary that receives it: a binary
/// of the non-threaded runtime refuses `-N`. So the driver gives each reference call the options
/// of the binary it runs, never the options its caller exported as `GHCRTS`: none to a
/// non-threaded tool, and `REFERENCE_GHCRTS` (by default `-N1`) to a threaded one.
#[test]
fn conformance_driver_gives_each_reference_tool_its_own_ghc_runtime_options() {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let script = r#"
import json, sys
sys.path.insert(0, sys.argv[1])
import run
print(json.dumps({
    "kompile": run.reference_process_env("kompile")["GHCRTS"],
    "krun": run.reference_process_env("krun", ["x.imp"])["GHCRTS"],
    "krun-pattern": run.reference_process_env("krun", ["--pattern", "p"])["GHCRTS"],
    "kore-parser": run.reference_process_env("kore-parser")["GHCRTS"],
}))
"#;
    let probe = |environment: &[(&str, &str)]| {
        let mut command = Command::new("python3");
        command
            .env("K_KOMPILE", "/kbin/kompile")
            .env_remove("GHCRTS")
            .env_remove("REFERENCE_GHCRTS")
            .args(["-c", script])
            .arg(workspace.join("scripts/conformance"));
        for (name, value) in environment {
            command.env(name, value);
        }
        let output = command.output().unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        serde_json::from_slice::<serde_json::Value>(&output.stdout).unwrap()
    };
    let defaults = serde_json::json!({
        "kompile": "-N1", "krun": "-N1", "krun-pattern": "", "kore-parser": ""
    });
    assert_eq!(probe(&[]), defaults);
    assert_eq!(
        probe(&[("GHCRTS", "-N3")]),
        defaults,
        "the caller's GHCRTS reached a reference call"
    );
    assert_eq!(
        probe(&[("REFERENCE_GHCRTS", "-N2")]),
        serde_json::json!({
            "kompile": "-N2", "krun": "-N2", "krun-pattern": "", "kore-parser": ""
        }),
        "REFERENCE_GHCRTS replaces the threaded tools' default and reaches no other tool"
    );
}
