use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    os::unix::fs::PermissionsExt,
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

use toml::Value;

const EXPECTATIONS: &str = include_str!("../../../scripts/conformance/expectations.toml");

struct Fixture {
    root: PathBuf,
    log: PathBuf,
    runs: PathBuf,
    expectations: PathBuf,
    status: PathBuf,
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
        let status = root.join("implementation-status.toml");
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
tickets = ["A1-01"]
exclusion = ""
reason = ""

[[case]]
name = "b"
baseline_verdict = "mismatch"
baseline_stage = "search"
tickets = ["A1-01"]
exclusion = ""
reason = "owned mismatch"

[[case]]
name = "c"
baseline_verdict = "match"
baseline_stage = "kompile"
tickets = []
exclusion = "fixture-exclusion"
reason = "adjudicated fixture exclusion"

[[case]]
name = "d"
baseline_verdict = "krust-unsupported"
baseline_stage = "kast"
tickets = []
exclusion = ""
reason = ""
unexplained = true
"#,
        )
        .unwrap();
        fs::write(
            &status,
            r#"schema = 1
[[ticket]]
id = "A1-01"
state = "implemented"
verification = "targeted"
commits = ["fixture"]
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
            status,
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
            .args(["--status", self.status.to_str().unwrap()])
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
fn conformance_driver_forwards_kompile_warning_flags_and_md_selectors() {
    // D1-14 documented the driver dropping `-w2e -w all` (checkWarns) and D1-04's
    // markdownSelectors row exposed that krust's per-run recompilation never saw the
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
    // Host ratchet run 16: werrorCategory (`kompile -w2e -Wno missing-syntax-module`, ktest)
    // fell below its stage-1 floor and prelude-warnings (`-w all -w2e`, ktest) from match to
    // krust-error, because 2828e95 forwarded `-w2e` as `--warnings-to-errors` while dropping
    // the per-category `-Wno` krust cannot express, and because krust's extension warnings
    // (D1-05 UnadmittedHookNamespace) are promoted where the reference emits nothing. The
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
            assert!(
                category.get("arbiter").is_some() || category.get("decided_by").is_some(),
                "exclusion category needs a recorded authority: {category:?}"
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
        let tickets = case["tickets"].as_array().expect("ticket list");
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
                !tickets.is_empty()
                    || !exclusion.is_empty()
                    || case["unexplained"].as_bool() == Some(true),
                "accepted failure {name} needs an owner, exclusion, or unexplained marker"
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
    // Entry 0 is the stage-1 floor: a case that a later driver raised above it may fall back
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
fn conformance_ratchet_fails_below_the_stage_1_floor_across_driver_versions() {
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
fn conformance_ratchet_fails_while_a_case_stays_below_the_stage_1_floor() {
    // The exit criterion is "no case below its stage-1 rank": a case that already fell below
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
fn conformance_ratchet_audit_lists_cases_below_the_stage_1_floor() {
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
        stdout.contains("| a | 3 | 1 | 1 | mismatch | A1-01 |  |"),
        "audit table lists the non-excluded case: {stdout}"
    );
    assert!(
        stdout.contains("| c | 3 | 0 | 1 | krust-error |  | fixture-exclusion |"),
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
fn conformance_ratchet_reports_overdue_cases() {
    let fixture = Fixture::new();
    let baseline = fixture.results("baseline", &baseline_cases());
    assert!(fixture.seed(&baseline).status.success());
    let output = fixture.run("overdue", &baseline, &["--all"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let document = fixture.document();
    let run = document["run"].as_array().unwrap().last().unwrap();
    assert_eq!(run["overdue"].as_array().unwrap()[0].as_str(), Some("b"));
}

#[test]
fn conformance_ratchet_selects_cases_by_ticket() {
    let fixture = Fixture::new();
    let baseline = fixture.results("baseline", &baseline_cases());
    assert!(fixture.seed(&baseline).status.success());
    let output = fixture.run("ticket", &baseline, &["--ticket", "A1-01"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let args = fs::read_to_string(&fixture.args).unwrap();
    assert!(args.contains("--cases\na\nb\n"), "driver arguments: {args}");
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
