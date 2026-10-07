//! `krs parse`, `krs run`, `krs search`, and `krs prove` end to end, through `krs-exec`.
//!
//! The Definition IR these commands compile comes only from the collector, so the `krs-exec`
//! behaviours that need an authored definition (a tour-minimal run, its trace, depth 0, and a
//! proven and a disproved claim) are checked here, through the real executable.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Output;

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};
use serde_json::Value;

/// Shared with the CLI gate, which runs the same claims through Java `kprove`.
const CLAIMS: &str = include_str!("../../../tests/cli/fixtures/claims/src/lib.rs");
const PACKAGE: &str = "krs-cli-exec-fixture";

fn materialize(temporary: &Path, source: &str) -> PathBuf {
    let project = temporary.join("language");
    fs::create_dir_all(project.join("src")).unwrap();
    fs::write(project.join("src/lib.rs"), source).unwrap();
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    let krs_literal = serde_json::to_string(krs.to_str().unwrap()).unwrap();
    let manifest = format!(
        "[package]\nname = \"{PACKAGE}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nkrs = {{ path = {krs_literal} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-CLI-EXEC\"\n\n[package.metadata.krs.definitions.main]\nroot = \"crate\"\nsyntax-root = \"crate\"\n\n[workspace]\n"
    );
    fs::write(project.join("Cargo.toml"), manifest).unwrap();
    project.join("Cargo.toml")
}

/// The tour-minimal definition with the facade named `krs`: `foo` is the initial program.
fn tour_minimal() -> String {
    include_str!("../../../tests/tour-minimal/src/lib.rs")
        .replace("use k::", "use krs::")
        .replace("k::", "krs::")
}

fn krs(target: &Path, manifest: &Path, verb: &str, arguments: &[&str]) -> Output {
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    process
        .current_dir(manifest.parent().unwrap())
        .arg(verb)
        .args(["--manifest-path"])
        .arg(manifest)
        .args(["--package", PACKAGE, "--definition", "main"])
        .args(arguments);
    process.output().unwrap()
}

fn json(output: &Output) -> Value {
    assert!(
        output.status.code().is_some(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
        panic!(
            "stdout is not JSON ({error}):\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    })
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

#[test]
fn tour_minimal_runs_one_step_with_an_authored_trace_and_stays_put_at_depth_zero() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = materialize(temporary.path(), &tour_minimal());

    let run = krs(
        target.path(),
        &manifest,
        "run",
        &["--trace", "--output", "json"],
    );
    assert_eq!(run.status.code(), Some(0), "{}", stderr(&run));
    let report = json(&run);
    assert_eq!(report["schema"], "krs-exec/1");
    let run_report = &report["run"];
    assert_eq!(run_report["halt"], "stuck");
    assert_eq!(run_report["steps"], 1);
    assert_eq!(run_report["state"]["format"], "KAST");
    let trace = run_report["trace"].as_array().unwrap();
    assert_eq!(trace.len(), 1);
    assert_eq!(trace[0]["index"], 1);
    assert_eq!(trace[0]["label"], "ORG-KRS-CLI-EXEC.foo-to-bar");
    assert_eq!(trace[0]["origin"]["kind"], "authored");
    assert_eq!(trace[0]["origin"]["file"], "src/lib.rs");
    let line = trace[0]["origin"]["line"].as_u64().unwrap();
    let source = tour_minimal();
    assert!(
        source
            .lines()
            .nth(usize::try_from(line).unwrap() - 1)
            .unwrap()
            .contains("foo_to_bar"),
        "trace line {line} is not the foo_to_bar rule"
    );
    assert!(
        stderr(&run).contains("krs run: stuck after 1 step; <k> starts with `bar"),
        "{}",
        stderr(&run)
    );

    let human = krs(target.path(), &manifest, "run", &["--trace"]);
    assert_eq!(human.status.code(), Some(0), "{}", stderr(&human));
    assert!(
        stderr(&human).starts_with(&format!(
            "step 1  ORG-KRS-CLI-EXEC.foo-to-bar   src/lib.rs:{line}:"
        )),
        "{}",
        stderr(&human)
    );
    assert!(String::from_utf8_lossy(&human.stdout).contains("bar"));

    let depth_zero = krs(
        target.path(),
        &manifest,
        "run",
        &["--depth", "0", "--output", "json"],
    );
    assert_eq!(depth_zero.status.code(), Some(0), "{}", stderr(&depth_zero));
    let report = json(&depth_zero);
    assert_eq!(report["run"]["halt"], "depth-bound");
    assert_eq!(report["run"]["steps"], 0);
    assert!(stderr(&depth_zero).contains("<k> starts with `foo"));

    let stray = krs(target.path(), &manifest, "run", &["program.txt"]);
    assert_eq!(stray.status.code(), Some(2));
    assert!(
        stderr(&stray).contains("the init function takes no program (no $PGM); do not pass FILE"),
        "{}",
        stderr(&stray)
    );

    let search = krs(target.path(), &manifest, "search", &["--output", "json"]);
    assert_eq!(search.status.code(), Some(0), "{}", stderr(&search));
    let report = json(&search);
    assert_eq!(report["search"]["complete"], true);
    assert_eq!(report["search"]["solutions"].as_array().unwrap().len(), 1);

    let no_claims = krs(target.path(), &manifest, "prove", &[]);
    assert_eq!(no_claims.status.code(), Some(1));
    assert!(stderr(&no_claims).contains("this definition has no claims"));
}

#[test]
fn claims_prove_and_disprove_with_suggestions_for_unknown_labels() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = materialize(temporary.path(), CLAIMS);

    let prove = krs(target.path(), &manifest, "prove", &["--output", "json"]);
    assert_eq!(prove.status.code(), Some(1), "{}", stderr(&prove));
    let reports = json(&prove);
    let verdicts = reports["prove"]
        .as_array()
        .unwrap()
        .iter()
        .map(|report| {
            (
                report["claim"].as_str().unwrap().to_owned(),
                report["verdict"].as_str().unwrap().to_owned(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        verdicts,
        [
            (
                "ORG-KRS-CLI-EXEC-SPEC.bar-reaches-foo".to_owned(),
                "disproved".to_owned()
            ),
            (
                "ORG-KRS-CLI-EXEC-SPEC.foo-reaches-bar".to_owned(),
                "proven".to_owned()
            ),
        ]
    );
    assert_eq!(reports["prove"][1]["modality"], "all-path");
    assert_eq!(reports["prove"][1]["origin"]["file"], "src/lib.rs");

    let proven = krs(
        target.path(),
        &manifest,
        "prove",
        &["--claim", "foo-reaches-bar"],
    );
    assert_eq!(proven.status.code(), Some(0), "{}", stderr(&proven));
    assert_eq!(
        String::from_utf8_lossy(&proven.stdout),
        "ORG-KRS-CLI-EXEC-SPEC.foo-reaches-bar: proven\n"
    );

    let suggestion = krs(
        target.path(),
        &manifest,
        "prove",
        &["--claim", "foo_reaches_bar"],
    );
    assert_eq!(suggestion.status.code(), Some(1));
    assert!(
        stderr(&suggestion).contains(
            "no claim has label `foo_reaches_bar`; did you mean `ORG-KRS-CLI-EXEC-SPEC.foo-reaches-bar`?"
        ),
        "{}",
        stderr(&suggestion)
    );
}

#[test]
fn programs_parse_bind_and_report_their_errors() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = materialize(temporary.path(), CLAIMS);
    let program = temporary.path().join("foo.prog");
    fs::write(&program, "foo\n").unwrap();
    let program = program.to_str().unwrap();

    let run = krs(
        target.path(),
        &manifest,
        "run",
        &[program, "--output", "json"],
    );
    assert_eq!(run.status.code(), Some(0), "{}", stderr(&run));
    assert_eq!(json(&run)["run"]["steps"], 1);

    let missing = krs(target.path(), &manifest, "run", &[]);
    assert_eq!(missing.status.code(), Some(2));

    let unknown = krs(
        target.path(),
        &manifest,
        "run",
        &[program, "-c", "ENV=.Map"],
    );
    assert_eq!(unknown.status.code(), Some(1));
    assert!(
        stderr(&unknown).contains("unknown configuration variable `ENV`")
            && stderr(&unknown).contains("$PGM (init parameter pgm): ObjectTerm"),
        "{}",
        stderr(&unknown)
    );

    let parsed = krs(
        target.path(),
        &manifest,
        "parse",
        &[program, "--output", "json"],
    );
    assert_eq!(parsed.status.code(), Some(0), "{}", stderr(&parsed));
    assert_eq!(json(&parsed)["term"]["label"]["name"], "foo");

    let bad = temporary.path().join("bad.prog");
    fs::write(&bad, "fooo\n").unwrap();
    let rejected = krs(target.path(), &manifest, "parse", &[bad.to_str().unwrap()]);
    assert_eq!(rejected.status.code(), Some(1));
    assert!(
        stderr(&rejected).contains("bad.prog:1:4 does not parse at sort ObjectTerm"),
        "{}",
        stderr(&rejected)
    );

    let usage = krs(
        target.path(),
        &manifest,
        "run",
        &[program, "--max-solutions", "1"],
    );
    assert_eq!(usage.status.code(), Some(2));
    assert!(stderr(&usage).contains("--max-solutions does not apply to krs run"));
}
