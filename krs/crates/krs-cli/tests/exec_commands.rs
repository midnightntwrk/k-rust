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
        "[package]\nname = \"{PACKAGE}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nkrs = {{ path = {krs_literal} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-CLI-EXEC\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\n"
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
    // The default output prints the configuration through the grammar, as `krun --output pretty` does.
    assert_eq!(
        String::from_utf8_lossy(&human.stdout),
        "<k>\n  bar ~> .K\n</k>\n"
    );

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
    let program_text = krs(
        target.path(),
        &manifest,
        "parse",
        &[program, "--output", "program"],
    );
    assert_eq!(
        program_text.status.code(),
        Some(0),
        "{}",
        stderr(&program_text)
    );
    assert_eq!(String::from_utf8_lossy(&program_text.stdout), "foo\n");

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

/// One `krs run` against a private stage cache, returning its output and `stage.reused`.
fn krs_with_stage_cache(
    target: &Path,
    manifest: &Path,
    cache: &Path,
    counters: &Path,
    arguments: &[&str],
) -> (Output, u64) {
    let (output, document) = krs_counted(target, manifest, cache, counters, "run", arguments);
    let reused = document["counters"]["stage.reused"].as_u64().unwrap();
    (output, reused)
}

/// One successful `krs VERB` against a private stage cache, returning its output and its counters document.
fn krs_counted(
    target: &Path,
    manifest: &Path,
    cache: &Path,
    counters: &Path,
    verb: &str,
    arguments: &[&str],
) -> (Output, Value) {
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    process
        .env("KRS_STAGE_CACHE_DIR", cache)
        .env_remove("KRS_NO_REUSE")
        .current_dir(manifest.parent().unwrap())
        .arg(verb)
        .arg("--manifest-path")
        .arg(manifest)
        .args(["--package", PACKAGE, "--definition", "main", "--counters"])
        .arg(counters)
        .args(arguments);
    let output = process.output().unwrap();
    assert_eq!(output.status.code(), Some(0), "{}", stderr(&output));
    let document: Value = serde_json::from_slice(&fs::read(counters).unwrap()).unwrap();
    (output, document)
}

fn stage_entries(cache: &Path) -> Vec<PathBuf> {
    let Ok(shards) = fs::read_dir(cache.join("entries")) else {
        return Vec::new();
    };
    let mut entries = shards
        .flat_map(|shard| fs::read_dir(shard.unwrap().path()).unwrap())
        .map(|entry| entry.unwrap().path())
        .collect::<Vec<_>>();
    entries.sort();
    entries
}

#[test]
fn the_compiled_stage_is_reused_from_the_stage_cache_and_never_changes_a_result() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = materialize(temporary.path(), &tour_minimal());
    let cache = temporary.path().join("stage-cache");
    let counters = temporary.path().join("counters.json");
    let arguments = ["--trace", "--output", "json"];

    let (cold, reused) =
        krs_with_stage_cache(target.path(), &manifest, &cache, &counters, &arguments);
    assert_eq!(reused, 0);
    let entries = stage_entries(&cache);
    assert_eq!(entries.len(), 1, "one entry for one definition");

    let (warm, reused) =
        krs_with_stage_cache(target.path(), &manifest, &cache, &counters, &arguments);
    assert_eq!(reused, 1);
    assert_eq!(warm.stdout, cold.stdout);
    assert_eq!(warm.stderr, cold.stderr);
    // The restored stage keeps the authored trace origin.
    assert_eq!(
        json(&warm)["run"]["trace"][0]["origin"]["file"],
        "src/lib.rs"
    );

    // `--no-reuse` compiles again and stores the stage again.
    let mut no_reuse = arguments.to_vec();
    no_reuse.push("--no-reuse");
    let (fresh, reused) =
        krs_with_stage_cache(target.path(), &manifest, &cache, &counters, &no_reuse);
    assert_eq!(reused, 0);
    assert_eq!(fresh.stdout, cold.stdout);
    assert_eq!(stage_entries(&cache), entries);

    // A damaged entry is a miss, and the run replaces it.
    let mut bytes = fs::read(&entries[0]).unwrap();
    let last = bytes.len() - 1;
    bytes[last] ^= 0xff;
    fs::write(&entries[0], bytes).unwrap();
    let (repaired, reused) =
        krs_with_stage_cache(target.path(), &manifest, &cache, &counters, &arguments);
    assert_eq!(reused, 0);
    assert_eq!(repaired.stdout, cold.stdout);
    let (_, reused) = krs_with_stage_cache(target.path(), &manifest, &cache, &counters, &arguments);
    assert_eq!(reused, 1);

    // A store inside the input's Cargo workspace is never used, and each command says so.
    let inside = manifest.parent().unwrap().join("stage-cache");
    for _ in 0..2 {
        let (uncached, reused) =
            krs_with_stage_cache(target.path(), &manifest, &inside, &counters, &arguments);
        assert_eq!(reused, 0);
        assert_eq!(uncached.stdout, cold.stdout);
        let warning = stderr(&uncached);
        assert!(
            warning.contains("warning[krs::exec::stage-cache]")
                && warning.contains("KRS_STAGE_CACHE_DIR names `")
                && warning.contains("inside the Cargo workspace"),
            "{warning}"
        );
    }
    assert!(!inside.exists());
    // The warning is the only difference from a run with a usable store.
    assert!(!stderr(&cold).contains("krs::exec::stage-cache"));
}

/// The claims fixture plus an author spec module with one claim that holds.
const SPEC_MODULE: &str = r#"
#[krs::spec_module(name = "ORG-KRS-CLI-EXEC-AGAIN", imports = [crate])]
mod again {
    use crate::{Machine, Object};

    /// Holds, as `foo-reaches-bar` does.
    #[krs::claim(all_paths, label = "foo-reaches-bar-again")]
    fn foo_reaches_bar_again(
        krs::cells! {
            k: krs::configuration::KCell(Object::Foo(), tail @ ..),
            state @ ..
        }: Machine,
    ) -> Machine {
        krs::cells! {
            k: krs::configuration::KCell(Object::Bar(), ..tail),
            ..state
        }
    }
}
"#;

#[test]
fn the_spec_module_proof_definition_is_reused_from_the_stage_cache() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = materialize(temporary.path(), &format!("{CLAIMS}{SPEC_MODULE}"));
    let cache = temporary.path().join("stage-cache");
    let counters = temporary.path().join("counters.json");
    let arguments = [
        "--spec-module",
        "ORG-KRS-CLI-EXEC-AGAIN",
        "--output",
        "json",
    ];
    let reused = |document: &Value, counter: &str| document["counters"][counter].as_u64();

    // The first proof compiles and stores both the definition's stage and the spec module's.
    let (cold, document) = krs_counted(
        target.path(),
        &manifest,
        &cache,
        &counters,
        "prove",
        &arguments,
    );
    assert_eq!(reused(&document, "stage.reused"), Some(0));
    assert_eq!(reused(&document, "spec_stage.reused"), Some(0));
    assert_eq!(
        json(&cold)["prove"][0]["claim"],
        "ORG-KRS-CLI-EXEC-AGAIN.foo-reaches-bar-again"
    );
    assert_eq!(json(&cold)["prove"][0]["verdict"], "proven");
    let entries = stage_entries(&cache);
    assert_eq!(
        entries.len(),
        2,
        "the definition's stage and the spec module's"
    );

    // The second restores both, with the same report.
    let (warm, document) = krs_counted(
        target.path(),
        &manifest,
        &cache,
        &counters,
        "prove",
        &arguments,
    );
    assert_eq!(reused(&document, "stage.reused"), Some(1));
    assert_eq!(reused(&document, "spec_stage.reused"), Some(1));
    assert_eq!(warm.stdout, cold.stdout);
    assert_eq!(warm.stderr, cold.stderr);
    assert_eq!(stage_entries(&cache), entries);

    // A proof of the generated spec module loads no spec stage; it restores the definition's.
    let (_, document) = krs_counted(
        target.path(),
        &manifest,
        &cache,
        &counters,
        "prove",
        &["--claim", "foo-reaches-bar", "--output", "json"],
    );
    assert_eq!(reused(&document, "stage.reused"), Some(1));
    assert_eq!(reused(&document, "spec_stage.reused"), None);

    // `--no-reuse` compiles both again and replaces the entries.
    let mut no_reuse = arguments.to_vec();
    no_reuse.push("--no-reuse");
    let (fresh, document) = krs_counted(
        target.path(),
        &manifest,
        &cache,
        &counters,
        "prove",
        &no_reuse,
    );
    assert_eq!(reused(&document, "spec_stage.reused"), Some(0));
    assert_eq!(fresh.stdout, cold.stdout);
    assert_eq!(stage_entries(&cache), entries);
}

/// Two claims whose left-hand side is an or-pattern, `foo | bar`, which is a disjunction in K: one
/// backend claim per disjunct. `krs prove` proves each disjunct and reports the claim proven
/// only if every disjunct is (`either-reaches-bar`), with the weakest verdict otherwise
/// (`either-reaches-foo`: `bar` is stuck), beside the run's other claims.
#[test]
fn a_disjunctive_claim_is_proven_disjunct_by_disjunct() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let claim = |label: &str, function: &str, result: &str| {
        format!(
            r#"
    #[krs::claim(all_paths, label = "{label}")]
    fn {function}(
        krs::cells! {{
            k: krs::configuration::KCell(Object::Foo() | Object::Bar(), tail @ ..),
            state @ ..
        }}: Machine,
    ) -> Machine {{
        krs::cells! {{
            k: krs::configuration::KCell(Object::{result}(), ..tail),
            ..state
        }}
    }}
"#
        )
    };
    let end = CLAIMS.rfind('}').unwrap();
    let source = format!(
        "{}{}{}}}\n",
        &CLAIMS[..end],
        claim("either-reaches-bar", "either_reaches_bar", "Bar"),
        claim("either-reaches-foo", "either_reaches_foo", "Foo"),
    );
    let manifest = materialize(temporary.path(), &source);

    let prove = krs(target.path(), &manifest, "prove", &["--output", "json"]);
    assert_eq!(prove.status.code(), Some(1), "{}", stderr(&prove));
    let verdicts = json(&prove)["prove"]
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
            ("bar-reaches-foo", "disproved"),
            ("either-reaches-bar", "proven"),
            ("either-reaches-foo", "disproved"),
            ("foo-reaches-bar", "proven"),
        ]
        .map(|(claim, verdict)| (format!("ORG-KRS-CLI-EXEC-SPEC.{claim}"), verdict.to_owned()))
    );
}
