//! The killer record (`run --lock FILE`, README "The killer record"): one recorded killer per
//! killed mutation, kept while it still kills and is in the corpus, else the first killing program
//! in the search's order; written after a run that judged the whole list, compared under
//! `--locked`, and refused when it does not decode.
//!
//! Every run here is on a private copy of `testdata/flow/calc` with `[budget] time_ms` far above
//! any run's time, so no row depends on the clock. Statuses are always the ones a run without a
//! lock gives: the record orders the work and names the killer, never a status.

mod flow_support;

use kink_campaign::ScheduleMode;
use kink_flow::{
    FlowManifest, MutationList,
    cli::{EXIT_NO, EXIT_UNASKED, EXIT_YES, run_mode},
    lock::Lock,
    memo::MemoUse,
    results::CACHE_DIRECTORY,
    search::{RunMode, RunOptions, run, run_with},
    verdicts::{lock_text, verdicts},
};
use serde_json::{Value, json};
use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

fn flow(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../testdata/flow")
        .join(name)
}

/// A fresh directory for one test, under the target's temporary directory.
fn scratch(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-lock-{}", std::process::id()))
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

fn copy_dir(from: &Path, to: &Path) {
    fs::create_dir_all(to).unwrap();
    for entry in fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        if entry.file_name() == CACHE_DIRECTORY {
            continue;
        }
        if entry.file_type().unwrap().is_dir() {
            copy_dir(&entry.path(), &to.join(entry.file_name()));
        } else {
            fs::copy(entry.path(), to.join(entry.file_name())).unwrap();
        }
    }
}

/// The program entries of calc and of its unparsable program, by id.
fn program(id: &str) -> String {
    match id {
        "inline" => "[[program]]\nid = \"inline\"\ntext = \"2 * 3 + 1\"\n".to_owned(),
        id => format!("[[program]]\nid = \"{id}\"\nfile = \"programs/{id}.calc\"\n"),
    }
}

/// A private copy of calc whose manifest lists `programs` in that order, with a time bound far
/// above any run's time; its `FLOW.toml`.
fn calc(test: &str, programs: &[&str]) -> PathBuf {
    let dir = scratch(test).join("calc");
    copy_dir(&flow("calc"), &dir);
    let manifest = dir.join("FLOW.toml");
    write_manifest(&manifest, programs);
    manifest
}

/// Rewrite the calc manifest at `manifest` to list `programs`.
fn write_manifest(manifest: &Path, programs: &[&str]) {
    let mut text = "[spec]\nentry = \"calc.k\"\nmain_module = \"CALC\"\nsyntax_module = \
                    \"CALC-SYNTAX\"\n\n[budget]\ntime_ms = 600000\n"
        .to_owned();
    for id in programs {
        text.push('\n');
        text.push_str(&program(id));
    }
    fs::write(manifest, text).unwrap();
}

const CALC: [&str; 4] = ["add", "nested", "sub", "inline"];

fn options(lock: Option<&Path>) -> RunOptions {
    RunOptions {
        compile_workers: Some(1),
        lock: lock.map(Path::to_path_buf),
        ..RunOptions::default()
    }
}

/// `kink-flow run` through the library with `options`, in `mode`.
fn run_as(manifest: &Path, list: &str, options: &RunOptions, mode: RunMode) -> (Value, bool) {
    let flow = FlowManifest::read(manifest).unwrap();
    let list = MutationList::read(&manifest.with_file_name(list)).unwrap();
    run_with(&flow, &list, options, mode)
}

/// A first-kill run of calc's `MUTATIONS.toml` with the lock beside the manifest.
fn locked_run(manifest: &Path) -> Value {
    let lock = lock_of(manifest);
    let (document, ok) = run_as(
        manifest,
        "MUTATIONS.toml",
        &options(Some(&lock)),
        RunMode::Search,
    );
    assert!(ok, "{document:#}");
    document
}

fn lock_of(manifest: &Path) -> PathBuf {
    manifest.with_file_name("kink.lock")
}

fn row<'d>(document: &'d Value, id: &str) -> &'d Value {
    document["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["id"] == id)
        .unwrap_or_else(|| panic!("no row {id}: {document:#}"))
}

/// The programs of each call of a row.
fn calls(document: &Value, id: &str) -> Vec<Vec<String>> {
    row(document, id)["calls"]
        .as_array()
        .unwrap()
        .iter()
        .map(|call| {
            call["programs"]
                .as_array()
                .unwrap()
                .iter()
                .map(|p| p.as_str().unwrap().to_owned())
                .collect()
        })
        .collect()
}

/// `(id, status)` of every row.
fn statuses(document: &Value) -> Vec<(String, String)> {
    document["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .map(|row| {
            (
                row["id"].as_str().unwrap().to_owned(),
                row["status"].as_str().unwrap().to_owned(),
            )
        })
        .collect()
}

/// A lock that records `killers` (mutation id, program id) and nothing else.
fn lock_with(killers: &[(&str, &str)]) -> String {
    let mut text = format!(
        "{}\n[run]\nversion = {}\n",
        kink_flow::verdicts::record_header(None),
        kink_flow::verdicts::VERDICTS_VERSION
    );
    for (id, killer) in killers {
        text.push_str(&format!(
            "\n[[run.mutation]]\nid = \"{id}\"\nstatus = \"killed\"\nkiller = \"{killer}\"\n"
        ));
    }
    text
}

/// The first member of a full row's `killed_by` that witnesses the edit (its `witnesses`), else
/// its first: the first killer in the search's order.
fn first_in_search_order(full: &Value, id: &str) -> Value {
    let row = row(full, id);
    let killed_by = row["killed_by"].as_array().unwrap();
    let witnesses = row["witnesses"].as_array().unwrap();
    killed_by
        .iter()
        .find(|program| witnesses.contains(program))
        .or_else(|| killed_by.first())
        .cloned()
        .unwrap_or(Value::Null)
}

/// `kink-flow run FLOW.toml MUTATIONS.toml ARGS` through the binary, in the manifest's directory.
fn binary(manifest: &Path, args: &[&str]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_kink-flow"))
        .arg("run")
        .arg(manifest)
        .arg(manifest.with_file_name("MUTATIONS.toml"))
        .args(args)
        .current_dir(manifest.parent().unwrap())
        .output()
        .unwrap()
}

/// The parser: `--lock FILE` once, `--locked` once and only with `--lock`.
#[test]
fn the_lock_options_parse() {
    let files = || kink_flow::CommandFiles {
        mutations: Some(flow("calc").join("MUTATIONS.toml")),
        ..kink_flow::CommandFiles::default()
    };
    let parse = |args: &[&str]| {
        kink_flow::FlowCommand::parse(
            "run",
            files(),
            &args.iter().map(|a| (*a).to_owned()).collect::<Vec<_>>(),
        )
    };
    let kink_flow::FlowCommand::Run { options, .. } =
        parse(&["--locked", "--lock", "kink.lock"]).unwrap()
    else {
        panic!("run");
    };
    assert_eq!(
        (options.lock, options.locked),
        (Some(PathBuf::from("kink.lock")), true)
    );
    assert_eq!(
        parse(&["--locked"]).unwrap_err(),
        "--locked compares the run with its lock: give --lock FILE"
    );
    assert_eq!(
        parse(&["--lock", "a", "--lock", "b"]).unwrap_err(),
        "--lock specified more than once"
    );
    assert_eq!(parse(&["--lock"]).unwrap_err(), "--lock needs a file");
}

/// A run refused before its lock is read, its manifest or its mutation list not decoding, still
/// names the lock it left unwritten (reason `refused`), and leaves the file as it was; without
/// `--lock` its `lock` is null.
#[test]
fn a_run_refused_before_its_lock_names_the_lock_it_left_unwritten() {
    let manifest = calc("refused-inputs", &CALC);
    let lock = lock_of(&manifest);
    fs::write(&lock, "# kept\n").unwrap();
    let list = manifest.with_file_name("BROKEN.toml");
    fs::write(&list, "[[mutation]\n").unwrap();
    let broken = manifest.with_file_name("BROKEN-FLOW.toml");
    fs::write(&broken, "[spec\n").unwrap();
    let expected = json!({
        "path": lock.display().to_string(),
        "status": "not-written",
        "reason": "refused",
        "header": false,
        "header_changes": [],
        "changes": [],
        "difference": null,
        "clock_stopped": [],
        "kept": [],
    });
    for (flow, mutations) in [
        (&manifest, &list),
        (&broken, &manifest.with_file_name("MUTATIONS.toml")),
    ] {
        let (document, status) = kink_flow::cli::run(flow, mutations, &options(Some(&lock)));
        assert_eq!(status, EXIT_UNASKED, "{document:#}");
        assert_eq!(document["lock"], expected, "{document:#}");
        let (document, _) = kink_flow::cli::run(flow, mutations, &options(None));
        assert_eq!(document["lock"], Value::Null, "{document:#}");
    }
    assert_eq!(fs::read_to_string(&lock).unwrap(), "# kept\n");
}

/// A lock that does not decode refuses the run before admission: not TOML, another schema or
/// document, a repeated id, or a killer that is not a string. Exit 2, `lock.outcome` refused, the
/// rendering's `[lock]` section, no row, and the file is left as it was.
#[test]
fn an_unreadable_lock_refuses_the_run() {
    let manifest = calc("unreadable", &CALC);
    let lock = lock_of(&manifest);
    let header = "schema = \"kink-flow-verdicts\"\ndocument = \"run\"\n";
    for (text, what) in [
        ("<<<<<<< HEAD\nkiller = \"t1\"\n", "is not TOML"),
        (
            "schema = \"kink-flow-run\"\ndocument = \"run\"\n",
            "its schema is not",
        ),
        (
            "schema = \"kink-flow-verdicts\"\ndocument = \"results\"\n",
            "whose document is \"results\", not \"run\"",
        ),
        (
            "schema = \"kink-flow-verdicts\"\nrun = 3\n",
            "its run is not a table",
        ),
        (
            "schema = \"kink-flow-verdicts\"\n[ run ]\nversion = 25\n",
            "its run section does not begin with a line `[run]`",
        ),
        (
            &format!("{header}\n[[mutation]]\nid = \"no-mul\"\n\n[[mutation]]\nid = \"no-mul\"\n"),
            "the mutation \"no-mul\" is listed twice",
        ),
        (
            &format!("{header}\n[[mutation]]\nid = \"no-mul\"\nkiller = 3\n"),
            "the killer of \"no-mul\" is not a string",
        ),
    ] {
        fs::write(&lock, text).unwrap();
        let (document, status) = run_mode(
            &manifest,
            &manifest.with_file_name("MUTATIONS.toml"),
            &options(Some(&lock)),
            RunMode::Search,
        );
        assert_eq!(status, EXIT_UNASKED, "{what}: {document:#}");
        assert_eq!(document["lock"]["outcome"], "refused", "{what}");
        let detail = document["lock"]["detail"].as_str().unwrap();
        assert!(detail.contains(what), "{detail}");
        assert!(
            detail.ends_with("resolve the file, or delete it to start from the search's killers"),
            "{detail}"
        );
        assert!(document.get("mutations").is_none(), "{what}");
        assert!(document.get("spec").is_none(), "{what}");
        let rendering = verdicts(&document).unwrap();
        assert!(
            rendering.ends_with("\n[run.lock]\noutcome = \"refused\"\n"),
            "{rendering}"
        );
        assert_eq!(fs::read_to_string(&lock).unwrap(), text);
    }
}

/// Under `--locked`, a lock of another version of the rendering refuses the run before
/// admission, exit 2, naming the command that rewrites it without `--locked` (as `kink-flow`
/// spells it); the file is left as it was. Without `--locked` the same lock is read for its
/// killers, which a run tries first.
#[test]
fn a_lock_of_another_version_refuses_a_locked_run() {
    let manifest = calc("other-version", &CALC);
    let lock = lock_of(&manifest);
    let text = "schema = \"kink-flow-verdicts\"\nversion = 23\ndocument = \"run\"\n\n\
                [[mutation]]\nid = \"add-becomes-sub\"\nstatus = \"killed\"\nkiller = \"add\"\n";
    fs::write(&lock, text).unwrap();
    let locked = RunOptions {
        locked: true,
        ..options(Some(&lock))
    };
    let (document, status) = run_mode(
        &manifest,
        &manifest.with_file_name("MUTATIONS.toml"),
        &locked,
        RunMode::Search,
    );
    assert_eq!(status, EXIT_UNASKED, "{document:#}");
    assert_eq!(document["lock"]["outcome"], "refused", "{document:#}");
    assert_eq!(
        document["lock"]["detail"],
        format!(
            "{}: it is recorded at version 23 of the verdicts rendering, and this build writes \
             version {}, so --locked cannot find it current; run `kink-flow run` without \
             --locked once to rewrite it, and review its diff",
            lock.display(),
            kink_flow::verdicts::VERDICTS_VERSION
        )
    );
    assert!(document.get("mutations").is_none(), "{document:#}");
    assert_eq!(fs::read_to_string(&lock).unwrap(), text);
    let read = Lock::read(&lock).unwrap();
    assert_eq!(read.killers()["add-becomes-sub"], "add");
}

/// `Lock::read`: an absent file is an empty record; a version-5 lock (no `killer` lines) records
/// no killer; only `id` and `killer` decide anything.
#[test]
fn a_version_5_lock_records_no_killer() {
    let dir = scratch("version-5");
    let absent = Lock::read(&dir.join("kink.lock")).unwrap();
    assert_eq!((absent.text, absent.rows.len()), (None, 0));
    let path = dir.join("old.lock");
    fs::write(
        &path,
        "schema = \"kink-flow-verdicts\"\nversion = 5\ndocument = \"run\"\nschedule = \
         \"first-kill\"\nprofile = \"no-z3\"\n\n[spec]\noutcome = \"admitted\"\n\n[[mutation]]\nid = \
         \"add-becomes-sub\"\nstatus = \"killed\"\n\n[[mutation]]\nid = \"add-swaps-operands\"\n\
         status = \"survived\"\n",
    )
    .unwrap();
    let old = Lock::read(&path).unwrap();
    assert_eq!(old.rows.len(), 2);
    assert!(old.killers().is_empty());
    assert_eq!(old.rows[0].status.as_deref(), Some("killed"));
}

mod kink_tier {
    use super::*;

    /// CF-23 §3.3's example inverted: corpus `[nested, inline]` records `nested` as the killer of
    /// `add-becomes-sub`; with `add`, also a killer and first in the search's order, prepended,
    /// the killer stays `nested`, warm (no call) and cold (one call over `nested`), and the lock
    /// does not move.
    #[test]
    #[ignore = "kink"]
    fn the_recorded_killer_survives_a_prepended_killer() {
        let manifest = calc("prepended", &["nested", "inline"]);
        let first = locked_run(&manifest);
        assert_eq!(row(&first, "add-becomes-sub")["killer"], "nested");
        assert_eq!(first["lock"]["status"], "created");
        let recorded = fs::read_to_string(lock_of(&manifest)).unwrap();
        write_manifest(&manifest, &["add", "nested", "inline"]);
        let warm = locked_run(&manifest);
        let killed = row(&warm, "add-becomes-sub");
        assert_eq!(
            (
                &killed["killer"],
                &killed["killer_source"],
                &killed["killer_change"]
            ),
            (&json!("nested"), &json!("outcome-cache"), &Value::Null)
        );
        assert!(calls(&warm, "add-becomes-sub").is_empty());
        assert_eq!(warm["lock"]["status"], "unchanged");
        assert_eq!(fs::read_to_string(lock_of(&manifest)).unwrap(), recorded);
        // Cold, with the same lock: the recorded killer alone.
        let cold = calc("prepended-cold", &["add", "nested", "inline"]);
        fs::write(lock_of(&cold), &recorded).unwrap();
        let document = locked_run(&cold);
        let killed = row(&document, "add-becomes-sub");
        assert_eq!(
            (&killed["killer"], &killed["killer_source"]),
            (&json!("nested"), &json!("record"))
        );
        assert_eq!(calls(&document, "add-becomes-sub"), [["nested"]]);
        assert_eq!(fs::read_to_string(lock_of(&cold)).unwrap(), recorded);
    }

    /// With no record (an absent lock, or one with no killer), each killer is the first killing
    /// program in the search's order, which is the first member of `--full`'s `killed_by` that
    /// witnesses the edit: cold, warm, without the memos, and with 1 and 4 compile workers, the
    /// lock is byte-equal.
    #[test]
    #[ignore = "kink"]
    fn without_a_record_the_killer_is_the_search_first() {
        let full_manifest = calc("canonical-full", &CALC);
        let (full, ok) = run_as(
            &full_manifest,
            "MUTATIONS.toml",
            &RunOptions {
                schedule: ScheduleMode::Full,
                ..options(None)
            },
            RunMode::Search,
        );
        assert!(ok, "{full:#}");
        let manifest = calc("canonical", &CALC);
        let cold = locked_run(&manifest);
        for (id, status) in statuses(&cold) {
            let row = row(&cold, &id);
            assert_eq!(row["recorded_killer"], Value::Null, "{id}");
            if status == "killed" {
                assert_eq!(row["killer"], first_in_search_order(&full, &id), "{id}");
                assert_eq!(row["killer_change"], "no-record", "{id}");
            } else {
                assert_eq!(row["killer_change"], Value::Null, "{id}");
            }
        }
        assert_eq!(statuses(&cold), statuses(&full));
        let recorded = fs::read_to_string(lock_of(&manifest)).unwrap();
        assert_eq!(recorded, lock_text(&cold).unwrap());
        // Warm: tier 1 decides every row from the canonical prefix the cold run cached.
        let warm = locked_run(&manifest);
        assert_eq!(warm["lock"]["status"], "unchanged");
        // An empty lock, without the memos, and each worker count, each from a fresh cache.
        for (test, memo, workers) in [
            ("canonical-no-memo", MemoUse::Off, 1),
            ("canonical-workers", MemoUse::On, 4),
        ] {
            let other = calc(test, &CALC);
            fs::write(lock_of(&other), lock_with(&[])).unwrap();
            let (document, ok) = run_as(
                &other,
                "MUTATIONS.toml",
                &RunOptions {
                    memo,
                    compile_workers: Some(workers),
                    ..options(Some(&lock_of(&other)))
                },
                RunMode::Search,
            );
            assert!(ok, "{document:#}");
            assert_eq!(document["lock"]["status"], "written", "{test}");
            assert_eq!(
                fs::read_to_string(lock_of(&other)).unwrap(),
                recorded,
                "{test}"
            );
        }
    }

    /// A recorded killer that agrees: it runs alone, then the canonical call decides, the killer
    /// is the search's first, and the rewritten lock shows it.
    #[test]
    #[ignore = "kink"]
    fn a_recorded_killer_that_agrees_is_replaced() {
        let manifest = calc("agrees", &CALC);
        fs::write(lock_of(&manifest), lock_with(&[("add-becomes-sub", "sub")])).unwrap();
        let document = locked_run(&manifest);
        assert_eq!(
            calls(&document, "add-becomes-sub"),
            [vec!["sub"], vec!["add", "nested", "inline", "sub"]]
        );
        let killed = row(&document, "add-becomes-sub");
        assert_eq!(
            (
                &killed["killer"],
                &killed["recorded_killer"],
                &killed["killer_change"],
                &killed["killer_source"]
            ),
            (
                &json!("add"),
                &json!("sub"),
                &json!("no-longer-kills"),
                &json!("search")
            )
        );
        assert_eq!(document["lock"]["status"], "written");
        assert!(
            fs::read_to_string(lock_of(&manifest))
                .unwrap()
                .contains("id = \"add-becomes-sub\"\nstatus = \"killed\"\nkiller = \"add\"\n")
        );
    }

    /// A recorded killer that is no program of the corpus is `not-in-corpus`; one whose class is
    /// not comparable is `not-comparable`, reported as the row's `unusable_killer` with source
    /// `record`. Neither runs, and each killer is the search's first.
    #[test]
    #[ignore = "kink"]
    fn a_recorded_killer_outside_the_corpus_or_not_comparable() {
        let manifest = calc("outside", &["add", "bad", "nested", "sub", "inline"]);
        let lock = lock_of(&manifest);
        fs::write(
            &lock,
            lock_with(&[("add-becomes-sub", "gone"), ("no-mul", "bad")]),
        )
        .unwrap();
        // The unparsable program is refused, which the run reports beside the verdicts.
        let (document, _) = run_as(
            &manifest,
            "MUTATIONS.toml",
            &options(Some(&lock)),
            RunMode::Search,
        );
        let gone = row(&document, "add-becomes-sub");
        assert_eq!(
            (
                &gone["killer"],
                &gone["killer_change"],
                &gone["unusable_killer"]
            ),
            (&json!("add"), &json!("not-in-corpus"), &Value::Null)
        );
        assert_eq!(
            calls(&document, "add-becomes-sub"),
            [["add", "nested", "inline", "sub"]]
        );
        let bad = row(&document, "no-mul");
        assert_eq!(bad["killer_change"], "not-comparable");
        assert_eq!(bad["unusable_killer"]["program"], "bad");
        assert_eq!(bad["unusable_killer"]["source"], "record");
        assert_eq!(bad["unusable_killer"]["class"], "refused");
        assert_eq!(bad["killer"], "nested");
    }

    /// A recorded killer of a mutation decided before any program ran: `not-run`.
    #[test]
    #[ignore = "kink"]
    fn a_recorded_killer_of_a_mutation_decided_before_any_run() {
        let manifest = calc("before-any-run", &CALC);
        let lock = lock_of(&manifest);
        fs::write(
            &lock,
            lock_with(&[("no-such-rule", "add"), ("add-unbound", "add")]),
        )
        .unwrap();
        let (document, _) = run_as(
            &manifest,
            "MUTATIONS-statuses.toml",
            &options(Some(&lock)),
            RunMode::Search,
        );
        for (id, status) in [
            ("no-such-rule", "invalid-mutation"),
            ("add-unbound", "not-admitted"),
        ] {
            let refused = row(&document, id);
            assert_eq!(refused["status"], status, "{id}");
            assert_eq!(
                (&refused["recorded_killer"], &refused["killer_change"]),
                (&json!("add"), &json!("not-run")),
                "{id}"
            );
        }
    }

    /// A full run and a first-kill run write the same lock, and a full row's `killer` is the
    /// recorded one even where it is not the first of `killed_by`.
    #[test]
    #[ignore = "kink"]
    fn full_and_first_kill_write_one_lock() {
        let manifest = calc("one-lock", &CALC);
        let lock = lock_of(&manifest);
        fs::write(&lock, lock_with(&[("add-becomes-sub", "nested")])).unwrap();
        let first = locked_run(&manifest);
        assert_eq!(row(&first, "add-becomes-sub")["killer"], "nested");
        let recorded = fs::read_to_string(&lock).unwrap();
        let (full, status) = run_mode(
            &manifest,
            &manifest.with_file_name("MUTATIONS.toml"),
            &RunOptions {
                schedule: ScheduleMode::Full,
                locked: true,
                ..options(Some(&lock))
            },
            RunMode::Search,
        );
        assert_eq!(status, EXIT_YES, "{full:#}");
        assert_eq!(full["lock"]["status"], "unchanged");
        let killed = row(&full, "add-becomes-sub");
        assert_eq!(
            (&killed["killer"], &killed["killed_by"]),
            (&json!("nested"), &json!(["add", "nested", "inline"]))
        );
        assert_eq!(lock_text(&full).unwrap(), recorded);
        assert_eq!(statuses(&full), statuses(&first));
        // For a first-kill run the rendering is the lock.
        assert_eq!(verdicts(&first).unwrap(), recorded);
    }

    /// The lock is written only after a run that judged the whole list: under `--only` (which
    /// still tries the recorded killer first), `--verify`, and a run a corpus error stopped, the
    /// file is left as it was.
    #[test]
    #[ignore = "kink"]
    fn the_lock_is_written_only_after_a_complete_run() {
        let manifest = calc("complete", &CALC);
        let lock = lock_of(&manifest);
        let text = lock_with(&[("add-becomes-sub", "nested")]);
        fs::write(&lock, &text).unwrap();
        let (only, ok) = run_as(
            &manifest,
            "MUTATIONS.toml",
            &RunOptions {
                only: vec!["add-becomes-sub".to_owned()],
                ..options(Some(&lock))
            },
            RunMode::Search,
        );
        assert!(ok, "{only:#}");
        assert_eq!(
            (&only["lock"]["status"], &only["lock"]["reason"]),
            (&json!("not-written"), &json!("only"))
        );
        assert_eq!(calls(&only, "add-becomes-sub"), [["nested"]]);
        assert_eq!(row(&only, "add-becomes-sub")["killer_source"], "record");
        assert_eq!(fs::read_to_string(&lock).unwrap(), text);
        let (verified, ok) = run_as(
            &manifest,
            "MUTATIONS.toml",
            &options(Some(&lock)),
            RunMode::Verify,
        );
        assert!(ok, "{verified:#}");
        assert_eq!(verified["lock"]["reason"], "verify");
        assert_eq!(row(&verified, "add-becomes-sub")["killer"], "nested");
        assert_eq!(fs::read_to_string(&lock).unwrap(), text);
        // A forged baseline run digest: the first call's drift check stops the run.
        let results = manifest
            .parent()
            .unwrap()
            .join(CACHE_DIRECTORY)
            .join("results");
        for entry in walk(&results) {
            let mut record: Value =
                serde_json::from_str(&fs::read_to_string(&entry).unwrap()).unwrap();
            record["run_sha256"] = json!("0".repeat(64));
            fs::write(&entry, record.to_string()).unwrap();
        }
        let _ = fs::remove_dir_all(
            manifest
                .parent()
                .unwrap()
                .join(CACHE_DIRECTORY)
                .join("outcomes"),
        );
        let (stopped, ok) = run_as(
            &manifest,
            "MUTATIONS.toml",
            &options(Some(&lock)),
            RunMode::Search,
        );
        assert!(!ok);
        assert!(stopped["stopped"].is_object(), "{stopped:#}");
        assert_eq!(stopped["lock"]["reason"], "stopped");
        assert_eq!(fs::read_to_string(&lock).unwrap(), text);
    }

    /// Every file under `dir`.
    fn walk(dir: &Path) -> Vec<PathBuf> {
        let mut files = Vec::new();
        for entry in fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                files.extend(walk(&path));
            } else {
                files.push(path);
            }
        }
        files
    }

    /// `--locked` writes nothing: an unchanged lock gives the statuses' exit; a lock the run
    /// would change, or an absent one, is a finding (exit 1, `stale`, its `changes`), and the
    /// binary names each change on stderr. A lock recorded on another Z3 build is a finding with
    /// every row agreeing, its header's differing keys named (`header_changes`).
    #[test]
    #[ignore = "kink"]
    fn locked() {
        let manifest = calc("locked", &CALC);
        let lock = lock_of(&manifest);
        let locked = || RunOptions {
            locked: true,
            ..options(Some(&lock))
        };
        let mutations = manifest.with_file_name("MUTATIONS.toml");
        let (absent, status) = run_mode(&manifest, &mutations, &locked(), RunMode::Search);
        assert_eq!(status, EXIT_NO, "{absent:#}");
        assert_eq!(absent["lock"]["status"], "stale");
        assert_eq!(absent["lock"]["header"], true);
        assert!(!lock.exists());
        let (written, status) = run_mode(
            &manifest,
            &mutations,
            &options(Some(&lock)),
            RunMode::Search,
        );
        assert_eq!(status, EXIT_YES, "{written:#}");
        let recorded = fs::read_to_string(&lock).unwrap();
        let (unchanged, status) = run_mode(&manifest, &mutations, &locked(), RunMode::Search);
        assert_eq!(status, EXIT_YES, "{unchanged:#}");
        assert_eq!(
            (&unchanged["lock"]["status"], &unchanged["lock"]["changes"]),
            (&json!("unchanged"), &json!([]))
        );
        // A hand-edited killer and a status the run would change.
        let edited = recorded
            .replace(
                "id = \"add-becomes-sub\"\nstatus = \"killed\"\nkiller = \"add\"",
                "id = \"add-becomes-sub\"\nstatus = \"killed\"\nkiller = \"gone\"",
            )
            .replace(
                "id = \"add-swaps-operands\"\nstatus = \"survived\"",
                "id = \"add-swaps-operands\"\nstatus = \"killed\"\nkiller = \"add\"",
            );
        assert_ne!(edited, recorded);
        fs::write(&lock, &edited).unwrap();
        let (stale, status) = run_mode(&manifest, &mutations, &locked(), RunMode::Search);
        assert_eq!(status, EXIT_NO, "{stale:#}");
        assert_eq!(stale["lock"]["status"], "stale");
        let changed = stale["lock"]["changes"]
            .as_array()
            .unwrap()
            .iter()
            .map(|change| change["mutation"].as_str().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(changed, ["add-becomes-sub", "add-swaps-operands"]);
        assert_eq!(fs::read_to_string(&lock).unwrap(), edited);
        let output = binary(&manifest, &["--lock", "kink.lock", "--locked"]);
        assert_eq!(output.status.code(), Some(i32::from(EXIT_NO)));
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(
            stderr.contains("kink.lock: add-becomes-sub: killer gone -> add (gone: not-in-corpus)"),
            "{stderr}"
        );
        assert!(
            stderr.contains("kink.lock: add-swaps-operands: killed -> survived"),
            "{stderr}"
        );
        // The recorded rows under another Z3 build's header: every verdict agrees, and it is
        // still a finding, each header key that differs named.
        let zeros = "0".repeat(64);
        let foreign = recorded.replacen(
            &flow_support::solver_lines(),
            &format!(
                "profile = \"z3\"\nz3_version = \"5.3.3.0 other\"\nz3_library_sha256 = \"{zeros}\"\n"
            ),
            1,
        );
        assert_ne!(foreign, recorded);
        fs::write(&lock, &foreign).unwrap();
        let output = binary(&manifest, &["--lock", "kink.lock", "--locked"]);
        assert_eq!(output.status.code(), Some(i32::from(EXIT_NO)));
        let document: Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(document["version"], 41);
        assert_eq!(
            (&document["lock"]["status"], &document["lock"]["header"]),
            (&json!("stale"), &json!(true))
        );
        assert_eq!(document["lock"]["changes"], json!([]), "{document:#}");
        let header_changes = &document["lock"]["header_changes"];
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(
            stderr
                .contains("kink.lock: [run] z3_version differs: recorded \"5.3.3.0 other\", now ")
                && stderr.contains("(another Z3 build)"),
            "{stderr}"
        );
        if cfg!(feature = "z3") {
            let build = k_rust::backend::z3_build().unwrap();
            let digest = build
                .library_sha256
                .clone()
                .expect("this build names its Z3 library");
            assert_eq!(
                *header_changes,
                json!([
                    {"key": "z3_version", "recorded": "5.3.3.0 other", "now": build.version},
                    {"key": "z3_library_sha256", "recorded": zeros, "now": digest},
                ])
            );
            assert!(
                stderr.contains(&format!(
                    "kink.lock: [run] z3_library_sha256 differs: recorded \"{zeros}\", \
                     now \"{digest}\" (another Z3 build)"
                )),
                "{stderr}"
            );
        } else {
            assert_eq!(
                *header_changes,
                json!([
                    {"key": "profile", "recorded": "z3", "now": "no-z3"},
                    {"key": "z3_library_sha256", "recorded": zeros, "now": null},
                    {"key": "z3_version", "recorded": "5.3.3.0 other", "now": null},
                ])
            );
        }
        assert_eq!(fs::read_to_string(&lock).unwrap(), foreign);
    }

    /// The library's default options name no lock: a run writes nothing beside the manifest.
    #[test]
    #[ignore = "kink"]
    fn a_library_run_writes_nothing_beside_the_manifest() {
        let manifest = calc("library", &CALC);
        let dir = manifest.parent().unwrap().to_path_buf();
        let before = fs::read_dir(&dir)
            .unwrap()
            .map(|entry| entry.unwrap().file_name())
            .collect::<std::collections::BTreeSet<_>>();
        let flow = FlowManifest::read(&manifest).unwrap();
        let list = MutationList::read(&manifest.with_file_name("MUTATIONS.toml")).unwrap();
        let (document, ok) = run(&flow, &list, &RunOptions::default());
        assert!(ok, "{document:#}");
        assert_eq!(document["lock"], Value::Null);
        let after = fs::read_dir(&dir)
            .unwrap()
            .map(|entry| entry.unwrap().file_name())
            .filter(|name| name != CACHE_DIRECTORY)
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(after, before);
    }
}

/// FB45-LOCKED-TIMEOUT: a run `budget.time_ms` cancelled changes no recorded status, killer or
/// lock entry. On the loop fixture under `time_ms = 500`, `countdown-escapes` makes
/// `countdown(3)` loop for ever and `countdown(1)` end at `countdown(-1)`, and `spin(0)` never
/// ends on the baseline: the clock stops those runs on every host, so the outcome of each test is
/// deterministic, while the lock entries these tests record by hand stand for what a host that
/// finished the runs would have recorded.
mod clock {
    use super::*;
    use kink_flow::{
        CommandFiles, EditAction, EditSpec, FlowCommand, FrontEnd,
        cli::{EXIT_UNANSWERED, dispatch},
        flips::{Derived, DerivedEntry, DerivedList, Judged, Occurrence, Reach},
    };
    use kink_patch::SentenceRef;

    /// A private copy of the loop fixture whose manifest lists `programs` (`(id, text)`) under a
    /// 500 ms clock; its `FLOW.toml`.
    fn looping(test: &str, programs: &[(&str, &str)]) -> PathBuf {
        let dir = scratch(test).join("loop");
        copy_dir(&flow("loop"), &dir);
        // A work budget so large that the clock fires first (FB45-KINK): these runs test the
        // clock's path.
        let mut text = "[spec]\nentry = \"loop.k\"\nmain_module = \"LOOP\"\nsyntax_module = \
                        \"LOOP-SYNTAX\"\n\n[budget]\ntime_ms = 500\nmax_depth = 1000000000\n\
                        work_factor = 1000000000000\n"
            .to_owned();
        for (id, program) in programs {
            text.push_str(&format!(
                "\n[[program]]\nid = \"{id}\"\ntext = \"{program}\"\n"
            ));
        }
        let manifest = dir.join("FLOW.toml");
        fs::write(&manifest, text).unwrap();
        manifest
    }

    fn run_status(manifest: &Path, locked: bool) -> (Value, u8) {
        let lock = lock_of(manifest);
        let options = RunOptions {
            locked,
            ..options(Some(&lock))
        };
        run_mode(
            manifest,
            &manifest.with_file_name("MUTATIONS.toml"),
            &options,
            RunMode::Search,
        )
    }

    /// The lock's text with `countdown-escapes`'s row replaced by `row` (its lines after `id`).
    fn with_row(text: &str, row: &str) -> String {
        let start = text
            .find("id = \"countdown-escapes\"\n")
            .expect("the lock has the row");
        let start = start + "id = \"countdown-escapes\"\n".len();
        let end = text[start..]
            .find("\n[")
            .map_or(text.len(), |at| start + at + 1);
        format!("{}{row}{}", &text[..start], &text[end..])
    }

    fn stopped(document: &Value) -> Vec<(String, String)> {
        document["lock"]["clock_stopped"]
            .as_array()
            .unwrap_or_else(|| panic!("no clock_stopped: {:#}", document["lock"]))
            .iter()
            .map(|stop| {
                (
                    stop["program"].as_str().unwrap().to_owned(),
                    stop["run"].as_str().unwrap().to_owned(),
                )
            })
            .collect()
    }

    /// A recorded killer whose run on the mutant the clock stopped is kept, unverified: under
    /// `--locked` the entry is not decided on this host (exit 3), not a difference (exit 1), and
    /// without it the lock keeps the killer. A recorded survivor that a program which finished
    /// kills is a difference: a kill is a function of the inputs, whichever earlier run timed
    /// out.
    #[test]
    #[ignore = "kink"]
    fn a_killer_the_clock_stopped_is_kept_unverified() {
        let manifest = looping(
            "killer-stopped",
            &[("countdown", "countdown(3)"), ("one", "countdown(1)")],
        );
        let lock = lock_of(&manifest);
        let (cold, _) = run_status(&manifest, false);
        let row = row(&cold, "countdown-escapes");
        assert_eq!(
            (&row["status"], &row["killer"]),
            (&json!("killed"), &json!("one"))
        );
        let written = fs::read_to_string(&lock).unwrap();
        assert!(written.contains("killer = \"one\""), "{written}");

        // A host that finished countdown's run recorded it as the killer.
        let recorded = with_row(&written, "status = \"killed\"\nkiller = \"countdown\"\n");
        fs::write(&lock, &recorded).unwrap();
        let (locked, status) = run_status(&manifest, true);
        assert_eq!(
            locked["lock"]["status"], "undecided",
            "{:#}",
            locked["lock"]
        );
        assert_eq!(status, EXIT_UNANSWERED, "{:#}", locked["lock"]);
        assert_eq!(locked["lock"]["changes"], json!([]), "{:#}", locked["lock"]);
        assert_eq!(
            locked["lock"]["kept"],
            json!([{
                "mutation": "countdown-escapes",
                "recorded": {"status": "killed", "killer": "countdown", "reason": null},
                "now": {"status": "killed", "killer": "one", "reason": null},
            }])
        );
        assert_eq!(
            stopped(&locked),
            [("countdown".to_owned(), "mutant".to_owned())]
        );
        assert_eq!(fs::read_to_string(&lock).unwrap(), recorded);
        // Without `--locked` the killer is kept, and the lock does not move.
        let (kept, status) = run_status(&manifest, false);
        assert_eq!(status, EXIT_YES, "{:#}", kept["lock"]);
        assert_eq!(kept["lock"]["status"], "unchanged", "{:#}", kept["lock"]);
        assert_eq!(kept["lock"]["kept"], locked["lock"]["kept"]);
        assert_eq!(fs::read_to_string(&lock).unwrap(), recorded);
        let output = binary(&manifest, &["--lock", "kink.lock", "--locked"]);
        assert_eq!(output.status.code(), Some(i32::from(EXIT_UNANSWERED)));
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(
            stderr.contains(
                "kink.lock: countdown-escapes: the clock (budget.time_ms) stopped the run \
                 of countdown on its mutant"
            ) && stderr.contains(
                "kink.lock: countdown-escapes: kept killed (killer countdown) unverified: \
                 this host gives killed (killer one)"
            ),
            "{stderr}"
        );

        // A recorded survivor: `one` finished and kills, so the status moved, whatever
        // countdown's stopped run would have given.
        let survived = with_row(&written, "status = \"survived\"\n");
        fs::write(&lock, &survived).unwrap();
        let (stale, status) = run_status(&manifest, true);
        assert_eq!(status, EXIT_NO, "{:#}", stale["lock"]);
        assert_eq!(stale["lock"]["status"], "stale");
        assert_eq!(stale["lock"]["kept"], json!([]));
        let (rewritten, _) = run_status(&manifest, false);
        assert_eq!(rewritten["lock"]["status"], "written");
        assert_eq!(fs::read_to_string(&lock).unwrap(), written);
    }

    /// A recorded survivor whose live status is `timeout` keeps its status; and a recorded killer
    /// whose baseline the clock stopped (so it is not comparable on this host) is kept too.
    #[test]
    #[ignore = "kink"]
    fn a_status_or_killer_a_stopped_run_decides_is_kept() {
        let manifest = looping(
            "status-stopped",
            &[("countdown", "countdown(3)"), ("twice", "twice(4)")],
        );
        let lock = lock_of(&manifest);
        let (cold, _) = run_status(&manifest, false);
        assert_eq!(row(&cold, "countdown-escapes")["status"], "timeout");
        let written = fs::read_to_string(&lock).unwrap();
        assert!(written.contains("status = \"timeout\""), "{written}");
        let survived = with_row(&written, "status = \"survived\"\n");
        fs::write(&lock, &survived).unwrap();
        let (locked, status) = run_status(&manifest, true);
        assert_eq!(
            locked["lock"]["status"], "undecided",
            "{:#}",
            locked["lock"]
        );
        assert_eq!(status, EXIT_UNANSWERED);
        assert_eq!(
            locked["lock"]["kept"][0]["now"]["status"], "timeout",
            "{:#}",
            locked["lock"]
        );
        let (kept, _) = run_status(&manifest, false);
        assert_eq!(kept["lock"]["status"], "unchanged", "{:#}", kept["lock"]);
        assert_eq!(fs::read_to_string(&lock).unwrap(), survived);

        // spin's baseline never ends: on this host it is not comparable, so it cannot be tried.
        let manifest = looping(
            "baseline-stopped",
            &[("spin", "spin(0)"), ("one", "countdown(1)")],
        );
        let lock = lock_of(&manifest);
        let (cold, _) = run_status(&manifest, false);
        assert_eq!(row(&cold, "countdown-escapes")["killer"], "one");
        let written = fs::read_to_string(&lock).unwrap();
        let recorded = with_row(&written, "status = \"killed\"\nkiller = \"spin\"\n");
        fs::write(&lock, &recorded).unwrap();
        let (locked, status) = run_status(&manifest, true);
        assert_eq!(
            locked["lock"]["status"], "undecided",
            "{:#}",
            locked["lock"]
        );
        assert_eq!(status, EXIT_UNANSWERED);
        assert_eq!(
            stopped(&locked),
            [("spin".to_owned(), "baseline".to_owned())]
        );
        let (kept, _) = run_status(&manifest, false);
        assert_eq!(kept["lock"]["status"], "unchanged", "{:#}", kept["lock"]);
        assert_eq!(fs::read_to_string(&lock).unwrap(), recorded);
    }

    fn coverage(manifest: &Path, locked: bool) -> (Value, u8) {
        coverage_of(manifest, locked, Derived::default())
    }

    /// `coverage --lock kink.lock [--locked]` for a front end that derives `derived`.
    fn coverage_of(manifest: &Path, locked: bool, derived: Derived<'_>) -> (Value, u8) {
        let mut options = vec![
            "--lock".to_owned(),
            manifest
                .with_file_name("kink.lock")
                .to_str()
                .unwrap()
                .to_owned(),
        ];
        if locked {
            options.push("--locked".to_owned());
        }
        let command = FlowCommand::parse("coverage", CommandFiles::default(), &options).unwrap();
        let flow = FlowManifest::read(manifest).unwrap();
        let front = FrontEnd {
            derived,
            ..FrontEnd::default()
        };
        dispatch(flow, command, front).expect("the command does not panic")
    }

    /// The rules item whose label is `label`.
    fn rule_id(document: &Value, label: &str) -> String {
        document["families"]["rules"]["items"]
            .as_array()
            .unwrap()
            .iter()
            .find(|item| {
                item["label"]
                    .as_str()
                    .is_some_and(|l| l == label || l.ends_with(&format!(".{label}")))
            })
            .and_then(|item| item["id"].as_str())
            .unwrap_or_else(|| panic!("no rule {label}"))
            .to_owned()
    }

    /// A coverage lock records an obligation as covered (unlisted); the program that covered it
    /// is stopped by the clock on this host, so the obligation shows open: the lock keeps it
    /// unlisted, unverified, and `--locked` says the lock is not decided here (exit 3), while an
    /// obligation a program that finished covers is a difference (exit 1) and is written.
    #[test]
    #[ignore = "kink"]
    fn a_coverage_obligation_a_stopped_program_could_cover_is_kept() {
        let manifest = looping(
            "coverage-stopped",
            &[("countdown", "countdown(3)"), ("twice", "twice(4)")],
        );
        let lock = manifest.with_file_name("kink.lock");
        let (first, _) = coverage(&manifest, false);
        assert_eq!(first["lock"]["status"], "created", "{:#}", first["lock"]);
        let spin = rule_id(&first, "spin");
        let done = rule_id(&first, "done");
        let written = fs::read_to_string(&lock).unwrap();
        let listed = format!("  \"{spin}\",\n");
        assert!(written.contains(&listed), "{written}");
        // A host on which a program covering spin finished recorded it covered.
        let recorded = written.replacen(&listed, "", 1);
        fs::write(&lock, &recorded).unwrap();
        let mut text = fs::read_to_string(&manifest).unwrap();
        text.push_str("\n[[program]]\nid = \"spin\"\ntext = \"spin(0)\"\n");
        fs::write(&manifest, text).unwrap();
        let (locked, status) = coverage(&manifest, true);
        assert_eq!(
            locked["lock"]["status"], "undecided",
            "{:#}",
            locked["lock"]
        );
        assert_eq!(status, EXIT_UNANSWERED, "{:#}", locked["lock"]);
        assert_eq!(
            locked["lock"]["open_changes"],
            json!([]),
            "{:#}",
            locked["lock"]
        );
        assert_eq!(
            locked["lock"]["kept"],
            json!([{"family": "rules", "obligation": spin, "recorded": null, "now": "open"}])
        );
        assert_eq!(
            stopped(&locked),
            [("spin".to_owned(), "baseline".to_owned())]
        );
        assert_eq!(fs::read_to_string(&lock).unwrap(), recorded);

        // An obligation recorded open that a program which finished covers moved.
        let open_done = recorded.replacen("open = [\n", &format!("open = [\n  \"{done}\",\n"), 1);
        fs::write(&lock, &open_done).unwrap();
        let (stale, status) = coverage(&manifest, true);
        assert_eq!(status, EXIT_NO, "{:#}", stale["lock"]);
        assert_eq!(
            stale["lock"]["open_changes"],
            json!([{"family": "rules", "obligation": done, "recorded": "open", "now": null}])
        );
        let (rewritten, _) = coverage(&manifest, false);
        assert_eq!(
            rewritten["lock"]["status"], "written",
            "{:#}",
            rewritten["lock"]
        );
        assert_eq!(fs::read_to_string(&lock).unwrap(), recorded);
    }

    /// The flip of the countdown rule's condition: `countdown(0)` then both ends at 0 and steps
    /// to `countdown(-1)`, `countdown(-2)`, ... for ever, so the clock stops its run on the
    /// mutant, and `countdown(3)` no longer steps, which distinguishes it. A recorded killer whose
    /// run the clock stopped is kept, as a mutation's is.
    #[test]
    #[ignore = "kink"]
    fn a_flips_killer_the_clock_stopped_is_kept() {
        let manifest = looping(
            "flip-stopped",
            &[("zero", "countdown(0)"), ("three", "countdown(3)")],
        );
        let lock = manifest.with_file_name("kink.lock");
        let (rules, _) = coverage(&manifest, false);
        let item = rules["families"]["rules"]["items"]
            .as_array()
            .unwrap()
            .iter()
            .find(|item| item["id"] == rule_id(&rules, "countdown").as_str())
            .unwrap()
            .clone();
        let id = "flip--countdown--positive";
        let list = DerivedList {
            entries: vec![DerivedEntry {
                id: id.to_owned(),
                operator: "flip".to_owned(),
                text: "I >Int 0".to_owned(),
                atom: json!({"kind": "boolean", "head": "I >Int 0"}),
                occurrences: vec![Occurrence {
                    sentence: SentenceRef {
                        module: item["module"].as_str().unwrap().to_owned(),
                        index: u32::try_from(item["index"].as_u64().unwrap()).unwrap(),
                    },
                    reach: Reach::Operand {
                        path: "0".to_owned(),
                    },
                }],
                judged: Judged::Admitted {
                    edits: vec![EditSpec {
                        file: None,
                        rule: Some("countdown".to_owned()),
                        line: None,
                        action: EditAction::Replace {
                            find: "requires I >Int 0".to_owned(),
                            replace: "requires I <=Int 0".to_owned(),
                        },
                    }],
                },
            }],
            ..DerivedList::default()
        };
        fs::remove_file(&lock).unwrap();
        let (first, _) = coverage_of(&manifest, false, Derived::Flips(&list));
        let flip = first["families"]["flips"]["items"][0].clone();
        assert_eq!(
            (&flip["status"], &flip["killer"], &flip["timed_out"][0]),
            (&json!("distinguished"), &json!("three"), &json!("zero")),
            "{flip:#}"
        );
        let written = fs::read_to_string(&lock).unwrap();
        let recorded = written.replacen("killer = \"three\"", "killer = \"zero\"", 1);
        assert_ne!(recorded, written);
        fs::write(&lock, &recorded).unwrap();
        let (locked, status) = coverage_of(&manifest, true, Derived::Flips(&list));
        assert_eq!(
            locked["lock"]["status"], "undecided",
            "{:#}",
            locked["lock"]
        );
        assert_eq!(status, EXIT_UNANSWERED, "{:#}", locked["lock"]);
        assert_eq!(
            locked["lock"]["kept"],
            json!([{
                "flip": id,
                "recorded": {"status": "distinguished", "killer": "zero", "reason": null},
                "now": {"status": "distinguished", "killer": "three", "reason": null},
            }])
        );
        assert!(
            stopped(&locked).contains(&("zero".to_owned(), "mutant".to_owned())),
            "{:#}",
            locked["lock"]
        );
        let (kept, _) = coverage_of(&manifest, false, Derived::Flips(&list));
        assert_eq!(kept["lock"]["status"], "unchanged", "{:#}", kept["lock"]);
        assert_eq!(fs::read_to_string(&lock).unwrap(), recorded);
    }

    /// An argued item's evidence run that the clock stops: `rule:unused` is argued by an
    /// invariant false wherever `unused` heads the computation, so its connection holds, and the
    /// evidence of `countdown(20000)`, which steps no rule that can step where `unused` matches, is
    /// vacuous: `connected`. The program's baseline record does not name `time_ms`, so under a
    /// clock of 50 ms, about a thirtieth of that run's time, the baseline stays cached and
    /// comparable while its evidence run, made again once the evidence memo is gone, is stopped:
    /// the standing would be `unchecked`, and the lock keeps `connected`, unverified.
    #[test]
    #[ignore = "kink"]
    fn a_standing_whose_evidence_run_the_clock_stopped_is_kept() {
        let manifest = looping("evidence-stopped", &[("long", "countdown(20000)")]);
        let k = manifest.with_file_name("loop.k");
        let definition = fs::read_to_string(&k).unwrap().replacen(
            "  rule [unused]:",
            "  syntax Bool ::= noUnused(K) [function, total, symbol(noUnused)]\n  rule \
             noUnused(unused(_) ~> _) => false\n  rule noUnused(_) => true [owise]\n  rule \
             [unused]:",
            1,
        );
        fs::write(&k, definition).unwrap();
        let clock = |ms: &str| {
            let text = fs::read_to_string(&manifest).unwrap();
            let at = text.find("time_ms = ").unwrap();
            let end = at + text[at..].find('\n').unwrap();
            fs::write(
                &manifest,
                format!("{}time_ms = {ms}{}", &text[..at], &text[end..]),
            )
            .unwrap();
        };
        clock("600000");
        let mut text = fs::read_to_string(&manifest).unwrap();
        text.push_str(
            "\n[[coverage.invariant]]\nname = \"no-unused\"\nfunction = \"noUnused\"\ncells = \
             [\"k\"]\n\n[[coverage.argued]]\nitem = \"rule:LOOP.unused\"\nargument = \"no \
             program writes unused\"\ninvariant = \"no-unused\"\n",
        );
        fs::write(&manifest, text).unwrap();
        let lock = manifest.with_file_name("kink.lock");
        let (first, _) = coverage(&manifest, false);
        let unused = first["families"]["rules"]["items"]
            .as_array()
            .unwrap()
            .iter()
            .find(|item| item["id"] == "rule:LOOP.unused")
            .unwrap()["argument_check"]
            .clone();
        assert_eq!(
            (&unused["standing"], &unused["evidence"]["clock_stopped"]),
            (&json!("connected"), &json!([])),
            "{unused:#}"
        );
        assert_eq!(first["lock"]["status"], "created", "{:#}", first["lock"]);
        let recorded = fs::read_to_string(&lock).unwrap();
        assert!(
            recorded.contains("  { id = \"rule:LOOP.unused\", standing = \"connected\" },\n"),
            "{recorded}"
        );

        // The evidence runs again, under a clock its run cannot meet.
        let cache = manifest.with_file_name(CACHE_DIRECTORY);
        fs::remove_dir_all(cache.join(kink_flow::memo::MEMO_DIRECTORY).join("evidence")).unwrap();
        clock("50");
        let (locked, status) = coverage(&manifest, true);
        let long = &locked["programs"][0];
        assert_eq!(
            (&long["class"], &long["cached"]),
            (&json!("comparable"), &json!(true)),
            "{long:#}"
        );
        assert_eq!(
            locked["lock"]["status"], "undecided",
            "{:#}",
            locked["lock"]
        );
        assert_eq!(status, EXIT_UNANSWERED, "{:#}", locked["lock"]);
        assert_eq!(
            locked["lock"]["kept"],
            json!([{"argument": "rule:LOOP.unused", "recorded": "connected", "now": "unchecked"}])
        );
        assert_eq!(
            locked["lock"]["clock_stopped"],
            json!([{"program": "long", "run": "evidence", "argument": "rule:LOOP.unused"}])
        );
        assert_eq!(fs::read_to_string(&lock).unwrap(), recorded);
        let (kept, _) = coverage(&manifest, false);
        assert_eq!(kept["lock"]["status"], "unchanged", "{:#}", kept["lock"]);
        assert_eq!(fs::read_to_string(&lock).unwrap(), recorded);
    }
}
