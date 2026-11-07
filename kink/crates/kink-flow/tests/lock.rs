//! The killer record (`run --lock FILE`, README "The killer record"): one recorded killer per
//! killed mutation, kept while it still kills and is in the corpus, else the first killing program
//! in the search's order; written after a run that judged the whole list, compared under
//! `--locked`, and refused when it does not decode.
//!
//! Every run here is on a private copy of `testdata/flow/calc` with `[budget] time_ms` far above
//! any run's time, so no row depends on the clock. Statuses are always the ones a run without a
//! lock gives: the record orders the work and names the killer, never a status.

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
    manifest.with_file_name("verdicts.lock")
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
    let mut text = "schema = \"kink-flow-verdicts\"\nversion = 7\ndocument = \"run\"\n".to_owned();
    for (id, killer) in killers {
        text.push_str(&format!(
            "\n[[mutation]]\nid = \"{id}\"\nstatus = \"killed\"\nkiller = \"{killer}\"\n"
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
        parse(&["--locked", "--lock", "verdicts.lock"]).unwrap()
    else {
        panic!("run");
    };
    assert_eq!(
        (options.lock, options.locked),
        (Some(PathBuf::from("verdicts.lock")), true)
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
        "changes": [],
        "difference": null,
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
            "its document is not \"run\"",
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
            rendering.ends_with("\n[lock]\noutcome = \"refused\"\n"),
            "{rendering}"
        );
        assert_eq!(fs::read_to_string(&lock).unwrap(), text);
    }
}

/// `Lock::read`: an absent file is an empty record; a version-5 lock (no `killer` lines) records
/// no killer; only `id` and `killer` decide anything.
#[test]
fn a_version_5_lock_records_no_killer() {
    let dir = scratch("version-5");
    let absent = Lock::read(&dir.join("verdicts.lock")).unwrap();
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
    /// binary names each change on stderr.
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
        let output = binary(&manifest, &["--lock", "verdicts.lock", "--locked"]);
        assert_eq!(output.status.code(), Some(i32::from(EXIT_NO)));
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(
            stderr.contains(
                "verdicts.lock: add-becomes-sub: killer gone -> add (gone: not-in-corpus)"
            ),
            "{stderr}"
        );
        assert!(
            stderr.contains("verdicts.lock: add-swaps-operands: killed -> survived"),
            "{stderr}"
        );
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
