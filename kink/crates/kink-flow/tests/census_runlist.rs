//! KINK-CENSUS-RUNLIST (fz26 P7-SIMPLE-KINK design, (a) stream cells): the definition-level census
//! reads only the open hooks k-rust evaluates without a run-level record; an open hook an execute
//! request cannot evaluate (a console operation, or one k-rust has no evaluator for) is judged per
//! run, through the run's `unsupportedHooks` list (kink-native `exclusion::RUN_LIST_HOOKS`). And a
//! program may not bind `$IO` on a definition with stream cells (`stream-mode`). The fixtures are
//! in `testdata/k/runlist`, outside the flow corpus that `tests/modality.rs` walks.

use kink_flow::{
    FlowManifest,
    admit::admit,
    cli::{EXIT_OK, results},
    results::{CACHE_DIRECTORY, ResultsOptions},
};
use serde_json::Value;
use std::{
    fs,
    path::{Path, PathBuf},
};

/// A private copy of `testdata/k/runlist` for one test, and the path of its manifest `manifest`.
fn fixture(manifest: &str, test: &str) -> PathBuf {
    let from = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/k/runlist");
    let to = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-census-runlist-{}", std::process::id()))
        .join(test);
    let _ = fs::remove_dir_all(&to);
    fs::create_dir_all(&to).unwrap();
    for entry in fs::read_dir(&from).unwrap() {
        let entry = entry.unwrap();
        if entry.file_name() != CACHE_DIRECTORY && entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), to.join(entry.file_name())).unwrap();
        }
    }
    to.join(manifest)
}

/// `kink-flow results` of `manifest`, its status checked.
#[track_caller]
fn classes(manifest: &Path) -> Value {
    let (document, status) = results(
        manifest,
        &ResultsOptions {
            verify: false,
            cache: None,
            mutations: None,
        },
    );
    assert_eq!(status, EXIT_OK, "{document:#}");
    document
}

/// `(id, class, cause)` of every program row.
fn rows(document: &Value) -> Vec<(String, String, String)> {
    document["programs"]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| {
            (
                p["id"].as_str().unwrap().to_owned(),
                p["class"].as_str().unwrap().to_owned(),
                p["cause"].as_str().unwrap_or_default().to_owned(),
            )
        })
        .collect()
}

/// Every row's id and class, and for each row whose class is not `comparable` that its cause
/// holds `reason` (for an exclusion, `excluded(name)`).
#[track_caller]
fn assert_rows(document: &Value, expected: &[(&str, &str, Option<&str>)]) {
    let rows = rows(document);
    assert_eq!(
        rows.iter()
            .map(|(id, class, _)| (id.as_str(), class.as_str()))
            .collect::<Vec<_>>(),
        expected
            .iter()
            .map(|(id, class, _)| (*id, *class))
            .collect::<Vec<_>>(),
        "{rows:#?}"
    );
    for ((id, _, cause), (_, _, reason)) in rows.iter().zip(expected) {
        match reason {
            Some(reason) => assert!(cause.contains(reason), "{id}: {cause}"),
            None => assert!(cause.is_empty(), "{id}: {cause}"),
        }
    }
}

/// The text a baseline row's cause holds when the run is excluded for `exclusion`.
fn excluded(exclusion: &str) -> String {
    format!("is no evidence: {exclusion})")
}

mod kink_tier {
    use super::*;

    /// Review R2-S1: in `iopw` (console operations, no bytes pair) the programs that apply
    /// `#write` and `#getc` are unknown for their run's `unsupported-hook`, and `n`, which applies
    /// neither, is comparable. Before, every program was `implementation-chosen-hook` (the census
    /// of `IO.write` and `IO.getc`). The full `iop` adds a rule applying the bytes pair, which
    /// stays in the census: every program, `n` included, stays `implementation-chosen-hook`.
    #[test]
    #[ignore = "kink"]
    fn console_operations_are_judged_per_run_and_the_bytes_pair_still_excludes() {
        let document = classes(&fixture("FLOW-iopw.toml", "iopw"));
        assert_rows(
            &document,
            &[
                ("w", "unknown", Some(&excluded("unsupported-hook"))),
                ("g", "unknown", Some(&excluded("unsupported-hook"))),
                ("n", "comparable", None),
            ],
        );
        let document = classes(&fixture("FLOW-iop.toml", "iop"));
        let census = excluded("implementation-chosen-hook");
        let census = Some(census.as_str());
        assert_rows(
            &document,
            &[
                ("w", "unknown", census),
                ("g", "unknown", census),
                ("b", "unknown", census),
                ("n", "unknown", census),
            ],
        );
    }

    /// A left-hand-side map key whose match fails: with `#getc(0)` in it (`lhsio`) the run lists
    /// `IO.getc` on `unsupportedHooks` though no rule applies, so the program is unknown for its
    /// run (before: `implementation-chosen-hook`); with the bytes pair in it (`lhs`, review B1)
    /// the census still excludes the definition, the hit and the miss alike.
    #[test]
    #[ignore = "kink"]
    fn a_failing_left_hand_side_is_judged_by_the_run_list_or_the_census() {
        let document = classes(&fixture("FLOW-lhsio.toml", "lhsio"));
        assert_rows(
            &document,
            &[("miss", "unknown", Some(&excluded("unsupported-hook")))],
        );
        let document = classes(&fixture("FLOW-lhs.toml", "lhs"));
        let census = excluded("implementation-chosen-hook");
        let census = Some(census.as_str());
        assert_rows(
            &document,
            &[("miss", "unknown", census), ("hit", "unknown", census)],
        );
    }

    /// Stock SIMPLE (untyped), unedited: the list-free programs, the empty one, `var x;`, and
    /// `var x; x = read();` on empty input and on `5\n`, are comparable. Before (with
    /// KINK-SC-DEFINED) each was `implementation-chosen-hook`: the prelude's stream rules, copied
    /// into its stream cells, apply `#getc`, `#write` and `Float2String`. Each end holds its
    /// stream cells, so it states the text printed and the input not yet read.
    ///
    /// `print(1);` and `var x = read(); print(x);` are comparable too since KINK-OVERLOAD-VALUE:
    /// the store keeps `main`'s body, which holds an irreducible overloaded list application
    /// (`1, .Vals`; `x = read(), .Exps`). With KINK-CENSUS-RUNLIST alone they were excluded by
    /// nothing but unknown ("a baseline declaration-scoped oracle gate rejected"): the walk
    /// admitted no overload application. It now admits one where k-rust's `is_data` holds.
    #[test]
    #[ignore = "kink"]
    fn stock_simple_programs_are_comparable() {
        let manifest = fixture("FLOW-simple.toml", "simple");
        let document = classes(&manifest);
        assert_rows(
            &document,
            &[
                ("empty", "comparable", None),
                ("decl", "comparable", None),
                ("read-empty", "comparable", None),
                ("read-5", "comparable", None),
                ("print", "comparable", None),
                ("read-print", "comparable", None),
            ],
        );
        assert!(
            rows(&document)
                .iter()
                .all(|(_, _, cause)| !cause.contains("is no evidence")),
            "{document:#}"
        );
    }

    /// A program that binds `$IO` on stock SIMPLE, a definition with stream cells, is refused at
    /// the inputs stage with reason `stream-mode`, whatever the value; binding `$STDIN` is
    /// admitted. Before, all three were admitted.
    #[test]
    #[ignore = "kink"]
    fn binding_io_on_a_stream_definition_is_refused() {
        let manifest = fixture("FLOW-simple-io.toml", "simple-io");
        let admission = admit(&FlowManifest::read(&manifest).unwrap());
        assert!(
            admission.record.refusal.is_none(),
            "{}",
            admission.record.text()
        );
        let outcomes = admission
            .programs
            .iter()
            .map(|p| {
                (
                    p.id.as_str(),
                    p.outcome
                        .as_ref()
                        .err()
                        .map(|r| (r.stage.as_str(), r.reason.as_str())),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(
            outcomes,
            [
                ("io-on", Some(("inputs", "stream-mode"))),
                ("io-off", Some(("inputs", "stream-mode"))),
                ("stdin", None),
            ]
        );
    }
}
