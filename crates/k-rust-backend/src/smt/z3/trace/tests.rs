//! The SMT trace writes each attempt's script before Z3 reads it, records each attempt's answer
//! and resource units as a JSON line, is off unless asked for, changes no answer, and replays a
//! traced script to the answers the traced query had.

use std::{ffi::OsString, num::NonZeroU32, path::PathBuf};

use serde_json::Value;

use super::*;
use crate::smt::{
    Z3Solver,
    z3::tests::{FACTORING_QUERY, PATH_SENSITIVE_QUERY, answers, definition},
};

/// A fresh, empty directory for one test's trace, removed when dropped.
pub(crate) struct Scratch(PathBuf);

impl Scratch {
    pub(crate) fn new(name: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "k-rust-smt-trace-{}-{name}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir_all(&path).unwrap();
        Self(path)
    }

    pub(crate) fn path(&self) -> &Path {
        &self.0
    }

    fn files(&self) -> Vec<String> {
        let mut names = fs::read_dir(&self.0)
            .unwrap()
            .map(|entry| entry.unwrap().file_name().to_string_lossy().into_owned())
            .collect::<Vec<_>>();
        names.sort();
        names
    }

    /// Every record of the trace's logs, in sequence order.
    pub(crate) fn records(&self) -> Vec<Value> {
        let mut records = Vec::new();
        for name in self.files() {
            if name.ends_with(".jsonl") {
                for line in fs::read_to_string(self.0.join(name)).unwrap().lines() {
                    records.push(serde_json::from_str::<Value>(line).expect("a JSON line"));
                }
            }
        }
        records.sort_by_key(|record| record["seq"].as_u64().unwrap());
        records
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

pub(crate) fn of_kind<'a>(records: &'a [Value], kind: &str) -> Vec<&'a Value> {
    records
        .iter()
        .filter(|record| record["kind"] == kind)
        .collect()
}

fn retried() -> Z3Options {
    Z3Options {
        budget: SmtBudget::Units(NonZeroU32::new(250_000).unwrap()),
        retry_limit: 2,
    }
}

/// The trace is on only when its directory variable names a directory, and keeps every script
/// only when asked to; in this process, without the variable, it is off.
#[test]
fn the_trace_is_off_unless_its_directory_is_named() {
    let variables = |pairs: &'static [(&'static str, &'static str)]| {
        move |name: &str| {
            pairs
                .iter()
                .find(|(key, _)| *key == name)
                .map(|(_, value)| OsString::from(value))
        }
    };
    assert_eq!(configured(variables(&[])), None);
    assert_eq!(configured(variables(&[(DIRECTORY_VARIABLE, "")])), None);
    assert_eq!(configured(variables(&[(SCRIPTS_VARIABLE, "all")])), None);
    assert_eq!(
        configured(variables(&[(DIRECTORY_VARIABLE, "/trace")])),
        Some((PathBuf::from("/trace"), false))
    );
    assert_eq!(
        configured(variables(&[
            (DIRECTORY_VARIABLE, "/trace"),
            (SCRIPTS_VARIABLE, "all")
        ])),
        Some((PathBuf::from("/trace"), true))
    );
    if std::env::var_os(DIRECTORY_VARIABLE).is_none() {
        assert!(active().is_none());
        // Off, a label changes nothing either.
        with_label("off", || assert_eq!(LABEL.with(Cell::get), None));
    }
}

/// An attempt's script is on disk, with a header that names the attempt, before Z3 reads it; it
/// stays there if the process ends before the attempt is answered, and gives way to the
/// attempt's JSON line once Z3 is done with it.
#[test]
fn an_attempts_script_is_written_before_its_check_and_recorded_after() {
    let scratch = Scratch::new("inflight");
    with_directory(Some(&scratch.0), false, || {
        let ladder = Ladder {
            options: retried(),
            clocked: true,
        };
        let limit = ladder.limit(1);
        let attempt = Attempt::begin(FACTORING_QUERY, &ladder, 1, limit).expect("the trace is on");
        let inflight = scratch
            .files()
            .into_iter()
            .find(|name| name.ends_with("-inflight.smt2"))
            .expect("the in-flight script is written before the check");
        let traced =
            TracedScript::parse(&fs::read_to_string(scratch.0.join(&inflight)).unwrap()).unwrap();
        assert_eq!(traced.script, FACTORING_QUERY);
        assert_eq!(traced.options, retried());
        assert_eq!(traced.attempt, Some(1));
        assert!(traced.z3.is_some());

        // An attempt never answered (Z3 ended the process inside its check) leaves its script.
        drop(attempt);
        assert!(scratch.0.join(&inflight).exists());

        // An answered attempt leaves its record at once, and removes its script once Z3 is
        // done with it: while its solver is held, a model can still be read.
        let answered = on_own_context(|| {
            let attempted = run_attempt(
                FACTORING_QUERY,
                &mut None,
                &ladder,
                0,
                ladder.limit(0),
                false,
            )
            .unwrap();
            assert!(scratch.0.join(&inflight).exists(), "{:?}", scratch.files());
            assert_eq!(of_kind(&scratch.records(), "check").len(), 1);
            answer_text(attempted.checked.result)
        });
        assert!(!scratch.0.join(&inflight).exists(), "{:?}", scratch.files());
        let records = scratch.records();
        let checks = of_kind(&records, "check");
        assert_eq!(checks.len(), 1, "{records:?}");
        assert_eq!(checks[0]["result"], answered);
        assert_eq!(checks[0]["script_sha256"], sha256(FACTORING_QUERY));
        assert_eq!(checks[0]["rlimit_param"], 250_000);
        assert_eq!(checks[0]["timeout_param"], Value::Null);
        assert!(checks[0]["rlimit_used"].as_u64().unwrap() > 0);
    });
}

/// A traced query records one parseable line per attempt, with the resource units each consumed,
/// keeps its script when asked to, leaves no in-flight script, and answers as it does untraced.
/// Replaying the kept script runs the same attempts to the same answers and unit counts.
#[test]
#[expect(
    clippy::disallowed_methods,
    reason = "the trace records and replays a clocked ladder as it does a clock-free one"
)]
fn a_traced_query_answers_as_untraced_and_replays_to_its_answers() {
    let run = |directory: Option<PathBuf>, options: Z3Options, script: &'static str| {
        std::thread::spawn(move || {
            with_directory(directory.as_deref(), true, || {
                with_label("test.scope", || {
                    let solver = Z3Solver::with_options(&definition(), options).unwrap();
                    answers(&solver, script, 1)
                })
            })
        })
        .join()
        .unwrap()
    };
    // A clocked ladder whose clock never ends an attempt: the query decides in under 1,000
    // units, far within a minute, so the traced, untraced and replayed answers compare.
    let clocked = Z3Options {
        budget: SmtBudget::clock(60_000),
        ..Z3Options::default()
    };
    for (options, script) in [
        (retried(), FACTORING_QUERY),
        (clocked, PATH_SENSITIVE_QUERY),
    ] {
        let scratch = Scratch::new("query");
        let untraced = run(None, options, script);
        let traced = run(Some(scratch.0.clone()), options, script);
        assert_eq!(traced, untraced);

        let records = scratch.records();
        let checks = of_kind(&records, "check");
        assert!(!checks.is_empty());
        for (index, check) in checks.iter().enumerate() {
            assert_eq!(check["attempt"], index);
            assert_eq!(check["label"], "test.scope");
            assert_eq!(check["script_sha256"], sha256(script));
            assert!(check["rlimit_used"].as_u64().unwrap() > 0, "{check}");
            assert!(check["wall_us"].is_u64(), "{check}");
            assert!(matches!(
                check["result"].as_str(),
                Some("sat" | "unsat" | "unknown")
            ));
        }
        let last = checks.last().unwrap()["result"].as_str().unwrap();
        assert_eq!(
            last,
            match traced.as_str() {
                "S" => "sat",
                "U" => "unsat",
                _ => "unknown",
            }
        );
        assert!(
            !scratch
                .files()
                .iter()
                .any(|name| name.ends_with("-inflight.smt2") || name.ends_with(".tmp")),
            "{:?}",
            scratch.files()
        );

        let kept = scratch.0.join(format!("{}.smt2", sha256(script)));
        let traced_script = TracedScript::parse(&fs::read_to_string(kept).unwrap()).unwrap();
        assert_eq!(traced_script.script, script);
        assert_eq!(traced_script.options, options);
        assert_eq!(traced_script.label.as_deref(), Some("test.scope"));
        let replayed = std::thread::spawn(move || {
            replay(
                &traced_script.script,
                traced_script.options,
                traced_script.clocked,
            )
        })
        .join()
        .unwrap()
        .unwrap();
        assert_eq!(
            replayed
                .iter()
                .map(|attempt| attempt.result)
                .collect::<Vec<_>>(),
            checks
                .iter()
                .map(|check| check["result"].as_str().unwrap())
                .collect::<Vec<_>>()
        );
        if options.budget.is_clock_free() {
            // Clock-free, each attempt's search is a function of the script and the ladder.
            assert_eq!(
                replayed
                    .iter()
                    .map(|attempt| attempt.rlimit_used)
                    .collect::<Vec<_>>(),
                checks
                    .iter()
                    .map(|check| check["rlimit_used"].as_u64().unwrap())
                    .collect::<Vec<_>>()
            );
        }
    }
}

/// A script Z3 does not load is recorded as rejected, with Z3's message, and replays as rejected.
#[test]
fn a_rejected_script_is_recorded() {
    let scratch = Scratch::new("rejected");
    let script = "(assert (> undeclared 0))";
    let solver = Z3Solver::resource_bounded(&definition()).unwrap();
    with_directory(Some(&scratch.0), false, || {
        assert!(matches!(solver.solve_uncached(script), Ok(Err(_))));
    });
    let records = scratch.records();
    let checks = of_kind(&records, "check");
    assert_eq!(checks.len(), 1, "{records:?}");
    assert_eq!(checks[0]["result"], "rejected");
    assert!(checks[0]["reason"].is_string());
    assert_eq!(checks[0]["rlimit_used"], Value::Null);
    assert!(replay(script, Z3Options::default(), true).is_err());
}

/// A script that is not a trace's reads as itself under the default ladder; a header whose
/// digest does not match its script is refused.
#[test]
fn plain_and_tampered_scripts() {
    let plain = TracedScript::parse("(check-sat)").unwrap();
    assert_eq!(plain.script, "(check-sat)");
    assert_eq!(plain.options, Z3Options::default());
    let ladder = Ladder {
        options: Z3Options::default(),
        clocked: true,
    };
    let text = header(&ladder, &sha256("(assert true)"), None, None) + "(assert false)";
    assert!(TracedScript::parse(&text).is_err());
    let text = header(&ladder, &sha256("(assert true)"), None, None) + "(assert true)";
    assert_eq!(TracedScript::parse(&text).unwrap().script, "(assert true)");
}

/// A header's budget is the default units when it states none, a clock when it states only a
/// clock, and is refused when it states two; a header written before the `budget` line reads as
/// it did: units under a `resource_limit` count, the clock of `timeout_ms` under `none`.
#[test]
#[expect(
    clippy::disallowed_methods,
    reason = "the expected budget of a header that states a clock"
)]
fn a_headers_budget_is_units_unless_it_states_a_clock() {
    let script = "(assert true)";
    let parse = |lines: &str| {
        TracedScript::parse(&format!(
            "{HEADER_MAGIC}\n; script_sha256 = {}\n{lines}{HEADER_END}\n{script}",
            sha256(script)
        ))
        .map(|traced| traced.options.budget)
    };
    assert_eq!(parse(""), Ok(SmtBudget::DEFAULT));
    assert_eq!(parse("; budget = clock 40\n"), Ok(SmtBudget::clock(40)));
    assert_eq!(
        parse("; budget = units 9\n"),
        Ok(SmtBudget::Units(NonZeroU32::new(9).unwrap()))
    );
    assert!(parse("; budget = units 9\n; budget = clock 40\n").is_err());
    assert!(parse("; budget = units 9\n; timeout_ms = 40\n").is_err());
    assert!(parse("; budget = units 0\n").is_err());
    assert_eq!(
        parse("; timeout_ms = 125\n; resource_limit = 7\n"),
        Ok(SmtBudget::Units(NonZeroU32::new(7).unwrap()))
    );
    assert_eq!(
        parse("; timeout_ms = 125\n; resource_limit = none\n"),
        Ok(SmtBudget::clock(125))
    );
    for budget in [SmtBudget::DEFAULT, SmtBudget::clock(3)] {
        let ladder = Ladder {
            options: Z3Options {
                budget,
                retry_limit: 1,
            },
            clocked: true,
        };
        let text = header(&ladder, &sha256(script), None, None) + script;
        assert_eq!(TracedScript::parse(&text).unwrap().options, ladder.options);
    }
}
