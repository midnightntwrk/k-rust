//! Re-pin lane 1 (L1-1), FB45-KINK: `[budget] work_factor`, the work budget of the mutants' runs,
//! a bound of polls on by default: `max(work_factor × P, P_max)`, `P` a program's baseline polls
//! and `P_max` the corpus's largest.
//!
//! The loop fixture's `countdown-escapes` makes `countdown(3)` step to itself forever. Its run
//! ends in a poll-bound leaf long before any time bound, so the program is `unknown` for the
//! mutant with a cause that names the polls and the bound, never a kill. The work budget counts
//! polls, not time, so that `unknown` is a function of its key and of the bound its record names,
//! and it is cached with its cause (CF-33d), whatever `time_ms` is; another factor re-runs the cut
//! run only, since a run that ended is the run without the bound. The same mutant stopped by the
//! clock instead (a factor so large that the clock fires first) is a timeout, which depends on the
//! host's load and is run again by every command.

use kink_flow::{
    FlowManifest, MutationList,
    results::CACHE_DIRECTORY,
    search::{RunOptions, run},
};
use serde_json::Value;
use std::{
    fs,
    path::{Path, PathBuf},
};

fn copy_dir(from: &Path, to: &Path) {
    fs::create_dir_all(to).unwrap();
    for entry in fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let name = entry.file_name();
        if name == CACHE_DIRECTORY {
            continue;
        }
        if entry.file_type().unwrap().is_dir() {
            copy_dir(&entry.path(), &to.join(&name));
        } else {
            fs::copy(entry.path(), to.join(&name)).unwrap();
        }
    }
}

/// The `time_ms` of a test whose expected outcome comes from a deterministic bound: nextest stops a
/// test after ten minutes, so this clock fires only on a test that fails anyway, and the bound
/// decides every passing run (R4-WALLCLOCK).
const NO_CLOCK_MS: u64 = 600_000;

/// A private copy of the loop fixture whose search manifest has the time bound `NO_CLOCK_MS` and
/// `work_factor = factor`.
fn fixture(test: &str, factor: u64) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-work-{}", std::process::id()))
        .join(test);
    let _ = fs::remove_dir_all(&dir);
    copy_dir(
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/flow/loop"),
        &dir,
    );
    let manifest = dir.join("FLOW-search.toml");
    set_factor(&manifest, factor);
    manifest
}

fn set_factor(manifest: &Path, factor: u64) {
    set_budget(manifest, factor, NO_CLOCK_MS);
}

/// The manifest's `[budget]` with `work_factor = factor` and `time_ms = time_ms`.
fn set_budget(manifest: &Path, factor: u64, time_ms: u64) {
    let text = fs::read_to_string(manifest).unwrap();
    let text = text
        .lines()
        .filter(|line| !line.starts_with("work_factor"))
        .map(|line| match line {
            line if line.starts_with("time_ms = ") => format!("time_ms = {time_ms}"),
            "[budget]" => format!("[budget]\nwork_factor = {factor}"),
            line => line.to_owned(),
        })
        .collect::<Vec<_>>()
        .join("\n");
    fs::write(manifest, text + "\n").unwrap();
}

fn search(manifest: &Path) -> Value {
    search_with(manifest, kink_campaign::ScheduleMode::FirstKill)
}

fn search_with(manifest: &Path, schedule: kink_campaign::ScheduleMode) -> Value {
    let (document, ok) = run(
        &FlowManifest::read(manifest).unwrap(),
        &MutationList::read(&manifest.with_file_name("MUTATIONS.toml")).unwrap(),
        &RunOptions {
            legacy_lock: None,
            only: Vec::new(),
            cache: None,
            compile_workers: None,
            memo: kink_flow::memo::MemoUse::On,
            schedule,
            lock: None,
            locked: false,
        },
    );
    assert!(ok, "{document:#}");
    document
}

/// `(program, outcome, cause, cached)` of every executed entry of `countdown-escapes`.
fn executed(document: &Value) -> Vec<(String, String, Option<String>, bool)> {
    let mutation = document["mutations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|m| m["id"] == "countdown-escapes")
        .unwrap();
    assert_eq!(mutation["status"], "unknown", "{mutation:#}");
    assert!(mutation["killer"].is_null());
    mutation["executed"]
        .as_array()
        .unwrap()
        .iter()
        .map(|e| {
            (
                e["program"].as_str().unwrap().to_owned(),
                e["outcome"].as_str().unwrap().to_owned(),
                e["cause"].as_str().map(str::to_owned),
                e["cached"].as_bool().unwrap(),
            )
        })
        .collect()
}

mod kink_tier {
    use super::*;

    /// CF-33d, FB45-KINK: the poll-bound `unknown` of `countdown` is cached with its cause, so the
    /// next command answers the whole row from the outcome cache (no call, no baseline run), with
    /// the cause the live run gave, under another `time_ms` too; raising the work factor re-runs
    /// only the cut run, and twice's agreement, a run that ended, is still read from the cache. The
    /// same mutant under the clock alone is a timeout, a host-bound cause, which is never cached:
    /// every command runs it again.
    #[test]
    #[ignore = "kink"]
    fn a_poll_bound_unknown_is_cached_with_its_cause_and_a_timeout_is_not() {
        let manifest = fixture("loop-work", 2);
        let first = search(&manifest);
        // The time bound is `NO_CLOCK_MS`; that the work budget, not the clock, stopped the loop is
        // the run's outcome and cause below: a run the clock stops is a timeout, and this one is
        // `unknown` because it reached its work budget, with one poll-bound leaf. So no elapsed
        // time is compared (a wall-time bound fails under load).
        let entries = executed(&first);
        assert_eq!(entries.len(), 2, "{entries:?}");
        let (program, outcome, cause, cached) = &entries[0];
        assert_eq!(
            (program.as_str(), outcome.as_str(), *cached),
            ("countdown", "unknown", false)
        );
        let cause = cause.as_deref().unwrap();
        assert!(
            cause.starts_with("the mutant's run used more than ")
                && cause.contains(" polls")
                && cause.contains("work_factor")
                && cause.contains("poll-bound 1"),
            "{cause}"
        );
        let bound = |document: &Value| {
            let floor = document["poll_floor"].as_u64().unwrap();
            let polls = document["programs"][0]["polls"].as_u64().unwrap();
            (polls, floor)
        };
        let (countdown_polls, floor) = bound(&first);
        assert_eq!(first["work_factor"], 2);
        assert_eq!(
            floor,
            first["programs"]
                .as_array()
                .unwrap()
                .iter()
                .map(|program| program["polls"].as_u64().unwrap())
                .max()
                .unwrap()
        );
        let limit = (2 * countdown_polls).max(floor);
        assert!(cause.contains(&format!("{limit}")), "{limit}: {cause}");
        assert_eq!(
            (entries[1].0.as_str(), entries[1].1.as_str(), entries[1].3),
            ("twice", "agree", false)
        );
        assert_eq!(first["outcome_cache"]["records_written"], 2, "{first:#}");

        // A re-run: both cells are cached, the unknown with the live run's cause, so the row is
        // decided with no call and no program's baseline runs.
        let second = search(&manifest);
        let row = row_of(&second);
        assert_eq!(row["calls"], serde_json::json!([]), "{row:#}");
        assert_eq!(
            executed(&second),
            [
                (
                    "countdown".to_owned(),
                    "unknown".to_owned(),
                    Some(cause.to_owned()),
                    true
                ),
                ("twice".to_owned(), "agree".to_owned(), None, true),
            ]
        );
        assert_eq!(second["outcome_cache"]["mutations_from_cache"], 1);
        assert_eq!(
            second["baseline_runs"]["live"], 0,
            "{:#}",
            second["baseline_runs"]
        );
        // Full, warm: the same cells, from the same store.
        let full = search_with(&manifest, kink_campaign::ScheduleMode::Full);
        assert_eq!(row_of(&full)["calls"], serde_json::json!([]));
        assert_eq!(executed(&full), executed(&second));

        // Another clock: no outcome depends on it, so the row is the cache's, cause for cause.
        set_budget(&manifest, 2, NO_CLOCK_MS / 10);
        let clocked_again = search(&manifest);
        assert_eq!(row_of(&clocked_again)["calls"], serde_json::json!([]));
        assert_eq!(executed(&clocked_again), executed(&second));
        let verdicts =
            |document: &Value| kink_flow::verdicts::verdicts(document).expect("a run rendering");
        assert_eq!(verdicts(&clocked_again), verdicts(&first));
        assert!(
            verdicts(&first).contains("\nwork_factor = 2\n"),
            "{}",
            verdicts(&first)
        );

        // A larger factor: only the cut run runs again, under its new bound; twice's run ended, so
        // it is the run without the bound, and its record serves the new bound too.
        set_factor(&manifest, 3);
        let raised = search(&manifest);
        let third = executed(&raised);
        assert_eq!(
            third
                .iter()
                .map(|(program, outcome, _, cached)| (program.as_str(), outcome.as_str(), *cached))
                .collect::<Vec<_>>(),
            // The cached cell first, then the live call's (search.rs, the assembled plan).
            [("twice", "agree", true), ("countdown", "unknown", false)],
            "{third:?}"
        );
        let raised_limit = (3 * countdown_polls).max(floor);
        let raised_cause = third[1].2.as_deref().unwrap();
        assert!(
            raised_cause.contains(&format!("{raised_limit}")),
            "{raised_limit}: {raised_cause}"
        );
        assert_eq!(raised["outcome_cache"]["records_written"], 1, "{raised:#}");
        assert!(
            verdicts(&raised).contains("\nwork_factor = 3\n"),
            "{}",
            verdicts(&raised)
        );

        // Under the fixture's clock and a factor so large that the clock fires first, the watchdog
        // stops countdown: a timeout, which depends on the host's load, so it is not written and
        // the next command runs it again (twice's agreement is cached under this context).
        let clocked =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/flow/loop/FLOW-search.toml");
        let dir = manifest.parent().unwrap().with_file_name("loop-clock");
        let _ = fs::remove_dir_all(&dir);
        copy_dir(clocked.parent().unwrap(), &dir);
        let clocked = dir.join("FLOW-search.toml");
        set_budget(&clocked, 1 << 40, 500);
        let cold = search_timeout(&clocked);
        assert_eq!(cold["outcome_cache"]["records_written"], 1, "{cold:#}");
        let warm = search_timeout(&clocked);
        assert_eq!(
            row_of(&warm)["calls"],
            serde_json::json!([{"programs": ["countdown"], "status": "timeout"}]),
            "{warm:#}"
        );
    }

    /// The `countdown-escapes` row of a document.
    fn row_of(document: &Value) -> &Value {
        document["mutations"]
            .as_array()
            .unwrap()
            .iter()
            .find(|m| m["id"] == "countdown-escapes")
            .unwrap()
    }

    /// A first-kill search of the clocked loop fixture, whose `countdown-escapes` times out.
    fn search_timeout(manifest: &Path) -> Value {
        let document = search(manifest);
        let row = row_of(&document);
        assert_eq!(row["status"], "timeout", "{row:#}");
        document
    }

    /// A private copy of `testdata/flow/diamonds` (or its `unguarded` directory) and its manifest.
    fn diamonds(test: &str, unguarded: bool) -> PathBuf {
        let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
            .join(format!("kink-flow-work-{}", std::process::id()))
            .join(test);
        let _ = fs::remove_dir_all(&dir);
        let from = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/flow/diamonds");
        copy_dir(
            &if unguarded {
                from.join("unguarded")
            } else {
                from
            },
            &dir,
        );
        dir.join("FLOW.toml")
    }

    /// `(status, killer, by-zero's outcome)` of the one mutation of the document.
    fn verdict(document: &Value) -> (String, Option<String>, String) {
        let [mutation] = document["mutations"].as_array().unwrap().as_slice() else {
            panic!("one mutation: {document:#}");
        };
        let outcome = mutation["executed"]
            .as_array()
            .unwrap()
            .iter()
            .find(|e| e["program"] == "by-zero")
            .map(|e| e["outcome"].as_str().unwrap().to_owned())
            .unwrap_or_default();
        (
            mutation["status"].as_str().unwrap().to_owned(),
            mutation["killer"].as_str().map(str::to_owned),
            outcome,
        )
    }

    /// fz26 KINK-PATHSET-FALLBACK, S9 (`testdata/flow/diamonds`): `end-guard-dropped` makes
    /// `go(14, 0)` end in one undefined step after 14 converging diamonds. The mutant's state set
    /// is complete in about 60 states, within `4 * W + 10000`, and `by-zero` kills through the
    /// exit stop (`{Stuck}` against the empty set) and the whole term (`{go(0, 0)}` against the
    /// empty set): an undefined step is no end (kink27 R1-UNDEF), so the mutant has none. Before
    /// the ticket kink replaced that state set by its path set, about 49 000 states, which the work
    /// budget cut: `by-zero` was `unknown` (2554 `trivial` leaves and one `work-bound`), and so
    /// was the mutation.
    #[test]
    #[ignore = "kink"]
    fn a_dropped_guard_after_converging_diamonds_is_killed_under_the_work_budget() {
        let manifest = diamonds("diamonds", false);
        assert_eq!(
            verdict(&search(&manifest)),
            (
                "killed".to_owned(),
                Some("by-zero".to_owned()),
                "distinguish".to_owned()
            )
        );
    }

    /// fz26 KINK-PATHSET-FALLBACK, S9, the baseline direction (`testdata/flow/diamonds/unguarded`):
    /// the baseline's run of `go(14, 0)` ends in one undefined step after 14 converging diamonds,
    /// and `end-guard-added` makes it stuck there. Both sides are complete state sets and `by-zero`
    /// kills. Before the ticket the baseline's state set was replaced by its path set, about
    /// 49 000 states, which the flow's 500 ms bound cuts (a baseline run has no work budget, so
    /// the clock is what separates the two; the margin is wide on both sides): `by-zero` was not
    /// comparable and the mutation survived.
    #[test]
    #[ignore = "kink"]
    fn an_added_guard_on_a_baseline_with_an_undefined_step_is_killed() {
        let manifest = diamonds("diamonds-unguarded", true);
        assert_eq!(
            verdict(&search(&manifest)),
            (
                "killed".to_owned(),
                Some("by-zero".to_owned()),
                "distinguish".to_owned()
            )
        );
    }
}
