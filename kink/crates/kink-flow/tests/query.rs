//! Per-input pattern checks: `PATTERNS.toml`, the lowering, the answers, the cache and
//! `kink-flow query` (flow F-18 deliverables 1-6).

use k_rust::backend::{
    BACKEND_SCHEMA_VERSION, CancelledResultOutput, ExecuteRequest, ExecutionStrategy,
    ResultModalityOutput, SearchPatternRequest, SearchTypeArg,
};
use k_rust::kore::{ast::Pattern, json as kore_json};
use kink_corpus::admission::input_backend;
use kink_flow::{
    FlowManifest, admit,
    cli::{EXIT_NO, EXIT_UNANSWERED, EXIT_UNASKED, EXIT_YES},
    pattern::{
        Answer, Facts, Lowering, PatternList, Route, SearchOutcome, Searcher, judge,
        search_modality, stopped_modality,
    },
    query::{QueryOptions, record_sha256},
    results::{CACHE_DIRECTORY, SIMPLIFICATION_ITERATIONS},
};
use kink_native::{
    exclusion::{DefinitionExclusions, HookReference},
    execution::SolverProfile,
};
use serde_json::{Value, json};
use std::{
    collections::{BTreeSet, VecDeque},
    fs,
    path::{Path, PathBuf},
    process::Command,
};

mod flow_support;

fn flow(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../testdata/flow")
        .join(name)
}

/// The answer to a pattern that a complete exploration never matches, in both profiles: the
/// fixtures' searches ask Z3 nothing it leaves undecided, so under Z3 each counts no undecided
/// solver answer and gives the `no` the portable profile gives (KINK-query-no-z3; before it, a
/// completed exploration was `unknown` under Z3).
const NO: &str = "no";

/// The exit status of a query some of whose unclaimed (pattern, program) pairs a complete
/// exploration never matches, every other pair hitting: `no` answers such a pair ([`NO`]).
const UNREACHED_STATUS: u8 = EXIT_YES;

/// The exit status of a query one of whose claims a complete exploration never matches, and no
/// pair of which could not be asked: the refuted claim is a finding ([`NO`]).
const REFUTED_STATUS: u8 = EXIT_NO;

/// The cause of a `no`: under Z3 the count that licensed it, without Z3 none.
fn no_cause() -> Value {
    if SolverProfile::BUILD == SolverProfile::Z3 {
        json!(
            "the exploration completed with no match, and the search received 0 undecided solver \
             answers, so no solver query it made was left undecided"
        )
    } else {
        Value::Null
    }
}

/// A fresh directory for one test, under the target's temporary directory.
fn scratch(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-query-{}", std::process::id()))
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

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

/// A private copy of a testdata/flow fixture.
fn fixture(name: &str, test: &str) -> PathBuf {
    let dir = scratch(test).join(name);
    copy_dir(&flow(name), &dir);
    dir
}

fn write(path: &Path, text: &str) {
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, text).unwrap();
}

/// `kink-flow query` on `manifest` and `patterns` (on a thread with the command's stack).
fn query(manifest: &Path, patterns: &Path, options: QueryOptions) -> (Value, u8) {
    let (manifest, patterns) = (manifest.to_path_buf(), patterns.to_path_buf());
    std::thread::Builder::new()
        .stack_size(kink_corpus::cli::DEFINITION_STACK_BYTES)
        .spawn(move || kink_flow::cli::query(&manifest, &patterns, &options))
        .unwrap()
        .join()
        .unwrap()
}

fn plain(manifest: &Path, patterns: &Path) -> (Value, u8) {
    query(manifest, patterns, QueryOptions::default())
}

/// `kink-flow query --full`: every (pattern, program) pair is asked, where a query without it
/// stops each pattern's obligation at its first hit.
fn full(manifest: &Path, patterns: &Path) -> (Value, u8) {
    query(
        manifest,
        patterns,
        QueryOptions {
            full: true,
            ..QueryOptions::default()
        },
    )
}

fn verify(manifest: &Path, patterns: &Path) -> (Value, u8) {
    query(
        manifest,
        patterns,
        QueryOptions {
            verify: true,
            ..QueryOptions::default()
        },
    )
}

/// The row of (`pattern`, `program`).
#[track_caller]
fn row<'a>(document: &'a Value, pattern: &str, program: &str) -> &'a Value {
    document["rows"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["pattern"] == pattern && row["program"] == program)
        .unwrap_or_else(|| panic!("no row ({pattern}, {program}) in {document:#}"))
}

/// `(pattern, program, answer)` of every row.
fn answers(document: &Value) -> Vec<(String, String, String)> {
    document["rows"]
        .as_array()
        .unwrap()
        .iter()
        .map(|row| {
            (
                row["pattern"].as_str().unwrap().to_owned(),
                row["program"].as_str().unwrap().to_owned(),
                row["answer"].as_str().unwrap().to_owned(),
            )
        })
        .collect()
}

fn expect(rows: &[(&str, &str, &str)]) -> Vec<(String, String, String)> {
    rows.iter()
        .map(|(p, q, a)| ((*p).to_owned(), (*q).to_owned(), (*a).to_owned()))
        .collect()
}

/// Whether each row whose answer the cache can hold (a `hit` or a `no`) was read from the cache.
fn cached(document: &Value) -> Vec<bool> {
    document["rows"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|row| cacheable(row))
        .map(|row| row["cached"].as_bool().unwrap())
        .collect()
}

/// Whether the cache can hold the answer of `row`.
fn cacheable(row: &Value) -> bool {
    matches!(row["answer"].as_str(), Some("hit" | "no"))
}

/// Every pattern record under the default cache of `dir`.
fn records(dir: &Path) -> Vec<PathBuf> {
    let mut found = Vec::new();
    let mut pending = vec![dir.join(CACHE_DIRECTORY).join("patterns")];
    while let Some(dir) = pending.pop() {
        let Ok(entries) = fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries {
            let path = entry.unwrap().path();
            if path.is_dir() {
                pending.push(path);
            } else {
                found.push(path);
            }
        }
    }
    found.sort();
    found
}

const CALC_PATTERNS: &str = r#"
[[pattern]]
id = "above-two"
pattern = "<k> I:Int </k> requires I >Int 2"
programs = ["add"]

[[pattern]]
id = "four"
note = "add's run never holds 4"
pattern = "<k> 4 </k>"
programs = ["add"]

[[pattern]]
id = "three"
pattern = "<k> 3 </k>"
"#;

/// Flow F-18 deliverable 1: decoding is strict and every error names its key.
#[test]
fn a_pattern_list_error_names_its_key() {
    for (text, key) in [
        (
            "[[pattern]]\nid = \"a\"\npattern = \"<k> 1 </k>\"\nprogram = [\"add\"]\n",
            "pattern \"a\".program",
        ),
        ("[[patterns]]\nid = \"a\"\n", "patterns"),
        ("[[pattern]]\npattern = \"<k> 1 </k>\"\n", "pattern[0].id"),
        (
            "[[pattern]]\nid = \"\"\npattern = \"<k> 1 </k>\"\n",
            "pattern[0].id",
        ),
        ("[[pattern]]\nid = \"a\"\n", "pattern \"a\".pattern"),
        (
            "[[pattern]]\nid = \"a\"\npattern = \"  \"\n",
            "pattern \"a\".pattern",
        ),
        (
            "[[pattern]]\nid = \"a\"\npattern = \"x\"\n[[pattern]]\nid = \"a\"\npattern = \"y\"\n",
            "pattern \"a\"",
        ),
        (
            "[[pattern]]\nid = \"a\"\npattern = \"x\"\nprograms = []\n",
            "pattern \"a\".programs",
        ),
        (
            "[[pattern]]\nid = \"a\"\npattern = \"x\"\nprograms = \"add\"\n",
            "pattern \"a\".programs",
        ),
        (
            "[[pattern]]\nid = \"a\"\npattern = \"x\"\nprograms = [\"add\", \"add\"]\n",
            "pattern \"a\".programs[1]",
        ),
        (
            "[[pattern]]\nid = \"a\"\npattern = \"x\"\nprograms = [1]\n",
            "pattern \"a\".programs[0]",
        ),
        (
            "[[pattern]]\nid = \"a\"\npattern = \"x\"\nnote = 3\n",
            "pattern \"a\".note",
        ),
    ] {
        let error = PatternList::decode(text).unwrap_err();
        assert_eq!(error.key, key, "{text}: {error}");
    }
    let list = PatternList::decode(CALC_PATTERNS).unwrap();
    assert_eq!(list.patterns.len(), 3);
    assert_eq!(
        list.patterns[1].note.as_deref(),
        Some("add's run never holds 4")
    );
    assert_eq!(list.patterns[2].programs, None);

    // A claim names a program the manifest does not have: the list is refused, nothing runs.
    let dir = fixture("calc", "unknown-claim");
    let patterns = dir.join("PATTERNS-bad.toml");
    write(
        &patterns,
        "[[pattern]]\nid = \"a\"\npattern = \"<k> 3 </k>\"\nprograms = [\"add\", \"nope\"]\n",
    );
    let (document, status) = plain(&dir.join("FLOW.toml"), &patterns);
    assert_eq!(status, EXIT_UNASKED);
    assert_eq!(document["pattern_list"]["outcome"], "refused");
    assert!(
        document["pattern_list"]["detail"]
            .as_str()
            .unwrap()
            .starts_with("pattern \"a\".programs[1]: "),
        "{document:#}"
    );
    assert!(!dir.join(CACHE_DIRECTORY).exists());
}

/// The `time_ms` of a test whose expected outcome comes from a deterministic bound: nextest stops a
/// test after ten minutes, so this clock fires only on a test that fails anyway, and the bound
/// decides every passing run (R4-WALLCLOCK).
const NO_CLOCK_MS: u64 = 600_000;

/// The loop flow with a depth bound of 50 and no clock that decides a run.
fn loop_bounded() -> String {
    format!(
        r#"
[spec]
entry = "loop.k"
main_module = "LOOP"
syntax_module = "LOOP-SYNTAX"

[budget]
time_ms = {NO_CLOCK_MS}
max_depth = 50

[[program]]
id = "spin"
file = "programs/spin.loop"

[[program]]
id = "countdown"
file = "programs/countdown.loop"
"#
    )
}

/// Flow F-18 deliverable 6: the initial configuration and the final one count.
#[test]
fn the_initial_and_the_final_states_count() {
    let dir = fixture("loop", "initial-final");
    let (document, status) = full(&dir.join("FLOW.toml"), &dir.join("PATTERNS.toml"));
    assert_eq!(status, UNREACHED_STATUS, "{document:#}");
    let start = row(&document, "countdown-starts", "countdown");
    assert_eq!(start["answer"], "hit");
    assert_eq!(start["claim"], "confirmed");
    assert_eq!(start["witness"]["depth"], 0);
    assert_eq!(start["witness"]["rules"], json!([]));
    // countdown(3) => countdown(2) => countdown(1) => countdown(0) => 0: only the final state.
    let end = row(&document, "zero", "countdown");
    assert_eq!(end["answer"], "hit");
    assert_eq!(end["witness"]["depth"], 4);
    assert_eq!(
        end["witness"]["rules"],
        json!([
            "LOOP.countdown",
            "LOOP.countdown",
            "LOOP.countdown",
            "LOOP.done"
        ])
    );
    assert_eq!(row(&document, "zero", "twice")["answer"], NO);
}

const NONDETERMINISTIC: &str = r#"
[spec]
entry = "calc.k"
main_module = "CALC"
syntax_module = "CALC-SYNTAX"

[[program]]
id = "both"
text = "(1 + 2) + (3 + 4)"
"#;

const ORDERS: &str = r#"
[[pattern]]
id = "left-first"
pattern = "<k> 3 + (3 + 4) </k>"

[[pattern]]
id = "right-first"
pattern = "<k> (1 + 2) + 7 </k>"

[[pattern]]
id = "never"
pattern = "<k> 3 + 3 </k>"
"#;

/// Flow F-18 deliverable 6: `+` is strict, so `(1 + 2) + (3 + 4)` has a path that evaluates the
/// left operand first and one that evaluates the right one first. Each order's intermediate state
/// is on some paths only, and each is a hit: the answer is "some path hits".
#[test]
fn a_state_on_some_paths_only_is_a_hit() {
    let dir = fixture("calc", "some-paths");
    let manifest = dir.join("FLOW-both.toml");
    write(&manifest, NONDETERMINISTIC);
    let patterns = dir.join("PATTERNS-orders.toml");
    write(&patterns, ORDERS);
    let (document, status) = plain(&manifest, &patterns);
    assert_eq!(status, UNREACHED_STATUS, "{document:#}");
    assert_eq!(
        answers(&document),
        expect(&[
            ("left-first", "both", "hit"),
            ("right-first", "both", "hit"),
            ("never", "both", NO),
        ])
    );
    assert_eq!(
        row(&document, "left-first", "both")["witness"]["rules"],
        json!(["CALC-SYNTAX.add1-heat", "CALC.add", "CALC-SYNTAX.add1-cool"])
    );
    assert_eq!(
        row(&document, "right-first", "both")["witness"]["rules"],
        json!(["CALC-SYNTAX.add2-heat", "CALC.add", "CALC-SYNTAX.add2-cool"])
    );
}

const CENSUS_SPEC: &str = r#"
// A rule lists a map's keys, an order domains.md does not fix and k-rust chooses (re-pin R0b,
// decision 1: testdata/k/r0b/implchosen.k).
module IMPLCHOSEN-SYNTAX
  imports INT-SYNTAX
  imports LIST
  syntax Prog ::= start(Int) [symbol(start)]
                | keys(List) [symbol(keys)]
                | count(Int) [symbol(count)]
endmodule
module IMPLCHOSEN
  imports IMPLCHOSEN-SYNTAX
  imports INT
  imports MAP
  imports LIST
  configuration <k> $PGM:Prog </k>
  rule [start]: <k> start(I) => keys(keys_list((1 |-> I) (2 |-> I))) </k>
  rule [count]: <k> count(I) => keys(ListItem(I)) </k>
endmodule
"#;

const PICK_SPEC: &str = r#"
// kink27 R3-CENSUS-RUNLEVEL (gap G1): the pattern holds `lst()`, whose equation lists a map's keys
// in an order the definition leaves open. k-rust lists 1 then 2; the run reaches
// `keys(ListItem(2) ListItem(1))`, which a model listing 2 then 1 matches. Only the pattern's
// matching reads the order.
module PICK-SYNTAX
  imports INT-SYNTAX
  imports LIST
  syntax Prog ::= pair(Int) [symbol(pair)]
  syntax Prog ::= keys(List) [symbol(keys)]
  syntax List ::= lst() [function, symbol(lst)]
endmodule
module PICK
  imports PICK-SYNTAX
  imports INT
  imports MAP
  imports LIST
  configuration <k> $PGM:Prog </k>
  rule lst() => keys_list((1 |-> 0) (2 |-> 0))
  rule [pair]: <k> pair(I) => keys(ListItem(I +Int 1) ListItem(I)) </k>
endmodule
"#;

fn exclusions() -> DefinitionExclusions {
    DefinitionExclusions::default()
}

fn facts<'a>(
    exclusions: &'a DefinitionExclusions,
    class: &'a str,
    profile: SolverProfile,
) -> Facts<'a> {
    Facts {
        exclusions,
        state: None,
        baseline_class: Some(class),
        baseline_cause: None,
        profile,
        no_data: None,
        route: Route::Search,
    }
}

/// Flow F-18: the answer rules, one premise at a time. A completed exploration is a `no` only on a
/// comparable baseline, a definition with no exclusion (a rule the short-circuit analysis flags is
/// none: the search's own readings decide, before the rules), an initial state with none, and
/// a search that received no undecided solver answer, in either profile (under Z3 the `no`'s cause
/// names that count); a hit stays a hit under every model-choice exclusion, and no answer is
/// given on a load stack stop or an equals condition.
#[test]
fn the_answer_rules() {
    let clean = exclusions();
    let hit = SearchOutcome::Hit(json!({"depth": 0}));
    let complete = SearchOutcome::Complete { smt_unknowns: 0 };
    let no = judge(&complete, &facts(&clean, "comparable", SolverProfile::NoZ3));
    assert_eq!(no.answer, "no");
    assert_eq!(no.cause, None);
    assert_eq!(
        judge(&hit, &facts(&clean, "timeout", SolverProfile::NoZ3)).answer,
        "hit"
    );
    for class in ["timeout", "unknown", "error", "refused"] {
        let answer = judge(&complete, &facts(&clean, class, SolverProfile::NoZ3));
        assert_eq!(answer.answer, "unknown", "{class}");
        assert!(
            answer
                .cause
                .unwrap()
                .contains(&format!("and it is {class}"))
        );
    }
    // KINK-query-no-z3: under Z3 a completed search that received no undecided solver answer is
    // a `no` whose cause names the count; one that received some is `unknown` with the count,
    // whatever the baseline (the count is read before it).
    let z3 = judge(&complete, &facts(&clean, "comparable", SolverProfile::Z3));
    assert_eq!(z3.answer, "no");
    assert!(
        z3.cause
            .as_deref()
            .unwrap()
            .contains("the search received 0 undecided solver answers"),
        "{z3:?}"
    );
    // FB-41: on the stopped route the cause names the three counts the run's answer sums.
    let stopped = Facts {
        route: Route::StoppedRun,
        ..facts(&clean, "comparable", SolverProfile::Z3)
    };
    let z3 = judge(&complete, &stopped);
    assert_eq!(z3.answer, "no");
    assert!(
        z3.cause.as_deref().unwrap().contains(
            "its run, its leaves' feasibility questions and its matcher received 0 undecided \
             solver answers"
        ),
        "{z3:?}"
    );
    let undecided = SearchOutcome::Complete { smt_unknowns: 2 };
    for (profile, class) in [
        (SolverProfile::Z3, "comparable"),
        (SolverProfile::Z3, "timeout"),
        (SolverProfile::NoZ3, "comparable"),
    ] {
        let answer = judge(&undecided, &facts(&clean, class, profile));
        assert_eq!(answer.answer, "unknown", "{profile:?} {class}");
        assert!(
            answer
                .cause
                .as_deref()
                .unwrap()
                .contains("the search received 2 undecided solver answer(s)"),
            "{answer:?}"
        );
    }
    assert_eq!(
        judge(&hit, &facts(&clean, "comparable", SolverProfile::Z3)).answer,
        "hit"
    );

    let mut census = exclusions();
    census.implementation_chosen.push(HookReference {
        module: "M".into(),
        sentence: "r".into(),
        symbol: "Lblkeys'Unds'list".into(),
        hook: "MAP.keys_list".into(),
    });
    // CF-03: a rule the short-circuit analysis flags is no definition exclusion; the search's
    // own list of readings decides (pattern `outcome`), so the rules give a no here.
    let mut short = exclusions();
    short.short_circuit_conditions.push("r".into());
    assert_eq!(
        judge(&complete, &facts(&short, "comparable", SolverProfile::NoZ3)).answer,
        "no"
    );
    let answer = judge(
        &complete,
        &facts(&census, "comparable", SolverProfile::NoZ3),
    );
    assert_eq!(answer.answer, "unknown");
    assert!(answer.cause.unwrap().contains("implementation-chosen-hook"));
    assert_eq!(
        judge(&hit, &facts(&census, "comparable", SolverProfile::NoZ3)).answer,
        "hit"
    );
    assert_eq!(
        judge(&hit, &facts(&short, "comparable", SolverProfile::NoZ3)).answer,
        "hit"
    );
    let state = Facts {
        state: Some(kink_native::exclusion::Exclusion::ImplementationChosenHook),
        ..facts(&clean, "comparable", SolverProfile::NoZ3)
    };
    assert_eq!(judge(&complete, &state).answer, "unknown");
    assert_eq!(judge(&hit, &state).answer, "hit");
    // Final review K3: a definition without data (a finding no name assumes, or a check that did
    // not read the whole definition) gives no `no`, whichever made it so; a hit stands.
    let without_data = Facts {
        no_data: Some(
            "the definition's full critical-pair check did not read the whole \
                       definition (2 simplifications of the check ran out of native stack)"
                .into(),
        ),
        ..facts(&clean, "comparable", SolverProfile::NoZ3)
    };
    let answer = judge(&complete, &without_data);
    assert_eq!(answer.answer, "unknown");
    assert!(answer.cause.unwrap().contains("ran out of native stack"));
    assert_eq!(judge(&hit, &without_data).answer, "hit");

    let mut load = exclusions();
    load.load_stack_stops = 1;
    let mut equals = exclusions();
    equals.equals_conditions.push("r".into());
    for (exclusions, name) in [(&load, "load-stack-stop"), (&equals, "equals-condition")] {
        for outcome in [&hit, &complete] {
            let answer = judge(
                outcome,
                &facts(exclusions, "comparable", SolverProfile::NoZ3),
            );
            assert_eq!(answer.answer, "unknown");
            assert!(answer.cause.unwrap().contains(name));
        }
    }
    let incomplete = judge(
        &SearchOutcome::Incomplete("a path reached max_depth = 5".into()),
        &facts(&clean, "comparable", SolverProfile::NoZ3),
    );
    assert_eq!(incomplete, Answer::unknown("a path reached max_depth = 5"));
    assert_eq!(
        judge(
            &SearchOutcome::Failed("refused".into()),
            &facts(&clean, "comparable", SolverProfile::NoZ3)
        )
        .answer,
        "error"
    );
}

/// CF-03: on a definition whose short-circuit analysis flags the rule `at` (its successor
/// applies `andThenBool` over `10 /Int I >Int 0`), a completed exploration gives a `no` exactly
/// when the search's list of short-circuit readings holds no entry that counts: from `at(1)` the
/// search reads a defined operand and `res(true)` is refuted (a `no`, which before CF-03 no
/// flagged definition gave), while from `at(0)` it reads `10 /Int 0 >Int 0`, which a backend that
/// evaluates the deciding `false` alone skips, so the answer is `unknown` with the step named; a
/// hit stands whatever the list holds.
#[test]
fn a_no_on_a_flagged_definition_needs_a_search_without_counting_readings() {
    let dir = scratch("short-circuit-no");
    write(
        &dir.join("scr.k"),
        r"module SCR-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Prog ::= at(Int) [symbol(at)] | res(Bool) [symbol(res)]
endmodule

module SCR
  imports SCR-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Prog </k>
  rule [at]: <k> at(I) => res(false andThenBool 10 /Int I >Int 0) </k>
endmodule
",
    );
    write(
        &dir.join("FLOW.toml"),
        "[spec]\nentry = \"scr.k\"\nmain_module = \"SCR\"\nsyntax_module = \"SCR-SYNTAX\"\n\n\
         [[program]]\nid = \"zero\"\ntext = \"at(0)\"\n\n[[program]]\nid = \"one\"\ntext = \"at(1)\"\n",
    );
    write(
        &dir.join("PATTERNS.toml"),
        "[[pattern]]\nid = \"true\"\npattern = \"<k> res(true) </k>\"\n\n\
         [[pattern]]\nid = \"start\"\npattern = \"<k> at(_) </k>\"\n",
    );
    let (document, status) = full(&dir.join("FLOW.toml"), &dir.join("PATTERNS.toml"));
    assert_eq!(status, EXIT_UNANSWERED, "{document:#}");
    assert_eq!(row(&document, "true", "one")["answer"], NO, "{document:#}");
    let zero = row(&document, "true", "zero");
    assert_eq!(zero["answer"], "unknown", "{zero:#}");
    let cause = zero["cause"].as_str().unwrap();
    for part in [
        "short-circuit-reading",
        "in the work of rule SCR.at",
        "the operand of BOOL.andThen after its deciding one",
        "undefined",
    ] {
        assert!(cause.contains(part), "{part:?} in {cause}");
    }
    for program in ["zero", "one"] {
        assert_eq!(
            row(&document, "start", program)["answer"],
            "hit",
            "{program}"
        );
    }
}

/// A definition whose only rule rewrites `go(N)` to `res(f(N))`, where `f`'s equations are
/// guarded by conditions over `h(N) *Int h(N)`, which no equation of `h` reduces: only the solver
/// decides them (a square is never negative), so the end is `res(1)` under Z3 and `res(f(3))`,
/// with `f(3)` left unevaluated, without it.
const UNDECIDED_SPEC: &str = r"module UNDECIDED-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= go(Int) [symbol(go)]
               | res(Int) [symbol(res)]
endmodule

module UNDECIDED
  imports UNDECIDED-SYNTAX
  imports INT
  configuration <k> $PGM:Pgm </k>

  syntax Int ::= h(Int) [function, total, symbol(h)]
  syntax Int ::= f(Int) [function, total, symbol(f)]

  rule f(N) => 1 requires h(N) *Int h(N) >=Int 0
  rule f(N) => 0 requires h(N) *Int h(N) <Int 0

  rule [step]: <k> go(N) => res(f(N)) </k>
endmodule
";

/// KINK-query-no-z3: a completed exploration is a `no` exactly when the search received no
/// undecided solver answer. Under Z3, with the default resource units the equation conditions of
/// [`UNDECIDED_SPEC`] are decided, the search counts none, and `go(4)` (never reached) is a `no`
/// whose cause names the count, while `res(1)` is a hit; with one unit per first attempt (set
/// through the manifest's budget, not the clock) Z3 decides neither condition, `f(3)` stays
/// unevaluated, the exploration still completes, and the answer is `unknown` with the count.
/// Without Z3 no answer is ever undecided, and the run that leaves `f(3)` unevaluated is not
/// comparable, so `go(4)` is `unknown` for its baseline as before.
#[test]
fn a_no_needs_a_search_without_undecided_solver_answers() {
    let dir = scratch("undecided-solver-answers");
    write(&dir.join("undecided.k"), UNDECIDED_SPEC);
    let spec = "[spec]\nentry = \"undecided.k\"\nmain_module = \"UNDECIDED\"\n\
                syntax_module = \"UNDECIDED-SYNTAX\"\n\n\
                [[program]]\nid = \"three\"\ntext = \"go(3)\"\n";
    // R4-WALLCLOCK: the clock is never what ends these searches and runs.
    write(
        &dir.join("FLOW.toml"),
        &format!("[budget]\ntime_ms = 600000\n\n{spec}"),
    );
    write(
        &dir.join("FLOW-units.toml"),
        &format!("[budget]\ntime_ms = 600000\nsmt_resource_limit = 1\n\n{spec}"),
    );
    write(
        &dir.join("PATTERNS.toml"),
        "[[pattern]]\nid = \"unreached\"\npattern = \"<k> go(4) </k>\"\n\n\
         [[pattern]]\nid = \"one\"\npattern = \"<k> res(1) </k>\"\n",
    );
    let (document, status) = plain(&dir.join("FLOW.toml"), &dir.join("PATTERNS.toml"));
    let unreached = row(&document, "unreached", "three");
    if SolverProfile::BUILD == SolverProfile::Z3 {
        assert_eq!(status, EXIT_YES, "{document:#}");
        assert_eq!(unreached["answer"], "no", "{unreached:#}");
        assert_eq!(unreached["cause"], no_cause(), "{unreached:#}");
        assert_eq!(row(&document, "one", "three")["answer"], "hit");

        let (units, status) = plain(&dir.join("FLOW-units.toml"), &dir.join("PATTERNS.toml"));
        assert_eq!(status, EXIT_UNANSWERED, "{units:#}");
        let unreached = row(&units, "unreached", "three");
        assert_eq!(unreached["answer"], "unknown", "{unreached:#}");
        let cause = unreached["cause"].as_str().unwrap();
        assert!(
            cause.starts_with("the exploration completed with no match, but a no is not given")
                && cause.contains("undecided solver answer(s)")
                && !cause.contains("received 0 "),
            "{unreached:#}"
        );
        // The run that leaves `f(3)` unevaluated also counted the undecided answers.
        let program = &units["programs"][0];
        assert!(program["smt_unknowns"].as_u64().unwrap() > 0, "{program:#}");
        assert_eq!(row(&units, "one", "three")["answer"], "unknown");
    } else {
        assert_eq!(status, EXIT_UNANSWERED, "{document:#}");
        assert_eq!(unreached["answer"], "unknown", "{unreached:#}");
        let cause = unreached["cause"].as_str().unwrap();
        assert!(
            cause.contains("a no also needs the program's baseline run to be comparable")
                && !cause.contains("undecided solver answer"),
            "{unreached:#}"
        );
        assert_eq!(document["programs"][0]["smt_unknowns"], 0, "{document:#}");
    }
}

/// FB-41: on a corpus with `[stop]` (here after `step`, whose successor `res(f(3))` is the run's
/// last state) a (pattern, program) is answered by the program's stopped run, and a `no` needs
/// every count of undecided solver answers the run's answer sums to be zero: the run's, its
/// leaves' feasibility questions' and its matcher's. Under Z3 with the default units `go(4)` is a
/// `no` whose cause names those counts and `res(1)` a hit; with one unit per first attempt Z3
/// decides neither condition of `f`, the run counts undecided answers and leaves their diagnostic
/// on its leaf, and `go(4)` is `unknown` (`diagnosed-leaf`, the first premise it misses). Without Z3 the run that leaves `f(3)` unevaluated is not comparable, so
/// `go(4)` is `unknown`. Each answer's key names the stop and the stopped route's modality; the
/// stopless corpus's key names neither, as before the stopped route existed.
#[test]
fn a_stopped_no_needs_every_count_of_undecided_solver_answers_zero() {
    let dir = scratch("stopped-undecided-solver-answers");
    write(&dir.join("undecided.k"), UNDECIDED_SPEC);
    let spec = "[spec]\nentry = \"undecided.k\"\nmain_module = \"UNDECIDED\"\n\
                syntax_module = \"UNDECIDED-SYNTAX\"\n\n\
                [[program]]\nid = \"three\"\ntext = \"go(3)\"\n";
    let stop = "[stop]\nafter = [\"UNDECIDED.step\"]\n\n";
    write(
        &dir.join("FLOW.toml"),
        &format!("[budget]\ntime_ms = 600000\n\n{spec}"),
    );
    write(
        &dir.join("FLOW-stop.toml"),
        &format!("[budget]\ntime_ms = 600000\n\n{stop}{spec}"),
    );
    write(
        &dir.join("FLOW-units.toml"),
        &format!("[budget]\ntime_ms = 600000\nsmt_resource_limit = 1\n\n{stop}{spec}"),
    );
    write(
        &dir.join("PATTERNS.toml"),
        "[[pattern]]\nid = \"unreached\"\npattern = \"<k> go(4) </k>\"\n\n\
         [[pattern]]\nid = \"one\"\npattern = \"<k> res(1) </k>\"\n",
    );
    let cache = |name: &str| QueryOptions {
        cache: Some(dir.join(name)),
        ..QueryOptions::default()
    };
    let (document, _) = query(
        &dir.join("FLOW-stop.toml"),
        &dir.join("PATTERNS.toml"),
        cache("stop"),
    );
    assert_eq!(document["version"], 8, "{document:#}");
    assert_eq!(
        document["stop"],
        json!({"before": [], "after": ["UNDECIDED.step"], "count": 1}),
        "{document:#}"
    );
    let unreached = row(&document, "unreached", "three");
    assert_eq!(unreached["route"], "stopped-run", "{unreached:#}");
    if SolverProfile::BUILD == SolverProfile::Z3 {
        assert_eq!(unreached["answer"], "no", "{unreached:#}");
        assert!(
            unreached["cause"].as_str().unwrap().contains(
                "its run, its leaves' feasibility questions and its matcher received 0 \
                 undecided solver answers"
            ),
            "{unreached:#}"
        );
        let one = row(&document, "one", "three");
        assert_eq!(one["answer"], "hit", "{one:#}");
        assert_eq!(one["witness"]["depth"], 1, "{one:#}");
        assert_eq!(one["witness"]["rules"], Value::Null, "{one:#}");

        let (units, status) = query(
            &dir.join("FLOW-units.toml"),
            &dir.join("PATTERNS.toml"),
            cache("units"),
        );
        assert_eq!(status, EXIT_UNANSWERED, "{units:#}");
        let unreached = row(&units, "unreached", "three");
        assert_eq!(unreached["answer"], "unknown", "{unreached:#}");
        // The undecided conditions of `f` leave their diagnostic on the run's one leaf, which is
        // the first premise the answer misses; the run counted the undecided answers too.
        assert!(
            unreached["cause"]
                .as_str()
                .unwrap()
                .contains("(diagnosed-leaf)"),
            "{unreached:#}"
        );
        let program = &units["programs"][0];
        assert!(program["smt_unknowns"].as_u64().unwrap() > 0, "{program:#}");
        assert_ne!(row(&units, "one", "three")["answer"], "hit", "{units:#}");
    } else {
        assert_eq!(unreached["answer"], "unknown", "{unreached:#}");
        assert!(
            unreached["cause"]
                .as_str()
                .unwrap()
                .contains("a no also needs the program's baseline run to be comparable"),
            "{unreached:#}"
        );
    }
    // The keys: the stopped route's names the stop and its modality, the stopless one's neither.
    let (plain_document, _) = query(
        &dir.join("FLOW.toml"),
        &dir.join("PATTERNS.toml"),
        cache("plain"),
    );
    assert_eq!(row(&plain_document, "one", "three")["route"], "search");
    assert_eq!(plain_document.get("stop"), None, "{plain_document:#}");
    let keys = |cache: &str| {
        let mut found = Vec::new();
        let mut pending = vec![dir.join(cache).join("patterns")];
        while let Some(dir) = pending.pop() {
            for entry in fs::read_dir(&dir).into_iter().flatten() {
                let path = entry.unwrap().path();
                if path.is_dir() {
                    pending.push(path);
                } else {
                    let record: Value =
                        serde_json::from_str(&fs::read_to_string(&path).unwrap()).unwrap();
                    found.push(record["key"].clone());
                }
            }
        }
        found
    };
    // Under Z3 both corpora have answers the cache holds.
    let z3 = SolverProfile::BUILD == SolverProfile::Z3;
    let stopped = keys("stop");
    assert!(!z3 || !stopped.is_empty());
    for key in stopped {
        assert_eq!(
            key["stop"],
            json!({"before": [], "after": ["UNDECIDED.step"], "count": 1}),
            "{key:#}"
        );
        assert_eq!(key["modality"], stopped_modality(), "{key:#}");
    }
    let plain_keys = keys("plain");
    assert!(!z3 || !plain_keys.is_empty());
    for key in plain_keys {
        assert_eq!(key.get("stop"), None, "{key:#}");
        assert_eq!(key["modality"], search_modality(), "{key:#}");
    }
}

fn execute_request(state: Pattern, max_depth: u64) -> ExecuteRequest {
    ExecuteRequest {
        state,
        module_name: None,
        max_depth: Some(max_depth),
        max_breadth: None,
        max_simplification_iterations: SIMPLIFICATION_ITERATIONS,
        strategy: ExecutionStrategy::All,
        stop_at_branch: false,
        cut_point_rules: Vec::new(),
        terminal_rules: Vec::new(),
        stop_count: None,
        step_timeout_ms: None,
        moving_average_timeout: false,
        assume_state_defined: false,
        result_modality: ResultModalityOutput::StateSet,
        collect_coverage: false,
        collect_offered: false,
        collect_counts: false,
        collect_conditions: None,
        collect_guards: None,
        collect_bindings: None,
        max_work: None,
        max_polls: None,
        trace: false,
        cancelled_result: CancelledResultOutput::Error,
        match_states: None,
        collect_committed: false,
        collect_windows: None,
        schema_version: BACKEND_SCHEMA_VERSION,
    }
}

fn decode(state: &Value) -> Pattern {
    let envelope = if state.get("format").is_some() {
        state.clone()
    } else {
        json!({"format": "KORE", "version": 1, "term": state})
    };
    kore_json::from_str(&envelope.to_string()).unwrap()
}

/// One manifest's admitted specification and programs, for the stepping walk.
struct Stepper {
    manifest: FlowManifest,
    admission: kink_flow::FlowAdmission,
}

impl Stepper {
    fn new(manifest: &Path) -> Self {
        let manifest = FlowManifest::read(manifest).unwrap();
        let admission = admit(&manifest);
        Self {
            manifest,
            admission,
        }
    }

    /// Whether some state stepping reaches from `program`'s initial state matches `pattern`: the
    /// state set explored one step at a time through `execute` (max_depth 1 from each new state),
    /// each state matched alone (a search of depth 0). `None` when a step does not end stuck or
    /// with successors, or the walk passes `limit` states.
    fn hit(&self, program: &str, pattern: &str, limit: usize) -> Option<bool> {
        let spec = self.admission.spec.as_ref().unwrap();
        let main = &self.manifest.spec.main_module;
        let test = self
            .admission
            .programs
            .iter()
            .find(|p| p.id == program)
            .unwrap()
            .outcome
            .as_ref()
            .unwrap();
        let searcher = Searcher::new(spec, main, self.manifest.budget).unwrap();
        let lowered = Lowering::new(spec, main)
            .unwrap()
            .lower(pattern, searcher.definition())
            .unwrap();
        let mut backend = input_backend(&spec.compiled, main).unwrap();
        let leaves = |backend: &mut k_rust::backend::Backend, state: Pattern, depth: u64| {
            let out = backend.execute_json(execute_request(state, depth)).unwrap();
            let result: Value = serde_json::from_str(&out).unwrap();
            result["leaves"].as_array().unwrap().clone()
        };
        let mut visited = BTreeSet::new();
        let mut queue = VecDeque::new();
        for leaf in leaves(&mut backend, test.initial_state.clone(), 0) {
            if visited.insert(leaf["state"].to_string()) {
                queue.push_back(leaf["state"].clone());
            }
        }
        while let Some(state) = queue.pop_front() {
            let matched = backend
                .search_pattern_json(SearchPatternRequest {
                    state: decode(&state),
                    pattern: lowered.target.clone(),
                    module_name: None,
                    search_type: SearchTypeArg::All,
                    max_depth: Some(0),
                    max_breadth: None,
                    max_results: Some(1),
                    max_simplification_iterations: SIMPLIFICATION_ITERATIONS,
                    schema_version: BACKEND_SCHEMA_VERSION,
                })
                .unwrap();
            let matched: Value = serde_json::from_str(&matched).unwrap();
            if !matched["matches"].as_array().unwrap().is_empty() {
                return Some(true);
            }
            for leaf in leaves(&mut backend, decode(&state), 1) {
                match (leaf["depth"].as_u64(), leaf["reason"].as_str()) {
                    (Some(1), Some("depth-bound")) => {
                        if visited.insert(leaf["state"].to_string()) {
                            if visited.len() > limit {
                                return None;
                            }
                            queue.push_back(leaf["state"].clone());
                        }
                    }
                    (_, Some("stuck")) => {}
                    _ => return None,
                }
            }
        }
        Some(false)
    }
}

/// The example of the crate README's `PATTERNS.toml` section decodes and answers on the calc
/// fixture.
#[test]
fn the_readme_example_answers() {
    let readme = include_str!("../README.md");
    let section = &readme[readme.find("### `PATTERNS.toml`").unwrap()..];
    let block = &section[section.find("```toml\n").unwrap() + 8..];
    let block = &block[..block.find("```").unwrap()];
    let list = PatternList::decode(block).unwrap();
    assert_eq!(list.patterns.len(), 2);
    let dir = fixture("calc", "readme");
    let patterns = dir.join("PATTERNS-readme.toml");
    write(&patterns, block);
    let (document, status) = plain(&dir.join("FLOW.toml"), &patterns);
    assert_eq!(status, UNREACHED_STATUS, "{document:#}");
    assert_eq!(
        answers(&document),
        expect(&[
            ("result-three", "add", "hit"),
            ("result-three", "sub", "hit"),
            // The obligation stops at its first hit in corpus order, its witness.
            ("result-above-five", "add", NO),
            ("result-above-five", "nested", "hit"),
        ])
    );
    let obligations = document["obligations"].as_array().unwrap();
    assert_eq!(obligations[0]["witness"], "add", "{document:#}");
    assert_eq!(obligations[1]["witness"], "nested", "{document:#}");
}

const CELLS_SPEC: &str = r#"
module CELLS-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int | "tick" "(" Int ")" [symbol(tick)]
endmodule
module CELLS
  imports CELLS-SYNTAX
  imports INT
  imports LIST
  configuration <T> <k> $PGM:Exp </k> <out> .List </out> <count> 0 </count> </T>
  rule <k> tick(I) => tick(I -Int 1) </k> <out> ... .List => ListItem(I) </out>
       <count> C => C +Int 1 </count> requires I >Int 0
  rule <k> tick(0) => 0 </k>
endmodule
"#;

/// FB-51's fixture: `<rom>` and `<out>` grow by one element per step, and the last step writes
/// one entry of `<mem>`.
const ROM_SPEC: &str = r#"
module ROM-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= "fill" "(" Int ")" [symbol(fill)] | "done" [symbol(done)]
endmodule
module ROM
  imports ROM-SYNTAX
  imports INT
  imports LIST
  imports MAP
  configuration <T> <k> $PGM:Exp </k> <rom> .List </rom> <out> .List </out> <mem> .Map </mem> </T>
  rule <k> fill(I) => fill(I -Int 1) </k> <rom> ... .List => ListItem(I) </rom>
       <out> ... .List => ListItem(I *Int 2) </out> requires I >Int 0
  rule <k> fill(0) => done </k> <mem> M => M[7 <- 42] </mem>
endmodule
"#;

/// The F-18 review's repro (scratch-F-18-review/repro-partial2): `f` is partial, and no
/// equation covers `f(3)`.
const PARTIAL_SPEC: &str = r#"
module CALCP-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int
               | "(" Exp ")" [bracket]
               > left:
                 Exp "+" Exp [strict, symbol(add)]
endmodule

module CALCP
  imports CALCP-SYNTAX
  imports INT
  configuration <k> $PGM:Exp </k>
  syntax KResult ::= Int
  syntax Exp ::= g(Int) [symbol(g)]
  // f is partial: its only equation covers 0
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(0) => 7
  rule [add]: I1:Int + I2:Int => I1 +Int I2
  rule [tof]: <k> 3 => g(f(3)) </k>
  rule [done]: <k> g(_) => 100 </k>
endmodule
"#;

/// The review's contrast (scratch-F-18-review/repro-partial): `h` is declared total, with no
/// equation at 3 either, so `g(h(3))` exists in every model.
const TOTAL_SPEC: &str = r#"
module CALCG-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int
               | "(" Exp ")" [bracket]
               > left:
                 Exp "+" Exp [strict, symbol(add)]
endmodule

module CALCG
  imports CALCG-SYNTAX
  imports INT
  configuration <k> $PGM:Exp </k>
  syntax KResult ::= Int
  syntax Exp ::= g(Int) [symbol(g)]
  syntax Int ::= f(Int) [function, symbol(f)]
  syntax Int ::= h(Int) [function, total, symbol(h)]
  rule f(0) => 7
  rule h(0) => 7
  rule [add]: I1:Int + I2:Int => I1 +Int I2
  rule [tof]: <k> 3 => g(f(3)) </k>
  rule [toh]: <k> 4 => g(h(3)) </k>
endmodule
"#;

/// A state with a map, whose element, concatenation and unit k-rust holds as one collection.
const STORE_SPEC: &str = r#"
module STORE-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int | "start" [symbol(start)]
endmodule
module STORE
  imports STORE-SYNTAX
  imports INT
  imports MAP
  configuration <T> <k> $PGM:Exp </k> <store> .Map </store> </T>
  rule <k> start => 0 </k> <store> _ => (1 |-> 10) (2 |-> 20) </store>
endmodule
"#;

fn spec_dir(
    test: &str,
    file: &str,
    module: &str,
    spec: &str,
    programs: &str,
    patterns: &str,
) -> PathBuf {
    let dir = scratch(test);
    write(&dir.join(file), spec);
    write(
        &dir.join("FLOW.toml"),
        &format!(
            "[spec]\nentry = \"{file}\"\nmain_module = \"{module}\"\nsyntax_module = \
             \"{module}-SYNTAX\"\n\n{programs}"
        ),
    );
    write(&dir.join("PATTERNS.toml"), patterns);
    dir
}

/// The result record of `program` in `document`'s cache under `dir`.
fn result_record(dir: &Path, document: &Value, program: &str) -> PathBuf {
    let digest = document["programs"]
        .as_array()
        .unwrap()
        .iter()
        .find(|p| p["id"] == program)
        .unwrap()["digest"]
        .as_str()
        .unwrap()
        .to_owned();
    dir.join(CACHE_DIRECTORY)
        .join("results")
        .join(
            document["spec"]["execution_digest"]["digest"]
                .as_str()
                .unwrap(),
        )
        .join(format!("{digest}.json"))
}

/// Rewrite one field of a JSON file.
fn forge(path: &Path, field: &str, value: Value) {
    let mut record: Value = serde_json::from_str(&fs::read_to_string(path).unwrap()).unwrap();
    record[field] = value;
    fs::write(path, serde_json::to_string(&record).unwrap()).unwrap();
}

/// The obligation of `pattern` in a query document.
#[track_caller]
/// The entry of a witness's state for the cell whose label is `label` (the last of its path).
fn witness_cell<'a>(witness: &'a Value, label: &str) -> &'a Value {
    witness["state"]["cells"]
        .as_array()
        .unwrap_or_else(|| panic!("a witness lists its cells: {witness:#}"))
        .iter()
        .find(|cell| cell["path"].as_array().and_then(|path| path.last()) == Some(&json!(label)))
        .unwrap_or_else(|| panic!("no cell {label}: {witness:#}"))
}

fn obligation<'a>(document: &'a Value, pattern: &str) -> &'a Value {
    document["obligations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|obligation| obligation["id"] == pattern)
        .unwrap_or_else(|| panic!("no obligation {pattern} in {document:#}"))
}

/// Each obligation's `(id, status, witness)`, in the document's order.
fn obligations(document: &Value) -> Vec<(String, String, Option<String>)> {
    document["obligations"]
        .as_array()
        .unwrap()
        .iter()
        .map(|o| {
            (
                o["id"].as_str().unwrap().to_owned(),
                o["status"].as_str().unwrap().to_owned(),
                o["witness"].as_str().map(str::to_owned),
            )
        })
        .collect()
}

/// `(id, status, witness)` as [`obligations`] gives it.
fn owed(rows: &[(&str, &str, Option<&str>)]) -> Vec<(String, String, Option<String>)> {
    rows.iter()
        .map(|(id, status, witness)| {
            (
                (*id).to_owned(),
                (*status).to_owned(),
                witness.map(str::to_owned),
            )
        })
        .collect()
}

/// A query of the witness fixture at `dir` with its lock `kink.lock`, under `--locked` when
/// `locked`, under `--full` when `full`.
fn locked_query(dir: &Path, locked: bool, full: bool) -> (Value, u8) {
    query(
        &dir.join("FLOW.toml"),
        &dir.join("PATTERNS.toml"),
        QueryOptions {
            lock: Some(dir.join("kink.lock")),
            locked,
            full,
            ..QueryOptions::default()
        },
    )
}

/// The `[query]` rows of the record at `dir/kink.lock`: `(id, status, witness)`.
fn locked_rows(dir: &Path) -> Vec<(String, String, Option<String>)> {
    let lock =
        kink_flow::lock::Lock::read_kind(&dir.join("kink.lock"), kink_flow::lock::LockKind::Query)
            .unwrap();
    lock.rows
        .iter()
        .map(|row| {
            assert_eq!(row.killer, None, "a query row records no killer");
            (
                row.id.clone(),
                row.status.clone().unwrap(),
                row.witness.clone(),
            )
        })
        .collect()
}

/// The witness fixture's FLOW.toml with `programs` (`(id, text)`) as its corpus, in order.
fn witness_corpus(dir: &Path, programs: &[(&str, &str)]) {
    let mut text = "[spec]\nentry = \"calc.k\"\nmain_module = \"CALC\"\nsyntax_module = \
                    \"CALC-SYNTAX\"\n"
        .to_owned();
    for (id, program) in programs {
        text.push_str(&format!(
            "\n[[program]]\nid = \"{id}\"\ntext = \"{program}\"\n"
        ));
    }
    write(&dir.join("FLOW.toml"), &text);
}

/// FB54-WITNESS acceptance 1 and 4: every pattern is an obligation, discharged by one witness.
/// The first query records the first hitter in corpus order (above-five: B of B and C), states an
/// obligation no program hits `open` (result-hundred), meets result-ninety-nine's `expect = "no"`,
/// and a claimed pattern's obligation reuses the claim's answer (result-three: A). Without
/// `--full` a pattern is asked until its first hit, so C is never asked of above-five; `--full`
/// asks every pair and lists both hitters, with the same witness and the same lock.
#[test]
fn the_first_query_records_one_witness_per_pattern() {
    let dir = fixture("witness", "witness-first");
    let (document, status) = locked_query(&dir, false, false);
    assert_eq!(status, EXIT_YES, "{document:#}");
    assert_eq!(document["version"], 8);
    let first = owed(&[
        ("above-five", "hit", Some("B")),
        ("result-hundred", "open", None),
        ("result-ninety-nine", "open", None),
        ("result-three", "hit", Some("A")),
    ]);
    assert_eq!(obligations(&document), first, "{document:#}");
    assert_eq!(
        obligation(&document, "result-ninety-nine")["expectation"]["verdict"],
        "met"
    );
    assert_eq!(
        obligation(&document, "above-five")["witness_change"],
        "no-record"
    );
    assert!(obligation(&document, "above-five")["hitters"].is_null());
    // The walk stops at its first hit: above-five asks A and B, result-three only its claim.
    assert_eq!(
        answers(&document),
        expect(&[
            ("above-five", "A", NO),
            ("above-five", "B", "hit"),
            ("result-hundred", "A", NO),
            ("result-hundred", "B", NO),
            ("result-hundred", "C", NO),
            ("result-ninety-nine", "A", NO),
            ("result-ninety-nine", "B", NO),
            ("result-ninety-nine", "C", NO),
            ("result-three", "A", "hit"),
        ])
    );
    assert_eq!(row(&document, "result-three", "A")["claim"], "confirmed");
    assert_eq!(document["lock"]["status"], "created", "{document:#}");
    assert_eq!(locked_rows(&dir), first);
    let text = fs::read_to_string(dir.join("kink.lock")).unwrap();
    assert!(
        text.contains(
            "[[query.pattern]]\nid = \"above-five\"\nstatus = \"hit\"\nwitness = \"B\"\n\n\
             [[query.pattern]]\nid = \"result-hundred\"\nstatus = \"open\"\n"
        ),
        "{text}"
    );
    // The expectation enters no lock.
    assert!(!text.contains("expect"), "{text}");

    // --full asks every pair and lists every hitter; the witness, and so the lock, are the same.
    let (full, status) = locked_query(&dir, true, true);
    assert_eq!(status, EXIT_YES, "{full:#}");
    assert_eq!(obligations(&full), first);
    assert_eq!(
        obligation(&full, "above-five")["hitters"],
        json!(["B", "C"])
    );
    assert_eq!(obligation(&full, "result-hundred")["hitters"], json!([]));
    assert_eq!(obligation(&full, "result-three")["hitters"], json!(["A"]));
    assert_eq!(full["lock"]["status"], "unchanged", "{full:#}");
    assert_eq!(full["rows"].as_array().unwrap().len(), 12, "{full:#}");
}

/// FB54-WITNESS acceptance 2 and 3: the record is a function of the corpus. A program added
/// before the witness in corpus order that also hits moves no witness, since the recorded witness
/// is asked first and still hits, so `--locked` passes. Deleting the witness re-opens the
/// obligation: the next hitter in corpus order (C) is the witness, `witness_change` says why,
/// `--locked` finds the lock stale (exit 1) and names the move, and a query without `--locked`
/// rewrites it.
#[test]
fn a_witness_is_kept_while_it_hits_and_moves_when_it_is_gone() {
    let dir = fixture("witness", "witness-moves");
    let (document, status) = locked_query(&dir, false, false);
    assert_eq!(status, EXIT_YES, "{document:#}");
    let recorded = fs::read_to_string(dir.join("kink.lock")).unwrap();

    // Z (10) comes first in corpus order and hits above-five; B is asked first and still hits.
    witness_corpus(
        &dir,
        &[
            ("Z", "5 + 5"),
            ("A", "1 + 2"),
            ("B", "2 * 3 + 1"),
            ("C", "4 * 2"),
        ],
    );
    let (added, status) = locked_query(&dir, true, false);
    assert_eq!(status, EXIT_YES, "{added:#}");
    assert_eq!(added["lock"]["status"], "unchanged", "{added:#}");
    assert_eq!(obligation(&added, "above-five")["witness"], "B");
    assert!(obligation(&added, "above-five")["witness_change"].is_null());
    // Only the recorded witness is asked of above-five.
    assert_eq!(
        answers(&added)
            .into_iter()
            .filter(|(pattern, _, _)| pattern == "above-five")
            .collect::<Vec<_>>(),
        expect(&[("above-five", "B", "hit")])
    );
    // The open obligations ask the new program too, and stay open.
    assert_eq!(obligation(&added, "result-hundred")["status"], "open");
    assert_eq!(fs::read_to_string(dir.join("kink.lock")).unwrap(), recorded);

    // B is deleted: above-five's witness moves to C, the first hitter in corpus order.
    witness_corpus(&dir, &[("A", "1 + 2"), ("C", "4 * 2")]);
    let (stale, status) = locked_query(&dir, true, false);
    assert_eq!(status, EXIT_NO, "{stale:#}");
    assert_eq!(stale["lock"]["status"], "stale", "{stale:#}");
    let moved = obligation(&stale, "above-five");
    assert_eq!(
        (
            &moved["witness"],
            &moved["recorded_witness"],
            &moved["witness_change"]
        ),
        (&json!("C"), &json!("B"), &json!("not-in-corpus")),
        "{moved:#}"
    );
    assert_eq!(
        kink_flow::lock::stale_lines(&stale),
        vec![format!(
            "{}: above-five: witness B -> C (B: not-in-corpus)",
            dir.join("kink.lock").display()
        )]
    );
    assert_eq!(fs::read_to_string(dir.join("kink.lock")).unwrap(), recorded);

    let (rewritten, status) = locked_query(&dir, false, false);
    assert_eq!(status, EXIT_YES, "{rewritten:#}");
    assert_eq!(rewritten["lock"]["status"], "written", "{rewritten:#}");
    assert_eq!(
        locked_rows(&dir),
        owed(&[
            ("above-five", "hit", Some("C")),
            ("result-hundred", "open", None),
            ("result-ninety-nine", "open", None),
            ("result-three", "hit", Some("A")),
        ])
    );
    let (again, status) = locked_query(&dir, true, false);
    assert_eq!(status, EXIT_YES, "{again:#}");
    assert_eq!(again["lock"]["status"], "unchanged");
}

/// FB54-WITNESS: `expect = "no"` is a claim about the corpus, checked as a mutation's `expect`
/// is: unmet on a hit (exit 1), whatever the lock says; and it may not stand beside `programs`.
/// `--only` and `--verify` leave the lock unwritten.
#[test]
fn an_expected_no_is_unmet_on_a_hit_and_only_leaves_the_lock_unwritten() {
    let dir = fixture("witness", "witness-expect");
    write(
        &dir.join("PATTERNS.toml"),
        "[[pattern]]\nid = \"seven\"\npattern = \"<k> 7 </k>\"\nexpect = \"no\"\n",
    );
    let (document, status) = locked_query(&dir, false, false);
    assert_eq!(status, EXIT_NO, "{document:#}");
    let seven = obligation(&document, "seven");
    assert_eq!(seven["status"], "hit");
    assert_eq!(seven["witness"], "B");
    assert_eq!(seven["expectation"]["verdict"], "unmet", "{seven:#}");
    assert_eq!(
        kink_flow::report::expectation_lines(&document),
        vec!["pattern seven: expected no, but B's run reaches a state that matches the pattern"]
    );
    // The fact is recorded; the claim is not.
    assert_eq!(locked_rows(&dir), owed(&[("seven", "hit", Some("B"))]));

    let error = PatternList::decode(
        "[[pattern]]\nid = \"a\"\npattern = \"<k> 7 </k>\"\nexpect = \"no\"\nprograms = [\"B\"]\n",
    )
    .unwrap_err();
    assert!(
        error.to_string().starts_with("pattern \"a\".expect: "),
        "{error}"
    );
    let error = PatternList::decode(
        "[[pattern]]\nid = \"a\"\npattern = \"<k> 7 </k>\"\nexpect = \"yes\"\n",
    )
    .unwrap_err();
    assert!(error.to_string().contains("expected \"no\""), "{error}");

    fs::remove_file(dir.join("kink.lock")).unwrap();
    for options in [
        QueryOptions {
            only: vec!["seven".into()],
            ..QueryOptions::default()
        },
        QueryOptions {
            verify: true,
            ..QueryOptions::default()
        },
    ] {
        let reason = if options.verify { "verify" } else { "only" };
        let (document, _) = query(
            &dir.join("FLOW.toml"),
            &dir.join("PATTERNS.toml"),
            QueryOptions {
                lock: Some(dir.join("kink.lock")),
                ..options
            },
        );
        assert_eq!(
            (&document["lock"]["status"], &document["lock"]["reason"]),
            (&json!("not-written"), &json!(reason)),
            "{document:#}"
        );
        assert!(!dir.join("kink.lock").exists());
    }
}

mod kink_tier {
    use super::*;

    /// fz26 KRUST-ANYWHERE-HEAD, review N5: SIMPLE's `array` is comparable now, so a `no` is
    /// reachable on it. A pattern holding a reducible application of the data head `_[_]`
    /// (`array(_, _)[2]`, which SIMPLE's `anywhere` rule rewrites to `lookup(..)`) is not
    /// normalized, but the search reads it up to equations (k-rust's `Implies` matching never
    /// compares an equation-head root as written), so a state compared there leaves the match
    /// undecided: `unknown`, never `no`. Its reduct's shape, `lookup(_)`, is a hit.
    #[test]
    #[ignore = "kink"]
    fn a_pattern_holding_a_reducible_array_access_is_never_no() {
        let dir = scratch("n5-array");
        let overload = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/k/overload");
        fs::copy(overload.join("simple.md"), dir.join("simple.md")).unwrap();
        fs::copy(
            overload.join("programs/array.simple"),
            dir.join("array.simple"),
        )
        .unwrap();
        write(
            &dir.join("FLOW.toml"),
            r#"[spec]
entry = "simple.md"
main_module = "SIMPLE-UNTYPED"
syntax_module = "SIMPLE-UNTYPED-SYNTAX"
[[program]]
id = "array"
file = "array.simple"
"#,
        );
        write(
            &dir.join("PATTERNS.toml"),
            r#"[[pattern]]
id = "reducible-read"
pattern = "<k> array(_, _) [ 2 ] ~> _ </k>"

[[pattern]]
id = "lookup-read"
pattern = "<k> lookup(_) ~> _ </k>"
"#,
        );
        let (document, status) = plain(&dir.join("FLOW.toml"), &dir.join("PATTERNS.toml"));
        assert_eq!(status, EXIT_UNANSWERED, "{document:#}");
        let reducible = row(&document, "reducible-read", "array");
        assert_eq!(reducible["answer"], "unknown", "{document:#}");
        assert!(
            reducible["cause"]
                .as_str()
                .unwrap()
                .contains("match against the pattern was left undecided"),
            "{document:#}"
        );
        assert_eq!(row(&document, "lookup-read", "array")["answer"], "hit");
    }

    /// Flow F-18: answers feed no verdict store. A query writes result records and pattern records
    /// only: no outcome, hint, memo or run document.
    #[test]
    #[ignore = "kink"]
    fn a_query_writes_no_verdict_store() {
        let dir = fixture("calc", "no-verdict");
        let (_, status) = plain(&dir.join("FLOW.toml"), &dir.join("PATTERNS.toml"));
        assert_eq!(status, REFUTED_STATUS);
        let names = fs::read_dir(dir.join(CACHE_DIRECTORY))
            .into_iter()
            .flatten()
            .map(|entry| entry.unwrap().file_name().into_string().unwrap())
            .collect::<BTreeSet<_>>();
        assert_eq!(
            names,
            BTreeSet::from(["patterns".to_owned(), "results".to_owned()])
        );
    }

    /// Under the Z3 profile the query document names the Z3 build its answers were decided on
    /// (`z3`), and so does the document of a pattern list that does not decode; under the
    /// portable profile neither names a Z3 build.
    #[test]
    #[ignore = "kink"]
    fn the_query_document_names_the_z3_build_under_the_z3_profile() {
        let z3 = flow_support::z3_member();
        let dir = fixture("calc", "z3-build");
        let (document, status) = plain(&dir.join("FLOW.toml"), &dir.join("PATTERNS.toml"));
        assert_eq!(status, REFUTED_STATUS, "{document:#}");
        assert_eq!(document.get("z3"), z3.as_ref(), "{document:#}");
        let error = PatternList::decode("[[patterns]]\nid = \"a\"\n").unwrap_err();
        let refused = kink_flow::query::pattern_list_refused(&error);
        assert_eq!(refused.get("z3"), z3.as_ref(), "{refused:#}");
    }

    /// Flow F-18 deliverable 4, CF-33: the pattern cache is on in both profiles (as tier 1 is):
    /// under Z3 the search's solver queries are bounded by Z3 resource units, which the key's
    /// budget names with the Z3 build. A hit and a `no` are cached in both.
    #[test]
    #[ignore = "kink"]
    fn the_pattern_cache_is_on_in_both_profiles() {
        let dir = fixture("calc", "profile");
        let (document, status) = plain(&dir.join("FLOW.toml"), &dir.join("PATTERNS.toml"));
        assert_eq!(status, REFUTED_STATUS, "{document:#}");
        assert_eq!(document["profile"], SolverProfile::BUILD.name());
        assert_eq!(document["pattern_cache"]["enabled"], true);
        assert_eq!(document["pattern_cache"]["reason"], Value::Null);
        assert!(!records(&dir).is_empty());
        assert_eq!(row(&document, "result-three", "add")["answer"], "hit");
        let refuted = row(&document, "result-four", "add");
        assert_eq!(refuted["answer"], NO);
        assert_eq!(refuted["cause"], no_cause());
        let (again, _) = plain(&dir.join("FLOW.toml"), &dir.join("PATTERNS.toml"));
        assert_eq!(row(&again, "result-three", "add")["cached"], true);
        assert_eq!(row(&again, "result-four", "add")["cached"], true);
    }

    /// Flow F-18 deliverable 2: a pattern that does not parse, that k-rust's pattern compiler
    /// refuses, or that names no cell of the configuration is `invalid-pattern` with k-rust's
    /// message, and never runs; the command exits 2, since its author must fix the pattern.
    #[test]
    #[ignore = "kink"]
    fn an_invalid_pattern_never_runs() {
        let dir = fixture("calc", "invalid");
        let patterns = dir.join("PATTERNS-invalid.toml");
        write(
            &patterns,
            r#"
[[pattern]]
id = "syntax"
pattern = "<k> 1 +* </k>"
programs = ["add"]

[[pattern]]
id = "ensures"
pattern = "<k> I:Int </k> ensures I >Int 0"
programs = ["add"]

[[pattern]]
id = "right-only"
pattern = "<k> X => Y:Int </k>"
programs = ["add"]

[[pattern]]
id = "cell"
pattern = "<state> 1 </state>"
programs = ["add"]
"#,
        );
        let (document, status) = plain(&dir.join("FLOW.toml"), &patterns);
        assert_eq!(status, EXIT_UNASKED, "{document:#}");
        for (id, detail) in [
            ("syntax", "could not parse rule in module \"CALC\""),
            (
                "ensures",
                "a search pattern cannot have an `ensures` clause",
            ),
            ("right-only", "occurs only on the right side of a rewrite"),
            (
                "cell",
                "the pattern names <state>, which is no cell of the configuration; the \
                 configuration declares: <k>",
            ),
        ] {
            let invalid = row(&document, id, "add");
            assert_eq!(invalid["answer"], "invalid-pattern", "{id}");
            assert_eq!(invalid["wall_ms"], Value::Null, "{id}: never run");
            assert!(
                invalid["cause"].as_str().unwrap().contains(detail),
                "{id}: {invalid:#}"
            );
            let pattern = document["patterns"]
                .as_array()
                .unwrap()
                .iter()
                .find(|p| p["id"] == id)
                .unwrap();
            assert_eq!(pattern["outcome"], "invalid-pattern");
            assert_eq!(pattern["digest"], Value::Null);
        }
        assert_eq!(document["counts"]["invalid-pattern"], 4);
        assert!(records(&dir).is_empty());
        // GUIDE-USABILITY 4: the position names the pattern's own text, not `PATTERNS.toml`
        // (which this list is not), and says so.
        let syntax = row(&document, "syntax", "add")["cause"]
            .as_str()
            .unwrap()
            .to_owned();
        assert!(
            syntax.contains("pattern:1:") && !syntax.contains("PATTERNS.toml"),
            "{syntax}"
        );
        assert!(
            syntax.contains("a line and column of the pattern's text"),
            "{syntax}"
        );
    }

    /// FB-53: a pattern whose tag is no cell of the configuration does not parse (k-rust scans a
    /// cell's tags as one terminal), and its cause names the tag and lists the configuration's
    /// cells, the top cell and `generatedCounter` left out. It stays `invalid-pattern`.
    #[test]
    #[ignore = "kink"]
    fn an_unknown_cell_is_named_with_the_configurations_cells() {
        let dir = scratch("unknown-cell");
        write(&dir.join("cells.k"), CELLS_SPEC);
        write(
            &dir.join("FLOW.toml"),
            "[spec]\nentry = \"cells.k\"\nmain_module = \"CELLS\"\nsyntax_module = \
             \"CELLS-SYNTAX\"\n\n[[program]]\nid = \"three\"\ntext = \"tick(3)\"\n",
        );
        write(
            &dir.join("PATTERNS.toml"),
            "[[pattern]]\nid = \"if\"\npattern = \"<IF> 5 </IF>\"\nprograms = [\"three\"]\n",
        );
        let (document, status) = plain(&dir.join("FLOW.toml"), &dir.join("PATTERNS.toml"));
        assert_eq!(status, EXIT_UNASKED, "{document:#}");
        let invalid = row(&document, "if", "three");
        assert_eq!(invalid["answer"], "invalid-pattern", "{invalid:#}");
        let cause = invalid["cause"].as_str().unwrap();
        assert!(
            cause.contains("could not parse rule in module \"CELLS\""),
            "{cause}"
        );
        assert!(
            cause.ends_with(
                "the pattern names <IF>, which is no cell of the configuration; the configuration \
                 declares: <T>, <k>, <out>, <count>"
            ),
            "{cause}"
        );
    }

    /// FB-51: a witness a reader can check. The pattern names `<k>`, `<mem>` (by a map entry) and
    /// `<out>` (by a list variable), and leaves out `<rom>`, a list of twelve elements: the
    /// witness lists the state by its cells, prints the named ones in full as K text, shortens
    /// `<rom>` to its length and its last elements, and shows the list binding the same way. The
    /// cache record keeps the facts, the state as whole KORE text, and a cached hit is printed as
    /// the live one was.
    #[test]
    #[ignore = "kink"]
    fn a_witness_prints_the_named_cells_in_full_and_shortens_the_rest() {
        let dir = spec_dir(
            "readable",
            "rom.k",
            "ROM",
            ROM_SPEC,
            "[[program]]\nid = \"twelve\"\ntext = \"fill(12)\"\n",
            "[[pattern]]\nid = \"filled\"\npattern = \"<k> done </k> <mem> 7 |-> V:Int </mem> \
             <out> L:List </out>\"\nprograms = [\"twelve\"]\n",
        );
        let (document, status) = plain(&dir.join("FLOW.toml"), &dir.join("PATTERNS.toml"));
        assert_eq!(status, EXIT_YES, "{document:#}");
        assert_eq!(document["version"], 8);
        let hit = row(&document, "filled", "twelve");
        assert_eq!(hit["answer"], "hit", "{hit:#}");
        let witness = &hit["witness"];
        assert_eq!(witness["depth"], 13, "{witness:#}");
        assert_eq!(witness["rendering"], "k");
        let full = |label: &str| {
            let cell = witness_cell(witness, label);
            assert_eq!(cell["named"], true, "{label}: {witness:#}");
            assert_eq!(cell["value"]["rendering"], "k", "{label}: {witness:#}");
            assert_eq!(cell["value"]["truncated"], false, "{label}: {witness:#}");
            cell["value"]["text"].as_str().unwrap().to_owned()
        };
        assert_eq!(full("<k>"), "done ~> .K");
        let mem = full("<mem>");
        assert!(mem.contains("7 |-> 42"), "{mem}");
        let out = full("<out>");
        assert_eq!(out.matches("ListItem").count(), 12, "{out}");
        let rom = witness_cell(witness, "<rom>");
        assert_eq!(rom["named"], false, "{witness:#}");
        assert_eq!(rom["path"], json!(["<generatedTop>", "<T>", "<rom>"]));
        let last = |value: &Value| {
            assert_eq!(
                (&value["collection"], &value["length"]),
                (&json!("list"), &json!(12)),
                "{value:#}"
            );
            value["last"]
                .as_array()
                .unwrap()
                .iter()
                .map(|item| item["text"].as_str().unwrap().to_owned())
                .collect::<Vec<_>>()
        };
        assert_eq!(
            last(&rom["value"]),
            ["8", "7", "6", "5", "4", "3", "2", "1"]
        );
        let bindings = witness["bindings"].as_array().unwrap();
        let binding = |name: &str| {
            &bindings
                .iter()
                .find(|binding| binding["variable"] == name)
                .unwrap_or_else(|| panic!("{name}: {witness:#}"))["value"]
        };
        assert_eq!(binding("V")["text"], "42", "{witness:#}");
        assert_eq!(
            last(binding("L")),
            ["16", "14", "12", "10", "8", "6", "4", "2"]
        );

        // The record keeps the facts; a second query reads it and prints the same witness.
        let record = records(&dir)
            .into_iter()
            .map(|path| serde_json::from_str::<Value>(&fs::read_to_string(path).unwrap()).unwrap())
            .find(|record| record["pattern_id"] == "filled")
            .unwrap();
        let state = record["witness"]["state"].as_str().unwrap();
        assert!(state.starts_with("Lbl'-LT-'generatedTop'-GT-'"), "{state}");
        assert_eq!(state.matches("LblListItem").count(), 24, "{state}");
        let (again, status) = plain(&dir.join("FLOW.toml"), &dir.join("PATTERNS.toml"));
        assert_eq!(status, EXIT_YES, "{again:#}");
        let cached = row(&again, "filled", "twelve");
        assert_eq!(cached["cached"], true, "{cached:#}");
        assert_eq!(cached["witness"], *witness);
    }

    /// Flow F-18 deliverable 3: a witness reports the bindings of the variables the author wrote
    /// only. k-rust's compiler completes the omitted sibling cells of `<count>` with variables
    /// (`_Gen<n>`) its list of generated variables does not name at 501f18b9, so kink also leaves
    /// out every variable spelled as k-rust's fresh-name passes spell one.
    #[test]
    #[ignore = "kink"]
    fn a_witness_binds_only_the_authors_variables() {
        let dir = scratch("cells");
        write(&dir.join("cells.k"), CELLS_SPEC);
        write(
            &dir.join("FLOW.toml"),
            "[spec]\nentry = \"cells.k\"\nmain_module = \"CELLS\"\nsyntax_module = \
             \"CELLS-SYNTAX\"\n\n[[program]]\nid = \"three\"\ntext = \"tick(3)\"\n",
        );
        write(
            &dir.join("PATTERNS.toml"),
            "[[pattern]]\nid = \"counted-two\"\npattern = \"<count> N:Int </count> requires N >Int \
             1\"\nprograms = [\"three\"]\n",
        );
        let (document, status) = plain(&dir.join("FLOW.toml"), &dir.join("PATTERNS.toml"));
        assert_eq!(status, EXIT_YES, "{document:#}");
        let kore = document["patterns"][0]["kore"].as_str().unwrap();
        assert!(
            kore.contains("Var'Unds'Gen"),
            "the completion's variables: {kore}"
        );
        let hit = row(&document, "counted-two", "three");
        assert_eq!(hit["answer"], "hit");
        assert_eq!(hit["witness"]["depth"], 2);
        assert_eq!(
            hit["witness"]["bindings"],
            json!([{"variable": "N", "value": {"text": "2", "rendering": "k", "truncated": false}}])
        );
    }

    /// Flow F-18 deliverable 5: a claim the run refutes is a `no` after a complete exploration of a
    /// comparable program, flagged `refuted` and listed in `refuted_claims`.
    #[test]
    #[ignore = "kink"]
    fn a_refuted_claim_follows_a_complete_exploration() {
        let dir = fixture("calc", "refuted");
        let patterns = dir.join("PATTERNS-claims.toml");
        write(&patterns, CALC_PATTERNS);
        let (document, status) = plain(&dir.join("FLOW.toml"), &patterns);
        assert_eq!(status, REFUTED_STATUS);
        let refuted = row(&document, "four", "add");
        assert_eq!(refuted["witness"], Value::Null);
        assert_eq!(refuted["answer"], "no");
        assert_eq!(refuted["claim"], "refuted");
        assert_eq!(refuted["cause"], no_cause());
        assert_eq!(
            document["refuted_claims"],
            json!([{"pattern": "four", "program": "add"}])
        );
        assert_eq!(
            document["programs"]
                .as_array()
                .unwrap()
                .iter()
                .find(|p| p["id"] == "add")
                .unwrap()["class"],
            "comparable"
        );
        // above-two: its claim, a hit by add, the first program, which is also its witness; four:
        // its claim and the walk of every other program, each a no; three: add, its witness.
        assert_eq!(
            document["counts"],
            json!({"hit": 2, "no": 4, "unknown": 0, "invalid-pattern": 0, "error": 0})
        );
    }

    /// Flow F-18 deliverables 2, 3 and 5: a claimed hit is confirmed, with the matching state, its
    /// depth, the bindings of the variables the author wrote (and of no generated one) and the rules
    /// of a path to it; a `requires` is a condition on those bindings.
    #[test]
    #[ignore = "kink"]
    fn a_claimed_hit_has_its_witness() {
        let dir = fixture("calc", "claimed-hit");
        let patterns = dir.join("PATTERNS-claims.toml");
        write(&patterns, CALC_PATTERNS);
        let (document, status) = plain(&dir.join("FLOW.toml"), &patterns);
        assert_eq!(status, REFUTED_STATUS, "{document:#}");
        assert_eq!(document["schema"], "kink-flow-query");
        assert_eq!(document["version"], 8);
        // GUIDE-USABILITY 5 (KINK-R4 fix round): every kink-flow document names k-rust's build
        // identity, not the version alone.
        assert_eq!(document["k_rust_revision"], k_rust::build_identity());
        assert_eq!(document["profile"], SolverProfile::BUILD.name());
        let hit = row(&document, "above-two", "add");
        assert_eq!(hit["answer"], "hit");
        assert_eq!(hit["claimed"], true);
        assert_eq!(hit["claim"], "confirmed");
        assert_eq!(hit["cause"], Value::Null);
        assert_eq!(hit["cached"], false);
        let witness = &hit["witness"];
        assert_eq!(witness["depth"], 1);
        assert_eq!(witness["rendering"], "k");
        assert_eq!(witness["rules"], json!(["CALC.add"]));
        // FB-51: the state by its cells, the `<k>` the pattern names printed in full as K text.
        let k = witness_cell(witness, "<k>");
        assert_eq!(k["named"], true, "{witness:#}");
        assert_eq!(
            k["value"],
            json!({"text": "3 ~> .K", "rendering": "k", "truncated": false}),
            "{witness:#}"
        );
        // The only binding is the author's I; the cell completion's generated variables are not
        // reported.
        assert_eq!(
            witness["bindings"],
            json!([{"variable": "I", "value": {"text": "3", "rendering": "k", "truncated": false}}])
        );
        // The pattern's own row: its KORE target, with the condition as an equation.
        let pattern = &document["patterns"][0];
        assert_eq!(pattern["outcome"], "valid");
        assert_eq!(pattern["asked"], "claimed");
        assert!(
            pattern["kore"]
                .as_str()
                .unwrap()
                .contains("\\equals{SortBool{}")
        );
        // A pattern without claims is asked until its first hit in corpus order, its witness.
        assert_eq!(
            answers(&document)
                .into_iter()
                .filter(|(p, _, _)| p == "three")
                .collect::<Vec<_>>(),
            expect(&[("three", "add", "hit")])
        );
        assert_eq!(document["obligations"][2]["witness"], "add", "{document:#}");
        assert_eq!(row(&document, "three", "add")["claim"], Value::Null);
        assert_eq!(
            row(&document, "three", "add")["witness"]["bindings"],
            json!([])
        );
    }

    /// Flow F-18 deliverable 6: on a definition decision 1's census flags, a would-be `no` is
    /// `unknown` (another model of the open value could reach the pattern). At 501f18b9 a hit stayed
    /// a hit; since k-rust 58720d2e5 (KINK-17/1) the only match here carries an open-value mark, so
    /// it is `unknown` too (below).
    ///
    /// Re-pin P-2 (P-1-review-1 cosmetic finding): renamed from
    /// `a_census_flagged_definition_gives_hits_and_no_no`, which no longer says what it asserts.
    ///
    /// Re-pin kink27 R3-CENSUS-RUNLEVEL: `MAP.keys_list` is a k-rust class, judged per run, so the
    /// census no longer flags the definition; the would-be `no` is `unknown` for the value the search
    /// read (`implementation-chosen-value`, on its `implementationChosenValues` list, and on the
    /// baseline run's) instead of `implementation-chosen-hook`. Renamed from
    /// `a_census_flagged_definition_gives_no_hit_on_a_marked_match_and_no_no`.
    #[test]
    #[ignore = "kink"]
    fn a_marked_search_gives_no_hit_and_no_no() {
        let dir = scratch("census");
        write(&dir.join("implchosen.k"), CENSUS_SPEC);
        write(
            &dir.join("FLOW.toml"),
            "[spec]\nentry = \"implchosen.k\"\nmain_module = \"IMPLCHOSEN\"\nsyntax_module = \
             \"IMPLCHOSEN-SYNTAX\"\n\n[[program]]\nid = \"start\"\ntext = \"start(1)\"\n",
        );
        write(
            &dir.join("PATTERNS.toml"),
            "[[pattern]]\nid = \"listed\"\npattern = \"<k> keys(_:List) </k>\"\n\n[[pattern]]\nid = \
             \"never\"\npattern = \"<k> count(_) </k>\"\nprograms = [\"start\"]\n",
        );
        let (document, status) = plain(&dir.join("FLOW.toml"), &dir.join("PATTERNS.toml"));
        assert_eq!(status, EXIT_UNANSWERED, "{document:#}");
        // Re-pin probe P-1 (k-rust 58720d2e5; KINK-17/1, head 728e7eb34, merge 3a196ed14, which
        // adds marks of open values, and they reach the four search responses too): the match's
        // path read `keys_list` of two keys, so it carries an
        // `implementation-chosen-value` mark (class `order`), and a hit needs a match without any
        // backend diagnostic, so the would-be hit is `unknown` and is not cached. Fail-closed (hit ->
        // unknown); adopting the marks (probe P-1 deliverable 5) decides whether a marked witness
        // may be a hit.
        let listed = row(&document, "listed", "start");
        assert_eq!(listed["answer"], "unknown", "{listed:#}");
        assert!(
            listed["cause"]
                .as_str()
                .unwrap()
                .contains("backend diagnostic"),
            "{listed:#}"
        );
        let never = row(&document, "never", "start");
        assert_eq!(never["answer"], "unknown");
        assert_eq!(never["claim"], "unconfirmed");
        assert!(
            never["cause"]
                .as_str()
                .unwrap()
                .contains("implementation-chosen-value"),
            "{never:#}"
        );
        // Neither unknown is cached (re-pin probe P-1: at 501f18b9 the hit was, one record).
        assert_eq!(records(&dir).len(), 0);
    }

    /// kink27 R3-CENSUS-RUNLEVEL: the undecided-match route of a pattern whose match would read a
    /// value the definition leaves open. This is not gap G1's regression test, which is kink-flow's
    /// unit test `pattern::tests::a_search_that_read_an_open_value_gives_no_no` on hand-built
    /// responses; this test passes at the base too. `pair(1)` reaches `keys(ListItem(2) ListItem(1))`,
    /// which reads no open value, so the program's baseline run is comparable and the census flags
    /// nothing; the pattern `keys(lst())` holds `lst()`, whose normal form lists 1 then 2 in k-rust
    /// and 2 then 1 in another model of the definition, which then matches the reached state. At
    /// this k-rust the search leaves that match undecided (an incomplete entry, read before the
    /// search's `implementationChosenValues` list): k-rust's matcher does not normalize the
    /// pattern's function application to a class value, so the answer is `unknown` for the
    /// undecided match and no mark is listed. No end-to-end route to G1 is known at this pin, so
    /// G1 is defensive here. Were the match decided at a later k-rust, the matching, part of the
    /// search, would list the mark and the answer must be `unknown` (`implementation-chosen-value`);
    /// this test then fails and is re-pinned as G1's end-to-end test.
    #[test]
    #[ignore = "kink"]
    fn a_pattern_whose_match_would_read_an_open_value_is_left_undecided() {
        let dir = scratch("pick");
        write(&dir.join("pick.k"), PICK_SPEC);
        write(
            &dir.join("FLOW.toml"),
            "[spec]\nentry = \"pick.k\"\nmain_module = \"PICK\"\nsyntax_module = \
             \"PICK-SYNTAX\"\n\n[[program]]\nid = \"pair\"\ntext = \"pair(1)\"\n",
        );
        write(
            &dir.join("PATTERNS.toml"),
            "[[pattern]]\nid = \"listed\"\npattern = \"<k> keys(lst()) </k>\"\n",
        );
        let (document, status) = plain(&dir.join("FLOW.toml"), &dir.join("PATTERNS.toml"));
        assert_eq!(status, EXIT_UNANSWERED, "{document:#}");
        let listed = row(&document, "listed", "pair");
        assert_eq!(listed["answer"], "unknown", "{listed:#}");
        let cause = listed["cause"].as_str().unwrap();
        assert!(
            cause.contains("match against the pattern was left undecided"),
            "{listed:#}"
        );
        assert_eq!(records(&dir).len(), 0);
    }

    /// Flow F-18 deliverable 5: the binary's `query` command, its document and its exit codes.
    #[test]
    #[ignore = "kink"]
    fn the_binarys_query_command() {
        let binary = env!("CARGO_BIN_EXE_kink-flow");
        let dir = fixture("calc", "binary");
        let manifest = dir.join("FLOW.toml");
        let patterns = dir.join("PATTERNS.toml");
        let cache = scratch("binary-cache");
        let output = Command::new(binary)
            .arg("query")
            .arg(&manifest)
            .arg(&patterns)
            .args(["--only", "result-four", "--cache"])
            .arg(&cache)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(i32::from(REFUTED_STATUS)));
        let document: Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(document["schema"], "kink-flow-query");
        // The claim, then the obligation's walk, which no program ends with a hit.
        assert_eq!(
            answers(&document),
            expect(&[
                ("result-four", "add", NO),
                ("result-four", "nested", NO),
                ("result-four", "sub", NO),
                ("result-four", "inline", NO),
            ])
        );
        assert_eq!(document["obligations"][0]["status"], "open", "{document:#}");
        assert_eq!(
            document["refuted_claims"],
            json!([{"pattern": "result-four", "program": "add"}])
        );
        assert!(cache.join("patterns").is_dir());
        assert!(!dir.join(CACHE_DIRECTORY).exists());
        for (args, code) in [
            (vec!["--only", "nope"], EXIT_UNASKED),
            (vec!["--verify", "--verify"], EXIT_UNASKED),
            (vec!["--bogus"], EXIT_UNASKED),
        ] {
            let output = Command::new(binary)
                .arg("query")
                .arg(&manifest)
                .arg(&patterns)
                .args(&args)
                .output()
                .unwrap();
            assert_eq!(output.status.code(), Some(i32::from(code)), "{args:?}");
        }
        let output = Command::new(binary)
            .arg("query")
            .arg(&manifest)
            .arg(dir.join("MISSING.toml"))
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(i32::from(EXIT_UNASKED)));
        let bad = dir.join("BAD.toml");
        fs::write(
            &bad,
            "[[pattern]]\nid = \"a\"\npattern = \"x\"\nlabel = 1\n",
        )
        .unwrap();
        let output = Command::new(binary)
            .arg("query")
            .arg(&manifest)
            .arg(&bad)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(i32::from(EXIT_UNASKED)));
        let document: Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(
            document["pattern_list"]["detail"],
            "pattern \"a\".label: unknown key"
        );
    }

    /// F-18 review 1, critical: a hit needs the matched state's term to be defined. A reached state
    /// holding `f(3)`, an application of a partial function no equation reduces, may denote no
    /// configuration, and k-rust's search match states that undecided fact as its condition
    /// (`\ceil(f(3))`): it is `unknown` (a condition k-rust did not decide), never a confirmed
    /// claim, and nothing is cached. The same state with a total function, and a state holding a
    /// map, stay hits.
    #[test]
    #[ignore = "kink"]
    fn a_hit_needs_a_defined_state() {
        let dir = spec_dir(
            "partial",
            "calcp.k",
            "CALCP",
            PARTIAL_SPEC,
            "[[program]]\nid = \"partial\"\ntext = \"1 + 2\"\n",
            "[[pattern]]\nid = \"g-holds-an-int\"\npattern = \"<k> g(I:Int) </k>\"\nprograms = \
             [\"partial\"]\n\n[[pattern]]\nid = \"reaches-100\"\npattern = \"<k> 100 </k>\"\nprograms \
             = [\"partial\"]\n\n[[pattern]]\nid = \"never\"\npattern = \"<k> 5 </k>\"\nprograms = \
             [\"partial\"]\n",
        );
        let (document, status) = plain(&dir.join("FLOW.toml"), &dir.join("PATTERNS.toml"));
        assert_eq!(status, EXIT_UNANSWERED, "{document:#}");
        let partial = row(&document, "g-holds-an-int", "partial");
        assert_eq!(partial["answer"], "unknown", "{partial:#}");
        assert_eq!(partial["claim"], "unconfirmed");
        assert_eq!(partial["witness"], Value::Null);
        let cause = partial["cause"].as_str().unwrap();
        assert!(
            cause.contains("under a condition k-rust did not decide"),
            "{cause}"
        );
        assert!(cause.contains("(depth 2)"), "{cause}");
        for pattern in ["reaches-100", "never"] {
            assert_eq!(row(&document, pattern, "partial")["answer"], "unknown");
        }
        assert_eq!(document["counts"]["hit"], 0);
        assert_eq!(document["pattern_cache"]["records_written"], 0);
        assert!(records(&dir).is_empty());

        let dir = spec_dir(
            "total",
            "calcg.k",
            "CALCG",
            TOTAL_SPEC,
            "[[program]]\nid = \"partial\"\ntext = \"1 + 2\"\n\n[[program]]\nid = \"total\"\ntext = \
             \"1 + 3\"\n",
            "[[pattern]]\nid = \"g-any\"\npattern = \"<k> g(_) </k>\"\n",
        );
        let (document, status) = plain(&dir.join("FLOW.toml"), &dir.join("PATTERNS.toml"));
        assert_eq!(status, EXIT_UNANSWERED, "{document:#}");
        let total = row(&document, "g-any", "total");
        assert_eq!(total["answer"], "hit", "{total:#}");
        assert!(
            witness_cell(&total["witness"], "<k>")["value"]["text"]
                .as_str()
                .unwrap()
                .contains('h'),
            "{total:#}"
        );
        let partial = row(&document, "g-any", "partial");
        assert_eq!(partial["answer"], "unknown", "{partial:#}");
        assert!(
            partial["cause"]
                .as_str()
                .unwrap()
                .contains("under a condition k-rust did not decide")
        );

        let dir = spec_dir(
            "store",
            "store.k",
            "STORE",
            STORE_SPEC,
            "[[program]]\nid = \"start\"\ntext = \"start\"\n",
            "[[pattern]]\nid = \"two-holds\"\npattern = \"<store> ... 2 |-> V:Int ... </store>\"\nprograms \
             = [\"start\"]\n",
        );
        let (document, status) = plain(&dir.join("FLOW.toml"), &dir.join("PATTERNS.toml"));
        assert_eq!(status, EXIT_YES, "{document:#}");
        let store = row(&document, "two-holds", "start");
        assert_eq!(store["answer"], "hit", "{store:#}");
        assert_eq!(
            store["witness"]["bindings"],
            json!([{"variable": "V", "value": {"text": "20", "rendering": "k", "truncated": false}}])
        );
    }

    /// Flow F-18 tail: `--verify` compares a stored hit's witness too. A record that keeps the hit
    /// but carries another witness (its digest recomputed) is used as it is by a plain query, and
    /// `--verify` reports it as a mismatch although both answers are hits.
    #[test]
    #[ignore = "kink"]
    fn verify_reports_a_forged_witness() {
        let dir = fixture("calc", "forged-witness");
        let manifest = dir.join("FLOW.toml");
        let patterns = dir.join("PATTERNS.toml");
        let (first, _) = plain(&manifest, &patterns);
        let hit = row(&first, "result-three", "add");
        assert_eq!(hit["answer"], "hit");
        let live_witness = hit["witness"].clone();
        assert!(live_witness.is_object(), "{hit:#}");
        let path = records(&dir)
            .into_iter()
            .find(|path| {
                let record: Value =
                    serde_json::from_str(&fs::read_to_string(path).unwrap()).unwrap();
                record["pattern_id"] == "result-three" && record["program_id"] == "add"
            })
            .unwrap();
        let mut record: Value = serde_json::from_str(&fs::read_to_string(&path).unwrap()).unwrap();
        assert_eq!(record["answer"], "hit");
        // FB-51: the record keeps the witness's facts, the state as whole KORE text; the document
        // prints them.
        let live_facts = record["witness"].clone();
        assert_eq!(live_facts["depth"], live_witness["depth"]);
        assert!(live_facts["state"].is_string(), "{live_facts:#}");
        assert_eq!(live_facts.get("rendering"), None, "{live_facts:#}");
        let mut witness = live_facts.clone();
        witness["depth"] = json!(99);
        witness["rules"] = json!(["forged"]);
        record["witness"] = witness.clone();
        record["record_sha256"] = json!(
            record_sha256(
                &record["key"],
                "hit",
                &witness,
                &record["baseline_run_sha256"]
            )
            .to_string()
        );
        let forged = serde_json::to_string(&record).unwrap();
        fs::write(&path, &forged).unwrap();

        // The digest recomputes, so a plain query uses the record, forged witness and all.
        let (trusted, status) = plain(&manifest, &patterns);
        assert_eq!(status, REFUTED_STATUS, "{trusted:#}");
        let cached = row(&trusted, "result-three", "add");
        assert_eq!(cached["answer"], "hit");
        assert_eq!(cached["cached"], true);
        assert_eq!(
            (&cached["witness"]["depth"], &cached["witness"]["rules"]),
            (&json!(99), &json!(["forged"])),
            "{cached:#}"
        );
        let mut printed = live_witness.clone();
        printed["depth"] = json!(99);
        printed["rules"] = json!(["forged"]);
        assert_eq!(
            cached["witness"], printed,
            "a cached hit is printed as a live one"
        );

        let (verified, status) = verify(&manifest, &patterns);
        assert_eq!(status, EXIT_NO, "{verified:#}");
        let live = row(&verified, "result-three", "add");
        assert_eq!(live["answer"], "hit");
        assert_eq!(live["witness"], live_witness);
        assert_eq!(live["verify"], "mismatch");
        assert_eq!(row(&verified, "result-three", "sub")["verify"], "match");
        let mismatches = verified["mismatches"].as_array().unwrap();
        assert_eq!(mismatches.len(), 1, "{verified:#}");
        assert_eq!(mismatches[0]["pattern"], "result-three");
        assert_eq!(mismatches[0]["program"], "add");
        assert_eq!(mismatches[0]["cached"]["answer"], "hit");
        assert_eq!(mismatches[0]["cached"]["witness"], witness);
        assert_eq!(mismatches[0]["live"]["answer"], "hit");
        assert_eq!(mismatches[0]["live"]["witness"], live_facts);
        assert_eq!(
            fs::read_to_string(&path).unwrap(),
            forged,
            "--verify writes nothing"
        );
    }

    /// Flow F-18 deliverable 3: a depth bound or the clock turns a would-be `no` into `unknown`
    /// with its cause, and a hit is found in a run that never ends (the search stops at its first
    /// match); none of the unknowns is cached.
    #[test]
    #[ignore = "kink"]
    fn a_bound_turns_a_would_be_no_into_unknown() {
        let dir = fixture("loop", "bounds");
        let bounded = dir.join("FLOW-bounded.toml");
        write(&bounded, &loop_bounded());
        let patterns = dir.join("PATTERNS.toml");
        let (document, status) = full(&bounded, &patterns);
        assert_eq!(status, EXIT_UNANSWERED, "{document:#}");
        let cut = row(&document, "zero", "spin");
        assert_eq!(cut["answer"], "unknown");
        assert!(
            cut["cause"]
                .as_str()
                .unwrap()
                .contains("a path reached max_depth = 50"),
            "{cut:#}"
        );
        assert_eq!(row(&document, "spin-five", "spin")["answer"], "hit");
        assert_eq!(row(&document, "spin-five", "spin")["witness"]["depth"], 5);
        assert_eq!(row(&document, "spin-five", "countdown")["answer"], NO);

        // The clock: a depth the run cannot reach and a small time bound.
        let (document, status) = full(&dir.join("FLOW-timeout.toml"), &patterns);
        assert_eq!(status, EXIT_UNANSWERED, "{document:#}");
        let timed = row(&document, "zero", "spin");
        assert_eq!(timed["answer"], "unknown");
        // FB54-WITNESS: the clock stopped spin's search, which comes before zero's witness,
        // countdown, in corpus order: the obligation's witness rests on that run.
        assert_eq!(timed["clock_stopped"], "search", "{timed:#}");
        let zero = document["obligations"]
            .as_array()
            .unwrap()
            .iter()
            .find(|o| o["id"] == "zero")
            .unwrap();
        assert_eq!(zero["witness"], "countdown", "{zero:#}");
        assert_eq!(
            zero["clock_stopped"],
            json!([{"program": "spin", "run": "search"}]),
            "{zero:#}"
        );
        assert!(
            timed["cause"]
                .as_str()
                .unwrap()
                .starts_with("the search did not finish within time_ms = 500"),
            "{timed:#}"
        );
        // The baseline run of spin times out, yet the hit stands: it is an existential fact.
        assert_eq!(document["programs"][0]["class"], "timeout", "{document:#}");
        assert_eq!(row(&document, "spin-five", "spin")["answer"], "hit");
        // A complete exploration of a comparable program is a no.
        assert_eq!(row(&document, "spin-five", "countdown")["answer"], NO);

        let (again, _) = full(&dir.join("FLOW-timeout.toml"), &patterns);
        assert_eq!(row(&again, "zero", "spin")["cached"], false);
        assert_eq!(row(&again, "zero", "spin")["answer"], "unknown");
        // The hit is cached.
        assert_eq!(row(&again, "spin-five", "spin")["cached"], true);
    }

    /// Flow F-18 deliverable 4 (the CACHE-ID rule): a forged record under the current key is
    /// honoured (whoever can write the cache can forge an answer), and `--verify` re-derives every
    /// answer, reports the forged one and exits 1, writing nothing. A record whose digest does not
    /// recompute is not used.
    #[test]
    #[ignore = "kink"]
    fn verify_reports_a_forged_record() {
        let dir = fixture("calc", "forged");
        let manifest = dir.join("FLOW.toml");
        let patterns = dir.join("PATTERNS.toml");
        let (first, _) = plain(&manifest, &patterns);
        let hit = row(&first, "result-three", "add");
        assert_eq!(hit["answer"], "hit");
        let path = records(&dir)
            .into_iter()
            .find(|path| {
                let record: Value =
                    serde_json::from_str(&fs::read_to_string(path).unwrap()).unwrap();
                record["pattern_id"] == "result-three" && record["program_id"] == "add"
            })
            .unwrap();
        let mut record: Value = serde_json::from_str(&fs::read_to_string(&path).unwrap()).unwrap();
        // The program's current result record holds the baseline run digest the forged no names.
        let program = first["programs"]
            .as_array()
            .unwrap()
            .iter()
            .find(|p| p["id"] == "add")
            .unwrap()["digest"]
            .as_str()
            .unwrap()
            .to_owned();
        let result: Value = serde_json::from_str(
            &fs::read_to_string(
                dir.join(CACHE_DIRECTORY)
                    .join("results")
                    .join(
                        first["spec"]["execution_digest"]["digest"]
                            .as_str()
                            .unwrap(),
                    )
                    .join(format!("{program}.json")),
            )
            .unwrap(),
        )
        .unwrap();
        let run_sha256 = result["run_sha256"].clone();
        assert!(run_sha256.is_string());
        record["answer"] = json!("no");
        record["witness"] = Value::Null;
        record["baseline_run_sha256"] = run_sha256.clone();
        record["record_sha256"] =
            json!(record_sha256(&record["key"], "no", &Value::Null, &run_sha256).to_string());
        let forged = serde_json::to_string(&record).unwrap();
        fs::write(&path, &forged).unwrap();

        let (trusted, status) = plain(&manifest, &patterns);
        assert_eq!(status, EXIT_NO);
        assert_eq!(row(&trusted, "result-three", "add")["answer"], "no");
        assert_eq!(row(&trusted, "result-three", "add")["cached"], true);

        let (verified, status) = verify(&manifest, &patterns);
        assert_eq!(status, EXIT_NO, "{verified:#}");
        let live = row(&verified, "result-three", "add");
        assert_eq!(live["answer"], "hit");
        assert_eq!(live["verify"], "mismatch");
        assert_eq!(row(&verified, "result-three", "sub")["verify"], "match");
        let mismatches = verified["mismatches"].as_array().unwrap();
        assert_eq!(mismatches.len(), 1, "{verified:#}");
        assert_eq!(mismatches[0]["pattern"], "result-three");
        assert_eq!(mismatches[0]["program"], "add");
        assert_eq!(mismatches[0]["cached"]["answer"], "no");
        assert_eq!(mismatches[0]["live"]["answer"], "hit");
        assert_eq!(verified["pattern_cache"]["records_written"], 0);
        assert_eq!(
            fs::read_to_string(&path).unwrap(),
            forged,
            "--verify writes nothing"
        );

        // A record whose digest does not recompute is ignored and replaced.
        record["record_sha256"] = json!("00".repeat(32));
        fs::write(&path, serde_json::to_string(&record).unwrap()).unwrap();
        let (recomputed, _) = plain(&manifest, &patterns);
        assert_eq!(row(&recomputed, "result-three", "add")["answer"], "hit");
        assert_eq!(row(&recomputed, "result-three", "add")["cached"], false);
    }

    /// Flow F-18 deliverable 4: a second command answers from the cache with no search; editing a
    /// program recomputes its rows only, a comment or layout edit of the specification keeps every
    /// cached answer (the key names the execution digest, the loaded definition without
    /// positions), and editing a rule of the specification or the budget's bounds recomputes
    /// every row; the time bound is not one of them.
    #[test]
    #[ignore = "kink"]
    fn the_cache_is_reused_and_invalidated_by_key() {
        let dir = fixture("calc", "cache");
        // Every pair is asked (`--full`), so the same pairs are asked after each edit, whatever
        // the edit does to the obligations' walks.
        let manifest = dir.join("FLOW.toml");
        let patterns = dir.join("PATTERNS.toml");
        let (first, status) = full(&manifest, &patterns);
        assert_eq!(status, REFUTED_STATUS, "{first:#}");
        assert!(cached(&first).iter().all(|c| !c));
        let written = first["pattern_cache"]["records_written"].as_u64().unwrap();
        assert!(written > 0);
        assert_eq!(first["pattern_cache"]["enabled"], true);

        let (second, _) = full(&manifest, &patterns);
        assert!(cached(&second).iter().all(|c| *c), "{second:#}");
        assert_eq!(answers(&second), answers(&first));
        assert_eq!(second["pattern_cache"]["records_written"], 0);
        assert!(
            second["rows"]
                .as_array()
                .unwrap()
                .iter()
                .filter(|r| cacheable(r))
                .all(|r| r["wall_ms"].is_null())
        );
        for (a, b) in first["rows"]
            .as_array()
            .unwrap()
            .iter()
            .zip(second["rows"].as_array().unwrap())
        {
            assert_eq!(a["witness"], b["witness"]);
        }

        // A program edit: only add's rows are recomputed.
        fs::write(dir.join("programs/add.calc"), "1 + 3\n").unwrap();
        let (edited, _) = full(&manifest, &patterns);
        for row in edited["rows"].as_array().unwrap() {
            assert_eq!(
                row["cached"],
                row["program"] != "add" && cacheable(row),
                "{row:#}"
            );
        }
        assert_eq!(row(&edited, "result-three", "add")["answer"], NO);
        assert_eq!(row(&edited, "result-three", "add")["claim"], "refuted");

        // A comment and blank lines: every cached answer stands.
        let spec = fs::read_to_string(dir.join("calc.k")).unwrap();
        fs::write(
            dir.join("calc.k"),
            format!("// a comment at the top\n\n{spec}// and one at the end\n"),
        )
        .unwrap();
        let (commented, _) = full(&manifest, &patterns);
        assert_ne!(commented["spec"]["digest"], edited["spec"]["digest"]);
        assert_eq!(
            commented["spec"]["execution_digest"],
            edited["spec"]["execution_digest"]
        );
        assert!(cached(&commented).iter().all(|c| *c), "{commented:#}");
        assert_eq!(answers(&commented), answers(&edited));

        // A rule edit: every row is recomputed.
        let spec = fs::read_to_string(dir.join("calc.k")).unwrap();
        fs::write(dir.join("calc.k"), spec.replace("I1 -Int I2", "I2 -Int I1")).unwrap();
        let (respec, _) = full(&manifest, &patterns);
        assert!(cached(&respec).iter().all(|c| !c));

        // A time bound: every cached answer stands.
        let mut text = fs::read_to_string(&manifest).unwrap();
        text.push_str("\n[budget]\ntime_ms = 20000\n");
        fs::write(&manifest, &text).unwrap();
        let (retimed, _) = full(&manifest, &patterns);
        assert!(cached(&retimed).iter().all(|c| *c), "{retimed:#}");

        // A depth bound: every row is recomputed.
        text.push_str("max_depth = 1000\n");
        fs::write(&manifest, text).unwrap();
        let (rebudget, _) = full(&manifest, &patterns);
        assert!(cached(&rebudget).iter().all(|c| !c));
        assert_eq!(answers(&rebudget), answers(&respec));
    }

    /// F-18 review 1, minor: a cached `no` is used only while the program's current result record is
    /// comparable with the baseline run digest the `no` was given against. A result record with
    /// another run digest, or of class unknown, under the same key makes the command search again
    /// (an unknown then gives unknown), and a stored timeout is never read, so the program runs
    /// again; a cached hit does not depend on the baseline.
    #[test]
    #[ignore = "kink"]
    fn a_cached_no_needs_the_same_comparable_baseline() {
        let dir = fixture("calc", "stored-no");
        let manifest = dir.join("FLOW.toml");
        let patterns = dir.join("PATTERNS.toml");
        let (first, status) = plain(&manifest, &patterns);
        assert_eq!(status, EXIT_NO, "{first:#}");
        assert_eq!(row(&first, "result-four", "add")["answer"], "no");
        let path = result_record(&dir, &first, "add");
        let original: Value = serde_json::from_str(&fs::read_to_string(&path).unwrap()).unwrap();
        assert_eq!(original["class"], "comparable");

        // Another baseline run digest: the stored no is not used; the live search says no again.
        forge(&path, "run_sha256", json!("00".repeat(32)));
        let (digest, _) = plain(&manifest, &patterns);
        let no = row(&digest, "result-four", "add");
        assert_eq!(
            (no["cached"].clone(), no["answer"].clone()),
            (json!(false), json!("no")),
            "{no:#}"
        );
        assert_eq!(row(&digest, "result-three", "add")["cached"], true);

        // A stored timeout is never read (a timeout depends on the host's load): the program is
        // recomputed, comparable, and the no stands.
        fs::write(&path, serde_json::to_string(&original).unwrap()).unwrap();
        let (again, _) = plain(&manifest, &patterns);
        assert_eq!(row(&again, "result-four", "add")["answer"], "no");
        forge(&path, "class", json!("timeout"));
        let (timeout, _) = plain(&manifest, &patterns);
        let add = timeout["programs"]
            .as_array()
            .unwrap()
            .iter()
            .find(|p| p["id"] == "add")
            .unwrap();
        assert_eq!(
            (add["class"].clone(), add["cached"].clone()),
            (json!("comparable"), json!(false))
        );
        let no = row(&timeout, "result-four", "add");
        assert_eq!(
            (no["cached"].clone(), no["answer"].clone()),
            (json!(true), json!("no")),
            "{no:#}"
        );
        // An unknown under the same key: the no is not used, and the live answer is unknown.
        forge(&path, "class", json!("unknown"));
        let (timeout, _) = plain(&manifest, &patterns);
        let unknown = row(&timeout, "result-four", "add");
        assert_eq!(unknown["cached"], false, "{unknown:#}");
        assert_eq!(unknown["answer"], "unknown", "{unknown:#}");
        assert!(
            unknown["cause"]
                .as_str()
                .unwrap()
                .contains("and it is unknown")
        );
        let hit = row(&timeout, "result-three", "add");
        assert_eq!(
            (hit["cached"].clone(), hit["answer"].clone()),
            (json!(true), json!("hit"))
        );

        // Under --verify the answer is judged with the live baseline run, not the stale record: the
        // live no is printed, and the command exits 1 for the result record's difference.
        let (verified, status) = verify(&manifest, &patterns);
        assert_eq!(status, EXIT_NO, "{verified:#}");
        assert_eq!(row(&verified, "result-four", "add")["answer"], "no");
        assert!(
            verified["mismatches"]
                .as_array()
                .unwrap()
                .iter()
                .any(|m| m["program"] == "add"
                    && m["detail"].as_str().is_some_and(|d| d.contains("class"))),
            "{verified:#}"
        );
    }

    /// Flow F-18 stop rule 3: the search under the state set finds exactly the hits a walk of the
    /// state set one step at a time finds, on every program and pattern of these fixtures.
    #[test]
    #[ignore = "kink"]
    fn the_search_finds_the_hits_stepping_finds() {
        let calc = fixture("calc", "stepping-calc");
        write(&calc.join("FLOW-both.toml"), NONDETERMINISTIC);
        write(&calc.join("PATTERNS-orders.toml"), ORDERS);
        write(&calc.join("PATTERNS-claims.toml"), CALC_PATTERNS);
        let loop_dir = fixture("loop", "stepping-loop");
        let cases = [
            (calc.join("FLOW.toml"), calc.join("PATTERNS.toml")),
            (calc.join("FLOW.toml"), calc.join("PATTERNS-claims.toml")),
            (
                calc.join("FLOW-both.toml"),
                calc.join("PATTERNS-orders.toml"),
            ),
            (loop_dir.join("FLOW.toml"), loop_dir.join("PATTERNS.toml")),
        ];
        let mut compared = 0;
        for (manifest, patterns) in cases {
            // Every pair, so that every answer is compared with stepping.
            let (document, status) = full(&manifest, &patterns);
            // Answered, with the refuted claims of the claims fixture as findings.
            assert_ne!(status, EXIT_UNASKED, "{document:#}");
            assert_eq!(
                status,
                kink_flow::cli::query_status(&document),
                "{document:#}"
            );
            let list = PatternList::read(&patterns).unwrap();
            let stepper = Stepper::new(&manifest);
            for row in document["rows"].as_array().unwrap() {
                let entry = list
                    .patterns
                    .iter()
                    .find(|p| p.id == row["pattern"])
                    .unwrap();
                let program = row["program"].as_str().unwrap();
                let stepped = stepper.hit(program, &entry.pattern, 10_000);
                let expected = match row["answer"].as_str().unwrap() {
                    "hit" => Some(true),
                    "no" => Some(false),
                    other => panic!("{other} in {row:#}"),
                };
                assert_eq!(stepped, expected, "{} on {program}", entry.id);
                compared += 1;
            }
        }
        // Under `--full` every pattern asks every program, a claimed one included.
        assert_eq!(compared, 16 + 12 + 3 + 6);
    }
}

/// FB55-LIST-SCAN: a definition that appends `write(49424, N)`, then other writes, then
/// `read(49424, N)` to a `<bus>` list, one step each.
const BUS_SPEC: &str = r"module BUS-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= log(Int) [symbol(log)]
endmodule

module BUS
  imports BUS-SYNTAX
  imports INT
  imports LIST
  imports BOOL
  syntax KItem ::= w(Int, Int) [symbol(w)] | r(Int, Int) [symbol(r)]
  syntax KItem ::= write(Int, Int) [symbol(write)] | read(Int, Int) [symbol(read)]
  configuration <k> $PGM:Pgm </k> <bus> .List </bus>
  rule [log]: <k> log(N) => w(1, 0) ~> w(49424, N) ~> w(2, 0) ~> r(49424, N) ... </k>
  rule [w]: <k> w(A, V) => .K ... </k> <bus> B => B ListItem(write(A, V)) </bus>
  rule [r]: <k> r(A, V) => .K ... </k> <bus> B => B ListItem(read(A, V)) </bus>
endmodule
";

const BUS_PATTERNS: &str = r#"
[[pattern]]
id = "between"
pattern = "<bus> _:List ListItem(write(49424, _:Int)) _:List </bus>"

[[pattern]]
id = "write-then-read"
pattern = "<bus> L1:List ListItem(write(A1, V1)) L2:List ListItem(read(A2, V2)) L3:List </bus> requires V1 ==Int V2 andBool A1 ==Int A2"

[[pattern]]
id = "read-then-write"
pattern = "<bus> L1:List ListItem(read(A1, V1)) L2:List ListItem(write(A2, V2)) L3:List </bus> requires V1 ==Int V2"

[[pattern]]
id = "requires-only"
pattern = "<bus> L:List </bus> requires write(49424, W) in L"
"#;

/// FB55-LIST-SCAN: k-rust decides a pattern with an item between two list parts, or two ordered
/// items, on the closed `<bus>` lists a run reaches, so `kink-flow query` answers it: a write
/// followed later by a read of the value written is a hit, and the reverse order, which no state
/// has, a decided `no`. A `requires` naming a variable the cell patterns do not bind is left
/// undecided, and its cause says how to write the element in the cell instead.
#[test]
fn list_items_between_list_parts_are_answered() {
    let dir = spec_dir(
        "list-scan",
        "bus.k",
        "BUS",
        BUS_SPEC,
        "[[program]]\nid = \"log\"\ntext = \"log(7)\"\n",
        BUS_PATTERNS,
    );
    let (document, status) = plain(&dir.join("FLOW.toml"), &dir.join("PATTERNS.toml"));
    assert_eq!(status, EXIT_UNANSWERED, "{document:#}");
    assert_eq!(
        row(&document, "between", "log")["answer"],
        "hit",
        "{document:#}"
    );
    let written = row(&document, "write-then-read", "log");
    assert_eq!(written["answer"], "hit", "{written:#}");
    assert_eq!(written["witness"]["depth"], 5, "{written:#}");
    assert_eq!(
        row(&document, "read-then-write", "log")["answer"],
        NO,
        "{document:#}"
    );
    let unbound = row(&document, "requires-only", "log");
    assert_eq!(unbound["answer"], "unknown", "{unbound:#}");
    let cause = unbound["cause"].as_str().unwrap();
    for part in ["requires-only variable", "W", "L1:List ListItem(E) L2:List"] {
        assert!(cause.contains(part), "{part:?} in {cause}");
    }
}
