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
    pattern::{Answer, Facts, Lowering, PatternList, SearchOutcome, Searcher, judge},
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
    let (document, status) = plain(&dir.join("FLOW.toml"), &dir.join("PATTERNS.toml"));
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
    let (document, status) = plain(&dir.join("FLOW.toml"), &dir.join("PATTERNS.toml"));
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
        max_work: None,
        trace: false,
        cancelled_result: CancelledResultOutput::Error,
        match_states: None,
        collect_committed: false,
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
            ("result-above-five", "add", NO),
            ("result-above-five", "nested", "hit"),
            ("result-above-five", "sub", NO),
            ("result-above-five", "inline", "hit"),
        ])
    );
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
            ("cell", "could not parse rule in module \"CALC\""),
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
            json!([{"variable": "VarN:SortInt{}", "value": {"kore": "\\dv{SortInt{}}(\"2\")", "truncated": false}}])
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
        assert_eq!(
            document["counts"],
            json!({"hit": 3, "no": 3, "unknown": 0, "invalid-pattern": 0, "error": 0})
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
        assert_eq!(document["version"], 3);
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
        assert_eq!(witness["rendering"], "kore");
        assert_eq!(witness["rules"], json!(["CALC.add"]));
        assert_eq!(witness["state"]["truncated"], false);
        assert!(
            witness["state"]["kore"]
                .as_str()
                .unwrap()
                .contains("\\dv{SortInt{}}(\"3\")")
        );
        // The only binding is the author's I; the cell completion's generated variables are not
        // reported.
        assert_eq!(
            witness["bindings"],
            json!([{"variable": "VarI:SortInt{}", "value": {"kore": "\\dv{SortInt{}}(\"3\")", "truncated": false}}])
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
        // The corpus form asks every program; only those that reach 3 hit.
        assert_eq!(
            answers(&document)
                .into_iter()
                .filter(|(p, _, _)| p == "three")
                .collect::<Vec<_>>(),
            expect(&[
                ("three", "add", "hit"),
                ("three", "nested", NO),
                ("three", "sub", "hit"),
                ("three", "inline", NO),
            ])
        );
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
        // Re-pin probe P-1 (k-rust 58720d2e5; KINK-17/1, head 728e7eb34, merge 3a196ed14; k-rust's
        // draft answers-add3 section 2.1 "New marks of open values", which reach the four search
        // responses too): the match's path read `keys_list` of two keys, so it carries an
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
        assert_eq!(answers(&document), expect(&[("result-four", "add", NO)]));
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
            total["witness"]["state"]["kore"]
                .as_str()
                .unwrap()
                .contains("Lblh{}"),
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
            json!([{"variable": "VarV:SortInt{}", "value": {"kore": "\\dv{SortInt{}}(\"20\")", "truncated": false}}])
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
        assert_eq!(record["witness"], live_witness);
        let mut witness = live_witness.clone();
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
        assert_eq!(cached["witness"], witness);

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
        assert_eq!(mismatches[0]["live"]["witness"], live_witness);
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
        let (document, status) = plain(&bounded, &patterns);
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
        let (document, status) = plain(&dir.join("FLOW-timeout.toml"), &patterns);
        assert_eq!(status, EXIT_UNANSWERED, "{document:#}");
        let timed = row(&document, "zero", "spin");
        assert_eq!(timed["answer"], "unknown");
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

        let (again, _) = plain(&dir.join("FLOW-timeout.toml"), &patterns);
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
        let manifest = dir.join("FLOW.toml");
        let patterns = dir.join("PATTERNS.toml");
        let (first, status) = plain(&manifest, &patterns);
        assert_eq!(status, REFUTED_STATUS, "{first:#}");
        assert!(cached(&first).iter().all(|c| !c));
        let written = first["pattern_cache"]["records_written"].as_u64().unwrap();
        assert!(written > 0);
        assert_eq!(first["pattern_cache"]["enabled"], true);

        let (second, _) = plain(&manifest, &patterns);
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
        let (edited, _) = plain(&manifest, &patterns);
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
        let (commented, _) = plain(&manifest, &patterns);
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
        let (respec, _) = plain(&manifest, &patterns);
        assert!(cached(&respec).iter().all(|c| !c));

        // A time bound: every cached answer stands.
        let mut text = fs::read_to_string(&manifest).unwrap();
        text.push_str("\n[budget]\ntime_ms = 20000\n");
        fs::write(&manifest, &text).unwrap();
        let (retimed, _) = plain(&manifest, &patterns);
        assert!(cached(&retimed).iter().all(|c| *c), "{retimed:#}");

        // A depth bound: every row is recomputed.
        text.push_str("max_depth = 1000\n");
        fs::write(&manifest, text).unwrap();
        let (rebudget, _) = plain(&manifest, &patterns);
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
            let (document, status) = plain(&manifest, &patterns);
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
        assert_eq!(compared, 11 + 6 + 3 + 5);
    }
}
