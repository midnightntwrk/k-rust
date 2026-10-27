//! Executions mark every leaf whose path read a value the definition leaves open
//! (`docs/compatibility.md`, "Implementation-chosen hook values"): the leaf carries an
//! `implementation-chosen-value` diagnostic naming the hook and the class, and the result lists
//! every mark the run observed (`implementationChosenValues`), including the marks of work that
//! ended on no reported leaf. A mark never changes what the run explores: leaves, their order and
//! the work counts are those of an unmarked run.
//!
//! Every run goes through the facade (`Backend::execute`, `Backend::execute_observed`,
//! `Backend::search`), which runs programs in `Execution` mode, in both result modalities unless a
//! test says otherwise. The marks are read from the JSON a consumer reads.

use std::collections::BTreeSet;

use k_rust::{
    backend::{
        Backend, BackendOptions, ExecuteRequest, ExecutionStrategy, ObservedRequest,
        ResultModalityOutput, SearchPatternRequest, SearchRequest, SearchTypeArg,
    },
    builtin::embedded,
    kast::Sort,
    kompile::{
        CompilationBackend, CompileOptions, ConfigurationAssembler, ProgramGrammar,
        compile_loaded_definition,
    },
    kore::{ast::Pattern, codec, parser::parse_pattern, printer::Printer},
    outer::{LoadOptions, ResolvedSource, load_with_options},
};
use serde_json::Value;

const MODALITIES: [ResultModalityOutput; 2] = [
    ResultModalityOutput::PathSet,
    ResultModalityOutput::StateSet,
];

/// One mark: the hook and the class.
type Mark = (String, String);

fn mark(hook: &str, class: &str) -> Mark {
    (hook.to_owned(), class.to_owned())
}

/// Compile `source` (main and syntax module `MAIN`) with the prelude and assemble the initial
/// configuration whose `$PGM` is `program` at sort `Pgm`.
fn compile(source: &str, program: &str) -> (String, Pattern) {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("test.k", source),
        "MAIN",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            ..CompilationBackend::Rust.load_options()
        },
    )
    .unwrap();
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
    let frontend = loaded.into_definition();
    let grammar = ProgramGrammar::new(&frontend).unwrap();
    let mut assembler =
        ConfigurationAssembler::new(&grammar, "MAIN", "MAIN", &artifacts.configuration_variables);
    assembler.program(&Sort::new("Pgm"), program).unwrap();
    (artifacts.definition_kore, assembler.finish().unwrap())
}

fn backend(kore: &str) -> Backend {
    Backend::new(kore, "MAIN", BackendOptions::default()).unwrap()
}

fn request(
    initial: &Pattern,
    modality: ResultModalityOutput,
    strategy: ExecutionStrategy,
) -> ExecuteRequest {
    ExecuteRequest {
        result_modality: modality,
        strategy,
        ..ExecuteRequest::new(initial.clone())
    }
}

/// The result of `execute` as JSON, checked equal to `execute_observed`'s in every field the
/// marks are part of: each leaf's state, reason and diagnostics, and the result's list.
fn execute_with(
    kore: &str,
    initial: &Pattern,
    modality: ResultModalityOutput,
    strategy: ExecutionStrategy,
) -> Value {
    execute_edited(kore, initial, modality, strategy, |_| {})
}

/// [`execute_with`] of the request `edit` changes.
fn execute_edited(
    kore: &str,
    initial: &Pattern,
    modality: ResultModalityOutput,
    strategy: ExecutionStrategy,
    edit: impl Fn(&mut ExecuteRequest),
) -> Value {
    let edited = || {
        let mut request = request(initial, modality, strategy);
        edit(&mut request);
        request
    };
    let plain = backend(kore).execute(edited()).unwrap();
    let observed = backend(kore)
        .execute_observed(ObservedRequest {
            request: edited(),
            rules: None,
        })
        .unwrap();
    let plain = serde_json::to_value(&plain).unwrap();
    let observed = serde_json::to_value(&observed).unwrap();
    let essence = |result: &Value| {
        let leaves = result["leaves"]
            .as_array()
            .unwrap()
            .iter()
            .map(|leaf| (leaf["state"].clone(), leaf["reason"].clone(), marks(leaf)))
            .collect::<Vec<_>>();
        (leaves, run_marks(result))
    };
    assert_eq!(
        essence(&plain),
        essence(&observed),
        "observed and unobserved runs mark alike"
    );
    plain
}

fn execute(kore: &str, initial: &Pattern, modality: ResultModalityOutput) -> Value {
    execute_with(kore, initial, modality, ExecutionStrategy::All)
}

/// The marks among a leaf's (or a search state's) diagnostics.
fn marks(leaf: &Value) -> BTreeSet<Mark> {
    leaf["diagnostics"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|diagnostic| diagnostic["kind"] == "implementation-chosen-value")
        .map(|diagnostic| {
            mark(
                diagnostic["hook"].as_str().unwrap(),
                diagnostic["class"].as_str().unwrap(),
            )
        })
        .collect()
}

/// The result's list of every mark the run observed, in order.
fn run_marks(result: &Value) -> Vec<Mark> {
    result["implementationChosenValues"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|entry| {
            mark(
                entry["hook"].as_str().unwrap(),
                entry["class"].as_str().unwrap(),
            )
        })
        .collect()
}

fn leaves(result: &Value) -> &Vec<Value> {
    result["leaves"].as_array().unwrap()
}

/// A leaf's state, printed.
fn printed(leaf: &Value) -> String {
    Printer::compact().print_pattern(&codec::from_value(&leaf["state"]).unwrap())
}

/// The one leaf whose printed state contains `needle`.
fn leaf_with<'a>(result: &'a Value, needle: &str) -> &'a Value {
    let found = leaves(result)
        .iter()
        .filter(|leaf| printed(leaf).contains(needle))
        .collect::<Vec<_>>();
    assert_eq!(found.len(), 1, "one leaf holds {needle}: {result:#}");
    found[0]
}

/// Every leaf of a run of `program` carries exactly `expected`, and so does the result's list,
/// in both modalities; with `expected` empty the result has no `implementationChosenValues` key.
fn assert_marked(source: &str, program: &str, expected: &[Mark]) {
    let (kore, initial) = compile(source, program);
    for modality in MODALITIES {
        let result = execute(&kore, &initial, modality);
        let context = format!("{program} under {modality:?}: {result:#}");
        assert!(!leaves(&result).is_empty(), "{context}");
        for leaf in leaves(&result) {
            assert_eq!(
                marks(leaf),
                expected.iter().cloned().collect::<BTreeSet<_>>(),
                "{context}"
            );
        }
        assert_eq!(run_marks(&result), expected, "{context}");
        if expected.is_empty() {
            assert!(
                result.get("implementationChosenValues").is_none(),
                "{context}"
            );
        }
    }
}

const COLLECTIONS: &str = r#"
module MAIN
  imports INT
  imports MAP
  imports SET
  imports LIST
  imports COLLECTIONS
  syntax Pgm ::= choiceMap(Int) | choiceOne(Int) | keys(Int) | vals(Int) | s2l(Int)
               | choiceSet(Int) | done(KItem)
  configuration <k> $PGM:Pgm </k>
  rule choiceMap(N) => done(choice((N |-> 0) (N +Int 1 |-> 0)))
  rule choiceOne(N) => done(choice(N |-> 0))
  rule keys(N) => done(keys_list((N |-> 0) (N +Int 1 |-> 0)))
  rule vals(N) => done(values((N |-> 0) (N +Int 1 |-> 1)))
  rule s2l(N) => done(Set2List(SetItem(N) SetItem(N +Int 1)))
  rule choiceSet(N) => done(choice(SetItem(N) SetItem(N +Int 1)))
endmodule
"#;

#[test]
fn the_item_choice_gives_of_two_items_is_marked_and_of_one_item_is_not() {
    assert_marked(COLLECTIONS, "choiceMap(1)", &[mark("MAP.choice", "item")]);
    assert_marked(COLLECTIONS, "choiceSet(1)", &[mark("SET.choice", "item")]);
    assert_marked(COLLECTIONS, "choiceOne(1)", &[]);
}

#[test]
fn the_listing_order_of_two_items_is_marked() {
    assert_marked(COLLECTIONS, "keys(1)", &[mark("MAP.keys_list", "order")]);
    assert_marked(COLLECTIONS, "vals(1)", &[mark("MAP.values", "order")]);
    assert_marked(COLLECTIONS, "s2l(1)", &[mark("SET.set2list", "order")]);
}

const VALUES: &str = r#"
requires "substitution.md"
module MAIN
  imports INT
  imports FLOAT
  imports STRING
  imports SUBSTITUTION
  syntax Exp ::= KVar | lam(KVar, Exp) [binder] | app(Exp, Exp) | Int
  syntax Pgm ::= mixed(Float) | nan(Float) | b2s(Int) | mz(Float) | sub(Exp, Exp, KVar)
               | done(KItem)
  configuration <k> $PGM:Pgm </k>
  rule mixed(F) => done(F +Float 2.0)
  rule nan(F) => done(signFloat(F /Float F))
  rule b2s(I) => done(Base2String(I, 16))
  rule mz(F) => done(minFloat(F, --Float F))
  rule sub(T, V, X) => done(T[V / X])
endmodule
"#;

#[test]
fn float_letter_case_and_substitution_values_computed_at_run_time_are_marked() {
    assert_marked(
        VALUES,
        "mixed(0.1f)",
        &[mark("FLOAT.add", "float-destination")],
    );
    assert_marked(VALUES, "nan(0.0)", &[mark("FLOAT.sign", "nan-sign")]);
    assert_marked(
        VALUES,
        "b2s(255)",
        &[mark("STRING.base2string", "letter-case")],
    );
    assert_marked(VALUES, "b2s(9)", &[]);
    assert_marked(VALUES, "mz(0.0)", &[mark("FLOAT.min", "signed-zero")]);
    assert_marked(
        VALUES,
        "sub(lam(y, app(x, y)), 1, x)",
        &[mark("SUBSTITUTION.substOne", "fresh-name")],
    );
}

const CONDITIONS: &str = r#"
module MAIN
  imports INT
  imports MAP
  imports LIST
  imports K-EQUAL
  syntax List ::= f(Map) [function]
  rule f(M) => keys_list(M)
  syntax Pgm ::= r(Map) | q(Map) | a(Int) | b(Int)
  configuration <k> $PGM:Pgm </k>
  rule r(M) => a(1) requires keys_list(M)[0] ==K 1
  rule r(_) => b(2) [owise]
  rule q(M) => a(1) requires size(f(M)) >Int 1
  rule q(_) => b(2) [owise]
endmodule
"#;

/// The attempt of `r`'s first rule reads the listing order whether or not it applies: when its
/// condition is false the owise rule fires, and in another order the condition may hold.
#[test]
fn a_condition_that_read_an_open_value_marks_the_leaf_whether_or_not_the_rule_applied() {
    let keys = [mark("MAP.keys_list", "order")];
    // k-rust lists the keys in ascending order: the condition holds, `a`.
    assert_marked(CONDITIONS, "r(2 |-> 0 1 |-> 0)", &keys);
    // The first key is 2: the condition is false and the owise rule gives `b`.
    assert_marked(CONDITIONS, "r(10 |-> 0 2 |-> 0)", &keys);
    let (kore, initial) = compile(CONDITIONS, "r(10 |-> 0 2 |-> 0)");
    let result = execute(&kore, &initial, ResultModalityOutput::PathSet);
    leaf_with(&result, "Lblb'LPar");
    // An equation reached only inside a `requires` marks too.
    assert_marked(CONDITIONS, "q(1 |-> 0 2 |-> 0)", &keys);
}

const CANDIDATES: &str = r#"
module MAIN
  imports INT
  imports MAP
  imports LIST
  syntax Int ::= t(Map) [function, total]
  rule t(M) => 1 /Int (size(keys_list(M)) -Int 2)
  syntax Pgm ::= s(Map) | v(Map) | w(Map) | x(KItem) | y(Int)
  configuration <k> $PGM:Pgm </k>
  rule s(M) => x(keys_list(M))
  rule s(_) => y(1)
  // The right-hand side reads keys_list and is undefined on two keys; the sibling is defined
  // everywhere, so the candidate leaves no leaf.
  rule v(M) => x(1 /Int (size(keys_list(M)) -Int 2))
  rule v(_) => y(1)
  // The same through a function declared total, which only the successor's normalization shows
  // undefined.
  rule w(M) => x(t(M))
  rule w(_) => y(1)
endmodule
"#;

/// Under `path-set` the leaf of the candidate whose right-hand side read the listing carries the
/// mark and its sibling's does not: the sibling's leaf is a leaf in every model.
#[test]
fn only_the_candidate_whose_right_hand_side_read_an_open_value_is_marked() {
    let (kore, initial) = compile(CANDIDATES, "s(1 |-> 0 2 |-> 0)");
    for modality in MODALITIES {
        let result = execute(&kore, &initial, modality);
        assert_eq!(leaves(&result).len(), 2, "{result:#}");
        assert_eq!(
            marks(leaf_with(&result, "Lblx'LPar")),
            BTreeSet::from([mark("MAP.keys_list", "order")]),
            "{modality:?}: {result:#}"
        );
        assert_eq!(
            marks(leaf_with(&result, "Lbly'LPar")),
            BTreeSet::new(),
            "{modality:?}: {result:#}"
        );
        assert_eq!(run_marks(&result), [mark("MAP.keys_list", "order")]);
    }
}

/// Under the sequential strategy the instances on which a candidate is undefined go to the
/// candidates after it, so whether `y` is taken rests on the first candidate's own work: the
/// step notes the facts of an undefined alternative (`v`, in `apply`) and of a candidate it
/// rejects after normalizing it (`w`, a function trusted as total) again on the state's path,
/// and the `y` leaf carries the mark.
#[test]
fn under_the_sequential_strategy_a_rejected_candidates_mark_is_on_the_leaf_taken_after_it() {
    for program in ["v(1 |-> 0 2 |-> 0)", "w(1 |-> 0 2 |-> 0)"] {
        let (kore, initial) = compile(CANDIDATES, program);
        for modality in MODALITIES {
            let result = execute_with(&kore, &initial, modality, ExecutionStrategy::Any);
            let context = format!("{program}, {modality:?}: {result:#}");
            assert_eq!(leaves(&result).len(), 1, "{context}");
            assert_eq!(
                marks(leaf_with(&result, "Lbly'LPar")),
                BTreeSet::from([mark("MAP.keys_list", "order")]),
                "{context}"
            );
            assert_eq!(
                run_marks(&result),
                [mark("MAP.keys_list", "order")],
                "{context}"
            );
        }
    }
}

/// A candidate that read an open value and vanished (its instances are its defined sibling's)
/// leaves no leaf, but in another model it may give one: the result's list names its mark.
#[test]
fn a_vanished_candidates_mark_is_on_the_result_list_and_on_no_leaf() {
    for program in ["v(1 |-> 0 2 |-> 0)", "w(1 |-> 0 2 |-> 0)"] {
        let (kore, initial) = compile(CANDIDATES, program);
        for modality in MODALITIES {
            let result = execute(&kore, &initial, modality);
            let context = format!("{program}, {modality:?}: {result:#}");
            assert_eq!(leaves(&result).len(), 1, "{context}");
            leaf_with(&result, "Lbly'LPar");
            assert_eq!(marks(&leaves(&result)[0]), BTreeSet::new(), "{context}");
            assert_eq!(
                run_marks(&result),
                [mark("MAP.keys_list", "order")],
                "{context}"
            );
        }
    }
}

const DIAMOND: &str = r#"
module MAIN
  imports INT
  imports MAP
  imports LIST
  syntax Pgm ::= a(Map) | b(Map) | c(Map) | d(Map) | e(Int)
  configuration <k> $PGM:Pgm </k>
  rule [ab]: a(M) => b(M)
  rule [ac]: a(M) => c(M)
  rule [bd]: b(M) => d(M)
  rule [cd]: c(M) => d(M) requires size(keys_list(M)) >Int 0
  rule [de]: d(_) => e(1 /Int 0)
endmodule
"#;

/// The diamond `a -> b -> d`, `a -> c -> d` whose `d` step is undefined, with only the `c` path
/// reading an open value. Under `state-set` the `d` reached through `c` is merged into the one
/// reached through `b` as in an unmarked run (a mark never blocks a merge): one `trivial` leaf,
/// the same work, and the mark on the result's list. Under `path-set` exactly the leaf of the `c`
/// path is marked.
#[test]
fn a_mark_never_blocks_a_state_set_merge_and_reaches_the_result_list() {
    let (kore, initial) = compile(DIAMOND, "a(1 |-> 0 2 |-> 0)");
    let keys = mark("MAP.keys_list", "order");
    let state_set = execute(&kore, &initial, ResultModalityOutput::StateSet);
    // The result of main 9906372f8, where nothing marks: one leaf, five states visited and four expanded (the merged arrival is visited, not expanded).
    assert_eq!(leaves(&state_set).len(), 1, "{state_set:#}");
    assert_eq!(leaves(&state_set)[0]["reason"], "trivial", "{state_set:#}");
    assert_eq!(state_set["work"], 5, "{state_set:#}");
    assert_eq!(state_set["expanded"], 4, "{state_set:#}");
    assert_eq!(run_marks(&state_set), std::slice::from_ref(&keys));
    let path_set = execute(&kore, &initial, ResultModalityOutput::PathSet);
    assert_eq!(leaves(&path_set).len(), 2, "{path_set:#}");
    for leaf in leaves(&path_set) {
        let through_c = leaf["trace"]
            .as_array()
            .unwrap()
            .iter()
            .any(|entry| entry["label"] == "MAIN.cd");
        let expected = if through_c {
            BTreeSet::from([keys.clone()])
        } else {
            BTreeSet::new()
        };
        assert_eq!(marks(leaf), expected, "{leaf:#}");
    }
    assert_eq!(run_marks(&path_set), [keys]);
}

const DISCARDED: &str = r#"
module MAIN
  imports INT
  imports MAP
  imports LIST
  imports BOOL
  imports K-EQUAL
  syntax Pgm ::= s(Map) | p(Int, Map) | size2(Map) | done(Int)
  configuration <k> $PGM:Pgm </k>
  rule s(M) => p(1, M)
  rule s(M) => p(2, M)
  rule s(M) => p(3, M)
  rule p(N, M) => done(#if true #then N #else 10 /Int (#if keys_list(M)[0] ==K 1 #then 1 #else 0 #fi) #fi)
  rule size2(M) => done(#if true #then 1 #else size(keys_list(M)) #fi)
endmodule
"#;

/// The operand a decided `#if` discards is only checked for definedness. `size` is total, so
/// the definedness of `size(keys_list(M))` is the same whatever the listing: no mark.
#[test]
fn a_discarded_operand_whose_definedness_cannot_depend_on_the_value_is_not_marked() {
    assert_marked(DISCARDED, "size2(1 |-> 0 2 |-> 0)", &[]);
}

/// Here the discarded operand's definedness depends on the listing: with the keys in k-rust's
/// order the first key is 1 and `10 /Int 1` is defined, so the `#if` is `N`; with the other order
/// the divisor is zero and the `#if` is undefined. Three paths read the same application, the later ones
/// through the deferred hook memo, and every leaf is marked.
#[test]
fn a_discarded_operand_whose_definedness_depends_on_the_value_marks_every_path_through_the_memo() {
    let (kore, initial) = compile(DISCARDED, "s(1 |-> 0 2 |-> 0)");
    for modality in MODALITIES {
        let result = execute(&kore, &initial, modality);
        assert_eq!(leaves(&result).len(), 3, "{result:#}");
        for leaf in leaves(&result) {
            assert_eq!(
                marks(leaf),
                BTreeSet::from([mark("MAP.keys_list", "order")]),
                "{modality:?}: {result:#}"
            );
        }
    }
}

const SEARCH: &str = r#"
module MAIN
  imports INT
  imports MAP
  imports LIST
  syntax Pgm ::= s(Map) | a(Map) | b(Map) | c(Int)
  configuration <k> $PGM:Pgm </k>
  rule s(M) => b(M)
  rule s(M) => a(M)
  rule b(_) => c(2)
  rule a(M) => c(size(keys_list(M)))
endmodule
"#;

/// Both paths reach `c(2)` at depth 2; the search keeps the first (through `b`, unmarked) and
/// drops the second (through `a`, which read the listing). The kept state carries the dropped
/// one's mark.
#[test]
fn a_search_duplicate_that_carries_a_mark_gives_it_to_the_kept_state() {
    let (kore, initial) = compile(SEARCH, "s(1 |-> 0 2 |-> 0)");
    let response = backend(&kore)
        .search(SearchRequest {
            search_type: SearchTypeArg::All,
            ..SearchRequest::new(initial)
        })
        .unwrap();
    let response = serde_json::to_value(&response).unwrap();
    let states = response["states"].as_array().unwrap();
    let c = states
        .iter()
        .filter(|state| printed(state).contains("Lblc'LPar"))
        .collect::<Vec<_>>();
    assert_eq!(c.len(), 1, "{response:#}");
    assert_eq!(
        marks(c[0]),
        BTreeSet::from([mark("MAP.keys_list", "order")]),
        "{response:#}"
    );
}

const SURVIVORS: &str = r#"
module MAIN
  imports INT
  imports MAP
  imports LIST
  syntax Pgm ::= w(Map) | x(Int) | z(Int) | h(Int)
  configuration <k> $PGM:Pgm </k>
  rule [wx]: w(M) => x(1 /Int ({keys_list(M)[0]}:>Int -Int 1))
  rule [wz]: w(_) => z(3)
  rule [zz]: z(N) => z(N -Int 1) requires N >Int 0
  rule [zh]: z(0) => h(0)
endmodule
"#;

/// Whether `wx` is defined rests on the listing order. k-rust lists the keys of the first map
/// as 1, 2, so the divisor is 0 and `wx` is undefined: `wz` is the state's one successor. On the
/// second map the divisor is 1 and `wx` gives `x(1)`, which is what the first map gives in the
/// other order: `w` has two successors.
const SURVIVOR_PROGRAMS: [&str; 2] = ["w(1 |-> 0 2 |-> 0)", "w(2 |-> 0 3 |-> 0)"];

/// A named change to a request.
type RequestEdit = (&'static str, fn(&mut ExecuteRequest));

/// The requests whose halts rest on how many candidates of a step survive.
const COUNT_OPTIONS: [RequestEdit; 3] = [
    ("terminal-rules", |request| {
        request.terminal_rules = vec!["MAIN.wz".to_owned()];
    }),
    ("cut-point-rules", |request| {
        request.cut_point_rules = vec!["MAIN.wz".to_owned()];
    }),
    ("stop-at-branch", |request| request.stop_at_branch = true),
];

/// With no such option, `h(0)` is reached through `wz` whatever `wx` gives, and it is unmarked;
/// `x(1)` is marked. A terminal or cut-point rule, or a stop at a branch, ends the run at `w` or
/// `z(3)` only where `wz` is `w`'s one successor, which rests on `wx`'s undefinedness: in the other
/// order the first map's run ends with `x(1)` and `h(0)` instead. So under each of them every leaf
/// carries `wx`'s mark (the halting state's path takes every candidate's marks).
#[test]
fn a_halt_that_rests_on_how_many_candidates_survive_carries_every_candidates_marks() {
    let keys = BTreeSet::from([mark("MAP.keys_list", "order")]);
    for program in SURVIVOR_PROGRAMS {
        let (kore, initial) = compile(SURVIVORS, program);
        for modality in MODALITIES {
            let plain = execute(&kore, &initial, modality);
            assert_eq!(
                marks(leaf_with(&plain, "Lblh'LPar")),
                BTreeSet::new(),
                "{program}, {modality:?}: {plain:#}"
            );
            for leaf in leaves(&plain) {
                if printed(leaf).contains("Lblx'LPar") {
                    assert_eq!(marks(leaf), keys, "{program}, {modality:?}: {plain:#}");
                }
            }
            for (option, edit) in COUNT_OPTIONS {
                let result =
                    execute_edited(&kore, &initial, modality, ExecutionStrategy::All, edit);
                let context = format!("{program}, {option}, {modality:?}: {result:#}");
                assert!(!leaves(&result).is_empty(), "{context}");
                for leaf in leaves(&result) {
                    assert_eq!(marks(leaf), keys, "{context}");
                }
                assert_eq!(
                    run_marks(&result),
                    [mark("MAP.keys_list", "order")],
                    "{context}"
                );
            }
        }
    }
}

/// `maxWork` and `maxBreadth` count the states of every path, so where they cut a run rests on
/// the paths off a leaf's own: on the second map, with `maxWork` 3, `z(3)` is a `work-bound`
/// leaf because `x(1)` took a state, and in the other order the first map's run cuts at `z(1)`;
/// with `maxBreadth` 1, `x(1)` and `z(3)` are `breadth-bound` leaves only because `w` has two
/// successors. Every leaf of such a run carries every mark of the run's list.
#[test]
fn a_run_bounded_by_work_or_breadth_marks_every_leaf_with_its_list() {
    let bounds: [RequestEdit; 2] = [
        ("max-work", |request| request.max_work = Some(3)),
        ("max-breadth", |request| request.max_breadth = Some(1)),
    ];
    for program in SURVIVOR_PROGRAMS {
        let (kore, initial) = compile(SURVIVORS, program);
        for modality in MODALITIES {
            for (bound, edit) in bounds {
                let result =
                    execute_edited(&kore, &initial, modality, ExecutionStrategy::All, edit);
                let context = format!("{program}, {bound}, {modality:?}: {result:#}");
                let list = run_marks(&result);
                assert_eq!(list, [mark("MAP.keys_list", "order")], "{context}");
                assert!(!leaves(&result).is_empty(), "{context}");
                for leaf in leaves(&result) {
                    assert_eq!(
                        marks(leaf),
                        list.iter().cloned().collect::<BTreeSet<_>>(),
                        "{context}"
                    );
                }
            }
        }
    }
}

/// Without a stop rule among `w`'s candidates, `w` cannot halt by one, whatever survives:
/// `wx`'s mark stays on its own paths. Under `path-set` the `h(0)` that `wz` leads to is
/// unmarked with `zh` as the terminal or the cut-point rule (the leaf is `h(0)` or `z(0)`).
/// Where a candidate of the state is a stop rule, its marks are on the state's path even when it
/// vanished: with `wx` as the terminal rule, `wx` is undefined on the first map and `wz` is `w`'s
/// one successor, while in the other order `wx` survives too, so every leaf carries the mark.
#[test]
fn a_state_whose_candidates_use_no_stop_rule_keeps_their_marks_on_their_own_paths() {
    let keys = BTreeSet::from([mark("MAP.keys_list", "order")]);
    let unselected: [(RequestEdit, &str); 2] = [
        (
            ("terminal-zh", |request| {
                request.terminal_rules = vec!["MAIN.zh".to_owned()];
            }),
            "Lblh'LPar",
        ),
        (
            ("cut-point-zh", |request| {
                request.cut_point_rules = vec!["MAIN.zh".to_owned()];
            }),
            "Lblz'LPar",
        ),
    ];
    let modality = ResultModalityOutput::PathSet;
    for program in SURVIVOR_PROGRAMS {
        let (kore, initial) = compile(SURVIVORS, program);
        for ((option, edit), reached) in unselected {
            let result = execute_edited(&kore, &initial, modality, ExecutionStrategy::All, edit);
            let context = format!("{program}, {option}: {result:#}");
            assert_eq!(
                marks(leaf_with(&result, reached)),
                BTreeSet::new(),
                "{context}"
            );
            for leaf in leaves(&result) {
                if printed(leaf).contains("Lblx'LPar") {
                    assert_eq!(marks(leaf), keys, "{context}");
                }
            }
        }
        for strategy in [ExecutionStrategy::All, ExecutionStrategy::Any] {
            let result = execute_edited(&kore, &initial, modality, strategy, |request| {
                request.terminal_rules = vec!["MAIN.wx".to_owned()];
            });
            let context = format!("{program}, terminal-wx, {strategy:?}: {result:#}");
            assert!(!leaves(&result).is_empty(), "{context}");
            for leaf in leaves(&result) {
                assert_eq!(marks(leaf), keys, "{context}");
            }
        }
    }
}

const MERGE: &str = r#"
module MAIN
  imports INT
  imports MAP
  imports LIST
  syntax Pgm ::= a(Map) | b(Int) | c(Map) | x(Int)
  configuration <k> $PGM:Pgm </k>
  rule [ac]: a(M) => c(M)
  rule [ab]: a(_) => b(3)
  rule [cx]: c(M) => x(0) requires {keys_list(M)[0]}:>Int ==Int 2
  rule [bb]: b(N) => b(N -Int 1) requires N >Int 0
  rule [bx]: b(0) => x(0)
endmodule
"#;

/// [`MERGE`] with `ab` first, so that the `b` chain is explored first.
const MERGE_AB_FIRST: &str = r#"
module MAIN
  imports INT
  imports MAP
  imports LIST
  syntax Pgm ::= a(Map) | b(Int) | c(Map) | x(Int)
  configuration <k> $PGM:Pgm </k>
  rule [ab]: a(_) => b(3)
  rule [ac]: a(M) => c(M)
  rule [cx]: c(M) => x(0) requires {keys_list(M)[0]}:>Int ==Int 2
  rule [bb]: b(N) => b(N -Int 1) requires N >Int 0
  rule [bx]: b(0) => x(0)
endmodule
"#;

/// `x(0)` is reached through the `b` chain at depth 5 in every model and, in the model that lists
/// the keys of the map the other way, also through `c` at depth 2 (`cx`'s condition reads the
/// listing; k-rust's run of `a(2 |-> 0 3 |-> 0)` behaves like it). A `state-set` result keeps the
/// first `x(0)` leaf it meets, which may stand for a later one of another halt: in that model,
/// with `maxDepth` 5 the depth-2 `stuck` leaf stands for the depth-5 `depth-bound` one, and with
/// `cx` as the terminal rule the `terminal` leaf stands for the `stuck` one. k-rust's unmarked
/// `x(0)` leaf is then absent there, so under `state-set` it carries the run's list, in either
/// rule order. A halt that only a leaf of its own class can stand for (`stuck` without terminal
/// rules, beside `cut-point`) keeps its configuration and halt in every model, and only its witness
/// (depth and trace) may change, so it stays unmarked; a `path-set` result merges nothing and is
/// unchanged.
#[test]
fn under_state_set_a_leaf_another_halt_can_stand_for_carries_the_list() {
    let keys = BTreeSet::from([mark("MAP.keys_list", "order")]);
    let cases: [(RequestEdit, bool); 4] = [
        (("plain", |_| {}), false),
        (("max-depth-5", |request| request.max_depth = Some(5)), true),
        (
            ("terminal-cx", |request| {
                request.terminal_rules = vec!["MAIN.cx".to_owned()];
            }),
            true,
        ),
        (
            ("cut-point-cx", |request| {
                request.cut_point_rules = vec!["MAIN.cx".to_owned()];
            }),
            false,
        ),
    ];
    for source in [MERGE, MERGE_AB_FIRST] {
        let (kore, initial) = compile(source, "a(1 |-> 0 2 |-> 0)");
        for modality in MODALITIES {
            for ((option, edit), replaceable) in cases {
                let result =
                    execute_edited(&kore, &initial, modality, ExecutionStrategy::All, edit);
                let context = format!("{option}, {modality:?}: {result:#}");
                assert_eq!(
                    run_marks(&result),
                    [mark("MAP.keys_list", "order")],
                    "{context}"
                );
                let expected = if replaceable && modality == ResultModalityOutput::StateSet {
                    keys.clone()
                } else {
                    BTreeSet::new()
                };
                assert_eq!(
                    marks(leaf_with(&result, "Lblx'LPar")),
                    expected,
                    "{context}"
                );
                assert_eq!(marks(leaf_with(&result, "Lblc'LPar")), keys, "{context}");
            }
        }
    }
}

const SEARCH_ON: &str = r#"
module MAIN
  imports INT
  imports MAP
  imports LIST
  syntax Pgm ::= s(Map) | a(Map) | b(Map) | c(Int) | e(Int)
  configuration <k> $PGM:Pgm </k>
  rule s(M) => b(M)
  rule s(M) => a(M)
  rule b(_) => c(2)
  rule a(M) => c(size(keys_list(M)))
  rule c(N) => e(N)
endmodule
"#;

/// The marks among a search response's states (or witnesses, or matches' states), by printed
/// head.
fn state_marks(states: &[Value], head: &str) -> Vec<BTreeSet<Mark>> {
    states
        .iter()
        .filter(|state| printed(state).contains(head))
        .map(marks)
        .collect()
}

/// The `c(2)` reached through `a`, which read the listing, is dropped as a duplicate of the one
/// reached through `b`. The kept state carries its mark, and so does every state derived from
/// it (`e(2)`): the dropped state's successors are the kept one's. Every search response lists
/// the mark.
#[test]
fn a_search_duplicates_marks_reach_the_kept_states_descendants_and_every_search_lists_them() {
    let (kore, initial) = compile(SEARCH_ON, "s(1 |-> 0 2 |-> 0)");
    let keys = BTreeSet::from([mark("MAP.keys_list", "order")]);
    let search = SearchRequest {
        search_type: SearchTypeArg::All,
        ..SearchRequest::new(initial.clone())
    };
    let response = serde_json::to_value(backend(&kore).search(search.clone()).unwrap()).unwrap();
    let states = response["states"].as_array().unwrap();
    assert_eq!(
        state_marks(states, "Lblc'LPar"),
        std::slice::from_ref(&keys),
        "{response:#}"
    );
    assert_eq!(
        state_marks(states, "Lble'LPar"),
        std::slice::from_ref(&keys),
        "{response:#}"
    );
    assert_eq!(
        run_marks(&response),
        [mark("MAP.keys_list", "order")],
        "{response:#}"
    );
    // A path search keeps both paths: only those through `a` are marked.
    let paths = serde_json::to_value(backend(&kore).search_paths(search).unwrap()).unwrap();
    let witnesses = paths["witnesses"].as_array().unwrap();
    let mut e = state_marks(witnesses, "Lble'LPar");
    e.sort();
    assert_eq!(e, [BTreeSet::new(), keys.clone()], "{paths:#}");
    assert_eq!(
        run_marks(&paths),
        [mark("MAP.keys_list", "order")],
        "{paths:#}"
    );
    let target = parse_pattern("VarResult:SortGeneratedTopCell{}").unwrap();
    let pattern = SearchPatternRequest {
        search_type: SearchTypeArg::All,
        ..SearchPatternRequest::new(initial, target)
    };
    let matched =
        serde_json::to_value(backend(&kore).search_pattern(pattern.clone()).unwrap()).unwrap();
    assert_eq!(
        run_marks(&matched),
        [mark("MAP.keys_list", "order")],
        "{matched:#}"
    );
    // The match of the kept `c(2)` was taken before the duplicate was dropped; it takes the marks
    // its result received since, and so does the match of `e(2)`.
    let matched_states = matched["matches"]
        .as_array()
        .unwrap()
        .iter()
        .map(|found| found["state"].clone())
        .collect::<Vec<_>>();
    for head in ["Lblc'LPar", "Lble'LPar"] {
        assert_eq!(
            state_marks(&matched_states, head),
            std::slice::from_ref(&keys),
            "{matched:#}"
        );
    }
    let matched_paths =
        serde_json::to_value(backend(&kore).search_pattern_paths(pattern).unwrap()).unwrap();
    assert_eq!(
        run_marks(&matched_paths),
        [mark("MAP.keys_list", "order")],
        "{matched_paths:#}"
    );
}

const PATTERN_EXISTENTIAL: &str = r#"
module MAIN
  imports INT
  imports MAP
  imports LIST
  syntax Pgm ::= go(Map) | c(Int) | t(Int)
  configuration <k> $PGM:Pgm </k>
  rule [g1]: go(M) => t(size(keys_list(M)))
  rule [t]: t(N) => c(N)
  rule [g2]: go(_) => c(?X) ensures ?X ==Int 2
endmodule
"#;

/// Two distinct search states can have one solution: `g2` gives `c(?X)` with `?X` equal to 2,
/// whose state differs from the `c(2)` that `g1` and `t` give by its constraint on the minted
/// variable, and a target that names only the term matches both with the same bindings. The
/// graph search keeps both, the unmarked one at depth 1 and the one that read the listing at
/// depth 2. The pattern search keeps the first match for the solution, and it carries the mark of
/// the dropped one.
#[test]
fn a_pattern_match_dropped_as_the_same_solution_gives_its_marks_to_the_kept_match() {
    let (kore, initial) = compile(PATTERN_EXISTENTIAL, "go(1 |-> 0 2 |-> 0)");
    let keys = BTreeSet::from([mark("MAP.keys_list", "order")]);
    let search = SearchRequest {
        search_type: SearchTypeArg::All,
        ..SearchRequest::new(initial.clone())
    };
    let response = serde_json::to_value(backend(&kore).search(search).unwrap()).unwrap();
    let mut found = response["states"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|state| {
            printed(state)
                .contains(r#"Lblc'LParUndsRParUnds'MAIN'Unds'Pgm'Unds'Int{}(\dv{SortInt{}}("2"))"#)
        })
        .map(|state| (state["depth"].as_u64().unwrap(), marks(state)))
        .collect::<Vec<_>>();
    found.sort();
    assert_eq!(
        found,
        [(1, BTreeSet::new()), (2, keys.clone())],
        "{response:#}"
    );
    let target = parse_pattern(
        r"Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortPgm{}, SortKItem{}}(Lblc'LParUndsRParUnds'MAIN'Unds'Pgm'Unds'Int{}(VarN:SortInt{})), dotk{}())), VarG:SortGeneratedCounterCell{})",
    )
    .unwrap();
    let pattern = SearchPatternRequest {
        search_type: SearchTypeArg::All,
        ..SearchPatternRequest::new(initial, target)
    };
    let matched = serde_json::to_value(backend(&kore).search_pattern(pattern).unwrap()).unwrap();
    let matches = matched["matches"].as_array().unwrap();
    assert_eq!(matches.len(), 1, "{matched:#}");
    assert_eq!(matches[0]["state"]["depth"], 1, "{matched:#}");
    assert_eq!(marks(&matches[0]["state"]), keys, "{matched:#}");
}

const SEARCH_END: &str = r#"
module MAIN
  imports INT
  imports MAP
  imports LIST
  syntax Pgm ::= go(Map) | c(Int)
  configuration <k> $PGM:Pgm </k>
  rule go(M) => c(size(keys_list(M)))
endmodule
"#;

/// With one result allowed, the search stops at the initial state, and whether it ends
/// `exhausted` or at its result bound rests on that state's step, which reads the listing: the
/// result is unmarked (its path read nothing), and the search's list names the mark.
#[test]
fn the_end_of_a_bounded_search_rests_on_its_list() {
    let (kore, initial) = compile(SEARCH_END, "go(1 |-> 0 2 |-> 0)");
    let response = serde_json::to_value(
        backend(&kore)
            .search(SearchRequest {
                search_type: SearchTypeArg::All,
                max_results: Some(1),
                ..SearchRequest::new(initial)
            })
            .unwrap(),
    )
    .unwrap();
    let states = response["states"].as_array().unwrap();
    assert_eq!(
        state_marks(states, "Lblgo'LPar"),
        [BTreeSet::new()],
        "{response:#}"
    );
    assert_eq!(
        run_marks(&response),
        [mark("MAP.keys_list", "order")],
        "{response:#}"
    );
}

const PLAIN: &str = r#"
module MAIN
  imports INT
  imports FLOAT
  imports STRING
  syntax Pgm ::= s(Float) | done(String)
  configuration <k> $PGM:Pgm </k>
  rule s(F) => done(Float2String(F))
endmodule
"#;

/// A run that evaluates no open value is as on main: no mark and no
/// `implementationChosenValues` key, its other diagnostics unchanged.
#[test]
fn a_run_without_open_values_has_main_s_diagnostics_and_no_list() {
    let (kore, initial) = compile(PLAIN, "s(1.0)");
    for modality in MODALITIES {
        let result = backend(&kore)
            .execute(request(&initial, modality, ExecutionStrategy::All))
            .unwrap();
        let result = serde_json::to_value(&result).unwrap();
        assert!(
            result.get("implementationChosenValues").is_none(),
            "{result:#}"
        );
        let diagnostics = leaves(&result)
            .iter()
            .map(|leaf| leaf["diagnostics"].clone())
            .collect::<Vec<_>>();
        // The diagnostics of main 9906372f8.
        assert_eq!(
            serde_json::to_string(&diagnostics).unwrap(),
            r#"[[{"hook":"STRING.float2string","kind":"unsupported-hook-unevaluated","reason":"no evaluator in this backend, and no equation of the definition applies"}]]"#,
            "{modality:?}: {result:#}"
        );
    }
}

/// The capability is advertised.
#[test]
fn the_capability_is_advertised() {
    let (kore, _) = compile(PLAIN, "s(1.0)");
    let capabilities = serde_json::to_value(backend(&kore).capabilities()).unwrap();
    assert_eq!(capabilities["implementationChosenValues"], true);
}

/// A rule with two `!` names (`mk`), whose association of names to counter offsets the
/// definition leaves open (`fresh-association`); two rules with one name each, applied on two
/// steps (`one`, then `again`); and, for `go`, a two-name rule whose right-hand side is
/// undefined where `!A` is 0, beside a plain sibling (FZ-FRESH design, probe P-RB).
const FRESH: &str = r#"
module MAIN
  imports INT
  imports BOOL
  syntax Pgm ::= mk(Int) | one(Int) | go(Int)
  syntax KItem ::= "again"
  configuration <T> <k> $PGM:Pgm </k> <a> 7 </a> <b> 7 </b> <r> 7 </r> </T>
  rule [mk]: <k> mk(_) => .K ... </k> <a> _ => !_A:Int </a> <b> _ => !_B:Int </b>
  rule <k> one(_) => again ... </k> <a> _ => !_A:Int </a>
  rule <k> again => .K ... </k> <b> _ => !_B:Int </b>
  rule [div]: <k> go(_) => .K ... </k> <r> _ => 10 /Int !_A:Int </r> <b> _ => !_B:Int </b>
  rule <k> go(_) => .K ... </k>
endmodule
"#;

/// The attributes of the axiom of `kore` labelled `label`.
fn axiom_attributes(kore: &str, label: &str) -> Vec<Pattern> {
    let definition = k_rust::kore::parser::parse_definition(kore).unwrap();
    let labelled = |attributes: &[Pattern]| {
        attributes
            .iter()
            .any(|attribute| attribute_string(attribute, "label").as_deref() == Some(label))
    };
    let axioms = definition
        .modules
        .iter()
        .flat_map(|module| &module.sentences)
        .filter_map(|sentence| match sentence {
            k_rust::kore::ast::Sentence::Axiom { attributes, .. } if labelled(&attributes.0) => {
                Some(attributes.0.clone())
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    let [attributes] = &axioms[..] else {
        panic!("one axiom is labelled {label}: {axioms:?}");
    };
    attributes.clone()
}

/// The string argument of `attribute` when it is an application of `name` to one string.
fn attribute_string(attribute: &Pattern, name: &str) -> Option<String> {
    match attribute {
        Pattern::Application { symbol, arguments } if symbol.name == name => match &arguments[..] {
            [Pattern::String(value)] => {
                Some(String::from_utf8_lossy(value.as_bytes()).into_owned())
            }
            _ => None,
        },
        _ => None,
    }
}

/// The `UNIQUE_ID` of the rewrite axiom of `kore` labelled `label`, the hook a
/// `fresh-association` mark of that rule names.
fn unique_id(kore: &str, label: &str) -> String {
    axiom_attributes(kore, label)
        .iter()
        .find_map(|attribute| attribute_string(attribute, "UNIQUE'Unds'ID"))
        .expect("the axiom has a UNIQUE_ID")
}

/// KR-MARK (FZ-FRESH): a step that builds a candidate of a rule with two `!` names takes k-rust's
/// association of the names to counter offsets, which the definition leaves open
/// (`docs/compatibility.md`, "Compiler-resolved fresh constants"): the leaf and the run's list
/// carry the mark `fresh-association`, whose hook is the rule's `UNIQUE_ID`.
#[test]
fn a_step_of_a_rule_with_two_fresh_names_is_marked_with_the_rule() {
    let (kore, _) = compile(FRESH, "mk(3)");
    let rule = unique_id(&kore, "MAIN.mk");
    assert_marked(FRESH, "mk(3)", &[mark(&rule, "fresh-association")]);
}

/// G-ONE-NAME (FZ-FRESH): a rule with one `!` name has one association, so a run that applies
/// two such rules (each mints one value, two values in all) is unmarked.
#[test]
fn rules_with_one_fresh_name_each_are_not_marked() {
    assert_marked(FRESH, "one(3)", &[]);
}

/// KR-ROLLBACK (FZ-FRESH): `go`'s two-name candidate is undefined under k-rust's association
/// (`!A` is 0, `10 /Int 0`) and vanishes beside its plain sibling, so the one leaf (`<r> 7`) is
/// a leaf under every association and unmarked; under the other association the candidate gives
/// a second end, so the run's list names the mark.
#[test]
fn a_vanished_two_name_candidates_mark_is_on_the_result_list_and_on_no_leaf() {
    let (kore, initial) = compile(FRESH, "go(3)");
    let rule = unique_id(&kore, "MAIN.div");
    for modality in MODALITIES {
        let result = execute(&kore, &initial, modality);
        let context = format!("{modality:?}: {result:#}");
        assert_eq!(leaves(&result).len(), 1, "{context}");
        assert_eq!(marks(&leaves(&result)[0]), BTreeSet::new(), "{context}");
        assert_eq!(
            run_marks(&result),
            [mark(&rule, "fresh-association")],
            "{context}"
        );
    }
}

/// G-NO-DIGEST (FZ-FRESH): a two-name rule is classified when the definition is loaded, from the
/// compiled counter advance, so compilation records nothing of it: the axiom carries only its id,
/// its label and its source location, and the compiled definition (and with it the execution digest) is
/// the one compiled before the mark existed.
#[test]
fn a_two_name_rule_compiles_without_an_attribute_for_its_association() {
    let (kore, _) = compile(FRESH, "mk(3)");
    let attributes = axiom_attributes(&kore, "MAIN.mk");
    let names = attributes
        .iter()
        .map(|attribute| match attribute {
            Pattern::Application { symbol, .. } => symbol.name.as_str(),
            other => panic!("an attribute that is no application: {other:?}"),
        })
        .collect::<Vec<_>>();
    assert_eq!(
        names,
        [
            "UNIQUE'Unds'ID",
            "label",
            "org'Stop'kframework'Stop'attributes'Stop'Location",
            "org'Stop'kframework'Stop'attributes'Stop'Source",
        ]
    );
}

/// The backend's own executions, for what the facade does not reach: several initial patterns
/// sharing one run, and a console.
mod backend_runs {
    use super::*;
    use k_rust_backend::{
        evaluation::EvaluationMode,
        rewrite::{
            ExecutionMode, ExecutionOptions, ExecutionResult, Pattern as BackendPattern,
            execute_disjunction_with_solver_and_observer, execute_with_io_state,
        },
        search::ResultModality,
        smt::NoSolver,
        transition::ExecutionIoState,
    };

    fn internal(kore: &str, initial: &Pattern) -> (Backend, BackendPattern) {
        let mut backend = backend(kore);
        let definition = backend.select_definition(None).unwrap();
        let pattern = definition
            .admit_unverified(initial, &[])
            .internalize_pattern()
            .unwrap();
        (backend, pattern)
    }

    /// The marks on each leaf, read through the diagnostics' debug form (`hook` and `class`).
    fn leaf_marks(result: &ExecutionResult) -> Vec<usize> {
        result
            .leaves
            .iter()
            .map(|leaf| {
                format!("{:?}", leaf.diagnostics)
                    .matches("ImplementationChosenValue")
                    .count()
            })
            .collect()
    }

    const LOOP: &str = r#"
module MAIN
  imports INT
  imports MAP
  imports LIST
  imports K-EQUAL
  syntax Pgm ::= loop(Int, Map) | done(Int)
  configuration <k> $PGM:Pgm </k>
  rule [hit]: loop(N, M) => done(N) requires keys_list(M)[0] ==K 7
  rule loop(N, M) => loop(N -Int 1, M) requires N >Int 0 [priority(60)]
  rule loop(0, _) => done(0) [priority(60)]
endmodule
"#;

    /// The sequential step keeps one refutation memo for the run, shared by its initial
    /// patterns. `hit`'s condition is refuted through the listing on the first pattern; a memo
    /// that stored that refutation would answer the second pattern's attempt without reading
    /// the listing, and that path's leaf would carry no mark. A refutation that read an open
    /// value is not stored, so every leaf is marked.
    #[test]
    fn a_refutation_that_read_an_open_value_is_not_reused_without_its_mark() {
        let (kore, initial) = compile(LOOP, "loop(2, 1 |-> 0 2 |-> 0)");
        let (mut backend, pattern) = internal(&kore, &initial);
        let definition = backend.select_definition(None).unwrap();
        let result = execute_disjunction_with_solver_and_observer(
            &definition,
            vec![pattern.clone(), pattern],
            ExecutionOptions {
                mode: ExecutionMode::Any,
                result_modality: ResultModality::PathSet,
                evaluation: EvaluationMode::Execution,
                ..ExecutionOptions::default()
            },
            &NoSolver,
            |_| {},
        );
        assert_eq!(result.leaves.len(), 2, "{result:#?}");
        assert!(
            leaf_marks(&result).iter().all(|count| *count == 1),
            "{:?}: {result:#?}",
            leaf_marks(&result)
        );
    }

    const READ: &str = r#"
module MAIN
  imports INT
  imports STRING
  imports K-IO
  syntax Pgm ::= rd(Int) | done(IOString)
  configuration <k> $PGM:Pgm </k>
  rule rd(N) => done(#read(0, N))
endmodule
"#;

    /// `#read` may return fewer characters than requested: a read that returned two is marked,
    /// one that returned one is not (one character could be fewer only by being none, which
    /// states end of file). The backend's executions with default options run in `Proof`, where
    /// the read count is not withheld (a proof route has no console), and mark it too.
    #[test]
    fn a_read_of_two_characters_is_marked_and_of_one_is_not() {
        for (program, expected) in [("rd(2)", 1), ("rd(1)", 0)] {
            let (kore, initial) = compile(READ, program);
            let (mut backend, pattern) = internal(&kore, &initial);
            let definition = backend.select_definition(None).unwrap();
            for evaluation in [EvaluationMode::Execution, EvaluationMode::Proof] {
                let result = execute_with_io_state(
                    &definition,
                    pattern.clone(),
                    ExecutionOptions {
                        evaluation,
                        ..ExecutionOptions::default()
                    },
                    ExecutionIoState::new(b"AB".to_vec()),
                );
                assert_eq!(
                    leaf_marks(&result),
                    [expected],
                    "{program}, {evaluation:?}: {result:#?}"
                );
                assert_eq!(
                    format!("{result:?}").matches("ReadCount").count() > 0,
                    expected > 0,
                    "{program}, {evaluation:?}: {result:#?}"
                );
            }
        }
    }

    const EFFECTS: &str = r#"
module MAIN
  imports INT
  imports BOOL
  imports K-EQUAL
  imports K-IO
  imports STRING
  imports SET
  imports MAP
  imports LIST
  syntax Pgm ::= "pAnd" | "pOr" | "pAndThen" | "pImplies" | "pImpliesWrite" | "pRelevant"
               | "pPure" | "pEmpty" | "pIte" | "pNest" | "pFun" | "pWrite" | "pCondAnd"
               | "pCondIte" | "pAnyIte" | "pAnyFunIte" | "pAnyCond" | "pAnyCondIte"
               | "pIteOnly" | "pSet" | "pSetRev" | "pMap" | "pMapRev" | "pList" | "pListRev"
  syntax KItem ::= res(K)
  configuration <k> $PGM:Pgm </k>
  rule pAnd => (false andBool (#getc(0) ==K 65)) ~> #getc(0)
  rule pOr => (true orBool (#getc(0) ==K 65)) ~> #getc(0)
  rule pAndThen => (false andThenBool (#getc(0) ==K 65)) ~> #getc(0)
  rule pImplies => (false impliesBool (#getc(0) ==K 65)) ~> #getc(0)
  rule pImpliesWrite => (false impliesBool wrote(#write(1, "y"))) ~> #getc(0)
  rule pRelevant => (true andBool (#getc(0) ==K 65)) ~> #getc(0)
  rule pPure => (false andBool (1 ==Int 1)) ~> #getc(0)
  rule pEmpty => (false andBool wrote(#write(1, substrString("a", 0, 0)))) ~> #getc(0)
  syntax Bool ::= wrote(K) [function, total]
  rule wrote(_) => true
  rule pIte => #if true #then .K #else #write(1, "x") #fi ~> #getc(0)
  rule pNest => (false andBool (true orBool (#getc(0) ==K 65))) ~> #getc(0)
  syntax Bool ::= rd() [function]
  rule rd() => #getc(0) ==K 65
  rule pFun => (false andBool rd()) ~> #getc(0)
  rule pWrite => (false andBool wrote(#write(1, "x"))) ~> #getc(0)
  syntax Int ::= g() [function] | g3() [function]
  rule g() => 1 requires false andBool (#getc(0) ==K 65)
  rule g() => 2 [owise]
  rule pCondAnd => res(g()) ~> #getc(0)
  rule g3() => 1 requires #if true #then true #else wrote(#write(1, "x")) #fi
  rule g3() => 2 [owise]
  rule pCondIte => res(g3()) ~> #getc(0)
  syntax KItem ::= viaAny(Int)
  rule viaAny(N) => #getc(N) [anywhere]
  syntax K ::= fa() [function, total]
  rule fa() => viaAny(0)
  rule pAnyIte => #if true #then .K #else viaAny(0) #fi ~> #getc(0)
  rule pAnyFunIte => #if true #then .K #else fa() #fi ~> #getc(0)
  syntax Int ::= g4() [function] | g5() [function]
  rule g4() => 1 requires false andBool wrote(fa())
  rule g4() => 2 [owise]
  rule pAnyCond => res(g4()) ~> #getc(0)
  rule g5() => 1 requires #if true #then true #else wrote(fa()) #fi
  rule g5() => 2 [owise]
  rule pAnyCondIte => res(g5()) ~> #getc(0)
  rule pIteOnly => #if true #then .K #else #write(1, "x") #fi
  syntax KItem ::= zz(Int) | aa(Int)
  syntax Int ::= aOfSet(Set) [function] | aOfMap(Map) [function] | aOfList(List) [function]
  rule aOfSet(SetItem(aa(I)) _) => I
  rule aOfMap((aa(I) |-> _) _) => I
  rule aOfList(ListItem(aa(I)) ListItem(zz(_))) => I
  rule aOfList(ListItem(zz(_)) ListItem(aa(I))) => I
  rule pSet => aOfSet(SetItem(zz({#getc(0)}:>Int)) SetItem(aa({#getc(0)}:>Int)))
  rule pSetRev => aOfSet(SetItem(aa({#getc(0)}:>Int)) SetItem(zz({#getc(0)}:>Int)))
  rule pMap => aOfMap((zz({#getc(0)}:>Int) |-> 1) (aa({#getc(0)}:>Int) |-> 2))
  rule pMapRev => aOfMap((aa({#getc(0)}:>Int) |-> 1) (zz({#getc(0)}:>Int) |-> 2))
  rule pList => aOfList(ListItem(zz({#getc(0)}:>Int)) ListItem(aa({#getc(0)}:>Int)))
  rule pListRev => aOfList(ListItem(aa({#getc(0)}:>Int)) ListItem(zz({#getc(0)}:>Int)))
endmodule
"#;

    /// The marks of the run's one leaf and the run's list, by hook, and the code its last
    /// `#getc(0)` read; with Z3 when `z3` holds, without a solver otherwise.
    fn effect_run(program: &str, z3: bool) -> (Vec<String>, Vec<String>, Option<&'static str>) {
        effect_run_with(program, z3, true)
    }

    /// [`effect_run`], with a console (input `AB`) only when `console` holds.
    fn effect_run_with(
        program: &str,
        z3: bool,
        console: bool,
    ) -> (Vec<String>, Vec<String>, Option<&'static str>) {
        let (kore, initial) = compile(EFFECTS, program);
        let (mut backend, pattern) = internal(&kore, &initial);
        let definition = backend.select_definition(None).unwrap();
        let options = ExecutionOptions {
            evaluation: EvaluationMode::Execution,
            ..ExecutionOptions::default()
        };
        let io = ExecutionIoState::new(b"AB".to_vec());
        let result = if z3 {
            #[cfg(feature = "z3-inference")]
            {
                let solver = k_rust_backend::smt::Z3Solver::new(&definition).unwrap();
                k_rust_backend::rewrite::execute_disjunction_with_solver_and_io_state_and_observer_with_initial_status(
                    &definition,
                    vec![pattern],
                    options,
                    &solver,
                    io,
                    |_| {},
                )
                .0
            }
            #[cfg(not(feature = "z3-inference"))]
            unreachable!("no Z3 in this build")
        } else if console {
            execute_with_io_state(&definition, pattern, options, io)
        } else {
            k_rust_backend::rewrite::execute(&definition, pattern, options)
        };
        assert_eq!(result.leaves.len(), 1, "{program}: {result:#?}");
        let leaf = format!("{:?}", result.leaves[0].pattern);
        let read = ["65", "66"]
            .into_iter()
            .find(|code| leaf.contains(&format!("\"{code}\"")));
        let mut marks: Vec<String> = result.leaves[0]
            .diagnostics
            .iter()
            .filter_map(|diagnostic| {
                if let k_rust_backend::diagnostic::BackendDiagnostic::ImplementationChosenValue {
                    hook,
                    class,
                } = diagnostic
                {
                    Some(format!("{hook}/{}", class.name()))
                } else {
                    None
                }
            })
            .collect();
        marks.sort();
        let mut listed: Vec<String> = result
            .implementation_chosen_values
            .iter()
            .map(|chosen| format!("{}/{}", chosen.hook, chosen.class.name()))
            .collect();
        listed.sort();
        (marks, listed, read)
    }

    /// Whether an operand a decided connective makes irrelevant performs its console effects is
    /// the backend's choice for `andBool`, `orBool`, `impliesBool` (`notBool P orBool Q`) and
    /// `#if`, so a leaf whose console rests on the choice is marked `effect-order`, and so is the
    /// run's list. k-rust performs the right operand of `andBool`, `orBool` and `impliesBool`
    /// (the second `#getc` reads `B`, 66; `pImpliesWrite` writes `y`) and skips `#if`'s discarded
    /// one. A nested connective marks both, an operand that reaches the read through a function
    /// equation marks, and so does a non-empty `#write`. `andThenBool` skips its right operand
    /// (65), which is specified, and is unmarked. A right operand the left one does not make
    /// irrelevant, one without effects, and one whose only effect writes nothing (the console is
    /// observably unchanged) are unmarked.
    /// In a function equation's condition, which k-rust simplifies without the console, a decided
    /// `#if` leaves its discarded operand's effect unperformed (`pCondIte` writes nothing); the run
    /// has a console, so another backend may perform the effect, and the leaf is marked
    /// (`pCondAnd`, which needs the solver to decide its condition, is
    /// `a_decided_connective_in_an_equation_condition_is_marked`).
    /// An operand that reaches the read through an anywhere rule (`viaAny(0)`, and `fa()`, whose
    /// equation gives `viaAny(0)`) holds a console effect too, in a discarded `#if` branch and in
    /// a condition (`pAnyCondIte`). `viaAny` is therefore `impure`, and it is not `total`: the
    /// definedness of the discarded `viaAny(0)` (`pAnyIte`) depends on an application that is not
    /// performed, so the run stops there at the unsupported hook, marked and with nothing read;
    /// `fa()` is declared `total`, so `pAnyFunIte` goes on and reads.
    /// The operands compare the read with `==K`, which is defined whatever is read, so that the
    /// discarded `andThenBool` operand's definedness does not rest on a read that is not
    /// performed (that is the unsupported-hook outcome).
    #[test]
    fn a_console_effect_a_decided_connective_made_irrelevant_is_marked() {
        let effect_order = |hooks: &[&str]| {
            hooks
                .iter()
                .map(|hook| format!("{hook}/effect-order"))
                .collect()
        };
        let expected: [(&str, Vec<String>, Option<&str>); 16] = [
            ("pAnd", effect_order(&["BOOL.and"]), Some("66")),
            ("pOr", effect_order(&["BOOL.or"]), Some("66")),
            ("pAndThen", Vec::new(), Some("65")),
            ("pImplies", effect_order(&["BOOL.implies"]), Some("66")),
            ("pImpliesWrite", effect_order(&["BOOL.implies"]), Some("65")),
            ("pRelevant", Vec::new(), Some("66")),
            ("pPure", Vec::new(), Some("65")),
            ("pEmpty", Vec::new(), Some("65")),
            ("pIte", effect_order(&["KEQUAL.ite"]), Some("65")),
            ("pNest", effect_order(&["BOOL.and", "BOOL.or"]), Some("66")),
            ("pFun", effect_order(&["BOOL.and"]), Some("66")),
            ("pWrite", effect_order(&["BOOL.and"]), Some("65")),
            ("pCondIte", effect_order(&["KEQUAL.ite"]), Some("65")),
            ("pAnyIte", effect_order(&["KEQUAL.ite"]), None),
            ("pAnyFunIte", effect_order(&["KEQUAL.ite"]), Some("65")),
            ("pAnyCondIte", effect_order(&["KEQUAL.ite"]), Some("65")),
        ];
        // A run with one leaf lists exactly that leaf's marks.
        let expected = expected.map(|(program, marks, read)| (program, marks.clone(), marks, read));
        let found = expected.clone().map(|(program, _, _, _)| {
            let (marks, listed, read) = effect_run(program, false);
            (program, marks, listed, read)
        });
        assert_eq!(found, expected);
    }

    /// `g()` with `rule g() => 1 requires false andBool (#getc(0) ==K 65)` and
    /// `rule g() => 2 [owise]`: the condition is simplified without the console, so k-rust leaves
    /// the read unperformed, and the solver decides the condition false from the left operand
    /// (`res(2)`, and the last `#getc` reads `A`, 65). A backend that evaluates `andBool`'s right
    /// operand with its effects reads `A` there, and the last read gives 66, so the leaf is marked.
    #[cfg(feature = "z3-inference")]
    #[test]
    fn a_decided_connective_in_an_equation_condition_is_marked() {
        let marks = vec!["BOOL.and/effect-order".to_owned()];
        assert_eq!(
            effect_run("pCondAnd", true),
            (marks.clone(), marks, Some("65"))
        );
    }

    /// The anywhere form of `a_decided_connective_in_an_equation_condition_is_marked`:
    /// `g4()` with `rule g4() => 1 requires false andBool wrote(fa())`, where `fa()` reaches the
    /// read through the anywhere rule of `viaAny`, takes the `owise` equation and reads nothing.
    #[cfg(feature = "z3-inference")]
    #[test]
    fn a_decided_connective_over_an_anywhere_reached_effect_in_a_condition_is_marked() {
        let marks = vec!["BOOL.and/effect-order".to_owned()];
        assert_eq!(
            effect_run("pAnyCond", true),
            (marks.clone(), marks, Some("65"))
        );
    }

    /// Labels that reach an effect through an anywhere rule (`viaAny`, and `fa` through it), an
    /// `ensures` (`viaEns`), a macro's right side (`usesM` through `m`), a console hook not
    /// declared `impure` (`fu` through `myGetc`), and a simplification whose right side copies a
    /// matched application (`_+Int_`, through `eff(N) +Int 0 => eff(N)`); `lhsS` applies `eff`
    /// only on a simplification's left side and `clean` reaches nothing.
    const REACH: &str = r#"
module MAIN
  imports INT
  imports BOOL
  imports K-EQUAL
  imports K-IO
  syntax Pgm ::= "p"
  configuration <k> $PGM:Pgm </k>
  rule p => .K
  syntax Int ::= fa() [function] | viaEns(Int) [function] | myGetc(Int) [function, hook(IO.getc)]
               | fu() [function] | eff(Int) [function, impure] | lhsS(Int) [function]
  syntax Num ::= Int | viaAny(Int) | m(Int) [macro] | usesM() [function] | clean(Int)
  rule viaAny(N) => {#getc(N)}:>Int [anywhere]
  rule fa() => {viaAny(0)}:>Int
  rule viaEns(N) => N ensures {#getc(0)}:>Int ==Int 65
  rule m(N) => {#getc(N)}:>Int
  rule usesM() => m(0)
  rule clean(N) => N [anywhere]
  rule fu() => myGetc(0)
  rule eff(N) => N
  rule lhsS(N) => N
  rule lhsS(eff(N)) => N [simplification]
  rule eff(N) +Int 0 => eff(N) [simplification]
endmodule
"#;

    /// The frontend's `impure` attribute and the backend's load-time console-effect set are one
    /// closure from the same seeds over the same rules and rule parts, so on the compiled KORE of
    /// the FU-27 and KINK-17/4 fixtures the symbols the KORE declares `impure` are exactly the
    /// symbols the load finds.
    #[test]
    fn the_emitted_impure_attribute_equals_the_load_time_effect_set() {
        for (name, source, program) in [("REACH", REACH, "p"), ("EFFECTS", EFFECTS, "pAnd")] {
            let (kore, _) = compile(source, program);
            let parsed = k_rust::kore::parser::parse_definition(&kore).unwrap();
            let declared: BTreeSet<String> = parsed
                .modules
                .iter()
                .flat_map(|module| module.sentences.iter())
                .filter_map(|sentence| match sentence {
                    k_rust::kore::ast::Sentence::SymbolDeclaration {
                        symbol, attributes, ..
                    } if attributes.0.iter().any(|attribute| {
                        matches!(attribute, Pattern::Application { symbol, .. } if symbol.name == "impure")
                    }) =>
                    {
                        Some(symbol.name.clone())
                    }
                    _ => None,
                })
                .collect();
            let mut backend = backend(&kore);
            let loaded = backend
                .select_definition(None)
                .unwrap()
                .console_effect_symbols()
                .expect("every effectful equation has a root symbol");
            assert_eq!(declared, loaded, "{name}");
            if name == "REACH" {
                for symbol in [
                    "Lblfa'LParRParUnds'MAIN'Unds'Int",
                    "LblviaEns'LParUndsRParUnds'MAIN'Unds'Int'Unds'Int",
                    "LblmyGetc'LParUndsRParUnds'MAIN'Unds'Int'Unds'Int",
                    "Lblfu'LParRParUnds'MAIN'Unds'Int",
                    "LblviaAny'LParUndsRParUnds'MAIN'Unds'Num'Unds'Int",
                    "LblusesM'LParRParUnds'MAIN'Unds'Num",
                    "Lbl'UndsPlus'Int'Unds'",
                ] {
                    assert!(declared.contains(symbol), "{symbol}: {declared:?}");
                }
                for symbol in [
                    "LbllhsS'LParUndsRParUnds'MAIN'Unds'Int'Unds'Int",
                    "Lblclean'LParUndsRParUnds'MAIN'Unds'Num'Unds'Int",
                ] {
                    assert!(!declared.contains(symbol), "{symbol}: {declared:?}");
                }
            }
        }
    }

    /// A run without a console performs no effect, so a decided `#if` over a discarded `#write`
    /// marks nothing, on the leaf or on the run's list; with a console it is marked.
    #[test]
    fn a_run_without_a_console_marks_no_effect_order() {
        assert_eq!(
            effect_run_with("pIteOnly", false, false),
            (Vec::new(), Vec::new(), None)
        );
        let marks = vec!["KEQUAL.ite/effect-order".to_owned()];
        assert_eq!(
            effect_run_with("pIteOnly", false, true),
            (marks.clone(), marks, None)
        );
    }

    /// The items of a `Set` or `Map` literal perform their effects in k-rust's order of the item
    /// terms, whatever their source order (`aa(..)` before `zz(..)`, so `aa` reads `A`, 65);
    /// `List` items, like the arguments of an application, left to right (the second item reads
    /// `B`, 66). Nothing is marked: the order is k-rust's stated reading.
    #[test]
    fn collection_items_perform_their_effects_in_the_documented_order() {
        let found = ["pSet", "pSetRev", "pMap", "pMapRev", "pList", "pListRev"]
            .map(|program| (program, effect_run(program, false)));
        let unmarked = |read| (Vec::new(), Vec::new(), Some(read));
        assert_eq!(
            found,
            [
                ("pSet", unmarked("65")),
                ("pSetRev", unmarked("65")),
                ("pMap", unmarked("65")),
                ("pMapRev", unmarked("65")),
                ("pList", unmarked("66")),
                ("pListRev", unmarked("65")),
            ]
        );
    }
}
