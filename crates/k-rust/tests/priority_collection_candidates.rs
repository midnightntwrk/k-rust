//! A rule blocks the lower priorities on every instance it applies to, through any of its
//! matches.
//!
//! `pick` matches `go(SetItem(X) SetItem(Y))` twice, binding its element to `X` or to `Y`, so it
//! applies exactly where `X > 0` or `Y > 0`. `low` may therefore take only the instances where
//! `X <= 0` and `Y <= 0`; an instance with `X <= 0` and `Y > 0` is `pick`'s through its second
//! match, and its successor is `done` under either strategy (the ground run of `go(-1, 1)`
//! agrees). Strategy `any` follows one match of `pick`, but the instances the other match
//! covers are still blocked from `low`.

use k_rust::{
    backend::{
        Backend, BackendOptions, ExecuteRequest, ExecutionLeaf, ExecutionResult, ExecutionStrategy,
        HaltReasonOutput, PatternRequest, ResultModalityOutput,
    },
    builtin::embedded,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    kore::{codec, parser::parse_pattern, printer::Printer},
    outer::{LoadOptions, ResolvedSource, load_with_options},
};

const SOURCE: &str = r#"module PICK-SYNTAX
  imports INT-SYNTAX
  imports SET
  syntax Prog ::= go(Set) [symbol(go)]
                | "done" [symbol(done)]
                | "other" [symbol(other)]
endmodule

module PICK
  imports PICK-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports SET
  configuration <k> $PGM:Prog </k>

  rule [pick]: <k> go(SetItem(X:Int) _:Set) => done </k> requires X >Int 0 [priority(10)]
  rule [low]:  <k> go(_) => other </k> [priority(50)]
endmodule
"#;

fn compile(source: &str) -> String {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("pick.k", source),
        "PICK",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            excluded_module_attributes: vec![
                CompilationBackend::Rust.excluded_module_attribute().into(),
            ],
            ..LoadOptions::default()
        },
    )
    .unwrap();
    compile_loaded_definition(&loaded, CompileOptions::default())
        .unwrap()
        .definition_kore
}

fn element(value: &str) -> String {
    format!("LblSetItem{{}}(inj{{SortInt{{}}, SortKItem{{}}}}({value}))")
}

fn program(first: &str, second: &str) -> String {
    format!(
        "Lblgo{{}}(Lbl'Unds'Set'Unds'{{}}({}, {}))",
        element(first),
        element(second)
    )
}

fn request(program: &str, strategy: ExecutionStrategy) -> ExecuteRequest {
    let top = format!(
        "Lbl'-LT-'generatedTop'-GT-'{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}(inj{{SortProg{{}}, SortKItem{{}}}}({program}), dotk{{}}())), Lbl'-LT-'generatedCounter'-GT-'{{}}(\\dv{{SortInt{{}}}}(\"0\")))"
    );
    let mut request = ExecuteRequest {
        result_modality: ResultModalityOutput::PathSet,
        ..ExecuteRequest::new(parse_pattern(&top).unwrap())
    };
    request.strategy = strategy;
    request
}

fn text(leaf: &ExecutionLeaf) -> String {
    Printer::compact().print_pattern(&codec::from_value(&leaf.state).unwrap())
}

fn summary(result: &ExecutionResult) -> Vec<(HaltReasonOutput, u64, String)> {
    result
        .leaves
        .iter()
        .map(|leaf| (leaf.reason, leaf.depth, text(leaf)))
        .collect()
}

fn positive(variable: &str) -> String {
    format!(
        "\\equals{{SortBool{{}}, SortGeneratedTopCell{{}}}}(\\dv{{SortBool{{}}}}(\"true\"), Lbl'Unds-GT-'Int'Unds'{{}}({variable}:SortInt{{}}, \\dv{{SortInt{{}}}}(\"0\")))"
    )
}

fn not_positive(variable: &str) -> String {
    format!("\\not{{SortGeneratedTopCell{{}}}}({})", positive(variable))
}

/// The solver's verdict on the instances of `leaf` that also satisfy every `condition`.
fn verdict(backend: &mut Backend, leaf: &ExecutionLeaf, conditions: &[String]) -> String {
    let pattern = conditions.iter().fold(text(leaf), |pattern, condition| {
        format!("\\and{{SortGeneratedTopCell{{}}}}({pattern}, {condition})")
    });
    backend
        .get_model(PatternRequest::new(parse_pattern(&pattern).unwrap()))
        .unwrap()
        .satisfiable
}

fn backend() -> Backend {
    Backend::new(&compile(SOURCE), "PICK", BackendOptions::default()).unwrap()
}

/// The leaves of `go(X, Y)` under `strategy` whose state is a successor of the step.
fn symbolic_successors(backend: &mut Backend, strategy: ExecutionStrategy) -> Vec<ExecutionLeaf> {
    let result = backend
        .execute(request(&program("X:SortInt{}", "Y:SortInt{}"), strategy))
        .unwrap();
    // `X = Y` makes the set undefined: that instance has no successor.
    assert!(
        result.leaves.iter().all(
            |leaf| leaf.reason == HaltReasonOutput::Stuck && leaf.depth == 1
                || leaf.reason == HaltReasonOutput::Trivial && leaf.depth == 0
        ),
        "{strategy:?}: {:#?}",
        summary(&result)
    );
    result
        .leaves
        .into_iter()
        .filter(|leaf| leaf.depth == 1)
        .collect()
}

/// No `other` successor has an instance where `pick` applies, and every instance where `pick`
/// applies only through its match on `Y` has a `done` successor.
fn assert_priority_respected(backend: &mut Backend, strategy: ExecutionStrategy) {
    assert!(backend.capabilities().smt, "the checks below need a solver");
    let leaves = symbolic_successors(backend, strategy);
    let mut covered = false;
    for leaf in &leaves {
        let state = text(leaf);
        let second_match_only = verdict(backend, leaf, &[not_positive("X"), positive("Y")]);
        if state.contains("Lblother{}()") {
            for variable in ["X", "Y"] {
                assert_eq!(
                    verdict(backend, leaf, &[positive(variable)]),
                    "unsat",
                    "{strategy:?}: `low` took an instance with {variable} > 0, where `pick` \
                     applies: {state}"
                );
            }
        } else {
            assert!(state.contains("Lbldone{}()"), "{strategy:?}: {state}");
            covered |= second_match_only == "sat";
        }
    }
    assert!(
        covered,
        "{strategy:?}: no `done` successor for X <= 0 and Y > 0: {:#?}",
        leaves.iter().map(text).collect::<Vec<_>>()
    );
}

/// A ground instance where `pick` applies only through one match reaches `done` under both
/// strategies, whichever element the set stores first.
#[test]
fn a_ground_instance_follows_the_match_that_applies() {
    let mut backend = backend();
    for strategy in [ExecutionStrategy::All, ExecutionStrategy::Any] {
        for (first, second) in [("-1", "1"), ("1", "-1")] {
            let ground = backend
                .execute(request(
                    &program(
                        &format!("\\dv{{SortInt{{}}}}(\"{first}\")"),
                        &format!("\\dv{{SortInt{{}}}}(\"{second}\")"),
                    ),
                    strategy,
                ))
                .unwrap();
            let [leaf] = &ground.leaves[..] else {
                panic!("{strategy:?}: one leaf: {:#?}", summary(&ground));
            };
            assert_eq!(leaf.reason, HaltReasonOutput::Stuck);
            assert!(
                text(leaf).contains("Lbldone{}()"),
                "{strategy:?}: {:#?}",
                summary(&ground)
            );
        }
    }
}

#[test]
#[cfg_attr(
    not(feature = "z3-inference"),
    ignore = "comparing the leaves' conditions needs a solver"
)]
fn every_match_of_a_higher_rule_blocks_the_lower_priority_under_strategy_all() {
    assert_priority_respected(&mut backend(), ExecutionStrategy::All);
}

#[test]
#[cfg_attr(
    not(feature = "z3-inference"),
    ignore = "comparing the leaves' conditions needs a solver"
)]
fn every_match_of_a_higher_rule_blocks_the_lower_priority_under_strategy_any() {
    assert_priority_respected(&mut backend(), ExecutionStrategy::Any);
}

/// `pick` applies to `0` but its result `10 /Int 0` is undefined there, so the instance goes to
/// the next match, whose result is defined.
const UNDEFINED_FIRST: &str = r#"module PICK-SYNTAX
  imports INT-SYNTAX
  imports SET
  syntax Prog ::= go(Set) [symbol(go)]
                | "other" [symbol(other)]
                | res(Int) [symbol(res)]
endmodule

module PICK
  imports PICK-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports SET
  configuration <k> $PGM:Prog </k>

  rule [pick]: <k> go(SetItem(X:Int) _:Set) => res(10 /Int X) </k> requires X >=Int 0 [priority(10)]
  rule [low]:  <k> go(_) => other </k> [priority(50)]
endmodule
"#;

/// A ground instance where one match of `pick` has an undefined result follows another match
/// whose result is defined, and is undefined (`trivial`, never `low`'s) when no match has one.
#[test]
fn a_ground_instance_skips_a_match_whose_result_is_undefined() {
    let mut backend =
        Backend::new(&compile(UNDEFINED_FIRST), "PICK", BackendOptions::default()).unwrap();
    let ground = |value: &str| format!("\\dv{{SortInt{{}}}}(\"{value}\")");
    for strategy in [ExecutionStrategy::All, ExecutionStrategy::Any] {
        for (first, second) in [("0", "5"), ("5", "0")] {
            let result = backend
                .execute(request(&program(&ground(first), &ground(second)), strategy))
                .unwrap();
            let [leaf] = &result.leaves[..] else {
                panic!("{strategy:?}: one leaf: {:#?}", summary(&result));
            };
            assert_eq!(leaf.reason, HaltReasonOutput::Stuck, "{strategy:?}");
            assert!(
                text(leaf).contains(r#"Lblres{}(\dv{SortInt{}}("2"))"#),
                "{strategy:?}: {:#?}",
                summary(&result)
            );
        }
        let result = backend
            .execute(request(&program(&ground("0"), &ground("-1")), strategy))
            .unwrap();
        let [leaf] = &result.leaves[..] else {
            panic!("{strategy:?}: one leaf: {:#?}", summary(&result));
        };
        assert_eq!(leaf.reason, HaltReasonOutput::Trivial, "{strategy:?}");
    }
}
