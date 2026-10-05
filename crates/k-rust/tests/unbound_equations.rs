//! A K function rule whose right-hand side has a variable its left-hand side does not bind.
//!
//! `rule f(X) => Y requires Y ==Int X +Int 1` compiles to the equation
//! `f(X) = Y requires Y = X + 1`, closed over `X` and `Y`: it is consistent and says
//! `f(X) = X + 1`. Matching `f(X)` fixes no value for `Y`, so the backend does not use an
//! instance of it, but it loads the definition: programs that never call `f` run, and a call is
//! kept as it is rather than replaced by a term carrying the equation's own `Y`, even where the
//! `requires` holds for every `Y`. An `owise` rule of the same function applies only where the
//! equation's `requires` is refuted.

use k_rust::{
    backend::{
        Backend, BackendDiagnosticOutput, BackendOptions, ConditionIndeterminacyOutput,
        ExecuteRequest, ExecutionLeaf, ResultModalityOutput, RuleVariableOutput,
    },
    builtin::embedded,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    kore::{codec, parser::parse_pattern, printer::Printer},
    outer::{LoadOptions, ResolvedSource, load_with_options},
};

const SOURCE: &str = r#"module UNBOUND-SYNTAX
  imports INT-SYNTAX
  syntax Int ::= f(Int) [function, symbol(f)]
               | g(Int) [function, symbol(g)]
               | h(Int) [function, symbol(h)]
  syntax Prog ::= run(Int) [symbol(run)]
                | done(Int) [symbol(done)]
endmodule

module UNBOUND
  imports UNBOUND-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  configuration <k> .K </k>
  rule f(X) => Y requires Y ==Int X +Int 1
  rule g(X) => Y requires Y ==Int X +Int 1 andBool X >Int 0
  rule g(_) => 0 [owise]
  rule h(X) => Y requires X >Int 0 andBool Y ==Int Y
  rule <k> run(I) => done(I) </k>
endmodule
"#;

fn backend() -> Backend {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("unbound.k", SOURCE),
        "UNBOUND",
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
    let compiled = compile_loaded_definition(&loaded, CompileOptions::default())
        .expect("the function rule compiles");
    Backend::new(
        &compiled.definition_kore,
        "UNBOUND",
        BackendOptions::default(),
    )
    .expect("a definition with such an equation loads")
}

fn int(value: i64) -> String {
    format!("\\dv{{SortInt{{}}}}(\"{value}\")")
}

/// The leaves of running `run(argument)` from the top configuration, as compact KORE.
fn run(backend: &mut Backend, argument: &str) -> Vec<String> {
    run_leaves(backend, argument)
        .iter()
        .map(|leaf: &ExecutionLeaf| {
            Printer::compact().print_pattern(&codec::from_value(&leaf.state).unwrap())
        })
        .collect()
}

/// The leaves of running `run(argument)` from the top configuration.
fn run_leaves(backend: &mut Backend, argument: &str) -> Vec<ExecutionLeaf> {
    let top = format!(
        "Lbl'-LT-'generatedTop'-GT-'{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}(inj{{SortProg{{}}, SortKItem{{}}}}(Lblrun{{}}({argument})), dotk{{}}())), Lbl'-LT-'generatedCounter'-GT-'{{}}(\\dv{{SortInt{{}}}}(\"0\")))"
    );
    let state = parse_pattern(&top).unwrap();
    backend
        .execute(ExecuteRequest {
            result_modality: ResultModalityOutput::PathSet,
            max_depth: Some(4),
            ..ExecuteRequest::new(state)
        })
        .unwrap()
        .leaves
}

/// The diagnostics of `leaf` that report an equation instance left unused because its result
/// has variables its left-hand side does not bind: the variables, and the equation variables its
/// predicates name.
fn unbound_reports(leaf: &ExecutionLeaf) -> Vec<(Vec<String>, Vec<RuleVariableOutput>)> {
    leaf.diagnostics
        .iter()
        .filter_map(|diagnostic| match diagnostic {
            BackendDiagnosticOutput::UndecidedCondition {
                reason: ConditionIndeterminacyOutput::UnboundResultVariables { variables },
                rule_variables,
                ..
            } => Some((variables.clone(), rule_variables.clone())),
            _ => None,
        })
        .collect()
}

fn done(argument: &str) -> String {
    format!("Lbldone{{}}({argument})")
}

/// No leaf names a variable of the equation.
fn assert_no_equation_variable(leaves: &[String]) {
    for leaf in leaves {
        assert!(!leaf.contains("VarY") && !leaf.contains("Eq-h"), "{leaf}");
    }
}

#[test]
fn a_definition_with_an_unbound_result_variable_runs_and_keeps_the_call() {
    let mut backend = backend();

    // A program that never calls `f` runs to its end.
    let leaves = run(&mut backend, &int(7));
    assert!(
        matches!(&leaves[..], [leaf] if leaf.contains(&done(&int(7)))),
        "{leaves:?}"
    );

    // A call of `f` is kept in every leaf: no instance of its equation is used, and no variable
    // of the equation reaches a leaf. `f` is partial, so the step that binds `f(3)` to the
    // rule's variable depends on the definedness of `f(3)`: with a solver it also leaves the
    // remainder where `f(3)` is undefined, and without one it does not step.
    let call = format!("Lblf{{}}({})", int(3));
    let leaves = run(&mut backend, &call);
    assert!(
        !leaves.is_empty() && leaves.iter().all(|leaf| leaf.contains(&call)),
        "{leaves:?}"
    );
    assert!(
        leaves.iter().all(|leaf| !leaf.contains(&int(4))),
        "{leaves:?}"
    );
    assert_no_equation_variable(&leaves);

    // Each leaf that keeps the call says why: the diagnostic names the unbound `Y`, and its
    // requires `Y = 4` names the equation's `Y` by its printed and its definition name.
    for leaf in run_leaves(&mut backend, &call) {
        assert_eq!(
            unbound_reports(&leaf),
            [(
                vec!["VarY".to_owned()],
                vec![RuleVariableOutput {
                    name: "Eq-hVarY".into(),
                    definition_name: "VarY".into(),
                }],
            )],
            "{:?}",
            leaf.diagnostics
        );
    }
    // A program that never calls `f` has nothing to explain.
    for leaf in run_leaves(&mut backend, &int(7)) {
        assert!(unbound_reports(&leaf).is_empty(), "{:?}", leaf.diagnostics);
    }

    // Where the equation's `requires` is not refuted, the `owise` rule, which would give `g(3)`
    // the value 0 that the equation contradicts, is not used either.
    let call = format!("Lblg{{}}({})", int(3));
    let leaves = run(&mut backend, &call);
    assert!(
        !leaves.is_empty() && leaves.iter().all(|leaf| leaf.contains(&call)),
        "{leaves:?}"
    );
    assert!(
        leaves.iter().all(|leaf| !leaf.contains(&done(&int(0)))),
        "{leaves:?}"
    );
    assert_no_equation_variable(&leaves);

    // A `requires` that holds for every value of the variable does not make the instance usable
    // either: `h(X) = Y requires X > 0 and Y = Y` says that `h(3)` equals every integer.
    let call = format!("Lblh{{}}({})", int(3));
    let leaves = run(&mut backend, &call);
    assert!(
        !leaves.is_empty() && leaves.iter().all(|leaf| leaf.contains(&call)),
        "{leaves:?}"
    );
    assert_no_equation_variable(&leaves);

    // Where it is refuted, the equation says nothing about `g(-1)` and the `owise` rule applies.
    let argument = format!("Lblg{{}}({})", int(-1));
    let leaves = run(&mut backend, &argument);
    assert!(
        matches!(&leaves[..], [leaf] if leaf.contains(&done(&int(0)))),
        "{leaves:?}"
    );
    for leaf in run_leaves(&mut backend, &argument) {
        assert!(unbound_reports(&leaf).is_empty(), "{:?}", leaf.diagnostics);
    }
}
