//! The rule-only term syntax of module `K` (`kast.md`): the local functions `#let` and `#fun`,
//! and the pattern tests `:=K` and `:/=K`, loaded through the embedded prelude in either
//! inference build.
//!
//! These productions belong to every rule grammar. `#fun3` and `#let` are parametric in a result
//! sort and in an argument sort that occurs only in the bound pattern and the bound value, so
//! nothing but those subterms constrains it; the maximal variable typing is the one at the top
//! sort, and the loaded rule carries no label parameter. Both builds therefore load the same
//! rule, and the generated lambdas compile to the same KORE; the snapshots below are shared by
//! the two builds, so each build is checked against the same text.
//!
//! One reading is not shared: where `#fun(P => B)(A)` also reads as `#fun2` over the rewrite
//! `P => B` at a well-sorted typing, the Z3 build keeps that `prefer` reading, while the portable
//! rule grammar admits no rewrite directly at a parametric production's argument and reads it
//! as `#fun3(P, B, A)`. A `#fun2` reading is well-sorted only where its `#fun3` twin is (take both
//! of `#fun3`'s parameters at `#fun2`'s), and it is kept only at the maximal typing, which is then
//! the twin's; so the two readings have the same variable sorts and both lower to the lambda
//! `P => B` applied to `A`. The loaded label differs; the compiled definition does not.

use k_rust::{
    builtin::embedded,
    definition::Sentence,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    outer::{LoadOptions, LoadedDefinition, ResolvedSource, load_with_options},
};

fn load(name: &str, source: &str) -> LoadedDefinition {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    load_with_options(
        ResolvedSource::new(format!("{name}.k"), source),
        name,
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            excluded_module_attributes: vec![
                CompilationBackend::Rust.excluded_module_attribute().into(),
            ],
            ..LoadOptions::default()
        },
    )
    .unwrap_or_else(|error| panic!("{name} does not load: {error:?}"))
}

/// A module `P` over `op(Int)` and `val(Int)` whose only rule is `rule`.
fn probe(rule: &str) -> String {
    format!(
        "module P\n  imports INT\n  imports BOOL\n  imports K-EQUAL\n  \
         syntax Op ::= op(Int) [symbol(op)] | val(Int) [symbol(val)]\n  {rule}\nendmodule\n"
    )
}

/// Every rule of the main module as `body requires condition`.
fn loaded_rules(loaded: &LoadedDefinition) -> Vec<String> {
    loaded
        .definition()
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
            Sentence::Rule { body, requires, .. } => Some(format!("{body} requires {requires}")),
            _ => None,
        })
        .collect()
}

/// The sentences of the compiled definition that name a generated lambda: its symbol, its
/// equations and definedness axioms, and the rules that apply it.
fn lambda_kore(loaded: &LoadedDefinition) -> String {
    let compiled = compile_loaded_definition(loaded, CompileOptions::default()).unwrap();
    let mut sentences = Vec::new();
    let mut current = String::new();
    for line in compiled.definition_kore.lines() {
        let starts_sentence = line.starts_with("  ") && !line.starts_with("   ");
        if starts_sentence || line.starts_with("module ") || line == "endmodule" {
            if current.contains("lambda") {
                sentences.push(std::mem::take(&mut current));
            }
            current.clear();
        }
        if starts_sentence {
            current = format!("{line}\n");
        } else if !current.is_empty() {
            current.push_str(line);
            current.push('\n');
        }
    }
    assert!(
        !sentences.is_empty(),
        "the definition should contain a lambda"
    );
    sentences.concat()
}

/// A rule of `P` with the rule it loads as, in both builds, or, where the builds differ only in
/// reading `#fun(P => B)(A)` as `#fun2` or `#fun3`, in the Z3 and the portable build.
struct Case {
    name: &'static str,
    rule: &'static str,
    loaded: &'static str,
    portable: Option<&'static str>,
}

/// The case's rule loads as the rule its build expects, and the generated lambdas of that loaded
/// definition compile to the snapshot `probe_<name>`, which both builds share.
fn assert_case(case: &Case) {
    let loaded = load("P", &probe(case.rule));
    let expected = if cfg!(feature = "z3-inference") {
        case.loaded
    } else {
        case.portable.unwrap_or(case.loaded)
    };
    assert_eq!(loaded_rules(&loaded), [expected], "{}", case.name);
    insta::assert_snapshot!(
        format!("probe_{}", case.name),
        lambda_kore(&loaded),
        case.rule
    );
}

/// One test per case, named by the case.
macro_rules! local_function_cases {
    ($($name:ident { $($field:ident: $value:expr),* $(,)? })*) => {
        mod local_function_rules_load_and_compile_to_the_same_kore_in_both_builds {
            $(
                #[test]
                fn $name() {
                    super::assert_case(&super::Case {
                        name: stringify!($name),
                        $($field: $value),*
                    });
                }
            )*
        }
    };
}

local_function_cases! {
    let_variable {
        rule: "rule op(A) => val(#let Y = A #in Y)",
        loaded: "op(#SemanticCastToInt(A))=>val(#let(#SemanticCastToInt(Y),#SemanticCastToInt(A),#SemanticCastToInt(Y))) requires #token(\"true\",\"Bool\")",
        portable: None,
    }
    let_cast_binder {
        rule: "rule op(A) => val(#let Y:Int = A #in Y)",
        loaded: "op(#SemanticCastToInt(A))=>val(#let(#SemanticCastToInt(Y),#SemanticCastToInt(A),#SemanticCastToInt(Y))) requires #token(\"true\",\"Bool\")",
        portable: None,
    }
    let_partial_body {
        rule: "rule op(A) => val(#let Y = A #in 10 /Int Y)",
        loaded: "op(#SemanticCastToInt(A))=>val(#let(#SemanticCastToInt(Y),#SemanticCastToInt(A),`_/Int_`(#token(\"10\",\"Int\"),#SemanticCastToInt(Y)))) requires #token(\"true\",\"Bool\")",
        portable: None,
    }
    let_unconstrained_binder {
        rule: "rule op(A) => val(#let X = op(A) #in 1)",
        loaded: "op(#SemanticCastToInt(A))=>val(#let(#SemanticCastToK(X),op(#SemanticCastToInt(A)),#token(\"1\",\"Int\"))) requires #token(\"true\",\"Bool\")",
        portable: None,
    }
    let_nested {
        rule: "rule op(A) => val(#let X = A #in #let Z = X #in Z +Int X)",
        loaded: "op(#SemanticCastToInt(A))=>val(#let(#SemanticCastToInt(X),#SemanticCastToInt(A),#let(#SemanticCastToInt(Z),#SemanticCastToInt(X),`_+Int_`(#SemanticCastToInt(Z),#SemanticCastToInt(X))))) requires #token(\"true\",\"Bool\")",
        portable: None,
    }
    let_in_requires {
        rule: "rule op(A) => val(A) requires #let B = A #in B >Int 0",
        loaded: "op(#SemanticCastToInt(A))=>val(#SemanticCastToInt(A)) requires #let(#SemanticCastToInt(B),#SemanticCastToInt(A),`_>Int_`(#SemanticCastToInt(B),#token(\"0\",\"Int\")))",
        portable: None,
    }
    fun_identity {
        rule: "rule op(A) => val(#fun(Y => Y)(A))",
        loaded: "op(#SemanticCastToInt(A))=>val(#fun2(#SemanticCastToInt(Y)=>#SemanticCastToInt(Y),#SemanticCastToInt(A))) requires #token(\"true\",\"Bool\")",
        portable: Some(
            "op(#SemanticCastToInt(A))=>val(#fun3(#SemanticCastToInt(Y),#SemanticCastToInt(Y),#SemanticCastToInt(A))) requires #token(\"true\",\"Bool\")",
        ),
    }
    fun_body_under_a_function {
        rule: "rule op(A) => val(#fun(Y => Y +Int 1)(A))",
        loaded: "op(#SemanticCastToInt(A))=>val(#fun2(#SemanticCastToInt(Y)=>`_+Int_`(#SemanticCastToInt(Y),#token(\"1\",\"Int\")),#SemanticCastToInt(A))) requires #token(\"true\",\"Bool\")",
        portable: Some(
            "op(#SemanticCastToInt(A))=>val(#fun3(#SemanticCastToInt(Y),`_+Int_`(#SemanticCastToInt(Y),#token(\"1\",\"Int\")),#SemanticCastToInt(A))) requires #token(\"true\",\"Bool\")",
        ),
    }
    fun_unconstrained_pattern {
        rule: "rule op(A) => val(#fun(X => 1)(A))",
        loaded: "op(#SemanticCastToInt(A))=>val(#fun3(#SemanticCastToK(X),#token(\"1\",\"Int\"),#SemanticCastToInt(A))) requires #token(\"true\",\"Bool\")",
        portable: None,
    }
    fun_constructor_pattern {
        rule: "rule op(A) => val(#fun(op(X) => X)(op(A)))",
        loaded: "op(#SemanticCastToInt(A))=>val(#fun3(op(#SemanticCastToInt(X)),#SemanticCastToInt(X),op(#SemanticCastToInt(A)))) requires #token(\"true\",\"Bool\")",
        portable: None,
    }
    fun_nested_argument {
        rule: "rule op(A) => val(#fun(X => X)(#fun(Z => Z)(A)))",
        loaded: "op(#SemanticCastToInt(A))=>val(#fun3(#SemanticCastToInt(X),#SemanticCastToInt(X),#fun2(#SemanticCastToK(Z)=>#SemanticCastToK(Z),#SemanticCastToInt(A)))) requires #token(\"true\",\"Bool\")",
        portable: Some(
            "op(#SemanticCastToInt(A))=>val(#fun3(#SemanticCastToInt(X),#SemanticCastToInt(X),#fun3(#SemanticCastToK(Z),#SemanticCastToK(Z),#SemanticCastToInt(A)))) requires #token(\"true\",\"Bool\")",
        ),
    }
    match_k {
        rule: "rule op(A) => val(0) requires A :=K 1",
        loaded: "op(#SemanticCastToInt(A))=>val(#token(\"0\",\"Int\")) requires `_:=K_`(#SemanticCastToInt(A),#token(\"1\",\"Int\"))",
        portable: None,
    }
    mismatch_k {
        rule: "rule op(A) => val(0) requires A :/=K 1",
        loaded: "op(#SemanticCastToInt(A))=>val(#token(\"0\",\"Int\")) requires `_:/=K_`(#SemanticCastToInt(A),#token(\"1\",\"Int\"))",
        portable: None,
    }
}

/// `tests/fixtures/reference/kompile/let-list-binder`: `#let` and `#fun` binders whose bound
/// variable is also a user-list element.
#[test]
fn let_list_binder_fixture_compiles_to_the_same_kore_in_both_builds() {
    let source = include_str!("fixtures/reference/kompile/let-list-binder/test.k");
    insta::assert_snapshot!(lambda_kore(&load("LET-LIST-BINDER", source)));
}

/// A `#fun` inside the right-hand side of a rewrite nested in a map pattern, the construct of the
/// `ambiguous-rewrite` corpus case.
#[test]
fn fun_under_a_nested_rewrite_compiles_to_the_same_kore_in_both_builds() {
    let source = r#"module AMB
  imports INT
  imports MAP
  syntax Type ::= "type"
  syntax Foo ::= foo(Map)
  rule foo(1 |-> 0 => 1 |-> #fun(T::Type => T |-> T)(type))
endmodule
"#;
    insta::assert_snapshot!(lambda_kore(&load("AMB", source)));
}

/// A `#fun` in a configuration-dependent function rule over a user list, the construct of the
/// `fun-int-list-config` corpus fixture.
#[test]
fn fun_in_a_configuration_dependent_rule_compiles_to_the_same_kore_in_both_builds() {
    let source = r#"module FUN-CONFIG
  imports INT
  imports MAP
  configuration
    <k> $PGM:KItem </k>
    <cell> .Map </cell>
  syntax IntList ::= List{Int, ""}
  syntax Int ::= funIntListAndConfig() [function]
  rule [[ funIntListAndConfig() => #fun(_V1 => 0)(.IntList) ]]
    <cell> M </cell>
endmodule
"#;
    insta::assert_snapshot!(lambda_kore(&load("FUN-CONFIG", source)));
}

fn lambda_declarations(loaded: &LoadedDefinition) -> Vec<String> {
    let compiled = compile_loaded_definition(loaded, CompileOptions::default()).unwrap();
    let definition = k_rust::kore::parser::parse_definition(&compiled.definition_kore).unwrap();
    definition
        .modules
        .into_iter()
        .flat_map(|module| module.sentences)
        .filter(|sentence| {
            matches!(sentence, k_rust::kore::ast::Sentence::SymbolDeclaration { symbol, .. }
            if symbol.name.starts_with("Lbl'Hash'lambda"))
        })
        .map(|sentence| k_rust::kore::printer::Printer::pretty(1000).print_sentence(&sentence))
        .collect()
}

#[test]
fn lambda_over_total_initializer_is_total() {
    let loaded = load(
        "MN5",
        r#"
module MN5
  imports INT
  syntax KItem ::= use(Int) [function, symbol(use)] | wrap(NCell) [symbol(wrap)]
  configuration <n> 0 </n>
  rule use(A) => wrap(#fun(X:Int => initNCell)(A))
endmodule
"#,
    );
    let sentences = lambda_declarations(&loaded);
    let declaration = sentences
        .iter()
        .find(|sentence| sentence.trim_start().starts_with("symbol "))
        .unwrap();
    assert!(declaration.contains("total{}()"), "{declaration}");
}

#[test]
fn nested_lambdas_share_initializer_evidence() {
    let loaded = load(
        "MN5",
        r#"
module MN5
  imports INT
  syntax KItem ::= use(Int) [function, symbol(use)] | wrap(NCell) [symbol(wrap)]
  configuration <n> 0 </n>
  rule use(A) => wrap(#fun(X:Int => #fun(Y:Int => initNCell)(X))(A))
endmodule
"#,
    );
    let sentences = lambda_declarations(&loaded);
    let declarations = sentences
        .iter()
        .filter(|sentence| sentence.trim_start().starts_with("symbol "))
        .collect::<Vec<_>>();
    assert_eq!(declarations.len(), 2, "{sentences:?}");
    for declaration in declarations {
        assert!(declaration.contains("total{}()"), "{declaration}");
    }
}

#[test]
fn deferred_lambdas_require_defined_content_and_covering_patterns() {
    for (content, pattern) in [("bad(0)", "X:Int"), ("0", "0")] {
        let loaded = load(
            "MN5",
            &format!(
                r#"
module MN5
  imports INT
  syntax Int ::= bad(Int) [function, symbol(bad)]
  syntax KItem ::= use(Int) [function, symbol(use)] | wrap(NCell) [symbol(wrap)]
  configuration <n> {content} </n>
  rule bad(I) => I /Int 0
  rule use(A) => wrap(#fun({pattern} => initNCell)(A))
endmodule
"#
            ),
        );
        let sentences = lambda_declarations(&loaded);
        let declaration = sentences
            .iter()
            .find(|sentence| sentence.trim_start().starts_with("symbol "))
            .unwrap();
        assert!(!declaration.contains("total{}()"), "{declaration}");
    }
}

#[test]
fn lambda_over_initializer_with_narrower_pattern_is_not_total() {
    let loaded = load(
        "NARROW",
        r#"
module NARROW
  imports INT
  syntax KItem ::= use(K) [function, symbol(use)] | wrap(NCell) [symbol(wrap)]
  configuration <n> 0 </n>
  rule use(A) => wrap(#fun(X:Int => initNCell)(A))
endmodule
"#,
    );
    let declarations = lambda_declarations(&loaded);
    assert_eq!(declarations.len(), 1, "{declarations:?}");
    assert!(declarations[0].contains("(SortK{})"), "{declarations:?}");
    assert!(
        !declarations[0].contains("total{}()"),
        "{}",
        declarations[0]
    );
}

#[test]
fn lambda_with_constant_body_and_narrower_pattern_is_not_total() {
    let loaded = load(
        "NARROW",
        r#"
module NARROW
  imports INT
  syntax KItem ::= use(K) [function, symbol(use)] | wrap(Int) [symbol(wrap)]
  rule use(A) => wrap(#fun(X:Int => 0)(A))
endmodule
"#,
    );
    let declarations = lambda_declarations(&loaded);
    assert_eq!(declarations.len(), 1, "{declarations:?}");
    assert!(declarations[0].contains("(SortK{})"), "{declarations:?}");
    assert!(
        !declarations[0].contains("total{}()"),
        "{}",
        declarations[0]
    );
}

#[test]
fn lambda_over_initializer_with_nested_cast_is_not_total() {
    let loaded = load(
        "NARROW",
        r#"
module NARROW
  imports INT
  syntax KItem ::= use(KItem) [function, symbol(use)] | wrap(NCell) [symbol(wrap)]
  configuration <n> 0 </n>
  rule use(A) => wrap(#fun((X:Int):KItem => initNCell)(A))
endmodule
"#,
    );
    let declarations = lambda_declarations(&loaded);
    assert_eq!(declarations.len(), 1, "{declarations:?}");
    assert!(
        declarations[0].contains("(SortKItem{})"),
        "{declarations:?}"
    );
    assert!(
        !declarations[0].contains("total{}()"),
        "{}",
        declarations[0]
    );
}

#[test]
fn lambda_with_constant_body_and_nested_cast_is_not_total() {
    let loaded = load(
        "NARROW",
        r#"
module NARROW
  imports INT
  syntax KItem ::= use(KItem) [function, symbol(use)] | wrap(Int) [symbol(wrap)]
  rule use(A) => wrap(#fun((X:Int):KItem => 0)(A))
endmodule
"#,
    );
    let declarations = lambda_declarations(&loaded);
    assert_eq!(declarations.len(), 1, "{declarations:?}");
    assert!(
        declarations[0].contains("(SortKItem{})"),
        "{declarations:?}"
    );
    assert!(
        !declarations[0].contains("total{}()"),
        "{}",
        declarations[0]
    );
}

#[test]
fn lambda_with_inferred_narrower_variable_is_not_total() {
    let loaded = load(
        "NARROW",
        r#"
module NARROW
  imports INT
  syntax KItem ::= use(KItem) [function, symbol(use)] | wrap(Int) [symbol(wrap)]
  rule use(A) => wrap(#fun(X:KItem => X +Int 1)(A))
endmodule
"#,
    );
    let declarations = lambda_declarations(&loaded);
    assert_eq!(declarations.len(), 1, "{declarations:?}");
    assert!(
        declarations[0].contains("(SortKItem{})"),
        "{declarations:?}"
    );
    assert!(
        !declarations[0].contains("total{}()"),
        "{}",
        declarations[0]
    );
}

#[test]
fn lambda_over_initializer_with_inferred_narrower_variable_is_not_total() {
    let loaded = load(
        "NARROW",
        r#"
module NARROW
  imports INT
  syntax KItem ::= use(KItem) [function, symbol(use)] | p(Int, NCell) [symbol(p)]
  configuration <n> 0 </n>
  rule use(A) => #fun(X:KItem => p(X, initNCell))(A)
endmodule
"#,
    );
    let declarations = lambda_declarations(&loaded);
    assert_eq!(declarations.len(), 1, "{declarations:?}");
    assert!(
        declarations[0].contains("(SortKItem{})"),
        "{declarations:?}"
    );
    assert!(
        !declarations[0].contains("total{}()"),
        "{}",
        declarations[0]
    );
}
