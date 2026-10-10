#![cfg(feature = "z3-inference")]

use std::collections::BTreeSet;
use std::sync::Arc;

use k_rust::builtin::embedded;
use k_rust::definition::{
    Attributes, Definition, LOCATION_ATTRIBUTE, Location, ResolvedDefinition, SOURCE_ATTRIBUTE,
    SOURCE_ID_ATTRIBUTE,
};
use k_rust::inner::{RuleError, definition_with_named_projections};
use k_rust::kompile::{
    CompilationBackend, CompileOptions, CompileSearchPatternError, CompiledSearchPattern,
    GroundCause, GroundInput, KoreVariableIdentity, SortInjectionError, UndeterminedCause,
    UndeterminedSite, compile_loaded_definition, compile_search_pattern,
};
use k_rust::kore::ast::Pattern;
use k_rust::kore::parser::{parse_definition, parse_pattern};
use k_rust::outer::{LoadOptions, ResolvedSource, load_with_options};
use k_rust_backend::definition::BackendDefinition;

#[path = "support/shared.rs"]
mod shared;

const DEFINITION: &str = include_str!("fixtures/search-pattern/pattern.k");
const GROUND: &str = include_str!("fixtures/search-pattern/ground.pattern");
const MACRO_ROOTS: &str = include_str!("fixtures/search-pattern/macro-roots.pattern");
const MACRO_ROOTS_COLLISION_FREE: &str =
    include_str!("fixtures/search-pattern/macro-roots-collision-free.pattern");
const REFERENCE_MACRO_ROOTS: &str =
    include_str!("fixtures/search-pattern/reference-macro-roots.kore");
const REFERENCE_MACRO_ROOTS_COLLISION_FREE: &str =
    include_str!("fixtures/search-pattern/reference-macro-roots-collision-free.kore");
const REFERENCE_GROUND: &str = include_str!("fixtures/search-pattern/reference-ground.kore");
const ROOT_SORTED_OR: &str = include_str!("fixtures/search-pattern/root-sorted-or.pattern");
const REFERENCE_ROOT_SORTED_OR: &str =
    include_str!("fixtures/search-pattern/reference-root-sorted-or.kore");
const REFERENCE_EXPLICIT_GEN_BINDER: &str =
    include_str!("fixtures/search-pattern/reference-explicit-gen-binder.kore");
const EXPLICIT_GEN_BINDER: &str =
    include_str!("fixtures/search-pattern/explicit-gen-binder.pattern");
const SEARCH8: &str = include_str!("fixtures/search-pattern/search8.k");
const PATTERN_SOURCE: &str = "<command line>";
const PATTERN_LOCATION: Location = Location {
    start_line: 7,
    start_column: 3,
    end_line: 7,
    end_column: 31,
};

struct Context {
    parsing: Definition,
    execution: Definition,
    definition_kore: String,
}

fn load_context(path: &str, source: &str, main_module: &str) -> Context {
    let prelude = embedded("prelude.md").expect("embedded prelude should exist");
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new(path, source),
        main_module,
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![prelude],
            excluded_module_attributes: vec![
                CompilationBackend::Rust.excluded_module_attribute().into(),
            ],
            ..LoadOptions::default()
        },
    )
    .expect("search-pattern fixture should load");
    let parsing = definition_with_named_projections(loaded.definition());
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default())
        .expect("search-pattern fixture should compile");
    Context {
        parsing,
        execution: artifacts.execution_definition,
        definition_kore: artifacts.definition_kore,
    }
}

/// The context of `DEFINITION`, loaded once per process and inference mode and shared by the
/// tests, which only read it.
fn context() -> Arc<Context> {
    static CONTEXT: shared::Shared<Context> = shared::Shared::new();
    CONTEXT.get(|| load_context("search-pattern/pattern.k", DEFINITION, "MAIN"))
}

/// A definition whose `size` label is phantom in its sort parameter `S`.
const PHANTOM: &str = r#"requires "domains.md"
module MAIN
  imports INT
  syntax {S} Int ::= size() [function, total, symbol(size)]
  configuration <k> $PGM:Int </k>
endmodule
"#;

/// The context of `PHANTOM`, shared as [`context`] is.
fn phantom_context() -> Arc<Context> {
    static CONTEXT: shared::Shared<Context> = shared::Shared::new();
    CONTEXT.get(|| load_context("search-pattern/phantom.k", PHANTOM, "MAIN"))
}

fn compile(contents: &str) -> Result<CompiledSearchPattern, CompileSearchPatternError> {
    compile_in(&context(), "MAIN", contents)
}

fn compile_in(
    context: &Context,
    module: &str,
    contents: &str,
) -> Result<CompiledSearchPattern, CompileSearchPatternError> {
    let parsing = ResolvedDefinition::resolve(&context.parsing).unwrap();
    let execution = ResolvedDefinition::resolve(&context.execution).unwrap();
    let mut attributes = Attributes::default();
    attributes.insert(SOURCE_ATTRIBUTE, serde_json::json!(PATTERN_SOURCE));
    attributes.insert(SOURCE_ID_ATTRIBUTE, serde_json::json!(23));
    attributes.insert(LOCATION_ATTRIBUTE, serde_json::json!([7, 3, 7, 31]));
    attributes.insert("contentStartOffset", serde_json::json!(101));
    attributes.insert("contentStartLine", serde_json::json!(7));
    attributes.insert("contentStartColumn", serde_json::json!(3));
    compile_search_pattern(&parsing, &execution, module, contents.trim(), attributes)
}

fn walk(pattern: &Pattern, visit: &mut impl FnMut(&Pattern)) {
    visit(pattern);
    match pattern {
        Pattern::Application { arguments, .. }
        | Pattern::And { arguments, .. }
        | Pattern::Or { arguments, .. }
        | Pattern::AssociativeApplication { arguments, .. } => {
            for argument in arguments {
                walk(argument, visit);
            }
        }
        Pattern::Not { argument, .. }
        | Pattern::Next { argument, .. }
        | Pattern::Ceil { argument, .. }
        | Pattern::Floor { argument, .. } => walk(argument, visit),
        Pattern::Implies { left, right, .. }
        | Pattern::Iff { left, right, .. }
        | Pattern::Rewrites { left, right, .. }
        | Pattern::Equals { left, right, .. }
        | Pattern::In { left, right, .. } => {
            walk(left, visit);
            walk(right, visit);
        }
        Pattern::Exists { body, .. }
        | Pattern::Forall { body, .. }
        | Pattern::Mu { body, .. }
        | Pattern::Nu { body, .. } => walk(body, visit),
        Pattern::String(_)
        | Pattern::Variable(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::DomainValue { .. } => {}
    }
}

fn variable_names(pattern: &Pattern) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    walk(pattern, &mut |pattern| {
        if let Pattern::Variable(variable) = pattern {
            names.insert(variable.name.clone());
        }
    });
    names
}

fn pair_variable_names(pattern: &Pattern) -> (String, String) {
    let mut result = None;
    walk(pattern, &mut |pattern| {
        if let Pattern::Application { symbol, arguments } = pattern
            && symbol.name == "Lblpair"
        {
            let [Pattern::Variable(first), Pattern::Variable(second)] = arguments.as_slice() else {
                panic!("expected direct variable pair arguments: {arguments:#?}")
            };
            result = Some((first.name.clone(), second.name.clone()));
        }
    });
    result.expect("compiled pattern should contain pair")
}

#[test]
fn search_pattern_compilation_macro_roots_share_one_expander() {
    let compiled = compile(MACRO_ROOTS).unwrap();
    assert_eq!(
        compiled.generated_anonymous_variables,
        BTreeSet::from([
            KoreVariableIdentity::element("Var'Unds'DotVar0"),
            KoreVariableIdentity::element("Var'Unds'Gen1"),
            KoreVariableIdentity::element("Var'Unds'Gen2"),
        ])
    );
    let generated_names = compiled
        .generated_anonymous_variables
        .iter()
        .map(|identity| identity.name.clone())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        generated_names
            .iter()
            .filter(|name| name.contains("Gen"))
            .count(),
        2
    );
    assert_eq!(
        generated_names
            .iter()
            .filter(|name| name.contains("DotVar"))
            .count(),
        1
    );
    assert!(generated_names.is_subset(&variable_names(&compiled.pattern)));

    let (generated, authored) = pair_variable_names(&compiled.pattern);
    assert_ne!(generated, authored);
    assert_eq!(authored, "Var'Unds'Gen0");
    assert!(
        compiled
            .generated_anonymous_variables
            .contains(&KoreVariableIdentity::element(generated))
    );
}

#[test]
fn search_pattern_compilation_collision_free_macro_roots_are_distinct() {
    let compiled = compile(MACRO_ROOTS_COLLISION_FREE).unwrap();
    assert_eq!(
        compiled.generated_anonymous_variables,
        BTreeSet::from([
            KoreVariableIdentity::element("Var'Unds'DotVar0"),
            KoreVariableIdentity::element("Var'Unds'Gen0"),
            KoreVariableIdentity::element("Var'Unds'Gen1"),
        ])
    );

    let (generated, authored) = pair_variable_names(&compiled.pattern);
    assert_ne!(generated, authored);
    assert_eq!(authored, "VarZ");
    assert!(
        compiled
            .generated_anonymous_variables
            .contains(&KoreVariableIdentity::element(generated))
    );
}

#[test]
fn pinned_macro_collision_is_an_expected_semantic_divergence() {
    // Pinned K does not seed its standalone macro allocator from the authored roots. Its first
    // generated _Gen0 therefore captures the authored _Gen0. Rust deliberately reserves every
    // authored name and keeps the two equality classes distinct.
    let reference = parse_pattern(REFERENCE_MACRO_ROOTS.trim()).unwrap();
    let rust = compile(MACRO_ROOTS).unwrap().pattern;
    let (reference_generated, reference_authored) = pair_variable_names(&reference);
    let (rust_generated, rust_authored) = pair_variable_names(&rust);

    assert_eq!(reference_generated, reference_authored);
    assert_ne!(rust_generated, rust_authored);
    assert_eq!(reference_authored, rust_authored);
    assert_ne!(reference, rust);
}

#[test]
fn pinned_collision_free_macro_roots_match_exactly() {
    let reference = parse_pattern(REFERENCE_MACRO_ROOTS_COLLISION_FREE.trim()).unwrap();
    let rust = compile(MACRO_ROOTS_COLLISION_FREE).unwrap().pattern;
    assert_eq!(rust, reference);
}

#[test]
fn pinned_ground_and_explicit_binder_patterns_match_exactly() {
    for (contents, reference) in [
        (GROUND, REFERENCE_GROUND),
        (EXPLICIT_GEN_BINDER, REFERENCE_EXPLICIT_GEN_BINDER),
    ] {
        let reference = parse_pattern(reference.trim()).unwrap();
        let rust = compile(contents).unwrap().pattern;
        assert_eq!(rust, reference);
    }
}

#[test]
fn search_pattern_compilation_preserves_root_sorted_ml_connectives() {
    let reference = parse_pattern(REFERENCE_ROOT_SORTED_OR.trim()).unwrap();
    let rust = compile(ROOT_SORTED_OR).unwrap().pattern;
    assert_eq!(rust, reference);

    let definition = parse_definition(&context().definition_kore).unwrap();
    let backend = BackendDefinition::internalize(&definition, "MAIN").unwrap();
    let _admitted = backend.verify_standalone_pattern(&rust, &[]).unwrap();
}

#[test]
fn search_pattern_compilation_user_gen0_is_named_in_ml_binder() {
    let compiled = compile(EXPLICIT_GEN_BINDER).unwrap();
    assert_eq!(compiled.generated_anonymous_variables.len(), 1);
    assert!(
        compiled
            .generated_anonymous_variables
            .iter()
            .all(|identity| identity.name.contains("DotVar"))
    );
    let mut binders = Vec::new();
    walk(&compiled.pattern, &mut |pattern| {
        if let Pattern::Exists { variable, .. } = pattern {
            binders.push(variable.name.clone());
        }
    });
    assert_eq!(binders, ["Var'Unds'Gen0"]);
    assert!(
        !compiled
            .generated_anonymous_variables
            .contains(&KoreVariableIdentity::element("Var'Unds'Gen0"))
    );
    let rendered = compiled.pattern.to_string();
    assert!(rendered.contains("LblisExp"), "{rendered}");
    assert!(rendered.contains("LblisK"), "{rendered}");
}

#[test]
fn search_pattern_compilation_macro_generated_ml_binder_is_anonymous() {
    let compiled = compile("<k> a </k> requires binderMacro").unwrap();
    assert_eq!(
        compiled
            .generated_anonymous_variables
            .iter()
            .filter(|identity| identity.name.contains("Gen"))
            .count(),
        1
    );
    let mut binders = Vec::new();
    walk(&compiled.pattern, &mut |pattern| {
        if let Pattern::Exists { variable, .. } = pattern {
            binders.push(variable.name.clone());
        }
    });
    assert_eq!(binders.len(), 1);
    assert!(
        compiled
            .generated_anonymous_variables
            .iter()
            .any(|identity| identity.name == binders[0])
    );
}

#[test]
fn search_pattern_compilation_macro_generated_binder_avoids_authored_gen0() {
    let compiled = compile("<k> pair(a, _Gen0:Exp) </k> requires binderMacro").unwrap();
    let mut binders = Vec::new();
    walk(&compiled.pattern, &mut |pattern| {
        if let Pattern::Exists { variable, .. } = pattern {
            binders.push(variable.name.clone());
        }
    });
    assert_eq!(binders.len(), 1);
    assert_ne!(binders[0], "Var'Unds'Gen0");
    assert!(
        compiled
            .generated_anonymous_variables
            .contains(&KoreVariableIdentity::element(binders[0].clone()))
    );
    assert!(variable_names(&compiled.pattern).contains("Var'Unds'Gen0"));
    assert!(
        !compiled
            .generated_anonymous_variables
            .contains(&KoreVariableIdentity::element("Var'Unds'Gen0"))
    );
}

#[test]
fn search_pattern_compilation_projects_rewrite_left() {
    let compiled = compile("<k> pair((a => b), (b => c)) </k>").unwrap();
    let mut rewrites = 0;
    walk(&compiled.pattern, &mut |pattern| {
        rewrites += usize::from(matches!(pattern, Pattern::Rewrites { .. }));
    });
    assert_eq!(rewrites, 0);
    let rendered = compiled.pattern.to_string();
    assert!(rendered.contains("Lbla"), "{rendered}");
    assert!(rendered.contains("Lblb"), "{rendered}");
    assert!(!rendered.contains("Lblc"), "{rendered}");
}

/// The body of a compiled pattern and the distinct conjuncts of its condition (`_andBool_` is
/// idempotent, so a test the condition repeats says nothing more).
fn body_and_tests(compiled: &CompiledSearchPattern) -> (Pattern, BTreeSet<String>) {
    let Pattern::And { arguments, .. } = &compiled.pattern else {
        panic!("expected a conjunction: {}", compiled.pattern)
    };
    let mut tests = BTreeSet::new();
    for argument in &arguments[1..] {
        let mut pending = vec![argument];
        while let Some(pattern) = pending.pop() {
            match pattern {
                Pattern::Equals { left, .. } => pending.push(left),
                Pattern::Application { symbol, arguments }
                    if symbol.name == "Lbl'Unds'andBool'Unds'" =>
                {
                    pending.extend(arguments)
                }
                other => {
                    tests.insert(other.to_string());
                }
            }
        }
    }
    (arguments[0].clone(), tests)
}

/// A pattern with a rewrite denotes its left side, so a cast around the rewrite constrains the
/// left side's value: `pair((X => a):Exp, b)` is the pattern `pair(X:Exp, b)`, with the same
/// sort tests, and its condition holds no rewrite.
#[test]
fn search_pattern_compilation_tests_a_cast_around_a_rewrite_on_the_left_side() {
    for (cast_rewrite, direct) in [
        ("<k> pair((X => a):Exp, b) </k>", "<k> pair(X:Exp, b) </k>"),
        ("<k> (pair(X, Y) => a):Exp </k>", "<k> pair(X, Y):Exp </k>"),
    ] {
        let compiled = compile(cast_rewrite).unwrap();
        let mut rewrites = 0;
        walk(&compiled.pattern, &mut |pattern| {
            rewrites += usize::from(matches!(pattern, Pattern::Rewrites { .. }));
        });
        assert_eq!(rewrites, 0, "{}", compiled.pattern);
        let (body, tests) = body_and_tests(&compiled);
        let (direct_body, direct_tests) = body_and_tests(&compile(direct).unwrap());
        assert_eq!(body, direct_body, "{cast_rewrite}");
        assert_eq!(tests, direct_tests, "{cast_rewrite}");
        assert!(
            tests.iter().all(|test| test.contains("LblisExp")),
            "{tests:?}"
        );
    }
}

#[test]
fn search_pattern_compilation_retains_requires_after_transforms() {
    let compiled = compile("<k> a </k> requires false").unwrap();
    let Pattern::And { arguments, .. } = &compiled.pattern else {
        panic!("expected conjunction")
    };
    assert!(matches!(arguments.as_slice(), [_, Pattern::Equals { .. }]));

    let error = compile("<k> a </k> requires cellPredicate(<top> <k> a </k> <k> b </k> </top>)")
        .unwrap_err();
    let CompileSearchPatternError::CellConcretization(error) = error else {
        panic!("expected cell-concretization error: {error:?}")
    };
    assert_eq!(error.diagnostics.len(), 1);
    assert_eq!(
        error.diagnostics[0].code,
        k_rust::diagnostic::DiagnosticCode::InvalidCellConcretization
    );
    assert_eq!(error.diagnostics[0].source.as_deref(), Some(PATTERN_SOURCE));
    assert_eq!(error.diagnostics[0].location, Some(PATTERN_LOCATION));
}

/// A pattern denotes the configurations its left side matches under its `requires`, and
/// describes no later state, so an `ensures` other than `true` says nothing it denotes and is
/// rejected at the pattern; `ensures true` is the clause every pattern has.
#[test]
fn search_pattern_compilation_rejects_an_ensures_clause() {
    let error = compile("<k> a </k> ensures predicate(X:Exp)").unwrap_err();
    let CompileSearchPatternError::Denotation(diagnostic) = &error else {
        panic!("expected a denotation error: {error:?}")
    };
    assert_eq!(
        diagnostic.code,
        k_rust::diagnostic::DiagnosticCode::InvalidSearchPattern
    );
    assert!(diagnostic.message.contains("`ensures`"), "{error}");
    assert_eq!(diagnostic.source.as_deref(), Some(PATTERN_SOURCE));
    assert!(diagnostic.location.is_some(), "{diagnostic:?}");
    compile("<k> a </k> ensures true").unwrap();
}

/// A variable that occurs only on a rewrite's right side is constrained by nothing the pattern
/// denotes, so the pattern is rejected naming it; one that also occurs on the left side, or in
/// `requires`, is constrained, and an anonymous variable names nothing.
#[test]
fn search_pattern_compilation_rejects_a_variable_only_on_a_right_side() {
    for (pattern, variables) in [
        ("<k> X => Y </k>", "variable Y "),
        ("<k> pair(X => Y, Z => W) </k>", "variables W, Y "),
    ] {
        let error = compile(pattern).unwrap_err();
        let CompileSearchPatternError::Denotation(diagnostic) = &error else {
            panic!("{pattern}: expected a denotation error: {error:?}")
        };
        assert_eq!(
            diagnostic.code,
            k_rust::diagnostic::DiagnosticCode::InvalidSearchPattern
        );
        assert!(
            diagnostic.message.contains(variables)
                && diagnostic
                    .message
                    .contains("only on the right side of a rewrite"),
            "{pattern}: {error}"
        );
        assert_eq!(diagnostic.source.as_deref(), Some(PATTERN_SOURCE));
    }
    for pattern in [
        "<k> X => X </k>",
        "<k> X => _ </k>",
        "<k> pair(X, a => Y) </k> requires predicate(pair(X, Y))",
    ] {
        compile(pattern).unwrap_or_else(|error| panic!("{pattern}: {error}"));
    }
}

#[test]
fn search_pattern_compilation_retains_parse_error_provenance() {
    let error = compile("<k>").unwrap_err();
    let CompileSearchPatternError::Rule(RuleError::Parse(error)) = error else {
        panic!("expected rule parse error: {error:?}")
    };
    assert_eq!(error.source.as_deref(), Some(PATTERN_SOURCE));
    // EOF is a zero-width point three columns after the supplied pattern origin.
    assert_eq!(
        error.location,
        Some(Location {
            start_line: 7,
            start_column: 6,
            end_line: 7,
            end_column: 6,
        })
    );
}

#[test]
fn search_pattern_compilation_reuses_transformed_context() {
    let definition = parse_definition(&context().definition_kore).unwrap();
    let backend = BackendDefinition::internalize(&definition, "MAIN").unwrap();
    for contents in [GROUND, MACRO_ROOTS, MACRO_ROOTS_COLLISION_FREE] {
        let compiled = compile(contents).unwrap();
        backend
            .verify_standalone_pattern(&compiled.pattern, &[])
            .unwrap()
            .internalize_pattern()
            .unwrap();
    }
    let explicit_binder = compile(EXPLICIT_GEN_BINDER).unwrap();
    let _admitted = backend
        .verify_standalone_pattern(&explicit_binder.pattern, &[])
        .unwrap();
}

#[test]
fn search_pattern_compilation_builds_generated_top_kore() {
    let true_requires = compile("<k> a </k>").unwrap();
    let Pattern::And { sort, arguments } = &true_requires.pattern else {
        panic!("expected conjunction")
    };
    assert_eq!(sort.to_string(), "SortGeneratedTopCell{}");
    assert!(matches!(arguments.as_slice(), [_, Pattern::Top { .. }]));

    let constrained = compile(GROUND).unwrap();
    let Pattern::And { sort, arguments } = &constrained.pattern else {
        panic!("expected conjunction")
    };
    assert_eq!(sort.to_string(), "SortGeneratedTopCell{}");
    let [
        _,
        Pattern::Equals {
            operand_sort,
            result_sort,
            right,
            ..
        },
    ] = arguments.as_slice()
    else {
        panic!("expected body and requires equality")
    };
    assert_eq!(operand_sort.to_string(), "SortBool{}");
    assert_eq!(result_sort.to_string(), "SortGeneratedTopCell{}");
    assert!(matches!(right.as_ref(), Pattern::DomainValue { value, .. } if value == "true"));
}

#[test]
fn search_pattern_compilation_rejects_non_top_body() {
    let parsed = k_rust::outer::parse(
        "non-top.k",
        r#"module MAIN
  syntax Exp ::= "a" [symbol(a)]
  syntax TopCell ::= "<top>" Exp "</top>" [cell, cellName(top), maincell, symbol(<top>)]
endmodule
"#,
    )
    .unwrap();
    let execution = k_rust::outer::lower(&parsed, "MAIN").unwrap();
    let parsing = definition_with_named_projections(&execution);
    let parsing = ResolvedDefinition::resolve(&parsing).unwrap();
    let execution = ResolvedDefinition::resolve(&execution).unwrap();
    assert_eq!(
        compile_search_pattern(
            &parsing,
            &execution,
            "MAIN",
            "<top> a </top>",
            Attributes::default(),
        )
        .unwrap_err(),
        CompileSearchPatternError::ExpectedGeneratedTopCell {
            actual: k_rust::kast::Sort::new("TopCell"),
        }
    );
}

#[test]
fn search_pattern_compilation_rejects_an_undetermined_ground_instance() {
    let context = phantom_context();
    for pattern in ["<k> size() ~> _ </k>", "<k> _ </k> requires size() ==Int 0"] {
        let error = compile_in(&context, "MAIN", pattern)
            .expect_err("a phantom label has no ground instance");
        let CompileSearchPatternError::SortInjection(SortInjectionError::UndeterminedInstance(
            instance,
        )) = &error
        else {
            panic!("{pattern}: {error:?}")
        };
        assert!(
            matches!(
                &instance.site,
                UndeterminedSite::Ground {
                    input: GroundInput::SearchPattern,
                    cause: GroundCause::Instance(UndeterminedCause::Phantom { label, parameter }),
                } if label == "size" && parameter == &k_rust::kast::Sort::new("S")
            ),
            "{error}"
        );
        assert!(error.to_string().contains("size"), "{error}");
        assert!(error.to_string().contains("search pattern"), "{error}");
    }
}

#[test]
fn a_phantom_search_pattern_diagnostic_offers_no_cast() {
    let context = phantom_context();
    let message = compile_in(&context, "MAIN", "<k> size():Int ~> _ </k>")
        .unwrap_err()
        .to_string();
    assert!(message.contains("no sort cast can fix it"), "{message}");
    assert!(!message.contains("add a sort cast"), "{message}");
    assert!(!message.contains("sentence sort variable"), "{message}");
    assert!(
        !message.contains("only the sort of a predicate"),
        "{message}"
    );
}

#[test]
fn an_open_search_pattern_diagnostic_keeps_cast_advice() {
    let context = load_context(
        "search-pattern/open.k",
        r#"module MAIN
  syntax Foo ::= "a" [symbol(a)]
  syntax {S} Foo ::= wrap(S) [symbol(wrap)]
  syntax {S} S ::= undef() [function, total, symbol(undef)]
  configuration <k> $PGM:Foo </k>
endmodule
"#,
        "MAIN",
    );
    let message = compile_in(&context, "MAIN", "<k> wrap(undef()) ~> _ </k>")
        .unwrap_err()
        .to_string();
    assert!(message.contains("wrap"), "{message}");
    assert!(message.contains("add a sort cast"), "{message}");
    assert!(!message.contains("sentence sort variable"), "{message}");
    assert!(
        !message.contains("only the sort of a predicate"),
        "{message}"
    );
}

#[test]
fn a_numeral_sorted_search_position_is_rejected_at_load() {
    let prelude = embedded("prelude.md").expect("embedded prelude should exist");
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let error = load_with_options(
        ResolvedSource::new("search-pattern/search8.k", SEARCH8),
        "SEARCH8",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![prelude],
            excluded_module_attributes: vec![
                CompilationBackend::Rust.excluded_module_attribute().into(),
            ],
            ..LoadOptions::default()
        },
    )
    .expect_err("a numeral cannot have terms or search operand positions");
    let k_rust::outer::LoadError::SourceDiagnostics(mut diagnostics) = error else {
        panic!("{error}");
    };
    diagnostics.sort_by_key(|diagnostic| diagnostic.location.map(|location| location.start_line));
    assert_eq!(diagnostics.len(), 2, "{diagnostics:#?}");
    for (diagnostic, (sentence, place)) in diagnostics.iter().zip([
        ("syntax 8 ::=", "the sort of a production."),
        ("syntax Foo ::=", "an operand of a production."),
    ]) {
        assert_eq!(
            diagnostic.code,
            k_rust::diagnostic::DiagnosticCode::InvalidNumeralSort,
            "{diagnostic:#?}"
        );
        assert_eq!(diagnostic.severity, k_rust::diagnostic::Severity::Error);
        let line = SEARCH8
            .lines()
            .position(|line| line.trim_start().starts_with(sentence))
            .expect("the rejected sentence is in the fixture") as u32
            + 1;
        assert_eq!(
            diagnostic.location.unwrap().start_line,
            line,
            "{diagnostic:#?}"
        );
        assert!(diagnostic.message.ends_with(place), "{diagnostic:#?}");
    }
}

/// A transformed surface search root must reject malformed injection syntax, including syntax
/// introduced by a macro after the authored pattern has parsed successfully.
#[test]
fn search_pattern_compilation_rejects_retained_unlicensed_injections() {
    use k_rust::definition::Sentence;
    use k_rust::kast::{Label, Sort, Term};
    let inj = |source: &str, target: &str, operand: Term| Term::Apply {
        label: Label::with_parameters("inj", vec![Sort::new(source), Sort::new(target)]),
        arguments: vec![operand],
    };
    for invalid in [
        inj("K", "KItem", Term::Sequence(vec![])),
        inj("KItem", "K", inj("Exp", "KItem", Term::apply("a", vec![]))),
        inj("Exp", "Exp", Term::apply("a", vec![])),
        inj(
            "Exp",
            "KItem",
            Term::Token {
                token: "true".into(),
                sort: Sort::new("Bool"),
            },
        ),
    ] {
        let base = context();
        let mut execution = base.execution.clone();
        let mut replaced = false;
        for module in &mut execution.modules {
            for sentence in &mut module.local_sentences {
                let Sentence::Rule { body, .. } = k_rust::definition::sentence_mut(sentence) else {
                    continue;
                };
                let Term::Rewrite { left, right: _ } = body.unannotated() else {
                    continue;
                };
                if matches!(left.unannotated(), Term::Apply { label, .. } if label.name == "bodyMacro")
                {
                    *body = Term::Rewrite {
                        left: left.clone(),
                        right: Box::new(invalid.clone()),
                    };
                    replaced = true;
                }
            }
        }
        assert!(replaced, "the fixture retains its bodyMacro rule");
        let modified = Context {
            parsing: base.parsing.clone(),
            execution,
            definition_kore: base.definition_kore.clone(),
        };
        let error = compile_in(&modified, "MAIN", "<top> <k> bodyMacro </k> </top>")
            .expect_err("a retained injection must not escape through search compilation");
        assert!(
            error.to_string().contains("inj") || error.to_string().contains("sort"),
            "{invalid}: {error}"
        );
    }
}

/// Class test for the search-pattern ticket: a search pattern denotes the configurations its
/// body's left side matches, under its `requires`, so a condition conjunct over a named variable
/// that occurs only on a rewrite's right side or only in `ensures` holds whenever it is
/// satisfiable at all and constrains nothing. Every named variable of the compiled condition must
/// therefore occur in the compiled body or in the written `requires`, or the pattern must be
/// rejected. The first two patterns are controls that hold on main (the cast's variable is on the
/// left side). The third is a control that must also compile: `Y` occurs only in `requires`, an
/// existential that constrains `X` through `predicate(pair(X, Y))`, so rejecting every variable
/// outside the body would reject a pattern that means something. The others hold a written
/// variable, and its cast, only on a rewrite's right side or only in `ensures`, which on main
/// compile to a dead conjunct (`X => Y:Bool` matches what `X => Y:Exp` matches).
#[test]
fn a_compiled_search_condition_tests_only_variables_its_body_binds() {
    let mut failures = Vec::new();
    // Each pattern, with the variables its `requires` alone binds, and whether it must compile.
    for (pattern, existential, must_compile) in [
        ("<k> X:Bool </k>", &[][..], true),
        ("<k> X => X:Bool </k>", &[], true),
        (
            "<k> X </k> requires predicate(Y:Exp) andBool predicate(pair(X, Y))",
            &["VarY"],
            true,
        ),
        ("<k> X => Y:Bool </k>", &[], false),
        ("<k> X => Y:Bool ~> Z </k>", &[], false),
        ("<k> (X => Y):Exp </k>", &[], false),
        ("<k> a </k> ensures predicate(X:Exp)", &[], false),
    ] {
        let compiled = match compile(pattern) {
            Ok(compiled) => compiled,
            Err(error) => {
                if must_compile {
                    failures.push(format!("{pattern}: rejected: {error}"));
                }
                continue;
            }
        };
        let Pattern::And { arguments, .. } = &compiled.pattern else {
            panic!("expected a conjunction: {}", compiled.pattern)
        };
        let bound = variable_names(&arguments[0]);
        let unbound = arguments[1..]
            .iter()
            .flat_map(variable_names)
            .filter(|name| !bound.contains(name) && !existential.contains(&name.as_str()))
            .collect::<BTreeSet<_>>();
        if !unbound.is_empty() {
            failures.push(format!(
                "{pattern}: the condition tests {unbound:?}, which neither the body nor `requires` binds: {}",
                compiled.pattern
            ));
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}
