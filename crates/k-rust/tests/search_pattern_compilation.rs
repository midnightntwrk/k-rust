#![cfg(feature = "z3-inference")]

use std::collections::BTreeSet;
use std::sync::OnceLock;

use k_rust::builtin::embedded;
use k_rust::definition::{
    Attributes, Definition, LOCATION_ATTRIBUTE, Location, ResolvedDefinition, SOURCE_ATTRIBUTE,
    SOURCE_ID_ATTRIBUTE,
};
use k_rust::inner::{RuleError, definition_with_named_projections};
use k_rust::kompile::{
    CompilationBackend, CompileOptions, CompileSearchPatternError, CompiledSearchPattern,
    KoreVariableIdentity, compile_loaded_definition, compile_search_pattern,
};
use k_rust::kore::ast::Pattern;
use k_rust::kore::parser::{parse_definition, parse_pattern};
use k_rust::outer::{LoadOptions, ResolvedSource, load_with_options};
use k_rust_backend::definition::BackendDefinition;

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

fn context() -> &'static Context {
    static CONTEXT: OnceLock<Context> = OnceLock::new();
    CONTEXT.get_or_init(|| {
        let prelude = embedded("prelude.md").expect("embedded prelude should exist");
        let mut resolver = |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        };
        let loaded = load_with_options(
            ResolvedSource::new("search-pattern/pattern.k", DEFINITION),
            "MAIN",
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
        let parsing = definition_with_named_projections(&loaded.definition);
        let artifacts = compile_loaded_definition(&loaded, CompileOptions::default())
            .expect("search-pattern fixture should compile");
        Context {
            parsing,
            execution: artifacts.execution_definition,
            definition_kore: artifacts.definition_kore,
        }
    })
}

fn compile(contents: &str) -> Result<CompiledSearchPattern, CompileSearchPatternError> {
    let context = context();
    let parsing = ResolvedDefinition::resolve(&context.parsing).unwrap();
    let execution = ResolvedDefinition::resolve(&context.execution).unwrap();
    let mut attributes = Attributes::default();
    attributes.insert(SOURCE_ATTRIBUTE, serde_json::json!(PATTERN_SOURCE));
    attributes.insert(SOURCE_ID_ATTRIBUTE, serde_json::json!(23));
    attributes.insert(LOCATION_ATTRIBUTE, serde_json::json!([7, 3, 7, 31]));
    attributes.insert("contentStartOffset", serde_json::json!(101));
    attributes.insert("contentStartLine", serde_json::json!(7));
    attributes.insert("contentStartColumn", serde_json::json!(3));
    compile_search_pattern(&parsing, &execution, "MAIN", contents.trim(), attributes)
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
    BackendDefinition::internalize(&definition, "MAIN")
        .unwrap()
        .verify_standalone_pattern(&rust)
        .unwrap();
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

#[test]
fn search_pattern_compilation_retains_requires_and_ignores_ensures_after_transforms() {
    let without_ensures = compile("<k> a </k> requires false").unwrap();
    let with_ensures = compile("<k> a </k> requires false ensures false").unwrap();
    assert_eq!(with_ensures, without_ensures);
    let Pattern::And { arguments, .. } = &with_ensures.pattern else {
        panic!("expected conjunction")
    };
    assert!(matches!(arguments.as_slice(), [_, Pattern::Equals { .. }]));

    let error = compile("<k> a </k> ensures cellPredicate(<top> <k> a </k> <k> b </k> </top>)")
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

#[test]
fn search_pattern_compilation_collects_casts_from_ensures_before_discarding_it() {
    let compiled = compile("<k> a </k> ensures predicate(X:Exp)").unwrap();
    let rendered = compiled.pattern.to_string();
    assert!(rendered.contains("LblisExp"), "{rendered}");
    assert!(rendered.contains("VarX"), "{rendered}");
    assert!(!rendered.contains("Lblpredicate"), "{rendered}");
}

#[test]
fn search_pattern_compilation_retains_parse_error_provenance() {
    let error = compile("<k>").unwrap_err();
    let CompileSearchPatternError::Rule(RuleError::Parse(error)) = error else {
        panic!("expected rule parse error: {error:?}")
    };
    assert_eq!(error.source.as_deref(), Some(PATTERN_SOURCE));
    assert_eq!(error.location, Some(PATTERN_LOCATION));
}

#[test]
fn search_pattern_compilation_reuses_transformed_context() {
    let definition = parse_definition(&context().definition_kore).unwrap();
    let backend = BackendDefinition::internalize(&definition, "MAIN").unwrap();
    for contents in [GROUND, MACRO_ROOTS, MACRO_ROOTS_COLLISION_FREE] {
        let compiled = compile(contents).unwrap();
        backend
            .verify_standalone_pattern(&compiled.pattern)
            .unwrap();
        backend.internalize_pattern(&compiled.pattern, &[]).unwrap();
    }
    let explicit_binder = compile(EXPLICIT_GEN_BINDER).unwrap();
    backend
        .verify_standalone_pattern(&explicit_binder.pattern)
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
