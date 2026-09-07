//! Fresh compilation selection follows the pinned frontend's outer/inner validation boundary.
//! The paired reference controls are recorded in draft/compiler-optimization/module-selection.

use indoc::indoc;
use k_rust::{
    definition::Sentence,
    diagnostic::{DiagnosticCode, DiagnosticPolicy, Severity, WarningLevel},
    outer::{
        LoadError, LoadOptions, LoadedDefinition, ResolvedSource, load_for_compilation,
        load_structured, load_with_base, load_with_options, lower, parse,
    },
};

fn compile(
    source: &str,
    syntax: Option<&str>,
    options: &LoadOptions,
) -> Result<(LoadedDefinition, String), LoadError> {
    load_for_compilation(
        ResolvedSource::new("selection.k", source),
        "MAIN",
        syntax,
        &mut |_: &str, required: &str| Err(format!("unexpected require: {required}")),
        options,
    )
}

fn names(loaded: &LoadedDefinition) -> Vec<&str> {
    loaded
        .definition
        .modules
        .iter()
        .map(|module| module.name.as_str())
        .collect()
}

fn has_rule(loaded: &LoadedDefinition, module: &str) -> bool {
    loaded
        .resolved
        .module(loaded.resolved.module_id(module).unwrap())
        .local_sentences
        .iter()
        .any(|sentence| matches!(sentence, Sentence::Rule { .. }))
}

#[test]
fn malformed_unselected_bubble_is_omitted_but_selected_syntax_still_fails() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "ok" [symbol(ok)]
          rule ok => ok
        endmodule
        module UNUSED
          imports MAIN
          rule ok =>
        endmodule
    "#};
    let (loaded, syntax) = compile(source, Some("MAIN"), &LoadOptions::default()).unwrap();
    assert_eq!(syntax, "MAIN");
    assert_eq!(names(&loaded), ["MAIN"]);
    assert!(has_rule(&loaded, "MAIN"));
    assert_eq!(
        loaded.files[0].modules.len(),
        2,
        "source files are not trimmed"
    );
    assert!(!loaded.source_table.is_empty());
    let error = compile(source, Some("UNUSED"), &LoadOptions::default()).unwrap_err();
    let LoadError::RuleParsing(k_rust::inner::RuleError::Parse(error)) = error else {
        panic!("expected selected bubble parse failure, got {error:?}");
    };
    assert_eq!(error.module, "UNUSED");
}

#[test]
fn explicit_and_default_syntax_roots_are_retained_with_no_bubble_entries() {
    let source = indoc! {r#"
        module MAIN endmodule
        module EXTRA
          syntax Exp ::= "extra" [symbol(extra)]
          rule extra => extra
        endmodule
        module MAIN-SYNTAX
          syntax Exp ::= "default" [symbol(default)]
          rule default => default
        endmodule
        module EMPTY
          syntax Marker ::= "marker"
        endmodule
    "#};
    let (explicit, chosen) = compile(source, Some("EXTRA"), &LoadOptions::default()).unwrap();
    assert_eq!(chosen, "EXTRA");
    assert_eq!(names(&explicit), ["MAIN", "EXTRA", "EMPTY"]);
    assert!(has_rule(&explicit, "EXTRA"));
    let (default, chosen) = compile(source, None, &LoadOptions::default()).unwrap();
    assert_eq!(chosen, "MAIN-SYNTAX");
    assert_eq!(names(&default), ["MAIN", "MAIN-SYNTAX", "EMPTY"]);
    assert!(has_rule(&default, "MAIN-SYNTAX"));
    assert!(
        !default
            .diagnostics
            .iter()
            .any(|d| d.code == DiagnosticCode::MissingSyntaxModule)
    );
}

#[test]
fn imported_bubbles_are_classified_before_backend_exclusion_including_private_imports() {
    let source = indoc! {r#"
        module MAIN endmodule
        module BUBBLE [concrete]
          rule invalid =>
        endmodule
        module IMPORTER
          imports private BUBBLE
          syntax Marker ::= "notRetained"
        endmodule
    "#};
    let options = LoadOptions {
        excluded_module_attributes: vec!["concrete".into()],
        ..LoadOptions::default()
    };
    let (loaded, _) = compile(source, Some("MAIN"), &options).unwrap();
    assert_eq!(names(&loaded), ["MAIN"]);
}

#[test]
fn pre_exclusion_import_closure_survives_a_removed_intermediate_module() {
    let source = indoc! {r#"
        module MAIN
          imports EXCLUDED
        endmodule
        module EXCLUDED [concrete]
          imports CHILD
        endmodule
        module CHILD
          syntax Exp ::= "child" [symbol(child)]
          rule child => child
        endmodule
    "#};
    let options = LoadOptions {
        excluded_module_attributes: vec!["concrete".into()],
        ..LoadOptions::default()
    };
    let (loaded, _) = compile(source, Some("MAIN"), &options).unwrap();
    assert_eq!(names(&loaded), ["MAIN", "CHILD"]);
    assert!(loaded.definition.main_module().unwrap().imports.is_empty());
    assert!(has_rule(&loaded, "CHILD"));
}

#[test]
fn utility_roots_preserve_their_bubble_dependencies() {
    let source = indoc! {r#"
        module MAIN endmodule
        module K-REFLECTION
          imports CHILD
        endmodule
        module CHILD
          syntax Exp ::= "child" [symbol(child)]
          rule child => child
        endmodule
    "#};
    let (loaded, _) = compile(source, Some("MAIN"), &LoadOptions::default()).unwrap();
    assert_eq!(names(&loaded), ["MAIN", "K-REFLECTION", "CHILD"]);
    assert!(has_rule(&loaded, "CHILD"));
}

#[test]
fn missing_and_excluded_syntax_roots_do_not_fall_back() {
    let source = "module MAIN endmodule\nmodule MAIN-SYNTAX [concrete] endmodule";
    let options = LoadOptions {
        excluded_module_attributes: vec!["concrete".into()],
        ..LoadOptions::default()
    };
    for syntax in [None, Some("MAIN-SYNTAX")] {
        assert!(matches!(compile(source, syntax, &options),
            Err(LoadError::ExcludedSyntaxModule { module, attribute })
                if module == "MAIN-SYNTAX" && attribute == "concrete"));
    }
    let error = compile(source, Some("ABSENT"), &options).unwrap_err();
    assert!(matches!(&error, LoadError::MissingSyntaxModule(name) if name == "ABSENT"));
    assert_eq!(
        error.to_string(),
        "Could not find main syntax module with name ABSENT in definition."
    );
    assert!(
        matches!(compile("module MAIN [concrete] endmodule", Some("MAIN"), &options),
        Err(LoadError::ExcludedMainModule { module, .. }) if module == "MAIN")
    );
}

#[test]
fn missing_default_warning_is_emitted_once_and_obeys_policy() {
    let source = "module MAIN endmodule";
    let options = LoadOptions {
        diagnostics: DiagnosticPolicy {
            level: WarningLevel::All,
            warnings_to_errors: false,
        },
        ..LoadOptions::default()
    };
    let (loaded, syntax) = compile(source, None, &options).unwrap();
    assert_eq!(syntax, "MAIN");
    assert_eq!(loaded.diagnostics.len(), 1);
    assert_eq!(
        loaded.diagnostics[0].code,
        DiagnosticCode::MissingSyntaxModule
    );
    assert_eq!(loaded.diagnostics[0].source.as_deref(), Some("selection.k"));
    let mut suppressed = options.clone();
    suppressed.diagnostics.level = WarningLevel::None;
    assert!(
        compile(source, None, &suppressed)
            .unwrap()
            .0
            .diagnostics
            .is_empty()
    );
    let mut promoted = options;
    promoted.diagnostics.warnings_to_errors = true;
    let Err(LoadError::SourceDiagnostics(diagnostics)) = compile(source, None, &promoted) else {
        panic!("missing syntax warning must be promoted");
    };
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::MissingSyntaxModule);
    assert_eq!(diagnostics[0].severity, Severity::Error);
}

fn configuration_options() -> LoadOptions {
    LoadOptions {
        implicit_sources: vec![ResolvedSource::new(
            "prelude.k",
            indoc! {r#"
            module MAP
              syntax Map
            endmodule
            module DEFAULT-CONFIGURATION
              syntax K
              configuration <k> $PGM:K </k>
            endmodule
        "#},
        )],
        ..LoadOptions::default()
    }
}

#[test]
fn default_configuration_is_retained_only_when_needed() {
    let options = configuration_options();
    let (fallback, _) = compile("module MAIN endmodule", Some("MAIN"), &options).unwrap();
    assert!(names(&fallback).contains(&"DEFAULT-CONFIGURATION"));
    assert!(
        fallback
            .definition
            .main_module()
            .unwrap()
            .imports
            .iter()
            .any(|i| i.name == "DEFAULT-CONFIGURATION")
    );
    let authored = indoc! {r#"
        module MAIN
          syntax K
          configuration <k> $PGM:K </k>
        endmodule
    "#};
    let (loaded, _) = compile(authored, Some("MAIN"), &options).unwrap();
    assert!(!names(&loaded).contains(&"DEFAULT-CONFIGURATION"));
    assert!(
        loaded
            .definition
            .main_module()
            .unwrap()
            .imports
            .iter()
            .any(|i| i.name == "MAP")
    );
}

#[test]
fn configuration_fallback_is_decided_after_backend_filtering() {
    let source = indoc! {r#"
        module MAIN
          imports CONFIG
        endmodule
        module CONFIG [concrete]
          syntax K
          configuration <k> $PGM:K </k>
        endmodule
    "#};
    let mut options = configuration_options();
    options.excluded_module_attributes = vec!["concrete".into()];
    let (loaded, _) = compile(source, Some("MAIN"), &options).unwrap();
    assert!(!names(&loaded).contains(&"CONFIG"));
    assert!(names(&loaded).contains(&"DEFAULT-CONFIGURATION"));
    assert!(
        loaded
            .definition
            .main_module()
            .unwrap()
            .imports
            .iter()
            .any(|i| i.name == "DEFAULT-CONFIGURATION")
    );
}

#[test]
fn distinct_proof_configuration_root_and_its_imports_are_retained() {
    let source = indoc! {r#"
        module MAIN endmodule
        module CONFIG
          imports CHILD
        endmodule
        module CHILD
          syntax K
          configuration <k> $PGM:K </k>
        endmodule
    "#};
    let mut options = configuration_options();
    options.configuration_module = Some("CONFIG".into());
    let (loaded, _) = compile(source, Some("MAIN"), &options).unwrap();
    assert!(names(&loaded).contains(&"CONFIG"));
    assert!(names(&loaded).contains(&"CHILD"));
    assert!(!names(&loaded).contains(&"DEFAULT-CONFIGURATION"));
    options.configuration_module = Some("MISSING".into());
    assert!(matches!(compile(source, Some("MAIN"), &options),
        Err(LoadError::MissingConfigurationModule(name)) if name == "MISSING"));
    options.configuration_module = Some("CONFIG".into());
    let (fallback, _) = compile(
        "module MAIN endmodule\nmodule CONFIG endmodule",
        Some("MAIN"),
        &options,
    )
    .unwrap();
    let config = fallback
        .definition
        .modules
        .iter()
        .find(|m| m.name == "CONFIG")
        .unwrap();
    assert!(
        config
            .imports
            .iter()
            .any(|i| i.name == "DEFAULT-CONFIGURATION")
    );
    assert!(
        !fallback
            .definition
            .main_module()
            .unwrap()
            .imports
            .iter()
            .any(|i| i.name == "DEFAULT-CONFIGURATION")
    );
}

#[test]
fn unselected_outer_errors_remain_errors_before_syntax_selection() {
    for invalid in [
        "imports MISSING",
        "syntax Exp ::= MissingSort",
        "syntax Alias = MissingSort\nsyntax Exp ::= Alias",
        r#"syntax Exp ::= List{Exp, ","}"#,
    ] {
        let source =
            format!("module MAIN endmodule\nmodule UNUSED\n{invalid}\nrule invalid =>\nendmodule");
        let baseline = load_with_options(
            ResolvedSource::new("selection.k", &source),
            "MAIN",
            &mut |_: &str, required: &str| Err(format!("unexpected {required}")),
            &LoadOptions::default(),
        )
        .unwrap_err();
        assert!(
            matches!(
                baseline,
                LoadError::DefinitionResolution(_) | LoadError::SourceDiagnostics(_)
            ),
            "the generic loader must reject the same outer fragment {invalid:?}: {baseline:?}"
        );
        let error = compile(&source, Some("ABSENT"), &LoadOptions::default()).unwrap_err();
        assert_eq!(format!("{error:?}"), format!("{baseline:?}"));
        assert!(
            matches!(
                error,
                LoadError::DefinitionResolution(_) | LoadError::SourceDiagnostics(_)
            ),
            "outer error for {invalid:?} must precede syntax selection: {error:?}"
        );
    }
    let source =
        "module MAIN endmodule\nmodule A imports B endmodule\nmodule B imports A endmodule";
    assert!(matches!(
        compile(source, Some("MAIN"), &LoadOptions::default()),
        Err(LoadError::DefinitionResolution(_))
    ));
}

#[test]
fn generic_prepared_and_structured_loading_keep_their_module_policy() {
    let source = indoc! {r#"
        module MAIN endmodule
        module UNUSED
          syntax Exp ::= "unused" [symbol(unused)]
          rule unused => unused
        endmodule
    "#};
    let options = LoadOptions::default();
    let mut resolver = |_: &str, required: &str| Err(format!("unexpected {required}"));
    let generic = load_with_options(
        ResolvedSource::new("base.k", source),
        "MAIN",
        &mut resolver,
        &options,
    )
    .unwrap();
    assert!(has_rule(&generic, "UNUSED"));
    let prepared = load_with_base(
        ResolvedSource::new("proof.k", "module PROOF imports MAIN endmodule"),
        "PROOF",
        &mut resolver,
        &options,
        &generic.definition,
        &["base.k".into()],
    )
    .unwrap();
    assert!(has_rule(&prepared, "UNUSED"));
    let structured = load_structured(
        lower(&parse("structured.k", source).unwrap(), "MAIN").unwrap(),
        &options,
    )
    .unwrap();
    assert!(has_rule(&structured, "UNUSED"));
    let (selected, _) = compile(source, Some("MAIN"), &options).unwrap();
    assert_eq!(names(&selected), ["MAIN"]);
}

#[test]
fn selected_modules_preserve_serialized_metadata_and_private_imports() {
    let source = indoc! {r#"
        module CHILD
          syntax Exp ::= "child" [symbol(child)]
        endmodule
        module MAIN
          imports private CHILD
          rule child => child
        endmodule
        module UNUSED
          imports MAIN
          imports CHILD
          rule child => child
        endmodule
    "#};
    let options = LoadOptions::default();
    let mut generic = load_with_options(
        ResolvedSource::new("selection.k", source),
        "MAIN",
        &mut |_: &str, required: &str| Err(format!("unexpected {required}")),
        &options,
    )
    .unwrap();
    let (selected, _) = compile(source, Some("MAIN"), &options).unwrap();
    generic
        .definition
        .modules
        .retain(|module| module.name != "UNUSED");
    assert_eq!(
        k_rust::definition::json::to_provenance_string_pretty(
            &selected.definition,
            &selected.source_table
        )
        .unwrap(),
        k_rust::definition::json::to_provenance_string_pretty(
            &generic.definition,
            &generic.source_table
        )
        .unwrap(),
        "selected contents, catalog references, source spans, and serialized origin metadata must agree"
    );
    assert!(!selected.definition.main_module().unwrap().imports[0].public);
    assert_eq!(selected.source_table, generic.source_table);
}

#[test]
fn markdown_selection_and_requires_resolution_precede_module_selection() {
    let entry = indoc! {r#"
        ```k
        requires "dependency.md"
        module MAIN
          imports DEP
        endmodule
        ```
        ```{.k .concrete}
        module HIDDEN endmodule
        ```
    "#};
    let dependency = indoc! {r#"
        ```k
        module DEP
          syntax Exp ::= "dep" [symbol(dep)]
          rule dep => dep
        endmodule
        module UNUSED
          imports DEP
          rule dep =>
        endmodule
        ```
    "#};
    let mut requested = Vec::new();
    let (loaded, syntax) = load_for_compilation(
        ResolvedSource::new("entry.md", entry),
        "MAIN",
        Some("MAIN"),
        &mut |source: &str, required: &str| {
            requested.push((source.to_owned(), required.to_owned()));
            Ok(ResolvedSource::new("dependency.md", dependency))
        },
        &LoadOptions {
            markdown_selector: "k & ! concrete".into(),
            ..LoadOptions::default()
        },
    )
    .unwrap();
    assert_eq!(syntax, "MAIN");
    assert_eq!(requested, [("entry.md".into(), "dependency.md".into())]);
    assert_eq!(names(&loaded), ["DEP", "MAIN"]);
    assert_eq!(
        loaded
            .files
            .iter()
            .map(|file| file.source.as_str())
            .collect::<Vec<_>>(),
        ["dependency.md", "entry.md"]
    );
    assert_eq!(loaded.files[0].modules.len(), 2);
    assert_eq!(loaded.files[1].modules.len(), 1);
    assert!(has_rule(&loaded, "DEP"));
}
