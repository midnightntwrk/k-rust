use std::collections::BTreeMap;

use indoc::indoc;
use k_rust::definition::Sentence;
use k_rust::diagnostic::{
    DiagnosticCode, DiagnosticPolicy, Severity, WarningCategory, WarningLevel,
};
use k_rust::kast::TermSpan;
use k_rust::outer::{LoadError, LoadOptions, ResolvedSource, load, load_with_options};
use k_rust::provenance::SourceId;
use proptest::prelude::*;

#[derive(Debug)]
#[allow(dead_code)]
struct LoadSummary {
    files: Vec<String>,
    flat_modules: Vec<String>,
    dependency_order: Vec<String>,
    main_priorities: Vec<Vec<Vec<String>>>,
}

#[test]
fn loads_diamond_requires_dependency_first_and_resolves_global_tags() {
    let sources = BTreeMap::from([
        (
            "b.k",
            indoc! {r#"
                requires "d.k"
                module B
                  imports D
                endmodule
            "#},
        ),
        (
            "c.k",
            indoc! {r#"
                requires "d.k"
                module C
                  imports D
                endmodule
            "#},
        ),
        (
            "d.k",
            indoc! {r#"
                module D
                  syntax Exp ::= "foo" [klabel(foo)]
                endmodule
            "#},
        ),
    ]);
    let main_source = indoc! {r#"
        requires "b.k"
        requires "c.k"
        module MAIN
          imports B
          imports C
          syntax Exp ::= "bar" [symbol(bar)]
          syntax priority foo > bar
        endmodule
    "#};
    let mut resolver = |_: &str, required: &str| {
        sources
            .get(required)
            .map(|text| ResolvedSource::new(required, *text))
            .ok_or_else(|| "not found".to_owned())
    };
    let loaded = load(
        ResolvedSource::new("main.k", main_source),
        "MAIN",
        &mut resolver,
    )
    .unwrap();

    let main = loaded.resolved.main_module_id();
    let summary = LoadSummary {
        files: loaded
            .files
            .iter()
            .map(|file| file.source.clone())
            .collect(),
        flat_modules: loaded
            .definition
            .modules
            .iter()
            .map(|module| module.name.clone())
            .collect(),
        dependency_order: loaded
            .resolved
            .dependency_order()
            .iter()
            .map(|id| loaded.resolved.module(*id).name.clone())
            .collect(),
        main_priorities: loaded
            .resolved
            .sentences(main)
            .into_iter()
            .filter_map(|sentence| match sentence {
                k_rust::definition::Sentence::SyntaxPriority { priorities, .. } => {
                    Some(priorities.clone())
                }
                _ => None,
            })
            .collect(),
    };
    insta::with_settings!({
        description => format!("main.k:\n\n{main_source}\n\nRequired sources:\n\n{sources:#?}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(summary);
    });
}

#[test]
fn canonical_source_identity_deduplicates_diamond_leaves() {
    let mut resolutions = 0;
    let mut resolver = |_: &str, required: &str| {
        resolutions += 1;
        match required {
            "left.k" | "right.k" => Ok(ResolvedSource::new(
                "canonical/shared.k",
                "module SHARED endmodule",
            )),
            _ => Err("not found".to_owned()),
        }
    };
    let loaded = load(
        ResolvedSource::new(
            "main.k",
            indoc! {r#"
                requires "left.k"
                requires "right.k"
                module MAIN imports SHARED endmodule
            "#},
        ),
        "MAIN",
        &mut resolver,
    )
    .unwrap();

    assert_eq!(resolutions, 2);
    assert_eq!(
        loaded
            .files
            .iter()
            .map(|file| file.source.as_str())
            .collect::<Vec<_>>(),
        ["canonical/shared.k", "main.k"]
    );
}

#[test]
fn load_time_warnings_fail_the_load_under_warnings_to_errors() {
    let source = indoc! {r#"
        ```{k
        module IGNORED endmodule
        ```

        ```k
        module MAIN endmodule
        ```
    "#};
    let load_with_policy = |diagnostics| {
        let mut resolver = |_: &str, required: &str| Err(format!("unexpected {required}"));
        load_with_options(
            ResolvedSource::new("main.md", source),
            "MAIN",
            &mut resolver,
            &LoadOptions {
                diagnostics,
                ..LoadOptions::default()
            },
        )
    };

    let normal = load_with_policy(DiagnosticPolicy::default()).unwrap();
    assert!(normal.diagnostics.is_empty());

    let all = load_with_policy(DiagnosticPolicy {
        level: WarningLevel::All,
        warnings_to_errors: false,
    })
    .unwrap();
    assert_eq!(all.diagnostics.len(), 1);
    assert_eq!(all.diagnostics[0].code, DiagnosticCode::MarkdownWarning);
    assert_eq!(all.diagnostics[0].severity, Severity::Warning);
    assert_eq!(all.diagnostics[0].source.as_deref(), Some("main.md"));
    assert_eq!(all.diagnostics[0].location.unwrap().start_line, 1);
    assert_eq!(all.diagnostics[0].location.unwrap().start_column, 4);

    let error = load_with_policy(DiagnosticPolicy {
        level: WarningLevel::All,
        warnings_to_errors: true,
    })
    .unwrap_err();
    let LoadError::SourceDiagnostics(diagnostics) = error else {
        panic!("expected upgraded load-time diagnostics, got {error:?}");
    };
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, DiagnosticCode::MarkdownWarning);
    assert_eq!(diagnostics[0].severity, Severity::Error);
}

#[test]
fn legacy_builtin_names_warn_and_rewrite() {
    for (legacy, current) in [
        ("ffi.k", "ffi.md"),
        ("json.k", "json.md"),
        ("rat.k", "rat.md"),
        ("substitution.k", "substitution.md"),
        ("domains.k", "domains.md"),
        ("kast.k", "kast.md"),
    ] {
        let source =
            format!("requires \"{legacy}\"\nmodule MAIN\n  imports LEGACY-BUILTIN\nendmodule\n");
        let mut resolved_name = None;
        let mut resolver = |_: &str, required: &str| {
            resolved_name = Some(required.to_owned());
            Ok(ResolvedSource::new(
                required,
                "```k\nmodule LEGACY-BUILTIN endmodule\n```\n",
            ))
        };
        let loaded = load(
            ResolvedSource::new("main.k", &source),
            "MAIN",
            &mut resolver,
        )
        .unwrap();

        assert_eq!(resolved_name.as_deref(), Some(current));
        let [warning] = loaded.diagnostics.as_slice() else {
            panic!(
                "expected one legacy-requires warning, got {:#?}",
                loaded.diagnostics
            );
        };
        assert_eq!(warning.code, DiagnosticCode::FutureError);
        assert_eq!(
            warning.code.warning_category(),
            Some(WarningCategory::FutureError)
        );
        assert_eq!(warning.severity, Severity::Warning);
        assert_eq!(
            warning.message,
            format!(
                "Requiring a K file in the K builtin directory via a deprecated filename. Please replace \"{legacy}\" with \"{current}\"."
            )
        );
        assert_eq!(warning.source.as_deref(), Some("main.k"));
        assert_eq!(
            warning.location,
            Some(k_rust::definition::Location {
                start_line: 1,
                start_column: 1,
                end_line: 1,
                end_column: u32::try_from(format!("requires \"{legacy}\"").len()).unwrap() + 1,
            })
        );
    }
}

#[test]
fn relocation_preserves_logical_identity() {
    fn load_at(root: &str) -> k_rust::outer::LoadedDefinition {
        let source = "module MAIN\n  syntax Value ::= \"value\"\nendmodule\n";
        let mut resolver = |_: &str, required: &str| Err(format!("unexpected {required}"));
        load_with_options(
            ResolvedSource::new(format!("{root}/src/main.k"), source),
            "MAIN",
            &mut resolver,
            &LoadOptions {
                project_root: Some(root.into()),
                ..LoadOptions::default()
            },
        )
        .unwrap()
    }

    let first = load_at("/checkout/first");
    let second = load_at("/relocated/second");

    assert_eq!(first.source_table, second.source_table);
    assert_eq!(first.source_table.offset_map(SourceId(0)), None);
    assert_eq!(
        first.source_table.raw_range(TermSpan {
            source: SourceId(0),
            start: 0,
            end: 6,
        }),
        Some(0..6),
    );
    let identity = first.source_table.iter().next().unwrap();
    assert_eq!(identity.logical, "src/main.k");
    assert_eq!(
        identity.resolve_under("/checkout/first"),
        std::path::PathBuf::from("/checkout/first/src/main.k"),
    );
    assert_eq!(
        identity.resolve_under("/relocated/second"),
        std::path::PathBuf::from("/relocated/second/src/main.k"),
    );
}

#[test]
fn applies_imported_sort_synonyms_after_resolving_the_source_graph() {
    let mut resolver = |_: &str, required: &str| match required {
        "base.k" => Ok(ResolvedSource::new(
            "base.k",
            indoc! {r#"
                module BASE
                  syntax Alias = Exp
                endmodule
            "#},
        )),
        _ => Err("not found".to_owned()),
    };
    let loaded = load(
        ResolvedSource::new(
            "main.k",
            indoc! {r#"
                requires "base.k"
                module MAIN
                  imports BASE
                  syntax Alias ::= "wrap" Alias [klabel(wrap)]
                endmodule
            "#},
        ),
        "MAIN",
        &mut resolver,
    )
    .unwrap();

    let flat_main = loaded.definition.main_module().unwrap();
    let Sentence::Production { sort, items, .. } = &flat_main.local_sentences[0] else {
        panic!("expected production")
    };
    assert_eq!(sort, &k_rust::kast::Sort::new("Exp"));
    assert!(matches!(
        &items[1],
        k_rust::definition::ProductionItem::NonTerminal { sort, .. }
            if sort == &k_rust::kast::Sort::new("Exp")
    ));

    let resolved_main = loaded.resolved.main_module();
    let Sentence::Production { sort, .. } = &resolved_main.local_sentences[0] else {
        panic!("expected production")
    };
    assert_eq!(sort, &k_rust::kast::Sort::new("Exp"));
}

#[test]
fn parses_and_expands_configurations_with_visible_user_syntax() {
    let source = indoc! {r#"
        module MAIN
          syntax K
          syntax Map
          syntax Int ::= r"[0-9]+" [token]
          configuration <top><k> $PGM:Int </k><counter> 0 </counter></top>
        endmodule
    "#};
    let mut resolver = |_: &str, _: &str| Err("not found".to_owned());
    let loaded = load(ResolvedSource::new("main.k", source), "MAIN", &mut resolver).unwrap();

    let sentences = &loaded.definition.main_module().unwrap().local_sentences;
    assert!(
        !sentences
            .iter()
            .any(|sentence| matches!(sentence, Sentence::Configuration { .. }))
    );
    let labels = sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                label: Some(label), ..
            } => Some(label.name.as_str()),
            _ => None,
        })
        .collect::<Vec<_>>();
    insta::with_settings!({
        description => format!("main.k:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(labels);
    });
}

#[test]
fn imports_the_default_configuration_and_map_module_implicitly() {
    let implicit = indoc! {r#"
        module MAP
          syntax Map
        endmodule

        module DEFAULT-CONFIGURATION
          syntax K
          configuration <k> $PGM:K </k>
        endmodule
    "#};
    let entry = "module MAIN endmodule";
    let mut resolver = |_: &str, _: &str| Err("not found".to_owned());
    let loaded = load_with_options(
        ResolvedSource::new("main.k", entry),
        "MAIN",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![ResolvedSource::new("prelude.k", implicit)],
            ..LoadOptions::default()
        },
    )
    .expect("implicit configuration should load");

    let main = loaded
        .definition
        .modules
        .iter()
        .find(|module| module.name == "MAIN")
        .expect("main module should exist");
    assert!(
        main.imports
            .iter()
            .any(|import| { import.name == "DEFAULT-CONFIGURATION" && import.public })
    );

    let default_configuration = loaded
        .definition
        .modules
        .iter()
        .find(|module| module.name == "DEFAULT-CONFIGURATION")
        .expect("default configuration module should exist");
    assert!(
        default_configuration
            .imports
            .iter()
            .any(|import| import.name == "MAP" && import.public)
    );
    assert!(!default_configuration.local_sentences.iter().any(|sentence| {
        matches!(sentence, Sentence::Configuration { .. })
            || matches!(sentence, Sentence::Bubble { sentence_type, .. } if sentence_type == "config")
    }));
}

#[test]
fn imports_default_configuration_into_distinct_configuration_module() {
    let implicit = indoc! {r#"
        module DEFAULT-CONFIGURATION
          syntax K
          syntax Map
          configuration <k> $PGM:K </k>
        endmodule
    "#};
    let entry = indoc! {"
        module SEMANTICS
        endmodule

        module SPEC
          imports SEMANTICS
        endmodule
    "};
    let mut resolver = |_: &str, _: &str| Err("not found".to_owned());
    let loaded = load_with_options(
        ResolvedSource::new("spec.k", entry),
        "SPEC",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![ResolvedSource::new("prelude.k", implicit)],
            configuration_module: Some("SEMANTICS".into()),
            ..LoadOptions::default()
        },
    )
    .expect("implicit configuration should attach to the semantics module");

    let semantics = loaded
        .definition
        .modules
        .iter()
        .find(|module| module.name == "SEMANTICS")
        .expect("semantics module should exist");
    assert!(
        semantics
            .imports
            .iter()
            .any(|import| import.name == "DEFAULT-CONFIGURATION" && import.public)
    );
}

macro_rules! load_error_snapshot {
    ($name:ident, $entry:expr, $sources:expr, $main:expr) => {
        #[test]
        fn $name() {
            let entry = $entry;
            let main = $main;
            let sources: BTreeMap<&str, &str> = BTreeMap::from($sources);
            let mut resolver = |_: &str, required: &str| {
                sources
                    .get(required)
                    .map(|text| ResolvedSource::new(required, *text))
                    .ok_or_else(|| format!("{required} was not found"))
            };
            let error = load(ResolvedSource::new("main.k", entry), main, &mut resolver).unwrap_err();
            insta::with_settings!({
                description => format!(
                    "main.k:\n\n{entry}\n\nRequired sources:\n\n{sources:#?}\n\nMain module: {main}"
                ),
                omit_expression => true,
                prepend_module_to_snapshot => true,
            }, {
                insta::assert_debug_snapshot!(error);
            });
        }
    };
}

load_error_snapshot!(
    missing_required_source,
    "requires \"missing.k\"",
    [],
    "MAIN"
);

#[test]
fn deduplicates_mutual_requires_cycles_dependency_first() {
    let sources = BTreeMap::from([
        (
            "body.k",
            indoc! {r#"
                requires "lib.k"
                module BODY endmodule
            "#},
        ),
        (
            "lib.k",
            indoc! {r#"
                requires "body.k"
                module LIB endmodule
            "#},
        ),
    ]);
    let entry = indoc! {r#"
        requires "lib.k"
        module MAIN
          imports LIB
          imports BODY
        endmodule
    "#};
    let mut resolver = |_: &str, required: &str| {
        sources
            .get(required)
            .map(|text| ResolvedSource::new(required, *text))
            .ok_or_else(|| "not found".to_owned())
    };

    let loaded = load(ResolvedSource::new("main.k", entry), "MAIN", &mut resolver)
        .expect("requires cycles should be de-duplicated like the reference frontend");

    assert_eq!(
        loaded
            .files
            .iter()
            .map(|file| file.source.as_str())
            .collect::<Vec<_>>(),
        ["body.k", "lib.k", "main.k"]
    );
}

load_error_snapshot!(
    duplicate_modules_across_sources,
    indoc! {r#"
        requires "other.k"
        module SAME endmodule
    "#},
    [("other.k", "module SAME endmodule")],
    "SAME"
);

load_error_snapshot!(
    missing_main_module,
    "module PRESENT endmodule",
    [],
    "MISSING"
);

load_error_snapshot!(
    missing_imported_module,
    "module MAIN imports ABSENT endmodule",
    [],
    "MAIN"
);

load_error_snapshot!(
    malformed_configuration,
    indoc! {r#"
        module MAIN
          configuration <k> @@@ </k>
        endmodule
    "#},
    [],
    "MAIN"
);

#[test]
fn source_checks_precede_import_resolution() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "(" Int ")" [bracket]
        endmodule
    "#};
    let mut resolver = |_: &str, _: &str| Err("not found".to_owned());
    let error = load(ResolvedSource::new("main.k", source), "MAIN", &mut resolver).unwrap_err();
    assert!(matches!(error, LoadError::SourceDiagnostics(_)));
    insta::with_settings!({
        description => format!("main.k:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(error);
    });
}

#[test]
fn reference_load_rejects_undefined_sorts_and_duplicate_user_lists() {
    let cases = [
        (
            "undefined-sort/test.k",
            include_str!("fixtures/reference/outer/undefined-sort/test.k"),
            "UNDEFINED-SORT",
            "Could not find sorts: [Bar]",
        ),
        (
            "undefined-sort-unrelated/test.k",
            include_str!("fixtures/reference/outer/undefined-sort-unrelated/test.k"),
            "UNDEFINED-SORT-UNRELATED",
            "Could not find sorts: [Bar]",
        ),
        (
            "duplicate-user-list/test.k",
            include_str!("fixtures/reference/outer/duplicate-user-list/test.k"),
            "DUPLICATE-USER-LIST",
            "Sort Es previously declared as a user list at ",
        ),
    ];

    for (source_name, source, main_module, expected) in cases {
        let mut resolver = |_: &str, required: &str| Err(format!("unexpected {required}"));
        let error = load(
            ResolvedSource::new(source_name, source),
            main_module,
            &mut resolver,
        )
        .unwrap_err();
        let LoadError::SourceDiagnostics(diagnostics) = error else {
            panic!("expected source diagnostics for {source_name}, got {error:?}");
        };
        assert!(
            diagnostics.iter().any(|diagnostic| {
                diagnostic.message.starts_with(expected)
                    && diagnostic.source.as_deref() == Some(source_name)
                    && diagnostic.location.is_some()
            }),
            "{source_name}: {diagnostics:#?}"
        );
    }
}

#[test]
fn temporary_cell_sort_declarations_are_removed_after_expansion() {
    let source = indoc! {r#"
        module CHECKCELLSORTDECLOK-SYNTAX
          syntax K
          syntax Map
          syntax Pgm
        endmodule

        module CHECKCELLSORTDECLOK
          imports CHECKCELLSORTDECLOK-SYNTAX
          configuration <T> <k> $PGM:Pgm </k> </T>
          syntax Pgm ::= KCell
        endmodule
    "#};
    let mut resolver = |_: &str, required: &str| Err(format!("unexpected {required}"));
    let loaded = load(
        ResolvedSource::new("checkCellSortDeclOK.k", source),
        "CHECKCELLSORTDECLOK",
        &mut resolver,
    )
    .unwrap();

    assert!(loaded.definition.modules.iter().all(|module| {
        module.local_sentences.iter().all(|sentence| {
            !matches!(sentence, Sentence::SyntaxSort { attributes, .. }
                if attributes.get("temporary-cell-sort-decl").is_some())
        })
    }));
}

#[test]
fn load_rechecks_sorts_after_configuration_expansion() {
    let source = indoc! {r#"
        module CHECKCELLSORTDECLFAIL-SYNTAX
          syntax K
          syntax Map
          syntax Pgm
        endmodule

        module CHECKCELLSORTDECLFAIL
          imports CHECKCELLSORTDECLFAIL-SYNTAX
          configuration <T> <k> $PGM:Pgm </k> </T>
          syntax Pgm ::= MisTypedCell
        endmodule
    "#};
    let mut resolver = |_: &str, required: &str| Err(format!("unexpected {required}"));
    let error = load(
        ResolvedSource::new("checkCellSortDeclFail.k", source),
        "CHECKCELLSORTDECLFAIL",
        &mut resolver,
    )
    .unwrap_err();
    let LoadError::SourceDiagnostics(diagnostics) = error else {
        panic!("expected source diagnostics, got {error:?}");
    };

    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message == "Could not find sorts: [MisTypedCell]"
            && diagnostic.source.as_deref() == Some("checkCellSortDeclFail.k")
            && diagnostic.location.is_some()
    }));
}

proptest! {
    #[test]
    fn arbitrary_entry_source_never_panics(source in any::<String>()) {
        let mut resolver = |_: &str, required: &str| Err(format!("missing {required}"));
        let _ = load(ResolvedSource::new("fuzz.k", source), "FUZZ", &mut resolver);
    }
}
