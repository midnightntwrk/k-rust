use std::collections::BTreeMap;

use indoc::indoc;
use k_rust::definition::{ProductionItem, Sentence};
use k_rust::diagnostic::{
    Diagnostic, DiagnosticCode, DiagnosticPolicy, Severity, WarningCategory, WarningLevel,
};
use k_rust::kast::TermSpan;
use k_rust::outer::{
    LoadError, LoadOptions, ResolvedSource, load, load_with_options, load_with_prepared_base,
    prepared_module_declarations,
};
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
fn bison_lists_orient_only_outer_user_list_sugar() {
    for separator in [",", ""] {
        let source = format!(
            r#"
module LISTS
  syntax Element ::= "e" [token]
  syntax Elements ::= NeList{{Element, "{separator}"}} [symbol(elements)]
endmodule
"#
        );
        let load = |bison_lists| {
            let mut resolver = |_: &str, _: &str| Err("not found".to_owned());
            load_with_options(
                ResolvedSource::new("lists.k", source.clone()),
                "LISTS",
                &mut resolver,
                &LoadOptions {
                    bison_lists,
                    ..LoadOptions::default()
                },
            )
            .unwrap()
        };
        let default = load(false);
        let bison = load(true);
        let recursive = |loaded: &k_rust::outer::LoadedDefinition| {
            loaded
                .definition()
                .main_module()
                .unwrap()
                .local_sentences
                .iter()
                .find(|sentence| {
                    matches!(&***sentence, Sentence::Production { items, attributes, .. }
                        if attributes.get_str("userList") == Some("+")
                            && items.iter().filter(|item| matches!(item, ProductionItem::NonTerminal { .. })).count() == 2)
                })
                .unwrap()
                .clone()
        };
        let default = recursive(&default);
        let bison = recursive(&bison);
        let Sentence::Production {
            label: default_label,
            parameters: default_parameters,
            items: default_items,
            attributes: default_attributes,
            ..
        } = &*default
        else {
            unreachable!()
        };
        let Sentence::Production {
            label: bison_label,
            parameters: bison_parameters,
            items: bison_items,
            attributes: bison_attributes,
            ..
        } = &*bison
        else {
            unreachable!()
        };
        let nonterminals = |items: Vec<ProductionItem>| {
            items
                .into_iter()
                .filter_map(|item| match item {
                    ProductionItem::NonTerminal { sort, .. } => Some(sort.name),
                    _ => None,
                })
                .collect::<Vec<_>>()
        };

        assert_eq!(
            nonterminals(default_items.to_vec()),
            ["Element", "Elements"]
        );
        assert_eq!(nonterminals(bison_items.to_vec()), ["Elements", "Element"]);
        assert_eq!(bison_label, default_label);
        assert_eq!(bison_parameters, default_parameters);
        assert_eq!(bison_attributes, default_attributes);
    }
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

    let main = loaded.resolved().main_module_id();
    let summary = LoadSummary {
        files: loaded
            .files()
            .iter()
            .map(|file| file.source.clone())
            .collect(),
        flat_modules: loaded
            .definition()
            .modules
            .iter()
            .map(|module| module.name.clone())
            .collect(),
        dependency_order: loaded
            .resolved()
            .dependency_order()
            .iter()
            .map(|id| loaded.resolved().module(*id).name.clone())
            .collect(),
        main_priorities: loaded
            .resolved()
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
            .files()
            .iter()
            .map(|file| file.source.as_str())
            .collect::<Vec<_>>(),
        ["canonical/shared.k", "main.k"]
    );
}

#[cfg(feature = "cli")]
#[test]
fn equivalent_duplicate_modules_accept_native_file_copies() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/reference/outer/equivalent-duplicate-module-copy");
    let mut resolver =
        k_rust::native::FileResolver::new(&root, std::iter::empty::<std::path::PathBuf>());
    let entry = resolver.load_entry(root.join("main.k")).unwrap();
    let loaded = load(entry, "MAIN", &mut resolver).unwrap();

    assert_eq!(
        loaded
            .definition()
            .modules
            .iter()
            .filter(|module| module.name == "SHARED")
            .count(),
        1
    );
    assert!(
        loaded
            .definition()
            .modules
            .iter()
            .any(|module| module.name == "SIBLING")
    );
    assert_eq!(loaded.files().len(), 3);
}

#[test]
fn equivalent_duplicate_modules_retain_sources_siblings_and_first_provenance() {
    let left = indoc! {r#"
        module SHARED
          syntax Value ::= "value" [symbol(value), unused]
        endmodule
    "#};
    let right = indoc! {r#"
        module SHARED
        syntax   Value::=   "value" [unused(), symbol(value)]
        endmodule

        module SIBLING endmodule
    "#};
    let sources = BTreeMap::from([("left/shared.k", left), ("right/shared.k", right)]);
    let mut resolver = |_: &str, required: &str| {
        sources
            .get(required)
            .map(|text| ResolvedSource::new(required, *text))
            .ok_or_else(|| "not found".to_owned())
    };
    let loaded = load(
        ResolvedSource::new(
            "main.k",
            indoc! {r#"
                requires "left/shared.k"
                requires "right/shared.k"
                module MAIN
                  imports SHARED
                  imports SIBLING
                endmodule
            "#},
        ),
        "MAIN",
        &mut resolver,
    )
    .unwrap();

    let shared = loaded
        .definition()
        .modules
        .iter()
        .filter(|module| module.name == "SHARED")
        .collect::<Vec<_>>();
    assert_eq!(shared.len(), 1);
    assert_eq!(shared[0].attributes.source(), Some("left/shared.k"));
    assert_eq!(
        shared[0].attributes.source_id(),
        Some(loaded.files()[0].source_id)
    );
    assert!(
        loaded
            .definition()
            .modules
            .iter()
            .any(|module| module.name == "SIBLING")
    );
    assert_eq!(
        loaded
            .files()
            .iter()
            .map(|file| file.source.as_str())
            .collect::<Vec<_>>(),
        ["left/shared.k", "right/shared.k", "main.k"]
    );
    assert_eq!(loaded.files()[1].modules.len(), 2);
    assert_eq!(loaded.source_table().iter().len(), 3);
}

#[test]
fn equivalent_duplicate_modules_follow_kil_sort_synonym_content() {
    let sources = BTreeMap::from([
        (
            "left/shared.k",
            "module SHARED\n  syntax {A} New = Old\nendmodule",
        ),
        (
            "right/shared.k",
            "module SHARED\n  syntax {B} New = Old\nendmodule",
        ),
    ]);
    let mut resolver = |_: &str, required: &str| {
        sources
            .get(required)
            .map(|text| ResolvedSource::new(required, *text))
            .ok_or_else(|| "not found".to_owned())
    };
    let loaded = load(
        ResolvedSource::new(
            "main.k",
            indoc! {r#"
                requires "left/shared.k"
                requires "right/shared.k"
                module MAIN imports SHARED endmodule
            "#},
        ),
        "MAIN",
        &mut resolver,
    )
    .unwrap();

    assert_eq!(
        loaded
            .definition()
            .modules
            .iter()
            .filter(|module| module.name == "SHARED")
            .count(),
        1
    );
}

#[test]
fn duplicate_modules_distinguish_named_regular_syntax_declarations() {
    let sources = BTreeMap::from([
        (
            "left/shared.k",
            "module SHARED\n  syntax foo:Sort ::= \"x\"\nendmodule",
        ),
        (
            "right/shared.k",
            "module SHARED\n  syntax bar:Sort ::= \"x\"\nendmodule",
        ),
    ]);
    let mut resolver = |_: &str, required: &str| {
        sources
            .get(required)
            .map(|text| ResolvedSource::new(required, *text))
            .ok_or_else(|| "not found".to_owned())
    };
    let error = load(
        ResolvedSource::new(
            "main.k",
            indoc! {r#"
                requires "left/shared.k"
                requires "right/shared.k"
                module MAIN endmodule
            "#},
        ),
        "MAIN",
        &mut resolver,
    )
    .unwrap_err();

    assert_eq!(
        error,
        LoadError::DuplicateModule {
            name: "SHARED".into(),
            first_source: "left/shared.k".into(),
            second_source: "right/shared.k".into(),
        }
    );
}

#[test]
fn duplicate_modules_reject_each_changed_equivalence_component() {
    let cases = [
        (
            "right/copied.k",
            "module SHARED endmodule",
            "module SHARED endmodule",
        ),
        (
            "right/shared.k",
            "module SHARED endmodule",
            "\nmodule SHARED endmodule",
        ),
        (
            "right/shared.k",
            "module SHARED\n  syntax A\nendmodule",
            "module SHARED\n  syntax B\nendmodule",
        ),
    ];
    for (second_source, first_text, second_text) in cases {
        let sources = BTreeMap::from([("left/shared.k", first_text), (second_source, second_text)]);
        let mut resolver = |_: &str, required: &str| {
            sources
                .get(required)
                .map(|text| ResolvedSource::new(required, *text))
                .ok_or_else(|| "not found".to_owned())
        };
        let entry = format!(
            "requires \"left/shared.k\"\nrequires \"{second_source}\"\nmodule MAIN endmodule"
        );
        let error = load(ResolvedSource::new("main.k", entry), "MAIN", &mut resolver).unwrap_err();
        assert_eq!(
            error,
            LoadError::DuplicateModule {
                name: "SHARED".into(),
                first_source: "left/shared.k".into(),
                second_source: second_source.into(),
            }
        );
    }
}

#[test]
fn duplicate_modules_reject_a_changed_third_declaration() {
    let sources = BTreeMap::from([
        ("left/shared.k", "module SHARED endmodule"),
        ("middle/shared.k", "module SHARED endmodule"),
        ("right/shared.k", "module SHARED [private] endmodule"),
    ]);
    let mut resolver = |_: &str, required: &str| {
        sources
            .get(required)
            .map(|text| ResolvedSource::new(required, *text))
            .ok_or_else(|| "not found".to_owned())
    };
    let error = load(
        ResolvedSource::new(
            "main.k",
            indoc! {r#"
                requires "left/shared.k"
                requires "middle/shared.k"
                requires "right/shared.k"
                module MAIN endmodule
            "#},
        ),
        "MAIN",
        &mut resolver,
    )
    .unwrap_err();

    assert_eq!(
        error,
        LoadError::DuplicateModule {
            name: "SHARED".into(),
            first_source: "left/shared.k".into(),
            second_source: "right/shared.k".into(),
        }
    );
}

#[test]
fn prepared_markdown_sources_are_reread_and_compared_under_the_current_selector() {
    let definition = indoc! {r#"
        ```k
        module TEST
          syntax Value ::= "k" [symbol(kValue)]
        ```
        ```keep
          syntax Value ::= "keep" [symbol(keepValue)]
        ```
        ```k
        endmodule
        ```
    "#};
    let specification = indoc! {r#"
        ```k
        requires "test.md"
        module SPEC imports TEST endmodule
        ```
    "#};
    let combined = LoadOptions {
        markdown_selector: "k|keep".into(),
        ..LoadOptions::default()
    };
    let mut no_requires = |_: &str, required: &str| Err(format!("unexpected {required}"));
    let base = load_with_options(
        ResolvedSource::new("test.md", definition),
        "TEST",
        &mut no_requires,
        &combined,
    )
    .unwrap();
    let declarations = prepared_module_declarations(base.files(), base.definition());
    let provided = vec!["test.md".to_owned()];
    let prepared = k_rust::definition::json::ProvenanceDefinition {
        definition: base.definition().clone(),
        source_table: base.source_table().clone(),
    };

    let load_spec = |selector: &str| {
        let mut resolver = |_: &str, required: &str| match required {
            "test.md" => Ok(ResolvedSource::new("test.md", definition)),
            _ => Err(format!("unexpected {required}")),
        };
        load_with_prepared_base(
            ResolvedSource::new("spec.md", specification),
            "SPEC",
            &mut resolver,
            &LoadOptions {
                markdown_selector: selector.into(),
                ..LoadOptions::default()
            },
            &prepared,
            &provided,
            &declarations,
        )
    };

    let same = load_spec("k|keep").unwrap();
    assert!(
        same.definition()
            .modules
            .iter()
            .any(|module| module.name == "TEST")
    );
    assert!(
        same.definition()
            .modules
            .iter()
            .any(|module| module.name == "SPEC")
    );
    // The base's term spans index its own table, so the loaded table extends it unchanged: the
    // re-read, byte-identical `test.md` keeps its identity and offset map, and `spec.md` follows.
    let base_sources = base.source_table().iter().cloned().collect::<Vec<_>>();
    let loaded_sources = same.source_table().iter().cloned().collect::<Vec<_>>();
    assert_eq!(loaded_sources[..base_sources.len()], base_sources[..]);
    assert_eq!(loaded_sources.len(), base_sources.len() + 1);
    assert_eq!(loaded_sources.last().unwrap().logical, "spec.md");
    for index in 0..base_sources.len() {
        let id = k_rust::provenance::SourceId(index);
        assert_eq!(
            same.source_table().offset_map(id),
            base.source_table().offset_map(id)
        );
    }

    let error = load_spec("k").unwrap_err();
    assert!(matches!(
        error,
        LoadError::PreparedModuleMismatch {
            ref name,
            ref first_source,
            ref second_source,
            ..
        } if name == "TEST" && first_source == "test.md" && second_source == "test.md"
    ));
    assert!(
        error
            .to_string()
            .contains("This can happen if --md-selector differs for kompile and kprove")
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
    assert!(normal.diagnostics().is_empty());

    let all = load_with_policy(DiagnosticPolicy {
        level: WarningLevel::All,
        warnings_to_errors: false,
    })
    .unwrap();
    assert_eq!(all.diagnostics().len(), 1);
    assert_eq!(all.diagnostics()[0].code, DiagnosticCode::MarkdownWarning);
    assert_eq!(all.diagnostics()[0].severity, Severity::Warning);
    assert_eq!(all.diagnostics()[0].source.as_deref(), Some("main.md"));
    assert_eq!(all.diagnostics()[0].location.unwrap().start_line, 1);
    assert_eq!(all.diagnostics()[0].location.unwrap().start_column, 4);

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
fn configuration_collection_warnings_follow_the_load_policy() {
    let source = indoc! {r#"
        module MAIN
          configuration
            <top><bad multiplicity="*" type="Set"> $FOO </bad></top>
        endmodule
    "#};
    let mut resolver = |_: &str, required: &str| Err(format!("unexpected {required}"));
    let error = load_with_options(
        ResolvedSource::new("config.k", source),
        "MAIN",
        &mut resolver,
        &LoadOptions {
            diagnostics: DiagnosticPolicy {
                level: WarningLevel::All,
                warnings_to_errors: true,
            },
            ..LoadOptions::default()
        },
    )
    .unwrap_err();
    let LoadError::SourceDiagnostics(diagnostics) = error else {
        panic!("expected upgraded configuration warning, got {error:?}");
    };
    let collection = diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.code == DiagnosticCode::CellCollectionVarWithoutInitial)
        .collect::<Vec<_>>();
    assert_eq!(collection.len(), 1, "{diagnostics:#?}");
    assert_eq!(collection[0].severity, Severity::Error);
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
        let [warning] = loaded.diagnostics() else {
            panic!(
                "expected one legacy-requires warning, got {:#?}",
                loaded.diagnostics()
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

    assert_eq!(first.source_table(), second.source_table());
    assert_eq!(first.source_table().offset_map(SourceId(0)), None);
    assert_eq!(
        first.source_table().raw_range(TermSpan {
            source: SourceId(0),
            start: 0,
            end: 6,
        }),
        Some(0..6),
    );
    let identity = first.source_table().iter().next().unwrap();
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

    let flat_main = loaded.definition().main_module().unwrap();
    let Sentence::Production { sort, items, .. } = &*flat_main.local_sentences[0] else {
        panic!("expected production")
    };
    assert_eq!(sort, &k_rust::kast::Sort::new("Exp"));
    assert!(matches!(
        &items[1],
        k_rust::definition::ProductionItem::NonTerminal { sort, .. }
            if sort == &k_rust::kast::Sort::new("Exp")
    ));

    let resolved_main = loaded.resolved().main_module();
    let Sentence::Production { sort, .. } = &*resolved_main.local_sentences[0] else {
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

    let sentences = &loaded.definition().main_module().unwrap().local_sentences;
    assert!(
        !sentences
            .iter()
            .any(|sentence| matches!(&**sentence, Sentence::Configuration { .. }))
    );
    let labels = sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
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
        .definition()
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
        .definition()
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
        matches!(&**sentence, Sentence::Configuration { .. })
            || matches!(&**sentence, Sentence::Bubble { sentence_type, .. } if sentence_type == "config")
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
        .definition()
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
            .files()
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
fn fu19_standalone_schematic_declaration_supplies_an_operand_head() {
    let source = indoc! {r#"
        module MAIN
          syntax {W} MInt{W}
          syntax {W} Foo ::= f(MInt{W}) [symbol(f)]
        endmodule
    "#};
    let mut resolver = |_: &str, required: &str| Err(format!("unexpected {required}"));
    load(ResolvedSource::new("main.k", source), "MAIN", &mut resolver).unwrap();
}

#[test]
fn fu19_standalone_ground_declaration_with_an_unused_binder_supplies_an_operand_instance() {
    let source = indoc! {r#"
        module MAIN
          syntax {W} MInt{8}
          syntax Foo ::= f(MInt{8}) [symbol(f)]
        endmodule
    "#};
    let mut resolver = |_: &str, required: &str| Err(format!("unexpected {required}"));
    load(ResolvedSource::new("main.k", source), "MAIN", &mut resolver).unwrap();
}

#[test]
fn fu19_standalone_nullary_declaration_with_an_unused_binder_supplies_an_operand_sort() {
    let source = indoc! {r#"
        module MAIN
          syntax {W} Foo
          syntax Bar ::= f(Foo) [symbol(f)]
        endmodule
    "#};
    let mut resolver = |_: &str, required: &str| Err(format!("unexpected {required}"));
    load(ResolvedSource::new("main.k", source), "MAIN", &mut resolver).unwrap();
}

#[test]
fn fu19_standalone_registration_preserves_undefined_and_unsupported_sort_diagnostics() {
    for (source, code, line, message) in [
        (
            indoc! {r#"
                module MAIN
                  syntax {W} MInt{W}
                  syntax Foo ::= f(MInt{8}) [symbol(f)]
                endmodule
            "#},
            DiagnosticCode::UndefinedSort,
            3,
            "Could not find sorts: [MInt{8}]",
        ),
        (
            indoc! {r#"
                module MAIN
                  syntax Foo ::= f(Unknown) [symbol(f)]
                endmodule
            "#},
            DiagnosticCode::UndefinedSort,
            2,
            "Could not find sorts: [Unknown]",
        ),
        (
            indoc! {r#"
                module MAIN
                  syntax {S} Box{S}
                endmodule
            "#},
            DiagnosticCode::UnsupportedParametricSort,
            2,
            "User-defined parametric sorts are currently unsupported: Box{S}",
        ),
        (
            indoc! {r#"
                module MAIN
                  syntax {W} MInt{MInt{W}}
                endmodule
            "#},
            DiagnosticCode::UnsupportedParametricSort,
            2,
            "Nested parametric sorts are currently unsupported: MInt{MInt{W}}",
        ),
    ] {
        let mut resolver = |_: &str, required: &str| Err(format!("unexpected {required}"));
        let error = load(ResolvedSource::new("main.k", source), "MAIN", &mut resolver).unwrap_err();
        let LoadError::SourceDiagnostics(diagnostics) = error else {
            panic!("expected source diagnostics, got {error:?}");
        };
        let errors = diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.severity == Severity::Error)
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), 1, "{diagnostics:#?}");
        let diagnostic = errors[0];
        assert_eq!(diagnostic.code, code, "{diagnostics:#?}");
        assert_eq!(diagnostic.message, message);
        assert_eq!(diagnostic.source.as_deref(), Some("main.k"));
        assert_eq!(diagnostic.location.unwrap().start_line, line);
    }
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

    assert!(loaded.definition().modules.iter().all(|module| {
        module.local_sentences.iter().all(|sentence| {
            !matches!(&**sentence, Sentence::SyntaxSort { attributes, .. }
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

/// Load `source` as `main.k` with the embedded prelude as its implicit source.
fn load_with_prelude(
    source: &str,
    main_module: &str,
) -> Result<k_rust::outer::LoadedDefinition, LoadError> {
    let prelude = k_rust::builtin::embedded("prelude.md").expect("embedded prelude should exist");
    let mut resolver = |_: &str, required: &str| {
        k_rust::builtin::embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    load_with_options(
        ResolvedSource::new("main.k", source.to_owned()),
        main_module,
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![prelude],
            ..LoadOptions::default()
        },
    )
}

/// The single `KernelSortPosition` error the load of `source` fails with, after checking that it
/// is an error on line `line` of `main.k` and that it names `cycle`.
fn kernel_sort_position_error(
    source: &str,
    main_module: &str,
    line: u32,
    cycle: &str,
) -> Diagnostic {
    let Err(error) = load_with_prelude(source, main_module) else {
        panic!("{main_module} loads, but its declared subsorts contradict a kernel position");
    };
    let LoadError::SourceDiagnostics(diagnostics) = error else {
        panic!("expected source diagnostics, got {error:?}");
    };
    let mut kernel = diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.code == DiagnosticCode::KernelSortPosition)
        .cloned()
        .collect::<Vec<_>>();
    assert_eq!(kernel.len(), 1, "{diagnostics:#?}");
    let diagnostic = kernel.pop().expect("one diagnostic");
    assert_eq!(diagnostic.severity, Severity::Error);
    assert_eq!(diagnostic.source.as_deref(), Some("main.k"));
    let location = diagnostic.location.expect("the diagnostic has a location");
    assert_eq!(location.start_line, line, "{diagnostic:#?}");
    assert!(
        diagnostic
            .message
            .contains(&format!("closing the cycle {cycle}:")),
        "{diagnostic:#?}"
    );
    diagnostic
}

/// Load `source`, which states no kernel-position contradiction, and check that it loads.
fn assert_loads_without_kernel_sort_position(source: &str, main_module: &str) {
    let loaded = load_with_prelude(source, main_module)
        .unwrap_or_else(|error| panic!("{main_module} loads: {error:?}"));
    assert!(
        loaded
            .diagnostics()
            .iter()
            .all(|diagnostic| diagnostic.code != DiagnosticCode::KernelSortPosition),
        "{:#?}",
        loaded.diagnostics()
    );
}

const C1_WITHOUT_ITS_CONTRADICTION: &str = indoc! {r#"
    module C1
      imports BASIC-K
      syntax Exp ::= "a" | "b" | f(Exp) [function]
      rule f(X) => X
      configuration <k> $PGM:Exp </k>
    endmodule
"#};

#[test]
fn a_sort_of_k_items_declared_above_kitem_is_rejected_at_load_before_any_bubble() {
    let source = indoc! {r#"
        module C1
          imports BASIC-K
          syntax Exp ::= "a" | "b" | f(Exp) [function]
          syntax Exp ::= KItem
          rule f(X) => X
          configuration <k> $PGM:Exp </k>
        endmodule
    "#};
    let diagnostic = kernel_sort_position_error(source, "C1", 4, "KItem < Exp < KItem");
    assert!(
        diagnostic
            .message
            .contains("KItem < Exp is declared by `syntax Exp ::= KItem`"),
        "{diagnostic:#?}"
    );
    assert!(
        diagnostic
            .message
            .contains("Exp < KItem because every Exp is a KItem"),
        "{diagnostic:#?}"
    );
}

#[test]
fn a_sort_of_k_items_declared_above_kitem_is_rejected_without_a_bubble() {
    let source = indoc! {r#"
        module C3
          imports BASIC-K
          syntax Exp ::= "a" | "b"
          syntax Exp ::= KItem
        endmodule
    "#};
    kernel_sort_position_error(source, "C3", 4, "KItem < Exp < KItem");
}

#[test]
fn a_sort_a_variable_stands_at_declared_below_kbott_is_rejected_at_load() {
    let source = indoc! {r#"
        module C5
          imports BASIC-K
          syntax Exp ::= "a" | "b"
          syntax KBott ::= Exp
          configuration <k> $PGM:Exp </k>
        endmodule
    "#};
    let diagnostic = kernel_sort_position_error(source, "C5", 4, "Exp < KBott < Exp");
    assert!(
        diagnostic
            .message
            .contains("Exp < KBott is declared by `syntax KBott ::= Exp`; KBott < Exp because a variable may stand at Exp"),
        "{diagnostic:#?}"
    );
}

#[test]
fn a_contradiction_declared_in_an_import_is_reported_once_on_its_declaration() {
    let source = indoc! {r#"
        module A
          imports BASIC-K
          syntax Exp ::= "a" | "b"
          syntax Exp ::= K
        endmodule

        module MAIN
          imports A
          syntax Stmt ::= Exp
        endmodule
    "#};
    // Line 4 is A's `syntax Exp ::= K`; MAIN's view repeats the contradiction and is not reported
    // again.
    let diagnostic = kernel_sort_position_error(source, "MAIN", 4, "KItem < K < Exp < KItem");
    assert!(
        diagnostic
            .message
            .contains("K < Exp is declared by `syntax Exp ::= K`"),
        "{diagnostic:#?}"
    );
}

#[test]
fn a_contradiction_declared_in_an_import_is_not_repeated_by_importers_that_extend_its_sort() {
    let source = indoc! {r#"
        module A
          imports BASIC-K
          syntax Exp ::= "a" | "b"
          syntax Exp ::= K
        endmodule

        module B
          imports A
          syntax Aaa ::= Exp
        endmodule

        module C
          imports A
          syntax Abb ::= Exp
        endmodule

        module MAIN
          imports B
          imports C
        endmodule
    "#};
    kernel_sort_position_error(source, "MAIN", 4, "KItem < K < Exp < KItem");
}

#[test]
fn a_contradiction_through_an_intermediate_declared_sort_is_rejected_at_load() {
    let source = indoc! {r#"
        module MAIN
          imports BASIC-K
          syntax #W ::= KItem
          syntax Exp ::= #W
          syntax Exp ::= "a"
        endmodule
    "#};
    let diagnostic = kernel_sort_position_error(source, "MAIN", 3, "KItem < #W < Exp < KItem");
    assert!(
        diagnostic
            .message
            .contains("KItem < #W is declared by `syntax #W ::= KItem`"),
        "{diagnostic:#?}"
    );
    assert!(
        diagnostic
            .message
            .contains("#W < Exp is declared by `syntax Exp ::= #W`"),
        "{diagnostic:#?}"
    );
}

#[test]
fn a_contradiction_through_a_user_list_is_rejected_at_load() {
    let source = indoc! {r#"
        module MAIN
          imports BASIC-K
          syntax #W ::= KItem
          syntax Ws ::= List{#W, ","}
        endmodule
    "#};
    let diagnostic = kernel_sort_position_error(source, "MAIN", 3, "KItem < #W < Ws < KItem");
    assert!(
        diagnostic
            .message
            .contains("#W < Ws is declared by the user list Ws of #W"),
        "{diagnostic:#?}"
    );
}

#[test]
fn declared_subsorts_consistent_with_the_kernel_positions_load() {
    assert_loads_without_kernel_sort_position(
        indoc! {r#"
            module K4
              imports KAST
            endmodule
        "#},
        "K4",
    );
    assert_loads_without_kernel_sort_position(
        indoc! {r#"
            module MAIN
              imports BASIC-K
              syntax Exp ::= "a" | "b"
              syntax KItem ::= Exp
            endmodule
        "#},
        "MAIN",
    );
    assert_loads_without_kernel_sort_position(
        indoc! {r#"
            module MAIN
              imports BASIC-K
              syntax Exp ::= "a" | "b"
              syntax K ::= Exp
            endmodule
        "#},
        "MAIN",
    );
    assert_loads_without_kernel_sort_position(C1_WITHOUT_ITS_CONTRADICTION, "C1");
}

proptest! {
    #[test]
    fn arbitrary_entry_source_never_panics(source in any::<String>()) {
        let mut resolver = |_: &str, required: &str| Err(format!("missing {required}"));
        let _ = load(ResolvedSource::new("fuzz.k", source), "FUZZ", &mut resolver);
    }
}

/// The raw text a rule body's span denotes, resolved through `source_table`.
fn rule_body_raw_text<'a>(
    definition: &k_rust::definition::Definition,
    source_table: &k_rust::provenance::SourceTable,
    module: &str,
    raw: &'a str,
) -> (SourceId, &'a str) {
    let module = definition
        .modules
        .iter()
        .find(|candidate| candidate.name == module)
        .unwrap();
    let body = module
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
            Sentence::Rule { body, .. } => Some(body),
            _ => None,
        })
        .unwrap();
    let span = body.metadata().and_then(|metadata| metadata.span).unwrap();
    let range = source_table.raw_range(span).unwrap();
    (span.source, &raw[range])
}

#[test]
fn a_prepared_markdown_source_reloaded_under_another_selector_is_a_distinct_extraction() {
    // The `spec` block follows the `k` block, so the two selectors extract different texts from
    // the same raw bytes; each set of spans must resolve through its own extraction's map.
    let text = indoc! {r#"
        ```k
        module TEST
          syntax Value ::= "a" [symbol(aValue)] | "b" [symbol(bValue)]
          rule b => a
        endmodule
        ```
        Prose between the blocks.
        ```spec
        module SPEC
          imports TEST
          rule a => b
        endmodule
        ```
    "#};
    let mut no_requires = |_: &str, required: &str| Err(format!("unexpected {required}"));
    let base = load_with_options(
        ResolvedSource::new("test.md", text),
        "TEST",
        &mut no_requires,
        &LoadOptions {
            markdown_selector: "k".into(),
            ..LoadOptions::default()
        },
    )
    .unwrap();
    let declarations = prepared_module_declarations(base.files(), base.definition());
    let prepared = k_rust::definition::json::ProvenanceDefinition {
        definition: base.definition().clone(),
        source_table: base.source_table().clone(),
    };
    let loaded = load_with_prepared_base(
        ResolvedSource::new("test.md", text),
        "SPEC",
        &mut no_requires,
        &LoadOptions {
            markdown_selector: "k|spec".into(),
            ..LoadOptions::default()
        },
        &prepared,
        &["test.md".to_owned()],
        &declarations,
    )
    .unwrap();

    let (base_source, base_text) =
        rule_body_raw_text(loaded.definition(), loaded.source_table(), "TEST", text);
    let (spec_source, spec_text) =
        rule_body_raw_text(loaded.definition(), loaded.source_table(), "SPEC", text);
    assert_eq!(base_text, "b => a");
    assert_eq!(spec_text, "a => b");
    assert_ne!(base_source, spec_source);
    assert_eq!(
        loaded.source_table().get(base_source),
        loaded.source_table().get(spec_source)
    );
    assert_eq!(
        loaded.source_table().offset_map(base_source),
        base.source_table().offset_map(base_source)
    );

    // The serialized form distinguishes the two extractions of one logical source.
    let encoded =
        k_rust::definition::json::to_provenance_string(loaded.definition(), loaded.source_table())
            .unwrap();
    let decoded = k_rust::definition::json::from_provenance_str(&encoded).unwrap();
    assert_eq!(&decoded.source_table, loaded.source_table());
    assert_eq!(&decoded.definition, loaded.definition());
    assert_eq!(
        rule_body_raw_text(&decoded.definition, &decoded.source_table, "SPEC", text),
        (spec_source, "a => b")
    );
    assert_eq!(
        rule_body_raw_text(&decoded.definition, &decoded.source_table, "TEST", text),
        (base_source, "b => a")
    );
}

#[test]
fn a_synonym_chain_is_applied_to_its_end() {
    let source = indoc! {r#"
        module MAIN
        syntax Num ::= "zero" [symbol(zero)]
        syntax B = Num
        syntax A = B
        syntax Foo ::= g(A) [symbol(g)]
        endmodule
    "#};
    let mut resolver = |_: &str, required: &str| Err(format!("unexpected {required}"));
    let loaded = load(ResolvedSource::new("main.k", source), "MAIN", &mut resolver).unwrap();
    let production = loaded.definition().main_module().unwrap().local_sentences.iter()
        .find(|sentence| matches!(&***sentence, Sentence::Production { label: Some(label), .. } if label.name == "g"))
        .unwrap();
    let Sentence::Production { items, .. } = &**production else {
        panic!("expected g production")
    };
    let arguments = items
        .iter()
        .filter_map(|item| {
            if let ProductionItem::NonTerminal { sort, .. } = item {
                Some(sort)
            } else {
                None
            }
        })
        .collect::<Vec<_>>();
    assert_eq!(arguments, [&k_rust::kast::Sort::new("Num")]);
}

#[test]
fn a_private_import_chain_is_applied_to_its_end() {
    let source = indoc! {r#"
        module M0
        syntax Num ::= "zero" [symbol(zero)]
        syntax B = Num
        endmodule
        module M1
        imports private M0
        syntax A = B
        endmodule
        module MAIN
        imports M1
        syntax Foo ::= g(A) [symbol(g)]
        endmodule
    "#};
    let mut resolver = |_: &str, required: &str| Err(format!("unexpected {required}"));
    let loaded = load(ResolvedSource::new("main.k", source), "MAIN", &mut resolver).unwrap();
    let production = loaded.definition().main_module().unwrap().local_sentences.iter()
        .find(|sentence| matches!(&***sentence, Sentence::Production { label: Some(label), .. } if label.name == "g"))
        .unwrap();
    let Sentence::Production { items, .. } = &**production else {
        panic!("expected g production")
    };
    let arguments = items
        .iter()
        .filter_map(|item| {
            if let ProductionItem::NonTerminal { sort, .. } = item {
                Some(sort)
            } else {
                None
            }
        })
        .collect::<Vec<_>>();
    assert_eq!(arguments, [&k_rust::kast::Sort::new("Num")]);
}

#[test]
fn cyclic_sort_synonyms_are_rejected_at_load() {
    for source in [
        indoc! {r#"
            module MAIN
            syntax A = B
            syntax B = A
            syntax Foo ::= "foo"
            endmodule
        "#},
        indoc! {r#"
            module MAIN
            syntax A = A
            endmodule
        "#},
    ] {
        let mut resolver = |_: &str, required: &str| Err(format!("unexpected {required}"));
        let result = load(ResolvedSource::new("main.k", source), "MAIN", &mut resolver);
        let Err(LoadError::SourceDiagnostics(diagnostics)) = result else {
            panic!("expected source diagnostics for cyclic synonyms, load was accepted")
        };
        let defects = diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.code == DiagnosticCode::InvalidSortSynonym)
            .collect::<Vec<_>>();
        assert_eq!(defects.len(), 1, "{diagnostics:#?}");
        assert_eq!(defects[0].source.as_deref(), Some("main.k"));
        assert_eq!(defects[0].location.unwrap().start_line, 2);
    }
}

#[test]
fn an_ambiguous_sort_synonym_is_rejected_at_load() {
    let source = indoc! {r#"
        module L
        syntax Num ::= "zero"
        syntax A = Num
        endmodule
        module R
        syntax Bit ::= "one"
        syntax A = Bit
        endmodule
        module MAIN
        imports L
        imports R
        syntax Foo ::= g(A)
        endmodule
    "#};
    let mut resolver = |_: &str, required: &str| Err(format!("unexpected {required}"));
    let result = load(ResolvedSource::new("main.k", source), "MAIN", &mut resolver);
    let Err(LoadError::SourceDiagnostics(diagnostics)) = result else {
        panic!("expected source diagnostics for ambiguous synonym, load was accepted")
    };
    assert_eq!(
        diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.code == DiagnosticCode::InvalidSortSynonym)
            .count(),
        1,
        "{diagnostics:#?}"
    );
}

#[test]
fn a_production_parameter_shadows_a_synonym_at_load() {
    let source = indoc! {r#"
        module MAIN
        syntax Num ::= "zero"
        syntax S = Num
        syntax {S} S ::= myid(S) [function, symbol(myid)]
        endmodule
    "#};
    let mut resolver = |_: &str, required: &str| Err(format!("unexpected {required}"));
    let loaded = load(ResolvedSource::new("main.k", source), "MAIN", &mut resolver).unwrap();
    let production = loaded.definition().main_module().unwrap().local_sentences.iter()
        .find(|sentence| matches!(&***sentence, Sentence::Production { label: Some(label), .. } if label.name == "myid"))
        .unwrap();
    let Sentence::Production {
        parameters,
        sort,
        items,
        ..
    } = &**production
    else {
        panic!("expected myid production")
    };
    assert_eq!(parameters, &[k_rust::kast::Sort::new("S")]);
    assert_eq!(sort, &k_rust::kast::Sort::new("S"));
    let arguments = items
        .iter()
        .filter_map(|item| {
            if let ProductionItem::NonTerminal { sort, .. } = item {
                Some(sort)
            } else {
                None
            }
        })
        .collect::<Vec<_>>();
    assert_eq!(arguments, [&k_rust::kast::Sort::new("S")]);
}

fn synonym_overlap_error(
    source: &str,
    main_module: &str,
    synonym_line: u32,
    other_meaning: &str,
) -> Diagnostic {
    let mut resolver = |_: &str, required: &str| Err(format!("unexpected {required}"));
    let result = load(
        ResolvedSource::new("main.k", source),
        main_module,
        &mut resolver,
    );
    assert_synonym_overlap_error(result, synonym_line, other_meaning)
}

fn assert_synonym_overlap_error(
    result: Result<k_rust::outer::LoadedDefinition, LoadError>,
    synonym_line: u32,
    other_meaning: &str,
) -> Diagnostic {
    let diagnostics = match result {
        Err(LoadError::SourceDiagnostics(diagnostics)) => diagnostics,
        Err(error) => panic!("expected source diagnostics for a synonym overlap, got {error:?}"),
        Ok(_) => panic!("expected source diagnostics for a synonym overlap, load was accepted"),
    };
    let errors = diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Error)
        .collect::<Vec<_>>();
    assert_eq!(errors.len(), 1, "{diagnostics:#?}");
    let diagnostic = errors[0];
    assert_eq!(diagnostic.code, DiagnosticCode::InvalidSortSynonym);
    assert_eq!(diagnostic.source.as_deref(), Some("main.k"));
    assert_eq!(
        diagnostic
            .location
            .expect("the synonym has a location")
            .start_line,
        synonym_line,
        "{diagnostic:#?}"
    );
    assert!(
        diagnostic.message.contains(other_meaning),
        "{diagnostic:#?}"
    );
    diagnostic.clone()
}

#[test]
fn synonym_overlap_with_the_injected_counter_body_sort_is_rejected_without_int_import() {
    let source = indoc! {r#"
        module P8
          syntax Foo ::= "foo"
          syntax Int = Foo
          rule foo => foo
        endmodule
    "#};
    assert_synonym_overlap_error(
        load_with_prelude(source, "P8"),
        3,
        "Int is given a sort position in generated or injected grammar syntax by syntax GeneratedCounterCell",
    );
}

#[test]
fn synonym_overlap_with_implicit_configuration_imports_is_rejected_before_configuration_parsing() {
    for alias in ["Map", "Set", "List"] {
        let source = format!(
            "module TEST-IMPLICIT\n  syntax Foo ::= \"foo\" | \"bar\"\n  syntax {alias} = Foo\n  configuration <k> $PGM:K </k>\n  rule <k> foo => bar ...</k>\nendmodule\n"
        );
        assert_synonym_overlap_error(
            load_with_prelude(&source, "TEST-IMPLICIT"),
            3,
            &format!("{alias} is declared as a sort by syntax {alias}"),
        );
    }
}

#[test]
fn a_cell_named_nonterminal_with_a_visible_synonym_is_a_use() {
    use k_rust::kast::Sort;
    for (alias, synonym_module) in [
        ("FooCell", ""),
        ("FooCellFragment", ""),
        (
            "FooCell",
            "module ALIASES\n  imports INT\n  syntax FooCell = Int\nendmodule\n",
        ),
    ] {
        let alias_declaration = if synonym_module.is_empty() {
            format!("syntax {alias} = Int")
        } else {
            "imports private ALIASES".to_owned()
        };
        let source = format!(
            "{synonym_module}module C2\n  imports INT\n  {alias_declaration}\n  syntax Bar ::= bar({alias})\n  syntax KItem ::= Bar\n  configuration <k> $PGM:K </k>\n  rule bar(_X:{alias}) => .K\nendmodule\n"
        );
        let loaded = load_with_prelude(&source, "C2")
            .unwrap_or_else(|error| panic!("{alias} must denote Int: {error:?}"));
        let production = loaded
            .definition()
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .find(|sentence| {
                matches!(sentence.as_ref(), Sentence::Production { sort, .. }
                    if sort == &Sort::new("Bar"))
            })
            .expect("bar is retained");
        let Sentence::Production { items, .. } = production.as_ref() else {
            panic!("expected bar's production")
        };
        let operands = items
            .iter()
            .filter_map(|item| match item {
                ProductionItem::NonTerminal { sort, .. } => Some(sort.clone()),
                ProductionItem::Terminal(_) | ProductionItem::RegexTerminal { .. } => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(operands, vec![Sort::new("Int")]);
        assert!(loaded.definition().modules.iter().all(|module| {
            module.local_sentences.iter().all(|sentence| {
                !matches!(sentence.as_ref(), Sentence::SyntaxSort { sort, .. } if sort.name == alias)
            })
        }));
    }
}

#[test]
fn a_real_cell_still_gives_a_cell_named_alias_a_second_meaning() {
    assert_synonym_overlap_error(
        load_with_prelude(
            indoc! {r#"
                module C2
                  imports INT
                  syntax FooCell = Int
                  syntax Bar ::= bar(FooCell)
                  syntax KItem ::= Bar
                  configuration <k> $PGM:K </k> <foo> 0 </foo>
                  rule bar(_X:FooCell) => .K
                endmodule
            "#},
            "C2",
        ),
        3,
        "FooCell is given a sort position in generated or injected grammar syntax by syntax FooCell",
    );
}

#[test]
fn synonym_overlap_with_configuration_cell_sorts_is_rejected_before_rule_parsing() {
    for (alias, imports, configuration, referent) in [
        ("ACell", "imports INT", "<k> $PGM:K </k> <a> 0 </a>", "Int"),
        ("KCell", "", "<k> $PGM:K </k>", "Foo"),
        (
            "GeneratedTopCell",
            "",
            "<k> $PGM:K </k> <a> foo </a>",
            "Foo",
        ),
        ("GeneratedCounterCell", "", "<k> $PGM:K </k>", "Foo"),
        (
            "TopCellFragment",
            "",
            "<top> <k> $PGM:K </k> <a> foo </a> </top>",
            "Foo",
        ),
        (
            "ItemCellBag",
            "",
            "<k> $PGM:K </k> <item multiplicity=\"*\"> foo </item>",
            "Foo",
        ),
        (
            "ItemCellMap",
            "",
            "<k> $PGM:K </k> <item multiplicity=\"*\" type=\"Map\"> <key> foo </key> </item>",
            "Foo",
        ),
    ] {
        let source = format!(
            "module TEST-CELLS\n  {imports}\n  syntax Foo ::= \"foo\"\n  configuration {configuration}\n  syntax {alias} = {referent}\n  rule <k> foo => .K ...</k>\nendmodule\n"
        );
        let diagnostic = assert_synonym_overlap_error(
            load_with_prelude(&source, "TEST-CELLS"),
            5,
            &format!("{alias} is given a sort position in generated or injected grammar syntax"),
        );
        assert!(
            diagnostic.message.contains(&format!("syntax {alias}")),
            "{diagnostic:#?}"
        );
    }
}

#[test]
fn synonym_overlap_with_injected_generated_cell_sorts_is_rejected_without_configuration() {
    for (alias, meaning) in [
        (
            "GeneratedTopCell",
            "GeneratedTopCell names the compiler-generated <generatedTop> configuration cell",
        ),
        (
            "GeneratedCounterCell",
            "GeneratedCounterCell is given a sort position in generated or injected grammar syntax by syntax GeneratedCounterCell",
        ),
    ] {
        let source = format!(
            "module TEST-CELLS\n  syntax Foo ::= \"foo\"\n  syntax {alias} = Foo\n  rule foo => foo\nendmodule\n"
        );
        assert_synonym_overlap_error(load_with_prelude(&source, "TEST-CELLS"), 3, meaning);
    }
}

#[test]
fn synonym_overlap_with_a_future_generated_top_wrapper_is_rejected_at_load() {
    assert_synonym_overlap_error(
        load_with_prelude(
            indoc! {r#"
            module P5
              configuration <k> $PGM:K </k>
              syntax Foo ::= "foo"
              syntax GeneratedTopCell = Foo
              rule <k> foo => .K ...</k>
            endmodule
        "#},
            "P5",
        ),
        4,
        "GeneratedTopCell names the compiler-generated <generatedTop> configuration cell",
    );
}

#[test]
fn synonym_overlap_with_implicit_ml_syntax_is_rejected_at_load() {
    synonym_overlap_error(
        indoc! {r#"
            module ML-SYNTAX
              syntax A ::= "a"
            endmodule
            module MAIN
              syntax T ::= "t"
              syntax A = T
              rule t => t
            endmodule
        "#},
        "MAIN",
        6,
        "A is given a sort position in generated or injected grammar syntax by syntax A ::= \"a\"",
    );
}

#[test]
fn synonym_overlap_with_a_bare_sort_is_rejected_at_load() {
    synonym_overlap_error(
        indoc! {r#"
            module E1
              syntax T ::= "t"
              syntax A
              syntax A = T
              syntax Foo ::= g(A) | "done"
              rule g(t) => done
            endmodule
        "#},
        "E1",
        4,
        "A is declared as a sort by syntax A",
    );
}

#[test]
fn synonym_overlap_with_a_token_sort_is_rejected_at_load() {
    synonym_overlap_error(
        indoc! {r#"
            module E5
              syntax T ::= "t"
              syntax A [token]
              syntax A = T
              syntax Foo ::= g(A) | "done"
              rule g(t) => done
            endmodule
        "#},
        "E5",
        4,
        "A is declared as a sort by syntax A",
    );
}

#[test]
fn synonym_overlap_with_an_imported_production_is_rejected_at_load() {
    synonym_overlap_error(
        indoc! {r#"
            module E3-BASE
              syntax A ::= "a"
            endmodule
            module E3
              imports E3-BASE
              syntax T ::= "t"
              syntax A = T
              syntax Foo ::= g(A) | "done"
              rule g(t) => done
            endmodule
        "#},
        "E3",
        7,
        "A is declared as a sort by syntax A ::= \"a\"",
    );
}

#[test]
fn synonym_overlap_is_rejected_before_a_rule_can_create_a_cast_ambiguity() {
    synonym_overlap_error(
        indoc! {r#"
            module ALIAS-MIN
              syntax T ::= "t"
              syntax A
              syntax A = T
              rule _X:A => t
            endmodule
        "#},
        "ALIAS-MIN",
        4,
        "A is declared as a sort by syntax A",
    );
}

#[test]
fn synonym_overlap_with_a_kernel_sort_is_rejected_at_load() {
    synonym_overlap_error(
        indoc! {r#"
            module K1
              syntax Foo ::= "foo" | g(KItem)
              syntax KItem = Foo
              rule g(_) => foo
            endmodule
        "#},
        "K1",
        3,
        "KItem is a kernel sort, whose meaning K fixes",
    );
}

#[test]
fn synonym_overlap_with_a_parser_sort_is_rejected_at_load() {
    synonym_overlap_error(
        indoc! {r#"
            module K3
              syntax Foo ::= "foo" | g(#Bar)
              syntax #Bar = Foo
              rule g(foo) => foo
            endmodule
        "#},
        "K3",
        3,
        "#Bar is a parser sort (#), which has no terms",
    );
}

#[test]
fn synonym_overlap_is_reported_once_at_the_first_combining_importer() {
    let declarations = indoc! {r#"
        module B
          syntax A ::= "a"
        endmodule
        module S
          syntax T ::= "t"
          syntax A = T
        endmodule
    "#};
    let source = format!(
        "{declarations}\nmodule MAIN\n  imports B\n  imports S\nendmodule\n\
         module TOP\n  imports MAIN\nendmodule\n"
    );
    let diagnostic = synonym_overlap_error(
        &source,
        "TOP",
        6,
        "A is declared as a sort by syntax A ::= \"a\"",
    );
    assert!(
        diagnostic
            .message
            .contains("a second meaning in module MAIN:"),
        "{diagnostic:#?}"
    );

    // Neither defining module sees the other meaning until an importer combines their views.
    for (module, source) in [
        ("B", "module B\nsyntax A ::= \"a\"\nendmodule\n"),
        (
            "S",
            "module S\nsyntax T ::= \"t\"\nsyntax A = T\nendmodule\n",
        ),
    ] {
        let mut resolver = |_: &str, required: &str| Err(format!("unexpected {required}"));
        let loaded = load(ResolvedSource::new("main.k", source), module, &mut resolver)
            .unwrap_or_else(|error| panic!("{module} alone must load: {error:?}"));
        assert!(
            loaded
                .diagnostics()
                .iter()
                .all(|diagnostic| diagnostic.code != DiagnosticCode::InvalidSortSynonym),
            "{:#?}",
            loaded.diagnostics()
        );
    }
}

#[test]
fn synonym_overlap_controls_load_and_productions_use_the_alias_denotation() {
    for (module, source, label, denotation) in [
        (
            "E4",
            indoc! {r#"
                module E4
                  syntax T ::= "t"
                  syntax A = T
                  syntax A ::= "a" [symbol(a)]
                  syntax Foo ::= g(A) | "done"
                  rule g(a) => done
                endmodule
            "#},
            "a",
            "T",
        ),
        (
            "WAD-RAY",
            indoc! {r#"
                module WAD-RAY
                  syntax Rat ::= r"[0-9]+" [token]
                  syntax Wad = Rat
                  syntax Ray = Rat
                  syntax Wad ::= "f(" Ray ")" [symbol(f)]
                  rule f(0:Wad) => 0
                endmodule
            "#},
            "f",
            "Rat",
        ),
        (
            "CHAIN",
            indoc! {r#"
                module CHAIN
                  syntax Rat ::= r"[0-9]+" [token]
                  syntax Ray = Rat
                  syntax Wad = Ray
                  syntax Wad ::= "f(" Ray ")" [symbol(f)]
                  rule f(0:Wad) => 0
                endmodule
            "#},
            "f",
            "Rat",
        ),
        (
            "BOUND",
            indoc! {r#"
                module BOUND
                  syntax Num ::= "zero"
                  syntax S = Num
                  syntax {S} S ::= myid(S) [function, symbol(myid)]
                endmodule
            "#},
            "myid",
            "S",
        ),
    ] {
        let mut resolver = |_: &str, required: &str| Err(format!("unexpected {required}"));
        let loaded = load(ResolvedSource::new("main.k", source), module, &mut resolver)
            .unwrap_or_else(|error| panic!("{module} must load: {error:?}"));
        assert!(
            loaded
                .diagnostics()
                .iter()
                .all(|diagnostic| diagnostic.code != DiagnosticCode::InvalidSortSynonym),
            "{:#?}",
            loaded.diagnostics()
        );
        let production = loaded
            .definition()
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .find(|sentence| {
                matches!(&***sentence, Sentence::Production { label: Some(candidate), .. }
                if candidate.name == label)
            })
            .expect("the production is retained");
        let Sentence::Production { sort, .. } = &**production else {
            panic!("expected a production")
        };
        assert_eq!(sort, &k_rust::kast::Sort::new(denotation), "{module}");
    }
}

#[test]
fn a_numeral_sort_with_terms_is_rejected_before_any_bubble() {
    let mut accepted = Vec::new();
    for (module, source, lines) in [
        (
            "N1B",
            indoc! {r#"
            module N1B
              syntax 8 ::= "eight"
              syntax Foo ::= bar(8) | "done"
              rule bar(eight) => done
            endmodule
        "#},
            vec![2, 3],
        ),
        (
            "N20",
            indoc! {r#"
            module N20
              syntax Foo ::= "foo"
              syntax 8 = Foo
              syntax Bar ::= bar(8) | "done"
              rule bar(foo) => done
            endmodule
        "#},
            vec![3],
        ),
    ] {
        let diagnostics = match load_with_prelude(source, module) {
            Err(LoadError::SourceDiagnostics(diagnostics)) => diagnostics,
            Ok(_) => {
                accepted.push(module);
                continue;
            }
            Err(error) => panic!(
                "{module}: expected numeral source diagnostics before any bubble, got {error:?}"
            ),
        };
        let errors = diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.severity == Severity::Error)
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), lines.len(), "{diagnostics:#?}");
        assert!(
            errors
                .iter()
                .all(|diagnostic| diagnostic.code == DiagnosticCode::InvalidNumeralSort),
            "{diagnostics:#?}"
        );
        let mut actual_lines = errors
            .iter()
            .map(|diagnostic| {
                assert_eq!(diagnostic.source.as_deref(), Some("main.k"));
                diagnostic
                    .location
                    .expect("the offending sentence has a location")
                    .start_line
            })
            .collect::<Vec<_>>();
        actual_lines.sort();
        assert_eq!(actual_lines, lines);
        if module == "N20" {
            assert!(
                errors[0].message.ends_with("a sort synonym."),
                "{diagnostics:#?}"
            );
        }
    }
    assert!(
        accepted.is_empty(),
        "numeral terms loaded before any bubble was checked: {accepted:?}"
    );
}
