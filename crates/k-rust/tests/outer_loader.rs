use std::collections::BTreeMap;

use indoc::indoc;
use k_rust::definition::Sentence;
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
        endmodule

        module DEFAULT-CONFIGURATION
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

proptest! {
    #[test]
    fn arbitrary_entry_source_never_panics(source in any::<String>()) {
        let mut resolver = |_: &str, required: &str| Err(format!("missing {required}"));
        let _ = load(ResolvedSource::new("fuzz.k", source), "FUZZ", &mut resolver);
    }
}
