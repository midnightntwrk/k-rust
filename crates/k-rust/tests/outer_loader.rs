use std::collections::BTreeMap;

use indoc::indoc;
use k_rust::definition::Sentence;
use k_rust::outer::{LoadError, ResolvedSource, load};
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
                requires "b.k"
                requires "c.k"
                module MAIN
                  imports B
                  imports C
                  syntax Exp ::= "bar" [symbol(bar)]
                  syntax priority foo > bar
                endmodule
            "#},
        ),
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
    insta::assert_debug_snapshot!(summary);
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
    let mut resolver = |_: &str, _: &str| Err("not found".to_owned());
    let loaded = load(
        ResolvedSource::new(
            "main.k",
            indoc! {r#"
                module MAIN
                  syntax Int ::= r"[0-9]+" [token]
                  configuration <top><k> $PGM:Int </k><counter> 0 </counter></top>
                endmodule
            "#},
        ),
        "MAIN",
        &mut resolver,
    )
    .unwrap();

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
    insta::assert_debug_snapshot!(labels);
}

macro_rules! load_error_snapshot {
    ($name:ident, $entry:expr, $sources:expr, $main:expr) => {
        #[test]
        fn $name() {
            let sources: BTreeMap<&str, &str> = BTreeMap::from($sources);
            let mut resolver = |_: &str, required: &str| {
                sources
                    .get(required)
                    .map(|text| ResolvedSource::new(required, *text))
                    .ok_or_else(|| format!("{required} was not found"))
            };
            let error =
                load(ResolvedSource::new("main.k", $entry), $main, &mut resolver).unwrap_err();
            insta::assert_debug_snapshot!(error);
        }
    };
}

load_error_snapshot!(
    missing_required_source,
    "requires \"missing.k\"",
    [],
    "MAIN"
);

load_error_snapshot!(
    circular_requires,
    "requires \"b.k\"",
    [
        ("b.k", "requires \"main.k\""),
        ("main.k", "requires \"b.k\"")
    ],
    "MAIN"
);

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
    let mut resolver = |_: &str, _: &str| Err("not found".to_owned());
    let error = load(
        ResolvedSource::new(
            "main.k",
            indoc! {r#"
                module MAIN
                  syntax Exp ::= "(" Int ")" [bracket]
                endmodule
            "#},
        ),
        "MAIN",
        &mut resolver,
    )
    .unwrap_err();
    assert!(matches!(error, LoadError::SourceDiagnostics(_)));
    insta::assert_debug_snapshot!(error);
}

proptest! {
    #[test]
    fn arbitrary_entry_source_never_panics(source in any::<String>()) {
        let mut resolver = |_: &str, required: &str| Err(format!("missing {required}"));
        let _ = load(ResolvedSource::new("fuzz.k", source), "FUZZ", &mut resolver);
    }
}
