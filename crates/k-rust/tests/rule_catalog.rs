use std::collections::BTreeSet;

use k_rust::{
    backend::{
        Backend, BackendDiagnosticOutput, BackendOptions, CompiledRuleKind, ExecuteRequest,
        ObservationEventOutput, ObservedRequest,
    },
    builtin::embedded,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    kore::parser::parse_pattern,
    outer::{LoadOptions, ResolvedSource, load_with_options},
};

const SOURCE: &str = r#"module CATALOG-SYNTAX
  syntax S ::= "x" [symbol(x)]
             | "y" [symbol(y)]
             | "z" [symbol(z)]
             | "w" [symbol(w)]
             | "f(" S ")" [function, symbol(f)]
             | "m(" S ")" [macro, symbol(m)]
endmodule

module CATALOG
  imports CATALOG-SYNTAX
  imports BASIC-K
  imports INT-SYNTAX
  configuration <k> .K </k>

  rule x => y [priority(42)]
  rule x => y [priority(42)]
  rule f(y) => z [label(function)]
  rule f(z) => w [simplification, label(simplify)]
  rule f(w) => x [non-executable, label(nonexec)]
  rule w => y [label(collision-a)]
  rule w => y [label(collision-b)]
  rule m(X:S) => X:S [label(macro)]
endmodule
"#;

const X_STATE: &str = r#"Lbl'-LT-'generatedTop'-GT-'{}(
    Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortS{}, SortKItem{}}(Lblx{}()), dotk{}())),
    Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0"))
)"#;

fn backend() -> Backend {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("catalog.k", SOURCE),
        "CATALOG",
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
    let compiled = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
    let syntax = k_rust::kore::parser::parse_definition(&compiled.definition_kore).unwrap();
    let module = syntax.modules.last().unwrap().name.as_str();
    Backend::new(&compiled.definition_kore, module, BackendOptions::default()).unwrap()
}

#[test]
fn source_sentences_have_compiled_kinds_and_origins() {
    let backend = backend();
    let catalog = backend.rule_catalog(None).unwrap();
    let local: Vec<_> = catalog
        .iter()
        .filter(|entry| {
            entry
                .origins
                .iter()
                .any(|origin| origin.source.as_deref() == Some("Source(catalog.k)"))
        })
        .collect();
    let by_label = |label: &str| -> Vec<_> {
        local
            .iter()
            .copied()
            .filter(|entry| entry.label.as_deref() == Some(label))
            .collect()
    };

    let rewrites: Vec<_> = local
        .iter()
        .copied()
        .filter(|entry| {
            entry.kind == CompiledRuleKind::Rewrite
                && entry.origins.iter().any(|origin| {
                    origin
                        .location
                        .as_deref()
                        .is_some_and(|s| s.starts_with("Location(16,"))
                })
        })
        .collect();
    let [rewrite] = rewrites.as_slice() else {
        panic!("expected one collapsed rewrite in {local:#?}");
    };
    assert_eq!(rewrite.kind, CompiledRuleKind::Rewrite);
    assert!(rewrite.executable);
    assert_eq!(rewrite.label, None);
    assert_eq!(rewrite.priority, 42);
    assert!(!rewrite.shared_identity);
    let locations: Vec<_> = rewrite
        .origins
        .iter()
        .filter(|origin| origin.source.as_deref() == Some("Source(catalog.k)"))
        .map(|origin| origin.location.as_deref())
        .collect();
    assert_eq!(locations.len(), 2);
    assert!(locations[0].unwrap().starts_with("Location(16,"));
    assert!(locations[1].unwrap().starts_with("Location(17,"));

    for (label, kind, executable) in [
        ("function", CompiledRuleKind::FunctionEquation, true),
        ("simplify", CompiledRuleKind::Simplification, true),
        ("nonexec", CompiledRuleKind::FunctionEquation, false),
    ] {
        let entries = by_label(label);
        let [entry] = entries.as_slice() else {
            panic!("expected one {label} entry in {local:#?}");
        };
        assert_eq!(entry.kind, kind, "{label}");
        assert_eq!(entry.executable, executable, "{label}");
        assert_eq!(entry.origins.len(), 1, "{label}");
        assert!(!entry.shared_identity, "{label}");
    }
    let collision_a_entries = by_label("collision-a");
    let [collision_a] = collision_a_entries.as_slice() else {
        panic!("expected collision-a in {local:#?}");
    };
    let collision_b_entries = by_label("collision-b");
    let [collision_b] = collision_b_entries.as_slice() else {
        panic!("expected collision-b in {local:#?}");
    };
    assert_eq!(collision_a.id, collision_b.id);
    assert!(collision_a.shared_identity && collision_b.shared_identity);
    assert_eq!(collision_a.kind, CompiledRuleKind::Rewrite);
    assert_eq!(collision_b.kind, CompiledRuleKind::Rewrite);
    assert_eq!(
        local.len(),
        6,
        "unexpected source-compiled rules: {local:#?}"
    );
    assert!(by_label("macro").is_empty(), "macro entered the catalog");

    let wire = serde_json::to_value(rewrite).unwrap();
    assert_eq!(wire["kind"], "rewrite");
    assert_eq!(wire["sharedIdentity"], false);
    assert!(serde_json::from_value::<k_rust::backend::CompiledRuleOutput>(wire.clone()).is_ok());
    let mut unknown_field = wire;
    unknown_field["sentenceIndex"] = serde_json::json!(16);
    assert!(serde_json::from_value::<k_rust::backend::CompiledRuleOutput>(unknown_field).is_err());
}

#[test]
fn catalog_rewrite_identities_install_as_observation_filters() {
    let mut backend = backend();
    let catalog = backend.rule_catalog(None).unwrap();
    let ids: BTreeSet<_> = catalog.iter().map(|entry| entry.id.as_str()).collect();
    let state = parse_pattern(X_STATE).unwrap();
    let request = ExecuteRequest {
        max_depth: Some(1),
        ..ExecuteRequest::new(state)
    };

    for entry in catalog.iter().filter(|entry| {
        entry.kind == CompiledRuleKind::Rewrite && entry.executable && !entry.shared_identity
    }) {
        backend
            .execute_observed(ObservedRequest {
                request: request.clone(),
                rules: Some(vec![entry.id.clone()]),
            })
            .unwrap_or_else(|error| panic!("catalog rewrite {} was rejected: {error}", entry.id));
    }

    let ambiguous = catalog
        .iter()
        .find(|entry| entry.label.as_deref() == Some("collision-a"))
        .unwrap();
    let error = backend
        .execute_observed(ObservedRequest {
            request: request.clone(),
            rules: Some(vec![ambiguous.id.clone()]),
        })
        .expect_err("shared identity must be rejected by the observation filter");
    assert!(
        error
            .to_string()
            .contains("is carried by axioms that differ"),
        "{error}"
    );

    let observed = backend
        .execute_observed(ObservedRequest {
            request,
            rules: None,
        })
        .unwrap();
    let applied: Vec<_> = observed
        .leaves
        .iter()
        .flat_map(|leaf| &leaf.observations)
        .filter_map(|event| match event {
            ObservationEventOutput::Transition { id, .. } => Some(id.rule.as_str()),
            _ => None,
        })
        .collect();
    assert!(!applied.is_empty());
    assert!(applied.iter().all(|id| ids.contains(id)));
}

/// Equations that carry neither a label nor a `UNIQUE_ID` all have the id `UNKNOWN`, so a
/// condition reported for one of them names it by its id and by the first written sentence of
/// its axiom, which is the first of its catalog entry's origins: a client tells the two
/// equations apart and finds each one's entry.
#[test]
fn an_undecided_condition_of_an_unnamed_equation_names_its_catalog_entry() {
    let definition = r#"[] module MAIN
        sort SortS{} []
        symbol a{}() : SortS{} [constructor{}(), functional{}()]
        symbol c{}(SortS{}, SortS{}) : SortS{} [constructor{}(), functional{}()]
        symbol f{}(SortS{}) : SortS{} [function{}()]
        symbol g{}(SortS{}) : SortS{} [function{}()]
        axiom{R} \implies{R}(\top{R}(), \equals{SortS{}, R}(
            f{}(X:SortS{}), \and{SortS{}}(Y:SortS{}, \top{SortS{}}())))
            [simplification{}(),
             org'Stop'kframework'Stop'attributes'Stop'Source{}("Source(test.k)"),
             org'Stop'kframework'Stop'attributes'Stop'Location{}("Location(3,3,3,20)")]
        axiom{R} \implies{R}(\top{R}(), \equals{SortS{}, R}(
            g{}(X:SortS{}), \and{SortS{}}(Y:SortS{}, \top{SortS{}}())))
            [simplification{}(),
             org'Stop'kframework'Stop'attributes'Stop'Source{}("Source(test.k)"),
             org'Stop'kframework'Stop'attributes'Stop'Location{}("Location(4,3,4,20)")]
    endmodule []"#;
    let mut backend = Backend::new(definition, "MAIN", BackendOptions::default()).unwrap();
    let catalog = backend.rule_catalog(None).unwrap();
    let state = parse_pattern("c{}(f{}(a{}()), g{}(a{}()))").unwrap();
    let leaves = backend.execute(ExecuteRequest::new(state)).unwrap().leaves;
    let named: Vec<_> = leaves
        .iter()
        .flat_map(|leaf| &leaf.diagnostics)
        .filter_map(|diagnostic| match diagnostic {
            BackendDiagnosticOutput::UndecidedCondition {
                rule_id, origin, ..
            } => Some((rule_id.clone(), origin.clone().expect("an origin"))),
            _ => None,
        })
        .collect();
    let locations: BTreeSet<_> = named
        .iter()
        .map(|(_, origin)| origin.location.clone().unwrap())
        .collect();
    assert_eq!(
        locations,
        BTreeSet::from([
            "Location(3,3,3,20)".to_owned(),
            "Location(4,3,4,20)".to_owned()
        ]),
        "{named:?}"
    );
    for (rule_id, origin) in &named {
        assert_eq!(rule_id, "UNKNOWN");
        let entries: Vec<_> = catalog
            .iter()
            .filter(|entry| &entry.id == rule_id && entry.origins.first() == Some(origin))
            .collect();
        assert_eq!(entries.len(), 1, "{origin:?} in {catalog:?}");
        assert!(entries[0].shared_identity);
    }
}

/// Two equations whose axioms carry neither a label, a `UNIQUE_ID`, a `Source` nor a
/// `Location` share the id `UNKNOWN` and every written position, so only their places in the
/// definition tell them apart: a condition reported for each names its own sentence there,
/// and that origin finds the one catalog entry the equation belongs to.
#[test]
fn an_undecided_condition_of_an_unnamed_unlocated_equation_names_its_catalog_entry() {
    let definition = r#"[] module MAIN
        sort SortS{} []
        symbol a{}() : SortS{} [constructor{}(), functional{}()]
        symbol c{}(SortS{}, SortS{}) : SortS{} [constructor{}(), functional{}()]
        symbol f{}(SortS{}) : SortS{} [function{}()]
        symbol g{}(SortS{}) : SortS{} [function{}()]
        axiom{R} \implies{R}(\top{R}(), \equals{SortS{}, R}(
            f{}(X:SortS{}), \and{SortS{}}(Y:SortS{}, \top{SortS{}}())))
            [simplification{}()]
        axiom{R} \implies{R}(\top{R}(), \equals{SortS{}, R}(
            g{}(X:SortS{}), \and{SortS{}}(Y:SortS{}, \top{SortS{}}())))
            [simplification{}()]
    endmodule []"#;
    let mut backend = Backend::new(definition, "MAIN", BackendOptions::default()).unwrap();
    let catalog = backend.rule_catalog(None).unwrap();
    let state = parse_pattern("c{}(f{}(a{}()), g{}(a{}()))").unwrap();
    let leaves = backend.execute(ExecuteRequest::new(state)).unwrap().leaves;
    let named: Vec<_> = leaves
        .iter()
        .flat_map(|leaf| &leaf.diagnostics)
        .filter_map(|diagnostic| match diagnostic {
            BackendDiagnosticOutput::UndecidedCondition {
                rule_id, origin, ..
            } => Some((rule_id.clone(), origin.clone().expect("an origin"))),
            _ => None,
        })
        .collect();
    let places: BTreeSet<_> = named
        .iter()
        .map(|(_, origin)| {
            assert_eq!((&origin.source, &origin.location), (&None, &None));
            let sentence = origin.sentence.as_ref().expect("a sentence place");
            (sentence.module.clone(), sentence.index)
        })
        .collect();
    assert_eq!(
        places,
        BTreeSet::from([("MAIN".to_owned(), 5), ("MAIN".to_owned(), 6)]),
        "{named:?}"
    );
    for (rule_id, origin) in &named {
        assert_eq!(rule_id, "UNKNOWN");
        let entries: Vec<_> = catalog
            .iter()
            .filter(|entry| &entry.id == rule_id && entry.origins.first() == Some(origin))
            .collect();
        assert_eq!(entries.len(), 1, "{origin:?} in {catalog:?}");
        assert!(entries[0].shared_identity);
    }
}
