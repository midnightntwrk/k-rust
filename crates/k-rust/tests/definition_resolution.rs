use std::collections::BTreeMap;

use k_rust::definition::{
    Attributes, Definition, FlatImport, FlatModule, ResolveError, ResolvedDefinition, Sentence,
};
use serde_json::Value;

fn attrs(entries: &[(&str, &str)]) -> Attributes {
    Attributes::new(
        entries
            .iter()
            .map(|(key, value)| ((*key).into(), Value::String((*value).into())))
            .collect::<BTreeMap<_, _>>(),
    )
}

fn marker(name: &str) -> Sentence {
    Sentence::Bubble {
        sentence_type: "rule".into(),
        contents: name.into(),
        attributes: Attributes::default(),
    }
}

fn module(name: &str, imports: &[(&str, bool)]) -> FlatModule {
    FlatModule {
        name: name.into(),
        imports: imports
            .iter()
            .map(|(name, public)| FlatImport {
                name: (*name).into(),
                public: *public,
            })
            .collect(),
        local_sentences: vec![marker(name)],
        attributes: Attributes::default(),
    }
}

fn definition(modules: Vec<FlatModule>) -> Definition {
    Definition {
        main_module: "A".into(),
        modules,
        attributes: Attributes::default(),
    }
}

fn module_names(
    resolved: &ResolvedDefinition,
    modules: &[k_rust::definition::ModuleId],
) -> Vec<String> {
    modules
        .iter()
        .map(|id| resolved.module(*id).name.clone())
        .collect()
}

#[test]
fn resolves_diamond_imports_dependency_first() {
    let definition = definition(vec![
        module("A", &[("C", false), ("B", true)]),
        module("B", &[("D", true)]),
        module("C", &[("D", true)]),
        module("D", &[]),
    ]);
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let a = resolved.main_module_id();

    assert_eq!(
        module_names(&resolved, resolved.dependency_order()),
        ["D", "B", "C", "A"]
    );
    assert_eq!(
        resolved
            .direct_imports(a)
            .into_iter()
            .map(|import| (resolved.module(import.module).name.as_str(), import.public))
            .collect::<Vec<_>>(),
        [("B", true), ("C", false)]
    );
    assert_eq!(
        module_names(&resolved, &resolved.transitive_imports(a)),
        ["B", "C", "D"]
    );
    assert_eq!(
        resolved
            .sentences(a)
            .into_iter()
            .map(|sentence| match sentence {
                Sentence::Bubble { contents, .. } => contents.as_str(),
                _ => panic!("expected marker sentence"),
            })
            .collect::<Vec<_>>(),
        ["D", "B", "C", "A"]
    );
}

#[test]
fn topology_is_independent_of_flat_module_order() {
    let forward = ResolvedDefinition::resolve(&definition(vec![
        module("A", &[("B", true), ("C", true)]),
        module("B", &[("D", true)]),
        module("C", &[("D", true)]),
        module("D", &[]),
    ]))
    .unwrap();
    let reverse = ResolvedDefinition::resolve(&definition(vec![
        module("D", &[]),
        module("C", &[("D", true)]),
        module("B", &[("D", true)]),
        module("A", &[("C", true), ("B", true)]),
    ]))
    .unwrap();

    assert_eq!(
        module_names(&forward, forward.dependency_order()),
        module_names(&reverse, reverse.dependency_order())
    );
}

#[test]
fn rejects_invalid_module_graphs_with_specific_errors() {
    assert_eq!(
        ResolvedDefinition::resolve(&definition(vec![module("A", &[]), module("A", &[])]))
            .unwrap_err(),
        ResolveError::DuplicateModule("A".into())
    );

    let mut missing_main = definition(vec![module("A", &[])]);
    missing_main.main_module = "MAIN".into();
    assert_eq!(
        ResolvedDefinition::resolve(&missing_main).unwrap_err(),
        ResolveError::MissingMainModule("MAIN".into())
    );

    assert_eq!(
        ResolvedDefinition::resolve(&definition(vec![module("A", &[("MISSING", true)])]))
            .unwrap_err(),
        ResolveError::MissingImport {
            module: "A".into(),
            import: "MISSING".into(),
        }
    );
    assert_eq!(
        ResolvedDefinition::resolve(&definition(vec![module("A", &[("A", true)])])).unwrap_err(),
        ResolveError::SelfImport("A".into())
    );

    let cycle = definition(vec![
        module("A", &[("B", true)]),
        module("B", &[("C", true)]),
        module("C", &[("A", true)]),
    ]);
    assert_eq!(
        ResolvedDefinition::resolve(&cycle).unwrap_err(),
        ResolveError::CircularImports(vec!["A".into(), "B".into(), "C".into(), "A".into()])
    );
}

#[test]
fn applies_scala_public_sentence_rules() {
    let mut public = marker("public");
    let Sentence::Bubble { attributes, .. } = &mut public else {
        unreachable!()
    };
    *attributes = attrs(&[("public", "")]);

    let mut private = marker("private");
    let Sentence::Bubble { attributes, .. } = &mut private else {
        unreachable!()
    };
    *attributes = attrs(&[("private", "")]);

    let mut private_module = module("A", &[]);
    private_module.attributes = attrs(&[("private", "")]);
    private_module.local_sentences = vec![marker("ordinary"), public.clone(), private.clone()];
    let resolved = ResolvedDefinition::resolve(&definition(vec![private_module])).unwrap();
    assert_eq!(
        resolved.public_sentences(resolved.main_module_id()),
        [&public]
    );

    let mut ordinary_module = module("A", &[]);
    ordinary_module.local_sentences = vec![marker("ordinary"), public, private];
    let resolved = ResolvedDefinition::resolve(&definition(vec![ordinary_module])).unwrap();
    assert_eq!(
        resolved.public_sentences(resolved.main_module_id()).len(),
        2
    );
}

#[test]
fn deduplicates_flat_sets_only_during_resolution() {
    let repeated = marker("same");
    let mut a = module("A", &[("B", true), ("B", true)]);
    a.local_sentences = vec![repeated.clone(), repeated.clone()];
    let mut b = module("B", &[]);
    b.local_sentences = vec![repeated];
    let definition = definition(vec![a, b]);

    assert_eq!(definition.modules[0].local_sentences.len(), 2);
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let a = resolved.main_module_id();
    assert_eq!(resolved.module(a).local_sentences.len(), 1);
    assert_eq!(resolved.direct_imports(a).len(), 1);
    assert_eq!(resolved.sentences(a).len(), 1);
}

#[test]
fn resolves_the_upstream_reduced_fixture() {
    let definition =
        k_rust::definition::json::from_str(include_str!("fixtures/kast/definition.json")).unwrap();
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    assert_eq!(resolved.module(resolved.main_module_id()).name, "IMP");
    assert_eq!(
        module_names(&resolved, resolved.dependency_order()),
        ["BOOL-SYNTAX", "IMP"]
    );
}
