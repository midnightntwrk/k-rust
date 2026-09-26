use std::sync::Arc;

use std::collections::{BTreeMap, BTreeSet};

use k_rust::definition::{
    Attributes, Definition, FlatImport, FlatModule, ResolvedDefinition, Sentence,
};
use proptest::prelude::*;

const MODULE_NAMES: [&str; 5] = [
    "POTENTIAL-IMPORT-A",
    "POTENTIAL-IMPORT-B",
    "POTENTIAL-IMPORT-C",
    "POTENTIAL-IMPORT-D",
    "MAIN",
];

fn marker(name: &str) -> Sentence {
    Sentence::Bubble {
        sentence_type: "rule".into(),
        contents: name.into(),
        attributes: Attributes::default(),
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]

    #[test]
    fn every_dag_edge_is_dependency_first(
        edges in prop::collection::vec(any::<bool>(), 10),
        order_keys in prop::collection::vec(any::<u8>(), 5),
    ) {
        let mut edge_index = 0;
        let mut modules = Vec::new();
        for (importer, &module_name) in MODULE_NAMES.iter().enumerate() {
            let mut imports = Vec::new();
            for &imported_name in MODULE_NAMES.iter().take(importer) {
                if edges[edge_index] {
                    imports.push(FlatImport {
                        name: imported_name.into(),
                        public: (edge_index % 2) == 0,
                    });
                }
                edge_index += 1;
            }
            modules.push(FlatModule {
                name: module_name.into(),
                imports,
                local_sentences: vec![Arc::new(marker(module_name))],
                attributes: Attributes::default(),
            });
        }
        modules.sort_by_key(|module| {
            let index = MODULE_NAMES
                .iter()
                .position(|name| *name == module.name.as_str())
                .unwrap();
            (order_keys[index], module.name.clone())
        });

        let resolved = ResolvedDefinition::resolve(&Definition {
            main_module: "MAIN".into(),
            modules,
            attributes: Attributes::default(),
        })
        .unwrap();
        let positions = resolved
            .dependency_order()
            .iter()
            .enumerate()
            .map(|(position, id)| (resolved.module(*id).name.clone(), position))
            .collect::<BTreeMap<_, _>>();

        for (id, module) in resolved.modules() {
            for import in resolved.direct_imports(id) {
                let imported = &resolved.module(import.module).name;
                prop_assert!(positions[imported] < positions[&module.name]);
            }

            let mut expected = BTreeSet::new();
            let mut pending = resolved
                .direct_imports(id)
                .into_iter()
                .map(|import| import.module)
                .collect::<Vec<_>>();
            while let Some(import) = pending.pop() {
                if expected.insert(import) {
                    pending.extend(
                        resolved
                            .direct_imports(import)
                            .into_iter()
                            .map(|next| next.module),
                    );
                }
            }
            let actual = resolved.transitive_imports(id).into_iter().collect::<BTreeSet<_>>();
            prop_assert_eq!(actual, expected);
        }
    }
}

fn bubble(contents: u8, attribute: u8) -> Sentence {
    let mut attributes = BTreeMap::new();
    if attribute > 0 {
        attributes.insert(
            "variant".to_owned(),
            serde_json::json!(attribute.to_string()),
        );
    }
    Sentence::Bubble {
        sentence_type: "rule".into(),
        contents: format!("contents {contents}"),
        attributes: Attributes::new(attributes),
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]

    /// A module sees the first sentence of each equivalence class among the local sentences of
    /// itself and its transitive imports, in dependency order.
    #[test]
    fn visible_sentences_keep_the_first_of_each_equivalence_class(
        edges in prop::collection::vec(any::<bool>(), 10),
        sentences in prop::collection::vec(
            prop::collection::vec((0u8..4, 0u8..3), 0..6),
            5,
        ),
    ) {
        let mut edge_index = 0;
        let mut modules = Vec::new();
        for (importer, &module_name) in MODULE_NAMES.iter().enumerate() {
            let mut imports = Vec::new();
            for &imported_name in MODULE_NAMES.iter().take(importer) {
                if edges[edge_index] {
                    imports.push(FlatImport {
                        name: imported_name.into(),
                        public: true,
                    });
                }
                edge_index += 1;
            }
            modules.push(FlatModule {
                name: module_name.into(),
                imports,
                local_sentences: sentences[importer]
                    .iter()
                    .map(|&(contents, attribute)| Arc::new(bubble(contents, attribute)))
                    .collect(),
                attributes: Attributes::default(),
            });
        }
        let resolved = ResolvedDefinition::resolve(&Definition {
            main_module: "MAIN".into(),
            modules,
            attributes: Attributes::default(),
        })
        .unwrap();

        for (id, _) in resolved.modules() {
            let mut visible = resolved.transitive_imports(id).into_iter().collect::<BTreeSet<_>>();
            visible.insert(id);
            let mut expected = Vec::<&Sentence>::new();
            for module in resolved.dependency_order().iter().filter(|module| visible.contains(module)) {
                for sentence in &resolved.module(*module).local_sentences {
                    if !expected
                        .iter()
                        .any(|kept| k_rust::definition::sentence_equivalent(kept, sentence))
                    {
                        expected.push(sentence);
                    }
                }
            }
            prop_assert_eq!(resolved.sentences(id), expected);
        }
    }
}
