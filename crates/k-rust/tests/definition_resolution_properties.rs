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
