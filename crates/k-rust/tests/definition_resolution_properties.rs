use std::collections::BTreeMap;

use k_rust::definition::{
    Attributes, Definition, FlatImport, FlatModule, ResolvedDefinition, Sentence,
};
use proptest::prelude::*;

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
        for importer in 0..5 {
            let mut imports = Vec::new();
            for imported in 0..importer {
                if edges[edge_index] {
                    imports.push(FlatImport {
                        name: format!("M{imported}"),
                        public: (edge_index % 2) == 0,
                    });
                }
                edge_index += 1;
            }
            modules.push(FlatModule {
                name: format!("M{importer}"),
                imports,
                local_sentences: vec![marker(&format!("M{importer}"))],
                attributes: Attributes::default(),
            });
        }
        modules.sort_by_key(|module| {
            let index = module.name[1..].parse::<usize>().unwrap();
            (order_keys[index], module.name.clone())
        });

        let resolved = ResolvedDefinition::resolve(&Definition {
            main_module: "M4".into(),
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
        }
    }
}
