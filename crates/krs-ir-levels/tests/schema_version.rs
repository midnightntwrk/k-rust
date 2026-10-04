//! Semantic IR and Definition IR documents accept only the current schema version.

use krs_ir::{
    ConfigurationRoot, FixedCell, FixedConfiguration, FixedInitializerCell, ModuleId,
    SchemaVersion, SemanticId, testing,
};
use krs_ir_levels::{
    DefinitionIr, DefinitionModule, DefinitionSentence, DefinitionSortRef, DefinitionTerm,
    SemanticModule, SemanticSortRef, SemanticTerm, SemanticTheory, SymbolId,
};

fn semantic_theory() -> SemanticTheory {
    let cell = SemanticId::new("cell.k").unwrap();
    let configuration = FixedConfiguration::new(
        testing::origin("semantic.configuration"),
        SemanticId::new("configuration").unwrap(),
        ConfigurationRoot::GeneratedTop,
        vec![
            FixedCell::leaf(
                testing::origin("semantic.cell"),
                cell.clone(),
                "k",
                vec![],
                SemanticSortRef::int(),
            )
            .unwrap(),
        ],
        testing::origin("semantic.initializer"),
        SemanticId::new("initializer").unwrap(),
        vec![],
        vec![FixedInitializerCell::term(
            testing::origin("semantic.initializer.cell"),
            cell,
            SemanticTerm::token(
                testing::origin("semantic.token"),
                SemanticSortRef::int(),
                "0",
            )
            .unwrap(),
        )],
    )
    .unwrap();
    SemanticTheory::new(vec![SemanticModule::new(
        testing::origin("semantic.module"),
        ModuleId::new("MINIMAL").unwrap(),
        vec![],
        vec![],
        vec![],
        vec![],
        vec![],
        vec![],
        Some(configuration),
        vec![],
    )])
    .unwrap()
}

fn definition_ir() -> DefinitionIr {
    let cell = SymbolId::new("cell.k").unwrap();
    let configuration = FixedConfiguration::new(
        testing::origin("definition.configuration"),
        SemanticId::new("configuration").unwrap(),
        ConfigurationRoot::GeneratedTop,
        vec![
            FixedCell::leaf(
                testing::origin("definition.cell"),
                cell.clone(),
                "k",
                vec![],
                DefinitionSortRef::int(),
            )
            .unwrap(),
        ],
        testing::origin("definition.initializer"),
        SemanticId::new("initializer").unwrap(),
        vec![],
        vec![FixedInitializerCell::term(
            testing::origin("definition.initializer.cell"),
            cell,
            DefinitionTerm::token(
                testing::origin("definition.token"),
                DefinitionSortRef::int(),
                "0",
            )
            .unwrap(),
        )],
    )
    .unwrap();
    let main = ModuleId::new("MINIMAL").unwrap();
    DefinitionIr::new(
        main.clone(),
        vec![DefinitionModule::new(
            testing::origin("definition.module"),
            main,
            vec![],
            vec![],
            vec![DefinitionSentence::Configuration(configuration)],
        )],
    )
    .unwrap()
}

#[test]
fn ir_documents_reject_every_noncurrent_schema_version() {
    let expected_schema = format!("expected {}", SchemaVersion::CURRENT.0);
    let semantic = serde_json::to_value(semantic_theory()).unwrap();
    let definition = serde_json::to_value(definition_ir()).unwrap();

    for version in (0..=SchemaVersion::CURRENT.0 + 5).chain([u32::MAX]) {
        if version != SchemaVersion::CURRENT.0 {
            let mut wire = semantic.clone();
            wire["schema_version"] = version.into();
            let error = serde_json::from_value::<SemanticTheory>(wire).unwrap_err();
            assert!(error.to_string().contains(&expected_schema), "{error}");

            let mut wire = definition.clone();
            wire["schema_version"] = version.into();
            let error = serde_json::from_value::<DefinitionIr>(wire).unwrap_err();
            assert!(error.to_string().contains(&expected_schema), "{error}");
        }
    }
}
