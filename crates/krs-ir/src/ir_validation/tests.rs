use super::*;
use crate::{
    DefinitionLevel, DefinitionSortRef, DefinitionTerm, DefinitionValidationError, ItemKind,
    SemanticLevel, SemanticSortRef, SemanticTerm, SemanticValidationError, SymbolId, SymbolKind,
    testing,
};

fn check<L: Validation>(term: &IrTerm<L>, declarations: &Declarations<L>) -> Result<(), L::Error> {
    validate_term::<L>(
        term,
        &BTreeMap::new(),
        declarations,
        &BTreeMap::new(),
        &BTreeMap::new(),
        &mut BTreeSet::new(),
    )
}

#[test]
fn cell_references_keep_level_specific_checks_and_order() {
    let semantic_cell = SemanticTerm::cell(
        testing::origin("cell"),
        SemanticSortRef::int(),
        SemanticId::new("undeclared").unwrap(),
        vec![SemanticTerm::token(testing::origin("content"), SemanticSortRef::int(), "0").unwrap()],
    );
    assert_eq!(
        check::<SemanticLevel>(&semantic_cell, &BTreeMap::new()),
        Ok(())
    );
    let empty_semantic = SemanticTerm::cell(
        testing::origin("cell"),
        SemanticSortRef::int(),
        SemanticId::new("undeclared").unwrap(),
        Vec::new(),
    );
    assert_eq!(
        check::<SemanticLevel>(&empty_semantic, &BTreeMap::new()),
        Err(SemanticValidationError::InvalidCellFraming),
    );

    let id = SymbolId::new("undeclared").unwrap();
    let empty_definition = DefinitionTerm::cell(
        testing::origin("cell"),
        DefinitionSortRef::int(),
        id.clone(),
        Vec::new(),
    );
    assert_eq!(
        check::<DefinitionLevel>(&empty_definition, &BTreeMap::new()),
        Err(DefinitionValidationError::DanglingSymbol(id.clone())),
    );
    assert_eq!(
        check::<DefinitionLevel>(
            &empty_definition,
            &BTreeMap::from([(id.clone(), SymbolKind::Sort)])
        ),
        Err(DefinitionValidationError::WrongSymbolKind {
            id: id.clone(),
            expected: SymbolKind::Cell,
            actual: SymbolKind::Sort,
        }),
    );
    assert_eq!(
        check::<DefinitionLevel>(&empty_definition, &BTreeMap::from([(id, SymbolKind::Cell)])),
        Err(DefinitionValidationError::InvalidCellFraming),
    );
}

#[test]
fn applications_keep_missing_reference_and_wrong_role_errors() {
    let authored = testing::item("terms", "constructor", ItemKind::Constructor);
    let semantic = SemanticTerm::application(
        testing::origin("application"),
        SemanticSortRef::int(),
        ApplicationRef::Declared(authored.clone()),
        Vec::new(),
    );
    for declarations in [
        BTreeMap::new(),
        BTreeMap::from([(authored.clone(), ItemKind::Constructor)]),
    ] {
        assert_eq!(
            check::<SemanticLevel>(&semantic, &declarations),
            Err(SemanticValidationError::DanglingProduction(Box::new(
                authored.clone()
            ))),
        );
    }
    assert_eq!(
        check::<SemanticLevel>(
            &semantic,
            &BTreeMap::from([(authored.clone(), ItemKind::Sort)])
        ),
        Err(SemanticValidationError::WrongItemKind {
            id: Box::new(authored),
            expected: ItemKind::Constructor,
            actual: ItemKind::Sort,
        }),
    );

    let symbol = SymbolId::new("constructor").unwrap();
    let definition = DefinitionTerm::application(
        testing::origin("application"),
        DefinitionSortRef::int(),
        ApplicationRef::Declared(symbol.clone()),
        Vec::new(),
    );
    for declarations in [
        BTreeMap::new(),
        BTreeMap::from([(symbol.clone(), SymbolKind::Production)]),
    ] {
        assert_eq!(
            check::<DefinitionLevel>(&definition, &declarations),
            Err(DefinitionValidationError::DanglingSymbol(symbol.clone())),
        );
    }
    assert_eq!(
        check::<DefinitionLevel>(
            &definition,
            &BTreeMap::from([(symbol.clone(), SymbolKind::Sort)])
        ),
        Err(DefinitionValidationError::WrongSymbolKind {
            id: symbol,
            expected: SymbolKind::Production,
            actual: SymbolKind::Sort,
        }),
    );
}

#[test]
fn duplicate_term_origins_precede_dangling_sorts_and_variables() {
    fn duplicate<L: Validation>(term: &IrTerm<L>) -> Result<(), L::Error> {
        validate_term::<L>(
            term,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &mut BTreeSet::from([term.origin().key().clone()]),
        )
    }
    let origin = testing::origin("duplicate");
    let semantic = SemanticTerm::variable(
        origin.clone(),
        SemanticSortRef::Declared(testing::item("sorts", "Missing", ItemKind::Sort)),
        SemanticId::new("missing").unwrap(),
    );
    assert_eq!(
        duplicate::<SemanticLevel>(&semantic),
        Err(SemanticValidationError::DuplicateSourceMapKey(
            origin.key().clone()
        )),
    );
    let definition = DefinitionTerm::variable(
        origin.clone(),
        DefinitionSortRef::Declared(SymbolId::new("missing").unwrap()),
        SemanticId::new("missing").unwrap(),
    );
    assert_eq!(
        duplicate::<DefinitionLevel>(&definition),
        Err(DefinitionValidationError::DuplicateSourceMapKey(
            origin.key().clone()
        )),
    );
}
