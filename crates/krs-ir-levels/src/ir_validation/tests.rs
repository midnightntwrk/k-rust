use super::*;
use crate::{
    DefinitionLevel, DefinitionSortRef, DefinitionTerm, DefinitionValidationError, SemanticLevel,
    SemanticSortRef, SemanticTerm, SemanticValidationError, SymbolId, SymbolKind,
};
use krs_ir::{ItemKind, testing};

fn check<L: Validation>(term: &IrTerm<L>, declarations: &Declarations<L>) -> Result<(), L::Error> {
    check_cells::<L>(term, declarations, &BTreeSet::new())
}

fn check_cells<L: Validation>(
    term: &IrTerm<L>,
    declarations: &Declarations<L>,
    cell_ids: &BTreeSet<L::Cell>,
) -> Result<(), L::Error> {
    validate_term::<L>(
        term,
        &BTreeMap::new(),
        declarations,
        &BTreeMap::new(),
        &BTreeMap::new(),
        cell_ids,
        &mut BTreeSet::new(),
    )?;
    if !L::CHECK_CELL_REFERENCES_DURING_TERM_VALIDATION {
        validate_term_cell_references::<L>(term, declarations, cell_ids)?;
    }
    Ok(())
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
        Err(SemanticValidationError::DanglingCell(
            SemanticId::new("undeclared").unwrap()
        ))
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
    let registered = BTreeSet::from([SemanticId::new("undeclared").unwrap()]);
    assert_eq!(
        check_cells::<SemanticLevel>(&semantic_cell, &BTreeMap::new(), &registered),
        Ok(())
    );
    assert_eq!(
        check_cells::<SemanticLevel>(&empty_semantic, &BTreeMap::new(), &registered),
        Err(SemanticValidationError::InvalidCellFraming)
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
            &BTreeSet::new(),
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

/// A level's production attribute.
type LevelAttribute<L> = ProductionAttribute<<L as IrLevel>::Sort, <L as IrLevel>::Declaration>;

fn bn128_point_check<L: Validation>(
    sorts: &BTreeMap<&L::Declaration, &str>,
    point_sort: &L::Sort,
    constructors: &[(usize, Option<LevelAttribute<L>>)],
    hook: HookOperation,
) -> Result<(), L::Error> {
    let constructor_items = constructors
        .iter()
        .map(|(arity, _)| {
            (0..*arity)
                .map(|index| {
                    GrammarProductionItem::non_terminal(
                        testing::origin("point-field"),
                        ProductionFieldId::new(format!("field{index}")).unwrap(),
                        L::builtin_sort(BuiltinSort::Int),
                    )
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let constructor_attributes = constructors
        .iter()
        .map(|(_, attribute)| attribute.iter().cloned().collect::<Vec<_>>())
        .collect::<Vec<_>>();
    let result = L::builtin_sort(BuiltinSort::Bool);
    let argument_sorts = match hook {
        HookOperation::KryptoBn128Add => vec![point_sort.clone(), point_sort.clone()],
        HookOperation::KryptoBn128Mul => {
            vec![point_sort.clone(), L::builtin_sort(BuiltinSort::Int)]
        }
        HookOperation::KryptoBn128Ate => vec![L::builtin_sort(BuiltinSort::List); 2],
        _ => vec![point_sort.clone()],
    };
    let hook_items = argument_sorts
        .into_iter()
        .enumerate()
        .map(|(index, sort)| {
            GrammarProductionItem::non_terminal(
                testing::origin("hook-point"),
                ProductionFieldId::new(format!("argument{index}")).unwrap(),
                sort,
            )
        })
        .collect::<Vec<_>>();
    let hook_attributes = vec![ProductionAttribute::Hook {
        origin: testing::origin("hook"),
        operation: hook,
    }];
    let hook_result = if matches!(
        hook,
        HookOperation::KryptoBn128Add | HookOperation::KryptoBn128Mul
    ) {
        point_sort
    } else {
        &result
    };
    let productions = constructor_items
        .iter()
        .zip(&constructor_attributes)
        .map(|(items, attributes)| ProductionView {
            result_sort: point_sort,
            items,
            attributes,
        })
        .chain(std::iter::once(ProductionView {
            result_sort: hook_result,
            items: &hook_items,
            attributes: &hook_attributes,
        }));
    validate_hook_point_constructors::<L>(sorts, productions)
}

#[test]
fn bn128_point_constructors_are_checked_in_both_levels() {
    let semantic_id = testing::item("points", "G1Point", ItemKind::Sort);
    let semantic_sort = SemanticSortRef::declared(semantic_id.clone());
    let definition_id = SymbolId::new("point").unwrap();
    let definition_sort = DefinitionSortRef::declared(definition_id.clone());
    for hook in [
        HookOperation::KryptoBn128Valid,
        HookOperation::KryptoBn128Add,
        HookOperation::KryptoBn128Mul,
    ] {
        assert_eq!(
            bn128_point_check::<SemanticLevel>(
                &BTreeMap::from([(&semantic_id, "G1Point")]),
                &semantic_sort,
                &[(2, None)],
                hook,
            ),
            Ok(())
        );
        assert_eq!(
            bn128_point_check::<DefinitionLevel>(
                &BTreeMap::from([(&definition_id, "G1Point")]),
                &definition_sort,
                &[(2, None)],
                hook,
            ),
            Ok(())
        );
        for (name, constructors, count) in [
            ("OtherPoint", vec![(2, None)], 1),
            ("G1Point", vec![], 0),
            ("G1Point", vec![(2, None), (2, None)], 2),
            ("G1Point", vec![(3, None)], 0),
        ] {
            assert_eq!(
                bn128_point_check::<SemanticLevel>(
                    &BTreeMap::from([(&semantic_id, name)]),
                    &semantic_sort,
                    &constructors,
                    hook,
                ),
                Err(SemanticValidationError::InvalidBn128PointConstructor {
                    hook,
                    sort: name.to_owned(),
                    expected_signature: krs_ir::Bn128PointSignature::G1,
                    matching_constructors: count,
                })
            );
        }
    }
    for attribute in [
        ProductionAttribute::Function {
            origin: testing::origin("function"),
        },
        ProductionAttribute::Alias {
            origin: testing::origin("alias"),
        },
        ProductionAttribute::Bracket {
            origin: testing::origin("bracket"),
        },
        ProductionAttribute::Token {
            origin: testing::origin("token"),
            lexical_precedence: None,
        },
    ] {
        assert_eq!(
            bn128_point_check::<SemanticLevel>(
                &BTreeMap::from([(&semantic_id, "G1Point")]),
                &semantic_sort,
                &[(2, Some(attribute))],
                HookOperation::KryptoBn128Valid,
            ),
            Err(SemanticValidationError::InvalidBn128PointConstructor {
                hook: HookOperation::KryptoBn128Valid,
                sort: "G1Point".to_owned(),
                expected_signature: krs_ir::Bn128PointSignature::G1,
                matching_constructors: 0,
            })
        );
    }
}

#[test]
fn bn128_g2_and_pairing_require_the_four_integer_constructor() {
    let id = testing::item("points", "G2Point", ItemKind::Sort);
    let sort = SemanticSortRef::declared(id.clone());
    assert_eq!(
        bn128_point_check::<SemanticLevel>(
            &BTreeMap::from([(&id, "G2Point")]),
            &sort,
            &[(4, None)],
            HookOperation::KryptoBn128G2Valid,
        ),
        Ok(())
    );
    assert_eq!(
        bn128_point_check::<SemanticLevel>(
            &BTreeMap::from([(&id, "G2Point")]),
            &sort,
            &[(2, None)],
            HookOperation::KryptoBn128G2Valid,
        ),
        Err(SemanticValidationError::InvalidBn128PointConstructor {
            hook: HookOperation::KryptoBn128G2Valid,
            sort: "G2Point".to_owned(),
            expected_signature: krs_ir::Bn128PointSignature::G2,
            matching_constructors: 0,
        })
    );
    let g1_id = testing::item("points", "G1Point", ItemKind::Sort);
    let g1_sort = SemanticSortRef::declared(g1_id.clone());
    assert_eq!(
        bn128_point_check::<SemanticLevel>(
            &BTreeMap::from([(&g1_id, "G1Point"), (&id, "G2Point")]),
            &g1_sort,
            &[(2, None)],
            HookOperation::KryptoBn128Ate,
        ),
        Err(SemanticValidationError::InvalidBn128PointConstructor {
            hook: HookOperation::KryptoBn128Ate,
            sort: "G2Point".to_owned(),
            expected_signature: krs_ir::Bn128PointSignature::G2,
            matching_constructors: 0,
        })
    );
}

#[test]
fn bn128_semantic_sort_names_follow_definition_lowering() {
    let point_id = testing::item("points", "Coordinate", ItemKind::Sort);
    let point_sort = SemanticSortRef::declared(point_id.clone());
    let point = crate::SemanticProduction::new(
        testing::origin("point-production"),
        testing::item("points", "Point", ItemKind::Constructor),
        point_sort.clone(),
        (0..2)
            .map(|index| {
                GrammarProductionItem::non_terminal(
                    testing::origin(&format!("point-field-{index}")),
                    ProductionFieldId::new(format!("field{index}")).unwrap(),
                    SemanticSortRef::int(),
                )
            })
            .collect(),
        vec![],
    )
    .unwrap();
    let hook = crate::SemanticProduction::new(
        testing::origin("hook-production"),
        testing::item("points", "PointValid", ItemKind::Constructor),
        SemanticSortRef::bool(),
        vec![GrammarProductionItem::non_terminal(
            testing::origin("hook-argument"),
            ProductionFieldId::new("point").unwrap(),
            point_sort,
        )],
        vec![
            ProductionAttribute::Function {
                origin: testing::origin("function"),
            },
            ProductionAttribute::Total {
                origin: testing::origin("total"),
            },
            ProductionAttribute::Hook {
                origin: testing::origin("hook"),
                operation: HookOperation::KryptoBn128Valid,
            },
        ],
    )
    .unwrap();
    let cell_id = SemanticId::new("cell").unwrap();
    let configuration = FixedConfiguration::new(
        testing::origin("configuration"),
        SemanticId::new("configuration").unwrap(),
        krs_ir::ConfigurationRoot::GeneratedTop,
        vec![
            FixedCell::leaf(
                testing::origin("cell"),
                cell_id.clone(),
                "main",
                vec![],
                SemanticSortRef::int(),
            )
            .unwrap(),
        ],
        testing::origin("initializer"),
        SemanticId::new("initializer").unwrap(),
        vec![],
        vec![FixedInitializerCell::term(
            testing::origin("initialized-cell"),
            cell_id,
            SemanticTerm::token(testing::origin("zero"), SemanticSortRef::int(), "0").unwrap(),
        )],
    )
    .unwrap();
    let theory = |symbol| {
        crate::SemanticTheory::new(vec![crate::SemanticModule::new(
            testing::origin("module"),
            krs_ir::ModuleId::new("POINTS").unwrap(),
            vec![],
            vec![crate::SemanticSort::with_api(
                testing::origin("sort"),
                point_id.clone(),
                krs_ir::RustVisibility::Inherited,
                Some(krs_ir::ExplicitSymbol::new(symbol).unwrap()),
            )],
            vec![],
            vec![point.clone(), hook.clone()],
            vec![],
            vec![],
            Some(configuration.clone()),
            vec![],
        )])
    };
    assert!(theory("public::G1Point").is_ok());
    assert_eq!(
        theory("public::OtherPoint"),
        Err(SemanticValidationError::InvalidBn128PointConstructor {
            hook: HookOperation::KryptoBn128Valid,
            sort: "OtherPoint".to_owned(),
            expected_signature: krs_ir::Bn128PointSignature::G1,
            matching_constructors: 1,
        })
    );
}

#[test]
fn bn128_pairing_accepts_both_named_point_constructors() {
    let g1_id = testing::item("points", "G1Point", ItemKind::Sort);
    let g2_id = testing::item("points", "G2Point", ItemKind::Sort);
    let g1 = SemanticSortRef::declared(g1_id.clone());
    let g2 = SemanticSortRef::declared(g2_id.clone());
    let result = SemanticSortRef::bool();
    let items = |arity| {
        (0..arity)
            .map(|index| {
                GrammarProductionItem::non_terminal(
                    testing::origin("coordinate"),
                    ProductionFieldId::new(format!("coordinate{index}")).unwrap(),
                    SemanticSortRef::int(),
                )
            })
            .collect::<Vec<_>>()
    };
    let g1_items = items(2);
    let g2_items = items(4);
    let hook_items = (0..2)
        .map(|index| {
            GrammarProductionItem::non_terminal(
                testing::origin("hook-list"),
                ProductionFieldId::new(format!("points{index}")).unwrap(),
                SemanticSortRef::list(),
            )
        })
        .collect::<Vec<_>>();
    let attributes = vec![ProductionAttribute::Hook {
        origin: testing::origin("hook"),
        operation: HookOperation::KryptoBn128Ate,
    }];
    assert_eq!(
        validate_hook_point_constructors::<SemanticLevel>(
            &BTreeMap::from([(&g1_id, "G1Point"), (&g2_id, "G2Point")]),
            vec![
                ProductionView {
                    result_sort: &g1,
                    items: &g1_items,
                    attributes: &[]
                },
                ProductionView {
                    result_sort: &g2,
                    items: &g2_items,
                    attributes: &[]
                },
                ProductionView {
                    result_sort: &result,
                    items: &hook_items,
                    attributes: &attributes
                },
            ]
            .into_iter(),
        ),
        Ok(())
    );
}

fn check_context_alias<L: Validation>(
    alias: &crate::IrContextAlias<L>,
    configuration: Option<&Configuration<L>>,
    declarations: &Declarations<L>,
    signatures: &Signatures<L>,
    sort_parents: &SortParents<L>,
    cell_ids: &BTreeSet<L::Cell>,
    nodes: &mut BTreeSet<SourceMapKey>,
) -> Result<(), L::Error> {
    validate_context_alias::<L>(
        alias,
        declarations,
        signatures,
        sort_parents,
        cell_ids,
        nodes,
    )?;
    if !L::CHECK_CELL_REFERENCES_DURING_TERM_VALIDATION {
        for cell in alias.body().cells() {
            validate_term_cell_references::<L>(cell.pattern(), declarations, cell_ids)?;
        }
    }
    validate_context_alias_frames::<L>(alias, configuration, declarations)
}

fn alias<L: Validation>(
    cell: L::Cell,
    pattern: IrTerm<L>,
    frame: CellContentFrame,
    variables: Vec<IrVariable<L>>,
) -> crate::IrContextAlias<L> {
    crate::IrContextAlias::new(
        testing::origin("alias"),
        testing::item("contexts", "eval", ItemKind::ContextAlias),
        testing::origin("name"),
        "eval".into(),
        testing::origin("here"),
        SemanticId::new("HERE").unwrap(),
        variables,
        krs_ir::FixedConfigurationPattern::new(
            testing::origin("pattern"),
            SemanticId::new("configuration").unwrap(),
            vec![krs_ir::FixedCellPattern::new(
                testing::origin("cell"),
                cell,
                pattern,
                frame,
            )],
            Vec::new(),
        )
        .unwrap(),
    )
}

fn alias_configuration<L: Validation>(cell: L::Cell, sort: L::Sort) -> Configuration<L> {
    FixedConfiguration::new(
        testing::origin("configuration"),
        SemanticId::new("configuration").unwrap(),
        krs_ir::ConfigurationRoot::GeneratedTop,
        vec![
            FixedCell::leaf(
                testing::origin("declared-cell"),
                cell.clone(),
                "k",
                vec![],
                sort.clone(),
            )
            .unwrap(),
        ],
        testing::origin("initializer"),
        SemanticId::new("initializer").unwrap(),
        vec![],
        vec![FixedInitializerCell::term(
            testing::origin("initialized-cell"),
            cell,
            IrTerm::<L>::token(testing::origin("zero"), sort, "0").unwrap(),
        )],
    )
    .unwrap()
}

#[expect(
    clippy::too_many_lines,
    reason = "The same acceptance and rejection cases run against both identity representations."
)]
fn context_alias_checks<L: Validation>(cell: &L::Cell, declarations: &Declarations<L>)
where
    L::Error: Eq + std::fmt::Debug,
{
    let here = SemanticId::new("HERE").unwrap();
    let tail = SemanticId::new("tail").unwrap();
    let cell_ids = BTreeSet::from([cell.clone()]);
    let check = |alias: &crate::IrContextAlias<L>| {
        let configuration = alias_configuration::<L>(
            cell.clone(),
            alias.body().cells()[0].pattern().sort().clone(),
        );
        check_context_alias::<L>(
            alias,
            Some(&configuration),
            declarations,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &cell_ids,
            &mut BTreeSet::new(),
        )
    };
    let variable = || {
        IrTerm::<L>::variable(
            testing::origin("use"),
            L::builtin_sort(BuiltinSort::Int),
            here.clone(),
        )
    };
    let variables = || {
        vec![IrVariable::<L>::new(
            here.clone(),
            L::builtin_sort(BuiltinSort::Int),
        )]
    };
    let sequence = || IrTerm::<L> {
        origin: testing::origin("sequence"),
        sort: L::builtin_sort(BuiltinSort::KSequence),
        kind: IrTermKind::KSequence {
            item_sort: L::builtin_sort(BuiltinSort::Int),
            items: vec![variable()],
        },
    };
    let frame = |binding| CellContentFrame::KSequenceTail {
        origin: testing::origin("frame"),
        binding,
    };
    let scalar_configuration =
        alias_configuration::<L>(cell.clone(), L::builtin_sort(BuiltinSort::KSequence));
    let scalar_alias = alias::<L>(
        cell.clone(),
        variable(),
        frame(Some(tail.clone())),
        vec![
            IrVariable::<L>::new(here.clone(), L::builtin_sort(BuiltinSort::Int)),
            IrVariable::<L>::new(tail.clone(), L::builtin_sort(BuiltinSort::KSequence)),
        ],
    );
    assert_eq!(
        check_context_alias::<L>(
            &scalar_alias,
            Some(&scalar_configuration),
            declarations,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &cell_ids,
            &mut BTreeSet::new(),
        ),
        Ok(())
    );
    assert_eq!(
        check(&alias::<L>(
            cell.clone(),
            variable(),
            CellContentFrame::Exact,
            variables()
        )),
        Ok(())
    );
    assert_eq!(
        check(&alias::<L>(
            cell.clone(),
            sequence(),
            frame(None),
            variables()
        )),
        Ok(())
    );
    let mut bound = variables();
    bound.push(IrVariable::<L>::new(
        tail.clone(),
        L::builtin_sort(BuiltinSort::KSequence),
    ));
    assert_eq!(
        check(&alias::<L>(
            cell.clone(),
            sequence(),
            frame(Some(tail.clone())),
            bound
        )),
        Ok(())
    );

    assert_eq!(
        check(&alias::<L>(
            cell.clone(),
            variable(),
            frame(None),
            variables()
        )),
        Err(L::error(ValidationError::ContextAliasFrameSortMismatch))
    );
    assert_eq!(
        check(&alias::<L>(
            cell.clone(),
            sequence(),
            frame(Some(tail.clone())),
            variables()
        )),
        Err(L::error(ValidationError::ContextAliasFrameBindingMismatch(
            tail.clone()
        )))
    );
    let mut wrong = variables();
    wrong.push(IrVariable::<L>::new(
        tail.clone(),
        L::builtin_sort(BuiltinSort::Int),
    ));
    assert_eq!(
        check(&alias::<L>(
            cell.clone(),
            sequence(),
            frame(Some(tail.clone())),
            wrong
        )),
        Err(L::error(ValidationError::ContextAliasFrameBindingMismatch(
            tail.clone()
        )))
    );
    let mut unused = variables();
    unused.push(IrVariable::<L>::new(
        tail,
        L::builtin_sort(BuiltinSort::Int),
    ));
    assert_eq!(
        check(&alias::<L>(
            cell.clone(),
            variable(),
            CellContentFrame::Exact,
            unused
        )),
        Err(L::error(ValidationError::ContextAliasVariableClosure))
    );

    let dangling = SemanticId::new("dangling").unwrap();
    assert_eq!(
        check(&alias::<L>(
            cell.clone(),
            IrTerm::variable(
                testing::origin("use"),
                L::builtin_sort(BuiltinSort::Int),
                dangling.clone()
            ),
            CellContentFrame::Exact,
            variables()
        )),
        Err(L::error(ValidationError::DanglingVariable(dangling)))
    );
    assert_eq!(
        check(&alias::<L>(
            cell.clone(),
            IrTerm::variable(
                testing::origin("use"),
                L::builtin_sort(BuiltinSort::Map),
                here.clone()
            ),
            CellContentFrame::Exact,
            variables()
        )),
        Err(L::error(ValidationError::VariableSortMismatch(
            here.clone()
        )))
    );

    let map_variable = || {
        IrTerm::<L>::variable(
            testing::origin("map-use"),
            L::builtin_sort(BuiltinSort::Map),
            here.clone(),
        )
    };
    let map_variables = || {
        vec![
            IrVariable::<L>::new(here.clone(), L::builtin_sort(BuiltinSort::Map)),
            IrVariable::<L>::new(
                SemanticId::new("rest").unwrap(),
                L::builtin_sort(BuiltinSort::Map),
            ),
        ]
    };
    assert_eq!(
        check(&alias::<L>(
            cell.clone(),
            map_variable(),
            CellContentFrame::MapRemainder {
                origin: testing::origin("frame"),
                binding: Some(SemanticId::new("rest").unwrap())
            },
            map_variables()
        )),
        Ok(())
    );
    assert_eq!(
        check(&alias::<L>(
            cell.clone(),
            variable(),
            CellContentFrame::MapRemainder {
                origin: testing::origin("frame"),
                binding: None
            },
            variables()
        )),
        Err(L::error(ValidationError::ContextAliasFrameSortMismatch))
    );
}

#[test]
fn context_alias_body_and_frame_checks_are_shared() {
    context_alias_checks::<SemanticLevel>(&SemanticId::new("k").unwrap(), &BTreeMap::new());
    let cell = SymbolId::new("k").unwrap();
    context_alias_checks::<DefinitionLevel>(
        &cell,
        &BTreeMap::from([(cell.clone(), SymbolKind::Cell)]),
    );
}

#[test]
fn bn128_point_coordinates_must_all_have_builtin_integer_sort() {
    let id = testing::item("points", "G1Point", ItemKind::Sort);
    let point = SemanticSortRef::declared(id.clone());
    let result = SemanticSortRef::bool();
    let attributes = vec![ProductionAttribute::Hook {
        origin: testing::origin("hook"),
        operation: HookOperation::KryptoBn128Valid,
    }];
    let hook_items = vec![GrammarProductionItem::non_terminal(
        testing::origin("hook-argument"),
        ProductionFieldId::new("point").unwrap(),
        point.clone(),
    )];
    let coordinate_items = [SemanticSortRef::int(), SemanticSortRef::bool()]
        .into_iter()
        .enumerate()
        .map(|(index, sort)| {
            GrammarProductionItem::non_terminal(
                testing::origin("coordinate"),
                ProductionFieldId::new(format!("coordinate{index}")).unwrap(),
                sort,
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        validate_hook_point_constructors::<SemanticLevel>(
            &BTreeMap::from([(&id, "G1Point")]),
            vec![
                ProductionView {
                    result_sort: &point,
                    items: &coordinate_items,
                    attributes: &[]
                },
                ProductionView {
                    result_sort: &result,
                    items: &hook_items,
                    attributes: &attributes
                },
            ]
            .into_iter(),
        ),
        Err(SemanticValidationError::InvalidBn128PointConstructor {
            hook: HookOperation::KryptoBn128Valid,
            sort: "G1Point".to_owned(),
            expected_signature: krs_ir::Bn128PointSignature::G1,
            matching_constructors: 0,
        })
    );
}

#[test]
fn semantic_theory_checks_alias_bodies_against_registered_cells() {
    let cell = SemanticId::new("k").unwrap();
    let configuration = FixedConfiguration::new(
        testing::origin("configuration"),
        SemanticId::new("configuration").unwrap(),
        krs_ir::ConfigurationRoot::GeneratedTop,
        vec![
            FixedCell::leaf(
                testing::origin("declared-cell"),
                cell.clone(),
                "k",
                vec![],
                SemanticSortRef::int(),
            )
            .unwrap(),
        ],
        testing::origin("initializer"),
        SemanticId::new("initializer").unwrap(),
        vec![],
        vec![FixedInitializerCell::term(
            testing::origin("initialized-cell"),
            cell.clone(),
            SemanticTerm::token(testing::origin("zero"), SemanticSortRef::int(), "0").unwrap(),
        )],
    )
    .unwrap();
    let here = SemanticId::new("HERE").unwrap();
    let valid = alias::<SemanticLevel>(
        cell,
        SemanticTerm::variable(testing::origin("use"), SemanticSortRef::int(), here.clone()),
        CellContentFrame::Exact,
        vec![crate::SemanticVariable::new(here, SemanticSortRef::int())],
    );
    let theory = |alias| {
        crate::SemanticTheory::new(vec![crate::SemanticModule::new_with_context_aliases(
            testing::origin("module"),
            krs_ir::ModuleId::new("CONTEXTS").unwrap(),
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            Some(configuration.clone()),
            vec![alias],
            vec![],
        )])
    };
    assert!(theory(valid.clone()).is_ok());
    // Configuration identities share the semantic namespace but are not fixed-cell declarations.
    let not_a_cell = SemanticId::new("configuration").unwrap();
    let mut dangling_cell = valid.clone();
    dangling_cell.body = krs_ir::FixedConfigurationPattern::new(
        testing::origin("pattern"),
        not_a_cell.clone(),
        vec![krs_ir::FixedCellPattern::new(
            testing::origin("cell"),
            not_a_cell.clone(),
            valid.body.cells()[0].pattern().clone(),
            CellContentFrame::Exact,
        )],
        vec![],
    )
    .unwrap();
    assert_eq!(
        theory(dangling_cell),
        Err(SemanticValidationError::DanglingCell(not_a_cell))
    );
    let mut dangling_variable = valid;
    let variable = SemanticId::new("missing").unwrap();
    dangling_variable.body = krs_ir::FixedConfigurationPattern::new(
        testing::origin("pattern"),
        SemanticId::new("configuration").unwrap(),
        vec![krs_ir::FixedCellPattern::new(
            testing::origin("cell"),
            SemanticId::new("k").unwrap(),
            SemanticTerm::variable(
                testing::origin("use"),
                SemanticSortRef::int(),
                variable.clone(),
            ),
            CellContentFrame::Exact,
        )],
        vec![],
    )
    .unwrap();
    assert_eq!(
        theory(dangling_variable),
        Err(SemanticValidationError::DanglingVariable(variable))
    );
}

#[test]
fn semantic_sentence_errors_precede_new_cell_reference_checks() {
    let cell = SemanticId::new("k").unwrap();
    let missing = SemanticId::new("missing").unwrap();
    let configuration = alias_configuration::<SemanticLevel>(cell, SemanticSortRef::int());
    let theory = |variables| {
        let body = SemanticTerm::rewrite(
            testing::origin("rewrite"),
            SemanticSortRef::int(),
            SemanticTerm::cell(
                testing::origin("cell-use"),
                SemanticSortRef::int(),
                missing.clone(),
                vec![
                    SemanticTerm::token(testing::origin("child"), SemanticSortRef::int(), "0")
                        .unwrap(),
                ],
            ),
            SemanticTerm::token(testing::origin("result"), SemanticSortRef::int(), "0").unwrap(),
        )
        .unwrap();
        let rule = crate::SemanticRule::new(
            testing::origin("rule"),
            testing::item("rules", "step", ItemKind::Rule),
            SentenceKind::Transition,
            variables,
            body,
        )
        .unwrap();
        crate::SemanticTheory::new(vec![crate::SemanticModule::new(
            testing::origin("module"),
            krs_ir::ModuleId::new("CELLS").unwrap(),
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            Some(configuration.clone()),
            vec![rule],
        )])
    };
    assert_eq!(
        theory(vec![]),
        Err(SemanticValidationError::DanglingCell(missing.clone()))
    );
    assert_eq!(
        theory(vec![crate::SemanticVariable::new(
            SemanticId::new("unused").unwrap(),
            SemanticSortRef::int()
        )]),
        Err(SemanticValidationError::VariableClosure)
    );
}
