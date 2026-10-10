use k_rust::{
    definition::Sentence,
    kore::{ast::Pattern as KorePattern, parser::parse_definition},
};
use krs_ir::{
    ApplicationRef, CellContentFrame, CellPost, ClaimModality, ConfigurationRoot, FixedCell,
    FixedCellClause, FixedConfiguration, FixedConfigurationRewrite, FixedConfigurationVariable,
    FixedInitializerCell, NodeOrigin, ProductionFieldId, ProductionFieldReference,
    ProductionResultSort, SourceMapKey, StrictnessKind,
};
use krs_ir_levels::{
    DefinitionClaim, DefinitionIr, DefinitionModule, DefinitionProductionAttribute,
    DefinitionSentence, DefinitionSortRef, DefinitionTerm, LabelId, LabelIdentity,
    ProductionItem as IrProductionItem, ProductionSentence, RuleSentence, SymbolId, SymbolKind,
    SyntaxSortSentence,
};

use crate::{
    Author, Backend, CompileOptions, GeneratingPass, InputAddress, InputSentenceKind, InputSpace,
    NativeNodePlace, ProvenanceError, SentenceNodeRole, adapt_definition, adapt_definition_for,
    compile_definition, prepare_definition,
    test_fixtures::{node, semantic_id, smoke_definition, symbol},
};

fn unique_ids(kore: &str) -> std::collections::BTreeSet<String> {
    let definition = parse_definition(kore).expect("compiled KORE must reparse");
    definition
        .modules
        .iter()
        .flat_map(|module| &module.sentences)
        .filter_map(|sentence| match sentence {
            k_rust::kore::ast::Sentence::Axiom { attributes, .. }
            | k_rust::kore::ast::Sentence::Claim { attributes, .. } => Some(attributes),
            _ => None,
        })
        .flat_map(|attributes| &attributes.0)
        .filter_map(|pattern| match pattern {
            KorePattern::Application { symbol, arguments } if symbol.name == "UNIQUE'Unds'ID" => {
                let [KorePattern::String(id)] = arguments.as_slice() else {
                    panic!("UNIQUE_ID must have one string argument")
                };
                Some(id.as_utf8().expect("UNIQUE_ID must be UTF-8").to_owned())
            }
            _ => None,
        })
        .collect()
}

fn macro_unique_ids(macros: &str) -> std::collections::BTreeSet<String> {
    if macros.trim().is_empty() {
        return std::collections::BTreeSet::new();
    }
    unique_ids(&format!("module MACROS []\n{macros}\nendmodule []"))
}

#[test]
fn smoke_relation_covers_emitted_ids_and_authors() {
    let ir = smoke_definition();
    let artifacts = compile_definition(&ir, CompileOptions::default()).unwrap();
    for emitted in [
        &artifacts.definition_kore,
        &artifacts.syntax_definition_kore,
        &artifacts.macros_kore,
    ] {
        assert!(!emitted.contains("krs-source-map"));
    }
    let ids = artifacts
        .sentence_provenance
        .iter()
        .map(|(id, _)| id.to_owned())
        .collect::<std::collections::BTreeSet<_>>();
    let mut emitted_ids = unique_ids(&artifacts.definition_kore);
    emitted_ids.extend(macro_unique_ids(&artifacts.macros_kore));
    assert_eq!(emitted_ids, ids);
    let rule = &ir.modules()[0].sentences()[1];
    let key = rule.origin().key();
    let emitted = artifacts.sentence_provenance.emitted_by(key);
    assert!(!emitted.is_empty());
    for id in emitted {
        let provenance = artifacts.sentence_provenance.get(id).unwrap();
        assert!(provenance.authors().iter().any(|author| matches!(author,
            Author::Krs { origin, .. } if origin == rule.origin()
        )));
    }
    assert!(artifacts.sentence_provenance.iter().any(|(_, provenance)| {
        provenance.authors().is_empty()
            && provenance.generated_by() == Some(GeneratingPass::GenerateSortPredicateRules)
    }));
    assert!(artifacts.sentence_provenance.iter().any(|(_, provenance)| {
        provenance
            .authors()
            .iter()
            .any(|author| matches!(author, Author::Builtin { .. }))
    }));
}

#[test]
fn the_relation_round_trips_through_its_serde_form() {
    let artifacts = compile_definition(&smoke_definition(), CompileOptions::default()).unwrap();
    let relation = &artifacts.sentence_provenance;
    let json = serde_json::to_string(relation).unwrap();
    let decoded: crate::SentenceProvenance = serde_json::from_str(&json).unwrap();
    assert_eq!(&decoded, relation);
    assert_eq!(serde_json::to_string(&decoded).unwrap(), json);

    // Names from another k-rust pin are refused, not misread.
    let unknown_pass = json.replacen("\"generate-sort-predicate-rules\"", "\"no-such-pass\"", 1);
    assert_ne!(unknown_pass, json);
    assert!(serde_json::from_str::<crate::SentenceProvenance>(&unknown_pass).is_err());
    let unknown_kind = json.replacen("\"kind\":\"rule\"", "\"kind\":\"no-such-kind\"", 1);
    assert_ne!(unknown_kind, json);
    assert!(serde_json::from_str::<crate::SentenceProvenance>(&unknown_kind).is_err());
}

/// The smoke definition with one authored one-path claim, and that claim's origin.
fn smoke_definition_with_claim() -> (DefinitionIr, NodeOrigin) {
    let ir = smoke_definition();
    let main = &ir.modules()[0];
    let value = DefinitionSortRef::declared(SymbolId::new("sort.value").unwrap());
    let term = |key: &str, production: &str| {
        DefinitionTerm::k_sequence(
            node(&format!("{key}.sequence")),
            DefinitionSortRef::declared(SymbolId::new("sort.kitem").unwrap()),
            vec![DefinitionTerm::application(
                node(key),
                value.clone(),
                ApplicationRef::Declared(SymbolId::new(production).unwrap()),
                Vec::new(),
            )],
        )
    };
    let body = FixedConfigurationRewrite::new(
        node("def.claim.rewrite"),
        semantic_id("configuration.machine"),
        vec![FixedCellClause::new(
            node("def.claim.cell"),
            SymbolId::new("cell.k").unwrap(),
            term("def.claim.foo", "production.foo"),
            CellPost::Replace {
                term: term("def.claim.bar", "production.bar"),
            },
            CellContentFrame::Exact,
        )],
        Vec::new(),
    )
    .unwrap();
    let claim = DefinitionSentence::Rule(
        RuleSentence::new_configuration(
            node("def.claim"),
            LabelIdentity::new(
                LabelId::new("claim.foo-to-bar").unwrap(),
                "ORG-EXAMPLE-SMOKE.claims.foo-to-bar",
            )
            .unwrap(),
            krs_ir::ConfigurationSentenceKind::Claim,
            Vec::new(),
            body,
        )
        .with_claim(Some(DefinitionClaim::new(
            node("def.claim.modality"),
            ClaimModality::OnePath,
            None,
            Vec::new(),
        ))),
    );
    let origin = claim.origin().clone();
    let mut sentences = main.sentences().to_vec();
    sentences.push(claim);
    let main = DefinitionModule::new(
        main.origin().clone(),
        main.id().clone(),
        main.imports().iter().cloned().collect(),
        main.production_groups().to_vec(),
        sentences,
    );
    let ir = DefinitionIr::new(
        ir.main_module().clone(),
        vec![main, ir.modules()[1].clone()],
    )
    .unwrap();
    (ir, origin)
}

#[test]
fn authored_claim_has_an_emitted_identity_with_its_origin() {
    let (ir, origin) = smoke_definition_with_claim();
    let artifacts = compile_definition(
        &ir,
        CompileOptions {
            backend: Backend::Haskell,
            ..CompileOptions::default()
        },
    )
    .unwrap();
    assert_eq!(artifacts.omitted_claims, 0);
    let relation_ids = artifacts
        .sentence_provenance
        .iter()
        .map(|(id, _)| id.to_owned())
        .collect::<std::collections::BTreeSet<_>>();
    let mut emitted_ids = unique_ids(&artifacts.definition_kore);
    emitted_ids.extend(macro_unique_ids(&artifacts.macros_kore));
    assert_eq!(relation_ids, emitted_ids);
    let ids = artifacts.sentence_provenance.emitted_by(origin.key());
    assert!(!ids.is_empty());
    for id in ids {
        assert!(artifacts.sentence_provenance.get(id).unwrap().authors().iter().any(|author| {
            matches!(author, Author::Krs { kind: InputSentenceKind::Claim, origin: actual, .. } if actual == &origin)
        }));
    }
}

#[test]
fn llvm_compilation_omits_claims_and_keeps_provenance_consistent() {
    let (ir, origin) = smoke_definition_with_claim();
    let adapted = adapt_definition_for(&ir, Backend::Llvm).unwrap();
    assert_eq!(adapted.omitted_claims(), 1);
    assert!(adapted.definition().modules.iter().all(|module| {
        module
            .local_sentences
            .iter()
            .all(|sentence| !matches!(**sentence, Sentence::Claim { .. }))
    }));
    assert!(
        adapted
            .origins()
            .iter()
            .all(|mapping| mapping.key != *origin.key())
    );

    let artifacts = compile_definition(&ir, CompileOptions::default())
        .expect("a claim does not prevent concrete compilation");
    assert_eq!(artifacts.omitted_claims, 1);
    assert!(
        artifacts
            .sentence_provenance
            .emitted_by(origin.key())
            .is_empty()
    );
    let relation_ids = artifacts
        .sentence_provenance
        .iter()
        .map(|(id, _)| id.to_owned())
        .collect::<std::collections::BTreeSet<_>>();
    let mut emitted_ids = unique_ids(&artifacts.definition_kore);
    emitted_ids.extend(macro_unique_ids(&artifacts.macros_kore));
    assert_eq!(relation_ids, emitted_ids);
}

#[test]
fn equal_content_rules_share_identity_and_keep_both_authors() {
    let ir = smoke_definition();
    let main = &ir.modules()[0];
    let DefinitionSentence::Rule(first) = &main.sentences()[1] else {
        panic!("smoke main must contain a rule")
    };
    let second = DefinitionSentence::Rule(
        RuleSentence::new(
            node("def.rule.foo-to-bar-again"),
            LabelIdentity::new(
                LabelId::new("rule.foo-to-bar-again").unwrap(),
                "ORG-EXAMPLE-SMOKE.rules.foo-to-bar-again",
            )
            .unwrap(),
            first.kind(),
            Vec::new(),
            DefinitionTerm::rewrite(
                node("def.term.rule.rewrite-again"),
                DefinitionSortRef::declared(SymbolId::new("sort.value").unwrap()),
                DefinitionTerm::application(
                    node("def.term.rule.foo-again"),
                    DefinitionSortRef::declared(SymbolId::new("sort.value").unwrap()),
                    ApplicationRef::Declared(SymbolId::new("production.foo").unwrap()),
                    Vec::new(),
                ),
                DefinitionTerm::application(
                    node("def.term.rule.bar-again"),
                    DefinitionSortRef::declared(SymbolId::new("sort.value").unwrap()),
                    ApplicationRef::Declared(SymbolId::new("production.bar").unwrap()),
                    Vec::new(),
                ),
            )
            .unwrap(),
        )
        .unwrap(),
    );
    let mut main_sentences = main.sentences().to_vec();
    main_sentences.push(second);
    let main = DefinitionModule::new(
        main.origin().clone(),
        main.id().clone(),
        main.imports().iter().cloned().collect(),
        main.production_groups().to_vec(),
        main_sentences,
    );
    let ir = DefinitionIr::new(
        ir.main_module().clone(),
        vec![main, ir.modules()[1].clone()],
    )
    .unwrap();
    let artifacts = compile_definition(&ir, CompileOptions::default()).unwrap();
    let first_key = SourceMapKey::new("def.rule.foo-to-bar").unwrap();
    let second_key = SourceMapKey::new("def.rule.foo-to-bar-again").unwrap();
    let first_ids = artifacts.sentence_provenance.emitted_by(&first_key);
    let second_ids = artifacts.sentence_provenance.emitted_by(&second_key);
    assert_eq!(first_ids, second_ids);
    assert_eq!(first_ids.len(), 1);
    let authors = artifacts
        .sentence_provenance
        .get(&first_ids[0])
        .unwrap()
        .authors();
    let krs_keys = authors
        .iter()
        .filter_map(|author| match author {
            Author::Krs { origin, .. } => Some(origin.key().as_str()),
            Author::Builtin { .. } => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(krs_keys, [first_key.as_str(), second_key.as_str()]);
}

#[test]
fn strict_production_has_multiple_emitted_ids() {
    let ir = smoke_definition();
    let syntax = &ir.modules()[1];
    let value = DefinitionSortRef::declared(SymbolId::new("sort.value").unwrap());
    let strict = DefinitionSentence::Production(
        ProductionSentence::new(
            node("def.production.strict"),
            symbol("production.strict", "Lblstrict", SymbolKind::Production),
            value.clone(),
            vec![
                IrProductionItem::terminal(node("def.production.strict.open"), "strict(").unwrap(),
                IrProductionItem::non_terminal(
                    node("def.production.strict.field"),
                    ProductionFieldId::new("argument").unwrap(),
                    value,
                ),
                IrProductionItem::terminal(node("def.production.strict.close"), ")").unwrap(),
            ],
            vec![DefinitionProductionAttribute::Strictness {
                origin: node("def.production.strict.attribute"),
                kind: StrictnessKind::Strict,
                using: None,
                fields: vec![ProductionFieldReference::new(
                    node("def.production.strict.selected"),
                    ProductionFieldId::new("argument").unwrap(),
                )],
                result_sort: ProductionResultSort::new(
                    node("def.production.strict.result"),
                    DefinitionSortRef::declared(SymbolId::new("sort.kresult").unwrap()),
                ),
            }],
        )
        .unwrap(),
    );
    let strict_origin = strict.origin().clone();
    let mut syntax_sentences = syntax.sentences().to_vec();
    syntax_sentences.push(strict);
    let syntax = DefinitionModule::new(
        syntax.origin().clone(),
        syntax.id().clone(),
        syntax.imports().iter().cloned().collect(),
        syntax.production_groups().to_vec(),
        syntax_sentences,
    );
    let ir = DefinitionIr::new(
        ir.main_module().clone(),
        vec![ir.modules()[0].clone(), syntax],
    )
    .unwrap();
    let artifacts = compile_definition(&ir, CompileOptions::default()).unwrap();
    let ids = artifacts
        .sentence_provenance
        .emitted_by(strict_origin.key());
    assert!(ids.len() >= 2);
    for id in ids {
        assert!(artifacts.sentence_provenance.get(id).unwrap().authors().iter().any(|author| {
            matches!(author, Author::Krs { origin, kind: InputSentenceKind::Production, .. } if origin == &strict_origin)
        }));
    }
}

#[test]
fn two_cell_configuration_has_multiple_emitted_ids() {
    let ir = smoke_definition();
    let main = &ir.modules()[0];
    let program = semantic_id("program");
    let k_cell = SymbolId::new("cell.k").unwrap();
    let state_cell = SymbolId::new("cell.state").unwrap();
    let value = DefinitionSortRef::declared(SymbolId::new("sort.value").unwrap());
    let configuration = DefinitionSentence::Configuration(
        FixedConfiguration::new(
            node("def.configuration.two-cell"),
            semantic_id("configuration.machine"),
            ConfigurationRoot::GeneratedTop,
            vec![
                FixedCell::leaf(
                    node("def.cell.k.two-cell"),
                    k_cell.clone(),
                    "k",
                    Vec::new(),
                    DefinitionSortRef::k_sequence(),
                )
                .unwrap(),
                FixedCell::leaf(
                    node("def.cell.state"),
                    state_cell.clone(),
                    "state",
                    Vec::new(),
                    value.clone(),
                )
                .unwrap(),
            ],
            node("def.initializer.two-cell"),
            semantic_id("initializer.machine"),
            vec![
                FixedConfigurationVariable::new(
                    node("def.initializer.program.two-cell"),
                    program.clone(),
                    "PGM",
                    value.clone(),
                    true,
                )
                .unwrap(),
            ],
            vec![
                FixedInitializerCell::term(
                    node("def.initializer.k.two-cell"),
                    k_cell,
                    DefinitionTerm::k_sequence(
                        node("def.initializer.k.sequence.two-cell"),
                        DefinitionSortRef::declared(SymbolId::new("sort.kitem").unwrap()),
                        vec![DefinitionTerm::variable(
                            node("def.initializer.program.term.two-cell"),
                            value.clone(),
                            program,
                        )],
                    ),
                ),
                FixedInitializerCell::term(
                    node("def.initializer.state"),
                    state_cell,
                    DefinitionTerm::application(
                        node("def.initializer.state.foo"),
                        value,
                        ApplicationRef::Declared(SymbolId::new("production.foo").unwrap()),
                        Vec::new(),
                    ),
                ),
            ],
        )
        .unwrap(),
    );
    let origin = configuration.origin().clone();
    let mut sentences = main.sentences().to_vec();
    sentences[0] = configuration;
    let main = DefinitionModule::new(
        main.origin().clone(),
        main.id().clone(),
        main.imports().iter().cloned().collect(),
        main.production_groups().to_vec(),
        sentences,
    );
    let ir = DefinitionIr::new(
        ir.main_module().clone(),
        vec![main, ir.modules()[1].clone()],
    )
    .unwrap();
    let artifacts = compile_definition(&ir, CompileOptions::default()).unwrap();
    let ids = artifacts.sentence_provenance.emitted_by(origin.key());
    assert!(ids.len() >= 2);
    for id in ids {
        assert!(artifacts.sentence_provenance.get(id).unwrap().authors().iter().any(|author| {
            matches!(author, Author::Krs { origin: actual, kind: InputSentenceKind::Configuration, .. } if actual == &origin)
        }));
    }
}

#[test]
fn provenance_join_rejects_broken_input_addresses() {
    use std::collections::BTreeMap;

    use k_rust::kompile::EmittedSentenceProvenance;

    let ir = smoke_definition();
    let adapted = adapt_definition(&ir).unwrap();
    let loaded = prepare_definition(adapted.definition().clone(), Backend::Llvm).unwrap();
    let address = InputAddress {
        input: InputSpace::Structured,
        module: "SMOKE".to_owned(),
        index: 1,
    };
    let relation = |address: InputAddress, kind: InputSentenceKind| {
        BTreeMap::from([(
            "rule-id".to_owned(),
            EmittedSentenceProvenance {
                input_addresses: vec![address.clone()],
                input_sentence_kinds: BTreeMap::from([(address, kind)]),
                generated_by: None,
            },
        )])
    };
    let valid = relation(address.clone(), InputSentenceKind::Rule);
    assert!(super::join_sentence_provenance(&ir, &adapted, &loaded, &valid).is_ok());

    let mut missing = adapted.clone();
    missing.origins.retain(|mapping| {
        !(mapping.module == "SMOKE"
            && mapping.place
                == NativeNodePlace::Sentence {
                    index: 1,
                    role: SentenceNodeRole::Sentence,
                })
    });
    assert_eq!(
        super::join_sentence_provenance(&ir, &missing, &loaded, &valid),
        Err(ProvenanceError::MissingSentenceMapping(address.clone()))
    );

    let mut duplicate = adapted.clone();
    let mapping = duplicate
        .origins
        .iter()
        .find(|mapping| {
            mapping.module == "SMOKE"
                && mapping.place
                    == NativeNodePlace::Sentence {
                        index: 1,
                        role: SentenceNodeRole::Sentence,
                    }
        })
        .unwrap()
        .clone();
    duplicate.origins.push(mapping);
    assert_eq!(
        super::join_sentence_provenance(&ir, &duplicate, &loaded, &valid),
        Err(ProvenanceError::DuplicateSentenceMapping {
            module: "SMOKE".to_owned(),
            index: 1,
        })
    );

    let compile_address = InputAddress {
        input: InputSpace::Compile,
        ..address.clone()
    };
    assert_eq!(
        super::join_sentence_provenance(
            &ir,
            &adapted,
            &loaded,
            &relation(compile_address.clone(), InputSentenceKind::Rule),
        ),
        Err(ProvenanceError::LossyCompileAddress(compile_address))
    );

    assert_eq!(
        super::join_sentence_provenance(
            &ir,
            &adapted,
            &loaded,
            &relation(address.clone(), InputSentenceKind::Production),
        ),
        Err(ProvenanceError::KindMismatch {
            address: address.clone(),
            expected: InputSentenceKind::Rule,
            actual: InputSentenceKind::Production,
        })
    );

    let out_of_range = InputAddress {
        index: 100,
        ..address
    };
    assert_eq!(
        super::join_sentence_provenance(
            &ir,
            &adapted,
            &loaded,
            &relation(out_of_range.clone(), InputSentenceKind::Rule),
        ),
        Err(ProvenanceError::IndexOutOfRange(out_of_range))
    );
}

#[test]
fn provenance_join_uses_mapping_key_for_ir_sentence_kind() {
    use std::collections::BTreeMap;

    use k_rust::kompile::EmittedSentenceProvenance;

    let ir = smoke_definition();
    let adapted = adapt_definition(&ir).unwrap();
    let loaded = prepare_definition(adapted.definition().clone(), Backend::Llvm).unwrap();
    let main = &ir.modules()[0];
    let mut shifted_sentences = main.sentences().to_vec();
    shifted_sentences.push(DefinitionSentence::SyntaxSort(
        SyntaxSortSentence::new(
            node("def.middle"),
            symbol("sort.middle", "Middle", SymbolKind::Sort),
        )
        .unwrap(),
    ));
    let shifted_main = DefinitionModule::new(
        main.origin().clone(),
        main.id().clone(),
        main.imports().iter().cloned().collect(),
        main.production_groups().to_vec(),
        shifted_sentences,
    );
    let shifted_ir = DefinitionIr::new(
        ir.main_module().clone(),
        vec![shifted_main, ir.modules()[1].clone()],
    )
    .unwrap();
    assert_eq!(
        shifted_ir.modules()[0].sentences()[2].origin().key(),
        main.sentences()[1].origin().key()
    );
    let address = InputAddress {
        input: InputSpace::Structured,
        module: "SMOKE".to_owned(),
        index: 1,
    };
    let relation = BTreeMap::from([(
        "rule-id".to_owned(),
        EmittedSentenceProvenance {
            input_addresses: vec![address.clone()],
            input_sentence_kinds: BTreeMap::from([(address, InputSentenceKind::Rule)]),
            generated_by: None,
        },
    )]);
    assert!(super::join_sentence_provenance(&shifted_ir, &adapted, &loaded, &relation).is_ok());
}
