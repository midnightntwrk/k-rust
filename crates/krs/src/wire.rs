//! Runtime substitution of indexed, static host payloads.

use std::convert::Infallible;

use krs_ir::wire::{
    ItemSlot, WireApplicationReference, WireConfigurationReference, WireContextAliasReference,
    WireHeadRuleCellReference, WirePayload, WireSortReference, WireTypeReference,
};
use krs_ir::{
    HostApplicationReference, HostApplicationTarget, HostCellDeclarationReference,
    HostCellReference, HostConfigurationReference, HostContextAliasReference,
    HostDescriptorPayload, HostEnumVariantReference, HostHeadRuleCellReference, HostItemId,
    HostSortReference, HostStage, HostTypeKey, HostTypeReference, RefMap, WireStage,
};

/// Rust-resolved application identity inserted into a static descriptor payload.
#[doc(hidden)]
#[derive(Clone, Debug)]
pub enum __KrsTargetSlot {
    /// Build-local nominal Rust type identity.
    Nominal(HostTypeKey),
    /// Exact owner and generated marker for a Rust enum variant.
    Variant {
        owner: HostTypeKey,
        marker: HostTypeKey,
    },
    /// Application identity, including an inferred readable-rule head.
    Target(HostApplicationTarget),
}

/// Independently indexed Rust-resolved references for a static descriptor payload.
#[doc(hidden)]
#[derive(Clone, Copy, Debug, Default)]
pub struct __KrsSlots<'a> {
    /// Build-local Rust type identities.
    pub types: &'a [HostTypeKey],
    /// Macro-context identities for referenced items.
    pub items: &'a [HostItemId],
    /// Application identities.
    pub targets: &'a [__KrsTargetSlot],
}

/// Decode one static rule payload and insert the factory's Rust-resolved slots.
#[doc(hidden)]
#[inline(never)]
#[track_caller]
#[must_use]
pub fn __krs_host_payload(wire: &str, slots: __KrsSlots<'_>) -> HostDescriptorPayload {
    let payload: WirePayload = krs_ir::json::from_slice(wire.as_bytes())
        .unwrap_or_else(|error| panic!("KRS generated rule wire is malformed: {error}"));
    let payload = payload.try_map_refs(&mut Decoder { slots }).unwrap();
    match payload {
        krs_ir::wire::StaticPayload::StructuredRule(rule) => {
            HostDescriptorPayload::StructuredRule(rule)
        }
        krs_ir::wire::StaticPayload::HeadRule(rule) => HostDescriptorPayload::HeadRule(rule),
        krs_ir::wire::StaticPayload::Constructor(constructor) => {
            HostDescriptorPayload::Constructor(constructor.into())
        }
        krs_ir::wire::StaticPayload::Grammar(grammar) => HostDescriptorPayload::Grammar(grammar),
    }
}

struct Decoder<'a> {
    slots: __KrsSlots<'a>,
}

impl Decoder<'_> {
    fn type_reference(&self, wire: WireTypeReference) -> HostTypeReference {
        let key = *self.slots.types.get(wire.slot.0).unwrap_or_else(|| {
            panic!(
                "KRS generated rule wire has an invalid type slot {}",
                wire.slot.0
            )
        });
        HostTypeReference {
            key,
            authored_path: wire.authored_path,
        }
    }

    fn target(&self, wire: WireApplicationReference) -> HostApplicationReference {
        let target = match self.slots.targets.get(wire.target.0).unwrap_or_else(|| {
            panic!(
                "KRS generated rule wire has an invalid target slot {}",
                wire.target.0
            )
        }) {
            __KrsTargetSlot::Target(target) => target.clone(),
            __KrsTargetSlot::Nominal(key) => HostApplicationTarget::Nominal(HostTypeReference {
                key: *key,
                authored_path: wire.authored_path.clone(),
            }),
            __KrsTargetSlot::Variant { owner, marker } => {
                let (owner_path, _) = wire.authored_path.rsplit_once("::").unwrap_or_else(|| {
                    panic!("KRS generated rule wire has an unqualified enum variant path")
                });
                HostApplicationTarget::EnumVariant(
                    HostEnumVariantReference::new(
                        HostTypeReference {
                            key: *owner,
                            authored_path: owner_path.trim().to_owned(),
                        },
                        *marker,
                        wire.authored_path.clone(),
                    )
                    .expect("KRS generated rule wire has an invalid enum variant path"),
                )
            }
        };
        assert!(
            target.authored_path() == wire.authored_path
                || target
                    .authored_path()
                    .strip_suffix(&wire.authored_path)
                    .is_some_and(|prefix| prefix.ends_with("::")),
            "KRS generated rule wire has a mismatched authored application path"
        );
        HostApplicationReference {
            key: wire.key,
            target,
        }
    }
}

impl RefMap<WireStage, HostStage> for Decoder<'_> {
    type Error = Infallible;

    fn sort(&mut self, wire: WireSortReference) -> Result<HostSortReference, Self::Error> {
        Ok(HostSortReference {
            key: wire.key,
            target: self.type_reference(wire.target),
        })
    }

    fn application(
        &mut self,
        wire: WireApplicationReference,
    ) -> Result<HostApplicationReference, Self::Error> {
        Ok(self.target(wire))
    }

    fn nominal(&mut self, wire: WireTypeReference) -> Result<HostTypeReference, Self::Error> {
        Ok(self.type_reference(wire))
    }

    fn context_alias(
        &mut self,
        wire: WireContextAliasReference,
    ) -> Result<HostContextAliasReference, Self::Error> {
        Ok(HostContextAliasReference {
            key: wire.key,
            alias: self.item(wire.slot)?,
        })
    }

    fn configuration(
        &mut self,
        wire: WireConfigurationReference,
    ) -> Result<HostConfigurationReference, Self::Error> {
        Ok(HostConfigurationReference {
            key: wire.key,
            configuration: self.type_reference(wire.configuration),
        })
    }

    fn cell(&mut self, wire: Infallible) -> Result<HostCellReference, Self::Error> {
        match wire {}
    }

    fn head_rule_cell(
        &mut self,
        wire: WireHeadRuleCellReference,
    ) -> Result<HostHeadRuleCellReference, Self::Error> {
        Ok(HostHeadRuleCellReference {
            key: wire.key,
            name: wire.name,
        })
    }

    fn item(&mut self, slot: ItemSlot) -> Result<HostItemId, Self::Error> {
        Ok(self
            .slots
            .items
            .get(slot.0)
            .unwrap_or_else(|| panic!("KRS generated wire has an invalid item slot {}", slot.0))
            .clone())
    }

    fn cell_declaration(
        &mut self,
        wire: Infallible,
    ) -> Result<HostCellDeclarationReference, Self::Error> {
        match wire {}
    }

    fn initializer_owner(&mut self, wire: WireTypeReference) -> Result<HostTypeKey, Self::Error> {
        Ok(self.type_reference(wire).key)
    }

    fn parent(&mut self, wire: WireTypeReference) -> Result<HostTypeReference, Self::Error> {
        self.nominal(wire)
    }

    fn constructor_sort(
        &mut self,
        wire: WireSortReference,
    ) -> Result<HostSortReference, Self::Error> {
        self.sort(wire)
    }

    fn constructor_field_sort(
        &mut self,
        wire: WireTypeReference,
    ) -> Result<HostTypeReference, Self::Error> {
        self.nominal(wire)
    }
}

#[cfg(test)]
mod tests {
    use super::{__KrsSlots, __KrsTargetSlot, __krs_host_payload, Decoder};
    use krs_ir::wire::{
        ItemSlot, TargetSlot, TypeSlot, WireApplicationReference, WireConstructorDescriptor,
        WireConstructorFieldDescriptor, WireContextAliasReference, WireGrammarDescriptor,
        WireHeadRule, WirePayload, WireProduction, WireProductionAttribute, WireProductionItem,
        WireProductionOwner, WireSortReference, WireStructuredRule, WireTerm, WireTypeReference,
    };
    use krs_ir::{
        DescriptorAssociativitySentence, DescriptorGroupReference, DescriptorLiteral,
        DescriptorPrecedenceChain, GroupAssociativity, HostConstructorDescriptor,
        HostConstructorFieldDescriptor, HostContextAliasReference, HostDescriptorPayload,
        HostGrammarDescriptor, HostHeadRule, HostItemId, HostPackageKey, HostProduction,
        HostProductionAttribute, HostProductionItem, HostProductionOwner, HostSortReference,
        HostStructuredRuleDescriptor, HostTerm, HostTypeKey, HostTypeReference, ItemKind,
        ProductionGroupId, ProtocolHeadRuleResult, ProvenanceKey, ProvenanceRole, SentenceKind,
        StrictnessKind,
    };
    use std::any::TypeId;

    fn key(role: ProvenanceRole) -> ProvenanceKey {
        ProvenanceKey::new(role, 0)
    }

    fn type_id() -> TypeId {
        TypeId::of::<u64>()
    }

    fn marker_id() -> TypeId {
        TypeId::of::<u32>()
    }

    #[test]
    fn application_slots_reconstruct_diagnostic_paths() {
        let decoder = Decoder {
            slots: __KrsSlots {
                targets: &[
                    __KrsTargetSlot::Nominal(HostTypeKey(type_id)),
                    __KrsTargetSlot::Variant {
                        owner: HostTypeKey(type_id),
                        marker: HostTypeKey(marker_id),
                    },
                ],
                ..__KrsSlots::default()
            },
        };
        let nominal = decoder.target(WireApplicationReference {
            key: key(ProvenanceRole::TermApplicationHead),
            target: TargetSlot(0),
            authored_path: "int :: add".to_owned(),
        });
        assert_eq!(nominal.target.authored_path(), "int :: add");
        let variant = decoder.target(WireApplicationReference {
            key: key(ProvenanceRole::TermApplicationHead),
            target: TargetSlot(1),
            authored_path: "Op :: Gt".to_owned(),
        });
        assert_eq!(variant.target.authored_path(), "Op :: Gt");
    }

    fn type_slots() -> __KrsSlots<'static> {
        __KrsSlots {
            types: &[HostTypeKey(type_id)],
            ..__KrsSlots::default()
        }
    }

    fn wire_sort() -> WireSortReference {
        WireSortReference {
            key: key(ProvenanceRole::SortDeclaration),
            target: WireTypeReference {
                slot: TypeSlot(0),
                authored_path: "u64".to_owned(),
            },
        }
    }

    fn host_sort() -> HostSortReference {
        HostSortReference {
            key: key(ProvenanceRole::SortDeclaration),
            target: HostTypeReference {
                key: HostTypeKey(type_id),
                authored_path: "u64".to_owned(),
            },
        }
    }

    fn wire_term() -> WireTerm {
        WireTerm::Literal {
            key: key(ProvenanceRole::TermLiteral),
            literal: DescriptorLiteral::Int("42".to_owned()),
        }
    }

    fn host_term() -> HostTerm {
        HostTerm::Literal {
            key: key(ProvenanceRole::TermLiteral),
            literal: DescriptorLiteral::Int("42".to_owned()),
        }
    }

    fn decode(wire: &WirePayload, slots: __KrsSlots<'_>) -> HostDescriptorPayload {
        let encoded = serde_json::to_string(&wire).unwrap();
        let parsed: WirePayload = krs_ir::json::from_slice(encoded.as_bytes()).unwrap();
        assert_eq!(serde_json::to_string(&parsed).unwrap(), encoded);
        __krs_host_payload(&encoded, slots)
    }

    #[test]
    fn constructor_wire_matches_code_built_payload() {
        let wire = WirePayload::Constructor(WireConstructorDescriptor {
            sort: wire_sort(),
            fields: vec![WireConstructorFieldDescriptor {
                name: "value".to_owned(),
                sort: WireTypeReference {
                    slot: TypeSlot(0),
                    authored_path: "u64".to_owned(),
                },
            }],
        });
        let actual = decode(&wire, type_slots());
        let expected = HostDescriptorPayload::Constructor(HostConstructorDescriptor {
            sort: host_sort(),
            fields: vec![HostConstructorFieldDescriptor {
                name: "value".to_owned(),
                sort: HostTypeReference {
                    key: HostTypeKey(type_id),
                    authored_path: "u64".to_owned(),
                },
            }],
        });
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    }

    #[test]
    fn grammar_associativity_wire_matches_code_built_payload() {
        let sentence = DescriptorAssociativitySentence {
            key: key(ProvenanceRole::AssociativitySentence),
            associativity: GroupAssociativity::Left,
            groups: vec![DescriptorGroupReference {
                key: key(ProvenanceRole::AssociativityGroupReference),
                group: ProductionGroupId::new("arith").unwrap(),
            }],
        };
        let actual = decode(
            &WirePayload::Grammar(Box::new(WireGrammarDescriptor::Associativity {
                key: key(ProvenanceRole::AssociativityDeclaration),
                sentences: vec![sentence.clone()],
            })),
            __KrsSlots::default(),
        );
        let expected =
            HostDescriptorPayload::Grammar(Box::new(HostGrammarDescriptor::Associativity {
                key: key(ProvenanceRole::AssociativityDeclaration),
                sentences: vec![sentence],
            }));
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    }

    #[test]
    fn grammar_production_wire_matches_code_built_payload() {
        let wire = WirePayload::Grammar(Box::new(WireGrammarDescriptor::Production(
            WireProduction {
                key: key(ProvenanceRole::ConstructorDeclaration),
                template_key: None,
                owner: WireProductionOwner::TokenSort { sort: wire_sort() },
                result_sort: wire_sort(),
                items: vec![WireProductionItem::Terminal {
                    key: key(ProvenanceRole::ConstructorSyntax),
                    text: "+".to_owned(),
                }],
                attributes: vec![WireProductionAttribute::Function {
                    key: key(ProvenanceRole::FunctionDeclaration),
                }],
            },
        )));
        let actual = decode(&wire, type_slots());
        let expected = HostDescriptorPayload::Grammar(Box::new(HostGrammarDescriptor::Production(
            HostProduction {
                key: key(ProvenanceRole::ConstructorDeclaration),
                template_key: None,
                owner: HostProductionOwner::TokenSort { sort: host_sort() },
                result_sort: host_sort(),
                items: vec![HostProductionItem::Terminal {
                    key: key(ProvenanceRole::ConstructorSyntax),
                    text: "+".to_owned(),
                }],
                attributes: vec![HostProductionAttribute::Function {
                    key: key(ProvenanceRole::FunctionDeclaration),
                }],
            },
        )));
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    }

    #[test]
    fn grammar_ordering_and_subsort_wire_match_code_built_payloads() {
        let chain = DescriptorPrecedenceChain {
            key: key(ProvenanceRole::PrecedenceChain),
            groups: vec![DescriptorGroupReference {
                key: key(ProvenanceRole::AssociativityGroupReference),
                group: ProductionGroupId::new("arith").unwrap(),
            }],
        };
        let actual = decode(
            &WirePayload::Grammar(Box::new(WireGrammarDescriptor::Precedence {
                key: key(ProvenanceRole::PrecedenceDeclaration),
                chains: vec![chain.clone()],
            })),
            __KrsSlots::default(),
        );
        let expected =
            HostDescriptorPayload::Grammar(Box::new(HostGrammarDescriptor::Precedence {
                key: key(ProvenanceRole::PrecedenceDeclaration),
                chains: vec![chain],
            }));
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));

        let actual = decode(
            &WirePayload::Grammar(Box::new(WireGrammarDescriptor::Subsort {
                key: key(ProvenanceRole::SubsortDeclaration),
                subsort: wire_sort(),
                supersort: wire_sort(),
            })),
            type_slots(),
        );
        let expected = HostDescriptorPayload::Grammar(Box::new(HostGrammarDescriptor::Subsort {
            key: key(ProvenanceRole::SubsortDeclaration),
            subsort: host_sort(),
            supersort: host_sort(),
        }));
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    }

    #[test]
    fn grammar_strictness_item_slot_matches_code_built_payload() {
        let package =
            HostPackageKey::new("semantics", "0.1.0", std::env::current_dir().unwrap()).unwrap();
        let alias =
            HostItemId::new(package, ["semantics"], "eval", ItemKind::ContextAlias, "").unwrap();
        let wire = WirePayload::Grammar(Box::new(WireGrammarDescriptor::Production(
            WireProduction {
                key: key(ProvenanceRole::ConstructorDeclaration),
                template_key: None,
                owner: WireProductionOwner::TokenSort { sort: wire_sort() },
                result_sort: wire_sort(),
                items: vec![],
                attributes: vec![WireProductionAttribute::Strictness {
                    key: key(ProvenanceRole::StrictnessDeclaration),
                    kind: StrictnessKind::Strict,
                    using: Some(WireContextAliasReference {
                        key: key(ProvenanceRole::AliasProduction),
                        slot: ItemSlot(0),
                    }),
                    fields: vec![],
                    result_sort: Box::new(wire_sort()),
                }],
            },
        )));
        let actual = decode(
            &wire,
            __KrsSlots {
                types: &[HostTypeKey(type_id)],
                items: std::slice::from_ref(&alias),
                targets: &[],
            },
        );
        let expected = HostDescriptorPayload::Grammar(Box::new(HostGrammarDescriptor::Production(
            HostProduction {
                key: key(ProvenanceRole::ConstructorDeclaration),
                template_key: None,
                owner: HostProductionOwner::TokenSort { sort: host_sort() },
                result_sort: host_sort(),
                items: vec![],
                attributes: vec![HostProductionAttribute::Strictness {
                    key: key(ProvenanceRole::StrictnessDeclaration),
                    kind: StrictnessKind::Strict,
                    using: Some(HostContextAliasReference {
                        key: key(ProvenanceRole::AliasProduction),
                        alias,
                    }),
                    fields: vec![],
                    result_sort: Box::new(host_sort()),
                }],
            },
        )));
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    }

    #[test]
    fn structured_wire_matches_code_built_payload() {
        let wire = WirePayload::StructuredRule(Box::new(WireStructuredRule {
            sentence_kind: SentenceKind::Equation,
            label: None,
            requires: None,
            priority: None,
            simplification: None,
            pattern_key: key(ProvenanceRole::RulePattern),
            result_key: key(ProvenanceRole::RuleResult),
            subject_sort: wire_sort(),
            result_sort: wire_sort(),
            bindings: vec![],
            subject: wire_term(),
            result: wire_term(),
        }));
        let encoded = serde_json::to_string(&wire).unwrap();
        assert!(encoded.contains("\"slot\":0,\"authored_path\":\"u64\""));
        let decoded: WirePayload = krs_ir::json::from_slice(encoded.as_bytes()).unwrap();
        assert_eq!(serde_json::to_string(&decoded).unwrap(), encoded);
        let actual = __krs_host_payload(&encoded, type_slots());
        let expected =
            HostDescriptorPayload::StructuredRule(Box::new(HostStructuredRuleDescriptor {
                sentence_kind: SentenceKind::Equation,
                label: None,
                requires: None,
                priority: None,
                simplification: None,
                pattern_key: key(ProvenanceRole::RulePattern),
                result_key: key(ProvenanceRole::RuleResult),
                subject_sort: host_sort(),
                result_sort: host_sort(),
                bindings: vec![],
                subject: host_term(),
                result: host_term(),
            }));
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    }

    #[test]
    fn head_wire_matches_code_built_payload() {
        let wire = WirePayload::HeadRule(Box::new(WireHeadRule {
            sentence_kind: SentenceKind::Transition,
            label: None,
            priority: None,
            pattern_key: key(ProvenanceRole::RulePattern),
            result_key: key(ProvenanceRole::RuleResult),
            head_sort: Some(wire_sort()),
            configuration: None,
            computation_cell_name: None,
            bindings: vec![],
            subject: wire_term(),
            result: ProtocolHeadRuleResult::Erase,
            requires: None,
            extras: vec![],
        }));
        let encoded = serde_json::to_string(&wire).unwrap();
        let decoded: WirePayload = krs_ir::json::from_slice(encoded.as_bytes()).unwrap();
        assert_eq!(serde_json::to_string(&decoded).unwrap(), encoded);
        let actual = __krs_host_payload(&encoded, type_slots());
        let expected = HostDescriptorPayload::HeadRule(Box::new(HostHeadRule {
            sentence_kind: SentenceKind::Transition,
            label: None,
            priority: None,
            pattern_key: key(ProvenanceRole::RulePattern),
            result_key: key(ProvenanceRole::RuleResult),
            head_sort: Some(host_sort()),
            configuration: None,
            computation_cell_name: None,
            bindings: vec![],
            subject: host_term(),
            result: ProtocolHeadRuleResult::Erase,
            requires: None,
            extras: vec![],
        }));
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    }

    #[test]
    #[should_panic(expected = "KRS generated rule wire has an invalid type slot 0")]
    fn out_of_range_type_slot_panics() {
        let wire = WirePayload::Constructor(WireConstructorDescriptor {
            sort: wire_sort(),
            fields: vec![],
        });
        let _ = decode(&wire, __KrsSlots::default());
    }

    #[test]
    #[should_panic(expected = "KRS generated rule wire has an invalid target slot 2")]
    fn out_of_range_target_slot_panics() {
        let decoder = Decoder {
            slots: __KrsSlots::default(),
        };
        let _ = decoder.target(WireApplicationReference {
            key: key(ProvenanceRole::TermApplicationHead),
            target: TargetSlot(2),
            authored_path: "Op".to_owned(),
        });
    }

    #[test]
    #[should_panic(expected = "KRS generated wire has an invalid item slot 3")]
    fn out_of_range_item_slot_panics() {
        let mut decoder = Decoder {
            slots: __KrsSlots::default(),
        };
        let _ =
            krs_ir::RefMap::<krs_ir::WireStage, krs_ir::HostStage>::item(&mut decoder, ItemSlot(3));
    }

    #[test]
    #[should_panic(expected = "KRS generated rule wire is malformed")]
    fn malformed_wire_panics() {
        let _ = __krs_host_payload("{", __KrsSlots::default());
    }
}
