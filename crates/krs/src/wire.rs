//! Runtime substitution of indexed, static host payloads.

use krs_ir::wire::{
    WireApplicationReference, WireCellTermField, WireConfigurationReference,
    WireConstructorDescriptor, WireContextAliasReference, WireGrammarDescriptor, WireHeadRule,
    WireHeadRuleExtra, WireHeadRuleResult, WirePayload, WireProduction, WireProductionAttribute,
    WireProductionItem, WireProductionOwner, WireRuleCondition, WireSortReference,
    WireStructuredRule, WireTerm, WireTermArgument, WireTypeReference,
};
use krs_ir::{
    HostApplicationReference, HostApplicationTarget, HostCellTermField, HostConfigurationReference,
    HostConstructorDescriptor, HostConstructorFieldDescriptor, HostContextAliasReference,
    HostDescriptorPayload, HostEnumVariantReference, HostGrammarDescriptor, HostHeadRule,
    HostHeadRuleCellReference, HostHeadRuleExtra, HostHeadRuleResult, HostItemId, HostProduction,
    HostProductionAttribute, HostProductionItem, HostProductionOwner, HostRuleCondition,
    HostSortReference, HostStructuredRuleDescriptor, HostTerm, HostTermArgument, HostTypeKey,
    HostTypeReference, ProtocolHeadRuleBinding,
};

/// Rust-resolved value inserted into an indexed descriptor payload.
#[doc(hidden)]
#[derive(Clone, Debug)]
pub enum __KrsSlot {
    /// Build-local Rust type identity.
    Type(HostTypeKey),
    /// Exact owner and generated marker for a Rust enum variant.
    Variant {
        owner: HostTypeKey,
        marker: HostTypeKey,
    },
    /// Application identity, including an inferred readable-rule head.
    Target(HostApplicationTarget),
    /// Macro-context identity for a referenced context alias.
    Item(HostItemId),
}

/// Decode one static rule payload and insert the factory's Rust-resolved slots.
#[doc(hidden)]
#[inline(never)]
#[track_caller]
#[must_use]
pub fn __krs_host_payload(wire: &str, slots: &[__KrsSlot]) -> HostDescriptorPayload {
    let payload: WirePayload = krs_ir::json::from_slice(wire.as_bytes())
        .unwrap_or_else(|error| panic!("KRS generated rule wire is malformed: {error}"));
    let decoder = Decoder { slots };
    match payload {
        WirePayload::StructuredRule(rule) => {
            HostDescriptorPayload::StructuredRule(Box::new(decoder.structured(*rule)))
        }
        WirePayload::HeadRule(rule) => {
            HostDescriptorPayload::HeadRule(Box::new(decoder.head(*rule)))
        }
        WirePayload::Constructor(constructor) => {
            HostDescriptorPayload::Constructor(decoder.constructor(constructor))
        }
        WirePayload::Grammar(grammar) => {
            HostDescriptorPayload::Grammar(Box::new(decoder.grammar(*grammar)))
        }
    }
}

struct Decoder<'a> {
    slots: &'a [__KrsSlot],
}

impl Decoder<'_> {
    fn type_reference(&self, wire: WireTypeReference) -> HostTypeReference {
        let key = match self.slots.get(wire.slot) {
            Some(__KrsSlot::Type(key)) => *key,
            _ => panic!(
                "KRS generated rule wire has an invalid type slot {}",
                wire.slot
            ),
        };
        HostTypeReference {
            key,
            authored_path: wire.authored_path,
        }
    }

    fn target(&self, wire: WireApplicationReference) -> HostApplicationReference {
        let target = match self.slots.get(wire.target) {
            Some(__KrsSlot::Target(target)) => target.clone(),
            Some(__KrsSlot::Type(key)) => HostApplicationTarget::Nominal(HostTypeReference {
                key: *key,
                authored_path: wire.authored_path.clone(),
            }),
            Some(__KrsSlot::Variant { owner, marker }) => {
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
            _ => panic!(
                "KRS generated rule wire has an invalid target slot {}",
                wire.target
            ),
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

    fn sort(&self, wire: WireSortReference) -> HostSortReference {
        HostSortReference {
            key: wire.key,
            target: self.type_reference(wire.target),
        }
    }

    fn constructor(&self, wire: WireConstructorDescriptor) -> HostConstructorDescriptor {
        HostConstructorDescriptor {
            sort: self.sort(wire.sort),
            syntax: wire.syntax,
            fields: wire
                .fields
                .into_iter()
                .map(|field| HostConstructorFieldDescriptor {
                    name: field.name,
                    sort: self.type_reference(field.sort),
                })
                .collect(),
        }
    }

    fn grammar(&self, wire: WireGrammarDescriptor) -> HostGrammarDescriptor {
        match wire {
            WireGrammarDescriptor::Production(production) => {
                HostGrammarDescriptor::Production(self.production(production))
            }
            WireGrammarDescriptor::Subsort {
                key,
                subsort,
                supersort,
            } => HostGrammarDescriptor::Subsort {
                key,
                subsort: self.sort(subsort),
                supersort: self.sort(supersort),
            },
            WireGrammarDescriptor::Precedence { key, chains } => {
                HostGrammarDescriptor::Precedence { key, chains }
            }
            WireGrammarDescriptor::Associativity { key, sentences } => {
                HostGrammarDescriptor::Associativity { key, sentences }
            }
        }
    }

    fn production(&self, wire: WireProduction) -> HostProduction {
        HostProduction {
            key: wire.key,
            template_key: wire.template_key,
            owner: match wire.owner {
                WireProductionOwner::Constructor { constructor } => {
                    HostProductionOwner::Constructor {
                        constructor: self.target(constructor),
                    }
                }
                WireProductionOwner::TokenSort { sort } => HostProductionOwner::TokenSort {
                    sort: self.sort(sort),
                },
                WireProductionOwner::BracketSort { sort } => HostProductionOwner::BracketSort {
                    sort: self.sort(sort),
                },
            },
            result_sort: self.sort(wire.result_sort),
            items: wire
                .items
                .into_iter()
                .map(|item| self.production_item(item))
                .collect(),
            attributes: wire
                .attributes
                .into_iter()
                .map(|attribute| self.production_attribute(attribute))
                .collect(),
        }
    }

    fn production_item(&self, wire: WireProductionItem) -> HostProductionItem {
        match wire {
            WireProductionItem::Terminal { key, text } => {
                HostProductionItem::Terminal { key, text }
            }
            WireProductionItem::NonTerminal {
                key,
                field_key,
                declaration_key,
                field,
                sort,
            } => HostProductionItem::NonTerminal {
                key,
                field_key,
                declaration_key,
                field,
                sort: Box::new(self.sort(*sort)),
            },
            WireProductionItem::RegexTerminal {
                key,
                precede_regex,
                regex,
                follow_regex,
            } => HostProductionItem::RegexTerminal {
                key,
                precede_regex,
                regex,
                follow_regex,
            },
        }
    }

    fn production_attribute(&self, wire: WireProductionAttribute) -> HostProductionAttribute {
        match wire {
            WireProductionAttribute::Documentation { key, text } => {
                HostProductionAttribute::Documentation { key, text }
            }
            WireProductionAttribute::Function { key } => HostProductionAttribute::Function { key },
            WireProductionAttribute::Total { key } => HostProductionAttribute::Total { key },
            WireProductionAttribute::Hook { key, operation } => {
                HostProductionAttribute::Hook { key, operation }
            }
            WireProductionAttribute::Alias { key } => HostProductionAttribute::Alias { key },
            WireProductionAttribute::Token {
                key,
                lexical_precedence,
            } => HostProductionAttribute::Token {
                key,
                lexical_precedence,
            },
            WireProductionAttribute::Group { reference } => {
                HostProductionAttribute::Group { reference }
            }
            WireProductionAttribute::Bracket { key } => HostProductionAttribute::Bracket { key },
            WireProductionAttribute::Avoid { key } => HostProductionAttribute::Avoid { key },
            WireProductionAttribute::Format { key, fragments } => {
                HostProductionAttribute::Format { key, fragments }
            }
            WireProductionAttribute::Strictness {
                key,
                kind,
                using,
                fields,
                result_sort,
            } => HostProductionAttribute::Strictness {
                key,
                kind,
                using: using.map(|reference| self.context_alias(reference)),
                fields,
                result_sort: Box::new(self.sort(*result_sort)),
            },
        }
    }

    fn context_alias(&self, wire: WireContextAliasReference) -> HostContextAliasReference {
        let alias = match self.slots.get(wire.slot) {
            Some(__KrsSlot::Item(item)) => item.clone(),
            _ => panic!("KRS generated wire has an invalid item slot {}", wire.slot),
        };
        HostContextAliasReference {
            key: wire.key,
            alias,
        }
    }

    fn configuration(&self, wire: WireConfigurationReference) -> HostConfigurationReference {
        HostConfigurationReference {
            key: wire.key,
            configuration: self.type_reference(wire.configuration),
        }
    }

    fn condition(&self, wire: WireRuleCondition) -> HostRuleCondition {
        HostRuleCondition {
            key: wire.key,
            term: self.term(wire.term),
        }
    }

    fn term(&self, wire: WireTerm) -> HostTerm {
        match wire {
            WireTerm::Variable {
                key,
                path_key,
                name,
            } => HostTerm::Variable {
                key,
                path_key,
                name,
            },
            WireTerm::Application {
                head_class,
                reference,
                path_key,
                arguments,
            } => HostTerm::Application {
                head_class,
                reference: self.target(reference),
                path_key,
                arguments: arguments
                    .into_iter()
                    .map(|argument| match argument {
                        WireTermArgument::Positional { value } => HostTermArgument::Positional {
                            value: Box::new(self.term(*value)),
                        },
                        WireTermArgument::Named { key, field, value } => HostTermArgument::Named {
                            key,
                            field,
                            value: Box::new(self.term(*value)),
                        },
                    })
                    .collect(),
            },
            WireTerm::Literal { key, literal } => HostTerm::Literal { key, literal },
            WireTerm::Wildcard { key } => HostTerm::Wildcard { key },
            WireTerm::BuiltinToken { key, sort, value } => {
                HostTerm::BuiltinToken { key, sort, value }
            }
            WireTerm::Anonymous {
                key,
                sort,
                spelling,
            } => HostTerm::Anonymous {
                key,
                sort: self.sort(sort),
                spelling,
            },
            WireTerm::OrBool { key, arguments } => HostTerm::OrBool {
                key,
                arguments: arguments.into_iter().map(|term| self.term(term)).collect(),
            },
            WireTerm::Cell {
                key,
                declaration,
                fields,
            } => HostTerm::Cell {
                key,
                declaration: self.type_reference(declaration),
                fields: fields
                    .into_iter()
                    .map(
                        |WireCellTermField { key, field, value }| HostCellTermField {
                            key,
                            field,
                            value: Box::new(self.term(*value)),
                        },
                    )
                    .collect(),
            },
        }
    }

    fn structured(&self, rule: WireStructuredRule) -> HostStructuredRuleDescriptor {
        HostStructuredRuleDescriptor {
            sentence_kind: rule.sentence_kind,
            label: rule.label,
            requires: rule.requires.map(|condition| self.condition(condition)),
            priority: rule.priority,
            simplification: rule.simplification,
            pattern_key: rule.pattern_key,
            result_key: rule.result_key,
            subject_sort: self.sort(rule.subject_sort),
            result_sort: self.sort(rule.result_sort),
            bindings: rule.bindings,
            subject: self.term(rule.subject),
            result: self.term(rule.result),
        }
    }

    fn head(&self, rule: WireHeadRule) -> HostHeadRule {
        HostHeadRule {
            sentence_kind: rule.sentence_kind,
            label: rule.label,
            priority: rule.priority,
            pattern_key: rule.pattern_key,
            result_key: rule.result_key,
            head_sort: rule.head_sort.map(|sort| self.sort(sort)),
            configuration: rule.configuration.map(|config| self.configuration(config)),
            computation_cell_name: rule.computation_cell_name,
            bindings: rule
                .bindings
                .into_iter()
                .map(|binding| ProtocolHeadRuleBinding {
                    name: binding.name,
                    refinement: binding.refinement.map(|sort| self.sort(sort)),
                })
                .collect(),
            subject: self.term(rule.subject),
            result: self.head_result(rule.result),
            requires: rule.requires.map(|condition| self.condition(condition)),
            extras: rule
                .extras
                .into_iter()
                .map(|extra| self.head_extra(extra))
                .collect(),
        }
    }

    fn head_result(&self, result: WireHeadRuleResult) -> HostHeadRuleResult {
        match result {
            WireHeadRuleResult::Replace(term) => HostHeadRuleResult::Replace(self.term(term)),
            WireHeadRuleResult::Splice(terms) => {
                HostHeadRuleResult::Splice(terms.into_iter().map(|term| self.term(term)).collect())
            }
            WireHeadRuleResult::Erase => HostHeadRuleResult::Erase,
        }
    }

    fn head_extra(&self, extra: WireHeadRuleExtra) -> HostHeadRuleExtra {
        match extra {
            WireHeadRuleExtra::HaveMap {
                cell,
                key,
                value_binding,
            } => HostHeadRuleExtra::HaveMap {
                cell: HostHeadRuleCellReference {
                    key: cell.key,
                    name: cell.name,
                },
                key: self.term(key),
                value_binding,
            },
            WireHeadRuleExtra::UpdateMap {
                cell,
                base_binding,
                update,
            } => HostHeadRuleExtra::UpdateMap {
                cell: HostHeadRuleCellReference {
                    key: cell.key,
                    name: cell.name,
                },
                base_binding,
                update: self.term(update),
            },
            WireHeadRuleExtra::RewriteCell {
                cell,
                result_key,
                before,
                after,
            } => HostHeadRuleExtra::RewriteCell {
                cell: HostHeadRuleCellReference {
                    key: cell.key,
                    name: cell.name,
                },
                result_key,
                before: self.term(before),
                after: self.term(after),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{__KrsSlot, __krs_host_payload, Decoder};
    use krs_ir::wire::{
        WireApplicationReference, WireConstructorDescriptor, WireConstructorFieldDescriptor,
        WireContextAliasReference, WireGrammarDescriptor, WireHeadRule, WirePayload,
        WireProduction, WireProductionAttribute, WireProductionItem, WireProductionOwner,
        WireSortReference, WireStructuredRule, WireTerm, WireTypeReference,
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
            slots: &[
                __KrsSlot::Type(HostTypeKey(type_id)),
                __KrsSlot::Variant {
                    owner: HostTypeKey(type_id),
                    marker: HostTypeKey(marker_id),
                },
            ],
        };
        let nominal = decoder.target(WireApplicationReference {
            key: key(ProvenanceRole::TermApplicationHead),
            target: 0,
            authored_path: "int :: add".to_owned(),
        });
        assert_eq!(nominal.target.authored_path(), "int :: add");
        let variant = decoder.target(WireApplicationReference {
            key: key(ProvenanceRole::TermApplicationHead),
            target: 1,
            authored_path: "Op :: Gt".to_owned(),
        });
        assert_eq!(variant.target.authored_path(), "Op :: Gt");
    }

    fn wire_sort() -> WireSortReference {
        WireSortReference {
            key: key(ProvenanceRole::SortDeclaration),
            target: WireTypeReference {
                slot: 0,
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

    fn decode(wire: &WirePayload, slots: &[__KrsSlot]) -> HostDescriptorPayload {
        let encoded = serde_json::to_string(&wire).unwrap();
        let parsed: WirePayload = krs_ir::json::from_slice(encoded.as_bytes()).unwrap();
        assert_eq!(serde_json::to_string(&parsed).unwrap(), encoded);
        __krs_host_payload(&encoded, slots)
    }

    #[test]
    fn constructor_wire_matches_code_built_payload() {
        let wire = WirePayload::Constructor(WireConstructorDescriptor {
            sort: wire_sort(),
            syntax: Some("{value}".to_owned()),
            fields: vec![WireConstructorFieldDescriptor {
                name: "value".to_owned(),
                sort: WireTypeReference {
                    slot: 0,
                    authored_path: "u64".to_owned(),
                },
            }],
        });
        let actual = decode(&wire, &[__KrsSlot::Type(HostTypeKey(type_id))]);
        let expected = HostDescriptorPayload::Constructor(HostConstructorDescriptor {
            sort: host_sort(),
            syntax: Some("{value}".to_owned()),
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
            &[],
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
        let actual = decode(&wire, &[__KrsSlot::Type(HostTypeKey(type_id))]);
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
            &[],
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
            &[__KrsSlot::Type(HostTypeKey(type_id))],
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
                        slot: 1,
                    }),
                    fields: vec![],
                    result_sort: Box::new(wire_sort()),
                }],
            },
        )));
        let actual = decode(
            &wire,
            &[
                __KrsSlot::Type(HostTypeKey(type_id)),
                __KrsSlot::Item(alias.clone()),
            ],
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
        let actual = __krs_host_payload(&encoded, &[__KrsSlot::Type(HostTypeKey(type_id))]);
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
        let actual = __krs_host_payload(&encoded, &[__KrsSlot::Type(HostTypeKey(type_id))]);
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
    #[should_panic(expected = "KRS generated rule wire is malformed")]
    fn malformed_wire_panics() {
        let _ = __krs_host_payload("{", &[]);
    }
}
