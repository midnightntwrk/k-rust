//! Runtime substitution of indexed, static rule payloads.

use krs_ir::wire::{
    WireApplicationReference, WireCellTermField, WireConfigurationReference, WireHeadRule,
    WireHeadRuleExtra, WireHeadRuleResult, WirePayload, WireRuleCondition, WireSortReference,
    WireStructuredRule, WireTerm, WireTermArgument, WireTypeReference,
};
use krs_ir::{
    HostApplicationReference, HostApplicationTarget, HostCellTermField, HostConfigurationReference,
    HostDescriptorPayload, HostEnumVariantReference, HostHeadRule, HostHeadRuleCellReference,
    HostHeadRuleExtra, HostHeadRuleResult, HostRuleCondition, HostSortReference,
    HostStructuredRuleDescriptor, HostTerm, HostTermArgument, HostTypeKey, HostTypeReference,
    ProtocolHeadRuleBinding,
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
        WireApplicationReference, WireHeadRule, WirePayload, WireSortReference, WireStructuredRule,
        WireTerm, WireTypeReference,
    };
    use krs_ir::{
        DescriptorLiteral, HostDescriptorPayload, HostHeadRule, HostSortReference,
        HostStructuredRuleDescriptor, HostTerm, HostTypeKey, HostTypeReference,
        ProtocolHeadRuleResult, ProvenanceKey, SentenceKind,
    };
    use std::any::TypeId;

    fn key(role: &str) -> ProvenanceKey {
        ProvenanceKey::new(role, 0).unwrap()
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
            key: key("application"),
            target: 0,
            authored_path: "int :: add".to_owned(),
        });
        assert_eq!(nominal.target.authored_path(), "int :: add");
        let variant = decoder.target(WireApplicationReference {
            key: key("application"),
            target: 1,
            authored_path: "Op :: Gt".to_owned(),
        });
        assert_eq!(variant.target.authored_path(), "Op :: Gt");
    }

    fn wire_sort() -> WireSortReference {
        WireSortReference {
            key: key("sort"),
            target: WireTypeReference {
                slot: 0,
                authored_path: "u64".to_owned(),
            },
        }
    }

    fn host_sort() -> HostSortReference {
        HostSortReference {
            key: key("sort"),
            target: HostTypeReference {
                key: HostTypeKey(type_id),
                authored_path: "u64".to_owned(),
            },
        }
    }

    fn wire_term() -> WireTerm {
        WireTerm::Literal {
            key: key("literal"),
            literal: DescriptorLiteral::Int("42".to_owned()),
        }
    }

    fn host_term() -> HostTerm {
        HostTerm::Literal {
            key: key("literal"),
            literal: DescriptorLiteral::Int("42".to_owned()),
        }
    }

    #[test]
    fn structured_wire_matches_code_built_payload() {
        let wire = WirePayload::StructuredRule(Box::new(WireStructuredRule {
            sentence_kind: SentenceKind::Equation,
            label: None,
            requires: None,
            priority: None,
            simplification: None,
            pattern_key: key("rule_pattern"),
            result_key: key("rule_result"),
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
                pattern_key: key("rule_pattern"),
                result_key: key("rule_result"),
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
            pattern_key: key("rule_pattern"),
            result_key: key("rule_result"),
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
            pattern_key: key("rule_pattern"),
            result_key: key("rule_result"),
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
