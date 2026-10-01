//! Grammar shape and exact-provenance contexts for the shared term validator.

use std::collections::BTreeSet;

use super::{
    CellTermField, DescriptorApplicationHeadClass, DescriptorApplicationReference,
    DescriptorLiteral, DescriptorSortReference, DescriptorTerm, DescriptorTermArgument,
    GrammarTransportError, TermKeyCounters, TermSide, increment, insert_exact, require_key,
    validate_list_application_shape, validate_map_application_shape,
    validate_set_application_shape,
};
use crate::transport::validation::TermValidation;
use crate::{BuiltinSort, DescriptorStage, ProductionFieldId, ProvenanceKey, StableItemId};

pub(super) struct GrammarTermValidation<'a, F> {
    pub(super) provenance: F,
    pub(super) bindings: &'a BTreeSet<String>,
    pub(super) seen_variables: &'a mut BTreeSet<String>,
    pub(super) allow_wildcards: bool,
}

impl<F: Fn(&ProvenanceKey) -> bool + Copy> TermValidation<DescriptorStage>
    for GrammarTermValidation<'_, F>
{
    type Error = GrammarTransportError;

    fn variable(
        &mut self,
        key: &ProvenanceKey,
        path_key: &ProvenanceKey,
        name: &str,
    ) -> Result<(), Self::Error> {
        require_key(key, self.provenance)?;
        require_key(path_key, self.provenance)?;
        if name.trim().is_empty() || !self.bindings.contains(name) {
            return Err(GrammarTransportError::InvalidBinding(name.to_owned()));
        }
        self.seen_variables.insert(name.to_owned());
        Ok(())
    }

    fn application(
        &mut self,
        head_class: DescriptorApplicationHeadClass,
        reference: &DescriptorApplicationReference,
        path_key: &ProvenanceKey,
        arguments: &[DescriptorTermArgument],
    ) -> Result<(), Self::Error> {
        require_key(&reference.key, self.provenance)?;
        require_key(path_key, self.provenance)?;
        reference.application.validate()?;
        if head_class == DescriptorApplicationHeadClass::BareReference && !arguments.is_empty() {
            return Err(GrammarTransportError::InvalidApplication(
                "a bare-reference constructor must have no arguments",
            ));
        }
        validate_map_application_shape(head_class, &reference.application, arguments)?;
        validate_list_application_shape(head_class, &reference.application, arguments)?;
        validate_set_application_shape(head_class, &reference.application, arguments)
    }

    fn literal(
        &mut self,
        key: &ProvenanceKey,
        literal: &DescriptorLiteral,
    ) -> Result<(), Self::Error> {
        require_key(key, self.provenance)?;
        literal.validate()
    }

    fn wildcard(&mut self, key: &ProvenanceKey) -> Result<(), Self::Error> {
        require_key(key, self.provenance)?;
        if !self.allow_wildcards {
            return Err(GrammarTransportError::InvalidTerm(
                "wildcards are allowed only in rule subjects",
            ));
        }
        Ok(())
    }

    fn builtin_token(
        &mut self,
        _: &ProvenanceKey,
        _: BuiltinSort,
        _: &str,
    ) -> Result<(), Self::Error> {
        unsupported_claim_term()
    }

    fn anonymous(
        &mut self,
        _: &ProvenanceKey,
        _: &DescriptorSortReference,
        _: &str,
    ) -> Result<(), Self::Error> {
        unsupported_claim_term()
    }

    fn or_bool(&mut self, _: &ProvenanceKey, _: &[DescriptorTerm]) -> Result<(), Self::Error> {
        unsupported_claim_term()
    }

    fn cell(
        &mut self,
        _: &ProvenanceKey,
        _: &StableItemId,
        _: &[CellTermField<DescriptorStage>],
    ) -> Result<(), Self::Error> {
        unsupported_cell_term()
    }

    fn argument(
        &mut self,
        argument: &DescriptorTermArgument,
        named: bool,
        fields: &mut BTreeSet<ProductionFieldId>,
    ) -> Result<(), Self::Error> {
        match argument {
            DescriptorTermArgument::Positional { .. } if !named => Ok(()),
            DescriptorTermArgument::Named { key, field, .. } if named => {
                require_key(key, self.provenance)?;
                if !fields.insert(field.clone()) {
                    return Err(GrammarTransportError::InvalidApplication(
                        "named field occurs more than once",
                    ));
                }
                Ok(())
            }
            DescriptorTermArgument::Positional { .. } | DescriptorTermArgument::Named { .. } => {
                Err(GrammarTransportError::InvalidApplication(
                    "positional and named arguments are mixed",
                ))
            }
        }
    }

    fn cell_field(
        &mut self,
        _: &CellTermField<DescriptorStage>,
        _: &mut BTreeSet<ProductionFieldId>,
    ) -> Result<(), Self::Error> {
        unsupported_cell_term()
    }
}

pub(super) struct TermProvenanceValidation<'a> {
    pub(super) keys: &'a mut BTreeSet<ProvenanceKey>,
    pub(super) side: TermSide,
    pub(super) counters: &'a mut TermKeyCounters,
}

impl TermValidation<DescriptorStage> for TermProvenanceValidation<'_> {
    type Error = GrammarTransportError;

    fn variable(
        &mut self,
        key: &ProvenanceKey,
        path_key: &ProvenanceKey,
        _: &str,
    ) -> Result<(), Self::Error> {
        insert_exact(
            self.keys,
            path_key,
            self.side.path_role(),
            self.counters.path,
        )?;
        self.counters.path = increment(self.counters.path)?;
        insert_exact(
            self.keys,
            key,
            self.side.reference_role(),
            self.counters.reference,
        )?;
        self.counters.reference = increment(self.counters.reference)?;
        Ok(())
    }

    fn application(
        &mut self,
        head_class: DescriptorApplicationHeadClass,
        reference: &DescriptorApplicationReference,
        path_key: &ProvenanceKey,
        _: &[DescriptorTermArgument],
    ) -> Result<(), Self::Error> {
        insert_exact(
            self.keys,
            path_key,
            self.side.path_role(),
            self.counters.path,
        )?;
        self.counters.path = increment(self.counters.path)?;
        match head_class {
            DescriptorApplicationHeadClass::Applied => {
                insert_exact(
                    self.keys,
                    &reference.key,
                    self.side.application_role(),
                    self.counters.application,
                )?;
                self.counters.application = increment(self.counters.application)?;
            }
            DescriptorApplicationHeadClass::BareReference => {
                insert_exact(
                    self.keys,
                    &reference.key,
                    self.side.reference_role(),
                    self.counters.reference,
                )?;
                self.counters.reference = increment(self.counters.reference)?;
            }
        }
        Ok(())
    }

    fn literal(&mut self, key: &ProvenanceKey, _: &DescriptorLiteral) -> Result<(), Self::Error> {
        insert_exact(
            self.keys,
            key,
            self.side.literal_role(),
            self.counters.literal,
        )?;
        self.counters.literal = increment(self.counters.literal)?;
        Ok(())
    }

    fn wildcard(&mut self, key: &ProvenanceKey) -> Result<(), Self::Error> {
        let Some(role) = self.side.wildcard_role() else {
            return Err(GrammarTransportError::InvalidTerm(
                "wildcards are allowed only in rule subjects",
            ));
        };
        insert_exact(self.keys, key, role, self.counters.wildcard)?;
        self.counters.wildcard = increment(self.counters.wildcard)?;
        Ok(())
    }

    fn builtin_token(
        &mut self,
        _: &ProvenanceKey,
        _: BuiltinSort,
        _: &str,
    ) -> Result<(), Self::Error> {
        unsupported_claim_term()
    }

    fn anonymous(
        &mut self,
        _: &ProvenanceKey,
        _: &DescriptorSortReference,
        _: &str,
    ) -> Result<(), Self::Error> {
        unsupported_claim_term()
    }

    fn or_bool(&mut self, _: &ProvenanceKey, _: &[DescriptorTerm]) -> Result<(), Self::Error> {
        unsupported_claim_term()
    }

    fn cell(
        &mut self,
        _: &ProvenanceKey,
        _: &StableItemId,
        _: &[CellTermField<DescriptorStage>],
    ) -> Result<(), Self::Error> {
        unsupported_cell_term()
    }

    fn argument(
        &mut self,
        argument: &DescriptorTermArgument,
        _: bool,
        _: &mut BTreeSet<ProductionFieldId>,
    ) -> Result<(), Self::Error> {
        if let DescriptorTermArgument::Named { key, .. } = argument {
            insert_exact(
                self.keys,
                key,
                self.side.record_field_role(),
                self.counters.record_field,
            )?;
            self.counters.record_field = increment(self.counters.record_field)?;
        }
        Ok(())
    }

    fn cell_field(
        &mut self,
        _: &CellTermField<DescriptorStage>,
        _: &mut BTreeSet<ProductionFieldId>,
    ) -> Result<(), Self::Error> {
        unsupported_cell_term()
    }
}

fn unsupported_claim_term() -> Result<(), GrammarTransportError> {
    Err(GrammarTransportError::InvalidTerm(
        "claim-only term used outside a whole-configuration claim",
    ))
}

fn unsupported_cell_term() -> Result<(), GrammarTransportError> {
    Err(GrammarTransportError::InvalidTerm(
        "complete cell terms require configuration rules",
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        DescriptorApplicationRef, DescriptorTermArgument, ItemKind, ProvenanceRole, testing,
    };

    fn key(role: ProvenanceRole, ordinal: u32) -> ProvenanceKey {
        ProvenanceKey::new(role, ordinal)
    }

    fn application(arguments: Vec<DescriptorTermArgument>) -> DescriptorTerm {
        DescriptorTerm::Application {
            head_class: DescriptorApplicationHeadClass::Applied,
            reference: DescriptorApplicationReference {
                key: key(ProvenanceRole::RuleLeftApplicationHead, 0),
                application: DescriptorApplicationRef::Declared(testing::item_in(
                    testing::package("test", "test"),
                    "terms",
                    "Target",
                    ItemKind::Constructor,
                )),
            },
            path_key: key(ProvenanceRole::RuleLeftPath, 0),
            arguments,
        }
    }

    fn literal(ordinal: u32) -> Box<DescriptorTerm> {
        Box::new(DescriptorTerm::Literal {
            key: key(ProvenanceRole::RuleLeftLiteral, ordinal),
            literal: DescriptorLiteral::Int("0".to_owned()),
        })
    }

    #[test]
    fn grammar_named_argument_checks_provenance_before_duplicates_and_children() {
        let missing = key(ProvenanceRole::RuleLeftRecordFieldName, 1);
        let field = ProductionFieldId::new("value").unwrap();
        let term = application(vec![
            DescriptorTermArgument::Named {
                key: key(ProvenanceRole::RuleLeftRecordFieldName, 0),
                field: field.clone(),
                value: literal(0),
            },
            DescriptorTermArgument::Named {
                key: missing.clone(),
                field,
                value: Box::new(DescriptorTerm::Variable {
                    key: key(ProvenanceRole::RuleLeftReference, 0),
                    path_key: key(ProvenanceRole::RuleLeftPath, 1),
                    name: "undeclared".to_owned(),
                }),
            },
        ]);
        assert_eq!(
            term.validate(
                |key| key != &missing,
                &BTreeSet::new(),
                &mut BTreeSet::new(),
                true
            ),
            Err(GrammarTransportError::MissingProvenance(missing)),
        );
        assert_eq!(
            term.validate(|_| true, &BTreeSet::new(), &mut BTreeSet::new(), true),
            Err(GrammarTransportError::InvalidApplication(
                "named field occurs more than once"
            )),
        );
    }

    #[test]
    fn provenance_collection_preserves_permissive_application_shapes() {
        let field = ProductionFieldId::new("value").unwrap();
        let mut term = application(vec![
            DescriptorTermArgument::Named {
                key: key(ProvenanceRole::RuleLeftRecordFieldName, 0),
                field: field.clone(),
                value: literal(0),
            },
            DescriptorTermArgument::Positional { value: literal(1) },
            DescriptorTermArgument::Named {
                key: key(ProvenanceRole::RuleLeftRecordFieldName, 1),
                field,
                value: literal(2),
            },
        ]);
        let DescriptorTerm::Application { reference, .. } = &mut term else {
            unreachable!();
        };
        reference.application = DescriptorApplicationRef::Declared(testing::item_in(
            testing::package("test", "test"),
            "terms",
            "Target",
            ItemKind::Sort,
        ));
        for (head_class, head_role) in [
            (
                DescriptorApplicationHeadClass::Applied,
                ProvenanceRole::RuleLeftApplicationHead,
            ),
            (
                DescriptorApplicationHeadClass::BareReference,
                ProvenanceRole::RuleLeftReference,
            ),
        ] {
            let DescriptorTerm::Application {
                head_class: class,
                reference,
                ..
            } = &mut term
            else {
                unreachable!();
            };
            *class = head_class;
            reference.key = key(head_role, 0);
            let mut keys = BTreeSet::new();
            term.collect_expected_term_keys(
                &mut keys,
                TermSide::Left,
                &mut TermKeyCounters::default(),
            )
            .unwrap();
            assert_eq!(
                keys,
                BTreeSet::from([
                    key(ProvenanceRole::RuleLeftPath, 0),
                    key(head_role, 0),
                    key(ProvenanceRole::RuleLeftRecordFieldName, 0),
                    key(ProvenanceRole::RuleLeftRecordFieldName, 1),
                    key(ProvenanceRole::RuleLeftLiteral, 0),
                    key(ProvenanceRole::RuleLeftLiteral, 1),
                    key(ProvenanceRole::RuleLeftLiteral, 2),
                ])
            );
        }
    }
}
