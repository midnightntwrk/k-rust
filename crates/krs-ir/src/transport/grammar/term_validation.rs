//! Grammar shape and exact-provenance contexts for the shared term validator.

use std::collections::BTreeSet;

use super::{
    CellTermField, DescriptorApplicationHeadClass, DescriptorApplicationReference,
    DescriptorLiteral, DescriptorSortReference, DescriptorTerm, GrammarTransportError,
    TermKeyCounters, TermSide, increment, insert_exact, require_key,
    validate_collection_application_shape,
};
use crate::transport::detail::{GrammarApplicationReason, GrammarTermReason};
use crate::transport::validation::TermValidation;
use crate::{
    BuiltinSort, DescriptorStage, ProductionFieldId, ProvenanceKey, ProvenanceRole, SortTestKind,
    StableItemId,
};

pub(super) struct GrammarTermValidation<'a, F> {
    pub(super) provenance: F,
    pub(super) bindings: &'a BTreeSet<String>,
    pub(super) seen_variables: &'a mut BTreeSet<String>,
    pub(super) allow_wildcards: bool,
    /// Whether the validator is inside a `k::matches!` pattern, whose names
    /// are local binders rather than rule bindings.
    pub(super) in_matches_pattern: bool,
    /// Whether the validator is inside a `let` pattern, whose names are
    /// local binders.
    pub(super) in_let_pattern: bool,
    /// The names bound by the enclosing `let` statements, innermost last.
    pub(super) let_scopes: Vec<BTreeSet<String>>,
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
        if name.trim().is_empty() {
            return Err(GrammarTransportError::InvalidBinding(name.to_owned()));
        }
        // A name in a `k::matches!` pattern is a local binder (BIND-1);
        // semantic lowering scopes it and rejects one that shadows a rule
        // binding.
        if self.in_matches_pattern
            || self.in_let_pattern
            || self.let_scopes.iter().any(|scope| scope.contains(name))
        {
            return Ok(());
        }
        if !self.bindings.contains(name) {
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
        arguments: &crate::Arguments<crate::DescriptorStage>,
    ) -> Result<(), Self::Error> {
        require_key(&reference.key, self.provenance)?;
        require_key(path_key, self.provenance)?;
        reference.application.validate()?;
        if head_class == DescriptorApplicationHeadClass::BareReference && !arguments.is_empty() {
            return Err(GrammarTransportError::InvalidApplication(
                GrammarApplicationReason::BareConstructorArguments,
            ));
        }
        validate_collection_application_shape(head_class, &reference.application, arguments)
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
        if !self.allow_wildcards && !self.in_matches_pattern && !self.in_let_pattern {
            return Err(GrammarTransportError::InvalidTerm(
                GrammarTermReason::WildcardsAreAllowedOnlyInRuleSubjects,
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

    fn or_bool(
        &mut self,
        _: &ProvenanceKey,
        _: &crate::AtLeastTwo<DescriptorTerm>,
    ) -> Result<(), Self::Error> {
        unsupported_claim_term()
    }

    fn lexeme(
        &mut self,
        key: &ProvenanceKey,
        sort: &DescriptorSortReference,
        text: &str,
    ) -> Result<(), Self::Error> {
        require_key(key, self.provenance)?;
        require_key(&sort.key, self.provenance)?;
        sort.sort.validate()?;
        if text.is_empty() {
            return Err(GrammarTransportError::InvalidTerm(
                GrammarTermReason::EmptyLexemeText,
            ));
        }
        Ok(())
    }

    fn cell(
        &mut self,
        _: &ProvenanceKey,
        _: &StableItemId,
        _: &[CellTermField<DescriptorStage>],
    ) -> Result<(), Self::Error> {
        unsupported_cell_term()
    }

    fn sort_test(
        &mut self,
        key: &ProvenanceKey,
        _: SortTestKind,
        sort: &DescriptorSortReference,
    ) -> Result<(), Self::Error> {
        require_key(key, self.provenance)?;
        require_key(&sort.key, self.provenance)?;
        sort.sort.validate()
    }

    fn pattern_as(
        &mut self,
        key: &ProvenanceKey,
        binding_key: &ProvenanceKey,
        name: &str,
    ) -> Result<(), Self::Error> {
        require_key(key, self.provenance)?;
        require_key(binding_key, self.provenance)?;
        if self.in_let_pattern {
            return Err(GrammarTransportError::InvalidTerm(
                GrammarTermReason::PatternAsOutsideLeftHandSide,
            ));
        }
        if self.in_matches_pattern {
            return if name.trim().is_empty() {
                Err(GrammarTransportError::InvalidBinding(name.to_owned()))
            } else {
                Ok(())
            };
        }
        if !self.allow_wildcards {
            return Err(GrammarTransportError::InvalidTerm(
                GrammarTermReason::PatternAsOutsideLeftHandSide,
            ));
        }
        if name.trim().is_empty() || !self.bindings.contains(name) {
            return Err(GrammarTransportError::InvalidBinding(name.to_owned()));
        }
        self.seen_variables.insert(name.to_owned());
        Ok(())
    }

    fn pattern_or(&mut self, key: &ProvenanceKey) -> Result<(), Self::Error> {
        require_key(key, self.provenance)?;
        if self.in_let_pattern || (!self.allow_wildcards && !self.in_matches_pattern) {
            return Err(GrammarTransportError::InvalidTerm(
                GrammarTermReason::PatternOrOutsideLeftHandSide,
            ));
        }
        Ok(())
    }

    fn matches(&mut self, key: &ProvenanceKey) -> Result<(), Self::Error> {
        require_key(key, self.provenance)?;
        if self.allow_wildcards || self.in_matches_pattern || self.in_let_pattern {
            return Err(GrammarTransportError::InvalidTerm(
                GrammarTermReason::MatchesInPattern,
            ));
        }
        Ok(())
    }

    fn matches_pattern(&mut self, inside: bool) {
        self.in_matches_pattern = inside;
    }

    fn let_binding(
        &mut self,
        key: &ProvenanceKey,
        sort: Option<&DescriptorSortReference>,
    ) -> Result<(), Self::Error> {
        require_key(key, self.provenance)?;
        if self.allow_wildcards || self.in_matches_pattern || self.in_let_pattern {
            return Err(GrammarTransportError::InvalidTerm(
                GrammarTermReason::LetInPattern,
            ));
        }
        if let Some(sort) = sort {
            require_key(&sort.key, self.provenance)?;
            sort.sort.validate()?;
        }
        Ok(())
    }

    fn let_pattern(&mut self, inside: bool) {
        self.in_let_pattern = inside;
    }

    fn let_body(&mut self, names: Option<&BTreeSet<String>>) {
        match names {
            Some(names) => self.let_scopes.push(names.clone()),
            None => {
                self.let_scopes.pop();
            }
        }
    }

    fn argument(
        &mut self,
        argument: crate::TermArgumentRef<'_, crate::DescriptorStage>,
        fields: &mut BTreeSet<ProductionFieldId>,
    ) -> Result<(), Self::Error> {
        match argument {
            crate::TermArgumentRef::Positional { .. } => Ok(()),
            crate::TermArgumentRef::Named { key, field, .. } => {
                require_key(key, self.provenance)?;
                if !fields.insert(field.clone()) {
                    return Err(GrammarTransportError::InvalidApplication(
                        GrammarApplicationReason::DuplicateNamedField,
                    ));
                }
                Ok(())
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
        _: &crate::Arguments<crate::DescriptorStage>,
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
        if self.counters.in_let_pattern {
            insert_exact(
                self.keys,
                key,
                ProvenanceRole::LetWildcard,
                self.counters.let_wildcard,
            )?;
            self.counters.let_wildcard = increment(self.counters.let_wildcard)?;
            return Ok(());
        }
        if self.counters.in_matches_pattern {
            insert_exact(
                self.keys,
                key,
                ProvenanceRole::MatchesWildcard,
                self.counters.matches_wildcard,
            )?;
            self.counters.matches_wildcard = increment(self.counters.matches_wildcard)?;
            return Ok(());
        }
        let Some(role) = self.side.wildcard_role() else {
            return Err(GrammarTransportError::InvalidTerm(
                GrammarTermReason::WildcardsAreAllowedOnlyInRuleSubjects,
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

    fn or_bool(
        &mut self,
        _: &ProvenanceKey,
        _: &crate::AtLeastTwo<DescriptorTerm>,
    ) -> Result<(), Self::Error> {
        unsupported_claim_term()
    }

    fn lexeme(
        &mut self,
        key: &ProvenanceKey,
        sort: &DescriptorSortReference,
        _: &str,
    ) -> Result<(), Self::Error> {
        insert_exact(
            self.keys,
            &sort.key,
            ProvenanceRole::LexemeSort,
            self.counters.lexeme,
        )?;
        insert_exact(
            self.keys,
            key,
            ProvenanceRole::LexemeText,
            self.counters.lexeme,
        )?;
        self.counters.lexeme = increment(self.counters.lexeme)?;
        Ok(())
    }

    fn cell(
        &mut self,
        _: &ProvenanceKey,
        _: &StableItemId,
        _: &[CellTermField<DescriptorStage>],
    ) -> Result<(), Self::Error> {
        unsupported_cell_term()
    }

    fn sort_test(
        &mut self,
        key: &ProvenanceKey,
        _: SortTestKind,
        sort: &DescriptorSortReference,
    ) -> Result<(), Self::Error> {
        insert_exact(
            self.keys,
            &sort.key,
            ProvenanceRole::SortTestSort,
            self.counters.sort_test,
        )?;
        insert_exact(
            self.keys,
            key,
            ProvenanceRole::SortTest,
            self.counters.sort_test,
        )?;
        self.counters.sort_test = increment(self.counters.sort_test)?;
        Ok(())
    }

    fn pattern_as(
        &mut self,
        key: &ProvenanceKey,
        binding_key: &ProvenanceKey,
        _: &str,
    ) -> Result<(), Self::Error> {
        if self.counters.in_let_pattern
            || (!matches!(self.side, TermSide::Left) && !self.counters.in_matches_pattern)
        {
            return Err(GrammarTransportError::InvalidTerm(
                GrammarTermReason::PatternAsOutsideLeftHandSide,
            ));
        }
        insert_exact(
            self.keys,
            key,
            ProvenanceRole::PatternAs,
            self.counters.pattern_as,
        )?;
        insert_exact(
            self.keys,
            binding_key,
            ProvenanceRole::PatternAsBinding,
            self.counters.pattern_as,
        )?;
        self.counters.pattern_as = increment(self.counters.pattern_as)?;
        Ok(())
    }

    fn pattern_or(&mut self, key: &ProvenanceKey) -> Result<(), Self::Error> {
        if self.counters.in_let_pattern
            || (!matches!(self.side, TermSide::Left) && !self.counters.in_matches_pattern)
        {
            return Err(GrammarTransportError::InvalidTerm(
                GrammarTermReason::PatternOrOutsideLeftHandSide,
            ));
        }
        insert_exact(
            self.keys,
            key,
            ProvenanceRole::PatternOr,
            self.counters.pattern_or,
        )?;
        self.counters.pattern_or = increment(self.counters.pattern_or)?;
        Ok(())
    }

    fn matches(&mut self, key: &ProvenanceKey) -> Result<(), Self::Error> {
        if matches!(self.side, TermSide::Left)
            || self.counters.in_matches_pattern
            || self.counters.in_let_pattern
        {
            return Err(GrammarTransportError::InvalidTerm(
                GrammarTermReason::MatchesInPattern,
            ));
        }
        insert_exact(
            self.keys,
            key,
            ProvenanceRole::Matches,
            self.counters.matches,
        )?;
        self.counters.matches = increment(self.counters.matches)?;
        Ok(())
    }

    fn matches_pattern(&mut self, inside: bool) {
        self.counters.in_matches_pattern = inside;
    }

    fn let_binding(
        &mut self,
        key: &ProvenanceKey,
        sort: Option<&DescriptorSortReference>,
    ) -> Result<(), Self::Error> {
        if matches!(self.side, TermSide::Left)
            || self.counters.in_matches_pattern
            || self.counters.in_let_pattern
        {
            return Err(GrammarTransportError::InvalidTerm(
                GrammarTermReason::LetInPattern,
            ));
        }
        if let Some(sort) = sort {
            insert_exact(
                self.keys,
                &sort.key,
                ProvenanceRole::LetSort,
                self.counters.let_binding,
            )?;
        }
        insert_exact(
            self.keys,
            key,
            ProvenanceRole::Let,
            self.counters.let_binding,
        )?;
        self.counters.let_binding = increment(self.counters.let_binding)?;
        Ok(())
    }

    fn let_pattern(&mut self, inside: bool) {
        self.counters.in_let_pattern = inside;
    }

    fn let_body(&mut self, _: Option<&BTreeSet<String>>) {}

    fn argument(
        &mut self,
        argument: crate::TermArgumentRef<'_, crate::DescriptorStage>,
        _: &mut BTreeSet<ProductionFieldId>,
    ) -> Result<(), Self::Error> {
        if let crate::TermArgumentRef::Named { key, .. } = argument {
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
        GrammarTermReason::UnexpectedClaimTerm,
    ))
}

fn unsupported_cell_term() -> Result<(), GrammarTransportError> {
    Err(GrammarTransportError::InvalidTerm(
        GrammarTermReason::CompleteCellTermsRequireConfigurationRules,
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
            arguments: arguments.try_into().unwrap(),
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
                GrammarApplicationReason::DuplicateNamedField
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
            DescriptorTermArgument::Named {
                key: key(ProvenanceRole::RuleLeftRecordFieldName, 1),
                field: ProductionFieldId::new("other").unwrap(),
                value: literal(1),
            },
            DescriptorTermArgument::Named {
                key: key(ProvenanceRole::RuleLeftRecordFieldName, 2),
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
                    key(ProvenanceRole::RuleLeftRecordFieldName, 2),
                    key(ProvenanceRole::RuleLeftLiteral, 0),
                    key(ProvenanceRole::RuleLeftLiteral, 1),
                    key(ProvenanceRole::RuleLeftLiteral, 2),
                ])
            );
        }
    }
}
