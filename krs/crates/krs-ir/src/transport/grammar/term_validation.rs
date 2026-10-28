//! Grammar shape and exact-provenance contexts for the shared term validator.

use std::collections::BTreeSet;

use super::{
    CellTermField, DescriptorApplicationHeadClass, DescriptorApplicationReference,
    DescriptorLiteral, DescriptorSortReference, DescriptorTerm, GrammarTransportError, require_key,
    validate_collection_application_shape,
};
use crate::transport::detail::{GrammarApplicationReason, GrammarTermReason};
use crate::transport::validation::TermValidation;
use crate::{
    BuiltinSort, DescriptorStage, ItemKind, ProductionFieldId, ProvenanceKey, ProvenanceRole,
    SortTestKind, StableItemId,
};

#[expect(
    clippy::struct_excessive_bools,
    reason = "Each flag records one independent context of the term walk."
)]
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
    /// Whether `k::rewrite!` is admitted: a single-body subject (KF-011).
    pub(super) allow_rewrite: bool,
    /// Whether the validator is inside the right side of a `k::rewrite!`,
    /// whose names use bindings without binding them.
    pub(super) in_rewrite_right: bool,
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
        if !self.in_rewrite_right {
            self.seen_variables.insert(name.to_owned());
        }
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
        reference.application.validate_term_head()?;
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
        if (!self.allow_wildcards || self.in_rewrite_right)
            && !self.in_matches_pattern
            && !self.in_let_pattern
        {
            return Err(GrammarTransportError::InvalidTerm(
                GrammarTermReason::WildcardsAreAllowedOnlyInRuleSubjects,
            ));
        }
        Ok(())
    }

    fn builtin_token(
        &mut self,
        key: &ProvenanceKey,
        sort: BuiltinSort,
        value: &str,
    ) -> Result<(), Self::Error> {
        require_key(key, self.provenance)?;
        builtin_token_role(sort, value).map(|_| ())
    }

    fn anonymous(
        &mut self,
        _: &ProvenanceKey,
        _: &DescriptorSortReference,
        _: &ProvenanceKey,
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

    /// A fragment is a cell term of its group's cell sort, which stands
    /// wherever a term does: it names a cell declaration and, unless it is
    /// open or an update, at least one child.
    fn cell(
        &mut self,
        key: &ProvenanceKey,
        path_key: &ProvenanceKey,
        declaration: &StableItemId,
        fields: &[CellTermField<DescriptorStage>],
        partial: bool,
    ) -> Result<(), Self::Error> {
        require_key(key, self.provenance)?;
        require_key(path_key, self.provenance)?;
        if declaration.item_kind() != ItemKind::Cell || (fields.is_empty() && !partial) {
            return Err(GrammarTransportError::InvalidTerm(
                GrammarTermReason::EmptyOrNonNominalFragment,
            ));
        }
        Ok(())
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

    fn application_instance(&mut self, sort: &DescriptorSortReference) -> Result<(), Self::Error> {
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

    fn closure(
        &mut self,
        key: &ProvenanceKey,
        binder_key: &ProvenanceKey,
        sort: &DescriptorSortReference,
    ) -> Result<(), Self::Error> {
        require_key(key, self.provenance)?;
        require_key(binder_key, self.provenance)?;
        require_key(&sort.key, self.provenance)?;
        if self.allow_wildcards || self.in_matches_pattern || self.in_let_pattern {
            return Err(GrammarTransportError::InvalidTerm(
                GrammarTermReason::ClosureInPattern,
            ));
        }
        sort.sort.validate()
    }

    fn let_body(&mut self, names: Option<&BTreeSet<String>>) {
        match names {
            Some(names) => self.let_scopes.push(names.clone()),
            None => {
                self.let_scopes.pop();
            }
        }
    }

    fn rewrite(
        &mut self,
        key: &ProvenanceKey,
        from_key: &ProvenanceKey,
        to_key: &ProvenanceKey,
        nested: bool,
    ) -> Result<(), Self::Error> {
        require_key(key, self.provenance)?;
        require_key(from_key, self.provenance)?;
        require_key(to_key, self.provenance)?;
        if !self.allow_rewrite || self.in_matches_pattern || self.in_let_pattern {
            return Err(GrammarTransportError::InvalidTerm(
                GrammarTermReason::RewriteOutsideSingleBodyRule,
            ));
        }
        if nested || self.in_rewrite_right {
            return Err(GrammarTransportError::InvalidTerm(
                GrammarTermReason::NestedRewrite,
            ));
        }
        Ok(())
    }

    fn rewrite_right(&mut self, inside: bool) {
        self.in_rewrite_right = inside;
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
        field: &CellTermField<DescriptorStage>,
        names: &mut BTreeSet<ProductionFieldId>,
    ) -> Result<(), Self::Error> {
        require_key(&field.key, self.provenance)?;
        if !names.insert(field.field.clone()) {
            return Err(GrammarTransportError::InvalidApplication(
                GrammarApplicationReason::DuplicateNamedField,
            ));
        }
        Ok(())
    }

    fn record_update(&mut self, base: &DescriptorTerm) -> Result<(), Self::Error> {
        let DescriptorTerm::Variable {
            key,
            path_key,
            name,
        } = base
        else {
            return Err(GrammarTransportError::InvalidTerm(
                GrammarTermReason::RecordUpdateBase,
            ));
        };
        self.variable(key, path_key, name)
    }
}

/// The provenance role of a builtin `Id` or `Bytes` literal: one constant
/// of its builtin sort, which a rule may match or build as a claim may.
/// The token must be a valid literal of the sort.
fn builtin_token_role(
    sort: BuiltinSort,
    value: &str,
) -> Result<ProvenanceRole, GrammarTransportError> {
    crate::transport::validation::builtin_token_literal_role(sort, value).ok_or(
        GrammarTransportError::InvalidTerm(GrammarTermReason::InvalidCompilerOwnedBuiltinToken),
    )
}

fn unsupported_claim_term() -> Result<(), GrammarTransportError> {
    Err(GrammarTransportError::InvalidTerm(
        GrammarTermReason::UnexpectedClaimTerm,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transport::keys::WireKeys;
    use crate::transport::rule::ValidationSide;
    use crate::{
        DescriptorApplicationRef, DescriptorTermArgument, ItemKind, ProvenanceRole, testing,
    };

    fn key(role: ProvenanceRole, ordinal: u32) -> ProvenanceKey {
        ProvenanceKey::new(role, ordinal)
    }

    fn application(arguments: Vec<DescriptorTermArgument>) -> DescriptorTerm {
        DescriptorTerm::Application {
            instance: Vec::new(),
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
            update: None,
            open: false,
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
            let mut keys = WireKeys::default();
            term.collect_wire_term_keys(&mut keys, ValidationSide::Left)
                .unwrap();
            assert_eq!(
                keys.defined(),
                &BTreeSet::from([
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

    /// A fragment is a term of its group's cell sort in a structured rule
    /// as in a configuration rule: it names a cell declaration and its
    /// children once each, and it binds the names its children hold.
    #[test]
    fn grammar_rules_hold_fragments() {
        let frame =
            |kind| testing::item_in(testing::package("test", "test"), "cells", "Frame", kind);
        let child = |ordinal, name: &str| CellTermField {
            key: key(ProvenanceRole::RuleLeftRecordFieldName, ordinal),
            field: ProductionFieldId::new(name).unwrap(),
            value: Box::new(DescriptorTerm::Variable {
                key: key(ProvenanceRole::RuleLeftReference, ordinal),
                path_key: key(ProvenanceRole::RuleLeftPath, ordinal + 1),
                name: format!("x{ordinal}"),
            }),
        };
        let fragment = |declaration, fields, open| DescriptorTerm::Cell {
            key: key(ProvenanceRole::RuleLeftApplicationHead, 0),
            path_key: key(ProvenanceRole::RuleLeftPath, 0),
            declaration,
            fields,
            open,
            update: None,
        };
        let bindings = BTreeSet::from(["x0".to_owned(), "x1".to_owned()]);
        let validate = |term: &DescriptorTerm, seen: &mut BTreeSet<String>| {
            term.validate(|_| true, &bindings, seen, true)
        };
        let mut seen = BTreeSet::new();
        let term = fragment(
            frame(ItemKind::Cell),
            vec![child(0, "ret"), child(1, "pc")],
            false,
        );
        assert_eq!(validate(&term, &mut seen), Ok(()));
        assert_eq!(seen, bindings);
        let mut keys = WireKeys::default();
        term.collect_wire_term_keys(&mut keys, ValidationSide::Left)
            .unwrap();
        assert!(
            keys.defined()
                .contains(&key(ProvenanceRole::RuleLeftApplicationHead, 0))
        );
        assert_eq!(
            validate(
                &fragment(frame(ItemKind::Cell), Vec::new(), true),
                &mut seen
            ),
            Ok(())
        );
        for invalid in [
            fragment(frame(ItemKind::Cell), Vec::new(), false),
            fragment(frame(ItemKind::Constructor), vec![child(0, "ret")], false),
        ] {
            assert_eq!(
                validate(&invalid, &mut seen),
                Err(GrammarTransportError::InvalidTerm(
                    GrammarTermReason::EmptyOrNonNominalFragment
                )),
            );
        }
        assert_eq!(
            validate(
                &fragment(
                    frame(ItemKind::Cell),
                    vec![child(0, "ret"), child(1, "ret")],
                    false
                ),
                &mut seen
            ),
            Err(GrammarTransportError::InvalidApplication(
                GrammarApplicationReason::DuplicateNamedField
            )),
        );
    }

    /// A rule's builtin `Id` and `Bytes` literals are constants of their
    /// sorts, as a claim's are: each defines a key of its kind's role, and a
    /// malformed token is rejected.
    #[test]
    fn grammar_rules_hold_builtin_literals() {
        let token = |sort, ordinal, value: &str| DescriptorTerm::BuiltinToken {
            key: key(
                match sort {
                    BuiltinSort::Id => ProvenanceRole::ClaimIdToken,
                    _ => ProvenanceRole::ClaimBytesToken,
                },
                ordinal,
            ),
            sort,
            value: value.to_owned(),
        };
        let term = application(vec![
            DescriptorTermArgument::Positional {
                value: Box::new(token(BuiltinSort::Bytes, 0, r#"b"\x01""#)),
            },
            DescriptorTermArgument::Positional {
                value: Box::new(token(BuiltinSort::Id, 0, "$x")),
            },
            DescriptorTermArgument::Positional {
                value: Box::new(token(BuiltinSort::Bytes, 1, r#"b"""#)),
            },
        ]);
        assert_eq!(
            term.validate(|_| true, &BTreeSet::new(), &mut BTreeSet::new(), true),
            Ok(())
        );
        let mut keys = WireKeys::default();
        term.collect_wire_term_keys(&mut keys, ValidationSide::Left)
            .unwrap();
        assert!(
            keys.defined()
                .contains(&key(ProvenanceRole::ClaimBytesToken, 1))
        );
        assert!(
            keys.defined()
                .contains(&key(ProvenanceRole::ClaimIdToken, 0))
        );
        for malformed in [
            token(BuiltinSort::Id, 0, "x"),
            token(BuiltinSort::Bytes, 0, "x"),
        ] {
            assert_eq!(
                malformed.validate(|_| true, &BTreeSet::new(), &mut BTreeSet::new(), true),
                Err(GrammarTransportError::InvalidTerm(
                    GrammarTermReason::InvalidCompilerOwnedBuiltinToken
                )),
            );
        }
    }
}
