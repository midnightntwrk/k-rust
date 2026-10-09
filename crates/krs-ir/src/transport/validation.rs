//! Stage reference checks and the recursive validator for transport terms.

use std::collections::BTreeSet;

use super::detail::StateTermReason;
use crate::{
    BuiltinSort, DescriptorStage, HostStage, ItemKind, ProductionFieldId, ProvenanceKey, Stage,
};

use super::configuration::StateTransportError;
use super::grammar::{
    CellTermField, DescriptorApplicationHeadClass, DescriptorLiteral, GrammarTransportError,
    SortTestKind, Term,
};

/// Host references carry Rust type keys without stable item kinds or field text.
/// Collector output must pass `Descriptor::new` after resolution, which runs the descriptor-stage contracts.
pub(crate) trait ValidationStage: Stage {
    /// Reads sort provenance from an unresolved host occurrence or a resolved descriptor occurrence.
    fn sort_key(sort: &Self::Sort) -> &ProvenanceKey;
    /// Reads application provenance from an unresolved host occurrence or a resolved descriptor occurrence.
    fn application_key(application: &Self::Application) -> &ProvenanceKey;
    /// Host sort kinds must be checked by `DescriptorStage::validate_sort` after resolution.
    fn validate_sort(sort: &Self::Sort) -> Result<(), GrammarTransportError>;
    /// Host application kinds and catalogs must be checked by `DescriptorStage::validate_application` after resolution.
    fn validate_application(application: &Self::Application) -> Result<(), GrammarTransportError>;
    /// Host fragments require children with their host error; `DescriptorStage::validate_fragment` must also check the resolved Cell kind.
    fn validate_fragment(
        declaration: &Self::Nominal,
        empty: bool,
    ) -> Result<(), StateTransportError>;
}

impl ValidationStage for HostStage {
    fn sort_key(sort: &Self::Sort) -> &ProvenanceKey {
        &sort.key
    }

    fn application_key(application: &Self::Application) -> &ProvenanceKey {
        &application.key
    }

    fn validate_sort(_: &Self::Sort) -> Result<(), GrammarTransportError> {
        Ok(())
    }

    fn validate_application(_: &Self::Application) -> Result<(), GrammarTransportError> {
        Ok(())
    }

    fn validate_fragment(_: &Self::Nominal, empty: bool) -> Result<(), StateTransportError> {
        if empty {
            Err(StateTransportError::InvalidTerm(
                StateTermReason::EmptyFragment,
            ))
        } else {
            Ok(())
        }
    }
}

impl ValidationStage for DescriptorStage {
    fn sort_key(sort: &Self::Sort) -> &ProvenanceKey {
        &sort.key
    }

    fn application_key(application: &Self::Application) -> &ProvenanceKey {
        &application.key
    }

    fn validate_sort(sort: &Self::Sort) -> Result<(), GrammarTransportError> {
        sort.sort.validate()
    }

    fn validate_application(application: &Self::Application) -> Result<(), GrammarTransportError> {
        application.application.validate()
    }

    fn validate_fragment(
        declaration: &Self::Nominal,
        empty: bool,
    ) -> Result<(), StateTransportError> {
        if declaration.item_kind() != ItemKind::Cell || empty {
            Err(StateTransportError::InvalidTerm(
                StateTermReason::EmptyOrNonNominalFragment,
            ))
        } else {
            Ok(())
        }
    }
}

/// Nonrecursive checks for one term context.
/// Each hook must finish the node's checks before the shared traversal visits its children.
pub(crate) trait TermValidation<S: ValidationStage> {
    type Error;

    fn variable(
        &mut self,
        key: &ProvenanceKey,
        path_key: &ProvenanceKey,
        name: &str,
    ) -> Result<(), Self::Error>;

    fn application(
        &mut self,
        head_class: DescriptorApplicationHeadClass,
        reference: &S::Application,
        path_key: &ProvenanceKey,
        arguments: &crate::Arguments<S>,
    ) -> Result<(), Self::Error>;

    fn literal(
        &mut self,
        key: &ProvenanceKey,
        literal: &DescriptorLiteral,
    ) -> Result<(), Self::Error>;

    fn wildcard(&mut self, key: &ProvenanceKey) -> Result<(), Self::Error>;

    fn builtin_token(
        &mut self,
        key: &ProvenanceKey,
        sort: BuiltinSort,
        value: &str,
    ) -> Result<(), Self::Error>;

    fn anonymous(
        &mut self,
        key: &ProvenanceKey,
        sort: &S::Sort,
        spelling: &str,
    ) -> Result<(), Self::Error>;

    fn or_bool(
        &mut self,
        key: &ProvenanceKey,
        _arguments: &crate::AtLeastTwo<Term<S>>,
    ) -> Result<(), Self::Error>;

    fn lexeme(
        &mut self,
        key: &ProvenanceKey,
        sort: &S::Sort,
        text: &str,
    ) -> Result<(), Self::Error>;

    fn cell(
        &mut self,
        key: &ProvenanceKey,
        declaration: &S::Nominal,
        fields: &[CellTermField<S>],
    ) -> Result<(), Self::Error>;

    fn sort_test(
        &mut self,
        key: &ProvenanceKey,
        kind: SortTestKind,
        sort: &S::Sort,
    ) -> Result<(), Self::Error>;

    /// `name @ pattern` (K's `#as`), admitted only in left-hand sides.
    fn pattern_as(
        &mut self,
        key: &ProvenanceKey,
        binding_key: &ProvenanceKey,
        name: &str,
    ) -> Result<(), Self::Error>;

    /// `A | B | ..` (K's `#Or`), admitted only in left-hand sides.
    fn pattern_or(&mut self, key: &ProvenanceKey) -> Result<(), Self::Error>;

    fn argument(
        &mut self,
        argument: crate::TermArgumentRef<'_, S>,
        fields: &mut BTreeSet<ProductionFieldId>,
    ) -> Result<(), Self::Error>;

    fn cell_field(
        &mut self,
        field: &CellTermField<S>,
        names: &mut BTreeSet<ProductionFieldId>,
    ) -> Result<(), Self::Error>;
}

pub(crate) fn validate_term<S: ValidationStage, C: TermValidation<S>>(
    term: &Term<S>,
    context: &mut C,
) -> Result<(), C::Error> {
    match term {
        Term::Variable {
            key,
            path_key,
            name,
        } => context.variable(key, path_key, name),
        Term::Application {
            head_class,
            reference,
            path_key,
            arguments,
        } => {
            context.application(*head_class, reference, path_key, arguments)?;
            validate_arguments(arguments, context)
        }
        Term::Literal { key, literal } => context.literal(key, literal),
        Term::Wildcard { key } => context.wildcard(key),
        Term::BuiltinToken { key, sort, value } => context.builtin_token(key, *sort, value),
        Term::Anonymous {
            key,
            sort,
            spelling,
        } => context.anonymous(key, sort, spelling),
        Term::OrBool { key, arguments } => {
            context.or_bool(key, arguments)?;
            for argument in arguments.iter() {
                validate_term(argument, context)?;
            }
            Ok(())
        }
        Term::Lexeme { key, sort, text } => context.lexeme(key, sort, text),
        Term::Cell {
            key,
            declaration,
            fields,
        } => {
            context.cell(key, declaration, fields)?;
            let mut names = BTreeSet::new();
            for field in fields {
                context.cell_field(field, &mut names)?;
                validate_term(&field.value, context)?;
            }
            Ok(())
        }
        Term::SortTest {
            key,
            kind,
            sort,
            operand,
        } => {
            context.sort_test(key, *kind, sort)?;
            validate_term(operand, context)
        }
        Term::As {
            key,
            binding_key,
            name,
            pattern,
        } => {
            context.pattern_as(key, binding_key, name)?;
            validate_term(pattern, context)
        }
        Term::Or { key, alternatives } => {
            context.pattern_or(key)?;
            for alternative in alternatives.iter() {
                validate_term(alternative, context)?;
            }
            Ok(())
        }
    }
}

fn validate_arguments<S: ValidationStage, C: TermValidation<S>>(
    arguments: &crate::Arguments<S>,
    context: &mut C,
) -> Result<(), C::Error> {
    let mut fields = BTreeSet::new();
    for argument in arguments {
        context.argument(argument.clone(), &mut fields)?;
        let (crate::TermArgumentRef::Positional { value }
        | crate::TermArgumentRef::Named { value, .. }) = argument;
        validate_term(value, context)?;
    }
    Ok(())
}
