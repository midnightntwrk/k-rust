//! Matching-logic predicates (KF-039): placement, inference, and lowering.
//!
//! A predicate is a descriptor term rooted at a `k::ml` connective, which the
//! collector resolved by `TypeId`. Its `ml::equals` and `ml::ceil` operands
//! are object terms, inferred and lowered like any condition term; its
//! `ml::exists` closure introduces a local binder (BIND-1) visible only in
//! the closure's body. A connective is never an object term: one below an
//! object function, or an object term where a predicate is expected, is an
//! error.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    BuiltinSort, DescriptorApplicationRef, DescriptorRuleCondition, DescriptorTerm, MlConnective,
    MlOperand, ProvenanceKey, SemanticId, SentenceKind,
};
use krs_ir_levels::{
    IrMlKind, SemanticCondition, SemanticMlPredicate, SemanticRuleCondition, SemanticScopedBinder,
    SemanticSortRef, SemanticVariable,
};

use super::catalog::semantic_sort_ref;
use super::error::DescriptorLoweringError;
use super::infer::{StructuredTermBuilder, least_instance};
use super::origin::semantic_origin;

/// The K spelling of a connective in diagnostics.
fn connective_name(connective: MlConnective) -> String {
    let marker = connective.facade_marker();
    format!("{}::{}", marker.module, marker.name)
}

/// The connective at the root of `term`, if any.
pub(super) fn root_connective(term: &DescriptorTerm) -> Option<MlConnective> {
    match term {
        DescriptorTerm::Application { reference, .. } => match reference.application {
            DescriptorApplicationRef::Ml(connective) => Some(connective),
            _ => None,
        },
        _ => None,
    }
}

/// Whether a condition is a matching-logic predicate.
pub(super) fn is_predicate_condition(condition: &DescriptorRuleCondition) -> bool {
    root_connective(&condition.term).is_some()
}

/// Rejects a predicate in the `requires` or `ensures` of a sentence kind
/// that admits only object-Bool conditions (KF-039, diagnostic 1).
pub(super) fn check_condition_placement(
    builder: &StructuredTermBuilder<'_>,
    kind: SentenceKind,
    condition: &DescriptorRuleCondition,
    ensures: bool,
) -> Result<(), DescriptorLoweringError> {
    let allowed = match kind {
        SentenceKind::Claim => true,
        SentenceKind::Simplification => !ensures,
        SentenceKind::Transition
        | SentenceKind::Equation
        | SentenceKind::Alias
        | SentenceKind::Desugar => false,
    };
    if allowed || !is_predicate_condition(condition) {
        return Ok(());
    }
    let sentence = match kind {
        SentenceKind::Transition => "a transition",
        SentenceKind::Equation => "an equation",
        SentenceKind::Simplification => "a simplification's ensures",
        _ => "this sentence",
    };
    Err(DescriptorLoweringError::MlPlacement {
        item: Box::new(builder.descriptor.id().clone()),
        reason: format!(
            "matching-logic conditions are allowed on claims and simplifications, not on {sentence}: a rule's condition is an object Bool (write `int::eq`, `bool::not`, ..., not `ml::equals`, `ml::not`)"
        ),
        range: builder.authored_range(&condition.key),
    })
}

/// Lowers one `requires` or `ensures` condition: an object Bool, or a
/// matching-logic predicate where the sentence admits one.
pub(super) fn lower_condition(
    builder: &mut StructuredTermBuilder<'_>,
    condition: &DescriptorRuleCondition,
    role: &str,
) -> Result<SemanticCondition, DescriptorLoweringError> {
    if root_connective(&condition.term).is_some() {
        return Ok(SemanticCondition::Predicate(
            builder.lower_predicate(&condition.term, false)?,
        ));
    }
    let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
    Ok(SemanticCondition::Bool(SemanticRuleCondition::new(
        semantic_origin(builder.descriptor, condition.key.clone(), role)?,
        builder.lower(&condition.term, Some(&bool_sort), false)?,
    )))
}

/// Infers one condition: an object Bool, or a predicate.
pub(super) fn infer_condition(
    builder: &mut StructuredTermBuilder<'_>,
    condition: &DescriptorRuleCondition,
) -> Result<(), DescriptorLoweringError> {
    if root_connective(&condition.term).is_some() {
        return builder.infer_predicate(&condition.term, false);
    }
    let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
    builder.infer(&condition.term, Some(&bool_sort), false)
}

/// The closure of an `ml::exists`.
struct Closure<'a> {
    key: &'a ProvenanceKey,
    binder_key: &'a ProvenanceKey,
    name: &'a str,
    sort: SemanticSortRef,
    sort_key: &'a ProvenanceKey,
    body: &'a DescriptorTerm,
}

impl StructuredTermBuilder<'_> {
    pub(super) fn invalid_ml(
        &self,
        key: &ProvenanceKey,
        reason: String,
    ) -> DescriptorLoweringError {
        DescriptorLoweringError::InvalidMlPredicate {
            item: Box::new(self.descriptor.id().clone()),
            reason,
            range: self.authored_range(key),
        }
    }

    /// The error for a connective below an object function (diagnostic 2).
    pub(super) fn ml_in_object_term(
        &self,
        key: &ProvenanceKey,
        connective: MlConnective,
    ) -> DescriptorLoweringError {
        self.invalid_ml(
            key,
            format!(
                "`{}` is a matching-logic predicate, not an object term: it cannot be an operand of an object function or stand where a value is expected; predicates combine only with ml::not, ml::and, ml::or, ml::implies, and ml::exists",
                connective_name(connective)
            ),
        )
    }

    /// The key that locates `term` in diagnostics.
    fn term_key(term: &DescriptorTerm) -> &ProvenanceKey {
        match term {
            DescriptorTerm::Application { reference, .. } => &reference.key,
            DescriptorTerm::Variable { key, .. }
            | DescriptorTerm::Literal { key, .. }
            | DescriptorTerm::Wildcard { key }
            | DescriptorTerm::BuiltinToken { key, .. }
            | DescriptorTerm::Anonymous { key, .. }
            | DescriptorTerm::OrBool { key, .. }
            | DescriptorTerm::Cell { key, .. }
            | DescriptorTerm::Lexeme { key, .. }
            | DescriptorTerm::SortTest { key, .. }
            | DescriptorTerm::As { key, .. }
            | DescriptorTerm::Or { key, .. }
            | DescriptorTerm::Matches { key, .. }
            | DescriptorTerm::Let { key, .. }
            | DescriptorTerm::Closure { key, .. }
            | DescriptorTerm::Rewrite { key, .. } => key,
        }
    }

    /// The operands of a connective, checked against its arity.
    fn ml_operands<'t>(
        &self,
        connective: MlConnective,
        key: &ProvenanceKey,
        arguments: &'t krs_ir::Arguments<krs_ir::DescriptorStage>,
    ) -> Result<Vec<&'t DescriptorTerm>, DescriptorLoweringError> {
        let mut operands = Vec::with_capacity(arguments.len());
        for argument in arguments {
            match argument {
                krs_ir::TermArgumentRef::Positional { value } => operands.push(value),
                krs_ir::TermArgumentRef::Named { .. } => {
                    return Err(self.invalid_ml(
                        key,
                        format!(
                            "`{}` takes positional operands",
                            connective_name(connective)
                        ),
                    ));
                }
            }
        }
        let expected = connective.operands().len();
        if operands.len() != expected {
            return Err(self.invalid_ml(
                key,
                format!(
                    "`{}` takes {expected} operand{}, but {} {} written",
                    connective_name(connective),
                    if expected == 1 { "" } else { "s" },
                    operands.len(),
                    if operands.len() == 1 { "is" } else { "are" },
                ),
            ));
        }
        Ok(operands)
    }

    /// The closure of an `ml::exists`, which must be its one operand.
    fn ml_closure<'t>(
        &self,
        key: &ProvenanceKey,
        operand: &'t DescriptorTerm,
    ) -> Result<Closure<'t>, DescriptorLoweringError> {
        let DescriptorTerm::Closure {
            key: closure_key,
            binder_key,
            name,
            sort,
            body,
        } = operand
        else {
            return Err(self.invalid_ml(
                key,
                "ml::exists takes exactly one closure with one typed parameter: `ml::exists(|x: Sort| predicate)`".to_owned(),
            ));
        };
        Ok(Closure {
            key: closure_key,
            binder_key,
            name,
            sort: semantic_sort_ref(&sort.sort),
            sort_key: &sort.key,
            body,
        })
    }

    /// Rejects an `ml::exists` binder that shadows a rule binder or an
    /// enclosing local binder (diagnostic 6).
    fn check_exists_shadowing(&self, closure: &Closure<'_>) -> Result<(), DescriptorLoweringError> {
        let name = closure.name;
        if self.binding_names.contains(name)
            || self.declared_binders.contains_key(name)
            || self.is_let_local_name(name)
        {
            return Err(self.invalid_ml(
                closure.binder_key,
                format!(
                    "the ml::exists binder `{name}` shadows a binder of the sentence; quantify a fresh name (K would silently shadow `{name}`)"
                ),
            ));
        }
        Ok(())
    }

    /// The error for an object term where a predicate is expected
    /// (diagnostic 2), with the fix-it `ml::equals(true, <term>)`.
    fn bool_where_predicate(&self, term: &DescriptorTerm) -> DescriptorLoweringError {
        let reason = "a predicate is expected here, but this is an object term; an object Bool enters matching logic only as `ml::equals(true, <term>)` (K's `{ true #Equals B }`)".to_owned();
        self.invalid_ml(Self::term_key(term), reason)
    }

    /// Infers the object operands of a predicate. `subject` is set on the
    /// left side of a predicate simplification, whose operands are patterns.
    pub(super) fn infer_predicate(
        &mut self,
        term: &DescriptorTerm,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        let DescriptorTerm::Application {
            reference,
            arguments,
            ..
        } = term
        else {
            return Err(self.bool_where_predicate(term));
        };
        let DescriptorApplicationRef::Ml(connective) = reference.application else {
            return Err(self.bool_where_predicate(term));
        };
        let operands = self.ml_operands(connective, &reference.key, arguments)?;
        match connective.operands() {
            [] => Ok(()),
            [MlOperand::Binder] => {
                if subject {
                    return Err(self.invalid_ml(
                        &reference.key,
                        "ml::exists cannot occur on the left side of a predicate simplification"
                            .to_owned(),
                    ));
                }
                let closure = self.ml_closure(&reference.key, operands[0])?;
                self.check_exists_shadowing(&closure)?;
                self.push_let_names(BTreeSet::from([closure.name.to_owned()]));
                let inferred = self.infer_predicate(closure.body, subject);
                self.pop_let_names();
                inferred
            }
            kinds => {
                for (operand, kind) in operands.into_iter().zip(kinds) {
                    match kind {
                        MlOperand::Predicate => self.infer_predicate(operand, subject)?,
                        MlOperand::Term => {
                            if let Some(inner) = root_connective(operand) {
                                return Err(self.ml_in_object_term(Self::term_key(operand), inner));
                            }
                            self.infer(operand, None, subject)?;
                        }
                        MlOperand::Binder => {
                            return Err(self.invalid_ml(
                                &reference.key,
                                "a closure occurs only as the one operand of ml::exists".to_owned(),
                            ));
                        }
                    }
                }
                Ok(())
            }
        }
    }

    /// Lowers a predicate whose operands were inferred.
    pub(super) fn lower_predicate(
        &mut self,
        term: &DescriptorTerm,
        subject: bool,
    ) -> Result<SemanticMlPredicate, DescriptorLoweringError> {
        let DescriptorTerm::Application {
            reference,
            arguments,
            ..
        } = term
        else {
            return Err(self.bool_where_predicate(term));
        };
        let DescriptorApplicationRef::Ml(connective) = reference.application else {
            return Err(self.bool_where_predicate(term));
        };
        let origin = semantic_origin(self.descriptor, reference.key.clone(), "ml-connective")?;
        let operands = self.ml_operands(connective, &reference.key, arguments)?;
        let kind = match connective {
            MlConnective::Top => IrMlKind::Top,
            MlConnective::Bottom => IrMlKind::Bottom,
            MlConnective::Not => IrMlKind::Not {
                operand: Box::new(self.lower_predicate(operands[0], subject)?),
            },
            MlConnective::And | MlConnective::Or | MlConnective::Implies => {
                let left = Box::new(self.lower_predicate(operands[0], subject)?);
                let right = Box::new(self.lower_predicate(operands[1], subject)?);
                match connective {
                    MlConnective::And => IrMlKind::And { left, right },
                    MlConnective::Or => IrMlKind::Or { left, right },
                    _ => IrMlKind::Implies { left, right },
                }
            }
            MlConnective::Equals => {
                let left = self.lower(operands[0], None, subject)?;
                let right = self.lower(operands[1], None, subject)?;
                let operand_sort = least_instance(
                    &[left.sort().clone(), right.sort().clone()],
                    None,
                    self.sort_parents,
                )
                .map_err(|_| {
                    self.invalid_ml(
                        &reference.key,
                        format!(
                            "the operands of ml::equals have sorts `{}` and `{}`, which share no least common sort; both sides of an equality denote values of one sort",
                            super::overload::sort_name(left.sort()),
                            super::overload::sort_name(right.sort())
                        ),
                    )
                })?;
                IrMlKind::Equals {
                    operand_sort,
                    left: Box::new(left),
                    right: Box::new(right),
                }
            }
            MlConnective::Ceil => {
                let term = self.lower(operands[0], None, subject)?;
                IrMlKind::Ceil {
                    operand_sort: term.sort().clone(),
                    term: Box::new(term),
                }
            }
            MlConnective::Exists => {
                let closure = self.ml_closure(&reference.key, operands[0])?;
                let id =
                    SemanticId::local(closure.name, self.wildcard_offset + self.wildcards.len())?;
                self.wildcards
                    .push(SemanticVariable::new(id.clone(), closure.sort.clone()));
                let binder = SemanticScopedBinder::new(
                    semantic_origin(self.descriptor, closure.key.clone(), "ml-exists-binder")?,
                    semantic_origin(
                        self.descriptor,
                        closure.binder_key.clone(),
                        "ml-exists-binder-name",
                    )?,
                    id.clone(),
                    semantic_origin(
                        self.descriptor,
                        closure.sort_key.clone(),
                        "ml-exists-binder-sort",
                    )?,
                    closure.sort.clone(),
                );
                self.push_let_scope(BTreeMap::from([(
                    closure.name.to_owned(),
                    (id, closure.sort.clone()),
                )]));
                let body = self.lower_predicate(closure.body, subject);
                self.pop_let_scope();
                IrMlKind::Exists {
                    binder,
                    body: Box::new(body?),
                }
            }
        };
        Ok(SemanticMlPredicate::new(origin, kind))
    }
}
