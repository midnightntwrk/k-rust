//! `concrete`, `symbolic`, and `smt_lemma` on equations and simplifications (KF-043).
//!
//! `concrete(x)` restricts a sentence to ground values of the left-hand binder
//! `x` (every binder when bare), `symbolic(x)` to values containing a variable,
//! and `smt_lemma` hands the equation to Z3 as an axiom. The keys name
//! left-hand binders by their Rust names; this module resolves them, checks
//! that no binder is restricted both ways, that no equation ordered after a
//! restricted one applies where the restriction skips it
//! ([`check_equation_restrictions`]), and that an `smt_lemma` mentions only
//! functions Z3 can see.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    ApplicationRef, Descriptor, DescriptorMatchRestriction, DescriptorRestriction, NodeOrigin,
    ProductionAttribute, SemanticId, SentenceKind, StableItemId, StructuredRuleDescriptor,
};
use krs_ir_levels::{
    IrMatchRestriction, IrRestriction, IrRestrictionVariable, IrTermKind, SemanticModule,
    SemanticProduction, SemanticRule, SemanticTerm,
};

use super::error::DescriptorLoweringError;
use super::origin::semantic_origin;
use crate::partition::production_display_name;

/// Lowers the keys of an equation or simplification, resolving each listed
/// name to its left-hand binder.
pub(super) fn lower_rule_restriction(
    descriptor: &Descriptor,
    rule: &StructuredRuleDescriptor,
) -> Result<Option<IrMatchRestriction>, DescriptorLoweringError> {
    let Some(restriction) = descriptor_restriction(rule) else {
        return Ok(None);
    };
    let concrete = restriction
        .concrete
        .as_ref()
        .map(|key| lower_key(descriptor, rule, key, "concrete"))
        .transpose()?;
    let symbolic = restriction
        .symbolic
        .as_ref()
        .map(|key| lower_key(descriptor, rule, key, "symbolic"))
        .transpose()?;
    if let (Some(concrete), Some(symbolic)) = (&concrete, &symbolic) {
        check_disjoint(descriptor, concrete, symbolic)?;
    }
    let smt_lemma = restriction
        .smt_lemma
        .as_ref()
        .map(|key| semantic_origin(descriptor, key.clone(), "smt-lemma"))
        .transpose()?;
    Ok(Some(IrMatchRestriction::new(concrete, symbolic, smt_lemma)))
}

fn descriptor_restriction(rule: &StructuredRuleDescriptor) -> Option<&DescriptorMatchRestriction> {
    match rule.sentence_kind {
        SentenceKind::Simplification => rule
            .simplification
            .as_ref()
            .and_then(|simplification| simplification.restriction.as_ref()),
        SentenceKind::Equation => rule.equation.as_ref().map(|equation| &equation.restriction),
        _ => None,
    }
}

fn lower_key(
    descriptor: &Descriptor,
    rule: &StructuredRuleDescriptor,
    key: &DescriptorRestriction,
    name: &str,
) -> Result<IrRestriction, DescriptorLoweringError> {
    let origin = semantic_origin(descriptor, key.key.clone(), &format!("restriction-{name}"))?;
    let mut variables = Vec::with_capacity(key.variables.len());
    for variable in &key.variables {
        let variable_origin =
            semantic_origin(descriptor, variable.key.clone(), "restriction-variable")?;
        if !rule.bindings.contains(&variable.name) {
            let binders = if rule.bindings.is_empty() {
                String::from("it has none")
            } else {
                format!(
                    "they are {}",
                    rule.bindings
                        .iter()
                        .map(|binding| format!("`{binding}`"))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            };
            return Err(invalid(
                descriptor.id(),
                format!(
                    "`{}` in `{name}(..)` is not a binder of the left-hand side of `{}`; `{name}(..)` names left-hand binders, and {binders}",
                    variable.name,
                    descriptor.id().item_name(),
                ),
                &variable_origin,
            ));
        }
        variables.push(IrRestrictionVariable::new(
            variable_origin,
            SemanticId::new(variable.name.clone())?,
        ));
    }
    Ok(IrRestriction::new(origin, variables))
}

/// No binder is both ground and symbolic: a bare key restricts every binder,
/// so it cannot be combined with the other key at all.
fn check_disjoint(
    descriptor: &Descriptor,
    concrete: &IrRestriction,
    symbolic: &IrRestriction,
) -> Result<(), DescriptorLoweringError> {
    let name = descriptor.id().item_name();
    if concrete.is_bare() && symbolic.is_bare() {
        return Err(invalid(
            descriptor.id(),
            format!(
                "`{name}` is both bare `concrete` and bare `symbolic`: no binder can be ground and symbolic at once; restrict different binders with `concrete(x)` and `symbolic(y)`"
            ),
            symbolic.origin(),
        ));
    }
    if concrete.is_bare() || symbolic.is_bare() {
        let (bare, other) = if concrete.is_bare() {
            ("concrete", symbolic)
        } else {
            ("symbolic", concrete)
        };
        return Err(invalid(
            descriptor.id(),
            format!(
                "`{name}` is bare `{bare}`, which restricts every left-hand binder, and also restricts binders the other way; list the binders of each key instead"
            ),
            other.origin(),
        ));
    }
    let concrete_ids = concrete
        .variables()
        .iter()
        .map(IrRestrictionVariable::id)
        .collect::<BTreeSet<_>>();
    if let Some(both) = symbolic
        .variables()
        .iter()
        .find(|variable| concrete_ids.contains(variable.id()))
    {
        return Err(invalid(
            descriptor.id(),
            format!(
                "`{}` is both concrete and symbolic in `{name}`; a binder cannot be ground and symbolic at once",
                both.id().as_str()
            ),
            both.origin(),
        ));
    }
    Ok(())
}

/// A function's restricted equations.
///
/// A restriction says when an equation is used, not what it states: an
/// equation restricted to ground `x` still holds where `x` is symbolic, and
/// is only not applied there; a function application no equation applies to
/// stays as it is, which is incomplete, not wrong. That holds as long as no
/// other equation of the function applies where the restriction skips this
/// one, for that equation would give the application its own value where the
/// restricted one, which still holds, may give another. An equation ordered
/// after it (an `owise` one, or one at a later priority) is defined to apply
/// exactly where the earlier ones do not, so it is such an equation unless
/// its own restriction skips it wherever this one is skipped:
///
/// - a `concrete` equation is skipped where a binder it restricts is not
///   ground, so the application's arguments are not ground, and a later bare
///   `concrete` equation is skipped there too, since every term its own
///   binders match in such arguments holds a variable;
/// - a `symbolic` equation is skipped where a binder it restricts is ground,
///   which no restriction of another equation, written over its own binders,
///   follows: so no equation may be ordered after it.
///
/// Equations of one order are one definition, which must agree where several
/// apply, so they never contradict one another's restriction. A
/// simplification states no definition, and is exempt.
///
/// Beyond that, the definition's routes carry a restriction on a function's
/// equation only in one form: both the native route and the K text route
/// compile through k-rust's frontend, whose rule-attribute check
/// (`check_function_rule_attributes` in `k-rust`'s
/// `definition/checks/labels.rs`) accepts `concrete` or `symbolic` on an
/// equation only when every equation of its function is bare `concrete` (or
/// bare `symbolic`). A listed restriction, or a restricted equation beside an
/// unrestricted one, holds its meaning but is refused here, at its key, since
/// no route compiles it.
pub(super) fn check_equation_restrictions(
    modules: &[SemanticModule],
) -> Result<(), DescriptorLoweringError> {
    let mut functions = BTreeMap::<&StableItemId, Vec<&SemanticRule>>::new();
    for rule in modules.iter().flat_map(SemanticModule::rules) {
        if rule.kind() != SentenceKind::Equation {
            continue;
        }
        if let Some(function) = rule.body().and_then(|body| root_production(body.from())) {
            functions.entry(function).or_default().push(rule);
        }
    }
    for (function, equations) in functions {
        for (name, key) in [
            ("concrete", IrMatchRestriction::concrete as KeyOf),
            ("symbolic", IrMatchRestriction::symbolic as KeyOf),
        ] {
            let restricted = equations
                .iter()
                .filter_map(|rule| rule.restriction().and_then(key).map(|key| (rule, key)))
                .collect::<Vec<_>>();
            for (rule, restriction) in &restricted {
                let later = equations.iter().find(|other| {
                    ordered_after(other, rule)
                        && !(name == "concrete"
                            && other
                                .restriction()
                                .and_then(key)
                                .is_some_and(IrRestriction::is_bare))
                });
                if let Some(later) = later {
                    return Err(invalid(
                        rule.id(),
                        later_equation_applies(name, rule, later),
                        restriction.origin(),
                    ));
                }
            }
            let Some((first, first_key)) = restricted.first() else {
                continue;
            };
            if let Some((rule, listed)) = restricted.iter().find(|(_, key)| !key.is_bare()) {
                return Err(invalid(
                    rule.id(),
                    format!(
                        "equation `{}` restricts only some binders with `{name}(..)`, which holds its meaning, but no route compiles it: the native and the K text route compile through k-rust's frontend, which takes `{name}` on an equation only bare, and only when every equation of its function is bare `{name}`; write bare `{name}`, or make it a #[k::simplification]",
                        rule.id().item_name()
                    ),
                    listed.origin(),
                ));
            }
            if let Some(other) = equations
                .iter()
                .find(|rule| rule.restriction().and_then(key).is_none())
            {
                return Err(invalid(
                    first.id(),
                    format!(
                        "equation `{}` is `{name}`, but equation `{}` of the same function `{}` is not, which holds its meaning, but no route compiles it: the native and the K text route compile through k-rust's frontend, which takes `{name}` on an equation only when every equation of its function is bare `{name}`; mark them all `{name}`, or make the restricted one a #[k::simplification]",
                        first.id().item_name(),
                        other.id().item_name(),
                        production_display_name(function),
                    ),
                    first_key.origin(),
                ));
            }
        }
    }
    Ok(())
}

/// The order of an equation among its function's: its priority, the default
/// 50 when it has none, an `owise` one after every other.
fn order(rule: &SemanticRule) -> (bool, u32) {
    rule.priority()
        .map_or((false, DEFAULT_PRIORITY), |priority| {
            (priority.is_owise(), priority.value())
        })
}

/// Whether `later` is ordered after `rule`: it applies only where `rule` does
/// not.
fn ordered_after(later: &SemanticRule, rule: &SemanticRule) -> bool {
    let ((later_owise, later_value), (owise, value)) = (order(later), order(rule));
    (later_owise && !owise) || (later_owise == owise && later_value > value)
}

/// The priority an equation without one has.
const DEFAULT_PRIORITY: u32 = 50;

/// Why the equation `later`, ordered after the `name`-restricted `rule`, would
/// apply where the restriction skips `rule`.
fn later_equation_applies(name: &str, rule: &SemanticRule, later: &SemanticRule) -> String {
    let (rule_name, later_name) = (rule.id().item_name(), later.id().item_name());
    let (later_owise, later_value) = order(later);
    let order = if later_owise {
        "`owise`".to_owned()
    } else {
        format!("`priority = {later_value}`")
    };
    let (skipped, fix) = if name == "concrete" {
        (
            "a binder it restricts is not ground",
            format!(
                "make `{later_name}` bare `concrete` too, which skips it wherever `{rule_name}` is skipped"
            ),
        )
    } else {
        (
            "a binder it restricts is ground",
            "give the equations one order".to_owned(),
        )
    };
    format!(
        "equation `{rule_name}` is `{name}`, so it is skipped where {skipped}, though it still holds there; equation `{later_name}`, ordered after it ({order}), applies wherever `{rule_name}` does not, so there it would give the function a value `{rule_name}` need not agree with: {fix}, or make `{rule_name}` a #[k::simplification]"
    )
}

type KeyOf = fn(&IrMatchRestriction) -> Option<&IrRestriction>;

fn root_production(term: &SemanticTerm) -> Option<&StableItemId> {
    match term.kind() {
        IrTermKind::Application {
            application: ApplicationRef::Declared(production),
            ..
        } => Some(production),
        _ => None,
    }
}

/// An `smt_lemma` becomes a Z3 axiom over the SMT translations of every
/// function it mentions; a function without one makes the backend fail or
/// silently drop the lemma.
pub(super) fn check_smt_lemmas(modules: &[SemanticModule]) -> Result<(), DescriptorLoweringError> {
    let productions = modules
        .iter()
        .flat_map(SemanticModule::productions)
        .map(|production| (production.id(), production))
        .collect::<BTreeMap<_, _>>();
    for rule in modules.iter().flat_map(SemanticModule::rules) {
        let Some(origin) = rule.restriction().and_then(IrMatchRestriction::smt_lemma) else {
            continue;
        };
        let Some(body) = rule.body() else {
            continue;
        };
        let mut terms = vec![body.from(), body.to()];
        terms.extend(
            rule.requires()
                .into_iter()
                .flat_map(krs_ir_levels::IrCondition::terms),
        );
        for term in terms {
            if let Some(unseen) = first_untranslatable(term, &productions) {
                return Err(DescriptorLoweringError::SmtLemmaUntranslatable {
                    reason: format!(
                        "`smt_lemma` on `{}` mentions {unseen}, which Z3 cannot see; Z3 sees a user function only through `smtlib = \"..\"` or `smt_hook = \"..\"`, so give it one or drop `smt_lemma`",
                        rule.id().item_name()
                    ),
                    range: origin.origin().exact_authored_range().map(Box::new),
                    item: Some(Box::new(rule.id().clone())),
                });
            }
        }
    }
    Ok(())
}

fn first_untranslatable(
    term: &SemanticTerm,
    productions: &BTreeMap<&StableItemId, &SemanticProduction>,
) -> Option<String> {
    let (unseen, children): (Option<String>, Vec<&SemanticTerm>) = match term.kind() {
        IrTermKind::Application {
            application,
            arguments,
            ..
        } => {
            let unseen = match application {
                ApplicationRef::Declared(id) => productions
                    .get(id)
                    .filter(|production| {
                        let attributes = production.attributes();
                        attributes.iter().any(|attribute| {
                            matches!(attribute, ProductionAttribute::Function { .. })
                        }) && !attributes.iter().any(|attribute| {
                            matches!(
                                attribute,
                                ProductionAttribute::Smtlib { .. }
                                    | ProductionAttribute::SmtHook { .. }
                            )
                        })
                    })
                    .map(|_| format!("function `{}`", production_display_name(id))),
                ApplicationRef::Builtin(operation) => {
                    (!operation.has_smt_translation()).then(|| {
                        let spec = operation.spec();
                        format!(
                            "builtin `{}::{}` (K `{}`), which has no SMT translation",
                            spec.rust_module, spec.rust_name, spec.k_label
                        )
                    })
                }
                // K generates `isS` and `project:S` without an SMT translation.
                ApplicationRef::Generated(operation) => Some(match operation {
                    krs_ir::GeneratedOperation::SortPredicate(_) => {
                        "the sort predicate `k::is!`, which has no SMT translation".to_owned()
                    }
                    krs_ir::GeneratedOperation::SortProjection(_) => {
                        "the sort projection `k::project!`, which has no SMT translation".to_owned()
                    }
                }),
            };
            (unseen, arguments.iter().collect())
        }
        IrTermKind::Map(operands) => (
            (!operands.operation().has_smt_translation()).then(|| {
                format!(
                    "the Map operation `{}`",
                    operands.operation().spec().k_label
                )
            }),
            operands.operands().collect(),
        ),
        IrTermKind::List(operands) => (
            (!operands.operation().has_smt_translation()).then(|| {
                format!(
                    "the List operation `{}`",
                    operands.operation().spec().k_label
                )
            }),
            operands.operands().collect(),
        ),
        IrTermKind::Set(operands) => (
            (!operands.operation().has_smt_translation()).then(|| {
                format!(
                    "the Set operation `{}`",
                    operands.operation().spec().k_label
                )
            }),
            operands.operands().collect(),
        ),
        IrTermKind::KSequence { items, .. } => (None, items.iter().collect()),
        IrTermKind::Cell { children, .. } => (None, children.iter().collect()),
        IrTermKind::Rewrite { from, to } => (None, vec![from.as_ref(), to.as_ref()]),
        IrTermKind::As { pattern, .. } => (None, vec![pattern.as_ref()]),
        IrTermKind::Or { alternatives } => (None, alternatives.iter().collect()),
        IrTermKind::Matches { .. } => (Some("`k::matches!` (K's :=K)".to_owned()), Vec::new()),
        IrTermKind::Let { .. } => (Some("a `let` block (K's #let)".to_owned()), Vec::new()),
        IrTermKind::Variable { .. } | IrTermKind::Token { .. } => (None, Vec::new()),
    };
    unseen.or_else(|| {
        children
            .into_iter()
            .find_map(|child| first_untranslatable(child, productions))
    })
}

fn invalid(item: &StableItemId, reason: String, origin: &NodeOrigin) -> DescriptorLoweringError {
    DescriptorLoweringError::InvalidMatchRestriction {
        reason,
        range: origin.origin().exact_authored_range().map(Box::new),
        item: Some(Box::new(item.clone())),
    }
}
