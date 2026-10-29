//! The root of an equation's and a simplification's subject
//! (`krs::analysis::subject-root-not-function`).
//!
//! An equation defines one function: it states the value of that function's
//! application to the arguments it matches, so its subject's root is that
//! application. A constructor application or a literal at the root is a
//! value, which evaluation leaves as written: it defines no function, and
//! stating what it equals either restates it or makes two different values
//! one. A builtin operation is defined by its builtin domain, not by the
//! definition's equations.
//!
//! A simplification rewrites an unevaluated application to an equal, simpler
//! term. Only a function's application, a declared or a builtin one, stands
//! unevaluated in a term; a constructor application, a collection's unit,
//! element or concatenation, or a literal is a value, so a simplification
//! rooted at one simplifies nothing, for the same reason.
//! A predicate simplification is rooted at its predicate, which `ml` judges.
//!
//! Whether a head is a function is a fact of the declaration it resolves to
//! ([`ProductionSignature::function`]), so this is decided here, after
//! resolution. The root is read after the alternatives at an equation's root
//! are distributed (`equation_alternatives`), so alternatives that apply one
//! constructor are that constructor's application. Alternatives left at the
//! root apply no one head: each is a whole subject, so the first that applies
//! no function is refused as a root without `|` is, and alternatives that each
//! apply a function but not one are refused as alternatives.

use std::collections::BTreeMap;

use krs_ir::{
    Descriptor, DescriptorApplicationRef, DescriptorPayload, DescriptorTerm, SentenceKind,
    StableItemId,
};

use super::catalog::ProductionSignature;
use super::collection_types::{application_spelling, spelling, term_key};
use super::equation_alternatives::{different_functions, root_alternatives};
use super::error::DescriptorLoweringError;
use super::function_patterns::{Applied, applied_function};
use super::origin::key_range;

/// Refuses each equation whose subject is not the application of a function
/// the definition declares, and each simplification whose subject is not the
/// application of a declared or builtin function, at the root's head.
///
/// # Errors
///
/// Returns [`DescriptorLoweringError::SubjectRootNotFunction`] for the first
/// such sentence, and [`DescriptorLoweringError::InvalidPatternOr`] for root
/// alternatives that apply different functions.
pub(super) fn check_subject_roots(
    descriptors: &[&Descriptor],
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<(), DescriptorLoweringError> {
    for descriptor in descriptors {
        let DescriptorPayload::StructuredRule(rule) = descriptor.payload() else {
            continue;
        };
        let refuse = |root: &DescriptorTerm, reason| {
            let key = match root {
                DescriptorTerm::Application { reference, .. } => &reference.key,
                other => term_key(other),
            };
            Err(DescriptorLoweringError::SubjectRootNotFunction {
                item: Box::new(descriptor.id().clone()),
                reason,
                range: key_range(descriptor, key).map(Box::new),
            })
        };
        match rule.sentence_kind {
            SentenceKind::Equation if matches!(rule.subject, DescriptorTerm::Or { .. }) => {
                let alternatives = root_alternatives(&rule.subject);
                for alternative in &alternatives {
                    if let Some(reason) = equation_root(alternative, catalog) {
                        return refuse(alternative, reason);
                    }
                }
                if let Some(error) = different_functions(descriptor, &alternatives) {
                    return Err(error);
                }
            }
            SentenceKind::Equation => {
                if let Some(reason) = equation_root(&rule.subject, catalog) {
                    return refuse(&rule.subject, reason);
                }
            }
            SentenceKind::Simplification if !rule.predicate => {
                if let Some(reason) = simplification_root(&rule.subject, catalog) {
                    return refuse(&rule.subject, reason);
                }
            }
            _ => {}
        }
    }
    Ok(())
}

/// What to write instead of a value at a sentence's root.
const INSTEAD: &str = "to define a function, write its application here, and to rewrite this term in a step of the computation, write a `#[k::rule]`";

/// Why `subject` is no equation's subject, or `None` when it applies a
/// declared function.
fn equation_root(
    subject: &DescriptorTerm,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Option<String> {
    let DescriptorTerm::Application { reference, .. } = subject else {
        return Some(format!(
            "an equation defines one function, so its subject is that function's application, and `{}` applies none: it is a value, which no equation defines; {INSTEAD}",
            spelling(subject)
        ));
    };
    match &reference.application {
        DescriptorApplicationRef::Declared(id) if is_function(id, catalog) => None,
        DescriptorApplicationRef::Declared(id) => Some(format!(
            "an equation defines one function, so its subject is that function's application, but `{}` is a constructor: its application is a value, which evaluation leaves as written, so the equation defines no function; {INSTEAD}",
            id.item_name()
        )),
        other => Some(format!(
            "an equation defines one function the definition declares, so its subject is that function's application, but `{}` is a builtin operation, which its builtin domain defines; to state a fact about its applications, write a `#[k::simplification]`",
            builtin_spelling(other)
        )),
    }
}

/// Why `subject` is no simplification's subject, or `None` when it applies a
/// declared or builtin function, or a builtin operation whose lowering
/// decides.
fn simplification_root(
    subject: &DescriptorTerm,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Option<String> {
    let value = match subject {
        DescriptorTerm::Application { reference, .. } => match &reference.application {
            DescriptorApplicationRef::Declared(id) if !is_function(id, catalog) => {
                format!("`{}` is a constructor, and its application", id.item_name())
            }
            DescriptorApplicationRef::Builtin(operation) if !operation.is_functional() => {
                format!(
                    "`{}` builds a value of its builtin domain, and its application",
                    builtin_spelling(&reference.application)
                )
            }
            // A collection's unit, element and concatenation build the collection: the
            // singleton set `set::item(x)` is a value as a constructor's application is.
            application
                if matches!(
                    applied_function(application, catalog),
                    Applied::Collection | Applied::Elements
                ) =>
            {
                format!(
                    "`{}` builds a value of its builtin domain, and its application",
                    builtin_spelling(application)
                )
            }
            _ => return None,
        },
        other => format!("`{}` applies no function and", spelling(other)),
    };
    Some(format!(
        "a simplification rewrites a function's unevaluated application to an equal, simpler term, but {value} is a value, which evaluation leaves as written, so the simplification simplifies nothing; to rewrite this term in a step of the computation, write a `#[k::rule]`"
    ))
}

/// A builtin operation as its facade path spells it, its arguments elided:
/// `k::builtin::int::add(..)`.
fn builtin_spelling(application: &DescriptorApplicationRef) -> String {
    match application {
        DescriptorApplicationRef::Builtin(operation) => {
            let spec = operation.spec();
            format!("k::builtin::{}::{}(..)", spec.rust_module, spec.rust_name)
        }
        other => application_spelling(other),
    }
}

fn is_function(id: &StableItemId, catalog: &BTreeMap<StableItemId, ProductionSignature>) -> bool {
    catalog.get(id).is_some_and(|signature| signature.function)
}
