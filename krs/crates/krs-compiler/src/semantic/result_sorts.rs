//! The sort of an equation's and a simplification's result
//! (`krs::analysis::invalid-term`).
//!
//! An equation or a simplification states that the application its subject writes equals its
//! result: an application of a function whose result sort is `S` has, wherever it has one, a
//! value of `S`. So the result's sort must be `S` or a sort below it. A result of another sort
//! (a `Stmt` for an `Int` function) states an equality no value satisfies: no value of the
//! result's sort is a value of the application's, so the sentence is ill-sorted, whatever sort
//! the author's signature writes around it.

use krs_ir::SentenceKind;
use krs_ir_levels::{IrSortRef, SemanticModule, definedness::Sorts};

use super::error::DescriptorLoweringError;
use super::overload::sort_name;

/// Refuses the first equation or term simplification whose result's sort is not below its
/// subject's ([module docs](self)).
///
/// # Errors
///
/// Returns [`DescriptorLoweringError::InvalidTerm`] for the first such sentence.
pub(super) fn check_result_sorts(
    modules: &[SemanticModule],
) -> Result<(), DescriptorLoweringError> {
    let Some(sorts) = Sorts::of_modules(modules) else {
        return Ok(());
    };
    for rule in modules.iter().flat_map(SemanticModule::rules) {
        let what = match rule.kind() {
            SentenceKind::Equation => "equation",
            SentenceKind::Simplification => "simplification",
            _ => continue,
        };
        let Some(body) = rule.body() else {
            continue;
        };
        if body.local_term().is_some() {
            continue;
        }
        let (subject, result) = (body.from().sort(), body.to().sort());
        // A sort parameter is the signature's own, which no term has.
        // Every sort is below `K`, a sequence of items.
        if matches!(subject, IrSortRef::Builtin(krs_ir::BuiltinSort::KSequence))
            || matches!(subject, IrSortRef::Parameter(_))
            || matches!(result, IrSortRef::Parameter(_))
            || sorts.is_subsort(result, subject)
        {
            continue;
        }
        let (subject, result) = (sort_name(subject), sort_name(result));
        return Err(DescriptorLoweringError::InvalidTerm {
            id: Box::new(rule.id().clone()),
            detail: format!(
                "the result of {what} `{}` has sort `{result}`, which is not below `{subject}`, the sort of the application its subject writes: the {what} states that the application equals its result, and no term of sort `{result}` is a value of sort `{subject}`; write a result of sort `{subject}`, or of a sort below it",
                rule.id().item_name(),
            ),
            range: body
                .to()
                .origin()
                .origin()
                .exact_authored_range()
                .map(Box::new),
        });
    }
    Ok(())
}
