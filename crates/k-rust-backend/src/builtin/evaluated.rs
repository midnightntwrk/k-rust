//! Which hooks the evaluator applies: [`evaluates`]; a responsibility, not an algorithm; no
//! counter of its own, no worklist.
//!
//! The simplifier evaluates a hooked application by its builtin before any equation, and applies
//! the symbol's equations only where the builtin gives no value (`simplify.rs`). A hook whose
//! builtin takes no step on any arguments (the dispatch answers `NotImplemented` by its name) is
//! read through its equations alone: they are its meaning in the theory the backend reads. A hook
//! whose builtin takes some step makes each equation at its symbol an axiom about the builtin's
//! values, which the critical-pair check pairs with the hook's written meaning
//! (`confluence/hooks.rs`).

use crate::term::names::{HookName, HookNamespace};

/// The hooks of the evaluated namespaces that the dispatch answers `NotImplemented` by name: no
/// builtin step exists at them. Each is checked against the dispatch
/// (`every_hook_of_the_builtin_modules_agrees_with_the_dispatch`).
const NOT_EVALUATED: &[&str] = &[
    "BYTES.bytes2hex",
    "BYTES.getMInt",
    "BYTES.lengthMInt",
    "BYTES.memset",
    "BYTES.padLeftMInt",
    "BYTES.padRightMInt",
    "BYTES.replaceAtMInt",
    "BYTES.substrMInt",
    "BYTES.updateMInt",
    "FLOAT.acos",
    "FLOAT.asin",
    "FLOAT.atan",
    "FLOAT.atan2",
    "FLOAT.cos",
    "FLOAT.exp",
    "FLOAT.exponent",
    "FLOAT.log",
    "FLOAT.minValue",
    "FLOAT.pow",
    "FLOAT.rat2float",
    "FLOAT.rem",
    "FLOAT.sin",
    "FLOAT.tan",
    "INT.rand",
    "INT.srand",
    "IO.accept",
    "IO.close",
    "IO.lock",
    "IO.log",
    "IO.mkstemp",
    "IO.open",
    "IO.remove",
    "IO.seek",
    "IO.seekEnd",
    "IO.shutdownWrite",
    "IO.system",
    "IO.tell",
    "IO.time",
    "IO.traceTerm",
    "IO.unlock",
    "LIST.fill",
    "LIST.getMInt",
    "LIST.push",
    "LIST.sizeMInt",
    "LIST.updateMInt",
    "MINT.MInt2bytes",
    "MINT.bytes2MInt",
    "MINT.literal",
    "MINT.pow",
    "MINT.round",
    "MINT.sext",
    "MINT.smax",
    "MINT.smin",
    "MINT.umax",
    "MINT.umin",
    "STRING.category",
    "STRING.directionality",
    "STRING.findChar",
    "STRING.float2string",
    "STRING.floatFormat",
    "STRING.replace",
    "STRING.replaceFirst",
    "STRING.rfindChar",
    "STRING.string2float",
    "STRING.uuid",
    "SUBSTITUTION.substMany",
];

/// Whether the backend's builtin takes a step at some application of `hook`: its namespace has an
/// evaluator and the evaluator implements `hook`. A hook in a namespace without an evaluator
/// (`HookNamespace::Other`) or without a namespace takes no step: the dispatch answers
/// `NotImplemented` for it.
///
/// Answering `true` for a hook that takes no step only costs precision (its equations are paired
/// with a written meaning, or reported for lacking one); answering `false` for a hook that takes
/// a step would leave its equations unchecked against it. So a hook of an evaluated namespace is
/// read as evaluated unless the dispatch is known to answer `NotImplemented` for its name.
#[must_use]
pub(crate) fn evaluates(hook: &str) -> bool {
    match HookName::parse(hook).map(HookName::kind) {
        None | Some(HookNamespace::Other) => false,
        Some(_) => !NOT_EVALUATED.contains(&hook),
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::{NOT_EVALUATED, evaluates};
    use crate::{
        builtin::{BuiltinResult, UnsupportedHookReason, evaluate_hook},
        term::{Sort, Term, Variable},
    };

    /// The hooks the builtin modules shipped with k-rust declare (`hook(NAMESPACE.name)`).
    fn declared_hooks() -> BTreeSet<String> {
        let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../k-rust/builtin");
        let mut hooks = BTreeSet::new();
        for entry in std::fs::read_dir(&directory).expect("the builtin directory") {
            let path = entry.expect("an entry").path();
            if path.extension().is_none_or(|extension| extension != "md") {
                continue;
            }
            let text = std::fs::read_to_string(&path).expect("a builtin module");
            for (index, _) in text.match_indices("hook(") {
                // `smt-hook(...)` names an SMT-LIB operator, not a builtin.
                if text[..index].ends_with('-') {
                    continue;
                }
                let rest = &text[index + "hook(".len()..];
                let Some(end) = rest.find(')') else { continue };
                let name = rest[..end].trim();
                if name.contains('.')
                    && name.chars().all(|character| {
                        character.is_ascii_alphanumeric() || "._".contains(character)
                    })
                {
                    // A sort's hook (`INT.Int`, `MINT.MInt`) names its domain, not a function.
                    let (_, operation) = name.split_once('.').expect("a namespace");
                    let sort = operation
                        .starts_with(|character: char| character.is_ascii_uppercase())
                        && !operation.contains(|character: char| character.is_ascii_digit());
                    if !sort {
                        hooks.insert(name.to_owned());
                    }
                }
            }
        }
        hooks
    }

    /// Whether the dispatch, outside an execution, answers anything but `NotImplemented` for an
    /// application of `hook` to fresh variables of some arity up to five: an implemented hook
    /// reads its arguments (answering `NotApplicable` or an arity error), an unimplemented one is
    /// refused by name whatever its arguments.
    fn dispatched(hook: &str) -> bool {
        (0..=5).any(|arity| {
            let arguments = (0..arity)
                .map(|index| {
                    Term::variable(Variable::new(format!("X{index}"), Sort::simple("SortInt")))
                })
                .collect::<Vec<_>>();
            let answer = std::panic::catch_unwind(|| evaluate_hook(hook, &arguments));
            !matches!(
                answer,
                Ok(Ok(Ok(BuiltinResult::Unsupported(
                    UnsupportedHookReason::NotImplemented
                ))))
            )
        })
    }

    /// The console hooks evaluated only inside an execution, which has the console: outside one
    /// the dispatch declines them as `NotImplemented` (`execution_context`).
    const IN_EXECUTION: [&str; 4] = ["IO.getc", "IO.read", "IO.putc", "IO.write"];

    #[test]
    fn every_hook_of_the_builtin_modules_agrees_with_the_dispatch() {
        let mut disagreements = Vec::new();
        let mut unevaluated = Vec::new();
        for hook in declared_hooks() {
            let expected = dispatched(&hook) || IN_EXECUTION.contains(&hook.as_str());
            if !expected {
                unevaluated.push(hook.clone());
            }
            if evaluates(&hook) != expected {
                disagreements.push(format!(
                    "{hook}: evaluates {}, the dispatch {expected}",
                    evaluates(&hook)
                ));
            }
        }
        for hook in NOT_EVALUATED {
            if dispatched(hook) {
                disagreements.push(format!("{hook} is listed unevaluated but is dispatched"));
            }
        }
        assert!(
            disagreements.is_empty(),
            "{}\nunevaluated: {unevaluated:?}",
            disagreements.join("\n")
        );
    }

    #[test]
    fn the_console_hooks_are_listed_as_dispatched_names() {
        for hook in IN_EXECUTION {
            assert!(evaluates(hook), "{hook}");
        }
    }
}
