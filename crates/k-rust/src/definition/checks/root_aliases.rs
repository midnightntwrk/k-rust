//! This definition check reads each rule's head once and walks its right-hand side and clauses once; callers supply the production catalog and no dedicated counter is recorded.
//!
//! Where the root alias of an equation may occur.
//!
//! An alias `P #as V` denotes the terms `P` denotes and names the matched term `V`. At the root
//! of a rule's left-hand side, `f(X) #as V`, the matched term is the very term the rule applies
//! to, its redex. A rewrite rule relates that term, inside the configuration before the step,
//! to the configuration after it, so `V => g(V)` describes a transition and is meaningful.
//!
//! A function, `anywhere`, `simplification`, macro or alias rule ([`EquationKind`]) instead
//! states an equation, `f(X) = R` under its `requires` clause, with `V` standing for `f(X)`
//! itself: the rule states `f(X) = R[f(X)/V]`. When `V` occurs in `R`, `requires` or `ensures`,
//! that equation mentions its own left-hand side:
//!
//! - when `R` is `V`, it is `f(X) = f(X)`, a tautology that defines nothing;
//! - otherwise evaluating `f(X)` by the equation produces, or must first decide a condition on,
//!   another instance of `f(X)`, which the same equation applies to again: arguments-first
//!   evaluation never terminates, and a macro expands forever;
//! - under a strict context the equation has no model at all: `f(X) = 1 +Int f(X)` holds of no
//!   integer, so the definition is inconsistent.
//!
//! None of these is a definition anyone intends, and refusing them loses nothing: an author who
//! means the matched term writes `f(X)` in place of `V`. A root alias that occurs nowhere else
//! (an anonymous `_`, or a name such as `_V` left unused) states nothing and is accepted.

use crate::definition::{ProductionCatalog, RuleHead, Sentence};
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::kast::binding::free_variables;
use crate::kast::{GeneratedLabel, Term};

use super::{EquationKind, is_anonymous};

/// Refuse each rule of an [`EquationKind`] whose root alias occurs in its right-hand side,
/// `requires` clause or `ensures` clause (module docs).
pub(super) fn check_equation_root_aliases(
    sentences: &[&Sentence],
    productions: &ProductionCatalog<'_>,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for sentence in sentences {
        let Sentence::Rule {
            body,
            requires,
            ensures,
            ..
        } = sentence
        else {
            continue;
        };
        let head = RuleHead::of(body);
        let Some(right) = head.right else {
            continue;
        };
        let aliases = head
            .root_alias_variables()
            .into_iter()
            .filter(|name| !is_anonymous(name))
            .collect::<Vec<_>>();
        if aliases.is_empty() {
            continue;
        }
        let Some(kind) = EquationKind::of(sentence, productions) else {
            continue;
        };
        let places = [
            ("right-hand side", free_variables(right)),
            ("requires clause", free_variables(requires)),
            ("ensures clause", free_variables(ensures)),
        ];
        for alias in aliases {
            let used = places
                .iter()
                .filter(|(_, variables)| variables.contains(alias))
                .map(|(place, _)| *place)
                .collect::<Vec<_>>();
            if used.is_empty() {
                continue;
            }
            let root = without_semantic_casts(head.root);
            diagnostics.push(Diagnostic::error(
                DiagnosticCode::InvalidAsPattern,
                format!(
                    "The root alias {alias} of {kind} occurs in its {used}. {kind_capitalized} \
                     states an equation, and its root alias names the term the equation \
                     rewrites, so the rule states that term equal to a result, or under a \
                     condition, that contains the same term again: a tautology when the \
                     right-hand side is {alias} alone, and otherwise an equation that applies \
                     to its own result without end, or has no model. Write the head term \
                     `{root}` in place of {alias}.",
                    kind = kind.rule(),
                    kind_capitalized = capitalized(kind.rule()),
                    used = used.join(" and "),
                ),
                sentence,
            ));
        }
    }
    diagnostics
}

/// `term` with each semantic cast `#SemanticCastToS(T)` replaced by `T` (`f(X:Int)` becomes
/// `f(X)`): the head term to write in place of the alias, whose variables the left-hand side
/// already binds at the sorts its casts state.
fn without_semantic_casts(term: &Term) -> Term {
    let mut term = term.clone();
    let mut pending = vec![&mut term];
    while let Some(mut node) = pending.pop() {
        while let Term::Annotated { term: inner, .. } = node {
            node = inner;
        }
        if let Term::Apply { label, arguments } = node
            && matches!(label.generated(), Some(GeneratedLabel::SemanticCast { .. }))
            && arguments.len() == 1
        {
            let operand = arguments.pop().expect("a cast has one operand");
            *node = operand;
            pending.push(node);
            continue;
        }
        pending.extend(node.children_mut());
    }
    term
}

fn capitalized(text: &str) -> String {
    let mut characters = text.chars();
    characters
        .next()
        .map(|first| first.to_uppercase().chain(characters).collect())
        .unwrap_or_default()
}
