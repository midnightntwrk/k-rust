//! This Java-compatible definition check traverses module sentences and terms linearly; callers supply derived catalogs and no dedicated counter is recorded.
//!
//! Variable-binding checks and position-aware KAST traversal.

use std::collections::BTreeSet;

use super::Sentence;
use super::term_position::{TermPosition, positioned_children};
use crate::definition::AttributeKey;
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::kast::{GeneratedLabel, InternalLabel, Term};

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum StructuralCheckBackend {
    Rust,
    #[default]
    Other,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct StructuralCheckOptions {
    /// Symbolic compilation permits existential variables.
    pub symbolic: bool,
    pub backend: StructuralCheckBackend,
    pub mode: CheckMode,
    /// Source prefixes exempt from the user-facing unused-symbol warning.
    pub builtin_source_prefixes: Vec<String>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub enum CheckMode {
    #[default]
    Definition,
    Proof {
        definition_module: String,
    },
}

/// Java `CheckRHSVariables`, including pattern/value validation.
pub fn check_rhs_variables(
    sentences: &[&Sentence],
    options: StructuralCheckOptions,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for sentence in sentences {
        match sentence {
            Sentence::Rule {
                body,
                requires,
                ensures,
                ..
            }
            | Sentence::Claim {
                body,
                requires,
                ensures,
                ..
            } => check_rule_variables(
                sentence,
                body,
                requires,
                ensures,
                &options,
                &mut diagnostics,
            ),
            Sentence::Context { body, requires, .. } => {
                check_context_variables(sentence, body, requires, false, &mut diagnostics)
            }
            Sentence::ContextAlias { body, requires, .. } => {
                check_context_variables(sentence, body, requires, true, &mut diagnostics)
            }
            _ => {}
        }
    }
    diagnostics
}

type VariableName = String;

/// A term of a rule-like sentence whose right-hand-side variables are checked.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum CheckedRoot {
    Body,
    Requires,
    Ensures,
}

#[cfg(any(debug_assertions, feature = "kompile-invariant-checks"))]
impl CheckedRoot {
    pub(crate) const fn as_str(self) -> &'static str {
        match self {
            Self::Body => "body",
            Self::Requires => "requires",
            Self::Ensures => "ensures",
        }
    }
}

/// How the right-hand-side variables of one rule-like sentence are bound.
///
/// A rewrite relates instances of its left-hand side to instances of its right-hand side, so a
/// right-hand-side variable has a value when the sentence applies only if a binding position
/// binds it or an exemption quantifies it: `?X` and `!X`, `THIS_CONFIGURATION`, `HOLE` of a
/// context alias, and the names a rule or claim lists in `unboundVariables`.
#[derive(Debug)]
pub(crate) struct RightHandSideBinding {
    /// For each checked root, in report order, its right-hand-side variables that no binding
    /// position binds and no exemption covers, in name order.
    pub(crate) unbound: Vec<(CheckedRoot, BTreeSet<VariableName>)>,
    /// The names the sentence's `unboundVariables` attribute exempts; a context exempts none.
    #[cfg(any(debug_assertions, feature = "kompile-invariant-checks"))]
    pub(crate) listed: BTreeSet<String>,
    /// Occurrences of `?X` in a sentence whose backend does not support existential variables.
    unsupported_existentials: usize,
}

/// The right-hand-side binding of a rule, claim, context or context alias; `None` for any other
/// sentence.
#[cfg(any(debug_assertions, feature = "kompile-invariant-checks"))]
pub(crate) fn right_hand_side_binding(
    sentence: &Sentence,
    options: &StructuralCheckOptions,
) -> Option<RightHandSideBinding> {
    match sentence {
        Sentence::Rule {
            body,
            requires,
            ensures,
            ..
        }
        | Sentence::Claim {
            body,
            requires,
            ensures,
            ..
        } => Some(rule_binding(sentence, body, requires, ensures, options)),
        Sentence::Context { body, requires, .. } => Some(context_binding(body, requires, false)),
        Sentence::ContextAlias { body, requires, .. } => {
            Some(context_binding(body, requires, true))
        }
        _ => None,
    }
}

fn check_rule_variables(
    sentence: &Sentence,
    body: &Term,
    requires: &Term,
    ensures: &Term,
    options: &StructuralCheckOptions,
    diagnostics: &mut Vec<Diagnostic>,
) {
    check_pattern_value(body, TermPosition::BODY, sentence, diagnostics);
    check_pattern_value(requires, TermPosition::CONDITION, sentence, diagnostics);
    check_pattern_value(ensures, TermPosition::CONDITION, sentence, diagnostics);
    report_binding(
        rule_binding(sentence, body, requires, ensures, options),
        sentence,
        diagnostics,
    );
}

fn check_context_variables(
    sentence: &Sentence,
    body: &Term,
    requires: &Term,
    is_alias: bool,
    diagnostics: &mut Vec<Diagnostic>,
) {
    report_binding(
        context_binding(body, requires, is_alias),
        sentence,
        diagnostics,
    );
}

fn rule_binding(
    sentence: &Sentence,
    body: &Term,
    requires: &Term,
    ensures: &Term,
    options: &StructuralCheckOptions,
) -> RightHandSideBinding {
    let is_claim = matches!(sentence, Sentence::Claim { .. });
    let error_existential = !options.symbolic
        && sentence.attributes().string(AttributeKey::Label) != Some("STDIN-STREAM.stdinUnblock");
    let requires_is_lhs = is_claim || options.backend == StructuralCheckBackend::Rust;
    let requires_position = if requires_is_lhs {
        TermPosition::BODY
    } else {
        TermPosition::CONDITION
    };
    let mut bound = BTreeSet::new();
    let mut unsupported_existentials = 0;
    gather_variables(
        body,
        TermPosition::BODY,
        false,
        error_existential,
        &mut bound,
        &mut unsupported_existentials,
    );
    gather_variables(
        ensures,
        TermPosition::CONDITION,
        false,
        error_existential,
        &mut bound,
        &mut unsupported_existentials,
    );
    gather_variables(
        requires,
        requires_position,
        false,
        error_existential,
        &mut bound,
        &mut unsupported_existentials,
    );

    let listed = unbound_variable_names(sentence);
    let unbound = [
        (CheckedRoot::Body, body, TermPosition::BODY),
        (CheckedRoot::Requires, requires, requires_position),
        (CheckedRoot::Ensures, ensures, TermPosition::CONDITION),
    ]
    .into_iter()
    .map(|(root, term, position)| {
        (
            root,
            unbound_at_root(term, position, false, &bound, &listed),
        )
    })
    .collect();
    RightHandSideBinding {
        unbound,
        #[cfg(any(debug_assertions, feature = "kompile-invariant-checks"))]
        listed,
        unsupported_existentials,
    }
}

fn context_binding(body: &Term, requires: &Term, is_alias: bool) -> RightHandSideBinding {
    let mut bound = BTreeSet::new();
    let mut unsupported_existentials = 0;
    gather_variables(
        body,
        TermPosition::BODY,
        false,
        false,
        &mut bound,
        &mut unsupported_existentials,
    );
    gather_variables(
        requires,
        TermPosition::CONDITION,
        false,
        false,
        &mut bound,
        &mut unsupported_existentials,
    );
    let listed = BTreeSet::new();
    let unbound = [
        (CheckedRoot::Body, body, TermPosition::BODY),
        (CheckedRoot::Requires, requires, TermPosition::CONDITION),
    ]
    .into_iter()
    .map(|(root, term, position)| {
        (
            root,
            unbound_at_root(term, position, is_alias, &bound, &listed),
        )
    })
    .collect();
    RightHandSideBinding {
        unbound,
        #[cfg(any(debug_assertions, feature = "kompile-invariant-checks"))]
        listed,
        unsupported_existentials,
    }
}

/// Report the unsupported existential variables, then the unbound variables of each root in order.
fn report_binding(
    binding: RightHandSideBinding,
    sentence: &Sentence,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for _ in 0..binding.unsupported_existentials {
        diagnostics.push(Diagnostic::error(
            DiagnosticCode::UnsupportedExistentialVariable,
            "Found existential variable not supported by concrete backend.",
            sentence,
        ));
    }
    for (_, unbound) in binding.unbound {
        for variable in unbound {
            diagnostics.push(Diagnostic::error(
                DiagnosticCode::UnboundVariable,
                format!(
                    "Found variable {} on right hand side of rule, not bound on left hand side. Did you mean \"?{}\"?",
                    variable, variable
                ),
                sentence,
            ));
        }
    }
}

// Invariant: `position` is the `TermPosition` of `term` in the rule, and each recursive call receives a child of `term` from `positioned_children`, so the size of `term` bounds the calls.
fn check_pattern_value(
    term: &Term,
    position: TermPosition,
    sentence: &Sentence,
    diagnostics: &mut Vec<Diagnostic>,
) {
    if let Term::Apply { label, .. } = term.unannotated()
        && [InternalLabel::Fun2, InternalLabel::Fun3, InternalLabel::Let]
            .iter()
            .any(|internal| label.is(*internal))
        && position.lhs
    {
        diagnostics.push(Diagnostic::error(
            DiagnosticCode::InvalidFunctionPattern,
            "Found #fun expression in a pattern location (LHS and outside of rewrite).",
            sentence,
        ));
    }
    for (child, child_position) in positioned_children(term, position) {
        check_pattern_value(child, child_position, sentence, diagnostics);
    }
}

// Invariant: `bound` holds the variables bound at the positions already visited and `unsupported_existentials` counts the rejected `?X` occurrences among them, and each recursive call receives a strict subterm of `term`, so the size of `term` bounds the calls.
fn gather_variables(
    term: &Term,
    position: TermPosition,
    in_binder_lhs: bool,
    error_existential: bool,
    bound: &mut BTreeSet<VariableName>,
    unsupported_existentials: &mut usize,
) {
    if let Term::Variable { name, .. } = term.unannotated() {
        if position.lhs || position.rhs && in_binder_lhs {
            bound.insert(name.to_owned());
        }
        if error_existential && name.starts_with('?') {
            *unsupported_existentials += 1;
        }
        return;
    }

    if let Term::Apply { label, arguments } = term.unannotated()
        && matches!(label.generated(), Some(GeneratedLabel::SemanticCast { .. }))
        && let Some(argument) = arguments.first()
    {
        gather_variables(
            argument,
            position,
            in_binder_lhs,
            error_existential,
            bound,
            unsupported_existentials,
        );
        return;
    }

    if let Term::Apply { label, arguments } = term.unannotated()
        && [InternalLabel::Exists, InternalLabel::Forall]
            .iter()
            .any(|internal| label.is(*internal))
        && arguments.len() >= 2
    {
        gather_variables(
            &arguments[0],
            position,
            true,
            error_existential,
            bound,
            unsupported_existentials,
        );
        gather_variables(
            &arguments[1],
            position,
            in_binder_lhs,
            error_existential,
            bound,
            unsupported_existentials,
        );
        for argument in &arguments[2..] {
            gather_variables(
                argument,
                position,
                in_binder_lhs,
                error_existential,
                bound,
                unsupported_existentials,
            );
        }
        return;
    }

    for (child, child_position) in positioned_children(term, position) {
        gather_variables(
            child,
            child_position,
            in_binder_lhs,
            error_existential,
            bound,
            unsupported_existentials,
        );
    }
}

/// The right-hand-side variables of `term` at `position` that `bound` does not bind and no
/// exemption covers.
fn unbound_at_root(
    term: &Term,
    position: TermPosition,
    is_alias: bool,
    bound: &BTreeSet<VariableName>,
    listed: &BTreeSet<String>,
) -> BTreeSet<VariableName> {
    let mut unbound = BTreeSet::new();
    compute_unbound(term, position, false, bound, &mut unbound);
    unbound.retain(|variable| !(listed.contains(variable) || is_alias && variable == "HOLE"));
    unbound
}

// Invariant: `unbound` holds the unbound right-hand-side variables of the subterms already visited, and each recursive call receives a strict subterm of `term`, so the size of `term` bounds the calls.
fn compute_unbound(
    term: &Term,
    position: TermPosition,
    in_k_lhs: bool,
    bound: &BTreeSet<VariableName>,
    unbound: &mut BTreeSet<VariableName>,
) {
    if let Term::Variable { name, .. } = term.unannotated() {
        if position.rhs
            && !in_k_lhs
            && name != "THIS_CONFIGURATION"
            && ((name == "_" && !position.lhs)
                || (name != "_"
                    && !name.starts_with('?')
                    && !name.starts_with('!')
                    && !bound.contains(name)))
        {
            unbound.insert(name.to_owned());
        }
        return;
    }

    if let Term::Apply { label, arguments } = term.unannotated() {
        if [InternalLabel::KEqualsK, InternalLabel::KNotEqualsK]
            .iter()
            .any(|internal| label.is(*internal))
            && arguments.len() >= 2
        {
            compute_unbound(&arguments[0], position, true, bound, unbound);
            compute_unbound(&arguments[1], position, in_k_lhs, bound, unbound);
            for argument in &arguments[2..] {
                compute_unbound(argument, position, in_k_lhs, bound, unbound);
            }
            return;
        }
        if matches!(label.generated(), Some(GeneratedLabel::SemanticCast { .. }))
            && let Some(argument) = arguments.first()
        {
            compute_unbound(argument, position, in_k_lhs, bound, unbound);
            return;
        }
    }

    for (child, child_position) in positioned_children(term, position) {
        compute_unbound(child, child_position, in_k_lhs, bound, unbound);
    }
}

fn unbound_variable_names(sentence: &Sentence) -> BTreeSet<String> {
    sentence
        .attributes()
        .string(AttributeKey::UnboundVariables)
        .into_iter()
        .flat_map(|names| names.split(','))
        .map(str::trim)
        .map(str::to_owned)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn symbolic_requires_gather_anonymous_lhs_binders() {
        let mut bound = BTreeSet::new();
        gather_variables(
            &Term::variable("_"),
            TermPosition::BODY,
            false,
            false,
            &mut bound,
            &mut 0,
        );
        assert_eq!(bound, BTreeSet::from(["_".to_owned()]));
    }
}
