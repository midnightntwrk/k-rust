//! Variable-binding checks and position-aware KAST traversal.

use std::collections::BTreeSet;

use super::Sentence;
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::kast::{Label, Sort, Term};

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum StructuralCheckBackend {
    Haskell,
    #[default]
    Other,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct StructuralCheckOptions {
    /// Symbolic compilation permits existential variables.
    pub symbolic: bool,
    pub backend: StructuralCheckBackend,
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
                matches!(sentence, Sentence::Claim { .. }),
                options,
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

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct VariableKey {
    name: String,
    sort: Option<Sort>,
}

impl VariableKey {
    fn new(name: &str, sort: Option<&Sort>) -> Self {
        Self {
            name: name.to_owned(),
            sort: sort.cloned(),
        }
    }
}

#[derive(Clone, Copy)]
struct TermPosition {
    lhs: bool,
    rhs: bool,
}

impl TermPosition {
    const BODY: Self = Self {
        lhs: true,
        rhs: true,
    };
    const CONDITION: Self = Self {
        lhs: false,
        rhs: true,
    };
    const LHS: Self = Self {
        lhs: true,
        rhs: false,
    };
    const RHS: Self = Self {
        lhs: false,
        rhs: true,
    };
}

fn check_rule_variables(
    sentence: &Sentence,
    body: &Term,
    requires: &Term,
    ensures: &Term,
    is_claim: bool,
    options: StructuralCheckOptions,
    diagnostics: &mut Vec<Diagnostic>,
) {
    check_pattern_value(body, TermPosition::BODY, sentence, diagnostics);
    check_pattern_value(requires, TermPosition::CONDITION, sentence, diagnostics);
    check_pattern_value(ensures, TermPosition::CONDITION, sentence, diagnostics);

    let error_existential = !options.symbolic
        && sentence.attributes().get_str("label") != Some("STDIN-STREAM.stdinUnblock");
    let requires_is_lhs = is_claim || options.backend == StructuralCheckBackend::Haskell;
    let requires_position = if requires_is_lhs {
        TermPosition::BODY
    } else {
        TermPosition::CONDITION
    };
    let mut bound = BTreeSet::new();
    gather_variables(
        body,
        TermPosition::BODY,
        false,
        error_existential,
        &mut bound,
        sentence,
        diagnostics,
    );
    gather_variables(
        ensures,
        TermPosition::CONDITION,
        false,
        error_existential,
        &mut bound,
        sentence,
        diagnostics,
    );
    gather_variables(
        requires,
        requires_position,
        false,
        error_existential,
        &mut bound,
        sentence,
        diagnostics,
    );

    let allowed = unbound_variable_names(sentence);
    report_unbound(
        body,
        TermPosition::BODY,
        false,
        &bound,
        &allowed,
        sentence,
        diagnostics,
    );
    report_unbound(
        requires,
        requires_position,
        false,
        &bound,
        &allowed,
        sentence,
        diagnostics,
    );
    report_unbound(
        ensures,
        TermPosition::CONDITION,
        false,
        &bound,
        &allowed,
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
    let mut bound = BTreeSet::new();
    gather_variables(
        body,
        TermPosition::BODY,
        false,
        false,
        &mut bound,
        sentence,
        diagnostics,
    );
    gather_variables(
        requires,
        TermPosition::CONDITION,
        false,
        false,
        &mut bound,
        sentence,
        diagnostics,
    );
    report_unbound(
        body,
        TermPosition::BODY,
        is_alias,
        &bound,
        &BTreeSet::new(),
        sentence,
        diagnostics,
    );
    report_unbound(
        requires,
        TermPosition::CONDITION,
        is_alias,
        &bound,
        &BTreeSet::new(),
        sentence,
        diagnostics,
    );
}

fn check_pattern_value(
    term: &Term,
    position: TermPosition,
    sentence: &Sentence,
    diagnostics: &mut Vec<Diagnostic>,
) {
    if let Term::Apply { label, .. } = term
        && matches!(label.name.as_str(), "#fun2" | "#fun3" | "#let")
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

#[allow(clippy::too_many_arguments)]
fn gather_variables(
    term: &Term,
    position: TermPosition,
    in_binder_lhs: bool,
    error_existential: bool,
    bound: &mut BTreeSet<VariableKey>,
    sentence: &Sentence,
    diagnostics: &mut Vec<Diagnostic>,
) {
    if let Term::Variable { name, sort } = term {
        if position.lhs && !is_anonymous(name) || position.rhs && in_binder_lhs {
            bound.insert(VariableKey::new(name, sort.as_ref()));
        }
        if error_existential && name.starts_with('?') {
            diagnostics.push(Diagnostic::error(
                DiagnosticCode::UnsupportedExistentialVariable,
                "Found existential variable not supported by concrete backend.",
                sentence,
            ));
        }
        return;
    }

    if let Term::Apply { label, arguments } = term
        && matches!(label.name.as_str(), "#Exists" | "#Forall")
        && arguments.len() >= 2
    {
        gather_variables(
            &arguments[0],
            position,
            true,
            error_existential,
            bound,
            sentence,
            diagnostics,
        );
        gather_variables(
            &arguments[1],
            position,
            in_binder_lhs,
            error_existential,
            bound,
            sentence,
            diagnostics,
        );
        for argument in &arguments[2..] {
            gather_variables(
                argument,
                position,
                in_binder_lhs,
                error_existential,
                bound,
                sentence,
                diagnostics,
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
            sentence,
            diagnostics,
        );
    }
}

fn report_unbound(
    term: &Term,
    position: TermPosition,
    is_alias: bool,
    bound: &BTreeSet<VariableKey>,
    allowed: &BTreeSet<String>,
    sentence: &Sentence,
    diagnostics: &mut Vec<Diagnostic>,
) {
    let mut unbound = BTreeSet::new();
    compute_unbound(term, position, false, None, bound, &mut unbound);
    for variable in unbound {
        if allowed.contains(&variable.name) || is_alias && variable.name == "HOLE" {
            continue;
        }
        diagnostics.push(Diagnostic::error(
            DiagnosticCode::UnboundVariable,
            format!(
                "Found variable {} on right hand side of rule, not bound on left hand side. Did you mean \"?{}\"?",
                variable.name, variable.name
            ),
            sentence,
        ));
    }
}

fn compute_unbound(
    term: &Term,
    position: TermPosition,
    in_k_lhs: bool,
    context_sort: Option<&Sort>,
    bound: &BTreeSet<VariableKey>,
    unbound: &mut BTreeSet<VariableKey>,
) {
    if let Term::Variable { name, sort } = term {
        let variable = VariableKey::new(name, context_sort.or(sort.as_ref()));
        if position.rhs
            && !in_k_lhs
            && name != "THIS_CONFIGURATION"
            && ((name == "_" && !position.lhs)
                || (name != "_"
                    && !name.starts_with('?')
                    && !name.starts_with('!')
                    && !bound.contains(&variable)))
        {
            unbound.insert(variable);
        }
        return;
    }

    if let Term::Apply { label, arguments } = term {
        if matches!(label.name.as_str(), "_:=K_" | "_:/=K_") && arguments.len() >= 2 {
            compute_unbound(&arguments[0], position, true, context_sort, bound, unbound);
            compute_unbound(
                &arguments[1],
                position,
                in_k_lhs,
                context_sort,
                bound,
                unbound,
            );
            for argument in &arguments[2..] {
                compute_unbound(argument, position, in_k_lhs, context_sort, bound, unbound);
            }
            return;
        }
        if let Some(sort) = semantic_cast_sort(label)
            && let Some(argument) = arguments.first()
        {
            compute_unbound(argument, position, in_k_lhs, Some(&sort), bound, unbound);
            return;
        }
    }

    for (child, child_position) in positioned_children(term, position) {
        compute_unbound(
            child,
            child_position,
            in_k_lhs,
            context_sort,
            bound,
            unbound,
        );
    }
}

fn semantic_cast_sort(label: &Label) -> Option<Sort> {
    let name = label.name.strip_prefix("#SemanticCastTo")?;
    (!name.is_empty()).then(|| Sort::new(name))
}

fn unbound_variable_names(sentence: &Sentence) -> BTreeSet<String> {
    sentence
        .attributes()
        .get_str("unboundVariables")
        .into_iter()
        .flat_map(|names| names.split(','))
        .map(str::trim)
        .map(str::to_owned)
        .collect()
}

fn is_anonymous(name: &str) -> bool {
    matches!(name, "_" | "?_" | "!_" | "@_")
}

fn positioned_children(term: &Term, position: TermPosition) -> Vec<(&Term, TermPosition)> {
    match term {
        Term::Rewrite { left, right } => vec![
            (
                left,
                TermPosition {
                    lhs: position.lhs,
                    rhs: false,
                },
            ),
            (right, TermPosition::RHS),
        ],
        Term::As { pattern, alias } => vec![(pattern, position), (alias, position)],
        Term::Sequence(items) => items.iter().map(|item| (item, position)).collect(),
        Term::Apply { label, arguments } if label.name == "#fun2" && arguments.len() >= 2 => {
            let mut children = vec![
                (&arguments[0], TermPosition::BODY),
                (&arguments[1], position),
            ];
            children.extend(arguments[2..].iter().map(|argument| (argument, position)));
            children
        }
        Term::Apply { label, arguments }
            if matches!(label.name.as_str(), "#fun3" | "#let") && arguments.len() >= 3 =>
        {
            let mut children = vec![
                (&arguments[0], TermPosition::LHS),
                (&arguments[1], TermPosition::RHS),
                (&arguments[2], position),
            ];
            children.extend(arguments[3..].iter().map(|argument| (argument, position)));
            children
        }
        Term::Apply { arguments, .. } => arguments
            .iter()
            .map(|argument| (argument, position))
            .collect(),
        Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => Vec::new(),
    }
}
