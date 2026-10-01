//! This Java-compatible definition check traverses module sentences and terms linearly; callers supply derived catalogs and no dedicated counter is recorded.
//!
//! Variable-binding checks and position-aware KAST traversal.

use std::collections::BTreeSet;

use super::term_position::{Scope, TermPosition, positioned_children, scoped_children};
use super::{Sentence, is_anonymous};
use crate::definition::AttributeKey;
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::kast::{GeneratedLabel, InternalLabel, Sort, Term};

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

// Invariant: `bound` holds the variables bound at the positions already visited and
// `unsupported_existentials` counts the rejected `?X` occurrences among them, and each recursive
// call, directly or through `visit_free`, receives a strict subterm of `term`, so the size of
// `term` bounds the calls.
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

    let children = scoped_children(term, position);
    if children.iter().any(|(_, _, scope)| *scope == Scope::Lambda) {
        // A local function stands for the application of the function it is lowered to
        // (`term_position`): its pattern binds in its own body only, and the variables its body
        // reads from this scope are arguments of that application, at the construct's position.
        // Its own scope is still walked, which counts its existential variables.
        let mut lambda_bound = BTreeSet::new();
        for &(child, child_position, _) in children
            .iter()
            .filter(|(_, _, scope)| *scope == Scope::Lambda)
        {
            gather_variables(
                child,
                child_position,
                false,
                error_existential,
                &mut lambda_bound,
                unsupported_existentials,
            );
        }
        let binds = position.lhs || position.rhs && in_binder_lhs;
        for (child, child_position, scope) in children {
            match scope {
                Scope::Lambda if binds => {
                    visit_free(
                        child,
                        child_position,
                        false,
                        None,
                        &lambda_bound,
                        &mut |variable| {
                            bound.insert(variable.name.to_owned());
                        },
                    );
                }
                Scope::Lambda => {}
                Scope::Enclosing => gather_variables(
                    child,
                    child_position,
                    in_binder_lhs,
                    error_existential,
                    bound,
                    unsupported_existentials,
                ),
            }
        }
        return;
    }

    for (child, child_position, _) in children {
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
    compute_unbound(term, position, bound, &mut unbound);
    unbound.retain(|variable| !(listed.contains(variable) || is_alias && variable == "HOLE"));
    unbound
}

/// The free variables of `term` at `position` in a sentence whose binding positions bind
/// `bound`, less the fresh variables `!X`, whose values the sentence generates when it applies.
fn compute_unbound(
    term: &Term,
    position: TermPosition,
    bound: &BTreeSet<VariableName>,
    unbound: &mut BTreeSet<VariableName>,
) {
    visit_free(term, position, false, None, bound, &mut |variable| {
        if !variable.name.starts_with('!') {
            unbound.insert(variable.name.to_owned());
        }
    });
}

/// An occurrence of a variable that its scope does not bind: the term enclosing the scope must
/// supply its value.
#[derive(Clone, Copy, Debug)]
pub(crate) struct FreeVariable<'t> {
    pub(crate) name: &'t str,
    /// The sort the occurrence is annotated with.
    pub(crate) sort: Option<&'t Sort>,
    /// The sort text of the innermost semantic cast enclosing the occurrence.
    pub(crate) cast: Option<&'t str>,
}

/// The free variables of the local function whose equation is `equation`, in the order of their
/// occurrences (one entry per occurrence): the variables its body reads from the term enclosing
/// it, which its lowering passes as extra arguments.
///
/// `equation` is the rewrite `P => B` of the function's pattern and body (or, for a K-matching
/// predicate, its pattern alone), which sits at `BODY` exactly as a rule body does; this is the
/// walk the definition check applies to a local function inside a sentence (`term_position`).
/// Fresh variables `!X` are free: the generated equation cannot create a fresh value, so the
/// enclosing term does.
pub(crate) fn local_function_free_variables(equation: &Term) -> Vec<FreeVariable<'_>> {
    let mut bound = BTreeSet::new();
    gather_variables(
        equation,
        TermPosition::BODY,
        false,
        false,
        &mut bound,
        &mut 0,
    );
    let mut free = Vec::new();
    visit_free(
        equation,
        TermPosition::BODY,
        false,
        None,
        &bound,
        &mut |variable| {
            free.push(variable);
        },
    );
    free
}

/// Whether an occurrence of `name` at `position` is free in a scope whose binding positions bind
/// `bound`: it is built (RHS) outside the matching pattern of `:=K` or `:/=K` (`in_k_lhs`),
/// which binds its own variables, and it is an anonymous variable that is not also matched (each
/// anonymous occurrence is a distinct variable, so no other occurrence binds it) or a named
/// variable that no binding position binds. `THIS_CONFIGURATION`, which a rule binds to the
/// whole configuration, and the existential variables `?X`, which the sentence mentioning them
/// quantifies, are never free.
fn is_free(
    name: &str,
    position: TermPosition,
    in_k_lhs: bool,
    bound: &BTreeSet<VariableName>,
) -> bool {
    position.rhs
        && !in_k_lhs
        && name != "THIS_CONFIGURATION"
        && !name.starts_with('?')
        && if is_anonymous(name) {
            !position.lhs
        } else {
            !bound.contains(name)
        }
}

// Invariant: `report` has received, in walk order, every variable occurrence visited so far that is
// free at its position (`is_free`) in the scope enclosing it, a local function's own scope
// included, and each recursive call receives a strict subterm of `term`, so the size of `term`
// bounds the calls.
fn visit_free<'t>(
    term: &'t Term,
    position: TermPosition,
    in_k_lhs: bool,
    cast: Option<&'t str>,
    bound: &BTreeSet<VariableName>,
    report: &mut dyn FnMut(FreeVariable<'t>),
) {
    match term.unannotated() {
        Term::Variable { name, sort } => {
            if is_free(name, position, in_k_lhs, bound) {
                report(FreeVariable {
                    name,
                    sort: sort.as_ref(),
                    cast,
                });
            }
            return;
        }
        Term::Apply { label, arguments } => {
            if [InternalLabel::KEqualsK, InternalLabel::KNotEqualsK]
                .iter()
                .any(|internal| label.is(*internal))
                && arguments.len() >= 2
            {
                visit_free(&arguments[0], position, true, cast, bound, report);
                for argument in &arguments[1..] {
                    visit_free(argument, position, in_k_lhs, cast, bound, report);
                }
                return;
            }
            if let Some(GeneratedLabel::SemanticCast { sort_text }) = label.generated()
                && let Some(argument) = arguments.first()
            {
                visit_free(argument, position, in_k_lhs, Some(sort_text), bound, report);
                return;
            }
        }
        _ => {}
    }

    let children = scoped_children(term, position);
    let mut lambda_bound = BTreeSet::new();
    for &(child, child_position, _) in children
        .iter()
        .filter(|(_, _, scope)| *scope == Scope::Lambda)
    {
        gather_variables(
            child,
            child_position,
            false,
            false,
            &mut lambda_bound,
            &mut 0,
        );
    }
    for (child, child_position, scope) in children {
        match scope {
            Scope::Enclosing => visit_free(child, child_position, in_k_lhs, cast, bound, report),
            // A variable free in a local function's own scope is an argument of the application
            // the construct is lowered to, so it is read at the construct's position here.
            Scope::Lambda => visit_free(
                child,
                child_position,
                false,
                cast,
                &lambda_bound,
                &mut |variable| {
                    if is_free(variable.name, position, in_k_lhs, bound) {
                        report(variable);
                    }
                },
            ),
        }
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

    fn rule(left: Term, right: Term) -> Sentence {
        Sentence::Rule {
            body: Term::Rewrite {
                left: Box::new(left),
                right: Box::new(right),
            },
            requires: Term::Token {
                token: "true".into(),
                sort: Sort::new("Bool"),
            },
            ensures: Term::Token {
                token: "true".into(),
                sort: Sort::new("Bool"),
            },
            attributes: Default::default(),
        }
    }

    fn unbound_names(sentence: &Sentence) -> Vec<String> {
        check_rhs_variables(&[sentence], StructuralCheckOptions::default())
            .into_iter()
            .filter(|diagnostic| diagnostic.code == DiagnosticCode::UnboundVariable)
            .map(|diagnostic| diagnostic.message)
            .collect()
    }

    /// `#let P = E #in B` is `#fun(P => B)(E)`: `E` is evaluated outside the scope of `P`, so a
    /// variable that only `P` binds has no value in `E`.
    #[test]
    fn a_variable_bound_only_by_a_let_pattern_is_unbound_in_its_value() {
        let x = || Term::variable("X");
        let y = || Term::variable("Y");
        let unbound = rule(
            Term::apply("foo", vec![x()]),
            Term::apply("#let", vec![y(), Term::apply("bar", vec![y(), x()]), y()]),
        );
        assert_eq!(
            unbound_names(&unbound),
            vec![
                "Found variable Y on right hand side of rule, not bound on left hand side. Did you mean \"?Y\"?"
            ]
        );

        // Control: the same rule whose value reads only the rule's own variable.
        let bound = rule(
            Term::apply("foo", vec![x()]),
            Term::apply("#let", vec![y(), Term::apply("bar", vec![x(), x()]), y()]),
        );
        assert_eq!(unbound_names(&bound), Vec::<String>::new());
    }

    /// A local function's pattern binds in its own body only: a variable it binds is unbound in
    /// the rest of the rule.
    #[test]
    fn a_local_function_pattern_does_not_bind_outside_its_body() {
        let y = || Term::variable("Y");
        let local = Term::apply(
            "#fun2",
            vec![
                Term::Rewrite {
                    left: Box::new(y()),
                    right: Box::new(y()),
                },
                Term::apply("one", Vec::new()),
            ],
        );
        let sentence = rule(
            Term::apply("foo", Vec::new()),
            Term::apply("pair", vec![local, y()]),
        );
        assert_eq!(
            unbound_names(&sentence),
            vec![
                "Found variable Y on right hand side of rule, not bound on left hand side. Did you mean \"?Y\"?"
            ]
        );
    }

    /// The closure variables of a local function are the variables its body reads from the
    /// enclosing term: those its pattern binds are not, and a nested `#let`'s value is read in
    /// the outer function's scope, so a variable only the nested pattern binds is one of them.
    #[test]
    fn local_function_free_variables_follow_the_let_scopes() {
        let variable = Term::variable;
        let nested = Term::apply(
            "#let",
            vec![
                variable("Z"),
                Term::apply("bar", vec![variable("Z"), variable("C")]),
                Term::apply("baz", vec![variable("Z"), variable("P"), variable("!F")]),
            ],
        );
        let equation = Term::Rewrite {
            left: Box::new(variable("P")),
            right: Box::new(nested),
        };
        let names = local_function_free_variables(&equation)
            .into_iter()
            .map(|variable| variable.name)
            .collect::<Vec<_>>();
        assert_eq!(names, ["Z", "C", "!F"]);
    }
}
