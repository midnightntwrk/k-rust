//! The local functions of a typed sentence, split into the scopes compilation lowers them to.
//!
//! Compilation lowers every local function (`#fun2`, `#fun3`, `#let`, `:=K`, `:/=K`) before it
//! resolves semantic casts and injects sorts (`kompile::passes::resolve_fun`): the construct
//! becomes an application `lambda(E, C1..Cn)` of a generated function in the enclosing term,
//! where `E` is the value it is applied to and `C1..Cn` its closure variables, and its pattern
//! `P` and body `B` become the generated equation `lambda(P, C1..Cn) => B`, a rule of its own.
//! The lambda's sorts are computed with the injector of the module that declares the sentence
//! ([`lambda_sorts`]).
//!
//! [`lower`] splits a loaded sentence the same way. Each local function is replaced, in the term
//! that encloses it, by a stand-in application of a label of its own to `E` and `C1..Cn`, and its
//! equation becomes a sentence of its own, `stand-in(P, C1..Cn) => B`. Each scope's semantic
//! casts are resolved apart, as compilation resolves them. Each stand-in application is then
//! replaced by a variable of the lambda's result sort, which is the sort compilation's lambda
//! application has, so the injector types the enclosing term as compilation does without
//! descending into the equation; the value and the equation are typed from [`LoweredLocal`].
//!
//! Cost: one walk of the sentence and of each scope it creates (N nodes in all), one sort
//! computation of each local function's pattern, value and body, and one semantic-cast
//! resolution per scope; O(N) besides those.

#![deny(clippy::wildcard_enum_match_arm)]

use std::collections::BTreeMap;

use crate::definition::{PartialOrder, Sentence};
use crate::kast::{Label, Sort, Term, TermParts};
use crate::kompile::passes::{
    LambdaSorts, LocalFunction, ResolveSemanticCastsError, closure_variables, lambda_sorts,
    resolve_semantic_casts_in_sentence, semantic_cast_variable_sorts,
};
use crate::names::BuiltinSort;

use super::super::{SortInjectionError, SortInjector};

/// The prefix of the stand-in labels and variables, which no source term can spell.
const STAND_IN: &str = "#localFunction";

/// One local function of a typed sentence, as compilation lowers it.
pub(super) struct LoweredLocal {
    pub(super) local: LocalFunction,
    /// The lambda's sorts, computed in the module that declares the sentence.
    pub(super) sorts: LambdaSorts,
    /// The value the lambda is applied to, resolved in the enclosing scope.
    pub(super) argument: Term,
    /// The pattern of the generated equation, resolved in the equation's scope.
    pub(super) pattern: Term,
    /// The body of the generated equation, resolved in its scope; `None` for a match.
    pub(super) body: Option<Term>,
}

/// The local functions of a sentence, by the name of their stand-in variable.
pub(super) type Locals = BTreeMap<String, LoweredLocal>;

/// A sentence split into compilation's scopes.
pub(super) struct Lowered {
    /// The enclosing sentence, resolved, with a stand-in variable for each outermost local
    /// function.
    pub(super) sentence: Sentence,
    pub(super) locals: Locals,
    /// The variable sorts of the semantic casts: the enclosing sentence's, then those of each
    /// equation for names the enclosing sentence does not cast.
    pub(super) variables: BTreeMap<String, Sort>,
}

pub(super) enum LoweringError {
    Sort(SortInjectionError),
    Casts(ResolveSemanticCastsError),
}

/// Whether any of `terms` holds a local function.
pub(super) fn has_local_function(terms: [&Term; 3]) -> bool {
    let mut found = false;
    for term in terms {
        term.visit_preorder(&mut |term| {
            if let Term::Apply { label, arguments } = term.unannotated()
                && matches!(LocalFunction::of(label, arguments.len()), Some(Ok(_)))
            {
                found = true;
            }
        });
    }
    found
}

/// Split `sentence`, a rule or claim, into compilation's scopes, computing each lambda's sorts
/// with `injector` (the declaring module's) and resolving each scope's semantic casts in the
/// order `declared`.
pub(super) fn lower(
    sentence: &Sentence,
    injector: &SortInjector<'_, '_>,
    declared: &PartialOrder<Sort>,
) -> Result<Lowered, LoweringError> {
    let mut lowering = Lowering {
        injector,
        next: 0,
        pending: BTreeMap::new(),
        equations: Vec::new(),
        error: None,
    };
    let enclosing = match sentence {
        Sentence::Rule {
            body,
            requires,
            ensures,
            attributes,
        } => Sentence::Rule {
            body: lowering.term(body),
            requires: lowering.term(requires),
            ensures: lowering.term(ensures),
            attributes: attributes.clone(),
        },
        Sentence::Claim {
            body,
            requires,
            ensures,
            attributes,
        } => Sentence::Claim {
            body: lowering.term(body),
            requires: lowering.term(requires),
            ensures: lowering.term(ensures),
            attributes: attributes.clone(),
        },
        Sentence::SyntaxSort { .. }
        | Sentence::SortSynonym { .. }
        | Sentence::SyntaxLexical { .. }
        | Sentence::Production { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::ContextAlias { .. }
        | Sentence::Context { .. }
        | Sentence::Configuration { .. }
        | Sentence::Bubble { .. } => unreachable!("the typer types rules and claims"),
    };
    if let Some(error) = lowering.error {
        return Err(LoweringError::Sort(error));
    }
    let Lowering {
        pending, equations, ..
    } = lowering;

    let mut variables =
        semantic_cast_variable_sorts(&enclosing, declared).map_err(LoweringError::Casts)?;
    let enclosing =
        resolve_semantic_casts_in_sentence(declared, enclosing).map_err(LoweringError::Casts)?;
    let mut resolved_equations = Vec::with_capacity(equations.len());
    // Invariant: `resolved_equations` holds the resolved body of every equation before `body`,
    // and `variables` their cast sorts for names not cast before; each iteration consumes one.
    for (name, body) in equations {
        let equation = Sentence::Rule {
            body,
            requires: truth(),
            ensures: truth(),
            attributes: sentence.attributes().clone(),
        };
        for (variable, sort) in
            semantic_cast_variable_sorts(&equation, declared).map_err(LoweringError::Casts)?
        {
            variables.entry(variable).or_insert(sort);
        }
        let Sentence::Rule { body, .. } =
            resolve_semantic_casts_in_sentence(declared, equation).map_err(LoweringError::Casts)?
        else {
            unreachable!("resolution keeps the sentence kind")
        };
        resolved_equations.push((name, body));
    }

    let mut arguments = BTreeMap::new();
    let enclosing = match enclosing {
        Sentence::Rule {
            body,
            requires,
            ensures,
            attributes,
        } => Sentence::Rule {
            body: stand_in_variables(body, &pending, &mut arguments),
            requires: stand_in_variables(requires, &pending, &mut arguments),
            ensures: stand_in_variables(ensures, &pending, &mut arguments),
            attributes,
        },
        Sentence::Claim {
            body,
            requires,
            ensures,
            attributes,
        } => Sentence::Claim {
            body: stand_in_variables(body, &pending, &mut arguments),
            requires: stand_in_variables(requires, &pending, &mut arguments),
            ensures: stand_in_variables(ensures, &pending, &mut arguments),
            attributes,
        },
        Sentence::SyntaxSort { .. }
        | Sentence::SortSynonym { .. }
        | Sentence::SyntaxLexical { .. }
        | Sentence::Production { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::ContextAlias { .. }
        | Sentence::Context { .. }
        | Sentence::Configuration { .. }
        | Sentence::Bubble { .. } => unreachable!("resolution keeps the sentence kind"),
    };
    let mut parts = BTreeMap::new();
    // Invariant: `parts` holds the pattern and body of every equation before `body`, with their
    // stand-ins replaced; each iteration consumes one equation.
    for (name, body) in resolved_equations {
        #[expect(
            clippy::wildcard_enum_match_arm,
            reason = "Term is syntax; an equation is a rewrite or a stand-in application"
        )]
        let (left, right) = match body.unannotated() {
            Term::Rewrite { left, right } => ((**left).clone(), Some((**right).clone())),
            _ => (body.clone(), None),
        };
        #[expect(
            clippy::wildcard_enum_match_arm,
            reason = "Term is syntax; the left side is the stand-in application"
        )]
        let pattern = match left.unannotated() {
            Term::Apply { arguments, .. } if !arguments.is_empty() => arguments[0].clone(),
            _ => unreachable!("an equation's left side applies its stand-in to the pattern"),
        };
        let pattern = stand_in_variables(pattern, &pending, &mut arguments);
        let body = right.map(|right| stand_in_variables(right, &pending, &mut arguments));
        parts.insert(name, (pattern, body));
    }
    let locals = pending
        .into_iter()
        .map(|(name, (local, sorts))| {
            let argument = arguments
                .remove(&name)
                .expect("every stand-in is applied in one scope");
            let (pattern, body) = parts
                .remove(&name)
                .expect("every local function has an equation");
            (
                name,
                LoweredLocal {
                    local,
                    sorts,
                    argument,
                    pattern,
                    body,
                },
            )
        })
        .collect();
    Ok(Lowered {
        sentence: enclosing,
        locals,
        variables,
    })
}

struct Lowering<'i, 'v, 'd> {
    injector: &'i SortInjector<'v, 'd>,
    next: usize,
    /// Each local function and its lambda's sorts, by stand-in name.
    pending: BTreeMap<String, (LocalFunction, LambdaSorts)>,
    /// Each generated equation, `stand-in(P, C1..Cn) => B`, by stand-in name.
    equations: Vec<(String, Term)>,
    /// The first sort the injector could not compute.
    error: Option<SortInjectionError>,
}

impl Lowering<'_, '_, '_> {
    /// `term` with every local function replaced by its stand-in application, each recorded
    /// with its equation.
    // Invariant: each call recurses into the direct subterms of `term`, or into the parts of
    // one local function; the depth of `term` bounds the recursion.
    fn term(&mut self, term: &Term) -> Term {
        match term {
            Term::Annotated { term, metadata } => self.term(term).with_metadata(metadata.clone()),
            Term::Apply { label, arguments } => match LocalFunction::of(label, arguments.len()) {
                Some(Ok(local)) => self.local_function(local, arguments),
                Some(Err(_)) | None => Term::Apply {
                    label: label.clone(),
                    arguments: arguments
                        .iter()
                        .map(|argument| self.term(argument))
                        .collect(),
                },
            },
            Term::Rewrite { left, right } => Term::Rewrite {
                left: Box::new(self.term(left)),
                right: Box::new(self.term(right)),
            },
            Term::As { pattern, alias } => Term::As {
                pattern: Box::new(self.term(pattern)),
                alias: Box::new(self.term(alias)),
            },
            Term::Sequence(items) => {
                Term::Sequence(items.iter().map(|item| self.term(item)).collect())
            }
            Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => term.clone(),
        }
    }

    fn local_function(&mut self, local: LocalFunction, arguments: &[Term]) -> Term {
        let error = &mut self.error;
        let sorts = lambda_sorts(self.injector, local, arguments, |failure| {
            error.get_or_insert(failure);
        });
        let name = format!("{STAND_IN}{}", self.next);
        self.next += 1;
        let label = Label::new(name.clone());
        let closure = closure_variables(&local.equation(arguments))
            .into_iter()
            .map(|variable| variable.term())
            .collect::<Vec<_>>();
        let ((pattern, _), body) = local.equation_parts(arguments);
        let value = self.term(&arguments[local.argument_index()]);
        let pattern = self.term(pattern);
        let body = body.map(|(body, _)| self.term(body));
        let mut equation_arguments = vec![pattern];
        equation_arguments.extend(closure.iter().cloned());
        let left = Term::Apply {
            label: label.clone(),
            arguments: equation_arguments,
        };
        let equation = match body {
            Some(body) => Term::Rewrite {
                left: Box::new(left),
                right: Box::new(body),
            },
            None => left,
        };
        self.equations.push((name.clone(), equation));
        self.pending.insert(name, (local, sorts));
        let mut call = vec![value];
        call.extend(closure);
        Term::Apply {
            label,
            arguments: call,
        }
    }
}

/// `term` with every stand-in application replaced by its stand-in variable, of the lambda's
/// result sort; the application's value goes to `arguments`.
// Invariant: each call recurses into the direct subterms of `term`; its depth bounds the
// recursion.
fn stand_in_variables(
    term: Term,
    pending: &BTreeMap<String, (LocalFunction, LambdaSorts)>,
    arguments: &mut BTreeMap<String, Term>,
) -> Term {
    let mut replace = |term: Term| stand_in_variables(term, pending, arguments);
    match term.into_parts() {
        TermParts::Annotated { term, metadata } => replace(*term).with_metadata(metadata),
        TermParts::Apply {
            label,
            arguments: children,
        } => {
            if let Some((_, sorts)) = pending.get(&label.name) {
                let value = children
                    .into_iter()
                    .next()
                    .expect("a stand-in application holds the value first");
                let value = stand_in_variables(value, pending, arguments);
                arguments.insert(label.name.clone(), value);
                return Term::Variable {
                    name: label.name,
                    sort: Some(sorts.result.clone()),
                };
            }
            Term::Apply {
                label,
                arguments: children.into_iter().map(replace).collect(),
            }
        }
        TermParts::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(replace(*left)),
            right: Box::new(replace(*right)),
        },
        TermParts::As { pattern, alias } => Term::As {
            pattern: Box::new(replace(*pattern)),
            alias: Box::new(replace(*alias)),
        },
        TermParts::Sequence(items) => Term::Sequence(items.into_iter().map(replace).collect()),
        leaf @ (TermParts::InjectedLabel(_)
        | TermParts::Variable { .. }
        | TermParts::Token { .. }) => Term::from(leaf),
    }
}

fn truth() -> Term {
    Term::Token {
        token: "true".into(),
        sort: Sort::builtin(BuiltinSort::Bool),
    }
}
