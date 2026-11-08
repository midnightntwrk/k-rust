//! Which names an or-pattern binds, read against the match it is part of.
//!
//! A sentence's left-hand side is one pattern however many terms it is
//! written as (a subject and its function context, the cells of a `cells!`
//! pattern, the entries of a readable record), and a name it repeats is one
//! variable: nonlinear matching. Inside `A | B`, a name the match binds
//! outside the or-pattern is that variable, so each alternative uses it and
//! none binds it: `x | 1` beside a binding of `x` matches a term equal to
//! `x`, or `1`. What every alternative must bind alike (rustc's E0408) is
//! the names it binds fresh. "Outside" is a fact of every match, not of the
//! order the terms are written in: a name binds outside an or-pattern when
//! every match that passes through the or-pattern binds it at a position
//! that is not inside it. Another or-pattern binds, for every match, only
//! the names all of its alternatives hold, so `(x | 1)` beside `(x | 2)`
//! binds `x` outside neither.
//!
//! A `k::matches!` pattern is a match of its own, whose names are its own
//! binders and never the sentence's, and a `let` pattern takes no `|`: the
//! sentence's reading stops at both, and a `k::matches!` pattern is read
//! as its own match.

use std::collections::BTreeSet;

use super::{TermArguments, TermTree, UnboundAlternative, subterms};

/// For each `A | B` of one match, the names some alternative binds fresh
/// and another does not ([`TermTree::Or`]): the names the match binds
/// outside the or-pattern left out.
#[derive(Clone, Debug, Default)]
pub struct AlternativeBindings {
    /// Each or-pattern of the match, by identity, and the names it binds
    /// unequally, in first-appearance order.
    ors: Vec<(*const TermTree, Vec<UnboundAlternative>)>,
}

impl AlternativeBindings {
    /// Reads every or-pattern of the match `scope` writes: the terms one
    /// match matches together, below a `k::matches!` or `let` pattern
    /// excepted.
    #[must_use]
    pub fn of(scope: &[&TermTree]) -> Self {
        let mut ors = Vec::new();
        for tree in scope {
            or_patterns(tree, &mut ors);
        }
        let ors = ors
            .into_iter()
            .map(|or| {
                let TermTree::Or { unbound, .. } = or else {
                    unreachable!("or_patterns collects or-patterns only")
                };
                let outside = scope.iter().fold(BTreeSet::new(), |mut outside, tree| {
                    surely_bound(tree, or, &mut outside);
                    outside
                });
                let unequal = unbound
                    .iter()
                    .filter(|unbound| !outside.contains(&unbound.name))
                    .cloned()
                    .collect();
                (std::ptr::from_ref(or), unequal)
            })
            .collect();
        Self { ors }
    }

    /// The names `or` binds unequally where this match is read, none when
    /// every alternative binds the same fresh names; every name its
    /// alternatives hold unequally when `or` is no or-pattern of this match.
    #[must_use]
    pub fn unbound<'t>(&'t self, or: &'t TermTree) -> &'t [UnboundAlternative] {
        match self.ors.iter().find(|(known, _)| std::ptr::eq(*known, or)) {
            Some((_, unequal)) => unequal,
            None => match or {
                TermTree::Or { unbound, .. } => unbound,
                _ => &[],
            },
        }
    }
}

/// The or-patterns of `tree` that belong to its match, in preorder: not
/// those of a `k::matches!` pattern, a match of its own, nor of a `let`
/// pattern, which takes none.
fn or_patterns<'t>(tree: &'t TermTree, output: &mut Vec<&'t TermTree>) {
    let below = match tree {
        TermTree::Matches { subject, .. } => vec![subject.as_ref()],
        TermTree::Let { value, body, .. } => vec![value.as_ref(), body.as_ref()],
        TermTree::Or { .. } => {
            output.push(tree);
            subterms(tree)
        }
        _ => subterms(tree),
    };
    for subterm in below {
        or_patterns(subterm, output);
    }
}

/// Adds to `output` the names every match of `tree` binds outside
/// `target`: in a position no or-pattern encloses, in the alternative of an
/// or-pattern that holds `target` (a match through `target` takes it), or
/// in every alternative of another or-pattern. A name is a binding position
/// where the pattern holds it (as a binder, an alias, a constructor's or a
/// cell's field, a sort test's operand, a rewrite's left side); a test, a
/// `let` block and a record update's base read names, which bind none.
fn surely_bound(tree: &TermTree, target: &TermTree, output: &mut BTreeSet<String>) {
    if std::ptr::eq(tree, target) {
        return;
    }
    match tree {
        TermTree::Reference(path) => {
            if let Some(ident) = crate::path::pattern_binder(path) {
                output.insert(syn::ext::IdentExt::unraw(ident).to_string());
            }
        }
        TermTree::As { binding, pattern } => {
            output.insert(syn::ext::IdentExt::unraw(binding).to_string());
            surely_bound(pattern, target, output);
        }
        TermTree::Or { alternatives, .. } => {
            if let Some(holding) = alternatives
                .iter()
                .find(|alternative| holds(alternative, target))
            {
                surely_bound(holding, target, output);
                return;
            }
            let mut every: Option<BTreeSet<String>> = None;
            for alternative in alternatives {
                let mut names = BTreeSet::new();
                surely_bound(alternative, target, &mut names);
                every = Some(match every {
                    None => names,
                    Some(every) => every.intersection(&names).cloned().collect(),
                });
            }
            output.extend(every.unwrap_or_default());
        }
        TermTree::Application(application) => match &application.arguments {
            TermArguments::Positional(arguments) => {
                for argument in arguments {
                    surely_bound(argument, target, output);
                }
            }
            TermArguments::Named(arguments) => {
                for argument in arguments {
                    surely_bound(&argument.value, target, output);
                }
            }
        },
        TermTree::Cell(cell) => {
            for field in &cell.fields {
                surely_bound(&field.value, target, output);
            }
        }
        TermTree::SortTest { operand, .. } => surely_bound(operand, target, output),
        TermTree::Rewrite { from, .. } => surely_bound(from, target, output),
        TermTree::Matches { .. }
        | TermTree::Let { .. }
        | TermTree::Closure { .. }
        | TermTree::OrBool { .. }
        | TermTree::Literal(_)
        | TermTree::Wildcard(_)
        | TermTree::IdToken { .. }
        | TermTree::BytesToken { .. }
        | TermTree::Anonymous { .. }
        | TermTree::Lexeme { .. } => {}
    }
}

/// Whether `target` is `tree` or below it.
fn holds(tree: &TermTree, target: &TermTree) -> bool {
    std::ptr::eq(tree, target)
        || subterms(tree)
            .into_iter()
            .any(|subterm| holds(subterm, target))
}
