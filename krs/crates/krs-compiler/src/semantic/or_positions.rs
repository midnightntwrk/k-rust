//! Where an `A | B` or-pattern (K's `#Or`) may stand in a pattern that the
//! compiled definition reads as an equation (KF-030).
//!
//! An equation `f(P) => R` defines `f` by matching its arguments, and an
//! or-pattern at the root of an argument, `f(A | B) => R`, is the equations
//! `f(A) => R` and `f(B) => R`. Below that root an or-pattern means the same
//! by distribution (a symbol distributes over `#Or`, so `f(g(A | B))` is
//! `f(g(A) | g(B))`, and `x @ (A | B)` is `(x @ A) | (x @ B)`), but the
//! definition compiler reads an equation's alternatives only at an argument's
//! root, so `krs build` refuses the others. This check refuses them first,
//! with the rewrite that keeps the alternatives at the root:
//!
//! - in a function equation or an anywhere rule, an or-pattern below a
//!   symbol, below an alias, or in a function context cell, and one at an
//!   argument's root whose alternatives are of a sort below the argument's,
//!   which K's sort injection places below an injection;
//! - in a simplification, any or-pattern: a simplification rewrites one term;
//! - in a `k::matches!(t, P)` pattern, which K tests with a generated function
//!   whose one equation matches `P` at the root of its argument, an
//!   or-pattern below `P`'s root, and one at the root whose alternatives are
//!   of a sort below `t`'s.
//!
//! Other transitions and claims match an or-pattern anywhere, so their own
//! sides are not checked.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{ApplicationRef, SentenceKind, StableItemId};
use krs_ir_levels::{
    IrCondition, RuleBodyRef, SemanticModule, SemanticRule, SemanticSortRef, SemanticTerm,
    SemanticTermKind,
};

use super::catalog::{ProductionSignature, semantic_is_subsort};
use super::error::DescriptorLoweringError;
use super::overload::sort_name;

/// Refuses an or-pattern where the definition compiler does not read it.
pub(super) fn check_or_pattern_positions(
    modules: &[SemanticModule],
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
    sort_parents: &BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
) -> Result<(), DescriptorLoweringError> {
    let check = Check {
        catalog,
        sort_parents,
    };
    for rule in modules.iter().flat_map(SemanticModule::rules) {
        let refusal = check
            .sentence(rule)
            .or_else(|| sentence_terms(rule).find_map(|term| check.matches_in(term)));
        if let Some(Refusal { node, problem }) = refusal {
            return Err(DescriptorLoweringError::InvalidPatternOr {
                item: Box::new(rule.id().clone()),
                reason: problem.reason(),
                range: node.origin().origin().exact_authored_range().map(Box::new),
            });
        }
    }
    Ok(())
}

/// Where a refused or-pattern stands.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Site {
    /// A function equation's or an anywhere rule's left-hand side.
    Equation,
    /// A `k::matches!` pattern.
    Matches,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Problem {
    /// Directly below an alias at the root: `x @ (A | B)`.
    BelowAlias(Site),
    /// Below a symbol, or below an alias that is not at the root.
    BelowRoot(Site),
    /// At the root, with alternatives of a sort below the position's.
    Injected {
        site: Site,
        alternatives: String,
        position: String,
    },
    /// In a function context cell.
    Context,
    /// Anywhere in a simplification's left-hand side.
    Simplification,
}

impl Problem {
    fn reason(&self) -> String {
        match self {
            Self::BelowAlias(Site::Equation) => {
                "`x @ (A | B)` puts the alternatives below the alias, but an equation's alternatives compile only at the root of an argument of the function it defines; write `(x @ A) | (x @ B)`, which binds `x` to the same term".to_owned()
            }
            Self::BelowAlias(Site::Matches) => {
                "`x @ (A | B)` puts the alternatives below the alias, but a `k::matches!` pattern's alternatives compile only at its root (K tests it with a generated equation); write `(x @ A) | (x @ B)`".to_owned()
            }
            Self::BelowRoot(Site::Equation) => {
                "an equation's alternatives compile only at the root of an argument of the function it defines, and a symbol distributes over `|`; write them at the argument's root, `F(G(A) | G(B))` for `F(G(A | B))`, or write one equation per alternative".to_owned()
            }
            Self::BelowRoot(Site::Matches) => {
                "a `k::matches!` pattern's alternatives compile only at its root (K tests it with a generated equation), and a symbol distributes over `|`; write them at the root, `G(A) | G(B)` for `G(A | B)`, or test each with `k::matches!(t, P1) || k::matches!(t, P2)`".to_owned()
            }
            Self::Injected {
                site: Site::Equation,
                alternatives,
                position,
            } => format!(
                "the alternatives have sort `{alternatives}`, below the argument's sort `{position}`, so sort injection places the or-pattern below an injection, not at the argument's root, where an equation's alternatives compile; write one equation per alternative"
            ),
            Self::Injected {
                site: Site::Matches,
                alternatives,
                position,
            } => format!(
                "the alternatives have sort `{alternatives}`, below the tested term's sort `{position}`, so sort injection places the or-pattern below an injection, not at the root of the generated equation that tests it; test each with `k::matches!(t, P1) || k::matches!(t, P2)`"
            ),
            Self::Context => {
                "an equation's alternatives compile only at the root of an argument of the function it defines, and a function context cell is not one; write one equation per alternative".to_owned()
            }
            Self::Simplification => {
                "a simplification rewrites one term, and an or-pattern in its left-hand side is not one; write one simplification per alternative".to_owned()
            }
        }
    }
}

struct Refusal<'t> {
    node: &'t SemanticTerm,
    problem: Problem,
}

struct Check<'c> {
    catalog: &'c BTreeMap<StableItemId, ProductionSignature>,
    sort_parents: &'c BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
}

impl Check<'_> {
    /// The or-patterns of a sentence's own left-hand side.
    fn sentence<'t>(&self, rule: &'t SemanticRule) -> Option<Refusal<'t>> {
        if rule.kind() == SentenceKind::Simplification {
            return pre_patterns(rule).into_iter().find_map(|term| {
                first_or(term).map(|node| Refusal {
                    node,
                    problem: Problem::Simplification,
                })
            });
        }
        if rule.kind() != SentenceKind::Equation && rule.anywhere().is_none() {
            return None;
        }
        let from_body = match rule.relational_body() {
            RuleBodyRef::Term(body) => self.application_pattern(body.from()),
            body => pre_patterns_of(body).into_iter().find_map(|term| {
                first_or(term).map(|node| Refusal {
                    node,
                    problem: Problem::BelowRoot(Site::Equation),
                })
            }),
        };
        from_body.or_else(|| {
            rule.function_context()?
                .cells()
                .cells()
                .iter()
                .find_map(|cell| first_or(cell.pattern()))
                .map(|node| Refusal {
                    node,
                    problem: Problem::Context,
                })
        })
    }

    /// An equation's left-hand side: each argument of the defined
    /// application is an argument root.
    fn application_pattern<'t>(&self, pattern: &'t SemanticTerm) -> Option<Refusal<'t>> {
        let SemanticTermKind::Application {
            application,
            arguments,
            ..
        } = pattern.kind()
        else {
            return below_root(pattern, Site::Equation);
        };
        let signature = match application {
            ApplicationRef::Declared(production) => self.catalog.get(production),
            _ => None,
        };
        arguments.iter().enumerate().find_map(|(index, argument)| {
            let position = signature
                .and_then(|signature| signature.fields.get(index))
                .map(|(_, sort)| sort)
                .filter(|sort| !matches!(sort, SemanticSortRef::Parameter(_)));
            self.root(argument, position, Site::Equation)
        })
    }

    /// A term at a root, the argument of an application at sort `position`
    /// (when known), where an or-pattern is read alternative by alternative.
    fn root<'t>(
        &self,
        term: &'t SemanticTerm,
        position: Option<&SemanticSortRef>,
        site: Site,
    ) -> Option<Refusal<'t>> {
        match term.kind() {
            SemanticTermKind::Or { alternatives } => {
                if let Some(position) = position
                    && !semantic_is_subsort(position, term.sort(), self.sort_parents)
                {
                    return Some(Refusal {
                        node: term,
                        problem: Problem::Injected {
                            site,
                            alternatives: sort_name(term.sort()),
                            position: sort_name(position),
                        },
                    });
                }
                alternatives
                    .iter()
                    .find_map(|alternative| self.root(alternative, None, site))
            }
            SemanticTermKind::As { pattern, .. } => {
                let mut aliased = pattern.as_ref();
                while let SemanticTermKind::As { pattern, .. } = aliased.kind() {
                    aliased = pattern;
                }
                if matches!(aliased.kind(), SemanticTermKind::Or { .. }) {
                    return Some(Refusal {
                        node: aliased,
                        problem: Problem::BelowAlias(site),
                    });
                }
                below_root(aliased, site)
            }
            _ => below_root(term, site),
        }
    }

    /// The first refused or-pattern of a `k::matches!` pattern in `term`.
    fn matches_in<'t>(&self, term: &'t SemanticTerm) -> Option<Refusal<'t>> {
        if let SemanticTermKind::Matches {
            subject, pattern, ..
        } = term.kind()
            && let Some(refusal) = self.root(pattern, Some(subject.sort()), Site::Matches)
        {
            return Some(refusal);
        }
        term.children()
            .into_iter()
            .find_map(|child| self.matches_in(child))
    }
}

/// The first or-pattern at or below `term`, as one below an argument root.
fn below_root(term: &SemanticTerm, site: Site) -> Option<Refusal<'_>> {
    first_or(term).map(|node| Refusal {
        node,
        problem: Problem::BelowRoot(site),
    })
}

/// The first or-pattern at or below `term`, in preorder.
fn first_or(term: &SemanticTerm) -> Option<&SemanticTerm> {
    if matches!(term.kind(), SemanticTermKind::Or { .. }) {
        return Some(term);
    }
    term.children().into_iter().find_map(first_or)
}

fn pre_patterns(rule: &SemanticRule) -> Vec<&SemanticTerm> {
    pre_patterns_of(rule.relational_body())
}

fn pre_patterns_of(body: RuleBodyRef<'_, krs_ir_levels::SemanticLevel>) -> Vec<&SemanticTerm> {
    match body {
        RuleBodyRef::Term(body) => vec![body.from()],
        RuleBodyRef::Predicate(body) => body.lhs().terms(),
        RuleBodyRef::Configuration { body, .. } => body
            .parts()
            .iter()
            .filter_map(krs_ir::ClausePart::pre_term)
            .collect(),
    }
}

/// Every term of a sentence: its sides, conditions, and function context.
fn sentence_terms(rule: &SemanticRule) -> impl Iterator<Item = &SemanticTerm> {
    let body = match rule.relational_body() {
        RuleBodyRef::Term(body) => vec![body.from(), body.to()],
        RuleBodyRef::Predicate(body) => {
            let mut terms = body.lhs().terms();
            terms.extend(body.rhs().terms());
            terms
        }
        RuleBodyRef::Configuration { body, .. } => body
            .parts()
            .iter()
            .flat_map(|part| part.pre_term().into_iter().chain(part.post_term()))
            .collect(),
    };
    let context = rule.function_context().into_iter().flat_map(|context| {
        context
            .cells()
            .cells()
            .iter()
            .map(krs_ir::FixedCellPattern::pattern)
    });
    body.into_iter()
        .chain(rule.requires().into_iter().flat_map(IrCondition::terms))
        .chain(rule.ensures().into_iter().flat_map(IrCondition::terms))
        .chain(context)
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use krs_ir::{
        ApplicationRef, AtLeastTwo, BuiltinSort, ItemKind, NodeOrigin, PackageId, SemanticId,
        SourceMapKey, StableItemId,
    };
    use krs_ir_levels::{SemanticSortRef, SemanticTerm};

    use super::{Check, Problem, Site};

    const K: SemanticSortRef = SemanticSortRef::Builtin(BuiltinSort::KSequence);
    const INT: SemanticSortRef = SemanticSortRef::Builtin(BuiltinSort::Int);

    fn origin() -> NodeOrigin {
        NodeOrigin::new(
            SourceMapKey::new("sem.or-positions").unwrap(),
            krs_ir::testing::authored(0, 1),
        )
    }

    fn constructor(name: &str, arguments: Vec<SemanticTerm>) -> SemanticTerm {
        SemanticTerm::application(
            origin(),
            K,
            ApplicationRef::Declared(
                StableItemId::new(
                    PackageId::new("OR-POSITIONS", "or-positions", "0.1.0", "test").unwrap(),
                    ["fixture"],
                    name,
                    ItemKind::Constructor,
                    "",
                )
                .unwrap(),
            ),
            arguments,
        )
    }

    fn unit(name: &str) -> SemanticTerm {
        constructor(name, Vec::new())
    }

    fn or(sort: SemanticSortRef, alternatives: Vec<SemanticTerm>) -> SemanticTerm {
        SemanticTerm::pattern_or(origin(), sort, AtLeastTwo::try_from(alternatives).unwrap())
    }

    fn alias(name: &str, pattern: SemanticTerm) -> SemanticTerm {
        SemanticTerm::pattern_as(
            origin(),
            K,
            SemanticId::new(name.to_owned()).unwrap(),
            pattern,
        )
    }

    fn token(value: &str) -> SemanticTerm {
        SemanticTerm::token(origin(), INT, value).unwrap()
    }

    fn problem(term: &SemanticTerm, position: Option<&SemanticSortRef>) -> Option<Problem> {
        let catalog = BTreeMap::new();
        let parents = BTreeMap::<SemanticSortRef, BTreeSet<SemanticSortRef>>::new();
        let check = Check {
            catalog: &catalog,
            sort_parents: &parents,
        };
        check
            .root(term, position, Site::Equation)
            .map(|refusal| refusal.problem)
    }

    #[test]
    fn alternatives_at_an_argument_root_are_read() {
        let term = or(K, vec![unit("red"), unit("green")]);
        assert_eq!(problem(&term, Some(&K)), None);
    }

    #[test]
    fn an_alias_over_alternatives_is_refused_with_the_distributed_form() {
        let term = alias("op", or(K, vec![unit("red"), unit("green")]));
        assert_eq!(
            problem(&term, Some(&K)),
            Some(Problem::BelowAlias(Site::Equation))
        );
        let reason = Problem::BelowAlias(Site::Equation).reason();
        assert!(reason.contains("`(x @ A) | (x @ B)`"), "{reason}");
    }

    #[test]
    fn aliases_inside_root_alternatives_are_read() {
        let term = or(
            K,
            vec![alias("op", unit("red")), alias("op", unit("green"))],
        );
        assert_eq!(problem(&term, Some(&K)), None);
    }

    #[test]
    fn alternatives_below_a_symbol_are_refused() {
        let term = constructor("color", vec![or(K, vec![unit("red"), unit("green")])]);
        assert_eq!(
            problem(&term, Some(&K)),
            Some(Problem::BelowRoot(Site::Equation))
        );
        let below_root_alternative = or(
            K,
            vec![
                constructor("color", vec![or(K, vec![unit("red"), unit("green")])]),
                unit("blue"),
            ],
        );
        assert_eq!(
            problem(&below_root_alternative, Some(&K)),
            Some(Problem::BelowRoot(Site::Equation))
        );
    }

    #[test]
    fn alternatives_below_the_position_sort_are_refused() {
        let term = or(INT, vec![token("1"), token("2")]);
        assert_eq!(
            problem(&term, Some(&K)),
            Some(Problem::Injected {
                site: Site::Equation,
                alternatives: "Int".to_owned(),
                position: "K".to_owned(),
            })
        );
        assert_eq!(problem(&term, Some(&INT)), None);
    }

    #[test]
    fn a_matches_pattern_is_read_at_its_root_at_the_tested_sort() {
        let catalog = BTreeMap::new();
        let parents = BTreeMap::new();
        let check = Check {
            catalog: &catalog,
            sort_parents: &parents,
        };
        let test = |subject: SemanticTerm, pattern: SemanticTerm| {
            let term = SemanticTerm::matches(
                origin(),
                SemanticSortRef::Builtin(BuiltinSort::Bool),
                subject,
                pattern,
                Vec::new(),
            );
            check.matches_in(&term).map(|refusal| refusal.problem)
        };
        let subject =
            || SemanticTerm::variable(origin(), K, SemanticId::new("E".to_owned()).unwrap());
        assert_eq!(
            test(subject(), or(K, vec![unit("red"), unit("green")])),
            None
        );
        assert_eq!(
            test(
                subject(),
                constructor("color", vec![or(K, vec![unit("red"), unit("green")])])
            ),
            Some(Problem::BelowRoot(Site::Matches))
        );
        assert_eq!(
            test(subject(), or(INT, vec![token("1"), token("2")])),
            Some(Problem::Injected {
                site: Site::Matches,
                alternatives: "Int".to_owned(),
                position: "K".to_owned(),
            })
        );
    }
}
