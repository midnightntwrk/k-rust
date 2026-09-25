//! A read-only typing view of a loaded rule-like sentence, computed by the injector's own sort
//! functions and the variable sorts of semantic-cast resolution.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::definition::{AttributeKey, ProductionItem, ResolvedDefinition, Sentence};
use crate::kast::parser::parse_sort_text;
use crate::kast::{GeneratedLabel, InternalLabel, Sort, Term};
use crate::kompile::passes::{
    ResolveSemanticCastsError, is_anonymous, semantic_cast_variable_sorts, with_kitem_subsorts,
};
use crate::kompile::view::View;
use crate::names::BuiltinSort;

use super::{SortInjectionError, SortInjector, SortMismatch, render_term};

/// The sorts at one position of a sentence.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PositionTyping {
    /// The sort of the term at the position, or `None` for syntax that has no sort (the `#cells`
    /// wrapper, `#dots`, `#noDots`) and for a variable whose sort nothing determines.
    pub sort: Option<Sort>,
    /// The sort the position requires of its term, or `None` where the compiler places no sort
    /// requirement (a rule body's root, a child of a syntax-only term, an argument of a
    /// construct without a production).
    pub required: Option<Sort>,
}

/// The typing of one rule-like sentence, as the compiler computes it.
///
/// Paths are those of [`crate::provenance::DestinationAnchor::path`]: the first step selects the
/// sentence field (0 body, 1 requires, 2 ensures), and each further step selects a child: the
/// left (0) or right (1) side of a rewrite, the pattern (0) or alias (1) of an as-pattern, an
/// application's argument (semantic casts included), or a sequence item. Annotations are
/// transparent.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SentenceTyping {
    /// Every position of the sentence.
    pub positions: BTreeMap<Vec<u32>, PositionTyping>,
    /// The sort of each named variable that semantic-cast resolution determines.
    pub variables: BTreeMap<String, Sort>,
}

/// Why a sentence has no typing: the same errors compilation reports for it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SentenceTypingError {
    /// The sentence is not a rule or claim.
    NotRuleLike,
    /// The module is not in the definition.
    MissingModule(String),
    /// The variables' sort annotations and casts disagree.
    SemanticCasts(ResolveSemanticCastsError),
    /// A term is ill-sorted at its position, a cast is incomparable with its operand, or a
    /// production cannot be instantiated; `location` is the sentence's `source:line` when known.
    Sort {
        location: Option<String>,
        error: SortInjectionError,
    },
}

impl fmt::Display for SentenceTypingError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotRuleLike => write!(formatter, "only rules and claims have a typing view"),
            Self::MissingModule(module) => write!(formatter, "module {module:?} was not found"),
            Self::SemanticCasts(error) => error.fmt(formatter),
            Self::Sort { location, error } => {
                if let Some(location) = location {
                    write!(formatter, "{location}: ")?;
                }
                error.fmt(formatter)
            }
        }
    }
}

impl std::error::Error for SentenceTypingError {}

/// The typing of `sentence`, a rule or claim of `module`, at the loaded layer.
///
/// Each position reports the sort of its term and the sort its position requires, both computed
/// by the functions compilation uses: semantic-cast resolution's variable sorts, and the sort
/// injector's production signatures (with its parametric instantiation), least upper bounds of
/// rewrite and as-pattern sides, and subsort order. The sentence is checked on the way with the
/// injector's rules, so a sentence compilation rejects for an ill-sorted term, an incomparable
/// cast, or disagreeing variable annotations returns that error here.
///
/// The view does not infer: a variable without an explicit sort or a cast reports no sort.
///
/// A term whose sort is at or below its position's required sort is accepted by compilation at
/// that position. Compilation accepts more in three places, which the view reports as
/// requirements it does not state: below a semantic cast it also accepts an operand strictly above
/// the cast sort (a projected downcast); at a collection or user-list position it also accepts an
/// element it wraps; and rewrite and as-pattern sides are required to be below the least upper
/// bound of the current sides, which a replacement may raise.
pub fn sentence_typing(
    definition: &ResolvedDefinition,
    module: &str,
    sentence: &Sentence,
) -> Result<SentenceTyping, SentenceTypingError> {
    let module_id = definition
        .module_id(module)
        .ok_or_else(|| SentenceTypingError::MissingModule(module.to_owned()))?;
    let cycle = |cycle: crate::definition::PartialOrderCycle<Sort>| SentenceTypingError::Sort {
        location: None,
        error: SortInjectionError::CircularSubsort(cycle.path),
    };
    let sorts = definition.sort_catalog(module_id);
    // A loaded definition has not yet run the stage that declares every user sort below `KItem`;
    // injection runs after it, so the view types the sentence in that order.
    let subsorts = with_kitem_subsorts(
        &definition.subsorts(module_id).map_err(cycle)?,
        sorts.all_sorts(),
    )
    .map_err(cycle)?;
    let injector = SortInjector {
        productions: View::Shared(definition.production_catalog(module_id)),
        sorts: View::Owned(sorts),
        subsorts: View::Owned(subsorts),
        next_sort_parameter: Cell::new(0),
        used_sort_parameters: RefCell::new(BTreeSet::new()),
    };
    injector.sentence_typing(sentence)
}

impl SortInjector<'_, '_> {
    /// [`sentence_typing`] with an injector already built for the sentence's module.
    pub fn sentence_typing(
        &self,
        sentence: &Sentence,
    ) -> Result<SentenceTyping, SentenceTypingError> {
        let (Sentence::Rule {
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
        }) = sentence
        else {
            return Err(SentenceTypingError::NotRuleLike);
        };
        let variables = semantic_cast_variable_sorts(sentence, &self.subsorts)
            .map_err(SentenceTypingError::SemanticCasts)?;
        let location =
            sentence
                .attributes()
                .source()
                .map(|source| match sentence.attributes().location() {
                    Some(location) => format!("{source}:{}", location.start_line),
                    None => source.to_owned(),
                });
        let mut walk = Walk {
            injector: self,
            variables: &variables,
            positions: BTreeMap::new(),
        };
        let boolean = Sort::builtin(BuiltinSort::Bool);
        self.next_sort_parameter.set(0);
        self.used_sort_parameters.borrow_mut().clear();
        // As in `inject_rule_body`, the body is typed at a fresh sort variable, which a parametric
        // result sort (a matching-logic connective, say) takes.
        let top = self.fresh_sort_parameter();
        let result = (|| {
            walk.visit(body, &mut vec![0], Some(&top), None)?;
            for (field, condition) in [(1, requires), (2, ensures)] {
                let mut path = vec![field];
                let sort = walk.visit(condition, &mut path, Some(&boolean), None)?;
                walk.place(condition, &path, sort.as_ref(), &boolean)?;
            }
            Ok(())
        })();
        result.map_err(|error| SentenceTypingError::Sort { location, error })?;
        Ok(SentenceTyping {
            positions: walk.positions,
            variables,
        })
    }

    /// Whether compilation accepts a term of sort `actual` at a position of sort `expected`: the
    /// decision `inject_with_position` makes before building an injection or a wrapper.
    fn accepts_at(
        &self,
        term: &Term,
        actual: &Sort,
        expected: &Sort,
    ) -> Result<bool, SortInjectionError> {
        if actual == expected {
            return Ok(true);
        }
        let kitem = Sort::builtin(BuiltinSort::KItem);
        if expected.is_builtin(BuiltinSort::K) {
            return Ok(*actual == kitem || self.below(actual, &kitem));
        }
        if self
            .collection_wrapper(term, actual, expected, term.clone(), false)?
            .is_some()
            || self
                .user_list_wrapper(actual, expected, term.clone())
                .is_some()
        {
            return Ok(true);
        }
        Ok(self.below(actual, expected))
    }
}

struct Walk<'a, 'view, 'definition> {
    injector: &'a SortInjector<'view, 'definition>,
    variables: &'a BTreeMap<String, Sort>,
    positions: BTreeMap<Vec<u32>, PositionTyping>,
}

impl Walk<'_, '_, '_> {
    /// Record `required` at `path` and reject the term there unless compilation accepts it.
    fn place(
        &mut self,
        term: &Term,
        path: &[u32],
        sort: Option<&Sort>,
        required: &Sort,
    ) -> Result<(), SortInjectionError> {
        if let Some(position) = self.positions.get_mut(path) {
            position.required = Some(required.clone());
        }
        let Some(sort) = sort else {
            return Ok(());
        };
        if self.injector.accepts_at(term, sort, required)? {
            Ok(())
        } else {
            Err(SortInjectionError::IllSortedTerm(Box::new(SortMismatch {
                term: render_term(term),
                found: sort.clone(),
                required: required.clone(),
            })))
        }
    }

    fn child(
        &mut self,
        term: &Term,
        path: &mut Vec<u32>,
        index: usize,
        hint: Option<&Sort>,
        cast: Option<&Sort>,
    ) -> Result<Option<Sort>, SortInjectionError> {
        path.push(u32::try_from(index).expect("a term has fewer than 2^32 children"));
        let sort = self.visit(term, path, hint, cast);
        path.pop();
        sort
    }

    fn place_child(
        &mut self,
        term: &Term,
        path: &mut Vec<u32>,
        index: usize,
        sort: Option<&Sort>,
        required: &Sort,
    ) -> Result<(), SortInjectionError> {
        path.push(u32::try_from(index).expect("a term has fewer than 2^32 children"));
        let placed = self.place(term, path, sort, required);
        path.pop();
        placed
    }

    /// Record the sort of `term` at `path` and of every subterm, returning the term's sort.
    ///
    /// `hint` is the sort the enclosing position expects, which instantiates a parametric
    /// production as it does during injection; `cast` is the sort of a directly enclosing
    /// semantic cast, which types an anonymous variable.
    // Invariant: each call records `path` once and recurses only into the direct subterms of `term`, extending `path` by one step; the depth of `term` bounds the recursion.
    fn visit(
        &mut self,
        term: &Term,
        path: &mut Vec<u32>,
        hint: Option<&Sort>,
        cast: Option<&Sort>,
    ) -> Result<Option<Sort>, SortInjectionError> {
        self.positions
            .insert(path.clone(), PositionTyping::default());
        let injector = self.injector;
        let kitem = Sort::builtin(BuiltinSort::KItem);
        let natural = match term.unannotated() {
            Term::Variable { name, sort } => sort.clone().or_else(|| {
                if is_anonymous(name) {
                    cast.cloned()
                } else {
                    self.variables.get(name).cloned()
                }
            }),
            Term::InjectedLabel(_) => Some(kitem.clone()),
            Term::Token { sort, .. } => Some(sort.clone()),
            Term::Sequence(items) => {
                for (index, item) in items.iter().enumerate() {
                    let sort = self.child(item, path, index, Some(&kitem), None)?;
                    let required = if sort
                        .as_ref()
                        .is_some_and(|sort| sort.is_builtin(BuiltinSort::K))
                    {
                        Sort::builtin(BuiltinSort::K)
                    } else {
                        kitem.clone()
                    };
                    self.place_child(item, path, index, sort.as_ref(), &required)?;
                }
                Some(Sort::builtin(BuiltinSort::K))
            }
            Term::Rewrite { left, right } => self.sides(path, [left, right], hint)?,
            Term::As { pattern, alias } => self.sides(path, [pattern, alias], hint)?,
            Term::Apply { label, arguments } => {
                if let Some(target) = label.semantic_cast_sort() {
                    let [argument] = arguments.as_slice() else {
                        return Err(SortInjectionError::InvalidArity {
                            label: label.name.clone(),
                            expected: 1,
                            actual: arguments.len(),
                        });
                    };
                    let sort = self.child(argument, path, 0, Some(&target), Some(&target))?;
                    if let Some(position) =
                        self.positions.get_mut(&[path.as_slice(), &[0]].concat())
                    {
                        position.required = Some(target.clone());
                    }
                    if let Some(sort) = &sort
                        && !matches!(argument.unannotated(), Term::Variable { .. })
                        && !injector.below(sort, &target)
                        && !injector.below(&target, sort)
                    {
                        return Err(SortInjectionError::IncomparableCast(Box::new(
                            SortMismatch {
                                term: render_term(argument),
                                found: sort.clone(),
                                required: target,
                            },
                        )));
                    }
                    Some(target)
                } else if label.is(InternalLabel::Cells)
                    || label.is(InternalLabel::Dots)
                    || label.is(InternalLabel::NoDots)
                {
                    for (index, argument) in arguments.iter().enumerate() {
                        self.child(argument, path, index, None, None)?;
                    }
                    None
                } else if injector.has_production(term, label) {
                    self.application(term, path, hint)?
                } else if let Some(GeneratedLabel::Projection { sort_text }) = label.generated()
                    && let Ok(target) = parse_sort_text(sort_text)
                    && let [argument] = arguments.as_slice()
                {
                    // `project:S` of a downcast is declared by a later stage as
                    // `S ::= "project:S" "(" K ")"`; the loaded layer already uses it.
                    let k = Sort::builtin(BuiltinSort::K);
                    let sort = self.child(argument, path, 0, Some(&k), None)?;
                    self.place_child(argument, path, 0, sort.as_ref(), &k)?;
                    Some(target)
                } else {
                    for (index, argument) in arguments.iter().enumerate() {
                        self.child(argument, path, index, None, None)?;
                    }
                    Some(injector.term_sort_with_arity(term, hint, true)?)
                }
            }
            Term::Annotated { .. } => unreachable!("unannotated terms carry no annotation"),
        };
        let sort = match (
            natural,
            term.metadata().and_then(|metadata| metadata.sort.as_ref()),
        ) {
            (Some(natural), Some(target)) if *target != natural => {
                if injector.subsorts.less_than_eq(target, &natural) {
                    Some(target.clone())
                } else if !injector.below(&natural, target) && !injector.below(target, &natural) {
                    return Err(SortInjectionError::IncomparableCast(Box::new(
                        SortMismatch {
                            term: render_term(term),
                            found: natural,
                            required: target.clone(),
                        },
                    )));
                } else {
                    Some(natural)
                }
            }
            (natural, _) => natural,
        };
        if let Some(position) = self.positions.get_mut(path.as_slice()) {
            position.sort = sort.clone();
        }
        Ok(sort)
    }

    /// The sides of a rewrite or as-pattern: both are placed at their least upper bound, bounded
    /// by the position's sort as in the injector's inference.
    fn sides(
        &mut self,
        path: &mut Vec<u32>,
        sides: [&Term; 2],
        hint: Option<&Sort>,
    ) -> Result<Option<Sort>, SortInjectionError> {
        let sorts = sides
            .iter()
            .enumerate()
            .map(|(index, side)| self.child(side, path, index, hint, None))
            .collect::<Result<Vec<_>, _>>()?;
        let known = sorts.iter().flatten().cloned().collect::<Vec<_>>();
        if known.is_empty() {
            return Ok(None);
        }
        let bound = self.injector.least_upper_bound(&known, hint)?;
        for (index, (side, sort)) in sides.iter().zip(&sorts).enumerate() {
            self.place_child(side, path, index, sort.as_ref(), &bound)?;
        }
        Ok(Some(bound))
    }

    /// An application of a production: an authored cell `label(#dots|#noDots, body,
    /// #dots|#noDots)`, whose body is placed at the cell's single declared child sort when it
    /// has one, or an ordinary application placed by the injector's signature.
    fn application(
        &mut self,
        term: &Term,
        path: &mut Vec<u32>,
        hint: Option<&Sort>,
    ) -> Result<Option<Sort>, SortInjectionError> {
        let injector = self.injector;
        let Term::Apply { label, arguments } = term.unannotated() else {
            unreachable!("only applications have productions")
        };
        let production = injector.production(term, label)?;
        let Sentence::Production {
            sort,
            items,
            attributes,
            ..
        } = production
        else {
            unreachable!("the production catalog holds productions")
        };
        if attributes.has(AttributeKey::Cell)
            && let [left, body, right] = arguments.as_slice()
            && [left, right].iter().all(|marker| is_dots_marker(marker))
        {
            let children = items
                .iter()
                .filter_map(|item| match item {
                    ProductionItem::NonTerminal { sort, .. } => Some(sort.clone()),
                    _ => None,
                })
                .collect::<Vec<_>>();
            let content = match children.as_slice() {
                [content] => Some(content.clone()),
                _ => None,
            };
            let result = sort.clone();
            self.child(left, path, 0, None, None)?;
            let body_sort = self.child(body, path, 1, content.as_ref(), None)?;
            if let Some(content) = &content {
                self.place_child(body, path, 1, body_sort.as_ref(), content)?;
            }
            self.child(right, path, 2, None, None)?;
            return Ok(Some(result));
        }
        let signature = injector.signature(term, label, arguments, hint, false)?;
        for (index, (argument, required)) in arguments.iter().zip(&signature.arguments).enumerate()
        {
            let sort = self.child(argument, path, index, Some(required), None)?;
            self.place_child(argument, path, index, sort.as_ref(), required)?;
        }
        Ok(Some(signature.result))
    }
}

fn is_dots_marker(term: &Term) -> bool {
    matches!(
        term.unannotated(),
        Term::Apply { label, arguments }
            if arguments.is_empty()
                && (label.is(InternalLabel::Dots) || label.is(InternalLabel::NoDots))
    )
}
