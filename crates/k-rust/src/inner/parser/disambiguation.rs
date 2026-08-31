//! Priority and associativity filtering over production-bearing parse trees.

#[cfg(test)]
use std::collections::BTreeMap;
use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;

#[cfg(test)]
use super::parametric::substitute_sort;
use super::{
    Grammar, Item, PackedNode, PackedTerm, ParseError, ParsedTerm, Production,
    cmp_packed_structurally, lower_term, packed_terms_in_structural_order,
};
use crate::kast::{Sort, Term, string};

use super::canonical_packed_error;

fn packed_sets_share_nodes(
    left: &BTreeSet<Rc<PackedTerm>>,
    right: &BTreeSet<Rc<PackedTerm>>,
) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| Rc::ptr_eq(left, right))
}

type PackedTransformResult = Result<Rc<PackedTerm>, ParseError>;
type PackedTransformMemo = HashMap<*const PackedTerm, (Rc<PackedTerm>, PackedTransformResult)>;
type PackedPriorityChildMemo =
    HashMap<(*const PackedTerm, usize, Option<Side>), (Rc<PackedTerm>, PackedTransformResult)>;

impl Grammar {
    /// Apply Java's pre-inference ambiguity factoring after record and application syntax has
    /// already been resolved, retaining identity sharing until the forest is compressed.
    pub(super) fn factor_pre_inference_packed_ambiguities(
        &self,
        term: Rc<PackedTerm>,
    ) -> Rc<PackedTerm> {
        self.factor_packed_ambiguities(term, &mut HashMap::new())
    }

    fn factor_packed_ambiguities(
        &self,
        term: Rc<PackedTerm>,
        memo: &mut HashMap<*const PackedTerm, (Rc<PackedTerm>, Rc<PackedTerm>)>,
    ) -> Rc<PackedTerm> {
        let identity = Rc::as_ptr(&term);
        if let Some((_, factored)) = memo.get(&identity) {
            return Rc::clone(factored);
        }
        let factored = match &term.node {
            PackedNode::InstantiatedProduction {
                production,
                parameters,
                children,
                metadata,
            } => {
                let factored_children = children
                    .iter()
                    .map(|child| self.factor_packed_ambiguities(Rc::clone(child), memo))
                    .collect::<Vec<_>>();
                if factored_children
                    .iter()
                    .zip(children)
                    .all(|(factored, original)| Rc::ptr_eq(factored, original))
                {
                    Rc::clone(&term)
                } else {
                    PackedTerm::instantiated_production(
                        *production,
                        parameters.clone(),
                        factored_children,
                        metadata.clone(),
                    )
                }
            }
            PackedNode::Term(_) => Rc::clone(&term),
            PackedNode::Production {
                production,
                children,
                metadata,
            } => {
                let factored_children = children
                    .iter()
                    .map(|child| self.factor_packed_ambiguities(Rc::clone(child), memo))
                    .collect::<Vec<_>>();
                if factored_children
                    .iter()
                    .zip(children)
                    .all(|(factored, original)| Rc::ptr_eq(factored, original))
                {
                    Rc::clone(&term)
                } else {
                    PackedTerm::production(*production, factored_children, metadata.clone())
                }
            }
            PackedNode::Ambiguity(alternatives) => {
                let mut flattened = BTreeSet::new();
                for alternative in alternatives {
                    let alternative = self.factor_packed_ambiguities(Rc::clone(alternative), memo);
                    match &alternative.node {
                        PackedNode::Ambiguity(nested) => {
                            flattened.extend(nested.iter().cloned());
                        }
                        _ => {
                            flattened.insert(alternative);
                        }
                    }
                }
                let factored = self.factor_packed_production_alternatives(flattened, memo);
                if matches!(
                    &factored.node,
                    PackedNode::Ambiguity(factored_alternatives)
                        if packed_sets_share_nodes(factored_alternatives, alternatives)
                ) {
                    Rc::clone(&term)
                } else {
                    factored
                }
            }
        };
        // Retain the input allocation as part of the entry. Factoring recursively creates
        // temporary ambiguity nodes; allowing one to drop while its raw address remains a key
        // would let a later allocation reuse the address and receive the wrong cached result.
        memo.insert(identity, (term, Rc::clone(&factored)));
        factored
    }

    fn factor_packed_production_alternatives(
        &self,
        alternatives: BTreeSet<Rc<PackedTerm>>,
        memo: &mut HashMap<*const PackedTerm, (Rc<PackedTerm>, Rc<PackedTerm>)>,
    ) -> Rc<PackedTerm> {
        if alternatives.len() <= 1 {
            return PackedTerm::ambiguity(alternatives);
        }
        let Some(first) = alternatives
            .iter()
            .min_by(|left, right| cmp_packed_structurally(left, right))
        else {
            return PackedTerm::ambiguity(alternatives);
        };
        let PackedNode::Production {
            production,
            children,
            metadata,
        } = &first.node
        else {
            if let PackedNode::InstantiatedProduction {
                production,
                parameters,
                children,
                metadata,
            } = &first.node
            {
                let production = *production;
                let parameters = parameters.clone();
                let children = children.clone();
                let metadata = metadata.clone();
                if !alternatives.iter().all(|alternative| {
                    matches!(
                        &alternative.node,
                        PackedNode::InstantiatedProduction {
                            production: candidate,
                            parameters: candidate_parameters,
                            children: candidate_children,
                            ..
                        } if *candidate == production
                            && candidate_parameters == &parameters
                            && candidate_children.len() == children.len()
                    )
                }) {
                    return PackedTerm::ambiguity(alternatives);
                }
                let differing = (0..children.len())
                    .filter(|index| {
                        alternatives.iter().any(|alternative| {
                            let PackedNode::InstantiatedProduction {
                                children: candidate_children,
                                ..
                            } = &alternative.node
                            else {
                                unreachable!()
                            };
                            candidate_children[*index] != children[*index]
                        })
                    })
                    .collect::<Vec<_>>();
                let [index] = differing.as_slice() else {
                    return PackedTerm::ambiguity(alternatives);
                };
                let mut factored_children = children;
                let child_alternatives = alternatives
                    .iter()
                    .map(|alternative| {
                        let PackedNode::InstantiatedProduction {
                            children: candidate_children,
                            ..
                        } = &alternative.node
                        else {
                            unreachable!()
                        };
                        Rc::clone(&candidate_children[*index])
                    })
                    .collect();
                factored_children[*index] =
                    self.factor_packed_ambiguities(PackedTerm::ambiguity(child_alternatives), memo);
                return PackedTerm::instantiated_production(
                    production,
                    parameters,
                    factored_children,
                    metadata,
                );
            }
            return PackedTerm::ambiguity(alternatives);
        };
        if !alternatives.iter().all(|alternative| {
            matches!(
                &alternative.node,
                PackedNode::Production {
                    production: candidate,
                    children: candidate_children,
                    ..
                } if candidate == production
                    && candidate_children.len() == children.len()
            )
        }) {
            return PackedTerm::ambiguity(alternatives);
        }
        let differing = (0..children.len())
            .filter(|index| {
                alternatives.iter().any(|alternative| {
                    let PackedNode::Production {
                        children: candidate_children,
                        ..
                    } = &alternative.node
                    else {
                        unreachable!()
                    };
                    candidate_children[*index] != children[*index]
                })
            })
            .collect::<Vec<_>>();
        let [index] = differing.as_slice() else {
            return PackedTerm::ambiguity(alternatives);
        };
        let mut factored_children = children.clone();
        let child_alternatives = alternatives
            .iter()
            .map(|alternative| {
                let PackedNode::Production {
                    children: candidate_children,
                    ..
                } = &alternative.node
                else {
                    unreachable!()
                };
                Rc::clone(&candidate_children[*index])
            })
            .collect();
        factored_children[*index] =
            self.factor_packed_ambiguities(PackedTerm::ambiguity(child_alternatives), memo);
        PackedTerm::production(*production, factored_children, metadata.clone())
    }

    pub(super) fn filter_or_defer_packed_priority(
        &self,
        term: Rc<PackedTerm>,
    ) -> Result<Rc<PackedTerm>, ParseError> {
        match self.filter_packed_priority(Rc::clone(&term)) {
            Ok(term) => Ok(term),
            // A locally invalid nested rewrite/sequence/let may be the losing view of an
            // ambiguity whose sibling has that operation at the root. Retain only those failures
            // until the packed root preference can select the sibling.
            Err(ParseError::Scope { child, .. })
                if matches!(child.as_str(), "#KRewrite" | "#KSequence" | "#let") =>
            {
                Ok(term)
            }
            Err(error) => Err(error),
        }
    }

    pub(super) fn filter_packed_priority(
        &self,
        term: Rc<PackedTerm>,
    ) -> Result<Rc<PackedTerm>, ParseError> {
        self.filter_packed_priority_memo(term, &mut HashMap::new(), &mut HashMap::new())
    }

    fn filter_packed_priority_memo(
        &self,
        term: Rc<PackedTerm>,
        memo: &mut PackedTransformMemo,
        child_memo: &mut PackedPriorityChildMemo,
    ) -> Result<Rc<PackedTerm>, ParseError> {
        let identity = Rc::as_ptr(&term);
        if let Some((_, filtered)) = memo.get(&identity) {
            return filtered.clone();
        }
        #[cfg(test)]
        super::PACKED_PRIORITY_COMPUTATIONS.set(super::PACKED_PRIORITY_COMPUTATIONS.get() + 1);
        let filtered = (|| -> PackedTransformResult {
            match &term.node {
                PackedNode::InstantiatedProduction { .. } => {
                    unreachable!("instantiated productions are created after packed priority")
                }
                PackedNode::Term(_) => Ok(Rc::clone(&term)),
                PackedNode::Ambiguity(original_alternatives) => {
                    let mut alternatives = original_alternatives.clone();
                    for preferred in ["#KRewrite", "#KSequence", "#let"] {
                        let matching = alternatives
                            .iter()
                            .filter(|alternative| {
                                self.packed_top_parse_label(alternative) == Some(preferred)
                            })
                            .cloned()
                            .collect::<BTreeSet<_>>();
                        if !matching.is_empty() {
                            alternatives = matching;
                        }
                    }
                    let mut retained = BTreeSet::new();
                    let mut errors = Vec::new();
                    for alternative in alternatives {
                        match self.filter_packed_priority_memo(
                            Rc::clone(&alternative),
                            memo,
                            child_memo,
                        ) {
                            Ok(alternative) => match &alternative.node {
                                PackedNode::Ambiguity(nested) => {
                                    retained.extend(nested.iter().cloned())
                                }
                                _ => {
                                    retained.insert(alternative);
                                }
                            },
                            Err(error) => {
                                errors.push((alternative, error));
                            }
                        }
                    }
                    if retained.is_empty() {
                        Err(canonical_packed_error(errors))
                    } else if packed_sets_share_nodes(&retained, original_alternatives) {
                        Ok(Rc::clone(&term))
                    } else {
                        Ok(PackedTerm::ambiguity(retained))
                    }
                }
                PackedNode::Production {
                    production,
                    children,
                    metadata,
                } => {
                    let descriptor = &self.productions[*production];
                    let checked = if descriptor.record.is_some() || descriptor.syntactic_subsort {
                        BTreeSet::new()
                    } else {
                        descriptor.apply_priority.clone().unwrap_or_else(|| {
                            let mut positions = BTreeSet::new();
                            if matches!(descriptor.items.first(), Some(Item::NonTerminal(_))) {
                                positions.insert(1);
                            }
                            if matches!(descriptor.items.last(), Some(Item::NonTerminal(_))) {
                                positions.insert(children.len());
                            }
                            positions
                        })
                    };
                    let child_count = children.len();
                    let filtered_children = children
                        .iter()
                        .enumerate()
                        .map(|(index, child)| {
                            let position = index + 1;
                            let side = checked.contains(&position).then(|| {
                                if position == 1
                                    && matches!(
                                        descriptor.items.first(),
                                        Some(Item::NonTerminal(_))
                                    )
                                {
                                    Side::Left
                                } else if position == child_count
                                    && matches!(descriptor.items.last(), Some(Item::NonTerminal(_)))
                                {
                                    Side::Right
                                } else {
                                    Side::Middle
                                }
                            });
                            self.filter_packed_priority_child(
                                *production,
                                Rc::clone(child),
                                side,
                                memo,
                                child_memo,
                            )
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    if filtered_children
                        .iter()
                        .zip(children)
                        .all(|(filtered, original)| Rc::ptr_eq(filtered, original))
                    {
                        Ok(Rc::clone(&term))
                    } else {
                        Ok(PackedTerm::production(
                            *production,
                            filtered_children,
                            metadata.clone(),
                        ))
                    }
                }
            }
        })();
        memo.insert(identity, (Rc::clone(&term), filtered.clone()));
        filtered
    }

    fn packed_top_parse_label<'a>(&'a self, term: &'a PackedTerm) -> Option<&'a str> {
        let PackedNode::Production {
            production,
            children,
            ..
        } = &term.node
        else {
            return None;
        };
        let descriptor = &self.productions[*production];
        descriptor.parse_label.as_deref().or_else(|| {
            if descriptor.syntactic_subsort
                || (descriptor.parse_label.is_none() && children.len() == 1)
            {
                children
                    .first()
                    .and_then(|child| self.packed_top_parse_label(child))
            } else {
                None
            }
        })
    }

    fn filter_packed_priority_child(
        &self,
        parent: usize,
        child: Rc<PackedTerm>,
        side: Option<Side>,
        memo: &mut PackedTransformMemo,
        child_memo: &mut PackedPriorityChildMemo,
    ) -> Result<Rc<PackedTerm>, ParseError> {
        let identity = Rc::as_ptr(&child);
        let key = (identity, parent, side);
        if let Some((_, filtered)) = child_memo.get(&key) {
            return filtered.clone();
        }
        let filtered = self.filter_packed_priority_child_uncached(
            parent,
            Rc::clone(&child),
            side,
            memo,
            child_memo,
        );
        child_memo.insert(key, (child, filtered.clone()));
        filtered
    }

    fn filter_packed_priority_child_uncached(
        &self,
        parent: usize,
        child: Rc<PackedTerm>,
        side: Option<Side>,
        memo: &mut PackedTransformMemo,
        child_memo: &mut PackedPriorityChildMemo,
    ) -> Result<Rc<PackedTerm>, ParseError> {
        if let PackedNode::Ambiguity(alternatives) = &child.node {
            let mut retained = BTreeSet::new();
            let mut errors = Vec::new();
            for alternative in alternatives {
                match self.filter_packed_priority_child(
                    parent,
                    Rc::clone(alternative),
                    side,
                    memo,
                    child_memo,
                ) {
                    Ok(alternative) => match &alternative.node {
                        PackedNode::Ambiguity(nested) => retained.extend(nested.iter().cloned()),
                        _ => {
                            retained.insert(alternative);
                        }
                    },
                    Err(error) => {
                        errors.push((Rc::clone(alternative), error));
                    }
                }
            }
            return if retained.is_empty() {
                Err(canonical_packed_error(errors))
            } else if packed_sets_share_nodes(&retained, alternatives) {
                Ok(child)
            } else {
                Ok(PackedTerm::ambiguity(retained))
            };
        }
        if let Some(side) = side
            && let PackedNode::Production { production, .. } = &child.node
        {
            let shallow = ParsedTerm::Production {
                production: *production,
                children: Vec::new(),
                metadata: crate::kast::TermMetadata::default(),
            };
            if let Some(error) = self.child_violation(&self.productions[parent], &shallow, side) {
                return Err(error);
            }
        }
        self.filter_packed_priority_memo(child, memo, child_memo)
    }

    /// Prefer an ambiguous rewrite operand whose declared result exactly matches its concrete
    /// sibling. The polymorphic rewrite grammar otherwise widens both operands to `K`, retaining
    /// unrelated productions with identical surface syntax (for example Bytes and WordStack
    /// updates) after inference.
    pub(super) fn prefer_exact_packed_rewrite_sibling_sorts(
        &self,
        term: Rc<PackedTerm>,
    ) -> Rc<PackedTerm> {
        self.prefer_exact_packed_rewrite_sibling_sorts_memo(term, &mut HashMap::new())
    }

    fn prefer_exact_packed_rewrite_sibling_sorts_memo(
        &self,
        term: Rc<PackedTerm>,
        memo: &mut HashMap<*const PackedTerm, (Rc<PackedTerm>, Rc<PackedTerm>)>,
    ) -> Rc<PackedTerm> {
        let identity = Rc::as_ptr(&term);
        if let Some((_, preferred)) = memo.get(&identity) {
            return Rc::clone(preferred);
        }
        let mut preferred = match &term.node {
            PackedNode::InstantiatedProduction { .. } => {
                unreachable!("instantiated productions are created after packed rewrite preference")
            }
            PackedNode::Term(_) => Rc::clone(&term),
            PackedNode::Ambiguity(alternatives) => PackedTerm::ambiguity(
                alternatives
                    .iter()
                    .map(|alternative| {
                        self.prefer_exact_packed_rewrite_sibling_sorts_memo(
                            Rc::clone(alternative),
                            memo,
                        )
                    })
                    .collect(),
            ),
            PackedNode::Production {
                production,
                children,
                metadata,
            } => PackedTerm::production(
                *production,
                children
                    .iter()
                    .map(|child| {
                        self.prefer_exact_packed_rewrite_sibling_sorts_memo(Rc::clone(child), memo)
                    })
                    .collect(),
                metadata.clone(),
            ),
        };
        let PackedNode::Production {
            production,
            children,
            metadata,
        } = &preferred.node
        else {
            memo.insert(identity, (term, Rc::clone(&preferred)));
            return preferred;
        };
        if self.productions[*production]
            .label
            .as_ref()
            .is_some_and(|label| label.name == "#KRewrite")
            && children.len() == 2
        {
            let left_sort = self.declared_packed_term_sort(&children[0]);
            let right_sort = self.declared_packed_term_sort(&children[1]);
            let mut preferred_children = children.clone();
            if let Some(sort) = right_sort {
                preferred_children[0] =
                    self.prefer_packed_ambiguity_result_sort(&preferred_children[0], &sort);
            }
            if let Some(sort) = left_sort {
                preferred_children[1] =
                    self.prefer_packed_ambiguity_result_sort(&preferred_children[1], &sort);
            }
            preferred = PackedTerm::production(*production, preferred_children, metadata.clone());
        }
        memo.insert(identity, (term, Rc::clone(&preferred)));
        preferred
    }

    fn prefer_packed_ambiguity_result_sort(
        &self,
        term: &Rc<PackedTerm>,
        expected: &Sort,
    ) -> Rc<PackedTerm> {
        let PackedNode::Ambiguity(alternatives) = &term.node else {
            return Rc::clone(term);
        };
        let subsorts = crate::definition::PartialOrder::new(self.subsort_relations.iter().cloned())
            .expect("the grammar rejected semantic subsort cycles during construction");
        if alternatives.iter().any(|alternative| {
            self.declared_packed_term_sort(alternative)
                .is_some_and(|sort| {
                    sort != *expected
                        && (subsorts.less_than_eq(&sort, expected)
                            || subsorts.less_than_eq(expected, &sort))
                })
        }) {
            return Rc::clone(term);
        }
        let matching = alternatives
            .iter()
            .filter(|alternative| {
                self.declared_packed_term_sort(alternative).as_ref() == Some(expected)
            })
            .cloned()
            .collect::<BTreeSet<_>>();
        if matching.is_empty() {
            Rc::clone(term)
        } else {
            PackedTerm::ambiguity(matching)
        }
    }

    fn declared_packed_term_sort(&self, term: &PackedTerm) -> Option<Sort> {
        match &term.node {
            PackedNode::Production { production, .. } => {
                Some(self.productions[*production].result.clone())
            }
            PackedNode::InstantiatedProduction { .. } => {
                unreachable!("instantiated productions are created after rewrite preference")
            }
            PackedNode::Term(term) => match term.unannotated() {
                Term::Variable { sort, .. } => sort.clone(),
                Term::Token { sort, .. } => Some(sort.clone()),
                _ => term.metadata().and_then(|metadata| metadata.sort.clone()),
            },
            PackedNode::Ambiguity(_) => None,
        }
    }

    #[cfg(test)]
    pub(super) fn prefer_exact_rewrite_sibling_sorts(&self, term: ParsedTerm) -> ParsedTerm {
        let rebuilt = match term {
            ParsedTerm::Term(_) => return term,
            ParsedTerm::Ambiguity(alternatives) => ParsedTerm::Ambiguity(
                alternatives
                    .into_iter()
                    .map(|alternative| self.prefer_exact_rewrite_sibling_sorts(alternative))
                    .collect(),
            ),
            ParsedTerm::Production {
                production,
                children,
                metadata,
            } => ParsedTerm::Production {
                production,
                children: children
                    .into_iter()
                    .map(|child| self.prefer_exact_rewrite_sibling_sorts(child))
                    .collect(),
                metadata,
            },
            ParsedTerm::InstantiatedProduction {
                production,
                parameters,
                children,
                metadata,
            } => ParsedTerm::InstantiatedProduction {
                production,
                parameters,
                children: children
                    .into_iter()
                    .map(|child| self.prefer_exact_rewrite_sibling_sorts(child))
                    .collect(),
                metadata,
            },
        };
        let (production, children) = match &rebuilt {
            ParsedTerm::Production {
                production,
                children,
                ..
            }
            | ParsedTerm::InstantiatedProduction {
                production,
                children,
                ..
            } => (*production, children),
            ParsedTerm::Term(_) | ParsedTerm::Ambiguity(_) => return rebuilt,
        };
        if self.productions[production]
            .label
            .as_ref()
            .is_none_or(|label| label.name != "#KRewrite")
            || children.len() != 2
        {
            return rebuilt;
        }
        let left_sort = self.declared_term_sort(&children[0]);
        let right_sort = self.declared_term_sort(&children[1]);
        let mut rebuilt = rebuilt;
        let children = match &mut rebuilt {
            ParsedTerm::Production { children, .. }
            | ParsedTerm::InstantiatedProduction { children, .. } => children,
            ParsedTerm::Term(_) | ParsedTerm::Ambiguity(_) => unreachable!(),
        };
        if let Some(sort) = right_sort {
            children[0] = self.prefer_ambiguity_result_sort(children[0].clone(), &sort);
        }
        if let Some(sort) = left_sort {
            children[1] = self.prefer_ambiguity_result_sort(children[1].clone(), &sort);
        }
        rebuilt
    }

    #[cfg(test)]
    fn prefer_ambiguity_result_sort(&self, term: ParsedTerm, expected: &Sort) -> ParsedTerm {
        let ParsedTerm::Ambiguity(alternatives) = term else {
            return term;
        };
        let subsorts = crate::definition::PartialOrder::new(self.subsort_relations.iter().cloned())
            .expect("the grammar rejected semantic subsort cycles during construction");
        if alternatives.iter().any(|alternative| {
            self.declared_term_sort(alternative).is_some_and(|sort| {
                sort != *expected
                    && (subsorts.less_than_eq(&sort, expected)
                        || subsorts.less_than_eq(expected, &sort))
            })
        }) {
            // Let whole-sentence inference choose between related result sorts. Constraints from
            // a rule condition can legitimately select a super-sort even when the rewrite's other
            // side has the exact subsort (for example an overloaded Gas function rewriting to 0).
            return ParsedTerm::Ambiguity(alternatives);
        }
        let matching = alternatives
            .iter()
            .filter(|alternative| self.declared_term_sort(alternative).as_ref() == Some(expected))
            .cloned()
            .collect::<BTreeSet<_>>();
        if matching.is_empty() {
            ParsedTerm::Ambiguity(alternatives)
        } else if matching.len() == 1 {
            matching.into_iter().next().expect("one alternative exists")
        } else {
            ParsedTerm::Ambiguity(matching)
        }
    }

    #[cfg(test)]
    fn declared_term_sort(&self, term: &ParsedTerm) -> Option<Sort> {
        match term {
            ParsedTerm::Production { production, .. } => {
                Some(self.productions[*production].result.clone())
            }
            ParsedTerm::InstantiatedProduction {
                production,
                parameters,
                ..
            } => {
                let production = &self.productions[*production];
                let origin = production.parametric_origin.as_ref()?;
                let substitution = origin
                    .parameters
                    .iter()
                    .cloned()
                    .zip(parameters.iter().cloned())
                    .collect::<BTreeMap<_, _>>();
                Some(substitute_sort(&production.result, &substitution))
            }
            ParsedTerm::Term(term) => match term.unannotated() {
                Term::Variable { sort, .. } => sort.clone(),
                Term::Token { sort, .. } => Some(sort.clone()),
                _ => term.metadata().and_then(|metadata| metadata.sort.clone()),
            },
            ParsedTerm::Ambiguity(_) => None,
        }
    }

    /// Apply priority and associativity to every packed ambiguity branch.
    ///
    /// Java's `SetsTransformerWithErrors` removes only the invalid alternatives beneath an
    /// ambiguity. Treating a packed child as one opaque node either retained invalid associations
    /// or discarded valid siblings, so this transformation performs the same branch-wise filter.
    /// This owned pass remains necessary after generated record productions collapse and expose
    /// edges which their parser-only wrappers deliberately exempt from priority checking.
    #[cfg(test)]
    pub(super) fn filter_priority(&self, term: ParsedTerm) -> Result<ParsedTerm, ParseError> {
        match term {
            ParsedTerm::Term(_) => Ok(term),
            ParsedTerm::Ambiguity(mut alternatives) => {
                // Java's PriorityVisitor gives these three structural forms precedence over
                // every other top-level interpretation, in this order. This is what makes
                // `lhs => rhs #And condition` scope as a rewrite whose RHS contains `#And`
                // instead of retaining the competing `#And(rewrite(lhs, rhs), condition)` tree.
                for preferred in ["#KRewrite", "#KSequence", "#let"] {
                    let matching = alternatives
                        .iter()
                        .filter(|alternative| self.top_parse_label(alternative) == Some(preferred))
                        .cloned()
                        .collect::<BTreeSet<_>>();
                    if !matching.is_empty() {
                        alternatives = matching;
                    }
                }
                let mut retained = BTreeSet::new();
                let mut first_error = None;
                for alternative in alternatives {
                    match self.filter_priority(alternative) {
                        Ok(ParsedTerm::Ambiguity(nested)) => retained.extend(nested),
                        Ok(alternative) => {
                            retained.insert(alternative);
                        }
                        Err(error) => {
                            first_error.get_or_insert(error);
                        }
                    }
                }
                match retained.len() {
                    0 => Err(first_error.expect("an empty ambiguity had no valid alternative")),
                    1 => Ok(retained.pop_first().expect("length was one")),
                    _ => Ok(ParsedTerm::Ambiguity(retained)),
                }
            }
            ParsedTerm::Production {
                production,
                children,
                metadata,
            } => {
                let descriptor = &self.productions[production];
                let checked = if descriptor.record.is_some() || descriptor.syntactic_subsort {
                    BTreeSet::new()
                } else {
                    descriptor.apply_priority.clone().unwrap_or_else(|| {
                        let mut positions = BTreeSet::new();
                        if matches!(descriptor.items.first(), Some(Item::NonTerminal(_))) {
                            positions.insert(1);
                        }
                        if matches!(descriptor.items.last(), Some(Item::NonTerminal(_))) {
                            positions.insert(children.len());
                        }
                        positions
                    })
                };
                let child_count = children.len();
                let children = children
                    .into_iter()
                    .enumerate()
                    .map(|(index, child)| {
                        let position = index + 1;
                        let side = checked.contains(&position).then(|| {
                            if position == 1
                                && matches!(descriptor.items.first(), Some(Item::NonTerminal(_)))
                            {
                                Side::Left
                            } else if position == child_count
                                && matches!(descriptor.items.last(), Some(Item::NonTerminal(_)))
                            {
                                Side::Right
                            } else {
                                Side::Middle
                            }
                        });
                        self.filter_priority_child(descriptor, child, side)
                    })
                    .collect::<Result<_, _>>()?;
                Ok(ParsedTerm::Production {
                    production,
                    children,
                    metadata,
                })
            }
            ParsedTerm::InstantiatedProduction { .. } => {
                unreachable!("instantiated productions are created after priority filtering")
            }
        }
    }

    #[cfg(test)]
    fn top_parse_label<'a>(&'a self, term: &'a ParsedTerm) -> Option<&'a str> {
        let (production, children) = match term {
            ParsedTerm::Production {
                production,
                children,
                ..
            }
            | ParsedTerm::InstantiatedProduction {
                production,
                children,
                ..
            } => (*production, children),
            ParsedTerm::Term(_) | ParsedTerm::Ambiguity(_) => return None,
        };
        let descriptor = &self.productions[production];
        descriptor.parse_label.as_deref().or_else(|| {
            if descriptor.syntactic_subsort
                || (descriptor.parse_label.is_none() && children.len() == 1)
            {
                children
                    .first()
                    .and_then(|child| self.top_parse_label(child))
            } else {
                None
            }
        })
    }

    #[cfg(test)]
    fn filter_priority_child(
        &self,
        parent: &Production,
        child: ParsedTerm,
        side: Option<Side>,
    ) -> Result<ParsedTerm, ParseError> {
        if let ParsedTerm::Ambiguity(alternatives) = child {
            let mut retained = BTreeSet::new();
            let mut first_error = None;
            for alternative in alternatives {
                match self.filter_priority_child(parent, alternative, side) {
                    Ok(ParsedTerm::Ambiguity(nested)) => retained.extend(nested),
                    Ok(alternative) => {
                        retained.insert(alternative);
                    }
                    Err(error) => {
                        first_error.get_or_insert(error);
                    }
                }
            }
            return match retained.len() {
                0 => Err(first_error.expect("an empty ambiguity had no valid alternative")),
                1 => Ok(retained.pop_first().expect("length was one")),
                _ => Ok(ParsedTerm::Ambiguity(retained)),
            };
        }
        if let Some(side) = side
            && let Some(error) = self.child_violation(parent, &child, side)
        {
            return Err(error);
        }
        self.filter_priority(child)
    }

    fn child_violation(
        &self,
        parent: &Production,
        child: &ParsedTerm,
        side: Side,
    ) -> Option<ParseError> {
        let ParsedTerm::Production {
            production: child, ..
        } = child
        else {
            return None;
        };
        let child = &self.productions[*child];
        let (Some(parent_label), Some(child_label)) = (&parent.parse_label, &child.parse_label)
        else {
            return None;
        };
        let allowed_parent = |exceptions: &[&str]| {
            parent.syntactic_subsort || exceptions.contains(&parent_label.as_str())
        };
        if child_label == "#KRewrite"
            && !allowed_parent(&[
                "#ruleRequires",
                "#ruleEnsures",
                "#ruleRequiresEnsures",
                "#KRewrite",
                "#withConfig",
                "#KList",
            ])
        {
            return Some(ParseError::Scope {
                parent: parent_label.clone(),
                child: child_label.clone(),
            });
        }
        if child_label == "#KSequence"
            && !allowed_parent(&[
                "#ruleRequires",
                "#ruleEnsures",
                "#ruleRequiresEnsures",
                "#KRewrite",
                "#KSequence",
                "#KList",
            ])
        {
            return Some(ParseError::Scope {
                parent: parent_label.clone(),
                child: child_label.clone(),
            });
        }
        if child_label == "#let"
            && !allowed_parent(&[
                "#ruleRequires",
                "#ruleEnsures",
                "#ruleRequiresEnsures",
                "#KRewrite",
                "#KSequence",
                "#let",
                "#KList",
            ])
        {
            return Some(ParseError::Scope {
                parent: parent_label.clone(),
                child: child_label.clone(),
            });
        }
        if (parent_label == "#SyntacticCast" || parent_label.starts_with("#SemanticCastTo"))
            && matches!(child.items.last(), Some(Item::NonTerminal(_)))
        {
            return Some(ParseError::CastPriority {
                cast: parent_label.clone(),
                child: child_label.clone(),
            });
        }
        if self.priorities.less_than(parent_label, child_label) {
            return Some(ParseError::Priority {
                parent: parent_label.clone(),
                child: child_label.clone(),
            });
        }
        if side == Side::Right
            && self
                .associativities
                .left
                .contains(&(parent_label.clone(), child_label.clone()))
        {
            return Some(ParseError::Associativity {
                parent: parent_label.clone(),
                child: child_label.clone(),
                side: "right",
            });
        }
        if side == Side::Left
            && self
                .associativities
                .right
                .contains(&(parent_label.clone(), child_label.clone()))
        {
            return Some(ParseError::Associativity {
                parent: parent_label.clone(),
                child: child_label.clone(),
                side: "left",
            });
        }
        None
    }

    pub(super) fn lower(&self, term: ParsedTerm) -> Term {
        match term {
            ParsedTerm::Term(term) => term,
            ParsedTerm::Production {
                production,
                children,
                mut metadata,
            } => {
                let production = &self.productions[production];
                metadata.production = production
                    .source_production
                    .map(|production| crate::kast::ResolvedProductionId(production.0));
                let children = children
                    .into_iter()
                    .map(|child| self.lower(child))
                    .collect::<Vec<_>>();
                lower_term(production, &children).with_metadata(metadata)
            }
            ParsedTerm::InstantiatedProduction {
                production,
                parameters,
                children,
                mut metadata,
            } => {
                let production = &self.productions[production];
                metadata.production = production
                    .source_production
                    .map(|production| crate::kast::ResolvedProductionId(production.0));
                let children = children
                    .into_iter()
                    .map(|child| self.lower(child))
                    .collect::<Vec<_>>();
                let mut instantiated = production.clone();
                if let Some(label) = &mut instantiated.label {
                    label.parameters = parameters;
                }
                lower_term(&instantiated, &children).with_metadata(metadata)
            }
            ParsedTerm::Ambiguity(_) => {
                unreachable!("ambiguities are rejected before lowering to KAST")
            }
        }
    }

    /// Remove the concrete grouping nodes discarded by Scala's final
    /// `RemoveBracketVisitor`, while retaining semantic and outer casts.
    pub(super) fn remove_brackets_and_syntactic_casts(&self, term: ParsedTerm) -> ParsedTerm {
        match term {
            ParsedTerm::Term(_) => term,
            ParsedTerm::Ambiguity(alternatives) => ParsedTerm::Ambiguity(
                alternatives
                    .into_iter()
                    .map(|alternative| self.remove_brackets_and_syntactic_casts(alternative))
                    .collect(),
            ),
            ParsedTerm::Production {
                production,
                mut children,
                metadata,
            } => {
                let descriptor = &self.productions[production];
                let syntactic_cast = descriptor.label.as_ref().is_some_and(|label| {
                    matches!(
                        label.name.as_str(),
                        "#SyntacticCast" | "#SyntacticCastBraced"
                    )
                });
                if (descriptor.bracket || syntactic_cast) && children.len() == 1 {
                    return self.remove_brackets_and_syntactic_casts(children.remove(0));
                }
                ParsedTerm::Production {
                    production,
                    metadata,
                    children: children
                        .into_iter()
                        .map(|child| self.remove_brackets_and_syntactic_casts(child))
                        .collect(),
                }
            }
            ParsedTerm::InstantiatedProduction {
                production,
                parameters,
                mut children,
                metadata,
            } => {
                let descriptor = &self.productions[production];
                let syntactic_cast = descriptor.label.as_ref().is_some_and(|label| {
                    matches!(
                        label.name.as_str(),
                        "#SyntacticCast" | "#SyntacticCastBraced"
                    )
                });
                if (descriptor.bracket || syntactic_cast) && children.len() == 1 {
                    return self.remove_brackets_and_syntactic_casts(children.remove(0));
                }
                ParsedTerm::InstantiatedProduction {
                    production,
                    parameters,
                    metadata,
                    children: children
                        .into_iter()
                        .map(|child| self.remove_brackets_and_syntactic_casts(child))
                        .collect(),
                }
            }
        }
    }

    /// Resolve `#KApply` nodes to every visible production with the same label and arity.
    pub(super) fn resolve_packed_applications(
        &self,
        term: Rc<PackedTerm>,
    ) -> Result<Rc<PackedTerm>, ParseError> {
        self.resolve_packed_applications_memo(term, &mut HashMap::new())
    }

    fn resolve_packed_applications_memo(
        &self,
        term: Rc<PackedTerm>,
        memo: &mut PackedTransformMemo,
    ) -> Result<Rc<PackedTerm>, ParseError> {
        let identity = Rc::as_ptr(&term);
        if let Some((_, resolved)) = memo.get(&identity) {
            return resolved.clone();
        }
        let resolved = (|| -> PackedTransformResult {
            match &term.node {
                PackedNode::InstantiatedProduction { .. } => {
                    unreachable!(
                        "instantiated productions are created after application resolution"
                    )
                }
                PackedNode::Term(_) => Ok(Rc::clone(&term)),
                PackedNode::Ambiguity(alternatives) => {
                    let mut resolved = BTreeSet::new();
                    let mut first_error = None;
                    for alternative in packed_terms_in_structural_order(alternatives) {
                        match self.resolve_packed_applications_memo(Rc::clone(&alternative), memo) {
                            Ok(alternative) => match &alternative.node {
                                PackedNode::Ambiguity(nested) => {
                                    resolved.extend(nested.iter().cloned())
                                }
                                _ => {
                                    resolved.insert(alternative);
                                }
                            },
                            Err(error) => {
                                first_error.get_or_insert(error);
                            }
                        }
                        if resolved.len() > super::MAX_DERIVATIONS_PER_STATE {
                            return Err(ParseError::TooManyParses {
                                limit: super::MAX_DERIVATIONS_PER_STATE,
                            });
                        }
                    }
                    if resolved.is_empty() {
                        Err(first_error.expect("an empty ambiguity had no resolution result"))
                    } else {
                        Ok(PackedTerm::ambiguity(resolved))
                    }
                }
                PackedNode::Production {
                    production,
                    children,
                    metadata,
                } => {
                    #[cfg(test)]
                    if self.productions[*production]
                        .label
                        .as_ref()
                        .is_some_and(|label| label.name == "#KApply")
                    {
                        super::PACKED_APPLICATION_RESOLUTIONS
                            .set(super::PACKED_APPLICATION_RESOLUTIONS.get() + 1);
                    }
                    let children = children
                        .iter()
                        .map(|child| self.resolve_packed_applications_memo(Rc::clone(child), memo))
                        .collect::<Result<Vec<_>, _>>()?;
                    if self.productions[*production]
                        .label
                        .as_ref()
                        .map(|label| label.name.as_str())
                        != Some("#KApply")
                    {
                        Ok(PackedTerm::production(
                            *production,
                            children,
                            metadata.clone(),
                        ))
                    } else {
                        let [label, arguments] = children.as_slice() else {
                            return Err(ParseError::UnknownApplication {
                                label: "<malformed>".into(),
                                arity: children.len().saturating_sub(1),
                            });
                        };
                        let label = packed_klabel_name(label).ok_or_else(|| {
                            ParseError::UnknownApplication {
                                label: "<malformed>".into(),
                                arity: 0,
                            }
                        })?;
                        let argument_lists = self.flatten_packed_klist(arguments)?;
                        let arities = argument_lists.iter().map(Vec::len).collect::<BTreeSet<_>>();
                        let mut candidates = BTreeSet::new();
                        for arguments in argument_lists {
                            for (candidate, candidate_production) in
                                self.productions.iter().enumerate()
                            {
                                if candidate != *production
                                    && candidate_production.record.is_none()
                                    && candidate_production.label.as_ref().is_some_and(
                                        |candidate_label| candidate_label.name == label,
                                    )
                                    && production_arity(candidate_production) == arguments.len()
                                {
                                    let candidate =
                                        candidate_production.term_production.unwrap_or(candidate);
                                    let mut candidate_metadata = metadata.clone();
                                    candidate_metadata.production = self.productions[candidate]
                                        .source_production
                                        .map(|production| {
                                            crate::kast::ResolvedProductionId(production.0)
                                        });
                                    candidates.insert(PackedTerm::production(
                                        candidate,
                                        arguments.clone(),
                                        candidate_metadata,
                                    ));
                                    if candidates.len() > super::MAX_DERIVATIONS_PER_STATE {
                                        return Err(ParseError::TooManyParses {
                                            limit: super::MAX_DERIVATIONS_PER_STATE,
                                        });
                                    }
                                }
                            }
                        }
                        if candidates.is_empty() {
                            Err(ParseError::UnknownApplication {
                                label,
                                arity: arities.first().copied().unwrap_or(0),
                            })
                        } else {
                            Ok(PackedTerm::ambiguity(candidates))
                        }
                    }
                }
            }
        })();
        memo.insert(identity, (term, resolved.clone()));
        resolved
    }

    fn flatten_packed_klist(
        &self,
        term: &Rc<PackedTerm>,
    ) -> Result<Vec<Vec<Rc<PackedTerm>>>, ParseError> {
        let flattened = match &term.node {
            PackedNode::InstantiatedProduction { .. } => {
                unreachable!("instantiated productions are created after K-list flattening")
            }
            PackedNode::Ambiguity(alternatives) => {
                let mut flattened = Vec::new();
                for alternative in packed_terms_in_structural_order(alternatives) {
                    flattened.extend(self.flatten_packed_klist(&alternative)?);
                    if flattened.len() > super::MAX_DERIVATIONS_PER_STATE {
                        return Err(ParseError::TooManyParses {
                            limit: super::MAX_DERIVATIONS_PER_STATE,
                        });
                    }
                }
                flattened
            }
            PackedNode::Production {
                production,
                children,
                ..
            } => match self.productions[*production]
                .label
                .as_ref()
                .map(|label| label.name.as_str())
            {
                Some("#EmptyKList") => vec![Vec::new()],
                Some("#KList") if children.len() == 2 => {
                    let left = self.flatten_packed_klist(&children[0])?;
                    let right = self.flatten_packed_klist(&children[1])?;
                    left.into_iter()
                        .flat_map(|left| {
                            right.iter().map(move |right| {
                                let mut combined = left.clone();
                                combined.extend(right.iter().cloned());
                                combined
                            })
                        })
                        .take(super::MAX_DERIVATIONS_PER_STATE + 1)
                        .collect()
                }
                _ => vec![vec![Rc::clone(term)]],
            },
            PackedNode::Term(_) => vec![vec![Rc::clone(term)]],
        };
        if flattened.len() > super::MAX_DERIVATIONS_PER_STATE {
            Err(ParseError::TooManyParses {
                limit: super::MAX_DERIVATIONS_PER_STATE,
            })
        } else {
            Ok(flattened)
        }
    }

    #[cfg(test)]
    pub(super) fn resolve_applications(&self, term: ParsedTerm) -> Result<ParsedTerm, ParseError> {
        match term {
            ParsedTerm::Term(_) => Ok(term),
            ParsedTerm::Ambiguity(alternatives) => {
                let mut resolved = BTreeSet::new();
                let mut first_error = None;
                for alternative in alternatives {
                    match self.resolve_applications(alternative) {
                        Ok(ParsedTerm::Ambiguity(nested)) => resolved.extend(nested),
                        Ok(alternative) => {
                            resolved.insert(alternative);
                        }
                        Err(error) => {
                            first_error.get_or_insert(error);
                        }
                    }
                    if resolved.len() > super::MAX_DERIVATIONS_PER_STATE {
                        return Err(ParseError::TooManyParses {
                            limit: super::MAX_DERIVATIONS_PER_STATE,
                        });
                    }
                }
                match resolved.len() {
                    0 => Err(first_error.expect("an empty ambiguity had no resolution result")),
                    1 => Ok(resolved.pop_first().expect("length was one")),
                    _ => Ok(ParsedTerm::Ambiguity(resolved)),
                }
            }
            ParsedTerm::Production {
                production,
                children,
                metadata,
            } => {
                let children = children
                    .into_iter()
                    .map(|child| self.resolve_applications(child))
                    .collect::<Result<Vec<_>, _>>()?;
                if self.productions[production]
                    .label
                    .as_ref()
                    .map(|label| label.name.as_str())
                    != Some("#KApply")
                {
                    return Ok(ParsedTerm::Production {
                        production,
                        children,
                        metadata,
                    });
                }
                let [label, arguments] = children.as_slice() else {
                    return Err(ParseError::UnknownApplication {
                        label: "<malformed>".into(),
                        arity: children.len().saturating_sub(1),
                    });
                };
                let label = klabel_name(label).ok_or_else(|| ParseError::UnknownApplication {
                    label: "<malformed>".into(),
                    arity: 0,
                })?;
                let argument_lists = self.flatten_klist(arguments)?;
                let arities = argument_lists.iter().map(Vec::len).collect::<BTreeSet<_>>();
                let mut candidates = BTreeSet::new();
                for arguments in argument_lists {
                    for (candidate, candidate_production) in self.productions.iter().enumerate() {
                        if candidate != production
                            && candidate_production.record.is_none()
                            && candidate_production
                                .label
                                .as_ref()
                                .is_some_and(|candidate_label| candidate_label.name == label)
                            && production_arity(candidate_production) == arguments.len()
                        {
                            let candidate =
                                candidate_production.term_production.unwrap_or(candidate);
                            let mut candidate_metadata = metadata.clone();
                            candidate_metadata.production = self.productions[candidate]
                                .source_production
                                .map(|production| crate::kast::ResolvedProductionId(production.0));
                            candidates.insert(ParsedTerm::Production {
                                production: candidate,
                                children: arguments.clone(),
                                metadata: candidate_metadata,
                            });
                            if candidates.len() > super::MAX_DERIVATIONS_PER_STATE {
                                return Err(ParseError::TooManyParses {
                                    limit: super::MAX_DERIVATIONS_PER_STATE,
                                });
                            }
                        }
                    }
                }
                match candidates.len() {
                    0 => Err(ParseError::UnknownApplication {
                        label,
                        arity: arities.first().copied().unwrap_or(0),
                    }),
                    1 => Ok(candidates.pop_first().expect("length was one")),
                    _ => Ok(ParsedTerm::Ambiguity(candidates)),
                }
            }
            ParsedTerm::InstantiatedProduction { .. } => {
                unreachable!("applications are resolved before sort inference")
            }
        }
    }

    #[cfg(test)]
    fn flatten_klist(&self, term: &ParsedTerm) -> Result<Vec<Vec<ParsedTerm>>, ParseError> {
        let flattened = match term {
            ParsedTerm::Ambiguity(alternatives) => {
                let mut flattened = Vec::new();
                for alternative in alternatives {
                    flattened.extend(self.flatten_klist(alternative)?);
                    if flattened.len() > super::MAX_DERIVATIONS_PER_STATE {
                        return Err(ParseError::TooManyParses {
                            limit: super::MAX_DERIVATIONS_PER_STATE,
                        });
                    }
                }
                flattened
            }
            ParsedTerm::Production {
                production,
                children,
                ..
            } => match self.productions[*production]
                .label
                .as_ref()
                .map(|label| label.name.as_str())
            {
                Some("#EmptyKList") => vec![Vec::new()],
                Some("#KList") if children.len() == 2 => {
                    let left = self.flatten_klist(&children[0])?;
                    let right = self.flatten_klist(&children[1])?;
                    left.into_iter()
                        .flat_map(|left| {
                            right.iter().map(move |right| {
                                let mut combined = left.clone();
                                combined.extend(right.iter().cloned());
                                combined
                            })
                        })
                        .take(super::MAX_DERIVATIONS_PER_STATE + 1)
                        .collect()
                }
                _ => vec![vec![term.clone()]],
            },
            ParsedTerm::Term(_) => vec![vec![term.clone()]],
            ParsedTerm::InstantiatedProduction { .. } => {
                unreachable!("K lists are flattened before sort inference")
            }
        };
        if flattened.len() > super::MAX_DERIVATIONS_PER_STATE {
            Err(ParseError::TooManyParses {
                limit: super::MAX_DERIVATIONS_PER_STATE,
            })
        } else {
            Ok(flattened)
        }
    }

    /// Factor alternatives with a shared production into one differing child.
    pub(super) fn factor_ambiguities(&self, term: ParsedTerm) -> ParsedTerm {
        match term {
            ParsedTerm::Term(_) => term,
            ParsedTerm::Production {
                production,
                children,
                metadata,
            } => ParsedTerm::Production {
                production,
                metadata,
                children: children
                    .into_iter()
                    .map(|child| self.factor_ambiguities(child))
                    .collect(),
            },
            ParsedTerm::InstantiatedProduction {
                production,
                parameters,
                children,
                metadata,
            } => ParsedTerm::InstantiatedProduction {
                production,
                parameters,
                metadata,
                children: children
                    .into_iter()
                    .map(|child| self.factor_ambiguities(child))
                    .collect(),
            },
            ParsedTerm::Ambiguity(alternatives) => {
                let mut flattened = BTreeSet::new();
                for alternative in alternatives {
                    match self.factor_ambiguities(alternative) {
                        ParsedTerm::Ambiguity(nested) => flattened.extend(nested),
                        alternative => {
                            flattened.insert(alternative);
                        }
                    }
                }
                let mut alternatives = flattened;
                if alternatives.len() == 1 {
                    return alternatives.pop_first().expect("length was one");
                }
                if let Some(ParsedTerm::InstantiatedProduction {
                    production,
                    parameters,
                    children,
                    metadata,
                }) = alternatives.first()
                {
                    let production = *production;
                    let parameters = parameters.clone();
                    let children = children.clone();
                    let metadata = metadata.clone();
                    if !alternatives.iter().all(|alternative| {
                        matches!(
                            alternative,
                            ParsedTerm::InstantiatedProduction {
                                production: candidate,
                                parameters: candidate_parameters,
                                children: candidate_children,
                                ..
                            } if *candidate == production
                                && candidate_parameters == &parameters
                                && candidate_children.len() == children.len()
                        )
                    }) {
                        return ParsedTerm::Ambiguity(alternatives);
                    }
                    let differing = (0..children.len())
                        .filter(|index| {
                            alternatives.iter().any(|alternative| {
                                let ParsedTerm::InstantiatedProduction {
                                    children: candidate_children,
                                    ..
                                } = alternative
                                else {
                                    unreachable!()
                                };
                                candidate_children[*index] != children[*index]
                            })
                        })
                        .collect::<Vec<_>>();
                    let [index] = differing.as_slice() else {
                        return ParsedTerm::Ambiguity(alternatives);
                    };
                    let mut factored_children = children;
                    let child_alternatives = alternatives
                        .into_iter()
                        .map(|alternative| {
                            let ParsedTerm::InstantiatedProduction { mut children, .. } =
                                alternative
                            else {
                                unreachable!()
                            };
                            children.remove(*index)
                        })
                        .collect();
                    factored_children[*index] =
                        self.factor_ambiguities(ParsedTerm::Ambiguity(child_alternatives));
                    return ParsedTerm::InstantiatedProduction {
                        production,
                        parameters,
                        children: factored_children,
                        metadata,
                    };
                }
                let Some(ParsedTerm::Production {
                    production,
                    children,
                    metadata,
                }) = alternatives.first()
                else {
                    return ParsedTerm::Ambiguity(alternatives);
                };
                let production = *production;
                let children = children.clone();
                let metadata = metadata.clone();
                if !alternatives.iter().all(|alternative| {
                    matches!(
                        alternative,
                        ParsedTerm::Production {
                            production: candidate,
                            children: candidate_children,
                            ..
                        } if *candidate == production && candidate_children.len() == children.len()
                    )
                }) {
                    return ParsedTerm::Ambiguity(alternatives);
                }
                let differing = (0..children.len())
                    .filter(|index| {
                        alternatives.iter().any(|alternative| {
                            let ParsedTerm::Production {
                                children: candidate_children,
                                ..
                            } = alternative
                            else {
                                unreachable!()
                            };
                            candidate_children[*index] != children[*index]
                        })
                    })
                    .collect::<Vec<_>>();
                let [index] = differing.as_slice() else {
                    return ParsedTerm::Ambiguity(alternatives);
                };
                let mut factored_children = children;
                let child_alternatives = alternatives
                    .into_iter()
                    .map(|alternative| {
                        let ParsedTerm::Production { mut children, .. } = alternative else {
                            unreachable!()
                        };
                        children.remove(*index)
                    })
                    .collect();
                factored_children[*index] =
                    self.factor_ambiguities(ParsedTerm::Ambiguity(child_alternatives));
                ParsedTerm::Production {
                    production,
                    children: factored_children,
                    metadata,
                }
            }
        }
    }

    /// Resolve a nullary overloaded production to the unique least production
    /// with the same label, matching Scala's post-inference terminator pass.
    pub(super) fn resolve_overloaded_terminators(
        &self,
        term: ParsedTerm,
    ) -> Result<ParsedTerm, ParseError> {
        match term {
            ParsedTerm::Term(_) => Ok(term),
            ParsedTerm::Ambiguity(alternatives) => Ok(ParsedTerm::Ambiguity(
                alternatives
                    .into_iter()
                    .map(|alternative| self.resolve_overloaded_terminators(alternative))
                    .collect::<Result<_, _>>()?,
            )),
            ParsedTerm::Production {
                production,
                children,
                metadata,
            } => {
                let children = children
                    .into_iter()
                    .enumerate()
                    .map(|(child_index, child)| {
                        if let Some(terminator) =
                            self.program_list_terminator(production, child_index, &child)
                        {
                            Ok(terminator)
                        } else {
                            self.resolve_overloaded_terminators(child)
                        }
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let current = &self.productions[production];
                let Some(source) = current.source_production else {
                    return Ok(ParsedTerm::Production {
                        production,
                        children,
                        metadata,
                    });
                };
                if !children.is_empty() || !self.overloads.contains(&source) {
                    return Ok(ParsedTerm::Production {
                        production,
                        children,
                        metadata,
                    });
                }

                let candidates = self
                    .productions
                    .iter()
                    .filter_map(|candidate| {
                        let candidate_source = candidate.source_production?;
                        (candidate.label == current.label
                            && production_arity(candidate) == 0
                            && self.overloads.less_than_eq(&candidate_source, &source))
                        .then_some(candidate_source)
                    })
                    .collect::<BTreeSet<_>>();
                let least = self.overloads.minimal(candidates.iter());
                if least.len() != 1 {
                    let possible_sorts = self
                        .productions
                        .iter()
                        .filter(|candidate| {
                            candidate
                                .source_production
                                .is_some_and(|candidate| least.contains(&candidate))
                        })
                        .map(|candidate| candidate.result.clone())
                        .collect::<BTreeSet<_>>()
                        .into_iter()
                        .collect();
                    return Err(ParseError::OverloadedTerminator { possible_sorts });
                }
                let selected = *least.first().expect("length was checked above");
                let selected = self
                    .productions
                    .iter()
                    .enumerate()
                    .find_map(|(index, candidate)| {
                        (candidate.source_production == Some(selected)
                            && candidate.label == current.label
                            && production_arity(candidate) == 0)
                            .then_some(index)
                    })
                    .expect("a least source production came from a parser production");
                Ok(ParsedTerm::Production {
                    production: selected,
                    children,
                    metadata,
                })
            }
            ParsedTerm::InstantiatedProduction {
                production,
                parameters,
                children,
                metadata,
            } => Ok(ParsedTerm::InstantiatedProduction {
                production,
                parameters,
                metadata,
                children: children
                    .into_iter()
                    .map(|child| self.resolve_overloaded_terminators(child))
                    .collect::<Result<_, _>>()?,
            }),
        }
    }

    /// Apply Scala's post-inference overload and `prefer`/`avoid` selection,
    /// then push shared-production ambiguity into its one differing child.
    pub(super) fn filter_overloads_prefer_avoid(&self, term: ParsedTerm) -> ParsedTerm {
        match term {
            ParsedTerm::Term(_) => term,
            ParsedTerm::Production {
                production,
                children,
                metadata,
            } => ParsedTerm::Production {
                production,
                metadata,
                children: children
                    .into_iter()
                    .map(|child| self.filter_overloads_prefer_avoid(child))
                    .collect(),
            },
            ParsedTerm::InstantiatedProduction {
                production,
                parameters,
                children,
                metadata,
            } => ParsedTerm::InstantiatedProduction {
                production,
                parameters,
                metadata,
                children: children
                    .into_iter()
                    .map(|child| self.filter_overloads_prefer_avoid(child))
                    .collect(),
            },
            ParsedTerm::Ambiguity(mut alternatives) => {
                if alternatives.len() == 1 {
                    return self.filter_overloads_prefer_avoid(
                        alternatives.pop_first().expect("length was one"),
                    );
                }

                alternatives = self.remove_overloads(alternatives);
                if alternatives.len() == 1 {
                    return self.filter_overloads_prefer_avoid(
                        alternatives.pop_first().expect("length was one"),
                    );
                }

                let preferred = alternatives
                    .iter()
                    .filter(|alternative| self.is_preferred(alternative))
                    .cloned()
                    .collect::<BTreeSet<_>>();
                if !preferred.is_empty() {
                    alternatives = preferred;
                } else {
                    let retained = alternatives
                        .iter()
                        .filter(|alternative| !self.is_avoided(alternative))
                        .cloned()
                        .collect::<BTreeSet<_>>();
                    if !retained.is_empty() {
                        alternatives = retained;
                    }
                }

                let alternatives = alternatives
                    .into_iter()
                    .map(|alternative| self.filter_overloads_prefer_avoid(alternative))
                    .collect::<BTreeSet<_>>();
                if alternatives.len() == 1 {
                    return alternatives.into_iter().next().expect("length was one");
                }
                let ambiguity = ParsedTerm::Ambiguity(alternatives);
                let factored = self.factor_ambiguities(ambiguity.clone());
                if factored == ambiguity {
                    ambiguity
                } else {
                    self.filter_overloads_prefer_avoid(factored)
                }
            }
        }
    }

    fn remove_overloads(&self, alternatives: BTreeSet<ParsedTerm>) -> BTreeSet<ParsedTerm> {
        let alternatives = self.remove_bracket_overloads(alternatives);
        if alternatives.len() == 1 {
            return alternatives;
        }
        let Some(productions) = alternatives
            .iter()
            .map(|alternative| {
                let production = match alternative {
                    ParsedTerm::Production { production, .. }
                    | ParsedTerm::InstantiatedProduction { production, .. } => production,
                    ParsedTerm::Term(_) | ParsedTerm::Ambiguity(_) => return None,
                };
                self.productions[*production].source_production
            })
            .collect::<Option<BTreeSet<_>>>()
        else {
            return alternatives;
        };
        let minimal = self.overloads.minimal(productions.iter());
        alternatives
            .into_iter()
            .filter(|alternative| {
                let production = match alternative {
                    ParsedTerm::Production { production, .. }
                    | ParsedTerm::InstantiatedProduction { production, .. } => production,
                    ParsedTerm::Term(_) | ParsedTerm::Ambiguity(_) => {
                        unreachable!("non-production alternatives were returned above")
                    }
                };
                self.productions[*production]
                    .source_production
                    .is_some_and(|production| minimal.contains(&production))
            })
            .collect()
    }

    fn remove_bracket_overloads(&self, alternatives: BTreeSet<ParsedTerm>) -> BTreeSet<ParsedTerm> {
        let Some(productions) = alternatives
            .iter()
            .map(|alternative| match alternative {
                ParsedTerm::Production { production, .. }
                | ParsedTerm::InstantiatedProduction { production, .. }
                    if self.productions[*production].bracket =>
                {
                    Some(*production)
                }
                ParsedTerm::Production { .. }
                | ParsedTerm::InstantiatedProduction { .. }
                | ParsedTerm::Term(_)
                | ParsedTerm::Ambiguity(_) => None,
            })
            .collect::<Option<BTreeSet<_>>>()
        else {
            return alternatives;
        };
        let order =
            crate::definition::PartialOrder::new(self.syntactic_subsort_relations.iter().cloned())
                .expect("the grammar rejected syntactic subsort cycles during construction");
        let minimal = productions
            .iter()
            .filter(|candidate| {
                !productions.iter().any(|other| {
                    other != *candidate
                        && bracket_production_less_than(
                            &self.productions[*other],
                            &self.productions[**candidate],
                            &order,
                        )
                })
            })
            .copied()
            .collect::<BTreeSet<_>>();
        alternatives
            .into_iter()
            .filter(|alternative| {
                let production = match alternative {
                    ParsedTerm::Production { production, .. }
                    | ParsedTerm::InstantiatedProduction { production, .. } => production,
                    ParsedTerm::Term(_) | ParsedTerm::Ambiguity(_) => unreachable!(),
                };
                minimal.contains(production)
            })
            .collect()
    }

    fn is_preferred(&self, term: &ParsedTerm) -> bool {
        matches!(term, ParsedTerm::Production { production, .. } | ParsedTerm::InstantiatedProduction { production, .. } if self.productions[*production].prefer)
    }

    fn is_avoided(&self, term: &ParsedTerm) -> bool {
        matches!(term, ParsedTerm::Production { production, .. } | ParsedTerm::InstantiatedProduction { production, .. } if self.productions[*production].avoid)
    }

    /// Lift ambiguity in a top-level rewrite LHS above its `#RuleContent` wrapper.
    pub(super) fn push_top_lhs_packed_ambiguity_up(&self, term: Rc<PackedTerm>) -> Rc<PackedTerm> {
        if let PackedNode::Ambiguity(alternatives) = &term.node {
            let mut lifted = BTreeSet::new();
            for alternative in alternatives {
                let alternative = self.push_top_lhs_packed_ambiguity_up(Rc::clone(alternative));
                match &alternative.node {
                    PackedNode::Ambiguity(nested) => lifted.extend(nested.iter().cloned()),
                    _ => {
                        lifted.insert(alternative);
                    }
                }
            }
            return PackedTerm::ambiguity(lifted);
        }
        let PackedNode::Production {
            production,
            children,
            metadata,
        } = &term.node
        else {
            return term;
        };
        if self.productions[*production].result.name != "#RuleContent" || children.is_empty() {
            return term;
        }
        let bodies = self.expand_packed_rule_body_lhs(Rc::clone(&children[0]));
        if bodies.len() == 1 {
            let body = bodies.into_iter().next().expect("length was one");
            if Rc::ptr_eq(&body, &children[0]) {
                return term;
            }
            let mut rebuilt_children = children.clone();
            rebuilt_children[0] = body;
            return PackedTerm::production(*production, rebuilt_children, metadata.clone());
        }
        PackedTerm::ambiguity(
            bodies
                .into_iter()
                .map(|body| {
                    let mut alternative_children = children.clone();
                    alternative_children[0] = body;
                    PackedTerm::production(*production, alternative_children, metadata.clone())
                })
                .collect(),
        )
    }

    fn expand_packed_rule_body_lhs(&self, body: Rc<PackedTerm>) -> BTreeSet<Rc<PackedTerm>> {
        let PackedNode::Production {
            production,
            children,
            metadata,
        } = &body.node
        else {
            return BTreeSet::from([body]);
        };
        let label = self.productions[*production]
            .label
            .as_ref()
            .map(|label| label.name.as_str());
        if label == Some("#withConfig") && !children.is_empty() {
            return self
                .expand_packed_rule_body_lhs(Rc::clone(&children[0]))
                .into_iter()
                .map(|child| {
                    let mut alternative_children = children.clone();
                    alternative_children[0] = child;
                    PackedTerm::production(*production, alternative_children, metadata.clone())
                })
                .collect();
        }
        if label != Some("#KRewrite") || children.len() != 2 {
            return BTreeSet::from([body]);
        }
        let PackedNode::Ambiguity(alternatives) = &children[0].node else {
            return BTreeSet::from([body]);
        };
        alternatives
            .iter()
            .map(|left| {
                PackedTerm::production(
                    *production,
                    vec![Rc::clone(left), Rc::clone(&children[1])],
                    metadata.clone(),
                )
            })
            .collect()
    }

    #[cfg(test)]
    pub(super) fn push_top_lhs_ambiguity_up(&self, term: ParsedTerm) -> ParsedTerm {
        if let ParsedTerm::Ambiguity(alternatives) = term {
            let lifted = alternatives
                .into_iter()
                .map(|alternative| self.push_top_lhs_ambiguity_up(alternative))
                .flat_map(|alternative| match alternative {
                    ParsedTerm::Ambiguity(nested) => nested,
                    alternative => BTreeSet::from([alternative]),
                })
                .collect();
            return ParsedTerm::Ambiguity(lifted);
        }
        let ParsedTerm::Production {
            production,
            mut children,
            metadata,
        } = term
        else {
            return term;
        };
        if self.productions[production].result.name != "#RuleContent" || children.is_empty() {
            return ParsedTerm::Production {
                production,
                children,
                metadata,
            };
        }
        let bodies = self.expand_rule_body_lhs(children.remove(0));
        if bodies.len() == 1 {
            children.insert(0, bodies.into_iter().next().expect("length was one"));
            return ParsedTerm::Production {
                production,
                children,
                metadata,
            };
        }
        ParsedTerm::Ambiguity(
            bodies
                .into_iter()
                .map(|body| {
                    let mut alternative_children = children.clone();
                    alternative_children.insert(0, body);
                    ParsedTerm::Production {
                        production,
                        children: alternative_children,
                        metadata: metadata.clone(),
                    }
                })
                .collect(),
        )
    }

    #[cfg(test)]
    fn expand_rule_body_lhs(&self, body: ParsedTerm) -> BTreeSet<ParsedTerm> {
        let ParsedTerm::Production {
            production,
            mut children,
            metadata,
        } = body
        else {
            return BTreeSet::from([body]);
        };
        let label = self.productions[production]
            .label
            .as_ref()
            .map(|label| label.name.as_str());
        if label == Some("#withConfig") && !children.is_empty() {
            let expanded = self.expand_rule_body_lhs(children.remove(0));
            return expanded
                .into_iter()
                .map(|child| {
                    let mut alternative_children = children.clone();
                    alternative_children.insert(0, child);
                    ParsedTerm::Production {
                        production,
                        children: alternative_children,
                        metadata: metadata.clone(),
                    }
                })
                .collect();
        }
        if label != Some("#KRewrite") || children.len() != 2 {
            return BTreeSet::from([ParsedTerm::Production {
                production,
                children,
                metadata,
            }]);
        }
        let left = children.remove(0);
        let right = children.remove(0);
        match left {
            ParsedTerm::Ambiguity(alternatives) => alternatives
                .into_iter()
                .map(|left| ParsedTerm::Production {
                    production,
                    children: vec![left, right.clone()],
                    metadata: metadata.clone(),
                })
                .collect(),
            left => BTreeSet::from([ParsedTerm::Production {
                production,
                children: vec![left, right],
                metadata,
            }]),
        }
    }

    pub(super) fn ambiguity_count(term: &ParsedTerm) -> usize {
        match term {
            ParsedTerm::Term(_) => 1,
            ParsedTerm::Production { children, .. } => {
                children.iter().fold(1usize, |count, child| {
                    count.saturating_mul(Self::ambiguity_count(child))
                })
            }
            ParsedTerm::InstantiatedProduction { children, .. } => {
                children.iter().fold(1usize, |count, child| {
                    count.saturating_mul(Self::ambiguity_count(child))
                })
            }
            ParsedTerm::Ambiguity(alternatives) => {
                alternatives.iter().fold(0usize, |count, item| {
                    count.saturating_add(Self::ambiguity_count(item))
                })
            }
        }
    }
}

fn bracket_production_less_than(
    lesser: &Production,
    greater: &Production,
    sorts: &crate::definition::PartialOrder<crate::kast::Sort>,
) -> bool {
    if lesser.items.len() != greater.items.len()
        || !sorts.less_than_eq(&lesser.result, &greater.result)
    {
        return false;
    }
    let mut strict = lesser.result != greater.result;
    for (lesser, greater) in lesser.items.iter().zip(&greater.items) {
        match (lesser, greater) {
            (Item::NonTerminal(lesser), Item::NonTerminal(greater))
                if sorts.less_than_eq(lesser, greater) =>
            {
                strict |= lesser != greater;
            }
            (Item::Terminal(lesser), Item::Terminal(greater)) if lesser == greater => {}
            (
                Item::Regex { source: lesser, .. },
                Item::Regex {
                    source: greater, ..
                },
            ) if lesser == greater => {}
            _ => return false,
        }
    }
    strict
}

fn production_arity(production: &Production) -> usize {
    production
        .items
        .iter()
        .filter(|item| matches!(item, Item::NonTerminal(_)))
        .count()
}

#[cfg(test)]
fn klabel_name(term: &ParsedTerm) -> Option<String> {
    let Term::Token { token, sort } = term.leaf()? else {
        return None;
    };
    if sort.name != "KLabel" {
        return None;
    }
    if token.starts_with('`') {
        string::unquote_label(token).ok()
    } else {
        Some(token.clone())
    }
}

fn packed_klabel_name(term: &PackedTerm) -> Option<String> {
    let PackedNode::Term(term) = &term.node else {
        return None;
    };
    let Term::Token { token, sort } = term.unannotated() else {
        return None;
    };
    if sort.name != "KLabel" {
        return None;
    }
    if token.starts_with('`') {
        string::unquote_label(token).ok()
    } else {
        Some(token.clone())
    }
}

#[derive(Clone, Copy, Eq, Hash, PartialEq)]
enum Side {
    Left,
    Right,
    Middle,
}

pub(super) fn parse_apply_priority(source: &str) -> Result<BTreeSet<usize>, ParseError> {
    source
        .split(|character: char| character == ',' || character.is_ascii_whitespace())
        .filter(|piece| !piece.is_empty())
        .map(|piece| {
            piece
                .parse::<usize>()
                .map_err(|_| ParseError::InvalidApplyPriority {
                    value: source.to_owned(),
                    position: piece.to_owned(),
                })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::definition::{PartialOrder, ProductionId, ProductionItem, Sentence};
    use crate::kast::{Label, Sort};

    fn nonterminal(sort: &str) -> ProductionItem {
        ProductionItem::NonTerminal {
            sort: Sort::new(sort),
            name: None,
        }
    }

    fn add_production(
        grammar: &mut Grammar,
        result: &str,
        arguments: &[&str],
        label: &str,
    ) -> usize {
        let index = grammar.productions.len();
        grammar
            .add(
                Sort::new(result),
                arguments.iter().map(|sort| nonterminal(sort)).collect(),
                Some(Label::new(label)),
                false,
                false,
            )
            .unwrap();
        index
    }

    fn variable(name: &str) -> ParsedTerm {
        ParsedTerm::Term(Term::variable(name))
    }

    fn terminal_production(result: &str, terminal: &str, label: &str) -> Sentence {
        Sentence::Production {
            label: Some(Label::new(label)),
            parameters: Vec::new(),
            sort: Sort::new(result),
            items: vec![ProductionItem::Terminal(terminal.into())],
            attributes: Default::default(),
        }
    }

    fn subsort(result: &str, child: &str) -> Sentence {
        Sentence::Production {
            label: None,
            parameters: Vec::new(),
            sort: Sort::new(result),
            items: vec![nonterminal(child)],
            attributes: Default::default(),
        }
    }

    fn render(grammar: &Grammar, term: &ParsedTerm) -> String {
        match term {
            ParsedTerm::Term(term) => term.to_string(),
            ParsedTerm::Production {
                production,
                children,
                ..
            } => {
                let label = grammar.productions[*production]
                    .label
                    .as_ref()
                    .map_or("<unlabeled>", |label| label.name.as_str());
                format!(
                    "{label}({})",
                    children
                        .iter()
                        .map(|child| render(grammar, child))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            ParsedTerm::InstantiatedProduction {
                production,
                parameters,
                children,
                ..
            } => {
                let label = grammar.productions[*production]
                    .label
                    .as_ref()
                    .map_or("<unlabeled>", |label| label.name.as_str());
                format!(
                    "{label}{{{}}}({})",
                    parameters
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(", "),
                    children
                        .iter()
                        .map(|child| render(grammar, child))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            ParsedTerm::Ambiguity(alternatives) => format!(
                "amb{{{}}}",
                alternatives
                    .iter()
                    .map(|alternative| render(grammar, alternative))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }

    #[test]
    fn factors_a_shared_production_into_the_differing_child() {
        let mut grammar = Grammar::default();
        let pair = add_production(&mut grammar, "Exp", &["Exp", "Exp"], "pair");
        let alternatives = BTreeSet::from([
            ParsedTerm::Production {
                production: pair,
                children: vec![variable("A"), variable("C")],
                metadata: Default::default(),
            },
            ParsedTerm::Production {
                production: pair,
                children: vec![variable("B"), variable("C")],
                metadata: Default::default(),
            },
        ]);

        let factored = grammar.factor_ambiguities(ParsedTerm::Ambiguity(alternatives));
        let ParsedTerm::Production { children, .. } = factored else {
            panic!("expected the shared production to be factored")
        };
        assert!(matches!(children[0], ParsedTerm::Ambiguity(ref items) if items.len() == 2));
        assert_eq!(children[1], variable("C"));
    }

    #[test]
    fn flattens_nested_ambiguities_while_factoring() {
        let grammar = Grammar::default();
        let nested = ParsedTerm::Ambiguity(BTreeSet::from([
            variable("A"),
            ParsedTerm::Ambiguity(BTreeSet::from([variable("B"), variable("C")])),
        ]));

        let factored = grammar.factor_ambiguities(nested);

        assert!(matches!(factored, ParsedTerm::Ambiguity(ref items) if items.len() == 3));
        assert_eq!(render(&grammar, &factored), "amb{A, B, C}");
    }

    #[test]
    fn lifts_top_level_rewrite_lhs_ambiguity_above_rule_content() {
        let mut grammar = Grammar::default();
        let rewrite = add_production(&mut grammar, "#RuleExp", &["Exp", "Exp"], "#KRewrite");
        let rule = add_production(
            &mut grammar,
            "#RuleContent",
            &["#RuleExp"],
            "#ruleNoConditions",
        );
        let root = ParsedTerm::Production {
            production: rule,
            children: vec![ParsedTerm::Production {
                production: rewrite,
                children: vec![
                    ParsedTerm::Ambiguity(BTreeSet::from([variable("A"), variable("B")])),
                    variable("C"),
                ],
                metadata: Default::default(),
            }],
            metadata: Default::default(),
        };

        let lifted = grammar.push_top_lhs_ambiguity_up(root);
        assert!(matches!(lifted, ParsedTerm::Ambiguity(ref items) if items.len() == 2));
    }

    #[test]
    fn applies_prefer_and_avoid_only_at_ambiguity_roots() {
        let mut grammar = Grammar::default();
        let preferred = add_production(&mut grammar, "Exp", &[], "preferred");
        let ordinary = add_production(&mut grammar, "Exp", &[], "ordinary");
        let avoided = add_production(&mut grammar, "Exp", &[], "avoided");
        let also_avoided = add_production(&mut grammar, "Exp", &[], "alsoAvoided");
        grammar.productions[preferred].prefer = true;
        grammar.productions[avoided].avoid = true;
        grammar.productions[also_avoided].avoid = true;

        let alternative = |production| ParsedTerm::Production {
            production,
            children: Vec::new(),
            metadata: Default::default(),
        };
        let selected =
            grammar.filter_overloads_prefer_avoid(ParsedTerm::Ambiguity(BTreeSet::from([
                alternative(preferred),
                alternative(ordinary),
                alternative(avoided),
            ])));
        assert_eq!(selected, alternative(preferred));

        let without_prefer =
            grammar.filter_overloads_prefer_avoid(ParsedTerm::Ambiguity(BTreeSet::from([
                alternative(ordinary),
                alternative(avoided),
            ])));
        assert_eq!(without_prefer, alternative(ordinary));

        let all_avoided =
            grammar.filter_overloads_prefer_avoid(ParsedTerm::Ambiguity(BTreeSet::from([
                alternative(avoided),
                alternative(also_avoided),
            ])));
        assert!(matches!(all_avoided, ParsedTerm::Ambiguity(ref items) if items.len() == 2));

        let wrapper = add_production(&mut grammar, "Exp", &["Exp"], "wrapper");
        let nested =
            grammar.filter_overloads_prefer_avoid(ParsedTerm::Ambiguity(BTreeSet::from([
                ParsedTerm::Production {
                    production: wrapper,
                    children: vec![alternative(preferred)],
                    metadata: Default::default(),
                },
                ParsedTerm::Production {
                    production: wrapper,
                    children: vec![alternative(ordinary)],
                    metadata: Default::default(),
                },
            ])));
        assert_eq!(
            nested,
            ParsedTerm::Production {
                production: wrapper,
                children: vec![alternative(preferred)],
                metadata: Default::default(),
            }
        );

        assert_eq!(render(&grammar, &selected), "preferred()");
        assert_eq!(render(&grammar, &without_prefer), "ordinary()");
        assert_eq!(
            render(&grammar, &all_avoided),
            "amb{avoided(), alsoAvoided()}"
        );
        assert_eq!(render(&grammar, &nested), "wrapper(preferred())");
    }

    #[test]
    fn removes_overloads_before_applying_prefer_and_avoid() {
        let mut grammar = Grammar::default();
        let specific = add_production(&mut grammar, "Small", &[], "pick");
        let general = add_production(&mut grammar, "Large", &[], "pick");
        grammar.productions[specific].source_production = Some(ProductionId(0));
        grammar.productions[general].source_production = Some(ProductionId(1));
        grammar.productions[general].prefer = true;
        grammar.overloads = PartialOrder::new([(ProductionId(0), ProductionId(1))]).unwrap();

        let alternative = |production| ParsedTerm::Production {
            production,
            children: Vec::new(),
            metadata: Default::default(),
        };
        let filtered =
            grammar.filter_overloads_prefer_avoid(ParsedTerm::Ambiguity(BTreeSet::from([
                alternative(specific),
                alternative(general),
            ])));

        assert_eq!(filtered, alternative(specific));
        assert_eq!(render(&grammar, &filtered), "pick()");
    }

    #[test]
    fn resolves_overloaded_terminators_and_rejects_incomparable_minima() {
        let sentences = [
            terminal_production("Small", "small", "unit"),
            subsort("Large", "Small"),
            terminal_production("Large", "large", "unit"),
        ];
        let grammar = Grammar::from_sentences(&sentences).unwrap();
        let source = |result: &str| {
            grammar
                .productions
                .iter()
                .enumerate()
                .find_map(|(index, production)| {
                    (production.result.name == result
                        && production
                            .label
                            .as_ref()
                            .is_some_and(|label| label.name == "unit"))
                    .then_some(index)
                })
                .unwrap()
        };
        let resolved = grammar
            .resolve_overloaded_terminators(ParsedTerm::Production {
                production: source("Large"),
                children: Vec::new(),
                metadata: Default::default(),
            })
            .unwrap();
        assert_eq!(render(&grammar, &resolved), "unit()");
        let ParsedTerm::Production { production, .. } = resolved else {
            unreachable!()
        };
        assert_eq!(grammar.productions[production].result.name, "Small");

        let mut ambiguous = Grammar::default();
        let first = add_production(&mut ambiguous, "First", &[], "unit");
        let second = add_production(&mut ambiguous, "Second", &[], "unit");
        let general = add_production(&mut ambiguous, "General", &[], "unit");
        for (index, source) in [first, second, general].into_iter().enumerate() {
            ambiguous.productions[source].source_production = Some(ProductionId(index));
        }
        ambiguous.overloads = PartialOrder::new([
            (ProductionId(0), ProductionId(2)),
            (ProductionId(1), ProductionId(2)),
        ])
        .unwrap();
        let error = ambiguous
            .resolve_overloaded_terminators(ParsedTerm::Production {
                production: general,
                children: Vec::new(),
                metadata: Default::default(),
            })
            .unwrap_err();

        assert_eq!(grammar.productions[production].result, Sort::new("Small"));
        assert_eq!(
            error,
            ParseError::OverloadedTerminator {
                possible_sorts: vec![Sort::new("First"), Sort::new("Second")],
            }
        );
    }
}
