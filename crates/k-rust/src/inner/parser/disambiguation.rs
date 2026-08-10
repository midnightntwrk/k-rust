//! Priority and associativity filtering over production-bearing parse trees.

use std::collections::BTreeSet;

use super::{Grammar, Item, ParseError, ParsedTerm, Production, lower_term};
use crate::kast::{Term, string};

impl Grammar {
    pub(super) fn priority_violation(&self, term: &ParsedTerm) -> Option<ParseError> {
        let ParsedTerm::Production {
            production,
            children,
        } = term
        else {
            return match term {
                ParsedTerm::Ambiguity(alternatives) => alternatives
                    .iter()
                    .find_map(|alternative| self.priority_violation(alternative)),
                ParsedTerm::Term(_) => None,
                ParsedTerm::Production { .. } => unreachable!(),
                ParsedTerm::InstantiatedProduction { .. } => {
                    unreachable!("instantiated productions are created after priority filtering")
                }
            };
        };
        let parent = &self.productions[*production];
        // Scala collapses generated record syntax before priority filtering.
        // Ignore the wrapper's borrowed label here; the positional production
        // is checked after `collapse_record_productions` reconstructs it.
        if parent.record.is_some() {
            return children
                .iter()
                .find_map(|child| self.priority_violation(child));
        }
        if parent.syntactic_subsort {
            return children
                .iter()
                .find_map(|child| self.priority_violation(child));
        }

        let checked = parent.apply_priority.clone().unwrap_or_else(|| {
            let mut positions = BTreeSet::new();
            if matches!(parent.items.first(), Some(Item::NonTerminal(_))) {
                positions.insert(1);
            }
            if matches!(parent.items.last(), Some(Item::NonTerminal(_))) {
                positions.insert(children.len());
            }
            positions
        });
        for position in checked {
            let Some(child) = children.get(position.saturating_sub(1)) else {
                continue;
            };
            let side =
                if position == 1 && matches!(parent.items.first(), Some(Item::NonTerminal(_))) {
                    Side::Left
                } else if position == children.len()
                    && matches!(parent.items.last(), Some(Item::NonTerminal(_)))
                {
                    Side::Right
                } else {
                    Side::Middle
                };
            if let Some(error) = self.child_violation(parent, child, side) {
                return Some(error);
            }
        }
        children
            .iter()
            .find_map(|child| self.priority_violation(child))
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
        if child.syntactic_subsort {
            return None;
        }
        let (Some(parent_label), Some(child_label)) = (&parent.parse_label, &child.parse_label)
        else {
            return None;
        };
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
            } => {
                let production = &self.productions[production];
                let children = children
                    .into_iter()
                    .map(|child| self.lower(child))
                    .collect::<Vec<_>>();
                lower_term(production, &children)
            }
            ParsedTerm::InstantiatedProduction {
                production,
                parameters,
                children,
            } => {
                let production = &self.productions[production];
                let children = children
                    .into_iter()
                    .map(|child| self.lower(child))
                    .collect::<Vec<_>>();
                let mut instantiated = production.clone();
                if let Some(label) = &mut instantiated.label {
                    label.parameters = parameters;
                }
                lower_term(&instantiated, &children)
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
                    children: children
                        .into_iter()
                        .map(|child| self.remove_brackets_and_syntactic_casts(child))
                        .collect(),
                }
            }
        }
    }

    /// Resolve `#KApply` nodes to every visible production with the same label and arity.
    pub(super) fn resolve_applications(&self, term: ParsedTerm) -> Result<ParsedTerm, ParseError> {
        match term {
            ParsedTerm::Term(_) => Ok(term),
            ParsedTerm::Ambiguity(alternatives) => alternatives
                .into_iter()
                .map(|alternative| self.resolve_applications(alternative))
                .collect::<Result<BTreeSet<_>, _>>()
                .map(ParsedTerm::Ambiguity),
            ParsedTerm::Production {
                production,
                children,
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
                            candidates.insert(ParsedTerm::Production {
                                production: candidate,
                                children: arguments.clone(),
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
            } => ParsedTerm::Production {
                production,
                children: children
                    .into_iter()
                    .map(|child| self.factor_ambiguities(child))
                    .collect(),
            },
            ParsedTerm::InstantiatedProduction {
                production,
                parameters,
                children,
            } => ParsedTerm::InstantiatedProduction {
                production,
                parameters,
                children: children
                    .into_iter()
                    .map(|child| self.factor_ambiguities(child))
                    .collect(),
            },
            ParsedTerm::Ambiguity(alternatives) => {
                let mut alternatives = alternatives
                    .into_iter()
                    .map(|alternative| self.factor_ambiguities(alternative))
                    .collect::<BTreeSet<_>>();
                if alternatives.len() == 1 {
                    return alternatives.pop_first().expect("length was one");
                }
                if let Some(ParsedTerm::InstantiatedProduction {
                    production,
                    parameters,
                    children,
                }) = alternatives.first()
                {
                    let production = *production;
                    let parameters = parameters.clone();
                    let children = children.clone();
                    if !alternatives.iter().all(|alternative| {
                        matches!(
                            alternative,
                            ParsedTerm::InstantiatedProduction {
                                production: candidate,
                                parameters: candidate_parameters,
                                children: candidate_children,
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
                    };
                }
                let Some(ParsedTerm::Production {
                    production,
                    children,
                }) = alternatives.first()
                else {
                    return ParsedTerm::Ambiguity(alternatives);
                };
                let production = *production;
                let children = children.clone();
                if !alternatives.iter().all(|alternative| {
                    matches!(
                        alternative,
                        ParsedTerm::Production {
                            production: candidate,
                            children: candidate_children,
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
            } => {
                let children = children
                    .into_iter()
                    .map(|child| self.resolve_overloaded_terminators(child))
                    .collect::<Result<Vec<_>, _>>()?;
                let current = &self.productions[production];
                let Some(source) = current.source_production else {
                    return Ok(ParsedTerm::Production {
                        production,
                        children,
                    });
                };
                if !children.is_empty() || !self.overloads.contains(&source) {
                    return Ok(ParsedTerm::Production {
                        production,
                        children,
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
                })
            }
            ParsedTerm::InstantiatedProduction {
                production,
                parameters,
                children,
            } => Ok(ParsedTerm::InstantiatedProduction {
                production,
                parameters,
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
            } => ParsedTerm::Production {
                production,
                children: children
                    .into_iter()
                    .map(|child| self.filter_overloads_prefer_avoid(child))
                    .collect(),
            },
            ParsedTerm::InstantiatedProduction {
                production,
                parameters,
                children,
            } => ParsedTerm::InstantiatedProduction {
                production,
                parameters,
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

    fn is_preferred(&self, term: &ParsedTerm) -> bool {
        matches!(term, ParsedTerm::Production { production, .. } | ParsedTerm::InstantiatedProduction { production, .. } if self.productions[*production].prefer)
    }

    fn is_avoided(&self, term: &ParsedTerm) -> bool {
        matches!(term, ParsedTerm::Production { production, .. } | ParsedTerm::InstantiatedProduction { production, .. } if self.productions[*production].avoid)
    }

    /// Lift ambiguity in a top-level rewrite LHS above its `#RuleContent` wrapper.
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
        } = term
        else {
            return term;
        };
        if self.productions[production].result.name != "#RuleContent" || children.is_empty() {
            return ParsedTerm::Production {
                production,
                children,
            };
        }
        let bodies = self.expand_rule_body_lhs(children.remove(0));
        if bodies.len() == 1 {
            children.insert(0, bodies.into_iter().next().expect("length was one"));
            return ParsedTerm::Production {
                production,
                children,
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
                    }
                })
                .collect(),
        )
    }

    fn expand_rule_body_lhs(&self, body: ParsedTerm) -> BTreeSet<ParsedTerm> {
        let ParsedTerm::Production {
            production,
            mut children,
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
                    }
                })
                .collect();
        }
        if label != Some("#KRewrite") || children.len() != 2 {
            return BTreeSet::from([ParsedTerm::Production {
                production,
                children,
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
                })
                .collect(),
            left => BTreeSet::from([ParsedTerm::Production {
                production,
                children: vec![left, right],
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

fn production_arity(production: &Production) -> usize {
    production
        .items
        .iter()
        .filter(|item| matches!(item, Item::NonTerminal(_)))
        .count()
}

fn klabel_name(term: &ParsedTerm) -> Option<String> {
    let ParsedTerm::Term(Term::Token { token, sort }) = term else {
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

#[derive(Clone, Copy, Eq, PartialEq)]
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
            },
            ParsedTerm::Production {
                production: pair,
                children: vec![variable("B"), variable("C")],
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
            }],
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
                },
                ParsedTerm::Production {
                    production: wrapper,
                    children: vec![alternative(ordinary)],
                },
            ])));
        assert_eq!(
            nested,
            ParsedTerm::Production {
                production: wrapper,
                children: vec![alternative(preferred)],
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
