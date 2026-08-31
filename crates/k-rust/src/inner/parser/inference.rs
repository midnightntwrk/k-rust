//! Portable sort inference for unambiguous, non-parametric parse trees.

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::rc::Rc;

use crate::definition::PartialOrder;
use crate::kast::{Sort, Term};

use super::{Grammar, Item, PackedNode, PackedTerm, ParseError, ParsedTerm, Production};

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum SortRef {
    Concrete(Sort),
    Variable(usize),
}

#[derive(Clone, Debug, Default)]
struct Bounds {
    lower: BTreeSet<SortRef>,
    upper: BTreeSet<SortRef>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum VariableId {
    Named(String),
    Anonymous(usize),
}

struct Solver<'a> {
    order: &'a PartialOrder<Sort>,
    bounds: Vec<Bounds>,
    variables: BTreeMap<VariableId, usize>,
    constraint_cache: BTreeSet<(SortRef, SortRef)>,
    next_anonymous: usize,
}

impl Grammar {
    pub(super) fn infer_packed_sorts(
        &self,
        term: Rc<PackedTerm>,
        top_sort: &Sort,
        explicitly_anywhere: bool,
    ) -> Result<ParsedTerm, ParseError> {
        if !self.packed_sort_inference_supported(&term) {
            #[cfg(feature = "z3-inference")]
            return self.infer_packed_sorts_z3(term, top_sort, explicitly_anywhere);
            #[cfg(not(feature = "z3-inference"))]
            {
                let (ambiguity, parametric_sorts) = self.packed_z3_reasons(&term);
                return Err(ParseError::Z3InferenceRequired {
                    ambiguity,
                    parametric_sorts,
                });
            }
        }
        self.infer_sorts(term.unpack(), top_sort, explicitly_anywhere)
    }

    fn packed_sort_inference_supported(&self, term: &Rc<PackedTerm>) -> bool {
        fn supported(
            grammar: &Grammar,
            term: &Rc<PackedTerm>,
            visited: &mut HashSet<*const PackedTerm>,
        ) -> bool {
            if !visited.insert(Rc::as_ptr(term)) {
                return true;
            }
            match &term.node {
                PackedNode::Ambiguity(_) => false,
                PackedNode::Term(term) => match term.unannotated() {
                    Term::Token { sort, .. } => sort.parameters.is_empty(),
                    _ => true,
                },
                PackedNode::Production {
                    production,
                    children,
                    ..
                } => {
                    let production = &grammar.productions[*production];
                    production.parametric_origin.is_none()
                        && production.result.parameters.is_empty()
                        && production.items.iter().all(|item| {
                            !matches!(item, Item::NonTerminal(sort) if !sort.parameters.is_empty())
                        })
                        && children
                            .iter()
                            .all(|child| supported(grammar, child, visited))
                }
                PackedNode::InstantiatedProduction { .. } => {
                    unreachable!("sort support is checked before inference")
                }
            }
        }

        supported(self, term, &mut HashSet::new())
    }

    #[cfg(not(feature = "z3-inference"))]
    fn packed_z3_reasons(&self, term: &Rc<PackedTerm>) -> (bool, bool) {
        fn reasons(
            grammar: &Grammar,
            term: &Rc<PackedTerm>,
            visited: &mut HashSet<*const PackedTerm>,
        ) -> (bool, bool) {
            if !visited.insert(Rc::as_ptr(term)) {
                return (false, false);
            }
            match &term.node {
                PackedNode::Ambiguity(alternatives) => alternatives.iter().fold(
                    (true, false),
                    |(ambiguity, parametric), alternative| {
                        let (child_ambiguity, child_parametric) =
                            reasons(grammar, alternative, visited);
                        (ambiguity || child_ambiguity, parametric || child_parametric)
                    },
                ),
                PackedNode::Production {
                    production,
                    children,
                    ..
                } => {
                    let descriptor = &grammar.productions[*production];
                    let local = descriptor.parametric_origin.is_some()
                        || !descriptor.result.parameters.is_empty()
                        || descriptor.items.iter().any(|item| {
                            matches!(item, Item::NonTerminal(sort) if !sort.parameters.is_empty())
                        });
                    children
                        .iter()
                        .fold((false, local), |(ambiguity, parametric), child| {
                            let (child_ambiguity, child_parametric) =
                                reasons(grammar, child, visited);
                            (ambiguity || child_ambiguity, parametric || child_parametric)
                        })
                }
                PackedNode::Term(term) => match term.unannotated() {
                    Term::Token { sort, .. } => (false, !sort.parameters.is_empty()),
                    _ => (false, false),
                },
                PackedNode::InstantiatedProduction { .. } => {
                    unreachable!("Z3 reasons are computed before inference")
                }
            }
        }

        reasons(self, term, &mut HashSet::new())
    }

    pub(super) fn infer_sorts(
        &self,
        term: ParsedTerm,
        top_sort: &Sort,
        explicitly_anywhere: bool,
    ) -> Result<ParsedTerm, ParseError> {
        if !self.sort_inference_supported(&term) {
            #[cfg(feature = "z3-inference")]
            return self.infer_sorts_z3(term, top_sort, explicitly_anywhere);
            #[cfg(not(feature = "z3-inference"))]
            {
                let (ambiguity, parametric_sorts) = self.z3_reasons(&term);
                return Err(ParseError::Z3InferenceRequired {
                    ambiguity,
                    parametric_sorts,
                });
            }
        }
        let order = PartialOrder::new(self.subsort_relations.iter().cloned()).map_err(|cycle| {
            inference_error(format!(
                "cannot infer sorts with a circular subsort relation: {}",
                cycle
                    .path
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(" < ")
            ))
        })?;
        let anywhere = explicitly_anywhere || self.lhs_is_function_or_macro(&term);
        let mut solver = Solver::new(&order);
        let inferred = solver.infer(self, &term, anywhere)?;
        solver.constrain(inferred, SortRef::Concrete(top_sort.clone()))?;
        let variable_sorts = solver.realize_variables()?;
        let mut next_anonymous = 0;
        self.insert_inferred_casts(term, &variable_sorts, false, &mut next_anonymous)
    }

    fn sort_inference_supported(&self, term: &ParsedTerm) -> bool {
        match term {
            ParsedTerm::Ambiguity(_) => false,
            ParsedTerm::Term(term) => match term.unannotated() {
                Term::Token { sort, .. } => sort.parameters.is_empty(),
                _ => true,
            },
            ParsedTerm::Production {
                production,
                children,
                ..
            } => {
                let production = &self.productions[*production];
                production.parametric_origin.is_none()
                    && production.result.parameters.is_empty()
                    && production.items.iter().all(|item| {
                        !matches!(item, Item::NonTerminal(sort) if !sort.parameters.is_empty())
                    })
                    && children
                        .iter()
                        .all(|child| self.sort_inference_supported(child))
            }
            ParsedTerm::InstantiatedProduction { .. } => {
                unreachable!("instantiated productions are created by Z3 inference")
            }
        }
    }

    #[cfg(not(feature = "z3-inference"))]
    fn z3_reasons(&self, term: &ParsedTerm) -> (bool, bool) {
        match term {
            ParsedTerm::Ambiguity(alternatives) => {
                alternatives
                    .iter()
                    .fold((true, false), |(ambiguity, parametric), alternative| {
                        let (_, child_parametric) = self.z3_reasons(alternative);
                        (ambiguity, parametric || child_parametric)
                    })
            }
            ParsedTerm::Production {
                production,
                children,
                ..
            } => {
                let descriptor = &self.productions[*production];
                let local = descriptor.parametric_origin.is_some()
                    || !descriptor.result.parameters.is_empty()
                    || descriptor.items.iter().any(
                        |item| matches!(item, Item::NonTerminal(sort) if !sort.parameters.is_empty()),
                    );
                children
                    .iter()
                    .fold((false, local), |(ambiguity, parametric), child| {
                        let (child_ambiguity, child_parametric) = self.z3_reasons(child);
                        (ambiguity || child_ambiguity, parametric || child_parametric)
                    })
            }
            ParsedTerm::Term(term) => match term.unannotated() {
                Term::Token { sort, .. } => (false, !sort.parameters.is_empty()),
                _ => (false, false),
            },
            ParsedTerm::InstantiatedProduction { .. } => {
                unreachable!("Z3 inference reasons are computed before inference")
            }
        }
    }

    pub(super) fn lhs_is_function_or_macro(&self, term: &ParsedTerm) -> bool {
        let Some(rewrite) = self.top_rewrite(term) else {
            return false;
        };
        let ParsedTerm::Production { production, .. } = strip_brackets(self, rewrite.0) else {
            return false;
        };
        let production = &self.productions[*production];
        production.function || production.macro_like
    }

    fn top_rewrite<'a>(&self, term: &'a ParsedTerm) -> Option<(&'a ParsedTerm, &'a ParsedTerm)> {
        let mut term = strip_brackets(self, term);
        loop {
            let ParsedTerm::Production {
                production,
                children,
                ..
            } = term
            else {
                return None;
            };
            let production = &self.productions[*production];
            if production.result.name == "#RuleContent" {
                term = strip_brackets(self, children.first()?);
                continue;
            }
            if production.result.name == "#RuleBody"
                && production
                    .label
                    .as_ref()
                    .is_some_and(|label| label.name == "#withConfig")
            {
                term = strip_brackets(self, children.first()?);
                continue;
            }
            return (production
                .label
                .as_ref()
                .is_some_and(|label| label.name == "#KRewrite")
                && children.len() == 2)
                .then(|| (&children[0], &children[1]));
        }
    }

    fn insert_inferred_casts(
        &self,
        term: ParsedTerm,
        variable_sorts: &BTreeMap<VariableId, Sort>,
        existing_cast: bool,
        next_anonymous: &mut usize,
    ) -> Result<ParsedTerm, ParseError> {
        match term {
            ParsedTerm::Term(ref leaf) if matches!(leaf.unannotated(), Term::Variable { .. }) => {
                let Term::Variable { name, .. } = leaf.unannotated() else {
                    unreachable!()
                };
                let id = variable_id(name, next_anonymous);
                if existing_cast {
                    return Ok(term);
                }
                let sort = variable_sorts.get(&id).ok_or_else(|| {
                    inference_error(format!("no inferred sort was produced for variable {name}"))
                })?;
                let label = format!("#SemanticCastTo{sort}");
                let production = self
                    .productions
                    .iter()
                    .enumerate()
                    .find_map(|(index, production)| {
                        (production.label.as_ref().is_some_and(|candidate| candidate.name == label)
                            && production_arity(production) == 1)
                            .then_some(index)
                    })
                    .ok_or_else(|| {
                        inference_error(format!(
                            "cannot record inferred sort {sort} for variable {name}: missing semantic-cast production"
                        ))
                    })?;
                Ok(ParsedTerm::Production {
                    production,
                    children: vec![term],
                    metadata: super::TermMetadata::default(),
                })
            }
            ParsedTerm::Term(_) => Ok(term),
            ParsedTerm::Ambiguity(_) => Err(inference_error(
                "portable sort inference received an ambiguous parse forest",
            )),
            ParsedTerm::Production {
                production,
                children,
                metadata,
            } => {
                let is_cast = self.productions[production]
                    .label
                    .as_ref()
                    .is_some_and(|label| label.name.starts_with("#SemanticCastTo"));
                Ok(ParsedTerm::Production {
                    production,
                    metadata,
                    children: children
                        .into_iter()
                        .map(|child| {
                            self.insert_inferred_casts(
                                child,
                                variable_sorts,
                                is_cast,
                                next_anonymous,
                            )
                        })
                        .collect::<Result<_, _>>()?,
                })
            }
            ParsedTerm::InstantiatedProduction { .. } => {
                unreachable!("portable inference cannot create instantiated productions")
            }
        }
    }
}

impl<'a> Solver<'a> {
    fn new(order: &'a PartialOrder<Sort>) -> Self {
        Self {
            order,
            bounds: Vec::new(),
            variables: BTreeMap::new(),
            constraint_cache: BTreeSet::new(),
            next_anonymous: 0,
        }
    }

    fn infer(
        &mut self,
        grammar: &Grammar,
        term: &ParsedTerm,
        anywhere: bool,
    ) -> Result<SortRef, ParseError> {
        match term {
            ParsedTerm::Ambiguity(_) => Err(inference_error(
                "portable sort inference does not support ambiguous parse forests",
            )),
            ParsedTerm::Term(term) => match term.unannotated() {
                Term::Variable { name, .. } => self.variable(name),
                Term::Token { sort, .. } => Ok(SortRef::Concrete(sort.clone())),
                _ => Err(inference_error(
                    "unexpected lowered KAST node in the concrete parse forest",
                )),
            },
            ParsedTerm::Production {
                production,
                children,
                ..
            } => {
                let production = &grammar.productions[*production];
                let child_sorts = children
                    .iter()
                    .map(|child| self.infer(grammar, child, anywhere))
                    .collect::<Result<Vec<_>, _>>()?;
                let expected = production
                    .items
                    .iter()
                    .filter_map(|item| match item {
                        Item::NonTerminal(sort) => Some(sort),
                        Item::Terminal(_) | Item::Regex { .. } => None,
                    })
                    .collect::<Vec<_>>();
                if expected.len() != child_sorts.len() {
                    return Err(inference_error(format!(
                        "production {:?} has {} nonterminals but its parse node has {} children",
                        production.parse_label,
                        expected.len(),
                        child_sorts.len()
                    )));
                }
                let anywhere_lhs_sort = (anywhere
                    && production
                        .label
                        .as_ref()
                        .is_some_and(|label| label.name == "#KRewrite")
                    && children.len() == 2)
                    .then(|| declared_sort(grammar, strip_brackets(grammar, &children[0])));
                for (index, ((term, child), expected)) in children
                    .iter()
                    .zip(child_sorts.iter().cloned())
                    .zip(expected.iter())
                    .enumerate()
                {
                    let expected = SortRef::Concrete(
                        if index == 1
                            && let Some(lhs_sort) = &anywhere_lhs_sort
                        {
                            lhs_sort.clone()
                        } else {
                            (*expected).clone()
                        },
                    );
                    self.constrain(child.clone(), expected.clone())?;
                    if is_anonymous_leaf(term) {
                        // Scala's inferencer treats every anonymous occurrence as having exactly
                        // the sort required by its context.  A mere upper bound is insufficient
                        // for parser sorts such as KItem, whose synthetic hierarchy is not always
                        // represented by an ordinary subsort production.
                        self.constrain(expected, child)?;
                    }
                }
                if production.label.as_ref().is_some_and(|label| {
                    matches!(
                        label.name.as_str(),
                        "#SyntacticCast" | "#SyntacticCastBraced"
                    )
                }) && let Some(child) = expected.first()
                {
                    let cast = SortRef::Concrete(production.result.clone());
                    let child = SortRef::Concrete((*child).clone());
                    self.constrain(cast.clone(), child.clone())?;
                    self.constrain(child, cast)?;
                }
                Ok(SortRef::Concrete(production.result.clone()))
            }
            ParsedTerm::InstantiatedProduction { .. } => {
                unreachable!("instantiated productions are created after constraint solving")
            }
        }
    }

    fn variable(&mut self, name: &str) -> Result<SortRef, ParseError> {
        let id = variable_id(name, &mut self.next_anonymous);
        let variable = if let Some(variable) = self.variables.get(&id) {
            *variable
        } else {
            let variable = self.bounds.len();
            self.bounds.push(Bounds::default());
            self.variables.insert(id, variable);
            self.constrain(
                SortRef::Variable(variable),
                SortRef::Concrete(Sort::new("K")),
            )?;
            variable
        };
        Ok(SortRef::Variable(variable))
    }

    fn constrain(&mut self, lesser: SortRef, greater: SortRef) -> Result<(), ParseError> {
        if lesser == greater
            || !self
                .constraint_cache
                .insert((lesser.clone(), greater.clone()))
        {
            return Ok(());
        }
        match (lesser, greater) {
            (SortRef::Variable(variable), greater) => {
                self.bounds[variable].upper.insert(greater.clone());
                let lower = self.bounds[variable]
                    .lower
                    .iter()
                    .cloned()
                    .collect::<Vec<_>>();
                for lesser in lower {
                    self.constrain(lesser, greater.clone())?;
                }
                Ok(())
            }
            (lesser, SortRef::Variable(variable)) => {
                self.bounds[variable].lower.insert(lesser.clone());
                let upper = self.bounds[variable]
                    .upper
                    .iter()
                    .cloned()
                    .collect::<Vec<_>>();
                for greater in upper {
                    self.constrain(lesser.clone(), greater)?;
                }
                Ok(())
            }
            (SortRef::Concrete(lesser), SortRef::Concrete(greater)) => {
                if self.order.less_than_eq(&lesser, &greater) {
                    Ok(())
                } else {
                    Err(inference_error(format!(
                        "unexpected sort {lesser}; expected a subsort of {greater}"
                    )))
                }
            }
        }
    }

    fn realize_variables(&self) -> Result<BTreeMap<VariableId, Sort>, ParseError> {
        self.variables
            .iter()
            .map(|(id, variable)| {
                self.realize_variable(*variable)
                    .map(|sort| (id.clone(), sort))
            })
            .collect()
    }

    fn realize_variable(&self, variable: usize) -> Result<Sort, ParseError> {
        let upper = self.concrete_bounds(variable, true, &mut BTreeSet::new());
        let lower = self.concrete_bounds(variable, false, &mut BTreeSet::new());
        let candidates = if upper.len() == 1 {
            upper.clone()
        } else {
            let bounds = self.order.lower_bounds(upper.iter());
            self.order.maximal(bounds.iter())
        }
        .into_iter()
        .filter(|sort| !self.order.less_than_eq(sort, &Sort::new("KBott")))
        .filter(|candidate| {
            lower
                .iter()
                .all(|bound| self.order.less_than_eq(bound, candidate))
        })
        .collect::<BTreeSet<_>>();
        if candidates.len() == 1 {
            Ok(candidates.into_iter().next().expect("one candidate"))
        } else if candidates.is_empty() {
            Err(inference_error(format!(
                "variable has incompatible sort bounds: lower {lower:?}, upper {upper:?}"
            )))
        } else {
            Err(inference_error(format!(
                "variable sort has incomparable candidates {candidates:?} from bounds {upper:?}"
            )))
        }
    }

    fn concrete_bounds(
        &self,
        variable: usize,
        upper: bool,
        visited: &mut BTreeSet<usize>,
    ) -> BTreeSet<Sort> {
        if !visited.insert(variable) {
            return BTreeSet::new();
        }
        let bounds = if upper {
            &self.bounds[variable].upper
        } else {
            &self.bounds[variable].lower
        };
        bounds
            .iter()
            .flat_map(|bound| match bound {
                SortRef::Concrete(sort) => BTreeSet::from([sort.clone()]),
                SortRef::Variable(variable) => {
                    self.concrete_bounds(*variable, upper, &mut visited.clone())
                }
            })
            .collect()
    }
}

fn strip_brackets<'a>(grammar: &Grammar, mut term: &'a ParsedTerm) -> &'a ParsedTerm {
    while let ParsedTerm::Production {
        production,
        children,
        ..
    } = term
    {
        if !grammar.productions[*production].bracket || children.len() != 1 {
            break;
        }
        term = &children[0];
    }
    term
}

fn is_anonymous_leaf(term: &ParsedTerm) -> bool {
    matches!(
        term,
        ParsedTerm::Term(term)
            if matches!(term.unannotated(), Term::Variable { name, .. } if is_anonymous(name))
    )
}

fn declared_sort(grammar: &Grammar, term: &ParsedTerm) -> Sort {
    match term {
        ParsedTerm::Production { production, .. } => {
            grammar.productions[*production].result.clone()
        }
        ParsedTerm::InstantiatedProduction { production, .. } => {
            grammar.productions[*production].result.clone()
        }
        ParsedTerm::Term(term) => match term.unannotated() {
            Term::Token { sort, .. } => sort.clone(),
            _ => Sort::new("K"),
        },
        ParsedTerm::Ambiguity(_) => Sort::new("K"),
    }
}

fn production_arity(production: &Production) -> usize {
    production
        .items
        .iter()
        .filter(|item| matches!(item, Item::NonTerminal(_)))
        .count()
}

fn variable_id(name: &str, next_anonymous: &mut usize) -> VariableId {
    if is_anonymous(name) {
        let id = VariableId::Anonymous(*next_anonymous);
        *next_anonymous += 1;
        id
    } else {
        VariableId::Named(name.to_owned())
    }
}

fn is_anonymous(name: &str) -> bool {
    name.starts_with('_')
        || name.starts_with("?_")
        || name.starts_with("!_")
        || name.starts_with("@_")
}

fn inference_error(message: impl Into<String>) -> ParseError {
    ParseError::SortInference {
        message: message.into(),
    }
}
