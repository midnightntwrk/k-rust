//! Portable sort inference for unambiguous, monomorphic parse trees.

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::rc::Rc;

use crate::definition::{PartialOrder, ProductionItem};
use crate::kast::{Sort, Term};

use super::{
    Grammar, Item, PackedNode, PackedTerm, ParseError, ParsedTerm, Production,
    inferred_variable_name,
};

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
    parameters: Vec<(String, Vec<usize>)>,
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
        let unpacked = term.unpack();
        self.infer_sorts(unpacked, top_sort, explicitly_anywhere)
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
                    signature_is_monomorphic(production)
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
                    let local = !signature_is_monomorphic(descriptor);
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
        #[cfg(feature = "z3-inference")]
        if checked_inference_requested() {
            let portable = self.infer_sorts_portable(term.clone(), top_sort, explicitly_anywhere);
            let z3 = self.infer_sorts_z3(term, top_sort, explicitly_anywhere);
            return checked_inference_result(portable, z3);
        }
        self.infer_sorts_portable(term, top_sort, explicitly_anywhere)
    }

    fn infer_sorts_portable(
        &self,
        term: ParsedTerm,
        top_sort: &Sort,
        explicitly_anywhere: bool,
    ) -> Result<ParsedTerm, ParseError> {
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
        let anywhere_top = anywhere
            .then(|| self.top_rewrite_node(&term))
            .flatten()
            .map(std::ptr::from_ref);
        let mut solver = Solver::new(&order);
        let inferred = solver.infer(self, &term, anywhere_top, "root")?;
        // Synthetic rule-grammar result sorts describe parser context, not bounds on a
        // rewrite's formal result parameter. Concrete caller sorts remain real constraints.
        if is_real_ground_sort(top_sort) || !solver.is_parameter_ref(&inferred) {
            solver.constrain(inferred, SortRef::Concrete(top_sort.clone()))?;
        }
        let variable_sorts = solver.realize_variables()?;
        let parameter_sorts = solver.realize_parameters()?;
        let mut next_anonymous = 0;
        self.insert_inferred_casts(
            term,
            &variable_sorts,
            &parameter_sorts,
            false,
            &mut next_anonymous,
            "root",
        )
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
                signature_is_monomorphic(production)
                    && children
                        .iter()
                        .all(|child| self.sort_inference_supported(child))
            }
            ParsedTerm::InstantiatedProduction { .. } => {
                unreachable!("sort support is checked before inference")
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
                let local = !signature_is_monomorphic(descriptor);
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
        self.function_lhs(term).is_some()
    }

    pub(super) fn function_lhs<'a>(&self, term: &'a ParsedTerm) -> Option<&'a ParsedTerm> {
        let rewrite = self.top_rewrite(term)?;
        let lhs = strip_brackets(self, rewrite.0);
        let ParsedTerm::Production { production, .. } = lhs else {
            return None;
        };
        let production = &self.productions[*production];
        (production.function || production.macro_like).then_some(lhs)
    }

    fn top_rewrite<'a>(&self, term: &'a ParsedTerm) -> Option<(&'a ParsedTerm, &'a ParsedTerm)> {
        let term = self.top_rewrite_node(term)?;
        let ParsedTerm::Production { children, .. } = term else {
            unreachable!("top_rewrite_node returns a production")
        };
        Some((&children[0], &children[1]))
    }

    fn top_rewrite_node<'a>(&self, term: &'a ParsedTerm) -> Option<&'a ParsedTerm> {
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
                .then_some(term);
        }
    }

    fn insert_inferred_casts(
        &self,
        term: ParsedTerm,
        variable_sorts: &BTreeMap<VariableId, Sort>,
        parameter_sorts: &BTreeMap<String, Vec<Sort>>,
        existing_cast: bool,
        next_anonymous: &mut usize,
        path: &str,
    ) -> Result<ParsedTerm, ParseError> {
        match term {
            ParsedTerm::Term(ref leaf) if inferred_variable_name(leaf).is_some() => {
                let Some(name) = inferred_variable_name(leaf) else {
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
                let descriptor = &self.productions[production];
                let is_cast = descriptor
                    .label
                    .as_ref()
                    .is_some_and(|label| label.name.starts_with("#SemanticCastTo"));
                let children = children
                    .into_iter()
                    .enumerate()
                    .map(|(index, child)| {
                        self.insert_inferred_casts(
                            child,
                            variable_sorts,
                            parameter_sorts,
                            is_cast,
                            next_anonymous,
                            &format!("{path}_c{index}"),
                        )
                    })
                    .collect::<Result<_, _>>()?;
                if descriptor.parametric_origin.is_some() {
                    let parameters = parameter_sorts.get(path).cloned().ok_or_else(|| {
                        inference_error(format!(
                            "no inferred parameters were produced for production at {path}"
                        ))
                    })?;
                    Ok(ParsedTerm::InstantiatedProduction {
                        production,
                        parameters,
                        children,
                        metadata,
                    })
                } else {
                    Ok(ParsedTerm::Production {
                        production,
                        children,
                        metadata,
                    })
                }
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
            parameters: Vec::new(),
            constraint_cache: BTreeSet::new(),
            next_anonymous: 0,
        }
    }

    fn infer(
        &mut self,
        grammar: &Grammar,
        term: &ParsedTerm,
        anywhere_top: Option<*const ParsedTerm>,
        path: &str,
    ) -> Result<SortRef, ParseError> {
        match term {
            ParsedTerm::Ambiguity(_) => Err(inference_error(
                "portable sort inference does not support ambiguous parse forests",
            )),
            ParsedTerm::Term(term) => match (inferred_variable_name(term), term.unannotated()) {
                (Some(name), _) => self.variable(name),
                (None, Term::Token { sort, .. }) => Ok(SortRef::Concrete(sort.clone())),
                (None, _) => Err(inference_error(
                    "unexpected lowered KAST node in the concrete parse forest",
                )),
            },
            ParsedTerm::Production {
                production,
                children,
                ..
            } => {
                let production = &grammar.productions[*production];
                let parameter_slots = production.parametric_origin.as_ref().map(|origin| {
                    origin
                        .parameters
                        .iter()
                        .map(|_| self.fresh_slot())
                        .collect::<Vec<_>>()
                });
                if let Some(slots) = &parameter_slots {
                    self.parameters.push((path.to_owned(), slots.clone()));
                }
                let parameter_substitution = production
                    .parametric_origin
                    .as_ref()
                    .zip(parameter_slots.as_ref())
                    .map(|(origin, slots)| {
                        origin
                            .parameters
                            .iter()
                            .cloned()
                            .zip(slots.iter().copied().map(SortRef::Variable))
                            .collect::<BTreeMap<_, _>>()
                    })
                    .unwrap_or_default();
                let child_sorts = children
                    .iter()
                    .enumerate()
                    .map(|(index, child)| {
                        self.infer(grammar, child, anywhere_top, &format!("{path}_c{index}"))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let (expected, actual) = if let Some(origin) = &production.parametric_origin {
                    (
                        origin
                            .items
                            .iter()
                            .filter_map(|item| match item {
                                ProductionItem::NonTerminal { sort, .. } => {
                                    Some(substitute_sort_ref(sort, &parameter_substitution))
                                }
                                ProductionItem::Terminal(_)
                                | ProductionItem::RegexTerminal { .. } => None,
                            })
                            .collect::<Vec<_>>(),
                        substitute_sort_ref(&origin.result, &parameter_substitution),
                    )
                } else {
                    (
                        production
                            .items
                            .iter()
                            .filter_map(|item| match item {
                                Item::NonTerminal(sort) => Some(SortRef::Concrete(sort.clone())),
                                Item::Terminal(_) | Item::Regex { .. } => None,
                            })
                            .collect::<Vec<_>>(),
                        SortRef::Concrete(production.result.clone()),
                    )
                };
                if expected.len() != child_sorts.len() {
                    return Err(inference_error(format!(
                        "production {:?} has {} nonterminals but its parse node has {} children",
                        production.parse_label,
                        expected.len(),
                        child_sorts.len()
                    )));
                }
                let anywhere_lhs_sort = (anywhere_top.is_some_and(|top| std::ptr::eq(term, top))
                    && production
                        .label
                        .as_ref()
                        .is_some_and(|label| label.name == "#KRewrite")
                    && children.len() == 2)
                    .then(|| {
                        if matches!(
                            strip_brackets(grammar, &children[0]),
                            ParsedTerm::Term(term)
                                if matches!(term.unannotated(), Term::Variable { .. })
                        ) {
                            SortRef::Concrete(Sort::new("K"))
                        } else {
                            child_sorts[0].clone()
                        }
                    });
                for (index, ((term, child), expected)) in children
                    .iter()
                    .zip(child_sorts.iter().cloned())
                    .zip(expected.iter().cloned())
                    .enumerate()
                {
                    let expected = if index == 1
                        && let Some(lhs_sort) = &anywhere_lhs_sort
                    {
                        lhs_sort.clone()
                    } else {
                        expected
                    };
                    if is_anonymous_leaf(term) {
                        // Scala's inferencer treats every anonymous occurrence as having exactly
                        // the sort required by its context.  A mere upper bound is insufficient
                        // for parser sorts such as KItem, whose synthetic hierarchy is not always
                        // represented by an ordinary subsort production.
                        self.constrain(child.clone(), expected.clone())?;
                        self.constrain(expected, child)?;
                    } else if !(self.is_parameter_ref(&child)
                        && matches!(
                            &expected,
                            SortRef::Concrete(sort) if !is_real_ground_sort(sort)
                        ))
                    {
                        // Rule-grammar scaffolding sorts carry parser context, not semantic sort
                        // bounds for a formal production parameter. The Z3 engine and reference
                        // SimpleSub path likewise keep that parameter independent of the wrapper.
                        self.constrain(child, expected)?;
                    }
                }
                if let Some(lhs_sort) = anywhere_lhs_sort
                    && !matches!(&actual, SortRef::Concrete(sort) if !is_real_ground_sort(sort))
                {
                    // A monomorphic #KRewrite may return #RuleK, which is parser scaffolding.
                    // Only semantic results (including formal parameters) inherit the LHS bound.
                    self.constrain(actual.clone(), lhs_sort)?;
                }
                if production.label.as_ref().is_some_and(|label| {
                    matches!(
                        label.name.as_str(),
                        "#SyntacticCast" | "#SyntacticCastBraced"
                    )
                }) && let Some(child) = expected.first()
                {
                    self.constrain(actual.clone(), child.clone())?;
                    self.constrain(child.clone(), actual.clone())?;
                }
                Ok(actual)
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

    fn fresh_slot(&mut self) -> usize {
        let variable = self.bounds.len();
        self.bounds.push(Bounds::default());
        variable
    }

    fn is_parameter_ref(&self, sort: &SortRef) -> bool {
        let SortRef::Variable(variable) = sort else {
            return false;
        };
        self.parameters
            .iter()
            .any(|(_, slots)| slots.contains(variable))
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

    fn realize_parameters(&self) -> Result<BTreeMap<String, Vec<Sort>>, ParseError> {
        self.parameters
            .iter()
            .map(|(path, slots)| {
                slots
                    .iter()
                    .map(|slot| self.realize_variable(*slot))
                    .collect::<Result<Vec<_>, _>>()
                    .map(|sorts| (path.clone(), sorts))
            })
            .collect()
    }

    fn realize_variable(&self, variable: usize) -> Result<Sort, ParseError> {
        if self.bounds[variable].lower.is_empty() && self.bounds[variable].upper.is_empty() {
            return Ok(Sort::new("K"));
        }
        let upper = self.concrete_bounds(variable, true, &mut BTreeSet::new());
        let lower = self.concrete_bounds(variable, false, &mut BTreeSet::new());
        if upper.is_empty() && lower.is_empty() {
            return Ok(Sort::new("K"));
        }
        let k = Sort::new("K");
        if upper.is_empty() && lower.iter().all(|bound| self.order.less_than_eq(bound, &k)) {
            return Ok(k);
        }
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

fn signature_is_monomorphic(production: &Production) -> bool {
    if let Some(origin) = &production.parametric_origin {
        let bare = |sort: &Sort| origin.parameters.contains(sort) || sort.parameters.is_empty();
        bare(&origin.result)
            && origin.items.iter().all(|item| {
                !matches!(
                    item,
                    ProductionItem::NonTerminal { sort, .. } if !bare(sort)
                )
            })
    } else {
        production.result.parameters.is_empty()
            && production
                .items
                .iter()
                .all(|item| !matches!(item, Item::NonTerminal(sort) if !sort.parameters.is_empty()))
    }
}

fn substitute_sort_ref(sort: &Sort, substitution: &BTreeMap<Sort, SortRef>) -> SortRef {
    substitution
        .get(sort)
        .cloned()
        .unwrap_or_else(|| SortRef::Concrete(sort.clone()))
}

fn is_real_ground_sort(sort: &Sort) -> bool {
    !sort.parameters.is_empty()
        || !super::is_parser_sort(sort)
        || matches!(sort.name.as_str(), "K" | "KItem" | "KLabel")
        || sort.name.parse::<u64>().is_ok()
}

#[cfg(feature = "z3-inference")]
fn checked_inference_requested() -> bool {
    std::env::var("KRUST_TYPE_INFERENCE_MODE").as_deref() == Ok("checked")
}

#[cfg(feature = "z3-inference")]
fn checked_inference_result(
    portable: Result<ParsedTerm, ParseError>,
    z3: Result<ParsedTerm, ParseError>,
) -> Result<ParsedTerm, ParseError> {
    match (portable, z3) {
        (Ok(portable), Ok(z3)) if portable == z3 => Ok(portable),
        (Err(portable), Err(_)) => Err(portable),
        (Ok(portable), Ok(z3)) => Err(inference_error(format!(
            "portable and Z3 sort inference produced different terms: portable {portable:?}; Z3 {z3:?}"
        ))),
        (Ok(portable), Err(z3)) => Err(inference_error(format!(
            "portable and Z3 sort inference disagree: portable accepted {portable:?}; Z3 rejected with {z3}"
        ))),
        (Err(portable), Ok(z3)) => Err(inference_error(format!(
            "portable and Z3 sort inference disagree: portable rejected with {portable}; Z3 accepted {z3:?}"
        ))),
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::definition::Attributes;
    use crate::kast::{Label, TermMetadata};

    use super::super::ParametricOrigin;

    fn nonterminal(sort: &str) -> ProductionItem {
        ProductionItem::NonTerminal {
            sort: Sort::new(sort),
            name: None,
        }
    }

    fn parametric_rewrite_grammar() -> (Grammar, usize, usize, usize, usize) {
        let mut grammar = Grammar::default();
        let constant = |grammar: &mut Grammar, sort: &str, label: &str| {
            let index = grammar.productions.len();
            grammar
                .add(
                    Sort::new(sort),
                    vec![ProductionItem::Terminal(label.into())],
                    Some(Label::new(label)),
                    false,
                    false,
                )
                .unwrap();
            index
        };
        let a = constant(&mut grammar, "A", "a");
        let b = constant(&mut grammar, "B", "b");
        let foo = grammar.productions.len();
        grammar
            .add(
                Sort::new("Foo"),
                vec![nonterminal("Base")],
                Some(Label::new("foo")),
                false,
                false,
            )
            .unwrap();
        let rewrite = grammar.productions.len();
        grammar
            .add(
                Sort::new("Base"),
                vec![nonterminal("Base"), nonterminal("Base")],
                Some(Label::new("#KRewrite")),
                false,
                false,
            )
            .unwrap();
        let parameter = Sort::new("S");
        grammar.productions[rewrite].parametric_origin = Some(ParametricOrigin {
            label: Some(Label::new("#KRewrite")),
            parameters: vec![parameter.clone()],
            result: parameter.clone(),
            items: vec![
                ProductionItem::NonTerminal {
                    sort: parameter.clone(),
                    name: None,
                },
                ProductionItem::Terminal("=>".into()),
                ProductionItem::NonTerminal {
                    sort: parameter.clone(),
                    name: None,
                },
            ],
            attributes: Attributes::default(),
            substitution: BTreeMap::from([(parameter, Sort::new("Base"))]),
        });
        grammar.subsort_relations.extend([
            (Sort::new("A"), Sort::new("Base")),
            (Sort::new("B"), Sort::new("Base")),
            (Sort::new("Base"), Sort::new("K")),
            (Sort::new("Foo"), Sort::new("K")),
        ]);
        (grammar, a, b, foo, rewrite)
    }

    fn production(production: usize, children: Vec<ParsedTerm>) -> ParsedTerm {
        ParsedTerm::Production {
            production,
            children,
            metadata: TermMetadata::default(),
        }
    }

    fn packed_production(production: usize, children: Vec<Rc<PackedTerm>>) -> Rc<PackedTerm> {
        PackedTerm::production(production, children, TermMetadata::default())
    }

    #[test]
    fn rewrite_rules_without_ambiguity_take_the_portable_path() {
        let (grammar, a, b, _, rewrite) = parametric_rewrite_grammar();
        let forest = packed_production(
            rewrite,
            vec![packed_production(a, vec![]), packed_production(b, vec![])],
        );

        assert!(grammar.packed_sort_inference_supported(&forest));
        assert!(grammar.sort_inference_supported(&forest.unpack()));
        assert!(
            !grammar.packed_sort_inference_supported(&PackedTerm::ambiguity(BTreeSet::from([
                forest,
                packed_production(a, vec![])
            ]),))
        );
        assert!(
            !grammar.packed_sort_inference_supported(&PackedTerm::leaf(Term::Token {
                token: "1p6".into(),
                sort: Sort::with_parameters("MInt", vec![Sort::new("6")]),
            },))
        );
    }

    #[test]
    fn portable_anywhere_bound_applies_to_the_top_rewrite_only() {
        let (grammar, a, b, foo, rewrite) = parametric_rewrite_grammar();
        let leaf = |index| production(index, vec![]);
        let nested = production(rewrite, vec![leaf(a), leaf(b)]);
        let lhs = production(foo, vec![nested]);
        let rhs = production(foo, vec![leaf(b)]);
        let body = production(rewrite, vec![lhs, rhs]);

        grammar
            .infer_sorts_portable(body, &Sort::new("K"), true)
            .expect("the nested rewrite gets only its ordinary parameter bounds");

        let widening = production(rewrite, vec![leaf(a), leaf(b)]);
        grammar
            .infer_sorts_portable(widening, &Sort::new("K"), true)
            .expect_err("the top rewrite RHS cannot widen beyond its declared LHS sort");
    }

    #[test]
    fn portable_function_bound_uses_the_inferred_parametric_lhs_sort() {
        let mut grammar = Grammar::default();
        let false_token = grammar.productions.len();
        grammar
            .add(
                Sort::new("Bool"),
                vec![ProductionItem::Terminal("false".into())],
                Some(Label::new("false")),
                false,
                false,
            )
            .unwrap();
        let k_value = grammar.productions.len();
        grammar
            .add(
                Sort::new("K"),
                vec![ProductionItem::Terminal("k".into())],
                Some(Label::new("k")),
                false,
                false,
            )
            .unwrap();
        let equals = grammar.productions.len();
        grammar
            .add(
                Sort::new("Bag"),
                vec![nonterminal("K"), nonterminal("K")],
                Some(Label::new("#Equals")),
                false,
                false,
            )
            .unwrap();
        grammar.productions[equals].function = true;
        let operand = Sort::new("S");
        let result = Sort::new("R");
        grammar.productions[equals].parametric_origin = Some(ParametricOrigin {
            label: Some(Label::new("#Equals")),
            parameters: vec![operand.clone(), result.clone()],
            result: result.clone(),
            items: vec![
                ProductionItem::NonTerminal {
                    sort: operand.clone(),
                    name: None,
                },
                ProductionItem::NonTerminal {
                    sort: operand.clone(),
                    name: None,
                },
            ],
            attributes: Attributes::default(),
            substitution: BTreeMap::from([(operand, Sort::new("K")), (result, Sort::new("Bag"))]),
        });
        let rewrite = grammar.productions.len();
        grammar
            .add(
                Sort::new("K"),
                vec![nonterminal("K"), nonterminal("K")],
                Some(Label::new("#KRewrite")),
                false,
                false,
            )
            .unwrap();
        let parameter = Sort::new("P");
        grammar.productions[rewrite].parametric_origin = Some(ParametricOrigin {
            label: Some(Label::new("#KRewrite")),
            parameters: vec![parameter.clone()],
            result: parameter.clone(),
            items: vec![
                ProductionItem::NonTerminal {
                    sort: parameter.clone(),
                    name: None,
                },
                ProductionItem::NonTerminal {
                    sort: parameter.clone(),
                    name: None,
                },
            ],
            attributes: Attributes::default(),
            substitution: BTreeMap::from([(parameter, Sort::new("K"))]),
        });
        grammar.subsort_relations.extend([
            (Sort::new("Bool"), Sort::new("K")),
            (Sort::new("K"), Sort::new("Bag")),
        ]);
        let lhs = production(
            equals,
            vec![
                production(false_token, vec![]),
                production(false_token, vec![]),
            ],
        );
        let body = production(rewrite, vec![lhs, production(k_value, vec![])]);

        let inferred = grammar
            .infer_sorts_portable(body, &Sort::new("#RuleBody"), false)
            .unwrap();
        let ParsedTerm::InstantiatedProduction {
            parameters,
            children,
            ..
        } = inferred
        else {
            panic!("the rewrite should retain its inferred parameter")
        };
        assert_eq!(parameters, [Sort::new("K")]);
        assert!(matches!(
            &children[0],
            ParsedTerm::InstantiatedProduction { parameters, .. }
                if parameters == &[Sort::new("K"), Sort::new("K")]
        ));
    }

    #[cfg(feature = "z3-inference")]
    #[test]
    fn checked_mode_requires_exact_cross_engine_agreement() {
        let x = ParsedTerm::Term(Term::variable("X"));
        let y = ParsedTerm::Term(Term::variable("Y"));

        assert_eq!(
            checked_inference_result(Ok(x.clone()), Ok(x.clone())),
            Ok(x.clone())
        );
        assert!(matches!(
            checked_inference_result(
                Err(inference_error("portable rejection")),
                Err(inference_error("Z3 rejection")),
            ),
            Err(ParseError::SortInference { ref message }) if message == "portable rejection"
        ));
        assert!(matches!(
            checked_inference_result(Ok(x.clone()), Ok(y)),
            Err(ParseError::SortInference { ref message })
                if message.contains("produced different terms")
        ));
        assert!(matches!(
            checked_inference_result(Ok(x), Err(inference_error("Z3 rejection"))),
            Err(ParseError::SortInference { ref message })
                if message.contains("portable accepted") && message.contains("Z3 rejected")
        ));
    }
}
