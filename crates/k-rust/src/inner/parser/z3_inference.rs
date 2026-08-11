//! Native Z3-backed sort inference for ambiguous and parametric parse forests.

use std::collections::{BTreeMap, BTreeSet};

use z3::ast::{Ast, Bool, Datatype};
use z3::{DatatypeAccessor, DatatypeBuilder, DatatypeSort, Model, SatResult, Solver};

use crate::definition::{PartialOrder, SortHead};
use crate::kast::{Sort, Term};

use super::{Grammar, Item, ParseError, ParsedTerm, Production};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CastContext {
    None,
    Semantic,
    Strict,
}

struct Encoding<'a> {
    grammar: &'a Grammar,
    datatype: DatatypeSort,
    heads: Vec<SortHead>,
    head_indexes: BTreeMap<SortHead, usize>,
    ground_sorts: BTreeSet<Sort>,
    semantic: PartialOrder<Sort>,
    syntactic: PartialOrder<Sort>,
    variables: BTreeMap<String, Datatype>,
    parameters: BTreeSet<String>,
    anywhere: bool,
}

impl Grammar {
    pub(super) fn infer_sorts_z3(
        &self,
        term: ParsedTerm,
        top_sort: &Sort,
        explicitly_anywhere: bool,
    ) -> Result<ParsedTerm, ParseError> {
        let anywhere = explicitly_anywhere || self.lhs_is_function_or_macro(&term);
        let mut encoding = Encoding::new(self, &term, top_sort, anywhere)?;
        let expected = encoding.sort_value(top_sort, &BTreeMap::new())?;
        let constraint = encoding.constraint(&term, &expected, CastContext::None, "root")?;
        if encoding.variables.is_empty() {
            return Ok(term);
        }

        let solver = Solver::new();
        solver.assert(&constraint);
        encoding.exclude_klabel_parameters(&solver)?;
        encoding.apply_soft_preferences(&solver)?;
        match solver.check() {
            SatResult::Unsat => {
                return Err(z3_error(
                    "no well-sorted parse or variable assignment exists",
                ));
            }
            SatResult::Unknown => {
                return Err(z3_error(format!(
                    "Z3 could not solve sort constraints{}",
                    solver
                        .get_reason_unknown()
                        .map(|reason| format!(": {reason}"))
                        .unwrap_or_default()
                )));
            }
            SatResult::Sat => {}
        }

        let models = encoding.maximal_models(&solver)?;
        let mut candidates = BTreeSet::new();
        let mut first_error = None;
        for model in models {
            match encoding.apply_model(term.clone(), top_sort, CastContext::None, "root", &model) {
                Ok(candidate) => {
                    candidates.insert(candidate);
                }
                Err(error) => {
                    first_error.get_or_insert(error);
                }
            }
        }
        match candidates.len() {
            0 => Err(first_error.unwrap_or_else(|| {
                z3_error("Z3 produced no well-typed parse after model substitution")
            })),
            1 => Ok(candidates.pop_first().expect("length was one")),
            _ => Ok(ParsedTerm::Ambiguity(candidates)),
        }
    }
}

impl<'a> Encoding<'a> {
    fn new(
        grammar: &'a Grammar,
        term: &ParsedTerm,
        top_sort: &Sort,
        anywhere: bool,
    ) -> Result<Self, ParseError> {
        let semantic = PartialOrder::new(grammar.subsort_relations.iter().cloned())
            .map_err(|cycle| ParseError::CircularSubsorts { path: cycle.path })?;
        let syntactic = PartialOrder::new(grammar.syntactic_subsort_relations.iter().cloned())
            .map_err(|cycle| ParseError::CircularSubsorts { path: cycle.path })?;
        let mut heads = BTreeSet::new();
        let mut ground_sorts = BTreeSet::new();
        collect_sort(top_sort, &mut heads, &mut ground_sorts);
        for (lesser, greater) in grammar
            .subsort_relations
            .iter()
            .chain(&grammar.syntactic_subsort_relations)
        {
            collect_sort(lesser, &mut heads, &mut ground_sorts);
            collect_sort(greater, &mut heads, &mut ground_sorts);
        }
        for production in &grammar.productions {
            collect_sort(&production.result, &mut heads, &mut ground_sorts);
            for sort in nonterminal_sorts(production) {
                collect_sort(sort, &mut heads, &mut ground_sorts);
            }
            if let Some(origin) = &production.parametric_origin {
                collect_parametric_sort(&origin.result, &origin.parameters, &mut heads);
                for item in &origin.items {
                    if let crate::definition::ProductionItem::NonTerminal { sort, .. } = item {
                        collect_parametric_sort(sort, &origin.parameters, &mut heads);
                    }
                }
            }
        }
        collect_term_sorts(term, &mut heads, &mut ground_sorts);
        if heads.is_empty() {
            heads.insert(SortHead::nullary("K"));
            ground_sorts.insert(Sort::new("K"));
        }
        let heads = heads.into_iter().collect::<Vec<_>>();
        let head_indexes = heads
            .iter()
            .cloned()
            .enumerate()
            .map(|(index, head)| (head, index))
            .collect::<BTreeMap<_, _>>();
        let mut builder = DatatypeBuilder::new("KRustInferenceSort");
        for (index, head) in heads.iter().enumerate() {
            let field_names = (0..head.parameters())
                .map(|parameter| format!("sort_{index}_parameter_{parameter}"))
                .collect::<Vec<_>>();
            let fields = field_names
                .iter()
                .map(|name| {
                    (
                        name.as_str(),
                        DatatypeAccessor::datatype("KRustInferenceSort"),
                    )
                })
                .collect();
            builder = builder.variant(&format!("KSort{index}"), fields);
        }
        let datatype = builder.finish();
        Ok(Self {
            grammar,
            datatype,
            heads,
            head_indexes,
            ground_sorts,
            semantic,
            syntactic,
            variables: BTreeMap::new(),
            parameters: BTreeSet::new(),
            anywhere,
        })
    }

    fn constraint(
        &mut self,
        term: &ParsedTerm,
        expected: &Datatype,
        cast_context: CastContext,
        path: &str,
    ) -> Result<Bool, ParseError> {
        match term {
            ParsedTerm::Ambiguity(alternatives) => {
                let constraints = alternatives
                    .iter()
                    .enumerate()
                    .map(|(index, alternative)| {
                        self.constraint(
                            alternative,
                            expected,
                            cast_context,
                            &format!("{path}_a{index}"),
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(or_all(&constraints))
            }
            ParsedTerm::Term(term) => match term.unannotated() {
                Term::Variable { name, .. } => {
                    let variable = self.term_variable(name, path);
                    Ok(match cast_context {
                        CastContext::Strict => variable.eq(expected),
                        CastContext::None | CastContext::Semantic => {
                            self.less_than_eq(&variable, expected, false)?
                        }
                    })
                }
                Term::Token { sort, .. } => {
                    let actual = self.sort_value(sort, &BTreeMap::new())?;
                    Ok(match cast_context {
                        CastContext::Strict => actual.eq(expected),
                        CastContext::None | CastContext::Semantic => {
                            self.less_than_eq(&actual, expected, false)?
                        }
                    })
                }
                _ => Err(z3_error(
                    "unexpected lowered KAST node in the concrete parse forest",
                )),
            },
            ParsedTerm::Production {
                production,
                children,
                ..
            } => {
                let descriptor = &self.grammar.productions[*production];
                let parameters = self.production_parameters(descriptor, path);
                let actual_sort = production_result(descriptor);
                let actual = self.sort_value(actual_sort, &parameters)?;
                let mut constraints = Vec::new();
                if is_real_sort(actual_sort, parameters.keys()) {
                    let strict = cast_context == CastContext::Strict
                        || descriptor.parametric_origin.as_ref().is_some_and(|origin| {
                            origin
                                .parameters
                                .iter()
                                .any(|parameter| parameter == actual_sort)
                        });
                    constraints.push(if strict {
                        actual.eq(expected)
                    } else {
                        self.less_than_eq(&actual, expected, false)?
                    });
                }

                let expected_children = production_nonterminals(descriptor);
                if expected_children.len() != children.len() {
                    return Err(z3_error(format!(
                        "production {:?} has {} nonterminals but its parse node has {} children",
                        descriptor.parse_label,
                        expected_children.len(),
                        children.len()
                    )));
                }
                let child_context = cast_context_for(descriptor);
                for (index, (child, child_sort)) in
                    children.iter().zip(expected_children).enumerate()
                {
                    let child_path = format!("{path}_c{index}");
                    let child_expected = if self.anywhere
                        && descriptor
                            .label
                            .as_ref()
                            .is_some_and(|label| label.name == "#KRewrite")
                        && index == 1
                        && children.len() == 2
                    {
                        self.actual_sort(&children[0], &format!("{path}_c0"))?
                    } else if is_cast(descriptor) {
                        self.sort_value(production_result(descriptor), &parameters)?
                    } else {
                        self.sort_value(child_sort, &parameters)?
                    };
                    constraints.push(self.constraint(
                        child,
                        &child_expected,
                        child_context,
                        &child_path,
                    )?);
                }
                Ok(and_all(&constraints))
            }
            ParsedTerm::InstantiatedProduction { .. } => {
                unreachable!("Z3 constraints are generated before model substitution")
            }
        }
    }

    fn actual_sort(&mut self, term: &ParsedTerm, path: &str) -> Result<Datatype, ParseError> {
        match term {
            ParsedTerm::Production { production, .. } => {
                let descriptor = &self.grammar.productions[*production];
                let parameters = self.production_parameters(descriptor, path);
                self.sort_value(production_result(descriptor), &parameters)
            }
            ParsedTerm::Term(term) => match term.unannotated() {
                Term::Token { sort, .. } => self.sort_value(sort, &BTreeMap::new()),
                Term::Variable { name, .. } => Ok(self.term_variable(name, path)),
                _ => Err(z3_error("cannot determine the sort of this KAST node")),
            },
            ParsedTerm::Ambiguity(_) => Err(z3_error(
                "cannot determine one declared sort for an ambiguous rewrite left-hand side",
            )),
            ParsedTerm::InstantiatedProduction { .. } => {
                unreachable!("actual sorts are requested before model substitution")
            }
        }
    }

    fn production_parameters(
        &mut self,
        production: &Production,
        path: &str,
    ) -> BTreeMap<Sort, Datatype> {
        let Some(origin) = &production.parametric_origin else {
            return BTreeMap::new();
        };
        origin
            .parameters
            .iter()
            .enumerate()
            .map(|(index, parameter)| {
                let name = format!("parameter_{path}_{index}");
                let value = self
                    .variables
                    .entry(name.clone())
                    .or_insert_with(|| Datatype::new_const(name.clone(), &self.datatype.sort))
                    .clone();
                self.parameters.insert(name);
                (parameter.clone(), value)
            })
            .collect()
    }

    fn term_variable(&mut self, name: &str, path: &str) -> Datatype {
        let key = if is_anonymous(name) {
            format!("anonymous_{path}")
        } else {
            format!("variable_{name}")
        };
        self.variables
            .entry(key.clone())
            .or_insert_with(|| Datatype::new_const(key, &self.datatype.sort))
            .clone()
    }

    fn sort_value(
        &self,
        sort: &Sort,
        parameters: &BTreeMap<Sort, Datatype>,
    ) -> Result<Datatype, ParseError> {
        if let Some(value) = parameters.get(sort) {
            return Ok(value.clone());
        }
        let head = SortHead::from(sort);
        let index =
            self.head_indexes.get(&head).copied().ok_or_else(|| {
                z3_error(format!("sort head {head} is missing from the Z3 datatype"))
            })?;
        let arguments = sort
            .parameters
            .iter()
            .map(|parameter| self.sort_value(parameter, parameters))
            .collect::<Result<Vec<_>, _>>()?;
        let references = arguments
            .iter()
            .map(|argument| argument as &dyn Ast)
            .collect::<Vec<_>>();
        self.datatype.variants[index]
            .constructor
            .apply(&references)
            .as_datatype()
            .ok_or_else(|| z3_error(format!("failed to construct Z3 value for sort {sort}")))
    }

    fn less_than_eq(
        &self,
        lesser: &Datatype,
        greater: &Datatype,
        syntactic: bool,
    ) -> Result<Bool, ParseError> {
        let order = if syntactic {
            &self.syntactic
        } else {
            &self.semantic
        };
        let mut relations = Vec::new();
        for left in &self.ground_sorts {
            if !is_real_ground_sort(left) {
                continue;
            }
            for right in &self.ground_sorts {
                if !is_real_ground_sort(right) {
                    continue;
                }
                if left == right || order.less_than_eq(left, right) {
                    let left = self.sort_value(left, &BTreeMap::new())?;
                    let right = self.sort_value(right, &BTreeMap::new())?;
                    relations.push(Bool::and(&[lesser.eq(&left), greater.eq(&right)]));
                }
            }
        }
        Ok(or_all(&relations))
    }

    fn exclude_klabel_parameters(&self, solver: &Solver) -> Result<(), ParseError> {
        if !self.head_indexes.contains_key(&SortHead::nullary("KLabel")) {
            return Ok(());
        }
        let klabel = self.sort_value(&Sort::new("KLabel"), &BTreeMap::new())?;
        for parameter in &self.parameters {
            let value = self
                .variables
                .get(parameter)
                .expect("parameters are also inference variables");
            solver.assert(value.ne(&klabel));
        }
        Ok(())
    }

    fn apply_soft_preferences(&self, solver: &Solver) -> Result<(), ParseError> {
        let mut constraints = Vec::new();
        for preferred in ["K", "KItem", "Bag"] {
            let sort = Sort::new(preferred);
            if !self.ground_sorts.contains(&sort) {
                continue;
            }
            let preferred = self.sort_value(&sort, &BTreeMap::new())?;
            for variable in self.variables.values() {
                constraints.push(self.less_than_eq(&preferred, variable, false)?);
            }
        }
        if constraints.is_empty() {
            return Ok(());
        }

        // Scala gives these equal-weight soft constraints the same optimization
        // group. Find and then require the greatest satisfiable cardinality so
        // the result does not depend on traversal order.
        let weighted = constraints
            .iter()
            .map(|constraint| (constraint, 1))
            .collect::<Vec<_>>();
        let mut low = 0;
        let mut high = constraints.len();
        while low < high {
            let candidate = low + (high - low).div_ceil(2);
            solver.push();
            solver.assert(Bool::pb_ge(&weighted, candidate as i32));
            let status = solver.check();
            solver.pop(1);
            match status {
                SatResult::Sat => low = candidate,
                SatResult::Unsat => high = candidate - 1,
                SatResult::Unknown => {
                    return Err(z3_error(
                        "Z3 returned unknown while applying sort-inference preferences",
                    ));
                }
            }
        }
        solver.assert(Bool::pb_ge(&weighted, low as i32));
        Ok(())
    }

    fn maximal_models(&self, solver: &Solver) -> Result<Vec<BTreeMap<String, Sort>>, ParseError> {
        let real_variables = self
            .variables
            .keys()
            .filter(|name| !self.parameters.contains(*name))
            .cloned()
            .collect::<Vec<_>>();
        let mut models = Vec::new();
        loop {
            match solver.check() {
                SatResult::Unsat => break,
                SatResult::Unknown => {
                    return Err(z3_error(
                        "Z3 returned unknown while enumerating sort models",
                    ));
                }
                SatResult::Sat => {}
            }
            let mut values = self.read_model(
                &solver
                    .get_model()
                    .ok_or_else(|| z3_error("Z3 returned sat without a model"))?,
            )?;
            loop {
                solver.push();
                let greater = real_variables
                    .iter()
                    .map(|name| {
                        let current = self.sort_value(
                            values
                                .get(name)
                                .expect("all inference variables have model values"),
                            &BTreeMap::new(),
                        )?;
                        self.less_than_eq(
                            &current,
                            self.variables
                                .get(name)
                                .expect("real variables are registered"),
                            true,
                        )
                    })
                    .collect::<Result<Vec<_>, ParseError>>()?;
                let distinct = real_variables
                    .iter()
                    .map(|name| {
                        let current = self.sort_value(
                            values
                                .get(name)
                                .expect("all inference variables have model values"),
                            &BTreeMap::new(),
                        )?;
                        Ok(self
                            .variables
                            .get(name)
                            .expect("real variables are registered")
                            .ne(&current))
                    })
                    .collect::<Result<Vec<_>, ParseError>>()?;
                solver.assert(and_all(&greater));
                solver.assert(or_all(&distinct));
                let status = solver.check();
                if status == SatResult::Sat {
                    values = self.read_model(
                        &solver
                            .get_model()
                            .ok_or_else(|| z3_error("Z3 returned sat without a model"))?,
                    )?;
                }
                solver.pop(1);
                match status {
                    SatResult::Sat => continue,
                    SatResult::Unsat => break,
                    SatResult::Unknown => {
                        return Err(z3_error(
                            "Z3 returned unknown while maximizing inferred sorts",
                        ));
                    }
                }
            }
            let dominated = real_variables
                .iter()
                .map(|name| {
                    let maximal = self.sort_value(
                        values
                            .get(name)
                            .expect("all inference variables have model values"),
                        &BTreeMap::new(),
                    )?;
                    self.less_than_eq(
                        self.variables
                            .get(name)
                            .expect("real variables are registered"),
                        &maximal,
                        true,
                    )
                })
                .collect::<Result<Vec<_>, ParseError>>()?;
            solver.assert(and_all(&dominated).not());
            models.push(values);
            if real_variables.is_empty() {
                break;
            }
        }
        Ok(models)
    }

    fn read_model(&self, model: &Model) -> Result<BTreeMap<String, Sort>, ParseError> {
        self.variables
            .iter()
            .map(|(name, variable)| {
                let value = model
                    .eval(variable, true)
                    .ok_or_else(|| z3_error(format!("Z3 omitted a value for {name}")))?;
                self.decode_sort(&value).map(|sort| (name.clone(), sort))
            })
            .collect()
    }

    fn decode_sort(&self, value: &Datatype) -> Result<Sort, ParseError> {
        let constructor = value.decl().name();
        let index = constructor
            .strip_prefix("KSort")
            .and_then(|index| index.parse::<usize>().ok())
            .filter(|index| *index < self.heads.len())
            .ok_or_else(|| z3_error(format!("unexpected Z3 sort constructor {constructor:?}")))?;
        let parameters = value
            .children()
            .into_iter()
            .map(|child| {
                child
                    .as_datatype()
                    .ok_or_else(|| z3_error("Z3 sort constructor had a non-sort child"))
                    .and_then(|child| self.decode_sort(&child))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let head = &self.heads[index];
        if parameters.len() != head.parameters() {
            return Err(z3_error(format!(
                "Z3 constructor for {head} returned {} parameters",
                parameters.len()
            )));
        }
        Ok(Sort::with_parameters(head.as_str(), parameters))
    }

    fn apply_model(
        &self,
        term: ParsedTerm,
        expected: &Sort,
        cast_context: CastContext,
        path: &str,
        model: &BTreeMap<String, Sort>,
    ) -> Result<ParsedTerm, ParseError> {
        match term {
            ParsedTerm::Ambiguity(alternatives) => {
                let mut retained = BTreeSet::new();
                let mut first_error = None;
                for (index, alternative) in alternatives.into_iter().enumerate() {
                    match self.apply_model(
                        alternative,
                        expected,
                        cast_context,
                        &format!("{path}_a{index}"),
                        model,
                    ) {
                        Ok(alternative) => {
                            retained.insert(alternative);
                        }
                        Err(error) => {
                            first_error.get_or_insert(error);
                        }
                    }
                }
                match retained.len() {
                    0 => Err(first_error
                        .unwrap_or_else(|| z3_error("all ambiguity alternatives were ill-sorted"))),
                    1 => Ok(retained.pop_first().expect("length was one")),
                    _ => Ok(ParsedTerm::Ambiguity(retained)),
                }
            }
            ParsedTerm::Term(ref leaf) if matches!(leaf.unannotated(), Term::Variable { .. }) => {
                let Term::Variable { name, .. } = leaf.unannotated() else {
                    unreachable!()
                };
                let key = if is_anonymous(name) {
                    format!("anonymous_{path}")
                } else {
                    format!("variable_{name}")
                };
                let inferred = model
                    .get(&key)
                    .ok_or_else(|| z3_error(format!("Z3 omitted a sort for variable {name}")))?;
                self.check_sort(inferred, expected, cast_context)?;
                if cast_context == CastContext::Semantic {
                    return Ok(term);
                }
                self.wrap_with_cast(term, inferred)
            }
            ParsedTerm::Term(ref leaf) if matches!(leaf.unannotated(), Term::Token { .. }) => {
                let Term::Token { sort, .. } = leaf.unannotated() else {
                    unreachable!()
                };
                self.check_sort(sort, expected, cast_context)?;
                Ok(term)
            }
            ParsedTerm::Term(_) => Err(z3_error(
                "unexpected lowered KAST node during Z3 model substitution",
            )),
            ParsedTerm::Production {
                production,
                children,
                metadata,
            } => {
                let descriptor = &self.grammar.productions[production];
                let parameter_values = descriptor
                    .parametric_origin
                    .as_ref()
                    .map(|origin| {
                        origin
                            .parameters
                            .iter()
                            .enumerate()
                            .map(|(index, parameter)| {
                                let name = format!("parameter_{path}_{index}");
                                model
                                    .get(&name)
                                    .cloned()
                                    .map(|value| (parameter.clone(), value))
                                    .ok_or_else(|| {
                                        z3_error(format!(
                                            "Z3 omitted production parameter {parameter}"
                                        ))
                                    })
                            })
                            .collect::<Result<BTreeMap<_, _>, _>>()
                    })
                    .transpose()?
                    .unwrap_or_default();
                let actual = substitute_sort(production_result(descriptor), &parameter_values);
                if is_real_ground_sort(&actual) {
                    self.check_sort(&actual, expected, cast_context)?;
                }
                let expected_children = production_nonterminals(descriptor);
                let child_context = cast_context_for(descriptor);
                let anywhere_lhs_sort = (self.anywhere
                    && descriptor
                        .label
                        .as_ref()
                        .is_some_and(|label| label.name == "#KRewrite")
                    && children.len() == 2)
                    .then(|| {
                        declared_model_sort(
                            self.grammar,
                            &children[0],
                            model,
                            &format!("{path}_c0"),
                        )
                    });
                let children = children
                    .into_iter()
                    .zip(expected_children)
                    .enumerate()
                    .map(|(index, (child, child_sort))| {
                        let child_expected = if index == 1
                            && let Some(lhs_sort) = &anywhere_lhs_sort
                        {
                            lhs_sort.clone()
                        } else if is_cast(descriptor) {
                            actual.clone()
                        } else {
                            substitute_sort(child_sort, &parameter_values)
                        };
                        self.apply_model(
                            child,
                            &child_expected,
                            child_context,
                            &format!("{path}_c{index}"),
                            model,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let inferred_parameters = descriptor
                    .parametric_origin
                    .as_ref()
                    .map(|origin| {
                        origin
                            .parameters
                            .iter()
                            .map(|parameter| {
                                parameter_values
                                    .get(parameter)
                                    .cloned()
                                    .expect("every formal parameter has a model value")
                            })
                            .collect::<Vec<_>>()
                    })
                    .unwrap_or_default();
                let result = if descriptor.parametric_origin.is_some() {
                    ParsedTerm::InstantiatedProduction {
                        production,
                        parameters: inferred_parameters,
                        children,
                        metadata,
                    }
                } else {
                    ParsedTerm::Production {
                        production,
                        children,
                        metadata,
                    }
                };
                if descriptor.parametric_origin.is_some()
                    && (!actual.parameters.is_empty()
                        || production_nonterminals(descriptor)
                            .iter()
                            .any(|sort| !sort.parameters.is_empty()))
                    && cast_context != CastContext::Semantic
                {
                    self.wrap_with_cast(result, &actual)
                } else {
                    Ok(result)
                }
            }
            ParsedTerm::InstantiatedProduction { .. } => {
                unreachable!("a model is applied only once")
            }
        }
    }

    fn check_sort(
        &self,
        actual: &Sort,
        expected: &Sort,
        context: CastContext,
    ) -> Result<(), ParseError> {
        let valid = if context == CastContext::Strict {
            actual == expected
        } else {
            actual == expected || self.semantic.less_than_eq(actual, expected)
        };
        if valid {
            Ok(())
        } else {
            Err(z3_error(format!(
                "unexpected sort {actual}; expected {}{expected}",
                if context == CastContext::Strict {
                    "exactly "
                } else {
                    "a subsort of "
                }
            )))
        }
    }

    fn wrap_with_cast(&self, term: ParsedTerm, sort: &Sort) -> Result<ParsedTerm, ParseError> {
        let label = format!("#SemanticCastTo{sort}");
        let production = self
            .grammar
            .productions
            .iter()
            .enumerate()
            .find_map(|(index, production)| {
                (production
                    .label
                    .as_ref()
                    .is_some_and(|candidate| candidate.name == label)
                    && nonterminal_sorts(production).len() == 1)
                    .then_some(index)
            })
            .ok_or_else(|| {
                z3_error(format!(
                    "cannot record inferred sort {sort}: missing semantic-cast production"
                ))
            })?;
        Ok(ParsedTerm::Production {
            production,
            children: vec![term],
            metadata: super::TermMetadata::default(),
        })
    }
}

fn production_result(production: &Production) -> &Sort {
    production
        .parametric_origin
        .as_ref()
        .map_or(&production.result, |origin| &origin.result)
}

fn production_nonterminals(production: &Production) -> Vec<&Sort> {
    if let Some(origin) = &production.parametric_origin {
        origin
            .items
            .iter()
            .filter_map(|item| match item {
                crate::definition::ProductionItem::NonTerminal { sort, .. } => Some(sort),
                _ => None,
            })
            .collect()
    } else {
        nonterminal_sorts(production)
    }
}

fn nonterminal_sorts(production: &Production) -> Vec<&Sort> {
    production
        .items
        .iter()
        .filter_map(|item| match item {
            Item::NonTerminal(sort) => Some(sort),
            Item::Terminal(_) | Item::Regex { .. } => None,
        })
        .collect()
}

fn cast_context_for(production: &Production) -> CastContext {
    match production.label.as_ref().map(|label| label.name.as_str()) {
        Some(label) if label.starts_with("#SemanticCastTo") => CastContext::Semantic,
        Some("#SyntacticCast" | "#SyntacticCastBraced") => CastContext::Strict,
        _ => CastContext::None,
    }
}

fn is_cast(production: &Production) -> bool {
    cast_context_for(production) != CastContext::None
}

fn substitute_sort(sort: &Sort, parameters: &BTreeMap<Sort, Sort>) -> Sort {
    parameters.get(sort).cloned().unwrap_or_else(|| Sort {
        name: sort.name.clone(),
        parameters: sort
            .parameters
            .iter()
            .map(|parameter| substitute_sort(parameter, parameters))
            .collect(),
    })
}

fn declared_model_sort(
    grammar: &Grammar,
    term: &ParsedTerm,
    model: &BTreeMap<String, Sort>,
    path: &str,
) -> Sort {
    match term {
        ParsedTerm::Production { production, .. } => {
            let descriptor = &grammar.productions[*production];
            let parameters = descriptor
                .parametric_origin
                .as_ref()
                .map(|origin| {
                    origin
                        .parameters
                        .iter()
                        .enumerate()
                        .filter_map(|(index, parameter)| {
                            model
                                .get(&format!("parameter_{path}_{index}"))
                                .cloned()
                                .map(|value| (parameter.clone(), value))
                        })
                        .collect()
                })
                .unwrap_or_default();
            substitute_sort(production_result(descriptor), &parameters)
        }
        ParsedTerm::Term(term) => match term.unannotated() {
            Term::Token { sort, .. } => sort.clone(),
            Term::Variable { name, .. } => {
                let key = if is_anonymous(name) {
                    format!("anonymous_{path}")
                } else {
                    format!("variable_{name}")
                };
                model.get(&key).cloned().unwrap_or_else(|| Sort::new("K"))
            }
            _ => Sort::new("K"),
        },
        ParsedTerm::InstantiatedProduction { production, .. } => {
            grammar.productions[*production].result.clone()
        }
        ParsedTerm::Ambiguity(_) => Sort::new("K"),
    }
}

fn collect_sort(sort: &Sort, heads: &mut BTreeSet<SortHead>, ground: &mut BTreeSet<Sort>) {
    heads.insert(SortHead::from(sort));
    ground.insert(sort.clone());
    for parameter in &sort.parameters {
        collect_sort(parameter, heads, ground);
    }
}

fn collect_parametric_sort(sort: &Sort, formals: &[Sort], heads: &mut BTreeSet<SortHead>) {
    if formals.contains(sort) {
        return;
    }
    heads.insert(SortHead::from(sort));
    for parameter in &sort.parameters {
        collect_parametric_sort(parameter, formals, heads);
    }
}

fn collect_term_sorts(
    term: &ParsedTerm,
    heads: &mut BTreeSet<SortHead>,
    ground: &mut BTreeSet<Sort>,
) {
    match term {
        ParsedTerm::Term(term) => {
            if let Term::Token { sort, .. } = term.unannotated() {
                collect_sort(sort, heads, ground);
            }
        }
        ParsedTerm::Production { children, .. }
        | ParsedTerm::InstantiatedProduction { children, .. } => {
            for child in children {
                collect_term_sorts(child, heads, ground);
            }
        }
        ParsedTerm::Ambiguity(alternatives) => {
            for alternative in alternatives {
                collect_term_sorts(alternative, heads, ground);
            }
        }
    }
}

fn is_real_sort<'a>(sort: &Sort, formals: impl Iterator<Item = &'a Sort>) -> bool {
    if formals.into_iter().any(|formal| formal == sort) {
        return true;
    }
    is_real_ground_sort(sort)
}

fn is_real_ground_sort(sort: &Sort) -> bool {
    !sort.parameters.is_empty()
        || !is_parser_sort(sort)
        || matches!(sort.name.as_str(), "K" | "KItem" | "KLabel")
        || sort.name.parse::<u64>().is_ok()
}

fn is_parser_sort(sort: &Sort) -> bool {
    matches!(
        sort.name.as_str(),
        "KBott" | "K" | "KLabel" | "KList" | "KItem" | "KConfigVar" | "KString"
    ) || sort.name.starts_with('#')
        || sort.name.parse::<u64>().is_ok()
}

fn is_anonymous(name: &str) -> bool {
    name.starts_with('_')
        || name.starts_with("?_")
        || name.starts_with("!_")
        || name.starts_with("@_")
}

fn and_all(items: &[Bool]) -> Bool {
    if items.is_empty() {
        Bool::from_bool(true)
    } else {
        Bool::and(items)
    }
}

fn or_all(items: &[Bool]) -> Bool {
    if items.is_empty() {
        Bool::from_bool(false)
    } else {
        Bool::or(items)
    }
}

fn z3_error(message: impl Into<String>) -> ParseError {
    ParseError::SortInference {
        message: message.into(),
    }
}
