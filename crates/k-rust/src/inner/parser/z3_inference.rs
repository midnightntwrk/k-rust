//! Native Z3-backed sort inference for ambiguous and parametric parse forests.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use z3::ast::{Ast, Bool, Datatype};
use z3::{DatatypeAccessor, DatatypeBuilder, DatatypeSort, Model, SatResult, Solver};

use crate::definition::{PartialOrder, SortHead};
use crate::kast::{Sort, Term};

use super::{
    Grammar, Item, PackedNode, PackedTerm, ParseError, ParsedTerm, Production,
    cmp_packed_structurally, packed_terms_in_structural_order,
};

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum CastContext {
    None,
    Semantic,
    Strict,
    Parser,
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
    packed_ids: HashMap<*const PackedTerm, usize>,
    anywhere: bool,
}

type PackedConstraintKey = (*const PackedTerm, Datatype, CastContext);
type PackedConstraintMemo =
    HashMap<PackedConstraintKey, (Rc<PackedTerm>, Result<Bool, ParseError>)>;
type PackedModelKey = (*const PackedTerm, Sort, CastContext);
type PackedModelMemo =
    BTreeMap<PackedModelKey, (Rc<PackedTerm>, Result<Rc<PackedTerm>, ParseError>)>;

impl Grammar {
    pub(super) fn infer_packed_sorts_z3(
        &self,
        term: Rc<PackedTerm>,
        top_sort: &Sort,
        explicitly_anywhere: bool,
    ) -> Result<ParsedTerm, ParseError> {
        let anywhere = explicitly_anywhere || self.packed_lhs_is_function_or_macro(&term);
        let mut encoding = Encoding::new_packed(self, &term, top_sort, anywhere)?;
        let expected = encoding.sort_value(top_sort, &BTreeMap::new())?;
        let root_context = if !is_real_ground_sort(top_sort) {
            CastContext::Parser
        } else {
            CastContext::None
        };
        let constraint =
            encoding.constraint_packed(&term, &expected, root_context, &mut HashMap::new())?;

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
            match encoding.apply_model_packed(
                Rc::clone(&term),
                top_sort,
                root_context,
                &model,
                &mut BTreeMap::new(),
            ) {
                Ok(candidate) => {
                    candidates.insert(candidate);
                }
                Err(error) => {
                    first_error.get_or_insert(error);
                }
            }
        }
        if candidates.is_empty() {
            return Err(first_error.unwrap_or_else(|| {
                z3_error("Z3 produced no well-typed parse after model substitution")
            }));
        }
        let inferred =
            self.factor_pre_inference_packed_ambiguities(PackedTerm::ambiguity(candidates));
        Ok(inferred.unpack())
    }

    fn packed_lhs_is_function_or_macro(&self, root: &Rc<PackedTerm>) -> bool {
        let mut term = strip_packed_brackets(self, root);
        loop {
            let PackedNode::Production {
                production,
                children,
                ..
            } = &term.node
            else {
                return false;
            };
            let descriptor = &self.productions[*production];
            if descriptor.result.name == "#RuleContent" {
                let Some(child) = children.first() else {
                    return false;
                };
                term = strip_packed_brackets(self, child);
                continue;
            }
            if descriptor.result.name == "#RuleBody"
                && descriptor
                    .label
                    .as_ref()
                    .is_some_and(|label| label.name == "#withConfig")
            {
                let Some(child) = children.first() else {
                    return false;
                };
                term = strip_packed_brackets(self, child);
                continue;
            }
            if !descriptor
                .label
                .as_ref()
                .is_some_and(|label| label.name == "#KRewrite")
                || children.len() != 2
            {
                return false;
            }
            let lhs = strip_packed_brackets(self, &children[0]);
            let PackedNode::Production { production, .. } = &lhs.node else {
                return false;
            };
            let lhs = &self.productions[*production];
            return lhs.function || lhs.macro_like;
        }
    }

    pub(super) fn infer_sorts_z3(
        &self,
        term: ParsedTerm,
        top_sort: &Sort,
        explicitly_anywhere: bool,
    ) -> Result<ParsedTerm, ParseError> {
        let anywhere = explicitly_anywhere || self.lhs_is_function_or_macro(&term);
        let mut encoding = Encoding::new(self, &term, top_sort, anywhere)?;
        let expected = encoding.sort_value(top_sort, &BTreeMap::new())?;
        let root_context = if !is_real_ground_sort(top_sort) {
            CastContext::Parser
        } else {
            CastContext::None
        };
        let constraint = encoding.constraint(&term, &expected, root_context, "root")?;
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
            match encoding.apply_model(term.clone(), top_sort, root_context, "root", &model) {
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
        Self::new_with_term_sorts(grammar, top_sort, anywhere, |heads, ground| {
            collect_term_sorts(term, heads, ground);
        })
    }

    fn new_packed(
        grammar: &'a Grammar,
        term: &Rc<PackedTerm>,
        top_sort: &Sort,
        anywhere: bool,
    ) -> Result<Self, ParseError> {
        let mut encoding =
            Self::new_with_term_sorts(grammar, top_sort, anywhere, |heads, ground| {
                collect_packed_term_sorts(term, heads, ground);
            })?;
        encoding.packed_ids = packed_term_ids(term);
        Ok(encoding)
    }

    fn new_with_term_sorts(
        grammar: &'a Grammar,
        top_sort: &Sort,
        anywhere: bool,
        collect_terms: impl FnOnce(&mut BTreeSet<SortHead>, &mut BTreeSet<Sort>),
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
        collect_terms(&mut heads, &mut ground_sorts);
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
            packed_ids: HashMap::new(),
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
                    let variable = self.term_variable(term, name, path);
                    Ok(match (is_anonymous(name), cast_context) {
                        // Anonymous occurrences are independent variables, but each one has the
                        // exact sort demanded by its context in the reference inferencer.
                        (true, _) | (_, CastContext::Strict) => variable.eq(expected),
                        (false, CastContext::Parser) => Bool::from_bool(true),
                        (false, CastContext::None | CastContext::Semantic) => {
                            self.less_than_eq(&variable, expected, false)?
                        }
                    })
                }
                Term::Token { sort, .. } => {
                    let actual = self.sort_value(sort, &BTreeMap::new())?;
                    Ok(match cast_context {
                        CastContext::Strict => actual.eq(expected),
                        CastContext::Parser => Bool::from_bool(true),
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
                metadata,
            } => {
                let descriptor = &self.grammar.productions[*production];
                let parameters =
                    self.production_parameters(*production, descriptor, metadata, path);
                let actual_sort = production_result(descriptor);
                let actual = self.sort_value(actual_sort, &parameters)?;
                let mut constraints = Vec::new();
                if cast_context != CastContext::Parser
                    && is_real_sort(actual_sort, parameters.keys())
                {
                    let strict = cast_context == CastContext::Strict
                        || descriptor
                            .parametric_origin
                            .as_ref()
                            .is_some_and(|origin| origin.parameters.contains(&origin.result));
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
                    let child_context = match cast_context_for(descriptor) {
                        CastContext::None if !is_real_ground_sort(child_sort) => {
                            CastContext::Parser
                        }
                        context => context,
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

    fn constraint_packed(
        &mut self,
        term: &Rc<PackedTerm>,
        expected: &Datatype,
        cast_context: CastContext,
        memo: &mut PackedConstraintMemo,
    ) -> Result<Bool, ParseError> {
        let identity = Rc::as_ptr(term);
        let key = (identity, expected.clone(), cast_context);
        if let Some((_, constraint)) = memo.get(&key) {
            return constraint.clone();
        }
        let result = (|| match &term.node {
            PackedNode::Ambiguity(alternatives) => {
                let constraints = packed_terms_in_structural_order(alternatives)
                    .into_iter()
                    .map(|alternative| {
                        self.constraint_packed(&alternative, expected, cast_context, memo)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(or_all(&constraints))
            }
            PackedNode::Term(leaf) => match leaf.unannotated() {
                Term::Variable { name, .. } => {
                    let variable = self.packed_term_variable(leaf, name, identity);
                    Ok(match (is_anonymous(name), cast_context) {
                        (true, _) | (_, CastContext::Strict) => variable.eq(expected),
                        (false, CastContext::Parser) => Bool::from_bool(true),
                        (false, CastContext::None | CastContext::Semantic) => {
                            self.less_than_eq(&variable, expected, false)?
                        }
                    })
                }
                Term::Token { sort, .. } => {
                    let actual = self.sort_value(sort, &BTreeMap::new())?;
                    Ok(match cast_context {
                        CastContext::Strict => actual.eq(expected),
                        CastContext::Parser => Bool::from_bool(true),
                        CastContext::None | CastContext::Semantic => {
                            self.less_than_eq(&actual, expected, false)?
                        }
                    })
                }
                _ => Err(z3_error(
                    "unexpected lowered KAST node in the packed parse forest",
                )),
            },
            PackedNode::Production {
                production,
                children,
                metadata,
            } => {
                let descriptor = &self.grammar.productions[*production];
                let parameters =
                    self.packed_production_parameters(*production, descriptor, metadata, identity);
                let actual_sort = production_result(descriptor);
                let actual = self.sort_value(actual_sort, &parameters)?;
                let mut constraints = Vec::new();
                if cast_context != CastContext::Parser
                    && is_real_sort(actual_sort, parameters.keys())
                {
                    let strict = cast_context == CastContext::Strict
                        || descriptor
                            .parametric_origin
                            .as_ref()
                            .is_some_and(|origin| origin.parameters.contains(&origin.result));
                    constraints.push(if strict {
                        actual.eq(expected)
                    } else {
                        self.less_than_eq(&actual, expected, false)?
                    });
                }
                let expected_children = production_nonterminals(descriptor);
                if expected_children.len() != children.len() {
                    return Err(z3_error(format!(
                        "production {:?} has {} nonterminals but its packed node has {} children",
                        descriptor.parse_label,
                        expected_children.len(),
                        children.len()
                    )));
                }
                for (index, (child, child_sort)) in
                    children.iter().zip(expected_children).enumerate()
                {
                    let child_expected = if self.anywhere
                        && descriptor
                            .label
                            .as_ref()
                            .is_some_and(|label| label.name == "#KRewrite")
                        && index == 1
                        && children.len() == 2
                    {
                        self.actual_packed_sort(&children[0])?
                    } else if is_cast(descriptor) {
                        self.sort_value(production_result(descriptor), &parameters)?
                    } else {
                        self.sort_value(child_sort, &parameters)?
                    };
                    let child_context = match cast_context_for(descriptor) {
                        CastContext::None if !is_real_ground_sort(child_sort) => {
                            CastContext::Parser
                        }
                        context => context,
                    };
                    constraints.push(self.constraint_packed(
                        child,
                        &child_expected,
                        child_context,
                        memo,
                    )?);
                }
                Ok(and_all(&constraints))
            }
            PackedNode::InstantiatedProduction { .. } => {
                unreachable!("constraints are generated before model application")
            }
        })();
        memo.insert(key, (Rc::clone(term), result.clone()));
        result
    }

    fn actual_packed_sort(&mut self, term: &Rc<PackedTerm>) -> Result<Datatype, ParseError> {
        match &term.node {
            PackedNode::Production {
                production,
                metadata,
                ..
            } => {
                let descriptor = &self.grammar.productions[*production];
                let parameters = self.packed_production_parameters(
                    *production,
                    descriptor,
                    metadata,
                    Rc::as_ptr(term),
                );
                self.sort_value(production_result(descriptor), &parameters)
            }
            PackedNode::Term(leaf) => match leaf.unannotated() {
                Term::Token { sort, .. } => self.sort_value(sort, &BTreeMap::new()),
                Term::Variable { name, .. } => {
                    Ok(self.packed_term_variable(leaf, name, Rc::as_ptr(term)))
                }
                _ => Err(z3_error("cannot determine the sort of this KAST node")),
            },
            PackedNode::Ambiguity(_) => Err(z3_error(
                "cannot determine one declared sort for an ambiguous rewrite left-hand side",
            )),
            PackedNode::InstantiatedProduction { .. } => {
                unreachable!("actual sorts are requested before model application")
            }
        }
    }

    fn packed_production_parameters(
        &mut self,
        production_index: usize,
        production: &Production,
        metadata: &super::TermMetadata,
        identity: *const PackedTerm,
    ) -> BTreeMap<Sort, Datatype> {
        let Some(origin) = &production.parametric_origin else {
            return BTreeMap::new();
        };
        origin
            .parameters
            .iter()
            .enumerate()
            .map(|(index, parameter)| {
                let name = packed_inference_parameter_key(
                    production_index,
                    metadata,
                    self.packed_id(identity),
                    index,
                );
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

    fn packed_term_variable(
        &mut self,
        term: &Term,
        name: &str,
        identity: *const PackedTerm,
    ) -> Datatype {
        let key = packed_inference_variable_key(term, name, self.packed_id(identity));
        self.variables
            .entry(key.clone())
            .or_insert_with(|| Datatype::new_const(key, &self.datatype.sort))
            .clone()
    }

    fn packed_id(&self, identity: *const PackedTerm) -> usize {
        self.packed_ids
            .get(&identity)
            .copied()
            .expect("every reachable packed term received a stable inference identity")
    }

    fn actual_sort(&mut self, term: &ParsedTerm, path: &str) -> Result<Datatype, ParseError> {
        match term {
            ParsedTerm::Production {
                production,
                metadata,
                ..
            } => {
                let descriptor = &self.grammar.productions[*production];
                let parameters =
                    self.production_parameters(*production, descriptor, metadata, path);
                self.sort_value(production_result(descriptor), &parameters)
            }
            ParsedTerm::Term(term) => match term.unannotated() {
                Term::Token { sort, .. } => self.sort_value(sort, &BTreeMap::new()),
                Term::Variable { name, .. } => Ok(self.term_variable(term, name, path)),
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
        production_index: usize,
        production: &Production,
        metadata: &super::TermMetadata,
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
                let name = inference_parameter_key(production_index, metadata, path, index);
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

    fn term_variable(&mut self, term: &Term, name: &str, path: &str) -> Datatype {
        let key = inference_variable_key(term, name, path);
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

    fn apply_model_packed(
        &self,
        term: Rc<PackedTerm>,
        expected: &Sort,
        cast_context: CastContext,
        model: &BTreeMap<String, Sort>,
        memo: &mut PackedModelMemo,
    ) -> Result<Rc<PackedTerm>, ParseError> {
        let identity = Rc::as_ptr(&term);
        let key = (identity, expected.clone(), cast_context);
        if let Some((_, result)) = memo.get(&key) {
            return result.clone();
        }
        let result = (|| match &term.node {
            PackedNode::Ambiguity(alternatives) => {
                let mut retained = BTreeSet::new();
                let mut errors = Vec::new();
                for alternative in packed_terms_in_structural_order(alternatives) {
                    match self.apply_model_packed(
                        Rc::clone(&alternative),
                        expected,
                        cast_context,
                        model,
                        memo,
                    ) {
                        Ok(alternative) => match &alternative.node {
                            PackedNode::Ambiguity(nested) => {
                                retained.extend(nested.iter().cloned());
                            }
                            _ => {
                                retained.insert(alternative);
                            }
                        },
                        Err(error) => errors.push((alternative, error)),
                    }
                }
                if retained.is_empty() {
                    Err(errors
                        .into_iter()
                        .min_by(|(left, _), (right, _)| cmp_packed_structurally(left, right))
                        .map(|(_, error)| error)
                        .unwrap_or_else(|| z3_error("all ambiguity alternatives were ill-sorted")))
                } else {
                    Ok(PackedTerm::ambiguity(retained))
                }
            }
            PackedNode::Term(leaf) if matches!(leaf.unannotated(), Term::Variable { .. }) => {
                let Term::Variable { name, .. } = leaf.unannotated() else {
                    unreachable!()
                };
                let key = packed_inference_variable_key(leaf, name, self.packed_id(identity));
                let inferred = model
                    .get(&key)
                    .ok_or_else(|| z3_error(format!("Z3 omitted a sort for variable {name}")))?;
                self.check_sort(inferred, expected, cast_context)?;
                if cast_context == CastContext::Semantic {
                    Ok(Rc::clone(&term))
                } else {
                    self.wrap_with_packed_cast(Rc::clone(&term), inferred)
                }
            }
            PackedNode::Term(leaf) if matches!(leaf.unannotated(), Term::Token { .. }) => {
                let Term::Token { sort, .. } = leaf.unannotated() else {
                    unreachable!()
                };
                self.check_sort(sort, expected, cast_context)?;
                Ok(Rc::clone(&term))
            }
            PackedNode::Term(_) => Err(z3_error(
                "unexpected lowered KAST node during packed Z3 model substitution",
            )),
            PackedNode::Production {
                production,
                children,
                metadata,
            } => {
                let descriptor = &self.grammar.productions[*production];
                let parameter_values = descriptor
                    .parametric_origin
                    .as_ref()
                    .map(|origin| {
                        origin
                            .parameters
                            .iter()
                            .enumerate()
                            .map(|(index, parameter)| {
                                let name = packed_inference_parameter_key(
                                    *production,
                                    metadata,
                                    self.packed_id(identity),
                                    index,
                                );
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
                let anywhere_lhs_sort = (self.anywhere
                    && descriptor
                        .label
                        .as_ref()
                        .is_some_and(|label| label.name == "#KRewrite")
                    && children.len() == 2)
                    .then(|| self.declared_packed_model_sort(&children[0], model));
                let transformed_children = children
                    .iter()
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
                        let child_context = match cast_context_for(descriptor) {
                            CastContext::None if !is_real_ground_sort(child_sort) => {
                                CastContext::Parser
                            }
                            context => context,
                        };
                        self.apply_model_packed(
                            Rc::clone(child),
                            &child_expected,
                            child_context,
                            model,
                            memo,
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
                let transformed = if descriptor.parametric_origin.is_some() {
                    PackedTerm::instantiated_production(
                        *production,
                        inferred_parameters,
                        transformed_children,
                        metadata.clone(),
                    )
                } else {
                    PackedTerm::production(*production, transformed_children, metadata.clone())
                };
                if descriptor.parametric_origin.is_some()
                    && (!actual.parameters.is_empty()
                        || production_nonterminals(descriptor)
                            .iter()
                            .any(|sort| !sort.parameters.is_empty()))
                    && cast_context != CastContext::Semantic
                {
                    self.wrap_with_packed_cast(transformed, &actual)
                } else {
                    Ok(transformed)
                }
            }
            PackedNode::InstantiatedProduction { .. } => {
                unreachable!("a model is applied only once")
            }
        })();
        memo.insert(key, (term, result.clone()));
        result
    }

    fn declared_packed_model_sort(
        &self,
        term: &Rc<PackedTerm>,
        model: &BTreeMap<String, Sort>,
    ) -> Sort {
        match &term.node {
            PackedNode::Production {
                production,
                metadata,
                ..
            } => {
                let descriptor = &self.grammar.productions[*production];
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
                                    .get(&packed_inference_parameter_key(
                                        *production,
                                        metadata,
                                        self.packed_id(Rc::as_ptr(term)),
                                        index,
                                    ))
                                    .cloned()
                                    .map(|value| (parameter.clone(), value))
                            })
                            .collect()
                    })
                    .unwrap_or_default();
                substitute_sort(production_result(descriptor), &parameters)
            }
            PackedNode::Term(leaf) => match leaf.unannotated() {
                Term::Token { sort, .. } => sort.clone(),
                Term::Variable { name, .. } => model
                    .get(&packed_inference_variable_key(
                        leaf,
                        name,
                        self.packed_id(Rc::as_ptr(term)),
                    ))
                    .cloned()
                    .unwrap_or_else(|| Sort::new("K")),
                _ => Sort::new("K"),
            },
            PackedNode::Ambiguity(_) => Sort::new("K"),
            PackedNode::InstantiatedProduction { production, .. } => {
                self.grammar.productions[*production].result.clone()
            }
        }
    }

    fn wrap_with_packed_cast(
        &self,
        term: Rc<PackedTerm>,
        sort: &Sort,
    ) -> Result<Rc<PackedTerm>, ParseError> {
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
        Ok(PackedTerm::production(
            production,
            vec![term],
            super::TermMetadata::default(),
        ))
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
                let key = inference_variable_key(leaf, name, path);
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
                                let name =
                                    inference_parameter_key(production, &metadata, path, index);
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
                        let child_context = match cast_context_for(descriptor) {
                            CastContext::None if !is_real_ground_sort(child_sort) => {
                                CastContext::Parser
                            }
                            context => context,
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
        let valid = match context {
            CastContext::Parser => true,
            CastContext::Strict => actual == expected,
            CastContext::None | CastContext::Semantic => {
                actual == expected || self.semantic.less_than_eq(actual, expected)
            }
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
        ParsedTerm::Production {
            production,
            metadata,
            ..
        } => {
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
                                .get(&inference_parameter_key(*production, metadata, path, index))
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
                let key = inference_variable_key(term, name, path);
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

fn collect_packed_term_sorts(
    root: &Rc<PackedTerm>,
    heads: &mut BTreeSet<SortHead>,
    ground: &mut BTreeSet<Sort>,
) {
    let mut visited = HashSet::new();
    let mut pending = vec![Rc::clone(root)];
    while let Some(term) = pending.pop() {
        if !visited.insert(Rc::as_ptr(&term)) {
            continue;
        }
        match &term.node {
            PackedNode::Term(term) => {
                if let Term::Token { sort, .. } = term.unannotated() {
                    collect_sort(sort, heads, ground);
                }
            }
            PackedNode::Production { children, .. } => {
                pending.extend(children.iter().cloned());
            }
            PackedNode::Ambiguity(alternatives) => {
                pending.extend(alternatives.iter().cloned());
            }
            PackedNode::InstantiatedProduction { .. } => {
                unreachable!("sorts are collected before model application")
            }
        }
    }
}

fn packed_term_ids(root: &Rc<PackedTerm>) -> HashMap<*const PackedTerm, usize> {
    fn visit(term: &Rc<PackedTerm>, ids: &mut HashMap<*const PackedTerm, usize>, next: &mut usize) {
        let identity = Rc::as_ptr(term);
        if ids.contains_key(&identity) {
            return;
        }
        ids.insert(identity, *next);
        *next += 1;
        match &term.node {
            PackedNode::Production { children, .. } => {
                for child in children {
                    visit(child, ids, next);
                }
            }
            PackedNode::Ambiguity(alternatives) => {
                for alternative in packed_terms_in_structural_order(alternatives) {
                    visit(&alternative, ids, next);
                }
            }
            PackedNode::Term(_) => {}
            PackedNode::InstantiatedProduction { .. } => {
                unreachable!("packed identities are assigned before model application")
            }
        }
    }

    let mut ids = HashMap::new();
    visit(root, &mut ids, &mut 0);
    ids
}

fn strip_packed_brackets<'a>(
    grammar: &Grammar,
    mut term: &'a Rc<PackedTerm>,
) -> &'a Rc<PackedTerm> {
    while let PackedNode::Production {
        production,
        children,
        ..
    } = &term.node
    {
        if !grammar.productions[*production].bracket || children.len() != 1 {
            break;
        }
        term = &children[0];
    }
    term
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

fn inference_variable_key(term: &Term, name: &str, path: &str) -> String {
    if !is_anonymous(name) {
        return format!("variable_{name}");
    }
    if let Some(span) = term.metadata().and_then(|metadata| metadata.span) {
        // One source occurrence can appear beneath several alternatives in the shared parse
        // forest. K's parser assigns that occurrence one inference variable; using its span here
        // preserves the same identity after our value-based forest representation is factored.
        format!("anonymous_{}_{}", span.start, span.end)
    } else {
        format!("anonymous_{path}")
    }
}

fn packed_inference_variable_key(term: &Term, name: &str, identity: usize) -> String {
    if !is_anonymous(name) {
        return format!("variable_{name}");
    }
    if let Some(span) = term.metadata().and_then(|metadata| metadata.span) {
        format!("anonymous_{}_{}", span.start, span.end)
    } else {
        format!("anonymous_n{identity}")
    }
}

fn inference_parameter_key(
    production: usize,
    metadata: &super::TermMetadata,
    path: &str,
    parameter: usize,
) -> String {
    if let Some(span) = metadata.span {
        format!(
            "parameter_{}_{}_{}_{}",
            production, span.start, span.end, parameter
        )
    } else {
        format!("parameter_{path}_{parameter}")
    }
}

fn packed_inference_parameter_key(
    production: usize,
    metadata: &super::TermMetadata,
    identity: usize,
    parameter: usize,
) -> String {
    if let Some(span) = metadata.span {
        format!(
            "parameter_{}_{}_{}_{}",
            production, span.start, span.end, parameter
        )
    } else {
        format!("parameter_n{identity}_{parameter}")
    }
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
