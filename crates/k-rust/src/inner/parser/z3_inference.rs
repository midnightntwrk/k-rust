//! Native Z3-backed sort inference for ambiguous and parametric parse forests.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use z3::ast::{Ast, Bool, Datatype};
use z3::{DatatypeAccessor, DatatypeBuilder, DatatypeSort, Model, SatResult, Solver};

use crate::definition::{PartialOrder, SortHead};
use crate::kast::{Sort, Term};

use super::{
    Grammar, Item, PackedNode, PackedTerm, ParseError, ParsedTerm, Production,
    cmp_packed_structurally, inferred_variable_name, packed_terms_in_structural_order,
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
    ground_values: RefCell<BTreeMap<Sort, Datatype>>,
    semantic_relation: Vec<(Datatype, Datatype)>,
    syntactic_relation: Vec<(Datatype, Datatype)>,
    variables: BTreeMap<String, Datatype>,
    parameters: BTreeSet<String>,
    /// Soft per-ambiguity preferences for the overload-minimal function-LHS branches.
    packed_overload_preferences: Vec<Bool>,
    packed_ids: HashMap<*const PackedTerm, usize>,
    anywhere: bool,
    top_rewrite_paths: HashSet<String>,
    top_rewrite_ids: HashSet<*const PackedTerm>,
    /// Numeric sort names declared by the grammar as parameters of an instantiated parametric
    /// sort (`Module.definedSorts` keeps the Nat heads of `definedInstantiations`).
    declared_nat_sorts: BTreeSet<String>,
    /// Whether a token leaf was constrained against a ground sort it cannot satisfy, so a term
    /// without variables must still be solved and rejected.
    ill_sorted_ground: bool,
    /// `ExpectedSortsVisitor.isIncremental`: after an unsat check the constraints are rebuilt
    /// one alternative per ambiguity and replayed singly to name the offending term.
    incremental: bool,
    replay: Vec<ReplayConstraint>,
}

const UNSAT_MESSAGE: &str = "no well-sorted parse or variable assignment exists";

/// One constraint of the incremental replay (`TypeInferencer.Constraint`).
struct ReplayConstraint {
    constraint: Bool,
    subject: ReplaySubject,
    expected: Datatype,
}

enum ReplaySubject {
    Variable {
        name: String,
        variable: Datatype,
    },
    Term {
        /// The actual sort value, evaluated in the last satisfiable model; `None` when the
        /// sort is an undeclared Nat instantiation, which `eval` returns unchanged.
        actual: Option<Datatype>,
        undeclared: Option<Sort>,
        production: String,
    },
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
        encoding.top_rewrite_ids = packed_top_rewrites(self, &term);
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
        encoding.restrict_to_real_sorts(&solver);
        let seed = encoding.seed_model(&solver)?;
        match solver.check() {
            SatResult::Unsat => {
                return Err(encoding.explain_unsat_packed(&term, &expected, root_context));
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

        let models = encoding.maximal_models(&solver, seed)?;
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
        self.packed_function_lhs(root).is_some()
    }

    /// The left-hand side of a function or macro rule, looking through the rule-content and
    /// configuration wrappers. Its inferred sort, rather than the declared rule-body sort, bounds
    /// the whole rewrite.
    fn packed_function_lhs<'t>(&self, root: &'t Rc<PackedTerm>) -> Option<&'t Rc<PackedTerm>> {
        let mut term = strip_packed_brackets(self, root);
        loop {
            let PackedNode::Production {
                production,
                children,
                ..
            } = &term.node
            else {
                return None;
            };
            let descriptor = &self.productions[*production];
            if descriptor.result.name == "#RuleContent" {
                term = strip_packed_brackets(self, children.first()?);
                continue;
            }
            if descriptor.result.name == "#RuleBody"
                && descriptor
                    .label
                    .as_ref()
                    .is_some_and(|label| label.name == "#withConfig")
            {
                term = strip_packed_brackets(self, children.first()?);
                continue;
            }
            if !descriptor
                .label
                .as_ref()
                .is_some_and(|label| label.name == "#KRewrite")
                || children.len() != 2
            {
                return None;
            }
            let lhs = strip_packed_brackets(self, &children[0]);
            let PackedNode::Production { production, .. } = &lhs.node else {
                return None;
            };
            let production = &self.productions[*production];
            return (production.function || production.macro_like).then_some(lhs);
        }
    }

    /// The function or macro left-hand side that bounds the first child of a top-sort node, as
    /// `getFunction` (TypeInferencer.java:380-404) finds it: brackets are stripped, a `#KRewrite`
    /// contributes its left-hand side, and the rule wrappers are not looked through. A top-sort
    /// node is one whose result is `#RuleContent` or `#RuleBody` (TypeInferencer.java:592-593),
    /// so `#withConfig` bounds its rewrite exactly as `#RuleContent` bounds a bare rewrite. The
    /// returned path locates the left-hand side relative to `child_path`.
    fn body_function_lhs<'t>(
        &self,
        child: &'t ParsedTerm,
        child_path: &str,
    ) -> Option<(&'t ParsedTerm, String)> {
        let mut path = child_path.to_owned();
        let mut term = self.strip_brackets_with_path(child, &mut path);
        if let ParsedTerm::Production {
            production,
            children,
            ..
        } = term
            && self.productions[*production]
                .label
                .as_ref()
                .is_some_and(|label| label.name == "#KRewrite")
            && children.len() == 2
        {
            path.push_str("_c0");
            term = self.strip_brackets_with_path(&children[0], &mut path);
        }
        let ParsedTerm::Production { production, .. } = term else {
            return None;
        };
        let production = &self.productions[*production];
        (production.function || production.macro_like).then_some((term, path))
    }

    fn strip_brackets_with_path<'t>(
        &self,
        mut term: &'t ParsedTerm,
        path: &mut String,
    ) -> &'t ParsedTerm {
        while let ParsedTerm::Production {
            production,
            children,
            ..
        } = term
            && self.productions[*production].bracket
            && children.len() == 1
        {
            path.push_str("_c0");
            term = &children[0];
        }
        term
    }

    /// The packed twin of [`Grammar::body_function_lhs`]; an ambiguity stops the search as in
    /// `getFunction`.
    fn packed_body_function_lhs<'t>(
        &self,
        child: &'t Rc<PackedTerm>,
    ) -> Option<&'t Rc<PackedTerm>> {
        let mut term = strip_packed_brackets(self, child);
        if let PackedNode::Production {
            production,
            children,
            ..
        } = &term.node
            && self.productions[*production]
                .label
                .as_ref()
                .is_some_and(|label| label.name == "#KRewrite")
            && children.len() == 2
        {
            term = strip_packed_brackets(self, &children[0]);
        }
        let PackedNode::Production { production, .. } = &term.node else {
            return None;
        };
        let production = &self.productions[*production];
        (production.function || production.macro_like).then_some(term)
    }

    pub(super) fn infer_sorts_z3(
        &self,
        term: ParsedTerm,
        top_sort: &Sort,
        explicitly_anywhere: bool,
    ) -> Result<ParsedTerm, ParseError> {
        let anywhere = explicitly_anywhere || self.lhs_is_function_or_macro(&term);
        let mut encoding = Encoding::new(self, &term, top_sort, anywhere)?;
        encoding.top_rewrite_paths = top_rewrite_paths(self, &term);
        let expected = encoding.sort_value(top_sort, &BTreeMap::new())?;
        let root_context = if !is_real_ground_sort(top_sort) {
            CastContext::Parser
        } else {
            CastContext::None
        };
        let constraint = encoding.constraint(&term, &expected, root_context, "root")?;
        if encoding.variables.is_empty() && !encoding.ill_sorted_ground {
            return Ok(term);
        }

        let solver = Solver::new();
        solver.assert(&constraint);
        encoding.exclude_klabel_parameters(&solver)?;
        encoding.restrict_to_real_sorts(&solver);
        let seed = encoding.seed_model(&solver)?;
        match solver.check() {
            SatResult::Unsat => {
                return Err(encoding.explain_unsat(&term, &expected, root_context));
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

        let models = encoding.maximal_models(&solver, seed)?;
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
        // Only the grammar declares sorts; a `MInt{32}` token must not declare its own width.
        let mut declared_nat_sorts = BTreeSet::new();
        for production in &grammar.productions {
            collect_declared_nats(&production.result, &[], &mut declared_nat_sorts);
            for sort in nonterminal_sorts(production) {
                collect_declared_nats(sort, &[], &mut declared_nat_sorts);
            }
            if let Some(origin) = &production.parametric_origin {
                collect_declared_nats(&origin.result, &origin.parameters, &mut declared_nat_sorts);
                for item in &origin.items {
                    if let crate::definition::ProductionItem::NonTerminal { sort, .. } = item {
                        collect_declared_nats(sort, &origin.parameters, &mut declared_nat_sorts);
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
        let mut encoding = Self {
            grammar,
            datatype,
            heads,
            head_indexes,
            ground_sorts,
            semantic,
            syntactic,
            ground_values: RefCell::new(BTreeMap::new()),
            semantic_relation: Vec::new(),
            syntactic_relation: Vec::new(),
            variables: BTreeMap::new(),
            parameters: BTreeSet::new(),
            packed_overload_preferences: Vec::new(),
            packed_ids: HashMap::new(),
            anywhere,
            top_rewrite_paths: HashSet::new(),
            top_rewrite_ids: HashSet::new(),
            declared_nat_sorts,
            ill_sorted_ground: false,
            incremental: false,
            replay: Vec::new(),
        };
        for sort in encoding.ground_sorts.iter() {
            encoding.sort_value(sort, &BTreeMap::new())?;
        }
        encoding.semantic_relation = encoding.order_relation(false)?;
        encoding.syntactic_relation = encoding.order_relation(true)?;
        Ok(encoding)
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
                // Incremental mode explains one branch of an ambiguity, as the reference does.
                let considered = if self.incremental {
                    1
                } else {
                    alternatives.len()
                };
                let constraints = alternatives
                    .iter()
                    .take(considered)
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
            ParsedTerm::Term(term) => match (inferred_variable_name(term), term.unannotated()) {
                (Some(name), _) => {
                    let variable = self.term_variable(term, name, path);
                    self.variable_constraint(variable, name, expected, cast_context)
                }
                (None, Term::Token { sort, .. }) => {
                    self.token_constraint(term, sort, expected, cast_context)
                }
                (None, _) => Err(z3_error(
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
                    let constraint = if strict {
                        actual.eq(expected)
                    } else {
                        self.less_than_eq(&actual, expected, false)?
                    };
                    self.record_replay(
                        &constraint,
                        ReplaySubject::Term {
                            actual: Some(actual.clone()),
                            undeclared: None,
                            production: production_text(descriptor),
                        },
                        expected,
                    );
                    constraints.push(constraint);
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
                    let function_child_sort = (index == 0 && is_top_sort_production(descriptor))
                        .then(|| self.grammar.body_function_lhs(child, &child_path))
                        .flatten();
                    let child_expected = if let Some((lhs, lhs_path)) = &function_child_sort {
                        self.actual_sort(lhs, lhs_path)?
                    } else if self.anywhere
                        && self.top_rewrite_paths.contains(path)
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
                    let formal_child = descriptor
                        .parametric_origin
                        .as_ref()
                        .is_some_and(|origin| origin.parameters.contains(child_sort));
                    let child_context = match cast_context_for(descriptor) {
                        // A semantic cast applied directly to a variable is a declaration of
                        // that variable's exact sort. The reference inferencer emits equality
                        // for this shape, while semantic casts around compound terms remain
                        // ordinary subsort constraints.
                        CastContext::Semantic if matches!(child, ParsedTerm::Term(term) if inferred_variable_name(term).is_some()) => {
                            CastContext::Strict
                        }
                        CastContext::None if function_child_sort.is_some() => CastContext::None,
                        CastContext::None if !formal_child && !is_real_ground_sort(child_sort) => {
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
                let mut alternatives = packed_terms_in_structural_order(alternatives);
                if self.incremental {
                    // Incremental mode explains one branch of an ambiguity, as the reference does.
                    alternatives.truncate(1);
                }
                let constraints = alternatives
                    .iter()
                    .map(|alternative| {
                        self.constraint_packed(alternative, expected, cast_context, memo)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let overloads = alternatives
                    .iter()
                    .map(|alternative| {
                        let lhs = self.grammar.packed_function_lhs(alternative)?;
                        let PackedNode::Production { production, .. } = &lhs.node else {
                            return None;
                        };
                        self.grammar.productions[*production].source_production
                    })
                    .collect::<Option<Vec<_>>>();
                if let Some(overloads) = overloads
                    && !self.incremental
                {
                    let productions = overloads.iter().copied().collect::<BTreeSet<_>>();
                    let minimal = self.grammar.overloads.minimal(productions.iter());
                    if minimal.len() < productions.len() {
                        let preferred = constraints
                            .iter()
                            .zip(overloads)
                            .filter_map(|(constraint, production)| {
                                minimal.contains(&production).then_some(constraint.clone())
                            })
                            .collect::<Vec<_>>();
                        self.packed_overload_preferences.push(or_all(&preferred));
                    }
                }
                Ok(or_all(&constraints))
            }
            PackedNode::Term(leaf) => match (inferred_variable_name(leaf), leaf.unannotated()) {
                (Some(name), _) => {
                    let variable = self.packed_term_variable(leaf, name, identity);
                    self.variable_constraint(variable, name, expected, cast_context)
                }
                (None, Term::Token { sort, .. }) => {
                    self.token_constraint(leaf, sort, expected, cast_context)
                }
                (None, _) => Err(z3_error(
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
                    let constraint = if strict {
                        actual.eq(expected)
                    } else {
                        self.less_than_eq(&actual, expected, false)?
                    };
                    self.record_replay(
                        &constraint,
                        ReplaySubject::Term {
                            actual: Some(actual.clone()),
                            undeclared: None,
                            production: production_text(descriptor),
                        },
                        expected,
                    );
                    constraints.push(constraint);
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
                    let function_lhs = (index == 0 && is_top_sort_production(descriptor))
                        .then(|| self.grammar.packed_body_function_lhs(child))
                        .flatten();
                    let child_expected = if let Some(lhs) = function_lhs {
                        self.actual_packed_sort(lhs)?
                    } else if self.anywhere
                        && self.top_rewrite_ids.contains(&identity)
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
                    let formal_child = descriptor
                        .parametric_origin
                        .as_ref()
                        .is_some_and(|origin| origin.parameters.contains(child_sort));
                    let child_context = match cast_context_for(descriptor) {
                        CastContext::Semantic if matches!(&child.node, PackedNode::Term(term) if inferred_variable_name(term).is_some()) => {
                            CastContext::Strict
                        }
                        CastContext::None if function_lhs.is_some() => CastContext::None,
                        CastContext::None if !formal_child && !is_real_ground_sort(child_sort) => {
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
            PackedNode::Term(leaf) => match (inferred_variable_name(leaf), leaf.unannotated()) {
                (Some(name), _) => Ok(self.packed_term_variable(leaf, name, Rc::as_ptr(term))),
                (None, Term::Token { sort, .. }) => self.sort_value(sort, &BTreeMap::new()),
                (None, _) => Err(z3_error("cannot determine the sort of this KAST node")),
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
            ParsedTerm::Term(term) => match (inferred_variable_name(term), term.unannotated()) {
                (Some(name), _) => Ok(self.term_variable(term, name, path)),
                (None, Term::Token { sort, .. }) => self.sort_value(sort, &BTreeMap::new()),
                (None, _) => Err(z3_error("cannot determine the sort of this KAST node")),
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

    /// `TypeInferencer.isBadNatSort`: a numeric sort name the grammar never declared as a
    /// parameter of an instantiated sort, at any depth.
    fn is_bad_nat_sort(&self, sort: &Sort) -> bool {
        (sort.name.parse::<u64>().is_ok() && !self.declared_nat_sorts.contains(&sort.name))
            || sort
                .parameters
                .iter()
                .any(|parameter| self.is_bad_nat_sort(parameter))
    }

    fn variable_constraint(
        &mut self,
        variable: Datatype,
        name: &str,
        expected: &Datatype,
        cast_context: CastContext,
    ) -> Result<Bool, ParseError> {
        // The reference grammar reaches a variable under rule scaffolding only through
        // `#RuleBody ::= K` (kast.md:343), a production k-rust's forest collapses, so the
        // scaffolding sort bounds the variable by `K` (TypeInferencer.java:644 with that
        // production's nonterminal; InferenceDriver.java:49-53 for SimpleSub).
        let scaffolding_bound = (cast_context == CastContext::Parser)
            .then(|| self.scaffolding_variable_bound())
            .transpose()?
            .flatten();
        let (expected, cast_context) = match &scaffolding_bound {
            Some(bound) => (bound, CastContext::None),
            None => (expected, cast_context),
        };
        let constraint = match (is_anonymous(name), cast_context) {
            // Anonymous occurrences are independent variables, but each one has the
            // exact sort demanded by its context in the reference inferencer.
            (true, _) | (_, CastContext::Strict) => variable.eq(expected),
            (false, CastContext::Parser) => Bool::from_bool(true),
            (false, CastContext::None | CastContext::Semantic) => {
                self.less_than_eq(&variable, expected, false)?
            }
        };
        if is_anonymous(name) || cast_context != CastContext::Parser {
            self.record_replay(
                &constraint,
                ReplaySubject::Variable {
                    name: name.to_owned(),
                    variable,
                },
                expected,
            );
        }
        Ok(constraint)
    }

    /// The `K` value that bounds a variable expected at a scaffolding sort, when the grammar
    /// declares `K` at all (hand-built test grammars may not).
    fn scaffolding_variable_bound(&self) -> Result<Option<Datatype>, ParseError> {
        let k = Sort::new("K");
        if !self.head_indexes.contains_key(&SortHead::from(&k)) {
            return Ok(None);
        }
        self.sort_value(&k, &BTreeMap::new()).map(Some)
    }

    fn token_constraint(
        &mut self,
        leaf: &Term,
        sort: &Sort,
        expected: &Datatype,
        cast_context: CastContext,
    ) -> Result<Bool, ParseError> {
        if self.is_bad_nat_sort(sort) {
            // `pushConstraint` writes `false` for an undeclared Nat instantiation before any
            // cast context applies (TypeInferencer.java:729-731).
            self.ill_sorted_ground = true;
            let constraint = Bool::from_bool(false);
            self.record_replay(
                &constraint,
                ReplaySubject::Term {
                    actual: None,
                    undeclared: Some(sort.clone()),
                    production: self.token_production_text(leaf, sort),
                },
                expected,
            );
            return Ok(constraint);
        }
        let actual = self.sort_value(sort, &BTreeMap::new())?;
        let constraint = match cast_context {
            CastContext::Strict => actual.eq(expected),
            CastContext::Parser => Bool::from_bool(true),
            CastContext::None | CastContext::Semantic => {
                self.less_than_eq(&actual, expected, false)?
            }
        };
        if !self.ground_token_fits(sort, expected, cast_context) {
            self.ill_sorted_ground = true;
        }
        if cast_context != CastContext::Parser {
            self.record_replay(
                &constraint,
                ReplaySubject::Term {
                    actual: Some(actual),
                    undeclared: None,
                    production: self.token_production_text(leaf, sort),
                },
                expected,
            );
        }
        Ok(constraint)
    }

    /// Whether a token of a ground sort satisfies a ground expected sort; a symbolic expected
    /// sort is left to the solver.
    fn ground_token_fits(&self, actual: &Sort, expected: &Datatype, context: CastContext) -> bool {
        let Ok(expected) = self.decode_sort(expected) else {
            return true;
        };
        match context {
            CastContext::Parser => true,
            CastContext::Strict => actual == &expected,
            CastContext::None | CastContext::Semantic => {
                actual == &expected || self.semantic.less_than_eq(actual, &expected)
            }
        }
    }

    fn record_replay(&mut self, constraint: &Bool, subject: ReplaySubject, expected: &Datatype) {
        if self.incremental {
            self.replay.push(ReplayConstraint {
                constraint: constraint.clone(),
                subject,
                expected: expected.clone(),
            });
        }
    }

    /// The production text the reference prints for a token leaf: the MINT.literal
    /// instantiation substituted with the leaf's width, otherwise the declaring production.
    fn token_production_text(&self, leaf: &Term, sort: &Sort) -> String {
        let production = leaf
            .metadata()
            .and_then(|metadata| metadata.production)
            .and_then(|id| {
                self.grammar.productions.iter().find(|production| {
                    production.token
                        && production
                            .source_production
                            .is_some_and(|source| source.0 == id.0)
                })
            });
        match production {
            Some(production) => match &production.parametric_origin {
                Some(origin) => {
                    super::render_production(&crate::definition::Sentence::Production {
                        label: origin.label.clone(),
                        parameters: Vec::new(),
                        sort: sort.clone(),
                        items: origin.items.clone(),
                        attributes: origin.attributes.clone(),
                    })
                    .unwrap_or_else(|| production_text(production))
                }
                None => production_text(production),
            },
            None => format!("syntax {sort} ::= <token>"),
        }
    }

    fn explain_unsat_packed(
        &mut self,
        term: &Rc<PackedTerm>,
        expected: &Datatype,
        root_context: CastContext,
    ) -> ParseError {
        self.incremental = true;
        self.replay.clear();
        let explained = self
            .constraint_packed(term, expected, root_context, &mut HashMap::new())
            .and_then(|_| self.replay_constraints());
        self.incremental = false;
        explained.unwrap_or_else(|_| z3_error(UNSAT_MESSAGE))
    }

    fn explain_unsat(
        &mut self,
        term: &ParsedTerm,
        expected: &Datatype,
        root_context: CastContext,
    ) -> ParseError {
        self.incremental = true;
        self.replay.clear();
        let explained = self
            .constraint(term, expected, root_context, "root")
            .and_then(|_| self.replay_constraints());
        self.incremental = false;
        explained.unwrap_or_else(|_| z3_error(UNSAT_MESSAGE))
    }

    /// `TypeInferencer.push`/`replayConstraints`: assert the recorded constraints one at a time,
    /// variable bounds first, and name the first one that is unsatisfiable together with the
    /// sorts of the last satisfiable model.
    fn replay_constraints(&self) -> Result<ParseError, ParseError> {
        let solver = Solver::new();
        self.exclude_klabel_parameters(&solver)?;
        self.restrict_to_real_sorts(&solver);
        let mut constraints = self.replay.iter().collect::<Vec<_>>();
        constraints.sort_by_key(|constraint| {
            !matches!(constraint.subject, ReplaySubject::Variable { .. })
        });
        for constraint in constraints {
            solver.push();
            solver.assert(&constraint.constraint);
            match solver.check() {
                SatResult::Sat => {
                    solver.pop(1);
                    solver.assert(&constraint.constraint);
                }
                SatResult::Unknown => {
                    return Err(z3_error("Could not solve sort constraints."));
                }
                SatResult::Unsat => {
                    solver.pop(1);
                    if !matches!(solver.check(), SatResult::Sat) {
                        return Err(z3_error("Unknown sort inference error."));
                    }
                    let model = solver
                        .get_model()
                        .ok_or_else(|| z3_error("Z3 produced no model for the replay"))?;
                    let expected = self.eval_sort(&model, &constraint.expected)?;
                    let message = match &constraint.subject {
                        ReplaySubject::Variable { name, variable } => format!(
                            "Unexpected sort {} for variable {name}. Expected: {expected}",
                            self.eval_sort(&model, variable)?
                        ),
                        ReplaySubject::Term {
                            actual,
                            undeclared,
                            production,
                        } => {
                            let actual = match (undeclared, actual) {
                                (Some(sort), _) => sort.clone(),
                                (None, Some(actual)) => self.eval_sort(&model, actual)?,
                                (None, None) => {
                                    return Err(z3_error("replay constraint without a sort"));
                                }
                            };
                            format!(
                                "Unexpected sort {actual} for term parsed as production {production}. Expected: {expected}"
                            )
                        }
                    };
                    return Ok(z3_error(message));
                }
            }
        }
        Err(z3_error("Unknown sort inference error."))
    }

    fn eval_sort(&self, model: &Model, value: &Datatype) -> Result<Sort, ParseError> {
        let value = model
            .eval(value, true)
            .ok_or_else(|| z3_error("Z3 omitted a sort value in the replay model"))?;
        self.decode_sort(&value)
    }

    fn sort_value(
        &self,
        sort: &Sort,
        parameters: &BTreeMap<Sort, Datatype>,
    ) -> Result<Datatype, ParseError> {
        if let Some(value) = parameters.get(sort) {
            return Ok(value.clone());
        }
        let cacheable = parameters.is_empty() && self.ground_sorts.contains(sort);
        if cacheable && let Some(value) = self.ground_values.borrow().get(sort) {
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
        let value = self.datatype.variants[index]
            .constructor
            .apply(&references)
            .as_datatype()
            .ok_or_else(|| z3_error(format!("failed to construct Z3 value for sort {sort}")))?;
        if cacheable {
            self.ground_values
                .borrow_mut()
                .insert(sort.clone(), value.clone());
        }
        Ok(value)
    }

    fn less_than_eq(
        &self,
        lesser: &Datatype,
        greater: &Datatype,
        syntactic: bool,
    ) -> Result<Bool, ParseError> {
        let relation = if syntactic {
            &self.syntactic_relation
        } else {
            &self.semantic_relation
        };
        let mut cases = relation
            .iter()
            .map(|(left, right)| Bool::and(&[lesser.eq(left), greater.eq(right)]))
            .collect::<Vec<_>>();
        cases.push(lesser.eq(greater));
        Ok(or_all(&cases))
    }

    fn order_relation(&self, syntactic: bool) -> Result<Vec<(Datatype, Datatype)>, ParseError> {
        let order = if syntactic {
            &self.syntactic
        } else {
            &self.semantic
        };
        let mut relation = Vec::new();
        for left in &self.ground_sorts {
            if !is_real_ground_sort(left) {
                continue;
            }
            let left_value = self.sort_value(left, &BTreeMap::new())?;
            for right in &self.ground_sorts {
                if !is_real_ground_sort(right) {
                    continue;
                }
                if left == right || order.less_than_eq(left, right) {
                    let right_value = self.sort_value(right, &BTreeMap::new())?;
                    relation.push((left_value.clone(), right_value));
                }
            }
        }
        Ok(relation)
    }

    /// `TypeInferencer` declares its Z3 `Sort` datatype from the module's sorts filtered by
    /// `isRealSort` (TypeInferencer.java:118-130: parametric heads, and no parser sort except
    /// `K`, `KItem`, `KLabel` and the Nat sorts), and every variable and sort parameter is a
    /// constant of that datatype, so a scaffolding sort such as `KList` is never their value.
    /// k-rust's datatype also carries the grammar's scaffolding sorts, which the production
    /// constraints need as ground values, so the variables and parameters are restricted here.
    fn restrict_to_real_sorts(&self, solver: &Solver) {
        let unreal = self
            .heads
            .iter()
            .enumerate()
            .filter(|(_, head)| {
                head.parameters() == 0 && !is_real_ground_sort(&Sort::new(head.as_str()))
            })
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        for value in self.variables.values() {
            for index in &unreal {
                let is_unreal = self.datatype.variants[*index]
                    .tester
                    .apply(&[value])
                    .as_bool()
                    .expect("a datatype tester returns a Bool");
                solver.assert(is_unreal.not());
            }
        }
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

    /// Seed maximal-model search with the reference's soft `K`/`KItem`/`Bag` preferences.
    ///
    /// The cardinality assertion is scoped to this first model. Maximal-model enumeration runs
    /// after the pop with only hard constraints, so an incomparable model with fewer preferred
    /// assignments cannot be pruned.
    /// The reference's soft `K`/`KItem`/`Bag` preferences (TypeInferencer.java:364-370) for the
    /// selected inference constants.
    fn top_preferences(&self, select: impl Fn(&str) -> bool) -> Result<Vec<Bool>, ParseError> {
        let mut constraints = Vec::new();
        for preferred in ["K", "KItem", "Bag"] {
            let sort = Sort::new(preferred);
            if !self.ground_sorts.contains(&sort) {
                continue;
            }
            let preferred = self.sort_value(&sort, &BTreeMap::new())?;
            for (name, variable) in &self.variables {
                if select(name) {
                    constraints.push(self.less_than_eq(&preferred, variable, false)?);
                }
            }
        }
        Ok(constraints)
    }

    fn seed_model(&self, solver: &Solver) -> Result<Option<BTreeMap<String, Sort>>, ParseError> {
        let constraints = self.top_preferences(|_| true)?;
        if constraints.is_empty() {
            return Ok(None);
        }

        solver.push();
        let seed = (|| {
            self.assert_preferred(solver, &constraints)?;
            match solver.check() {
                SatResult::Sat => self
                    .read_model(
                        &solver
                            .get_model()
                            .ok_or_else(|| z3_error("Z3 returned sat without a seed model"))?,
                    )
                    .map(Some),
                SatResult::Unsat => Ok(None),
                SatResult::Unknown => Err(z3_error(
                    "Z3 returned unknown while seeding sort-inference preferences",
                )),
            }
        })();
        solver.pop(1);
        seed
    }

    /// Assert that the largest satisfiable number of `preferences` holds and return that count.
    /// The caller scopes the assertion with `push`/`pop`.
    fn assert_preferred(&self, solver: &Solver, preferences: &[Bool]) -> Result<usize, ParseError> {
        if preferences.is_empty() {
            return Ok(0);
        }
        let weighted = preferences
            .iter()
            .map(|constraint| (constraint, 1))
            .collect::<Vec<_>>();
        let mut low = 0;
        let mut high = preferences.len();
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
        Ok(low)
    }

    /// Re-select the formal parameters of a maximal model: first so that as many
    /// overload-minimal function-LHS branches as possible stay well-sorted, then so that as many
    /// parameters as possible sit at the seed's `K`/`KItem`/`Bag` preferences.
    ///
    /// A packed ambiguity can share a formal parameter between overload branches that bind it to
    /// different sorts. Model application discards the branch the arbitrary Z3 value contradicts
    /// before the post-inference overload filter can select it. The maximality climb over the
    /// real variables likewise re-reads every parameter from an unconstrained model, so a
    /// parameter the seed placed at `K` (a top rewrite over a bare variable) can come back at any
    /// satisfying sort. The real variables are pinned to their maximal values, so only formal
    /// parameters move, and the assertions are popped before enumeration continues with hard
    /// constraints alone.
    fn prefer_parameters(
        &self,
        solver: &Solver,
        values: &mut BTreeMap<String, Sort>,
    ) -> Result<(), ParseError> {
        let top_preferences = self.top_preferences(|name| self.parameters.contains(name))?;
        if self.packed_overload_preferences.is_empty() && top_preferences.is_empty() {
            return Ok(());
        }
        solver.push();
        let preferred = (|| {
            for (name, variable) in &self.variables {
                if self.parameters.contains(name) {
                    continue;
                }
                let current = self.sort_value(
                    values
                        .get(name)
                        .expect("all inference variables have model values"),
                    &BTreeMap::new(),
                )?;
                solver.assert(variable.eq(&current));
            }
            let overloads = self.assert_preferred(solver, &self.packed_overload_preferences)?;
            let tops = self.assert_preferred(solver, &top_preferences)?;
            if overloads == 0 && tops == 0 {
                return Ok(None);
            }
            match solver.check() {
                SatResult::Sat => self
                    .read_model(&solver.get_model().ok_or_else(|| {
                        z3_error("Z3 returned sat without an overload branch model")
                    })?)
                    .map(Some),
                SatResult::Unsat => Ok(None),
                SatResult::Unknown => Err(z3_error(
                    "Z3 returned unknown while selecting overload branch parameters",
                )),
            }
        })();
        solver.pop(1);
        if let Some(preferred) = preferred? {
            *values = preferred;
        }
        Ok(())
    }

    fn maximal_models(
        &self,
        solver: &Solver,
        seed: Option<BTreeMap<String, Sort>>,
    ) -> Result<Vec<BTreeMap<String, Sort>>, ParseError> {
        let real_variables = self
            .variables
            .keys()
            .filter(|name| !self.parameters.contains(*name))
            .cloned()
            .collect::<Vec<_>>();
        let mut models = Vec::new();
        let mut first = seed;
        loop {
            let mut values = if let Some(seed) = first.take() {
                seed
            } else {
                match solver.check() {
                    SatResult::Unsat => break,
                    SatResult::Unknown => {
                        return Err(z3_error(
                            "Z3 returned unknown while enumerating sort models",
                        ));
                    }
                    SatResult::Sat => {}
                }
                self.read_model(
                    &solver
                        .get_model()
                        .ok_or_else(|| z3_error("Z3 returned sat without a model"))?,
                )?
            };
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
            self.prefer_parameters(solver, &mut values)?;
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
            PackedNode::Term(leaf) if inferred_variable_name(leaf).is_some() => {
                let Some(name) = inferred_variable_name(leaf) else {
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
                    && self.top_rewrite_ids.contains(&identity)
                    && descriptor
                        .label
                        .as_ref()
                        .is_some_and(|label| label.name == "#KRewrite")
                    && children.len() == 2)
                    .then(|| self.declared_packed_model_sort(&children[0], model));
                let function_body_sort = is_top_sort_production(descriptor)
                    .then(|| {
                        children.first().and_then(|child| {
                            self.grammar
                                .packed_body_function_lhs(child)
                                .map(|lhs| self.declared_packed_model_sort(lhs, model))
                        })
                    })
                    .flatten();
                let transformed_children = children
                    .iter()
                    .zip(expected_children)
                    .enumerate()
                    .map(|(index, (child, child_sort))| {
                        let child_expected = if index == 0
                            && let Some(function_sort) = &function_body_sort
                        {
                            function_sort.clone()
                        } else if index == 1
                            && let Some(lhs_sort) = &anywhere_lhs_sort
                        {
                            lhs_sort.clone()
                        } else if is_cast(descriptor) {
                            actual.clone()
                        } else {
                            substitute_sort(child_sort, &parameter_values)
                        };
                        let formal_child = descriptor
                            .parametric_origin
                            .as_ref()
                            .is_some_and(|origin| origin.parameters.contains(child_sort));
                        let child_context = match cast_context_for(descriptor) {
                            CastContext::None if index == 0 && function_body_sort.is_some() => {
                                CastContext::None
                            }
                            CastContext::None
                                if !formal_child && !is_real_ground_sort(child_sort) =>
                            {
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
            PackedNode::Term(leaf) => match (inferred_variable_name(leaf), leaf.unannotated()) {
                (None, Term::Token { sort, .. }) => sort.clone(),
                (Some(name), _) => model
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
            ParsedTerm::Term(ref leaf) if inferred_variable_name(leaf).is_some() => {
                let Some(name) = inferred_variable_name(leaf) else {
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
                    && self.top_rewrite_paths.contains(path)
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
                let function_body_sort = is_top_sort_production(descriptor)
                    .then(|| {
                        children.first().and_then(|child| {
                            self.grammar
                                .body_function_lhs(child, &format!("{path}_c0"))
                                .map(|(lhs, lhs_path)| {
                                    declared_model_sort(self.grammar, lhs, model, &lhs_path)
                                })
                        })
                    })
                    .flatten();
                let children = children
                    .into_iter()
                    .zip(expected_children)
                    .enumerate()
                    .map(|(index, (child, child_sort))| {
                        let child_expected = if index == 0
                            && let Some(function_sort) = &function_body_sort
                        {
                            function_sort.clone()
                        } else if index == 1
                            && let Some(lhs_sort) = &anywhere_lhs_sort
                        {
                            lhs_sort.clone()
                        } else if is_cast(descriptor) {
                            actual.clone()
                        } else {
                            substitute_sort(child_sort, &parameter_values)
                        };
                        let formal_child = descriptor
                            .parametric_origin
                            .as_ref()
                            .is_some_and(|origin| origin.parameters.contains(child_sort));
                        let child_context = match cast_context_for(descriptor) {
                            CastContext::None if index == 0 && function_body_sort.is_some() => {
                                CastContext::None
                            }
                            CastContext::None
                                if !formal_child && !is_real_ground_sort(child_sort) =>
                            {
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
        if self.is_bad_nat_sort(actual) {
            return Err(z3_error(format!(
                "Unexpected sort {actual}: its numeric sort parameter is not declared by the module"
            )));
        }
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
        ParsedTerm::Term(term) => match (inferred_variable_name(term), term.unannotated()) {
            (None, Term::Token { sort, .. }) => sort.clone(),
            (Some(name), _) => {
                let key = inference_variable_key(term, name, path);
                model.get(&key).cloned().unwrap_or_else(|| Sort::new("K"))
            }
            (None, _) => Sort::new("K"),
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

/// Numeric sort names used as parameters of a declared instantiation such as `MInt{6}`; sort
/// variables of a parametric origin are skipped.
fn collect_declared_nats(sort: &Sort, formals: &[Sort], declared: &mut BTreeSet<String>) {
    if formals.contains(sort) {
        return;
    }
    if sort.name.parse::<u64>().is_ok() {
        declared.insert(sort.name.clone());
    }
    for parameter in &sort.parameters {
        collect_declared_nats(parameter, formals, declared);
    }
}

fn production_text(production: &Production) -> String {
    production
        .source_production_text
        .clone()
        .unwrap_or_else(|| {
            super::render_added_production(
                &production.result,
                &production.declared_items,
                production.token,
                None,
            )
        })
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

/// Locate each rewrite at a rule body's top level. An ambiguous root can contain several such
/// nodes, so identities are collected per branch while nested rewrites remain excluded.
fn top_rewrite_paths(grammar: &Grammar, root: &ParsedTerm) -> HashSet<String> {
    fn visit(grammar: &Grammar, term: &ParsedTerm, path: String, targets: &mut HashSet<String>) {
        match term {
            ParsedTerm::Ambiguity(alternatives) => {
                for (index, alternative) in alternatives.iter().enumerate() {
                    visit(grammar, alternative, format!("{path}_a{index}"), targets);
                }
            }
            ParsedTerm::Production {
                production,
                children,
                ..
            } => {
                let descriptor = &grammar.productions[*production];
                if (descriptor.bracket && children.len() == 1)
                    || descriptor.result.name == "#RuleContent"
                    || (descriptor.result.name == "#RuleBody"
                        && descriptor
                            .label
                            .as_ref()
                            .is_some_and(|label| label.name == "#withConfig"))
                {
                    if let Some(child) = children.first() {
                        visit(grammar, child, format!("{path}_c0"), targets);
                    }
                } else if descriptor
                    .label
                    .as_ref()
                    .is_some_and(|label| label.name == "#KRewrite")
                    && children.len() == 2
                {
                    targets.insert(path);
                }
            }
            ParsedTerm::Term(_) | ParsedTerm::InstantiatedProduction { .. } => {}
        }
    }
    let mut targets = HashSet::new();
    visit(grammar, root, "root".to_owned(), &mut targets);
    targets
}

fn packed_top_rewrites(grammar: &Grammar, root: &Rc<PackedTerm>) -> HashSet<*const PackedTerm> {
    fn visit(grammar: &Grammar, term: &Rc<PackedTerm>, targets: &mut HashSet<*const PackedTerm>) {
        match &term.node {
            PackedNode::Ambiguity(alternatives) => {
                for alternative in alternatives {
                    visit(grammar, alternative, targets);
                }
            }
            PackedNode::Production {
                production,
                children,
                ..
            } => {
                let descriptor = &grammar.productions[*production];
                if (descriptor.bracket && children.len() == 1)
                    || descriptor.result.name == "#RuleContent"
                    || (descriptor.result.name == "#RuleBody"
                        && descriptor
                            .label
                            .as_ref()
                            .is_some_and(|label| label.name == "#withConfig"))
                {
                    if let Some(child) = children.first() {
                        visit(grammar, child, targets);
                    }
                } else if descriptor
                    .label
                    .as_ref()
                    .is_some_and(|label| label.name == "#KRewrite")
                    && children.len() == 2
                {
                    targets.insert(Rc::as_ptr(term));
                }
            }
            PackedNode::Term(_) | PackedNode::InstantiatedProduction { .. } => {}
        }
    }
    let mut targets = HashSet::new();
    visit(grammar, root, &mut targets);
    targets
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

/// Whether a production's first child is bounded by a function left-hand side: the reference
/// treats a node expected at `#RuleContent` or `#RuleBody` as a top-sort node
/// (TypeInferencer.java:592-593, :640). k-rust's forest collapses `#RuleBody ::= K`, so the
/// `#RuleBody`-sorted node that survives is `#withConfig`.
fn is_top_sort_production(production: &Production) -> bool {
    matches!(
        production.result.name.as_str(),
        "#RuleContent" | "#RuleBody"
    )
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::definition::ProductionItem;
    use crate::kast::Label;

    fn nonterminal(name: &str) -> ProductionItem {
        ProductionItem::NonTerminal {
            sort: Sort::new(name),
            name: None,
        }
    }

    #[test]
    fn semantic_cast_directly_on_variable_is_strict() {
        let mut grammar = Grammar::default();
        grammar
            .add(
                Sort::new("Big"),
                vec![nonterminal("KItem")],
                Some(Label::new("#SemanticCastToBig")),
                false,
                false,
            )
            .unwrap();
        grammar
            .add(
                Sort::new("Small"),
                vec![nonterminal("KItem")],
                Some(Label::new("#SemanticCastToSmall")),
                false,
                false,
            )
            .unwrap();
        let foo = grammar.productions.len();
        grammar
            .add(
                Sort::new("Foo"),
                vec![nonterminal("Small")],
                Some(Label::new("foo")),
                false,
                false,
            )
            .unwrap();
        let pair = grammar.productions.len();
        grammar
            .add(
                Sort::new("K"),
                vec![nonterminal("Big"), nonterminal("Foo")],
                Some(Label::new("pair")),
                false,
                false,
            )
            .unwrap();
        grammar
            .subsort_relations
            .insert((Sort::new("Small"), Sort::new("Big")));

        let variable = || ParsedTerm::Term(Term::variable("X"));
        let term = ParsedTerm::Production {
            production: pair,
            children: vec![
                ParsedTerm::Production {
                    production: 0,
                    children: vec![variable()],
                    metadata: Default::default(),
                },
                ParsedTerm::Production {
                    production: foo,
                    children: vec![variable()],
                    metadata: Default::default(),
                },
            ],
            metadata: Default::default(),
        };
        let error = grammar
            .infer_sorts_z3(term, &Sort::new("K"), false)
            .expect_err("Big cast and Small use of X must conflict");
        assert!(
            error.to_string().contains("Unexpected sort")
                || error.to_string().contains("no well-sorted parse")
                || error.to_string().contains("unexpected sort"),
            "unexpected inference error: {error}"
        );
    }

    #[test]
    fn undeclared_mint_width_is_ill_sorted() {
        // TypeInferencer.isBadNatSort: a numeric parameter sort whose head the module does not
        // define is written to Z3 as `false`, so `foo(0p32)` over `foo(MInt{6})` is unsat even
        // though no variable takes part (checks/checkMIntLiteral.k).
        fn mint(width: &str) -> Sort {
            Sort::with_parameters("MInt", vec![Sort::new(width)])
        }
        let mut grammar = Grammar::default();
        let foo = grammar.productions.len();
        grammar
            .add(
                Sort::new("KItem"),
                vec![ProductionItem::NonTerminal {
                    sort: mint("6"),
                    name: None,
                }],
                Some(Label::new("foo")),
                false,
                false,
            )
            .unwrap();
        let application = |width: &str| ParsedTerm::Production {
            production: foo,
            children: vec![ParsedTerm::Term(Term::Token {
                token: format!("0p{width}"),
                sort: mint(width),
            })],
            metadata: Default::default(),
        };

        grammar
            .infer_sorts_z3(application("6"), &Sort::new("KItem"), false)
            .expect("the declared width MInt{6} is well-sorted");
        let error = grammar
            .infer_sorts_z3(application("32"), &Sort::new("KItem"), false)
            .expect_err("MInt{32} is not declared by the grammar");
        assert!(
            error.to_string().contains("Unexpected sort MInt{32}"),
            "unexpected inference error: {error}"
        );
    }

    #[test]
    fn top_rewrite_path_tracks_transparent_brackets() {
        let mut grammar = Grammar::default();
        let rewrite = grammar.productions.len();
        grammar
            .add(
                Sort::new("#RuleBody"),
                vec![nonterminal("K"), nonterminal("K")],
                Some(Label::new("#KRewrite")),
                false,
                false,
            )
            .unwrap();
        let bracket = grammar.productions.len();
        grammar
            .add(
                Sort::new("#RuleBody"),
                vec![nonterminal("#RuleBody")],
                None,
                false,
                false,
            )
            .unwrap();
        grammar.productions[bracket].bracket = true;

        let term = ParsedTerm::Production {
            production: bracket,
            children: vec![ParsedTerm::Production {
                production: rewrite,
                children: vec![
                    ParsedTerm::Term(Term::variable("L")),
                    ParsedTerm::Term(Term::variable("R")),
                ],
                metadata: Default::default(),
            }],
            metadata: Default::default(),
        };

        assert_eq!(
            top_rewrite_paths(&grammar, &term),
            HashSet::from(["root_c0".to_owned()])
        );
    }

    #[test]
    fn packed_ambiguous_top_rewrites_all_keep_anywhere_bounds() {
        let mut grammar = Grammar::default();
        let small_a = grammar.productions.len();
        grammar
            .add(
                Sort::new("Small"),
                vec![ProductionItem::Terminal("a".into())],
                Some(Label::new("smallA")),
                false,
                false,
            )
            .unwrap();
        let small_b = grammar.productions.len();
        grammar
            .add(
                Sort::new("Small"),
                vec![ProductionItem::Terminal("b".into())],
                Some(Label::new("smallB")),
                false,
                false,
            )
            .unwrap();
        let big = grammar.productions.len();
        grammar
            .add(
                Sort::new("Big"),
                vec![ProductionItem::Terminal("big".into())],
                Some(Label::new("big")),
                false,
                false,
            )
            .unwrap();
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
        grammar.subsort_relations.extend([
            (Sort::new("Small"), Sort::new("K")),
            (Sort::new("Big"), Sort::new("K")),
        ]);

        let leaf = |production| PackedTerm::production(production, vec![], Default::default());
        let rhs = leaf(big);
        let alternative = |lhs| {
            PackedTerm::production(
                rewrite,
                vec![leaf(lhs), Rc::clone(&rhs)],
                Default::default(),
            )
        };
        let term =
            PackedTerm::ambiguity(BTreeSet::from([alternative(small_a), alternative(small_b)]));

        grammar
            .infer_packed_sorts_z3(term, &Sort::new("K"), true)
            .expect_err("each ambiguous top rewrite must reject Big as an anywhere RHS for Small");
    }

    #[test]
    fn unpacked_ambiguous_rewrite_paths_include_branch_indexes() {
        let mut grammar = Grammar::default();
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
        let alternative = |name| ParsedTerm::Production {
            production: rewrite,
            children: vec![
                ParsedTerm::Term(Term::variable(name)),
                ParsedTerm::Term(Term::variable("R")),
            ],
            metadata: Default::default(),
        };
        let term = ParsedTerm::Ambiguity(BTreeSet::from([alternative("L1"), alternative("L2")]));

        assert_eq!(
            top_rewrite_paths(&grammar, &term),
            HashSet::from(["root_a0".to_owned(), "root_a1".to_owned()])
        );
    }
}
