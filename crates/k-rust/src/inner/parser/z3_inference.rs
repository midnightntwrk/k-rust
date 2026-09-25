//! ```toml algorithm
//! id = "parser.inference.z3"
//! name = "Z3-backed maximal-model sort inference"
//! sites = ["Grammar::infer_packed_sorts_z3", "Grammar::infer_sorts_z3", "encoding_base", "EncodingBase::sort_value", "EncodingBase::order_relation", "EncodingBase::decode_sort", "OrderRelation::new", "OrderRelation::full_disjunction", "Encoding::assert_packed_hard_constraints", "Encoding::less_than_eq", "Encoding::restrict_to_real_sorts", "Encoding::exclude_klabel_parameters", "Encoding::seed_model", "Encoding::prefer_parameters", "Encoding::maximal_models", "Encoding::admissible_parameters", "Encoding::read_model", "or_all"]
//! variable = "H = sort heads; G = ground sorts; N = term nodes; M = maximal typings; R = grammar productions; c = solver checks; P = pairs of a subsort relation, at most G^2; U = largest up- or down-set of a ground sort value, at most G; A = admissible parameter vectors of one maximal typing, at most 256"
//! counters = ["ParserZ3Checks", "ParserZ3EncodingBuilds"]
//! consumes = [{ type = "k_rust::inner::parser::forest::PackedTerm", role = "packed forest" }]
//! produces = [{ type = "k_rust::inner::parser::forest::ParsedTerm", role = "sorted tree" }]
//! span = "per problem"
//! lean = ["KRust.SubsortEncoding.new_equiv", "KRust.MaximalModels.maximal_models_spec", "KRust.MaximalModels.runs_agree_up_to_pref", "KRust.MaximalModels.runs_agree_candidates"]
//!
//! [[cost]]
//! mode = "encoding construction"
//! bound = "O(H + G^2 + R) plus one PartialOrder::new construction"
//!
//! [[cost]]
//! mode = "one inference"
//! bound = "O(N x M + c)"
//!
//! [[cost]]
//! mode = "one order constraint (less_than_eq)"
//! bound = "O(U) when a side is closed, O(P) otherwise"
//!
//! [[cost]]
//! mode = "admissible parameter enumeration of one recorded model with formal parameters"
//! bound = "A solver checks, and A model applications of O(N) nodes each, whose candidates join the one ambiguity the post-inference passes resolve; the inference fails when A exceeds 256"
//!
//! [[cost]]
//! mode = "cached encoding base that does not cover the term sorts"
//! bound = "one uncached encoding construction per inference"
//! ```
//!
//! Z3-backed maximal-model sort inference for ambiguous and parametric parse forests.
//!
//! Each check is counted by `Counter::ParserZ3Checks`; model enumeration is proportional to
//! the number of maximal typings times solver checks. Grammar-determined encoding construction is
//! O(heads + ground sorts squared) once per grammar generation and top sort on each thread,
//! including the up- and down-set of every ground sort value in the subsort relation; each
//! attempt then constructs O(term nodes) constraints. An order constraint with a closed side is
//! built from that side's up- or down-set rather than from the whole relation
//! (`Encoding::less_than_eq`). `ParserZ3EncodingBuilds` counts base builds.
//! The unpacked path remains a checked oracle.
//!
//! One order on sorts is encoded: the grammar's subsort relation (`Grammar::subsort_relations`,
//! the unlabelled single-nonterminal productions). Well-sortedness and maximality both read it.
//! A labelled single-nonterminal production such as `A ::= B [symbol(f)]` is a constructor
//! `f : B -> A`, not a subsort: no `B` value is an `A` value, so it neither makes a `B` typing
//! of a variable ill-sorted where an `A` is expected nor makes that typing dominated by an `A`
//! typing. The grammar's syntactic relation, which also holds such productions, belongs to
//! bracket and priority filtering and is not encoded.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::ops::Deref;
use std::rc::Rc;

use k_rust_kore::measure::{self, Algorithm, Counter};
use z3::ast::{Ast, Bool, Datatype};
use z3::{DatatypeAccessor, DatatypeBuilder, DatatypeSort, Model, SatResult, Solver};

use crate::definition::{PartialOrder, SortHead};
use crate::kast::{FrontendSort, GeneratedLabel, InternalLabel, Label, Sort, Term};
use crate::names::BuiltinSort;

use super::{
    Grammar, Item, PackedNode, PackedTerm, ParseError, ParsedTerm, Production,
    cmp_packed_structurally, inferred_variable_name, packed_terms_in_structural_order,
};

/// Every check-sat call of sort inference goes through here so `parser.z3_checks` counts them.
fn check(solver: &Solver) -> SatResult {
    measure::bump(Counter::ParserZ3Checks);
    solver.check()
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum CastContext {
    None,
    Semantic,
    Strict,
    Parser,
}

struct EncodingBase {
    datatype: DatatypeSort,
    heads: Vec<SortHead>,
    head_indexes: BTreeMap<SortHead, usize>,
    ground_sorts: BTreeSet<Sort>,
    semantic: PartialOrder<Sort>,
    ground_values: RefCell<BTreeMap<Sort, Datatype>>,
    /// The values of `ground_values`, filled once `build` has cached every ground sort: the
    /// closed constructor terms that `less_than_eq` treats as a closed side.
    closed_values: HashSet<Datatype>,
    semantic_relation: OrderRelation,
    /// Numeric sort names declared by the grammar as parameters of an instantiated parametric
    /// sort (`Module.definedSorts` keeps the Nat heads of `definedInstantiations`).
    declared_nat_sorts: BTreeSet<String>,
}

/// One subsort order over the real ground sort values (`EncodingBase::order_relation`), with the
/// up-set and the down-set of each value, built once with the encoding base.
/// `up[l]` lists the `r` of the pairs `(l, r)` and `down[r]` the `l` of the pairs `(l, r)`, both in
/// the order of `pairs`; a value in no pair has no entry.
struct OrderRelation {
    pairs: Vec<(Datatype, Datatype)>,
    up: HashMap<Datatype, Vec<Datatype>>,
    down: HashMap<Datatype, Vec<Datatype>>,
}

impl OrderRelation {
    fn new(pairs: Vec<(Datatype, Datatype)>) -> Self {
        let mut up = HashMap::<Datatype, Vec<Datatype>>::new();
        let mut down = HashMap::<Datatype, Vec<Datatype>>::new();
        for (lesser, greater) in &pairs {
            up.entry(lesser.clone()).or_default().push(greater.clone());
            down.entry(greater.clone())
                .or_default()
                .push(lesser.clone());
        }
        Self { pairs, up, down }
    }

    fn up(&self, lesser: &Datatype) -> &[Datatype] {
        self.up.get(lesser).map_or(&[], Vec::as_slice)
    }

    fn down(&self, greater: &Datatype) -> &[Datatype] {
        self.down.get(greater).map_or(&[], Vec::as_slice)
    }

    /// `OR over (l, r) in pairs of (lesser = l and greater = r)`, then `or lesser = greater`: the
    /// order constraint written over the whole relation, which `Encoding::less_than_eq` keeps
    /// when neither side is a closed value.
    fn full_disjunction(&self, lesser: &Datatype, greater: &Datatype) -> Bool {
        let mut cases = self
            .pairs
            .iter()
            .map(|(left, right)| Bool::and(&[lesser.eq(left), greater.eq(right)]))
            .collect::<Vec<_>>();
        cases.push(lesser.eq(greater));
        or_all(&cases)
    }
}

#[derive(Default)]
struct TermSorts {
    heads: BTreeSet<SortHead>,
    ground: BTreeSet<Sort>,
}

struct Encoding<'a> {
    grammar: &'a Grammar,
    base: Rc<EncodingBase>,
    variables: BTreeMap<String, Datatype>,
    parameters: BTreeSet<String>,
    /// Soft per-ambiguity preferences for the overload-minimal function-LHS branches.
    packed_overload_preferences: Vec<Bool>,
    packed_ids: HashMap<*const PackedTerm, usize>,
    anywhere: bool,
    top_rewrite_paths: HashSet<String>,
    top_rewrite_ids: HashSet<*const PackedTerm>,
    /// Whether a token leaf was constrained against a ground sort it cannot satisfy, so a term
    /// without variables must still be solved and rejected.
    ill_sorted_ground: bool,
    /// `ExpectedSortsVisitor.isIncremental`: after an unsat check the constraints are rebuilt
    /// one alternative per ambiguity and replayed singly to name the offending term.
    incremental: bool,
    replay: Vec<ReplayConstraint>,
}

impl Deref for Encoding<'_> {
    type Target = EncodingBase;

    fn deref(&self) -> &Self::Target {
        &self.base
    }
}

type EncodingBaseKey = (u64, Sort);
type EncodingBaseCache = Vec<(EncodingBaseKey, Rc<EncodingBase>)>;

thread_local! {
    static ENCODING_BASES: RefCell<EncodingBaseCache> = const {
        RefCell::new(Vec::new())
    };
    #[cfg(test)]
    static FORCE_UNCACHED_BASE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// Test switch: `less_than_eq` writes every order constraint over the whole relation.
    #[cfg(test)]
    static FORCE_FULL_DISJUNCTION: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// Test recorder: when `Some`, `less_than_eq` appends each call and the formula it built.
    #[cfg(test)]
    static ORDER_CONSTRAINTS: RefCell<Option<Vec<OrderConstraintCall>>> = const {
        RefCell::new(None)
    };
}

/// One `less_than_eq` call, as `ORDER_CONSTRAINTS` records it.
#[cfg(test)]
struct OrderConstraintCall {
    lesser: Datatype,
    greater: Datatype,
    formula: Bool,
}

const ENCODING_BASE_CACHE_CAPACITY: usize = 8;

const UNSAT_MESSAGE: &str = "no well-sorted parse or variable assignment exists";

/// The most admissible parameter vectors `Encoding::admissible_parameters` returns for one
/// recorded variable typing; it fails instead of keeping a subset when there are more.
const PARAMETER_CHOICE_LIMIT: usize = 256;

/// The maximal preference counts `Encoding::prefer_parameters` asserts.
#[derive(Clone, Copy, Default)]
struct PreferenceCounts {
    overloads: usize,
    tops: usize,
}

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
        let _span = measure::algorithm_span(Algorithm::ParserInferenceZ3);
        let mut encoding =
            Encoding::for_packed_inference(self, &term, top_sort, explicitly_anywhere)?;
        let solver = Solver::new();
        let (expected, root_context) =
            encoding.assert_packed_hard_constraints(&term, top_sort, &solver)?;
        let seed = encoding.seed_model(&solver)?;
        match check(&solver) {
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

        // Every admissible parameter vector of every maximal typing is a candidate; the
        // post-inference passes then treat them as the alternatives of one ambiguity
        // (`Encoding::admissible_parameters`).
        let models = encoding.maximal_models(&solver, seed)?;
        let mut candidates = BTreeSet::new();
        let mut first_error = None;
        for model in models.into_iter().flatten() {
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
            if descriptor.result.is_frontend(FrontendSort::RuleContent) {
                term = strip_packed_brackets(self, children.first()?);
                continue;
            }
            if descriptor.result.is_frontend(FrontendSort::RuleBody)
                && descriptor
                    .label
                    .as_ref()
                    .is_some_and(|label| label.is(InternalLabel::WithConfig))
            {
                term = strip_packed_brackets(self, children.first()?);
                continue;
            }
            if !descriptor
                .label
                .as_ref()
                .is_some_and(|label| label.is(InternalLabel::KRewrite))
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
    /// so `#withConfig` bounds its rewrite exactly as `#RuleContent` bounds a bare rewrite. For an
    /// anywhere rule `isFunction(t, isAnywhere)` (TypeInferencer.java:413-421) holds for every
    /// left-hand side `getFunction` returns, so a constructor such as `foo()` or a token such as
    /// `1` (a `Constant` is a `ProductionReference`) bounds the rewrite by its own sort
    /// (`getFunctionSort`, :429); a variable left-hand side keeps the ordinary bound. The returned
    /// path locates the left-hand side relative to `child_path`.
    fn body_function_lhs<'t>(
        &self,
        child: &'t ParsedTerm,
        child_path: &str,
        anywhere: bool,
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
                .is_some_and(|label| label.is(InternalLabel::KRewrite))
            && children.len() == 2
        {
            path.push_str("_c0");
            term = self.strip_brackets_with_path(&children[0], &mut path);
        }
        match term {
            ParsedTerm::Production { production, .. } => {
                let production = &self.productions[*production];
                (anywhere || production.function || production.macro_like).then_some((term, path))
            }
            ParsedTerm::Term(leaf) => (anywhere && is_token_leaf(leaf)).then_some((term, path)),
            ParsedTerm::Ambiguity(_) | ParsedTerm::InstantiatedProduction { .. } => None,
        }
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
        anywhere: bool,
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
                .is_some_and(|label| label.is(InternalLabel::KRewrite))
            && children.len() == 2
        {
            term = strip_packed_brackets(self, &children[0]);
        }
        match &term.node {
            PackedNode::Production { production, .. } => {
                let production = &self.productions[*production];
                (anywhere || production.function || production.macro_like).then_some(term)
            }
            PackedNode::Term(leaf) => (anywhere && is_token_leaf(leaf)).then_some(term),
            PackedNode::Ambiguity(_) | PackedNode::InstantiatedProduction { .. } => None,
        }
    }

    pub(super) fn infer_sorts_z3(
        &self,
        term: ParsedTerm,
        top_sort: &Sort,
        explicitly_anywhere: bool,
    ) -> Result<ParsedTerm, ParseError> {
        let _span = measure::algorithm_span(Algorithm::ParserInferenceZ3);
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
        match check(&solver) {
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

        // Every admissible parameter vector is a candidate, as in `infer_packed_sorts_z3`.
        let models = encoding.maximal_models(&solver, seed)?;
        let mut candidates = BTreeSet::new();
        let mut first_error = None;
        for model in models.into_iter().flatten() {
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

impl EncodingBase {
    fn build(
        grammar: &Grammar,
        top_sort: &Sort,
        term_sorts: &TermSorts,
    ) -> Result<Self, ParseError> {
        measure::bump(Counter::ParserZ3EncodingBuilds);
        let semantic = PartialOrder::new(grammar.subsort_relations.iter().cloned())
            .map_err(|cycle| ParseError::CircularSubsorts { path: cycle.path })?;
        let mut heads = BTreeSet::new();
        let mut ground_sorts = BTreeSet::new();
        collect_sort(top_sort, &mut heads, &mut ground_sorts);
        for (lesser, greater) in &grammar.subsort_relations {
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
        heads.extend(term_sorts.heads.iter().cloned());
        ground_sorts.extend(term_sorts.ground.iter().cloned());
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
        let mut base = Self {
            datatype: builder.finish(),
            heads,
            head_indexes,
            ground_sorts,
            semantic,
            ground_values: RefCell::new(BTreeMap::new()),
            closed_values: HashSet::new(),
            semantic_relation: OrderRelation::new(Vec::new()),
            declared_nat_sorts,
        };
        for sort in &base.ground_sorts {
            base.sort_value(sort, &BTreeMap::new())?;
        }
        // `sort_value` caches exactly the sorts of `ground_sorts`, all cached above, so
        // `ground_values` does not grow after this point.
        base.closed_values = base.ground_values.borrow().values().cloned().collect();
        base.semantic_relation = OrderRelation::new(base.order_relation()?);
        Ok(base)
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

    fn order_relation(&self) -> Result<Vec<(Datatype, Datatype)>, ParseError> {
        let order = &self.semantic;
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

    fn covers(&self, term_sorts: &TermSorts) -> bool {
        term_sorts
            .heads
            .iter()
            .all(|head| self.head_indexes.contains_key(head))
            && term_sorts.ground.is_subset(&self.ground_sorts)
    }
}

fn encoding_base(
    grammar: &Grammar,
    top_sort: &Sort,
    term_sorts: &TermSorts,
) -> Result<Rc<EncodingBase>, ParseError> {
    #[cfg(test)]
    if FORCE_UNCACHED_BASE.with(std::cell::Cell::get) {
        return encoding_base_uncached(grammar, top_sort, term_sorts);
    }

    let key = (grammar.generation, top_sort.clone());
    let cached = ENCODING_BASES.with(|bases| {
        let mut bases = bases.borrow_mut();
        let position = bases.iter().position(|(candidate, _)| candidate == &key)?;
        let entry = bases.remove(position);
        let base = Rc::clone(&entry.1);
        bases.push(entry);
        Some(base)
    });
    if let Some(base) = cached {
        return if base.covers(term_sorts) {
            Ok(base)
        } else {
            encoding_base_uncached_impl(grammar, top_sort, term_sorts)
        };
    }

    let base = encoding_base_uncached_impl(grammar, top_sort, &TermSorts::default())?;
    ENCODING_BASES.with(|bases| {
        let mut bases = bases.borrow_mut();
        bases.retain(|(candidate, _)| candidate != &key);
        bases.push((key, Rc::clone(&base)));
        if bases.len() > ENCODING_BASE_CACHE_CAPACITY {
            bases.remove(0);
        }
    });
    if base.covers(term_sorts) {
        Ok(base)
    } else {
        encoding_base_uncached_impl(grammar, top_sort, term_sorts)
    }
}

fn encoding_base_uncached_impl(
    grammar: &Grammar,
    top_sort: &Sort,
    term_sorts: &TermSorts,
) -> Result<Rc<EncodingBase>, ParseError> {
    EncodingBase::build(grammar, top_sort, term_sorts).map(Rc::new)
}

#[cfg(test)]
fn encoding_base_uncached(
    grammar: &Grammar,
    top_sort: &Sort,
    term_sorts: &TermSorts,
) -> Result<Rc<EncodingBase>, ParseError> {
    encoding_base_uncached_impl(grammar, top_sort, term_sorts)
}

#[cfg(test)]
fn with_uncached_encoding_base<T>(f: impl FnOnce() -> T) -> T {
    FORCE_UNCACHED_BASE.with(|force| {
        let previous = force.replace(true);
        let result = f();
        force.set(previous);
        result
    })
}

impl<'a> Encoding<'a> {
    fn new(
        grammar: &'a Grammar,
        term: &ParsedTerm,
        top_sort: &Sort,
        anywhere: bool,
    ) -> Result<Self, ParseError> {
        let mut term_sorts = TermSorts::default();
        collect_term_sorts(term, &mut term_sorts.heads, &mut term_sorts.ground);
        Self::new_with_term_sorts(grammar, top_sort, anywhere, &term_sorts)
    }

    fn new_packed(
        grammar: &'a Grammar,
        term: &Rc<PackedTerm>,
        top_sort: &Sort,
        anywhere: bool,
    ) -> Result<Self, ParseError> {
        let mut term_sorts = TermSorts::default();
        collect_packed_term_sorts(term, &mut term_sorts.heads, &mut term_sorts.ground);
        let mut encoding = Self::new_with_term_sorts(grammar, top_sort, anywhere, &term_sorts)?;
        encoding.packed_ids = packed_term_ids(term);
        Ok(encoding)
    }

    /// The encoding of one `Grammar::infer_packed_sorts_z3` problem, before any constraint.
    fn for_packed_inference(
        grammar: &'a Grammar,
        term: &Rc<PackedTerm>,
        top_sort: &Sort,
        explicitly_anywhere: bool,
    ) -> Result<Self, ParseError> {
        let anywhere = explicitly_anywhere || grammar.packed_lhs_is_function_or_macro(term);
        let mut encoding = Self::new_packed(grammar, term, top_sort, anywhere)?;
        encoding.top_rewrite_ids = packed_top_rewrites(grammar, term);
        Ok(encoding)
    }

    /// Assert the hard constraints of a packed inference on `solver`: the term constraint at
    /// `top_sort`, the `KLabel` exclusion and the real-sort restriction. Returns the top sort's
    /// value and the root cast context, which model application and the unsat explanation
    /// reuse.
    fn assert_packed_hard_constraints(
        &mut self,
        term: &Rc<PackedTerm>,
        top_sort: &Sort,
        solver: &Solver,
    ) -> Result<(Datatype, CastContext), ParseError> {
        let expected = self.sort_value(top_sort, &BTreeMap::new())?;
        let root_context = if !is_real_ground_sort(top_sort) {
            CastContext::Parser
        } else {
            CastContext::None
        };
        let constraint =
            self.constraint_packed(term, &expected, root_context, &mut HashMap::new())?;
        solver.assert(&constraint);
        self.exclude_klabel_parameters(solver)?;
        self.restrict_to_real_sorts(solver);
        Ok((expected, root_context))
    }

    fn new_with_term_sorts(
        grammar: &'a Grammar,
        top_sort: &Sort,
        anywhere: bool,
        term_sorts: &TermSorts,
    ) -> Result<Self, ParseError> {
        Ok(Self {
            grammar,
            base: encoding_base(grammar, top_sort, term_sorts)?,
            variables: BTreeMap::new(),
            parameters: BTreeSet::new(),
            packed_overload_preferences: Vec::new(),
            packed_ids: HashMap::new(),
            anywhere,
            top_rewrite_paths: HashSet::new(),
            top_rewrite_ids: HashSet::new(),
            ill_sorted_ground: false,
            incremental: false,
            replay: Vec::new(),
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
                        self.less_than_eq(&actual, expected)?
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
                        .then(|| {
                            self.grammar
                                .body_function_lhs(child, &child_path, self.anywhere)
                        })
                        .flatten();
                    let child_expected = if let Some((lhs, lhs_path)) = &function_child_sort {
                        self.actual_sort(lhs, lhs_path)?
                    } else if self.anywhere
                        && self.top_rewrite_paths.contains(path)
                        && descriptor
                            .label
                            .as_ref()
                            .is_some_and(|label| label.is(InternalLabel::KRewrite))
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
                        self.less_than_eq(&actual, expected)?
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
                        .then(|| self.grammar.packed_body_function_lhs(child, self.anywhere))
                        .flatten();
                    let child_expected = if let Some(lhs) = function_lhs {
                        self.actual_packed_sort(lhs)?
                    } else if self.anywhere
                        && self.top_rewrite_ids.contains(&identity)
                        && descriptor
                            .label
                            .as_ref()
                            .is_some_and(|label| label.is(InternalLabel::KRewrite))
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
                    .or_insert_with(|| Datatype::new_const(name.clone(), &self.base.datatype.sort))
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
            .or_insert_with(|| Datatype::new_const(key, &self.base.datatype.sort))
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
                    .or_insert_with(|| Datatype::new_const(name.clone(), &self.base.datatype.sort))
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
            .or_insert_with(|| Datatype::new_const(key, &self.base.datatype.sort))
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
                self.less_than_eq(&variable, expected)?
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
            CastContext::None | CastContext::Semantic => self.less_than_eq(&actual, expected)?,
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
                            .is_some_and(|source| source == id)
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
        // Invariant: the solver contains exactly the satisfiable replay prefix; the next
        // constraint becomes permanent only when its temporary scoped check is satisfiable.
        for constraint in constraints {
            solver.push();
            solver.assert(&constraint.constraint);
            match check(&solver) {
                SatResult::Sat => {
                    solver.pop(1);
                    solver.assert(&constraint.constraint);
                }
                SatResult::Unknown => {
                    return Err(z3_error("Could not solve sort constraints."));
                }
                SatResult::Unsat => {
                    solver.pop(1);
                    if !matches!(check(&solver), SatResult::Sat) {
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

    /// The order constraint `lesser <= greater` in the subsort order: true exactly in the models
    /// where the two values are equal or are a pair `(l, r)` of the relation `R`
    /// (`order_relation`). `R` is the grammar's semantic subsort relation, the one order every
    /// caller uses: the hard constraints, the preferences, and the climb and blocking clause of
    /// `maximal_models`.
    ///
    /// The formula over the whole relation, `OR over (l, r) in R of (lesser = l and greater =
    /// r)` then `or lesser = greater` (`OrderRelation::full_disjunction`), costs `|R|` disjuncts.
    /// When a side is a closed value `c`, one of the cached constructor terms of `closed_values`,
    /// a smaller formula is equivalent to it:
    ///
    /// - `lesser = c`: `OR over r in up(c) of greater = r`, then `or c = greater`;
    /// - `greater = c`: `OR over l in down(c) of lesser = l`, then `or lesser = c`;
    /// - both closed: the constant `lesser == greater or (lesser, greater) in R`.
    ///
    /// Equivalence argument. `KRustInferenceSort` is a Z3 algebraic datatype, which is free:
    /// two syntactically distinct constructor terms denote distinct elements in every model.
    /// Every value in `R` and in `closed_values` is a constructor term that `sort_value` builds,
    /// and Z3 shares structurally equal terms, so AST identity (`==` and `Hash` on `Datatype`)
    /// is syntactic identity. With `lesser = c`, the disjunct `(c = l and greater = r)` is
    /// therefore false in every model when `l` is not `c`, and is `greater = r` when it is; the
    /// remaining disjuncts are the up-set's. Symmetrically for a closed `greater`. With both
    /// sides closed every equality between them is decided by identity, so the formula is the
    /// constant. No property of `R` is used (not transitivity, not reflexivity), only that the
    /// side treated as closed is a constructor term; a closed term that is not one (an accessor
    /// applied to a value, say) is not in `closed_values` and gets the full disjunction.
    /// Lean: `KRust.SubsortEncoding.new_equiv` (lean/KRust/SubsortEncoding.lean); Rust test:
    /// `tests::ground_side_encoding_is_equivalent`; model conformance of this formula with the
    /// Lean `new`: `tests::lean_bridge::less_than_eq_agrees_with_new`.
    ///
    /// Output argument. Every caller combines these formulas with `and`, `not`, `or` and
    /// pseudo-Boolean bounds, so replacing each by an equivalent one leaves every asserted
    /// formula equivalent: the hard constraints, the climbing and blocking clauses of
    /// `maximal_models` and the preferences of `top_preferences`, hence the same satisfiable
    /// problems, order and preference counts (`KRust.MaximalModels.Equivalent`, Rust test
    /// `tests::order_constraints_are_equivalent_at_every_call_site`).
    /// `maximal_models` then records the same maximal real typings, each with a parameter
    /// vector that `prefer_parameters` admits under either formula
    /// (`KRust.MaximalModels.runs_agree_up_to_pref`). Every admissible vector is applied, so
    /// the candidate parses are the same (`KRust.MaximalModels.runs_agree_candidates`). What
    /// may change is what depends on the particular models
    /// Z3 returns: the number of checks (`ParserZ3Checks`), the order of recorded models, and
    /// the sorts named in the diagnostics of a rejected input.
    fn less_than_eq(&self, lesser: &Datatype, greater: &Datatype) -> Result<Bool, ParseError> {
        let relation = &self.semantic_relation;
        #[cfg(test)]
        if FORCE_FULL_DISJUNCTION.with(std::cell::Cell::get) {
            return Ok(relation.full_disjunction(lesser, greater));
        }
        let formula = match (
            self.closed_values.contains(lesser),
            self.closed_values.contains(greater),
        ) {
            (true, true) => {
                Bool::from_bool(lesser == greater || relation.up(lesser).contains(greater))
            }
            (true, false) => {
                let mut cases = relation
                    .up(lesser)
                    .iter()
                    .map(|right| greater.eq(right))
                    .collect::<Vec<_>>();
                cases.push(lesser.eq(greater));
                or_all(&cases)
            }
            (false, true) => {
                let mut cases = relation
                    .down(greater)
                    .iter()
                    .map(|left| lesser.eq(left))
                    .collect::<Vec<_>>();
                cases.push(lesser.eq(greater));
                or_all(&cases)
            }
            (false, false) => relation.full_disjunction(lesser, greater),
        };
        #[cfg(test)]
        ORDER_CONSTRAINTS.with(|calls| {
            if let Some(calls) = calls.borrow_mut().as_mut() {
                calls.push(OrderConstraintCall {
                    lesser: lesser.clone(),
                    greater: greater.clone(),
                    formula: formula.clone(),
                });
            }
        });
        Ok(formula)
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
        if !self
            .head_indexes
            .contains_key(&SortHead::nullary(FrontendSort::KLabel.as_str()))
        {
            return Ok(());
        }
        let klabel = self.sort_value(&Sort::frontend(FrontendSort::KLabel), &BTreeMap::new())?;
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
        for preferred in [
            BuiltinSort::K.k_name(),
            BuiltinSort::KItem.k_name(),
            FrontendSort::Bag.as_str(),
        ] {
            let sort = Sort::new(preferred);
            if !self.ground_sorts.contains(&sort) {
                continue;
            }
            let preferred = self.sort_value(&sort, &BTreeMap::new())?;
            for (name, variable) in &self.variables {
                if select(name) {
                    constraints.push(self.less_than_eq(&preferred, variable)?);
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
            match check(solver) {
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
        // Invariant: `low` preferences are satisfiable, values above `high` are unsatisfiable,
        // and the interval strictly shrinks toward the maximal satisfiable count.
        while low < high {
            let candidate = low + (high - low).div_ceil(2);
            solver.push();
            solver.assert(Bool::pb_ge(&weighted, candidate as i32));
            let status = check(solver);
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
    ///
    /// Returns the maximal overload and top-preference counts; together with the hard
    /// constraints and the pinned real variables they define the admissible parameter vectors
    /// that [`Encoding::admissible_parameters`] enumerates.
    fn prefer_parameters(
        &self,
        solver: &Solver,
        values: &mut BTreeMap<String, Sort>,
    ) -> Result<PreferenceCounts, ParseError> {
        let top_preferences = self.top_preferences(|name| self.parameters.contains(name))?;
        let mut counts = PreferenceCounts::default();
        if self.packed_overload_preferences.is_empty() && top_preferences.is_empty() {
            return Ok(counts);
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
            counts = PreferenceCounts { overloads, tops };
            if overloads == 0 && tops == 0 {
                return Ok(None);
            }
            match check(solver) {
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
        Ok(counts)
    }

    /// Enumerate the maximal real-variable typings, each with every admissible parameter vector
    /// ([`Encoding::admissible_parameters`]); the first model of each group is the one
    /// `prefer_parameters` kept.
    ///
    /// Maximal is pointwise in the subsort order of `less_than_eq`, the order of the hard
    /// constraints: the climb raises a satisfying typing while some variable can grow, and the
    /// blocking clause excludes every typing below a recorded one. Two typings that differ by a
    /// labelled chain production (`T:Id` against `T:Type` with `Type ::= Id [symbol(class)]`)
    /// are incomparable, so both are recorded and the post-inference passes decide between
    /// their parses (`prefer`/`avoid`, or an ambiguity).
    fn maximal_models(
        &self,
        solver: &Solver,
        seed: Option<BTreeMap<String, Sort>>,
    ) -> Result<Vec<Vec<BTreeMap<String, Sort>>>, ParseError> {
        let real_variables = self
            .variables
            .keys()
            .filter(|name| !self.parameters.contains(*name))
            .cloned()
            .collect::<Vec<_>>();
        let mut models = Vec::new();
        let mut first = seed;
        // Invariant: every recorded model is maximal and blocked; each iteration consumes the
        // optional seed or finds the next unblocked satisfying assignment.
        loop {
            let mut values = if let Some(seed) = first.take() {
                seed
            } else {
                match check(solver) {
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
            // Invariant: `values` is satisfiable and each successful iteration strictly raises
            // at least one real variable in the finite sort order.
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
                let status = check(solver);
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
            let counts = self.prefer_parameters(solver, &mut values)?;
            let admissible = self.admissible_parameters(solver, &values, counts)?;
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
                    )
                })
                .collect::<Result<Vec<_>, ParseError>>()?;
            solver.assert(and_all(&dominated).not());
            models.push(admissible);
            if real_variables.is_empty() {
                break;
            }
        }
        Ok(models)
    }

    /// Every admissible parameter vector of a recorded variable typing, `chosen` first.
    ///
    /// The hard constraints fix the variable typing `chosen` records, but not always its formal
    /// parameters: several vectors can reach the maximal preference counts that
    /// `prefer_parameters` asserts, and no inference criterion orders them, since they share
    /// the typing and the counts. Each of them types a well-sorted parse of the sentence, so each
    /// is returned, and the caller applies each one as a candidate. The post-inference passes
    /// then see every such parse as an alternative of one ambiguity, exactly as they see the
    /// parses of two incomparable maximal typings: they resolve it (overloads, `prefer`/`avoid`,
    /// alternatives that lower to the same term) or report it as `ParseError::Ambiguous`. The
    /// parse is therefore a function of the admissible set, not of the vector Z3 returned.
    ///
    /// With the real variables pinned to `chosen` and both maximal counts asserted, the
    /// constraints are exactly those that define an admissible vector: the blocking clauses of
    /// earlier records name only real variables and hold at `chosen`, which is unblocked. Each
    /// step excludes exactly the last vector found, so an `Unsat` answer means that the whole
    /// admissible set has been returned; a singleton set costs one check. A parameter linked by
    /// the order constraints to no ground sort and no real variable can range over infinitely
    /// many values of the datatype's parametric heads; when there are more than
    /// `PARAMETER_CHOICE_LIMIT` vectors the inference fails instead of keeping a subset.
    fn admissible_parameters(
        &self,
        solver: &Solver,
        chosen: &BTreeMap<String, Sort>,
        counts: PreferenceCounts,
    ) -> Result<Vec<BTreeMap<String, Sort>>, ParseError> {
        let mut admissible = vec![chosen.clone()];
        if self.parameters.is_empty() {
            return Ok(admissible);
        }
        solver.push();
        let result = (|| {
            for (name, variable) in &self.variables {
                if self.parameters.contains(name) {
                    continue;
                }
                let current = self.sort_value(
                    chosen
                        .get(name)
                        .expect("all inference variables have model values"),
                    &BTreeMap::new(),
                )?;
                solver.assert(variable.eq(&current));
            }
            let top_preferences = if counts.tops > 0 {
                self.top_preferences(|name| self.parameters.contains(name))?
            } else {
                Vec::new()
            };
            for (preferences, count) in [
                (&self.packed_overload_preferences, counts.overloads),
                (&top_preferences, counts.tops),
            ] {
                if count > 0 {
                    let weighted = preferences
                        .iter()
                        .map(|constraint| (constraint, 1))
                        .collect::<Vec<_>>();
                    solver.assert(Bool::pb_ge(&weighted, count as i32));
                }
            }
            // Invariant: `admissible` holds distinct admissible vectors, each excluded on the
            // solver once found; each iteration excludes the last one and finds a further one,
            // stops, or fails at the limit.
            loop {
                let last = admissible.last().expect("`chosen` is the first vector");
                let blocked = self
                    .parameters
                    .iter()
                    .map(|name| {
                        let value = self.sort_value(
                            last.get(name)
                                .expect("all inference variables have model values"),
                            &BTreeMap::new(),
                        )?;
                        Ok(self
                            .variables
                            .get(name)
                            .expect("parameters are also inference variables")
                            .ne(&value))
                    })
                    .collect::<Result<Vec<_>, ParseError>>()?;
                solver.assert(or_all(&blocked));
                match check(solver) {
                    SatResult::Unsat => return Ok(()),
                    SatResult::Unknown => {
                        return Err(z3_error(
                            "Z3 returned unknown while enumerating admissible sort parameters",
                        ));
                    }
                    SatResult::Sat => {}
                }
                if admissible.len() == PARAMETER_CHOICE_LIMIT {
                    return Err(z3_error(format!(
                        "sort inference found more than {PARAMETER_CHOICE_LIMIT} admissible sort \
                         parameter choices for one variable typing and cannot enumerate the \
                         parses of the sentence"
                    )));
                }
                admissible.push(self.read_model(&solver.get_model().ok_or_else(|| {
                    z3_error("Z3 returned sat without an admissible parameter model")
                })?)?);
            }
        })();
        solver.pop(1);
        result.map(|()| admissible)
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
                // A semantic cast bounds the variable from above; it records the variable's sort
                // only when the model chose the bound itself. Otherwise the variable carries the
                // model's sort under the cast, so every occurrence agrees on it.
                if cast_context == CastContext::Semantic && inferred == expected {
                    Ok(Rc::clone(&term))
                } else if cast_context == CastContext::Semantic
                    && let Some(variable) = super::variable_with_inferred_sort(leaf, inferred)
                {
                    Ok(PackedTerm::leaf(variable))
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
                        .is_some_and(|label| label.is(InternalLabel::KRewrite))
                    && children.len() == 2)
                    .then(|| self.declared_packed_model_sort(&children[0], model));
                let function_body_sort = is_top_sort_production(descriptor)
                    .then(|| {
                        children.first().and_then(|child| {
                            self.grammar
                                .packed_body_function_lhs(child, self.anywhere)
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
                if declares_parametric_sort(descriptor) && cast_context != CastContext::Semantic {
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
        let label = Label::semantic_cast(sort).name;
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
                // As in the packed read-back: under a semantic cast the variable carries the
                // model's sort itself unless the model chose the bound.
                if cast_context == CastContext::Semantic {
                    if inferred == expected {
                        return Ok(term);
                    }
                    if let Some(variable) = super::variable_with_inferred_sort(leaf, inferred) {
                        return Ok(ParsedTerm::Term(variable));
                    }
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
                        .is_some_and(|label| label.is(InternalLabel::KRewrite))
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
                                .body_function_lhs(child, &format!("{path}_c0"), self.anywhere)
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
                if declares_parametric_sort(descriptor) && cast_context != CastContext::Semantic {
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
        let label = Label::semantic_cast(sort).name;
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

/// TypeInferenceVisitor.java:278-293 (`hasParametricSort`): a parametric production is wrapped
/// in the cast of its instantiated sort only when the *original* production declares a
/// parametric-headed sort as its result or as a nonterminal (`{Width} MInt{Width} ::= ...`,
/// `{Width} Bool ::= MInt{Width} "==MInt" MInt{Width}`). The instantiated result of a sort-variable
/// production such as `{Sort} Sort ::= Sort "=>" Sort` does not count even when the model
/// instantiates it at a parametric instance like `MInt{64}`.
fn declares_parametric_sort(production: &Production) -> bool {
    production.parametric_origin.is_some()
        && (!production_result(production).parameters.is_empty()
            || production_nonterminals(production)
                .iter()
                .any(|sort| !sort.parameters.is_empty()))
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
    let Some(label) = production.label.as_ref() else {
        return CastContext::None;
    };
    if matches!(label.generated(), Some(GeneratedLabel::SemanticCast { .. })) {
        return CastContext::Semantic;
    }
    match InternalLabel::of(&label.name) {
        Some(InternalLabel::SyntacticCast | InternalLabel::SyntacticCastBraced) => {
            CastContext::Strict
        }
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
    // Invariant: `visited` contains every packed identity already scanned and `pending` contains
    // reachable identities whose token sorts or descendants remain to be examined.
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
    // Invariant: `ids` assigns one stable preorder number to every visited identity; recursion
    // only descends into an identity absent from the map.
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
                    || descriptor.result.is_frontend(FrontendSort::RuleContent)
                    || (descriptor.result.is_frontend(FrontendSort::RuleBody)
                        && descriptor
                            .label
                            .as_ref()
                            .is_some_and(|label| label.is(InternalLabel::WithConfig)))
                {
                    if let Some(child) = children.first() {
                        visit(grammar, child, format!("{path}_c0"), targets);
                    }
                } else if descriptor
                    .label
                    .as_ref()
                    .is_some_and(|label| label.is(InternalLabel::KRewrite))
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
                    || descriptor.result.is_frontend(FrontendSort::RuleContent)
                    || (descriptor.result.is_frontend(FrontendSort::RuleBody)
                        && descriptor
                            .label
                            .as_ref()
                            .is_some_and(|label| label.is(InternalLabel::WithConfig)))
                {
                    if let Some(child) = children.first() {
                        visit(grammar, child, targets);
                    }
                } else if descriptor
                    .label
                    .as_ref()
                    .is_some_and(|label| label.is(InternalLabel::KRewrite))
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
/// A token leaf that is not a variable: the only leaf `getFunction` can return with a real sort.
fn is_token_leaf(leaf: &Term) -> bool {
    inferred_variable_name(leaf).is_none() && matches!(leaf.unannotated(), Term::Token { .. })
}

fn is_top_sort_production(production: &Production) -> bool {
    [FrontendSort::RuleContent, FrontendSort::RuleBody]
        .iter()
        .any(|sort| production.result.name == sort.as_str())
}

fn is_real_ground_sort(sort: &Sort) -> bool {
    !sort.parameters.is_empty()
        || !is_parser_sort(sort)
        || sort.name == BuiltinSort::K.k_name()
        || sort.name == BuiltinSort::KItem.k_name()
        || sort.is_frontend(FrontendSort::KLabel)
        || sort.name.parse::<u64>().is_ok()
}

fn is_parser_sort(sort: &Sort) -> bool {
    [BuiltinSort::K, BuiltinSort::KItem, BuiltinSort::KConfigVar]
        .iter()
        .any(|builtin| sort.name == builtin.k_name())
        || [
            FrontendSort::KBott,
            FrontendSort::KLabel,
            FrontendSort::KList,
            FrontendSort::KString,
        ]
        .iter()
        .any(|frontend| sort.name == frontend.as_str())
        || sort.name.starts_with('#')
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
    use super::super::ParametricOrigin;
    use super::*;
    use crate::definition::ProductionItem;
    use crate::kast::Label;
    use proptest::prelude::*;

    mod lean_bridge;

    fn nonterminal(name: &str) -> ProductionItem {
        ProductionItem::NonTerminal {
            sort: Sort::new(name),
            name: None,
        }
    }

    fn cached_encoding_fixture(sort_count: usize) -> (Grammar, Rc<PackedTerm>, Sort) {
        let mut grammar = Grammar::default();
        for index in 0..sort_count {
            grammar
                .add(
                    Sort::new(format!("S{index}")),
                    vec![ProductionItem::Terminal(format!("s{index}"))],
                    Some(Label::new(format!("s{index}"))),
                    false,
                    false,
                )
                .unwrap();
            if index > 0 {
                grammar.subsort_relations.insert((
                    Sort::new(format!("S{}", index - 1)),
                    Sort::new(format!("S{index}")),
                ));
            }
        }
        let top_sort =
            Sort::with_parameters("Box", vec![Sort::new(format!("S{}", sort_count - 1))]);
        let production = grammar.productions.len();
        grammar
            .add(
                top_sort.clone(),
                vec![ProductionItem::Terminal("box".into())],
                Some(Label::new("box")),
                false,
                false,
            )
            .unwrap();
        (
            grammar,
            PackedTerm::production(production, vec![], Default::default()),
            top_sort,
        )
    }

    fn decoded_relation(
        base: &EncodingBase,
        relation: &[(Datatype, Datatype)],
    ) -> Result<Vec<(Sort, Sort)>, ParseError> {
        relation
            .iter()
            .map(|(left, right)| Ok((base.decode_sort(left)?, base.decode_sort(right)?)))
            .collect()
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(32))]

        #[test]
        fn cached_encoding_base_matches_uncached(sort_count in 2usize..6) {
            let (grammar, term, top_sort) = cached_encoding_fixture(sort_count);
            let mut term_sorts = TermSorts::default();
            collect_packed_term_sorts(&term, &mut term_sorts.heads, &mut term_sorts.ground);
            let cached = encoding_base(&grammar, &top_sort, &term_sorts).unwrap();
            let uncached = encoding_base_uncached(&grammar, &top_sort, &term_sorts).unwrap();
            prop_assert_eq!(&cached.heads, &uncached.heads);
            prop_assert_eq!(&cached.head_indexes, &uncached.head_indexes);
            prop_assert_eq!(&cached.ground_sorts, &uncached.ground_sorts);
            prop_assert_eq!(&cached.declared_nat_sorts, &uncached.declared_nat_sorts);
            let cached_variants = cached.datatype.variants.iter()
                .map(|variant| variant.constructor.name().to_string())
                .collect::<Vec<_>>();
            let uncached_variants = uncached.datatype.variants.iter()
                .map(|variant| variant.constructor.name().to_string())
                .collect::<Vec<_>>();
            prop_assert_eq!(cached_variants, uncached_variants);
            prop_assert_eq!(
                decoded_relation(&cached, &cached.semantic_relation.pairs).unwrap(),
                decoded_relation(&uncached, &uncached.semantic_relation.pairs).unwrap()
            );
        }

        #[test]
        fn cached_and_uncached_inference_agree(
            first_sort_count in 2usize..5,
            second_sort_count in 2usize..5,
            repetitions in 1usize..4,
        ) {
            let first = cached_encoding_fixture(first_sort_count);
            let second = cached_encoding_fixture(second_sort_count);
            for (grammar, term, top_sort) in [&first, &second].into_iter().cycle().take(2 * repetitions) {
                let before = measure::snapshot();
                let cached = grammar.infer_packed_sorts_z3(Rc::clone(term), top_sort, false);
                let cached_checks = measure::snapshot()
                    .delta(&before)
                    .get(Counter::ParserZ3Checks);
                let before = measure::snapshot();
                let uncached = with_uncached_encoding_base(|| {
                    grammar.infer_packed_sorts_z3(Rc::clone(term), top_sort, false)
                });
                let uncached_checks = measure::snapshot()
                    .delta(&before)
                    .get(Counter::ParserZ3Checks);
                prop_assert_eq!(cached, uncached);
                prop_assert_eq!(cached_checks, uncached_checks);
            }
        }

        #[test]
        fn cached_sort_values_round_trip(sort_count in 2usize..6, repetitions in 1usize..4) {
            let (grammar, term, top_sort) = cached_encoding_fixture(sort_count);
            for _ in 0..repetitions {
                grammar
                    .infer_packed_sorts_z3(Rc::clone(&term), &top_sort, false)
                    .unwrap();
            }
            let mut term_sorts = TermSorts::default();
            collect_packed_term_sorts(&term, &mut term_sorts.heads, &mut term_sorts.ground);
            let base = encoding_base(&grammar, &top_sort, &term_sorts).unwrap();
            for sort in &base.ground_sorts {
                let value = base.sort_value(sort, &BTreeMap::new()).unwrap();
                prop_assert_eq!(base.decode_sort(&value).unwrap(), sort.clone());
            }
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(48))]

        /// Rust side of the Lean theorem `KRust.SubsortEncoding.new_equiv`
        /// (lean/KRust/SubsortEncoding.lean): for every relation `R` over cached ground sort
        /// values, `Encoding::less_than_eq`, which encodes a constraint with a closed side from
        /// that side's up- or down-set (the model's `new`), and the full disjunction over `R`
        /// (`OrderRelation::full_disjunction`, the model's `old`) are logically equivalent, so
        /// Z3 must report `¬(old ⇔ new)` unsatisfiable.
        /// The Lean proof says this test cannot fail as long as its one hypothesis `hI` holds
        /// (distinct cached constructor terms denote distinct values in every Z3 model); the test
        /// checks that the Rust code matches the Lean model and that Z3 satisfies `hI`.
        /// `R` is arbitrary, not a closed partial order, because the theorem needs no hypothesis
        /// on it. The sides
        /// are every cached ground value and, for the model's `other` case, two variables, a
        /// constructor applied to a variable, and an accessor applied to a cached value (a
        /// closed term that is not a cached constructor term), so every pair of kinds
        /// (closed/closed, closed/open, open/closed, open/open) occurs.
        #[test]
        fn ground_side_encoding_is_equivalent(
            sort_count in 2usize..5,
            semantic in proptest::collection::vec((0usize..16, 0usize..16), 0..12),
        ) {
            let (grammar, term, top_sort) = cached_encoding_fixture(sort_count);
            let mut term_sorts = TermSorts::default();
            collect_packed_term_sorts(&term, &mut term_sorts.heads, &mut term_sorts.ground);
            let mut base = EncodingBase::build(&grammar, &top_sort, &term_sorts).unwrap();
            let ground = base.ground_values.borrow().values().cloned().collect::<Vec<_>>();
            base.semantic_relation = OrderRelation::new(
                semantic
                    .iter()
                    .map(|(left, right)| {
                        (
                            ground[left % ground.len()].clone(),
                            ground[right % ground.len()].clone(),
                        )
                    })
                    .collect(),
            );
            let mut encoding =
                Encoding::new_with_term_sorts(&grammar, &top_sort, false, &term_sorts).unwrap();
            encoding.base = Rc::new(base);

            let sort = &encoding.datatype.sort;
            let box_index = encoding.head_indexes[&SortHead::from(&top_sort)];
            let box_variant = &encoding.datatype.variants[box_index];
            let boxed = encoding.sort_value(&top_sort, &BTreeMap::new()).unwrap();
            let x = Datatype::new_const("x", sort);
            let others = vec![
                x.clone(),
                Datatype::new_const("y", sort),
                box_variant.constructor.apply(&[&x]).as_datatype().unwrap(),
                box_variant.accessors[0].apply(&[&boxed]).as_datatype().unwrap(),
            ];
            let sides = ground.iter().chain(&others).collect::<Vec<_>>();
            let relation = &encoding.semantic_relation;
            for lesser in &sides {
                for greater in &sides {
                    let old = relation.full_disjunction(lesser, greater);
                    let new = encoding.less_than_eq(lesser, greater).unwrap();
                    let solver = Solver::new();
                    solver.assert(old.iff(&new).not());
                    prop_assert_eq!(
                        solver.check(),
                        SatResult::Unsat,
                        "old and new differ for {} <= {}",
                        lesser,
                        greater
                    );
                }
            }
        }
    }

    /// The order of a generated subsort problem: sorts `S0..S{n-1}` and the nullary sorts in
    /// `EXTRA_ORDER_SORTS`, related by pairs oriented from the lesser to the greater index, so
    /// every generated relation is acyclic.
    const EXTRA_ORDER_SORTS: [&str; 4] = ["K", "KItem", "KList", "#RuleBody"];

    fn order_sort(index: usize, sort_count: usize) -> Sort {
        if index < sort_count {
            Sort::new(format!("S{index}"))
        } else {
            Sort::new(EXTRA_ORDER_SORTS[(index - sort_count) % EXTRA_ORDER_SORTS.len()])
        }
    }

    fn oriented_pairs(pairs: &[(usize, usize)], sort_count: usize) -> BTreeSet<(Sort, Sort)> {
        let element_count = sort_count + EXTRA_ORDER_SORTS.len();
        pairs
            .iter()
            .map(|(left, right)| (left % element_count, right % element_count))
            .filter(|(left, right)| left != right)
            .map(|(left, right)| {
                (
                    order_sort(left.min(right), sort_count),
                    order_sort(left.max(right), sort_count),
                )
            })
            .collect()
    }

    /// A grammar whose encoding datatype has the generated nullary sorts, the unary head `Box`
    /// (the top sort `Box{S0}`) and the binary head `Pair` (a production of sort `Pair{S0, S1}`);
    /// `semantic` becomes its subsort relation.
    fn order_fixture(sort_count: usize, semantic: &[(usize, usize)]) -> (Grammar, Sort, TermSorts) {
        let mut grammar = Grammar::default();
        for index in 0..sort_count + EXTRA_ORDER_SORTS.len() {
            grammar
                .add(
                    order_sort(index, sort_count),
                    vec![ProductionItem::Terminal(format!("s{index}"))],
                    Some(Label::new(format!("s{index}"))),
                    false,
                    false,
                )
                .unwrap();
        }
        grammar
            .add(
                Sort::with_parameters("Pair", vec![Sort::new("S0"), Sort::new("S1")]),
                vec![ProductionItem::Terminal("pair".into())],
                Some(Label::new("pair")),
                false,
                false,
            )
            .unwrap();
        grammar.subsort_relations = oriented_pairs(semantic, sort_count);
        let top_sort = Sort::with_parameters("Box", vec![Sort::new("S0")]);
        (grammar, top_sort, TermSorts::default())
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(48))]

        /// Rust side of the hypothesis `hP : P.WF` of `KRust.MaximalModels`
        /// (lean/KRust/MaximalModels.lean): `Encoding::less_than_eq`, the semantic subsort order
        /// that the hard constraints, the preferences, the climb and the blocking clause all
        /// use, is reflexive and transitive on every value of the encoding datatype.
        /// Fresh constants range over every value a Z3 model can give a variable or a parameter,
        /// including values of the parametric heads and of the parser sorts that
        /// `restrict_to_real_sorts` excludes, so Z3 must report an irreflexive or a
        /// transitivity-breaking assignment unsatisfiable.
        #[test]
        fn subsort_order_is_a_preorder_on_model_values(
            sort_count in 2usize..5,
            semantic in proptest::collection::vec((0usize..16, 0usize..16), 0..10),
        ) {
            let (grammar, top_sort, term_sorts) = order_fixture(sort_count, &semantic);
            let encoding =
                Encoding::new_with_term_sorts(&grammar, &top_sort, false, &term_sorts).unwrap();
            let sort = &encoding.datatype.sort;
            let x = Datatype::new_const("x", sort);
            let y = Datatype::new_const("y", sort);
            let z = Datatype::new_const("z", sort);
            let le = |lesser: &Datatype, greater: &Datatype| {
                encoding.less_than_eq(lesser, greater).unwrap()
            };
            let solver = Solver::new();
            solver.assert(le(&x, &x).not());
            prop_assert_eq!(solver.check(), SatResult::Unsat, "less_than_eq(x, x) is falsifiable");
            let solver = Solver::new();
            solver.assert(le(&x, &y));
            solver.assert(le(&y, &z));
            solver.assert(le(&x, &z).not());
            prop_assert_eq!(
                solver.check(),
                SatResult::Unsat,
                "less_than_eq is not transitive"
            );
        }

        /// Rust side of the hypothesis `hR : P.RoundTrip` of `KRust.MaximalModels`: for every
        /// value `v` that `model.eval` returns for a constant of the encoding datatype,
        /// `sort_value(decode_sort(v))` is the same Z3 term as `v` (`Datatype`'s `==` is
        /// `Z3_is_eq_ast`). This extends `cached_sort_values_round_trip`, which starts from
        /// ground sorts, to the values of models, including nested parametric values.
        /// The constants are constrained at random (a constructor applied to other constants, a
        /// tester, an equality or a disequality with a cached ground value), and always so that
        /// `x3 = Pair(x0, x1)` with `x0 ≠ x1`.
        #[test]
        fn model_values_round_trip(
            sort_count in 2usize..5,
            semantic in proptest::collection::vec((0usize..16, 0usize..16), 0..6),
            constraints in proptest::collection::vec(
                (0usize..4, 0usize..6, 0usize..16, 0usize..16), 0..8,
            ),
        ) {
            let (grammar, top_sort, term_sorts) = order_fixture(sort_count, &semantic);
            let encoding =
                Encoding::new_with_term_sorts(&grammar, &top_sort, false, &term_sorts).unwrap();
            let datatype = &encoding.datatype;
            let ground = encoding.ground_values.borrow().values().cloned().collect::<Vec<_>>();
            let constants = (0..6)
                .map(|index| Datatype::new_const(format!("x{index}"), &datatype.sort))
                .collect::<Vec<_>>();
            let apply = |head: usize, first: usize| {
                let variant = &datatype.variants[head % datatype.variants.len()];
                let arguments = (0..variant.accessors.len())
                    .map(|offset| &constants[(first + offset) % constants.len()] as &dyn Ast)
                    .collect::<Vec<_>>();
                variant.constructor.apply(&arguments).as_datatype().unwrap()
            };
            let pair = encoding.head_indexes[&SortHead::new("Pair", 2)];
            let solver = Solver::new();
            solver.assert(constants[3].eq(apply(pair, 0)));
            solver.assert(constants[0].ne(&constants[1]));
            for (kind, subject, head, other) in &constraints {
                let subject = &constants[*subject];
                let constraint = match kind {
                    0 => subject.eq(apply(*head, *other)),
                    1 => datatype.variants[head % datatype.variants.len()]
                        .tester
                        .apply(&[subject])
                        .as_bool()
                        .unwrap(),
                    2 => subject.eq(&ground[other % ground.len()]),
                    _ => subject.ne(&ground[other % ground.len()]),
                };
                solver.assert(&constraint);
            }
            if solver.check() != SatResult::Sat {
                return Ok(());
            }
            let model = solver.get_model().unwrap();
            for constant in &constants {
                let value = model.eval(constant, true).unwrap();
                let sort = encoding.decode_sort(&value).unwrap();
                let encoded = encoding.sort_value(&sort, &BTreeMap::new()).unwrap();
                prop_assert!(
                    encoded == value,
                    "{} evaluates to {}, which decodes to {} and re-encodes to {}",
                    constant,
                    value,
                    sort,
                    encoded
                );
            }
        }
    }

    /// One generated problem of `maximal_models_conform_to_brute_force_maximum`: an ambiguity
    /// over productions `p{k} : R ::= "p{k}" A B` applied to the variables `X`, `Y`, `Z`,
    /// optionally under a unary production `w : R ::= "w" A`, and optionally under a parametric
    /// production `q : {P} R ::= "q" P P` whose second child is one of the variables.
    /// The grammar's syntactic relation carries extra pairs beyond the subsort pairs (a labelled
    /// single-nonterminal production puts such a pair there); the maximality order must ignore
    /// them.
    struct ConformanceProblem {
        grammar: Grammar,
        term: Rc<PackedTerm>,
        top_sort: Sort,
        /// The subsort pairs the generator produced, before any closure.
        semantic: BTreeSet<(Sort, Sort)>,
    }

    #[allow(clippy::too_many_arguments)]
    fn conformance_problem(
        sort_count: usize,
        semantic: &[(usize, usize)],
        extra_syntactic: &[(usize, usize)],
        top: Option<usize>,
        productions: &[(usize, usize, usize)],
        alternatives: &[(usize, usize, usize)],
        wrapper: Option<(usize, usize)>,
        parametric: Option<(usize, usize)>,
    ) -> ConformanceProblem {
        // Sorts `S0..S{n-1}`, and `K` above all of them when `top` is `None`, which also turns
        // on the `K` preferences of `seed_model`.
        let sort = |index: usize| Sort::new(format!("S{}", index % sort_count));
        let mut grammar = Grammar::default();
        for index in 0..sort_count {
            grammar
                .add(
                    sort(index),
                    vec![ProductionItem::Terminal(format!("s{index}"))],
                    Some(Label::new(format!("s{index}"))),
                    false,
                    false,
                )
                .unwrap();
        }
        let oriented = |pairs: &[(usize, usize)]| {
            pairs
                .iter()
                .map(|(left, right)| (left % sort_count, right % sort_count))
                .filter(|(left, right)| left != right)
                .map(|(left, right)| (sort(left.min(right)), sort(left.max(right))))
                .collect::<BTreeSet<_>>()
        };
        let mut semantic = oriented(semantic);
        let top_sort = if let Some(top) = top {
            sort(top)
        } else {
            semantic.extend((0..sort_count).map(|index| (sort(index), Sort::new("K"))));
            Sort::new("K")
        };
        let mut syntactic = oriented(extra_syntactic);
        syntactic.extend(semantic.iter().cloned());
        grammar.subsort_relations = semantic.clone();
        grammar.syntactic_subsort_relations = syntactic;

        let mut indexes = Vec::new();
        for (k, (result, first, second)) in productions.iter().enumerate() {
            indexes.push(grammar.productions.len());
            grammar
                .add(
                    sort(*result),
                    vec![
                        ProductionItem::Terminal(format!("p{k}")),
                        nonterminal(sort(*first).name.as_str()),
                        nonterminal(sort(*second).name.as_str()),
                    ],
                    Some(Label::new(format!("p{k}"))),
                    false,
                    false,
                )
                .unwrap();
        }
        let variable = |index: usize| PackedTerm::leaf(Term::variable(["X", "Y", "Z"][index % 3]));
        let mut term = PackedTerm::ambiguity(
            alternatives
                .iter()
                .map(|(production, first, second)| {
                    PackedTerm::production(
                        indexes[production % indexes.len()],
                        vec![variable(*first), variable(*second)],
                        Default::default(),
                    )
                })
                .collect(),
        );
        if let Some((result, argument)) = wrapper {
            let index = grammar.productions.len();
            grammar
                .add(
                    sort(result),
                    vec![
                        ProductionItem::Terminal("w".into()),
                        nonterminal(sort(argument).name.as_str()),
                    ],
                    Some(Label::new("w")),
                    false,
                    false,
                )
                .unwrap();
            term = PackedTerm::production(index, vec![term], Default::default());
        }
        if let Some((result, second)) = parametric {
            // `{P} R ::= "q" P P`, instantiated at `R` in the grammar; the inference encodes `P`
            // as a formal parameter.
            let index = grammar.productions.len();
            grammar
                .add(
                    sort(result),
                    vec![
                        ProductionItem::Terminal("q".into()),
                        nonterminal(sort(result).name.as_str()),
                        nonterminal(sort(result).name.as_str()),
                    ],
                    Some(Label::new("q")),
                    false,
                    false,
                )
                .unwrap();
            let parameter = Sort::new("P");
            grammar.productions[index].parametric_origin = Some(ParametricOrigin {
                label: Some(Label::new("q")),
                parameters: vec![parameter.clone()],
                result: sort(result),
                items: vec![
                    ProductionItem::Terminal("q".into()),
                    ProductionItem::NonTerminal {
                        sort: parameter.clone(),
                        name: None,
                    },
                    ProductionItem::NonTerminal {
                        sort: parameter.clone(),
                        name: None,
                    },
                ],
                attributes: Default::default(),
                substitution: BTreeMap::from([(parameter, sort(result))]),
            });
            term = PackedTerm::production(index, vec![term, variable(second)], Default::default());
        }
        ConformanceProblem {
            grammar,
            term,
            top_sort,
            semantic,
        }
    }

    /// A perturbation of the solver and of the formulas that leaves the constraint set the
    /// same up to logical equivalence.
    #[derive(Clone, Copy, Debug)]
    struct Perturbation {
        random_seed: Option<u32>,
        /// Reverse the subsort relation of the encoding base, which reverses the order of the
        /// disjuncts of every `less_than_eq`.
        reverse_disjuncts: bool,
        /// Write every order constraint over the whole relation (`FORCE_FULL_DISJUNCTION`), as
        /// `less_than_eq` did before it used the up- and down-sets of a closed side.
        full_disjunction: bool,
    }

    /// Reverse the pairs of a relation, and so the order of its up- and down-sets.
    fn reversed(relation: &OrderRelation) -> OrderRelation {
        OrderRelation::new(relation.pairs.iter().rev().cloned().collect())
    }

    /// The recorded models of one conformance problem: the formal-parameter names and, for each
    /// recorded variable typing in recorded order, its admissible models
    /// (`Encoding::maximal_models`); `None` when the hard constraints are unsatisfiable.
    type RecordedModels = Option<(BTreeSet<String>, Vec<Vec<BTreeMap<String, Sort>>>)>;

    /// The inference path of `Grammar::infer_packed_sorts_z3` up to `maximal_models`: the same
    /// encoding (`Encoding::for_packed_inference`), hard constraints
    /// (`Encoding::assert_packed_hard_constraints`), seed and enumeration, with the
    /// perturbation applied. Returns `None` when the hard constraints are unsatisfiable, and
    /// otherwise the recorded models projected onto the real variables, in recorded order.
    fn recorded_real_projections(
        problem: &ConformanceProblem,
        perturbation: Perturbation,
    ) -> Result<Option<Vec<BTreeMap<String, Sort>>>, ParseError> {
        Ok(
            recorded_models(problem, perturbation)?.map(|(parameters, models)| {
                models
                    .into_iter()
                    .map(|admissible| {
                        let mut model = admissible
                            .into_iter()
                            .next()
                            .expect("a recorded typing has an admissible vector");
                        model.retain(|name, _| !parameters.contains(name));
                        model
                    })
                    .collect()
            }),
        )
    }

    /// `maximal_models` on the inference path of `recorded_real_projections`, with the
    /// perturbation applied.
    fn recorded_models(
        problem: &ConformanceProblem,
        perturbation: Perturbation,
    ) -> Result<RecordedModels, ParseError> {
        let previous =
            FORCE_FULL_DISJUNCTION.with(|force| force.replace(perturbation.full_disjunction));
        let result = recorded_models_unforced(problem, perturbation);
        FORCE_FULL_DISJUNCTION.with(|force| force.set(previous));
        result
    }

    fn recorded_models_unforced(
        problem: &ConformanceProblem,
        perturbation: Perturbation,
    ) -> Result<RecordedModels, ParseError> {
        let term = &problem.term;
        let mut encoding = with_uncached_encoding_base(|| {
            Encoding::for_packed_inference(&problem.grammar, term, &problem.top_sort, false)
        })?;
        if perturbation.reverse_disjuncts {
            let base = Rc::get_mut(&mut encoding.base).expect("an uncached base is not shared");
            base.semantic_relation = reversed(&base.semantic_relation);
        }
        let solver = Solver::new();
        if let Some(seed) = perturbation.random_seed {
            let mut params = z3::Params::new();
            params.set_u32("random_seed", seed);
            solver.set_params(&params);
        }
        encoding.assert_packed_hard_constraints(term, &problem.top_sort, &solver)?;
        let seed = encoding.seed_model(&solver)?;
        match check(&solver) {
            SatResult::Unsat => return Ok(None),
            SatResult::Unknown => return Err(z3_error("unknown in a conformance problem")),
            SatResult::Sat => {}
        }
        let models = encoding.maximal_models(&solver, seed)?;
        Ok(Some((encoding.parameters.clone(), models)))
    }

    /// `Pref(a)` by brute force for the real typing `real`: every assignment of the formal
    /// parameters to the nullary real sorts is checked against the hard constraints with every
    /// variable pinned; the satisfiable ones with the largest number of true overload
    /// preferences, then among those the largest number of true top preferences, are kept, as
    /// `prefer_parameters` orders them. The counts are read by evaluating each preference in the
    /// model of the pinned check.
    fn brute_force_admissible(
        problem: &ConformanceProblem,
        real: &BTreeMap<String, Sort>,
    ) -> Result<BTreeSet<BTreeMap<String, Sort>>, ParseError> {
        let term = &problem.term;
        let mut encoding = with_uncached_encoding_base(|| {
            Encoding::for_packed_inference(&problem.grammar, term, &problem.top_sort, false)
        })?;
        let solver = Solver::new();
        encoding.assert_packed_hard_constraints(term, &problem.top_sort, &solver)?;
        let top_preferences =
            encoding.top_preferences(|name| encoding.parameters.contains(name))?;
        // As in `brute_force_maximal`: no generated sort has a parametric head, so every value a
        // parameter can take is a nullary real sort of the datatype.
        let domain = encoding
            .ground_sorts
            .iter()
            .filter(|sort| sort.parameters.is_empty() && is_real_ground_sort(sort))
            .cloned()
            .collect::<Vec<_>>();
        let parameters = encoding.parameters.iter().cloned().collect::<Vec<_>>();
        let count = |model: &Model, preferences: &[Bool]| {
            preferences
                .iter()
                .filter(|preference| {
                    model
                        .eval(*preference, true)
                        .and_then(|value| value.as_bool())
                        .expect("a pinned model evaluates every preference")
                })
                .count()
        };
        let mut satisfiable = Vec::new();
        let mut choice = vec![0; parameters.len()];
        // Invariant: `choice` enumerates `domain^parameters` in odometer order.
        loop {
            let assignment = parameters
                .iter()
                .zip(&choice)
                .map(|(name, index)| (name.clone(), domain[*index].clone()))
                .collect::<BTreeMap<_, _>>();
            solver.push();
            for (name, sort) in real.iter().chain(&assignment) {
                let variable = encoding
                    .variables
                    .get(name)
                    .expect("every pinned name is an inference variable");
                solver.assert(variable.eq(&encoding.sort_value(sort, &BTreeMap::new())?));
            }
            let status = solver.check();
            if status == SatResult::Sat {
                let model = solver.get_model().expect("sat has a model");
                satisfiable.push((
                    (
                        count(&model, &encoding.packed_overload_preferences),
                        count(&model, &top_preferences),
                    ),
                    assignment,
                ));
            }
            solver.pop(1);
            if status == SatResult::Unknown {
                return Err(z3_error("unknown in a brute-force check"));
            }
            let Some(position) = choice.iter().position(|index| index + 1 < domain.len()) else {
                break;
            };
            choice[position] += 1;
            for index in &mut choice[..position] {
                *index = 0;
            }
        }
        let best = satisfiable.iter().map(|(counts, _)| *counts).max();
        Ok(satisfiable
            .into_iter()
            .filter(|(counts, _)| Some(*counts) == best)
            .map(|(_, assignment)| assignment)
            .collect())
    }

    /// `Max(π(Sat C))` by brute force: every assignment of the real variables to the real
    /// ground sorts is checked against the hard constraints with the variables pinned, and the
    /// maximal satisfiable ones under the pointwise reflexive-transitive closure of the
    /// generated subsort pairs are kept; the extra syntactic pairs play no part. The closure is
    /// computed here, not by `PartialOrder`.
    /// Returns `None` when no assignment is satisfiable.
    fn brute_force_maximal(
        problem: &ConformanceProblem,
    ) -> Result<Option<BTreeSet<BTreeMap<String, Sort>>>, ParseError> {
        let term = &problem.term;
        let mut encoding = with_uncached_encoding_base(|| {
            Encoding::for_packed_inference(&problem.grammar, term, &problem.top_sort, false)
        })?;
        let solver = Solver::new();
        encoding.assert_packed_hard_constraints(term, &problem.top_sort, &solver)?;

        // No generated sort has a parametric head (the parametric production `q` has a formal
        // parameter, not a parametric sort), so every value a real variable can take under
        // `restrict_to_real_sorts` is a nullary real sort of the datatype.
        let domain = encoding
            .ground_sorts
            .iter()
            .filter(|sort| sort.parameters.is_empty() && is_real_ground_sort(sort))
            .cloned()
            .collect::<Vec<_>>();
        let real_variables = encoding
            .variables
            .iter()
            .filter(|(name, _)| !encoding.parameters.contains(*name))
            .map(|(name, variable)| (name.clone(), variable.clone()))
            .collect::<Vec<_>>();
        let mut satisfiable = Vec::new();
        let mut choice = vec![0; real_variables.len()];
        // Invariant: `choice` enumerates `domain^real_variables` in odometer order.
        loop {
            solver.push();
            for ((_, variable), index) in real_variables.iter().zip(&choice) {
                solver
                    .assert(variable.eq(&encoding.sort_value(&domain[*index], &BTreeMap::new())?));
            }
            let status = solver.check();
            solver.pop(1);
            match status {
                SatResult::Sat => satisfiable.push(
                    real_variables
                        .iter()
                        .zip(&choice)
                        .map(|((name, _), index)| (name.clone(), domain[*index].clone()))
                        .collect::<BTreeMap<_, _>>(),
                ),
                SatResult::Unsat => {}
                SatResult::Unknown => return Err(z3_error("unknown in a brute-force check")),
            }
            let Some(position) = choice.iter().position(|index| index + 1 < domain.len()) else {
                break;
            };
            choice[position] += 1;
            for index in &mut choice[..position] {
                *index = 0;
            }
        }
        if satisfiable.is_empty() {
            return Ok(None);
        }

        let mut below = domain
            .iter()
            .flat_map(|lesser| domain.iter().map(move |greater| (lesser, greater)))
            .filter(|(lesser, greater)| {
                lesser == greater
                    || problem
                        .semantic
                        .contains(&((*lesser).clone(), (*greater).clone()))
            })
            .map(|(lesser, greater)| (lesser.clone(), greater.clone()))
            .collect::<BTreeSet<_>>();
        // Warshall's closure: after the pass for `middle`, every path through the sorts before
        // it is a pair.
        for middle in &domain {
            for lesser in &domain {
                for greater in &domain {
                    if below.contains(&(lesser.clone(), middle.clone()))
                        && below.contains(&(middle.clone(), greater.clone()))
                    {
                        below.insert((lesser.clone(), greater.clone()));
                    }
                }
            }
        }
        let le = |lesser: &BTreeMap<String, Sort>, greater: &BTreeMap<String, Sort>| {
            lesser
                .iter()
                .all(|(name, sort)| below.contains(&(sort.clone(), greater[name].clone())))
        };
        Ok(Some(
            satisfiable
                .iter()
                .filter(|candidate| {
                    satisfiable
                        .iter()
                        .all(|other| !le(candidate, other) || other == *candidate)
                })
                .cloned()
                .collect(),
        ))
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(128))]

        /// Rust side of the model-conformance hypothesis of `KRust.MaximalModels`: the Rust loop
        /// is one of the runs the relation `Run` allows. Checked through the consequence
        /// `maximal_models_spec` draws from it: over small generated grammars with ambiguous
        /// parses, the real projections `maximal_models` records are exactly the brute-force
        /// maximal satisfying assignments, with no duplicate; and they stay the same set when
        /// Z3's `random_seed` changes, when the disjuncts of every `less_than_eq` are reversed,
        /// and when every order constraint is written over the whole relation instead of from a
        /// closed side's up- or down-set (the consequence `runs_agree_up_to_pref` draws for
        /// equivalent encodings).
        #[test]
        fn maximal_models_conform_to_brute_force_maximum(
            sort_count in 3usize..6,
            semantic in proptest::collection::vec((0usize..8, 0usize..8), 0..8),
            extra_syntactic in proptest::collection::vec((0usize..8, 0usize..8), 0..4),
            top in proptest::option::of(0usize..8),
            productions in proptest::collection::vec((0usize..8, 0usize..8, 0usize..8), 1..5),
            alternatives in proptest::collection::vec((0usize..8, 0usize..3, 0usize..3), 1..5),
            wrapper in proptest::option::of((0usize..8, 0usize..8)),
            parametric in proptest::option::of((0usize..8, 0usize..3)),
            seeds in (1u32..1000, 1u32..1000),
        ) {
            let problem = conformance_problem(
                sort_count,
                &semantic,
                &extra_syntactic,
                top,
                &productions,
                &alternatives,
                wrapper,
                parametric,
            );
            let expected = brute_force_maximal(&problem).unwrap();
            let perturbation = |random_seed, reverse_disjuncts, full_disjunction| Perturbation {
                random_seed,
                reverse_disjuncts,
                full_disjunction,
            };
            for perturbation in [
                perturbation(None, false, false),
                perturbation(Some(seeds.0), false, false),
                perturbation(None, true, false),
                perturbation(Some(seeds.1), true, false),
                perturbation(None, false, true),
                perturbation(Some(seeds.1), true, true),
            ] {
                let recorded = recorded_real_projections(&problem, perturbation).unwrap();
                match (&expected, recorded) {
                    (None, None) => {}
                    (Some(expected), Some(recorded)) => {
                        let set = recorded.iter().cloned().collect::<BTreeSet<_>>();
                        prop_assert_eq!(
                            set.len(),
                            recorded.len(),
                            "{:?} recorded a real projection twice: {:?}",
                            perturbation,
                            recorded
                        );
                        prop_assert_eq!(&set, expected, "{:?}", perturbation);
                    }
                    (expected, recorded) => prop_assert!(
                        false,
                        "{:?}: brute force {:?}, maximal_models {:?}",
                        perturbation,
                        expected,
                        recorded
                    ),
                }
            }
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(128))]

        /// Rust side of the enumeration-conformance hypothesis of
        /// `KRust.MaximalModels.runs_agree_candidates`: for each recorded variable typing `a`,
        /// `maximal_models` returns exactly the brute-force admissible set `Pref(a)`, without a
        /// duplicate and with `prefer_parameters`'s own vector first, so the candidate set the
        /// inference applies is `Problem.candidates`. Checked on the generated problems of
        /// `maximal_models_conform_to_brute_force_maximum` that carry the parametric production,
        /// under the same perturbations.
        #[test]
        fn admissible_parameters_conform_to_brute_force(
            sort_count in 3usize..6,
            semantic in proptest::collection::vec((0usize..8, 0usize..8), 0..8),
            extra_syntactic in proptest::collection::vec((0usize..8, 0usize..8), 0..4),
            top in proptest::option::of(0usize..8),
            productions in proptest::collection::vec((0usize..8, 0usize..8, 0usize..8), 1..5),
            alternatives in proptest::collection::vec((0usize..8, 0usize..3, 0usize..3), 1..5),
            wrapper in proptest::option::of((0usize..8, 0usize..8)),
            parametric in (0usize..8, 0usize..3),
            seeds in (1u32..1000, 1u32..1000),
        ) {
            let problem = conformance_problem(
                sort_count,
                &semantic,
                &extra_syntactic,
                top,
                &productions,
                &alternatives,
                wrapper,
                Some(parametric),
            );
            for perturbation in [
                Perturbation { random_seed: None, reverse_disjuncts: false, full_disjunction: false },
                Perturbation { random_seed: Some(seeds.0), reverse_disjuncts: true, full_disjunction: false },
                Perturbation { random_seed: Some(seeds.1), reverse_disjuncts: false, full_disjunction: true },
            ] {
                let Some((parameters, models)) = recorded_models(&problem, perturbation).unwrap()
                else {
                    continue;
                };
                prop_assert!(!parameters.is_empty());
                for admissible in models {
                    let first = admissible.first().expect("a recorded typing has a vector");
                    let real = first
                        .iter()
                        .filter(|(name, _)| !parameters.contains(*name))
                        .map(|(name, sort)| (name.clone(), sort.clone()))
                        .collect::<BTreeMap<_, _>>();
                    let vectors = admissible
                        .iter()
                        .map(|model| {
                            prop_assert!(
                                model.iter().all(|(name, sort)| parameters.contains(name)
                                    || real.get(name) == Some(sort)),
                                "{:?}: an admissible model moved a real variable: {:?}",
                                perturbation,
                                model
                            );
                            Ok(model
                                .iter()
                                .filter(|(name, _)| parameters.contains(*name))
                                .map(|(name, sort)| (name.clone(), sort.clone()))
                                .collect::<BTreeMap<_, _>>())
                        })
                        .collect::<Result<Vec<_>, TestCaseError>>()?;
                    let set = vectors.iter().cloned().collect::<BTreeSet<_>>();
                    prop_assert_eq!(set.len(), vectors.len(), "{:?}: duplicate vector", perturbation);
                    prop_assert_eq!(
                        &set,
                        &brute_force_admissible(&problem, &real).unwrap(),
                        "{:?} at {:?}",
                        perturbation,
                        real
                    );
                }
            }
        }
    }

    /// The call sites of `Encoding::less_than_eq` in one packed inference.
    #[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
    enum OrderSite {
        /// The term constraint and the variable and token constraints under it
        /// (`Encoding::assert_packed_hard_constraints`).
        HardConstraint,
        /// `top_preferences`, read by `seed_model` and `prefer_parameters`.
        Preference,
        /// The climb of `maximal_models`: `current <= variable`.
        Climbing,
        /// The blocking clause of `maximal_models`: `variable <= maximal`.
        Blocking,
    }

    /// The kind of an inference variable on a side of an order constraint.
    #[derive(Clone, Copy, Debug)]
    enum Variable {
        Real,
        Parameter,
    }

    /// Run `f` with `ORDER_CONSTRAINTS` recording, and return its result and the calls.
    fn recording<T>(f: impl FnOnce() -> T) -> (T, Vec<OrderConstraintCall>) {
        let previous = ORDER_CONSTRAINTS.with(|calls| calls.replace(Some(Vec::new())));
        let result = f();
        let calls = ORDER_CONSTRAINTS.with(|calls| calls.replace(previous));
        (result, calls.expect("the recorder was set above"))
    }

    /// The `less_than_eq` calls of one packed inference, each with its call site.
    struct OrderConstraintCalls<'a> {
        encoding: Encoding<'a>,
        calls: Vec<(OrderSite, OrderConstraintCall)>,
        /// Whether the hard constraints are satisfiable, so that `maximal_models` ran.
        satisfiable: bool,
    }

    /// The `less_than_eq` calls of the inference path of `Grammar::infer_packed_sorts_z3` up
    /// to `maximal_models`, each with its call site. Every call uses the one subsort order, so
    /// the calls inside `maximal_models` are told apart by the position of the variable: a call
    /// whose greater side is a real variable is the climb (`current <= variable`), one whose
    /// lesser side is a real variable is the blocking clause (`variable <= maximal`), and one
    /// whose greater side is a formal parameter is a preference of `prefer_parameters` (which
    /// selects only the parameters).
    fn order_constraint_calls(
        problem: &ConformanceProblem,
    ) -> Result<OrderConstraintCalls<'_>, ParseError> {
        let term = &problem.term;
        let mut encoding = with_uncached_encoding_base(|| {
            Encoding::for_packed_inference(&problem.grammar, term, &problem.top_sort, false)
        })?;
        let solver = Solver::new();
        let mut sites = Vec::new();
        let (hard, calls) =
            recording(|| encoding.assert_packed_hard_constraints(term, &problem.top_sort, &solver));
        hard?;
        sites.extend(
            calls
                .into_iter()
                .map(|call| (OrderSite::HardConstraint, call)),
        );
        let (seed, calls) = recording(|| encoding.seed_model(&solver));
        let seed = seed?;
        sites.extend(calls.into_iter().map(|call| (OrderSite::Preference, call)));
        let satisfiable = match check(&solver) {
            SatResult::Sat => true,
            SatResult::Unsat => false,
            SatResult::Unknown => return Err(z3_error("unknown in a call-site problem")),
        };
        if satisfiable {
            let (models, calls) = recording(|| encoding.maximal_models(&solver, seed));
            models?;
            // Which kind of inference variable a value is, if any.
            let kind = |value: &Datatype| {
                encoding
                    .variables
                    .iter()
                    .find(|(_, variable)| *variable == value)
                    .map(|(name, _)| {
                        if encoding.parameters.contains(name) {
                            Variable::Parameter
                        } else {
                            Variable::Real
                        }
                    })
            };
            for call in calls {
                let site = match (kind(&call.lesser), kind(&call.greater)) {
                    (None, Some(Variable::Real)) => OrderSite::Climbing,
                    (Some(Variable::Real), None) => OrderSite::Blocking,
                    (None, Some(Variable::Parameter)) => OrderSite::Preference,
                    (lesser, greater) => {
                        return Err(z3_error(format!(
                            "unclassified order constraint in maximal_models: {} <= {} \
                             (variables: {lesser:?}, {greater:?})",
                            call.lesser, call.greater
                        )));
                    }
                };
                sites.push((site, call));
            }
        }
        Ok(OrderConstraintCalls {
            encoding,
            calls: sites,
            satisfiable,
        })
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(128))]

        /// Rust side of the hypothesis `e : Equivalent P Q` of `KRust.MaximalModels`, for the
        /// encodings with and without the closed-side rewrite of `Encoding::less_than_eq`: at
        /// every call site of `less_than_eq` in a packed inference (the hard constraints, the
        /// preferences, the climb and the blocking clause), the formula it built is logically
        /// equivalent to the full disjunction over the same relation, so Z3 must report
        /// `¬(old ⇔ new)` unsatisfiable for each call.
        /// Each call site asserts a Boolean combination (`and`, `not`, `or`, pseudo-Boolean
        /// bounds) of these formulas, so equivalence of every call gives equivalent hard
        /// constraints, climbing order and preferences: the same `sat`, `le` and `pref`.
        /// The problems are those of `maximal_models_conform_to_brute_force_maximum`, whose
        /// optional parametric production gives `prefer_parameters` a formal parameter; each
        /// case also checks that every call site its shape reaches was recorded.
        #[test]
        fn order_constraints_are_equivalent_at_every_call_site(
            sort_count in 3usize..6,
            semantic in proptest::collection::vec((0usize..8, 0usize..8), 0..8),
            extra_syntactic in proptest::collection::vec((0usize..8, 0usize..8), 0..4),
            top in proptest::option::of(0usize..8),
            productions in proptest::collection::vec((0usize..8, 0usize..8, 0usize..8), 1..5),
            alternatives in proptest::collection::vec((0usize..8, 0usize..3, 0usize..3), 1..5),
            wrapper in proptest::option::of((0usize..8, 0usize..8)),
            parametric in proptest::option::of((0usize..8, 0usize..3)),
        ) {
            let problem = conformance_problem(
                sort_count,
                &semantic,
                &extra_syntactic,
                top,
                &productions,
                &alternatives,
                wrapper,
                parametric,
            );
            let OrderConstraintCalls {
                encoding,
                calls,
                satisfiable,
            } = order_constraint_calls(&problem).unwrap();
            for (site, call) in &calls {
                let old = encoding
                    .semantic_relation
                    .full_disjunction(&call.lesser, &call.greater);
                let solver = Solver::new();
                solver.assert(old.iff(&call.formula).not());
                prop_assert_eq!(
                    solver.check(),
                    SatResult::Unsat,
                    "{:?}: old and new differ for {} <= {}",
                    site,
                    call.lesser,
                    call.greater
                );
            }
            let reached = calls.iter().map(|(site, _)| *site).collect::<BTreeSet<_>>();
            prop_assert!(reached.contains(&OrderSite::HardConstraint), "{:?}", reached);
            // `K` is a ground sort exactly when `top` is `None`, which turns on the preferences.
            prop_assert_eq!(reached.contains(&OrderSite::Preference), top.is_none(), "{:?}", reached);
            let real_variables = encoding
                .variables
                .keys()
                .any(|name| !encoding.parameters.contains(name));
            if satisfiable && real_variables {
                prop_assert!(reached.contains(&OrderSite::Climbing), "{:?}", reached);
                prop_assert!(reached.contains(&OrderSite::Blocking), "{:?}", reached);
            }
        }
    }

    /// `p(X)` read as `pa : R ::= "p" A` or `pb : R ::= "p" B`, with the labelled
    /// single-nonterminal productions `chains` (result, argument, label) added to the grammar.
    /// A labelled chain is a constructor, so it adds a pair to the grammar's syntactic relation
    /// and none to its subsort relation.
    fn labelled_chain_problem(chains: &[(&str, &str, &str)]) -> ConformanceProblem {
        let mut grammar = Grammar::default();
        for sort in ["A", "B"] {
            // The production that records the inferred sort of a variable.
            grammar
                .add(
                    Sort::new(sort),
                    vec![nonterminal("KItem")],
                    Some(Label::new(format!("#SemanticCastTo{sort}"))),
                    false,
                    false,
                )
                .unwrap();
        }
        for (result, argument, label) in chains {
            grammar
                .add(
                    Sort::new(*result),
                    vec![nonterminal(argument)],
                    Some(Label::new(*label)),
                    false,
                    false,
                )
                .unwrap();
            assert!(
                grammar
                    .syntactic_subsort_relations
                    .contains(&(Sort::new(*argument), Sort::new(*result)))
            );
        }
        assert!(grammar.subsort_relations.is_empty());
        let mut alternatives = BTreeSet::new();
        for (label, argument) in [("pa", "A"), ("pb", "B")] {
            let production = grammar.productions.len();
            grammar
                .add(
                    Sort::new("R"),
                    vec![ProductionItem::Terminal("p".into()), nonterminal(argument)],
                    Some(Label::new(label)),
                    false,
                    false,
                )
                .unwrap();
            alternatives.insert(PackedTerm::production(
                production,
                vec![PackedTerm::leaf(Term::variable("X"))],
                Default::default(),
            ));
        }
        ConformanceProblem {
            grammar,
            term: PackedTerm::ambiguity(alternatives),
            top_sort: Sort::new("R"),
            semantic: BTreeSet::new(),
        }
    }

    /// The maximal typings `maximal_models` records for `labelled_chain_problem(chains)`, and
    /// the labels of the casts that record `X`'s sort in the parses the inference returns.
    fn labelled_chain_typings(
        chains: &[(&str, &str, &str)],
    ) -> (BTreeSet<BTreeMap<String, Sort>>, BTreeSet<String>) {
        let problem = labelled_chain_problem(chains);
        let recorded = recorded_real_projections(
            &problem,
            Perturbation {
                random_seed: None,
                reverse_disjuncts: false,
                full_disjunction: false,
            },
        )
        .unwrap()
        .expect("p(X) is well-sorted");
        let inferred = problem
            .grammar
            .infer_packed_sorts_z3(Rc::clone(&problem.term), &problem.top_sort, false)
            .unwrap();
        let ParsedTerm::Ambiguity(parses) = &inferred else {
            panic!("expected an ambiguity of two parses, got {inferred:?}")
        };
        let casts = parses
            .iter()
            .map(|parse| {
                let ParsedTerm::Production { children, .. } = parse else {
                    panic!("unexpected parse {parse:?}")
                };
                let ParsedTerm::Production { production, .. } = &children[0] else {
                    panic!("X is not recorded through a cast in {parse:?}")
                };
                problem.grammar.productions[*production]
                    .label
                    .as_ref()
                    .expect("the casts are labelled")
                    .name
                    .clone()
            })
            .collect();
        (recorded.into_iter().collect(), casts)
    }

    fn both_casts() -> BTreeSet<String> {
        BTreeSet::from(["#SemanticCastToA".to_owned(), "#SemanticCastToB".to_owned()])
    }

    fn typing(sort: &str) -> BTreeMap<String, Sort> {
        BTreeMap::from([("variable_X".to_owned(), Sort::new(sort))])
    }

    #[test]
    fn a_labelled_chain_production_does_not_dominate_its_argument_typing() {
        // `f : A ::= B` is a constructor: no `B` value is an `A` value, so `{X:B}` is not below
        // `{X:A}` and both typings of `p(X)` are maximal.
        let (recorded, casts) = labelled_chain_typings(&[("A", "B", "f")]);
        assert_eq!(recorded, BTreeSet::from([typing("A"), typing("B")]));
        assert_eq!(casts, both_casts());
    }

    #[test]
    fn a_labelled_chain_cycle_is_not_a_subsort_cycle() {
        // `f : A ::= B` and `g : B ::= A` are a legal pair of constructors; the subsort order is
        // empty and acyclic, so the encoding builds and both typings stay maximal.
        let (recorded, casts) = labelled_chain_typings(&[("A", "B", "f"), ("B", "A", "g")]);
        assert_eq!(recorded, BTreeSet::from([typing("A"), typing("B")]));
        assert_eq!(casts, both_casts());
    }

    #[test]
    fn encoding_base_covers_its_grammar_sorts() {
        let mut grammar = Grammar::default();
        grammar
            .add(
                Sort::new("S"),
                vec![ProductionItem::Terminal("s".into())],
                Some(Label::new("s")),
                false,
                false,
            )
            .unwrap();
        let base = EncodingBase::build(&grammar, &Sort::new("S"), &TermSorts::default()).unwrap();
        let grammar_sorts = TermSorts {
            heads: base.heads.iter().cloned().collect(),
            ground: base.ground_sorts.clone(),
        };
        assert!(base.covers(&grammar_sorts));
    }

    #[test]
    fn encoding_base_does_not_cover_an_undeclared_mint_width() {
        let grammar = Grammar::default();
        let base = EncodingBase::build(&grammar, &Sort::new("K"), &TermSorts::default()).unwrap();
        let mut term_sorts = TermSorts::default();
        collect_sort(
            &Sort::with_parameters("MInt", vec![Sort::new("37")]),
            &mut term_sorts.heads,
            &mut term_sorts.ground,
        );
        assert!(!base.covers(&term_sorts));
    }

    /// `pair(X:Big, foo(X))` with `foo(Small)`, where the cast production (index 0) is `cast`.
    fn cast_variable_used_at_small(cast: Label) -> (Grammar, ParsedTerm) {
        let mut grammar = Grammar::default();
        grammar
            .add(
                Sort::new("Big"),
                vec![nonterminal("KItem")],
                Some(cast),
                false,
                false,
            )
            .unwrap();
        // The production that records the inferred sort of a variable at Small.
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
        (grammar, term)
    }

    #[test]
    fn semantic_cast_directly_on_variable_is_an_upper_bound() {
        // `X:Big` requires sort(X) <= Big; `foo(X)` requires sort(X) <= Small, so X is Small.
        let (grammar, term) = cast_variable_used_at_small(Label::new("#SemanticCastToBig"));
        let inferred = grammar
            .infer_sorts_z3(term, &Sort::new("K"), false)
            .expect("X at Small satisfies the Big bound and the Small use");
        // The occurrence without a cast records the inferred sort through the Small cast.
        let ParsedTerm::Production { children, .. } = &inferred else {
            panic!("unexpected inference result: {inferred:?}");
        };
        assert!(
            matches!(
                &children[1],
                ParsedTerm::Production { children, .. }
                    if matches!(&children[0], ParsedTerm::Production { production: 1, .. })
            ),
            "X should be recorded at Small: {inferred:?}"
        );
        // The cast occurrence records it too, on X under the Big bound, so X has one sort.
        assert!(
            matches!(
                &children[0],
                ParsedTerm::Production { production: 0, children, .. }
                    if matches!(
                        children[0].leaf(),
                        Some(Term::Variable { sort: Some(sort), .. }) if sort == &Sort::new("Small")
                    )
            ),
            "X under the Big cast should be recorded at Small: {inferred:?}"
        );
    }

    #[test]
    fn strict_cast_directly_on_variable_is_exact() {
        let (grammar, term) = cast_variable_used_at_small(Label::new("#SyntacticCast"));
        let error = grammar
            .infer_sorts_z3(term, &Sort::new("K"), false)
            .expect_err("X::Big and the Small use of X must conflict");
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
