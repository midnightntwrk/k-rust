//! ```toml algorithm
//! id = "backend.search.output"
//! name = "filtering, ordering, and deduplication of reported match conditions"
//! sites = ["MatchOutput::with_source", "MatchOutput::kept_conjuncts", "MatchOutput::generated_equality_variables", "variable_identities", "occurrences"]
//! variable = "q = conjuncts over all disjuncts; e = identities that decide the filter, per disjunct; h = pattern nodes on the paths from a disjunct's conjuncts to the first two occurrences of one identity, with their siblings; D = disjuncts; c = pattern nodes one comparison reads, up to the first difference, without reading equal backend terms"
//! counters = []
//! no_counter = "the output of a search or match has no dedicated counter"
//! span = "none"
//!
//! [[cost]]
//! mode = "one output"
//! bound = "O(q + sum e h + D log D c)"
//! ```
//!
//! Search-target compilation, generated-variable mapping, and hidden-binding filtering.
//!
//! The reported condition is read through backend-term pattern sources and never built as a
//! KORE tree, whose size is the size of the backend terms with every shared subterm written
//! out at each use.

use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fmt, io,
};

use k_rust_backend::{
    definition::BackendDefinition,
    externalize::{self, External, ResultSort},
    rewrite::Pattern,
    rule::Predicate,
    search::{PatternMatch, PatternSearchResult, match_disjunction},
    substitution::Substitution,
    term::{Sort as BackendSort, Variable, VariableKind as BackendVariableKind},
};

use crate::{
    kompile::{CompiledSearchPattern, KoreVariableIdentity},
    kore::{
        ast::{
            Pattern as KorePattern, Sort as KoreSort, Variable as KoreVariable,
            VariableKind as KoreVariableKind,
        },
        node::{PatternNode, PatternSource, compare, flatten_at, materialize},
    },
};

use super::{Backend, BackendError};

#[derive(Debug)]
pub struct BackendMatchTarget {
    pub pattern: Pattern,
    pub generated_anonymous_variables: BTreeSet<Variable>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GeneratedIdentityMappingError {
    Missing {
        identity: KoreVariableIdentity,
    },
    Ambiguous {
        identity: KoreVariableIdentity,
        candidates: BTreeSet<Variable>,
    },
}

impl fmt::Display for GeneratedIdentityMappingError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Missing { identity } => write!(
                formatter,
                "generated {:?} KORE variable {:?} is missing from the internalized match target",
                identity.kind, identity.name
            ),
            Self::Ambiguous {
                identity,
                candidates,
            } => write!(
                formatter,
                "generated {:?} KORE variable {:?} has multiple internalized sorts: {}",
                identity.kind,
                identity.name,
                candidates
                    .iter()
                    .map(|candidate| format!("{:?}", candidate.sort))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}

impl Error for GeneratedIdentityMappingError {}

impl Backend {
    pub fn match_patterns(
        &mut self,
        module: Option<&str>,
        target: &Pattern,
        alternatives: &[Pattern],
    ) -> Result<Vec<PatternMatch>, BackendError> {
        self.with_solver(module, |definition, _| {
            match_disjunction(definition, target, alternatives).map_err(|error| {
                BackendError(format!("KORE pattern match was indeterminate: {error:?}"))
            })
        })
    }
}

pub fn kore_variable_identity(variable: &crate::kore::ast::Variable) -> KoreVariableIdentity {
    KoreVariableIdentity {
        kind: variable.kind,
        name: variable.name.clone(),
    }
}

pub fn collect_predicate_variables(predicate: &Predicate, variables: &mut BTreeSet<Variable>) {
    match predicate {
        Predicate::True | Predicate::False => {}
        Predicate::Term(term) | Predicate::Ceil(term) | Predicate::Floor(term) => {
            variables.extend(term.attributes().variables.iter().cloned());
        }
        Predicate::Equals(left, right) | Predicate::In(left, right) => {
            variables.extend(left.attributes().variables.iter().cloned());
            variables.extend(right.attributes().variables.iter().cloned());
        }
        Predicate::Not(inner) => collect_predicate_variables(inner, variables),
        Predicate::And(inner) | Predicate::Or(inner) => {
            for predicate in inner {
                collect_predicate_variables(predicate, variables);
            }
        }
        Predicate::Implies(left, right) | Predicate::Iff(left, right) => {
            collect_predicate_variables(left, variables);
            collect_predicate_variables(right, variables);
        }
        Predicate::Exists(variable, inner) | Predicate::Forall(variable, inner) => {
            variables.insert(variable.clone());
            collect_predicate_variables(inner, variables);
        }
    }
}

pub fn map_generated_anonymous_variables(
    target: &Pattern,
    identities: &BTreeSet<KoreVariableIdentity>,
) -> Result<BTreeSet<Variable>, GeneratedIdentityMappingError> {
    let mut variables = target.term.attributes().variables.clone();
    for constraint in &target.constraints {
        collect_predicate_variables(constraint, &mut variables);
    }
    let mut mapped = BTreeSet::new();
    for identity in identities {
        let kind = match identity.kind {
            KoreVariableKind::Element => BackendVariableKind::Element,
            KoreVariableKind::Set => BackendVariableKind::Set,
        };
        let candidates = variables
            .iter()
            .filter(|variable| variable.kind == kind && variable.name.as_ref() == identity.name)
            .cloned()
            .collect::<BTreeSet<_>>();
        match candidates.len() {
            0 => {
                return Err(GeneratedIdentityMappingError::Missing {
                    identity: identity.clone(),
                });
            }
            1 => {
                mapped.extend(candidates);
            }
            _ => {
                return Err(GeneratedIdentityMappingError::Ambiguous {
                    identity: identity.clone(),
                    candidates,
                });
            }
        }
    }
    Ok(mapped)
}

pub fn prepare_backend_match_target(
    backend: &BackendDefinition,
    compiled: CompiledSearchPattern,
) -> Result<BackendMatchTarget, Box<dyn Error>> {
    backend.verify_standalone_pattern(&compiled.pattern)?;
    let occurring = compiled
        .pattern
        .variables()
        .iter()
        .map(kore_variable_identity)
        .collect::<BTreeSet<_>>();
    if let Some(identity) = compiled
        .generated_anonymous_variables
        .iter()
        .find(|identity| !occurring.contains(*identity))
    {
        return Err(io::Error::other(format!(
            "generated {:?} KORE variable {:?} does not occur in the compiled match target",
            identity.kind, identity.name
        ))
        .into());
    }
    let pattern = backend.internalize_pattern(&compiled.pattern, &[])?;
    let generated_anonymous_variables =
        map_generated_anonymous_variables(&pattern, &compiled.generated_anonymous_variables)?;
    Ok(BackendMatchTarget {
        pattern,
        generated_anonymous_variables,
    })
}

/// One match to report: its substitution and constraints, and the sort its predicates are written
/// at.
#[derive(Debug)]
pub struct MatchCondition {
    pub substitution: Substitution,
    pub constraints: Vec<Predicate>,
    pub predicate_sort: BackendSort,
}

/// The disjunction of match conditions a search or a pattern match reports, kept as the backend
/// data it is externalized from.
///
/// The printed pattern is the disjunction, at `result_sort`, of one conjunction per match: its
/// bindings (as equalities, by name and then sort) followed by its constraints. That condition
/// is then split into disjuncts at `result_sort`; each disjunct loses the equalities that only
/// bind a generated anonymous variable (see [`MatchOutput::kept_conjuncts`]); and the
/// disjuncts are ordered by the structural order of their KORE and deduplicated.
///
/// Each step reads the externalized pattern through [`External`] sources, one node at a time, so
/// neither the order, the filter, nor printing ([`MatchOutput::with_source`]) holds the KORE
/// tree, which writes out each subterm the backend terms share at each of its uses.
#[derive(Debug)]
pub struct MatchOutput {
    conditions: Vec<MatchCondition>,
    result_sort: KoreSort,
    generated_anonymous_variables: BTreeSet<KoreVariableIdentity>,
    function_symbols: BTreeSet<String>,
}

pub fn search_output(
    result: &PatternSearchResult,
    result_sort: &KoreSort,
    generated_anonymous_variables: &BTreeSet<Variable>,
    function_symbols: &BTreeSet<String>,
) -> MatchOutput {
    MatchOutput::new(
        result
            .matches
            .iter()
            .map(|found| MatchCondition {
                substitution: found.substitution.clone(),
                constraints: found.constraints.clone(),
                predicate_sort: found.state.pattern.term.sort(),
            })
            .collect(),
        result_sort,
        generated_anonymous_variables,
        function_symbols,
    )
}

pub fn pattern_matches_output(
    matches: &[PatternMatch],
    result_sort: &KoreSort,
    predicate_sort: &BackendSort,
    generated_anonymous_variables: &BTreeSet<Variable>,
    function_symbols: &BTreeSet<String>,
) -> MatchOutput {
    MatchOutput::new(
        matches
            .iter()
            .map(|found| MatchCondition {
                substitution: found.substitution.clone(),
                constraints: found.constraints.clone(),
                predicate_sort: predicate_sort.clone(),
            })
            .collect(),
        result_sort,
        generated_anonymous_variables,
        function_symbols,
    )
}

impl MatchOutput {
    pub fn new(
        conditions: Vec<MatchCondition>,
        result_sort: &KoreSort,
        generated_anonymous_variables: &BTreeSet<Variable>,
        function_symbols: &BTreeSet<String>,
    ) -> Self {
        Self {
            conditions,
            result_sort: result_sort.clone(),
            generated_anonymous_variables: generated_kore_identities(generated_anonymous_variables),
            function_symbols: function_symbols.clone(),
        }
    }

    /// The output pattern as a tree.
    pub fn to_pattern(&self) -> KorePattern {
        self.with_source(|source| materialize(source))
    }

    /// Call `consume` with the source of the output pattern.
    pub fn with_source<R>(&self, consume: impl FnOnce(External<'_>) -> R) -> R {
        let result_sort = &self.result_sort;
        let shape = externalize::ConjunctionShape::LeftNested;
        let predicates = self
            .conditions
            .iter()
            .map(|condition| {
                let sort = &condition.predicate_sort;
                externalize::ordered_bindings(
                    &condition.substitution,
                    externalize::BindingOrder::NameThenSort,
                )
                .into_iter()
                .map(|(variable, value)| External::Binding {
                    variable,
                    value,
                    sort,
                })
                .chain(
                    condition
                        .constraints
                        .iter()
                        .map(|predicate| External::Predicate {
                            predicate,
                            sort: ResultSort::Given(sort),
                            preserve_terms: false,
                        }),
                )
                .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let conditions = predicates
            .iter()
            .map(|predicates| {
                externalize::connective_source(result_sort, predicates, shape, true)
                    .unwrap_or(External::Top(result_sort))
            })
            .collect::<Vec<_>>();
        let condition = externalize::connective_source(result_sort, &conditions, shape, false)
            .unwrap_or(External::Bottom(result_sort));
        let kept = flatten_at(condition, result_sort, false)
            .into_iter()
            .map(|disjunct| self.kept_conjuncts(disjunct))
            .collect::<Vec<_>>();
        let mut solutions = kept
            .iter()
            .map(|conjuncts| {
                externalize::connective_source(result_sort, conjuncts, shape, true)
                    .unwrap_or(External::Top(result_sort))
            })
            .collect::<Vec<_>>();
        solutions.sort_by(|left, right| compare(*left, *right));
        solutions.dedup_by(|right, left| compare(*left, *right).is_eq());
        consume(
            externalize::connective_source(result_sort, &solutions, shape, false)
                .unwrap_or(External::Bottom(result_sort)),
        )
    }

    /// The conjuncts at the result sort of `disjunct`, without each equality whose left side is
    /// a variable or an application of a function symbol and whose left-side variables are all
    /// generated anonymous variables that occur exactly once in `disjunct`: such an equality
    /// only names the value a generated variable matched, and nothing else mentions it.
    ///
    /// Variables are identified by kind and externalized name, as the printed pattern shows
    /// them. Occurrences are counted over the whole disjunct, binders included, and only for the
    /// identities that decide the filter; see [`occurrences`].
    fn kept_conjuncts<'t>(&self, disjunct: External<'t>) -> Vec<External<'t>> {
        let conjuncts = flatten_at(disjunct, &self.result_sort, true);
        let mut once = BTreeMap::<KoreVariableIdentity, bool>::new();
        let mut occurs_once = |identity: &KoreVariableIdentity| {
            *once
                .entry(identity.clone())
                .or_insert_with(|| occurrences(&conjuncts, identity) == 1)
        };
        let filtered = conjuncts
            .iter()
            .map(|conjunct| {
                self.generated_equality_variables(*conjunct)
                    .is_some_and(|identities| identities.iter().all(&mut occurs_once))
            })
            .collect::<Vec<_>>();
        conjuncts
            .into_iter()
            .zip(filtered)
            .filter_map(|(conjunct, filtered)| (!filtered).then_some(conjunct))
            .collect()
    }

    /// The variable identities of the left side of `conjunct` when it is an equality whose left
    /// side is a variable or a function application and whose left-side variables are all
    /// generated anonymous variables; `None` otherwise.
    fn generated_equality_variables(
        &self,
        conjunct: External<'_>,
    ) -> Option<BTreeSet<KoreVariableIdentity>> {
        let PatternNode::Equals { left, .. } = conjunct.node() else {
            return None;
        };
        let eligible = match left.node() {
            PatternNode::Variable(_) => true,
            PatternNode::Application { symbol, .. } => self.function_symbols.contains(&symbol.name),
            _ => false,
        };
        if !eligible {
            return None;
        }
        let identities = variable_identities(left);
        identities
            .iter()
            .all(|identity| self.generated_anonymous_variables.contains(identity))
            .then_some(identities)
    }
}

/// The identity of each variable node and binder of `source`. A term whose variable set is empty
/// is not read.
fn variable_identities(source: External<'_>) -> BTreeSet<KoreVariableIdentity> {
    let mut identities = BTreeSet::new();
    let mut work = vec![source];
    // Invariant: `identities` holds the identities of the variable nodes and binders of the expanded sources, and `work` holds the sources not yet read; each source is pushed once, by its parent.
    while let Some(source) = work.pop() {
        if source.term_variables().is_some_and(BTreeSet::is_empty) {
            continue;
        }
        let node = source.node();
        if let Some(variable) = node_variable(&node) {
            identities.insert(kore_variable_identity(variable));
        }
        work.extend(node.split().1);
    }
    identities
}

/// The number of variable nodes and binders of `conjuncts` whose identity is `identity`, counted
/// up to 2.
///
/// A source whose backend variable set (a superset of the variables in its externalized form)
/// has no variable of this identity is not read, and the count stops at 2. So the work is one
/// path from each conjunct to each of at most two occurrences, plus the siblings along those
/// paths, rather than the size of the externalized tree.
fn occurrences(conjuncts: &[External<'_>], identity: &KoreVariableIdentity) -> usize {
    let has_identity = |variable: &Variable| {
        variable_kind(variable) == identity.kind
            && externalize::external_variable_name(&variable.name) == identity.name
    };
    let mut count = 0;
    let mut work = conjuncts.to_vec();
    // Invariant: `count` is the number of variable nodes and binders of the expanded sources with this identity, and `work` holds the unexpanded sources that may contain one; each source is pushed once.
    while let Some(source) = work.pop() {
        if source
            .term_variables()
            .is_some_and(|variables| !variables.iter().any(has_identity))
        {
            continue;
        }
        let node = source.node();
        if node_variable(&node)
            .is_some_and(|variable| kore_variable_identity(variable) == *identity)
        {
            count += 1;
            if count == 2 {
                return count;
            }
        }
        work.extend(node.split().1);
    }
    count
}

/// The variable of a variable node, or the bound variable of a binder.
fn node_variable<'n, S>(node: &'n PatternNode<'_, S>) -> Option<&'n KoreVariable> {
    match node {
        PatternNode::Variable(variable)
        | PatternNode::Exists { variable, .. }
        | PatternNode::Forall { variable, .. }
        | PatternNode::Mu { variable, .. }
        | PatternNode::Nu { variable, .. } => Some(variable),
        _ => None,
    }
}

const fn variable_kind(variable: &Variable) -> KoreVariableKind {
    match variable.kind {
        BackendVariableKind::Element => KoreVariableKind::Element,
        BackendVariableKind::Set => KoreVariableKind::Set,
    }
}

pub fn generated_kore_identities(variables: &BTreeSet<Variable>) -> BTreeSet<KoreVariableIdentity> {
    variables
        .iter()
        .map(|variable| KoreVariableIdentity {
            kind: variable_kind(variable),
            name: externalize::external_variable_name(&variable.name),
        })
        .collect()
}

#[cfg(test)]
mod tests {
    //! [`MatchOutput`] against the tree pipeline it replaced: the functions below are that
    //! pipeline (externalize every match condition, split and filter the tree, sort and
    //! deduplicate the disjunct trees), kept as the reference. The output must be the same
    //! pattern and print the same text.

    use std::sync::Arc;

    use k_rust_backend::term::{FunctionType, Symbol, SymbolType, Term};
    use proptest::prelude::*;

    use super::*;
    use crate::kore::printer::Printer as KorePrinter;

    fn raw_match_condition_output(
        substitution: &Substitution,
        constraints: &[Predicate],
        result_sort: &KoreSort,
        predicate_sort: &BackendSort,
    ) -> KorePattern {
        let predicate_sort_kore = externalize::sort(predicate_sort);
        let mut predicates = externalize::substitution_pattern(
            substitution,
            predicate_sort,
            externalize::BindingOrder::NameThenSort,
            externalize::ConjunctionShape::LeftNested,
        )
        .map(|pattern| pattern.into_conjuncts_at(&predicate_sort_kore))
        .unwrap_or_default();
        predicates.extend(
            constraints
                .iter()
                .map(|predicate| externalize::predicate_pattern(predicate, predicate_sort)),
        );
        externalize::conjunction(
            result_sort,
            predicates,
            externalize::ConjunctionShape::LeftNested,
        )
        .unwrap_or_else(|| KorePattern::Top {
            sort: result_sort.clone(),
        })
    }

    fn is_filterable_generated_equality(
        pattern: &KorePattern,
        generated_anonymous_variables: &BTreeSet<KoreVariableIdentity>,
        function_symbols: &BTreeSet<String>,
        occurrences: &BTreeMap<KoreVariableIdentity, usize>,
    ) -> bool {
        let KorePattern::Equals { left, .. } = pattern else {
            return false;
        };
        let eligible_left = match left.as_ref() {
            KorePattern::Variable(_) => true,
            KorePattern::Application { symbol, .. } => function_symbols.contains(&symbol.name),
            _ => false,
        };
        if !eligible_left {
            return false;
        }
        let left_variables = left
            .variables()
            .iter()
            .map(kore_variable_identity)
            .collect::<BTreeSet<_>>();
        left_variables.iter().all(|identity| {
            generated_anonymous_variables.contains(identity)
                && occurrences.get(identity) == Some(&1)
        })
    }

    fn filter_match_condition(
        condition: KorePattern,
        result_sort: &KoreSort,
        generated_anonymous_variables: &BTreeSet<Variable>,
        function_symbols: &BTreeSet<String>,
    ) -> KorePattern {
        let disjuncts = condition
            .into_disjuncts_at(result_sort)
            .into_iter()
            .map(|condition| {
                filter_match_conjunction(
                    condition,
                    result_sort,
                    generated_anonymous_variables,
                    function_symbols,
                )
            })
            .collect();
        externalize::disjunction(
            result_sort,
            order_distinct_match_outputs(disjuncts),
            externalize::ConjunctionShape::LeftNested,
        )
        .unwrap_or_else(|| KorePattern::Bottom {
            sort: result_sort.clone(),
        })
    }

    fn filter_match_conjunction(
        condition: KorePattern,
        result_sort: &KoreSort,
        generated_anonymous_variables: &BTreeSet<Variable>,
        function_symbols: &BTreeSet<String>,
    ) -> KorePattern {
        let occurrences = condition
            .variable_occurrences()
            .into_iter()
            .map(|((kind, name), count)| (KoreVariableIdentity { kind, name }, count))
            .collect::<BTreeMap<_, _>>();
        let generated_anonymous_variables =
            generated_kore_identities(generated_anonymous_variables);
        let conjuncts = condition
            .into_conjuncts_at(result_sort)
            .into_iter()
            .filter(|pattern| {
                !is_filterable_generated_equality(
                    pattern,
                    &generated_anonymous_variables,
                    function_symbols,
                    &occurrences,
                )
            })
            .collect();
        externalize::conjunction(
            result_sort,
            conjuncts,
            externalize::ConjunctionShape::LeftNested,
        )
        .unwrap_or_else(|| KorePattern::Top {
            sort: result_sort.clone(),
        })
    }

    fn order_distinct_match_outputs(mut solutions: Vec<KorePattern>) -> Vec<KorePattern> {
        solutions.sort();
        solutions.dedup();
        solutions
    }

    fn reference_output(
        conditions: &[MatchCondition],
        result_sort: &KoreSort,
        generated_anonymous_variables: &BTreeSet<Variable>,
        function_symbols: &BTreeSet<String>,
    ) -> KorePattern {
        let solutions = conditions
            .iter()
            .map(|condition| {
                raw_match_condition_output(
                    &condition.substitution,
                    &condition.constraints,
                    result_sort,
                    &condition.predicate_sort,
                )
            })
            .collect::<Vec<_>>();
        filter_match_condition(
            externalize::disjunction(
                result_sort,
                solutions,
                externalize::ConjunctionShape::LeftNested,
            )
            .unwrap_or_else(|| KorePattern::Bottom {
                sort: result_sort.clone(),
            }),
            result_sort,
            generated_anonymous_variables,
            function_symbols,
        )
    }

    const RESULT_SORT: &str = "SortGeneratedTopCell";

    /// Generated and named variables, of the result sort and of `SortBool`, so that one name
    /// occurs at two sorts (one identity); a set variable of a generated name; and two names
    /// that externalize to one identity (`Rule#X` is written `RuleX`).
    fn variable() -> impl Strategy<Value = Variable> {
        prop_oneof![
            Just(Variable::new(
                "Rule#Var'Unds'Gen2",
                BackendSort::simple(RESULT_SORT)
            )),
            Just(Variable::new(
                "RuleVar'Unds'Gen2",
                BackendSort::simple(RESULT_SORT)
            )),
            Just(Variable::new(
                "Var'Unds'Gen0",
                BackendSort::simple(RESULT_SORT)
            )),
            Just(Variable::new(
                "Var'Unds'Gen0",
                BackendSort::simple("SortBool")
            )),
            Just(Variable::new(
                "Var'Unds'Gen1",
                BackendSort::simple(RESULT_SORT)
            )),
            Just(Variable::new("VarX", BackendSort::simple(RESULT_SORT))),
            Just(Variable::set(
                "@Var'Unds'Gen0",
                BackendSort::simple(RESULT_SORT)
            )),
        ]
    }

    fn symbol(name: &str, function: bool) -> Arc<Symbol> {
        let mut symbol = Symbol::constructor(name, Vec::new(), BackendSort::simple(RESULT_SORT));
        if function {
            symbol.attributes.symbol_type = SymbolType::Function(FunctionType::Total);
        }
        Arc::new(symbol)
    }

    fn term() -> impl Strategy<Value = Term> {
        let leaf = prop_oneof![
            variable().prop_map(Term::variable),
            prop_oneof![Just("1"), Just("2")]
                .prop_map(|value| Term::domain_value(BackendSort::simple(RESULT_SORT), value)),
            prop_oneof![Just("true"), Just("false")]
                .prop_map(|value| Term::domain_value(BackendSort::simple("SortBool"), value)),
        ];
        leaf.prop_recursive(3, 16, 3, |inner| {
            (
                prop_oneof![Just(("LblF", true)), Just(("LblC", false))],
                prop::collection::vec(inner, 0..3),
            )
                .prop_map(|((name, function), arguments)| {
                    Term::application(symbol(name, function), Vec::new(), arguments)
                })
        })
    }

    fn predicate() -> impl Strategy<Value = Predicate> {
        let leaf = prop_oneof![
            Just(Predicate::True),
            Just(Predicate::False),
            term().prop_map(Predicate::Term),
            (term(), term()).prop_map(|(left, right)| Predicate::Equals(left, right)),
            term().prop_map(Predicate::Ceil),
        ];
        leaf.prop_recursive(2, 8, 3, |inner| {
            prop_oneof![
                inner
                    .clone()
                    .prop_map(|inner| Predicate::Not(Box::new(inner))),
                prop::collection::vec(inner.clone(), 0..3).prop_map(Predicate::And),
                prop::collection::vec(inner.clone(), 0..3).prop_map(Predicate::Or),
                (variable(), inner)
                    .prop_map(|(variable, inner)| Predicate::Exists(variable, Box::new(inner))),
            ]
        })
    }

    fn condition() -> impl Strategy<Value = MatchCondition> {
        (
            prop::collection::btree_map(variable(), term(), 0..3),
            prop::collection::vec(predicate(), 0..3),
            prop_oneof![
                3 => Just(BackendSort::simple(RESULT_SORT)),
                1 => Just(BackendSort::simple("SortInt")),
            ],
        )
            .prop_map(
                |(substitution, constraints, predicate_sort)| MatchCondition {
                    substitution,
                    constraints,
                    predicate_sort,
                },
            )
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(1024))]

        /// The source pipeline gives the reference pipeline's pattern and text: the same
        /// disjuncts, filtered, ordered, and deduplicated alike.
        #[test]
        fn match_output_equals_the_tree_pipeline(
            conditions in prop::collection::vec(condition(), 0..4),
            duplicate in any::<bool>(),
            generated in prop::collection::btree_set(variable(), 0..4),
            functions in any::<bool>(),
        ) {
            let mut conditions = conditions;
            if duplicate && let Some(first) = conditions.first() {
                let copy = MatchCondition {
                    substitution: first.substitution.clone(),
                    constraints: first.constraints.clone(),
                    predicate_sort: first.predicate_sort.clone(),
                };
                conditions.push(copy);
            }
            let result_sort = externalize::sort(&BackendSort::simple(RESULT_SORT));
            let function_symbols = if functions {
                BTreeSet::from(["LblF".to_owned()])
            } else {
                BTreeSet::new()
            };
            let expected =
                reference_output(&conditions, &result_sort, &generated, &function_symbols);
            let output = MatchOutput::new(conditions, &result_sort, &generated, &function_symbols);
            prop_assert_eq!(&output.to_pattern(), &expected);
            let mut printed = Vec::new();
            output
                .with_source(|source| KorePrinter::pretty(40).write_source(source, &mut printed))
                .unwrap();
            prop_assert_eq!(
                String::from_utf8(printed).unwrap(),
                KorePrinter::pretty(40).print_pattern(&expected)
            );
        }
    }
}
