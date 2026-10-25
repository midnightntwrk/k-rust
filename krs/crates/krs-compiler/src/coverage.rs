//! Coverage of `total` functions: `warning[krs::analysis::uncovered-total-function]`.
//!
//! `total` claims that a function has a value on every argument. The claim is
//! trusted, not proved: where no equation applies, the function still has a
//! value, but the definition does not say which. This lint finds those
//! arguments. It is a statement about under-specification, never about
//! soundness, so it warns.
//!
//! The values of a sort are its ground constructor terms, the values of its
//! subsorts, and the domain values of builtin sorts; they are known only for
//! the assembled definition, because another package may add constructors or
//! subsorts. An equation `f(p̄) => r requires φ` defines `f` on the argument
//! vectors that match `p̄` and make `φ` true. Priorities and `owise` decide
//! which equation applies, never whether one does, so they play no part, and
//! neither do `concrete`/`symbolic`, which restrict how a backend applies an
//! equation, not what it states.
//!
//! The patterns are compared by Maranget's usefulness algorithm over each
//! argument sort's constructors and value families. A guarded equation stays
//! in the matrix with its guard: a region every row of which is guarded is
//! covered exactly when the disjunction of their guards is valid, which
//! [`decide`] checks over a sound abstraction (Boolean structure, comparisons
//! with integer constants, the order of two integers, and opaque atoms). A
//! guard holds where it is defined and true: a partial Int operation in it
//! contributes the condition under which it is defined, so `w > 0 &&
//! x < 1 << (w - 1)` is read, with its shift's `w - 1 >= 0`. An application
//! of a total function is one unknown value ([`GuardReader`]), limited to its
//! equations' results when they cover it ([`Range`]); a `k::matches!` test
//! refines the patterns ([`expand`]). The abstraction only ever admits more
//! valuations than exist, never fewer, and a row never covers more than its
//! equation does, so the lint never calls an uncovered argument covered; it
//! can miss facts (a correlation between a call and its arguments, the
//! range of a result form it does not bound) and then reports a gap that
//! does not exist. Where it reports a condition, every argument that
//! satisfies the condition is uncovered ([`minimize`]).
//!
//! Skipped: `partial` functions (a missing case is what `partial` means),
//! hooked and `smt_hook` functions (the backend or the SMT term defines them),
//! and total functions, or instances of a sort-parametric one, with no
//! equation at all (declared, not defined: uninterpreted). Simplifications are
//! lemmas, not definitions, and are not read; an equation with a function
//! context or a matching-logic `requires` covers nothing.
//!
//! `#[k::function(total, underspecified = "..")]` states a gap on purpose and
//! silences the warning; on a function whose equations cover every argument it
//! is itself stale (`warning[krs::analysis::stale-underspecified]`).

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use krs_diagnostic::{Diagnostic, Location, Severity, codes};
use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, GeneratedOperation, GrammarProductionItemKind,
    GuardMeaning, ItemKind, ListOperation, MapOperation, ProductionAttribute, SemanticId,
    SemanticIdKind, SentenceKind, SetOperation, StableItemId,
};
use krs_ir_levels::{
    IrCondition, SemanticModule, SemanticProduction, SemanticRule, SemanticSortRef as Sort,
    SemanticTerm, SemanticTermKind,
};
use num_bigint::BigInt;

use crate::equation_domain::{
    ColumnValues, Domain, Evaluator, Ground, Undecided, equation_view, evaluable_functions,
};
use crate::int_facts::{IntFact, IntFacts};

/// The pattern-matrix nodes one function may visit before the lint gives up
/// on it (and reports nothing for it).
const NODE_BUDGET: usize = 200_000;
/// The valuations one guard decision may enumerate before giving up.
const VALUATION_BUDGET: u64 = 1 << 20;
/// The valuations the decisions of one function may enumerate in all.
const FUNCTION_VALUATION_BUDGET: u64 = 1 << 23;
/// The or-pattern alternatives one equation may expand to.
const ALTERNATIVE_LIMIT: usize = 64;
/// The uncovered arguments one warning names.
const WITNESS_LIMIT: usize = 3;

/// The coverage lint's subsort judge over `modules`.
#[cfg(feature = "test-support")]
pub(crate) fn subsort_judge(modules: &[SemanticModule]) -> impl Fn(&Sort, &Sort) -> bool + use<> {
    let signature = Signature::new(modules);
    move |candidate, expected| signature.is_subsort(candidate, expected)
}

/// The coverage warnings of a lowered definition's modules, in production order.
#[must_use]
pub fn coverage_warnings(modules: &[SemanticModule]) -> Vec<Diagnostic> {
    let signature = Signature::new(modules);
    let evaluator = Evaluator::with_functions(&signature, evaluable_functions(modules));
    let analysis = Analysis::new(&signature, &evaluator, modules);
    let raw = modules
        .iter()
        .any(|module| !module.raw_sentences().is_empty());
    let mut warnings = Vec::new();
    for production in modules.iter().flat_map(SemanticModule::productions) {
        let Some(outcomes) = analysis.outcomes(production.id()) else {
            continue;
        };
        let stated = production
            .attributes()
            .iter()
            .find(|attribute| matches!(attribute, ProductionAttribute::Underspecified { .. }));
        let mut uncovered = Vec::new();
        let mut decided = true;
        for (instance, outcome) in outcomes.iter() {
            match outcome {
                Outcome::Covered => {}
                Outcome::Uncovered(report) => uncovered.push((instance, report)),
                Outcome::Undecided => decided = false,
            }
        }
        match (stated, uncovered.is_empty()) {
            (Some(attribute), true) if decided => {
                warnings.push(stale_warning(production, attribute));
            }
            (None, false) => {
                for (instance, report) in uncovered {
                    warnings.push(uncovered_warning(production, instance, report, raw));
                }
            }
            _ => {}
        }
    }
    warnings
}

/// A function's verdict on each instance.
type Outcomes = Rc<Vec<(Vec<Sort>, Outcome)>>;

/// The verdicts on a definition's checked functions and the ranges they
/// give. Each function is checked once, when the lint first needs it: in
/// production order, or earlier when a function checked before it applies
/// it in a guard and asks for its range. A function still being checked (a
/// cycle) has no range; that is sound, and the order is deterministic.
struct Analysis<'m> {
    signature: &'m Signature,
    evaluator: &'m Evaluator<'m>,
    productions: BTreeMap<&'m StableItemId, &'m SemanticProduction>,
    equations: BTreeMap<&'m StableItemId, Vec<&'m SemanticRule>>,
    /// `None` while the function is being checked.
    outcomes: RefCell<BTreeMap<&'m StableItemId, Option<Outcomes>>>,
    /// `None` while the range is being inferred, and for no range.
    ranges: RefCell<BTreeMap<&'m StableItemId, Option<Rc<Range>>>>,
    /// Whether the definition has `raw_k!` sentences, which may add
    /// equations the lint does not see.
    raw: bool,
}

impl<'m> Analysis<'m> {
    fn new(
        signature: &'m Signature,
        evaluator: &'m Evaluator<'m>,
        modules: &'m [SemanticModule],
    ) -> Self {
        let mut equations = BTreeMap::<&StableItemId, Vec<&SemanticRule>>::new();
        for rule in modules.iter().flat_map(SemanticModule::rules) {
            if rule.kind() != SentenceKind::Equation {
                continue;
            }
            if let Some(body) = rule.body()
                && let SemanticTermKind::Application {
                    application: ApplicationRef::Declared(head),
                    ..
                } = body.from().kind()
            {
                equations.entry(head).or_default().push(rule);
            }
        }
        Self {
            signature,
            evaluator,
            productions: modules
                .iter()
                .flat_map(SemanticModule::productions)
                .map(|production| (production.id(), production))
                .collect(),
            equations,
            outcomes: RefCell::default(),
            ranges: RefCell::default(),
            raw: modules
                .iter()
                .any(|module| !module.raw_sentences().is_empty()),
        }
    }

    /// The verdicts on a checked function with equations; `None` for
    /// another function, or one still being checked.
    fn outcomes(&self, id: &StableItemId) -> Option<Outcomes> {
        if let Some(known) = self.outcomes.borrow().get(id) {
            return known.clone();
        }
        let (&key, &production) = self.productions.get_key_value(id)?;
        let rules = self.equations.get(id)?;
        if !checked(production) {
            return None;
        }
        self.outcomes.borrow_mut().insert(key, None);
        let outcomes = Rc::new(
            instances(rules)
                .into_iter()
                .map(|(instance, rules)| {
                    let outcome = check_instance(
                        self.signature,
                        self.evaluator,
                        production,
                        &instance,
                        &rules,
                        self,
                    );
                    (instance, outcome)
                })
                .collect::<Vec<_>>(),
        );
        self.outcomes
            .borrow_mut()
            .insert(key, Some(Rc::clone(&outcomes)));
        Some(outcomes)
    }

    /// See [`Range`].
    fn infer(&self, production: &SemanticProduction) -> Option<Rc<Range>> {
        let stated = production
            .attributes()
            .iter()
            .any(|attribute| matches!(attribute, ProductionAttribute::Underspecified { .. }));
        // A `raw_k!` equation could return another value, at a priority
        // that wins.
        if stated || self.raw || !production.parameters().is_empty() {
            return None;
        }
        let outcomes = self.outcomes(production.id())?;
        if !outcomes
            .iter()
            .all(|(_, outcome)| matches!(outcome, Outcome::Covered))
        {
            return None;
        }
        let mut range: Option<Range> = None;
        for rule in self.equations.get(production.id())? {
            let result = result_range(self.signature, self, rule.body()?.to())?;
            range = Some(match range {
                None => result,
                Some(range) => range.union(result)?,
            });
        }
        range.map(Rc::new)
    }
}

impl RangeOf for Analysis<'_> {
    fn range_of(&self, id: &StableItemId) -> Option<Rc<Range>> {
        if let Some(known) = self.ranges.borrow().get(id) {
            return known.clone();
        }
        let (&key, &production) = self.productions.get_key_value(id)?;
        self.ranges.borrow_mut().insert(key, None);
        let range = self.infer(production);
        self.ranges.borrow_mut().insert(key, range.clone());
        range
    }
}

/// Whether the lint judges a production: a total function the backend or
/// the SMT solver does not define.
pub(crate) fn checked(production: &SemanticProduction) -> bool {
    let has = |test: fn(&ProductionAttribute<Sort, StableItemId>) -> bool| {
        production.attributes().iter().any(test)
    };
    has(|attribute| matches!(attribute, ProductionAttribute::Function { .. }))
        && has(|attribute| matches!(attribute, ProductionAttribute::Total { .. }))
        && !has(|attribute| {
            matches!(
                attribute,
                ProductionAttribute::Hook { .. }
                    | ProductionAttribute::RawHook { .. }
                    | ProductionAttribute::SmtHook { .. }
            )
        })
}

/// A function's equations grouped by the instance their head names; a
/// non-parametric function has the one empty instance.
fn instances<'a>(rules: &[&'a SemanticRule]) -> BTreeMap<Vec<Sort>, Vec<&'a SemanticRule>> {
    let mut grouped = BTreeMap::<Vec<Sort>, Vec<&SemanticRule>>::new();
    for rule in rules {
        let instance = match rule.body().map(|body| body.from().kind()) {
            Some(SemanticTermKind::Application { instance, .. }) => instance.clone(),
            _ => Vec::new(),
        };
        grouped.entry(instance).or_default().push(rule);
    }
    grouped
}

// ---------------------------------------------------------------------------
// Sorts and their values

/// The constructors and value families of every sort of the definition.
#[derive(Default)]
pub(crate) struct Signature {
    /// Every constructor, parametric ones included.
    constructors: BTreeMap<StableItemId, ConstructorInfo>,
    /// The total functions, whose applications always have a value.
    total_functions: BTreeSet<StableItemId>,
    sorts: BTreeSet<Sort>,
    /// Every sort above each sort, the sort included.
    ancestors: BTreeMap<Sort, BTreeSet<Sort>>,
    /// Non-parametric constructors by their result sort.
    by_sort: BTreeMap<Sort, Vec<StableItemId>>,
    /// Constructors of one sort parameter, which build a value of every
    /// declared sort they are instantiated at.
    parametric: Vec<StableItemId>,
    /// Whether some parametric constructor has several parameters; every
    /// declared sort is then treated as open.
    wide_parametric: bool,
    token_sorts: BTreeSet<Sort>,
}

/// What the lint needs of one constructor.
#[derive(Clone, Debug)]
struct ConstructorInfo {
    result: Sort,
    parameters: Vec<krs_ir_levels::SortParameterId>,
    arguments: Vec<Sort>,
}

/// One kind of value of a sort: a constructor at an instance, or the values
/// of a sort whose values are not constructor terms (a family).
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Head {
    Constructor {
        id: StableItemId,
        instance: Vec<Sort>,
    },
    Family(Sort),
}

pub(crate) fn production_argument_sorts(production: &SemanticProduction) -> Vec<Sort> {
    production
        .items()
        .iter()
        .filter_map(|item| match item.kind() {
            GrammarProductionItemKind::NonTerminal { sort, .. } => Some(sort.clone()),
            GrammarProductionItemKind::Terminal { .. }
            | GrammarProductionItemKind::RegexTerminal { .. } => None,
        })
        .collect()
}

/// Whether a production builds values: a constructor that is not a
/// function, hook, alias, desugar, bracket, or token.
fn is_constructor(production: &SemanticProduction) -> bool {
    production.id().item_kind() == ItemKind::Constructor
        && !production.attributes().iter().any(|attribute| {
            matches!(
                attribute,
                ProductionAttribute::Function { .. }
                    | ProductionAttribute::Hook { .. }
                    | ProductionAttribute::RawHook { .. }
                    | ProductionAttribute::Alias { .. }
                    | ProductionAttribute::Desugar { .. }
                    | ProductionAttribute::Bracket { .. }
                    | ProductionAttribute::Token { .. }
            )
        })
}

/// Substitutes an instance for the sort parameters in `sorts`.
pub(crate) fn instantiate(
    sorts: &[Sort],
    parameters: &[krs_ir_levels::SortParameterId],
    instance: &[Sort],
) -> Vec<Sort> {
    sorts
        .iter()
        .map(|sort| match sort {
            Sort::Parameter(parameter) => parameters
                .iter()
                .position(|declared| declared == parameter)
                .and_then(|index| instance.get(index).cloned())
                .unwrap_or_else(|| sort.clone()),
            _ => sort.clone(),
        })
        .collect()
}

impl Signature {
    fn new(modules: &[SemanticModule]) -> Self {
        let mut signature = Self {
            sorts: BuiltinSort::ALL.into_iter().map(Sort::Builtin).collect(),
            ..Self::default()
        };
        let mut parents = BTreeMap::<Sort, BTreeSet<Sort>>::new();
        for module in modules {
            signature.sorts.extend(
                module
                    .sorts()
                    .iter()
                    .map(|sort| Sort::Declared(sort.id().clone())),
            );
            for edge in module.subsorts() {
                parents
                    .entry(edge.subsort().clone())
                    .or_default()
                    .insert(edge.supersort().clone());
            }
            for production in module.productions() {
                let has = |test: fn(&ProductionAttribute<Sort, StableItemId>) -> bool| {
                    production.attributes().iter().any(test)
                };
                if has(|attribute| matches!(attribute, ProductionAttribute::Token { .. })) {
                    signature
                        .token_sorts
                        .insert(production.result_sort().clone());
                }
                if has(|attribute| matches!(attribute, ProductionAttribute::Total { .. })) {
                    signature.total_functions.insert(production.id().clone());
                }
                if is_constructor(production) {
                    signature.add_constructor(
                        production.id().clone(),
                        ConstructorInfo {
                            result: production.result_sort().clone(),
                            parameters: production.parameters().to_vec(),
                            arguments: production_argument_sorts(production),
                        },
                    );
                }
            }
        }
        signature.close(&parents);
        signature
    }

    fn add_constructor(&mut self, id: StableItemId, info: ConstructorInfo) {
        if matches!(info.result, Sort::Parameter(_)) {
            self.wide_parametric |= info.parameters.len() != 1;
            self.parametric.push(id.clone());
        } else {
            self.sorts.insert(info.result.clone());
            self.by_sort
                .entry(info.result.clone())
                .or_default()
                .push(id.clone());
        }
        self.constructors.insert(id, info);
    }

    /// Records the subsort edges `parents` and closes them transitively.
    fn close(&mut self, parents: &BTreeMap<Sort, BTreeSet<Sort>>) {
        for (sort, above) in parents {
            self.sorts.insert(sort.clone());
            self.sorts.extend(above.iter().cloned());
        }
        for sort in &self.sorts {
            let mut seen = BTreeSet::new();
            let mut pending = vec![sort.clone()];
            while let Some(next) = pending.pop() {
                if seen.insert(next.clone())
                    && let Some(above) = parents.get(&next)
                {
                    pending.extend(above.iter().cloned());
                }
            }
            self.ancestors.insert(sort.clone(), seen);
        }
    }

    fn is_subsort(&self, sort: &Sort, of: &Sort) -> bool {
        sort == of
            || self
                .ancestors
                .get(sort)
                .is_some_and(|above| above.contains(of))
    }

    /// Whether a sort has values that are not constructor terms of this
    /// definition: builtin domains other than Bool, token sorts, `KItem`
    /// (every sort injects into it), cells, and declared sorts that no
    /// constructor builds (the lint does not assume such a sort is empty).
    fn is_open(&self, sort: &Sort) -> bool {
        match sort {
            Sort::Builtin(BuiltinSort::Bool) => false,
            Sort::Builtin(_) | Sort::Cell(_) | Sort::Parameter(_) => true,
            Sort::Declared(id) => {
                let built = self.sorts.iter().any(|below| {
                    self.is_subsort(below, sort)
                        && (self.by_sort.contains_key(below)
                            || matches!(below, Sort::Builtin(_))
                            || self.token_sorts.contains(below))
                });
                self.token_sorts.contains(sort)
                    || self.wide_parametric
                    || (id.package().k_namespace() == "KRS-FRAMEWORK" && id.item_name() == "KItem")
                    || (!built && self.parametric.is_empty())
            }
        }
    }

    /// Every kind of value of `sort`.
    fn heads(&self, sort: &Sort) -> Vec<Head> {
        let mut heads = Vec::new();
        for below in &self.sorts {
            if !self.is_subsort(below, sort) {
                continue;
            }
            if self.is_open(below) || matches!(below, Sort::Builtin(BuiltinSort::Bool)) {
                heads.push(Head::Family(below.clone()));
            }
            if let Some(constructors) = self.by_sort.get(below) {
                heads.extend(constructors.iter().map(|id| Head::Constructor {
                    id: id.clone(),
                    instance: Vec::new(),
                }));
            }
            if matches!(below, Sort::Declared(_)) && !self.token_sorts.contains(below) {
                heads.extend(self.parametric.iter().map(|id| Head::Constructor {
                    id: id.clone(),
                    instance: vec![below.clone()],
                }));
            }
        }
        if !self.sorts.contains(sort) {
            heads.push(Head::Family(sort.clone()));
        }
        heads
    }

    /// A constructor's argument sorts at an instance.
    fn arguments(&self, id: &StableItemId, instance: &[Sort]) -> Vec<Sort> {
        let info = &self.constructors[id];
        instantiate(&info.arguments, &info.parameters, instance)
    }

    /// The sort a head's values have.
    fn head_sort(&self, head: &Head) -> Sort {
        match head {
            Head::Family(sort) => sort.clone(),
            Head::Constructor { id, instance } => {
                let info = &self.constructors[id];
                instantiate(
                    std::slice::from_ref(&info.result),
                    &info.parameters,
                    instance,
                )
                .remove(0)
            }
        }
    }

    /// Whether a binder of sort `binder` matches every value of `head`.
    fn binder_covers(&self, binder: &Sort, head: &Head) -> bool {
        self.is_subsort(&self.head_sort(head), binder)
    }

    /// Whether a production is a constructor: its applications are values.
    pub(crate) fn is_constructor(&self, id: &StableItemId) -> bool {
        self.constructors.contains_key(id)
    }

    /// Whether a value is in a sort, `None` when the signature cannot tell:
    /// the value's own sort is below it, every value is a `KItem`, and a
    /// declared sort of the definition or a builtin domain contains no
    /// value whose sort the signature does not place below it. Other
    /// framework sorts and cells are not judged.
    pub(crate) fn value_in_sort(&self, value: &Ground, sort: &Sort) -> Option<bool> {
        let own = match value {
            Ground::Int(_) => Sort::Builtin(BuiltinSort::Int),
            Ground::Bool(_) => Sort::Builtin(BuiltinSort::Bool),
            Ground::Term { id, instance, .. } => {
                if !self.constructors.contains_key(id) {
                    return None;
                }
                self.head_sort(&Head::Constructor {
                    id: id.clone(),
                    instance: instance.clone(),
                })
            }
            Ground::Undefined => return None,
        };
        if self.is_subsort(&own, sort) {
            return Some(true);
        }
        match sort {
            Sort::Declared(id) if id.package().k_namespace() == "KRS-FRAMEWORK" => {
                (id.item_name() == "KItem").then_some(true)
            }
            Sort::Declared(_) | Sort::Builtin(BuiltinSort::Int | BuiltinSort::Bool) => Some(false),
            _ => None,
        }
    }
}

/// How a production is named in a message: `Enum::Variant` or the struct.
pub(crate) fn display_name(id: &StableItemId) -> String {
    match id
        .disambiguator()
        .strip_prefix(krs_ir::ENUM_VARIANT_DISAMBIGUATOR_PREFIX)
    {
        Some(family) => format!("{family}::{}", id.item_name()),
        None => id.item_name().to_owned(),
    }
}

fn sort_name(sort: &Sort) -> String {
    match sort {
        Sort::Builtin(builtin) => builtin.k_name().to_owned(),
        Sort::Declared(id) | Sort::Cell(id) => id.item_name().to_owned(),
        Sort::Parameter(parameter) => parameter.as_str().to_owned(),
    }
}

// ---------------------------------------------------------------------------
// Patterns

/// A path from a function's argument list to a subterm: the argument index,
/// then the argument index in each constructor below it.
type Path = Vec<usize>;

#[derive(Clone, Debug)]
enum Pattern {
    Binder(Sort),
    Constructor {
        id: StableItemId,
        instance: Vec<Sort>,
        arguments: Vec<Pattern>,
    },
    Literal {
        sort: Sort,
        value: String,
    },
    /// The values of one family head ([`Head::Family`]) and nothing else:
    /// a binder of the family's sort would also match the constructors of
    /// its subsorts. Only a complement ([`complement`]) builds one.
    Family(Sort),
    /// A pattern the lint does not decompose (a collection, a function
    /// application, a non-linear binder); it may match nothing.
    Opaque,
}

/// The paths a pattern's binders bind, relative to the pattern.
type Bindings = Vec<(SemanticId, Path)>;

/// One alternative of a pattern with its bindings.
type Alternative = (Pattern, Bindings);

/// The alternatives of an argument list: one pattern per argument for each
/// choice of an alternative in every argument, binders with their paths
/// from the list; `None` past [`ALTERNATIVE_LIMIT`].
fn argument_alternatives(
    signature: &Signature,
    arguments: &[SemanticTerm],
) -> Option<Vec<(Vec<Pattern>, Bindings)>> {
    let mut combined = vec![(Vec::new(), Bindings::new())];
    for (index, argument) in arguments.iter().enumerate() {
        let choices = alternatives(signature, argument);
        if combined.len() * choices.len() > ALTERNATIVE_LIMIT {
            return None;
        }
        combined = combined
            .into_iter()
            .flat_map(|(patterns, bindings)| {
                choices.iter().map(move |(pattern, inner)| {
                    let mut patterns: Vec<Pattern> = patterns.clone();
                    patterns.push(pattern.clone());
                    let mut bindings: Bindings = bindings.clone();
                    bindings.extend(inner.iter().map(|(binder, path)| {
                        let mut full = vec![index];
                        full.extend(path);
                        (binder.clone(), full)
                    }));
                    (patterns, bindings)
                })
            })
            .collect();
    }
    Some(combined)
}

fn literal_value(sort: &Sort, value: &str) -> String {
    if matches!(sort, Sort::Builtin(BuiltinSort::Int))
        && let Ok(number) = value.parse::<BigInt>()
    {
        return number.to_string();
    }
    value.to_owned()
}

/// The alternatives of an equation argument (or-patterns multiply).
fn alternatives(signature: &Signature, term: &SemanticTerm) -> Vec<Alternative> {
    match term.kind() {
        SemanticTermKind::Variable { variable } => {
            vec![(
                Pattern::Binder(term.sort().clone()),
                vec![(variable.clone(), Vec::new())],
            )]
        }
        SemanticTermKind::Token { value } => vec![(
            Pattern::Literal {
                sort: term.sort().clone(),
                value: literal_value(term.sort(), value),
            },
            Vec::new(),
        )],
        SemanticTermKind::Application {
            application: ApplicationRef::Declared(id),
            arguments,
            instance,
            ..
        } if signature.constructors.contains_key(id) => {
            let Some(combined) = argument_alternatives(signature, arguments) else {
                return vec![(Pattern::Opaque, Vec::new())];
            };
            combined
                .into_iter()
                .map(|(arguments, bindings)| {
                    (
                        Pattern::Constructor {
                            id: id.clone(),
                            instance: instance.clone(),
                            arguments,
                        },
                        bindings,
                    )
                })
                .collect()
        }
        SemanticTermKind::As { alias, pattern } => alternatives(signature, pattern)
            .into_iter()
            .map(|(pattern, mut bindings)| {
                bindings.push((alias.clone(), Vec::new()));
                (pattern, bindings)
            })
            .collect(),
        SemanticTermKind::Or {
            alternatives: choices,
        } => {
            let all = choices
                .iter()
                .flat_map(|choice| alternatives(signature, choice))
                .collect::<Vec<_>>();
            if all.len() > ALTERNATIVE_LIMIT {
                vec![(Pattern::Opaque, Vec::new())]
            } else {
                all
            }
        }
        _ => vec![(Pattern::Opaque, Vec::new())],
    }
}

/// Whether a pattern is decomposed all the way down: it has no opaque part.
fn decomposed(pattern: &Pattern) -> bool {
    match pattern {
        Pattern::Opaque => false,
        Pattern::Constructor { arguments, .. } => arguments.iter().all(decomposed),
        Pattern::Binder(_) | Pattern::Literal { .. } | Pattern::Family(_) => true,
    }
}

/// The canonical text and the rendering of a `k::matches!` pattern. Its
/// local binders bind only inside the test (BIND-1), so they are numbered by
/// first occurrence, which keeps what matters, where one repeats; each
/// wildcard is a binder of its own. `None` for a form the lint does not
/// render.
fn matches_pattern(
    term: &SemanticTerm,
    binders: &mut BTreeMap<SemanticId, usize>,
) -> Option<(String, String)> {
    let number = |binders: &mut BTreeMap<SemanticId, usize>, variable: &SemanticId| {
        let next = binders.len();
        if matches!(variable.kind(), SemanticIdKind::Wildcard) {
            binders.insert(variable.clone(), next);
            next
        } else {
            *binders.entry(variable.clone()).or_insert(next)
        }
    };
    match term.kind() {
        SemanticTermKind::Variable { variable } => {
            let index = number(binders, variable);
            Some((format!("_{index}:{:?}", term.sort()), binder_text(variable)))
        }
        SemanticTermKind::Token { value } => {
            Some((format!("{:?}:{value}", term.sort()), value.clone()))
        }
        SemanticTermKind::Application {
            application: ApplicationRef::Declared(id),
            arguments,
            instance,
            ..
        } => {
            let mut keys = Vec::new();
            let mut texts = Vec::new();
            for argument in arguments {
                let (key, text) = matches_pattern(argument, binders)?;
                keys.push(key);
                texts.push(text);
            }
            let text = if arguments.is_empty() {
                display_name(id)
            } else {
                format!("{}({})", display_name(id), texts.join(", "))
            };
            Some((format!("{id:?}{instance:?}({})", keys.join(", ")), text))
        }
        SemanticTermKind::As { alias, pattern } => {
            let (key, text) = matches_pattern(pattern, binders)?;
            let index = number(binders, alias);
            Some((
                format!("{key}@_{index}"),
                format!("{} @ {text}", binder_text(alias)),
            ))
        }
        SemanticTermKind::Or { alternatives } => {
            let mut keys = Vec::new();
            let mut texts = Vec::new();
            for alternative in alternatives {
                let (key, text) = matches_pattern(alternative, binders)?;
                keys.push(key);
                texts.push(text);
            }
            Some((format!("or({})", keys.join(" | ")), texts.join(" | ")))
        }
        _ => None,
    }
}

/// The pattern that matches exactly the values of one head: a constructor
/// over binders of its argument sorts, or a family.
fn head_pattern(signature: &Signature, head: &Head) -> Pattern {
    match head {
        Head::Constructor { id, instance } => Pattern::Constructor {
            id: id.clone(),
            instance: instance.clone(),
            arguments: signature
                .arguments(id, instance)
                .into_iter()
                .map(Pattern::Binder)
                .collect(),
        },
        Head::Family(sort) => Pattern::Family(sort.clone()),
    }
}

/// The subpattern at `path` of an argument list.
fn pattern_at<'p>(patterns: &'p [Pattern], path: &[usize]) -> Option<&'p Pattern> {
    let (first, rest) = path.split_first()?;
    let mut pattern = patterns.get(*first)?;
    for index in rest {
        let Pattern::Constructor { arguments, .. } = pattern else {
            return None;
        };
        pattern = arguments.get(*index)?;
    }
    Some(pattern)
}

/// `patterns` with the subpattern at `path` replaced.
fn replace_at(patterns: &[Pattern], path: &[usize], replacement: Pattern) -> Option<Vec<Pattern>> {
    fn replace(pattern: &mut Pattern, path: &[usize], replacement: Pattern) -> Option<()> {
        let Some((first, rest)) = path.split_first() else {
            *pattern = replacement;
            return Some(());
        };
        let Pattern::Constructor { arguments, .. } = pattern else {
            return None;
        };
        replace(arguments.get_mut(*first)?, rest, replacement)
    }
    let mut patterns = patterns.to_vec();
    let (first, rest) = path.split_first()?;
    replace(patterns.get_mut(*first)?, rest, replacement)?;
    Some(patterns)
}

/// Patterns whose union matches exactly what both `left` and `right`
/// match, over the lint's heads; `None` when one of them is opaque or the
/// union would exceed [`ALTERNATIVE_LIMIT`].
#[expect(
    clippy::too_many_lines,
    reason = "One case per pair of pattern kinds, as in unification."
)]
fn meet(signature: &Signature, left: &Pattern, right: &Pattern) -> Option<Vec<Pattern>> {
    let covers = |sort: &Sort, head: &Head| signature.binder_covers(sort, head);
    Some(match (left, right) {
        (Pattern::Opaque, _) | (_, Pattern::Opaque) => return None,
        (Pattern::Binder(first), Pattern::Binder(second)) => {
            if signature.is_subsort(first, second) {
                vec![left.clone()]
            } else if signature.is_subsort(second, first) {
                vec![right.clone()]
            } else {
                // The heads below `first` that `second` also covers.
                signature
                    .heads(first)
                    .iter()
                    .filter(|head| covers(second, head))
                    .map(|head| head_pattern(signature, head))
                    .collect()
            }
        }
        (Pattern::Binder(sort), other @ Pattern::Constructor { id, instance, .. })
        | (other @ Pattern::Constructor { id, instance, .. }, Pattern::Binder(sort)) => {
            let head = Head::Constructor {
                id: id.clone(),
                instance: instance.clone(),
            };
            if covers(sort, &head) {
                vec![other.clone()]
            } else {
                Vec::new()
            }
        }
        (
            Pattern::Binder(binder),
            other @ (Pattern::Literal { sort, .. } | Pattern::Family(sort)),
        )
        | (
            other @ (Pattern::Literal { sort, .. } | Pattern::Family(sort)),
            Pattern::Binder(binder),
        ) => {
            if covers(binder, &Head::Family(sort.clone())) {
                vec![other.clone()]
            } else {
                Vec::new()
            }
        }
        (
            Pattern::Family(family),
            other @ (Pattern::Literal { sort, .. } | Pattern::Family(sort)),
        )
        | (other @ Pattern::Literal { sort, .. }, Pattern::Family(family)) => {
            if family == sort {
                vec![other.clone()]
            } else {
                Vec::new()
            }
        }
        (
            Pattern::Literal { sort, value },
            Pattern::Literal {
                sort: other,
                value: other_value,
            },
        ) => {
            if sort == other && value == other_value {
                vec![left.clone()]
            } else {
                Vec::new()
            }
        }
        (
            Pattern::Constructor {
                id,
                instance,
                arguments,
            },
            Pattern::Constructor {
                id: other,
                instance: other_instance,
                arguments: other_arguments,
            },
        ) => {
            if id != other || instance != other_instance {
                return Some(Vec::new());
            }
            let mut combined = vec![Vec::new()];
            for (first, second) in arguments.iter().zip(other_arguments) {
                let met = meet(signature, first, second)?;
                if combined.len() * met.len() > ALTERNATIVE_LIMIT {
                    return None;
                }
                combined = combined
                    .into_iter()
                    .flat_map(|prefix: Vec<Pattern>| {
                        met.iter().map(move |argument| {
                            let mut arguments = prefix.clone();
                            arguments.push(argument.clone());
                            arguments
                        })
                    })
                    .collect();
            }
            combined
                .into_iter()
                .map(|arguments| Pattern::Constructor {
                    id: id.clone(),
                    instance: instance.clone(),
                    arguments,
                })
                .collect()
        }
        (Pattern::Constructor { .. }, Pattern::Literal { .. } | Pattern::Family(_))
        | (Pattern::Literal { .. } | Pattern::Family(_), Pattern::Constructor { .. }) => Vec::new(),
    })
}

/// A pattern with the residual conditions it needs: `n` complemented in Int
/// is every Int at that path but `n`.
type Refined = (Pattern, Vec<Formula>);

/// Patterns whose union matches exactly the values of `sort` that `pattern`
/// does not, at `path`; `None` where that cannot be stated exactly (an
/// opaque pattern, a literal of a sort other than Int and Bool) or past
/// [`ALTERNATIVE_LIMIT`].
///
/// Each head is stated exactly, a family by [`Pattern::Family`]: a binder
/// of the family's sort would also match the constructors of its
/// subsorts, and a row with it would cover more than its equation does.
fn complement(
    signature: &Signature,
    pattern: &Pattern,
    sort: &Sort,
    path: &[usize],
) -> Option<Vec<Refined>> {
    let heads = signature.heads(sort);
    // Every head of `sort` but `except`.
    let others = |except: Option<&Head>| -> Vec<Refined> {
        heads
            .iter()
            .filter(|head| Some(*head) != except)
            .map(|head| (head_pattern(signature, head), Vec::new()))
            .collect()
    };
    let refined = match pattern {
        Pattern::Opaque => return None,
        Pattern::Binder(binder) => heads
            .iter()
            .filter(|head| !signature.binder_covers(binder, head))
            .map(|head| (head_pattern(signature, head), Vec::new()))
            .collect(),
        Pattern::Family(family) => others(Some(&Head::Family(family.clone()))),
        Pattern::Constructor {
            id,
            instance,
            arguments,
        } => {
            let head = Head::Constructor {
                id: id.clone(),
                instance: instance.clone(),
            };
            if !heads.contains(&head) {
                return Some(others(None));
            }
            let mut refined = others(Some(&head));
            let sorts = signature.arguments(id, instance);
            for (index, (argument, argument_sort)) in arguments.iter().zip(&sorts).enumerate() {
                let mut inner = path.to_vec();
                inner.push(index);
                for (choice, residual) in complement(signature, argument, argument_sort, &inner)? {
                    let arguments = sorts
                        .iter()
                        .enumerate()
                        .map(|(position, sort)| {
                            if position == index {
                                choice.clone()
                            } else {
                                Pattern::Binder(sort.clone())
                            }
                        })
                        .collect();
                    refined.push((
                        Pattern::Constructor {
                            id: id.clone(),
                            instance: instance.clone(),
                            arguments,
                        },
                        residual,
                    ));
                }
            }
            refined
        }
        Pattern::Literal {
            sort: family,
            value,
        } => {
            let head = Head::Family(family.clone());
            if !heads.contains(&head) {
                return Some(others(None));
            }
            let mut refined = others(Some(&head));
            match family {
                Sort::Builtin(BuiltinSort::Bool) => refined.push((
                    Pattern::Literal {
                        sort: family.clone(),
                        value: (value != "true").to_string(),
                    },
                    Vec::new(),
                )),
                Sort::Builtin(BuiltinSort::Int) => refined.push((
                    Pattern::Family(family.clone()),
                    vec![
                        Formula::Atom(Atom::Bound {
                            subject: path_text(path),
                            bound: Bound::At,
                            constant: value.parse().ok()?,
                        })
                        .not(),
                    ],
                )),
                _ => return None,
            }
            refined
        }
    };
    (refined.len() <= ALTERNATIVE_LIMIT).then_some(refined)
}

/// The complement of a union of alternatives: the intersection of their
/// complements.
fn complement_all(
    signature: &Signature,
    alternatives: &[Pattern],
    sort: &Sort,
    path: &[usize],
) -> Option<Vec<Refined>> {
    let mut refined = vec![(Pattern::Binder(sort.clone()), Vec::new())];
    for alternative in alternatives {
        let complement = complement(signature, alternative, sort, path)?;
        let mut next = Vec::new();
        for (left, left_residual) in &refined {
            for (right, right_residual) in &complement {
                for met in meet(signature, left, right)? {
                    let mut residual = left_residual.clone();
                    residual.extend(right_residual.iter().cloned());
                    next.push((met, residual));
                }
            }
        }
        if next.len() > ALTERNATIVE_LIMIT {
            return None;
        }
        refined = next;
    }
    Some(refined)
}

// ---------------------------------------------------------------------------
// Guards

/// A comparison of an Int subject with a constant.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum Bound {
    /// `subject < constant`.
    Below,
    /// `subject == constant`.
    At,
    /// `constant < subject`.
    Above,
}

/// The order of two Int subjects.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum Order {
    Less,
    Equal,
    Greater,
}

/// An atomic proposition of a guard. Subjects are canonical terms, with
/// binders named by their path, so two equations share an atom exactly when
/// they test the same term.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum Atom {
    /// A Bool term the lint does not analyse further.
    Opaque(String),
    /// `subject < c`, `subject == c`, or `c < subject`.
    Bound {
        subject: String,
        bound: Bound,
        constant: BigInt,
    },
    /// The order of two subjects, `left` < `right` in canonical text order.
    Order {
        left: String,
        right: String,
        order: Order,
    },
}

/// A guard over atoms.
#[derive(Clone, Debug)]
pub(crate) enum Formula {
    Atom(Atom),
    Not(Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Constant(bool),
}

impl Formula {
    fn not(self) -> Self {
        Self::Not(Box::new(self))
    }

    fn and(self, other: Self) -> Self {
        Self::And(Box::new(self), Box::new(other))
    }

    /// The formula with the opaque atoms `truths` names replaced by their
    /// truth values.
    fn assign(&self, truths: &BTreeMap<&String, bool>) -> Self {
        match self {
            Self::Atom(Atom::Opaque(key)) => match truths.get(key) {
                Some(truth) => Self::Constant(*truth),
                None => self.clone(),
            },
            Self::Atom(_) | Self::Constant(_) => self.clone(),
            Self::Not(inner) => inner.assign(truths).not(),
            Self::And(left, right) => left.assign(truths).and(right.assign(truths)),
            Self::Or(left, right) => Self::Or(
                Box::new(left.assign(truths)),
                Box::new(right.assign(truths)),
            ),
        }
    }

    /// The formula with its constants folded away, or a constant.
    fn simplify(self) -> Self {
        match self {
            Self::Not(inner) => match inner.simplify() {
                Self::Constant(value) => Self::Constant(!value),
                inner => inner.not(),
            },
            Self::And(left, right) => match (left.simplify(), right.simplify()) {
                (Self::Constant(false), _) | (_, Self::Constant(false)) => Self::Constant(false),
                (Self::Constant(true), other) | (other, Self::Constant(true)) => other,
                (left, right) => left.and(right),
            },
            Self::Or(left, right) => match (left.simplify(), right.simplify()) {
                (Self::Constant(true), _) | (_, Self::Constant(true)) => Self::Constant(true),
                (Self::Constant(false), other) | (other, Self::Constant(false)) => other,
                (left, right) => Self::Or(Box::new(left), Box::new(right)),
            },
            other => other,
        }
    }

    fn atoms<'f>(&'f self, out: &mut BTreeSet<&'f Atom>) {
        match self {
            Self::Atom(atom) => {
                out.insert(atom);
            }
            Self::Not(inner) => inner.atoms(out),
            Self::And(left, right) | Self::Or(left, right) => {
                left.atoms(out);
                right.atoms(out);
            }
            Self::Constant(_) => {}
        }
    }
}

/// The subject-text renderings of one equation, keyed by canonical text.
type Names = BTreeMap<String, String>;

/// Reads one equation's guard. `paths` gives each pattern binder's path.
/// `None` when the guard mentions a term that may be undefined other than by
/// a partial Int operation outside its domain, or a binder the pattern does
/// not bind: such an equation covers nothing the lint can see.
///
/// A guard holds where it is defined and true. Each partial Int operation
/// it applies (division, remainder, shift, exponent, bit range) contributes
/// its domain as an obligation, a formula over the same atoms, and
/// [`GuardReader::guard`] conjoins the obligations with the guard's value.
///
/// An application of a total function is one unknown value of its result
/// sort, the same in every equation where its canonical text is the same
/// (same function and instance, arguments equal once binders are named by
/// their paths), and unrelated to every other subject, its own arguments
/// included. With `ranges`, the unknown lies among the values the
/// function's own equations return ([`Range`]).
///
/// `P :=K t` (`k::matches!`) is an opaque Bool atom keyed by the pattern
/// and `t`: `:=K` is defined wherever `t` is, so the atom over-approximates
/// as any opaque call does. Where `P` is linear and decomposable and `t` is
/// a pattern binder or a term of a declared sort, the reader also records
/// the test ([`Test`]), and [`expand`] reads it as pattern matching.
struct GuardReader<'r> {
    signature: &'r Signature,
    paths: &'r BTreeMap<SemanticId, Path>,
    names: Names,
    projections: Projections,
    obligations: Vec<Formula>,
    ranges: Option<&'r dyn RangeOf>,
    /// The `k::matches!` tests read as pattern matching, by atom key.
    tests: BTreeMap<String, Test>,
    /// The subjects of those tests that are not binders: the virtual
    /// columns, by canonical text.
    virtuals: BTreeMap<String, Virtual>,
    /// What the ranges of total functions state about Int subjects.
    facts: BTreeMap<String, Fact>,
}

/// A `k::matches!` test read as pattern matching.
#[derive(Clone, Debug)]
struct Test {
    subject: TestSubject,
    /// The tested term's sort, within which the test's complement is taken.
    sort: Sort,
    /// The pattern's alternatives, its local binders as binders of their
    /// sort (BIND-1: they bind nothing outside the test).
    alternatives: Vec<Pattern>,
}

/// Where the term a [`Test`] tests is in the matrix.
#[derive(Clone, Debug)]
enum TestSubject {
    /// A binder of the equation's pattern, at its path.
    Binder(Path),
    /// Another term, by its canonical text: one extra column of the
    /// function's matrix, whose value is the term's one unknown value.
    Virtual(String),
}

/// A virtual column: the sort of its term, and the heads its function's
/// range admits, if it has one.
#[derive(Clone, Debug)]
struct Virtual {
    sort: Sort,
    heads: Option<BTreeSet<Head>>,
}

/// The ranges of total functions, as far as the lint has inferred them.
trait RangeOf {
    fn range_of(&self, id: &StableItemId) -> Option<Rc<Range>>;
}

/// How a guard subject reads bits of another subject, its base.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Projection {
    /// `bitRangeInt(base, offset, length)`.
    BitRange { offset: BigInt, length: BigInt },
    /// `base &Int mask`, with a non-negative mask.
    Mask(BigInt),
    /// A length or size (`bytes::length`, `list::size`, ...), its own base:
    /// never negative.
    Size,
}

impl Projection {
    /// The fact `subject == value` states about the base: `Some(Err(()))`
    /// when the subject cannot have that value.
    fn fact(&self, value: &BigInt) -> Option<Result<IntFact, ()>> {
        let value = i128::try_from(value).ok()?;
        match self {
            Self::BitRange { offset, length } => IntFact::bit_range(
                i128::try_from(offset).ok()?,
                i128::try_from(length).ok()?,
                value,
            ),
            Self::Mask(mask) => IntFact::masked(i128::try_from(mask).ok()?, value),
            Self::Size => None,
        }
    }

    /// The least and greatest value the subject can have.
    fn range(&self) -> (BigInt, BigInt) {
        match self {
            Self::BitRange { length, .. } => (
                BigInt::from(0),
                usize::try_from(length)
                    .ok()
                    .filter(|length| *length <= 4096)
                    .map_or_else(
                        || BigInt::from(1) << 4096_usize,
                        |length| BigInt::from(1) << length,
                    )
                    - 1,
            ),
            Self::Mask(mask) => (BigInt::from(0), mask.clone()),
            Self::Size => (BigInt::from(0), BigInt::from(1) << 4096_usize),
        }
    }
}

/// The projections among the subjects of a function's guards, keyed by the
/// projecting subject's canonical text, with the base's.
pub(crate) type Projections = BTreeMap<String, (String, Projection)>;

/// `GetOrDefault` as `get_or_default`, the facade's spelling of a
/// collection operation.
fn snake_case(name: &str) -> String {
    let mut out = String::new();
    for (index, character) in name.chars().enumerate() {
        if character.is_ascii_uppercase() {
            if index > 0 {
                out.push('_');
            }
            out.push(character.to_ascii_lowercase());
        } else {
            out.push(character);
        }
    }
    out
}

/// The prefix of the binder that stands for an unnamed `k::bits!`
/// template's value; authors cannot write it.
const HIDDEN_BITS_BINDER: &str = "__krs_bits_";

/// How a diagnostic names a binder: its name, or `_` for an unnamed one,
/// a `k::bits!` template's hidden binder included.
pub(crate) fn binder_text(variable: &SemanticId) -> String {
    match variable.kind() {
        SemanticIdKind::Named if !variable.as_str().starts_with(HIDDEN_BITS_BINDER) => {
            variable.as_str().to_owned()
        }
        _ => "_".to_owned(),
    }
}

fn path_text(path: &[usize]) -> String {
    let mut text = String::from("$");
    for (index, step) in path.iter().enumerate() {
        if index > 0 {
            text.push('.');
        }
        text.push_str(&step.to_string());
    }
    text
}

impl<'r> GuardReader<'r> {
    fn new(
        signature: &'r Signature,
        paths: &'r BTreeMap<SemanticId, Path>,
        ranges: Option<&'r dyn RangeOf>,
    ) -> Self {
        Self {
            signature,
            paths,
            names: Names::new(),
            projections: Projections::new(),
            obligations: Vec::new(),
            ranges,
            tests: BTreeMap::new(),
            virtuals: BTreeMap::new(),
            facts: BTreeMap::new(),
        }
    }

    /// The range of a total function's application, if the lint inferred one.
    fn range(&self, term: &SemanticTerm) -> Option<Rc<Range>> {
        let SemanticTermKind::Application {
            application: ApplicationRef::Declared(id),
            ..
        } = term.kind()
        else {
            return None;
        };
        self.ranges?.range_of(id)
    }

    /// Constant-folds an Int term built from literals.
    fn constant(term: &SemanticTerm) -> Option<BigInt> {
        match term.kind() {
            SemanticTermKind::Token { value }
                if matches!(term.sort(), Sort::Builtin(BuiltinSort::Int)) =>
            {
                value.parse().ok()
            }
            SemanticTermKind::Application {
                application: ApplicationRef::Builtin(operation),
                arguments,
                ..
            } => {
                let values = arguments
                    .iter()
                    .map(Self::constant)
                    .collect::<Option<Vec<_>>>()?;
                let zero = BigInt::from(0);
                match (operation, values.as_slice()) {
                    (BuiltinOperation::IntAdd, [left, right]) => Some(left + right),
                    (BuiltinOperation::IntSub, [left, right]) => Some(left - right),
                    (BuiltinOperation::IntMul, [left, right]) => Some(left * right),
                    // Truncating division, as `/Int`; undefined by zero.
                    (BuiltinOperation::IntTDiv, [left, right]) if *right != zero => {
                        Some(left / right)
                    }
                    (BuiltinOperation::IntPow, [base, exponent]) => u32::try_from(exponent)
                        .ok()
                        .filter(|exponent| *exponent <= 4096)
                        .map(|exponent| base.pow(exponent)),
                    (BuiltinOperation::IntShiftLeft, [value, shift]) => usize::try_from(shift)
                        .ok()
                        .filter(|shift| *shift <= 4096)
                        .map(|shift| value << shift),
                    // Arithmetic shift rounds toward negative infinity, as `>>Int`.
                    (BuiltinOperation::IntShiftRight, [value, shift]) => {
                        usize::try_from(shift).ok().map(|shift| value >> shift)
                    }
                    (BuiltinOperation::IntBitRange, [value, index, length]) => {
                        let index = usize::try_from(index).ok()?;
                        let length = usize::try_from(length)
                            .ok()
                            .filter(|length| *length <= 4096)?;
                        let modulus = BigInt::from(1) << length;
                        let remainder = (value >> index) % &modulus;
                        Some(if remainder < zero {
                            remainder + modulus
                        } else {
                            remainder
                        })
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Whether a partial Int operation is defined because its restricted
    /// operand is a constant in range: a nonzero divisor, a non-negative
    /// shift or exponent.
    fn defined_at(operation: BuiltinOperation, arguments: &[SemanticTerm]) -> bool {
        let operand = |index: usize| arguments.get(index).and_then(Self::constant);
        let zero = BigInt::from(0);
        match operation {
            BuiltinOperation::IntTDiv
            | BuiltinOperation::IntEDiv
            | BuiltinOperation::IntMod
            | BuiltinOperation::IntTMod => operand(1).is_some_and(|divisor| divisor != zero),
            BuiltinOperation::IntShiftLeft
            | BuiltinOperation::IntShiftRight
            | BuiltinOperation::IntPow => operand(1).is_some_and(|amount| amount >= zero),
            // `bitRangeInt(I, IDX, LEN)` is `(I >>Int IDX) modInt (1 <<Int LEN)`:
            // both shifts are defined for a non-negative amount, and the
            // divisor is then at least 1.
            BuiltinOperation::IntBitRange => {
                operand(1).is_some_and(|index| index >= zero)
                    && operand(2).is_some_and(|length| length >= zero)
            }
            // `signExtendBitRangeInt` also shifts by `LEN -Int 1`.
            BuiltinOperation::IntSignExtendBitRange => {
                operand(1).is_some_and(|index| index >= zero)
                    && operand(2).is_some_and(|length| length >= BigInt::from(1))
            }
            _ => false,
        }
    }

    /// The canonical text of a defined term and records its rendering, and
    /// the base it reads bits of, if any.
    fn subject(&mut self, term: &SemanticTerm) -> Option<String> {
        let (key, text) = self.canonical(term)?;
        self.names.entry(key.clone()).or_insert(text);
        if let Some(range) = self.range(term)
            && let Range::Ints(intervals) = range.as_ref()
        {
            self.facts
                .entry(key.clone())
                .or_insert_with(|| Fact::Within(intervals.clone()));
        }
        if Self::constant(term).is_none()
            && let Some((base, projection)) = Self::projection(term)
        {
            let (base_key, base_text) = self.canonical(base)?;
            self.names.entry(base_key.clone()).or_insert(base_text);
            self.projections
                .entry(key.clone())
                .or_insert((base_key, projection));
        } else if Self::is_size(term) {
            self.projections
                .entry(key.clone())
                .or_insert((key.clone(), Projection::Size));
        }
        Some(key)
    }

    /// Whether a term is a length or a size, which is never negative.
    fn is_size(term: &SemanticTerm) -> bool {
        match term.kind() {
            SemanticTermKind::Application {
                application: ApplicationRef::Builtin(operation),
                ..
            } => matches!(
                operation,
                BuiltinOperation::BytesLength | BuiltinOperation::StringLength
            ),
            SemanticTermKind::Map(operands) => operands.operation() == MapOperation::Size,
            SemanticTermKind::List(operands) => operands.operation() == ListOperation::Size,
            SemanticTermKind::Set(operands) => operands.operation() == SetOperation::Size,
            _ => false,
        }
    }

    /// `bitRangeInt(base, o, l)` with constant `o` and `l`, or `base &Int m`
    /// with a constant non-negative `m`: its base and how it reads it.
    fn projection(term: &SemanticTerm) -> Option<(&SemanticTerm, Projection)> {
        let SemanticTermKind::Application {
            application: ApplicationRef::Builtin(operation),
            arguments,
            ..
        } = term.kind()
        else {
            return None;
        };
        match (operation, arguments.as_slice()) {
            (BuiltinOperation::IntBitRange, [base, offset, length]) => Some((
                base,
                Projection::BitRange {
                    offset: Self::constant(offset)?,
                    length: Self::constant(length)?,
                },
            )),
            (BuiltinOperation::IntBitAnd, [first, second]) => {
                let (base, mask) = match (Self::constant(first), Self::constant(second)) {
                    (None, Some(mask)) => (first, mask),
                    (Some(mask), None) => (second, mask),
                    _ => return None,
                };
                (mask >= BigInt::from(0)).then_some((base, Projection::Mask(mask)))
            }
            _ => None,
        }
    }

    /// The canonical texts and the renderings of terms, joined.
    fn canonical_list<'t>(
        &mut self,
        terms: impl Iterator<Item = &'t SemanticTerm>,
    ) -> Option<(String, String)> {
        let mut keys = Vec::new();
        let mut texts = Vec::new();
        for term in terms {
            let (key, text) = self.canonical(term)?;
            keys.push(key);
            texts.push(text);
        }
        Some((keys.join(", "), texts.join(", ")))
    }

    /// The canonical text and the rendering of a term, if it is defined
    /// wherever the reader's obligations hold: binders, literals,
    /// constructors, total functions, total builtins, partial Int builtins
    /// (whose domain becomes an obligation), and `k::is!`.
    fn canonical(&mut self, term: &SemanticTerm) -> Option<(String, String)> {
        if let Some(constant) = Self::constant(term) {
            let text = constant.to_string();
            return Some((text.clone(), text));
        }
        match term.kind() {
            SemanticTermKind::Variable { variable } => {
                let path = self.paths.get(variable)?;
                let text = binder_text(variable);
                Some((path_text(path), text))
            }
            SemanticTermKind::Token { value } => {
                Some((format!("{}:{value}", sort_name(term.sort())), value.clone()))
            }
            SemanticTermKind::Application {
                application,
                arguments,
                instance,
                ..
            } => {
                let (head_key, head_text) = match application {
                    ApplicationRef::Declared(id) => {
                        if !self.signature.constructors.contains_key(id)
                            && !self.signature.total_functions.contains(id)
                        {
                            return None;
                        }
                        (format!("{id:?}{instance:?}"), display_name(id))
                    }
                    ApplicationRef::Builtin(operation) => {
                        if !operation.is_total() && !Self::defined_at(*operation, arguments) {
                            let domain = self.domain(*operation, arguments)?;
                            self.obligations.push(domain);
                        }
                        let spec = operation.spec();
                        (
                            format!("{operation:?}"),
                            format!("{}::{}", spec.rust_module, spec.rust_name),
                        )
                    }
                    ApplicationRef::Generated(GeneratedOperation::SortPredicate(sort)) => (
                        format!("is:{sort:?}"),
                        format!("k::is!({}, ..)", sort_name(sort)),
                    ),
                    ApplicationRef::Generated(GeneratedOperation::SortProjection(_)) => {
                        return None;
                    }
                };
                let before = self.obligations.len();
                let (keys, texts) = self.canonical_list(arguments.iter())?;
                // A lazy connective inside a subject: whether it is defined
                // depends on the reading (see `formula`).
                if matches!(
                    application,
                    ApplicationRef::Builtin(
                        BuiltinOperation::BoolAndThen | BuiltinOperation::BoolOrElse
                    )
                ) && self.obligations.len() > before
                {
                    return None;
                }
                Some((
                    format!("{head_key}({keys})"),
                    format!("{head_text}({texts})"),
                ))
            }
            SemanticTermKind::Map(_) | SemanticTermKind::List(_) | SemanticTermKind::Set(_) => {
                self.canonical_collection(term)
            }
            _ => None,
        }
    }

    /// [`GuardReader::canonical`] of a Map, List or Set operation: a total
    /// one, or a lookup, whose domain becomes an obligation.
    fn canonical_collection(&mut self, term: &SemanticTerm) -> Option<(String, String)> {
        match term.kind() {
            SemanticTermKind::Map(operands) => {
                let operation = operands.operation();
                if operation == MapOperation::Get {
                    let [map, key] = operands.operands().collect::<Vec<_>>()[..] else {
                        return None;
                    };
                    let domain = self.key_domain(map, key)?;
                    self.obligations.push(domain);
                } else if !operation.is_total() {
                    return None;
                }
                let (keys, texts) = self.canonical_list(operands.operands())?;
                Some((
                    format!("map:{operation:?}({keys})"),
                    format!("map::{}({texts})", snake_case(&format!("{operation:?}"))),
                ))
            }
            SemanticTermKind::List(operands) => {
                let operation = operands.operation();
                if operation == ListOperation::Get {
                    let [list, index] = operands.operands().collect::<Vec<_>>()[..] else {
                        return None;
                    };
                    let domain = self.index_domain(list, index)?;
                    self.obligations.push(domain);
                } else if !operation.is_total() {
                    return None;
                }
                let (keys, texts) = self.canonical_list(operands.operands())?;
                Some((
                    format!("list:{operation:?}({keys})"),
                    format!("list::{}({texts})", snake_case(&format!("{operation:?}"))),
                ))
            }
            SemanticTermKind::Set(operands) => {
                let operation = operands.operation();
                if !operation.is_total() {
                    return None;
                }
                let (keys, texts) = self.canonical_list(operands.operands())?;
                Some((
                    format!("set:{operation:?}({keys})"),
                    format!("set::{}({texts})", snake_case(&format!("{operation:?}"))),
                ))
            }
            _ => None,
        }
    }

    /// Where a partial Int operation is defined, as a formula: a nonzero
    /// divisor, a non-negative shift or exponent, a non-negative bit index
    /// and length (a positive one for a sign extension). `None` for any
    /// other partial operation.
    fn domain(
        &mut self,
        operation: BuiltinOperation,
        arguments: &[SemanticTerm],
    ) -> Option<Formula> {
        let zero = BigInt::from(0);
        let at_least = |reader: &mut Self, index: usize, least: BigInt| {
            Some(
                reader
                    .compare(arguments.get(index)?, Bound::Below, least)?
                    .not(),
            )
        };
        match operation {
            BuiltinOperation::IntTDiv
            | BuiltinOperation::IntEDiv
            | BuiltinOperation::IntMod
            | BuiltinOperation::IntTMod => {
                Some(self.compare(arguments.get(1)?, Bound::At, zero)?.not())
            }
            BuiltinOperation::IntShiftLeft
            | BuiltinOperation::IntShiftRight
            | BuiltinOperation::IntPow => at_least(self, 1, zero),
            BuiltinOperation::IntBitRange => Some(Formula::And(
                Box::new(at_least(self, 1, zero.clone())?),
                Box::new(at_least(self, 2, zero)?),
            )),
            BuiltinOperation::IntSignExtendBitRange => Some(Formula::And(
                Box::new(at_least(self, 1, zero)?),
                Box::new(at_least(self, 2, BigInt::from(1))?),
            )),
            _ => None,
        }
    }

    /// Where `map::get(map, key)` is defined: `key` is a key of `map`.
    fn key_domain(&mut self, map: &SemanticTerm, key: &SemanticTerm) -> Option<Formula> {
        let (map_key, map_text) = self.canonical(map)?;
        let (key_key, key_text) = self.canonical(key)?;
        let atom = format!("map:InKeys({key_key}, {map_key})");
        self.names
            .entry(atom.clone())
            .or_insert_with(|| format!("map::in_keys({key_text}, {map_text})"));
        Some(Formula::Atom(Atom::Opaque(atom)))
    }

    /// Where `list::get(list, index)` is defined: `-size <= index < size`,
    /// a negative index counting from the end.
    fn index_domain(&mut self, list: &SemanticTerm, index: &SemanticTerm) -> Option<Formula> {
        let (list_key, list_text) = self.canonical(list)?;
        let size = format!("list:Size({list_key})");
        self.names
            .entry(size.clone())
            .or_insert_with(|| format!("list::size({list_text})"));
        self.projections
            .entry(size.clone())
            .or_insert((size.clone(), Projection::Size));
        let bound = |bound, constant| {
            Formula::Atom(Atom::Bound {
                subject: size.clone(),
                bound,
                constant,
            })
        };
        if let Some(constant) = Self::constant(index) {
            // A size is never negative: `c < size` for `c >= 0`, and
            // `-c <= size` for `c < 0`.
            return Some(if constant >= BigInt::from(0) {
                bound(Bound::Above, constant)
            } else {
                bound(Bound::Below, -constant).not()
            });
        }
        let index = self.subject(index)?;
        let below = if index < size {
            Atom::Order {
                left: index.clone(),
                right: size.clone(),
                order: Order::Less,
            }
        } else {
            Atom::Order {
                left: size.clone(),
                right: index.clone(),
                order: Order::Greater,
            }
        };
        let sum = format!("IntAdd({index}, {size})");
        let sum_text = format!("int::add({}, {})", self.names[&index], self.names[&size]);
        self.names.entry(sum.clone()).or_insert(sum_text);
        let negative = || {
            Formula::Atom(Atom::Bound {
                subject: index.clone(),
                bound: Bound::Below,
                constant: BigInt::from(0),
            })
        };
        // `0 <= index < size`, or `index < 0` and `index + size >= 0`: the
        // first case is one of order and bounds, which the decider relates
        // to the guard's own comparisons of `index`.
        let from_start = Formula::And(Box::new(negative().not()), Box::new(Formula::Atom(below)));
        let from_end = Formula::And(
            Box::new(negative()),
            Box::new(
                Formula::Atom(Atom::Bound {
                    subject: sum,
                    bound: Bound::Below,
                    constant: BigInt::from(0),
                })
                .not(),
            ),
        );
        Some(Formula::Or(Box::new(from_start), Box::new(from_end)))
    }

    /// A term with its constant summands taken out: `x + 2 - 5` is `x` and
    /// `-3`, so a comparison of it with a constant is one of `x`.
    fn offset(term: &SemanticTerm) -> (&SemanticTerm, BigInt) {
        if let SemanticTermKind::Application {
            application: ApplicationRef::Builtin(operation),
            arguments,
            ..
        } = term.kind()
            && let [left, right] = arguments.as_slice()
        {
            match (operation, Self::constant(left), Self::constant(right)) {
                (BuiltinOperation::IntAdd, None, Some(constant)) => {
                    let (base, offset) = Self::offset(left);
                    return (base, offset + constant);
                }
                (BuiltinOperation::IntAdd, Some(constant), None) => {
                    let (base, offset) = Self::offset(right);
                    return (base, offset + constant);
                }
                (BuiltinOperation::IntSub, None, Some(constant)) => {
                    let (base, offset) = Self::offset(left);
                    return (base, offset - constant);
                }
                _ => {}
            }
        }
        (term, BigInt::from(0))
    }

    /// `term < constant`, `term == constant` or `constant < term`.
    fn compare(&mut self, term: &SemanticTerm, bound: Bound, constant: BigInt) -> Option<Formula> {
        if let Some(value) = Self::constant(term) {
            return Some(Formula::Constant(match bound {
                Bound::Below => value < constant,
                Bound::At => value == constant,
                Bound::Above => constant < value,
            }));
        }
        let (base, offset) = Self::offset(term);
        Some(Formula::Atom(Atom::Bound {
            subject: self.subject(base)?,
            bound,
            constant: constant - offset,
        }))
    }

    /// Reads a guard: where it holds, its obligations and its value.
    fn guard(&mut self, term: &SemanticTerm) -> Option<Formula> {
        let value = self.formula(term, Some(true))?;
        let mut seen = BTreeSet::new();
        let obligations = std::mem::take(&mut self.obligations)
            .into_iter()
            .filter(|obligation| seen.insert(format!("{obligation:?}")))
            .collect::<Vec<_>>();
        Some(
            obligations
                .into_iter()
                .rev()
                .fold(value, |formula, obligation| {
                    Formula::And(Box::new(obligation), Box::new(formula))
                }),
        )
    }

    /// Reads a Bool guard term at a polarity: `Some(true)` where the guard
    /// holds when it does, `Some(false)` under one negation, `None` when
    /// both matter (an operand of `==`).
    ///
    /// Every operation is strict in matching logic, so an undefined operand
    /// makes the guard undefined, which [`GuardReader::guard`] states by its
    /// obligations. A backend may evaluate `andThenBool` and `orElseBool`
    /// lazily: `false andThenBool ⊥` is then `false`, and `true orElseBool ⊥`
    /// is `true`. The two readings agree on whether a guard holds unless an
    /// obligation comes from the right operand of an `andThenBool` read
    /// negatively or of an `orElseBool` read positively; there the reader
    /// gives up.
    fn formula(&mut self, term: &SemanticTerm, polarity: Option<bool>) -> Option<Formula> {
        if let SemanticTermKind::Token { value } = term.kind()
            && matches!(term.sort(), Sort::Builtin(BuiltinSort::Bool))
        {
            return match value.as_str() {
                "true" => Some(Formula::Constant(true)),
                "false" => Some(Formula::Constant(false)),
                _ => None,
            };
        }
        if let SemanticTermKind::Application {
            application: ApplicationRef::Builtin(operation),
            arguments,
            ..
        } = term.kind()
        {
            match (operation.guard_meaning(), arguments.as_slice()) {
                (GuardMeaning::Negation, [operand]) => {
                    return Some(
                        self.formula(operand, polarity.map(|positive| !positive))?
                            .not(),
                    );
                }
                (GuardMeaning::Conjunction | GuardMeaning::Disjunction, [left, right]) => {
                    let left = self.formula(left, polarity)?;
                    let before = self.obligations.len();
                    let right = self.formula(right, polarity)?;
                    let lazy_disagrees = match operation {
                        BuiltinOperation::BoolAndThen => polarity != Some(true),
                        BuiltinOperation::BoolOrElse => polarity != Some(false),
                        _ => false,
                    };
                    if lazy_disagrees && self.obligations.len() > before {
                        return None;
                    }
                    let (left, right) = (Box::new(left), Box::new(right));
                    return Some(if operation.guard_meaning() == GuardMeaning::Conjunction {
                        Formula::And(left, right)
                    } else {
                        Formula::Or(left, right)
                    });
                }
                (GuardMeaning::Implication, [left, right]) => {
                    return Some(Formula::Or(
                        Box::new(
                            self.formula(left, polarity.map(|positive| !positive))?
                                .not(),
                        ),
                        Box::new(self.formula(right, polarity)?),
                    ));
                }
                (GuardMeaning::Relation(literal), [first, second]) => {
                    let (left, right) = if literal.swapped {
                        (second, first)
                    } else {
                        (first, second)
                    };
                    let atom = self.relation(literal.relation, left, right, polarity)?;
                    return Some(if literal.positive { atom } else { atom.not() });
                }
                _ => {}
            }
        }
        if let SemanticTermKind::Matches {
            subject, pattern, ..
        } = term.kind()
        {
            return self.matches(subject, pattern);
        }
        let key = self.subject(term)?;
        // A Bool function whose equations all return one value.
        if let Some(range) = self.range(term)
            && let Range::Bools(values) = range.as_ref()
            && let [value] = values.iter().collect::<Vec<_>>()[..]
        {
            return Some(Formula::Constant(*value));
        }
        Some(Formula::Atom(Atom::Opaque(key)))
    }

    /// `pattern :=K subject` as an opaque atom, its test recorded when it
    /// can be read as pattern matching.
    fn matches(&mut self, subject: &SemanticTerm, pattern: &SemanticTerm) -> Option<Formula> {
        let (pattern_key, pattern_text) = matches_pattern(pattern, &mut BTreeMap::new())?;
        let subject_key = self.subject(subject)?;
        let key = format!("matches({pattern_key}, {subject_key})");
        let text = format!("k::matches!({}, {pattern_text})", self.names[&subject_key]);
        self.names.entry(key.clone()).or_insert(text);
        if let Some(test) = self.test(subject, &subject_key, pattern) {
            self.tests.entry(key.clone()).or_insert(test);
        }
        Some(Formula::Atom(Atom::Opaque(key)))
    }

    /// The test `pattern :=K subject` as pattern matching: `None` when the
    /// pattern is not linear or not decomposable, or the subject is neither
    /// a pattern binder nor a term of a declared sort.
    fn test(&mut self, subject: &SemanticTerm, key: &str, pattern: &SemanticTerm) -> Option<Test> {
        let choices = alternatives(self.signature, pattern);
        if choices.len() > ALTERNATIVE_LIMIT {
            return None;
        }
        let mut patterns = Vec::new();
        for (pattern, bindings) in choices {
            let mut seen = BTreeSet::new();
            let linear = bindings.iter().all(|(binder, _)| {
                matches!(binder.kind(), SemanticIdKind::Wildcard) || seen.insert(binder)
            });
            if !linear || !decomposed(&pattern) {
                return None;
            }
            patterns.push(pattern);
        }
        let place = match subject.kind() {
            SemanticTermKind::Variable { variable } => {
                TestSubject::Binder(self.paths.get(variable)?.clone())
            }
            _ if matches!(subject.sort(), Sort::Declared(_)) => {
                let heads = match self.range(subject).as_deref() {
                    Some(Range::Heads(heads)) => Some(heads.clone()),
                    _ => None,
                };
                self.virtuals.entry(key.to_owned()).or_insert(Virtual {
                    sort: subject.sort().clone(),
                    heads,
                });
                TestSubject::Virtual(key.to_owned())
            }
            _ => return None,
        };
        Some(Test {
            subject: place,
            sort: subject.sort().clone(),
            alternatives: patterns,
        })
    }

    /// A positive literal of a canonical relation.
    fn relation(
        &mut self,
        relation: BuiltinOperation,
        left: &SemanticTerm,
        right: &SemanticTerm,
        polarity: Option<bool>,
    ) -> Option<Formula> {
        match relation {
            BuiltinOperation::IntLess | BuiltinOperation::IntEqual => {
                let equal = relation == BuiltinOperation::IntEqual;
                match (Self::constant(left), Self::constant(right)) {
                    (Some(left), Some(right)) => Some(Formula::Constant(if equal {
                        left == right
                    } else {
                        left < right
                    })),
                    (None, Some(constant)) => {
                        self.compare(left, if equal { Bound::At } else { Bound::Below }, constant)
                    }
                    (Some(constant), None) => self.compare(
                        right,
                        if equal { Bound::At } else { Bound::Above },
                        constant,
                    ),
                    (None, None) => {
                        let left = self.subject(left)?;
                        let right = self.subject(right)?;
                        let order = if equal { Order::Equal } else { Order::Less };
                        Some(match left.cmp(&right) {
                            std::cmp::Ordering::Equal => Formula::Constant(equal),
                            std::cmp::Ordering::Less => {
                                Formula::Atom(Atom::Order { left, right, order })
                            }
                            std::cmp::Ordering::Greater => Formula::Atom(Atom::Order {
                                left: right,
                                right: left,
                                order: if equal { Order::Equal } else { Order::Greater },
                            }),
                        })
                    }
                }
            }
            // `t == true` is `t`, and `t == false` is `not t`.
            BuiltinOperation::BoolEqual => {
                let literal = |term: &SemanticTerm| match term.kind() {
                    SemanticTermKind::Token { value } if value == "true" => Some(true),
                    SemanticTermKind::Token { value } if value == "false" => Some(false),
                    _ => None,
                };
                match (literal(left), literal(right)) {
                    (_, Some(value)) => {
                        let polarity = polarity.map(|positive| positive == value);
                        let formula = self.formula(left, polarity)?;
                        Some(if value { formula } else { formula.not() })
                    }
                    (Some(value), None) => {
                        let polarity = polarity.map(|positive| positive == value);
                        let formula = self.formula(right, polarity)?;
                        Some(if value { formula } else { formula.not() })
                    }
                    (None, None) => self.opaque_relation(relation, left, right, true),
                }
            }
            _ => self.opaque_relation(relation, left, right, false),
        }
    }

    fn opaque_relation(
        &mut self,
        relation: BuiltinOperation,
        left: &SemanticTerm,
        right: &SemanticTerm,
        symmetric: bool,
    ) -> Option<Formula> {
        let mut left = self.subject(left)?;
        let mut right = self.subject(right)?;
        if (symmetric || relation.guard_meaning_symmetric()) && right < left {
            std::mem::swap(&mut left, &mut right);
        }
        let key = format!("{relation:?}({left}, {right})");
        let text = format!(
            "{}::{}({}, {})",
            relation.spec().rust_module,
            relation.spec().rust_name,
            self.names[&left],
            self.names[&right]
        );
        self.names.entry(key.clone()).or_insert(text);
        Some(Formula::Atom(Atom::Opaque(key)))
    }
}

trait SymmetricRelation {
    fn guard_meaning_symmetric(self) -> bool;
}

impl SymmetricRelation for BuiltinOperation {
    fn guard_meaning_symmetric(self) -> bool {
        matches!(self.guard_meaning(), GuardMeaning::Relation(literal) if literal.symmetric)
    }
}

/// The most `k::matches!` tests one equation alternative expands by; past
/// it, its tests stay opaque atoms.
const TEST_LIMIT: usize = 6;

/// The rows of one equation alternative whose guard has `k::matches!`
/// tests ([`Test`]): one row per truth assignment of the tests, its
/// patterns refined by each test's pattern where the assignment makes the
/// test true and by its complement where false, its guard the original one
/// with the tests replaced by their truth values. Assignments whose guard is
/// then false, and refinements that match nothing, give no row.
///
/// Exact: for any argument (and value of each virtual column), the tests
/// have exactly one truth assignment, the argument matches exactly that
/// assignment's refined patterns, and the equation applies exactly where
/// that assignment's guard holds. `None` past [`TEST_LIMIT`] tests or
/// [`ALTERNATIVE_LIMIT`] rows, or where a refinement cannot be stated
/// exactly; the caller then keeps the tests as opaque atoms.
fn expand(
    signature: &Signature,
    patterns: &[Pattern],
    guard: &Formula,
    tests: &BTreeMap<String, Test>,
    virtuals: &BTreeMap<String, Path>,
) -> Option<Vec<(Vec<Pattern>, Formula)>> {
    let mut atoms = BTreeSet::new();
    guard.atoms(&mut atoms);
    let used = atoms
        .into_iter()
        .filter_map(|atom| match atom {
            Atom::Opaque(key) => tests.get_key_value(key),
            _ => None,
        })
        .collect::<Vec<_>>();
    if used.is_empty() || used.len() > TEST_LIMIT {
        return None;
    }
    let mut rows = Vec::new();
    for mask in 0..1_usize << used.len() {
        let truths = used
            .iter()
            .enumerate()
            .map(|(index, (key, _))| (*key, mask >> index & 1 == 1))
            .collect::<BTreeMap<_, _>>();
        let residual = guard.assign(&truths).simplify();
        if matches!(residual, Formula::Constant(false)) {
            continue;
        }
        let mut refined = vec![(patterns.to_vec(), Vec::<Formula>::new())];
        for (key, test) in &used {
            let path = match &test.subject {
                TestSubject::Binder(path) => path,
                TestSubject::Virtual(subject) => virtuals.get(subject)?,
            };
            let choices = if truths[key] {
                test.alternatives
                    .iter()
                    .map(|pattern| (pattern.clone(), Vec::new()))
                    .collect()
            } else {
                complement_all(signature, &test.alternatives, &test.sort, path)?
            };
            let mut next = Vec::new();
            for (patterns, residuals) in &refined {
                let current = pattern_at(patterns, path)?;
                for (choice, choice_residuals) in &choices {
                    for met in meet(signature, current, choice)? {
                        let mut residuals = residuals.clone();
                        residuals.extend(choice_residuals.iter().cloned());
                        next.push((replace_at(patterns, path, met)?, residuals));
                    }
                }
            }
            if next.len() > ALTERNATIVE_LIMIT {
                return None;
            }
            refined = next;
        }
        for (patterns, residuals) in refined {
            let guard = residuals
                .into_iter()
                .fold(residual.clone(), |guard, residual| residual.and(guard))
                .simplify();
            if !matches!(guard, Formula::Constant(false)) {
                rows.push((patterns, guard));
            }
        }
        if rows.len() > ALTERNATIVE_LIMIT {
            return None;
        }
    }
    Some(rows)
}

// ---------------------------------------------------------------------------
// Ranges of total functions

/// The values a total function can return, from its own equations: the
/// union of what each equation's result can be. A function has a range only
/// when the lint finds it covered and it is neither `underspecified`,
/// hooked, `smt_hook`, nor sort-parametric: `total` and `function` make each
/// application exactly one value, and covered means some equation applies
/// at every argument, so the value is one of the results. On a gap the
/// value would be unspecified, so an uncovered function has no range.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Range {
    /// Sorted disjoint intervals.
    Ints(Vec<Interval>),
    Bools(BTreeSet<bool>),
    /// Constructor heads.
    Heads(BTreeSet<Head>),
}

impl Range {
    fn int(low: Option<BigInt>, high: Option<BigInt>) -> Self {
        Self::Ints(vec![(low, high)])
    }

    /// The union of two ranges, `None` when they are of different kinds.
    fn union(self, other: Self) -> Option<Self> {
        Some(match (self, other) {
            (Self::Ints(mut left), Self::Ints(right)) => {
                left.extend(right);
                Self::Ints(merged(left))
            }
            (Self::Bools(mut left), Self::Bools(right)) => {
                left.extend(right);
                Self::Bools(left)
            }
            (Self::Heads(mut left), Self::Heads(right)) => {
                left.extend(right);
                Self::Heads(left)
            }
            _ => return None,
        })
    }
}

/// Intervals sorted, with those that overlap or touch merged.
fn merged(mut intervals: Vec<Interval>) -> Vec<Interval> {
    // `None` sorts first, which is the unbounded low end.
    intervals.sort();
    let mut merged: Vec<Interval> = Vec::new();
    for (low, high) in intervals {
        if let Some((_, last_high)) = merged.last_mut() {
            let touches = match (&*last_high, &low) {
                (None, _) | (_, None) => true,
                (Some(last), Some(low)) => *low <= last + 1,
            };
            if touches {
                *last_high = match (&*last_high, high) {
                    (None, _) | (_, None) => None,
                    (Some(last), Some(high)) => Some(last.max(&high).clone()),
                };
                continue;
            }
        }
        merged.push((low, high));
    }
    merged
}

/// The values one result can have, or `None` for a form the lint does not
/// bound: a literal or ground constant, a constructor application (its
/// head), a total function's application (its range), `bitRangeInt(_, o,
/// l)`, `x &Int m` with `m >= 0`, `x modInt c` with `c != 0` (constant
/// `o`, `l`, `m`, `c`), and a length or size.
fn result_range(signature: &Signature, ranges: &dyn RangeOf, term: &SemanticTerm) -> Option<Range> {
    if let Some(constant) = GuardReader::constant(term) {
        return Some(Range::int(Some(constant.clone()), Some(constant)));
    }
    if GuardReader::is_size(term) {
        return Some(Range::int(Some(BigInt::from(0)), None));
    }
    match term.kind() {
        SemanticTermKind::Token { value }
            if matches!(term.sort(), Sort::Builtin(BuiltinSort::Bool)) =>
        {
            match value.as_str() {
                "true" => Some(Range::Bools(BTreeSet::from([true]))),
                "false" => Some(Range::Bools(BTreeSet::from([false]))),
                _ => None,
            }
        }
        SemanticTermKind::Application {
            application: ApplicationRef::Declared(id),
            instance,
            ..
        } => {
            if signature.constructors.contains_key(id) {
                Some(Range::Heads(BTreeSet::from([Head::Constructor {
                    id: id.clone(),
                    instance: instance.clone(),
                }])))
            } else {
                ranges.range_of(id).map(|range| range.as_ref().clone())
            }
        }
        SemanticTermKind::Application {
            application: ApplicationRef::Builtin(operation),
            arguments,
            ..
        } => {
            let zero = BigInt::from(0);
            let constant = |index: usize| arguments.get(index).and_then(GuardReader::constant);
            match operation {
                BuiltinOperation::IntBitRange => {
                    let length = usize::try_from(constant(2)?)
                        .ok()
                        .filter(|length| *length <= 4096)?;
                    constant(1).filter(|offset| *offset >= zero)?;
                    Some(Range::int(
                        Some(zero),
                        Some((BigInt::from(1) << length) - 1),
                    ))
                }
                BuiltinOperation::IntBitAnd => {
                    let mask = constant(1).or_else(|| constant(0))?;
                    (mask >= zero).then(|| Range::int(Some(zero), Some(mask)))
                }
                BuiltinOperation::IntMod => {
                    let divisor = constant(1).filter(|divisor| *divisor != zero)?;
                    Some(Range::int(
                        Some(zero),
                        Some(BigInt::from(divisor.magnitude().clone()) - 1),
                    ))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Deciding guards

/// What is already known about an Int subject: the patterns fix an Int path
/// on a branch (`Equal`, `Excluded`), and the equations of a total function
/// bound the values of its applications (`Within`, see [`Range`]).
#[derive(Clone, Debug)]
pub(crate) enum Fact {
    Equal(BigInt),
    Excluded(BTreeSet<BigInt>),
    /// The subject lies in one of these closed intervals, `None` being
    /// unbounded.
    Within(Vec<Interval>),
}

/// A closed interval of integers, `None` being unbounded.
pub(crate) type Interval = (Option<BigInt>, Option<BigInt>);

/// A valuation of a guard's atoms under which no guard holds.
#[derive(Clone, Debug, Default)]
pub(crate) struct Counterexample {
    /// A value of each Int subject.
    pub(crate) values: BTreeMap<String, BigInt>,
    /// The order of each pair of compared subjects.
    pub(crate) orders: BTreeMap<(String, String), Order>,
    /// The truth of each opaque atom.
    pub(crate) truths: BTreeMap<String, bool>,
}

/// Whether a canonical text reads the argument at `path`.
fn reads_path(text: &str, path: &[usize]) -> bool {
    let needle = path_text(path);
    text.match_indices(&needle).any(|(start, _)| {
        !matches!(
            text[start + needle.len()..].chars().next(),
            Some(next) if next.is_ascii_digit()
        )
    })
}

impl Counterexample {
    /// Whether a subject or atom of the counterexample reads the argument at `path`.
    fn mentions(&self, path: &[usize]) -> bool {
        let reads = |text: &String| reads_path(text, path);
        self.values.keys().any(reads)
            || self.truths.keys().any(reads)
            || self
                .orders
                .keys()
                .any(|(left, right)| reads(left) || reads(right))
    }
}

/// The verdict on a disjunction of guards.
#[derive(Clone, Debug)]
pub(crate) enum Verdict {
    Valid,
    Refuted(Counterexample),
    Undecided,
}

/// The integers a valuation point stands for: from `low` to `high`
/// inclusive, `None` being unbounded.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Region {
    low: Option<BigInt>,
    high: Option<BigInt>,
}

impl Region {
    fn exactly(value: &BigInt) -> Self {
        Self {
            low: Some(value.clone()),
            high: Some(value.clone()),
        }
    }

    /// The one integer of the region, if it has one.
    fn exact(&self) -> Option<&BigInt> {
        match (&self.low, &self.high) {
            (Some(low), Some(high)) if low == high => Some(low),
            _ => None,
        }
    }

    /// Whether the region shares an integer with `low..=high`.
    fn meets(&self, low: &BigInt, high: &BigInt) -> bool {
        self.low.as_ref().is_none_or(|own| own <= high)
            && self.high.as_ref().is_none_or(|own| own >= low)
    }

    /// The bounds the region states about its subject.
    fn facts(&self) -> Vec<IntFact> {
        if let Some(value) = self.exact().and_then(|value| i128::try_from(value).ok()) {
            return vec![IntFact::Equal(value)];
        }
        let mut facts = Vec::new();
        if let Some(low) = self.low.as_ref().and_then(|low| i128::try_from(low).ok()) {
            facts.push(IntFact::AtLeast(low));
        }
        if let Some(high) = self
            .high
            .as_ref()
            .and_then(|high| i128::try_from(high).ok())
            .and_then(|high| high.checked_add(1))
        {
            facts.push(IntFact::Below(high));
        }
        facts
    }
}

/// Points of an Int subject that realize every truth assignment its bounds
/// can take: each constant, and one point of each open interval between
/// consecutive constants, all avoiding `excluded`.
#[cfg(test)]
fn points(constants: &BTreeSet<BigInt>, excluded: &BTreeSet<BigInt>) -> Vec<BigInt> {
    regions(constants, excluded)
        .into_iter()
        .map(|(point, _)| point)
        .collect()
}

/// [`points`], each with the region of integers it stands for.
fn regions(constants: &BTreeSet<BigInt>, excluded: &BTreeSet<BigInt>) -> Vec<(BigInt, Region)> {
    let one = BigInt::from(1);
    let mut chosen = BTreeMap::new();
    for constant in constants {
        if !excluded.contains(constant) {
            chosen.insert(constant.clone(), Region::exactly(constant));
        }
    }
    let ordered = constants.iter().cloned().collect::<Vec<_>>();
    let mut intervals = Vec::<(Option<BigInt>, Option<BigInt>)>::new();
    match (ordered.first(), ordered.last()) {
        (Some(first), Some(last)) => {
            intervals.push((None, Some(first - &one)));
            for pair in ordered.windows(2) {
                intervals.push((Some(&pair[0] + &one), Some(&pair[1] - &one)));
            }
            intervals.push((Some(last + &one), None));
        }
        _ => intervals.push((None, None)),
    }
    for (low, high) in intervals {
        if let (Some(low), Some(high)) = (&low, &high)
            && low > high
        {
            continue;
        }
        // Search from the end nearest zero; `excluded` is finite, so a
        // point is found within `excluded.len() + 1` steps unless the
        // interval lies entirely inside `excluded`.
        let zero = BigInt::from(0);
        let start = match (&low, &high) {
            (Some(low), _) if *low > zero => low.clone(),
            (_, Some(high)) if *high < zero => high.clone(),
            _ => zero.clone(),
        };
        let mut found = None;
        'search: for upward in [true, false] {
            for distance in 0..=excluded.len() {
                let candidate = if upward {
                    &start + distance
                } else {
                    &start - distance
                };
                let inside = low.as_ref().is_none_or(|low| candidate >= *low)
                    && high.as_ref().is_none_or(|high| candidate <= *high);
                if inside && !excluded.contains(&candidate) {
                    found = Some(candidate);
                    break 'search;
                }
            }
        }
        if let Some(point) = found {
            chosen.insert(point, Region { low, high });
        }
    }
    let mut points = chosen.into_iter().collect::<Vec<_>>();
    // Non-negative points first, each side nearest zero first, so a witness
    // is the smallest natural number the patterns leave out when there is one.
    points.sort_by_key(|(point, _)| (point < &BigInt::from(0), point.magnitude().clone()));
    points
}

/// The parts of `regions` inside `intervals`, each with a point of its own:
/// a region's atoms have one truth value on all of it, so its part inside
/// an interval needs one point, the one nearest zero.
fn within(regions: Vec<(BigInt, Region)>, intervals: &[Interval]) -> Vec<(BigInt, Region)> {
    let zero = BigInt::from(0);
    let mut parts = Vec::new();
    for (_, region) in regions {
        for (low, high) in intervals {
            let low = match (&region.low, low) {
                (Some(own), Some(other)) => Some(own.max(other).clone()),
                (own, other) => own.clone().or_else(|| other.clone()),
            };
            let high = match (&region.high, high) {
                (Some(own), Some(other)) => Some(own.min(other).clone()),
                (own, other) => own.clone().or_else(|| other.clone()),
            };
            if let (Some(low), Some(high)) = (&low, &high)
                && low > high
            {
                continue;
            }
            let point = match (&low, &high) {
                (Some(low), _) if *low > zero => low.clone(),
                (_, Some(high)) if *high < zero => high.clone(),
                _ => zero.clone(),
            };
            parts.push((point, Region { low, high }));
        }
    }
    parts.sort_by_key(|(point, _)| (point < &zero, point.magnitude().clone()));
    parts
}

/// Whether the subjects' values can hold together, as far as the bits their
/// projections fix tell (see [`IntFacts`]): `false` only when no integers
/// realize the valuation, so a valuation it rules out stands for nothing.
fn consistent(
    regions: &BTreeMap<&String, &Region>,
    projections: &Projections,
    facts: &BTreeMap<String, Fact>,
) -> bool {
    let mut bases = BTreeMap::<&String, IntFacts>::new();
    for (subject, region) in regions {
        let Some((base, projection)) = projections.get(*subject) else {
            continue;
        };
        let (least, greatest) = projection.range();
        if !region.meets(&least, &greatest) {
            return false;
        }
        let known = bases.entry(base).or_default();
        if let Some(value) = region.exact() {
            match projection.fact(value) {
                Some(Ok(fact)) => known.add(fact),
                Some(Err(())) => return false,
                None => {}
            }
        }
    }
    for (base, known) in &mut bases {
        if let Some(region) = regions.get(base) {
            for fact in region.facts() {
                known.add(fact);
            }
        } else if let Some(Fact::Equal(value)) = facts.get(base.as_str())
            && let Ok(value) = i128::try_from(value)
        {
            known.add(IntFact::Equal(value));
        }
        if !known.satisfiable() {
            return false;
        }
    }
    true
}

/// Integers that give every subject a value in its region and every
/// compared pair its order, if there are any: the regions and orders are
/// difference constraints (`x - y <= c`), feasible exactly when their
/// constraint graph has no negative cycle, and the shortest distances are
/// then a solution. A length or size is also at least 0. A valuation
/// without a solution stands for no integers, so the decider skips it:
/// `a == b`, `b == c` and `a < c` are not independent.
fn ordered(
    regions: &BTreeMap<&String, &Region>,
    orders: &BTreeMap<(&String, &String), Order>,
    projections: &Projections,
) -> Option<BTreeMap<String, BigInt>> {
    let mut nodes = BTreeMap::<&String, usize>::new();
    for subject in regions
        .keys()
        .copied()
        .chain(orders.keys().flat_map(|(left, right)| [*left, *right]))
    {
        let next = nodes.len() + 1;
        nodes.entry(subject).or_insert(next);
    }
    // An edge `(from, to, w)` states `x[to] - x[from] <= w`; node 0 is zero.
    let mut edges = Vec::<(usize, usize, BigInt)>::new();
    for (subject, &node) in &nodes {
        if let Some(region) = regions.get(subject) {
            if let Some(low) = &region.low {
                edges.push((node, 0, -low));
            }
            if let Some(high) = &region.high {
                edges.push((0, node, high.clone()));
            }
        }
        if matches!(projections.get(*subject), Some((_, Projection::Size))) {
            edges.push((node, 0, BigInt::from(0)));
        }
    }
    for ((left, right), order) in orders {
        let (left, right) = (nodes[left], nodes[right]);
        match order {
            Order::Less => edges.push((right, left, BigInt::from(-1))),
            Order::Equal => {
                edges.push((right, left, BigInt::from(0)));
                edges.push((left, right, BigInt::from(0)));
            }
            Order::Greater => edges.push((left, right, BigInt::from(-1))),
        }
    }
    let mut distance = vec![BigInt::from(0); nodes.len() + 1];
    for round in 0..=nodes.len() {
        let mut changed = false;
        for (from, to, weight) in &edges {
            let candidate = &distance[*from] + weight;
            if candidate < distance[*to] {
                distance[*to] = candidate;
                changed = true;
            }
        }
        if !changed {
            break;
        }
        if round == nodes.len() {
            return None;
        }
    }
    Some(
        nodes
            .into_iter()
            .map(|(subject, node)| (subject.clone(), &distance[node] - &distance[0]))
            .collect(),
    )
}

/// The refuting valuation, without the projections of a subject whose
/// value is exact: those say nothing more.
fn counterexample(
    values: BTreeMap<&String, &BigInt>,
    orders: BTreeMap<(&String, &String), Order>,
    truths: BTreeMap<&String, bool>,
    regions: &BTreeMap<&String, &Region>,
    projections: &Projections,
) -> Counterexample {
    let implied = |subject: &String| {
        projections.get(subject).is_some_and(|(base, _)| {
            base != subject
                && regions
                    .get(base)
                    .is_some_and(|region| region.exact().is_some())
        })
    };
    Counterexample {
        values: values
            .into_iter()
            .filter(|(subject, _)| !implied(subject))
            .map(|(subject, value)| (subject.clone(), value.clone()))
            .collect(),
        orders: orders
            .into_iter()
            .map(|((left, right), order)| ((left.clone(), right.clone()), order))
            .collect(),
        truths: truths
            .into_iter()
            .map(|(key, value)| (key.clone(), value))
            .collect(),
    }
}

fn evaluate(
    formula: &Formula,
    values: &BTreeMap<&String, &BigInt>,
    orders: &BTreeMap<(&String, &String), Order>,
    truths: &BTreeMap<&String, bool>,
) -> bool {
    match formula {
        Formula::Atom(Atom::Opaque(key)) => truths[key],
        Formula::Atom(Atom::Bound {
            subject,
            bound,
            constant,
        }) => {
            let value = values[subject];
            match bound {
                Bound::Below => value < constant,
                Bound::At => value == constant,
                Bound::Above => constant < value,
            }
        }
        Formula::Atom(Atom::Order { left, right, order }) => orders[&(left, right)] == *order,
        Formula::Not(inner) => !evaluate(inner, values, orders, truths),
        Formula::And(left, right) => {
            evaluate(left, values, orders, truths) && evaluate(right, values, orders, truths)
        }
        Formula::Or(left, right) => {
            evaluate(left, values, orders, truths) || evaluate(right, values, orders, truths)
        }
        Formula::Constant(value) => *value,
    }
}

/// One part of a refuting valuation that [`minimize`] may free.
#[derive(Clone, Copy)]
enum Item<'v> {
    /// The subject of `domains[index]`.
    Value(usize),
    Order((&'v String, &'v String)),
    Truth(&'v String),
}

/// A refuting valuation reduced to a condition that every valuation
/// satisfying it refutes. The subjects, then the orders, then the opaque
/// atoms are freed one at a time, in key order; an item stays freed only
/// when no valuation of all the items freed so far, with the kept ones
/// fixed, makes a guard hold. Valuations no integers realize are skipped,
/// as [`decide`] skips them, and an item whose check would enumerate more
/// than [`VALUATION_BUDGET`] valuations is kept.
///
/// A subject the condition does not name is therefore really free: every
/// argument the condition describes is uncovered, whatever that subject
/// is. Freeing items one at a time but checking them together matters when
/// the guards need two atoms at once (`Sign(a) == 1 && Sign(b) == 1`):
/// neither atom alone can make a guard hold, yet both together can. A
/// subject whose value matters only where it is undefined (the quotient of
/// a zero divisor, say) is freed, since the guards fail whatever it is.
#[expect(clippy::type_complexity, reason = "The three parts of a valuation.")]
fn minimize<'v>(
    guards: &[&Formula],
    domains: &'v [(&'v String, Vec<(BigInt, Region)>)],
    values: &BTreeMap<&'v String, &'v BigInt>,
    orders: &BTreeMap<(&'v String, &'v String), Order>,
    truths: &BTreeMap<&'v String, bool>,
    projections: &Projections,
    facts: &BTreeMap<String, Fact>,
) -> (
    BTreeMap<&'v String, &'v BigInt>,
    BTreeMap<(&'v String, &'v String), Order>,
    BTreeMap<&'v String, bool>,
) {
    let positions = domains
        .iter()
        .map(|(subject, domain)| {
            domain
                .iter()
                .position(|(point, _)| point == values[subject])
                .unwrap_or(0)
        })
        .collect::<Vec<_>>();
    let items = (0..domains.len())
        .map(Item::Value)
        .chain(orders.keys().copied().map(Item::Order))
        .chain(truths.keys().copied().map(Item::Truth))
        .collect::<Vec<_>>();
    let orders_of = [Order::Less, Order::Equal, Order::Greater];
    let size = |item: &Item<'_>| match item {
        Item::Value(index) => domains[*index].1.len() as u64,
        Item::Order(_) => 3,
        Item::Truth(_) => 2,
    };
    // Whether every valuation of `free`, the other items fixed, refutes.
    let refutes = |free: &[Item<'v>]| {
        let mut count = 1_u64;
        for item in free {
            count = count.saturating_mul(size(item));
        }
        if count > VALUATION_BUDGET {
            return false;
        }
        for index in 0..count {
            let mut rest = index;
            let mut chosen = positions.clone();
            let mut varied_orders = orders.clone();
            let mut varied_truths = truths.clone();
            for item in free {
                let size = size(item);
                let choice = usize::try_from(rest % size).unwrap_or(0);
                rest /= size;
                match item {
                    Item::Value(subject) => chosen[*subject] = choice,
                    Item::Order(pair) => {
                        varied_orders.insert(*pair, orders_of[choice]);
                    }
                    Item::Truth(key) => {
                        varied_truths.insert(*key, choice == 1);
                    }
                }
            }
            let mut varied_values = values.clone();
            let mut regions = BTreeMap::new();
            for ((subject, domain), position) in domains.iter().zip(&chosen) {
                let (point, region) = &domain[*position];
                varied_values.insert(*subject, point);
                regions.insert(*subject, region);
            }
            if !projections.is_empty() && !consistent(&regions, projections, facts) {
                continue;
            }
            if !varied_orders.is_empty() && ordered(&regions, &varied_orders, projections).is_none()
            {
                continue;
            }
            if guards
                .iter()
                .any(|guard| evaluate(guard, &varied_values, &varied_orders, &varied_truths))
            {
                return false;
            }
        }
        true
    };
    let mut free = Vec::new();
    let mut kept = Vec::new();
    for item in items {
        free.push(item);
        if !refutes(&free) {
            free.pop();
            kept.push(item);
        }
    }
    let (mut kept_values, mut kept_orders, mut kept_truths) =
        (BTreeMap::new(), BTreeMap::new(), BTreeMap::new());
    for item in kept {
        match item {
            Item::Value(index) => {
                let subject = domains[index].0;
                kept_values.insert(subject, values[subject]);
            }
            Item::Order(pair) => {
                kept_orders.insert(pair, orders[&pair]);
            }
            Item::Truth(key) => {
                kept_truths.insert(key, truths[key]);
            }
        }
    }
    (kept_values, kept_orders, kept_truths)
}

/// Whether some guard holds under every valuation consistent with `facts`
/// (keyed by the path text of an Int binder).
///
/// Sound: every real valuation of the subjects gives each atom the value it
/// has under one of the enumerated valuations. An Int subject's bounds
/// change truth only at their constants, so the constants and one point
/// between each pair realize every assignment; two subjects are always in
/// exactly one of three orders, and a valuation whose orders and bounds no
/// integers realize together is skipped ([`ordered`]); distinct subjects are
/// otherwise treated as independent, which admits more valuations than
/// exist, never fewer.
///
/// A valuation that gives a projection of a subject (`bitRangeInt(t, o, l)`
/// or `t &Int m`, see [`Projections`]) a value its base cannot have
/// together with the others stands for no integers and is skipped.
#[cfg(test)]
pub(crate) fn decide(
    guards: &[&Formula],
    facts: &BTreeMap<String, Fact>,
    projections: &Projections,
) -> Verdict {
    decide_counted(guards, facts, projections, true, 0).0
}

/// [`decide`], with the number of valuations it had to consider. With
/// `minimize`, a refuting valuation is reduced to a condition every
/// valuation of which refutes (see [`minimize`]); without, it is the whole
/// valuation. The enumeration begins at valuation `start`, so a caller can
/// ask for the refutation after one it rejected; the number returned is
/// then the index after the last valuation considered.
#[expect(
    clippy::too_many_lines,
    reason = "One enumeration of the valuations: values, their consistency with projections and orders, truths, and the refutation."
)]
fn decide_counted(
    guards: &[&Formula],
    facts: &BTreeMap<String, Fact>,
    projections: &Projections,
    minimize: bool,
    start: u64,
) -> (Verdict, u64) {
    let mut atoms = BTreeSet::new();
    for guard in guards {
        guard.atoms(&mut atoms);
    }
    let mut constants = BTreeMap::<&String, BTreeSet<BigInt>>::new();
    let mut pairs = BTreeSet::<(&String, &String)>::new();
    let mut opaque = Vec::<&String>::new();
    for atom in &atoms {
        match atom {
            Atom::Opaque(key) => opaque.push(key),
            Atom::Bound {
                subject, constant, ..
            } => {
                constants
                    .entry(subject)
                    .or_default()
                    .insert(constant.clone());
            }
            Atom::Order { left, right, .. } => {
                pairs.insert((left, right));
            }
        }
    }
    let domains = constants
        .iter()
        .map(|(subject, constants)| {
            let values = match facts.get(subject.as_str()) {
                Some(Fact::Equal(value)) => vec![(value.clone(), Region::exactly(value))],
                Some(Fact::Excluded(excluded)) => regions(constants, excluded),
                Some(Fact::Within(intervals)) => {
                    within(regions(constants, &BTreeSet::new()), intervals)
                }
                None => regions(constants, &BTreeSet::new()),
            };
            (*subject, values)
        })
        .collect::<Vec<_>>();
    let pairs = pairs.into_iter().collect::<Vec<_>>();
    let mut count = 1_u64;
    for (_, values) in &domains {
        count = count.saturating_mul(values.len() as u64);
    }
    count = count.saturating_mul(3_u64.saturating_pow(pairs.len().try_into().unwrap_or(u32::MAX)));
    count = count.saturating_mul(2_u64.saturating_pow(opaque.len().try_into().unwrap_or(u32::MAX)));
    if count > VALUATION_BUDGET {
        return (Verdict::Undecided, count);
    }
    if domains.iter().any(|(_, values)| values.is_empty()) {
        // Some subject has no value consistent with the facts: the region
        // is empty, so nothing is uncovered there.
        return (Verdict::Valid, 0);
    }
    let orders_of = [Order::Less, Order::Equal, Order::Greater];
    for index in start..count {
        let mut rest = index;
        let mut values = BTreeMap::new();
        let mut regions = BTreeMap::new();
        for (subject, domain) in &domains {
            let size = domain.len() as u64;
            let (value, region) = &domain[usize::try_from(rest % size).unwrap_or(0)];
            values.insert(*subject, value);
            regions.insert(*subject, region);
            rest /= size;
        }
        if !projections.is_empty() && !consistent(&regions, projections, facts) {
            continue;
        }
        let mut orders = BTreeMap::new();
        for (left, right) in &pairs {
            orders.insert(
                (*left, *right),
                orders_of[usize::try_from(rest % 3).unwrap_or(0)],
            );
            rest /= 3;
        }
        let solution = if pairs.is_empty() {
            None
        } else {
            let Some(solution) = ordered(&regions, &orders, projections) else {
                continue;
            };
            Some(solution)
        };
        let mut truths = BTreeMap::new();
        for key in &opaque {
            truths.insert(*key, rest % 2 == 1);
            rest /= 2;
        }
        if !guards
            .iter()
            .any(|guard| evaluate(guard, &values, &orders, &truths))
        {
            let (values, orders, truths) = if minimize {
                self::minimize(
                    guards,
                    &domains,
                    &values,
                    &orders,
                    &truths,
                    projections,
                    facts,
                )
            } else {
                (values, orders, truths)
            };
            let mut refutation = counterexample(values, orders, truths, &regions, projections);
            // Unminimized, a refutation is a candidate valuation: give every
            // compared subject integers that realize its orders too.
            if !minimize && let Some(solution) = solution {
                refutation.values.extend(solution);
            }
            return (Verdict::Refuted(refutation), index + 1);
        }
    }
    (Verdict::Valid, count)
}

// ---------------------------------------------------------------------------
// The pattern matrix

#[derive(Clone, Debug)]
struct Row {
    patterns: Vec<Pattern>,
    guard: Option<Rc<Formula>>,
}

#[derive(Clone, Debug)]
struct Column {
    sort: Sort,
    path: Path,
    /// The only heads the column's values can have, when a range restricts
    /// a virtual column.
    heads: Option<Rc<BTreeSet<Head>>>,
}

/// An uncovered value, in a witness vector.
#[derive(Clone, Debug)]
enum Witness {
    Any,
    Constructor(String, Vec<Witness>),
    Literal(String),
}

#[derive(Clone, Debug)]
struct Gap {
    values: Vec<Witness>,
    /// For a region every equation of which is guarded: the valuation
    /// under which no guard holds.
    condition: Option<Counterexample>,
}

struct Search<'s> {
    signature: &'s Signature,
    projections: &'s Projections,
    /// What ranges state about Int subjects (see [`Fact::Within`]).
    ranges: &'s BTreeMap<String, Fact>,
    /// The canonical text of each virtual column's term, by its path.
    virtuals: &'s BTreeMap<Path, String>,
    nodes: usize,
    valuations: u64,
    exhausted: bool,
}

impl Search<'_> {
    /// Up to `limit` uncovered argument vectors of `columns`.
    #[expect(
        clippy::too_many_lines,
        reason = "One matrix step specializes by every head of the first column."
    )]
    fn missing(
        &mut self,
        rows: &[Row],
        columns: &[Column],
        facts: &BTreeMap<String, Fact>,
        limit: usize,
    ) -> Vec<Gap> {
        self.nodes += 1;
        if self.nodes > NODE_BUDGET {
            self.exhausted = true;
        }
        if self.exhausted || limit == 0 {
            return Vec::new();
        }
        let Some((column, rest)) = columns.split_first() else {
            return self.leaf(rows, facts);
        };
        let rows = rows
            .iter()
            .filter(|row| !matches!(row.patterns[0], Pattern::Opaque))
            .collect::<Vec<_>>();
        let explicit = rows
            .iter()
            .filter_map(|row| match &row.patterns[0] {
                Pattern::Constructor { id, instance, .. } => Some(Head::Constructor {
                    id: id.clone(),
                    instance: instance.clone(),
                }),
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        let mut gaps = Vec::new();
        // Constructors no row names: only binders match them, so all their
        // arguments are uncovered or none is; one representative per set of
        // matching rows suffices.
        let mut unnamed = BTreeMap::<Vec<usize>, Head>::new();
        for head in self.signature.heads(&column.sort) {
            if gaps.len() >= limit || self.exhausted {
                break;
            }
            if column
                .heads
                .as_ref()
                .is_some_and(|allowed| !allowed.contains(&head))
            {
                continue;
            }
            match &head {
                Head::Constructor { id, instance } if explicit.contains(&head) => {
                    let arguments = self.signature.arguments(id, instance);
                    let arity = arguments.len();
                    let specialized = rows
                        .iter()
                        .filter_map(|row| {
                            let tail = row.patterns[1..].iter().cloned();
                            let patterns = match &row.patterns[0] {
                                Pattern::Constructor {
                                    id: named,
                                    instance: named_instance,
                                    arguments,
                                } if named == id && named_instance == instance => {
                                    arguments.iter().cloned().chain(tail).collect()
                                }
                                Pattern::Binder(sort)
                                    if self.signature.binder_covers(sort, &head) =>
                                {
                                    arguments
                                        .iter()
                                        .cloned()
                                        .map(Pattern::Binder)
                                        .chain(tail)
                                        .collect()
                                }
                                _ => return None,
                            };
                            Some(Row {
                                patterns,
                                guard: row.guard.clone(),
                            })
                        })
                        .collect::<Vec<_>>();
                    let columns = arguments
                        .into_iter()
                        .enumerate()
                        .map(|(index, sort)| Column {
                            sort,
                            path: column.path.iter().copied().chain([index]).collect(),
                            heads: None,
                        })
                        .chain(rest.iter().cloned())
                        .collect::<Vec<_>>();
                    for mut gap in self.missing(&specialized, &columns, facts, limit - gaps.len()) {
                        let tail = gap.values.split_off(arity);
                        let mut values = vec![Witness::Constructor(display_name(id), gap.values)];
                        values.extend(tail);
                        gaps.push(Gap {
                            values,
                            condition: gap.condition,
                        });
                    }
                }
                Head::Constructor { .. } => {
                    let key = rows
                        .iter()
                        .enumerate()
                        .filter(|(_, row)| {
                            matches!(&row.patterns[0], Pattern::Binder(sort) if self.signature.binder_covers(sort, &head))
                        })
                        .map(|(index, _)| index)
                        .collect::<Vec<_>>();
                    unnamed.entry(key).or_insert(head);
                }
                Head::Family(family) => {
                    let found = self.family(
                        &rows,
                        column,
                        rest,
                        family,
                        &head,
                        facts,
                        limit - gaps.len(),
                    );
                    gaps.extend(found);
                }
            }
        }
        for (key, head) in unnamed {
            if gaps.len() >= limit || self.exhausted {
                break;
            }
            let Head::Constructor { id, instance } = &head else {
                continue;
            };
            let specialized = key
                .iter()
                .map(|&index| Row {
                    patterns: rows[index].patterns[1..].to_vec(),
                    guard: rows[index].guard.clone(),
                })
                .collect::<Vec<_>>();
            let arity = self.signature.arguments(id, instance).len();
            for gap in self.missing(&specialized, rest, facts, limit - gaps.len()) {
                let mut values = vec![Witness::Constructor(
                    display_name(id),
                    vec![Witness::Any; arity],
                )];
                values.extend(gap.values);
                gaps.push(Gap {
                    values,
                    condition: gap.condition,
                });
            }
        }
        gaps
    }

    /// The gaps among the values of one family in the first column: each
    /// literal some row names, then every other value.
    #[expect(
        clippy::too_many_arguments,
        clippy::too_many_lines,
        reason = "One matrix step over a family: its literals, then every other value."
    )]
    fn family(
        &mut self,
        rows: &[&Row],
        column: &Column,
        rest: &[Column],
        family: &Sort,
        head: &Head,
        facts: &BTreeMap<String, Fact>,
        limit: usize,
    ) -> Vec<Gap> {
        let boolean = matches!(family, Sort::Builtin(BuiltinSort::Bool));
        let integer = matches!(family, Sort::Builtin(BuiltinSort::Int));
        let named = rows
            .iter()
            .filter_map(|row| match &row.patterns[0] {
                Pattern::Literal { sort, value } if sort == family => Some(value.clone()),
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        let values = if boolean {
            vec!["true".to_owned(), "false".to_owned()]
        } else {
            named.iter().cloned().collect()
        };
        let path = path_text(&column.path);
        let mut gaps = Vec::new();
        for value in values {
            if gaps.len() >= limit || self.exhausted {
                break;
            }
            let specialized = rows
                .iter()
                .filter(|row| match &row.patterns[0] {
                    Pattern::Literal { sort, value: named } => sort == family && *named == value,
                    Pattern::Binder(sort) => self.signature.binder_covers(sort, head),
                    Pattern::Family(sort) => sort == family,
                    _ => false,
                })
                .map(|row| Row {
                    patterns: row.patterns[1..].to_vec(),
                    guard: row.guard.clone(),
                })
                .collect::<Vec<_>>();
            let mut facts = facts.clone();
            if integer && let Ok(number) = value.parse::<BigInt>() {
                facts.insert(path.clone(), Fact::Equal(number));
            }
            for gap in self.missing(&specialized, rest, &facts, limit - gaps.len()) {
                let mut values = vec![Witness::Literal(value.clone())];
                values.extend(gap.values);
                gaps.push(Gap {
                    values,
                    condition: gap.condition,
                });
            }
        }
        if boolean || gaps.len() >= limit || self.exhausted {
            return gaps;
        }
        let specialized = rows
            .iter()
            .filter(|row| match &row.patterns[0] {
                Pattern::Binder(sort) => self.signature.binder_covers(sort, head),
                Pattern::Family(sort) => sort == family,
                _ => false,
            })
            .map(|row| Row {
                patterns: row.patterns[1..].to_vec(),
                guard: row.guard.clone(),
            })
            .collect::<Vec<_>>();
        let mut facts = facts.clone();
        let excluded = named
            .iter()
            .filter_map(|value| value.parse::<BigInt>().ok())
            .collect::<BTreeSet<_>>();
        if integer {
            facts.insert(path.clone(), Fact::Excluded(excluded.clone()));
        }
        for mut gap in self.missing(&specialized, rest, &facts, limit - gaps.len()) {
            let chosen = gap
                .condition
                .as_mut()
                .and_then(|condition| condition.values.remove(&path));
            let constrained = gap
                .condition
                .as_ref()
                .is_some_and(|condition| condition.mentions(&column.path))
                || self.virtual_mentions(rest, &gap.values, &column.path);
            let witness = match family {
                // The guards constrain this argument through a term: name it
                // by its binder rather than by an arbitrary value.
                _ if chosen.is_none() && constrained => Witness::Any,
                Sort::Builtin(BuiltinSort::Int) => Witness::Literal(
                    chosen
                        .unwrap_or_else(|| {
                            regions(&BTreeSet::new(), &excluded)
                                .into_iter()
                                .next()
                                .map(|(point, _)| point)
                                .unwrap_or_default()
                        })
                        .to_string(),
                ),
                Sort::Builtin(BuiltinSort::String) => Witness::Literal(
                    (0..=named.len())
                        .map(|index| {
                            if index == 0 {
                                "\"\"".to_owned()
                            } else {
                                format!("\"{index}\"")
                            }
                        })
                        .find(|candidate| !named.contains(candidate))
                        .unwrap_or_default(),
                ),
                _ => Witness::Any,
            };
            let mut values = vec![witness];
            values.extend(gap.values);
            gaps.push(Gap {
                values,
                condition: gap.condition,
            });
        }
        gaps
    }

    /// Whether a virtual column among `columns` that a gap fixes to a head
    /// reads the argument at `path`: the gap's condition then names it.
    fn virtual_mentions(&self, columns: &[Column], values: &[Witness], path: &[usize]) -> bool {
        columns.iter().zip(values).any(|(column, value)| {
            !matches!(value, Witness::Any)
                && self
                    .virtuals
                    .get(&column.path)
                    .is_some_and(|key| reads_path(key, path))
        })
    }

    /// Every argument is decomposed: the region is covered by an unguarded
    /// row, or by guards whose disjunction is valid.
    fn leaf(&mut self, rows: &[Row], facts: &BTreeMap<String, Fact>) -> Vec<Gap> {
        if rows.iter().any(|row| row.guard.is_none()) {
            return Vec::new();
        }
        if rows.is_empty() {
            return vec![Gap {
                values: Vec::new(),
                condition: None,
            }];
        }
        let guards = rows
            .iter()
            .filter_map(|row| row.guard.as_deref())
            .collect::<Vec<_>>();
        let mut facts = facts.clone();
        facts.extend(
            self.ranges
                .iter()
                .map(|(subject, fact)| (subject.clone(), fact.clone())),
        );
        let (verdict, valuations) = decide_counted(&guards, &facts, self.projections, true, 0);
        self.valuations = self.valuations.saturating_add(valuations);
        if self.valuations > FUNCTION_VALUATION_BUDGET {
            self.exhausted = true;
            return Vec::new();
        }
        match verdict {
            Verdict::Valid => Vec::new(),
            Verdict::Refuted(counterexample) => vec![Gap {
                values: Vec::new(),
                condition: Some(counterexample),
            }],
            Verdict::Undecided => {
                self.exhausted = true;
                Vec::new()
            }
        }
    }
}

// ---------------------------------------------------------------------------
// One function instance

/// What the lint concludes about one function instance.
enum Outcome {
    Covered,
    Uncovered(Report),
    Undecided,
}

struct Report {
    gaps: Vec<Gap>,
    names: Names,
    /// The binder name at each argument path, from the first equation that
    /// binds one there.
    binders: BTreeMap<Path, String>,
    guarded: usize,
    unread: usize,
    contexts: usize,
    /// For a function the ground analysis decided: the values its
    /// equations bound, described.
    evaluated: Option<String>,
    /// The canonical text of each virtual column's term, in column order;
    /// they follow the arguments in each gap.
    virtuals: Vec<String>,
}

/// The values the equations bound at each argument, described.
fn describe_bounded(columns: &[ColumnValues]) -> String {
    let describe = |bounded: &[(i128, i128)]| {
        if bounded.is_empty() {
            return "no value".to_owned();
        }
        bounded
            .iter()
            .map(|(low, high)| {
                if high - low == 1 {
                    low.to_string()
                } else {
                    format!("{low}..={}", high - 1)
                }
            })
            .collect::<Vec<_>>()
            .join(", ")
    };
    let ints = columns
        .iter()
        .enumerate()
        .filter_map(|(index, column)| match column {
            ColumnValues::Int { bounded, .. } => Some((index, describe(bounded))),
            ColumnValues::Free => None,
        })
        .collect::<Vec<_>>();
    match ints.as_slice() {
        [(_, only)] if columns.len() == 1 => only.clone(),
        _ => ints
            .iter()
            .map(|(index, text)| format!("argument {} in {text}", index + 1))
            .collect::<Vec<_>>()
            .join(", "),
    }
}

/// Coverage decided by the ground analysis of the equations
/// (`equation_domain`): exact, so the outcome needs no abstraction of the
/// guards. `None` when the analysis gives up.
fn evaluate_instance<'a>(
    evaluator: &'a Evaluator<'a>,
    columns: &[Sort],
    rules: &[&'a SemanticRule],
) -> Option<Outcome> {
    let views = rules
        .iter()
        .map(|rule| equation_view(rule))
        .collect::<Option<Vec<_>>>()?;
    let domain = Domain::new(evaluator, columns, &views)?;
    let mut gaps = Vec::new();
    for point in domain.points() {
        let mut covered = false;
        for index in 0..views.len() {
            match domain.applies(index, &point) {
                Ok(true) => {
                    covered = true;
                    break;
                }
                Ok(false) => {}
                Err(Undecided) => return None,
            }
        }
        if !covered && gaps.len() < WITNESS_LIMIT {
            gaps.push(Gap {
                values: domain
                    .columns()
                    .iter()
                    .zip(&point)
                    .map(|(column, value)| match column {
                        ColumnValues::Int { .. } => Witness::Literal(value.to_string()),
                        ColumnValues::Free => Witness::Any,
                    })
                    .collect(),
                condition: None,
            });
        }
    }
    if gaps.is_empty() {
        return Some(Outcome::Covered);
    }
    Some(Outcome::Uncovered(Report {
        gaps,
        names: Names::new(),
        binders: BTreeMap::new(),
        guarded: rules
            .iter()
            .filter(|rule| rule.requires().is_some())
            .count(),
        unread: 0,
        contexts: 0,
        evaluated: Some(describe_bounded(domain.columns())),
        virtuals: Vec::new(),
    }))
}

fn check_instance(
    signature: &Signature,
    evaluator: &Evaluator<'_>,
    production: &SemanticProduction,
    instance: &[Sort],
    rules: &[&SemanticRule],
    ranges: &dyn RangeOf,
) -> Outcome {
    let columns = instantiate(
        &production_argument_sorts(production),
        production.parameters(),
        instance,
    );
    evaluate_instance(evaluator, &columns, rules)
        .unwrap_or_else(|| search_instance(signature, columns, rules, Some(ranges)))
}

/// Coverage decided by the pattern matrix and the guard abstraction. The
/// terms that `k::matches!` tests and that are not binders become virtual
/// columns after the arguments (see [`Test`]).
#[expect(
    clippy::too_many_lines,
    reason = "Reads every equation alternative, then lays out the matrix with its virtual columns."
)]
fn search_instance(
    signature: &Signature,
    columns: Vec<Sort>,
    rules: &[&SemanticRule],
    ranges: Option<&dyn RangeOf>,
) -> Outcome {
    let arity = columns.len();
    let mut read = Vec::<(Vec<Pattern>, Option<Formula>, BTreeMap<String, Test>)>::new();
    let mut names = Names::new();
    let mut projections = Projections::new();
    let mut facts = BTreeMap::<String, Fact>::new();
    let mut virtuals = BTreeMap::<String, Virtual>::new();
    let mut binders = BTreeMap::<Path, String>::new();
    let (mut guarded, mut unread, mut contexts) = (0, 0, 0);
    for rule in rules {
        let Some(body) = rule.body() else { continue };
        let SemanticTermKind::Application { arguments, .. } = body.from().kind() else {
            continue;
        };
        if rule.function_context().is_some() {
            contexts += 1;
            continue;
        }
        let Some(alternatives_of_row) = argument_alternatives(signature, arguments) else {
            unread += 1;
            continue;
        };
        if rule.requires().is_some() {
            guarded += 1;
        }
        for (patterns, bindings) in alternatives_of_row {
            let mut paths = BTreeMap::<SemanticId, Path>::new();
            let mut linear = true;
            for (binder, path) in &bindings {
                if binder_text(binder) != "_" {
                    binders
                        .entry(path.clone())
                        .or_insert_with(|| binder.as_str().to_owned());
                }
                linear &= paths.insert(binder.clone(), path.clone()).is_none();
            }
            // A binder that occurs twice matches only equal subterms, which
            // the matrix cannot express: the row covers nothing it can see.
            if !linear {
                unread += 1;
                continue;
            }
            match rule.requires() {
                None => read.push((patterns, None, BTreeMap::new())),
                Some(IrCondition::Bool(condition)) => {
                    let mut reader = GuardReader::new(signature, &paths, ranges);
                    let Some(formula) = reader.guard(condition.term()) else {
                        unread += 1;
                        continue;
                    };
                    for (key, text) in reader.names {
                        names.entry(key).or_insert(text);
                    }
                    for (key, projection) in reader.projections {
                        projections.entry(key).or_insert(projection);
                    }
                    for (key, fact) in reader.facts {
                        facts.entry(key).or_insert(fact);
                    }
                    for (key, column) in reader.virtuals {
                        virtuals.entry(key).or_insert(column);
                    }
                    read.push((patterns, Some(formula), reader.tests));
                }
                Some(IrCondition::Predicate(_)) => unread += 1,
            }
        }
    }
    let virtual_paths = virtuals
        .keys()
        .enumerate()
        .map(|(index, key)| (key.clone(), vec![arity + index]))
        .collect::<BTreeMap<_, _>>();
    let columns = columns
        .into_iter()
        .enumerate()
        .map(|(index, sort)| Column {
            sort,
            path: vec![index],
            heads: None,
        })
        .chain(virtuals.iter().map(|(key, column)| Column {
            sort: column.sort.clone(),
            path: virtual_paths[key].clone(),
            heads: column.heads.clone().map(Rc::new),
        }))
        .collect::<Vec<_>>();
    let mut rows = Vec::new();
    for (mut patterns, guard, tests) in read {
        patterns.extend(
            virtuals
                .values()
                .map(|column| Pattern::Binder(column.sort.clone())),
        );
        let Some(guard) = guard else {
            rows.push(Row {
                patterns,
                guard: None,
            });
            continue;
        };
        match expand(signature, &patterns, &guard, &tests, &virtual_paths) {
            Some(expanded) => rows.extend(expanded.into_iter().map(|(patterns, guard)| Row {
                patterns,
                guard: (!matches!(guard, Formula::Constant(true))).then(|| Rc::new(guard)),
            })),
            None => rows.push(Row {
                patterns,
                guard: Some(Rc::new(guard)),
            }),
        }
    }
    let virtual_keys = virtual_paths
        .iter()
        .map(|(key, path)| (path.clone(), key.clone()))
        .collect::<BTreeMap<_, _>>();
    let mut search = Search {
        signature,
        projections: &projections,
        ranges: &facts,
        virtuals: &virtual_keys,
        nodes: 0,
        valuations: 0,
        exhausted: false,
    };
    let gaps = search.missing(&rows, &columns, &BTreeMap::new(), WITNESS_LIMIT);
    if search.exhausted {
        return Outcome::Undecided;
    }
    if gaps.is_empty() {
        return Outcome::Covered;
    }
    Outcome::Uncovered(Report {
        gaps,
        names,
        binders,
        guarded,
        unread,
        contexts,
        evaluated: None,
        virtuals: virtuals.into_keys().collect(),
    })
}

// ---------------------------------------------------------------------------
// Diagnostics

fn location(origin: &krs_ir::NodeOrigin) -> Location {
    origin
        .origin()
        .exact_authored_range()
        .map_or(Location::None, Location::Source)
}

fn render(witness: &Witness) -> String {
    match witness {
        Witness::Any => "_".to_owned(),
        Witness::Literal(value) => value.clone(),
        Witness::Constructor(name, arguments) if arguments.is_empty() => name.clone(),
        Witness::Constructor(name, arguments) => format!(
            "{name}({})",
            arguments.iter().map(render).collect::<Vec<_>>().join(", ")
        ),
    }
}

/// Renders a witness vector, naming a top-level argument the guards or a
/// fixed virtual column constrain by its binder. The virtual columns'
/// values follow the arguments in `gap` and are not rendered here.
fn render_application(head: &str, gap: &Gap, report: &Report) -> String {
    let arity = gap.values.len() - report.virtuals.len();
    let fixed = gap.values[arity..]
        .iter()
        .zip(&report.virtuals)
        .filter(|(value, _)| !matches!(value, Witness::Any))
        .map(|(_, key)| key)
        .collect::<Vec<_>>();
    let arguments = gap.values[..arity]
        .iter()
        .enumerate()
        .map(
            |(index, witness)| match (witness, report.binders.get(&vec![index])) {
                (Witness::Any, Some(name))
                    if gap
                        .condition
                        .as_ref()
                        .is_some_and(|condition| condition.mentions(&[index]))
                        || fixed.iter().any(|key| reads_path(key, &[index])) =>
                {
                    name.clone()
                }
                _ => render(witness),
            },
        )
        .collect::<Vec<_>>();
    format!("{head}({})", arguments.join(", "))
}

/// The values a gap fixes for virtual columns, as condition parts.
fn render_virtuals(gap: &Gap, report: &Report) -> Vec<String> {
    let arity = gap.values.len() - report.virtuals.len();
    gap.values[arity..]
        .iter()
        .zip(&report.virtuals)
        .filter(|(value, _)| !matches!(value, Witness::Any))
        .map(|(value, key)| {
            let name = report
                .names
                .get(key)
                .cloned()
                .unwrap_or_else(|| key.clone());
            format!("`{name}` is `{}`", render(value))
        })
        .collect()
}

fn render_condition(condition: &Counterexample, names: &Names) -> String {
    let name = |key: &String| names.get(key).cloned().unwrap_or_else(|| key.clone());
    let mut parts = Vec::new();
    for (subject, value) in &condition.values {
        parts.push(format!("`{}` is {value}", name(subject)));
    }
    for ((left, right), order) in &condition.orders {
        let symbol = match order {
            Order::Less => "<",
            Order::Equal => "==",
            Order::Greater => ">",
        };
        parts.push(format!("`{} {symbol} {}`", name(left), name(right)));
    }
    for (key, truth) in &condition.truths {
        parts.push(format!("`{}` is {truth}", name(key)));
    }
    parts.join(", ")
}

fn uncovered_warning(
    production: &SemanticProduction,
    instance: &[Sort],
    report: &Report,
    raw: bool,
) -> Diagnostic {
    let mut head = display_name(production.id());
    if !instance.is_empty() {
        head = format!(
            "{head}::<{}>",
            instance
                .iter()
                .map(sort_name)
                .collect::<Vec<_>>()
                .join(", ")
        );
    }
    let describe = |gap: &Gap| {
        let application = render_application(&head, gap, report);
        let mut parts = render_virtuals(gap, report);
        if let Some(condition) = &gap.condition {
            let condition = render_condition(condition, &report.names);
            if !condition.is_empty() {
                parts.push(condition);
            }
        }
        if parts.is_empty() {
            format!("`{application}`")
        } else {
            format!("`{application}` when {}", parts.join(", "))
        }
    };
    let first = &report.gaps[0];
    let mut diagnostic = Diagnostic::error(
        codes::analysis::UNCOVERED_TOTAL_FUNCTION,
        format!(
            "total function `{head}` has no equation for {}",
            describe(first)
        ),
        location(production.origin()),
    );
    diagnostic.severity = Severity::Warning;
    if report.gaps.len() > 1 {
        diagnostic.notes.push(format!(
            "also uncovered: {}",
            report.gaps[1..]
                .iter()
                .map(describe)
                .collect::<Vec<_>>()
                .join("; ")
        ));
    }
    diagnostic.notes.push(format!(
        "`total` claims a value for every argument; where no equation applies, the value is some unspecified `{}`",
        sort_name(production.result_sort())
    ));
    if let Some(bounded) = &report.evaluated {
        if report.guarded > 0 {
            diagnostic.notes.push(format!(
                "KRS evaluated the `requires` of its equations on every argument they bound ({bounded}) and on one argument beyond them, which stands for every other"
            ));
        }
    } else if report.guarded > 0 {
        diagnostic.notes.push(format!(
            "{} of its equations have `requires`; KRS decides a `requires` only as a Boolean combination of comparisons with integer constants and between two integers and of `k::matches!` tests, reading the bits that comparisons of `bitRangeInt` and `&Int` fix and each application of a total function as one unknown value (one of its equations' results, when they cover every argument), where each partial Int operation in it (division, remainder, shift, exponent, bit range) is defined",
            report.guarded
        ));
    }
    if report.unread > 0 {
        diagnostic.notes.push(format!(
            "{} equation alternatives are not counted: their `requires` mentions a partial function or another operation that may be undefined, a lazy `&&` or `||` whose right operand may be, or a binder the pattern does not bind, or a binder occurs twice in the pattern",
            report.unread
        ));
    }
    if report.contexts > 0 {
        diagnostic.notes.push(format!(
            "{} equations read the configuration (a function context) and are not counted",
            report.contexts
        ));
    }
    if raw {
        diagnostic.notes.push(
            "the definition has `raw_k!` sentences, which the check does not read".to_owned(),
        );
    }
    diagnostic.help.push(
        "add equations for the missing arguments, an `#[k::equation(owise)]` equation, declare the function `partial`, or state the gap with `#[k::function(total, underspecified = \"..\", ..)]`"
            .to_owned(),
    );
    diagnostic
}

fn stale_warning(
    production: &SemanticProduction,
    attribute: &ProductionAttribute<Sort, StableItemId>,
) -> Diagnostic {
    let mut diagnostic = Diagnostic::error(
        codes::analysis::STALE_UNDERSPECIFIED,
        format!(
            "`{}` states `underspecified`, but its equations define every argument; remove `underspecified`",
            display_name(production.id())
        ),
        location(attribute.origin()),
    );
    diagnostic.severity = Severity::Warning;
    diagnostic
}

mod overlap;
pub(crate) use overlap::{EquationSignature, symbolic_overlap};

#[cfg(test)]
mod tests;
