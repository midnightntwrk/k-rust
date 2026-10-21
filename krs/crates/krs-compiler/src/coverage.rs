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
//! with integer constants, the order of two integers, and opaque atoms). The
//! abstraction only ever admits more valuations than exist, so it never calls
//! an uncovered argument covered; it can miss facts (the range of a function,
//! say) and then reports a gap that does not exist.
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

use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use krs_diagnostic::{Diagnostic, Location, Severity, codes};
use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, GeneratedOperation, GrammarProductionItemKind,
    GuardMeaning, ItemKind, ProductionAttribute, SemanticId, SemanticIdKind, SentenceKind,
    StableItemId,
};
use krs_ir_levels::{
    IrCondition, SemanticModule, SemanticProduction, SemanticRule, SemanticSortRef as Sort,
    SemanticTerm, SemanticTermKind,
};
use num_bigint::BigInt;

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

/// The coverage warnings of a lowered definition's modules, in production order.
#[must_use]
pub fn coverage_warnings(modules: &[SemanticModule]) -> Vec<Diagnostic> {
    let signature = Signature::new(modules);
    let raw = modules
        .iter()
        .any(|module| !module.raw_sentences().is_empty());
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
    let mut warnings = Vec::new();
    for production in modules.iter().flat_map(SemanticModule::productions) {
        if !checked(production) {
            continue;
        }
        let Some(rules) = equations.get(production.id()) else {
            continue;
        };
        let stated = production
            .attributes()
            .iter()
            .find(|attribute| matches!(attribute, ProductionAttribute::Underspecified { .. }));
        let mut uncovered = Vec::new();
        let mut decided = true;
        for (instance, rules) in instances(rules) {
            match check_instance(&signature, production, &instance, &rules) {
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
                    warnings.push(uncovered_warning(production, &instance, &report, raw));
                }
            }
            _ => {}
        }
    }
    warnings
}

/// Whether the lint judges a production: a total function the backend or
/// the SMT solver does not define.
fn checked(production: &SemanticProduction) -> bool {
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
struct Signature {
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
/// `None` when the guard mentions a term that may be undefined or a binder
/// the pattern does not bind: such an equation covers nothing the lint can
/// see.
struct GuardReader<'r> {
    signature: &'r Signature,
    paths: &'r BTreeMap<SemanticId, Path>,
    names: Names,
    projections: Projections,
}

/// How a guard subject reads bits of another subject, its base.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Projection {
    /// `bitRangeInt(base, offset, length)`.
    BitRange { offset: BigInt, length: BigInt },
    /// `base &Int mask`, with a non-negative mask.
    Mask(BigInt),
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

impl GuardReader<'_> {
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
        if Self::constant(term).is_none()
            && let Some((base, projection)) = Self::projection(term)
        {
            let (base_key, base_text) = self.canonical(base)?;
            self.names.entry(base_key.clone()).or_insert(base_text);
            self.projections
                .entry(key.clone())
                .or_insert((base_key, projection));
        }
        Some(key)
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

    /// The canonical text and the rendering of a term, if it is defined
    /// everywhere: binders, literals, constructors, total functions, total
    /// builtins, and `k::is!`.
    fn canonical(&self, term: &SemanticTerm) -> Option<(String, String)> {
        if let Some(constant) = Self::constant(term) {
            let text = constant.to_string();
            return Some((text.clone(), text));
        }
        let list = |reader: &Self, arguments: &mut dyn Iterator<Item = &SemanticTerm>| {
            let mut keys = Vec::new();
            let mut texts = Vec::new();
            for argument in arguments {
                let (key, text) = reader.canonical(argument)?;
                keys.push(key);
                texts.push(text);
            }
            Some((keys.join(", "), texts.join(", ")))
        };
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
                            return None;
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
                let (keys, texts) = list(self, &mut arguments.iter())?;
                Some((
                    format!("{head_key}({keys})"),
                    format!("{head_text}({texts})"),
                ))
            }
            SemanticTermKind::Map(operands) => {
                let operation = operands.operation();
                if !operation.is_total() {
                    return None;
                }
                let (keys, texts) = list(self, &mut operands.operands())?;
                Some((
                    format!("map:{operation:?}({keys})"),
                    format!("map::{}({texts})", snake_case(&format!("{operation:?}"))),
                ))
            }
            SemanticTermKind::List(operands) => {
                let operation = operands.operation();
                if !operation.is_total() {
                    return None;
                }
                let (keys, texts) = list(self, &mut operands.operands())?;
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
                let (keys, texts) = list(self, &mut operands.operands())?;
                Some((
                    format!("set:{operation:?}({keys})"),
                    format!("set::{}({texts})", snake_case(&format!("{operation:?}"))),
                ))
            }
            _ => None,
        }
    }

    /// Reads a Bool guard term.
    fn formula(&mut self, term: &SemanticTerm) -> Option<Formula> {
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
                (GuardMeaning::Negation, [operand]) => return Some(self.formula(operand)?.not()),
                (GuardMeaning::Conjunction, [left, right]) => {
                    return Some(Formula::And(
                        Box::new(self.formula(left)?),
                        Box::new(self.formula(right)?),
                    ));
                }
                (GuardMeaning::Disjunction, [left, right]) => {
                    return Some(Formula::Or(
                        Box::new(self.formula(left)?),
                        Box::new(self.formula(right)?),
                    ));
                }
                (GuardMeaning::Implication, [left, right]) => {
                    return Some(Formula::Or(
                        Box::new(self.formula(left)?.not()),
                        Box::new(self.formula(right)?),
                    ));
                }
                (GuardMeaning::Relation(literal), [first, second]) => {
                    let (left, right) = if literal.swapped {
                        (second, first)
                    } else {
                        (first, second)
                    };
                    let atom = self.relation(literal.relation, left, right)?;
                    return Some(if literal.positive { atom } else { atom.not() });
                }
                _ => {}
            }
        }
        Some(Formula::Atom(Atom::Opaque(self.subject(term)?)))
    }

    /// A positive literal of a canonical relation.
    fn relation(
        &mut self,
        relation: BuiltinOperation,
        left: &SemanticTerm,
        right: &SemanticTerm,
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
                    (None, Some(constant)) => Some(Formula::Atom(Atom::Bound {
                        subject: self.subject(left)?,
                        bound: if equal { Bound::At } else { Bound::Below },
                        constant,
                    })),
                    (Some(constant), None) => Some(Formula::Atom(Atom::Bound {
                        subject: self.subject(right)?,
                        bound: if equal { Bound::At } else { Bound::Above },
                        constant,
                    })),
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
                        let formula = self.formula(left)?;
                        Some(if value { formula } else { formula.not() })
                    }
                    (Some(value), None) => {
                        let formula = self.formula(right)?;
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

// ---------------------------------------------------------------------------
// Deciding guards

/// What the patterns already fix about an Int path on a branch.
#[derive(Clone, Debug)]
pub(crate) enum Fact {
    Equal(BigInt),
    Excluded(BTreeSet<BigInt>),
}

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

impl Counterexample {
    /// Whether a subject or atom of the counterexample reads the argument at `path`.
    fn mentions(&self, path: &[usize]) -> bool {
        let needle = path_text(path);
        let reads = |text: &String| {
            text.match_indices(&needle).any(|(start, _)| {
                !matches!(
                    text[start + needle.len()..].chars().next(),
                    Some(next) if next.is_ascii_digit()
                )
            })
        };
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
            regions
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

/// Whether some guard holds under every valuation consistent with `facts`
/// (keyed by the path text of an Int binder).
///
/// Sound: every real valuation of the subjects gives each atom the value it
/// has under one of the enumerated valuations. An Int subject's bounds
/// change truth only at their constants, so the constants and one point
/// between each pair realize every assignment; two subjects are always in
/// exactly one of three orders; distinct subjects are treated as
/// independent, which admits more valuations than exist, never fewer.
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
    decide_counted(guards, facts, projections).0
}

/// [`decide`], with the number of valuations it had to consider.
fn decide_counted(
    guards: &[&Formula],
    facts: &BTreeMap<String, Fact>,
    projections: &Projections,
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
    for index in 0..count {
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
        let mut truths = BTreeMap::new();
        for key in &opaque {
            truths.insert(*key, rest % 2 == 1);
            rest /= 2;
        }
        if !guards
            .iter()
            .any(|guard| evaluate(guard, &values, &orders, &truths))
        {
            return (
                Verdict::Refuted(counterexample(
                    values,
                    orders,
                    truths,
                    &regions,
                    projections,
                )),
                index + 1,
            );
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
            .filter(|row| matches!(&row.patterns[0], Pattern::Binder(sort) if self.signature.binder_covers(sort, head)))
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
                .is_some_and(|condition| condition.mentions(&column.path));
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
        let (verdict, valuations) = decide_counted(&guards, facts, self.projections);
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
}

fn check_instance(
    signature: &Signature,
    production: &SemanticProduction,
    instance: &[Sort],
    rules: &[&SemanticRule],
) -> Outcome {
    let columns = instantiate(
        &production_argument_sorts(production),
        production.parameters(),
        instance,
    )
    .into_iter()
    .enumerate()
    .map(|(index, sort)| Column {
        sort,
        path: vec![index],
    })
    .collect::<Vec<_>>();
    let mut rows = Vec::new();
    let mut names = Names::new();
    let mut projections = Projections::new();
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
            let guard = match rule.requires() {
                None => None,
                Some(IrCondition::Bool(condition)) => {
                    let mut reader = GuardReader {
                        signature,
                        paths: &paths,
                        names: Names::new(),
                        projections: Projections::new(),
                    };
                    let Some(formula) = reader.formula(condition.term()) else {
                        unread += 1;
                        continue;
                    };
                    for (key, text) in reader.names {
                        names.entry(key).or_insert(text);
                    }
                    for (key, projection) in reader.projections {
                        projections.entry(key).or_insert(projection);
                    }
                    Some(Rc::new(formula))
                }
                Some(IrCondition::Predicate(_)) => {
                    unread += 1;
                    continue;
                }
            };
            rows.push(Row { patterns, guard });
        }
    }
    let mut search = Search {
        signature,
        projections: &projections,
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

/// Renders a witness vector, naming a top-level argument the guards
/// constrain by its binder.
fn render_application(head: &str, gap: &Gap, binders: &BTreeMap<Path, String>) -> String {
    let arguments = gap
        .values
        .iter()
        .enumerate()
        .map(
            |(index, witness)| match (witness, &gap.condition, binders.get(&vec![index])) {
                (Witness::Any, Some(condition), Some(name)) if condition.mentions(&[index]) => {
                    name.clone()
                }
                _ => render(witness),
            },
        )
        .collect::<Vec<_>>();
    format!("{head}({})", arguments.join(", "))
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
        let application = render_application(&head, gap, &report.binders);
        match &gap.condition {
            Some(condition) => {
                let condition = render_condition(condition, &report.names);
                if condition.is_empty() {
                    format!("`{application}`")
                } else {
                    format!("`{application}` when {condition}")
                }
            }
            None => format!("`{application}`"),
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
    if report.guarded > 0 {
        diagnostic.notes.push(format!(
            "{} of its equations have `requires`; KRS decides a `requires` only as a Boolean combination of comparisons with integer constants and between two integers, reading the bits that comparisons of `bitRangeInt` and `&Int` fix, and only when every operation in it is defined on every argument",
            report.guarded
        ));
    }
    if report.unread > 0 {
        diagnostic.notes.push(format!(
            "{} equation alternatives are not counted: their `requires` mentions an operation that may be undefined or a binder the pattern does not bind, or a binder occurs twice in the pattern",
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

#[cfg(test)]
mod tests;
