//! Where a partial construct has a value, and the test that states it (NT-37).
//!
//! Some constructs denote a value only on part of their domain:
//!
//! - a sort projection `{t}:>S` (`k::project!(S, t)`), and a collection read KRS projects to a
//!   sort `S` below the `KItem` K's read returns, where `t` (the read) has sort `S`;
//! - a builtin operation whose domain the catalog states as facts over its operands
//!   ([`krs_ir::OperationDomain`]): a map lookup `m [ k ]` where `k` is a key of `m`, a list
//!   read `l [ i ]` where `i` is an index of `l` (`-size(l) <= i < size(l)`: a negative index
//!   counts from the end), a division where the divisor is not zero, a shift where the amount is
//!   not negative, a byte read at an index of the bytes, and every other the catalog lists;
//! - a `let` statement whose pattern may not match its value, where it matches.
//!
//! An application of a user function is not among them: a function's equations state where it
//! has a value, and a condition that applies a partial one has none where the function has none,
//! which is the author's to guard.
//!
//! A sentence's condition holds where it is true. Where a construct it evaluates has no value the
//! condition has none, so it does not hold, and the sentence does not apply. A backend that
//! evaluates the condition reaches the construct before it knows that, and the routes then
//! disagree: Java K's LLVM backend aborts, k-rust leaves the term undefined, and the symbolic
//! backends read `#Bottom`. So the condition states each construct's test before the construct,
//! joined with `andThenBool`, which every route evaluates first: where the test fails the
//! condition is `false`, where it holds the construct has its value, and the condition holds
//! exactly where it held before, under KRS's reading of the connectives, in which an operand's
//! definedness is part of the value of `&&`, `||` and `!` whether or not it is evaluated.
//!
//! The test stands where `false` and "no value" mean the same thing: a conjunct of the
//! condition's top-level conjunction (an operand of `andThenBool` or `andBool` there), or the body
//! of a `#let` that stands there. Below a negation, a disjunction or any other operation, `false`
//! may make the condition hold where the construct has no value, so a construct there is tested
//! at the conjunct that holds it. A conjunct that an earlier conjunct of the same chain already
//! tests needs no test of its own: `k::is!(Int, x) && k::project!(Int, x) > 0` is guarded as
//! written, and so is `0 <= i && l[i] > 0`'s lower bound, which `0 <=Int I` implies. A test an
//! author writes below `!` or `||` in the conjunct that evaluates the construct protects nothing
//! there ([`dead_tests`]).
//!
//! A pattern that matches evaluated terms (a transition's, a context's, an equation's) evaluates
//! what it computes before the condition, so it holds no partial construct: a lowering that would
//! put one there writes a fresh name the condition equates with the construct's value instead. A
//! concatenation of sets there is matched, not built, and has no domain to test.
//!
//! A result is not tested: where a construct in it has no value, the sentence applies (its
//! pattern matched and its condition held) and its result has no value, which every route ends
//! on; a test would make the sentence not apply there, and another sentence (an `owise` one, a
//! lower priority) apply in its place, which the author did not write. A claim's start state and
//! its `ensures` are not tested either: a start state with no value denotes no state, so the
//! claim states nothing there, as `requires isS(t)` would make it; and `ensures` with no value
//! is `ensures false`, as a test would make it.
//!
//! [`unguarded`] is the structural check of that rule over one sentence. It checks where each
//! test stands, from [`requirements`] and [`Requirement::test`], which the guarding pass shares,
//! so it does not check the tests themselves: the unit tests below pin each test by hand.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, DomainFact, DomainTerm, GeneratedOperation,
    ItemKind, NodeOrigin, OperationDomain, OperationSort, ProductionAttribute, SemanticId,
    SemanticIdKind, SentenceKind, StableItemId,
};

use crate::{
    IrTermKind, ListOperands, MapOperands, RuleBodyRef, SemanticCondition, SemanticModule,
    SemanticRule, SemanticSortRef, SemanticTerm, SetOperands, SortParameterId,
};

/// The sorts a test reads: the framework's `KItem`, the sort a projected read has when nothing
/// projects it; the subsort graph a `let` pattern's refutability is read with; and the sorts
/// whose values are one constructor's, whose record pattern of names matches every value.
#[derive(Clone, Debug)]
pub struct Sorts {
    k_item: SemanticSortRef,
    parents: BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>,
    records: BTreeMap<SemanticSortRef, (StableItemId, Vec<SemanticSortRef>)>,
    /// The field sorts of each constructor, which a pattern's name below it needs no test of.
    fields: BTreeMap<StableItemId, Vec<SemanticSortRef>>,
}

impl Sorts {
    /// The sorts of `k_item` and the subsort edges `(subsort, supersort)`, with no sort of one
    /// constructor.
    #[must_use]
    pub fn new(
        k_item: SemanticSortRef,
        edges: impl IntoIterator<Item = (SemanticSortRef, SemanticSortRef)>,
    ) -> Self {
        let mut parents = BTreeMap::<_, BTreeSet<_>>::new();
        for (subsort, supersort) in edges {
            parents.entry(subsort).or_default().insert(supersort);
        }
        Self {
            k_item,
            parents,
            records: BTreeMap::new(),
            fields: BTreeMap::new(),
        }
    }

    /// The sorts of a theory's modules: the one judge the guarding pass and the theory's
    /// validation read.
    ///
    /// A theory that declares no framework `KItem` has no term of that sort, so a sort
    /// parameter, which no term has either, stands in its place: every requirement and test
    /// that compares a term's sort with `KItem` then reads it as a theory with `KItem` reads a
    /// term of another sort, and whether a partial construct has a value does not depend on
    /// which sorts the theory declares. The one test that gives a term the sort `KItem`, a
    /// projected read's ([`Requirement::test`]), does not arise there: such a read is K's read
    /// of a `KItem`, so a theory that holds one keeps the framework module and its `KItem`.
    #[must_use]
    pub fn of_modules(modules: &[SemanticModule]) -> Self {
        let k_item = framework_k_item(modules)
            .unwrap_or_else(|| SemanticSortRef::Parameter(SortParameterId::new("KItem")));
        let mut sorts = Self::new(
            k_item,
            modules
                .iter()
                .flat_map(SemanticModule::subsorts)
                .map(|edge| (edge.subsort().clone(), edge.supersort().clone())),
        );
        let below = sorts
            .parents
            .values()
            .flatten()
            .cloned()
            .collect::<BTreeSet<_>>();
        let mut values = BTreeMap::<SemanticSortRef, Vec<&crate::SemanticProduction>>::new();
        let mut parametric = false;
        for production in modules.iter().flat_map(SemanticModule::productions) {
            if !builds_values(production) {
                continue;
            }
            if matches!(production.result_sort(), SemanticSortRef::Parameter(_)) {
                parametric = true;
            } else if production.id().item_kind() == ItemKind::Constructor
                && production.parameters().is_empty()
            {
                sorts
                    .fields
                    .insert(production.id().clone(), field_sorts(production));
            }
            values
                .entry(production.result_sort().clone())
                .or_default()
                .push(production);
        }
        if !parametric {
            for (sort, productions) in values {
                if let ([production], SemanticSortRef::Declared(_)) = (&productions[..], &sort)
                    && !below.contains(&sort)
                    && production.id().item_kind() == ItemKind::Constructor
                    && production.parameters().is_empty()
                    && !production
                        .attributes()
                        .iter()
                        .any(|attribute| matches!(attribute, ProductionAttribute::Token { .. }))
                {
                    let fields = field_sorts(production);
                    sorts
                        .records
                        .insert(sort, (production.id().clone(), fields));
                }
            }
        }
        sorts
    }

    /// The framework's `KItem`.
    #[must_use]
    pub const fn k_item(&self) -> &SemanticSortRef {
        &self.k_item
    }

    /// Whether a term of `candidate` may stand where `expected` is required: equal sorts, a
    /// subsort edge path, or `KItem` above every sort but `K` and a sort parameter.
    #[must_use]
    pub fn is_subsort(&self, candidate: &SemanticSortRef, expected: &SemanticSortRef) -> bool {
        let below_k_item = |sort: &SemanticSortRef| {
            !matches!(
                sort,
                SemanticSortRef::Builtin(BuiltinSort::KSequence) | SemanticSortRef::Parameter(_)
            )
        };
        if *expected == self.k_item && below_k_item(candidate) {
            return true;
        }
        let mut pending = vec![candidate];
        let mut visited = BTreeSet::new();
        while let Some(sort) = pending.pop() {
            if sort == expected {
                return true;
            }
            if visited.insert(sort) {
                pending.extend(self.parents.get(sort).into_iter().flatten());
            }
        }
        false
    }
}

/// The sorts of a production's arguments, in order.
fn field_sorts(production: &crate::SemanticProduction) -> Vec<SemanticSortRef> {
    production
        .items()
        .iter()
        .filter_map(|item| match item.kind() {
            krs_ir::GrammarProductionItemKind::NonTerminal { sort, .. } => Some(sort.clone()),
            _ => None,
        })
        .collect()
}

/// Whether a production builds values of its sort: neither a function nor a hook, an alias, a
/// desugar or a bracket, each of which stands for a term another production builds.
#[must_use]
pub fn builds_values(production: &crate::SemanticProduction) -> bool {
    !production.attributes().iter().any(|attribute| {
        matches!(
            attribute,
            ProductionAttribute::Function { .. }
                | ProductionAttribute::Hook { .. }
                | ProductionAttribute::RawHook { .. }
                | ProductionAttribute::Alias { .. }
                | ProductionAttribute::Desugar { .. }
                | ProductionAttribute::Bracket { .. }
        )
    })
}

/// The framework's `KItem` sort, when the modules declare it.
pub(crate) fn framework_k_item(modules: &[SemanticModule]) -> Option<SemanticSortRef> {
    modules
        .iter()
        .flat_map(SemanticModule::sorts)
        .map(crate::SemanticSort::id)
        .filter(|id| is_framework_k_item(id))
        .min()
        .cloned()
        .map(SemanticSortRef::Declared)
}

/// Recognises the framework's `KItem` sort declaration (`k::KItem`).
pub(crate) fn is_framework_k_item(id: &StableItemId) -> bool {
    is_framework_sort(id) && id.item_name() == "KItem"
}

/// Recognises a sort the framework declares (`k::KItem`, `k::KResult`).
#[must_use]
pub fn is_framework_sort(id: &StableItemId) -> bool {
    id.item_kind() == ItemKind::Sort
        && id.package().k_namespace() == "KRS-FRAMEWORK"
        && id.package().cargo_name() == "krs"
        && id.package().cargo_source() == "framework"
}

/// One fact a partial construct needs before it is evaluated.
#[derive(Clone, Copy, Debug)]
pub enum Requirement<'a> {
    /// `isS(t)`: the projection `{t}:>S` has a value. `read` marks a collection read KRS
    /// projects, whose test reads it at `KItem`, the sort K's read has.
    Sort {
        /// The projection's sort.
        sort: &'a SemanticSortRef,
        /// The projected term.
        operand: &'a SemanticTerm,
        /// Whether the operand is a read KRS projects.
        read: bool,
    },
    /// One fact of a builtin operation's domain, over the operands of `construct`.
    Domain {
        /// The fact, from the catalog.
        fact: DomainFact,
        /// The operation's application.
        construct: &'a SemanticTerm,
    },
    /// The statement `let P = v;` matches: `isS(v)` for a name of sort `S`, otherwise `P' :=K v`,
    /// `P'` being `P` with each name a wildcard, or an anonymous name of its sort where its
    /// position does not give it that sort.
    Match {
        /// The statement's pattern.
        pattern: &'a SemanticTerm,
        /// The statement's value.
        value: &'a SemanticTerm,
    },
}

/// The facts the construct at `term`'s root needs, in the order they must hold; empty for a
/// term that has a value wherever its operands have one. `projected` is false for the operand of
/// a generated sort operation, which the operation reads unprojected. A domain fact its literal
/// operands decide is left out.
#[must_use]
pub fn requirements<'a>(
    term: &'a SemanticTerm,
    projected: bool,
    sorts: &Sorts,
) -> Vec<Requirement<'a>> {
    let read_sort = || {
        (projected && term.sort() != &sorts.k_item).then(|| Requirement::Sort {
            sort: term.sort(),
            operand: term,
            read: true,
        })
    };
    let domain = |domain: OperationDomain| {
        let OperationDomain::Where(facts) = domain else {
            return Vec::new();
        };
        let bounds = Bounds::default();
        facts
            .iter()
            .filter(|fact| bounds.decide(**fact, term) != Some(true))
            .map(|fact| Requirement::Domain {
                fact: *fact,
                construct: term,
            })
            .collect::<Vec<_>>()
    };
    match term.kind() {
        IrTermKind::Application {
            application: ApplicationRef::Generated(GeneratedOperation::SortProjection(sort)),
            arguments,
            ..
        } => arguments
            .first()
            .map(|operand| Requirement::Sort {
                sort,
                operand,
                read: false,
            })
            .into_iter()
            .collect(),
        IrTermKind::Application {
            application: ApplicationRef::Builtin(operation),
            ..
        } => domain(operation.domain()),
        IrTermKind::Map(operands) => {
            let mut needed = domain(operands.operation().domain());
            if matches!(
                &**operands,
                MapOperands::Get { .. } | MapOperands::GetOrDefault { .. }
            ) {
                needed.extend(read_sort());
            }
            needed
        }
        IrTermKind::List(operands) => {
            let mut needed = domain(operands.operation().domain());
            if matches!(&**operands, ListOperands::Get { .. }) {
                needed.extend(read_sort());
            }
            needed
        }
        IrTermKind::Set(operands) => domain(operands.operation().domain()),
        IrTermKind::Let { pattern, value, .. } if !irrefutable(pattern, value.sort(), sorts) => {
            vec![Requirement::Match { pattern, value }]
        }
        _ => Vec::new(),
    }
}

/// Whether a `let` pattern matches every value of `value`'s sort: a name of that sort or above,
/// or a record of such names of a sort whose values are one constructor's.
#[must_use]
pub fn irrefutable(pattern: &SemanticTerm, value: &SemanticSortRef, sorts: &Sorts) -> bool {
    match pattern.kind() {
        IrTermKind::Variable { .. } => sorts.is_subsort(value, pattern.sort()),
        IrTermKind::Application {
            application: ApplicationRef::Declared(constructor),
            arguments,
            ..
        } => sorts.records.get(value).is_some_and(|(only, fields)| {
            only == constructor
                && fields.len() == arguments.len()
                && fields
                    .iter()
                    .zip(arguments)
                    .all(|(field, argument)| irrefutable(argument, field, sorts))
        }),
        _ => false,
    }
}

/// The operands of a builtin or collection application, in the catalog's operand order.
fn operation_operands(term: &SemanticTerm) -> Vec<&SemanticTerm> {
    match term.kind() {
        IrTermKind::Application { arguments, .. } => arguments.iter().collect(),
        IrTermKind::Map(operands) => operands.operands().collect(),
        IrTermKind::List(operands) => operands.operands().collect(),
        IrTermKind::Set(operands) => operands.operands().collect(),
        _ => Vec::new(),
    }
}

/// The length operation of the operand at `position` of `construct`: `lengthBytes`,
/// `lengthString`, or a list's `size`.
#[derive(Clone, Copy)]
enum Length {
    Bytes,
    String,
    List,
}

fn length_of(construct: &SemanticTerm, position: usize) -> Length {
    match construct.kind() {
        IrTermKind::Application {
            application: ApplicationRef::Builtin(operation),
            ..
        } => match operation.spec().argument_sorts.get(position) {
            Some(OperationSort::Builtin(BuiltinSort::String)) => Length::String,
            Some(OperationSort::Builtin(BuiltinSort::List)) => Length::List,
            _ => Length::Bytes,
        },
        _ => Length::List,
    }
}

/// The first operand position a domain term reads.
const fn first_operand(term: DomainTerm) -> Option<usize> {
    match term {
        DomainTerm::Operand(position) | DomainTerm::Length(position) => Some(position),
        DomainTerm::Int(_) => None,
        DomainTerm::Difference(left, right) | DomainTerm::Sum(left, right) => {
            match first_operand(*left) {
                Some(position) => Some(position),
                None => first_operand(*right),
            }
        }
    }
}

/// The operand positions a fact reads, in order.
fn fact_operands(fact: DomainFact) -> Vec<usize> {
    let mut positions = Vec::new();
    let term = |term: DomainTerm, positions: &mut Vec<usize>| {
        let mut pending = vec![term];
        while let Some(term) = pending.pop() {
            match term {
                DomainTerm::Operand(position) | DomainTerm::Length(position) => {
                    positions.push(position);
                }
                DomainTerm::Int(_) => {}
                DomainTerm::Difference(left, right) | DomainTerm::Sum(left, right) => {
                    pending.push(*right);
                    pending.push(*left);
                }
            }
        }
    };
    match fact {
        DomainFact::Less(left, right)
        | DomainFact::AtMost(left, right)
        | DomainFact::Equal(left, right) => {
            term(left, &mut positions);
            term(right, &mut positions);
        }
        DomainFact::NonZero(operand) => term(operand, &mut positions),
        DomainFact::KeyOf { key, map } => positions.extend([key, map]),
        DomainFact::Disjoint { left, right } => positions.extend([left, right]),
        DomainFact::OneOf { operand, .. } => positions.push(operand),
    }
    positions
}

/// The operand a fact is about: the first it reads as itself (an index, a divisor, a key), else
/// the first whose length it reads.
fn subject_position(fact: DomainFact) -> Option<usize> {
    fn direct(term: DomainTerm) -> Option<usize> {
        match term {
            DomainTerm::Operand(position) => Some(position),
            DomainTerm::Int(_) | DomainTerm::Length(_) => None,
            DomainTerm::Difference(left, right) | DomainTerm::Sum(left, right) => {
                direct(*left).or_else(|| direct(*right))
            }
        }
    }
    let terms = match fact {
        DomainFact::Less(left, right)
        | DomainFact::AtMost(left, right)
        | DomainFact::Equal(left, right) => vec![left, right],
        DomainFact::NonZero(operand) => vec![operand],
        DomainFact::KeyOf { key, .. } => return Some(key),
        DomainFact::Disjoint { left, .. } => return Some(left),
        DomainFact::OneOf { operand, .. } => return Some(operand),
    };
    terms
        .iter()
        .find_map(|term| direct(*term))
        .or_else(|| fact_operands(fact).first().copied())
}

impl<'a> Requirement<'a> {
    /// The construct whose value the requirement states, where a failure is located: the
    /// projected term, the first operand a domain fact reads, the `let`'s value.
    #[must_use]
    pub fn subject(&self) -> &'a SemanticTerm {
        match self {
            Self::Sort { operand, .. } => operand,
            Self::Domain { fact, construct } => subject_position(*fact)
                .and_then(|position| operation_operands(construct).get(position).copied())
                .unwrap_or(construct),
            Self::Match { value, .. } => value,
        }
    }

    /// The terms the test reads, whose names the test needs in scope.
    #[must_use]
    pub fn operands(&self) -> Vec<&'a SemanticTerm> {
        match self {
            Self::Sort { operand, .. } => vec![operand],
            Self::Domain { fact, construct } => {
                let operands = operation_operands(construct);
                fact_operands(*fact)
                    .into_iter()
                    .filter_map(|position| operands.get(position).copied())
                    .collect()
            }
            Self::Match { value, .. } => vec![value],
        }
    }

    /// The test: a Bool term that holds exactly where the requirement does. `copy` gives each
    /// copied node of the construct its origin in the test, and `fresh` each node the test adds
    /// (`at` is the node it stands for); `wildcard` names a pattern's name in the test: a
    /// wildcard, or, when the flag is set, an anonymous name of the sort.
    pub fn test(
        &self,
        sorts: &Sorts,
        copy: &mut dyn FnMut(&NodeOrigin) -> NodeOrigin,
        fresh: &mut dyn FnMut(&NodeOrigin) -> NodeOrigin,
        wildcard: &mut dyn FnMut(&SemanticSortRef, bool) -> SemanticId,
    ) -> SemanticTerm {
        let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
        let copied = |term: &SemanticTerm, copy: &mut dyn FnMut(&NodeOrigin) -> NodeOrigin| {
            term.map_origins(&mut |origin| copy(origin))
        };
        match *self {
            Self::Sort {
                sort,
                operand,
                read,
            } => {
                let mut tested = copied(operand, copy);
                if read {
                    tested.sort = sorts.k_item.clone();
                }
                SemanticTerm::application(
                    fresh(operand.origin()),
                    bool_sort,
                    ApplicationRef::Generated(GeneratedOperation::SortPredicate(sort.clone())),
                    vec![tested],
                )
            }
            Self::Domain { fact, construct } => Facts {
                construct,
                operands: operation_operands(construct),
                subject: self.subject(),
                copy,
                fresh,
            }
            .fact(fact),
            Self::Match { pattern, value }
                if matches!(pattern.kind(), IrTermKind::Variable { .. }) =>
            {
                SemanticTerm::application(
                    fresh(value.origin()),
                    bool_sort,
                    ApplicationRef::Generated(GeneratedOperation::SortPredicate(
                        pattern.sort().clone(),
                    )),
                    vec![copied(value, copy)],
                )
            }
            Self::Match { pattern, value } => SemanticTerm::matches(
                fresh(value.origin()),
                bool_sort,
                copied(value, copy),
                wildcarded(&copied(pattern, copy), None, sorts, wildcard),
                Vec::new(),
            ),
        }
    }

    /// Whether `facts`, the conjuncts that hold where the construct is evaluated, state this
    /// requirement: one of them is its test, or, for a domain fact over Ints, their bounds of
    /// its operands by constants decide it (`W >Int 0` gives `1 <<Int (W -Int 1)` its amount).
    #[must_use]
    pub fn established_by(&self, facts: &[&SemanticTerm], sorts: &Sorts) -> bool {
        if facts.iter().any(|fact| self.holds_by(fact, sorts)) {
            return true;
        }
        let Self::Domain { fact, construct } = *self else {
            return false;
        };
        Bounds::of(facts).decide(fact, construct) == Some(true)
    }

    /// Whether `fact` is this requirement's test, up to origins and wildcard names.
    #[must_use]
    pub fn holds_by(&self, fact: &SemanticTerm, sorts: &Sorts) -> bool {
        let test = self.test(
            sorts,
            &mut NodeOrigin::clone,
            &mut NodeOrigin::clone,
            &mut |_, typed| test_name(typed, 0),
        );
        same(fact, &test)
    }

    /// What the construct is, for a message: `projection`, `lookup`, `list read`, `let`
    /// statement, or the operation's call.
    #[must_use]
    pub fn construct_name(&self) -> String {
        match self {
            Self::Sort { read: false, .. } => "projection".to_owned(),
            Self::Sort { read: true, .. } => {
                "read, which KRS projects to its position's sort,".to_owned()
            }
            Self::Domain { construct, .. } => match construct.kind() {
                IrTermKind::Map(_) => "lookup".to_owned(),
                IrTermKind::List(operands) if matches!(&**operands, ListOperands::Get { .. }) => {
                    "list read".to_owned()
                }
                IrTermKind::List(operands) => {
                    let spec = krs_ir::CollectionApplication::spec(operands.operation());
                    format!("`{}`", spec.description)
                }
                IrTermKind::Set(_) => "set concatenation".to_owned(),
                IrTermKind::Application {
                    application: ApplicationRef::Builtin(operation),
                    ..
                } => {
                    let spec = operation.spec();
                    format!("`{}::{}`", spec.rust_module, spec.rust_name)
                }
                _ => "operation".to_owned(),
            },
            Self::Match { .. } => "`let` statement".to_owned(),
        }
    }
}

/// The builder of one domain fact's test over a construct's operands.
struct Facts<'c, 'f> {
    construct: &'c SemanticTerm,
    operands: Vec<&'c SemanticTerm>,
    subject: &'c SemanticTerm,
    copy: &'f mut dyn FnMut(&NodeOrigin) -> NodeOrigin,
    fresh: &'f mut dyn FnMut(&NodeOrigin) -> NodeOrigin,
}

impl Facts<'_, '_> {
    fn operand(&self, position: usize) -> &SemanticTerm {
        self.operands
            .get(position)
            .copied()
            .unwrap_or(self.construct)
    }

    fn anchor(&self, term: DomainTerm) -> NodeOrigin {
        first_operand(term).map_or_else(
            || self.subject.origin().clone(),
            |position| self.operand(position).origin().clone(),
        )
    }

    fn int(&mut self, value: i64) -> SemanticTerm {
        SemanticTerm {
            origin: (self.fresh)(&self.subject.origin().clone()),
            sort: SemanticSortRef::Builtin(BuiltinSort::Int),
            kind: IrTermKind::Token {
                value: value.to_string(),
            },
        }
    }

    fn term(&mut self, term: DomainTerm) -> SemanticTerm {
        let int_sort = SemanticSortRef::Builtin(BuiltinSort::Int);
        match term {
            DomainTerm::Operand(position) => {
                let operand = self.operand(position).clone();
                operand.map_origins(&mut |origin| (self.copy)(origin))
            }
            DomainTerm::Int(value) => self.int(value),
            DomainTerm::Length(position) => {
                let operand = self.operand(position).clone();
                let copied = operand.map_origins(&mut |origin| (self.copy)(origin));
                let origin = (self.fresh)(operand.origin());
                match length_of(self.construct, position) {
                    Length::List => {
                        SemanticTerm::list(origin, int_sort, ListOperands::Size { list: copied })
                    }
                    Length::Bytes => SemanticTerm::application(
                        origin,
                        int_sort,
                        ApplicationRef::Builtin(BuiltinOperation::BytesLength),
                        vec![copied],
                    ),
                    Length::String => SemanticTerm::application(
                        origin,
                        int_sort,
                        ApplicationRef::Builtin(BuiltinOperation::StringLength),
                        vec![copied],
                    ),
                }
            }
            DomainTerm::Difference(left, right) | DomainTerm::Sum(left, right) => {
                let operation = if matches!(term, DomainTerm::Sum(..)) {
                    BuiltinOperation::IntAdd
                } else {
                    BuiltinOperation::IntSub
                };
                // The right operand first: a length before the literal it is subtracted from.
                let right = self.term(*right);
                let left = self.term(*left);
                let anchor = self.anchor(term);
                let origin = (self.fresh)(&anchor);
                SemanticTerm::application(
                    origin,
                    int_sort,
                    ApplicationRef::Builtin(operation),
                    vec![left, right],
                )
            }
        }
    }

    fn compare(
        &mut self,
        operation: BuiltinOperation,
        arguments: Vec<SemanticTerm>,
    ) -> SemanticTerm {
        SemanticTerm::application(
            (self.fresh)(&self.subject.origin().clone()),
            SemanticSortRef::Builtin(BuiltinSort::Bool),
            ApplicationRef::Builtin(operation),
            arguments,
        )
    }

    fn fact(&mut self, fact: DomainFact) -> SemanticTerm {
        let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
        match fact {
            DomainFact::Less(left, right) => {
                let (left, right) = (self.term(left), self.term(right));
                self.compare(BuiltinOperation::IntLess, vec![left, right])
            }
            DomainFact::AtMost(left, right) => {
                let (left, right) = (self.term(left), self.term(right));
                self.compare(BuiltinOperation::IntLessEqual, vec![left, right])
            }
            DomainFact::Equal(left, right) => {
                let (left, right) = (self.term(left), self.term(right));
                self.compare(BuiltinOperation::IntEqual, vec![left, right])
            }
            DomainFact::NonZero(operand) => {
                let operand = self.term(operand);
                let zero = self.int(0);
                self.compare(BuiltinOperation::IntNotEqual, vec![operand, zero])
            }
            DomainFact::KeyOf { key, map } => {
                let key = self.term(DomainTerm::Operand(key));
                let map = self.term(DomainTerm::Operand(map));
                SemanticTerm::typed_map(
                    (self.fresh)(&self.subject.origin().clone()),
                    bool_sort,
                    MapOperands::InKeys { key, map },
                )
            }
            DomainFact::Disjoint { left, right } => {
                let set_sort = SemanticSortRef::Builtin(BuiltinSort::Set);
                let left = self.term(DomainTerm::Operand(left));
                let right = self.term(DomainTerm::Operand(right));
                let common = SemanticTerm::set(
                    (self.fresh)(&self.subject.origin().clone()),
                    set_sort.clone(),
                    SetOperands::Intersect { left, right },
                );
                let empty = SemanticTerm::set(
                    (self.fresh)(&self.subject.origin().clone()),
                    set_sort,
                    SetOperands::Empty,
                );
                self.compare(BuiltinOperation::KEqualEq, vec![common, empty])
            }
            DomainFact::OneOf { operand, texts } => {
                let string_sort = SemanticSortRef::Builtin(BuiltinSort::String);
                let mut alternatives = texts.iter().map(|text| {
                    let operand = self.term(DomainTerm::Operand(operand));
                    let text = SemanticTerm {
                        origin: (self.fresh)(&self.subject.origin().clone()),
                        sort: string_sort.clone(),
                        kind: IrTermKind::Token {
                            value: format!("{text:?}"),
                        },
                    };
                    self.compare(BuiltinOperation::StringEqual, vec![operand, text])
                });
                let first = alternatives
                    .next()
                    .expect("a domain names at least one text");
                let rest = alternatives.collect::<Vec<_>>();
                rest.into_iter().fold(first, |either, next| {
                    SemanticTerm::application(
                        either.origin().clone(),
                        bool_sort.clone(),
                        ApplicationRef::Builtin(BuiltinOperation::BoolOrElse),
                        vec![either, next],
                    )
                })
            }
        }
    }
}

/// The bounds that conjuncts state of Int terms by constants: `x <op> c`, `c <op> x` and their
/// negations, `x` read as a base term plus a constant (`w -Int 1` is `w` and `-1`).
#[derive(Default)]
struct Bounds<'t> {
    bounds: Vec<(&'t SemanticTerm, Interval)>,
}

/// An interval of Ints with optional ends, and values it excludes.
#[derive(Clone, Debug, Default)]
struct Interval {
    low: Option<i128>,
    high: Option<i128>,
    excluded: Vec<i128>,
}

impl Interval {
    fn exactly(value: i128) -> Self {
        Self {
            low: Some(value),
            high: Some(value),
            excluded: Vec::new(),
        }
    }

    fn at_least(low: i128) -> Self {
        Self {
            low: Some(low),
            ..Self::default()
        }
    }

    fn meet(&mut self, other: &Self) {
        self.low = match (self.low, other.low) {
            (Some(a), Some(b)) => Some(a.max(b)),
            (a, b) => a.or(b),
        };
        self.high = match (self.high, other.high) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (a, b) => a.or(b),
        };
        self.excluded.extend(other.excluded.iter().copied());
    }

    fn shift(&self, offset: i128) -> Self {
        Self {
            low: self.low.and_then(|low| low.checked_add(offset)),
            high: self.high.and_then(|high| high.checked_add(offset)),
            excluded: self
                .excluded
                .iter()
                .filter_map(|value| value.checked_add(offset))
                .collect(),
        }
    }

    fn excludes_zero(&self) -> bool {
        self.low.is_some_and(|low| low > 0)
            || self.high.is_some_and(|high| high < 0)
            || self.excluded.contains(&0)
    }
}

/// An Int literal's value.
fn int_literal(term: &SemanticTerm) -> Option<i128> {
    match term.kind() {
        IrTermKind::Token { value }
            if *term.sort() == SemanticSortRef::Builtin(BuiltinSort::Int) =>
        {
            value.parse().ok()
        }
        _ => None,
    }
}

/// `term` as a base term and a constant offset: `t +Int c`, `t -Int c`, `c +Int t`.
fn offset(term: &SemanticTerm) -> (&SemanticTerm, i128) {
    if let IrTermKind::Application {
        application: ApplicationRef::Builtin(operation),
        arguments,
        ..
    } = term.kind()
        && let [left, right] = arguments.as_slice()
    {
        match operation {
            BuiltinOperation::IntAdd => {
                if let Some(constant) = int_literal(right) {
                    let (base, inner) = offset(left);
                    return (base, inner.saturating_add(constant));
                }
                if let Some(constant) = int_literal(left) {
                    let (base, inner) = offset(right);
                    return (base, inner.saturating_add(constant));
                }
            }
            BuiltinOperation::IntSub => {
                if let Some(constant) = int_literal(right) {
                    let (base, inner) = offset(left);
                    return (base, inner.saturating_sub(constant));
                }
            }
            _ => {}
        }
    }
    (term, 0)
}

impl<'t> Bounds<'t> {
    fn of(facts: &[&'t SemanticTerm]) -> Self {
        let mut bounds = Self::default();
        for fact in facts {
            bounds.read(fact, true);
        }
        bounds
    }

    /// Records what `fact` states when it holds (`positive`) or fails.
    fn read(&mut self, fact: &'t SemanticTerm, positive: bool) {
        let IrTermKind::Application {
            application: ApplicationRef::Builtin(operation),
            arguments,
            ..
        } = fact.kind()
        else {
            return;
        };
        if *operation == BuiltinOperation::BoolNot {
            if let [operand] = arguments.as_slice() {
                self.read(operand, !positive);
            }
            return;
        }
        let [left, right] = arguments.as_slice() else {
            return;
        };
        // `subject R constant`, with `R` read from the subject's side.
        let (subject, constant, operation) = match (int_literal(left), int_literal(right)) {
            (None, Some(constant)) => (left, constant, *operation),
            (Some(constant), None) => (
                right,
                constant,
                match operation {
                    BuiltinOperation::IntLess => BuiltinOperation::IntGreater,
                    BuiltinOperation::IntLessEqual => BuiltinOperation::IntGreaterEqual,
                    BuiltinOperation::IntGreater => BuiltinOperation::IntLess,
                    BuiltinOperation::IntGreaterEqual => BuiltinOperation::IntLessEqual,
                    other => *other,
                },
            ),
            _ => return,
        };
        let operation = if positive {
            operation
        } else {
            match operation {
                BuiltinOperation::IntLess => BuiltinOperation::IntGreaterEqual,
                BuiltinOperation::IntLessEqual => BuiltinOperation::IntGreater,
                BuiltinOperation::IntGreater => BuiltinOperation::IntLessEqual,
                BuiltinOperation::IntGreaterEqual => BuiltinOperation::IntLess,
                BuiltinOperation::IntEqual => BuiltinOperation::IntNotEqual,
                BuiltinOperation::IntNotEqual => BuiltinOperation::IntEqual,
                _ => return,
            }
        };
        let (base, shift) = offset(subject);
        let Some(constant) = constant.checked_sub(shift) else {
            return;
        };
        let interval = match operation {
            BuiltinOperation::IntLess => Interval {
                high: constant.checked_sub(1),
                ..Interval::default()
            },
            BuiltinOperation::IntLessEqual => Interval {
                high: Some(constant),
                ..Interval::default()
            },
            BuiltinOperation::IntGreater => Interval {
                low: constant.checked_add(1),
                ..Interval::default()
            },
            BuiltinOperation::IntGreaterEqual => Interval::at_least(constant),
            BuiltinOperation::IntEqual => Interval::exactly(constant),
            BuiltinOperation::IntNotEqual => Interval {
                excluded: vec![constant],
                ..Interval::default()
            },
            _ => return,
        };
        match self.bounds.iter_mut().find(|(known, _)| same(known, base)) {
            Some((_, known)) => known.meet(&interval),
            None => self.bounds.push((base, interval)),
        }
    }

    /// The interval an Int term is known to lie in.
    fn interval(&self, term: &SemanticTerm) -> Interval {
        if let Some(value) = int_literal(term) {
            return Interval::exactly(value);
        }
        let (base, shift) = offset(term);
        let mut interval = Interval::default();
        if let Some(value) = int_literal(base) {
            interval = Interval::exactly(value);
        }
        if is_length(base) {
            interval.meet(&Interval::at_least(0));
        }
        for (known, bound) in &self.bounds {
            if same(known, base) {
                interval.meet(bound);
            }
        }
        interval.shift(shift)
    }

    fn domain_interval(&self, term: DomainTerm, construct: &SemanticTerm) -> Interval {
        match term {
            DomainTerm::Operand(position) => operation_operands(construct)
                .get(position)
                .map_or_else(Interval::default, |operand| self.interval(operand)),
            DomainTerm::Int(value) => Interval::exactly(i128::from(value)),
            DomainTerm::Length(_) => Interval::at_least(0),
            DomainTerm::Difference(left, right) | DomainTerm::Sum(left, right) => {
                let left = self.domain_interval(*left, construct);
                let right = self.domain_interval(*right, construct);
                let (right_low, right_high) = if matches!(term, DomainTerm::Sum(..)) {
                    (right.low, right.high)
                } else {
                    (
                        right.high.and_then(i128::checked_neg),
                        right.low.and_then(i128::checked_neg),
                    )
                };
                Interval {
                    low: left.low.zip(right_low).and_then(|(a, b)| a.checked_add(b)),
                    high: left
                        .high
                        .zip(right_high)
                        .and_then(|(a, b)| a.checked_add(b)),
                    excluded: Vec::new(),
                }
            }
        }
    }

    /// Whether the bounds decide `fact` over `construct`'s operands.
    fn decide(&self, fact: DomainFact, construct: &SemanticTerm) -> Option<bool> {
        let interval = |term| self.domain_interval(term, construct);
        match fact {
            DomainFact::Less(left, right) | DomainFact::AtMost(left, right) => {
                let strict = matches!(fact, DomainFact::Less(..));
                let (left, right) = (interval(left), interval(right));
                let holds = left
                    .high
                    .zip(right.low)
                    .is_some_and(|(high, low)| if strict { high < low } else { high <= low });
                let fails = left
                    .low
                    .zip(right.high)
                    .is_some_and(|(low, high)| if strict { low >= high } else { low > high });
                if holds {
                    Some(true)
                } else if fails {
                    Some(false)
                } else {
                    None
                }
            }
            DomainFact::Equal(left, right) => {
                let (left, right) = (interval(left), interval(right));
                match (left.low, left.high, right.low, right.high) {
                    (Some(a), Some(b), Some(c), Some(d)) if a == b && c == d => Some(a == c),
                    _ => None,
                }
            }
            DomainFact::NonZero(operand) => {
                let operand = interval(operand);
                if operand.excludes_zero() {
                    Some(true)
                } else if operand.low == Some(0) && operand.high == Some(0) {
                    Some(false)
                } else {
                    None
                }
            }
            DomainFact::KeyOf { .. } | DomainFact::Disjoint { .. } | DomainFact::OneOf { .. } => {
                None
            }
        }
    }
}

/// Whether `term` is a length or a size, which is never negative.
fn is_length(term: &SemanticTerm) -> bool {
    match term.kind() {
        IrTermKind::Application {
            application:
                ApplicationRef::Builtin(BuiltinOperation::BytesLength | BuiltinOperation::StringLength),
            ..
        } => true,
        IrTermKind::List(operands) => matches!(&**operands, ListOperands::Size { .. }),
        IrTermKind::Map(operands) => matches!(&**operands, MapOperands::Size { .. }),
        IrTermKind::Set(operands) => matches!(&**operands, SetOperands::Size { .. }),
        _ => false,
    }
}

/// The name a test gives a pattern's name: the wildcard, or the anonymous name `_Krs_Defined` of
/// its sort, with `ordinal`.
///
/// # Panics
///
/// Never: an underscore-prefixed spelling with an ordinal is an identity.
#[must_use]
pub fn test_name(typed: bool, ordinal: usize) -> SemanticId {
    if typed {
        SemanticId::anonymous("_Krs_Defined", ordinal)
            .expect("an underscore-prefixed spelling with an ordinal is an identity")
    } else {
        SemanticId::wildcard(ordinal)
    }
}

/// `pattern` with each name it binds a wildcard, which K writes `_` and which takes its
/// position's sort, where `expected`, the sort of the field it stands in, is a subsort of the
/// name's; elsewhere an anonymous name of the name's sort (`wildcard(sort, true)`), so that the
/// test keeps the sort the pattern requires.
fn wildcarded(
    pattern: &SemanticTerm,
    expected: Option<&SemanticSortRef>,
    sorts: &Sorts,
    wildcard: &mut dyn FnMut(&SemanticSortRef, bool) -> SemanticId,
) -> SemanticTerm {
    if let IrTermKind::Variable { .. } = pattern.kind() {
        let typed = !(any_sort(pattern.sort(), sorts)
            || expected.is_some_and(|field| sorts.is_subsort(field, pattern.sort())));
        return pattern.with_kind(IrTermKind::Variable {
            variable: wildcard(pattern.sort(), typed),
        });
    }
    if let IrTermKind::Application {
        application: ApplicationRef::Declared(constructor),
        arguments,
        instance,
        head_instance_fixed,
    } = pattern.kind()
    {
        let fields = sorts.fields.get(constructor);
        let arguments = arguments
            .iter()
            .enumerate()
            .map(|(index, argument)| {
                wildcarded(
                    argument,
                    fields.and_then(|fields| fields.get(index)),
                    sorts,
                    wildcard,
                )
            })
            .collect();
        return pattern.with_kind(IrTermKind::Application {
            application: ApplicationRef::Declared(constructor.clone()),
            arguments,
            instance: instance.clone(),
            head_instance_fixed: *head_instance_fixed,
        });
    }
    // Below a collection or another node no field sort is known: a name of a sort every term has
    // is a wildcard there.
    let mut term = pattern.clone();
    rename(&mut term, &mut |_, sort| {
        Some(wildcard(sort, !any_sort(sort, sorts)))
    });
    term
}

/// Whether every term of a position has `sort`: `KItem` or `K`.
fn any_sort(sort: &SemanticSortRef, sorts: &Sorts) -> bool {
    *sort == sorts.k_item || *sort == SemanticSortRef::Builtin(BuiltinSort::KSequence)
}

/// Renames each variable of `term` that `name` gives a new identity, below every node but a
/// rewrite, an alias, a test and a block, which a `let` pattern does not hold.
pub fn rename(
    term: &mut SemanticTerm,
    name: &mut dyn FnMut(&SemanticId, &SemanticSortRef) -> Option<SemanticId>,
) {
    if let IrTermKind::Variable { variable } = &mut term.kind {
        if let Some(renamed) = name(variable, &term.sort) {
            *variable = renamed;
        }
        return;
    }
    let mut each = |child: &SemanticTerm| {
        let mut child = child.clone();
        rename(&mut child, name);
        Ok::<_, std::convert::Infallible>(child)
    };
    let kind = match &term.kind {
        IrTermKind::Variable { .. }
        | IrTermKind::Token { .. }
        | IrTermKind::Rewrite { .. }
        | IrTermKind::As { .. }
        | IrTermKind::Matches { .. }
        | IrTermKind::Let { .. } => return,
        IrTermKind::Application {
            application,
            arguments,
            instance,
            head_instance_fixed,
        } => IrTermKind::Application {
            application: application.clone(),
            arguments: arguments
                .iter()
                .map(|child| each(child).unwrap_or_else(|never| match never {}))
                .collect(),
            instance: instance.clone(),
            head_instance_fixed: *head_instance_fixed,
        },
        IrTermKind::KSequence { item_sort, items } => IrTermKind::KSequence {
            item_sort: item_sort.clone(),
            items: items
                .iter()
                .map(|child| each(child).unwrap_or_else(|never| match never {}))
                .collect(),
        },
        IrTermKind::Map(operands) => {
            let Ok(operands) = operands.try_map_ref(&mut each);
            IrTermKind::Map(Box::new(operands))
        }
        IrTermKind::List(operands) => {
            let Ok(operands) = operands.try_map_ref(&mut each);
            IrTermKind::List(Box::new(operands))
        }
        IrTermKind::Set(operands) => {
            let Ok(operands) = operands.try_map_ref(&mut each);
            IrTermKind::Set(Box::new(operands))
        }
        IrTermKind::Cell { cell, children } => IrTermKind::Cell {
            cell: cell.clone(),
            children: children
                .iter()
                .map(|child| each(child).unwrap_or_else(|never| match never {}))
                .collect(),
        },
        IrTermKind::Or { alternatives } => {
            let Ok(alternatives) = alternatives.try_map_ref(&mut each);
            IrTermKind::Or { alternatives }
        }
    };
    term.kind = kind;
}

/// Whether two terms are one term, up to origins and the names of wildcards.
#[must_use]
pub fn same(left: &SemanticTerm, right: &SemanticTerm) -> bool {
    if left.sort() != right.sort() {
        return false;
    }
    let children = |left: &SemanticTerm, right: &SemanticTerm| {
        let (left, right) = (left.children(), right.children());
        left.len() == right.len() && left.iter().zip(&right).all(|(l, r)| same(l, r))
    };
    match (left.kind(), right.kind()) {
        (IrTermKind::Variable { variable: l }, IrTermKind::Variable { variable: r }) => {
            l == r || (is_wildcard(l) && is_wildcard(r)) || both_test_names(l, r)
        }
        (
            IrTermKind::Application {
                application: la,
                instance: li,
                ..
            },
            IrTermKind::Application {
                application: ra,
                instance: ri,
                ..
            },
        ) => la == ra && li == ri && children(left, right),
        (IrTermKind::Token { value: l }, IrTermKind::Token { value: r }) => l == r,
        (IrTermKind::Map(l), IrTermKind::Map(r)) => {
            l.operation() == r.operation() && children(left, right)
        }
        (IrTermKind::List(l), IrTermKind::List(r)) => {
            l.operation() == r.operation() && children(left, right)
        }
        (IrTermKind::Set(l), IrTermKind::Set(r)) => {
            l.operation() == r.operation() && children(left, right)
        }
        (IrTermKind::Cell { cell: l, .. }, IrTermKind::Cell { cell: r, .. }) => {
            l == r && children(left, right)
        }
        (
            IrTermKind::KSequence { item_sort: l, .. },
            IrTermKind::KSequence { item_sort: r, .. },
        ) => l == r && children(left, right),
        (IrTermKind::Rewrite { .. }, IrTermKind::Rewrite { .. })
        | (IrTermKind::Or { .. }, IrTermKind::Or { .. })
        | (IrTermKind::Matches { .. }, IrTermKind::Matches { .. })
        | (IrTermKind::Let { .. }, IrTermKind::Let { .. }) => children(left, right),
        (IrTermKind::As { alias: l, .. }, IrTermKind::As { alias: r, .. }) => {
            children(left, right) && l == r
        }
        _ => false,
    }
}

/// Whether two identities are both a test's anonymous name ([`test_name`]).
fn both_test_names(left: &SemanticId, right: &SemanticId) -> bool {
    let test = |id: &SemanticId| matches!(id.kind(), SemanticIdKind::Anonymous { name } if name == "_Krs_Defined");
    test(left) && test(right)
}

fn is_wildcard(id: &SemanticId) -> bool {
    id.kind() == SemanticIdKind::Wildcard
}

/// Whether `term` is `andThenBool` or `andBool`, whose operands are the conjuncts of a chain.
#[must_use]
pub fn conjunction(term: &SemanticTerm) -> Option<(&SemanticTerm, &SemanticTerm, bool)> {
    match term.kind() {
        IrTermKind::Application {
            application:
                ApplicationRef::Builtin(
                    operation @ (BuiltinOperation::BoolAndThen | BuiltinOperation::BoolAnd),
                ),
            arguments,
            ..
        } if arguments.len() == 2 => Some((
            &arguments[0],
            &arguments[1],
            *operation == BuiltinOperation::BoolAndThen,
        )),
        _ => None,
    }
}

/// The conjuncts of `term`'s top-level conjunction, which all hold where `term` does.
fn conjuncts<'a>(term: &'a SemanticTerm, output: &mut Vec<&'a SemanticTerm>) {
    match conjunction(term) {
        Some((left, right, _)) => {
            conjuncts(left, output);
            conjuncts(right, output);
        }
        None => output.push(term),
    }
}

/// A partial construct the check found without its test before it.
#[derive(Debug)]
pub struct Unguarded {
    /// Where the construct is.
    pub construct: NodeOrigin,
    /// Where it stands.
    pub place: Place,
}

/// Where an unguarded construct stands.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Place {
    /// In a sentence's condition, with no test before it.
    Condition,
    /// In a pattern that matches evaluated terms, which evaluates it before any condition.
    Pattern,
}

/// The first partial construct `rule` evaluates without its test before it (the module
/// documentation): one in a pattern over evaluated terms, or one in the condition that no
/// earlier conjunct of its chain tests. A result, a claim's start state, and a pattern matched
/// as written (a simplification's, a static clause's) are not read.
#[must_use]
pub fn unguarded(rule: &SemanticRule, sorts: &Sorts) -> Option<Unguarded> {
    if matches!(
        rule.kind(),
        SentenceKind::Transition | SentenceKind::Context | SentenceKind::Equation
    ) && rule.simplification().is_none()
    {
        for pattern in pattern_terms(rule) {
            if let Some(construct) = first_partial_in_pattern(pattern, true, sorts) {
                return Some(Unguarded {
                    construct: construct.origin().clone(),
                    place: Place::Pattern,
                });
            }
        }
    }
    let Some(SemanticCondition::Bool(condition)) = rule.requires() else {
        return None;
    };
    let mut found = None;
    Checker {
        sorts,
        unstated: true,
        visit: &mut |construct: &SemanticTerm, _: &Requirement<'_>, _: &SemanticTerm| {
            found.get_or_insert_with(|| construct.origin().clone());
        },
    }
    .guard_point(condition.term(), &[]);
    found.map(|construct| Unguarded {
        construct,
        place: Place::Condition,
    })
}

/// A test an author wrote in the conjunct that evaluates a partial construct, below `!`, `||`
/// or another operation, where it cannot protect the construct: the condition has no value
/// where the construct has none, whatever the test says ([`dead_tests`]).
#[derive(Debug)]
pub struct DeadTest {
    /// Where the construct is.
    pub construct: NodeOrigin,
    /// Where the author's test of it is.
    pub test: NodeOrigin,
    /// What the construct is, for a message ([`Requirement::construct_name`]).
    pub name: String,
}

/// Each partial construct in `rule`'s condition whose test the author also wrote below `!`,
/// `||` or another operation of the conjunct that evaluates it. Under KRS's reading of the
/// connectives such a test does not make the construct's value unneeded (`!k::is!(Int, a) ||
/// k::project!(Int, a) > 0` has no value where `a` is no `Int`), so the condition the guarding
/// pass writes (`isInt(A) andThenBool ..`) does not hold where the test says the construct has
/// no value, which an author reading `||` as Rust's would not expect.
#[must_use]
pub fn dead_tests(rule: &SemanticRule, sorts: &Sorts) -> Vec<DeadTest> {
    let Some(SemanticCondition::Bool(condition)) = rule.requires() else {
        return Vec::new();
    };
    let mut found = Vec::<DeadTest>::new();
    Checker {
        sorts,
        unstated: false,
        visit: &mut |construct: &SemanticTerm,
                     requirement: &Requirement<'_>,
                     conjunct: &SemanticTerm| {
            if let Some(test) = find(conjunct, &|candidate| {
                requirement.holds_by(candidate, sorts)
            }) && !found
                .iter()
                .any(|dead| dead.construct == *construct.origin())
            {
                found.push(DeadTest {
                    construct: construct.origin().clone(),
                    test: test.origin().clone(),
                    name: requirement.construct_name(),
                });
            }
        },
    }
    .guard_point(condition.term(), &[]);
    found
}

/// The first subterm of `term`, in preorder, that `wanted` accepts.
fn find<'t>(
    term: &'t SemanticTerm,
    wanted: &dyn Fn(&SemanticTerm) -> bool,
) -> Option<&'t SemanticTerm> {
    if wanted(term) {
        return Some(term);
    }
    term.children()
        .into_iter()
        .find_map(|child| find(child, wanted))
}

/// The terms of `rule` that are matched: a term rewrite's left side (with its rewrites' right
/// sides, which are built, read by [`first_partial_in_pattern`]), each matched cell's pattern.
fn pattern_terms(rule: &SemanticRule) -> Vec<&SemanticTerm> {
    match rule.relational_body() {
        RuleBodyRef::Term(body) => vec![body.local_term().unwrap_or_else(|| body.from())],
        RuleBodyRef::Configuration { body, .. } => body
            .parts()
            .iter()
            .filter_map(krs_ir::ClausePart::pre_term)
            .collect(),
        RuleBodyRef::Predicate(_) => Vec::new(),
    }
}

/// Whether `term` evaluates a partial construct anywhere, its rewrites' left sides included;
/// `projected` is false for the operand of a generated sort operation.
#[must_use]
pub fn holds_partial(term: &SemanticTerm, projected: bool, sorts: &Sorts) -> bool {
    first_partial_in_pattern(term, projected, sorts).is_some()
}

fn first_partial_in_pattern<'a>(
    term: &'a SemanticTerm,
    projected: bool,
    sorts: &Sorts,
) -> Option<&'a SemanticTerm> {
    if let IrTermKind::Rewrite { from, .. } = term.kind() {
        return first_partial_in_pattern(from, projected, sorts);
    }
    // A pattern matches a collection's constructors (a concatenation of sets among them); it
    // does not build them.
    if !builds_collection(term) && !requirements(term, projected, sorts).is_empty() {
        return Some(term);
    }
    let generated = is_generated(term);
    term.children()
        .into_iter()
        .find_map(|child| first_partial_in_pattern(child, !generated, sorts))
}

/// Whether `term` applies a collection's constructor (unit, element, concatenation).
fn builds_collection(term: &SemanticTerm) -> bool {
    match term.kind() {
        IrTermKind::Map(operands) => operands.operation().builds_collection(),
        IrTermKind::List(operands) => operands.operation().builds_collection(),
        IrTermKind::Set(operands) => operands.operation().builds_collection(),
        _ => false,
    }
}

/// Whether `term` applies a generated sort operation, which reads its operand unprojected.
#[must_use]
pub fn is_generated(term: &SemanticTerm) -> bool {
    matches!(
        term.kind(),
        IrTermKind::Application {
            application: ApplicationRef::Generated(_),
            ..
        }
    )
}

/// The `let` statement `term` is, when its pattern is one name every value of the value's
/// sort matches: the name and the value, which its body may read in the name's place.
#[must_use]
pub fn name_binding<'t>(
    term: &'t SemanticTerm,
    sorts: &Sorts,
) -> Option<(&'t SemanticId, &'t SemanticTerm, &'t SemanticTerm)> {
    let IrTermKind::Let {
        pattern,
        value,
        body,
        ..
    } = term.kind()
    else {
        return None;
    };
    match pattern.kind() {
        IrTermKind::Variable { variable } if irrefutable(pattern, value.sort(), sorts) => {
            Some((variable, value, body))
        }
        _ => None,
    }
}

/// `term` with each occurrence of the name `name` replaced by `value`.
#[must_use]
pub fn substituted(term: &SemanticTerm, name: &SemanticId, value: &SemanticTerm) -> SemanticTerm {
    if let IrTermKind::Variable { variable } = term.kind()
        && variable == name
    {
        return value.clone();
    }
    map_children(term, &mut |child| substituted(child, name, value))
}

/// `term`, a conjunct of a condition whose tests stand before it, with each `k::matches!` whose
/// subject is a sort projection stated on the projection's operand.
///
/// `k::matches!(k::project!(S, t), P)` means that `t` is an `S` whose value matches `P`. The
/// projection's test `isS(t)` stands before the conjunct, so where the conjunct is evaluated
/// the projection is `t` itself: a cast changes no value. `:=K` matches a term of any sort, so
/// `P :=K t` is well formed with `t` at its own sort and states the same test, with no
/// projection as its operand. A result is not tested, and keeps the projection, which has no
/// value where `t` is not an `S`.
#[must_use]
pub fn matched_on_operands(term: &SemanticTerm) -> SemanticTerm {
    let term = match term.kind() {
        IrTermKind::Matches {
            subject,
            pattern,
            binds,
        } if projected_operand(subject).is_some() => {
            let mut operand = &**subject;
            while let Some(inner) = projected_operand(operand) {
                operand = inner;
            }
            term.with_kind(IrTermKind::Matches {
                subject: Box::new(operand.clone()),
                pattern: pattern.clone(),
                binds: binds.clone(),
            })
        }
        _ => term.clone(),
    };
    map_children(&term, &mut matched_on_operands)
}

/// The operand of `term`, where `term` is a sort projection.
fn projected_operand(term: &SemanticTerm) -> Option<&SemanticTerm> {
    match term.kind() {
        IrTermKind::Application {
            application: ApplicationRef::Generated(GeneratedOperation::SortProjection(_)),
            arguments,
            ..
        } => match arguments.as_slice() {
            [operand] => Some(operand),
            _ => None,
        },
        _ => None,
    }
}

/// `term` with each child replaced by `map`'s image of it, in [`SemanticTerm::children`]'s
/// order.
fn map_children(
    term: &SemanticTerm,
    map: &mut dyn FnMut(&SemanticTerm) -> SemanticTerm,
) -> SemanticTerm {
    let mut each = |child: &SemanticTerm| Ok::<_, std::convert::Infallible>(map(child));
    let kind = match term.kind() {
        IrTermKind::Variable { .. } | IrTermKind::Token { .. } => return term.clone(),
        IrTermKind::Application {
            application,
            arguments,
            instance,
            head_instance_fixed,
        } => IrTermKind::Application {
            application: application.clone(),
            arguments: arguments.iter().map(&mut *map).collect(),
            instance: instance.clone(),
            head_instance_fixed: *head_instance_fixed,
        },
        IrTermKind::KSequence { item_sort, items } => IrTermKind::KSequence {
            item_sort: item_sort.clone(),
            items: items.iter().map(&mut *map).collect(),
        },
        IrTermKind::Map(operands) => {
            let Ok(operands) = operands.try_map_ref(&mut each);
            IrTermKind::Map(Box::new(operands))
        }
        IrTermKind::List(operands) => {
            let Ok(operands) = operands.try_map_ref(&mut each);
            IrTermKind::List(Box::new(operands))
        }
        IrTermKind::Set(operands) => {
            let Ok(operands) = operands.try_map_ref(&mut each);
            IrTermKind::Set(Box::new(operands))
        }
        IrTermKind::Cell { cell, children } => IrTermKind::Cell {
            cell: cell.clone(),
            children: children.iter().map(&mut *map).collect(),
        },
        IrTermKind::Rewrite { from, to } => IrTermKind::Rewrite {
            from: Box::new(map(from)),
            to: Box::new(map(to)),
        },
        IrTermKind::As { alias, pattern } => IrTermKind::As {
            alias: alias.clone(),
            pattern: Box::new(map(pattern)),
        },
        IrTermKind::Or { alternatives } => {
            let Ok(alternatives) = alternatives.try_map_ref(&mut each);
            IrTermKind::Or { alternatives }
        }
        IrTermKind::Matches {
            subject,
            pattern,
            binds,
        } => IrTermKind::Matches {
            subject: Box::new(map(subject)),
            pattern: Box::new(map(pattern)),
            binds: binds.clone(),
        },
        IrTermKind::Let {
            pattern,
            value,
            body,
            binds,
        } => IrTermKind::Let {
            pattern: Box::new(map(pattern)),
            value: Box::new(map(value)),
            body: Box::new(map(body)),
            binds: binds.clone(),
        },
    };
    term.with_kind(kind)
}

/// A walk of one condition's guard points and the constructs below them. `visit` receives each
/// construct with a requirement, and the conjunct that evaluates it; when `unstated`, only
/// those whose requirement `established` (the earlier conjuncts of its chain) does not state,
/// or whose test reads a name a `#let` inside its conjunct binds. A construct in the body of a
/// `#let` that binds one name every value matches is read with the name's value in its place,
/// which a test before the conjunct can read.
struct Checker<'s, 'v> {
    sorts: &'s Sorts,
    unstated: bool,
    visit: &'v mut dyn FnMut(&SemanticTerm, &Requirement<'_>, &SemanticTerm),
}

impl Checker<'_, '_> {
    fn guard_point<'t>(&mut self, term: &'t SemanticTerm, established: &[&'t SemanticTerm]) {
        if let Some((left, right, ordered)) = conjunction(term) {
            self.guard_point(left, established);
            let mut after = established.to_vec();
            if ordered {
                conjuncts(left, &mut after);
            }
            self.guard_point(right, &after);
            return;
        }
        if let IrTermKind::Let { value, body, .. } = term.kind()
            && *body.sort() == SemanticSortRef::Builtin(BuiltinSort::Bool)
        {
            self.leaf(value, true, established, &BTreeSet::new(), term);
            for requirement in requirements(term, true, self.sorts) {
                self.report(value, &requirement, established, &BTreeSet::new(), term);
            }
            // The body is evaluated where the statement matched, with its names bound: a test
            // of the statement's names inside it stands at a guard point.
            self.guard_point(body, established);
            return;
        }
        self.leaf(term, true, established, &BTreeSet::new(), term);
    }

    fn report(
        &mut self,
        construct: &SemanticTerm,
        requirement: &Requirement<'_>,
        established: &[&SemanticTerm],
        bound: &BTreeSet<SemanticId>,
        conjunct: &SemanticTerm,
    ) {
        if !self.unstated
            || reads_any(requirement, bound)
            || !requirement.established_by(established, self.sorts)
        {
            (self.visit)(construct, requirement, conjunct);
        }
    }

    /// Visits each construct in `term`, no place of which is a guard point; `bound` are the
    /// names the `#let`s inside `conjunct` around `term` bind, which no test before it reads.
    fn leaf(
        &mut self,
        term: &SemanticTerm,
        projected: bool,
        established: &[&SemanticTerm],
        bound: &BTreeSet<SemanticId>,
        conjunct: &SemanticTerm,
    ) {
        let generated = is_generated(term);
        if let Some((name, value, body)) = name_binding(term, self.sorts) {
            self.leaf(value, true, established, bound, conjunct);
            let body = substituted(body, name, value);
            self.leaf(&body, true, established, bound, conjunct);
            return;
        }
        if let IrTermKind::Let {
            value, body, binds, ..
        } = term.kind()
        {
            self.leaf(value, true, established, bound, conjunct);
            let mut inner = bound.clone();
            inner.extend(binds.iter().cloned());
            self.leaf(body, true, established, &inner, conjunct);
        } else if let IrTermKind::Matches { subject, .. } = term.kind() {
            self.leaf(subject, true, established, bound, conjunct);
        } else {
            for child in term.children() {
                self.leaf(child, !generated, established, bound, conjunct);
            }
        }
        for requirement in requirements(term, projected, self.sorts) {
            self.report(term, &requirement, established, bound, conjunct);
        }
    }
}

/// Whether the requirement's test reads a name in `names`.
#[must_use]
pub fn reads_any(requirement: &Requirement<'_>, names: &BTreeSet<SemanticId>) -> bool {
    !names.is_empty()
        && requirement
            .operands()
            .into_iter()
            .any(|operand| reads(operand, names))
}

/// Whether `term` reads a name in `names`.
#[must_use]
pub fn reads(term: &SemanticTerm, names: &BTreeSet<SemanticId>) -> bool {
    match term.kind() {
        IrTermKind::Variable { variable } => names.contains(variable),
        _ => term.children().into_iter().any(|child| reads(child, names)),
    }
}

#[cfg(test)]
mod tests;
