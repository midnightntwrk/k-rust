//! The taint closure: the symbols whose applications get no value claim, given the pairs that
//! do not provably join.
//!
//! A non-joined pair is an axiom the normal-form model may violate, so a model of the definition
//! may have to identify terms that `M_NF` keeps apart, or make undefined terms `M_NF` calls
//! defined. A quantified axiom `forall xs : Ss. phi(xs)` constrains exactly two things: the
//! interpretations of the symbols occurring in `phi`, and the elements of the sorts `Ss` its
//! variables range over. The closure follows both, through every other axiom: `T` is the least
//! set of equations and symbols closed under
//!
//! - **T0**: both equations of every non-joined pair are tainted;
//! - **T1**: an executable equation whose left-hand side mentions a tainted symbol is tainted;
//! - **T-sym**: a tainted equation taints every symbol it mentions (left-hand side, right-hand
//!   side, `requires`, `ensures`) that is neither a free constructor nor hooked (a free
//!   constructor's applications are its own values in every model; a hook's interpretation is
//!   fixed in every model, and precondition P6 makes its equations agree with it);
//! - **T-obs**: a tainted equation taints every equation head whose applications can occur inside
//!   an element of the sort of one of its variables ([`SortReach`]), in the model below.
//!
//! The closure is also seeded by the equations of the precondition rows that taint (an equation
//! headed by a free constructor or an injection) and by the heads a pinned symbol withdraws.
//!
//! The operator is monotone on a finite lattice, so a worklist that visits each equation once
//! and pushes each symbol once reaches its least fixpoint (Kleene iteration). With this closure,
//! one model of the definition makes every claim on an untainted term true at once, whenever the
//! definition has a model at all (sorts may be empty, and an axiom's variables range over
//! elements): from any model `M`, keep its elements as *old* ones, add as *new* elements the formal
//! normal forms that hold an untainted equation-head application, interpret untainted symbols by
//! the untainted equations, and each application holding a new element that no untainted equation
//! rewrites as `symbols.rs` states for its class (formally, `\bottom`, one fixed old element of a
//! sort that has one in every model, or a literal). No tainted equation can see a new element,
//! through its symbols (T1, T-sym) or through its variables (T-obs) (`docs/compatibility.md`,
//! "Anywhere rules").

use std::collections::{BTreeSet, VecDeque};

use k_rust_kore::names::WellKnownSymbol;
use rustc_hash::FxHashMap;

use super::{
    Equation,
    symbols::{OnNewArguments, Sorts},
};
use crate::{
    definition::BackendDefinition,
    rule::{RewriteRule, RuleRhs},
    term::{CollectionMetadata, FunctionType, HeadRole, Name, Sort, Symbol, SymbolType, Term},
};

/// ```toml algorithm-site
/// id = "backend.confluence.critical_pairs"
/// role = "part"
/// sites = ["Closure::taint", "SortReach::heads"]
/// ```
///
/// The data the closure walks: for each executable equation, the taintable symbols it mentions
/// and the sorts of its variables; for each symbol, the equations whose left-hand side mentions
/// it; and the sort reach. Built once per check, in one pass over the equations.
pub(super) struct Closure<'e> {
    equations: &'e [Equation],
    id_of: FxHashMap<*const RewriteRule, usize>,
    lhs_index: FxHashMap<Name, Vec<usize>>,
    reach: SortReach,
}

impl<'e> Closure<'e> {
    pub(super) fn new(
        definition: &BackendDefinition,
        sorts: &Sorts,
        equations: &'e [Equation],
    ) -> Self {
        let id_of = equations
            .iter()
            .enumerate()
            .map(|(id, equation)| (std::sync::Arc::as_ptr(&equation.rule), id))
            .collect();
        let mut lhs_index = FxHashMap::<Name, Vec<usize>>::default();
        for (id, equation) in equations.iter().enumerate() {
            let mut lhs = BTreeSet::new();
            equation.rule.lhs.visit_symbols(&mut |symbol| {
                if taintable(symbol) {
                    lhs.insert(symbol.name.clone());
                }
            });
            for symbol in lhs {
                lhs_index.entry(symbol).or_default().push(id);
            }
        }
        Self {
            equations,
            id_of,
            lhs_index,
            reach: SortReach::new(definition, sorts),
        }
    }

    /// The equation heads the pinned symbols withdraw (R1.4), with the symbols that pin them.
    pub(super) fn pinned_heads(&mut self) -> Vec<(Name, BTreeSet<Name>)> {
        self.reach.pinned_heads()
    }

    /// The tainted symbols of the closure seeded by the equations `seeds` (both equations of each
    /// non-joined pair, and the equations of the precondition rows that taint) and the symbols
    /// `symbols` (the pinned heads): a worklist that visits each equation once and pushes each
    /// symbol once.
    pub(super) fn taint<'r>(
        &mut self,
        seeds: impl IntoIterator<Item = &'r std::sync::Arc<RewriteRule>>,
        symbols: impl IntoIterator<Item = Name>,
    ) -> BTreeSet<Name> {
        let mut tainted_equations = vec![false; self.equations.len()];
        let mut tainted = BTreeSet::new();
        let mut queue = VecDeque::new();
        let switches = super::switches::active();
        if switches.seed_heads_only {
            for rule in seeds {
                if let crate::term::TermKind::Application { symbol, .. } = rule.lhs.kind() {
                    tainted.insert(symbol.name.clone());
                }
            }
            tainted.extend(symbols);
            return tainted;
        }
        for rule in seeds {
            if let Some(&id) = self.id_of.get(&std::sync::Arc::as_ptr(rule))
                && !tainted_equations[id]
            {
                tainted_equations[id] = true;
                queue.push_back(id);
            }
        }
        let mut pushed = symbols.into_iter().collect::<Vec<_>>();
        loop {
            for symbol in pushed.drain(..) {
                if tainted.insert(symbol.clone()) && !switches.drop_t1 {
                    for &other in self.lhs_index.get(&symbol).into_iter().flatten() {
                        if !tainted_equations[other] {
                            tainted_equations[other] = true;
                            queue.push_back(other);
                        }
                    }
                }
            }
            let Some(id) = queue.pop_front() else {
                return tainted;
            };
            let rule = &self.equations[id].rule;
            pushed.extend(mentioned_symbols(rule, !switches.drop_tsym_rhs));
            if !switches.drop_tobs {
                for variable in &rule.computed_attributes.variables {
                    pushed.extend(self.reach.heads(&variable.sort));
                }
            }
        }
    }
}

/// Whether the closure taints `symbol` when a tainted equation mentions it.
fn taintable(symbol: &Symbol) -> bool {
    symbol.attributes.head_role() != HeadRole::FreeConstructor && symbol.attributes.hook.is_none()
}

/// The taintable symbols `rule` mentions: anywhere, or in its left-hand side only when not
/// `everywhere` (a test switch).
fn mentioned_symbols(rule: &RewriteRule, everywhere: bool) -> BTreeSet<Name> {
    let mut symbols = BTreeSet::new();
    let mut visit_term = |term: &Term| {
        term.visit_symbols(&mut |symbol| {
            if taintable(symbol) {
                symbols.insert(symbol.name.clone());
            }
        });
    };
    visit_term(&rule.lhs);
    if !everywhere {
        return symbols;
    }
    match &rule.rhs {
        RuleRhs::Term(term) => visit_term(term),
        RuleRhs::Disjunction(alternatives) => {
            for alternative in alternatives {
                visit_term(&alternative.term);
                for predicate in alternative.ensures.iter() {
                    predicate.visit_terms(&mut visit_term);
                }
            }
        }
        RuleRhs::Predicates(predicates) => {
            for predicate in predicates {
                predicate.visit_terms(&mut visit_term);
            }
        }
        RuleRhs::Top | RuleRhs::Bottom => {}
    }
    for predicate in rule.requires.iter().chain(rule.ensures.iter()) {
        predicate.visit_terms(&mut visit_term);
    }
    symbols
}

/// For each sort, the equation heads whose applications can occur inside an element of it in the
/// model of the construction: the least fixpoint over the graph whose edges go from a sort to its
/// subsorts, to the element, key and value sorts of a collection sort, and to the argument sorts
/// of every symbol of that sort whose application holding a new element that model interprets
/// formally (`symbols.rs`, R1.2: constructors, equation heads, total symbols it cannot collapse
/// into an old element, partial symbols that are not declared functions). A sort parameter is
/// read as every sort. Computed by one depth-first walk per sort asked, memoized.
///
/// A symbol that model cannot interpret on new arguments at all (a total injective symbol into a
/// hooked sort) is *pinned*: the heads its argument sorts reach get no claim (R1.4).
pub(crate) struct SortReach {
    edges: FxHashMap<Sort, BTreeSet<Sort>>,
    heads_of: FxHashMap<Sort, BTreeSet<Name>>,
    /// Equation heads of a parametric result sort, in every sort.
    everywhere: BTreeSet<Name>,
    /// Argument sorts every sort reaches (those of parametric constructors and heads).
    from_everywhere: BTreeSet<Sort>,
    /// Whether some symbol has a parametric argument: then every sort reaches every head.
    all_heads: BTreeSet<Name>,
    reaches_everything: bool,
    memo: FxHashMap<Sort, BTreeSet<Name>>,
    /// The symbols `M'` cannot interpret on new arguments (R1.4), with their argument sorts.
    pinned: Vec<(Name, Vec<Sort>)>,
}

impl SortReach {
    pub(crate) fn new(definition: &BackendDefinition, sorts: &Sorts) -> Self {
        let mut reach = Self {
            edges: FxHashMap::default(),
            heads_of: FxHashMap::default(),
            everywhere: BTreeSet::new(),
            from_everywhere: BTreeSet::new(),
            all_heads: BTreeSet::new(),
            reaches_everything: false,
            memo: FxHashMap::default(),
            pinned: Vec::new(),
        };
        let switches = super::switches::active();
        for (sup, below) in definition.sort_graph().closures() {
            reach
                .edges
                .entry(sup.sort().clone())
                .or_default()
                .extend(below.iter().map(|sort| sort.sort().clone()));
        }
        for symbol in definition.symbols().values() {
            if let Some(collection) = &symbol.attributes.collection
                && !switches.drop_collection_edges
            {
                let (sort, parts) = match collection {
                    CollectionMetadata::Map(map) => (
                        map.map_sort.clone(),
                        vec![map.key_sort.clone(), map.value_sort.clone()],
                    ),
                    CollectionMetadata::List(list) | CollectionMetadata::Set(list) => {
                        (list.list_sort.clone(), vec![list.element_sort.clone()])
                    }
                };
                reach
                    .edges
                    .entry(Sort::simple(sort))
                    .or_default()
                    .extend(parts.into_iter().map(Sort::simple));
            }
            if symbol.is(WellKnownSymbol::Inj) {
                // A sort injection's edges are the subsort edges above.
                continue;
            }
            let parametric_result = has_sort_variable(&symbol.result_sort);
            if symbol.attributes.head_role() == HeadRole::EquationHead {
                reach.all_heads.insert(symbol.name.clone());
                if parametric_result {
                    reach.everywhere.insert(symbol.name.clone());
                } else {
                    reach
                        .heads_of
                        .entry(symbol.result_sort.clone())
                        .or_default()
                        .insert(symbol.name.clone());
                }
            }
            // An edge from the result sort to the argument sorts exactly where the model of the
            // construction interprets an application holding a new element formally (R1.2).
            let reading = if switches.collapse_every_total {
                revision_two_reading(definition, symbol)
            } else {
                sorts.on_new_arguments(definition, symbol)
            };
            match reading {
                OnNewArguments::Formal => {}
                OnNewArguments::Opaque => continue,
                OnNewArguments::Pinned => {
                    reach
                        .pinned
                        .push((symbol.name.clone(), symbol.argument_sorts.clone()));
                    continue;
                }
            }
            for argument in &symbol.argument_sorts {
                if has_sort_variable(argument) {
                    reach.reaches_everything = true;
                } else if parametric_result {
                    reach.from_everywhere.insert(argument.clone());
                } else {
                    reach
                        .edges
                        .entry(symbol.result_sort.clone())
                        .or_default()
                        .insert(argument.clone());
                }
            }
        }
        reach
    }

    /// The equation heads whose applications can occur inside an element of the argument sorts
    /// of a pinned symbol (R1.4), with the symbols that pin them.
    pub(crate) fn pinned_heads(&mut self) -> Vec<(Name, BTreeSet<Name>)> {
        let pinned = self.pinned.clone();
        pinned
            .into_iter()
            .map(|(symbol, arguments)| {
                let mut heads = BTreeSet::new();
                for argument in &arguments {
                    heads.extend(self.heads(argument));
                }
                (symbol, heads)
            })
            .filter(|(_, heads)| !heads.is_empty())
            .collect()
    }

    /// The equation heads whose applications can occur inside an element of `sort`.
    pub(crate) fn heads(&mut self, sort: &Sort) -> BTreeSet<Name> {
        if self.reaches_everything || has_sort_variable(sort) {
            return self.all_heads.clone();
        }
        if let Some(known) = self.memo.get(sort) {
            return known.clone();
        }
        let mut seen = BTreeSet::new();
        let mut stack = vec![sort.clone()];
        stack.extend(self.from_everywhere.iter().cloned());
        let mut heads = self.everywhere.clone();
        while let Some(sort) = stack.pop() {
            if !seen.insert(sort.clone()) {
                continue;
            }
            if has_sort_variable(&sort) {
                return self.all_heads.clone();
            }
            if let Some(found) = self.heads_of.get(&sort) {
                heads.extend(found.iter().cloned());
            }
            if let Some(next) = self.edges.get(&sort) {
                stack.extend(next.iter().cloned());
            }
        }
        self.memo.insert(sort.clone(), heads.clone());
        heads
    }
}

/// Test switch `collapse_every_total`: revision 2's reading (3.13 (l)), which keeps an edge only
/// for constructors, equation heads and declared total injective functions into a sort that is not
/// a builtin carrier.
fn revision_two_reading(definition: &BackendDefinition, symbol: &Symbol) -> OnNewArguments {
    let role = symbol.attributes.head_role();
    let injective_total = matches!(
        role,
        HeadRole::Function {
            injective: true,
            ..
        }
    ) && symbol.attributes.symbol_type
        == SymbolType::Function(FunctionType::Total)
        && symbol.attributes.hook.is_none()
        && !definition
            .sorts()
            .get(match &symbol.result_sort {
                Sort::Application { name, .. } => name,
                Sort::Variable(_) => return OnNewArguments::Formal,
            })
            .is_some_and(|info| info.hook.is_some() || info.has_domain_values);
    if matches!(role, HeadRole::FreeConstructor | HeadRole::EquationHead) || injective_total {
        OnNewArguments::Formal
    } else {
        OnNewArguments::Opaque
    }
}

fn has_sort_variable(sort: &Sort) -> bool {
    match sort {
        Sort::Variable(_) => true,
        Sort::Application { arguments, .. } => arguments.iter().any(has_sort_variable),
    }
}
