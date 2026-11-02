//! Query-local readings of pure functional values and their source domains.
//!
//! A value UF totalizes a partial function without asserting that it exists. Its domain UF
//! names only the unresolved head obligation; canonical ceil rules and strict child domains
//! retain source conditions and every original argument obligation. Domain lets are local to a predicate's
//! lexical scope, so neither shared DAGs nor quantifiers duplicate or capture their meanings.

use std::collections::{BTreeMap, BTreeSet};

use rustc_hash::{FxHashMap, FxHashSet};

use super::{SExpr, TranslationError, TranslationState};
use crate::{
    rule::Predicate,
    term::{FunctionType, SymbolType, Term, TermKind},
};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct SharedDomains {
    /// The domain of each node read in this scope: one name per node, however many parents
    /// and atoms share it. Keyed by the term's stored hash, with a pointer comparison first.
    pub(super) values: FxHashMap<Term, SExpr>,
    active: FxHashSet<Term>,
    reentrant: BTreeMap<Term, SExpr>,
    pub(super) bindings: Vec<(String, SExpr)>,
}

impl SharedDomains {
    pub(super) fn bind(&self, body: SExpr) -> SExpr {
        super::bind_shared(&self.bindings, body)
    }
}

impl TranslationState {
    /// Read each domain function that the finished query applies at a single point as a
    /// Boolean constant, in every part of the query, and record it for its declaration.
    ///
    /// A query-local domain function constrains the query only through its values at the
    /// points where it is applied. One syntactic application that no quantifier encloses (a
    /// `let` only names a value) has one point in each interpretation. A model of the function
    /// reading gives the constant that point's value; a model of the constant reading gives the
    /// function that is the constant everywhere. So the readings are equisatisfiable, and the
    /// query keeps its exactness and the variables of its models. Domain congruence needs two
    /// points, so it is not lost; a function that also occurs in a derived definition, under a
    /// quantifier, unapplied, or at two points keeps its rank. The solver is then not handed a
    /// function symbol that carries nothing: its presence alone selects another procedure,
    /// one that leaves undecided queries the constant reading decides.
    pub(super) fn close_single_point_domains(&mut self, mut parts: Vec<&mut SExpr>) {
        #[derive(Default)]
        struct Uses {
            applications: usize,
            excluded: bool,
        }
        fn count(expression: &SExpr, bound: bool, uses: &mut BTreeMap<String, Uses>) {
            match expression {
                SExpr::Atom(atom) => {
                    if let Some(entry) = uses.get_mut(atom.as_str()) {
                        entry.excluded = true;
                    }
                }
                SExpr::List(items) => {
                    let mut rest = items.as_slice();
                    if let Some((SExpr::Atom(head), arguments)) = items.split_first()
                        && let Some(entry) = uses.get_mut(head.as_str())
                    {
                        entry.applications += 1;
                        entry.excluded |= bound;
                        rest = arguments;
                    }
                    let binder = matches!(
                        items.first(),
                        Some(SExpr::Atom(head)) if head == "forall" || head == "exists"
                    );
                    for item in rest {
                        count(item, bound || binder, uses);
                    }
                }
            }
        }
        fn close(expression: &mut SExpr, names: &BTreeSet<String>) {
            if let SExpr::List(items) = expression {
                if let Some(SExpr::Atom(head)) = items.first()
                    && names.contains(head.as_str())
                {
                    *expression = SExpr::atom(head.clone());
                    return;
                }
                for item in items {
                    close(item, names);
                }
            }
        }

        let mut uses = self
            .domain_functions
            .iter()
            .filter(|(head, _)| !head.rank().0.is_empty())
            .map(|(_, name)| (name.clone(), Uses::default()))
            .collect::<BTreeMap<_, _>>();
        if uses.is_empty() {
            return;
        }
        for definition in &self.derived_definitions {
            for token in definition.split(|c: char| c.is_whitespace() || matches!(c, '(' | ')')) {
                if let Some(entry) = uses.get_mut(token) {
                    entry.excluded = true;
                }
            }
        }
        for part in &parts {
            count(part, false, &mut uses);
        }
        let names = uses
            .into_iter()
            .filter(|(_, uses)| uses.applications == 1 && !uses.excluded)
            .map(|(name, _)| name)
            .collect::<BTreeSet<_>>();
        if names.is_empty() {
            return;
        }
        for part in &mut parts {
            close(part, &names);
        }
        self.single_point_domains.extend(names);
    }

    /// Instantiate already-admitted cases at this opaque occurrence's scalar arguments.
    /// This also runs when a word plan bypasses the corresponding scalar value call.
    /// Each fact is closed at the actual query scope; no quantified source theory is added.
    #[cfg(any(feature = "z3", test))]
    pub(super) fn demand_summary_cases(
        &mut self,
        head: &super::CongruenceHead,
        arguments: &[Term],
    ) -> Result<(), TranslationError> {
        let Some(cases) = self.summary_cases.get(head).cloned() else {
            return Ok(());
        };
        if !self.active_summary_cases.insert(head.clone()) {
            return Ok(());
        }
        let result = (|| {
            for key in cases {
                if self.summary_case_budget == 0 {
                    break;
                }
                let reading = self.summaries.get(&key).expect("prepared case").clone();
                let TermKind::Application {
                    symbol,
                    sort_arguments,
                    ..
                } = reading.summary.formal.kind()
                else {
                    unreachable!();
                };
                if arguments.len() != key.static_arguments.len() {
                    continue;
                }
                let actual = arguments
                    .iter()
                    .zip(&key.static_arguments)
                    .map(|(argument, fixed)| fixed.as_ref().unwrap_or(argument).clone())
                    .collect();
                let call = Term::application(symbol.clone(), *sort_arguments, actual);
                let scope = self.source_scope(&call.attributes().variables.to_btree_set());
                if !self.summary_case_seen.insert((call.clone(), scope)) {
                    continue;
                }
                self.summary_case_budget -= 1;
                self.translate_term(&call)?;
            }
            Ok(())
        })();
        self.active_summary_cases.remove(head);
        result
    }

    #[cfg(any(feature = "z3", test))]
    pub(super) fn link_summary_to_function(
        &mut self,
        term: &Term,
        value: SExpr,
    ) -> Result<(), TranslationError> {
        if !self.active_summary_links.insert(term.clone()) {
            return Ok(());
        }
        let result = (|| {
            let TermKind::Application {
                symbol, arguments, ..
            } = term.kind()
            else {
                unreachable!();
            };
            let head = self
                .functional_head(term)
                .expect("admitted pure functional summary");
            let ordinary = self.translate_congruent(head, arguments)?;
            let domain = self.translate_predicate(&Predicate::Ceil(term.clone()))?;
            self.record_source_fact(SExpr::application(
                "=>",
                vec![
                    domain.clone(),
                    SExpr::application("=", vec![ordinary, value]),
                ],
            ))?;
            if symbol.attributes.symbol_type == SymbolType::Function(FunctionType::Partial) {
                let arguments_domain = if arguments.is_empty() {
                    SExpr::atom("true")
                } else {
                    self.translate_predicate(&Predicate::And(
                        arguments
                            .iter()
                            .map(|a| Predicate::Ceil(a.clone()))
                            .collect::<Vec<_>>()
                            .into(),
                    ))?
                };
                let head = self.translate_domain_head(term)?;
                self.record_source_fact(SExpr::application(
                    "=>",
                    vec![
                        arguments_domain,
                        SExpr::application("=", vec![head, domain]),
                    ],
                ))?;
            }
            Ok(())
        })();
        self.active_summary_links.remove(term);
        result
    }

    /// The domain of `term`: the SMT statement of `\ceil(term)`, memoized per node in the
    /// predicate's domain scope. A domain is exact in both polarities, so its own atoms carry
    /// their domains even inside a predicate read as a reading alone
    /// (`TranslationState::translate_predicate_reading`).
    pub(super) fn translate_domain(&mut self, term: &Term) -> Result<SExpr, TranslationError> {
        let outside = std::mem::replace(&mut self.atom_readings, false);
        let outside_defined = std::mem::take(&mut self.stated_defined);
        let result = self.translate_domain_node(term);
        self.atom_readings = outside;
        self.stated_defined = outside_defined;
        result
    }

    fn translate_domain_node(&mut self, term: &Term) -> Result<SExpr, TranslationError> {
        if self.congruence.is_some() && term.attributes().ceil_free() {
            // Eliminating a domain must not turn an uninterpreted input carrier into
            // an exact model query merely because its variable no longer needs a value.
            if term.attributes().variables.iter().any(|variable| {
                !super::sort_denotation(&variable.sort)
                    .is_ok_and(|sort| sort.exactness() == super::Exactness::Exact)
            }) {
                self.approximate(super::Exactness::Approximate);
            }
            return Ok(SExpr::atom("true"));
        }
        let original = Predicate::Ceil(term.clone());
        #[cfg(any(feature = "z3", test))]
        let summary = super::summary::reading(&self.summaries, term)
            .cloned()
            .filter(|_| self.eligible_operand(term));
        #[cfg(not(any(feature = "z3", test)))]
        let summary: Option<()> = None;
        let plan = self.domains.get(term).cloned();
        let observation = self.observations.get(term).cloned();
        let supplies_value = observation.is_some() || self.observation_demands.contains_key(term);
        if plan.is_none() && summary.is_none() && observation.is_none() {
            self.opaque_domain_reads += 1;
            return Ok(self.abstract_predicate(&original));
        }
        // The node denotes the same in the scope of its variables (`term_level`) and in every
        // scope inside it, so a domain memoized or under derivation there is this one.
        let level = self.term_level(term);
        let scopes = level..self.scopes.len();
        if let Some(value) = scopes.clone().rev().find_map(|index| {
            self.scopes[index]
                .domains
                .as_ref()
                .and_then(|scope| scope.values.get(term))
                .cloned()
        }) {
            return Ok(value);
        }
        let home = self.domain_scope_at(level).expect("predicate domain scope");
        // Source ceil equations can be recursive. Use an opaque atom to stop expansion;
        // an actual lexical reentry is tied to the completed domain below. A depth-limited
        // graph remains conservative rather than acquiring an invented total domain.
        let reentrant = scopes.rev().find(|&index| {
            self.scopes[index]
                .domains
                .as_ref()
                .is_some_and(|scope| scope.active.contains(term))
        });
        let active = &self.scopes[home]
            .domains
            .as_ref()
            .expect("a domain scope")
            .active;
        if active.len() >= 128 || reentrant.is_some() {
            self.opaque_domain_reads += 1;
            let reference = self.abstract_predicate(&original);
            if let Some(index) = reentrant {
                self.scopes[index]
                    .domains
                    .as_mut()
                    .expect("active scope")
                    .reentrant
                    .insert(term.clone(), reference.clone());
            }
            return Ok(reference);
        }
        self.scopes[home]
            .domains
            .as_mut()
            .expect("a domain scope")
            .active
            .insert(term.clone());
        let resolved = summary.is_none()
            && (observation.is_some() || plan.as_ref().is_some_and(|p| !p.contains(&original)));
        // The domain is the head's own condition conjoined with every non-`ceil_free` child's
        // domain (`domain_plan`, `observation_domain`), so within that condition a child may be
        // read as defined: `φ /\ D(c)` is `φ[D(c) := true] /\ D(c)`. An atom over a child there
        // then states no second copy of the child's domain, which inside a quantifier of the
        // condition (a sort projection's `\exists V. X = inj(V)`) would be a copy per binder
        // scope (`TranslationState::stated_defined`).
        self.stated_defined = crate::deferred::children(term)
            .into_iter()
            .cloned()
            .collect();
        let result = (|| {
            #[cfg(any(feature = "z3", test))]
            if let Some(reading) = summary {
                return self.translate_summary_domain(term, &reading);
            }
            let value = if let Some(reading) = observation {
                self.observation_domain(term, &reading)?
            } else {
                let plan = plan.expect("a source plan, observation or admitted summary");
                let mut parts = Vec::new();
                for predicate in plan.iter() {
                    if *predicate == original {
                        self.opaque_domain_reads += 1;
                        let head = self.translate_domain_head(term)?;
                        if let Some(name) = domain_function_name(&head) {
                            self.undecided_domain_heads.insert(name);
                        }
                        parts.push(head);
                    } else {
                        parts.push(self.translate_predicate(predicate)?);
                    }
                }
                match parts.as_slice() {
                    [] => SExpr::atom("true"),
                    [part] => part.clone(),
                    _ => SExpr::application("and", parts),
                }
            };
            Ok(value)
        })();
        self.stated_defined.clear();
        self.scopes[home]
            .domains
            .as_mut()
            .expect("active domain scope")
            .active
            .remove(term);
        let value = result?;
        let reference = self.bind_domain(level, Some(term), value);
        let reentrant = self.scopes[home]
            .domains
            .as_mut()
            .expect("active domain scope")
            .reentrant
            .remove(term);
        if let Some(placeholder) = reentrant {
            // A source consequence may demand this domain while its original derivation
            // is active. Tie that lexical placeholder to the completed whole-term domain,
            // including every strict argument; do not leave a second independent ceil.
            self.record_source_fact(SExpr::application(
                "=",
                vec![placeholder, reference.clone()],
            ))?;
        }
        // Memoize the fully computed domain before translating the head's arguments.
        // Their value demands may reenter this domain (for example a product field's
        // source reconstruction), which is no longer a recursive domain derivation.
        if resolved
            && let TermKind::Application {
                symbol, arguments, ..
            } = term.kind()
            && symbol.attributes.symbol_type == SymbolType::Function(FunctionType::Partial)
            && self.functional_head(term).is_some()
            && self.domain_link_seen.insert((
                term.clone(),
                self.source_scope(&term.attributes().variables.to_btree_set()),
            ))
        {
            let mut argument_domains = Vec::new();
            for argument in arguments {
                argument_domains.push(self.translate_domain(argument)?);
            }
            let head = self.translate_domain_head(term)?;
            let fact = SExpr::application(
                "=>",
                vec![
                    if argument_domains.is_empty() {
                        SExpr::atom("true")
                    } else {
                        SExpr::application("and", argument_domains)
                    },
                    SExpr::application("=", vec![head.clone(), reference.clone()]),
                ],
            );
            let fact = self.close_source_fact(fact)?;
            match domain_function_name(&head) {
                Some(name) => self.pending_domain_links.push((name, fact)),
                None => self.domain_facts.push(fact),
            }
        }
        // The conditional ceil equations at the application, facts beside its domain function
        // (`domain_lemmas`). Each reads the completed domain through the memo.
        if let Some(lemmas) = self.domain_lemmas.get(term).cloned()
            && self.domain_lemma_seen.insert((
                term.clone(),
                self.source_scope(&term.attributes().variables.to_btree_set()),
            ))
        {
            for lemma in lemmas.iter() {
                let fact = self.translate_predicate(lemma)?;
                self.record_source_fact(fact)?;
            }
        }
        // A demanded observation domain also demands its guarded value equation. For
        // example a ceil(get(put(...),q)) must transport its value through an opaque alias.
        // Cache the domain first so the value equation can use it without recursive expansion.
        if supplies_value {
            self.translate_term(term)?;
        }
        Ok(reference)
    }

    #[cfg(any(feature = "z3", test))]
    fn translate_summary_domain(
        &mut self,
        term: &Term,
        reading: &super::summary::Reading,
    ) -> Result<SExpr, TranslationError> {
        let TermKind::Application { arguments, .. } = term.kind() else {
            unreachable!()
        };
        let mut domains = Vec::new();
        for argument in arguments {
            domains.push(self.translate_domain(argument)?);
        }
        if !reading.summary.declared_total
            && let Some(domain_name) = &reading.domain_name
        {
            self.approximate(reading.exactness);
            let arguments = arguments
                .iter()
                .zip(&reading.summary.key.static_arguments)
                .filter(|(_, fixed)| fixed.is_none())
                .map(|(argument, _)| self.translate_term(argument))
                .collect::<Result<Vec<_>, _>>()?;
            domains.push(if arguments.is_empty() {
                SExpr::atom(domain_name.clone())
            } else {
                SExpr::application(domain_name.clone(), arguments)
            });
        }
        Ok(if domains.is_empty() {
            SExpr::atom("true")
        } else {
            SExpr::application("and", domains)
        })
    }

    fn translate_domain_head(&mut self, term: &Term) -> Result<SExpr, TranslationError> {
        let Some(head) = self.functional_head(term) else {
            return Ok(self.abstract_predicate(&Predicate::Ceil(term.clone())));
        };
        #[cfg(any(feature = "z3", test))]
        self.demand_summary_cases(
            &head,
            &crate::deferred::children(term)
                .into_iter()
                .cloned()
                .collect::<Vec<_>>(),
        )?;
        self.approximate(super::Exactness::Approximate);
        let name = match self.domain_functions.get(&head) {
            Some(name) => name.clone(),
            None => {
                let name = self.fresh_name();
                self.domain_functions.insert(head, name.clone());
                name
            }
        };
        let arguments = crate::deferred::children(term)
            .into_iter()
            .map(|arg| self.translate_term(arg))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(if arguments.is_empty() {
            SExpr::atom(name)
        } else {
            SExpr::application(name, arguments)
        })
    }
}

/// The name of the domain function a head-domain reading applies (`translate_domain_head`).
fn domain_function_name(head: &SExpr) -> Option<String> {
    match head {
        SExpr::Atom(name) if name.starts_with("SMT-") => Some(name.clone()),
        SExpr::List(items) => match items.first() {
            Some(SExpr::Atom(name)) if name.starts_with("SMT-") => Some(name.clone()),
            _ => None,
        },
        SExpr::Atom(_) => None,
    }
}

/// Derive source predicates before translation, with no query names or caller facts in them.
/// An unsupported operand or exhausted construction budget keeps its previous opaque reading.
#[cfg(any(feature = "z3", test))]
pub(super) fn prepare(
    definition: &crate::definition::BackendDefinition,
    state: &mut TranslationState,
    known: &[Predicate],
    substitution: &crate::substitution::Substitution,
    checked: &[Predicate],
) -> crate::stop::Stoppable<()> {
    use crate::stop;

    let mut remaining = 16_384_usize;
    stop::check()?;
    if known
        .len()
        .saturating_add(checked.len())
        .saturating_add(substitution.len())
        > remaining
    {
        return Ok(());
    }
    let mut predicates = known.iter().chain(checked).cloned().collect::<Vec<_>>();
    let mut candidates = Vec::new();
    // Substituted terms can contribute domains reached from a checked partial application.
    candidates.extend(substitution.values().cloned());
    let mut seen = FxHashSet::default();
    while !predicates.is_empty() || !candidates.is_empty() {
        stop::check()?;
        if remaining == 0 {
            break;
        }
        remaining -= 1;
        if let Some(predicate) = predicates.pop() {
            match predicate {
                Predicate::Ceil(term) | Predicate::Defined(term) => candidates.push(term),
                // An atom's operands: the translation states their domains beside it.
                Predicate::Term(term) if !term.attributes().ceil_free() => candidates.push(term),
                Predicate::Equals(left, right) => {
                    for side in [left, right] {
                        if !side.attributes().ceil_free() {
                            candidates.push(side);
                        }
                    }
                }
                Predicate::Not(p) | Predicate::Exists(_, p) | Predicate::Forall(_, p) => {
                    predicates.push((*p).clone());
                }
                Predicate::And(parts) | Predicate::Or(parts) => {
                    if parts.len() > remaining {
                        break;
                    }
                    predicates.extend(parts.iter().cloned());
                }
                Predicate::Implies(a, b) | Predicate::Iff(a, b) => {
                    predicates.extend([(*a).clone(), (*b).clone()]);
                }
                Predicate::True
                | Predicate::False
                | Predicate::Term(_)
                | Predicate::Floor(_)
                | Predicate::In(..)
                | Predicate::Absent(_) => {}
            }
            continue;
        }
        let term = candidates.pop().expect("pending domain candidate");
        if !seen.insert(term.clone()) {
            continue;
        }
        let Some(plan) = domain_plan(definition, state, &term, &mut remaining)? else {
            continue;
        };
        if plan.len() > remaining {
            break;
        }
        predicates.extend(
            plan.iter()
                .filter(|p| **p != Predicate::Ceil(term.clone()))
                .cloned(),
        );
        if let Some(lemmas) = state.domain_lemmas.get(&term) {
            predicates.extend(lemmas.iter().cloned());
        }
    }
    Ok(())
}

/// One source-owned head domain shared by observation discovery and final domain preparation.
/// The cached predicates contain no query facts or solver names; strict operands stay explicit.
///
/// The plan replaces every occurrence of `\ceil(term)` in the query, under a negation too,
/// and is tied to the head's domain function under the arguments' domains.
/// It must therefore be equivalent to `\ceil(term)` on defined arguments:
/// a stronger plan refutes a defined instance, a weaker one an undefined instance.
/// Its sources are each equivalent: an observation route (argued at each route's function);
/// an unconditional ceil equation's stated condition, an axiom, with its terms' definedness, implied by the condition itself,
/// or, for a `value-production` application no equation reduces, a conditional ceil equation's condition whose `requires` is decided true;
/// `\top` for a `value-production` application no equation reduces (and no ceil equation decides), a total or constructor head, a variable, a domain value, an injection
/// or a list literal (list concatenation is total);
/// a map literal's key disjointness; and every child's domain, since every application is strict.
/// Anything else keeps the opaque `\ceil` (kink27 R2-DOMAIN-ROUTES).
#[cfg(any(feature = "z3", test))]
pub(super) fn domain_plan(
    definition: &crate::definition::BackendDefinition,
    state: &mut TranslationState,
    term: &Term,
    remaining: &mut usize,
) -> crate::stop::Stoppable<Option<std::sync::Arc<[Predicate]>>> {
    use crate::definedness::apply_ceil_equation;
    crate::stop::check()?;
    if let Some(plan) = state.domains.get(term) {
        return Ok(Some(plan.clone()));
    }
    if *remaining == 0 || !state.eligible_operand(term) {
        return Ok(None);
    }
    // The ceil conditions are read as stated: the reading applies no equation to the query's
    // terms, whose evaluation, as of an operand a conditional discards, need not end
    // (`crate::definedness::with_stated_ceil_conditions`).
    let plan = crate::definedness::with_stated_ceil_conditions(
        || -> crate::stop::Stoppable<Option<Vec<Predicate>>> {
            Ok(match term.kind() {
                TermKind::Application { symbol, .. } if state.functional_head(term).is_some() => {
                    Some(
                        if symbol.attributes.symbol_type
                            == SymbolType::Function(FunctionType::Partial)
                        {
                            match apply_ceil_equation(definition, term) {
                                // The condition as stated: the translation reads each of its
                                // atoms with its operands' domains, so it needs no
                                // definedness-explicit form, whose conversion walks the shared
                                // argument terms as trees.
                                Some(conditions)
                                    if admit_conditions(state, &conditions, remaining) =>
                                {
                                    conditions
                                }
                                Some(_) => vec![Predicate::Ceil(term.clone())],
                                // No ceil theory states it: the hook's own reading, which the
                                // simplifier reads at the same place (`builtin::hook_domain`).
                                None => match crate::builtin::hook_domain(definition, term)? {
                                    Some(true) => Vec::new(),
                                    Some(false) => vec![Predicate::False],
                                    None => {
                                        domain_lemmas(definition, state, term, remaining);
                                        vec![Predicate::Ceil(term.clone())]
                                    }
                                },
                            }
                        } else {
                            Vec::new()
                        },
                    )
                }
                TermKind::Variable(_)
                | TermKind::DomainValue { .. }
                | TermKind::Injection { .. } => Some(Vec::new()),
                TermKind::Map { entries, .. }
                    if definition.map_operations(&term.sort()).is_some()
                        && entries.len().saturating_mul(entries.len()) <= *remaining =>
                {
                    crate::definedness::collection_head_domain(definition, term)
                        .ok()
                        .filter(|conditions| admit_conditions(state, conditions, remaining))
                }
                TermKind::List { .. } if definition.list_operations(&term.sort()).is_some() => {
                    Some(Vec::new())
                }
                TermKind::Application { .. }
                | TermKind::Map { .. }
                | TermKind::List { .. }
                | TermKind::Set { .. }
                | TermKind::And(..) => None,
            })
        },
    )?;
    let Some(mut plan) = plan else {
        return Ok(None);
    };
    // One head at a time: a full ceil walk here would repeatedly traverse shared
    // operands and can expand a small partial-function DAG exponentially. These
    // operands have already passed purity admission, so applications/injections keep
    // exactly their strict child domains, without evaluating deferred effects.
    for child in crate::deferred::children(term) {
        if !child.attributes().ceil_free() {
            plan.push(Predicate::Ceil(child.clone()));
        }
    }
    crate::stop::check()?;
    if plan.len() > *remaining {
        return Ok(None);
    }

    let plan: std::sync::Arc<[Predicate]> = plan.into();
    state.domains.insert(term.clone(), plan.clone());
    Ok(Some(plan))
}

/// Record, for the partial application `term` whose domain stays its head's domain function,
/// the instances of its conditional ceil equations as facts (`TranslationState::domain_lemmas`):
/// `A => (\ceil(term) <=> q)` for each instance `\ceil(term) = q requires R`, where `A` is `R`
/// with the definedness of the terms the instance binds and of `term`'s arguments
/// (`definedness::conditional_ceil_lemmas`). The equation's variables range over elements, so
/// each is an instance of an axiom of the definition where `A` holds, and it holds in every model
/// in which the domain function is the application's definedness; the domain itself stays exact.
/// Without the definedness in `A`, the fact would force the domain of a bound term that `R` does
/// not mention wherever `q` holds. Their predicates are stated as written, as a plan's conditions are, since
/// the translation reads each atom with its operands' domains, and admitted under the same
/// bound; an instance that is not is left out, which only weakens what the query knows.
#[cfg(any(feature = "z3", test))]
fn domain_lemmas(
    definition: &crate::definition::BackendDefinition,
    state: &mut TranslationState,
    term: &Term,
    remaining: &mut usize,
) {
    let mut lemmas = Vec::new();
    for (requires, condition) in crate::definedness::conditional_ceil_lemmas(definition, term) {
        if !admit_conditions(state, &requires, remaining)
            || !admit_conditions(state, &condition, remaining)
        {
            continue;
        }
        let conjunction = |mut predicates: Vec<Predicate>| match predicates.len() {
            0 => Predicate::True,
            1 => predicates.pop().expect("one predicate"),
            _ => Predicate::And(predicates.into()),
        };
        lemmas.push(Predicate::Implies(
            std::sync::Arc::new(conjunction(requires)),
            std::sync::Arc::new(Predicate::Iff(
                std::sync::Arc::new(Predicate::Ceil(term.clone())),
                std::sync::Arc::new(conjunction(condition)),
            )),
        ));
    }
    if !lemmas.is_empty() {
        state.domain_lemmas.insert(term.clone(), lemmas.into());
    }
}

/// Admit a plan's conditions: every term an atom reads is pure (`eligible_operand`, memoized
/// over the shared DAG, so a shared argument costs its distinct nodes once per query), and no
/// atom reads a term-level `\and`, whose definedness is more than its operands' (the
/// translation refuses a non-Boolean one). One unit of `remaining` per predicate node and term
/// read; the terms are not walked as trees.
/// Whether `term` holds a term-level `\and`. Each distinct node is read once per query: the
/// nodes of a walk that found none are recorded (`TranslationState::conjunction_free`), and one
/// unit of `remaining` is charged per node read; `true` when the budget runs out, which refuses
/// the plan.
#[cfg(any(feature = "z3", test))]
fn holds_term_conjunction(
    state: &mut TranslationState,
    term: &Term,
    remaining: &mut usize,
) -> bool {
    let mut seen = FxHashSet::default();
    let mut pending = vec![term];
    while let Some(term) = pending.pop() {
        if state.conjunction_free.contains(term) || !seen.insert(term.clone()) {
            continue;
        }
        if *remaining == 0 || matches!(term.kind(), TermKind::And(..)) {
            return true;
        }
        *remaining -= 1;
        pending.extend(crate::deferred::children(term));
    }
    state.conjunction_free.extend(seen);
    false
}

#[cfg(any(feature = "z3", test))]
fn admit_conditions(
    state: &mut TranslationState,
    conditions: &[Predicate],
    remaining: &mut usize,
) -> bool {
    enum Pending<'a> {
        Predicate(&'a Predicate),
        Term(&'a Term),
    }
    if conditions.len() > *remaining {
        return false;
    }
    let mut pending = conditions
        .iter()
        .map(Pending::Predicate)
        .collect::<Vec<_>>();
    while let Some(node) = pending.pop() {
        if *remaining == 0 {
            return false;
        }
        *remaining -= 1;
        match node {
            Pending::Term(term) => {
                if !state.eligible_operand(term) || holds_term_conjunction(state, term, remaining) {
                    return false;
                }
            }
            Pending::Predicate(predicate) => match predicate {
                Predicate::Term(t) => pending.push(Pending::Term(t)),
                Predicate::Equals(a, b) => pending.extend([Pending::Term(a), Pending::Term(b)]),
                Predicate::Not(p) | Predicate::Exists(_, p) | Predicate::Forall(_, p) => {
                    pending.push(Pending::Predicate(p));
                }
                Predicate::And(ps) | Predicate::Or(ps) => {
                    if ps.len() > *remaining {
                        return false;
                    }
                    pending.extend(ps.iter().map(Pending::Predicate));
                }
                Predicate::Implies(a, b) | Predicate::Iff(a, b) => {
                    pending.extend([Pending::Predicate(a), Pending::Predicate(b)]);
                }
                Predicate::Ceil(t) | Predicate::Defined(t) | Predicate::Floor(t) => {
                    if !state.eligible_operand(t) {
                        return false;
                    }
                }
                Predicate::In(a, b) => {
                    if !state.eligible_operand(a) || !state.eligible_operand(b) {
                        return false;
                    }
                }
                Predicate::True | Predicate::False | Predicate::Absent(_) => {}
            },
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        definition::BackendDefinition,
        smt::{CongruencePolicy, Exactness, translate_query_in_state},
        stop::{CancellationToken, StopCause},
        substitution::Substitution,
    };
    use std::sync::Arc;

    fn definition() -> BackendDefinition {
        let syntax = k_rust_kore::kore::parser::parse_definition(
            r#"[] module MAIN
              hooked-sort SortInt{} [hook{}("INT.Int"),hasDomainValues{}()]
              symbol f{}(SortInt{}) : SortInt{} [function{}()]
              symbol effect{}(SortInt{}) : SortInt{} [function{}(),impure{}()]
            endmodule []"#,
        )
        .unwrap();
        BackendDefinition::internalize(&syntax, "MAIN").unwrap()
    }

    /// Two applications of `f`, so that its domain function keeps its rank (a single point
    /// is a constant, [`a_domain_applied_at_one_point_is_a_constant`]).
    #[test]
    fn portable_domains_retain_argument_rank_and_conservative_model_evidence() {
        let definition = definition();
        let term = |source: &str| {
            definition
                .internalize_term(
                    &k_rust_kore::kore::parser::parse_pattern(source).unwrap(),
                    &[],
                )
                .unwrap()
        };
        let checked = [
            Predicate::Ceil(term("f{}(X:SortInt{})")),
            Predicate::Ceil(term("f{}(Y:SortInt{})")),
        ];
        let mut state = TranslationState::new();
        state.congruence = CongruencePolicy::from_definition(&definition).map(Arc::new);
        prepare(&definition, &mut state, &[], &Substitution::new(), &checked).unwrap();
        let (state, declarations, _, _, checked) =
            translate_query_in_state(&[], &Substitution::new(), &checked, state).unwrap();
        assert_eq!(state.exactness(), Exactness::Approximate);
        assert!(declarations.iter().any(|d| d.ends_with("(Int) Bool)")));
        assert!(SExpr::parse(&checked.to_string()).is_ok());
    }

    /// The declarations and the checked conjunction of the portable query over `checked`.
    fn domain_query(
        definition: &BackendDefinition,
        checked: &[Predicate],
    ) -> (Vec<String>, String) {
        let (declarations, _, checked) = seeded_domain_query(definition, checked, |_| {});
        (declarations, checked)
    }

    /// As [`domain_query`], with `seed` applied to the prepared state before translation, and
    /// the known part (which carries the domain facts) returned as well.
    fn seeded_domain_query(
        definition: &BackendDefinition,
        checked: &[Predicate],
        seed: impl FnOnce(&mut TranslationState),
    ) -> (Vec<String>, Vec<String>, String) {
        let mut state = TranslationState::new();
        state.congruence = CongruencePolicy::from_definition(definition).map(Arc::new);
        prepare(definition, &mut state, &[], &Substitution::new(), checked).unwrap();
        seed(&mut state);
        let (state, declarations, _, known, checked) =
            translate_query_in_state(&[], &Substitution::new(), checked, state).unwrap();
        assert_eq!(state.exactness(), Exactness::Approximate);
        let known = known.iter().map(ToString::to_string).collect();
        (declarations, known, checked.to_string())
    }

    /// The domain function declarations of a query: functions or constants of result `Bool`.
    fn domain_declarations(declarations: &[String]) -> Vec<&str> {
        declarations
            .iter()
            .filter(|d| d.starts_with("(declare-fun") && d.ends_with(" Bool)"))
            .map(String::as_str)
            .collect()
    }

    /// GAP K23: a node whose variables no quantifier binds is named once, in the scope of its
    /// own variables, however many binders read it. In `\exists Y. (f(X) = Y /\ \exists Z.
    /// f(X) = Z)` the value and the domain of `f(X)` mention neither `Y` nor `Z`, so each is one
    /// `let` outside both quantifiers, which both bodies read: a `let` is visible in its scope,
    /// and a term without the bound variable denotes the same inside the binder and outside.
    /// The domain function is then applied at one point outside every quantifier, so it is a
    /// constant ([`a_domain_applied_at_one_point_is_a_constant`]).
    #[test]
    fn a_node_read_under_nested_binders_is_named_once_in_the_scope_of_its_variables() {
        let definition = definition();
        let term = |source: &str| {
            definition
                .internalize_term(
                    &k_rust_kore::kore::parser::parse_pattern(source).unwrap(),
                    &[],
                )
                .unwrap()
        };
        let int = crate::term::Sort::simple("SortInt");
        let y = crate::term::Variable::new("Y", int);
        let z = crate::term::Variable::new("Z", int);
        let value = term("f{}(X:SortInt{})");
        let inner = Predicate::Exists(
            z.clone(),
            Arc::new(Predicate::Equals(value.clone(), Term::variable(z))),
        );
        let outer = Predicate::Exists(
            y.clone(),
            Arc::new(Predicate::And(
                vec![Predicate::Equals(value, Term::variable(y)), inner].into(),
            )),
        );
        let (declarations, _, checked) = seeded_domain_query(&definition, &[outer], |_| {});
        let [domain] = domain_declarations(&declarations)[..] else {
            panic!("one domain declaration: {declarations:?}");
        };
        assert!(domain.ends_with(" () Bool)"), "{domain}");
        let parsed = SExpr::parse(&checked).unwrap();
        fn lets(expression: &SExpr, names: &mut Vec<String>) {
            if let SExpr::List(items) = expression {
                if let [SExpr::Atom(head), SExpr::List(bindings), _] = items.as_slice()
                    && head == "let"
                {
                    for binding in bindings {
                        if let SExpr::List(pair) = binding
                            && let [SExpr::Atom(name), _] = pair.as_slice()
                        {
                            names.push(name.clone());
                        }
                    }
                }
                for item in items {
                    lets(item, names);
                }
            }
        }
        let mut names = Vec::new();
        lets(&parsed, &mut names);
        assert_eq!(names.len(), 2, "one value and one domain let: {checked}");
        let SExpr::List(conjunction) = &parsed else {
            panic!("a checked conjunction: {checked}");
        };
        let [_, SExpr::List(conjunct)] = conjunction.as_slice() else {
            panic!("one checked conjunct: {checked}");
        };
        assert_eq!(
            conjunct.first(),
            Some(&SExpr::atom("let")),
            "the lets enclose the quantifiers: {checked}"
        );
    }

    /// A domain function applied at a single point outside every quantifier is a Boolean
    /// constant: it has one value in each interpretation, so the function and the constant
    /// readings are equisatisfiable. Two points keep the function, which then carries domain
    /// congruence; so does one occurrence under a quantifier, which denotes a point per value of
    /// the bound variable.
    #[test]
    fn a_domain_applied_at_one_point_is_a_constant() {
        let definition = definition();
        let term = |source: &str| {
            definition
                .internalize_term(
                    &k_rust_kore::kore::parser::parse_pattern(source).unwrap(),
                    &[],
                )
                .unwrap()
        };
        let (declarations, checked) =
            domain_query(&definition, &[Predicate::Ceil(term("f{}(X:SortInt{})"))]);
        let [domain] = domain_declarations(&declarations)[..] else {
            panic!("one domain declaration: {declarations:?}");
        };
        assert!(domain.ends_with(" () Bool)"), "{domain}");
        let name = domain.split_whitespace().nth(1).unwrap();
        assert!(!checked.contains(&format!("({name} ")), "{checked}");

        let (declarations, _) = domain_query(
            &definition,
            &[
                Predicate::Ceil(term("f{}(X:SortInt{})")),
                Predicate::Not(Arc::new(Predicate::Ceil(term("f{}(Y:SortInt{})")))),
            ],
        );
        let [domain] = domain_declarations(&declarations)[..] else {
            panic!("one domain declaration: {declarations:?}");
        };
        assert!(domain.ends_with(" (Int) Bool)"), "{domain}");

        let bound = Predicate::Forall(
            crate::term::Variable::new("X", crate::term::Sort::simple("SortInt")),
            Arc::new(Predicate::Ceil(term("f{}(X:SortInt{})"))),
        );
        let (declarations, _) = domain_query(&definition, &[bound]);
        let [domain] = domain_declarations(&declarations)[..] else {
            panic!("one domain declaration: {declarations:?}");
        };
        assert!(domain.ends_with(" (Int) Bool)"), "{domain}");
    }

    /// A domain function applied once keeps its rank wherever the query mentions it at
    /// another place: inside a derived definition (whose body is not rewritten, so a constant
    /// there would be ill-sorted), at an unapplied occurrence, or under `exists`, which, like
    /// `forall`, denotes a point per value of the bound variable.
    #[test]
    fn a_domain_mentioned_elsewhere_or_under_exists_keeps_its_rank() {
        let definition = definition();
        let term = |source: &str| {
            definition
                .internalize_term(
                    &k_rust_kore::kore::parser::parse_pattern(source).unwrap(),
                    &[],
                )
                .unwrap()
        };
        let once = [Predicate::Ceil(term("f{}(X:SortInt{})"))];
        // The name translation gives the domain function of `f`; it is deterministic.
        let (declarations, _) = domain_query(&definition, &once);
        let [constant] = domain_declarations(&declarations)[..] else {
            panic!("one domain declaration: {declarations:?}");
        };
        let name = constant.split_whitespace().nth(1).unwrap().to_owned();
        let function = format!("(declare-fun {name} (Int) Bool)");
        let applied = format!("({name} ");

        let derived = format!("(define-fun-rec D ((x Int)) Bool ({name} x))");
        let (declarations, _, checked) = seeded_domain_query(&definition, &once, |state| {
            state.derived_definitions.push(derived.clone());
        });
        assert_eq!(domain_declarations(&declarations), [function.as_str()]);
        assert!(declarations.contains(&derived), "{declarations:?}");
        assert!(checked.contains(&applied), "{checked}");

        let fact = format!("(= {name} {name})");
        let (declarations, known, checked) = seeded_domain_query(&definition, &once, |state| {
            state.domain_facts.push(SExpr::parse(&fact).unwrap());
        });
        assert_eq!(domain_declarations(&declarations), [function.as_str()]);
        assert_eq!(known, [fact]);
        assert!(checked.contains(&applied), "{checked}");

        let bound = Predicate::Exists(
            crate::term::Variable::new("X", crate::term::Sort::simple("SortInt")),
            Arc::new(Predicate::Ceil(term("f{}(X:SortInt{})"))),
        );
        let (declarations, checked) = domain_query(&definition, &[bound]);
        let [domain] = domain_declarations(&declarations)[..] else {
            panic!("one domain declaration: {declarations:?}");
        };
        assert!(domain.ends_with(" (Int) Bool)"), "{domain}");
        let name = domain.split_whitespace().nth(1).unwrap();
        assert!(checked.contains("(exists "), "{checked}");
        assert!(checked.contains(&format!("({name} ")), "{checked}");
    }

    #[test]
    fn domain_preparation_propagates_a_cancelled_request() {
        let definition = definition();
        let token = CancellationToken::new();
        token.cancel();
        let mut state = TranslationState::new();
        let stopped = token
            .scope(|| prepare(&definition, &mut state, &[], &Substitution::new(), &[]))
            .unwrap_err();
        assert_eq!(stopped.into_cause(), StopCause::Cancelled);
    }
}
