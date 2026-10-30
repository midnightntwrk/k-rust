//! Query-local readings of pure functional values and their source domains.
//!
//! A value UF totalizes a partial function without asserting that it exists. Its domain UF
//! names only the unresolved head obligation; canonical ceil rules and strict child domains
//! retain source conditions and every original argument obligation. Domain lets are local to a predicate's
//! lexical scope, so neither shared DAGs nor quantifiers duplicate or capture their meanings.

use std::collections::{BTreeMap, BTreeSet};

use super::{SExpr, TranslationError, TranslationState};
use crate::{
    rule::Predicate,
    term::{FunctionType, SymbolType, Term, TermKind},
};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct SharedDomains {
    values: BTreeMap<Term, SExpr>,
    active: BTreeSet<Term>,
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

    pub(super) fn translate_domain(&mut self, term: &Term) -> Result<SExpr, TranslationError> {
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
            return Ok(self.abstract_predicate(&original));
        }
        let scope = self
            .shared_domains
            .as_mut()
            .expect("predicate domain scope");
        if let Some(value) = scope.values.get(term) {
            return Ok(value.clone());
        }
        // Source ceil equations can be recursive. Use an opaque atom to stop expansion;
        // an actual lexical reentry is tied to the completed domain below. A depth-limited
        // graph remains conservative rather than acquiring an invented total domain.
        let reentrant = scope.active.contains(term);
        if scope.active.len() >= 128 || reentrant {
            let reference = self.abstract_predicate(&original);
            if reentrant {
                self.shared_domains
                    .as_mut()
                    .expect("active scope")
                    .reentrant
                    .insert(term.clone(), reference.clone());
            }
            return Ok(reference);
        }
        scope.active.insert(term.clone());
        let resolved = summary.is_none()
            && (observation.is_some() || plan.as_ref().is_some_and(|p| !p.contains(&original)));
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
                        parts.push(self.translate_domain_head(term)?);
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
        let scope = self.shared_domains.as_mut().expect("active domain scope");
        scope.active.remove(term);
        let value = result?;
        let reference = if matches!(value, SExpr::Atom(_)) {
            scope.values.insert(term.clone(), value.clone());
            value
        } else {
            let name = self.fresh_name();
            let reference = SExpr::atom(name.clone());
            let scope = self.shared_domains.as_mut().expect("active domain scope");
            scope.bindings.push((name, value));
            scope.values.insert(term.clone(), reference.clone());
            reference
        };
        let reentrant = self
            .shared_domains
            .as_mut()
            .expect("active scope")
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
                    SExpr::application("=", vec![head, reference.clone()]),
                ],
            );
            self.record_source_fact(fact)?;
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
    let mut seen = BTreeSet::new();
    while !predicates.is_empty() || !candidates.is_empty() {
        stop::check()?;
        if remaining == 0 {
            break;
        }
        remaining -= 1;
        if let Some(predicate) = predicates.pop() {
            match predicate {
                Predicate::Ceil(term) | Predicate::Defined(term) => candidates.push(term),
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
                | Predicate::Equals(..)
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
    }
    Ok(())
}

/// One source-owned head domain shared by observation discovery and final domain preparation.
/// The cached predicates contain no query facts or solver names; strict operands stay explicit.
#[cfg(any(feature = "z3", test))]
pub(super) fn domain_plan(
    definition: &crate::definition::BackendDefinition,
    state: &mut TranslationState,
    term: &Term,
    remaining: &mut usize,
) -> crate::stop::Stoppable<Option<std::sync::Arc<[Predicate]>>> {
    use crate::definedness::{apply_ceil_equation, request_definedness};
    crate::stop::check()?;
    if let Some(plan) = state.domains.get(term) {
        return Ok(Some(plan.clone()));
    }
    if *remaining == 0 || !state.eligible_operand(term) {
        return Ok(None);
    }
    let mut plan = match term.kind() {
        TermKind::Application { symbol, .. } if state.functional_head(term).is_some() => {
            if symbol.attributes.symbol_type == SymbolType::Function(FunctionType::Partial) {
                match apply_ceil_equation(definition, term) {
                    Some(conditions) if admit_conditions(state, &conditions, remaining) => {
                        request_definedness(definition, conditions)
                            .unwrap_or_else(|_| vec![Predicate::Ceil(term.clone())])
                    }
                    Some(_) | None => vec![Predicate::Ceil(term.clone())],
                }
            } else {
                Vec::new()
            }
        }
        TermKind::Variable(_) | TermKind::DomainValue { .. } | TermKind::Injection { .. } => {
            Vec::new()
        }
        TermKind::Map { entries, .. }
            if definition.map_operations(&term.sort()).is_some()
                && entries.len().saturating_mul(entries.len()) <= *remaining =>
        {
            let Ok(conditions) = crate::definedness::collection_head_domain(definition, term)
            else {
                return Ok(None);
            };
            if !admit_conditions(state, &conditions, remaining) {
                return Ok(None);
            }
            conditions
        }
        TermKind::List { .. } if definition.list_operations(&term.sort()).is_some() => Vec::new(),
        TermKind::Application { .. }
        | TermKind::Map { .. }
        | TermKind::List { .. }
        | TermKind::Set { .. }
        | TermKind::And(..) => return Ok(None),
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

/// Bound the tree work of canonical condition conversion before asking it to traverse a
/// shared value DAG. Opaque domain atoms need no value walk; value atoms must be pure.
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
                if !state.eligible_operand(term) {
                    return false;
                }
                let children = crate::deferred::children(term);
                if children.len() > *remaining {
                    return false;
                }
                pending.extend(children.into_iter().map(Pending::Term));
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
        let mut state = TranslationState::new();
        state.congruence = CongruencePolicy::from_definition(definition).map(Arc::new);
        prepare(definition, &mut state, &[], &Substitution::new(), checked).unwrap();
        let (state, declarations, _, _, checked) =
            translate_query_in_state(&[], &Substitution::new(), checked, state).unwrap();
        assert_eq!(state.exactness(), Exactness::Approximate);
        (declarations, checked.to_string())
    }

    /// The domain function declarations of a query: functions or constants of result `Bool`.
    fn domain_declarations(declarations: &[String]) -> Vec<&str> {
        declarations
            .iter()
            .filter(|d| d.starts_with("(declare-fun") && d.ends_with(" Bool)"))
            .map(String::as_str)
            .collect()
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
