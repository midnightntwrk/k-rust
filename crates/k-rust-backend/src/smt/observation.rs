//! Translate source-checked finite observations while retaining the ordinary value/domain
//! signature. These source consequences are guarded, not asserted caller obligations.

use std::{collections::BTreeMap, sync::Arc};

use super::{SExpr, TranslationError, TranslationState};
use crate::{observation::reading::Reading, rule::Predicate, term::Term};

impl TranslationState {
    /// Forward congruence of the checked source map roles, retaining the original
    /// disjoint-concatenation domain. This does not assert injectivity or extensionality.
    pub(super) fn translate_map(
        &mut self,
        collection: &Arc<crate::term::MapDefinition>,
        entries: &crate::term::Items<(Term, Term)>,
        rest: &Option<Term>,
    ) -> Result<SExpr, TranslationError> {
        self.approximate(super::Exactness::Approximate);
        let sort = crate::term::Sort::simple(collection.map_sort.clone());
        let role = |name: crate::term::Name, arguments| super::CongruenceHead::Application {
            name,
            sorts: vec![],
            arguments,
            result: sort,
        };
        let unit = self.congruence_name(role(collection.symbols.unit.clone(), vec![]));
        let item = self.congruence_name(role(
            collection.symbols.element.clone(),
            vec![collection.key_sort, collection.value_sort],
        ));
        let concat =
            self.congruence_name(role(collection.symbols.concat.clone(), vec![sort, sort]));
        let mut value = match rest {
            Some(base) => self.translate_term(base)?,
            None => SExpr::atom(unit),
        };
        for (key, entry) in entries.iter().rev() {
            let entry = SExpr::application(
                item.clone(),
                vec![self.translate_term(key)?, self.translate_term(entry)?],
            );
            value = SExpr::application(concat.clone(), vec![entry, value]);
        }
        Ok(value)
    }

    /// Forward congruence of the actual source list roles. No injectivity or general
    /// sequence theory is asserted; original list domains remain separately required.
    pub(super) fn translate_list(
        &mut self,
        collection: &Arc<crate::term::ListDefinition>,
        heads: &crate::term::Items<Term>,
        rest: &Option<(Term, crate::term::Items<Term>)>,
    ) -> Result<SExpr, TranslationError> {
        self.approximate(super::Exactness::Approximate);
        let sort = crate::term::Sort::simple(collection.list_sort.clone());
        let role = |name: crate::term::Name, arguments| super::CongruenceHead::Application {
            name,
            sorts: vec![],
            arguments,
            result: sort,
        };
        let unit = self.congruence_name(role(collection.symbols.unit.clone(), vec![]));
        let item = self.congruence_name(role(
            collection.symbols.element.clone(),
            vec![collection.element_sort],
        ));
        let concat =
            self.congruence_name(role(collection.symbols.concat.clone(), vec![sort, sort]));
        let cons = |value, tail| {
            SExpr::application(
                concat.clone(),
                vec![SExpr::application(item.clone(), vec![value]), tail],
            )
        };
        let mut value = if let Some((base, tails)) = rest {
            if tails.is_empty() {
                self.translate_term(base)?
            } else {
                let mut suffix = SExpr::atom(unit.clone());
                for tail in tails.iter().rev() {
                    suffix = cons(self.translate_term(tail)?, suffix);
                }
                SExpr::application(concat.clone(), vec![self.translate_term(base)?, suffix])
            }
        } else {
            SExpr::atom(unit)
        };
        for head in heads.iter().rev() {
            value = cons(self.translate_term(head)?, value);
        }
        Ok(value)
    }

    pub(super) fn translate_observation(
        &mut self,
        term: &Term,
        reading: &Arc<Reading>,
    ) -> Result<SExpr, TranslationError> {
        // Always keep the original functional interpretation. A source equation about this
        // instance then also transports through opaque equal arguments and higher contexts.
        let original = self.translate_term_node_plain(term)?;
        let value = self.observation_value(reading, &original, &mut BTreeMap::new())?;
        let domain = self.translate_predicate(&Predicate::Ceil(term.clone()))?;
        self.approximate(super::Exactness::Approximate);
        self.record_source_fact(SExpr::application(
            "=>",
            vec![
                domain,
                SExpr::application("=", vec![original.clone(), value]),
            ],
        ))?;
        Ok(original)
    }

    fn observation_value(
        &mut self,
        reading: &Arc<Reading>,
        fallback: &SExpr,
        memo: &mut BTreeMap<usize, SExpr>,
    ) -> Result<SExpr, TranslationError> {
        let key = Arc::as_ptr(reading) as usize;
        if let Some(value) = memo.get(&key) {
            return Ok(value.clone());
        }
        let value = match reading.as_ref() {
            Reading::Leaf(term) => self.translate_term(term)?,
            Reading::Missing => fallback.clone(),
            Reading::If { test, yes, no } => SExpr::application(
                "ite",
                vec![
                    self.translate_predicate(test)?,
                    self.observation_value(yes, fallback, memo)?,
                    self.observation_value(no, fallback, memo)?,
                ],
            ),
        };
        let value = if matches!(value, SExpr::List(_)) {
            if self.shared_terms.is_some() {
                let name = self.fresh_name();
                self.shared_terms
                    .as_mut()
                    .expect("value scope")
                    .bindings
                    .push((name.clone(), value));
                SExpr::atom(name)
            } else {
                value
            }
        } else {
            value
        };
        memo.insert(key, value.clone());
        Ok(value)
    }

    pub(super) fn observation_domain(
        &mut self,
        term: &Term,
        reading: &Arc<Reading>,
    ) -> Result<SExpr, TranslationError> {
        let mut domains = Vec::new();
        // The source state and all original operands stay strict, including overwritten
        // values and both operands of a source state conditional.
        for child in crate::deferred::children(term) {
            domains.push(self.translate_domain(child)?);
        }
        domains.push(self.observation_leaf_domain(reading, &mut BTreeMap::new())?);
        Ok(SExpr::application("and", domains))
    }

    fn observation_leaf_domain(
        &mut self,
        reading: &Arc<Reading>,
        memo: &mut BTreeMap<usize, SExpr>,
    ) -> Result<SExpr, TranslationError> {
        let key = Arc::as_ptr(reading) as usize;
        if let Some(value) = memo.get(&key) {
            return Ok(value.clone());
        }
        let value = match reading.as_ref() {
            Reading::Leaf(term) => self.translate_domain(term)?,
            Reading::Missing => SExpr::atom("false"),
            Reading::If { test, yes, no } => SExpr::application(
                "ite",
                vec![
                    self.translate_predicate(test)?,
                    self.observation_leaf_domain(yes, memo)?,
                    self.observation_leaf_domain(no, memo)?,
                ],
            ),
        };
        let value = if matches!(value, SExpr::List(_)) {
            let name = self.fresh_name();
            self.shared_domains
                .as_mut()
                .expect("domain scope")
                .bindings
                .push((name.clone(), value));
            SExpr::atom(name)
        } else {
            value
        };
        memo.insert(key, value.clone());
        Ok(value)
    }
}

/// Discover plans from all demanded source terms. The additional ceil predicates prepare
/// domains of generated source leaves; they are never added to the query's assumptions.
#[cfg(any(feature = "z3", test))]
pub(super) fn prepare(
    definition: &crate::definition::BackendDefinition,
    state: &mut TranslationState,
    known: &[Predicate],
    substitution: &crate::substitution::Substitution,
    checked: &[Predicate],
) -> crate::stop::Stoppable<Vec<Predicate>> {
    use crate::{observation::reading::Builder, stop};
    use std::collections::BTreeSet;
    let mut remaining = 16_384usize;
    if known
        .len()
        .saturating_add(checked.len())
        .saturating_add(substitution.len())
        > remaining
    {
        return Ok(Vec::new());
    }
    let Some(originals) = original_terms(known, substitution, checked)? else {
        return Ok(Vec::new());
    };
    let mut list_prefixes = BTreeMap::<Term, usize>::new();
    for term in &originals {
        stop::check()?;
        if let crate::term::TermKind::Application { arguments, .. } = term.kind()
            && let Some(input) = arguments.first()
            && let Some((list, count)) = definition
                .list_operations(&input.sort())
                .and_then(|ops| ops.demanded_prefix(term))
        {
            let demand = list_prefixes.entry(list.clone()).or_default();
            *demand = (*demand).max(count);
        }
    }
    let mut predicates = known.iter().chain(checked).cloned().collect::<Vec<_>>();
    let mut terms = substitution.values().cloned().collect::<Vec<_>>();
    let mut builder = Builder::new(definition);
    let mut seen = BTreeSet::new();
    let mut seen_readings = BTreeSet::new();
    let mut readings = Vec::new();
    let mut domains = Vec::new();
    let mut equalities = BTreeSet::new();
    // Equalities select additional demands only. Even an equality under a negation or a
    // different binder may safely suggest a source-law instance; it is never assumed here.
    let mut aliases = BTreeMap::<Term, Vec<Term>>::new();
    for (variable, value) in substitution {
        stop::check()?;
        remaining -= 1;
        if variable.sort == value.sort() && definition.map_operations(&variable.sort).is_some() {
            let variable = Term::variable(variable.clone());
            aliases
                .entry(variable.clone())
                .or_default()
                .push(value.clone());
            aliases.entry(value.clone()).or_default().push(variable);
        }
    }
    while !terms.is_empty() || !predicates.is_empty() || !readings.is_empty() {
        stop::check()?;
        if remaining == 0 {
            break;
        }
        remaining -= 1;
        if let Some(reading) = readings.pop() {
            let reading: Arc<Reading> = reading;
            if !seen_readings.insert(Arc::as_ptr(&reading) as usize) {
                continue;
            }
            match reading.as_ref() {
                Reading::Leaf(term) => terms.push(term.clone()),
                Reading::Missing => {}
                Reading::If { test, yes, no } => {
                    predicates.push(test.clone());
                    readings.extend([yes.clone(), no.clone()]);
                }
            }
        } else if let Some(predicate) = predicates.pop() {
            match predicate {
                Predicate::Term(t) | Predicate::Ceil(t) | Predicate::Defined(t) => {
                    if let crate::term::TermKind::Application {
                        symbol, arguments, ..
                    } = t.kind()
                        && matches!(
                            symbol.attributes.hook.as_deref(),
                            Some("KEQUAL.eq" | "KEQUAL.ne")
                        )
                        && let [a, b] = arguments.as_slice()
                    {
                        equality_demands(
                            &mut builder,
                            state,
                            a,
                            b,
                            &mut equalities,
                            &mut predicates,
                            &mut remaining,
                        )?;
                    }
                    terms.push(t);
                }
                Predicate::Equals(a, b) => {
                    equality_demands(
                        &mut builder,
                        state,
                        &a,
                        &b,
                        &mut equalities,
                        &mut predicates,
                        &mut remaining,
                    )?;
                    if a.sort() == b.sort() && definition.map_operations(&a.sort()).is_some() {
                        aliases.entry(a.clone()).or_default().push(b.clone());
                        aliases.entry(b.clone()).or_default().push(a.clone());
                    }
                    terms.extend([a, b]);
                }
                Predicate::Not(p) | Predicate::Exists(_, p) | Predicate::Forall(_, p) => {
                    predicates.push((*p).clone())
                }
                Predicate::And(ps) | Predicate::Or(ps) => {
                    if ps.len() > remaining {
                        break;
                    }
                    predicates.extend(ps.iter().cloned());
                }
                Predicate::Implies(a, b) | Predicate::Iff(a, b) => {
                    predicates.extend([(*a).clone(), (*b).clone()])
                }
                Predicate::True
                | Predicate::False
                | Predicate::Floor(_)
                | Predicate::In(..)
                | Predicate::Absent(_) => {}
            }
        } else if let Some(term) = terms.pop() {
            if !seen.insert(term.clone()) {
                continue;
            }
            if let Some(plan) =
                super::functional::domain_plan(definition, state, &term, &mut remaining)?
            {
                if plan.len() > remaining {
                    break;
                }
                predicates.extend(
                    plan.iter()
                        .filter(|p| **p != Predicate::Ceil(term.clone()))
                        .cloned(),
                );
            }
            if let Some(ops) = definition.map_operations(&term.sort()) {
                state
                    .map_congruence
                    .insert(term.sort(), ops.collection.clone());
            }
            if let Some(ops) = definition.list_operations(&term.sort()) {
                state
                    .list_congruence
                    .insert(term.sort(), ops.collection.clone());
                if originals.contains(&term)
                    && !matches!(term.kind(), crate::term::TermKind::List { .. })
                    && state.eligible_operand(&term)
                    && let Some(fact) = ops.empty_fact(&term)
                {
                    predicates.push(fact.clone());
                    state
                        .observation_facts
                        .entry(term.clone())
                        .or_default()
                        .push(fact);
                }
            }
            if let Some(reading) = builder.of(&term)? {
                readings.push(reading.clone());
                state.observations.insert(term.clone(), reading);
            } else if let crate::term::TermKind::Application {
                symbol,
                sort_arguments,
                arguments,
            } = term.kind()
            {
                let position = match symbol.attributes.hook.as_deref() {
                    Some("MAP.lookup") if arguments.len() == 2 => Some(0),
                    Some("MAP.in_keys") if arguments.len() == 2 => Some(1),
                    _ => None,
                };
                if let Some(position) = position {
                    let mut pending = vec![arguments[position].clone()];
                    let mut reached = BTreeSet::new();
                    let mut demands = Vec::new();
                    while let Some(map) = pending.pop() {
                        stop::check()?;
                        if !reached.insert(map.clone()) {
                            continue;
                        }
                        let Some(next) = aliases.get(&map) else {
                            continue;
                        };
                        if next.len() > remaining {
                            break;
                        }
                        remaining -= next.len();
                        for alternative in next {
                            if alternative != &arguments[position] {
                                let mut arguments = arguments.clone();
                                arguments[position] = alternative.clone();
                                let source =
                                    Term::application(symbol.clone(), *sort_arguments, arguments);
                                if let Some(reading) = builder.of(&source)? {
                                    state.observations.insert(source.clone(), reading);
                                    terms.push(source.clone());
                                    demands.push(source);
                                }
                            }
                            pending.push(alternative.clone());
                        }
                    }
                    if !demands.is_empty() {
                        state.observation_demands.insert(term.clone(), demands);
                    }
                }
            }
            if originals.contains(&term)
                && state.eligible_operand(&term)
                && let crate::term::TermKind::Application { arguments, .. } = term.kind()
                && let [input] = arguments.as_slice()
                && let Some(selector) = definition.selector(&input.sort(), &term.sort())
                && selector.project(input.clone()).as_ref() == Some(&term)
            {
                // A projected value used by arithmetic may later be simplified to a
                // literal. Demand its checked inverse now, so that stored-item equality
                // still transports that value through reconstructed state contexts.
                let inverse = selector.embed(term.clone());
                if inverse != term {
                    let reading = Arc::new(Reading::Leaf(input.clone()));
                    state.observations.insert(inverse.clone(), reading.clone());
                    readings.push(reading);
                    terms.push(inverse.clone());
                    state
                        .observation_demands
                        .entry(term.clone())
                        .or_default()
                        .push(inverse);
                }
            }
            if originals.contains(&term)
                && !state.observations.contains_key(&term)
                && state.eligible_operand(&term)
                && let Some(canonical) = definition
                    .products()
                    .and_then(|p| p.canonical(&term))
                    .or_else(|| {
                        if matches!(term.kind(), crate::term::TermKind::List { .. }) {
                            return None;
                        }
                        definition
                            .list_operations(&term.sort())?
                            .prefix(term.clone(), list_prefixes.get(&term).copied().unwrap_or(1))
                    })
                && let Some(reading) = builder.of(&canonical)?
            {
                // Only values present in the original query get this demand. Generated
                // fields do not recursively unfold products or discover new witnesses.
                state
                    .observations
                    .insert(canonical.clone(), reading.clone());
                readings.push(reading);
                terms.push(canonical.clone());
                state
                    .observation_demands
                    .entry(term.clone())
                    .or_default()
                    .push(canonical);
            }
            let children = crate::deferred::children(&term);
            if children.len() > remaining {
                break;
            }
            terms.extend(children.into_iter().cloned());
            domains.push(Predicate::Ceil(term));
        }
    }
    Ok(domains)
}

/// Suggest finite source consequences at corresponding pure-context operands. The compared
/// equality, including one under a negation, supplies no assumption to these consequences.
#[cfg(any(feature = "z3", test))]
fn equality_demands(
    builder: &mut crate::observation::reading::Builder<'_>,
    state: &mut TranslationState,
    left: &Term,
    right: &Term,
    seen: &mut std::collections::BTreeSet<(Term, Term)>,
    predicates: &mut Vec<Predicate>,
    remaining: &mut usize,
) -> crate::stop::Stoppable<()> {
    use crate::term::TermKind;
    let mut pending = vec![(left.clone(), right.clone())];
    while let Some((a, b)) = pending.pop() {
        crate::stop::check()?;
        if a == b || a.sort() != b.sort() {
            continue;
        }
        let pair = if a < b {
            (a.clone(), b.clone())
        } else {
            (b.clone(), a.clone())
        };
        if !seen.insert(pair) {
            continue;
        }
        if *remaining == 0 {
            break;
        }
        *remaining -= 1;
        if let Some(fact) = builder.map_equality(&a, &b)? {
            predicates.push(fact.clone());
            state
                .observation_facts
                .entry(a.clone())
                .or_default()
                .push(fact);
        }
        let children = match (a.kind(), b.kind()) {
            (
                TermKind::Application {
                    symbol: x,
                    sort_arguments: sx,
                    arguments: ax,
                },
                TermKind::Application {
                    symbol: y,
                    sort_arguments: sy,
                    arguments: ay,
                },
            ) if x == y
                && sx == sy
                && ax.len() == ay.len()
                && !matches!(
                    x.attributes.hook.as_deref(),
                    Some("MAP.update" | "MAP.remove")
                ) =>
            {
                ax.iter()
                    .zip(ay)
                    .map(|(x, y)| (x.clone(), y.clone()))
                    .collect::<Vec<_>>()
            }
            (
                TermKind::Injection {
                    source: sx,
                    target: tx,
                    term: x,
                },
                TermKind::Injection {
                    source: sy,
                    target: ty,
                    term: y,
                },
            ) if sx == sy && tx == ty => vec![(x.clone(), y.clone())],
            _ => Vec::new(),
        };
        if children.len() > *remaining {
            break;
        }
        pending.extend(children);
    }
    Ok(())
}

#[cfg(any(feature = "z3", test))]
fn original_terms(
    known: &[Predicate],
    substitution: &crate::substitution::Substitution,
    checked: &[Predicate],
) -> crate::stop::Stoppable<Option<std::collections::BTreeSet<Term>>> {
    let mut predicates = known.iter().chain(checked).collect::<Vec<_>>();
    let mut terms = substitution.values().collect::<Vec<_>>();
    let mut seen = std::collections::BTreeSet::new();
    let mut remaining = 16_384usize;
    while !predicates.is_empty() || !terms.is_empty() {
        crate::stop::check()?;
        if remaining == 0 {
            return Ok(None);
        }
        remaining -= 1;
        if let Some(predicate) = predicates.pop() {
            match predicate {
                Predicate::Term(t) | Predicate::Ceil(t) | Predicate::Defined(t) => terms.push(t),
                Predicate::Equals(a, b) => terms.extend([a, b]),
                Predicate::Not(p) | Predicate::Exists(_, p) | Predicate::Forall(_, p) => {
                    predicates.push(p)
                }
                Predicate::And(ps) | Predicate::Or(ps) => {
                    if ps.len() > remaining {
                        return Ok(None);
                    }
                    predicates.extend(ps.iter());
                }
                Predicate::Implies(a, b) | Predicate::Iff(a, b) => {
                    predicates.extend([a.as_ref(), b.as_ref()])
                }
                Predicate::True
                | Predicate::False
                | Predicate::Floor(_)
                | Predicate::In(..)
                | Predicate::Absent(_) => {}
            }
        } else if let Some(term) = terms.pop() {
            if !seen.insert(term.clone()) {
                continue;
            }
            let children = crate::deferred::children(term);
            if children.len() > remaining {
                return Ok(None);
            }
            terms.extend(children);
        }
    }
    Ok(Some(seen))
}

/// Keep exact summary-only queries on their existing path. When a signature also has an
/// opaque occurrence, specialized instances must transport through that same ordinary UF.
#[cfg(feature = "z3")]
pub(super) fn finish_summary_readings(
    state: &mut TranslationState,
    demands: &[Predicate],
) -> crate::stop::Stoppable<()> {
    let mut opaque = std::collections::BTreeSet::new();
    for demand in demands {
        crate::stop::check()?;
        let Predicate::Ceil(term) = demand else {
            continue;
        };
        if super::summary::reading(&state.summaries, term).is_none()
            && let Some(head) = state.congruence_head(term)
        {
            opaque.insert(head);
        }
    }
    let summaries = state
        .summaries
        .values()
        .map(|r| r.summary.clone())
        .collect::<Vec<_>>();
    for summary in summaries {
        crate::stop::check()?;
        if let Some(head) = state.functional_head(&summary.formal)
            && opaque.contains(&head)
        {
            state.summary_congruence.insert(head.clone());
            state
                .summary_cases
                .entry(head)
                .or_default()
                .push(summary.key.clone());
        }
    }
    for term in state.observations.keys().cloned().collect::<Vec<_>>() {
        crate::stop::check()?;
        if super::summary::reading(&state.summaries, &term).is_some()
            && state
                .functional_head(&term)
                .is_none_or(|head| !state.summary_congruence.contains(&head))
        {
            // The existing complete summary already supplies this reading, with its
            // original exactness. No foreign carrier/value UF is needed for this query.
            state.observations.remove(&term);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{definition::BackendDefinition, substitution::Substitution};
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    fn source() -> &'static str {
        r#"[] module MAIN
          hooked-sort SortInt{} [hook{}("INT.Int"),hasDomainValues{}()]
          hooked-sort SortBool{} [hook{}("BOOL.Bool"),hasDomainValues{}()]
          hooked-sort SortMap{} [hook{}("MAP.Map"),unit{}(unit{}()),element{}(item{}()),concat{}(concat{}())]
          hooked-symbol unit{}() : SortMap{} [function{}(),total{}(),hook{}("MAP.unit")]
          hooked-symbol item{}(SortInt{},SortInt{}) : SortMap{} [function{}(),total{}(),hook{}("MAP.element")]
          hooked-symbol concat{}(SortMap{},SortMap{}) : SortMap{} [function{}(),hook{}("MAP.concat"),assoc{}(),comm{}()]
          hooked-symbol put{}(SortMap{},SortInt{},SortInt{}) : SortMap{} [function{}(),total{}(),hook{}("MAP.update")]
          hooked-symbol get{}(SortMap{},SortInt{}) : SortInt{} [function{}(),hook{}("MAP.lookup")]
          hooked-symbol member{}(SortInt{},SortMap{}) : SortBool{} [function{}(),total{}(),hook{}("MAP.in_keys")]
          hooked-symbol remove{}(SortMap{},SortInt{}) : SortMap{} [function{}(),total{}(),hook{}("MAP.remove")]
          hooked-symbol choose{S}(SortBool{},S,S) : S [function{}(),total{}(),hook{}("KEQUAL.ite"),smt-hook{}("ite")]
          symbol f{}(SortInt{}) : SortInt{} [function{}()]
          symbol effect{}(SortInt{}) : SortInt{} [function{}(),impure{}()]
        endmodule []"#
    }

    fn typed_source() -> String {
        source()
            .replace("item{}(SortInt{},SortInt{})", "item{}(SortKItem{},SortKItem{})")
            .replace("put{}(SortMap{},SortInt{},SortInt{})", "put{}(SortMap{},SortKItem{},SortKItem{})")
            .replace("get{}(SortMap{},SortInt{}) : SortInt{}", "get{}(SortMap{},SortKItem{}) : SortKItem{}")
            .replace("member{}(SortInt{},SortMap{})", "member{}(SortKItem{},SortMap{})")
            .replace("remove{}(SortMap{},SortInt{})", "remove{}(SortMap{},SortKItem{})")
            .replace("endmodule", r#"
              sort SortKItem{} []
              sort SortK{} []
              symbol inj{From,To}(From) : To [sortInjection{}()]
              symbol kseq{}(SortKItem{},SortK{}) : SortK{} [constructor{}(),injective{}()]
              symbol dotk{}() : SortK{} [constructor{}()]
              symbol project{}(SortK{}) : SortInt{} [function{}()]
              axiom{R} \exists{R}(V:SortKItem{},\equals{SortKItem{},R}(V:SortKItem{},inj{SortInt{},SortKItem{}}(X:SortInt{}))) [subsort{SortInt{},SortKItem{}}()]
              axiom{R} \implies{R}(\and{R}(\top{R}(),\and{R}(\in{SortK{},R}(X:SortK{},kseq{}(inj{SortInt{},SortKItem{}}(Y:SortInt{}),dotk{}())),\top{R}())),
                \equals{SortInt{},R}(project{}(X:SortK{}),\and{SortInt{}}(Y:SortInt{},\top{SortInt{}}()))) []
              axiom{R} \implies{R}(\top{R}(),\equals{R,R}(\ceil{SortInt{},R}(project{}(X:SortK{})),
                \exists{R}(Y:SortInt{},\equals{SortK{},R}(X:SortK{},kseq{}(inj{SortInt{},SortKItem{}}(Y:SortInt{}),dotk{}()))))) []
              axiom{R} \implies{R}(\ceil{SortInt{},R}(project{}(Z:SortK{})),
                \equals{SortK{},R}(kseq{}(inj{SortInt{},SortKItem{}}(project{}(Z:SortK{})),dotk{}()),\and{SortK{}}(Z:SortK{},\top{SortK{}}()))) [simplification{}()]
            endmodule"#)
    }

    #[test]
    fn canonical_map_domain_rows_are_checked_without_rejecting_the_compiler_contract() {
        let row = r#"axiom{R} \implies{R}(\top{R}(),\equals{R,R}(
          \ceil{SortMap{},R}(concat{}(item{}(@K:SortInt{},@V:SortInt{}),@M:SortMap{})),
          \and{R}(\equals{SortBool{},R}(member{}(@K:SortInt{},@M:SortMap{}),\dv{SortBool{}}("false")),\ceil{SortInt{},R}(@V:SortInt{})))) []
          endmodule"#;
        let text = source().replace("endmodule", row);
        let definition = definition(&text);
        let sort = crate::term::Sort::simple("SortMap");
        assert!(definition.map_operations(&sort).is_some());
        let changed = text.replace(r#"\dv{SortBool{}}("false")"#, r#"\dv{SortBool{}}("true")"#);
        assert!(self::definition(&changed).map_operations(&sort).is_none());
        let extra = text.replace("endmodule",r#"axiom{R} \implies{R}(\top{R}(),\equals{R,R}(\ceil{SortMap{},R}(concat{}(A:SortMap{},B:SortMap{})),\top{R}())) [] endmodule"#);
        assert!(self::definition(&extra).map_operations(&sort).is_none());
    }

    fn definition(source: &str) -> BackendDefinition {
        BackendDefinition::internalize(&parse_definition(source).unwrap(), "MAIN").unwrap()
    }

    fn term(definition: &BackendDefinition, text: &str) -> Term {
        definition
            .internalize_term(&parse_pattern(text).unwrap(), &[])
            .unwrap()
    }

    #[test]
    fn source_views_validate_operations_and_keep_alias_choices() {
        let definition = definition(source());
        let source = term(
            &definition,
            "get{}(put{}(M:SortMap{},K:SortInt{},V:SortInt{}),Q:SortInt{})",
        );
        let mut builder = crate::observation::reading::Builder::new(&definition);
        let reading = builder.of(&source).unwrap().unwrap();
        let Reading::If { test, yes, no } = reading.as_ref() else {
            panic!("unknown alias must stay guarded")
        };
        assert_eq!(
            *test,
            Predicate::Equals(
                term(&definition, "Q:SortInt{}"),
                term(&definition, "K:SortInt{}")
            )
        );
        assert_eq!(
            yes.as_ref(),
            &Reading::Leaf(term(&definition, "V:SortInt{}"))
        );
        assert_eq!(
            no.as_ref(),
            &Reading::Leaf(term(&definition, "get{}(M:SortMap{},Q:SortInt{})"))
        );
        assert!(Arc::ptr_eq(
            &reading,
            &builder.of(&source).unwrap().unwrap()
        ));
        let effect = term(
            &definition,
            "get{}(put{}(M:SortMap{},K:SortInt{},effect{}(V:SortInt{})),K:SortInt{})",
        );
        assert!(builder.of(&effect).unwrap().is_none());
        let checked = [Predicate::Ceil(source)];
        let mut state = TranslationState::new();
        state.congruence =
            super::super::CongruencePolicy::from_definition(&definition).map(Arc::new);
        let extra = prepare(&definition, &mut state, &[], &Substitution::new(), &checked).unwrap();
        super::super::functional::prepare(
            &definition,
            &mut state,
            &extra,
            &Substitution::new(),
            &checked,
        )
        .unwrap();
        let (state, declarations, _, _, checked) =
            super::super::translate_query_in_state(&[], &Substitution::new(), &checked, state)
                .unwrap();
        assert_eq!(state.exactness(), super::super::Exactness::Approximate);
        assert!(!state.domain_facts.is_empty());
        for expression in &declarations {
            assert!(SExpr::parse(expression).is_ok());
        }
        assert!(SExpr::parse(&checked.to_string()).is_ok());
    }

    #[test]
    fn missing_support_and_overridden_source_remain_conservative() {
        let without_member = source()
            .lines()
            .filter(|line| !line.contains("hooked-symbol member"))
            .collect::<Vec<_>>()
            .join("\n");
        let definition = definition(&without_member);
        let get = term(&definition, "get{}(M:SortMap{},K:SortInt{})");
        assert!(crate::observation::maps::lookup_domain(&definition, &get).is_none());
        let wildcard = source().replace("endmodule",r#"axiom{R} \implies{R}(\top{R}(),\equals{SortMap{},R}(X:SortMap{},\and{SortMap{}}(unit{}(),\top{SortMap{}}()))) [simplification{}()] endmodule"#);
        let definition = self::definition(&wildcard);
        assert!(
            definition
                .map_operations(&crate::term::Sort::simple("SortMap"))
                .is_none()
        );
        let impure_unit = source().replace(
            "unit{}() : SortMap{} [function{}(),",
            "unit{}() : SortMap{} [function{}(),impure{}(),",
        );
        let definition = self::definition(&impure_unit);
        assert!(
            definition
                .map_operations(&crate::term::Sort::simple("SortMap"))
                .is_none()
        );
        let unhooked_bool = source().replace(
            r#"hooked-sort SortBool{} [hook{}("BOOL.Bool"),hasDomainValues{}()]"#,
            "sort SortBool{} []",
        );
        let definition = self::definition(&unhooked_bool);
        assert!(
            crate::observation::reading::Builder::new(&definition)
                .of(&term(
                    &definition,
                    "member{}(K:SortInt{},put{}(M:SortMap{},K:SortInt{},V:SortInt{}))"
                ))
                .unwrap()
                .is_none()
        );
        assert!(
            crate::observation::maps::lookup_domain(
                &definition,
                &term(&definition, "get{}(M:SortMap{},K:SortInt{})")
            )
            .is_none()
        );
        let total = source().replace(
            "get{}(SortMap{},SortInt{}) : SortInt{} [function{}(),",
            "get{}(SortMap{},SortInt{}) : SortInt{} [function{}(),total{}(),",
        );
        let definition = self::definition(&total);
        assert!(
            crate::observation::reading::Builder::new(&definition)
                .of(&term(
                    &definition,
                    "get{}(put{}(M:SortMap{},K:SortInt{},V:SortInt{}),K:SortInt{})"
                ))
                .unwrap()
                .is_none()
        );
        let mutated = source().replace("endmodule",r#"axiom{R} \implies{R}(\top{R}(),\equals{SortInt{},R}(get{}(M:SortMap{},K:SortInt{}),\and{SortInt{}}(\dv{SortInt{}}("4"),\top{SortInt{}}()))) [simplification{}()] endmodule"#);
        let definition = self::definition(&mutated);
        let get = term(
            &definition,
            "get{}(put{}(M:SortMap{},K:SortInt{},V:SortInt{}),K:SortInt{})",
        );
        assert!(
            crate::observation::reading::Builder::new(&definition)
                .of(&get)
                .unwrap()
                .is_none()
        );
        assert!(crate::observation::maps::lookup_domain(&definition, &get).is_none());
    }

    #[cfg(feature = "z3")]
    fn check(
        definition: &BackendDefinition,
        known: &[Predicate],
        checked: Predicate,
    ) -> super::super::Validity {
        use crate::smt::SmtSolver;
        crate::smt::Z3Solver::new(definition)
            .unwrap()
            .check_predicates(known, &Substitution::new(), &[checked])
            .unwrap()
            .unwrap()
    }

    #[cfg(feature = "z3")]
    #[test]
    fn explicit_map_contexts_preserve_equal_computed_remainders_without_base_extensionality() {
        use super::super::Validity;
        let text = source().replace(
            "endmodule",
            "symbol context{}(SortMap{}) : SortInt{} [function{}()] endmodule",
        );
        let definition = definition(&text);
        let left_rest = term(&definition, "remove{}(M:SortMap{},K:SortInt{})");
        let right_rest = term(&definition, "remove{}(N:SortMap{},K:SortInt{})");
        let a = term(
            &definition,
            "context{}(concat{}(item{}(K:SortInt{},V:SortInt{}),remove{}(M:SortMap{},K:SortInt{})))",
        );
        let b = term(
            &definition,
            "context{}(concat{}(item{}(K:SortInt{},V:SortInt{}),remove{}(N:SortMap{},K:SortInt{})))",
        );
        let known = [
            Predicate::Equals(left_rest, right_rest),
            Predicate::Ceil(a.clone()),
        ];
        assert_eq!(
            check(&definition, &known, Predicate::Equals(a.clone(), b.clone())),
            Validity::Valid
        );
        assert_eq!(
            check(&definition, &known, Predicate::Ceil(b.clone())),
            Validity::Valid
        );
        assert_ne!(
            check(
                &definition,
                &[Predicate::Ceil(a.clone())],
                Predicate::Equals(a, b)
            ),
            Validity::Valid
        );
        assert_ne!(
            check(
                &definition,
                &known,
                Predicate::Equals(
                    term(&definition, "M:SortMap{}"),
                    term(&definition, "N:SortMap{}")
                )
            ),
            Validity::Valid
        );
    }

    #[cfg(feature = "z3")]
    #[test]
    fn finite_map_equality_compares_final_presence_values_and_preserved_bases() {
        use super::super::Validity;
        let text = source().replace(
            "endmodule",
            "symbol context{}(SortMap{}) : SortInt{} [function{}()] endmodule",
        );
        let definition = definition(&text);
        let a = term(
            &definition,
            "put{}(put{}(M:SortMap{},K:SortInt{},V:SortInt{}),J:SortInt{},W:SortInt{})",
        );
        let b = term(
            &definition,
            "put{}(put{}(M:SortMap{},J:SortInt{},W:SortInt{}),K:SortInt{},V:SortInt{})",
        );
        let different = Predicate::Not(Arc::new(Predicate::Equals(
            term(&definition, "K:SortInt{}"),
            term(&definition, "J:SortInt{}"),
        )));
        assert_eq!(
            check(
                &definition,
                std::slice::from_ref(&different),
                Predicate::Equals(a.clone(), b.clone())
            ),
            Validity::Valid
        );
        assert_ne!(
            check(&definition, &[], Predicate::Equals(a.clone(), b.clone())),
            Validity::Valid
        );
        let context =
            |value| Term::application(definition.symbols()["context"].clone(), vec![], vec![value]);
        assert_eq!(
            check(
                &definition,
                &[different],
                Predicate::Equals(context(a), context(b))
            ),
            Validity::Valid
        );
        let map = term(&definition, "M:SortMap{}");
        let key = term(&definition, "K:SortInt{}");
        let ops = definition.map_operations(&map.sort()).unwrap();
        let read = ops.lookup(&definition, map.clone(), &key).unwrap();
        let put_back = Term::application(
            definition.symbols()["put"].clone(),
            vec![],
            vec![map.clone(), key.clone(), read.clone()],
        );
        assert_eq!(
            check(
                &definition,
                &[Predicate::Ceil(read.clone())],
                Predicate::Equals(map.clone(), put_back)
            ),
            Validity::Valid
        );
        let frame = ops.remove(&definition, map.clone(), &key).unwrap();
        let rebuilt = Term::map(
            ops.collection.clone(),
            vec![(key.clone(), read.clone())],
            Some(frame),
        );
        let frame_query = crate::smt::SmtPrelude::from_definition(&definition)
            .unwrap()
            .query(
                &[Predicate::Ceil(read.clone())],
                &Substitution::new(),
                &[Predicate::Equals(map.clone(), rebuilt.clone())],
                false,
            )
            .unwrap()
            .unwrap();
        assert_eq!(
            check(
                &definition,
                &[Predicate::Ceil(read.clone())],
                Predicate::Equals(map.clone(), rebuilt)
            ),
            Validity::Valid,
            "{}",
            frame_query.base()
        );
        let wrong_frame = Term::map(
            ops.collection.clone(),
            vec![(key, read.clone())],
            Some(term(&definition, "R:SortMap{}")),
        );
        assert_ne!(
            check(
                &definition,
                &[Predicate::Ceil(read)],
                Predicate::Equals(map, wrong_frame)
            ),
            Validity::Valid
        );
    }

    #[cfg(feature = "z3")]
    #[test]
    fn finite_map_equality_retains_source_domains_and_binder_scopes() {
        use super::super::Validity;
        let definition = definition(source());
        let map = term(&definition, "M:SortMap{}");
        let key = term(&definition, "K:SortInt{}");
        let read = term(&definition, "get{}(M:SortMap{},K:SortInt{})");
        let put_back = Term::application(
            definition.symbols()["put"].clone(),
            vec![],
            vec![map.clone(), key.clone(), read.clone()],
        );
        let checked = Predicate::And(
            vec![
                Predicate::Equals(map.clone(), put_back.clone()),
                Predicate::Ceil(put_back),
            ]
            .into(),
        );
        assert_ne!(
            check(
                &definition,
                &[Predicate::Not(Arc::new(Predicate::Ceil(read)))],
                checked
            ),
            Validity::Valid
        );
        let left = term(
            &definition,
            "put{}(put{}(M:SortMap{},K:SortInt{},V:SortInt{}),J:SortInt{},W:SortInt{})",
        );
        let right = term(
            &definition,
            "put{}(put{}(N:SortMap{},J:SortInt{},W:SortInt{}),K:SortInt{},V:SortInt{})",
        );
        let known = [
            Predicate::Equals(map, term(&definition, "N:SortMap{}")),
            Predicate::Not(Arc::new(Predicate::Equals(
                key.clone(),
                term(&definition, "J:SortInt{}"),
            ))),
        ];
        assert_eq!(
            check(&definition, &known, Predicate::Equals(left, right)),
            Validity::Valid
        );
        let a = term(
            &definition,
            r#"put{}(put{}(M:SortMap{},K:SortInt{},V:SortInt{}),\dv{SortInt{}}("0"),W:SortInt{})"#,
        );
        let b = term(
            &definition,
            r#"put{}(put{}(M:SortMap{},\dv{SortInt{}}("0"),W:SortInt{}),K:SortInt{},V:SortInt{})"#,
        );
        let variable = crate::term::Variable::new("K", crate::term::Sort::simple("SortInt"));
        let theorem = Predicate::Forall(
            variable,
            Arc::new(Predicate::Implies(
                Arc::new(Predicate::Not(Arc::new(Predicate::Equals(
                    key,
                    Term::int(0),
                )))),
                Arc::new(Predicate::Equals(a, b)),
            )),
        );
        assert_eq!(check(&definition, &[], theorem), Validity::Valid);
    }

    #[cfg(feature = "z3")]
    #[test]
    fn conditional_finite_map_equality_does_not_demand_absent_unselected_lookups() {
        use super::super::Validity;
        let definition = definition(source());
        let a = term(
            &definition,
            "choose{SortMap{}}(B:SortBool{},put{}(put{}(unit{}(),K:SortInt{},V:SortInt{}),J:SortInt{},W:SortInt{}),put{}(unit{}(),J:SortInt{},W:SortInt{}))",
        );
        let b = term(
            &definition,
            "put{}(choose{SortMap{}}(B:SortBool{},put{}(unit{}(),K:SortInt{},V:SortInt{}),unit{}()),J:SortInt{},W:SortInt{})",
        );
        assert_eq!(
            check(&definition, &[], Predicate::Equals(a, b)),
            Validity::Valid
        );
        let partial = term(&definition, "f{}(X:SortInt{})");
        let shadowed = Term::application(
            definition.symbols()["put"].clone(),
            vec![],
            vec![
                Term::application(
                    definition.symbols()["put"].clone(),
                    vec![],
                    vec![
                        term(&definition, "M:SortMap{}"),
                        Term::int(0),
                        partial.clone(),
                    ],
                ),
                Term::int(0),
                Term::int(1),
            ],
        );
        assert_ne!(
            check(
                &definition,
                &[Predicate::Not(Arc::new(Predicate::Ceil(partial)))],
                Predicate::Ceil(shadowed)
            ),
            Validity::Valid
        );
    }

    #[cfg(feature = "z3")]
    #[test]
    fn finite_map_equality_declines_mutated_operations_and_polls_cancellation() {
        let text = source().replace("endmodule",r#"axiom{R} \implies{R}(\top{R}(),\equals{SortInt{},R}(get{}(M:SortMap{},K:SortInt{}),\and{SortInt{}}(\dv{SortInt{}}("7"),\top{SortInt{}}()))) [simplification{}()] endmodule"#);
        let changed = definition(&text);
        let a = term(
            &changed,
            "put{}(put{}(M:SortMap{},K:SortInt{},V:SortInt{}),J:SortInt{},W:SortInt{})",
        );
        let b = term(
            &changed,
            "put{}(put{}(M:SortMap{},J:SortInt{},W:SortInt{}),K:SortInt{},V:SortInt{})",
        );
        assert!(
            crate::observation::reading::Builder::new(&changed)
                .map_equality(&a, &b)
                .unwrap()
                .is_none()
        );
        let baseline = definition(source());
        let a = term(&baseline, "put{}(M:SortMap{},K:SortInt{},V:SortInt{})");
        let b = term(&baseline, "M:SortMap{}");
        assert!(
            crate::observation::reading::Builder::new(&baseline)
                .map_equality(&a, &b)
                .unwrap()
                .is_some()
        );
        let token = crate::stop::CancellationToken::new();
        token.cancel();
        let stopped = token
            .scope(|| crate::observation::reading::Builder::new(&baseline).map_equality(&a, &b))
            .unwrap_err();
        assert_eq!(stopped.into_cause(), crate::stop::StopCause::Cancelled);
    }

    #[cfg(feature = "z3")]
    #[test]
    fn finite_map_equality_query_construction_shares_repeated_demands() {
        let definition = definition(source());
        let prelude = crate::smt::SmtPrelude::from_definition(&definition).unwrap();
        let int = crate::term::Sort::simple("SortInt");
        for symbolic in [false, true] {
            for count in [1, 2, 8, 32] {
                let build = |indices: Vec<usize>| {
                    indices
                        .into_iter()
                        .fold(term(&definition, "M:SortMap{}"), |map, index| {
                            Term::application(
                                definition.symbols()["put"].clone(),
                                vec![],
                                vec![
                                    map,
                                    if symbolic {
                                        Term::variable(crate::term::Variable::new(
                                            format!("K{index}"),
                                            int,
                                        ))
                                    } else {
                                        Term::int(index)
                                    },
                                    Term::variable(crate::term::Variable::new(
                                        format!("V{index}"),
                                        int,
                                    )),
                                ],
                            )
                        })
                };
                let left = build((0..count).collect());
                let right = build((0..count).rev().collect());
                let equality = Predicate::Equals(left, right);
                let query = prelude
                    .query(
                        &[],
                        &Substitution::new(),
                        std::slice::from_ref(&equality),
                        false,
                    )
                    .unwrap()
                    .unwrap();
                let repeated = prelude
                    .query(
                        &[],
                        &Substitution::new(),
                        &[equality.clone(), equality],
                        false,
                    )
                    .unwrap()
                    .unwrap();
                let bytes = query.base().len() + query.checked().to_string().len();
                let repeated_bytes = repeated.base().len() + repeated.checked().to_string().len();
                eprintln!(
                    "finite map equality {count} symbolic={symbolic}: {bytes} bytes; repeated {repeated_bytes}"
                );
                assert!(bytes < 8 * 1024 * 1024, "{count}: {bytes} bytes");
                assert!(
                    repeated_bytes <= bytes * 2 + 4096,
                    "repeated {count}: {repeated_bytes} vs {bytes}"
                );
                assert!(query.model_mappings().is_none());
            }
        }
    }

    #[cfg(feature = "z3")]
    #[test]
    fn observations_compose_through_opaque_state_aliases_and_partial_contexts() {
        use super::super::Validity;
        let definition = definition(source());
        let put = term(&definition, "put{}(M:SortMap{},K:SortInt{},V:SortInt{})");
        let a = term(&definition, "A:SortMap{}");
        let read = term(&definition, "get{}(A:SortMap{},Q:SortInt{})");
        let known = [
            Predicate::Equals(a, put),
            Predicate::Equals(
                term(&definition, "Q:SortInt{}"),
                term(&definition, "K:SortInt{}"),
            ),
        ];
        assert_eq!(
            check(
                &definition,
                &known,
                Predicate::Equals(read.clone(), term(&definition, "V:SortInt{}"))
            ),
            Validity::Valid
        );
        assert_eq!(
            check(&definition, &known, Predicate::Ceil(read)),
            Validity::Valid
        );
        let checked = Predicate::Equals(
            term(&definition, "f{}(get{}(A:SortMap{},Q:SortInt{}))"),
            term(&definition, "f{}(V:SortInt{})"),
        );
        assert_eq!(check(&definition, &known, checked), Validity::Valid);
        {
            use crate::smt::SmtSolver;
            let substitution = Substitution::from([(
                crate::term::Variable::new("A", crate::term::Sort::simple("SortMap")),
                term(&definition, "put{}(M:SortMap{},K:SortInt{},V:SortInt{})"),
            )]);
            let checked = Predicate::Equals(
                term(&definition, "get{}(A:SortMap{},K:SortInt{})"),
                term(&definition, "V:SortInt{}"),
            );
            assert_eq!(
                crate::smt::Z3Solver::new(&definition)
                    .unwrap()
                    .check_predicates(&[], &substitution, &[checked])
                    .unwrap()
                    .unwrap(),
                Validity::Valid
            );
        }
        let not_equal = [
            Predicate::Not(Arc::new(Predicate::Equals(
                term(&definition, "A:SortMap{}"),
                term(&definition, "put{}(M:SortMap{},K:SortInt{},V:SortInt{})"),
            ))),
            Predicate::Equals(
                term(&definition, "K:SortInt{}"),
                term(&definition, "Q:SortInt{}"),
            ),
        ];
        assert_ne!(
            check(
                &definition,
                &not_equal,
                Predicate::Equals(
                    term(&definition, "get{}(A:SortMap{},Q:SortInt{})"),
                    term(&definition, "V:SortInt{}")
                )
            ),
            Validity::Valid
        );
        let recursive_alias = [Predicate::Equals(
            term(&definition, "M:SortMap{}"),
            term(&definition, "put{}(M:SortMap{},K:SortInt{},V:SortInt{})"),
        )];
        assert_eq!(
            check(
                &definition,
                &recursive_alias,
                Predicate::Equals(
                    term(&definition, "get{}(M:SortMap{},K:SortInt{})"),
                    term(&definition, "V:SortInt{}")
                )
            ),
            Validity::Valid
        );
        // A pure opaque partial function gets forward congruence, never injectivity.
        let known = [Predicate::Equals(
            term(&definition, "f{}(K:SortInt{})"),
            term(&definition, "f{}(Q:SortInt{})"),
        )];
        assert_ne!(
            check(
                &definition,
                &known,
                Predicate::Equals(
                    term(&definition, "K:SortInt{}"),
                    term(&definition, "Q:SortInt{}")
                )
            ),
            Validity::Valid
        );
    }

    #[cfg(feature = "z3")]
    #[test]
    fn selected_read_domains_retain_strict_state_operands() {
        use super::super::Validity;
        let definition = definition(source());
        let read = term(
            &definition,
            r#"get{}(choose{SortMap{}}(B:SortBool{},put{}(M:SortMap{},K:SortInt{},V:SortInt{}),unit{}()),K:SortInt{})"#,
        );
        let known = [Predicate::Term(term(&definition, "B:SortBool{}"))];
        assert_eq!(
            check(&definition, &known, Predicate::Ceil(read.clone())),
            Validity::Valid
        );
        assert_eq!(
            check(
                &definition,
                &known,
                Predicate::Equals(read, term(&definition, "V:SortInt{}"))
            ),
            Validity::Valid
        );
        let read = term(
            &definition,
            "get{}(put{}(put{}(M:SortMap{},K:SortInt{},f{}(X:SortInt{})),K:SortInt{},V:SortInt{}),K:SortInt{})",
        );
        let undefined = Predicate::Not(Arc::new(Predicate::Ceil(term(
            &definition,
            "f{}(X:SortInt{})",
        ))));
        assert_eq!(
            check(&definition, &[undefined], Predicate::Ceil(read)),
            Validity::Refuted
        );
        let missing = term(
            &definition,
            "get{}(remove{}(M:SortMap{},K:SortInt{}),K:SortInt{})",
        );
        assert_eq!(
            check(&definition, &[], Predicate::Ceil(missing)),
            Validity::Refuted
        );
        let query = crate::smt::SmtPrelude::from_definition(&definition)
            .unwrap()
            .query(
                &[],
                &Substitution::new(),
                &[Predicate::Ceil(term(
                    &definition,
                    "get{}(M:SortMap{},K:SortInt{})",
                ))],
                false,
            )
            .unwrap()
            .unwrap();
        assert!(query.model_mappings().is_none());
    }

    #[cfg(feature = "z3")]
    #[test]
    fn typed_observations_preserve_compiler_embeddings_and_quantifier_scopes() {
        use super::super::Validity;
        let definition = definition(&typed_source());
        let inject = |name: &str| format!("inj{{SortInt{{}},SortKItem{{}}}}({name}:SortInt{{}})");
        let (k, q, v, w) = (inject("K"), inject("Q"), inject("V"), inject("W"));
        let put = format!("put{{}}(M:SortMap{{}},{k},{v})");
        let read = term(&definition, &format!("get{{}}({put},{q})"));
        let old = term(&definition, &format!("get{{}}(M:SortMap{{}},{q})"));
        let apart = Predicate::Not(Arc::new(Predicate::Equals(
            term(&definition, "K:SortInt{}"),
            term(&definition, "Q:SortInt{}"),
        )));
        let known = [apart, Predicate::Ceil(old.clone())];
        assert_eq!(
            check(&definition, &known, Predicate::Equals(read, old)),
            Validity::Valid
        );
        let conditional =
            format!("choose{{SortMap{{}}}}(B:SortBool{{}},{put},put{{}}(M:SortMap{{}},{k},{w}))");
        let observed = term(
            &definition,
            &format!("project{{}}(kseq{{}}(get{{}}({conditional},{k}),dotk{{}}()))"),
        );
        let expected = term(
            &definition,
            "choose{SortInt{}}(B:SortBool{},V:SortInt{},W:SortInt{})",
        );
        assert_eq!(
            check(&definition, &[], Predicate::Ceil(observed.clone())),
            Validity::Valid
        );
        assert_eq!(
            check(&definition, &[], Predicate::Equals(observed, expected)),
            Validity::Valid
        );
        let read = term(&definition, &format!("get{{}}({put},{k})"));
        let key = crate::term::Variable::new("K", crate::term::Sort::simple("SortInt"));
        let quantified = Predicate::Forall(key, Arc::new(Predicate::Ceil(read)));
        assert_eq!(check(&definition, &[], quantified), Validity::Valid);
    }

    #[test]
    fn conditional_source_obstructions_are_checked_at_the_actual_rank() {
        let extra = r#"axiom{R} \implies{R}(\top{R}(),\equals{SortK{},R}(
            choose{SortK{}}(B:SortBool{},X:SortK{},Y:SortK{}),
            \and{SortK{}}(X:SortK{},\top{SortK{}}()))) [simplification{}()] endmodule"#;
        let original = typed_source().replace("endmodule", extra);
        let lookup = "get{}(choose{SortMap{}}(B:SortBool{},put{}(M:SortMap{},inj{SortInt{},SortKItem{}}(K:SortInt{}),inj{SortInt{},SortKItem{}}(V:SortInt{})),M:SortMap{}),inj{SortInt{},SortKItem{}}(K:SortInt{}))";
        let definition = definition(&original);
        assert!(
            crate::observation::reading::Builder::new(&definition)
                .of(&term(&definition, lookup))
                .unwrap()
                .is_some()
        );
        let changed = typed_source().replace("endmodule", &extra.replace("SortK{}", "SortMap{}"));
        let definition = self::definition(&changed);
        assert!(
            crate::observation::reading::Builder::new(&definition)
                .of(&term(&definition, lookup))
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn typed_storage_reconstruction_requires_the_checked_inverse_and_free_singleton() {
        let definition = definition(&typed_source());
        let raw_text = "get{}(M:SortMap{},inj{SortInt{},SortKItem{}}(K:SortInt{}))";
        let project_text = format!("project{{}}(kseq{{}}({raw_text},dotk{{}}()))");
        let stored_text = format!("inj{{SortInt{{}},SortKItem{{}}}}({project_text})");
        let (raw, projected, stored) = (
            term(&definition, raw_text),
            term(&definition, &project_text),
            term(&definition, &stored_text),
        );
        let plan = crate::observation::reading::Builder::new(&definition)
            .of(&stored)
            .unwrap()
            .unwrap();
        assert_eq!(plan.as_ref(), &Reading::Leaf(raw.clone()));
        #[cfg(feature = "z3")]
        {
            use super::super::Validity;
            let known = [Predicate::Ceil(projected.clone())];
            assert_eq!(
                check(&definition, &known, Predicate::Equals(stored.clone(), raw)),
                Validity::Valid
            );
            assert_eq!(
                check(
                    &definition,
                    &[Predicate::Not(Arc::new(Predicate::Ceil(projected)))],
                    Predicate::Ceil(stored)
                ),
                Validity::Refuted
            );
        }
        #[cfg(not(feature = "z3"))]
        let _ = projected;
        let without_injectivity =
            typed_source().replace("[constructor{}(),injective{}()]", "[constructor{}()]");
        let definition = self::definition(&without_injectivity);
        assert!(
            definition
                .selector(
                    &crate::term::Sort::simple("SortK"),
                    &crate::term::Sort::simple("SortInt")
                )
                .is_some()
        );
        assert!(
            crate::observation::reading::Builder::new(&definition)
                .of(&term(&definition, &stored_text))
                .unwrap()
                .is_some()
        );
        let equation_head = typed_source().replace(
            "[constructor{}(),injective{}()]",
            "[anywhere{}(),injective{}()]",
        );
        let definition = self::definition(&equation_head);
        assert!(
            crate::observation::reading::Builder::new(&definition)
                .of(&term(&definition, &stored_text))
                .unwrap()
                .is_none()
        );
    }

    #[cfg(feature = "z3")]
    #[test]
    fn finite_observation_sharing_and_cancelled_requests_are_bounded() {
        let definition = definition(source());
        let mut map = term(&definition, "M:SortMap{}");
        let int = crate::term::Sort::simple("SortInt");
        for i in 0..32 {
            map = Term::application(
                definition.symbols()["put"].clone(),
                vec![],
                vec![
                    map,
                    Term::variable(crate::term::Variable::new(format!("K{i}"), int)),
                    Term::variable(crate::term::Variable::new(format!("V{i}"), int)),
                ],
            );
        }
        let read = Term::application(
            definition.symbols()["get"].clone(),
            vec![],
            vec![map, term(&definition, "Q:SortInt{}")],
        );
        let query = crate::smt::SmtPrelude::from_definition(&definition)
            .unwrap()
            .query(
                &[],
                &Substitution::new(),
                &[Predicate::Ceil(read.clone())],
                false,
            )
            .unwrap()
            .unwrap();
        assert!(
            query.base().len() < 1_048_576,
            "{} emitted bytes",
            query.base().len()
        );
        assert!(query.model_mappings().is_none());
        let token = crate::stop::CancellationToken::new();
        token.cancel();
        let stopped = token
            .scope(|| crate::observation::reading::Builder::new(&definition).of(&read))
            .unwrap_err();
        assert_eq!(stopped.into_cause(), crate::stop::StopCause::Cancelled);
    }
}
