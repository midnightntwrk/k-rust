//! Decided API answers owned by one immutable solver/prelude, before query preparation.
//!
//! Fingerprints only select candidates. Reuse requires full, bounded structural comparison.
//! Admission charges every distinct retained term node, its argument capacity, literal/name
//! payloads, variable supports and collection-tree summaries. Shared nodes are visited once
//! per entry; sharing between entries is deliberately overcharged. Definition-owned symbols
//! and globally interned sorts are already retained by the solver, not by an entry.
//! Oversized keys decline reuse, without changing the query the ordinary solver receives.

use super::{Satisfiability, Validity};
use crate::{
    definition::BackendDefinition,
    evaluation::{self, EvaluationMode},
    rule::Predicate,
    stop::{self, Stoppable},
    substitution::Substitution,
    term::{CollectionMetadata, Term, TermAttributes, TermKind, Variable, equal_terms_bounded},
};
use rustc_hash::{FxHashSet, FxHasher};
use std::{
    collections::VecDeque,
    hash::{Hash, Hasher},
    mem::size_of,
    sync::Arc,
};

pub(super) const ENTRY_LIMIT: usize = 256;
pub(super) const RETENTION_LIMIT: usize = 64 * 1024 * 1024;
const ENTRY_RETENTION_LIMIT: usize = 4 * 1024 * 1024;
const WORK_LIMIT: usize = 32_768;

#[derive(Clone)]
pub(super) enum Answer {
    Sat(Satisfiability),
    Validity(Validity),
}
impl Answer {
    fn decided(&self) -> bool {
        matches!(
            self,
            Self::Sat(Satisfiability::Sat | Satisfiability::Unsat)
                | Self::Validity(
                    Validity::Valid
                        | Validity::Refuted
                        | Validity::InconsistentGroundTruth
                        | Validity::Contingent
                )
        )
    }
}

/// Borrowed lookup inputs: no query tree or script is copied to look for an answer.
pub(super) struct Query<'a> {
    validity: bool,
    mode: EvaluationMode,
    console: bool,
    known: &'a [Predicate],
    substitution: &'a Substitution,
    checked: &'a [Predicate],
}
impl<'a> Query<'a> {
    pub(super) fn new(
        validity: bool,
        known: &'a [Predicate],
        substitution: &'a Substitution,
        checked: &'a [Predicate],
    ) -> Self {
        Self {
            validity,
            mode: evaluation::current(),
            console: evaluation::console_attached(),
            known,
            substitution,
            checked,
        }
    }
    fn fingerprint(&self) -> u64 {
        let mut h = FxHasher::default();
        (
            self.validity,
            self.mode,
            self.console,
            self.known.len(),
            self.substitution.len(),
            self.checked.len(),
        )
            .hash(&mut h);
        // A fixed prefix of the logical tree, independent of its physical sharing. A collision
        // only costs candidate comparisons. Never hash an exponentially expanded predicate DAG.
        for (v, t) in self.substitution.iter().take(32) {
            variable_hash(v, &mut h);
            t.hash(&mut h);
        }
        let mut pending = self
            .known
            .iter()
            .chain(self.checked)
            .rev()
            .take(128)
            .collect::<Vec<_>>();
        for _ in 0..128 {
            let Some(p) = pending.pop() else {
                break;
            };
            std::mem::discriminant(p).hash(&mut h);
            match p {
                Predicate::Term(t)
                | Predicate::Ceil(t)
                | Predicate::Floor(t)
                | Predicate::Defined(t) => t.hash(&mut h),
                Predicate::Equals(a, b) | Predicate::In(a, b) => {
                    a.hash(&mut h);
                    b.hash(&mut h);
                }
                Predicate::Absent(a) => {
                    a.key().hash(&mut h);
                    a.rest().hash(&mut h);
                }
                Predicate::Not(p) => pending.push(p),
                Predicate::And(ps) | Predicate::Or(ps) => {
                    ps.len().hash(&mut h);
                    pending.extend(
                        ps.iter()
                            .rev()
                            .take(128_usize.saturating_sub(pending.len())),
                    );
                }
                Predicate::Implies(a, b) | Predicate::Iff(a, b) => {
                    pending.push(b);
                    pending.push(a);
                }
                Predicate::Exists(v, p) | Predicate::Forall(v, p) => {
                    variable_hash(v, &mut h);
                    pending.push(p);
                }
                Predicate::True | Predicate::False => {}
            }
        }
        h.finish()
    }
}
fn variable_hash(v: &Variable, h: &mut FxHasher) {
    v.kind.hash(h);
    std::ptr::from_ref(v.sort.node()).hash(h); // Sorts are globally interned.
    v.name.len().hash(h);
    v.name.as_bytes().iter().take(32).for_each(|b| b.hash(h));
}

struct Entry {
    fingerprint: u64,
    validity: bool,
    mode: EvaluationMode,
    console: bool,
    known: Vec<Predicate>,
    substitution: Substitution,
    checked: Vec<Predicate>,
    answer: Answer,
    retention: usize,
}

/// ```toml algorithm-site
/// id = "backend.smt.cache"
/// role = "part"
/// sites = ["Cache", "Cache::new", "Cache::get", "Cache::insert", "Query::fingerprint", "equal_inputs", "retention", "collection_cost"]
/// ```
pub(super) struct Cache {
    entries: VecDeque<Entry>,
    retention: usize,
    entry_limit: usize,
    retention_limit: usize,
}
// Do not print retained expression graphs through a derived Debug implementation.
impl std::fmt::Debug for Cache {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TypedQueryCache")
            .field("entries", &self.entries.len())
            .field("retention", &self.retention)
            .finish()
    }
}
impl Cache {
    pub(super) fn new(entry_limit: usize, retention_limit: usize) -> Self {
        Self {
            entries: VecDeque::new(),
            retention: 0,
            entry_limit,
            retention_limit,
        }
    }
    pub(super) fn get(&self, query: &Query<'_>) -> Stoppable<Option<Answer>> {
        let fingerprint = query.fingerprint();
        for e in self.entries.iter().rev() {
            stop::check()?;
            if e.fingerprint != fingerprint
                || e.validity != query.validity
                || e.mode != query.mode
                || e.console != query.console
            {
                continue;
            }
            let mut work = WORK_LIMIT;
            if equal_inputs(e, query, &mut work) == Some(true) {
                return Ok(Some(e.answer.clone()));
            }
        }
        Ok(None)
    }
    pub(super) fn insert(
        &mut self,
        query: &Query<'_>,
        answer: Answer,
        definition: &BackendDefinition,
    ) -> Stoppable<()> {
        if !answer.decided() || self.entry_limit == 0 {
            return Ok(());
        }
        let Some(retention) = retention(
            query,
            definition,
            self.retention_limit.min(ENTRY_RETENTION_LIMIT),
        )?
        else {
            return Ok(());
        };
        while self.entries.len() >= self.entry_limit
            || self.retention + retention > self.retention_limit
        {
            let Some(e) = self.entries.pop_front() else {
                return Ok(());
            };
            self.retention -= e.retention;
        }
        self.entries.push_back(Entry {
            fingerprint: query.fingerprint(),
            validity: query.validity,
            mode: query.mode,
            console: query.console,
            known: query.known.to_vec(),
            substitution: query.substitution.clone(),
            checked: query.checked.to_vec(),
            answer,
            retention,
        });
        self.retention += retention;
        Ok(())
    }
}

fn equal_inputs(e: &Entry, q: &Query<'_>, work: &mut usize) -> Option<bool> {
    if e.known.len() != q.known.len()
        || e.checked.len() != q.checked.len()
        || e.substitution.len() != q.substitution.len()
    {
        return Some(false);
    }
    for ((a, t), (b, u)) in e.substitution.iter().zip(q.substitution) {
        if a != b || !equal_terms_bounded(t, u, work)? {
            return Some(false);
        }
    }
    let mut pending = e
        .known
        .iter()
        .zip(q.known)
        .chain(e.checked.iter().zip(q.checked))
        .collect::<Vec<_>>();
    let mut seen = FxHashSet::default();
    while let Some((a, b)) = pending.pop() {
        *work = work.checked_sub(1)?;
        if std::ptr::eq(a, b) || !seen.insert((std::ptr::from_ref(a), std::ptr::from_ref(b))) {
            continue;
        }
        let same = match (a, b) {
            (Predicate::True, Predicate::True) | (Predicate::False, Predicate::False) => true,
            (Predicate::Term(a), Predicate::Term(b))
            | (Predicate::Ceil(a), Predicate::Ceil(b))
            | (Predicate::Floor(a), Predicate::Floor(b))
            | (Predicate::Defined(a), Predicate::Defined(b)) => equal_terms_bounded(a, b, work)?,
            (Predicate::Equals(a, b), Predicate::Equals(c, d))
            | (Predicate::In(a, b), Predicate::In(c, d)) => {
                equal_terms_bounded(a, c, work)? && equal_terms_bounded(b, d, work)?
            }
            (Predicate::Absent(a), Predicate::Absent(b)) => {
                a.binder() == b.binder()
                    && equal_terms_bounded(a.joined(), b.joined(), work)?
                    && equal_terms_bounded(a.key(), b.key(), work)?
                    && equal_terms_bounded(a.rest(), b.rest(), work)?
            }
            (Predicate::Not(a), Predicate::Not(b)) => {
                pending.push((a, b));
                true
            }
            (Predicate::And(a), Predicate::And(b)) | (Predicate::Or(a), Predicate::Or(b))
                if a.len() == b.len() =>
            {
                if a.len() > *work {
                    return None;
                }
                pending.extend(a.iter().zip(b.iter()));
                true
            }
            (Predicate::Implies(a, b), Predicate::Implies(c, d))
            | (Predicate::Iff(a, b), Predicate::Iff(c, d)) => {
                pending.extend([(a.as_ref(), c.as_ref()), (b.as_ref(), d.as_ref())]);
                true
            }
            (Predicate::Exists(a, p), Predicate::Exists(b, q))
            | (Predicate::Forall(a, p), Predicate::Forall(b, q))
                if a == b =>
            {
                pending.push((p, q));
                true
            }
            (
                Predicate::True
                | Predicate::False
                | Predicate::Term(_)
                | Predicate::Equals(..)
                | Predicate::Ceil(_)
                | Predicate::Floor(_)
                | Predicate::In(..)
                | Predicate::Not(_)
                | Predicate::And(_)
                | Predicate::Or(_)
                | Predicate::Implies(..)
                | Predicate::Iff(..)
                | Predicate::Exists(..)
                | Predicate::Forall(..)
                | Predicate::Absent(_)
                | Predicate::Defined(_),
                _,
            ) => false,
        };
        if !same {
            return Some(false);
        }
    }
    Some(true)
}

/// Conservative retention charge, not allocator telemetry. All additions are checked against
/// the remaining allowance before allocating or cloning the retained key. Predicate depth and
/// visit limits also bound admission work and the drop depth of the cloned logical spine.
fn retention(
    query: &Query<'_>,
    definition: &BackendDefinition,
    limit: usize,
) -> Stoppable<Option<usize>> {
    let mut left = limit;
    macro_rules! charge {
        ($n:expr) => {
            match left.checked_sub($n) {
                Some(n) => left = n,
                None => return Ok(None),
            }
        };
    }
    // Pay even the minimum four-slot VecDeque allocation on the first insertion.
    charge!(4 * size_of::<Entry>() + 128);
    if query
        .known
        .len()
        .saturating_add(query.checked.len())
        .saturating_add(query.substitution.len())
        > 1024
    {
        return Ok(None);
    }
    // One binding can retain a sparsely occupied BTreeMap node with eleven key/value
    // slots; charging only the used binding would miss that capacity.
    charge!(
        (query.known.len() + query.checked.len()) * size_of::<Predicate>()
            + query.substitution.len() * 1024
    );
    let mut terms = Vec::new();
    for (v, t) in query.substitution {
        charge!(v.name.len());
        terms.push(t);
    }
    let mut predicates = query
        .known
        .iter()
        .chain(query.checked)
        .map(|p| (p, 0))
        .collect::<Vec<_>>();
    let mut work = WORK_LIMIT;
    while let Some((p, depth)) = predicates.pop() {
        stop::check()?;
        if depth > 64 || work == 0 {
            return Ok(None);
        }
        work -= 1;
        charge!(size_of::<Predicate>() + 32);
        match p {
            Predicate::Term(t)
            | Predicate::Ceil(t)
            | Predicate::Floor(t)
            | Predicate::Defined(t) => terms.push(t),
            Predicate::Equals(a, b) | Predicate::In(a, b) => terms.extend([a, b]),
            Predicate::Absent(a) => {
                terms.extend([a.key(), a.rest(), a.joined()]);
                if let Some(v) = a.binder() {
                    charge!(v.name.len());
                }
            }
            Predicate::Not(p) => predicates.push((p, depth + 1)),
            Predicate::And(ps) | Predicate::Or(ps) => {
                if ps.len() > work {
                    return Ok(None);
                }
                predicates.extend(ps.iter().map(|p| (p, depth + 1)));
            }
            Predicate::Implies(a, b) | Predicate::Iff(a, b) => {
                predicates.extend([(a.as_ref(), depth + 1), (b.as_ref(), depth + 1)])
            }
            Predicate::Exists(v, p) | Predicate::Forall(v, p) => {
                charge!(v.name.len());
                predicates.push((p, depth + 1));
            }
            Predicate::True | Predicate::False => {}
        }
    }
    let mut seen = FxHashSet::default();
    while let Some(t) = terms.pop() {
        stop::check()?;
        if work == 0 {
            return Ok(None);
        }
        work -= 1;
        if !seen.insert(t.node_address()) {
            continue;
        }
        charge!(size_of::<TermKind>() + size_of::<TermAttributes>() + 64);
        let vars = &t.attributes().variables;
        charge!(vars.len().saturating_mul(256));
        for v in vars {
            charge!(v.name.len());
        }
        let items = match t.kind() {
            TermKind::Application {
                symbol, arguments, ..
            } => {
                // Foreign symbol metadata could retain arbitrary SMT text. It is not owned by
                // this immutable definition, so decline caching instead of undercharging it.
                if !definition
                    .symbols()
                    .get(&symbol.name)
                    .is_some_and(|s| Arc::ptr_eq(s, symbol))
                {
                    return Ok(None);
                }
                charge!(arguments.capacity().saturating_mul(size_of::<Term>()));
                arguments.len()
            }
            TermKind::DomainValue { value, .. } => {
                charge!(value.as_bytes().len() + 32);
                0
            }
            TermKind::Variable(v) => {
                charge!(v.name.len() + 32);
                0
            }
            TermKind::Map {
                definition,
                entries,
                ..
            } => {
                charge!(collection_cost(&CollectionMetadata::Map(
                    definition.clone()
                )));
                entries.len().saturating_mul(2)
            }
            TermKind::List {
                definition,
                heads,
                rest,
            } => {
                charge!(collection_cost(&CollectionMetadata::List(
                    definition.clone()
                )));
                heads
                    .len()
                    .saturating_add(rest.as_ref().map_or(0, |(_, t)| t.len()))
            }
            TermKind::Set {
                definition,
                elements,
                ..
            } => {
                charge!(collection_cost(&CollectionMetadata::Set(
                    definition.clone()
                )));
                elements.len()
            }
            TermKind::And(..) => 2,
            TermKind::Injection { .. } => 1,
        };
        if items > work {
            return Ok(None);
        }
        // At most O(items) chunk nodes; each summary has at most vars variables and tree
        // height at most log2(items)+1. This overcharges shared persistent summaries.
        if matches!(
            t.kind(),
            TermKind::Map { .. } | TermKind::List { .. } | TermKind::Set { .. }
        ) {
            let height = (usize::BITS - items.max(1).leading_zeros()) as usize + 1;
            charge!(items.saturating_mul(
                1024_usize.saturating_add(vars.len().saturating_mul(256).saturating_mul(height))
            ));
        }
        terms.extend(crate::term::immediate_children(t.kind()));
    }
    Ok(Some(limit - left))
}
fn collection_cost(c: &CollectionMetadata) -> usize {
    let (symbols, name) = match c {
        CollectionMetadata::Map(d) => (&d.symbols, &d.map_sort),
        CollectionMetadata::List(d) | CollectionMetadata::Set(d) => (&d.symbols, &d.list_sort),
    };
    [
        192,
        name.len(),
        symbols.unit.len(),
        symbols.element.len(),
        symbols.concat.len(),
    ]
    .into_iter()
    .fold(0, usize::saturating_add)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::Sort;
    use k_rust_kore::kore::parser::parse_definition;

    fn definition() -> BackendDefinition {
        BackendDefinition::internalize(
            &parse_definition(
                r#"[]
            module MAIN
            hooked-sort SortInt{} [hook{}("INT.Int"),hasDomainValues{}()]
            symbol pair{}(SortInt{},SortInt{}) : SortInt{} [function{}(),total{}()]
            endmodule []"#,
            )
            .unwrap(),
            "MAIN",
        )
        .unwrap()
    }
    fn diamond(d: &BackendDefinition, depth: usize) -> Term {
        let mut t = Term::int(1);
        for _ in 0..depth {
            t = Term::application(d.symbols()["pair"].clone(), Vec::new(), vec![t.clone(), t]);
        }
        t
    }
    fn get(cache: &Cache, q: &Query<'_>) -> Option<Answer> {
        cache.get(q).map_err(crate::stop::Stop::into_cause).unwrap()
    }
    fn insert(cache: &mut Cache, q: &Query<'_>, a: Answer, d: &BackendDefinition) {
        cache
            .insert(q, a, d)
            .map_err(crate::stop::Stop::into_cause)
            .unwrap()
    }
    #[test]
    fn equal_unshared_diamonds_reuse_without_tree_expansion() {
        let d = definition();
        let s = Substitution::new();
        let a = [Predicate::Equals(diamond(&d, 30), Term::int(1))];
        let b = [Predicate::Equals(diamond(&d, 30), Term::int(1))];
        let mut c = Cache::new(4, RETENTION_LIMIT);
        insert(
            &mut c,
            &Query::new(false, &a, &s, &[]),
            Answer::Sat(Satisfiability::Sat),
            &d,
        );
        assert_eq!(c.entries.len(), 1);
        assert!(
            c.retention < 50_000,
            "charge must follow the 31-node DAG, not its expanded tree"
        );
        assert!(matches!(
            get(&c, &Query::new(false, &b, &s, &[])),
            Some(Answer::Sat(Satisfiability::Sat))
        ));
    }
    #[test]
    fn a_shared_dag_and_its_unshared_tree_have_the_same_key_meaning() {
        fn tree(d: &BackendDefinition, n: usize) -> Term {
            if n == 0 {
                Term::int(1)
            } else {
                Term::application(
                    d.symbols()["pair"].clone(),
                    Vec::new(),
                    vec![tree(d, n - 1), tree(d, n - 1)],
                )
            }
        }
        let d = definition();
        let s = Substitution::new();
        let a = [Predicate::Ceil(diamond(&d, 8))];
        let b = [Predicate::Ceil(tree(&d, 8))];
        let mut c = Cache::new(4, RETENTION_LIMIT);
        insert(
            &mut c,
            &Query::new(false, &a, &s, &[]),
            Answer::Sat(Satisfiability::Sat),
            &d,
        );
        assert!(get(&c, &Query::new(false, &b, &s, &[])).is_some());
    }
    #[test]
    fn fingerprint_collisions_require_the_complete_substitution() {
        let d = definition();
        let mut a = Substitution::new();
        for n in 0..40 {
            a.insert(
                Variable::new(format!("X{n:02}"), Sort::simple("SortInt")),
                Term::int(n),
            );
        }
        let mut b = a.clone();
        b.insert(
            Variable::new("X39", Sort::simple("SortInt")),
            Term::int(999),
        );
        let qa = Query::new(false, &[], &a, &[]);
        let qb = Query::new(false, &[], &b, &[]);
        assert_eq!(qa.fingerprint(), qb.fingerprint());
        let mut c = Cache::new(4, RETENTION_LIMIT);
        insert(&mut c, &qa, Answer::Sat(Satisfiability::Sat), &d);
        assert!(get(&c, &qa).is_some());
        assert!(get(&c, &qb).is_none());
    }
    #[test]
    fn unknown_answers_are_not_inserted_and_fifo_eviction_is_bounded() {
        let d = definition();
        let s = Substitution::new();
        let mut c = Cache::new(1, RETENTION_LIMIT);
        let a = [Predicate::Equals(Term::int(1), Term::int(1))];
        let qa = Query::new(false, &a, &s, &[]);
        insert(
            &mut c,
            &qa,
            Answer::Sat(Satisfiability::Unknown("timeout".into())),
            &d,
        );
        assert!(c.entries.is_empty());
        insert(&mut c, &qa, Answer::Sat(Satisfiability::Sat), &d);
        let b = [Predicate::Equals(Term::int(2), Term::int(2))];
        let qb = Query::new(false, &b, &s, &[]);
        insert(&mut c, &qb, Answer::Sat(Satisfiability::Sat), &d);
        assert!(get(&c, &qa).is_none());
        assert!(get(&c, &qb).is_some());
        assert_eq!(c.retention, c.entries[0].retention);
        let charge = c.retention;
        let mut c = Cache::new(10, charge - 1);
        insert(&mut c, &qb, Answer::Sat(Satisfiability::Sat), &d);
        assert!(c.entries.is_empty());
        assert_eq!(c.retention, 0);
    }
    #[test]
    fn retained_payload_and_argument_capacity_are_charged_before_admission() {
        let d = definition();
        let s = Substitution::new();
        let mut c = Cache::new(4, 10_000);
        let huge = [Predicate::Ceil(Term::string("x".repeat(20_000)))];
        insert(
            &mut c,
            &Query::new(false, &huge, &s, &[]),
            Answer::Sat(Satisfiability::Sat),
            &d,
        );
        assert!(c.entries.is_empty());
        let mut arguments = Vec::with_capacity(20_000);
        arguments.extend([Term::int(1), Term::int(2)]);
        let t = Term::application(d.symbols()["pair"].clone(), Vec::new(), arguments);
        let huge = [Predicate::Ceil(t)];
        insert(
            &mut c,
            &Query::new(false, &huge, &s, &[]),
            Answer::Sat(Satisfiability::Sat),
            &d,
        );
        assert!(c.entries.is_empty());
        // A name-compatible foreign symbol can carry arbitrary text/metadata. The immutable
        // owner does not retain it; its graph therefore cannot be charged as owner-owned.
        let foreign = Arc::new(d.symbols()["pair"].as_ref().clone());
        let terms = [Predicate::Ceil(Term::application(
            foreign,
            Vec::new(),
            vec![Term::int(1), Term::int(2)],
        ))];
        insert(
            &mut c,
            &Query::new(false, &terms, &s, &[]),
            Answer::Sat(Satisfiability::Sat),
            &d,
        );
        assert!(c.entries.is_empty());
    }
    #[test]
    fn logical_kind_and_binder_are_part_of_the_exact_input() {
        let d = definition();
        let s = Substitution::new();
        let x = Variable::new("X", Sort::simple("SortInt"));
        let a = [Predicate::Exists(
            x.clone(),
            Arc::new(Predicate::Ceil(Term::variable(x.clone()))),
        )];
        let b = [Predicate::Forall(
            x.clone(),
            Arc::new(Predicate::Ceil(Term::variable(x))),
        )];
        let mut c = Cache::new(4, RETENTION_LIMIT);
        insert(
            &mut c,
            &Query::new(false, &a, &s, &[]),
            Answer::Sat(Satisfiability::Sat),
            &d,
        );
        assert!(get(&c, &Query::new(false, &b, &s, &[])).is_none());
        assert!(get(&c, &Query::new(true, &a, &s, &[])).is_none());
    }
}
