//! What a left-hand side's syntax says about the values it denotes.
//!
//! An equation `l = r` constrains the value every instance of `l` denotes. The instance-normal
//! scan and the simplifier's certificate conclude from a syntactic fact about `l` (it does not
//! unify with a subject, equation matching fails on it) that the equation does not apply to the
//! subject's value. Both read the evaluator's normal forms as distinct values. That reading
//! needs, for each equation, that no instance of a proper subterm of `l` is rewritten: otherwise
//! an instance of `l` has a reduct below its root (`w(h(1))` from `w(h(3))` under
//! `h(3) = h(1)`) that is a normal form the equation never matches, although the equation equates
//! its value with the right-hand side's. When the arguments of `l` are normal on every instance
//! ([`BackendDefinition::pattern_arguments_normal`]) there is no such reduct, and the syntactic
//! fact is a fact about values.
//!
//! For any other equation, the question is whether an instance of `l` can have the subject as a
//! reduct below its root, that is, whether each argument of an instance can reduce to the
//! subject's argument. That is ruled out at one argument position when no reduct of the pattern's
//! argument can have the subject argument's root ([`BackendDefinition::misses_values`]). A
//! reduct keeps the root of the term it comes from until an equation rewrites it at the root,
//! which gives the root of that equation's right-hand side, and so on ([`PatternFacts`]); a
//! right-hand side with an open root (a variable, a function application) leaves the roots
//! unbounded. This keeps FUN's overloaded application `P1 P2`, whose overload equation rewrites
//! some instances to an injection from `Val`, apart from an injected `Name`.
//!
//! Narrowing ([`BackendDefinition::narrow`]) asks which right-hand sides an equation gives a
//! reduct of a pattern, by matching the equation's left-hand side against the pattern. It reads
//! that left-hand side by its values as well: a subterm's syntax counts only where the subterm's
//! instances are normal forms (every subterm of a normal-argument equation's left-hand side, and
//! otherwise a subterm shown normal), and any other subterm stands for any value.

use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
    sync::Arc,
};

use rustc_hash::FxHashSet;

use super::{SCAN, Scan, ScanScope, ValueQuestion, compared_by_root, separated, token};
use crate::substitution::{Substitution, substitute};
use crate::{
    definition::BackendDefinition,
    rule::{RewriteRule, RuleRhs, TermIndex, Theory, term_index},
    term::{
        HeadRole, Term, TermKind,
        head::{
            Fixed, Head, NormalForms, PatternReading, Shape, classify_pattern, classify_value,
            compare_roots,
        },
    },
};

/// Facts about the left-hand sides of a definition's function and simplification equations,
/// computed once per definition ([`pattern_facts`]).
#[derive(Clone, Debug)]
pub(crate) struct PatternFacts {
    /// The equations whose left-hand side has instance-normal immediate subterms, by address
    /// ([`BackendDefinition::pattern_arguments_normal`]).
    normal_rules: FxHashSet<usize>,
    /// The roots the reducts of a term can have besides its own, by the term's index: the
    /// right-hand sides of the equations indexed there, and transitively those indexed by their
    /// roots. `None` when some such right-hand side has an open root. An index with no equations
    /// has none besides the term's own root.
    value_roots: Arc<BTreeMap<TermIndex, Option<Vec<Term>>>>,
    /// Some equation is indexed by a bare variable, so it may rewrite a term of any root to
    /// anything: no reduct's root is bounded.
    unbounded: bool,
}

thread_local! {
    /// While [`pattern_facts`] computes the facts on this thread, the ones it has shown so far:
    /// [`BackendDefinition::pattern_arguments_normal`] answers from them, so the computation
    /// neither waits on the definition's facts nor reaches for an answer it has not derived.
    static APPROXIMATION: RefCell<Option<Rc<PatternFacts>>> = const { RefCell::new(None) };
}

/// The key of a term equation of the definition: its address in the definition's theory, which
/// the definition's clones share (`Arc`).
fn rule_key(rule: &RewriteRule) -> usize {
    std::ptr::from_ref(rule).addr()
}

impl BackendDefinition {
    /// Whether every immediate subterm of the left-hand side of `rule`, a function or
    /// simplification equation of this definition (the arguments of its root, the elements of
    /// a collection, the operand of an injection, the conjuncts of an `\and`), is a normal
    /// pattern ([`Self::normal_pattern`]); `true` for a variable left-hand side. `false` for a
    /// rule that is not one of the definition's own term equations (a renamed copy included):
    /// the answer is looked up by the rule's address, so a caller asks with the rule equation
    /// selection returned.
    ///
    /// Where it holds, every instance of the left-hand side (variables ranging over values)
    /// has normal arguments, and so does every instance of an instance-normal subject, so an
    /// instance of the left-hand side and an instance of the subject that denote the same value
    /// at the same root are the same term. Then the syntactic answers about the left-hand side
    /// (it does not unify with the subject; equation matching refutes it; it matches the subject
    /// only at the substitution decomposition finds) are answers about the values it denotes.
    ///
    /// Deciding a left-hand side argument scans the equations that could reach it, whose own
    /// exclusion asks this question about their left-hand sides. The answers are therefore
    /// computed once per definition, in rounds, by [`pattern_facts`]: no equation's answer rests
    /// on itself, and the set does not depend on the order equations are asked in.
    pub(crate) fn pattern_arguments_normal(&self, rule: &RewriteRule) -> bool {
        let key = rule_key(rule);
        self.with_pattern_facts(|facts| facts.normal_rules.contains(&key))
    }

    /// Whether a failed match of the equation `equation` on `subject`, a ground term whose
    /// arguments the simplifier has evaluated, shows that no valuation of the equation's
    /// left-hand side denotes the subject's value: its left-hand side's arguments are normal
    /// patterns, or its values miss the subject at some argument ([`Self::misses_values`], with
    /// the simplifier's value certificate as the evidence for the subject's roots).
    pub(crate) fn failed_match_is_about_values(
        &self,
        equation: &RewriteRule,
        subject: &Term,
    ) -> bool {
        self.pattern_arguments_normal(equation) || {
            let _scope = ScanScope::enter();
            self.misses_values(
                &equation.lhs,
                subject,
                &mut crate::term::head::CertifiedOnly,
            )
        }
    }

    /// Whether no instance of the left-hand side `pattern` has `subject`, an application with the
    /// same root whose arguments are normal forms, as a reduct below the root, because at some
    /// argument position no reduct of the pattern's argument is the subject's argument
    /// ([`Self::values_apart`]). `subject_roots` fixes the roots of the subject's equation-head
    /// subterms. Positions are compared one at a time, so variables shared between positions are
    /// not followed: that only answers `false` more often.
    ///
    /// The question is answered `false` when [`super::VALUE_QUESTIONS`] are already open on the
    /// thread (`super::ValueQuestion`).
    pub(super) fn misses_values(
        &self,
        pattern: &Term,
        subject: &Term,
        subject_roots: &mut dyn NormalForms,
    ) -> bool {
        let Some(_question) = ValueQuestion::open() else {
            return false;
        };
        self.misses_values_at(pattern, subject, subject_roots)
    }

    fn misses_values_at(
        &self,
        pattern: &Term,
        subject: &Term,
        subject_roots: &mut dyn NormalForms,
    ) -> bool {
        match (pattern.kind(), subject.kind()) {
            (TermKind::And(left, right), _) => {
                self.misses_values_at(left, subject, subject_roots)
                    || self.misses_values_at(right, subject, subject_roots)
            }
            (
                TermKind::Application {
                    symbol: pattern_symbol,
                    arguments: pattern_arguments,
                    ..
                },
                TermKind::Application {
                    symbol: subject_symbol,
                    arguments: subject_arguments,
                    ..
                },
            ) if pattern_symbol.name == subject_symbol.name
                && pattern_arguments.len() == subject_arguments.len() =>
            {
                pattern_arguments
                    .iter()
                    .zip(subject_arguments)
                    .any(|(pattern, subject)| self.values_apart(pattern, subject, subject_roots))
            }
            _ => false,
        }
    }

    /// Whether no reduct of an instance of the pattern `pattern` is `subject`, a normal form whose
    /// root `subject_roots` must fix: no root a reduct can have
    /// ([`Self::value_representatives`]) leads to the subject ([`Self::representative_apart`]).
    fn values_apart(
        &self,
        pattern: &Term,
        subject: &Term,
        subject_roots: &mut dyn NormalForms,
    ) -> bool {
        if let TermKind::And(left, right) = pattern.kind() {
            return self.values_apart(left, subject, subject_roots)
                || self.values_apart(right, subject, subject_roots);
        }
        let Head::Fixed(subject_root) = classify_value(subject, subject_roots) else {
            return false;
        };
        self.value_representatives(pattern)
            .is_some_and(|representatives| {
                representatives.iter().all(|representative| {
                    self.representative_apart(representative, subject_root, subject_roots)
                })
            })
    }

    /// Terms that cover every reduct of an instance of `pattern`, read up to reducts: every such
    /// reduct is an instance of one of them in which each argument is a reduct of an instance of
    /// that term's argument. `None` when that is not bounded.
    ///
    /// A pattern whose instances are normal forms is its own only reduct. Otherwise a reduct
    /// keeps the pattern's root, with its arguments reduced, until an equation indexed by that
    /// root rewrites it; the result is an instance of that equation's right-hand side, whose
    /// variables are bound by matching its left-hand side against the reduct
    /// ([`Self::narrow`]), and it may be rewritten at its own root again. The representatives
    /// are the pattern and the right-hand sides so reached, up to [`REPRESENTATIVES`] terms and
    /// [`NARROWING_DEPTH`] levels of nested patterns; past either bound they are the pattern and
    /// every right-hand side its root's equations reach (`PatternFacts::value_roots`), which
    /// covers the same reducts with fewer bindings. An as-pattern is covered by either conjunct.
    fn value_representatives(&self, pattern: &Term) -> Option<Vec<Term>> {
        self.representatives(pattern, NARROWING_DEPTH)
    }

    fn representatives(&self, pattern: &Term, depth: usize) -> Option<Vec<Term>> {
        match pattern.kind() {
            TermKind::And(left, right) => {
                let conjunct = if matches!(left.kind(), TermKind::Variable(_)) {
                    right
                } else {
                    left
                };
                return self.representatives(conjunct, depth);
            }
            TermKind::Variable(_) => return None,
            _ => {}
        }
        match pattern.shape() {
            Shape::DomainValue
            | Shape::Injection
            | Shape::Collection(_)
            | Shape::Application(HeadRole::FreeConstructor | HeadRole::EquationHead) => {}
            Shape::Variable
            | Shape::And
            | Shape::Application(
                HeadRole::Function { .. } | HeadRole::Uninterpreted | HeadRole::Residual,
            ) => return None,
        }
        if self.normal_pattern(pattern) {
            return Some(vec![pattern.clone()]);
        }
        if depth == 0 {
            return self.reachable_representatives(pattern);
        }
        if self.with_pattern_facts(|facts| facts.unbounded) {
            return None;
        }
        let mut representatives = vec![pattern.clone()];
        let mut next = 0;
        while let Some(term) = representatives.get(next).cloned() {
            next += 1;
            let index = term_index(&term);
            let equations = [self.function_theory(), self.simplification_theory()]
                .into_iter()
                .filter_map(|theory| theory.get(&index))
                .flat_map(|groups| groups.values().flatten())
                .collect::<Vec<_>>();
            for equation in equations {
                let RuleRhs::Term(right) = &equation.rhs else {
                    return None;
                };
                let reading = if self.pattern_arguments_normal(equation) {
                    LeftReading::Values
                } else {
                    LeftReading::Checked
                };
                let Some(bindings) = self.narrow(&equation.lhs, &term, depth - 1, reading) else {
                    continue;
                };
                for binding in bindings {
                    let reduct = substitute(right, &binding);
                    if representatives.contains(&reduct) {
                        continue;
                    }
                    if representatives.len() == REPRESENTATIVES {
                        return self.reachable_representatives(pattern);
                    }
                    representatives.push(reduct);
                }
            }
        }
        Some(representatives)
    }

    /// The pattern and every right-hand side the equations of its root reach
    /// (`PatternFacts::value_roots`): representatives without bindings.
    fn reachable_representatives(&self, pattern: &Term) -> Option<Vec<Term>> {
        let mut representatives =
            self.with_pattern_facts(|facts| match facts.value_roots.get(&term_index(pattern)) {
                Some(roots) => roots.clone(),
                None => (!facts.unbounded).then(Vec::new),
            })?;
        representatives.push(pattern.clone());
        Some(representatives)
    }

    /// The bindings of the variables of an equation's left-hand side `left` under which a reduct
    /// of an instance of `term` (read up to reducts) that keeps `term`'s root has the value of an
    /// instance of `left`: one substitution per alternative, each binding a variable to a subterm
    /// of `term` (read up to reducts) or leaving it unbound (any value). `None` when no such
    /// reduct has such a value. A variable bound twice keeps its first binding: its value is a
    /// reduct of both subterms, so either covers it.
    ///
    /// `left` is read through its values (`reading`): a subterm of it is compared by its syntax
    /// only when its instances are normal forms, so that the instance is the value; any other
    /// subterm stands for any value and binds nothing ([`Self::narrow_argument`]).
    fn narrow(
        &self,
        left: &Term,
        term: &Term,
        depth: usize,
        reading: LeftReading,
    ) -> Option<Vec<Substitution>> {
        let unknown = || Some(vec![Substitution::new()]);
        match (left.kind(), term.kind()) {
            (TermKind::Variable(variable), _) => {
                Some(vec![Substitution::from([(variable.clone(), term.clone())])])
            }
            (TermKind::And(first, second), _) => {
                let first = self.narrow(first, term, depth, reading)?;
                let second = self.narrow(second, term, depth, reading)?;
                combine(first, second)
            }
            (_, TermKind::Variable(_)) => unknown(),
            (_, TermKind::And(conjunct, other)) => {
                let conjunct = if matches!(conjunct.kind(), TermKind::Variable(_)) {
                    other
                } else {
                    conjunct
                };
                self.narrow(left, conjunct, depth, reading)
            }
            (
                TermKind::Application {
                    symbol: left_symbol,
                    sort_arguments: left_sorts,
                    arguments: left_arguments,
                },
                TermKind::Application {
                    symbol: term_symbol,
                    sort_arguments: term_sorts,
                    arguments: term_arguments,
                },
            ) if left_symbol.name == term_symbol.name => {
                if left_sorts != term_sorts || left_arguments.len() != term_arguments.len() {
                    return unknown();
                }
                let mut alternatives = vec![Substitution::new()];
                for (left_argument, term_argument) in left_arguments.iter().zip(term_arguments) {
                    let argument =
                        self.narrow_argument(left_argument, term_argument, depth, reading)?;
                    alternatives = combine(alternatives, argument)?;
                }
                Some(alternatives)
            }
            (
                TermKind::Injection {
                    source: left_source,
                    target: left_target,
                    term: left_operand,
                },
                TermKind::Injection {
                    source: term_source,
                    target: term_target,
                    term: term_operand,
                },
            ) if left_target == term_target => {
                if left_source == term_source {
                    self.narrow_argument(left_operand, term_operand, depth, reading)
                } else {
                    // A reduct of an injection from `term_source` is one from that sort or, its
                    // operand having reduced to an injection, from a sort below it: one from
                    // `left_source` only when that is below, through an operand that reduces to
                    // an injection from it.
                    match self
                        .sort_graph()
                        .check_subsort(left_source, term_source)
                        .ok()
                    {
                        Some(false) => None,
                        Some(true) => self.narrow_argument(
                            &Term::injection(
                                left_source.clone(),
                                term_source.clone(),
                                left_operand.clone(),
                            ),
                            term_operand,
                            depth,
                            reading,
                        ),
                        None => unknown(),
                    }
                }
            }
            (
                TermKind::DomainValue {
                    sort: left_sort,
                    value: left_value,
                },
                TermKind::DomainValue {
                    sort: term_sort,
                    value: term_value,
                },
            ) if left_sort == term_sort && left_value != term_value => None,
            _ => match (
                classify_pattern(PatternReading::AsWritten, left),
                classify_pattern(PatternReading::AsWritten, term),
            ) {
                (Head::Fixed(left_root), Head::Fixed(term_root)) => {
                    let apart = match (left.kind(), term.kind()) {
                        (TermKind::Injection { .. }, TermKind::Application { .. })
                        | (TermKind::Application { .. }, TermKind::Injection { .. }) => true,
                        _ => {
                            compared_by_root(left_root)
                                && compared_by_root(term_root)
                                && separated(compare_roots(left_root, term_root))
                        }
                    };
                    if apart { None } else { unknown() }
                }
                _ => unknown(),
            },
        }
    }

    /// [`Self::narrow`] for an argument position: the argument `term` is read up to reducts, so
    /// each of its representatives is matched. Under [`LeftReading::Checked`] the left-hand side
    /// subterm `left` is compared by its syntax only when it is a normal pattern
    /// ([`Self::normal_pattern`]), and then so is every subterm below it; otherwise its value is
    /// any reduct of any of its instances, which this does not compute: it stands for any value
    /// and binds none of its variables.
    fn narrow_argument(
        &self,
        left: &Term,
        term: &Term,
        depth: usize,
        reading: LeftReading,
    ) -> Option<Vec<Substitution>> {
        if let TermKind::Variable(variable) = left.kind() {
            return Some(vec![Substitution::from([(variable.clone(), term.clone())])]);
        }
        if reading == LeftReading::Checked && !self.normal_pattern(left) {
            return Some(vec![Substitution::new()]);
        }
        let Some(representatives) = self.representatives(term, depth) else {
            return Some(vec![Substitution::new()]);
        };
        let mut alternatives = Vec::new();
        for representative in &representatives {
            if let Some(found) = self.narrow(left, representative, depth, LeftReading::Values) {
                alternatives.extend(found);
            }
        }
        bounded_alternatives(alternatives)
    }

    /// Whether no reduct with the root of `representative` is the normal form `subject`. A reduct
    /// that keeps the representative's root has the representative's arguments reduced (a root
    /// step gives another representative), so an application of the subject's symbol is apart
    /// when some pair of arguments is. Two injections into one sort with one source compare
    /// their operands. With the subject's source strictly below, the representative's operand
    /// would have to reduce to the subject's operand injected into the representative's source;
    /// with it strictly above, the subject's operand would have to be an injection. With neither
    /// below the other, they are apart when the sources have no common subsort or the subject's
    /// operand is constructor-like, so that its value is of the subject's source sort and of no
    /// sort not above it. An injection and an application never share a value; two domain
    /// values of one sort are apart when they differ; other roots are apart when the root
    /// comparison separates them.
    fn representative_apart(
        &self,
        representative: &Term,
        subject: Fixed<'_>,
        subject_roots: &mut dyn NormalForms,
    ) -> bool {
        let Head::Fixed(representative_root) =
            classify_pattern(PatternReading::AsWritten, representative)
        else {
            return false;
        };
        match (representative.kind(), subject.term().kind()) {
            (
                TermKind::Application {
                    symbol: representative_symbol,
                    sort_arguments: representative_sorts,
                    arguments: representative_arguments,
                },
                TermKind::Application {
                    symbol: subject_symbol,
                    sort_arguments: subject_sorts,
                    arguments: subject_arguments,
                },
            ) if representative_symbol.name == subject_symbol.name => {
                representative_sorts == subject_sorts
                    && representative_arguments.len() == subject_arguments.len()
                    && representative_arguments.iter().zip(subject_arguments).any(
                        |(pattern, subject)| self.values_apart(pattern, subject, subject_roots),
                    )
            }
            (
                TermKind::Injection {
                    source: representative_source,
                    target: representative_target,
                    term: representative_operand,
                },
                TermKind::Injection {
                    source: subject_source,
                    target: subject_target,
                    term: subject_operand,
                },
            ) => {
                let sorts = self.sort_graph();
                let below = |sub, sup| sorts.check_subsort(sub, sup).ok();
                if representative_target != subject_target {
                    false
                } else if representative_source == subject_source {
                    self.values_apart(representative_operand, subject_operand, subject_roots)
                } else if below(subject_source, representative_source) == Some(true) {
                    // The subject is the injection from the representative's source of
                    // `inj{subject_source, representative_source}(subject_operand)`.
                    self.values_apart(
                        representative_operand,
                        &Term::injection(
                            subject_source.clone(),
                            representative_source.clone(),
                            subject_operand.clone(),
                        ),
                        subject_roots,
                    )
                } else if below(representative_source, subject_source) == Some(true) {
                    !matches!(subject_operand.kind(), TermKind::Injection { .. })
                } else {
                    below(subject_source, representative_source) == Some(false)
                        && below(representative_source, subject_source) == Some(false)
                        && (sorts.known_overlap(representative_source, subject_source)
                            == Some(false)
                            || subject_operand.attributes().constructor_like)
                }
            }
            (TermKind::Injection { .. }, TermKind::Application { .. })
            | (TermKind::Application { .. }, TermKind::Injection { .. }) => true,
            (
                TermKind::DomainValue {
                    sort: representative_sort,
                    value: representative_value,
                },
                TermKind::DomainValue {
                    sort: subject_sort,
                    value: subject_value,
                },
            ) => representative_sort == subject_sort && representative_value != subject_value,
            _ => {
                compared_by_root(representative_root)
                    && compared_by_root(subject)
                    && separated(compare_roots(representative_root, subject))
            }
        }
    }

    /// The test [`pattern_facts`] applies to one left-hand side: every immediate subterm is a
    /// normal pattern ([`Self::normal_pattern`]); for a conjunction, of each conjunct.
    fn left_hand_side_arguments_normal(&self, pattern: &Term) -> bool {
        match pattern.kind() {
            TermKind::And(left, right) => {
                self.left_hand_side_arguments_normal(left)
                    && self.left_hand_side_arguments_normal(right)
            }
            _ => token::every_immediate_subterm(pattern, |subterm| self.normal_pattern(subterm)),
        }
    }

    /// Whether every valuation of the pattern `pattern` that denotes a value denotes it by a
    /// normal form that instantiates every conjunct of `pattern` alike. A conjunction-free
    /// pattern has this when it is instance-normal. A conjunction `p /\ q` (an as-pattern)
    /// denotes a value where both conjuncts denote it; when both have the property, the two
    /// normal forms denote one value, so they are one term. A constructor application or an
    /// injection has it when its arguments do, since it is a normal form when they are. Any
    /// other pattern with a conjunction inside is answered `false`, which is always sound.
    fn normal_pattern(&self, pattern: &Term) -> bool {
        match pattern.kind() {
            TermKind::And(left, right) => self.normal_pattern(left) && self.normal_pattern(right),
            _ if !contains_conjunction(pattern) => self.instance_normal_memoized(pattern).is_some(),
            _ => {
                matches!(
                    pattern.shape(),
                    Shape::Injection | Shape::Application(HeadRole::FreeConstructor)
                ) && token::every_immediate_subterm(pattern, |subterm| self.normal_pattern(subterm))
            }
        }
    }

    fn with_pattern_facts<R>(&self, read: impl FnOnce(&PatternFacts) -> R) -> R {
        match APPROXIMATION.with(|approximation| approximation.borrow().clone()) {
            Some(facts) => read(&facts),
            None => read(self.pattern_facts()),
        }
    }
}

/// How [`BackendDefinition::narrow`] reads an equation's left-hand side.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LeftReading {
    /// Every subterm below the root is a normal pattern: the left-hand side of a normal-argument
    /// equation ([`BackendDefinition::pattern_arguments_normal`]), or a subterm of a normal
    /// pattern. Its syntax is its values.
    Values,
    /// Any other equation: each argument is checked before its syntax is used.
    Checked,
}

/// The alternatives one narrowing found: `None` when there are none, the one alternative that
/// binds nothing when there are more than [`REPRESENTATIVES`].
fn bounded_alternatives(alternatives: Vec<Substitution>) -> Option<Vec<Substitution>> {
    if alternatives.is_empty() {
        None
    } else if alternatives.len() > REPRESENTATIVES {
        Some(vec![Substitution::new()])
    } else {
        Some(alternatives)
    }
}

/// The most representatives [`BackendDefinition::value_representatives`] keeps for one pattern,
/// and the most alternatives one narrowing keeps, before falling back to coarser ones.
const REPRESENTATIVES: usize = 64;

/// The levels of nested patterns whose representatives narrowing computes before falling back
/// to coarser ones.
const NARROWING_DEPTH: usize = 3;

/// Every pairing of an alternative of `first` with one of `second`, the first's binding kept
/// for a variable both bind; `None` when either has none. More than [`REPRESENTATIVES`]
/// pairings give the one alternative that binds nothing.
fn combine(first: Vec<Substitution>, second: Vec<Substitution>) -> Option<Vec<Substitution>> {
    if first.is_empty() || second.is_empty() {
        return None;
    }
    if first.len() * second.len() > REPRESENTATIVES {
        return Some(vec![Substitution::new()]);
    }
    Some(
        first
            .iter()
            .flat_map(|first| {
                second.iter().map(move |second| {
                    let mut both = second.clone();
                    both.extend(
                        first
                            .iter()
                            .map(|(variable, term)| (variable.clone(), term.clone())),
                    );
                    both
                })
            })
            .collect(),
    )
}

/// Whether `pattern`, a left-hand side subterm of the definition, has a conjunction at or
/// below its root.
fn contains_conjunction(pattern: &Term) -> bool {
    matches!(pattern.kind(), TermKind::And(..))
        || !token::every_immediate_subterm(pattern, |subterm| !contains_conjunction(subterm))
}

/// The [`PatternFacts`] of `definition`.
///
/// The value roots come first: they read only the equations' right-hand sides. The equations
/// with normal left-hand side arguments are then found in rounds. Starting from the empty set,
/// each round adds the equations whose left-hand side's immediate subterms are normal patterns
/// when instance normality reads the previous round's set: an equation in the set is excluded
/// from a scan by its syntax, any other by the reducts of its arguments
/// (`BackendDefinition::excluded`). Every equation in a round's set has normal arguments, so
/// every answer given during the round is sound, and so is every equation the round adds. Each
/// round's set is a function of the previous one and the rounds only add, so they stop when one
/// adds nothing, and the result does not depend on the order of the equations: each left-hand
/// side is tested in a scan scope of its own, from an empty memo.
///
/// The exclusion of an equation outside the set decides the instance normality of terms that are
/// not subterms of the term asked: the arguments of other left-hand sides and right-hand sides
/// instantiated by narrowing ([`BackendDefinition::misses_values`]). Those decisions can come back
/// to a term being decided (`f(f(inj(k(X)))) = c` asks about `f(inj(k(X)))` while deciding it),
/// and narrowing builds new terms at each level. A term asked while being decided is answered
/// "not instance-normal", and at most `super::VALUE_QUESTIONS` such exclusions are open at once
/// (`super::ValueQuestion`); both answers are conservative, so every answer stays sound.
///
/// The computation starts its own scan memo (and restores the caller's afterwards): it runs on
/// first use, which may be inside a scan whose memo was filled before the facts existed.
pub(crate) fn pattern_facts(definition: &BackendDefinition) -> PatternFacts {
    let theories = [
        definition.function_theory(),
        definition.simplification_theory(),
    ];
    let unbounded = theories.iter().any(|theory| {
        theory
            .get(&TermIndex::Variable)
            .is_some_and(|groups| groups.values().any(|rules| !rules.is_empty()))
    });
    let value_roots = Arc::new(value_roots(&theories, unbounded));
    let rules = theories
        .into_iter()
        .flat_map(|theory| theory.values())
        .flat_map(|groups| groups.values().flatten())
        .map(AsRef::as_ref)
        .collect::<Vec<&RewriteRule>>();
    let _computing = Computing::start();
    let mut facts = PatternFacts {
        normal_rules: FxHashSet::default(),
        value_roots,
        unbounded,
    };
    loop {
        let approximation = Rc::new(facts.clone());
        APPROXIMATION.with(|slot| *slot.borrow_mut() = Some(approximation));
        let added = rules
            .iter()
            .filter(|rule| !facts.normal_rules.contains(&rule_key(rule)))
            .filter(|rule| {
                let _scope = ScanScope::enter();
                definition.left_hand_side_arguments_normal(&rule.lhs)
            })
            .map(|rule| rule_key(rule))
            .collect::<Vec<_>>();
        if added.is_empty() {
            return facts;
        }
        facts.normal_rules.extend(added);
    }
}

/// [`PatternFacts::value_roots`] for every index of `theories` with a fixed root.
fn value_roots(theories: &[&Theory; 2], unbounded: bool) -> BTreeMap<TermIndex, Option<Vec<Term>>> {
    theories
        .iter()
        .flat_map(|theory| theory.keys())
        .filter(|index| !matches!(index, TermIndex::Variable | TermIndex::And))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .map(|index| {
            let roots = if unbounded {
                None
            } else {
                reachable_roots(theories, index)
            };
            (index.clone(), roots)
        })
        .collect()
}

/// The right-hand sides of the equations indexed by `start`, and of those indexed by the roots
/// of the right-hand sides met, transitively; `None` when one has an open root.
fn reachable_roots(theories: &[&Theory; 2], start: &TermIndex) -> Option<Vec<Term>> {
    let mut visited = BTreeSet::from([start.clone()]);
    let mut pending = vec![start.clone()];
    let mut roots = Vec::new();
    while let Some(index) = pending.pop() {
        let equations = theories
            .iter()
            .filter_map(|theory| theory.get(&index))
            .flat_map(|groups| groups.values().flatten());
        for equation in equations {
            let RuleRhs::Term(right) = &equation.rhs else {
                return None;
            };
            match right.shape() {
                Shape::DomainValue
                | Shape::Injection
                | Shape::Collection(_)
                | Shape::Application(HeadRole::FreeConstructor | HeadRole::EquationHead) => {
                    roots.push(right.clone());
                    let next = term_index(right);
                    if visited.insert(next.clone()) {
                        pending.push(next);
                    }
                }
                Shape::Variable
                | Shape::And
                | Shape::Application(
                    HeadRole::Function { .. } | HeadRole::Uninterpreted | HeadRole::Residual,
                ) => return None,
            }
        }
    }
    Some(roots)
}

/// [`pattern_facts`] in progress on this thread: holds the caller's scan memo, and on drop
/// (also when the computation unwinds) clears the approximation and restores the memo.
struct Computing {
    caller_scan: Scan,
}

impl Computing {
    fn start() -> Self {
        Self {
            caller_scan: SCAN.with(|scan| std::mem::take(&mut *scan.borrow_mut())),
        }
    }
}

impl Drop for Computing {
    fn drop(&mut self) {
        APPROXIMATION.with(|approximation| *approximation.borrow_mut() = None);
        let caller_scan = std::mem::take(&mut self.caller_scan);
        SCAN.with(|scan| *scan.borrow_mut() = caller_scan);
    }
}
