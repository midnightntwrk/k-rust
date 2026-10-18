//! The refutations a sequential execution reuses: a rule attempt that a configuration refuted is
//! not made again on a later configuration that agrees with it on everything the attempt read.
//!
//! # What an attempt reads
//!
//! The memo is kept only for a subject that is ground (no variable), `ceil_free` and without
//! constraints ([`RefutationMemo::eligible`]), and only for the two refutations whose cause the
//! attempt's own phases record ([`RefutationSite`]): its initial match `Failed` (P3), or its
//! initial match succeeded directly and its instantiated `requires` simplified to `False` with no
//! match condition (P11). An attempt that emitted a diagnostic, noted a path fact (it read a
//! value the definition leaves open, `crate::path_facts`), used the recovery ladder or
//! re-entered is not kept. On such a subject and up to those exits the attempt is a function of
//! the left-hand side's match against the subject term and of the `requires` instantiated by it:
//! the path knowledge is empty (no constraint, and `\ceil` of a `ceil_free` subject is empty),
//! the rule is not renamed apart (the subject has no variable), the fresh counter, the I/O state
//! and the one-state reading are not read before P13, the match conditions and the definedness
//! obligations of the bindings are empty (a direct match binds only left-hand-side variables, to
//! subterms of a `ceil_free` term, which are `ceil_free`, as is every collection the pattern
//! consumes), and the simplification options, solver and definition are the execution's.
//!
//! The matcher reads the subject along the left-hand side ([`same_reads`]):
//! - at an application of a free constructor, a subject application of the same symbol with the
//!   same sort arguments and arity is decomposed into its arguments and nothing else
//!   (`matcher_root_policy` decomposes two free-constructor applications of one name, overload
//!   resolution leaves one name alone, the root of a free-constructor application is classified
//!   from its symbol alone); an injection of equal source and target is decomposed alike;
//! - at an element variable that the rule reads nowhere else (it occurs once in the left-hand
//!   side, not in `requires`), the pair binds the variable when the subject's sort is a subsort
//!   of its sort, is deferred when the subject is a function application of an overlapping sort,
//!   and fails otherwise: a function of the subject's root symbol and sort arguments (or its
//!   injection target, its domain-value sort, its collection definition), and of its being an
//!   `\and`, which the matcher splits first. The binding itself is read by no other pair (the
//!   variable occurs once, and an alias whose value could mention it is a region below) and by
//!   no later phase up to P11 (its definedness obligation is empty, and `requires` does not
//!   mention it);
//! - everywhere else (a collection, a domain value, a function or an alias in the pattern, a
//!   variable the rule reads, or a subject that does not decompose at a constructor of the
//!   pattern) the matcher reads the subject's subterm in full, including the normal-form marks it
//!   carries, so the memo compares that subterm by identity (the same allocation, which also
//!   holds the same marks, as a term's attributes are fixed when it is allocated).
//!
//! The pairs are processed in an order fixed by the left-hand side, and every decision on a pair
//! reads only what is listed for it and the bindings of variables the rule reads, which are
//! identical subterms; so two subjects that agree on these reads give the same match result and,
//! for a successful one, bindings equal on every variable `requires` mentions, hence the same
//! instantiated `requires` and the same simplification of it. A `False` obtained through the
//! solver is an `Unsat` answer for that same ground formula, which holds again. The one state a
//! matching problem carries between pairs besides its bindings, the normal-form evidence it
//! records for subject subterms (`SubjectNormalForms`), is keyed by term value and is a fact
//! about values: where it could differ between the two subjects it can only decide a pair the
//! other subject leaves undecided, never contradict the stored refutation, which is a fact about
//! the values the reads fix (the rule has no instance whose left-hand side is such a subject and
//! whose `requires` holds). For a well-sorted subject the variable reads above always agree (an
//! argument of a free constructor has the argument's sort); they are compared all the same.
//!
//! A rule whose left-hand side or `requires` mentions a symbol with an effect
//! (`deferred::is_impure_symbol`) is excluded: its outcome may depend on the state of the world.
//!
//! # Cost
//!
//! A slot holds the last refuted subject of its rule, a handle to a configuration that shares its
//! unchanged subterms with the current one. An attempt pays one lookup by rule; a rule with a
//! stored refutation pays a walk of its left-hand side's constructor skeleton that stops at the
//! first differing read; a refuted attempt stores one handle. A run whose rules never fail at
//! these exits stores nothing.

use std::{
    cell::Cell,
    collections::{BTreeMap, BTreeSet},
};

use rustc_hash::FxHashMap;

use crate::{
    deferred::is_impure_symbol,
    definition::BackendDefinition,
    diagnostic,
    fresh::FreshCounter,
    rule::RewriteRule,
    simplify::SimplificationOptions,
    smt::SmtSolver,
    stop::Stoppable,
    term::{HeadRole, Symbol, Term, TermKind, Variable, VariableKind},
    transition::ExecutionIoState,
};

use super::{
    Pattern, RuleAttempt,
    apply::{RefutationSite, apply_rule, apply_rule_reporting},
};

/// The last refuted subject of each rule of one execution ([module documentation](self)).
#[derive(Default)]
pub(crate) struct RefutationMemo {
    /// Keyed by the rule's address, fixed while the execution borrows the definition.
    rules: FxHashMap<usize, RuleSlot>,
}

struct RuleSlot {
    /// `None` for a rule the memo is not kept for.
    plan: Option<ReadPlan>,
    refuted: Option<Term>,
}

/// The variables whose bound values an attempt of the rule reads: those of `requires`, those
/// the left-hand side mentions more than once, and set variables, each compared by identity.
struct ReadPlan {
    read: BTreeSet<Variable>,
}

impl RefutationMemo {
    /// `apply_rule` of `rule` on `pattern` without assuming the subject defined, answered
    /// `NotApplicable` without an attempt when `memo` holds a refutation of the rule that read
    /// what this attempt would read, and storing this attempt's refutation when it is one the
    /// memo keeps: a `NotApplicable` at a recorded site ([`RefutationSite::Match`] or
    /// [`RefutationSite::Requires`]) with no diagnostic emitted and no path fact noted
    /// (`crate::path_facts`), so that skipping a later attempt drops no report and no mark.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn apply_rule(
        memo: Option<&mut Self>,
        definition: &BackendDefinition,
        rule: &RewriteRule,
        pattern: &Pattern,
        fresh_counter: &mut FreshCounter,
        simplification_options: SimplificationOptions,
        solver: &dyn SmtSolver,
        io: Option<&ExecutionIoState>,
        ground_halt: bool,
    ) -> Stoppable<RuleAttempt> {
        let Some(memo) = memo.filter(|_| Self::eligible(pattern)) else {
            return apply_rule(
                definition,
                rule,
                pattern,
                fresh_counter,
                simplification_options,
                solver,
                false,
                io,
                ground_halt,
            );
        };
        if memo.refutes(rule, &pattern.term) {
            return Ok(RuleAttempt::NotApplicable);
        }
        let site = Cell::new(RefutationSite::Other);
        let emitted = diagnostic::next_position();
        let noted = crate::path_facts::marker();
        let attempt = apply_rule_reporting(
            definition,
            rule,
            pattern,
            fresh_counter,
            simplification_options,
            solver,
            false,
            io,
            ground_halt,
            Some(&site),
        )?;
        if matches!(attempt, RuleAttempt::NotApplicable)
            && matches!(site.get(), RefutationSite::Match | RefutationSite::Requires)
            && diagnostic::next_position() == emitted
            // A refutation that read a value the definition leaves open is one model's: a
            // later attempt decides it again, and its path is marked again.
            && !crate::path_facts::noted_since(noted)
        {
            memo.record(definition, rule, &pattern.term);
        }
        Ok(attempt)
    }

    /// Whether the memo is kept for an attempt on `pattern`: ground, `ceil_free`, and without
    /// constraints.
    fn eligible(pattern: &Pattern) -> bool {
        pattern.constraints.is_empty()
            && pattern.term.attributes().variables.is_empty()
            && pattern.term.attributes().ceil_free()
    }

    /// Whether an attempt of `rule` on `subject`, an [eligible](Self::eligible) subject, reads
    /// what the rule's last stored refutation read, so that it is refuted again.
    fn refutes(&self, rule: &RewriteRule, subject: &Term) -> bool {
        let Some(RuleSlot {
            plan: Some(plan),
            refuted: Some(refuted),
        }) = self.rules.get(&key(rule))
        else {
            return false;
        };
        same_reads(&rule.lhs, refuted, subject, &plan.read)
    }

    /// Store that an attempt of `rule` on `subject`, an [eligible](Self::eligible) subject, was
    /// refuted at a recorded site, unless the rule is excluded.
    fn record(&mut self, definition: &BackendDefinition, rule: &RewriteRule, subject: &Term) {
        let slot = self.rules.entry(key(rule)).or_insert_with(|| RuleSlot {
            plan: ReadPlan::of(definition, rule),
            refuted: None,
        });
        if slot.plan.is_some() {
            slot.refuted = Some(subject.clone());
        }
    }
}

fn key(rule: &RewriteRule) -> usize {
    std::ptr::from_ref(rule) as usize
}

impl ReadPlan {
    /// The plan of `rule`, or `None` when it mentions a symbol with an effect.
    fn of(definition: &BackendDefinition, rule: &RewriteRule) -> Option<Self> {
        let mut terms = vec![rule.lhs.clone()];
        for predicate in rule.requires.iter() {
            predicate.visit_terms(&mut |term| terms.push(term.clone()));
        }
        let mut impure = false;
        for term in &terms {
            term.visit_symbols(&mut |symbol| impure |= is_impure_symbol(definition, symbol));
        }
        if impure {
            return None;
        }
        let mut occurrences = BTreeMap::new();
        count_variables(&rule.lhs, &mut occurrences);
        let mut read = occurrences
            .into_iter()
            .filter(|(variable, count)| *count > 1 || variable.kind != VariableKind::Element)
            .map(|(variable, _)| variable)
            .collect::<BTreeSet<_>>();
        // Every variable of `requires`, free or bound by a quantifier: a superset only makes
        // the comparison stricter.
        for term in &terms[1..] {
            read.extend(term.attributes().variables.iter().cloned());
        }
        Some(Self { read })
    }
}

fn count_variables(term: &Term, occurrences: &mut BTreeMap<Variable, usize>) {
    if let TermKind::Variable(variable) = term.kind() {
        *occurrences.entry(variable.clone()).or_default() += 1;
        return;
    }
    for child in crate::deferred::children(term) {
        count_variables(child, occurrences);
    }
}

/// Whether the matcher reads the same of `old` and `new` against `pattern`
/// ([module documentation](self)).
fn same_reads(pattern: &Term, old: &Term, new: &Term, read: &BTreeSet<Variable>) -> bool {
    if old.ptr_eq(new) {
        return true;
    }
    match pattern.kind() {
        TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } if symbol.attributes.head_role() == HeadRole::FreeConstructor => {
            // A subject that does not decompose is read whole, and the two differ.
            let decomposed =
                |subject| arguments_of(symbol, sort_arguments, arguments.len(), subject);
            let (Some(old), Some(new)) = (decomposed(old), decomposed(new)) else {
                return false;
            };
            arguments
                .iter()
                .zip(old.iter().zip(new))
                .all(|(pattern, (old, new))| same_reads(pattern, old, new, read))
        }
        TermKind::Injection {
            source,
            target,
            term,
        } => {
            let (Some(old), Some(new)) =
                (injected(source, target, old), injected(source, target, new))
            else {
                return false;
            };
            same_reads(term, old, new, read)
        }
        TermKind::Variable(variable) if !read.contains(variable) => same_root(old, new),
        _ => false,
    }
}

/// The arguments of `subject` when it is an application of `symbol` with `sort_arguments` and
/// `arity` arguments.
fn arguments_of<'t>(
    symbol: &std::sync::Arc<Symbol>,
    sort_arguments: &[crate::term::Sort],
    arity: usize,
    subject: &'t Term,
) -> Option<&'t [Term]> {
    match subject.kind() {
        TermKind::Application {
            symbol: subject_symbol,
            sort_arguments: subject_sorts,
            arguments,
        } if same_symbol(symbol, subject_symbol)
            && subject_sorts.as_slice() == sort_arguments
            && arguments.len() == arity =>
        {
            Some(arguments)
        }
        _ => None,
    }
}

/// The injected term of `subject` when it is an injection from `source` to `target`.
fn injected<'t>(
    source: &crate::term::Sort,
    target: &crate::term::Sort,
    subject: &'t Term,
) -> Option<&'t Term> {
    match subject.kind() {
        TermKind::Injection {
            source: subject_source,
            target: subject_target,
            term,
        } if subject_source == source && subject_target == target => Some(term),
        _ => None,
    }
}

fn same_symbol(left: &std::sync::Arc<Symbol>, right: &std::sync::Arc<Symbol>) -> bool {
    std::sync::Arc::ptr_eq(left, right) || left == right
}

/// Whether `old` and `new` have one root as an unread variable's pair reads it: neither an
/// `\and`, and the same symbol and sort arguments, injection target, domain-value sort, or
/// collection definition, which fix the sort and whether the root is a function application.
fn same_root(old: &Term, new: &Term) -> bool {
    match (old.kind(), new.kind()) {
        (
            TermKind::Application {
                symbol: old_symbol,
                sort_arguments: old_sorts,
                ..
            },
            TermKind::Application {
                symbol: new_symbol,
                sort_arguments: new_sorts,
                ..
            },
        ) => same_symbol(old_symbol, new_symbol) && old_sorts == new_sorts,
        (
            TermKind::Injection {
                target: old_target, ..
            },
            TermKind::Injection {
                target: new_target, ..
            },
        ) => old_target == new_target,
        (
            TermKind::DomainValue { sort: old_sort, .. },
            TermKind::DomainValue { sort: new_sort, .. },
        ) => old_sort == new_sort,
        (
            TermKind::Map {
                definition: old_definition,
                ..
            },
            TermKind::Map {
                definition: new_definition,
                ..
            },
        ) => old_definition == new_definition,
        (
            TermKind::List {
                definition: old_definition,
                ..
            },
            TermKind::List {
                definition: new_definition,
                ..
            },
        ) => old_definition == new_definition,
        (
            TermKind::Set {
                definition: old_definition,
                ..
            },
            TermKind::Set {
                definition: new_definition,
                ..
            },
        ) => old_definition == new_definition,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;
    use crate::{fresh::RequestNames, smt::NoSolver};

    /// Rules over a three-cell configuration `cfg(head, count, other)`: one refuted at its match
    /// (`at-a`), one whose `requires` reads two cells (`below`), one whose `requires` reads one
    /// cell and leaves another unread (`positive`), one with a variable twice (`same`), one that
    /// reads the unread cell's contents through a constructor (`other-c`), and one whose
    /// `requires` calls an impure function (`impure`).
    const DEFINITION: &str = r#"[]
module MAIN
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
    sort SortItem{} []
    sort SortS{} []
    hooked-symbol ltInt{}(SortInt{}, SortInt{}) : SortBool{}
        [function{}(), total{}(), hook{}("INT.lt"), smt-hook{}("<")]
    hooked-symbol effect{}(SortInt{}) : SortBool{}
        [function{}(), total{}(), impure{}(), hook{}("TEST.unimplemented")]
    symbol cfg{}(SortItem{}, SortInt{}, SortItem{}) : SortS{} [constructor{}()]
    symbol a{}() : SortItem{} [constructor{}()]
    symbol b{}() : SortItem{} [constructor{}()]
    symbol c{}(SortInt{}) : SortItem{} [constructor{}()]
    symbol done{}() : SortS{} [constructor{}()]
    axiom{} \rewrites{SortS{}}(
        \and{SortS{}}(cfg{}(a{}(), M:SortInt{}, X:SortItem{}), \top{SortS{}}()),
        done{}()
    ) [label{}("at-a")]
    axiom{} \rewrites{SortS{}}(
        \and{SortS{}}(
            cfg{}(c{}(N:SortInt{}), M:SortInt{}, X:SortItem{}),
            \equals{SortBool{}, SortS{}}(ltInt{}(N:SortInt{}, M:SortInt{}), \dv{SortBool{}}("true"))
        ),
        done{}()
    ) [label{}("below")]
    axiom{} \rewrites{SortS{}}(
        \and{SortS{}}(
            cfg{}(c{}(N:SortInt{}), M:SortInt{}, X:SortItem{}),
            \equals{SortBool{}, SortS{}}(ltInt{}(\dv{SortInt{}}("1"), N:SortInt{}), \dv{SortBool{}}("true"))
        ),
        done{}()
    ) [label{}("positive")]
    axiom{} \rewrites{SortS{}}(
        \and{SortS{}}(cfg{}(X:SortItem{}, M:SortInt{}, X:SortItem{}), \top{SortS{}}()),
        done{}()
    ) [label{}("same")]
    axiom{} \rewrites{SortS{}}(
        \and{SortS{}}(cfg{}(H:SortItem{}, M:SortInt{}, c{}(\dv{SortInt{}}("2"))), \top{SortS{}}()),
        done{}()
    ) [label{}("other-c")]
    axiom{} \rewrites{SortS{}}(
        \and{SortS{}}(
            cfg{}(c{}(N:SortInt{}), M:SortInt{}, X:SortItem{}),
            \equals{SortBool{}, SortS{}}(effect{}(N:SortInt{}), \dv{SortBool{}}("true"))
        ),
        done{}()
    ) [label{}("impure")]
endmodule []"#;

    fn term(definition: &BackendDefinition, source: &str) -> Term {
        definition
            .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
            .expect("term should internalize")
    }

    fn rule<'d>(definition: &'d BackendDefinition, label: &str) -> &'d RewriteRule {
        definition
            .rewrite_theory()
            .values()
            .flat_map(|groups| groups.values())
            .flatten()
            .map(|stored| &stored.rule)
            .find(|rule| rule.attributes.label.as_deref() == Some(label))
            .expect("the rule is indexed")
    }

    fn fresh_attempt(
        definition: &BackendDefinition,
        rule: &RewriteRule,
        pattern: &Pattern,
    ) -> bool {
        let mut fresh = FreshCounter::for_request_names(RequestNames::of(&[pattern]));
        matches!(
            apply_rule(
                definition,
                rule,
                pattern,
                &mut fresh,
                SimplificationOptions::default(),
                &NoSolver,
                false,
                None,
                true,
            ),
            Ok(RuleAttempt::NotApplicable)
        )
    }

    /// Over every pair of configurations built from shared cell values, as an execution's
    /// successive configurations share their unchanged cells: after an attempt refuted on the
    /// first is stored, the memo answers for the second only where a fresh attempt on the second
    /// is refuted too. The memo must also answer for some pairs of distinct configurations, both
    /// for refutations at the match and at `requires`, and never for the rule whose `requires`
    /// has an effect.
    #[test]
    fn a_stored_refutation_answers_only_where_a_fresh_attempt_is_refuted() {
        let syntax = parse_definition(DEFINITION).expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let _apart = crate::rule::ApartScope::enter();
        let _domain = crate::term::domain::DomainScope::enter(&definition);
        let _hook_values = crate::deferred::HookValueScope::enter(&definition);
        let integers = (0..4)
            .map(|value| term(&definition, &format!(r#"\dv{{SortInt{{}}}}("{value}")"#)))
            .collect::<Vec<_>>();
        let mut items = vec![term(&definition, "a{}()"), term(&definition, "b{}()")];
        for value in 0..4 {
            items.push(term(
                &definition,
                &format!(r#"c{{}}(\dv{{SortInt{{}}}}("{value}"))"#),
            ));
        }
        let TermKind::Application { symbol, .. } =
            term(&definition, r#"cfg{}(a{}(), \dv{SortInt{}}("0"), a{}())"#)
                .kind()
                .clone()
        else {
            panic!("cfg is an application");
        };
        let mut subjects = Vec::new();
        for head in &items {
            for count in &integers {
                for other in &items {
                    subjects.push(Pattern {
                        term: Term::application(
                            symbol.clone(),
                            Vec::new(),
                            vec![head.clone(), count.clone(), other.clone()],
                        ),
                        constraints: Vec::new(),
                    });
                }
            }
        }
        for label in ["at-a", "below", "positive", "same", "other-c", "impure"] {
            let rule = rule(&definition, label);
            let refuted = subjects
                .iter()
                .map(|subject| fresh_attempt(&definition, rule, subject))
                .collect::<Vec<_>>();
            let mut answered_for_another = 0;
            for (first, stored) in subjects.iter().enumerate() {
                let mut memo = RefutationMemo::default();
                let mut fresh = FreshCounter::for_request_names(RequestNames::of(&[stored]));
                let attempt = RefutationMemo::apply_rule(
                    Some(&mut memo),
                    &definition,
                    rule,
                    stored,
                    &mut fresh,
                    SimplificationOptions::default(),
                    &NoSolver,
                    None,
                    true,
                )
                .expect("no stop");
                assert_eq!(
                    matches!(attempt, RuleAttempt::NotApplicable),
                    refuted[first],
                    "{label}: the memo's own attempt is the fresh one"
                );
                for (second, subject) in subjects.iter().enumerate() {
                    if memo.refutes(rule, &subject.term) {
                        assert!(
                            refuted[second],
                            "{label}: a refutation of {:?} answered for {:?}, which the rule does not refute",
                            stored.term, subject.term
                        );
                        answered_for_another += usize::from(first != second);
                    }
                }
            }
            if label == "impure" {
                assert_eq!(answered_for_another, 0, "{label}: excluded");
            } else {
                assert!(
                    answered_for_another > 0,
                    "{label}: the memo answered for no other configuration"
                );
            }
        }
    }

    /// A subject with a variable or a constraint is attempted without the memo, and a
    /// refutation on it is not stored.
    #[test]
    fn a_symbolic_or_constrained_subject_is_not_remembered() {
        let syntax = parse_definition(DEFINITION).expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let _apart = crate::rule::ApartScope::enter();
        let _domain = crate::term::domain::DomainScope::enter(&definition);
        let _hook_values = crate::deferred::HookValueScope::enter(&definition);
        let rule = rule(&definition, "at-a");
        let symbolic = Pattern {
            term: term(&definition, r#"cfg{}(b{}(), Y:SortInt{}, a{}())"#),
            constraints: Vec::new(),
        };
        let ground = term(&definition, r#"cfg{}(b{}(), \dv{SortInt{}}("0"), a{}())"#);
        let constrained = Pattern {
            term: ground.clone(),
            constraints: vec![crate::rule::Predicate::Equals(
                term(&definition, r#"\dv{SortInt{}}("0")"#),
                term(&definition, r#"\dv{SortInt{}}("0")"#),
            )],
        };
        for pattern in [&symbolic, &constrained] {
            let mut memo = RefutationMemo::default();
            let mut fresh = FreshCounter::for_request_names(RequestNames::of(&[pattern]));
            let attempt = RefutationMemo::apply_rule(
                Some(&mut memo),
                &definition,
                rule,
                pattern,
                &mut fresh,
                SimplificationOptions::default(),
                &NoSolver,
                None,
                true,
            )
            .expect("no stop");
            assert!(matches!(attempt, RuleAttempt::NotApplicable));
            assert!(memo.rules.is_empty(), "{:?}", pattern.term);
            assert!(!memo.refutes(rule, &ground));
        }
    }
}
