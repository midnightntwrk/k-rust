//! Instance normality: whether every instance of a term is a normal form of the equations.
//!
//! A production with `anywhere` equations (an anywhere rule or an overload equation) is not a
//! free constructor. Its equations may identify two of its applications with different
//! arguments: `wrap(s(z)) = wrap(z)` makes `wrap(s(X))` and `wrap(z)` equal for `X = z`. Such an
//! application denotes the value of its normal form under the equations, and the evaluator
//! treats that normal form as a constructor value: distinct normal forms are distinct values.
//! So the arguments of an anywhere head may be compared, and two different arguments may refute
//! an equality, only when the application is known to be a normal form for every valuation of
//! its variables, not merely for the valuation at hand.
//!
//! [`BackendDefinition::instance_normal`] decides that sufficient condition. A term is
//! instance-normal when every ground instance of it (each variable replaced by a normal-form
//! value of its sort) is a normal form:
//!
//! - a domain value or a variable is instance-normal, since a variable ranges over values;
//! - a constructor application or a sort injection is instance-normal when its arguments are:
//!   no equation is headed by a constructor or an injection, so it is normal when its parts are;
//! - an application of an `anywhere` symbol that is not a declared function is instance-normal
//!   when its arguments are and every equation the evaluator may apply to it (headed by that
//!   symbol or by a bare variable, of any priority, `requires` ignored) either does not
//!   syntactically unify with it or is refuted on it by equation matching. An equation applies
//!   to an instance only if the instance matches the equation's left-hand side, an instance
//!   matches only if the two terms unify, and a refutation by equation matching holds for every
//!   instance; ignoring `requires` only makes the test report more applications as possibly
//!   rewritten;
//! - a map, list or set term is instance-normal when its elements (keys, values, and the rest)
//!   are and no equation offered its collection index or a bare variable applies to it, as
//!   above: the collection axioms only identify representations of one collection value, which
//!   the matcher's collection matching compares as such, and equations over collection
//!   functions are headed by those functions, not by the collection term;
//! - a declared-function application, any other non-constructor application, and a conjunction
//!   are not instance-normal: their value is whatever their equations make it, so their shape
//!   does not determine their value.
//!
//! The equations scanned for an `anywhere` application or a collection are those equation
//! selection offers it, so the scan answers for every equation of the definition only when
//! selection reaches every term equation that could match an application
//! (`BackendDefinition::equation_selection_complete`). In a definition where it does not (a
//! simplification whose left-hand side is an `\and` of term patterns, filed apart), no
//! `anywhere` application and no collection is instance-normal.
//!
//! [`BackendDefinition::instance_normal`] scans ground terms too. That
//! [`Term::concrete_after_normalization`] holds is a syntactic fact (ground, every head a
//! constructor or an anywhere non-function production), not evidence that no equation applies:
//! the ground `wrap(s(z))` has it and is not a normal form. The answer is an [`InstanceNormal`]
//! token (`token.rs`). This module obtains one only from `InstanceNormal::decide`, which reads
//! the shape of the term it answers for itself and asks this module only for the answers about
//! the term's immediate subterms and for the test that excludes one candidate equation; for an
//! `anywhere` application or a collection it answers only through a scan that enumerates the
//! candidate equations itself, so no path can vouch for such a term without the scan.
//!
//! The syntactic unifiability test asks whether some instance of the subject could match the
//! equation's pattern, not whether two values are equal, so it decomposes every equal-name
//! application purely syntactically and does not recurse into instance normality. It reads the
//! roots through the rigidity classifier (`term::head`): the equation's left-hand side up to
//! equations, the subject as the values it denotes. It treats a pair as possibly unifiable
//! whenever its shape does not settle the question (a function or collection head, differing
//! injection sources, a sort mismatch it cannot interpret), so an answer of "does not unify" is
//! always a proof that no instance matches.

mod token;

use std::{cell::RefCell, collections::HashMap};

use rustc_hash::FxHashMap;

pub(crate) use token::{InstanceNormal, NormalArguments};

use crate::{
    definition::BackendDefinition,
    matching::{MatchMode, MatchResult, SortGraph, match_terms_in_definition},
    rule::RewriteRule,
    term::{
        Sort, Term, TermKind, Variable,
        head::{
            Fixed, FixedRoot, Head, InheritedFromArguments, PatternReading, RootComparison,
            classify_pattern, classify_value, compare_roots,
        },
    },
};

impl BackendDefinition {
    /// Whether every instance of `term` is a normal form of this definition's equations; see
    /// the [module documentation](self) for the definition and why it is sound to decompose or
    /// refute an `anywhere` head only on applications for which this holds. Makes no
    /// assumption about how `term` was produced.
    #[must_use]
    pub(crate) fn instance_normal(&self, term: &Term) -> Option<InstanceNormal> {
        let _scope = ScanScope::enter();
        self.instance_normal_memoized(term)
    }

    fn instance_normal_memoized(&self, term: &Term) -> Option<InstanceNormal> {
        if let Some(known) = ScanScope::known(term) {
            return known;
        }
        let normal = self.instance_normal_uncached(term);
        ScanScope::record(term, normal);
        normal
    }

    /// `InstanceNormal::decide` reads the shape of `term`; this module supplies the answers
    /// for its subterms, through the call's memo, and the exclusion test.
    fn instance_normal_uncached(&self, term: &Term) -> Option<InstanceNormal> {
        InstanceNormal::decide(
            self,
            term,
            |subterm| self.instance_normal_memoized(subterm),
            |rule, arguments| self.excluded(rule, arguments),
        )
    }

    /// Whether the equation `rule`, which equation selection offers an application headed like
    /// the scanned subject (`NoEquationReaches::scan` enumerates the candidates), cannot apply
    /// to any instance of that subject. It is excluded when its left-hand side does not
    /// syntactically unify with the subject, or when equation matching, which decides for the
    /// evaluator whether an equation applies to a term, fails on the subject: a failure holds
    /// for every instance of the subject (`matching::match_terms_in_definition`). The second
    /// test knows what the first does not: the sorts of injections and the productions of an
    /// overload family.
    fn excluded(&self, rule: &RewriteRule, arguments: NormalArguments<'_>) -> bool {
        !may_unify(self.sort_graph(), &rule.lhs, arguments)
            || self.matching_refutes(&rule.lhs, arguments.subject())
    }

    /// Whether equation matching refutes the left-hand side `pattern` on `subject`. Matching
    /// needs the two sides' variables apart; renaming the equation would take names from the
    /// request's counter, so a pair that shares a name is not asked.
    fn matching_refutes(&self, pattern: &Term, subject: &Term) -> bool {
        pattern
            .attributes()
            .variables
            .is_disjoint(&subject.attributes().variables)
            && matches!(
                match_terms_in_definition(MatchMode::Evaluate, self, pattern, subject),
                MatchResult::Failed(_)
            )
    }
}

thread_local! {
    /// The instance normality of the terms decided during the outermost
    /// [`BackendDefinition::instance_normal`] call on this thread, if one is open. Equation
    /// matching inside the scan asks about the subterms of the scanned term again; the answer
    /// is a function of the term and the definition, so it is kept for the call.
    static SCAN: RefCell<(usize, FxHashMap<Term, Option<InstanceNormal>>)> =
        RefCell::new((0, FxHashMap::default()));
}

/// One outermost [`BackendDefinition::instance_normal`] call; nested calls share its memo.
struct ScanScope(());

impl ScanScope {
    fn enter() -> Self {
        SCAN.with(|scan| scan.borrow_mut().0 += 1);
        Self(())
    }

    fn known(term: &Term) -> Option<Option<InstanceNormal>> {
        SCAN.with(|scan| scan.borrow().1.get(term).copied())
    }

    fn record(term: &Term, normal: Option<InstanceNormal>) {
        SCAN.with(|scan| {
            scan.borrow_mut().1.insert(term.clone(), normal);
        });
    }
}

impl Drop for ScanScope {
    fn drop(&mut self) {
        SCAN.with(|scan| {
            let mut scan = scan.borrow_mut();
            scan.0 -= 1;
            if scan.0 == 0 {
                scan.1.clear();
            }
        });
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Side {
    /// The equation's left-hand side.
    Pattern,
    /// The instance-normal subject application and its arguments.
    Subject,
}

/// A subterm together with the side it comes from: the two sides' variables are distinct even
/// when their names coincide, which renames the equation apart without rebuilding it.
type Sided<'a> = (Side, &'a Term);

/// Whether the equation pattern `pattern` and the scanned subject have a common syntactic
/// instance, as far as their shape decides it; `false` is a proof that none exists.
///
/// The subject is the one `arguments` names, and the precondition it carries is that the
/// subject's immediate subterms are instance-normal: a subject subterm headed by an `anywhere`
/// production denotes a value with that head, and the subject's own root is the root the
/// equation is tried on (`InheritedFromArguments`).
fn may_unify<'a>(sorts: &'a SortGraph, pattern: &'a Term, arguments: NormalArguments<'a>) -> bool {
    let subject = arguments.subject();
    if let TermKind::Variable(variable) = pattern.kind()
        && sorts_differ(&variable.sort, &subject.sort())
    {
        return false;
    }
    SyntacticUnifier {
        sorts,
        subject_values: InheritedFromArguments(arguments),
        bindings: HashMap::new(),
        pending: Vec::new(),
    }
    .run((Side::Pattern, pattern), (Side::Subject, subject))
}

struct SyntacticUnifier<'a> {
    sorts: &'a SortGraph,
    /// The oracle that fixes the subject side's equation-head roots.
    subject_values: InheritedFromArguments<'a>,
    bindings: HashMap<(Side, &'a Variable), Sided<'a>>,
    pending: Vec<(Sided<'a>, Sided<'a>)>,
}

impl<'a> SyntacticUnifier<'a> {
    fn run(mut self, left: Sided<'a>, right: Sided<'a>) -> bool {
        self.pending.push((left, right));
        while let Some((left, right)) = self.pending.pop() {
            if !self.unify_one(self.resolve(left), self.resolve(right)) {
                return false;
            }
        }
        true
    }

    /// Follow variable bindings until an unbound variable or a non-variable term.
    fn resolve(&self, mut term: Sided<'a>) -> Sided<'a> {
        while let TermKind::Variable(variable) = term.1.kind()
            && let Some(bound) = self.bindings.get(&(term.0, variable))
        {
            term = *bound;
        }
        term
    }

    /// Whether the variable `(side, variable)` occurs in `term` under the current bindings.
    /// Bindings are only added when this is false, so the bindings never form a cycle and the
    /// walk terminates.
    fn occurs(&self, side: Side, variable: &Variable, (term_side, term): Sided<'a>) -> bool {
        term.attributes().variables.iter().any(|other| {
            (term_side == side && other == variable)
                || self
                    .bindings
                    .get(&(term_side, other))
                    .is_some_and(|bound| self.occurs(side, variable, *bound))
        })
    }

    /// Unify one resolved pair; `false` only when the pair has no common instance. A pair whose
    /// shape does not decide the question is dropped, which keeps the answer an
    /// over-approximation of unifiability.
    ///
    /// The lint below covers a match on a single enum written here; it does not see the
    /// wildcard fallback arm of the `(TermKind, TermKind)` match, whose scrutinee is a tuple,
    /// and that arm is intentionally outside it. The match dispatches on structure only: every
    /// root decision in it is taken by `fixed`, `compared_by_root` and `separated`, which match
    /// one enum each under the same lint.
    #[deny(clippy::wildcard_enum_match_arm)]
    fn unify_one(&mut self, left: Sided<'a>, right: Sided<'a>) -> bool {
        if left.0 == right.0 && left.1 == right.1 {
            return true;
        }
        if let TermKind::Variable(variable) = left.1.kind() {
            return self.bind(left.0, variable, right);
        }
        if let TermKind::Variable(variable) = right.1.kind() {
            return self.bind(right.0, variable, left);
        }
        match (left.1.kind(), right.1.kind()) {
            (TermKind::And(first, second), _) => {
                self.pending.push(((left.0, first), right));
                self.pending.push(((left.0, second), right));
                true
            }
            (_, TermKind::And(first, second)) => {
                self.pending.push((left, (right.0, first)));
                self.pending.push((left, (right.0, second)));
                true
            }
            (
                TermKind::DomainValue {
                    sort: left_sort,
                    value: left_value,
                },
                TermKind::DomainValue {
                    sort: right_sort,
                    value: right_value,
                },
            ) => left_sort != right_sort || left_value == right_value,
            (
                TermKind::Application {
                    symbol: left_symbol,
                    sort_arguments: left_sorts,
                    arguments: left_arguments,
                },
                TermKind::Application {
                    symbol: right_symbol,
                    sort_arguments: right_sorts,
                    arguments: right_arguments,
                },
            ) if left_symbol.name == right_symbol.name => {
                if left_arguments.len() != right_arguments.len()
                    || left_sorts
                        .iter()
                        .zip(right_sorts)
                        .any(|(left, right)| sorts_differ(left, right))
                {
                    return false;
                }
                self.pending
                    .extend(left_arguments.iter().zip(right_arguments).map(
                        |(left_argument, right_argument)| {
                            ((left.0, left_argument), (right.0, right_argument))
                        },
                    ));
                true
            }
            (
                TermKind::Injection {
                    source: left_source,
                    target: left_target,
                    term: left_term,
                },
                TermKind::Injection {
                    source: right_source,
                    target: right_target,
                    term: right_term,
                },
            ) if left_source == right_source && left_target == right_target => {
                self.pending
                    .push(((left.0, left_term), (right.0, right_term)));
                true
            }
            // Two injections into one sort from different sorts denote a common value only
            // through a value of both source sorts, that is of a common subsort.
            (
                TermKind::Injection {
                    source: left_source,
                    target: left_target,
                    ..
                },
                TermKind::Injection {
                    source: right_source,
                    target: right_target,
                    ..
                },
            ) => {
                left_target != right_target
                    || self.sorts.known_overlap(left_source, right_source) != Some(false)
            }
            // An injection denotes a value of its source sort, which no application with a
            // fixed root denotes: a free-constructor application is not an injection, and
            // neither is an equation-head application on the subject side, whose root is fixed
            // by the precondition of `may_unify`.
            (TermKind::Injection { .. }, TermKind::Application { .. })
            | (TermKind::Application { .. }, TermKind::Injection { .. }) => !self
                .fixed(left)
                .zip(self.fixed(right))
                .is_some_and(|(left, right)| separated(compare_roots(left, right))),
            // Two different fixed roots have no common instance. This test separates an
            // injection only from an application (the arm above) and a collection from no root:
            // answering "may unify" is always sound here, and equation matching, the scan's
            // second test, compares those pairs with the sort graph and the collection axioms.
            _ => !self
                .fixed(left)
                .zip(self.fixed(right))
                .is_some_and(|(left, right)| {
                    compared_by_root(left)
                        && compared_by_root(right)
                        && separated(compare_roots(left, right))
                }),
        }
    }

    /// The root of one side, when fixed: the equation's left-hand side is read up to equations,
    /// so its equation-head roots are open; the subject is read as the values it denotes.
    #[deny(clippy::wildcard_enum_match_arm)]
    fn fixed(&mut self, (side, term): Sided<'a>) -> Option<Fixed<'a>> {
        let head = match side {
            Side::Pattern => classify_pattern(PatternReading::UpToEquations, term),
            Side::Subject => classify_value(term, &mut self.subject_values),
        };
        match head {
            Head::Fixed(fixed) => Some(fixed),
            Head::Open(_) | Head::Residual => None,
        }
    }

    fn bind(&mut self, side: Side, variable: &'a Variable, term: Sided<'a>) -> bool {
        if let TermKind::Variable(other) = term.1.kind()
            && term.0 == side
            && other == variable
        {
            return true;
        }
        // A cyclic binding has no finite syntactic solution, but a function or collection
        // head on the cycle may still denote it; stop and answer "may unify".
        if self.occurs(side, variable, term) {
            self.pending.clear();
            return true;
        }
        self.bindings.insert((side, variable), term);
        true
    }
}

/// Whether this test separates a fixed root from another fixed root by root alone. An injection
/// is separated only from an application, in the arm written for that pair, and a collection
/// from no root.
#[deny(clippy::wildcard_enum_match_arm)]
fn compared_by_root(fixed: Fixed<'_>) -> bool {
    match fixed.root() {
        FixedRoot::DomainValue | FixedRoot::FreeConstructor | FixedRoot::EquationHead(_) => true,
        FixedRoot::Injection | FixedRoot::Collection(_) => false,
    }
}

/// Whether two fixed roots, compared by root, have no common instance.
#[deny(clippy::wildcard_enum_match_arm)]
fn separated(comparison: RootComparison<'_>) -> bool {
    match comparison {
        RootComparison::Distinct(_) => true,
        // Equal names, two domain values and two injections have arms of their own in
        // `unify_one`; the root alone separates none of these pairs.
        RootComparison::SameApplication(_)
        | RootComparison::ArityMismatch
        | RootComparison::DomainValues
        | RootComparison::Injections
        | RootComparison::Collections(_) => false,
    }
}

/// Whether two sorts are certainly different: both are free of sort variables and unequal.
fn sorts_differ(left: &Sort, right: &Sort) -> bool {
    left != right && !has_sort_variable(left) && !has_sort_variable(right)
}

fn has_sort_variable(sort: &Sort) -> bool {
    match sort {
        Sort::Variable(_) => true,
        Sort::Application { arguments, .. } => arguments.iter().any(has_sort_variable),
    }
}

#[cfg(test)]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;
    use crate::term::HeadRole;

    /// `wrap` has the equation `wrap(s(z)) = wrap(z)`; `twin` the non-linear `twin(X, X) =
    /// wrap(z)`; `any` the unconditional `any(X) = wrap(z)`; `f` is a declared function.
    fn definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortNat{} []
                sort SortAddress{} []
                symbol z{}() : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol s{}(SortNat{}) : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol f{}(SortNat{}) : SortNat{} [function{}(), total{}(), no-evaluators{}()]
                symbol wrap{}(SortNat{}) : SortAddress{}
                    [anywhere{}(), functional{}(), injective{}()]
                symbol twin{}(SortNat{}, SortNat{}) : SortAddress{}
                    [anywhere{}(), functional{}(), injective{}()]
                symbol any{}(SortNat{}) : SortAddress{}
                    [anywhere{}(), functional{}(), injective{}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \top{R}(),
                        \and{R}(\in{SortNat{}, R}(X0:SortNat{}, s{}(z{}())), \top{R}())
                    ),
                    \equals{SortAddress{}, R}(
                        wrap{}(X0:SortNat{}),
                        \and{SortAddress{}}(wrap{}(z{}()), \top{SortAddress{}}())
                    )
                ) [anywhere{}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \top{R}(),
                        \and{R}(
                            \in{SortNat{}, R}(X0:SortNat{}, X:SortNat{}),
                            \and{R}(\in{SortNat{}, R}(X1:SortNat{}, X:SortNat{}), \top{R}())
                        )
                    ),
                    \equals{SortAddress{}, R}(
                        twin{}(X0:SortNat{}, X1:SortNat{}),
                        \and{SortAddress{}}(wrap{}(z{}()), \top{SortAddress{}}())
                    )
                ) [anywhere{}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \top{R}(),
                        \and{R}(\in{SortNat{}, R}(X0:SortNat{}, X:SortNat{}), \top{R}())
                    ),
                    \equals{SortAddress{}, R}(
                        any{}(X0:SortNat{}),
                        \and{SortAddress{}}(wrap{}(z{}()), \top{SortAddress{}}())
                    )
                ) [anywhere{}(), owise{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    fn normal(definition: &BackendDefinition, source: &str) -> bool {
        let term = definition
            .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
            .expect("term should internalize");
        definition.instance_normal(&term).is_some()
    }

    /// 5104f81b: the ground `wrap(s(z))` is concrete after normalization but not a normal form,
    /// so ground terms are scanned like any other.
    #[test]
    fn ground_terms_are_scanned_whatever_their_shape() {
        let definition = definition();
        let term = |source: &str| {
            definition
                .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
                .expect("term should internalize")
        };
        let redex = term("wrap{}(s{}(z{}()))");
        assert!(redex.concrete_after_normalization());
        assert_eq!(definition.instance_normal(&redex), None);
        let normal = definition.instance_normal(&term("wrap{}(s{}(s{}(z{}())))"));
        assert!(normal.is_some());
        // Its subterm `s(s(z))` inherits the token.
        assert_eq!(
            normal.map(InstanceNormal::argument),
            definition.instance_normal(&term("s{}(s{}(z{}()))"))
        );
        assert_eq!(definition.instance_normal(&term("any{}(z{}())")), None);
    }

    /// ece6117d, B4: a simplification whose left-hand side is an `\and` of term patterns is filed
    /// in the predicate theory, which equation selection never offers an application; here
    /// `\and(tag(s(X)), tag(s(X))) = tag(X)` rewrites `tag(s(z))`, which no offered equation
    /// reaches. With selection incomplete no equation head and no collection is instance-normal;
    /// without the axiom `tag(s(z))` is.
    #[test]
    fn an_equation_selection_does_not_offer_leaves_no_equation_head_instance_normal() {
        let source = |lemma: &str| {
            format!(
                r#"[]
            module MAIN
                sort SortNat{{}} []
                sort SortAddress{{}} []
                hooked-sort SortMap{{}}
                    [hook{{}}("MAP.Map"), unit{{}}(mapUnit{{}}()), element{{}}(mapItem{{}}()), concat{{}}(mapConcat{{}}())]
                symbol z{{}}() : SortNat{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                symbol s{{}}(SortNat{{}}) : SortNat{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                symbol tag{{}}(SortNat{{}}) : SortAddress{{}} [anywhere{{}}(), functional{{}}()]
                hooked-symbol mapUnit{{}}() : SortMap{{}} [function{{}}(), total{{}}(), hook{{}}("MAP.unit")]
                hooked-symbol mapItem{{}}(SortNat{{}}, SortNat{{}}) : SortMap{{}}
                    [function{{}}(), total{{}}(), hook{{}}("MAP.element")]
                hooked-symbol mapConcat{{}}(SortMap{{}}, SortMap{{}}) : SortMap{{}}
                    [function{{}}(), hook{{}}("MAP.concat"), assoc{{}}(), comm{{}}()]
                {lemma}
            endmodule []"#
            )
        };
        let lemma = r#"axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortAddress{}, R}(
                        \and{SortAddress{}}(tag{}(s{}(X:SortNat{})), tag{}(s{}(X:SortNat{}))),
                        \and{SortAddress{}}(tag{}(X:SortNat{}), \top{SortAddress{}}())
                    )
                ) [simplification{}()]"#;
        let internalize = |source: String| {
            let syntax = parse_definition(&source).expect("definition should parse");
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
        };
        let incomplete = internalize(source(lemma));
        assert!(incomplete.equation_selection_complete().is_none());
        assert!(!normal(&incomplete, "tag{}(s{}(z{}()))"));
        assert!(!normal(&incomplete, "mapItem{}(z{}(), z{}())"));
        assert!(normal(&incomplete, "s{}(z{}())"));
        let complete = internalize(source(""));
        assert!(complete.equation_selection_complete().is_some());
        assert!(normal(&complete, "tag{}(s{}(z{}()))"));
        assert!(normal(&complete, "mapItem{}(z{}(), z{}())"));
    }

    #[test]
    fn values_variables_and_constructors_over_them_are_instance_normal() {
        let definition = definition();
        assert!(normal(&definition, "X:SortNat{}"));
        assert!(normal(&definition, "s{}(s{}(X:SortNat{}))"));
        assert!(!normal(&definition, "s{}(f{}(X:SortNat{}))"));
        assert!(!normal(&definition, "f{}(z{}())"));
    }

    #[test]
    fn an_anywhere_application_is_normal_when_no_equation_unifies_with_it() {
        let definition = definition();
        assert!(!normal(&definition, "wrap{}(s{}(X:SortNat{}))"));
        assert!(!normal(&definition, "wrap{}(X:SortNat{})"));
        assert!(normal(&definition, "wrap{}(s{}(s{}(X:SortNat{})))"));
        assert!(normal(&definition, "wrap{}(z{}())"));
        assert!(!normal(&definition, "wrap{}(f{}(X:SortNat{}))"));
    }

    /// The equation variables are renamed apart from the subject's, and a non-linear pattern
    /// binds consistently: `twin(z, s(Y))` has no instance with equal arguments.
    #[test]
    fn non_linear_patterns_bind_consistently_and_apart_from_the_subject() {
        let definition = definition();
        assert!(normal(&definition, "twin{}(z{}(), s{}(Y:SortNat{}))"));
        assert!(!normal(&definition, "twin{}(Y:SortNat{}, z{}())"));
        assert!(!normal(&definition, "twin{}(X:SortNat{}, X:SortNat{})"));
    }

    /// A collection argument is a value when its elements are: an anywhere application over a
    /// map stays instance-normal, and a function element in the map does not.
    #[test]
    fn collections_are_instance_normal_when_their_elements_are() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortNat{} []
                sort SortBox{} []
                hooked-sort SortMap{}
                    [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
                symbol z{}() : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol f{}(SortNat{}) : SortNat{} [function{}(), total{}(), no-evaluators{}()]
                symbol box{}(SortMap{}) : SortBox{} [anywhere{}(), functional{}(), injective{}()]
                hooked-symbol mapUnit{}() : SortMap{} [function{}(), total{}(), hook{}("MAP.unit")]
                hooked-symbol mapItem{}(SortNat{}, SortNat{}) : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.element")]
                hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{}
                    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        assert!(normal(&definition, "box{}(mapItem{}(z{}(), z{}()))"));
        assert!(normal(
            &definition,
            "box{}(mapConcat{}(mapItem{}(z{}(), z{}()), M:SortMap{}))"
        ));
        assert!(!normal(&definition, "box{}(mapItem{}(z{}(), f{}(z{}())))"));
    }

    /// Priority and `requires` are ignored: an `owise` equation still rewrites some instances.
    #[test]
    fn every_equation_counts_whatever_its_priority() {
        let definition = definition();
        assert!(!normal(&definition, "any{}(s{}(X:SortNat{}))"));
    }

    /// `lift`, `pick` and `tagged` are anywhere heads with one equation each,
    /// `lift(1) = lift(0)`, `pick(s(X) #as Y) = pick(z)` (an as-pattern is a conjunction) and
    /// `tagged(inj{SortA, SortTop}(X)) = pick(z)`. An application is instance-normal only when
    /// no instance of it is an instance of the equation's left-hand side: a different domain
    /// value, a `z` against `s(X)`, and an injection from a sort with no common subsort with
    /// `SortA`; with `SortC` below both `SortA` and `SortB`, an injection from `SortB` may
    /// denote an injection from `SortA`.
    #[test]
    fn domain_values_conjunctions_and_injection_sources_decide_unifiability() {
        let definition = |overlap: bool| {
            let below_both = if overlap {
                [("SortC", "SortA"), ("SortC", "SortB"), ("SortC", "SortTop")]
                    .map(|(sub, sup)| {
                        format!(
                            r"axiom{{R}} \exists{{R}}(V:{sup}{{}},
                                \equals{{{sup}{{}}, R}}(V:{sup}{{}}, inj{{{sub}{{}}, {sup}{{}}}}(F:{sub}{{}})))
                                [subsort{{{sub}{{}}, {sup}{{}}}}()]"
                        )
                    })
                    .join("\n")
            } else {
                String::new()
            };
            let equation = |head: &str, argument_sort: &str, left: &str, right: &str| {
                format!(
                    r"axiom{{R}} \implies{{R}}(
                        \and{{R}}(
                            \top{{R}}(),
                            \and{{R}}(\in{{{argument_sort}{{}}, R}}(X0:{argument_sort}{{}}, {left}), \top{{R}}())
                        ),
                        \equals{{SortAddress{{}}, R}}(
                            {head}{{}}(X0:{argument_sort}{{}}),
                            \and{{SortAddress{{}}}}({right}, \top{{SortAddress{{}}}}())
                        )
                    ) [anywhere{{}}()]"
                )
            };
            let source = format!(
                r#"[]
                module MAIN
                    sort SortNat{{}} []
                    sort SortAddress{{}} []
                    sort SortTop{{}} []
                    sort SortA{{}} []
                    sort SortB{{}} []
                    sort SortC{{}} []
                    hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
                    symbol inj{{From, To}}(From) : To [sortInjection{{}}(), injective{{}}()]
                    symbol z{{}}() : SortNat{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                    symbol s{{}}(SortNat{{}}) : SortNat{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                    symbol a{{}}() : SortA{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                    symbol b{{}}() : SortB{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                    symbol c{{}}() : SortC{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                    symbol lift{{}}(SortInt{{}}) : SortAddress{{}} [anywhere{{}}(), functional{{}}(), injective{{}}()]
                    symbol pick{{}}(SortNat{{}}) : SortAddress{{}} [anywhere{{}}(), functional{{}}(), injective{{}}()]
                    symbol tagged{{}}(SortTop{{}}) : SortAddress{{}} [anywhere{{}}(), functional{{}}(), injective{{}}()]
                    axiom{{R}} \exists{{R}}(V:SortTop{{}},
                        \equals{{SortTop{{}}, R}}(V:SortTop{{}}, inj{{SortA{{}}, SortTop{{}}}}(F:SortA{{}})))
                        [subsort{{SortA{{}}, SortTop{{}}}}()]
                    axiom{{R}} \exists{{R}}(V:SortTop{{}},
                        \equals{{SortTop{{}}, R}}(V:SortTop{{}}, inj{{SortB{{}}, SortTop{{}}}}(F:SortB{{}})))
                        [subsort{{SortB{{}}, SortTop{{}}}}()]
                    {below_both}
                    {lift}
                    {pick}
                    {tagged}
                endmodule []"#,
                lift = equation(
                    "lift",
                    "SortInt",
                    r#"\dv{SortInt{}}("1")"#,
                    r#"lift{}(\dv{SortInt{}}("0"))"#
                ),
                pick = equation(
                    "pick",
                    "SortNat",
                    r"\and{SortNat{}}(s{}(X:SortNat{}), Y:SortNat{})",
                    "pick{}(z{}())"
                ),
                tagged = equation(
                    "tagged",
                    "SortTop",
                    r"inj{SortA{}, SortTop{}}(X:SortA{})",
                    "pick{}(z{}())"
                ),
            );
            let syntax = parse_definition(&source).expect("definition should parse");
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
        };
        let apart = definition(false);
        assert!(normal(&apart, r#"lift{}(\dv{SortInt{}}("2"))"#));
        assert!(normal(&apart, r#"lift{}(\dv{SortInt{}}("0"))"#));
        assert!(!normal(&apart, r#"lift{}(\dv{SortInt{}}("1"))"#));
        assert!(!normal(&apart, "lift{}(I:SortInt{})"));
        assert!(normal(&apart, "pick{}(z{}())"));
        assert!(!normal(&apart, "pick{}(s{}(z{}()))"));
        assert!(!normal(&apart, "pick{}(N:SortNat{})"));
        let from = |sort: &str| format!("tagged{{}}(inj{{{sort}{{}}, SortTop{{}}}}(V:{sort}{{}}))");
        assert!(normal(&apart, &from("SortB")));
        assert!(!normal(&apart, &from("SortA")));
        assert!(!normal(&apart, "tagged{}(T:SortTop{})"));
        let overlapping = definition(true);
        assert!(!normal(&overlapping, &from("SortB")));
        assert!(!normal(&overlapping, &from("SortC")));

        // Unification decomposes an anywhere head only on instance-normal applications, so it
        // keeps as one equation each pair the equations may identify: `pick(s(N))` is
        // `pick(z)` for every `N`, and `lift(I)` is `lift(0)` for `I = 0` and, through the
        // equation `lift(1) = lift(0)`, for `I = 1`; the substitution `I = 0` alone loses
        // `I = 1`.
        let term = |source: &str| {
            apart
                .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
                .expect("term should internalize")
        };
        for (left, right) in [
            ("pick{}(s{}(N:SortNat{}))", "pick{}(z{}())"),
            ("lift{}(I:SortInt{})", r#"lift{}(\dv{SortInt{}}("0"))"#),
        ] {
            let result = crate::unification::unify_term_pairs(
                &apart,
                crate::substitution::Substitution::new(),
                [(term(left), term(right))],
            );
            let crate::unification::UnificationResult::Unified(unified) = &result else {
                panic!("{left} = {right} is satisfiable: {result:?}");
            };
            assert!(unified.substitution.is_empty(), "{left}: {result:?}");
            assert_eq!(unified.constraints.len(), 1, "{left}: {result:?}");
        }
    }

    /// The classifier arms of the syntactic test separate two roots exactly where the rigidity
    /// predicate the test had before them did (`rigid` below is that predicate, transcribed): a
    /// domain value, a free-constructor application and, on the subject side only, an
    /// equation-head application; an injection only from such an application; a collection from
    /// nothing. Checked for every pair of root kinds those arms decide, on every combination of
    /// sides a resolved pair can have.
    #[test]
    fn the_classifier_arms_separate_the_roots_the_rigidity_predicate_did() {
        fn rigid((side, term): Sided<'_>) -> bool {
            match term.kind() {
                TermKind::DomainValue { .. } => true,
                TermKind::Application { symbol, .. } => match symbol.attributes.head_role() {
                    HeadRole::FreeConstructor => true,
                    HeadRole::EquationHead => side == Side::Subject,
                    HeadRole::Function { .. } | HeadRole::Uninterpreted | HeadRole::Residual => {
                        false
                    }
                },
                TermKind::Injection { .. }
                | TermKind::Variable(_)
                | TermKind::And(..)
                | TermKind::Map { .. }
                | TermKind::List { .. }
                | TermKind::Set { .. } => false,
            }
        }
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortNat{} []
                sort SortAddress{} []
                hooked-sort SortMap{}
                    [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
                symbol z{}() : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol s{}(SortNat{}) : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol f{}(SortNat{}) : SortNat{} [function{}(), total{}(), no-evaluators{}()]
                symbol wrap{}(SortNat{}) : SortAddress{} [anywhere{}(), functional{}()]
                symbol tag{}(SortNat{}) : SortAddress{} [anywhere{}(), functional{}()]
                symbol label{}(SortNat{}) : SortAddress{} [constructor{}(), functional{}(), macro{}()]
                hooked-symbol mapUnit{}() : SortMap{} [function{}(), total{}(), hook{}("MAP.unit")]
                hooked-symbol mapItem{}(SortNat{}, SortNat{}) : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.element")]
                hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{}
                    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let term = |source: &str| {
            definition
                .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
                .expect("term should internalize")
        };
        let zero = term("z{}()");
        let terms = [
            Term::domain_value(Sort::simple("SortNat"), "1"),
            Term::injection(
                Sort::simple("SortNat"),
                Sort::simple("SortAddress"),
                zero.clone(),
            ),
            term("mapItem{}(z{}(), z{}())"),
            zero.clone(),
            term("s{}(z{}())"),
            term("wrap{}(z{}())"),
            term("tag{}(z{}())"),
            term("f{}(z{}())"),
            term("label{}(z{}())"),
        ];
        let arguments = NormalArguments::of_subterms_for_test(&definition, &zero)
            .expect("a constant has no subterms");
        let sides = [Side::Pattern, Side::Subject];
        let mut checked = 0;
        for left in &terms {
            for right in &terms {
                let other_arm = match (left.kind(), right.kind()) {
                    (TermKind::DomainValue { .. }, TermKind::DomainValue { .. })
                    | (TermKind::Injection { .. }, TermKind::Injection { .. }) => true,
                    (
                        TermKind::Application { symbol: left, .. },
                        TermKind::Application { symbol: right, .. },
                    ) => left.name == right.name,
                    _ => false,
                };
                if other_arm {
                    continue;
                }
                for left_side in sides {
                    for right_side in sides {
                        let (left, right) = ((left_side, left), (right_side, right));
                        let expected = match (left.1.kind(), right.1.kind()) {
                            (TermKind::Injection { .. }, TermKind::Application { .. }) => {
                                !rigid(right)
                            }
                            (TermKind::Application { .. }, TermKind::Injection { .. }) => {
                                !rigid(left)
                            }
                            _ => !(rigid(left) && rigid(right)),
                        };
                        let mut unifier = SyntacticUnifier {
                            sorts: definition.sort_graph(),
                            subject_values: InheritedFromArguments(arguments),
                            bindings: HashMap::new(),
                            pending: Vec::new(),
                        };
                        assert_eq!(
                            unifier.unify_one(left, right),
                            expected,
                            "{left:?} against {right:?}"
                        );
                        checked += 1;
                    }
                }
            }
        }
        // Nine roots on each side, less the two same-kind pairs and the six same-name pairs.
        assert_eq!(checked, 4 * (9 * 9 - 2 - 6));
    }
}
