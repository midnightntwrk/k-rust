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
//!   when its arguments are and no equation the evaluator may apply to it (headed by that
//!   symbol or by a bare variable, of any priority, `requires` ignored) syntactically unifies
//!   with it. An equation applies to an instance only if the instance matches the equation's
//!   left-hand side, and an instance matches only if the two terms unify; ignoring `requires`
//!   only makes the test report more applications as possibly rewritten;
//! - a declared-function application, any other non-constructor application, a collection, and
//!   a conjunction are not instance-normal: their value is whatever their equations or their
//!   collection axioms make it, so their shape does not determine their value.
//!
//! [`BackendDefinition::instance_normal`] scans ground terms too. That
//! [`Term::concrete_after_normalization`] holds is a syntactic fact (ground, every head a
//! constructor or an anywhere non-function production), not evidence that no equation applies:
//! the ground `wrap(s(z))` has it and is not a normal form.
//! [`BackendDefinition::instance_normal_of_normal_form`] is the variant for a caller that can
//! point at the equation normalization that made its term a fixed point: every subterm of a
//! normal form is a normal form, so a ground subterm is instance-normal without the scan.
//!
//! The syntactic unifiability test asks whether some instance of the subject could match the
//! equation's pattern, not whether two values are equal, so it decomposes every equal-name
//! application purely syntactically and does not recurse into instance normality. It treats a
//! pair as possibly unifiable whenever its shape does not settle the question (a function or
//! collection head, differing injection sources, a sort mismatch it cannot interpret), so an
//! answer of "does not unify" is always a proof that no instance matches.

use std::collections::HashMap;

use crate::{
    definition::BackendDefinition,
    rule::{TermIndex, Theory},
    term::{Sort, SymbolType, Term, TermKind, Variable},
};

impl BackendDefinition {
    /// Whether every instance of `term` is a normal form of this definition's equations; see
    /// the [module documentation](self) for the definition and why it is sound to decompose or
    /// refute an `anywhere` head only on applications for which this holds. Makes no
    /// assumption about how `term` was produced.
    pub(crate) fn instance_normal(&self, term: &Term) -> bool {
        self.instance_normal_under(term, false)
    }

    /// [`Self::instance_normal`] for a term the caller guarantees is a fixed point of equation
    /// normalization, where a [`Term::concrete_after_normalization`] subterm is instance-normal
    /// without the equation scan. A caller must cite the normalization that establishes the
    /// precondition; a term assembled or substituted after normalization does not meet it.
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "the rewrite and equation matchers (KK-52) call it on normalized subjects"
        )
    )]
    pub(crate) fn instance_normal_of_normal_form(&self, term: &Term) -> bool {
        self.instance_normal_under(term, true)
    }

    fn instance_normal_under(&self, term: &Term, normalized: bool) -> bool {
        if normalized && term.concrete_after_normalization() {
            return true;
        }
        let arguments_normal = |arguments: &[Term]| {
            arguments
                .iter()
                .all(|argument| self.instance_normal_under(argument, normalized))
        };
        match term.kind() {
            TermKind::DomainValue { .. } | TermKind::Variable(_) => true,
            TermKind::Injection { term, .. } => self.instance_normal_under(term, normalized),
            TermKind::Application {
                symbol, arguments, ..
            } => {
                if symbol.attributes.symbol_type == SymbolType::Constructor {
                    arguments_normal(arguments)
                } else if symbol.attributes.anywhere && !symbol.attributes.declared_function {
                    arguments_normal(arguments) && !self.some_equation_may_apply(term)
                } else {
                    false
                }
            }
            TermKind::Map { .. }
            | TermKind::List { .. }
            | TermKind::Set { .. }
            | TermKind::And(..) => false,
        }
    }

    /// Whether some equation the evaluator may try on an application headed like `subject`
    /// syntactically unifies with it. The candidates are those equation selection offers such a
    /// subject: the rules indexed by its head symbol and the rules indexed by a bare variable.
    fn some_equation_may_apply(&self, subject: &Term) -> bool {
        let TermKind::Application { symbol, .. } = subject.kind() else {
            return true;
        };
        let indices = [TermIndex::Symbol(symbol.name.clone()), TermIndex::Variable];
        let theory_may_apply = |theory: &Theory| {
            indices.iter().any(|index| {
                theory.get(index).is_some_and(|groups| {
                    groups
                        .values()
                        .flatten()
                        .any(|rule| may_unify(&rule.lhs, subject))
                })
            })
        };
        theory_may_apply(&self.function_theory) || theory_may_apply(&self.simplification_theory)
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

/// Whether the equation pattern `pattern` and `subject` have a common syntactic instance, as far
/// as their shape decides it; `false` is a proof that none exists.
///
/// Precondition: the arguments of `subject` are instance-normal, so a subject subterm headed by
/// an `anywhere` production denotes a value with that head and can be treated as rigid.
fn may_unify(pattern: &Term, subject: &Term) -> bool {
    if let TermKind::Variable(variable) = pattern.kind()
        && sorts_differ(&variable.sort, &subject.sort())
    {
        return false;
    }
    SyntacticUnifier::default().run((Side::Pattern, pattern), (Side::Subject, subject))
}

#[derive(Default)]
struct SyntacticUnifier<'a> {
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
            _ => !(rigid(left) && rigid(right)),
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

/// Whether the head of `term` fixes the head of every value it denotes, so two such terms with
/// different heads have no common instance. On the subject side an `anywhere` application that
/// is not a declared function qualifies by the precondition of [`may_unify`]; on the pattern
/// side only a constructor or a domain value does.
fn rigid((side, term): Sided<'_>) -> bool {
    match term.kind() {
        TermKind::DomainValue { .. } => true,
        TermKind::Application { symbol, .. } => {
            symbol.attributes.symbol_type == SymbolType::Constructor
                || (side == Side::Subject
                    && symbol.attributes.anywhere
                    && !symbol.attributes.declared_function)
        }
        TermKind::Injection { .. }
        | TermKind::Variable(_)
        | TermKind::And(..)
        | TermKind::Map { .. }
        | TermKind::List { .. }
        | TermKind::Set { .. } => false,
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
        definition.instance_normal(&term)
    }

    /// The ground `wrap(s(z))` is concrete after normalization but not a normal form: only the
    /// normal-form variant, whose caller vouches for normalization, may skip the scan.
    #[test]
    fn ground_terms_are_scanned_unless_the_caller_vouches_for_normalization() {
        let definition = definition();
        let term = |source: &str| {
            definition
                .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
                .expect("term should internalize")
        };
        let redex = term("wrap{}(s{}(z{}()))");
        assert!(redex.concrete_after_normalization());
        assert!(!definition.instance_normal(&redex));
        assert!(definition.instance_normal_of_normal_form(&redex));
        assert!(definition.instance_normal(&term("wrap{}(s{}(s{}(z{}())))")));
        assert!(!definition.instance_normal(&term("any{}(z{}())")));
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

    /// Priority and `requires` are ignored: an `owise` equation still rewrites some instances.
    #[test]
    fn every_equation_counts_whatever_its_priority() {
        let definition = definition();
        assert!(!normal(&definition, "any{}(s{}(X:SortNat{}))"));
    }
}
