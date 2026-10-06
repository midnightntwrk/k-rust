//! Boundary contracts of the last two recovery kinds of an indeterminate rule match
//! (`crate::rewrite::recover`): the functional-symbolic narrowing and the function-equality
//! witness, the ones tried only after general unification left a collection pair unsolved.
//!
//! Both recover a rule application by stating the unresolved pairs as equalities over fresh
//! existentials for the rule's unbound variables. Each test checks that the step then splits
//! the configuration exactly: the applied branch's condition is equivalent to those equalities
//! (no pair dropped, none added), which constrain the configuration's own variable, and the
//! remainder is the configuration under their negation, so every instance is in exactly the one
//! of the two the rule's match puts it in.

use std::collections::BTreeSet;

use k_rust_kore::kore::{
    parser::{parse_definition, parse_pattern},
    printer::Printer,
};

use crate::{
    definition::BackendDefinition,
    externalize::{self, ConjunctionShape},
    fresh::FreshCounter,
    rewrite::{Pattern, RewriteResult, rewrite_step_with_solver},
    rule::Predicate,
    smt::{Satisfiability, SmtError, SmtSolver, Validity},
    stop::Stoppable,
    substitution::{Substitution, substitute},
    term::{HeadRole, Sort, Term, TermKind, Variable},
};

/// Maps from `SortKey` to `SortValue`, a function `opaqueMap` into them and `opaqueKey` into the
/// keys (no equations), constructors `box(SortMap)`, `st(SortMap, SortMap)`,
/// `st3(SortBox, SortBox, SortKey)` and `done`, and the rule `rule_lhs => done`.
fn definition(rule_lhs: &str) -> BackendDefinition {
    let source = format!(
        r#"[]
            module MAIN
                sort SortKey{{}} [hasDomainValues{{}}()]
                sort SortValue{{}} [hasDomainValues{{}}()]
                sort SortS{{}} []
                sort SortBox{{}} []
                hooked-sort SortMap{{}}
                    [hook{{}}("MAP.Map"), unit{{}}(mapUnit{{}}()), element{{}}(mapItem{{}}()), concat{{}}(mapConcat{{}}())]
                hooked-symbol mapUnit{{}}() : SortMap{{}} [function{{}}(), total{{}}(), hook{{}}("MAP.unit")]
                hooked-symbol mapItem{{}}(SortKey{{}}, SortValue{{}}) : SortMap{{}} [function{{}}(), total{{}}(), hook{{}}("MAP.element")]
                hooked-symbol mapConcat{{}}(SortMap{{}}, SortMap{{}}) : SortMap{{}} [function{{}}(), hook{{}}("MAP.concat"), assoc{{}}(), comm{{}}()]
                symbol opaqueMap{{}}(SortKey{{}}) : SortMap{{}} [function{{}}(), total{{}}()]
                symbol opaqueKey{{}}(SortValue{{}}) : SortKey{{}} [function{{}}(), total{{}}()]
                symbol box{{}}(SortMap{{}}) : SortBox{{}} [constructor{{}}(), functional{{}}()]
                symbol st{{}}(SortMap{{}}, SortMap{{}}) : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol st3{{}}(SortBox{{}}, SortBox{{}}, SortKey{{}}) : SortS{{}} [constructor{{}}(), functional{{}}()]
                symbol done{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                axiom{{}} \rewrites{{SortS{{}}}}(
                    \and{{SortS{{}}}}({rule_lhs}, \top{{SortS{{}}}}()),
                    \and{{SortS{{}}}}(done{{}}(), \top{{SortS{{}}}}())
                ) [label{{}}("narrow")]
            endmodule []"#
    );
    let syntax = parse_definition(&source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

fn term(definition: &BackendDefinition, source: &str) -> Term {
    definition
        .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
        .expect("term should internalize")
}

/// A solver for which every narrowing is satisfiable and every condition undecided, so that the
/// step keeps both the applied branch and the remainder.
struct Contingent;

impl SmtSolver for Contingent {
    fn is_sat(
        &self,
        _predicates: &[Predicate],
        _substitution: &Substitution,
    ) -> Stoppable<Result<Satisfiability, SmtError>> {
        Ok(Ok(Satisfiability::Sat))
    }

    fn check_predicates(
        &self,
        _known: &[Predicate],
        _substitution: &Substitution,
        _checked: &[Predicate],
    ) -> Stoppable<Result<Validity, SmtError>> {
        Ok(Ok(Validity::Contingent))
    }
}

fn free_variables(predicates: &[Predicate]) -> BTreeSet<Variable> {
    predicates
        .iter()
        .flat_map(Predicate::free_variables)
        .collect()
}

fn is_application_of(term: &Term, name: &str) -> bool {
    matches!(term.kind(), TermKind::Application { symbol, .. } if symbol.name.as_ref() == name)
}

/// The constraints as one compact KORE conjunction, for failure messages.
fn show(predicates: &[Predicate]) -> String {
    let sort = Sort::simple("SortS");
    externalize::predicates_pattern(
        predicates,
        &sort,
        |predicate| externalize::predicate_pattern(predicate, &sort),
        ConjunctionShape::Flat,
    )
    .map_or_else(
        || "true".to_owned(),
        |pattern| Printer::compact().print_pattern(&pattern),
    )
}

/// Whether `predicate` only states that terms are defined: a `ceil`, possibly under existentials,
/// or a key's absence from a map's other keys. An equality between a variable and a term implies
/// that the term is defined, so such a conjunct never narrows the expected condition.
fn is_definedness(predicate: &Predicate) -> bool {
    match predicate {
        Predicate::Ceil(_) | Predicate::Absent(_) => true,
        Predicate::Exists(_, inner) => is_definedness(inner),
        _ => false,
    }
}

/// The equalities a set of hypotheses entails by congruence of every symbol and injectivity of
/// free constructors, both valid in every model of a definition. Collection terms are atoms
/// compared syntactically, which only makes the closure entail less.
struct Closure {
    terms: Vec<Term>,
    parent: Vec<usize>,
}

impl Closure {
    fn new<'a>(
        hypotheses: &'a [(Term, Term)],
        goals: impl IntoIterator<Item = &'a (Term, Term)>,
    ) -> Self {
        let mut closure = Self {
            terms: Vec::new(),
            parent: Vec::new(),
        };
        for (left, right) in hypotheses.iter().chain(goals) {
            closure.add(left);
            closure.add(right);
        }
        for (left, right) in hypotheses {
            let (left, right) = (closure.add(left), closure.add(right));
            closure.union(left, right);
        }
        while closure.saturate_once() {}
        closure
    }

    fn add(&mut self, term: &Term) -> usize {
        if let Some(index) = self.terms.iter().position(|known| known == term) {
            return index;
        }
        if let TermKind::Application { arguments, .. } = term.kind() {
            for argument in arguments {
                self.add(argument);
            }
        }
        self.terms.push(term.clone());
        self.parent.push(self.parent.len());
        self.parent.len() - 1
    }

    fn find(&mut self, index: usize) -> usize {
        let parent = self.parent[index];
        if parent == index {
            return index;
        }
        let root = self.find(parent);
        self.parent[index] = root;
        root
    }

    fn union(&mut self, left: usize, right: usize) -> bool {
        let (left, right) = (self.find(left), self.find(right));
        self.parent[left] = right;
        left != right
    }

    fn saturate_once(&mut self) -> bool {
        let mut changed = false;
        for first in 0..self.terms.len() {
            for second in first + 1..self.terms.len() {
                let (first_term, second_term) =
                    (self.terms[first].clone(), self.terms[second].clone());
                let (
                    TermKind::Application {
                        symbol,
                        sort_arguments,
                        arguments,
                    },
                    TermKind::Application {
                        symbol: other_symbol,
                        sort_arguments: other_sort_arguments,
                        arguments: other_arguments,
                    },
                ) = (first_term.kind(), second_term.kind())
                else {
                    continue;
                };
                if symbol != other_symbol || sort_arguments != other_sort_arguments {
                    continue;
                }
                let pairs = arguments
                    .iter()
                    .zip(other_arguments)
                    .map(|(argument, other)| (self.add(argument), self.add(other)))
                    .collect::<Vec<_>>();
                if pairs
                    .iter()
                    .all(|&(argument, other)| self.find(argument) == self.find(other))
                {
                    changed |= self.union(first, second);
                }
                if symbol.attributes.head_role() == HeadRole::FreeConstructor
                    && self.find(first) == self.find(second)
                {
                    for (argument, other) in pairs {
                        changed |= self.union(argument, other);
                    }
                }
            }
        }
        changed
    }

    fn entails(&mut self, (left, right): &(Term, Term)) -> bool {
        let (left, right) = (self.add(left), self.add(right));
        self.find(left) == self.find(right)
    }
}

/// Whether `hypotheses` entail every one of `goals`.
fn entails_all(hypotheses: &[(Term, Term)], goals: &[(Term, Term)]) -> bool {
    let mut closure = Closure::new(hypotheses, goals);
    goals.iter().all(|goal| closure.entails(goal))
}

/// Every injective renaming of `from` onto `onto` that keeps each variable's sort.
fn renamings(from: &[Variable], onto: &BTreeSet<Variable>) -> Vec<Substitution> {
    let Some((first, rest)) = from.split_first() else {
        return vec![Substitution::new()];
    };
    onto.iter()
        .filter(|target| target.sort == first.sort)
        .flat_map(|target| {
            let mut remaining = onto.clone();
            remaining.remove(target);
            renamings(rest, &remaining).into_iter().map(|mut renaming| {
                renaming.insert(first.clone(), Term::variable(target.clone()));
                renaming
            })
        })
        .collect()
}

/// The applied branch's condition is `expected`, the equalities the rule's match leaves, with the
/// rule variables in `rule_variables` replaced by the branch's own fresh variables.
///
/// The branch's free variables other than `configuration` are its fresh existentials; there must
/// be one per rule variable. For some sort-preserving renaming of the rule variables onto them,
/// the branch's equalities and the renamed `expected` must entail each other, and every other
/// conjunct must be a definedness condition. A branch that drops a pair (wider than the rule's
/// match, so the remainder loses the instances in between) fails the first direction; one that
/// adds an equality fails the second.
fn assert_condition_is(
    branch: &Pattern,
    configuration: &Variable,
    rule_variables: &[Variable],
    expected: &[(Term, Term)],
) {
    let shown = show(&branch.constraints);
    let mut fresh = free_variables(&branch.constraints);
    assert!(
        fresh.remove(configuration),
        "the condition constrains {}: {shown}",
        configuration.name
    );
    assert_eq!(
        fresh.len(),
        rule_variables.len(),
        "one fresh existential per unbound rule variable: {shown}"
    );
    let equalities = branch
        .constraints
        .iter()
        .filter_map(|predicate| match predicate {
            Predicate::Equals(left, right) => Some((left.clone(), right.clone())),
            other => {
                assert!(is_definedness(other), "unexpected conjunct in {shown}");
                None
            }
        })
        .collect::<Vec<_>>();
    let matched = renamings(rule_variables, &fresh)
        .into_iter()
        .any(|renaming| {
            let expected = expected
                .iter()
                .map(|(left, right)| (substitute(left, &renaming), substitute(right, &renaming)))
                .collect::<Vec<_>>();
            entails_all(&equalities, &expected) && entails_all(&expected, &equalities)
        });
    assert!(
        matched,
        "the condition is not equivalent to the rule's pair equalities: {shown}"
    );
}

/// The one applied branch and the remainder of a step on `subject`.
fn split(definition: &BackendDefinition, subject: &str) -> (Pattern, Pattern) {
    let pattern = Pattern {
        term: term(definition, subject),
        constraints: Vec::new(),
    };
    let mut fresh = FreshCounter::for_request(&[&pattern]);
    match rewrite_step_with_solver(definition, &pattern, &mut fresh, &Contingent)
        .expect("no stop is armed")
    {
        RewriteResult::Branch {
            mut branches,
            remainder: Some(remainder),
            ..
        } if branches.len() == 1 => {
            let branch = branches.pop().expect("one branch");
            assert!(
                is_application_of(&branch.pattern.term, "done"),
                "{branch:?}"
            );
            assert_eq!(remainder.pattern.term, pattern.term);
            (branch.pattern, remainder.pattern)
        }
        other => panic!("expected one applied branch and a remainder, found {other:#?}"),
    }
}

/// The remainder's constraints are exactly the negation of the applied branch's condition, its
/// fresh variables existentially quantified: `¬∃ fresh. ⋀ branch`.
fn assert_complement(branch: &Pattern, remainder: &Pattern, configuration: &Variable) {
    let [Predicate::Not(negated)] = remainder.constraints.as_slice() else {
        panic!("expected a negated condition, found {remainder:#?}");
    };
    let mut bound = BTreeSet::new();
    let mut body = negated.as_ref();
    while let Predicate::Exists(variable, inner) = body {
        bound.insert(variable.clone());
        body = inner;
    }
    let conjuncts = match body {
        Predicate::And(conjuncts) => conjuncts.clone(),
        single => vec![single.clone()],
    };
    assert_eq!(
        conjuncts.iter().collect::<BTreeSet<_>>(),
        branch.constraints.iter().collect::<BTreeSet<_>>(),
        "the remainder negates the branch's condition"
    );
    let mut fresh = free_variables(&branch.constraints);
    fresh.remove(configuration);
    assert_eq!(bound, fresh, "exactly the fresh variables are quantified");
}

/// Functional-symbolic narrowing: the rule `st(opaqueMap(K), K2 |-> V2 R)` against `st(M, M)`.
/// Matching leaves `opaqueMap(K) ~ M` and `K2 |-> V2 R ~ M`, unification binds `M` and leaves
/// the two map sides unsolved, and each pair has a functional rule side and the configuration
/// variable `M`. The rule applies exactly to the instances with `M = opaqueMap(K')` and
/// `M = K2' |-> V2' R'` for some `K'`, `K2'`, `V2'`, `R'`, so the applied branch's condition is
/// those two equalities over fresh existentials. Dropping either widens the branch past the
/// rule's match and makes the remainder, its complement, lose the instances in between.
#[test]
fn functional_symbolic_narrowing_splits_the_configuration_on_its_variable() {
    let definition = definition(
        r#"st{}(opaqueMap{}(K:SortKey{}), mapConcat{}(mapItem{}(K2:SortKey{}, V2:SortValue{}), R:SortMap{}))"#,
    );
    let (branch, remainder) = split(&definition, "st{}(M:SortMap{}, M:SortMap{})");
    let m = Variable::new("M", Sort::simple("SortMap"));
    let rule_variables = [
        Variable::new("K", Sort::simple("SortKey")),
        Variable::new("K2", Sort::simple("SortKey")),
        Variable::new("V2", Sort::simple("SortValue")),
        Variable::new("R", Sort::simple("SortMap")),
    ];
    let configuration = Term::variable(m.clone());
    let expected = [
        (
            configuration.clone(),
            term(&definition, "opaqueMap{}(K:SortKey{})"),
        ),
        (
            configuration,
            term(
                &definition,
                "mapConcat{}(mapItem{}(K2:SortKey{}, V2:SortValue{}), R:SortMap{})",
            ),
        ),
    ];
    assert_condition_is(&branch, &m, &rule_variables, &expected);
    assert_complement(&branch, &remainder, &m);
}

/// Function-equality witness: the rule `st3(box(opaqueMap(K)), box(K2 |-> V2 R), opaqueKey(V))`
/// against `st3(B, B, "k")`. The third pair has a constructor-like subject, so the
/// functional-symbolic narrowing does not apply; every pair contains a function or a map, so
/// each becomes an equality. The rule applies exactly to the instances with
/// `B = box(opaqueMap(K'))`, `B = box(K2' |-> V2' R')` and `opaqueKey(V') = "k"` for some fresh
/// `K'`, `K2'`, `V2'`, `R'`, `V'`; the applied branch's condition is those three equalities.
#[test]
fn function_equality_recovery_splits_the_configuration_on_its_variable() {
    let definition = definition(
        r#"st3{}(box{}(opaqueMap{}(K:SortKey{})), box{}(mapConcat{}(mapItem{}(K2:SortKey{}, V2:SortValue{}), R:SortMap{})), opaqueKey{}(V:SortValue{}))"#,
    );
    let (branch, remainder) = split(
        &definition,
        r#"st3{}(B:SortBox{}, B:SortBox{}, \dv{SortKey{}}("k"))"#,
    );
    let b = Variable::new("B", Sort::simple("SortBox"));
    let rule_variables = [
        Variable::new("K", Sort::simple("SortKey")),
        Variable::new("K2", Sort::simple("SortKey")),
        Variable::new("V2", Sort::simple("SortValue")),
        Variable::new("R", Sort::simple("SortMap")),
        Variable::new("V", Sort::simple("SortValue")),
    ];
    let configuration = Term::variable(b.clone());
    let expected = [
        (
            configuration.clone(),
            term(&definition, "box{}(opaqueMap{}(K:SortKey{}))"),
        ),
        (
            configuration,
            term(
                &definition,
                "box{}(mapConcat{}(mapItem{}(K2:SortKey{}, V2:SortValue{}), R:SortMap{}))",
            ),
        ),
        (
            term(&definition, "opaqueKey{}(V:SortValue{})"),
            term(&definition, r#"\dv{SortKey{}}("k")"#),
        ),
    ];
    assert_condition_is(&branch, &b, &rule_variables, &expected);
    assert_complement(&branch, &remainder, &b);
}
