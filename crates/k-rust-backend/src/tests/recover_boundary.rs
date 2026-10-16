//! Boundary contracts of the last two recovery kinds of an indeterminate rule match
//! (`crate::rewrite::recover`): the functional-symbolic narrowing and the function-equality
//! witness, the ones tried only after general unification left a collection pair unsolved.
//!
//! Both recover a rule application by stating the unresolved pairs as equalities over fresh
//! existentials for the rule's unbound variables. Each test checks that the step then splits
//! the configuration exactly: the applied branch's condition is equivalent to those equalities
//! (no pair dropped, none added, and no other conjunct they do not imply), which constrain the
//! configuration's own variable, and the remainder is the configuration under their negation, so
//! every instance is in exactly the one of the two the rule's match puts it in.

use std::collections::BTreeSet;
use std::sync::Arc;

use k_rust_kore::kore::{
    parser::{parse_definition, parse_pattern},
    printer::Printer,
};

use crate::{
    definition::BackendDefinition,
    externalize::{self, ConjunctionShape},
    fresh::{FreshCounter, RequestNames},
    rewrite::{Pattern, RewriteResult, rewrite_step_with_solver},
    rule::{Absence, Predicate},
    smt::{Satisfiability, SmtError, SmtSolver, Validity},
    stop::Stoppable,
    substitution::{Substitution, substitute},
    term::{FunctionType, HeadRole, Sort, SymbolType, Term, TermKind, Variable, VariableKind},
};

/// Maps from `SortKey` to `SortValue`, a function `opaqueMap` into them and `opaqueKey` into the
/// keys (no equations), constructors `box(SortMap)`, `st(SortMap, SortMap)`,
/// `st3(SortBox, SortBox, SortKey)`, `done` and `res(SortKey, SortKey, SortValue, SortMap)`, and
/// the rule `rule_lhs => done`.
fn definition(rule_lhs: &str) -> BackendDefinition {
    definition_with_rhs(rule_lhs, "done{}()")
}

/// [`definition`] with the rule `rule_lhs => rule_rhs`.
fn definition_with_rhs(rule_lhs: &str, rule_rhs: &str) -> BackendDefinition {
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
                symbol res{{}}(SortKey{{}}, SortKey{{}}, SortValue{{}}, SortMap{{}}) : SortS{{}} [constructor{{}}(), functional{{}}()]
                axiom{{}} \rewrites{{SortS{{}}}}(
                    \and{{SortS{{}}}}({rule_lhs}, \top{{SortS{{}}}}()),
                    \and{{SortS{{}}}}({rule_rhs}, \top{{SortS{{}}}}())
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

/// The immediate subterms of `term`, collection elements included, so that the closure knows
/// every term a definedness witness can be drawn from.
fn children(term: &Term) -> Vec<Term> {
    match term.kind() {
        TermKind::Application { arguments, .. } => arguments.clone(),
        TermKind::Injection { term, .. } => vec![term.clone()],
        TermKind::And(left, right) => vec![left.clone(), right.clone()],
        TermKind::Map { entries, rest, .. } => entries
            .iter()
            .flat_map(|(key, value)| [key.clone(), value.clone()])
            .chain(rest.clone())
            .collect(),
        TermKind::List { heads, rest, .. } => heads
            .iter()
            .cloned()
            .chain(rest.iter().flat_map(|(middle, tails)| {
                std::iter::once(middle.clone()).chain(tails.iter().cloned())
            }))
            .collect(),
        TermKind::Set { elements, rest, .. } => {
            elements.iter().cloned().chain(rest.clone()).collect()
        }
        TermKind::DomainValue { .. } | TermKind::Variable(_) => Vec::new(),
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
        for child in children(term) {
            self.add(&child);
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

    /// The terms whose class is known to be defined, i.e. to denote exactly one element, by
    /// facts valid in every model: an element variable is one element, and so is a domain
    /// value; a constructor or a total (`functional`) symbol applied to defined arguments, and a
    /// sort injection of a defined term, are defined; a class is defined when one of its terms
    /// is, since its terms are equal. Every constructor of this module's definition is also
    /// declared `functional`.
    fn defined_terms(&mut self) -> Vec<bool> {
        let mut defined_classes = BTreeSet::new();
        loop {
            let mut changed = false;
            for index in 0..self.terms.len() {
                let term = self.terms[index].clone();
                let defined = match term.kind() {
                    TermKind::Variable(variable) => variable.kind == VariableKind::Element,
                    TermKind::DomainValue { .. } => true,
                    TermKind::Application {
                        symbol, arguments, ..
                    } => {
                        matches!(
                            symbol.attributes.symbol_type,
                            SymbolType::Constructor | SymbolType::Function(FunctionType::Total)
                        ) && arguments.iter().all(|argument| {
                            let argument = self.add(argument);
                            defined_classes.contains(&self.find(argument))
                        })
                    }
                    TermKind::Injection { term, .. } => {
                        let inner = self.add(term);
                        defined_classes.contains(&self.find(inner))
                    }
                    _ => false,
                };
                if defined {
                    changed |= defined_classes.insert(self.find(index));
                }
            }
            if !changed {
                break;
            }
        }
        (0..self.terms.len())
            .map(|index| defined_classes.contains(&self.find(index)))
            .collect()
    }

    /// Whether `term` is defined in every model of the hypotheses ([`Closure::defined_terms`]).
    fn defines(&mut self, term: &Term) -> bool {
        let index = self.add(term);
        while self.saturate_once() {}
        self.defined_terms()[index]
    }

    /// Whether the hypotheses entail the definedness condition `predicate`: `\ceil(t)` when `t`
    /// is defined; `\exists x. φ` when `φ` holds with `x` replaced by some term of `x`'s sort
    /// already in the closure (if `x` occurs in a defined `t`, its replacement is defined,
    /// because an application to `\bottom` is `\bottom`, so it witnesses `x`); an absence as
    /// the pattern it stands for ([`Absence`]): `\exists V. \ceil(key |-> V rest)` for a map,
    /// `\ceil(SetItem(key) rest)` for a set. Nothing else is entailed.
    fn entails_definedness(&mut self, predicate: &Predicate) -> bool {
        match predicate {
            Predicate::Ceil(term) => self.defines(term),
            Predicate::Exists(variable, body) => {
                let Predicate::Ceil(term) = body.as_ref() else {
                    return false;
                };
                let candidates = self
                    .terms
                    .iter()
                    .filter(|candidate| candidate.sort() == variable.sort)
                    .cloned()
                    .collect::<Vec<_>>();
                candidates.into_iter().any(|candidate| {
                    let instance =
                        substitute(term, &Substitution::from([(variable.clone(), candidate)]));
                    self.defines(&instance)
                })
            }
            Predicate::Absent(absence) => {
                let ceil = Predicate::Ceil(absence.joined().clone());
                match absence.binder() {
                    Some(binder) => {
                        self.entails_definedness(&Predicate::Exists(binder.clone(), Arc::new(ceil)))
                    }
                    None => self.entails_definedness(&ceil),
                }
            }
            _ => false,
        }
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
/// conjunct must be a definedness condition that the branch's equalities entail
/// ([`Closure::entails_definedness`]), so that the condition is equivalent to its equalities
/// alone. A branch that drops a pair (wider than the rule's match, so the remainder loses the
/// instances in between) fails the first direction; one that adds an equality fails the second;
/// one that adds a definedness condition the equalities do not imply (narrower than the rule's
/// match, possibly empty) fails the third check.
///
/// Returns those renamings, which name the fresh existential each rule variable became.
fn assert_condition_is(
    branch: &Pattern,
    configuration: &Variable,
    rule_variables: &[Variable],
    expected: &[(Term, Term)],
) -> Vec<Substitution> {
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
    let (equalities, others): (Vec<_>, Vec<_>) = branch
        .constraints
        .iter()
        .partition(|predicate| matches!(predicate, Predicate::Equals(..)));
    let equalities = equalities
        .into_iter()
        .map(|predicate| match predicate {
            Predicate::Equals(left, right) => (left.clone(), right.clone()),
            _ => unreachable!("partitioned on equalities"),
        })
        .collect::<Vec<_>>();
    let mut closure = Closure::new(&equalities, []);
    for other in others {
        assert!(
            closure.entails_definedness(other),
            "the conjunct {} is not implied by the branch's equalities: {shown}",
            show(std::slice::from_ref(other))
        );
    }
    let matched = renamings(rule_variables, &fresh)
        .into_iter()
        .filter(|renaming| {
            let expected = expected
                .iter()
                .map(|(left, right)| (substitute(left, renaming), substitute(right, renaming)))
                .collect::<Vec<_>>();
            entails_all(&equalities, &expected) && entails_all(&expected, &equalities)
        })
        .collect::<Vec<_>>();
    assert!(
        !matched.is_empty(),
        "the condition is not equivalent to the rule's pair equalities: {shown}"
    );
    matched
}

/// The one applied branch, whose term is `done`, and the remainder of a step on `subject`.
fn split(definition: &BackendDefinition, subject: &str) -> (Pattern, Pattern) {
    let pattern = Pattern {
        term: term(definition, subject),
        constraints: Vec::new(),
    };
    let (branch, remainder) = split_with(
        definition,
        &pattern,
        &mut FreshCounter::for_request(&[&pattern]),
    );
    assert!(is_application_of(&branch.term, "done"), "{branch:?}");
    (branch, remainder)
}

/// The one applied branch and the remainder of a step on `pattern`, minting from `fresh`.
fn split_with(
    definition: &BackendDefinition,
    pattern: &Pattern,
    fresh: &mut FreshCounter,
) -> (Pattern, Pattern) {
    match rewrite_step_with_solver(definition, pattern, fresh, &Contingent)
        .expect("no stop is armed")
    {
        RewriteResult::Branch {
            mut branches,
            remainder: Some(remainder),
            ..
        } if branches.len() == 1 => {
            let branch = branches.pop().expect("one branch");
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
        Predicate::And(conjuncts) => conjuncts.to_vec(),
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

/// The left-hand side of the functional-symbolic case, matched against `st(M, M)`.
const FUNCTIONAL_SYMBOLIC_LHS: &str = r#"st{}(opaqueMap{}(K:SortKey{}), mapConcat{}(mapItem{}(K2:SortKey{}, V2:SortValue{}), R:SortMap{}))"#;

/// The left-hand side of the function-equality case, matched against `st3(B, B, "k")`.
const FUNCTION_EQUALITY_LHS: &str = r#"st3{}(box{}(opaqueMap{}(K:SortKey{})), box{}(mapConcat{}(mapItem{}(K2:SortKey{}, V2:SortValue{}), R:SortMap{})), opaqueKey{}(V:SortValue{}))"#;

/// What a step of the functional-symbolic case must split on: the configuration variable `M`,
/// the rule's variables the match leaves unbound, and the rule's pair equalities over them.
fn functional_symbolic_pairs(
    definition: &BackendDefinition,
) -> (Variable, Vec<Variable>, Vec<(Term, Term)>) {
    let m = Variable::new("M", Sort::simple("SortMap"));
    let rule_variables = vec![
        Variable::new("K", Sort::simple("SortKey")),
        Variable::new("K2", Sort::simple("SortKey")),
        Variable::new("V2", Sort::simple("SortValue")),
        Variable::new("R", Sort::simple("SortMap")),
    ];
    let configuration = Term::variable(m.clone());
    let expected = vec![
        (
            configuration.clone(),
            term(definition, "opaqueMap{}(K:SortKey{})"),
        ),
        (
            configuration,
            term(
                definition,
                "mapConcat{}(mapItem{}(K2:SortKey{}, V2:SortValue{}), R:SortMap{})",
            ),
        ),
    ];
    (m, rule_variables, expected)
}

/// What a step of the function-equality case must split on, as [`functional_symbolic_pairs`].
fn function_equality_pairs(
    definition: &BackendDefinition,
) -> (Variable, Vec<Variable>, Vec<(Term, Term)>) {
    let b = Variable::new("B", Sort::simple("SortBox"));
    let rule_variables = vec![
        Variable::new("K", Sort::simple("SortKey")),
        Variable::new("K2", Sort::simple("SortKey")),
        Variable::new("V2", Sort::simple("SortValue")),
        Variable::new("R", Sort::simple("SortMap")),
        Variable::new("V", Sort::simple("SortValue")),
    ];
    let configuration = Term::variable(b.clone());
    let expected = vec![
        (
            configuration.clone(),
            term(definition, "box{}(opaqueMap{}(K:SortKey{}))"),
        ),
        (
            configuration,
            term(
                definition,
                "box{}(mapConcat{}(mapItem{}(K2:SortKey{}, V2:SortValue{}), R:SortMap{}))",
            ),
        ),
        (
            term(definition, "opaqueKey{}(V:SortValue{})"),
            term(definition, r#"\dv{SortKey{}}("k")"#),
        ),
    ];
    (b, rule_variables, expected)
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
    let definition = definition(FUNCTIONAL_SYMBOLIC_LHS);
    let (branch, remainder) = split(&definition, "st{}(M:SortMap{}, M:SortMap{})");
    let (m, rule_variables, expected) = functional_symbolic_pairs(&definition);
    assert_condition_is(&branch, &m, &rule_variables, &expected);
    assert_complement(&branch, &remainder, &m);
}

/// The condition check itself: a branch whose conjuncts are the rule's pair equalities and one
/// more definedness condition that they do not imply is not the rule's match. Here the extra
/// conjunct is the absence of `K2'` from `opaqueMap(K')`; the equalities put `K2'` in that map
/// (`opaqueMap(K') = K2' |-> V2' R'`), so the condition is unsatisfiable, the applied branch is
/// empty, and every instance would fall to the remainder.
#[test]
#[should_panic(expected = "is not implied by the branch's equalities")]
fn a_definedness_conjunct_the_equalities_do_not_imply_fails_the_condition_check() {
    let definition = definition(FUNCTIONAL_SYMBOLIC_LHS);
    let (mut branch, _) = split(&definition, "st{}(M:SortMap{}, M:SortMap{})");
    let (m, rule_variables, expected) = functional_symbolic_pairs(&definition);
    let absence = branch
        .constraints
        .iter()
        .find_map(|predicate| match predicate {
            Predicate::Absent(absence) => Some(absence.clone()),
            _ => None,
        })
        .expect("the branch states that its map pattern is defined");
    let opaque = branch
        .constraints
        .iter()
        .find_map(|predicate| match predicate {
            Predicate::Equals(left, right) => [left, right]
                .into_iter()
                .find(|side| is_application_of(side, "opaqueMap"))
                .cloned(),
            _ => None,
        })
        .expect("the branch equates the configuration with opaqueMap(K')");
    branch.constraints.push(Absence::predicate(
        absence.collection(),
        absence.key().clone(),
        opaque,
    ));
    assert_condition_is(&branch, &m, &rule_variables, &expected);
}

/// Function-equality witness: the rule `st3(box(opaqueMap(K)), box(K2 |-> V2 R), opaqueKey(V))`
/// against `st3(B, B, "k")`. The third pair has a constructor-like subject, so the
/// functional-symbolic narrowing does not apply; every pair contains a function or a map, so
/// each becomes an equality. The rule applies exactly to the instances with
/// `B = box(opaqueMap(K'))`, `B = box(K2' |-> V2' R')` and `opaqueKey(V') = "k"` for some fresh
/// `K'`, `K2'`, `V2'`, `R'`, `V'`; the applied branch's condition is those three equalities.
#[test]
fn function_equality_recovery_splits_the_configuration_on_its_variable() {
    let definition = definition(FUNCTION_EQUALITY_LHS);
    let (branch, remainder) = split(
        &definition,
        r#"st3{}(B:SortBox{}, B:SortBox{}, \dv{SortKey{}}("k"))"#,
    );
    let (b, rule_variables, expected) = function_equality_pairs(&definition);
    assert_condition_is(&branch, &b, &rule_variables, &expected);
    assert_complement(&branch, &remainder, &b);
}

/// The successor of a recovered match is the rule's right-hand side over the fresh existentials
/// its branch condition constrains, each one a mint of the request's counter.
///
/// The rule `lhs => res(K, K2, V2, R)` uses the variables the match leaves unbound, so its
/// successor is what the condition says only if it names the same existentials: the successor
/// must be the right-hand side under a renaming that makes the condition the rule's pair
/// equalities. And every name a rewrite introduces is minted by the request's counter, which
/// skips the spellings of the request's variables (`fresh::RequestNames`), so a successor never
/// prints a variable like one the request wrote. Here the request's names include the spellings
/// of the rule's own variables, as a client may write in an argument that an alias drops: a
/// recovery that let the rule's variables through unminted would print exactly like them.
#[test]
fn the_successor_of_a_recovered_match_is_over_the_minted_existentials_of_its_branch() {
    let rhs = "res{}(K:SortKey{}, K2:SortKey{}, V2:SortValue{}, R:SortMap{})";
    type Pairs = fn(&BackendDefinition) -> (Variable, Vec<Variable>, Vec<(Term, Term)>);
    let cases: [(&str, &str, Pairs); 2] = [
        (
            FUNCTIONAL_SYMBOLIC_LHS,
            "st{}(M:SortMap{}, M:SortMap{})",
            functional_symbolic_pairs,
        ),
        (
            FUNCTION_EQUALITY_LHS,
            r#"st3{}(B:SortBox{}, B:SortBox{}, \dv{SortKey{}}("k"))"#,
            function_equality_pairs,
        ),
    ];
    for (lhs, subject, pairs) in cases {
        let definition = definition_with_rhs(lhs, rhs);
        let rule = definition
            .rewrite_theory()
            .values()
            .flat_map(|groups| groups.values())
            .flatten()
            .next()
            .map(|stored| &stored.rule)
            .expect("the rule is indexed");
        let pattern = Pattern {
            term: term(&definition, subject),
            constraints: Vec::new(),
        };
        let mut names = RequestNames::of(&[&pattern]);
        names.add_variables(&rule.lhs.attributes().variables);
        let mut fresh = FreshCounter::for_request_names(names.clone());
        let (branch, remainder) = split_with(&definition, &pattern, &mut fresh);
        let (configuration, rule_variables, expected) = pairs(&definition);
        let renamings = assert_condition_is(&branch, &configuration, &rule_variables, &expected);
        assert_complement(&branch, &remainder, &configuration);
        let rhs = term(&definition, rhs);
        assert!(
            renamings
                .iter()
                .any(|renaming| substitute(&rhs, renaming) == branch.term),
            "{lhs}: the successor is not the right-hand side over the condition's existentials: \
             {:?} under {}",
            branch.term,
            show(&branch.constraints)
        );
        for variable in &branch.term.attributes().variables {
            assert!(
                !names.spells(&variable.name),
                "{lhs}: the successor's {} prints like a name of the request",
                variable.name
            );
        }
    }
}
