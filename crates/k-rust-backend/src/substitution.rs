//! Saturating substitutions over immutable backend terms.

use std::collections::{BTreeMap, BTreeSet};

use petgraph::{algo::kosaraju_scc, graph::DiGraph};

use crate::{
    matching::SortGraph,
    rule::Predicate,
    term::{Sort, Term, TermKind, Variable},
};

pub type Substitution = BTreeMap<Variable, Term>;

pub fn substitute(term: &Term, substitution: &Substitution) -> Term {
    if term
        .attributes()
        .variables
        .iter()
        .all(|variable| !substitution.contains_key(variable))
    {
        return term.clone();
    }

    match term.kind() {
        TermKind::And(left, right) => Term::and(
            substitute(left, substitution),
            substitute(right, substitution),
        ),
        TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } => Term::application(
            symbol.clone(),
            sort_arguments.clone(),
            arguments
                .iter()
                .map(|argument| substitute(argument, substitution))
                .collect(),
        ),
        TermKind::DomainValue { .. } => term.clone(),
        TermKind::Variable(variable) => substitution
            .get(variable)
            .cloned()
            .unwrap_or_else(|| term.clone()),
        TermKind::Injection {
            source,
            target,
            term,
        } => Term::injection(
            source.clone(),
            target.clone(),
            substitute(term, substitution),
        ),
        TermKind::Map {
            definition,
            entries,
            rest,
        } => Term::map(
            definition.clone(),
            entries
                .iter()
                .map(|(key, value)| {
                    (
                        substitute(key, substitution),
                        substitute(value, substitution),
                    )
                })
                .collect(),
            rest.as_ref().map(|term| substitute(term, substitution)),
        ),
        TermKind::List {
            definition,
            heads,
            rest,
        } => Term::list(
            definition.clone(),
            heads
                .iter()
                .map(|term| substitute(term, substitution))
                .collect(),
            rest.as_ref().map(|(middle, tails)| {
                (
                    substitute(middle, substitution),
                    tails
                        .iter()
                        .map(|term| substitute(term, substitution))
                        .collect(),
                )
            }),
        ),
        TermKind::Set {
            definition,
            elements,
            rest,
        } => Term::set(
            definition.clone(),
            elements
                .iter()
                .map(|term| substitute(term, substitution))
                .collect(),
            rest.as_ref().map(|term| substitute(term, substitution)),
        ),
    }
}

/// Compose substitutions so new bindings take priority and saturate old values.
pub fn compose(new: &Substitution, old: &Substitution) -> Substitution {
    let mut result = old
        .iter()
        .map(|(variable, term)| (variable.clone(), substitute(term, new)))
        .collect::<Substitution>();
    result.extend(new.clone());
    result
}

/// Extract every unambiguous, acyclic variable equality as a saturated substitution.
///
/// Duplicate bindings remain predicates. For each dependency cycle, the lexicographically first
/// variable is retained as an equality, matching the reference backend's deterministic cycle
/// breaking while allowing the rest of the component to become substitutions.
pub fn extract_substitution(
    constraints: &[Predicate],
    sorts: &SortGraph,
) -> (Substitution, Vec<Predicate>) {
    let mut potential = BTreeMap::<Variable, Vec<(usize, Term)>>::new();
    for (index, constraint) in constraints.iter().enumerate() {
        if let Some((variable, value)) = substitution_binding(constraint, sorts) {
            potential.entry(variable).or_default().push((index, value));
        }
    }
    let mut candidates = potential
        .into_iter()
        .filter_map(|(variable, bindings)| {
            let [(index, value)] = bindings.as_slice() else {
                return None;
            };
            Some((variable, (*index, value.clone())))
        })
        .collect::<BTreeMap<_, _>>();

    loop {
        let variables = candidates.keys().cloned().collect::<Vec<_>>();
        let indexes = variables
            .iter()
            .cloned()
            .enumerate()
            .map(|(index, variable)| (variable, index))
            .collect::<BTreeMap<_, _>>();
        let mut graph = DiGraph::<(), ()>::new();
        let nodes = variables
            .iter()
            .map(|_| graph.add_node(()))
            .collect::<Vec<_>>();
        for (variable, (_, value)) in &candidates {
            let source = nodes[indexes[variable]];
            for dependency in &value.attributes().variables {
                if let Some(index) = indexes.get(dependency) {
                    graph.add_edge(source, nodes[*index], ());
                }
            }
        }
        let mut removed = BTreeSet::new();
        for component in kosaraju_scc(&graph) {
            let cyclic = component.len() > 1
                || component
                    .first()
                    .is_some_and(|node| graph.contains_edge(*node, *node));
            if cyclic {
                let variable = component
                    .iter()
                    .map(|node| variables[node.index()].clone())
                    .min()
                    .expect("a strongly connected component is nonempty");
                removed.insert(variable);
            }
        }
        if removed.is_empty() {
            break;
        }
        candidates.retain(|variable, _| !removed.contains(variable));
    }

    let mut substitution = candidates
        .iter()
        .map(|(variable, (_, value))| (variable.clone(), value.clone()))
        .collect::<Substitution>();
    for _ in 0..substitution.len() {
        let previous = substitution.clone();
        for (variable, value) in &previous {
            let mut others = previous.clone();
            others.remove(variable);
            substitution.insert(variable.clone(), substitute(value, &others));
        }
        if substitution == previous {
            break;
        }
    }

    let selected = candidates
        .values()
        .map(|(index, _)| *index)
        .collect::<BTreeSet<_>>();
    let remaining = constraints
        .iter()
        .enumerate()
        .filter(|(index, _)| !selected.contains(index))
        .map(|(_, predicate)| predicate.clone())
        .collect();
    (substitution, remaining)
}

pub(crate) fn substitution_binding(
    predicate: &Predicate,
    sorts: &SortGraph,
) -> Option<(Variable, Term)> {
    let (left, right) = substitution_equality(predicate)?;
    if let TermKind::Variable(variable) = left.kind()
        && !right.attributes().variables.contains(variable)
        && let Some(value) = align_binding_value(variable, &right, sorts)
    {
        return Some((variable.clone(), value));
    }
    if let TermKind::Variable(variable) = right.kind()
        && !left.attributes().variables.contains(variable)
        && let Some(value) = align_binding_value(variable, &left, sorts)
    {
        return Some((variable.clone(), value));
    }
    None
}

fn align_binding_value(variable: &Variable, value: &Term, sorts: &SortGraph) -> Option<Term> {
    let value_sort = value.sort();
    if value_sort == variable.sort {
        return Some(value.clone());
    }
    sorts
        .check_subsort(&value_sort, &variable.sort)
        .ok()
        .filter(|is_subsort| *is_subsort)
        .map(|_| Term::injection(value_sort, variable.sort.clone(), value.clone()))
}

fn substitution_equality(predicate: &Predicate) -> Option<(Term, Term)> {
    let Predicate::Equals(left, right) = predicate else {
        return None;
    };
    let boolean = |term: &Term| match term.kind() {
        TermKind::DomainValue { sort, value } if sort == &crate::term::Sort::simple("SortBool") => {
            match value.as_ref() {
                "true" => Some(true),
                "false" => Some(false),
                _ => None,
            }
        }
        _ => None,
    };
    if let Some(expected) = boolean(right)
        && let Some(operands) = hooked_equality(left, expected)
    {
        return Some(operands);
    }
    if let Some(expected) = boolean(left)
        && let Some(operands) = hooked_equality(right, expected)
    {
        return Some(operands);
    }
    Some((left.clone(), right.clone()))
}

fn hooked_equality(term: &Term, expected: bool) -> Option<(Term, Term)> {
    let TermKind::Application {
        symbol, arguments, ..
    } = term.kind()
    else {
        return None;
    };
    let hook = symbol.attributes.hook.as_deref()?;
    let equality = matches!(hook, "INT.eq" | "KEQUAL.eq") && expected;
    let negated_equality = matches!(hook, "INT.ne" | "KEQUAL.ne") && !expected;
    if !(equality || negated_equality) {
        return None;
    }
    let [left, right] = arguments.as_slice() else {
        return None;
    };
    if matches!(hook, "KEQUAL.eq" | "KEQUAL.ne") {
        Some((strip_kseq(left), strip_kseq(right)))
    } else {
        Some((left.clone(), right.clone()))
    }
}

/// Remove the singleton K-sequence wrapper used for non-scalar K equality operands.
fn strip_kseq(term: &Term) -> Term {
    let TermKind::Application {
        symbol, arguments, ..
    } = term.kind()
    else {
        return term.clone();
    };
    let [first, tail] = arguments.as_slice() else {
        return term.clone();
    };
    let TermKind::Application {
        symbol: tail_symbol,
        arguments: tail_arguments,
        ..
    } = tail.kind()
    else {
        return term.clone();
    };
    if symbol.name.as_ref() != "kseq"
        || tail_symbol.name.as_ref() != "dotk"
        || !tail_arguments.is_empty()
    {
        return term.clone();
    }
    match first.kind() {
        TermKind::Injection { target, term, .. } if target == &Sort::simple("SortKItem") => {
            term.clone()
        }
        _ if first.sort() == Sort::simple("SortKItem") => first.clone(),
        _ => term.clone(),
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use crate::{
        matching::SortGraph,
        term::{CollectionSymbols, ListDefinition, Sort, Symbol},
    };

    use super::*;

    fn sort() -> Sort {
        Sort::simple("SomeSort")
    }

    fn variable(name: &str) -> Variable {
        Variable::new(name, sort())
    }

    fn var(name: &str) -> Term {
        Term::variable(variable(name))
    }

    fn con1(argument: Term) -> Term {
        Term::application(
            Arc::new(Symbol::constructor("con1", vec![sort()], sort())),
            Vec::new(),
            vec![argument],
        )
    }

    fn integer_equality(left: Term, right: Term) -> Predicate {
        let int_sort = sort();
        let bool_sort = Sort::simple("SortBool");
        let mut symbol =
            Symbol::constructor("intEq", vec![int_sort.clone(), int_sort], bool_sort.clone());
        symbol.attributes.hook = Some("INT.eq".into());
        Predicate::Equals(
            Term::application(Arc::new(symbol), Vec::new(), vec![left, right]),
            Term::domain_value(bool_sort, "true"),
        )
    }

    fn k_sequence(item: Term) -> Term {
        let item_sort = item.sort();
        let k_item_sort = Sort::simple("SortKItem");
        let k_sort = Sort::simple("SortK");
        Term::application(
            Arc::new(Symbol::constructor(
                "kseq",
                vec![k_item_sort.clone(), k_sort.clone()],
                k_sort.clone(),
            )),
            Vec::new(),
            vec![
                Term::injection(item_sort, k_item_sort, item),
                Term::application(
                    Arc::new(Symbol::constructor("dotk", Vec::new(), k_sort)),
                    Vec::new(),
                    Vec::new(),
                ),
            ],
        )
    }

    fn k_equality(hook: &str, expected: bool, left: Term, right: Term) -> Predicate {
        let k_sort = Sort::simple("SortK");
        let bool_sort = Sort::simple("SortBool");
        let mut symbol = Symbol::constructor(
            if hook == "KEQUAL.eq" {
                "kEqual"
            } else {
                "kNotEqual"
            },
            vec![k_sort.clone(), k_sort],
            bool_sort.clone(),
        );
        symbol.attributes.hook = Some(hook.into());
        Predicate::Equals(
            Term::application(
                Arc::new(symbol),
                Vec::new(),
                vec![k_sequence(left), k_sequence(right)],
            ),
            Term::domain_value(bool_sort, expected.to_string()),
        )
    }

    #[test]
    fn substitutes_through_applications_and_conjunctions() {
        let substitution = Substitution::from([(variable("X"), con1(var("Y")))]);
        assert_eq!(
            substitute(&con1(var("X")), &substitution),
            con1(con1(var("Y")))
        );
        assert_eq!(
            substitute(&Term::and(con1(var("X")), con1(var("Y"))), &substitution),
            Term::and(con1(con1(var("Y"))), con1(var("Y")))
        );
    }

    #[test]
    fn composition_is_idempotent() {
        let substitution = Substitution::from([(variable("X"), con1(var("Y")))]);
        assert_eq!(compose(&substitution, &substitution), substitution);
    }

    #[test]
    fn composition_is_transitive_and_saturating() {
        let new = Substitution::from([(variable("X"), var("Z"))]);
        let old = Substitution::from([(variable("Y"), var("X"))]);
        assert_eq!(
            compose(&new, &old),
            Substitution::from([(variable("X"), var("Z")), (variable("Y"), var("Z")),])
        );
    }

    #[test]
    fn extracts_and_saturates_acyclic_constraint_substitutions() {
        let value = Term::domain_value(sort(), "value");
        let constraints = vec![
            Predicate::Equals(var("Y"), con1(var("X"))),
            Predicate::Equals(var("X"), value.clone()),
        ];

        let (substitution, remaining) = extract_substitution(&constraints, &SortGraph::default());

        assert!(remaining.is_empty());
        assert_eq!(substitution[&variable("X")], value.clone());
        assert_eq!(substitution[&variable("Y")], con1(value));
    }

    #[test]
    fn extracts_substitutions_from_hooked_integer_equalities() {
        let value = Term::domain_value(sort(), "value");
        let constraint = integer_equality(var("X"), value.clone());

        let (substitution, remaining) = extract_substitution(&[constraint], &SortGraph::default());

        assert_eq!(substitution, Substitution::from([(variable("X"), value)]));
        assert!(remaining.is_empty());
    }

    #[test]
    fn extracts_substitutions_from_kequal_kseq_equalities() {
        let value = con1(var("X"));
        for constraint in [
            k_equality("KEQUAL.eq", true, var("Y"), value.clone()),
            k_equality("KEQUAL.eq", true, value.clone(), var("Y")),
            k_equality("KEQUAL.ne", false, var("Y"), value.clone()),
        ] {
            let (substitution, remaining) =
                extract_substitution(&[constraint], &SortGraph::default());

            assert_eq!(
                substitution,
                Substitution::from([(variable("Y"), value.clone())])
            );
            assert!(remaining.is_empty());
        }
    }

    #[test]
    fn reinjects_a_subsort_operand_of_a_kequal_binding() {
        let int_sort = Sort::simple("SortInt");
        let exp_sort = Sort::simple("SortExp");
        let variable = Variable::new("X", exp_sort.clone());
        let value = Term::domain_value(int_sort.clone(), "5");
        let constraint = k_equality(
            "KEQUAL.eq",
            true,
            Term::variable(variable.clone()),
            value.clone(),
        );
        let mut sorts = SortGraph::default();
        sorts.insert("SortExp", [Arc::<str>::from("SortInt")]);

        let (substitution, remaining) = extract_substitution(&[constraint], &sorts);

        assert_eq!(
            substitution,
            Substitution::from([(variable, Term::injection(int_sort, exp_sort, value),)])
        );
        assert!(remaining.is_empty());
    }

    #[test]
    fn keeps_kequal_bindings_with_incomparable_sorts_as_predicates() {
        let foo_sort = Sort::simple("SortFoo");
        let bar_sort = Sort::simple("SortBar");
        let variable = Variable::new("X", foo_sort.clone());
        let value = Term::domain_value(bar_sort, "bar");
        let constraint = k_equality("KEQUAL.eq", true, Term::variable(variable), value);
        let mut sorts = SortGraph::default();
        sorts.insert("SortFoo", std::iter::empty());

        let (substitution, remaining) =
            extract_substitution(std::slice::from_ref(&constraint), &sorts);

        assert!(substitution.is_empty());
        assert_eq!(remaining, [constraint]);
    }

    #[test]
    fn round_trips_backend_substitution_predicates() {
        let int_sort = Sort::simple("SortInt");
        let exp_sort = Sort::simple("SortExp");
        let list_sort = Sort::simple("SortList");
        let element_sort = Sort::simple("SortElement");
        let list_definition = Arc::new(ListDefinition {
            symbols: CollectionSymbols {
                unit: "listUnit".into(),
                element: "listItem".into(),
                concat: "listConcat".into(),
            },
            element_sort: "SortElement".into(),
            list_sort: "SortList".into(),
        });
        let substitution = Substitution::from([
            (
                Variable::new("EXP", exp_sort.clone()),
                Term::injection(
                    int_sort.clone(),
                    exp_sort,
                    Term::domain_value(int_sort, "5"),
                ),
            ),
            (
                Variable::new("LIST", list_sort),
                Term::list(
                    list_definition,
                    vec![Term::domain_value(element_sort, "item")],
                    None,
                ),
            ),
        ]);
        let predicates = substitution
            .iter()
            .map(|(variable, value)| {
                Predicate::Equals(Term::variable(variable.clone()), value.clone())
            })
            .collect::<Vec<_>>();

        assert_eq!(
            extract_substitution(&predicates, &SortGraph::default()),
            (substitution, Vec::new())
        );
    }

    #[test]
    fn breaks_cycles_and_retains_one_equation_per_component() {
        let constraints = vec![
            Predicate::Equals(var("Y"), con1(var("X"))),
            Predicate::Equals(var("X"), var("Y")),
        ];

        let (substitution, remaining) = extract_substitution(&constraints, &SortGraph::default());

        assert_eq!(
            substitution,
            Substitution::from([(variable("Y"), con1(var("X")))])
        );
        assert_eq!(remaining, [Predicate::Equals(var("X"), var("Y"))]);
    }

    #[test]
    fn retains_ambiguous_bindings_as_predicates() {
        let constraints = vec![
            Predicate::Equals(var("X"), var("Y")),
            Predicate::Equals(var("X"), con1(var("Y"))),
        ];

        let (substitution, remaining) = extract_substitution(&constraints, &SortGraph::default());

        assert!(substitution.is_empty());
        assert_eq!(remaining, constraints);
    }
}
