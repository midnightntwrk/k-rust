//! The frozen clone/remove loop and complete extraction at 8ff88a783 against the restoring helper.
use super::*;
use crate::term::{Sort, Symbol};
use crate::tests::lean_bridge::generators;
use proptest::prelude::*;
use std::sync::Arc;

/// The old loop, including its callback order and convergence-test placement.
/// Kept independent of `saturate_with` so the differential cannot silently test it against itself.
pub(crate) fn reference_saturate_with(
    substitution: &mut Substitution,
    mut apply: impl FnMut(&Term, &Substitution) -> Term,
) {
    for _ in 0..substitution.len() {
        let previous = substitution.clone();
        for (variable, value) in &previous {
            let mut others = previous.clone();
            others.remove(variable);
            substitution.insert(variable.clone(), apply(value, &others));
        }
        if *substitution == previous {
            break;
        }
    }
}

fn reference_extract(
    constraints: &[Predicate],
    mut binding: impl FnMut(&Predicate) -> Option<(Variable, Term)>,
) -> (Substitution, Vec<Predicate>) {
    // No constraint binds nothing and leaves nothing; a ground state's constraint list is empty
    // at every one of its several normalizations per step.
    if constraints.is_empty() {
        return (Substitution::new(), Vec::new());
    }
    let _span = measure::algorithm_span(Algorithm::BackendSubstitutionExtract);
    let mut potential = BTreeMap::<Variable, Vec<(usize, Term)>>::new();
    for (index, constraint) in constraints.iter().enumerate() {
        if let Some((variable, value)) = binding(constraint) {
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

    // Invariant: every removed candidate lay on a cycle of its round's graph; exit when none is.
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
    reference_saturate_with(&mut substitution, substitute);

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

fn variable(i: usize) -> Variable {
    Variable::new(format!("V{i}"), Sort::simple("S"))
}
fn tree(dependencies: impl IntoIterator<Item = usize>) -> Term {
    let arguments = dependencies
        .into_iter()
        .map(|i| Term::variable(variable(i)))
        .collect::<Vec<_>>();
    let symbol = Arc::new(Symbol::constructor(
        "f",
        vec![Sort::simple("S"); arguments.len()],
        Sort::simple("S"),
    ));
    Term::application(symbol, vec![], arguments)
}
fn compare(constraints: &[Predicate], bindable: &BTreeSet<Variable>) {
    let sorts = SortGraph::default();
    assert_eq!(
        reference_extract(constraints, |p| substitution_binding(p, &sorts)),
        extract_substitution(constraints, &sorts)
    );
    let restricted = reference_extract(constraints, |p| {
        let (left, right) = substitution_equality(p)?;
        let (left, right) = peel_equal_injections(left, right);
        restricted_binding(&left, &right, bindable, &sorts)
            .or_else(|| restricted_binding(&right, &left, bindable, &sorts))
    });
    assert_eq!(
        restricted,
        extract_substitution_for(constraints, bindable, &sorts)
    );
    assert!(restricted.0.keys().all(|v| bindable.contains(v)));
    for (key, value) in &restricted.0 {
        assert!(
            restricted
                .0
                .keys()
                .all(|v| !value.attributes().variables.contains(v)),
            "saturated: {key:?}"
        );
    }
}

#[test]
fn restoring_saturation_exhaustive_three_variable_graphs() {
    // Every directed graph, including self loops, intertwined SCCs and edges out of SCCs.
    for graph in 0..512u16 {
        let base = (0..3)
            .map(|i| {
                Predicate::Equals(
                    Term::variable(variable(i)),
                    tree((0..3).filter(|j| graph & (1 << (i * 3 + j)) != 0)),
                )
            })
            .collect::<Vec<_>>();
        for mask in 0..8 {
            let bindable = (0..3)
                .filter(|i| mask & (1 << i) != 0)
                .map(variable)
                .collect();
            compare(&base, &bindable);
            let mut changed = base.clone();
            changed.reverse();
            changed.push(base[0].clone()); // duplicate key stays a predicate
            changed.push(Predicate::Equals(tree([]), tree([]))); // nonbinding stays in order
            compare(&changed, &bindable);
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(4096))]

    #[test]
    fn restoring_saturation_generated_graphs(
        edges in prop::collection::vec((0usize..8, prop::collection::vec(0usize..8, 0..3)), 0..12),
        mask in any::<u8>(),
    ) {
        // At most eight bound variables, two occurrences per value: expansion <= a small binary tree of height eight.
        let constraints = edges.into_iter().map(|(i, ds)| Predicate::Equals(Term::variable(variable(i)), tree(ds))).collect::<Vec<_>>();
        let bindable = (0..8).filter(|i| mask & (1 << i) != 0).map(variable).collect();
        compare(&constraints, &bindable);
    }

    #[test]
    fn restoring_saturation_all_term_forms(left in generators::term(), right in generators::term(), mask in 0u8..4) {
        // Exactly two candidate keys bounds nested expansion; the shared generator covers all TermKind variants.
        let x = Variable::new("X", left.sort());
        let y = Variable::new("Y", right.sort());
        let constraints = vec![Predicate::Equals(Term::variable(x.clone()), left), Predicate::Equals(Term::variable(y.clone()), right)];
        let bindable = [(1, x), (2, y)].into_iter().filter(|(bit, _)| mask & bit != 0).map(|(_, v)| v).collect();
        compare(&constraints, &bindable);
    }

    #[test]
    fn substitution_locality_and_support(term in generators::term(), replacement in generators::term(), index in 0usize..32) {
        let variables = term.attributes().variables.iter().cloned().collect::<Vec<_>>();
        let key = variables.get(index % variables.len().max(1)).cloned().unwrap_or_else(|| variable(0));
        let substitution = Substitution::from([(key.clone(), replacement.clone())]);
        let result = substitute(&term, &substitution);
        // No variable can appear except an untouched input variable or a replacement variable.
        prop_assert!(result.attributes().variables.iter().all(|v| (v != &key && term.attributes().variables.contains(v)) || replacement.attributes().variables.contains(v)));
        let unused = Variable::new("DefinitelyUnused", Sort::simple("Unused"));
        prop_assert!(!term.attributes().variables.contains(&unused));
        let mut extended = substitution.clone();
        extended.insert(unused, replacement);
        prop_assert_eq!(result, substitute(&term, &extended));
    }
}

#[test]
fn restoring_saturation_preserves_cyclic_callback_inputs() {
    // The schedule optimization does not require acyclicity. Keep cyclic actual-substitute
    // values to aliases/unary terms so this test cannot construct an expanding binary tree.
    for count in 1..=6 {
        let mut original = Substitution::new();
        for i in 0..count {
            let value = if i % 2 == 0 {
                Term::variable(variable((i + 1) % count))
            } else {
                tree([(i + 1) % count])
            };
            original.insert(variable(i), value);
        }
        let mut old = original.clone();
        let mut new = original;
        let mut old_trace = Vec::new();
        let mut new_trace = Vec::new();
        reference_saturate_with(&mut old, |value, others| {
            old_trace.push((value.clone(), others.clone()));
            substitute(value, others)
        });
        saturate_with(&mut new, |value, others| {
            new_trace.push((value.clone(), others.clone()));
            substitute(value, others)
        });
        assert_eq!(old_trace, new_trace);
        assert_eq!(old, new);
    }
}

#[test]
fn restoring_saturation_preserves_large_btree_snapshots() {
    // Cross the BTreeMap node boundary and exercise rebalancing on remove/reinsert.
    // All values are unbound aliases, so the callback cannot expand the input.
    for count in [0, 1, 11, 12, 31, 256] {
        let original = (0..count)
            .map(|i| {
                (
                    variable(i),
                    Term::variable(Variable::new(format!("Outside{i}"), Sort::simple("S"))),
                )
            })
            .collect::<Substitution>();
        let mut old = original.clone();
        let mut new = original;
        let mut old_trace = Vec::new();
        let mut new_trace = Vec::new();
        reference_saturate_with(&mut old, |value, others| {
            old_trace.push((value.clone(), others.clone()));
            substitute(value, others)
        });
        saturate_with(&mut new, |value, others| {
            new_trace.push((value.clone(), others.clone()));
            substitute(value, others)
        });
        assert_eq!(old_trace, new_trace);
        assert_eq!(old, new);
    }
}
