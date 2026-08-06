use std::collections::BTreeSet;

use k_rust::definition::{PartialOrder, PartialOrderCycle};

fn set(values: impl IntoIterator<Item = &'static str>) -> BTreeSet<&'static str> {
    values.into_iter().collect()
}

#[test]
fn computes_direct_and_transitive_relations() {
    let order = PartialOrder::new([("A", "B"), ("B", "C"), ("A", "C"), ("D", "C")]).unwrap();

    assert!(order.directly_less_than(&"A", &"B"));
    assert!(!order.directly_less_than(&"A", &"D"));
    assert!(order.less_than(&"A", &"C"));
    assert!(order.less_than_eq(&"A", &"A"));
    assert!(order.greater_than(&"C", &"B"));
    assert!(order.in_some_relation(&"C", &"A"));
    assert!(order.in_some_relation_eq(&"A", &"A"));
    assert!(!order.less_than(&"C", &"A"));
    assert_eq!(order.relations_from(&"A"), Some(&set(["B", "C"])));

    let positions = order
        .sorted_elements()
        .iter()
        .enumerate()
        .map(|(index, element)| (*element, index))
        .collect::<std::collections::BTreeMap<_, _>>();
    for (lesser, greater) in order.direct_relations() {
        assert!(positions[lesser] < positions[greater]);
    }
}

#[test]
fn computes_bounds_extrema_and_components() {
    let order = PartialOrder::new([("A", "B"), ("B", "C"), ("D", "C"), ("X", "Y")]).unwrap();

    assert_eq!(order.upper_bounds([&"A", &"B"]), set(["B", "C"]));
    assert_eq!(order.lower_bounds([&"B", &"C"]), set(["A", "B"]));
    assert_eq!(
        order.upper_bounds(std::iter::empty()),
        set(["A", "B", "C", "D", "X", "Y"])
    );
    assert_eq!(order.minimal([&"A", &"B", &"C", &"D"]), set(["A", "D"]));
    assert_eq!(order.maximal([&"A", &"B", &"C", &"D"]), set(["C"]));
    assert_eq!(order.minimum([&"A", &"B", &"C"]), Some("A"));
    assert_eq!(order.minimum([&"A", &"D"]), None);
    assert_eq!(
        order.connected_components(),
        vec![set(["A", "B", "C", "D"]), set(["X", "Y"])]
    );
}

#[test]
fn excludes_isolated_elements_but_keeps_reflexivity() {
    let order = PartialOrder::<&str>::new([]).unwrap();
    assert!(!order.contains(&"isolated"));
    assert!(order.less_than_eq(&"isolated", &"isolated"));
    assert_eq!(order.elements().count(), 0);
}

#[test]
fn rejects_cycles_with_a_closed_path() {
    assert_eq!(
        PartialOrder::new([("A", "B"), ("B", "C"), ("C", "A")]).unwrap_err(),
        PartialOrderCycle {
            path: vec!["A", "B", "C", "A"]
        }
    );
    assert_eq!(
        PartialOrder::new([("A", "A")]).unwrap_err(),
        PartialOrderCycle {
            path: vec!["A", "A"]
        }
    );
}

#[test]
fn equality_uses_the_transitive_relation() {
    let reduced = PartialOrder::new([("A", "B"), ("B", "C")]).unwrap();
    let redundant = PartialOrder::new([("A", "B"), ("B", "C"), ("A", "C")]).unwrap();
    assert_eq!(reduced, redundant);
}
