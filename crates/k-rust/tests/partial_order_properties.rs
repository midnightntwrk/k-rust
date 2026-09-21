use std::collections::{BTreeMap, BTreeSet};

use k_rust::definition::PartialOrder;
use petgraph::algo::has_path_connecting;
use petgraph::graph::DiGraph;
use proptest::prelude::*;

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn closure_matches_reachability(bits in prop::collection::vec(any::<bool>(), 28)) {
        const N: usize = 8;
        let mut bit = 0;
        let mut edges = BTreeSet::new();
        for lesser in 0..N {
            for greater in lesser + 1..N {
                if bits[bit] {
                    edges.insert((lesser, greater));
                }
                bit += 1;
            }
        }

        let order = PartialOrder::new(edges.iter().copied()).unwrap();
        let mut graph = DiGraph::<usize, ()>::new();
        let nodes = (0..N).map(|node| graph.add_node(node)).collect::<Vec<_>>();
        for &(lesser, greater) in &edges {
            graph.add_edge(nodes[lesser], nodes[greater], ());
        }
        let mut reachable = [[false; N]; N];
        for &(lesser, greater) in &edges {
            reachable[lesser][greater] = true;
        }
        for intermediate in 0..N {
            for lesser in 0..N {
                for greater in 0..N {
                    reachable[lesser][greater] |=
                        reachable[lesser][intermediate] && reachable[intermediate][greater];
                }
            }
        }

        for (lesser, row) in reachable.iter().enumerate() {
            for (greater, expected) in row.iter().enumerate() {
                prop_assert_eq!(order.less_than(&lesser, &greater), *expected);
                prop_assert_eq!(
                    order.less_than(&lesser, &greater),
                    lesser != greater
                        && has_path_connecting(&graph, nodes[lesser], nodes[greater], None),
                );
            }
        }

        let positions = order.sorted_elements().iter().enumerate()
            .map(|(index, element)| (*element, index))
            .collect::<BTreeMap<_, _>>();
        for &(lesser, greater) in &edges {
            prop_assert!(positions[&lesser] < positions[&greater]);
        }
    }
}
