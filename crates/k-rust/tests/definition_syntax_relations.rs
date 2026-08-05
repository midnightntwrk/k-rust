use std::collections::BTreeSet;

use k_rust::definition::{
    Associativity, Attributes, Definition, FlatImport, FlatModule, PartialOrderCycle,
    ResolvedDefinition, Sentence, compute_associativities, compute_priorities,
};

fn priority(blocks: &[&[&str]]) -> Sentence {
    Sentence::SyntaxPriority {
        priorities: blocks
            .iter()
            .map(|block| block.iter().map(|tag| (*tag).into()).collect())
            .collect(),
        attributes: Attributes::default(),
    }
}

fn associativity(associativity: Associativity, tags: &[&str]) -> Sentence {
    Sentence::SyntaxAssociativity {
        associativity,
        tags: tags.iter().map(|tag| (*tag).into()).collect(),
        attributes: Attributes::default(),
    }
}

fn pairs(values: &[(&str, &str)]) -> BTreeSet<(String, String)> {
    values
        .iter()
        .map(|(left, right)| ((*left).into(), (*right).into()))
        .collect()
}

#[test]
fn priorities_connect_adjacent_blocks_and_close_transitively() {
    let sentence = priority(&[&["A", "B"], &["C"], &["D", "E"]]);
    let priorities = compute_priorities([&sentence]).unwrap();

    assert_eq!(
        priorities.direct_relations(),
        &pairs(&[("A", "C"), ("B", "C"), ("C", "D"), ("C", "E")])
    );
    assert!(priorities.less_than(&"A".into(), &"E".into()));
    assert!(!priorities.directly_less_than(&"A".into(), &"E".into()));
}

#[test]
fn empty_priority_blocks_break_the_adjacent_chain() {
    let sentence = priority(&[&["A"], &[], &["B"]]);
    let priorities = compute_priorities([&sentence]).unwrap();
    assert_eq!(priorities.elements().count(), 0);
}

#[test]
fn priorities_reject_self_and_indirect_cycles() {
    let self_cycle = priority(&[&["A"], &["A"]]);
    assert_eq!(
        compute_priorities([&self_cycle]).unwrap_err(),
        PartialOrderCycle {
            path: vec!["A".into(), "A".into()]
        }
    );

    let a_before_b = priority(&[&["A"], &["B"]]);
    let b_before_a = priority(&[&["B"], &["A"]]);
    assert_eq!(
        compute_priorities([&a_before_b, &b_before_a]).unwrap_err(),
        PartialOrderCycle {
            path: vec!["A".into(), "B".into(), "A".into()]
        }
    );
}

#[test]
fn associativity_builds_cartesian_tag_pairs() {
    let left = associativity(Associativity::Left, &["plus", "minus"]);
    let right = associativity(Associativity::Right, &["cons"]);
    let non_assoc = associativity(Associativity::NonAssoc, &["compare"]);
    let unspecified = associativity(Associativity::Unspecified, &["ignored"]);
    let relations = compute_associativities([&left, &right, &non_assoc, &unspecified]);

    assert_eq!(
        relations.left,
        pairs(&[
            ("plus", "plus"),
            ("plus", "minus"),
            ("minus", "plus"),
            ("minus", "minus"),
            ("compare", "compare"),
        ])
    );
    assert_eq!(
        relations.right,
        pairs(&[("cons", "cons"), ("compare", "compare")])
    );
}

#[test]
fn resolved_relations_include_imported_sentences() {
    let base = FlatModule {
        name: "BASE".into(),
        imports: Vec::new(),
        local_sentences: vec![
            priority(&[&["multiply"], &["add"]]),
            associativity(Associativity::Left, &["add"]),
        ],
        attributes: Attributes::default(),
    };
    let main = FlatModule {
        name: "MAIN".into(),
        imports: vec![FlatImport {
            name: "BASE".into(),
            public: true,
        }],
        local_sentences: vec![associativity(Associativity::Right, &["cons"])],
        attributes: Attributes::default(),
    };
    let resolved = ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![main, base],
        attributes: Attributes::default(),
    })
    .unwrap();
    let module = resolved.main_module_id();

    assert!(
        resolved
            .priorities(module)
            .unwrap()
            .less_than(&"multiply".into(), &"add".into())
    );
    assert_eq!(resolved.left_assoc(module), pairs(&[("add", "add")]));
    assert_eq!(resolved.right_assoc(module), pairs(&[("cons", "cons")]));
}
