//! A definition is the set of sentences of the modules its main module reaches. How many import
//! paths reach a module does not change that set, so a definition and the same definition with
//! a redundant import of a module it already reaches denote the same theory and must load to the
//! same axioms, claims and rules, with the same work.
//!
//! The two fixtures below have the same modules with the same sentences; the only difference is
//! one import line in `R`, which makes `BASE` reachable from `TOP` by two paths instead of one.

const _: () = assert!(cfg!(feature = "measure"));

use k_rust_backend::definition::BackendDefinition;
use k_rust_kore::{
    kore::parser::parse_definition,
    measure::{Snapshot, snapshot},
};

/// `BASE` holds an equation, a rewrite rule and a claim.
const BASE: &str = r#"
module BASE
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    sort SortS{} []
    hooked-symbol plusInt{}(SortInt{}, SortInt{}) : SortInt{}
        [function{}(), total{}(), hook{}("INT.add"), smt-hook{}("+")]
    symbol inc{}(SortInt{}) : SortS{} [constructor{}()]
    symbol f{}(SortInt{}) : SortInt{} [function{}(), total{}()]
    alias weakAlwaysFinally{S}(S) : S where weakAlwaysFinally{S}(@X:S) := @X:S []
    axiom{R} \implies{R}(
        \top{R}(),
        \equals{SortInt{}, R}(
            f{}(N:SortInt{}),
            \and{SortInt{}}(plusInt{}(N:SortInt{}, \dv{SortInt{}}("1")), \top{SortInt{}}())
        )
    ) [label{}("f"), simplification{}()]
    axiom{} \rewrites{SortS{}}(
        \and{SortS{}}(inc{}(N:SortInt{}), \top{SortS{}}()),
        inc{}(f{}(N:SortInt{}))
    ) [label{}("step")]
    claim{} \implies{SortS{}}(
        \and{SortS{}}(inc{}(\dv{SortInt{}}("0")), \top{SortS{}}()),
        weakAlwaysFinally{SortS{}}(inc{}(\dv{SortInt{}}("3")))
    ) [label{}("three")]
endmodule []
"#;

/// `TOP` reaches `BASE` by one path, through `L`.
const CHAIN: &str = r#"
module L
    import BASE []
endmodule []
module R
endmodule []
module TOP
    import L []
    import R []
endmodule []
"#;

/// `TOP` reaches `BASE` by two paths, through `L` and through `R`.
const DIAMOND: &str = r#"
module L
    import BASE []
endmodule []
module R
    import BASE []
endmodule []
module TOP
    import L []
    import R []
endmodule []
"#;

fn load(top: &str) -> (BackendDefinition, Snapshot) {
    let source = format!("[]\n{BASE}{top}");
    let syntax = parse_definition(&source).expect("definition should parse");
    let before = snapshot();
    let definition =
        BackendDefinition::internalize(&syntax, "TOP").expect("definition should internalize");
    (definition, snapshot().delta(&before))
}

#[test]
fn a_redundant_import_path_changes_neither_the_theory_nor_the_work_of_loading_it() {
    // The first load in a process also builds what the backend caches process-wide (one term
    // more in `term.constructed` at `934d29e7`), whichever fixture it loads; a load first, whose
    // work is not compared, keeps that out of the comparison.
    load(CHAIN);
    let (chain, chain_work) = load(CHAIN);
    let (diamond, diamond_work) = load(DIAMOND);
    assert_eq!(chain.modules(), diamond.modules());
    let mut differences = Vec::new();
    let mut compare = |what: &str, one: usize, two: usize| {
        if one != two {
            differences.push(format!("{what}: {one} by one path, {two} by two"));
        }
    };
    compare("axioms", chain.axioms().len(), diamond.axioms().len());
    compare("claims", chain.claims().len(), diamond.claims().len());
    compare(
        "reachability claims",
        chain.reachability_claims().len(),
        diamond.reachability_claims().len(),
    );
    compare(
        "classified axioms",
        chain.classified_axioms().len(),
        diamond.classified_axioms().len(),
    );
    for ((name, one), (_, two)) in chain_work.iter().zip(diamond_work.iter()) {
        compare(name, one as usize, two as usize);
    }
    assert!(
        differences.is_empty(),
        "the redundant import path changed the load: {differences:#?}"
    );
    assert_eq!(diamond.axioms(), chain.axioms());
    assert_eq!(diamond.claims(), chain.claims());
    assert_eq!(diamond.classified_axioms(), chain.classified_axioms());
}
