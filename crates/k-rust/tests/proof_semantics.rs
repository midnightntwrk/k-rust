//! Proof semantics on the KORE krust compiles, checked in-process.
//!
//! What a claim's proof concludes is the backend's contract: the prover's result for a claim of a
//! compiled definition. `cli.rs` checks how `krust kprove` reports these results (verdict lines,
//! exit status) on the same definitions (`support/proof_sources.rs`); the tests here compile each
//! definition as `kprove` does and ask the backend for the result directly, so a change to what
//! the prover concludes fails here, in the backend's terms, and not only through the rendering.
//! The prover decides the implications these results rest on with the backend's Z3 solver
//! (`z3-inference`), as `kprove` does; without it they are not decided.

#![cfg(feature = "z3-inference")]

use k_rust::{
    backend::{Backend, BackendOptions, ProofLeafOutcomeOutput, ProofResultOutput, ProveRequest},
    builtin::embedded,
    definition::CheckMode,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    kore::{codec, printer::Printer},
    outer::{LoadOptions, ResolvedSource, load_with_options},
};

#[path = "support/proof_sources.rs"]
mod proof_sources;
use proof_sources::{
    ANYWHERE_OVERLOAD_REMAINDER, LATER_BINDING_KEPT, LATER_BINDING_RECOVERED, LATER_BINDING_RULE,
    LET_PARTIAL_CONDITION, NEGATIVE_POWER, UNDEFINED_STEP,
};

/// The KORE of `source` compiled for proving `spec` against `definition`, as `kprove` compiles a
/// source: the prelude, the Rust backend's module selection, and claims all-path by default.
fn compile(source: &str, spec: &str, definition: &str) -> String {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("spec.k", source),
        spec,
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            configuration_module: Some(definition.to_owned()),
            ..CompilationBackend::Rust.load_options()
        },
    )
    .unwrap();
    compile_loaded_definition(
        &loaded,
        CompileOptions {
            backend: CompilationBackend::Rust,
            default_claims_to_all_path: true,
            check_mode: CheckMode::Proof {
                definition_module: definition.to_owned(),
            },
            ..CompileOptions::default()
        },
    )
    .unwrap()
    .definition_kore
}

/// The prover's result for the claim `claim` (a label or `#index`) of `spec`.
fn prove(kore: &str, spec: &str, claim: &str, request: ProveRequest) -> ProofResultOutput {
    let mut backend = Backend::new(kore, spec, BackendOptions::default()).unwrap();
    backend
        .prove(ProveRequest {
            claim: Some(claim.to_owned()),
            ..request
        })
        .unwrap_or_else(|error| panic!("{claim}: {error:?}"))
}

fn leaf_text(result: &ProofResultOutput) -> Vec<String> {
    result
        .leaves
        .iter()
        .map(|leaf| Printer::compact().print_pattern(&codec::from_value(&leaf.state).unwrap()))
        .collect()
}

/// Collection cells whose claims write a bare `Bag` variable as a side of a rewrite in the
/// collection's parent cell.
const BARE_BAG_SIDE: &str = r#"
module BARE-SYNTAX
  imports INT-SYNTAX
  syntax Cmd ::= mk(Int) | clr()
  syntax Pgm ::= Cmd | Cmd ";" Pgm
endmodule

module BARE
  imports BARE-SYNTAX
  imports INT
  configuration
    <T>
      <k> $PGM:Pgm </k>
      <rs> <r multiplicity="*" type="$TYPE"> <rid> 0 </rid> </r> </rs>
    </T>

  rule <k> C:Cmd ; P:Pgm => C ~> P ... </k>
  rule <k> mk(I) => .K ... </k> <rs> (.Bag => <r> <rid> I </rid> </r>) ... </rs>
  rule <k> clr() => .K ... </k> <rs> (_:Bag => .Bag) </rs>
endmodule

module BARE-SPEC
  imports BARE
  claim [any]: <k> mk(1) => .K ... </k> <rs> (L:Bag => ?A:Bag) </rs>
  claim [any-bare]: <k> mk(1) => .K ... </k> <rs> L:Bag => ?A:Bag </rs>
  claim [cleared]: <k> mk(1) ; clr() => .K ... </k> <rs> L:Bag => .Bag </rs>
  claim [item-first]: <k> mk(1) => .K ... </k> <rs> (L:Bag => <r> <rid> 1 </rid> </r> ?C:Bag) </rs>
  claim [item-between]: <k> mk(1) => .K ... </k> <rs> (L:Bag => ?A:Bag <r> <rid> 1 </rid> </r> ?C:Bag) </rs>
  claim [item-last]: <k> mk(1) => .K ... </k> <rs> (L:Bag => ?A:Bag <r> <rid> 1 </rid> </r>) </rs>
endmodule
"#;

/// A rewrite at the body of a collection's parent cell, whose sides are cells, `Bag` variables
/// or both, is a rewrite of `Bag`, the sort of a cell body: a side that is only a `Bag`
/// variable is no exception, in a rule (`clr`) and in a claim, parenthesized or as the whole
/// body. The claims are then decided by what they state. `mk` puts its item first in the list,
/// so the state is `<r> 1 </r> L` and the destinations that place the item first (`any`, the
/// existential being that state; `item-first`; `item-between` with `?A` empty) hold of every
/// `L`, while `item-last` holds of none but the empty `L` and is not proven. In a set or a map
/// the item is found without positions, so `item-last` holds as well; there `mk` has no
/// successor where `L` already holds its item, a branch these claims accept as vacuous.
#[test]
fn a_bare_bag_variable_is_a_side_of_a_cell_body_rewrite() {
    let status = |kore: &str, claim: &str| {
        prove(
            kore,
            "BARE-SPEC",
            &format!("BARE-SPEC.{claim}"),
            ProveRequest::default(),
        )
        .status
    };
    let list = compile(&BARE_BAG_SIDE.replace("$TYPE", "List"), "BARE-SPEC", "BARE");
    for claim in ["any", "any-bare", "cleared", "item-first", "item-between"] {
        assert_eq!(status(&list, claim), "proven", "List {claim}");
    }
    assert_ne!(status(&list, "item-last"), "proven", "List item-last");
    for collection in ["Set", "Map"] {
        let kore = compile(
            &BARE_BAG_SIDE.replace("$TYPE", collection),
            "BARE-SPEC",
            "BARE",
        );
        let vacuous = ProveRequest {
            allow_vacuous: true,
            ..ProveRequest::default()
        };
        for claim in ["any", "any-bare", "cleared", "item-first", "item-last"] {
            let result = prove(
                &kore,
                "BARE-SPEC",
                &format!("BARE-SPEC.{claim}"),
                vacuous.clone(),
            );
            assert_eq!(result.status, "proven", "{collection} {claim}");
        }
    }
}

/// A lower-priority rule applies to the remainder of a step as the remainder simplifies, not to
/// the step's subject: the priority-10 rule covers `N <= 0`, and on the remainder `N > 0` the
/// anywhere equation turns `app(N, 0)` into `c(N)`, which the `c` rule rewrites. So the claim
/// is proven in three states whether the overloaded item heads `<k>` or follows another item.
#[test]
fn a_lower_priority_rule_applies_to_the_simplified_remainder() {
    for next in ["", "mark() ~>"] {
        let kore = compile(
            &ANYWHERE_OVERLOAD_REMAINDER.replace("$NEXT", next),
            "OVL-SPEC",
            "OVL",
        );
        let result = prove(&kore, "OVL-SPEC", "#0", ProveRequest::default());
        assert_eq!(
            (
                result.status.as_str(),
                result.explored_states,
                result.unexplored_states
            ),
            ("proven", 3, 0),
            "next item {next:?}: {result:?}"
        );
    }
}

/// The rule binds `X` only in a later argument (`c(X, Y)` is matched against `f(A)`, which no
/// equation evaluates), so the step's condition over `X` is stated under the binding the match
/// leaves, and the claim fails on a `bar` leaf that names no rule variable and no existential.
/// A trusted lemma whose condition is over a variable a set element binds later applies only
/// where the condition holds of the bound value: each lemma is proven, and each main claim,
/// false at `A = 0`, is disproved by a stuck leaf.
#[test]
fn a_claim_condition_over_a_later_binding_is_stated_under_it() {
    for (source, module) in [
        (LATER_BINDING_KEPT, "LEMMAKEPT"),
        (LATER_BINDING_RECOVERED, "LEMMADEF"),
    ] {
        let spec = format!("{module}-SPEC");
        let kore = compile(source, &spec, module);
        let status = |claim: &str| {
            prove(
                &kore,
                &spec,
                &format!("{spec}.{claim}"),
                ProveRequest::default(),
            )
        };
        assert_eq!(status("lemma").status, "proven", "{module}");
        let main = status("main");
        assert_eq!(main.status, "disproved", "{module}: {main:?}");
        assert!(
            main.leaves
                .iter()
                .any(|leaf| leaf.outcome == ProofLeafOutcomeOutput::Stuck),
            "{module}: {main:?}"
        );
    }
}

#[test]
fn a_rule_condition_over_a_later_binding_is_stated_under_it() {
    let kore = compile(LATER_BINDING_RULE, "RULESOLVED-SPEC", "RULESOLVED");
    let result = prove(
        &kore,
        "RULESOLVED-SPEC",
        "RULESOLVED-SPEC.main",
        ProveRequest {
            max_counterexamples: 5,
            ..ProveRequest::default()
        },
    );
    assert_eq!(result.status, "failed", "{result:?}");
    let leaves = leaf_text(&result).join("\n");
    assert!(leaves.contains("Lblbar"), "{leaves}");
    assert!(!leaves.contains("RuleVar"), "{leaves}");
    assert!(!leaves.contains(r"\exists"), "{leaves}");
}

/// `10 /Int A` is undefined at `A = 0`, where the ground claim is disproved, so the symbolic
/// claim, which holds for every instance, is not proven, whether the division is bound by
/// `#let` or not.
#[test]
fn a_let_bound_partial_condition_keeps_its_definedness() {
    for (case, condition) in [
        ("plain", "10 /Int A <=Int 10 /Int A"),
        (
            "let",
            "(#let Y = A #in 10 /Int Y) <=Int (#let Y = A #in 10 /Int Y)",
        ),
    ] {
        let kore = compile(
            &LET_PARTIAL_CONDITION.replace("$CONDITION", condition),
            "LETDIV-SPEC",
            "LETDIV",
        );
        let status =
            |claim: &str| prove(&kore, "LETDIV-SPEC", claim, ProveRequest::default()).status;
        assert_ne!(status("LETDIV-SPEC.symbolic"), "proven", "{case}");
        assert_eq!(status("LETDIV-SPEC.ground"), "disproved", "{case}");
    }
}

/// A claim holds for every instance of its left-hand side, so a symbolic claim is not proven
/// while one of its instances ends in an undefined step (`apart(0, 0)`, whose `ensures` fails),
/// and allowing vacuous results accepts every claim. An instance a sibling rule takes to a
/// defined result (`cover`) and an `ensures` that always has a witness (`fresh`) leave no
/// undefined step. One-path, the instances where a rule applies but its result is undefined go to
/// the later rules of the same priority (`cover`, `skip` proven), never to a lower priority
/// (`low` fails), and fail where no rule of the priority gives a defined result (`pick`).
#[test]
fn a_claim_fails_on_the_instances_a_rule_leaves_undefined() {
    let kore = compile(UNDEFINED_STEP, "UNDEF-SPEC", "UNDEF");
    let status = |claim: &str, allow_vacuous: bool| {
        prove(
            &kore,
            "UNDEF-SPEC",
            &format!("UNDEF-SPEC.{claim}"),
            ProveRequest {
                allow_vacuous,
                ..ProveRequest::default()
            },
        )
    };
    for claim in [
        "sym", "gnd", "sym-one", "pick", "pick-one", "low-one", "low",
    ] {
        let result = status(claim, false);
        assert_eq!(result.status, "failed", "{claim}: {result:?}");
        assert!(
            result
                .leaves
                .iter()
                .any(|leaf| leaf.outcome == ProofLeafOutcomeOutput::Trivial),
            "{claim}: {result:?}"
        );
        assert_eq!(
            status(claim, true).status,
            "proven",
            "{claim} allowing vacuous results"
        );
    }
    for claim in [
        "defined",
        "cover",
        "fresh",
        "fresh-one",
        "cover-one",
        "skip-one",
        "skip",
    ] {
        assert_eq!(status(claim, false).status, "proven", "{claim}");
    }
}

/// `3 ^%Int B 7` is undefined for every negative `B` (no integer is `3 ^Int B`), so `gm(B)` takes
/// the `owise` rule there: the claim that it reaches `yes` for every negative `B` is not proven,
/// whatever value a solver's own power gives, and the claim that `-1` reaches `no` is.
#[test]
fn a_power_no_integer_is_the_value_of_proves_nothing() {
    let kore = compile(NEGATIVE_POWER, "NEGPOW-SPEC", "NEGPOW");
    let status = |claim: &str| prove(&kore, "NEGPOW-SPEC", claim, ProveRequest::default()).status;
    assert_ne!(status("NEGPOW-SPEC.negative"), "proven");
    assert_eq!(status("NEGPOW-SPEC.minus-one"), "proven");
}

/// `JUMPI` on `bool2Word(X <Int 0)` branches on the sign of `X`. The claim whose target `<pc>`
/// is the `#if` of that condition is proven, with or without a lemma about `bool2Word`, and each
/// claim that fixes one target `<pc>` fails on the other branch: `bool2Word` has no solver
/// translation, so the failing leaf is non-empty only modulo that abstraction and the claim
/// fails without being disproved.
#[test]
fn an_implication_through_an_untranslated_function_splits_on_its_condition() {
    const ITE: &str = include_str!("fixtures/reference/implication/ite-bug/ite-bug.k");
    const ITE_NO_LEMMA: &str =
        include_str!("fixtures/reference/implication/ite-bug/nolemma/ite-bug.k");
    let cases = [
        (
            ITE,
            include_str!("fixtures/reference/implication/ite-bug/passing-spec.k"),
            "PASSING-SPEC",
            "proven",
        ),
        (
            ITE,
            include_str!("fixtures/reference/implication/ite-bug/failing-1-spec.k"),
            "FAILING-1-SPEC",
            "failed",
        ),
        (
            ITE,
            include_str!("fixtures/reference/implication/ite-bug/failing-2-spec.k"),
            "FAILING-2-SPEC",
            "failed",
        ),
        (
            ITE_NO_LEMMA,
            include_str!("fixtures/reference/implication/ite-bug/nolemma/passing-spec.k"),
            "PASSING-SPEC",
            "proven",
        ),
    ];
    for (definition, spec_text, spec, status) in cases {
        let kore = compile(&format!("{definition}\n{spec_text}"), spec, "ITE-BUG");
        let result = prove(
            &kore,
            spec,
            "#0",
            ProveRequest {
                max_depth: Some(10),
                ..ProveRequest::default()
            },
        );
        assert_eq!(result.status, status, "{spec}: {result:?}");
    }
}

/// Cells `<r>` of a `multiplicity="*"` collection of type `$TYPE`, which `mk` adds at the front of
/// a list and `mkBack` at its back. The claims' right sides place an instance between parts of
/// the collection (`?A <r> … </r> ?C`), or before one part (`one`, `one-rest`, `absent`).
const COLLECTION_CELL_ITEM_ANYWHERE: &str = r#"
module LCELL-SYNTAX
  imports INT-SYNTAX
  syntax Cmd ::= mk(Int) | mkBack(Int)
  syntax Pgm ::= Cmd | Cmd ";" Pgm
endmodule

module LCELL
  imports LCELL-SYNTAX
  imports INT
  configuration
    <T>
      <k> $PGM:Pgm </k>
      <rs> <r multiplicity="*" type="$TYPE"> <rid> 0 </rid> </r> </rs>
    </T>

  rule <k> C:Cmd ; P:Pgm => C ~> P ... </k>
  rule <k> mk(I) => .K ... </k> <rs> (.Bag => <r> <rid> I </rid> </r>) ... </rs>
  rule <k> mkBack(I) => .K ... </k> <rs> B:Bag (.Bag => <r> <rid> I </rid> </r>) </rs>
endmodule

module LCELL-SPEC
  imports LCELL
  imports BOOL
  claim [one]: <k> mk(1) => .K ... </k> <rs> (<r> <rid> 0 </rid> </r> L:Bag => <r> <rid> 1 </rid> </r> ?C:Bag) </rs>
  claim [front]: <k> mk(1) => .K ... </k> <rs> (<r> <rid> 0 </rid> </r> L:Bag => ?A:Bag <r> <rid> 1 </rid> </r> ?C:Bag) </rs>
  claim [middle-concrete]: <k> mk(2) ; mk(3) => .K ... </k> <rs> (<r> <rid> 1 </rid> </r> => ?A:Bag <r> <rid> 2 </rid> </r> ?C:Bag) </rs>
  claim [after-segment]: <k> mkBack(5) => .K ... </k> <rs> (<r> <rid> 0 </rid> </r> L:Bag => ?A:Bag <r> <rid> 5 </rid> </r> ?C:Bag) </rs>
  claim [before-segment]: <k> mk(7) ; mkBack(5) => .K ... </k> <rs> (<r> <rid> 0 </rid> </r> L:Bag => ?A:Bag <r> <rid> 0 </rid> </r> ?C:Bag) </rs>
  claim [two-items]: <k> mk(2) ; mk(3) => .K ... </k> <rs> (<r> <rid> 1 </rid> </r> => ?A:Bag <r> <rid> 3 </rid> </r> ?B:Bag <r> <rid> 1 </rid> </r> ?C:Bag) </rs>
  claim [absent-closed]: <k> mk(2) ; mk(3) => .K ... </k> <rs> (<r> <rid> 1 </rid> </r> => ?A:Bag <r> <rid> 9 </rid> </r> ?C:Bag) </rs>
  claim [absent-open]: <k> mk(2) => .K ... </k> <rs> (<r> <rid> 0 </rid> </r> L:Bag => ?A:Bag <r> <rid> 9 </rid> </r> ?C:Bag) </rs>
  claim [wrong-order]: <k> mk(2) ; mk(3) => .K ... </k> <rs> (<r> <rid> 1 </rid> </r> => ?A:Bag <r> <rid> 1 </rid> </r> ?B:Bag <r> <rid> 3 </rid> </r> ?C:Bag) </rs>
  claim [symbolic-item]: <k> mk(N:Int) => .K ... </k> <rs> (<r> <rid> 1 </rid> </r> => ?A:Bag <r> <rid> 5 </rid> </r> ?C:Bag) </rs> requires N >Int 4 andBool N <Int 6
  claim [one-rest]: <k> mk(2) ; mk(3) => .K ... </k> <rs> (<r> <rid> 1 </rid> </r> => <r> <rid> 2 </rid> </r> ?C:Bag) </rs>
  claim [absent]: <k> mk(2) ; mk(3) => .K ... </k> <rs> (<r> <rid> 1 </rid> </r> => <r> <rid> 9 </rid> </r> ?C:Bag) </rs>
endmodule
"#;

/// A list is a finite sequence and concatenation is associative, so `?A <r> X </r> ?C` denotes
/// the lists that hold `<r> X </r>` anywhere: a final list that holds it at a known position is
/// one of them, whatever the opaque part `L` beside it is (`front`, `after-segment`,
/// `before-segment`), and two items are found in their written order (`two-items`). Every
/// element of a list without a part is at a known position, so an item at none of them
/// (`absent-closed`) and two items in the other order (`wrong-order`) disprove those claims,
/// while an item absent from the known items may be in `L` (`absent-open`), which leaves that
/// claim unproven. A state item that may be the destination's item keeps its position, and the
/// claim's condition decides it (`symbolic-item`: `N` is `5`, though not written so). In a set
/// or a map, where an item beside a part is decided without positions, an instance with a part
/// (`one-rest`) is found and an absent one is not.
#[test]
fn a_claim_finds_a_collection_cell_instance_between_two_parts_at_any_position() {
    let status = |kore: &str, claim: &str| {
        prove(
            kore,
            "LCELL-SPEC",
            &format!("LCELL-SPEC.{claim}"),
            ProveRequest::default(),
        )
        .status
    };
    let list = compile(
        &COLLECTION_CELL_ITEM_ANYWHERE.replace("$TYPE", "List"),
        "LCELL-SPEC",
        "LCELL",
    );
    for claim in [
        "one",
        "front",
        "middle-concrete",
        "after-segment",
        "before-segment",
        "two-items",
        "symbolic-item",
    ] {
        assert_eq!(status(&list, claim), "proven", "List {claim}");
    }
    for claim in ["absent-closed", "wrong-order"] {
        assert_eq!(status(&list, claim), "disproved", "List {claim}");
    }
    // Not disproved either: `L` may hold the instance.
    assert_eq!(status(&list, "absent-open"), "failed", "List absent-open");

    for collection in ["Set", "Map"] {
        let kore = compile(
            &COLLECTION_CELL_ITEM_ANYWHERE.replace("$TYPE", collection),
            "LCELL-SPEC",
            "LCELL",
        );
        assert_eq!(status(&kore, "one-rest"), "proven", "{collection} one-rest");
        assert_ne!(status(&kore, "absent"), "proven", "{collection} absent");
    }
}

/// Claims over the collection of [`COLLECTION_CELL_ITEM_ANYWHERE`] (its definition, with this
/// spec module) whose destinations place 0 to 3 items beside two or three existential parts;
/// `mk(2) ; mk(3)` takes `<r> 1 </r>` to the instances 1, 2 and 3. The `absent-` claims name an
/// instance 9 that is not among them.
const AC_FRAMES_SPEC: &str = r#"
module AC-SPEC
  imports LCELL
  claim [none-two]: <k> mk(2) ; mk(3) => .K ... </k> <rs> (<r> <rid> 1 </rid> </r> => ?A:Bag ?C:Bag) </rs>
  claim [none-three]: <k> mk(2) ; mk(3) => .K ... </k> <rs> (<r> <rid> 1 </rid> </r> => ?A:Bag ?B:Bag ?C:Bag) </rs>
  claim [one-two]: <k> mk(2) ; mk(3) => .K ... </k> <rs> (<r> <rid> 1 </rid> </r> => ?A:Bag <r> <rid> 2 </rid> </r> ?C:Bag) </rs>
  claim [one-three]: <k> mk(2) ; mk(3) => .K ... </k> <rs> (<r> <rid> 1 </rid> </r> => ?A:Bag <r> <rid> 2 </rid> </r> ?B:Bag ?C:Bag) </rs>
  claim [two-two]: <k> mk(2) ; mk(3) => .K ... </k> <rs> (<r> <rid> 1 </rid> </r> => <r> <rid> 3 </rid> </r> ?A:Bag <r> <rid> 1 </rid> </r> ?C:Bag) </rs>
  claim [two-three]: <k> mk(2) ; mk(3) => .K ... </k> <rs> (<r> <rid> 1 </rid> </r> => ?A:Bag <r> <rid> 1 </rid> </r> ?B:Bag <r> <rid> 3 </rid> </r> ?C:Bag) </rs>
  claim [three-three]: <k> mk(2) ; mk(3) => .K ... </k> <rs> (<r> <rid> 1 </rid> </r> => ?A:Bag <r> <rid> 3 </rid> </r> <r> <rid> 1 </rid> </r> ?B:Bag <r> <rid> 2 </rid> </r> ?C:Bag) </rs>
  claim [absent-one-two]: <k> mk(2) ; mk(3) => .K ... </k> <rs> (<r> <rid> 1 </rid> </r> => ?A:Bag <r> <rid> 9 </rid> </r> ?C:Bag) </rs>
  claim [absent-one-three]: <k> mk(2) ; mk(3) => .K ... </k> <rs> (<r> <rid> 1 </rid> </r> => ?A:Bag <r> <rid> 9 </rid> </r> ?B:Bag ?C:Bag) </rs>
  claim [absent-two-two]: <k> mk(2) ; mk(3) => .K ... </k> <rs> (<r> <rid> 1 </rid> </r> => <r> <rid> 3 </rid> </r> ?A:Bag <r> <rid> 9 </rid> </r> ?C:Bag) </rs>
  claim [absent-two-three]: <k> mk(2) ; mk(3) => .K ... </k> <rs> (<r> <rid> 1 </rid> </r> => ?A:Bag <r> <rid> 2 </rid> </r> ?B:Bag <r> <rid> 9 </rid> </r> ?C:Bag) </rs>
endmodule
"#;

/// Set and map concatenation is associative and commutative with the empty collection as unit,
/// so existential parts beside a set's or a map's items that occur nowhere else stand together
/// for their union, which is one part: any collection disjoint from the items. A destination
/// with two or three such parts and 0 to 3 items therefore holds exactly when its items are
/// instances of the final state, in any order (`two-three` writes 1 before 3), with any split of
/// the other instances between the parts as witness, all of them empty where every instance is
/// an item (`three-three`). An item that is no instance (`absent-`)
/// still leaves its claim unproven.
#[test]
fn existential_parts_beside_set_or_map_items_are_one_part() {
    let definition = &COLLECTION_CELL_ITEM_ANYWHERE[..COLLECTION_CELL_ITEM_ANYWHERE
        .find("module LCELL-SPEC")
        .unwrap()];
    for collection in ["Set", "Map"] {
        let kore = compile(
            &format!("{definition}{AC_FRAMES_SPEC}").replace("$TYPE", collection),
            "AC-SPEC",
            "LCELL",
        );
        let status = |claim: &str| {
            prove(
                &kore,
                "AC-SPEC",
                &format!("AC-SPEC.{claim}"),
                ProveRequest::default(),
            )
            .status
        };
        for claim in [
            "none-two",
            "none-three",
            "one-two",
            "one-three",
            "two-two",
            "two-three",
            "three-three",
        ] {
            assert_eq!(status(claim), "proven", "{collection} {claim}");
        }
        for claim in [
            "absent-one-two",
            "absent-one-three",
            "absent-two-two",
            "absent-two-three",
        ] {
            assert_ne!(status(claim), "proven", "{collection} {claim}");
        }
    }
}

/// A set `<s>` and a map `<m>` that `add` fills, and a set `<u>`, a map `<n>` and an integer `<c>`
/// beside them that no rule changes. The `-bound` claims name a part of `<s>` or `<m>` in `<u>`
/// or `<n>` too, the `-constrained` claims in their `ensures`, the `-sized` claims in a function
/// application in `<c>`.
const AC_FRAMES_ELSEWHERE: &str = r#"
module PAC-SYNTAX
  imports INT-SYNTAX
  syntax Cmd ::= add(Int)
  syntax Pgm ::= Cmd | Cmd ";" Pgm
endmodule

module PAC
  imports PAC-SYNTAX
  imports INT
  imports SET
  imports MAP
  imports BOOL
  configuration <T> <k> $PGM:Pgm </k> <s> .Set </s> <u> .Set </u> <m> .Map </m> <n> .Map </n> <c> 1 </c> </T>
  rule <k> C:Cmd ; P:Pgm => C ~> P ... </k>
  rule <k> add(I) => .K ... </k> <s> S => S SetItem(I) </s> <m> M => M[I <- I] </m> requires notBool I in S
endmodule

module PAC-SPEC
  imports PAC
  claim [set-none]: <k> add(1) ; add(2) ; add(3) => .K ... </k> <s> .Set => ?A:Set ?C:Set </s> <m> .Map => ?M:Map </m>
  claim [set-free]: <k> add(1) ; add(2) ; add(3) => .K ... </k> <s> .Set => ?A:Set SetItem(2) ?C:Set </s> <m> .Map => ?M:Map </m>
  claim [set-bound]: <k> add(1) ; add(2) ; add(3) => .K ... </k> <s> .Set => ?A:Set SetItem(2) ?C:Set </s> <m> .Map => ?M:Map </m> <u> SetItem(9) => ?C </u>
  claim [set-constrained]: <k> add(1) ; add(2) ; add(3) => .K ... </k> <s> .Set => ?A:Set SetItem(2) ?C:Set </s> <m> .Map => ?M:Map </m> ensures 1 in ?C
  claim [map-none]: <k> add(1) ; add(2) ; add(3) => .K ... </k> <s> .Set => ?S:Set </s> <m> .Map => ?A:Map ?B:Map ?C:Map </m>
  claim [map-free]: <k> add(1) ; add(2) ; add(3) => .K ... </k> <s> .Set => ?S:Set </s> <m> .Map => ?A:Map 2 |-> 2 ?C:Map </m>
  claim [map-bound]: <k> add(1) ; add(2) ; add(3) => .K ... </k> <s> .Set => ?S:Set </s> <m> .Map => ?A:Map 2 |-> 2 ?C:Map </m> <n> 9 |-> 9 => ?C </n>
  claim [map-constrained]: <k> add(1) ; add(2) ; add(3) => .K ... </k> <s> .Set => ?S:Set </s> <m> .Map => ?A:Map 2 |-> 2 ?C:Map </m> ensures 1 in_keys(?C)
  claim [set-sized]: <k> add(1) ; add(2) ; add(3) => .K ... </k> <s> .Set => ?A:Set SetItem(2) ?C:Set </s> <m> .Map => ?M:Map </m> <c> 1 => size(?C) </c>
  claim [map-sized]: <k> add(1) ; add(2) ; add(3) => .K ... </k> <s> .Set => ?S:Set </s> <m> .Map => ?A:Map 2 |-> 2 ?C:Map </m> <c> 1 => size(?C) </c>
endmodule
"#;

/// Parts are one part only when the destination states nothing else of them. A part that the
/// destination also names elsewhere is not free to take the whole remainder: in `-bound` it is
/// `<u>`'s or `<n>`'s `9`, which no split of 1 and 3 holds, so the claim is not proven; in
/// `-constrained` it must hold 1, which the split with 1 in it does, so the claim holds and is
/// not disproved (no split is tried, so it is left unproven); in `-sized` it must have one
/// element, which the split with 1 or 3 alone in it has, so that claim holds and is not disproved
/// either. The parts of a plain set or map value with no item, or beside one, are one part as in
/// a cell collection.
#[test]
fn a_part_named_elsewhere_in_the_destination_is_not_merged() {
    let kore = compile(AC_FRAMES_ELSEWHERE, "PAC-SPEC", "PAC");
    let status = |claim: &str| {
        prove(
            &kore,
            "PAC-SPEC",
            &format!("PAC-SPEC.{claim}"),
            ProveRequest::default(),
        )
        .status
    };
    for claim in ["set-none", "set-free", "map-none", "map-free"] {
        assert_eq!(status(claim), "proven", "{claim}");
    }
    for claim in ["set-bound", "map-bound"] {
        assert_ne!(status(claim), "proven", "{claim}");
    }
    for claim in [
        "set-constrained",
        "map-constrained",
        "set-sized",
        "map-sized",
    ] {
        assert_eq!(status(claim), "failed", "{claim}");
    }
}

/// Claims over the collection of [`COLLECTION_CELL_ITEM_ANYWHERE`] (its definition, with this
/// spec module) whose new instances have a symbolic identifier: `N` in (4, 6) is 5 alone, and
/// `M` in (6, 8) is 7 alone.
const AC_SYMBOLIC_SPEC: &str = r#"
module ACS-SPEC
  imports LCELL
  imports BOOL
  claim [sym-one]: <k> mk(N:Int) => .K </k> <rs> (<r> <rid> 1 </rid> </r> => <r> <rid> 5 </rid> </r> ?C:Bag) </rs> requires N >Int 4 andBool N <Int 6
  claim [sym-two]: <k> mk(N:Int) => .K </k> <rs> (<r> <rid> 1 </rid> </r> => ?A:Bag <r> <rid> 5 </rid> </r> ?C:Bag) </rs> requires N >Int 4 andBool N <Int 6
  claim [two-sym]: <k> mk(N:Int) ; mk(M:Int) => .K </k> <rs> (<r> <rid> 1 </rid> </r> => ?A:Bag <r> <rid> 7 </rid> </r> ?C:Bag) </rs> requires N >Int 4 andBool N <Int 6 andBool M >Int 6 andBool M <Int 8
  claim [two-sym-both]: <k> mk(N:Int) ; mk(M:Int) => .K </k> <rs> (<r> <rid> 1 </rid> </r> => <r> <rid> 7 </rid> </r> ?A:Bag <r> <rid> 5 </rid> </r> ?C:Bag) </rs> requires N >Int 4 andBool N <Int 6 andBool M >Int 6 andBool M <Int 8
  claim [sym-wide]: <k> mk(N:Int) => .K </k> <rs> (<r> <rid> 1 </rid> </r> => ?A:Bag <r> <rid> 5 </rid> </r> ?C:Bag) </rs> requires N >Int 4 andBool N <Int 7
  claim [two-sym-absent]: <k> mk(N:Int) ; mk(M:Int) => .K </k> <rs> (<r> <rid> 1 </rid> </r> => ?A:Bag <r> <rid> 6 </rid> </r> ?C:Bag) </rs> requires N >Int 4 andBool N <Int 6 andBool M >Int 6 andBool M <Int 8
  claim [sym-closed]: <k> mk(N:Int) => .K </k> <rs> (<r> <rid> 1 </rid> </r> => <r> <rid> 5 </rid> </r>) </rs> requires N >Int 4 andBool N <Int 6
endmodule
"#;

/// A set or map whose items are all known (no opaque part) is defined on each instance, so its
/// items are pairwise distinct there; a destination with items beside at most one part equals it
/// exactly when each destination item is a distinct one of them and the part holds the others.
/// An item whose identifier is symbolic is a case split on the identifier's equations with the
/// destination's items: `sym-` holds because `N` is 5 on every instance, with one part or with
/// the two parts read as one, and `two-sym-` because `M` is 7, whichever of `N` and `M` the
/// destination's 7 is compared with first. A claim where some instance lacks the item
/// (`sym-wide`, where `N` may be 6, and `two-sym-absent`) or holds one more (`sym-closed`, which
/// leaves out the instance 1) is not proven.
#[test]
fn a_set_or_map_item_with_a_symbolic_identifier_is_found_by_its_equations() {
    let definition = &COLLECTION_CELL_ITEM_ANYWHERE[..COLLECTION_CELL_ITEM_ANYWHERE
        .find("module LCELL-SPEC")
        .unwrap()];
    for collection in ["Set", "Map"] {
        let kore = compile(
            &format!("{definition}{AC_SYMBOLIC_SPEC}").replace("$TYPE", collection),
            "ACS-SPEC",
            "LCELL",
        );
        let status = |claim: &str| {
            prove(
                &kore,
                "ACS-SPEC",
                &format!("ACS-SPEC.{claim}"),
                ProveRequest::default(),
            )
            .status
        };
        for claim in ["sym-one", "sym-two", "two-sym", "two-sym-both"] {
            assert_eq!(status(claim), "proven", "{collection} {claim}");
        }
        for claim in ["sym-wide", "two-sym-absent", "sym-closed"] {
            let status = status(claim);
            assert!(
                matches!(status.as_str(), "failed" | "disproved"),
                "{collection} {claim}: {status}"
            );
        }
    }
}

/// Claims over the plain set `<s>` and map `<m>` of [`AC_FRAMES_ELSEWHERE`] (its definition, with
/// this spec module) that add a symbolic `N`, which is 5 alone in (4, 6).
const PAC_SYMBOLIC_SPEC: &str = r#"
module PACS-SPEC
  imports PAC
  claim [set-sym-one]: <k> add(N:Int) => .K </k> <s> .Set => SetItem(5) ?C:Set </s> <m> .Map => ?M:Map </m> requires N >Int 4 andBool N <Int 6
  claim [set-sym-two]: <k> add(N:Int) => .K </k> <s> .Set => ?A:Set SetItem(5) ?C:Set </s> <m> .Map => ?M:Map </m> requires N >Int 4 andBool N <Int 6
  claim [map-sym-one]: <k> add(N:Int) => .K </k> <s> .Set => ?S:Set </s> <m> .Map => 5 |-> 5 ?C:Map </m> requires N >Int 4 andBool N <Int 6
  claim [map-sym-two]: <k> add(N:Int) => .K </k> <s> .Set => ?S:Set </s> <m> .Map => ?A:Map 5 |-> 5 ?C:Map </m> requires N >Int 4 andBool N <Int 6
  claim [set-sym-wide]: <k> add(N:Int) => .K </k> <s> .Set => ?A:Set SetItem(5) ?C:Set </s> <m> .Map => ?M:Map </m> requires N >Int 4 andBool N <Int 7
  claim [map-sym-wide]: <k> add(N:Int) => .K </k> <s> .Set => ?S:Set </s> <m> .Map => ?A:Map 5 |-> 5 ?C:Map </m> requires N >Int 4 andBool N <Int 7
  claim [map-sym-value]: <k> add(N:Int) => .K </k> <s> .Set => ?S:Set </s> <m> .Map => ?A:Map 5 |-> 6 ?C:Map </m> requires N >Int 4 andBool N <Int 6
endmodule
"#;

/// The proof status of each of `claims` of `spec`, a module of the given source over
/// [`AC_FRAMES_ELSEWHERE`]'s definition.
fn pac_statuses(spec: &str, module: &str, claims: &[&str]) -> Vec<(String, String)> {
    let definition = &AC_FRAMES_ELSEWHERE[..AC_FRAMES_ELSEWHERE.find("module PAC-SPEC").unwrap()];
    let kore = compile(&format!("{definition}{spec}"), module, "PAC");
    claims
        .iter()
        .map(|claim| {
            let status = prove(
                &kore,
                module,
                &format!("{module}.{claim}"),
                ProveRequest::default(),
            )
            .status;
            ((*claim).to_owned(), status)
        })
        .collect()
}

/// The symbolic item of a plain set or map is found by its equations as a collection cell's is:
/// `N` is 5 on every instance, with one part or with the two parts read as one. A claim where
/// `N` may be 6 (`-wide`), or where the map's value is not `N`, is not proven.
#[test]
fn a_plain_set_or_map_item_with_a_symbolic_value_is_found_by_its_equations() {
    let proven = ["set-sym-one", "set-sym-two", "map-sym-one", "map-sym-two"];
    let unproven = ["set-sym-wide", "map-sym-wide", "map-sym-value"];
    let statuses = pac_statuses(
        PAC_SYMBOLIC_SPEC,
        "PACS-SPEC",
        &[proven.as_slice(), unproven.as_slice()].concat(),
    );
    for (claim, status) in statuses {
        if proven.contains(&claim.as_str()) {
            assert_eq!(status, "proven", "{claim}");
        } else {
            assert!(
                matches!(status.as_str(), "failed" | "disproved"),
                "{claim}: {status}"
            );
        }
    }
}

/// Claims over the plain set `<s>` and map `<m>` of [`AC_FRAMES_ELSEWHERE`] (its definition, with
/// this spec module) that end in a disjunction of two destinations for `<s>` or `<m>`; the
/// `-sym-` claims add a symbolic `N` in (4, 7), which is 5 or 6.
const PAC_DISJUNCTIVE_SPEC: &str = r#"
module PACD-SPEC
  imports PAC
  claim [set-or-two]: <k> add(1) ; add(2) ; add(3) => .K </k> <s> .Set => (?A:Set SetItem(2) ?C:Set) #Or (SetItem(9) ?D:Set) </s> <m> .Map => ?M:Map </m>
  claim [map-or-two]: <k> add(1) ; add(2) ; add(3) => .K </k> <s> .Set => ?S:Set </s> <m> .Map => (?A:Map 2 |-> 2 ?C:Map) #Or (9 |-> 9 ?D:Map) </m>
  claim [set-or-sym-one]: <k> add(N:Int) => .K </k> <s> .Set => (SetItem(5) ?C:Set) #Or (SetItem(6) ?D:Set) </s> <m> .Map => ?M:Map </m> requires N >Int 4 andBool N <Int 7
  claim [set-or-sym-two]: <k> add(N:Int) => .K </k> <s> .Set => (?A:Set SetItem(5) ?C:Set) #Or (?B:Set SetItem(6) ?D:Set) </s> <m> .Map => ?M:Map </m> requires N >Int 4 andBool N <Int 7
  claim [map-or-sym-two]: <k> add(N:Int) => .K </k> <s> .Set => ?S:Set </s> <m> .Map => (?A:Map 5 |-> 5 ?C:Map) #Or (?B:Map 6 |-> 6 ?D:Map) </m> requires N >Int 4 andBool N <Int 7
  claim [set-or-absent]: <k> add(1) ; add(2) ; add(3) => .K </k> <s> .Set => (?A:Set SetItem(9) ?C:Set) #Or (?B:Set SetItem(8) ?D:Set) </s> <m> .Map => ?M:Map </m>
  claim [map-or-absent]: <k> add(1) ; add(2) ; add(3) => .K </k> <s> .Set => ?S:Set </s> <m> .Map => (?A:Map 9 |-> 9 ?C:Map) #Or (?B:Map 2 |-> 3 ?D:Map) </m>
  claim [set-or-sym-wide]: <k> add(N:Int) => .K </k> <s> .Set => (?A:Set SetItem(5) ?C:Set) #Or (?B:Set SetItem(6) ?D:Set) </s> <m> .Map => ?M:Map </m> requires N >Int 4 andBool N <Int 8
  claim [set-or-bound]: <k> add(1) ; add(2) ; add(3) => .K </k> <s> .Set => (?A:Set SetItem(2) ?C:Set) #Or (SetItem(9) ?D:Set) </s> <m> .Map => ?M:Map </m> <u> SetItem(9) => ?C </u>
endmodule
"#;

/// A disjunctive destination holds where on each instance one of its disjuncts does, each
/// disjunct decided as a destination alone: its parts beside items read as one part
/// (`-or-two`, as `set-free` and `map-free` in [`AC_FRAMES_ELSEWHERE`]) and its symbolic items
/// split by their equations, so `-or-sym-` holds by its first disjunct where `N` is 5 and by its
/// second where `N` is 6, neither of which holds alone. Neither disjunct holds in `-or-absent`,
/// the instance 7 of `set-or-sym-wide` is in neither, and in `set-or-bound` the part `<u>` names
/// must be 9, which no split of the final set has, so those are not proven.
#[test]
fn a_disjunctive_set_or_map_destination_is_decided_disjunct_by_disjunct() {
    let proven = [
        "set-or-two",
        "map-or-two",
        "set-or-sym-one",
        "set-or-sym-two",
        "map-or-sym-two",
    ];
    let unproven = [
        "set-or-absent",
        "map-or-absent",
        "set-or-sym-wide",
        "set-or-bound",
    ];
    let statuses = pac_statuses(
        PAC_DISJUNCTIVE_SPEC,
        "PACD-SPEC",
        &[proven.as_slice(), unproven.as_slice()].concat(),
    );
    for (claim, status) in statuses {
        if proven.contains(&claim.as_str()) {
            assert_eq!(status, "proven", "{claim}");
        } else {
            assert!(
                matches!(status.as_str(), "failed" | "disproved"),
                "{claim}: {status}"
            );
        }
    }
}

/// Claims whose destination item is an existential that the `ensures` constrains, over the plain
/// set `<s>` and map `<m>` of [`AC_FRAMES_ELSEWHERE`] (its definition, with this spec module).
const PAC_EXISTENTIAL_ITEM_SPEC: &str = r#"
module PACX-SPEC
  imports PAC
  claim [set-ex]: <k> add(1) ; add(5) => .K </k> <s> .Set => SetItem(?X:Int) ?C:Set </s> <m> .Map => ?M:Map </m> ensures ?X >Int 3
  claim [map-ex]: <k> add(1) ; add(5) => .K </k> <s> .Set => ?S:Set </s> <m> .Map => ?K:Int |-> ?V:Int ?C:Map </m> ensures ?V >Int 3
  claim [set-ex-none]: <k> add(1) ; add(2) => .K </k> <s> .Set => SetItem(?X:Int) ?C:Set </s> <m> .Map => ?M:Map </m> ensures ?X >Int 3
  claim [map-ex-none]: <k> add(1) ; add(2) => .K </k> <s> .Set => ?S:Set </s> <m> .Map => ?K:Int |-> ?V:Int ?C:Map </m> ensures ?V >Int 3
endmodule
"#;

/// The same over the collection of [`COLLECTION_CELL_ITEM_ANYWHERE`], whose new instances have
/// the symbolic identifiers `N`, 5 alone in (4, 6), and `M`, 7 alone in (6, 8).
const AC_EXISTENTIAL_ITEM_SPEC: &str = r#"
module ACX-SPEC
  imports LCELL
  imports BOOL
  claim [ex-two]: <k> mk(N:Int) ; mk(M:Int) => .K </k> <rs> (<r> <rid> 1 </rid> </r> => <r> <rid> ?X:Int </rid> </r> <r> <rid> ?Y:Int </rid> </r> ?C:Bag) </rs> requires N >Int 4 andBool N <Int 6 andBool M >Int 6 andBool M <Int 8 ensures ?X >Int ?Y andBool ?Y >Int 4
  claim [ex-two-none]: <k> mk(N:Int) ; mk(M:Int) => .K </k> <rs> (<r> <rid> 1 </rid> </r> => <r> <rid> ?X:Int </rid> </r> <r> <rid> ?Y:Int </rid> </r> ?C:Bag) </rs> requires N >Int 4 andBool N <Int 6 andBool M >Int 6 andBool M <Int 8 ensures ?X >Int 8
endmodule
"#;

/// A destination item that is an existential is some item of a final collection of items alone,
/// each placement one disjunct, so the claim holds where one placement satisfies the `ensures`
/// (`5` in `{1, 5}`; `M` then `N` in the collection) and is not proven where none does.
#[test]
fn an_existential_set_or_map_item_is_any_final_item_its_constraint_admits() {
    let proven = ["set-ex", "map-ex"];
    let statuses = pac_statuses(
        PAC_EXISTENTIAL_ITEM_SPEC,
        "PACX-SPEC",
        &["set-ex", "map-ex", "set-ex-none", "map-ex-none"],
    );
    for (claim, status) in statuses {
        if proven.contains(&claim.as_str()) {
            assert_eq!(status, "proven", "{claim}");
        } else {
            assert!(
                matches!(status.as_str(), "failed" | "disproved"),
                "{claim}: {status}"
            );
        }
    }
    let definition = &COLLECTION_CELL_ITEM_ANYWHERE[..COLLECTION_CELL_ITEM_ANYWHERE
        .find("module LCELL-SPEC")
        .unwrap()];
    for collection in ["Set", "Map"] {
        let kore = compile(
            &format!("{definition}{AC_EXISTENTIAL_ITEM_SPEC}").replace("$TYPE", collection),
            "ACX-SPEC",
            "LCELL",
        );
        let status = |claim: &str| {
            prove(
                &kore,
                "ACX-SPEC",
                &format!("ACX-SPEC.{claim}"),
                ProveRequest::default(),
            )
            .status
        };
        assert_eq!(status("ex-two"), "proven", "{collection} ex-two");
        let none = status("ex-two-none");
        assert!(
            matches!(none.as_str(), "failed" | "disproved"),
            "{collection} ex-two-none: {none}"
        );
    }
}

/// Claims that `add` an integer `M` to the plain set `<s>` of [`AC_FRAMES_ELSEWHERE`] (its
/// definition, with this spec module) holding symbolic integers, whose ranges either keep `M`
/// apart from each of them (`-disjoint`, `set-two-sym`, `ex-sym`) or let it equal one
/// (`-overlap`).
const PAC_GUARDED_ADD_SPEC: &str = r#"
module PACG-SPEC
  imports PAC
  claim [step-disjoint]: <k> add(M:Int) => .K </k> <s> SetItem(N:Int) => SetItem(N) SetItem(M) </s> <m> X:Map => ?Y:Map </m> requires N >Int 4 andBool N <Int 6 andBool M >Int 6 andBool M <Int 8
  claim [step-two-disjoint]: <k> add(M:Int) => .K </k> <s> SetItem(N:Int) SetItem(L:Int) => SetItem(N) SetItem(L) SetItem(M) </s> <m> X:Map => ?Y:Map </m> requires N >Int 4 andBool N <Int 6 andBool L >Int 0 andBool L <Int 3 andBool M >Int 6 andBool M <Int 8
  claim [set-two-sym]: <k> add(N:Int) ; add(M:Int) => .K </k> <s> .Set => ?A:Set SetItem(7) ?C:Set </s> <m> .Map => ?M:Map </m> requires N >Int 4 andBool N <Int 6 andBool M >Int 6 andBool M <Int 8
  claim [ex-sym]: <k> add(N:Int) ; add(M:Int) => .K </k> <s> .Set => SetItem(?X:Int) ?C:Set </s> <m> .Map => ?M:Map </m> requires N >Int 4 andBool N <Int 6 andBool M >Int 0 andBool M <Int 2 ensures ?X >Int 3
  claim [step-overlap]: <k> add(M:Int) => .K </k> <s> SetItem(N:Int) => SetItem(N) SetItem(M) </s> <m> X:Map => ?Y:Map </m> requires N >Int 4 andBool N <Int 7 andBool M >Int 5 andBool M <Int 8
  claim [step-two-overlap]: <k> add(M:Int) => .K </k> <s> SetItem(N:Int) SetItem(L:Int) => SetItem(N) SetItem(L) SetItem(M) </s> <m> X:Map => ?Y:Map </m> requires N >Int 4 andBool N <Int 6 andBool L >Int 0 andBool L <Int 8 andBool M >Int 6 andBool M <Int 8
  claim [set-two-sym-overlap]: <k> add(N:Int) ; add(M:Int) => .K </k> <s> .Set => ?A:Set SetItem(7) ?C:Set </s> <m> .Map => ?M:Map </m> requires N >Int 4 andBool N <Int 8 andBool M >Int 6 andBool M <Int 8
  claim [ex-sym-overlap]: <k> add(N:Int) ; add(M:Int) => .K </k> <s> .Set => SetItem(?X:Int) ?C:Set </s> <m> .Map => ?M:Map </m> requires N >Int 4 andBool N <Int 6 andBool M >Int 0 andBool M <Int 6 ensures ?X >Int 3
endmodule
"#;

/// `add(M)` rewrites where `M` is not in the set and is stuck where it is. Membership in a set
/// whose elements are all known is equality with one of them, so where the ranges make `M`
/// differ from every element, the stuck branch's condition is unsatisfiable, the branch denotes
/// no state, and only the step remains. Where a range lets `M` equal an element (6, or 7 in
/// `step-two-overlap`, 5 in `ex-sym-overlap`), that instance is stuck before `.K`, and the
/// claim is not proven.
#[test]
fn a_guarded_add_has_no_stuck_branch_where_the_ranges_keep_its_item_out_of_the_set() {
    let proven = [
        "step-disjoint",
        "step-two-disjoint",
        "set-two-sym",
        "ex-sym",
    ];
    let unproven = [
        "step-overlap",
        "step-two-overlap",
        "set-two-sym-overlap",
        "ex-sym-overlap",
    ];
    let statuses = pac_statuses(
        PAC_GUARDED_ADD_SPEC,
        "PACG-SPEC",
        &[proven.as_slice(), unproven.as_slice()].concat(),
    );
    for (claim, status) in statuses {
        if proven.contains(&claim.as_str()) {
            assert_eq!(status, "proven", "{claim}");
        } else {
            assert!(
                matches!(status.as_str(), "failed" | "disproved"),
                "{claim}: {status}"
            );
        }
    }
}

/// Claims over the map `<m>` of [`AC_FRAMES_ELSEWHERE`] (its definition, with this spec module)
/// after `add`, which leaves `M[2 <- 2]` (`M[2 <- 2][3 <- 3]`) for an arbitrary map `M`, and
/// over a written union in `<u>` and written updates in `<n>`, which `add` leaves alone.
const PAC_UPDATE_SPEC: &str = r#"
module PACU-SPEC
  imports PAC
  claim [map-open-one]: <k> add(2) => .K </k> <s> S => ?S:Set </s> <m> M => 2 |-> 2 ?C:Map </m> requires notBool 2 in S
  claim [map-open-two]: <k> add(2) => .K </k> <s> S => ?S:Set </s> <m> M => ?A:Map 2 |-> 2 ?C:Map </m> requires notBool 2 in S
  claim [map-upd-one]: <k> add(2) => .K </k> <s> S => ?S:Set </s> <m> M => 2 |-> 2 ?C:Map </m> requires notBool 2 in S andBool notBool 2 in_keys(M)
  claim [map-two-items]: <k> add(2) ; add(3) => .K </k> <s> .Set => ?S:Set </s> <m> M => 2 |-> 2 3 |-> 3 ?C:Map </m>
  claim [update-override]: <k> add(2) => .K </k> <s> X => ?S:Set </s> <m> M => ?M:Map </m> <n> N[3 <- 5][3 <- 7] => 3 |-> 7 ?C:Map </n> requires notBool 2 in X
  claim [union-one]: <k> add(2) => .K </k> <s> X => ?S:Set </s> <m> M => ?M:Map </m> <u> S |Set SetItem(2) => SetItem(2) ?C:Set </u> requires notBool 2 in X
  claim [union-two]: <k> add(2) => .K </k> <s> X => ?S:Set </s> <m> M => ?M:Map </m> <u> SetItem(2) |Set S => ?A:Set SetItem(2) ?C:Set </u> requires notBool 2 in X
  claim [union-chain]: <k> add(2) => .K </k> <s> X => ?S:Set </s> <m> M => ?M:Map </m> <u> (S |Set SetItem(2)) |Set SetItem(3) => SetItem(2) SetItem(3) ?C:Set </u> requires notBool 2 in X
  claim [map-wrong-value]: <k> add(2) => .K </k> <s> S => ?S:Set </s> <m> M => 2 |-> 3 ?C:Map </m> requires notBool 2 in S
  claim [map-absent-key]: <k> add(2) => .K </k> <s> S => ?S:Set </s> <m> M => 3 |-> 3 ?C:Map </m> requires notBool 2 in S
  claim [update-overridden]: <k> add(2) => .K </k> <s> X => ?S:Set </s> <m> M => ?M:Map </m> <n> N[3 <- 5][3 <- 7] => 3 |-> 5 ?C:Map </n> requires notBool 2 in X
  claim [union-absent]: <k> add(2) => .K </k> <s> X => ?S:Set </s> <m> M => ?M:Map </m> <u> S |Set SetItem(2) => SetItem(3) ?C:Set </u> requires notBool 2 in X
  claim [update-symbolic-keys]: <k> add(2) => .K </k> <s> X => ?S:Set </s> <m> M => ?M:Map </m> <n> N[K:Int <- 1][L:Int <- 2] => K |-> 1 ?C:Map </n> requires notBool 2 in X
  claim [union-symbolic-items]: <k> add(2) => .K </k> <s> X => ?S:Set </s> <m> M => ?M:Map </m> <u> (S |Set SetItem(K:Int)) |Set SetItem(L:Int) => SetItem(K) SetItem(L) ?C:Set </u> requires notBool 2 in X
  claim [map-parts]: <k> add(2) => .K </k> <s> S => ?S:Set </s> <m> M => ?A:Map ?C:Map </m> requires notBool 2 in S
endmodule
"#;

/// `M[K <- V]` binds `K` to `V` and every other key as `M` does, so it is the map `K |-> V`
/// beside `M` without `K`, whatever `M` holds; `A |Set B` with `B` a set of items is `B` beside
/// `A -Set B`. A destination with items and a free part therefore holds of such a final
/// collection when its items are the ones written there: the part is the rest, for one part or
/// two read as one, along a chain of updates with distinct keys (the outer one winning where
/// both write a key) or of unions. A destination item with another value (`map-wrong-value`,
/// `update-overridden`) or another key or element (`map-absent-key`, `union-absent`, which `M`
/// or `S` may lack) is not proven, nor is the inner key of a chain whose keys may be equal
/// (`update-symbolic-keys`: where `K` is `L`, `K` is bound to 2), nor are two items of a chain of
/// unions that may be equal (`union-symbolic-items`: where `K` is `L`, the union adds one item).
/// A destination of parts alone holds of such a collection as of any other (`map-parts`).
#[test]
fn a_destination_item_written_by_a_final_update_or_union_is_found_beside_the_rest() {
    let proven = [
        "map-open-one",
        "map-open-two",
        "map-upd-one",
        "map-two-items",
        "update-override",
        "union-one",
        "union-two",
        "union-chain",
        "map-parts",
    ];
    let unproven = [
        "map-wrong-value",
        "map-absent-key",
        "update-overridden",
        "union-absent",
        "update-symbolic-keys",
        "union-symbolic-items",
    ];
    let statuses = pac_statuses(
        PAC_UPDATE_SPEC,
        "PACU-SPEC",
        &[proven.as_slice(), unproven.as_slice()].concat(),
    );
    for (claim, status) in statuses {
        if proven.contains(&claim.as_str()) {
            assert_eq!(status, "proven", "{claim}");
        } else {
            assert!(
                matches!(status.as_str(), "failed" | "disproved"),
                "{claim}: {status}"
            );
        }
    }
}

/// A proof evaluates only consequences of the definition, also when a library caller loads the
/// definition and proves inside its own `Execution` scope: the load's analyses and the proof both
/// run in `Proof`, so a claim about the order of `keys_list`, which the definition does not fix,
/// is neither proven nor disproved, while the claim that some list is reached is proven.
#[test]
fn a_proof_inside_an_execution_scope_reads_no_order_the_definition_leaves_open() {
    use k_rust_backend::evaluation::{EvaluationMode, with_evaluation};
    const SOURCE: &str = r#"
module ORD
  imports DOMAINS
  imports COLLECTIONS
  configuration <k> $PGM:Int </k>
  rule I:Int => keys_list(10 |-> 1 2 |-> 2 I |-> 3)
endmodule
module ORD-SPEC
  imports ORD
  claim [text-order]: <k> -1 => ListItem(-1) ListItem(10) ListItem(2) </k>
  claim [some-list]: <k> -1 => ?_L:List </k>
endmodule
"#;
    let kore = compile(SOURCE, "ORD-SPEC", "ORD");
    let statuses = with_evaluation(EvaluationMode::Execution, || {
        let mut backend = Backend::new(&kore, "ORD-SPEC", BackendOptions::default()).unwrap();
        ["ORD-SPEC.text-order", "ORD-SPEC.some-list"].map(|claim| {
            backend
                .prove(ProveRequest {
                    claim: Some(claim.to_owned()),
                    ..ProveRequest::default()
                })
                .unwrap_or_else(|error| panic!("{claim}: {error:?}"))
                .status
        })
    });
    assert!(
        !matches!(statuses[0].as_str(), "proven" | "disproved"),
        "{statuses:?}"
    );
    assert_eq!(statuses[1], "proven", "{statuses:?}");
}

/// The status of each of `claims` of `spec`, proven against `definition` in `source`.
fn claim_statuses(
    source: &str,
    spec: &str,
    definition: &str,
    claims: &[&str],
) -> Vec<(String, String)> {
    let kore = compile(source, spec, definition);
    claims
        .iter()
        .map(|claim| {
            let result = prove(
                &kore,
                spec,
                &format!("{spec}.{claim}"),
                ProveRequest::default(),
            );
            ((*claim).to_owned(), result.status)
        })
        .collect()
}

/// Each claim of `expected` whose status differs from the one it lists, described.
fn unexpected_statuses(
    source: &str,
    spec: &str,
    definition: &str,
    expected: &[(&str, &str)],
) -> Vec<String> {
    let claims = expected.iter().map(|(claim, _)| *claim).collect::<Vec<_>>();
    claim_statuses(source, spec, definition, &claims)
        .into_iter()
        .zip(expected)
        .filter(|((_, status), (_, expected))| status != expected)
        .map(|((claim, status), (_, expected))| {
            format!("{spec}.{claim}: {status}, expected {expected}")
        })
        .collect()
}

/// Destinations whose `#if` holds a partial operand: `undef()` has no equation, so it is
/// undefined in every model the definition admits.
const ITE_PARTIAL_BRANCH: &str = r#"
module PROVE
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Exp ::= Int | Bool
               | "a" "(" Bool ")" [symbol(a)]
  syntax Int ::= undef() [function, symbol(undef)]
  configuration <k> $PGM:Exp </k>
  rule <k> a(_) => 1 </k>
endmodule

module PROVE-SPEC
  imports PROVE
  claim [ground]: <k> a(true) => #if true #then 1 #else undef() #fi </k>
  claim [sym]: <k> a(B) => #if B #then 1 #else undef() #fi </k> requires B
  claim [plain]: <k> a(true) => 1 </k>
  claim [undefrhs]: <k> a(true) => 1 #And #Ceil(undef()) </k>
endmodule
"#;

/// The same claims where `undef()` has an equation, so it is defined.
const ITE_DEFINED_BRANCH: &str = r#"
module PROVE4
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Exp ::= Int | Bool
               | "a" "(" Bool ")" [symbol(a)]
  syntax Int ::= undef() [function, symbol(undef)]
  configuration <k> $PGM:Exp </k>
  rule <k> a(_) => 1 </k>
  rule undef() => 0
endmodule

module PROVE4-SPEC
  imports PROVE4
  claim [ground]: <k> a(true) => #if true #then 1 #else undef() #fi </k>
  claim [sym]: <k> a(B) => #if B #then 1 #else undef() #fi </k> requires B
endmodule
"#;

/// `#if` destinations with a partial condition or a partial branch, and a state that reaches an
/// `#if` itself (`c`). `p(false)` and `undefb()` have no equation.
const ITE_PARTIAL_CONDITION: &str = r#"
module PROVE3
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Exp ::= Int | Bool
               | "a" "(" Bool ")" [symbol(a)]
               | "c" "(" Bool ")" [symbol(c)]
  syntax Int ::= undef() [function, symbol(undef)]
  syntax Bool ::= undefb() [function, symbol(undefb)]
                | p(Bool)  [function, symbol(p)]
  rule p(true) => true
  configuration <k> $PGM:Exp </k>
  rule <k> a(_) => 1 </k>
  rule <k> c(B) => #if B #then 1 #else undef() #fi </k>
endmodule

module PROVE3-SPEC
  imports PROVE3
  claim [condundef]: <k> a(true) => #if undefb() #then 1 #else 1 #fi </k>
  claim [condpartial]: <k> a(B) => #if p(B) #then 1 #else 1 #fi </k>
  claim [symelse]: <k> a(B) => #if B #then undef() #else 1 #fi </k> requires notBool B
  claim [subj]: <k> c(B) => 1 </k> requires B
  claim [ctl]: <k> a(B) => #if B #then 1 #else 2 #fi </k> requires B
endmodule
"#;

/// Destinations whose Boolean connective or Int product has a partial operand, which the
/// connective or the product discards or absorbs on the claim's instances.
const CONNECTIVE_PARTIAL_OPERAND: &str = r#"
module PROVE5
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Exp ::= Int | Bool
               | "d" "(" Bool ")" [symbol(d)]
               | "z" "(" Bool ")" [symbol(z)]
  syntax Bool ::= undefb() [function, symbol(undefb)]
  syntax Int ::= undefi() [function, symbol(undefi)]
  configuration <k> $PGM:Exp </k>
  rule <k> d(_) => false </k>
  rule <k> z(_) => 0 </k>
endmodule

module PROVE5-SPEC
  imports PROVE5
  claim [andth]: <k> d(B) => B andThenBool undefb() </k> requires notBool B
  claim [andthg]: <k> d(false) => false andThenBool undefb() </k>
  claim [orel]: <k> d(B) => notBool (B orElseBool undefb()) </k> requires B
  claim [andb]: <k> d(B) => B andBool undefb() </k> requires notBool B
  claim [mul]: <k> z(B) => 0 *Int undefi() </k> requires B
endmodule
"#;

/// Destinations with a partial operand that the claim's condition makes defined or leaves
/// undefined on some instance: a division, and an existential the match binds to the state's
/// argument under a function defined only at `5`.
const PARTIAL_OPERAND_CONDITION: &str = r#"
module IMP
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Exp ::= Int | Bool
               | z(Int) [symbol(z)]
               | pr(Int, Int) [symbol(pr)]
               | mk(Int) [symbol(mk)]
  syntax Int ::= w(Int) [function, symbol(w)]
  rule w(5) => 5
  configuration <k> $PGM:Exp </k>
  rule <k> z(_) => 0 </k>
  rule <k> mk(X) => pr(X, 0) </k>
endmodule

module IMP-SPEC
  imports IMP
  claim [divok]: <k> z(Y) => 0 *Int (1 /Int Y) </k> requires Y =/=Int 0
  claim [divbad]: <k> z(Y) => 0 *Int (1 /Int Y) </k>
  claim [exbound]: <k> mk(X) => pr(?W, 0 *Int w(?W)) </k> requires X ==Int 5
  claim [exboundbad]: <k> mk(X) => pr(?W, 0 *Int w(?W)) </k>
endmodule
"#;

/// A destination term `t` denotes `⌈t⌉ ∧ t`, so a claim holds of an instance only where its
/// right-hand side is defined there. Each claim below reaches a value equal to its right-hand
/// side wherever that side is defined, but the side applies an operand that is undefined on the
/// claim's instances: the untaken branch of an `#if` (`sym`, `symelse`), its condition
/// (`condundef`, `condpartial`), the discarded operand of `andThenBool` or `orElseBool` (`andth`,
/// `orel`), an operand `andBool` or `*Int` absorbs (`andb`, `mul`). The right-hand side is
/// `\bottom` there, so none of them is proven, whether the operand is discarded by a split of
/// the destination or absorbed by a hook the solver reads as total. Where the operand is
/// defined (`PROVE4`'s `undef() => 0`, the `ctl` branch `2`), or the destination has none
/// (`plain`), the claim is proven; the ground forms (`ground`, `andthg`, `undefrhs`) and a state
/// that reaches the `#if` itself (`subj`) are not.
#[test]
fn a_claim_is_proven_only_where_its_right_hand_side_is_defined() {
    let wrong = [
        unexpected_statuses(
            ITE_PARTIAL_BRANCH,
            "PROVE-SPEC",
            "PROVE",
            &[
                ("sym", "failed"),
                ("ground", "failed"),
                ("undefrhs", "failed"),
                ("plain", "proven"),
            ],
        ),
        unexpected_statuses(
            ITE_PARTIAL_CONDITION,
            "PROVE3-SPEC",
            "PROVE3",
            &[
                ("symelse", "failed"),
                ("condundef", "failed"),
                ("condpartial", "failed"),
                ("subj", "failed"),
                ("ctl", "proven"),
            ],
        ),
        unexpected_statuses(
            ITE_DEFINED_BRANCH,
            "PROVE4-SPEC",
            "PROVE4",
            &[("sym", "proven"), ("ground", "proven")],
        ),
        unexpected_statuses(
            CONNECTIVE_PARTIAL_OPERAND,
            "PROVE5-SPEC",
            "PROVE5",
            &[
                ("andth", "failed"),
                ("orel", "failed"),
                ("andb", "failed"),
                ("mul", "failed"),
                ("andthg", "failed"),
            ],
        ),
    ]
    .concat();
    assert!(wrong.is_empty(), "{wrong:#?}");
}

/// A partial operand of the right-hand side that the claim's condition makes defined keeps the
/// claim proven: `1 /Int Y` under `Y =/=Int 0`, and `w(?W)` where the match binds `?W` to `X`
/// and the condition makes `X` the one argument `w` is defined at. Without the condition the
/// operand is undefined on some instance (`Y = 0`, `X = 0`), and the claim is not proven.
#[test]
fn a_claim_condition_that_defines_a_right_hand_side_operand_keeps_it_proven() {
    let wrong = unexpected_statuses(
        PARTIAL_OPERAND_CONDITION,
        "IMP-SPEC",
        "IMP",
        &[
            ("divok", "proven"),
            ("exbound", "proven"),
            ("divbad", "failed"),
            ("exboundbad", "failed"),
        ],
    );
    assert!(wrong.is_empty(), "{wrong:#?}");
}

/// Claims through operands `#if` discards: guarded recursion (`fact3`), a diverging discarded
/// operand on either side of a claim, and a symbolic condition the claim's condition decides.
const DISCARDED_OPERAND_CLAIMS: &str = r#"
module PROVE2
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Exp ::= Int | Bool
               | "go" "(" Int ")" [symbol(go)]
               | "a" "(" Bool ")" [symbol(a)]
               | "b" "(" ")"      [symbol(b)]
               | "lhs" "(" Int ")" [symbol(lhs)]
               | "a2" "(" Int ")" [symbol(a2)]
  syntax Int ::= fact(Int) [function, symbol(fact)]
               | loopi()   [function, symbol(loopi)]
  rule fact(N) => #if N <=Int 0 #then 1 #else N *Int fact(N -Int 1) #fi
  rule loopi() => loopi() +Int 1
  configuration <k> $PGM:Exp </k>
  rule <k> go(N) => fact(N) </k>
  rule <k> a(_) => 1 </k>
  rule <k> b() => #if true #then 1 #else loopi() #fi </k>
  rule <k> lhs(I) => I </k>
  rule <k> a2(_) => 1 </k>
endmodule

module PROVE2-SPEC
  imports PROVE2
  claim [fact3]: <k> go(3) => 6 </k>
  claim [rhsloop]: <k> a(true) => #if true #then 1 #else loopi() #fi </k>
  claim [symloop]: <k> a(B) => #if B #then 1 #else loopi() #fi </k> requires B
  claim [bloop]: <k> b() => 1 </k>
  claim [bboth]: <k> b() => #if true #then 1 #else loopi() #fi </k>
  claim [lhsite]: <k> lhs(#if true #then 1 #else loopi() #fi) => 1 </k>
  claim [symloop2]: <k> a2(X) => #if X >Int 0 #then 1 #else loopi() #fi </k> requires X >Int 5
endmodule
"#;

/// A discarded operand is never evaluated on a proof route either: no claim below halts on the
/// stack. A state that reaches the value under the discarded operand's open obligation has a
/// trivial leaf where the obligation fails, so `fact3`, `bloop` and `bboth` are not proven
/// (they are with vacuous results allowed); a destination whose discarded operand is undefined
/// on some instance is not reached there (`rhsloop` and `symloop` are stuck), and a claim's
/// left-hand side with one is proven, since the claim holds vacuously where it is undefined.
#[test]
fn a_claim_through_a_discarded_operand_never_evaluates_it() {
    let kore = compile(DISCARDED_OPERAND_CLAIMS, "PROVE2-SPEC", "PROVE2");
    let result = |claim: &str, allow_vacuous: bool| {
        prove(
            &kore,
            "PROVE2-SPEC",
            &format!("PROVE2-SPEC.{claim}"),
            ProveRequest {
                allow_vacuous,
                ..ProveRequest::default()
            },
        )
    };
    let has = |result: &ProofResultOutput, outcome: ProofLeafOutcomeOutput| {
        result.leaves.iter().any(|leaf| leaf.outcome == outcome)
    };
    for claim in ["fact3", "bloop", "bboth"] {
        let failed = result(claim, false);
        assert_eq!(failed.status, "failed", "{claim}: {failed:?}");
        assert!(
            has(&failed, ProofLeafOutcomeOutput::Trivial),
            "{claim}: {failed:?}"
        );
        assert_eq!(
            result(claim, true).status,
            "proven",
            "{claim} allowing vacuous results"
        );
    }
    // `symloop2`'s condition `X >Int 0` is decided by the solver from `X >Int 5`, before the
    // `else` branch's equation `1 = loopi()` would be simplified.
    for claim in ["rhsloop", "symloop", "symloop2"] {
        let failed = result(claim, false);
        assert_eq!(failed.status, "failed", "{claim}: {failed:?}");
        assert!(
            has(&failed, ProofLeafOutcomeOutput::Stuck),
            "{claim}: {failed:?}"
        );
    }
    let proven = result("lhsite", false);
    assert_eq!(proven.status, "proven", "{proven:?}");
    for claim in [
        "fact3", "rhsloop", "symloop", "symloop2", "bloop", "bboth", "lhsite",
    ] {
        assert!(
            !has(
                &result(claim, false),
                ProofLeafOutcomeOutput::StackExhausted
            ),
            "{claim}"
        );
    }
}

/// Claims whose conditionals discard a division by a variable the claim's condition keeps
/// nonzero, and their false twins.
const DISCARDED_DIVISION: &str = r#"
module D2
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Exp ::= Int | Bool | q(Int) [symbol(q)] | r(Int, Int) [symbol(r)] | s(Bool, Int) [symbol(s)]
  configuration <k> $PGM:Exp </k>
  rule <k> q(X) => #if X >Int 5 #then 1 #else 10 /Int X #fi </k>
  rule <k> r(W0, W1) => #if W1 ==Int 0 #then 0 #else W0 /Int W1 #fi </k>
  rule <k> s(B, X) => B orElseBool (10 /Int X ==Int 1) </k>
endmodule

module D2-SPEC
  imports D2
  claim [qpos]: <k> q(X) => 1 </k> requires X >Int 5
  claim [rnz]: <k> r(W0, W1) => W0 /Int W1 </k> requires W1 >Int 0
  claim [rz]: <k> r(_W0, W1) => 0 </k> requires W1 ==Int 0
  claim [sor]: <k> s(B, X) => true </k> requires B andBool X >Int 0
  claim [sorf]: <k> s(B, _X) => true </k> requires B
endmodule
"#;

/// The definedness of a discarded division over variables and literals is the instance of its
/// ceil equation (`W1 =/=Int 0`), which the solver decides from the claim's condition: `qpos`,
/// `rnz` (the `/Word` idiom) and `sor` are proven. `rz` discards `W0 /Int 0` and `sorf` may
/// divide by zero, so neither is.
#[test]
fn a_discarded_division_over_variables_states_its_divisor_condition() {
    let wrong = unexpected_statuses(
        DISCARDED_DIVISION,
        "D2-SPEC",
        "D2",
        &[
            ("qpos", "proven"),
            ("rnz", "proven"),
            ("sor", "proven"),
            ("rz", "failed"),
            ("sorf", "failed"),
        ],
    );
    assert!(wrong.is_empty(), "{wrong:#?}");
}

/// Claims whose conditional discards a hook over a ground map: a listing of two keys, whose
/// order only an execution chooses, and lookups.
const DISCARDED_COLLECTION_HOOK: &str = r#"
module GH
  imports INT
  imports BOOL
  imports MAP
  imports LIST
  imports K-EQUAL
  syntax Exp ::= Int | l(Bool) [symbol(l)] | f(Bool) [symbol(f)] | g(Bool) [symbol(g)] | h(Bool) [symbol(h)]
  configuration <k> $PGM:Exp </k>
  rule <k> l(B) => #if B #then 7 #else size(keys_list(1 |-> 10 3 |-> 30)) #fi </k>
  rule <k> f(B) => #if B #then 7 #else {keys_list(1 |-> 10 3 |-> 30)[0]}:>Int #fi </k>
  rule <k> g(B) => #if B #then 7 #else {(1 |-> 10 3 |-> 30)[3]}:>Int #fi </k>
  rule <k> h(B) => #if B #then 7 #else {(1 |-> 10 3 |-> 30)[2]}:>Int #fi </k>
endmodule

module GH-SPEC
  imports GH
  claim [listed]: <k> l(B) => 7 </k> requires B
  claim [first]: <k> f(B) => 7 </k> requires B
  claim [bound]: <k> g(B) => 7 </k> requires B
  claim [unbound]: <k> h(B) => 7 </k> requires B
endmodule
"#;

/// A discarded hook over a ground collection is decided by the hook on a proof route too, and a
/// value only an execution chooses is not chosen there: `keys_list` of two bindings is defined
/// whatever its order, so `listed` is proven without one, while `first`, whose discarded operand
/// is defined only if the listing's first key is an `Int` the projection accepts, is not proven
/// from k-rust's order. A lookup of a bound key is defined (`bound`), and one of a key the map
/// does not bind makes the conditional `\bottom` (`unbound`).
#[test]
fn a_claim_through_a_discarded_hook_over_a_ground_collection_chooses_no_value() {
    let wrong = unexpected_statuses(
        DISCARDED_COLLECTION_HOOK,
        "GH-SPEC",
        "GH",
        &[
            ("listed", "proven"),
            ("first", "failed"),
            ("bound", "proven"),
            ("unbound", "failed"),
        ],
    );
    assert!(wrong.is_empty(), "{wrong:#?}");
}

/// A claim whose conditional discards a definedness that depends on a console read is never
/// proven: its left-hand side or its destination meets the impure application, which is not
/// performed (`a_discarded_conditional_operand_performs_no_console_effect` in cli.rs).
const IMPURE_DISCARD: &str = r#"
requires "domains.md"
module MARKER
  imports K-IO
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Exp ::= a(Int) [symbol(a)] | b(Int) [symbol(b)]
  configuration <k> $PGM:Exp </k>
  rule <k> a(N) => b(N) </k>
endmodule

module MARKER-SPEC
  imports MARKER
  claim [m1]: <k> a(X) => b(#if true #then X #else 1 /Int ({#getc(0)}:>Int -Int 81) #fi) </k> requires X ==Int {#getc(0)}:>Int
  claim [m2]: <k> a(#if true #then 1 #else 1 /Int {#getc(0)}:>Int #fi) => b(#if true #then 1 #else 1 /Int ({#getc(0)}:>Int -Int 81) #fi) </k>
  claim [m3]: <k> b(#if true #then 1 #else 1 /Int {#getc(0)}:>Int #fi) => b(#if true #then 1 #else 1 /Int ({#getc(0)}:>Int -Int 81) #fi) </k>
endmodule
"#;

#[test]
fn a_claim_through_an_impure_discarded_operand_is_never_proven() {
    let statuses = claim_statuses(IMPURE_DISCARD, "MARKER-SPEC", "MARKER", &["m1", "m2", "m3"]);
    for (claim, status) in statuses {
        assert_ne!(status, "proven", "{claim}");
    }
}

/// An anywhere head with `w(X) = mk(1) [anywhere, concrete]` above an `owise` equation
/// `w(_) = mk(0)`: the first equation says `w(N) = mk(1)` for every `N`, and the `owise`
/// equation's premise excludes every `N` the first one matches.
const ANYWHERE_CONCRETE_OVER_OWISE: &str = r#"
module ANYW-SYNTAX
  imports INT-SYNTAX
  syntax W ::= w(Int) [symbol(w)] | mk(Int) [symbol(mk)]
endmodule

module ANYW
  imports ANYW-SYNTAX
  imports INT
  configuration <k> $PGM:W </k>
  rule w(_X) => mk(1) [anywhere, concrete]
  rule w(_) => mk(0) [anywhere, owise]
endmodule

module ANYW-SPEC
  imports ANYW
  claim [w-sym-zero]: <k> w(_N:Int) => mk(0) </k>
  claim [w-sym-one]: <k> w(_N:Int) => mk(1) </k>
  claim [w-3-one]: <k> w(3) => mk(1) </k>
endmodule
"#;

/// A function whose rules all carry `symbolic`: `s(X, Y) = 1` for every `X` and `Y`, and the
/// `owise` rule's premise excludes every argument the first rule matches. On `s(N, 3)` the first
/// rule's binding of `Y` to 3 is set aside, the `owise` rule's binding is not.
const SYMBOLIC_FUNCTION_OVER_OWISE: &str = r#"
module SYMF-SYNTAX
  imports INT-SYNTAX
  syntax Int ::= s(Int, Int) [function, symbol(s)]
endmodule

module SYMF
  imports SYMF-SYNTAX
  imports INT
  configuration <k> $PGM:Int </k>
  rule s(_X, _Y) => 1 [symbolic]
  rule s(_X, 3) => 0 [owise, symbolic]
endmodule

module SYMF-SPEC
  imports SYMF
  claim [owise-zero]: <k> s(_N:Int, 3) => 0 </k>
  claim [first-one]: <k> s(_N:Int, 3) => 1 </k>
endmodule
"#;

/// A map pattern that matches `w(1 |-> 5  20 |-> N)` in two ways: the instance at key 1 has its
/// `requires` refuted, the one at key 20 is set aside by `concrete(V)` (its value `N` is
/// symbolic) and its `requires` holds, so the first equation gives `mk(N)` and the `owise`
/// premise excludes the subject. At `w(1 |-> 5  2 |-> N)` both instances are refuted.
const SET_ASIDE_MAP_INSTANCE: &str = r#"
module INST-SYNTAX
  imports INT
  imports MAP
  imports BOOL
  syntax Foo ::= w(Map) [symbol(w)] | mk(Int) [symbol(mk)]
endmodule

module INST
  imports INST-SYNTAX
  configuration <k> $PGM:K </k>
  rule w((K:Int |-> V:Int) _M) => mk(V) requires K >Int 10 [anywhere, concrete(V)]
  rule w(_) => mk(0) [anywhere, owise]
endmodule

module INST-SPEC
  imports INST
  claim [mixed-zero]: <k> w(1 |-> 5  20 |-> N:Int) => mk(0) </k>
  claim [mixed-n]: <k> w(1 |-> 5  20 |-> N:Int) => mk(N) </k>
  claim [both-refuted-zero]: <k> w(1 |-> 5  2 |-> N:Int) => mk(0) </k>
endmodule
"#;

/// A `concrete` anywhere equation with a `requires` above an `owise` one: the `owise` premise
/// excludes exactly the arguments above 10.
const ANYWHERE_CONCRETE_REQUIRES_OVER_OWISE: &str = r#"
module ANYREQ-SYNTAX
  imports INT-SYNTAX
  syntax W ::= w(Int) [symbol(w)] | mk(Int) [symbol(mk)]
endmodule

module ANYREQ
  imports ANYREQ-SYNTAX
  imports INT
  configuration <k> $PGM:W </k>
  rule w(X) => mk(1) requires X >Int 10 [anywhere, concrete]
  rule w(_) => mk(0) [anywhere, owise]
endmodule

module ANYREQ-SPEC
  imports ANYREQ
  claim [refuted-zero]: <k> w(N:Int) => mk(0) </k> requires N <Int 5
  claim [open-zero]: <k> w(N:Int) => mk(0) </k> requires N <Int 50
  claim [held-one]: <k> w(N:Int) => mk(1) </k> requires N >Int 10
endmodule
"#;

/// The claims of `spec` whose status breaks `expected`: a claim marked `true` must end with the
/// status given, one marked `false` with any other.
fn statuses_breaking(
    source: &str,
    spec: &str,
    definition: &str,
    expected: &[(&str, bool, &str)],
) -> Vec<String> {
    let kore = compile(source, spec, definition);
    expected
        .iter()
        .filter_map(|(claim, equal, status)| {
            let found = prove(
                &kore,
                spec,
                &format!("{spec}.{claim}"),
                ProveRequest::default(),
            )
            .status;
            ((found == *status) != *equal).then(|| {
                let relation = if *equal {
                    "expected"
                } else {
                    "expected anything but"
                };
                format!("{spec}.{claim}: {found}, {relation} {status}")
            })
        })
        .collect()
}

/// An equation that matches but is set aside by a `concrete` or `symbolic` attribute still holds
/// of the application, so no lower-priority equation applies in its place: the false claims
/// that take the `owise` value are not proven, and the true claims that take the first
/// equation's value are not disproved. On a ground argument the `concrete` equation applies.
/// Among the instances of one map pattern, a set-aside one that holds is not hidden by one
/// whose `requires` is refuted; where every instance is refuted the `owise` equation applies.
#[test]
fn an_owise_equation_does_not_apply_below_a_set_aside_equation() {
    let wrong = [
        statuses_breaking(
            ANYWHERE_CONCRETE_OVER_OWISE,
            "ANYW-SPEC",
            "ANYW",
            &[
                ("w-sym-zero", false, "proven"),
                ("w-sym-one", false, "disproved"),
                ("w-3-one", true, "proven"),
            ],
        ),
        statuses_breaking(
            SYMBOLIC_FUNCTION_OVER_OWISE,
            "SYMF-SPEC",
            "SYMF",
            &[
                ("owise-zero", false, "proven"),
                ("first-one", false, "disproved"),
            ],
        ),
        statuses_breaking(
            SET_ASIDE_MAP_INSTANCE,
            "INST-SPEC",
            "INST",
            &[
                ("mixed-zero", false, "proven"),
                ("mixed-n", false, "disproved"),
                ("both-refuted-zero", true, "proven"),
            ],
        ),
    ]
    .concat();
    assert!(wrong.is_empty(), "{wrong:#?}");
}

/// The `owise` premise negates the competitor's left-hand side together with its `requires`, so
/// where that `requires` is refuted under the claim's condition the `owise` equation applies,
/// although `concrete` set the competitor's binding aside (`refuted-zero` is proven); where it
/// may hold, or holds, the application stays (`open-zero` is not proven, `held-one` is not
/// disproved).
#[test]
fn an_owise_equation_applies_below_a_set_aside_equation_whose_requires_is_refuted() {
    let wrong = statuses_breaking(
        ANYWHERE_CONCRETE_REQUIRES_OVER_OWISE,
        "ANYREQ-SPEC",
        "ANYREQ",
        &[
            ("refuted-zero", true, "proven"),
            ("open-zero", false, "proven"),
            ("held-one", false, "disproved"),
        ],
    );
    assert!(wrong.is_empty(), "{wrong:#?}");
}
