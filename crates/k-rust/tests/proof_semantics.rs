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
/// spec module) whose destinations place 0, 1 or 2 items beside two or three existential parts;
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
  claim [absent-one-two]: <k> mk(2) ; mk(3) => .K ... </k> <rs> (<r> <rid> 1 </rid> </r> => ?A:Bag <r> <rid> 9 </rid> </r> ?C:Bag) </rs>
  claim [absent-one-three]: <k> mk(2) ; mk(3) => .K ... </k> <rs> (<r> <rid> 1 </rid> </r> => ?A:Bag <r> <rid> 9 </rid> </r> ?B:Bag ?C:Bag) </rs>
  claim [absent-two-two]: <k> mk(2) ; mk(3) => .K ... </k> <rs> (<r> <rid> 1 </rid> </r> => <r> <rid> 3 </rid> </r> ?A:Bag <r> <rid> 9 </rid> </r> ?C:Bag) </rs>
  claim [absent-two-three]: <k> mk(2) ; mk(3) => .K ... </k> <rs> (<r> <rid> 1 </rid> </r> => ?A:Bag <r> <rid> 2 </rid> </r> ?B:Bag <r> <rid> 9 </rid> </r> ?C:Bag) </rs>
endmodule
"#;

/// Set and map concatenation is associative and commutative with the empty collection as unit,
/// so existential parts beside a set's or a map's items that occur nowhere else stand together
/// for their union, which is one part: any collection disjoint from the items. A destination
/// with two or three such parts and 0, 1 or 2 items therefore holds exactly when its items are
/// instances of the final state, in any order (`two-three` writes 1 before 3), with any split of
/// the other instances between the parts as witness. An item that is no instance (`absent-`)
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

/// A set `<s>` and a map `<m>` that `add` fills, and a set `<u>` and a map `<n>` beside them that
/// no rule changes. The `-bound` claims name a part of `<s>` or `<m>` in `<u>` or `<n>` too, the
/// `-constrained` claims in their `ensures`.
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
  configuration <T> <k> $PGM:Pgm </k> <s> .Set </s> <u> .Set </u> <m> .Map </m> <n> .Map </n> </T>
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
endmodule
"#;

/// Parts are one part only when the destination states nothing else of them. A part that the
/// destination also names elsewhere is not free to take the whole remainder: in `-bound` it is
/// `<u>`'s or `<n>`'s `9`, which no split of 1 and 3 holds, so the claim is not proven; in
/// `-constrained` it must hold 1, which the split with 1 in it does, so the claim holds and is
/// not disproved (no split is tried, so it is left unproven). The parts of a plain set or map
/// value with no item, or beside one, are one part as in a cell collection.
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
    for claim in ["set-constrained", "map-constrained"] {
        assert_eq!(status(claim), "failed", "{claim}");
    }
}
