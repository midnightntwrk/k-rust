//! The critical-pair check of function equations on the public path a client uses: compile K
//! source with the prelude, load it ([`Backend::select_definition`]), and read the load's verdict
//! ([`BackendDefinition::value_claims`]) or the check run again in every scope
//! ([`BackendDefinition::value_claims_in_scope`] with [`CheckScope::All`])
//! (`docs/compatibility.md`, "Value claims").
//!
//! A pair is `refuted` only when its two requires hold on no instance in any model. These tests
//! pin that on guards whose literals are spelled like Booleans but belong to another sort.

use k_rust::{
    backend::{Backend, BackendOptions},
    builtin::embedded,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    outer::{LoadOptions, ResolvedSource, load_with_options},
};
use k_rust_backend::{
    confluence::{CheckScope, UnjoinedPair, UnjoinedReason, ValueClaims},
    definition::BackendDefinition,
    rule::TermIndex,
};

fn compile(source: &str, main: &str) -> String {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("pairs.k", source),
        main,
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            excluded_module_attributes: vec![
                CompilationBackend::Rust.excluded_module_attribute().into(),
            ],
            ..LoadOptions::default()
        },
    )
    .unwrap();
    compile_loaded_definition(&loaded, CompileOptions::default())
        .unwrap()
        .definition_kore
}

/// The anywhere head `nw` over `wr`, which gives a definition a symbol whose claims a pair can
/// withdraw, so that the load classifies the pairs that reach it.
const ANYWHERE_HEAD: &str = "  syntax Wrap ::= wr(MyTok) [symbol(wr)] | nw(Wrap) [symbol(nw)]
  rule nw(wr(T)) => wr(T) [anywhere]";

/// The loaded definition of module `PAIRS` with `declarations` added, and with the anywhere head
/// `nw` when `with_head`. Without it the definition has nothing the load could withdraw, so the
/// load classifies none of its pairs; `CheckScope::All` classifies them either way.
fn definition(declarations: &str, with_head: bool) -> std::sync::Arc<BackendDefinition> {
    definition_importing("", declarations, with_head)
}

/// [`definition`], with the module also importing `imports` (`imports MAP` lines).
fn definition_importing(
    imports: &str,
    declarations: &str,
    with_head: bool,
) -> std::sync::Arc<BackendDefinition> {
    let head = if with_head { ANYWHERE_HEAD } else { "" };
    let source = format!(
        r#"module PAIRS
  imports INT
  imports BOOL
  imports STRING
  imports K-EQUAL
  imports LIST
{imports}
  syntax MyTok ::= r"[a-z][a-z0-9]*" [token]
{head}
  syntax Prog ::= go(MyTok) [symbol(go)] | val(Int) [symbol(val)]
{declarations}
  configuration <k> $PGM:Prog </k>
endmodule
"#
    );
    let kore = compile(&source, "PAIRS");
    let mut backend = Backend::new(&kore, "PAIRS", BackendOptions::default()).unwrap();
    backend.select_definition(None).unwrap()
}

/// The non-joined pairs of `claims` between the equations labelled `first` and `second` of
/// module `PAIRS`, in either order.
fn pairs_between<'a>(claims: &'a ValueClaims, first: &str, second: &str) -> Vec<&'a UnjoinedPair> {
    let label = |pair_rule: &k_rust_backend::rule::RewriteRule| {
        pair_rule.attributes.label.clone().unwrap_or_default()
    };
    let (first, second) = (format!("PAIRS.{first}"), format!("PAIRS.{second}"));
    claims
        .unjoined()
        .iter()
        .filter(|pair| {
            let labels = (label(&pair.first), label(&pair.second));
            labels == (first.clone(), second.clone()) || labels == (second.clone(), first.clone())
        })
        .collect()
}

/// `T =/=K #token("true", "MyTok")` beside `T =/=K #token("false", "MyTok")` holds at `T = abc`,
/// where the two equations give 1 and 2: the pair is not refuted, and the full check reports it
/// with its open conditions.
#[test]
fn a_token_spelled_true_or_false_is_not_a_boolean_literal() {
    for with_head in [false, true] {
        let definition = definition(
            r#"  syntax Int ::= ht(MyTok) [function, symbol(ht)]
  rule [a]: ht(T) => 1 requires T =/=K #token("true", "MyTok")
  rule [b]: ht(T) => 2 requires T =/=K #token("false", "MyTok")"#,
            with_head,
        );
        let all = definition.value_claims_in_scope(CheckScope::All);
        let pairs = pairs_between(&all, "a", "b");
        assert_eq!(
            pairs
                .iter()
                .map(|pair| pair.reason.clone())
                .collect::<Vec<_>>(),
            [UnjoinedReason::ConditionOpen],
            "with the head: {with_head}: {:?}",
            all.unjoined()
        );
    }
}

/// The same over `String`: `#Not({S #Equals "true"})` beside `#Not({S #Equals "false"})` holds at
/// `S = "abc"`.
#[test]
fn a_string_spelled_true_or_false_is_not_a_boolean_literal() {
    for with_head in [false, true] {
        let definition = definition(
            r#"  syntax Int ::= hs(String) [function, symbol(hs)]
  rule [a]: hs(S) => 1 requires #Not({ S #Equals "true" })
  rule [b]: hs(S) => 2 requires #Not({ S #Equals "false" })"#,
            with_head,
        );
        let all = definition.value_claims_in_scope(CheckScope::All);
        let pairs = pairs_between(&all, "a", "b");
        assert_eq!(
            pairs
                .iter()
                .map(|pair| pair.reason.clone())
                .collect::<Vec<_>>(),
            [UnjoinedReason::ConditionOpen],
            "with the head: {with_head}: {:?}",
            all.unjoined()
        );
    }
}

/// With the anywhere head `nw` in reach of `hg`'s second argument, the load itself classifies the
/// `hg` pair: guarded by the Boolean-like spellings it is reported and withdraws the claims of
/// `hg` and `nw`, exactly as with any other two spellings of the token sort.
#[test]
fn the_load_reports_a_pair_guarded_by_token_spellings_of_true_and_false() {
    for (first, second) in [("true", "false"), ("aaa", "bbb")] {
        let definition = definition(
            &format!(
                r#"  syntax Int ::= hg(MyTok, Wrap) [function, symbol(hg)]
  rule [c]: hg(T, _W) => 1 requires T =/=K #token("{first}", "MyTok")
  rule [d]: hg(T, _W) => 2 requires T =/=K #token("{second}", "MyTok")"#
            ),
            true,
        );
        let load = definition.value_claims();
        let pairs = pairs_between(load, "c", "d");
        assert_eq!(
            pairs
                .iter()
                .map(|pair| pair.reason.clone())
                .collect::<Vec<_>>(),
            [UnjoinedReason::ConditionOpen],
            "{first}/{second}: {:?}",
            load.unjoined()
        );
        let tainted = load.tainted_symbols();
        for symbol in ["Lblhg", "Lblnw"] {
            assert!(
                tainted.iter().any(|name| name.as_ref() == symbol),
                "{first}/{second}: {symbol} is not tainted: {tainted:?}"
            );
        }
    }
}

/// A join step that skips a priority group must not read such spellings as complementary either.
/// `p: f(T) => g(T)` beside `q: f(_T) => 0` joins only if `g(T)` reaches 0 on every instance; it
/// does not, since `g1` gives `g(abc) = 5` before the lower group `g2` is reached. Reading the
/// two guards of `g1` as complementary would skip `g1` at the join step and join the pair. The
/// same over `String`, and with the control spellings `aaa` and `bbb`.
#[test]
fn a_join_step_does_not_skip_a_group_guarded_by_true_and_false_spellings() {
    for (first, second) in [("true", "false"), ("aaa", "bbb")] {
        for declarations in [
            format!(
                r#"  syntax Int ::= f(MyTok) [function, symbol(f)] | g(MyTok) [function, symbol(g)]
  rule [p]: f(T) => g(T)
  rule [q]: f(_T) => 0
  rule [g1]: g(T) => 5 requires T =/=K #token("{first}", "MyTok") andBool T =/=K #token("{second}", "MyTok") [priority(40)]
  rule [g2]: g(_T) => 0 [priority(50)]"#
            ),
            format!(
                r#"  syntax Int ::= f(String) [function, symbol(f)] | g(String) [function, symbol(g)]
  rule [p]: f(S) => g(S)
  rule [q]: f(_S) => 0
  rule [g1]: g(S) => 5 requires #Not({{ S #Equals "{first}" }}) #And #Not({{ S #Equals "{second}" }}) [priority(40)]
  rule [g2]: g(_S) => 0 [priority(50)]"#
            ),
        ] {
            for with_head in [false, true] {
                let definition = definition(&declarations, with_head);
                let all = definition.value_claims_in_scope(CheckScope::All);
                let pairs = pairs_between(&all, "p", "q");
                assert_eq!(
                    pairs
                        .iter()
                        .map(|pair| pair.reason.clone())
                        .collect::<Vec<_>>(),
                    [UnjoinedReason::DifferentResults],
                    "{declarations} (with the head: {with_head}): {:?}",
                    all.unjoined()
                );
            }
        }
    }
}

/// A sort hooked `BOOL.Bool` has exactly the values `true` and `false`, so `B` differing from
/// both holds on no instance: the pair stays refuted, the load names nothing and keeps the claims
/// of `hm`, in both scopes and whether the guards are written with `#Not` or `=/=K`. The token
/// productions only give `MyBool` a token declaration, which `#token(_, "MyBool")` needs.
#[test]
fn a_sort_hooked_bool_keeps_its_complementary_literals() {
    for (first, second) in [
        (
            r#"#Not({ B #Equals #token("true", "MyBool") })"#,
            r#"#Not({ B #Equals #token("false", "MyBool") })"#,
        ),
        (
            r#"B =/=K #token("true", "MyBool")"#,
            r#"B =/=K #token("false", "MyBool")"#,
        ),
    ] {
        let definition = definition(
            &format!(
                r#"  syntax MyBool [hook(BOOL.Bool)]
  syntax MyBool ::= "tt" [token] | "ff" [token]
  syntax Int ::= hm(MyBool, Wrap) [function, symbol(hm)]
  rule [a]: hm(B, _W) => 1 requires {first}
  rule [b]: hm(B, _W) => 2 requires {second}"#
            ),
            true,
        );
        let load = definition.value_claims();
        assert!(
            pairs_between(load, "a", "b").is_empty(),
            "{:?}",
            load.unjoined()
        );
        assert!(
            !load
                .tainted_symbols()
                .iter()
                .any(|name| name.as_ref() == "Lblhm"),
            "{:?}",
            load.tainted_symbols()
        );
        let all = definition.value_claims_in_scope(CheckScope::All);
        assert!(
            pairs_between(&all, "a", "b").is_empty(),
            "{:?}",
            all.unjoined()
        );
    }
}

/// The request's acceptance: `f(I) => 1 requires I >Int 0` beside `f(I) => 2 requires I >Int -5`
/// overlap on `I = 1` with different results, so the full check reports one non-joined pair of
/// `f`'s two equations, in a definition that declares nothing a pair could withdraw and with no
/// symbol added for the check's sake. With `I <=Int 0` as the second guard the requires hold on
/// no integer, and no pair of `f` is reported.
#[test]
fn the_full_check_reports_the_pairs_of_a_definition_with_only_declared_functions() {
    for (second, expected) in [
        ("I >Int -5", vec![UnjoinedReason::ConditionOpen]),
        ("I <=Int 0", Vec::new()),
    ] {
        let definition = definition(
            &format!(
                "  syntax Int ::= f(Int) [function, symbol(f)]
  rule [a]: f(I) => 1 requires I >Int 0
  rule [b]: f(I) => 2 requires {second}"
            ),
            false,
        );
        assert!(definition.value_claims().unjoined().is_empty());
        let all = definition.value_claims_in_scope(CheckScope::All);
        assert_eq!(all.counts().skipped, 0);
        let pairs = pairs_between(&all, "a", "b");
        assert_eq!(
            pairs
                .iter()
                .map(|pair| pair.reason.clone())
                .collect::<Vec<_>>(),
            expected,
            "{second}: {:?}",
            all.unjoined()
        );
        assert!(pairs.iter().all(|pair| pair.withdrawn.is_empty()));
    }
}

/// The request's acceptance, per group: the full check classifies the one root pair of `f`'s
/// group of two equations, and the group says how it was decided (not joined with `I >Int -5`,
/// refuted with `I <=Int 0`).
#[test]
fn the_full_check_counts_the_pairs_of_each_group() {
    for (second, refuted, not_joined) in [("I >Int -5", 0, 1), ("I <=Int 0", 1, 0)] {
        let definition = definition(
            &format!(
                "  syntax Int ::= f(Int) [function, symbol(f)]
  rule [a]: f(I) => 1 requires I >Int 0
  rule [b]: f(I) => 2 requires {second}"
            ),
            false,
        );
        let all = definition.value_claims_in_scope(CheckScope::All);
        let groups = all
            .group_counts()
            .iter()
            .filter(|(key, _)| key.index == TermIndex::Symbol("Lblf".into()))
            .map(|(_, counts)| *counts)
            .collect::<Vec<_>>();
        assert_eq!(groups.len(), 1, "{second}: {:?}", all.group_counts());
        let f = groups[0];
        assert_eq!(
            (
                f.equations,
                f.root_pairs,
                f.skipped,
                f.refuted,
                f.not_joined
            ),
            (2, 1, 0, refuted, not_joined),
            "{second}: {f:?}"
        );
    }
}

/// The verdicts of the full check on the pair of `rules` (labelled `a` and `b`), in a definition
/// with nothing to withdraw: the reasons of the non-joined pairs between them.
fn reasons_between_a_and_b(rules: &str) -> Vec<UnjoinedReason> {
    let definition = definition(rules, false);
    let all = definition.value_claims_in_scope(CheckScope::All);
    pairs_between(&all, "a", "b")
        .iter()
        .map(|pair| pair.reason.clone())
        .collect()
}

/// Changing a guard's integer constant keeps a consistent definition shown consistent: the
/// comparisons of one term with literals bound it to no integer, in every build.
#[test]
fn requires_that_bound_one_integer_to_nothing_refute_the_pair() {
    let declaration = "  syntax Int ::= gn(Int) [function, symbol(gn)]";
    assert_eq!(
        reasons_between_a_and_b(&format!(
            "{declaration}
  rule [a]: gn(X) => X +Int 1 requires X >Int 5
  rule [b]: gn(X) => 0 requires X <=Int 0"
        )),
        []
    );
    assert_eq!(
        reasons_between_a_and_b(&format!(
            "{declaration}
  rule [a]: gn(X) => X +Int 1 requires X >=Int -5
  rule [b]: gn(X) => 0 requires X <Int 0"
        )),
        [UnjoinedReason::ConditionOpen]
    );
}

/// Over a partial term `X /Int Y`: complementary comparisons stay refuted by their literals, and
/// two negated bounds whose definedness arrives only as a sibling conjunct are not refuted.
#[test]
fn negated_bounds_of_a_partial_term_are_refuted_only_as_complementary_literals() {
    let declaration = "  syntax Int ::= gd(Int, Int) [function, symbol(gd)]";
    assert_eq!(
        reasons_between_a_and_b(&format!(
            "{declaration}
  rule [a]: gd(X, Y) => 1 requires notBool (X /Int Y >Int 5)
  rule [b]: gd(X, Y) => 2 requires notBool (X /Int Y <=Int 5)"
        )),
        []
    );
    // A known non-refutation (sound): after simplification the conjuncts are the two negated
    // bounds `X /Int Y <=Int 5` and `X /Int Y >=Int 6`, each true also where `X /Int Y` is
    // undefined, and the definedness of `X /Int Y` (`Y =/=Int 0`) is a sibling conjunct that no
    // syntactic rule links to the quotient, so the bounds are not used.
    assert_eq!(
        reasons_between_a_and_b(&format!(
            "{declaration}
  rule [a]: gd(X, Y) => 1 requires notBool (X /Int Y >Int 5)
  rule [b]: gd(X, Y) => 2 requires notBool (X /Int Y <Int 6)"
        )),
        [UnjoinedReason::ConditionOpen]
    );
}

/// FZ-POLISH: `f(I) => 1 requires I <Int 0` beside `f(-1) => 2` overlap at `I = -1`, where the
/// condition `-1 <Int 0` simplifies to `true`. The results differ wherever the overlap is
/// defined, so the pair is reported with what the join found, `DifferentResults`, not
/// `ConditionOpen`; and with `I >Int 0` in place of the guard the pair is refuted.
#[test]
fn a_pair_whose_conditions_simplify_to_true_keeps_different_results() {
    for (guard, expected) in [
        ("I <Int 0", vec![UnjoinedReason::DifferentResults]),
        ("I >Int 0", Vec::new()),
    ] {
        let definition = definition(
            &format!(
                "  syntax Int ::= f(Int) [function, symbol(f)]
  rule [a]: f(I) => 1 requires {guard}
  rule [b]: f(-1) => 2"
            ),
            false,
        );
        let all = definition.value_claims_in_scope(CheckScope::All);
        let pairs = pairs_between(&all, "a", "b");
        assert_eq!(
            pairs
                .iter()
                .map(|pair| pair.reason.clone())
                .collect::<Vec<_>>(),
            expected,
            "{guard}: {:?}",
            all.unjoined()
        );
    }
}

/// FZ-POLISH: the pair above records its simplified conditions (`true`), and the data
/// judgement marks it genuine with the ground instance `f(-1)`, whose reducts are `1` and `2`;
/// a pair under a guard the instances do not decide is recorded with its open conditions and
/// stays undecided.
#[test]
fn a_pair_with_different_results_on_a_ground_instance_is_genuine() {
    let holds = definition(
        "  syntax Int ::= f(Int) [function, symbol(f)]
  rule [a]: f(I) => 1 requires I <Int 0
  rule [b]: f(-1) => 2",
        false,
    );
    let all = holds.value_claims_in_scope(CheckScope::All);
    let [pair] = pairs_between(&all, "a", "b")[..] else {
        panic!("one pair: {:?}", all.unjoined());
    };
    assert_eq!(pair.conditions, Some(k_rust_backend::rule::Predicate::True));
    let heads = holds.data_heads();
    let genuine = heads
        .findings()
        .iter()
        .filter(|finding| finding.is_genuine())
        .collect::<Vec<_>>();
    assert_eq!(genuine.len(), 1, "{:?}", heads.findings());
    let instance = genuine[0].instance().expect("genuine");
    let values = [&instance.values.0, &instance.values.1];
    assert!(
        values.contains(&&k_rust_backend::term::Term::int(1))
            && values.contains(&&k_rust_backend::term::Term::int(2)),
        "{instance:?}"
    );

    let open = definition(
        r#"  syntax Int ::= ht(MyTok) [function, symbol(ht)]
  rule [a]: ht(T) => 1 requires T =/=K #token("true", "MyTok")
  rule [b]: ht(T) => 2 requires T =/=K #token("false", "MyTok")"#,
        false,
    );
    let all = open.value_claims_in_scope(CheckScope::All);
    let [pair] = pairs_between(&all, "a", "b")[..] else {
        panic!("one pair: {:?}", all.unjoined());
    };
    assert!(
        pair.conditions
            .as_ref()
            .is_some_and(|conditions| *conditions != k_rust_backend::rule::Predicate::True),
        "{pair:?}"
    );
    assert!(
        open.data_heads()
            .findings()
            .iter()
            .all(|finding| !finding.is_genuine())
    );
}

/// The genuine findings of `definition`'s full check between the equations labelled `first` and
/// `second`, and whether the check reports such a pair at all.
fn genuine_between(
    definition: &BackendDefinition,
    first: &str,
    second: &str,
) -> (bool, Vec<k_rust_backend::data_term::GroundInstance>) {
    let (first, second) = (format!("PAIRS.{first}"), format!("PAIRS.{second}"));
    let label = |rule: &k_rust_backend::rule::RewriteRule| rule.attributes.label.clone();
    let heads = definition.data_heads();
    let pairs = heads
        .findings()
        .iter()
        .filter(|finding| {
            finding.pair().is_some_and(|pair| {
                let labels = (label(&pair.first), label(&pair.second));
                labels == (Some(first.clone()), Some(second.clone()))
                    || labels == (Some(second.clone()), Some(first.clone()))
            })
        })
        .collect::<Vec<_>>();
    (
        !pairs.is_empty(),
        pairs
            .iter()
            .filter_map(|finding| finding.instance().cloned())
            .collect(),
    )
}

/// FZ-POLISH review B1 (`prio/b.k`): `f(0) => 3 [priority(10)]` takes every input where the
/// guards of the two priority-50 equations hold, so they apply nowhere and the definition is
/// confluent. The check still reports their pair (it pairs within one priority group), but the
/// instance `f(0)` is no instance where both apply: undecided, never genuine.
#[test]
fn a_pair_a_higher_priority_equation_preempts_is_not_genuine() {
    let definition = definition(
        "  syntax Int ::= f(Int) [function, symbol(f)]
  rule [p]: f(0) => 3 [priority(10)]
  rule [a]: f(X) => 1 requires X ==Int 0
  rule [b]: f(X) => 2 requires X ==Int 0",
        false,
    );
    let (reported, genuine) = genuine_between(&definition, "a", "b");
    assert!(reported);
    assert!(genuine.is_empty(), "{genuine:?}");
}

/// FZ-POLISH review B1 (`prio/o.k`): `g(X) => 3 requires X <=Int 0` beside two `owise`
/// equations: the pair really is not confluent, at `g(1)`, and that is the instance exhibited,
/// never `g(0)`, where the priority-50 equation applies.
#[test]
fn an_owise_pair_is_exhibited_where_both_owise_equations_apply() {
    let definition = definition(
        "  syntax Int ::= g(Int) [function, total, symbol(g)]
  rule [p]: g(X) => 3 requires X <=Int 0
  rule [a]: g(_) => 1 [owise]
  rule [b]: g(_) => 2 [owise]",
        false,
    );
    let (reported, genuine) = genuine_between(&definition, "a", "b");
    assert!(reported);
    let [instance] = &genuine[..] else {
        panic!("one genuine instance: {genuine:?}");
    };
    let k_rust_backend::term::TermKind::Application { arguments, .. } = instance.overlap.kind()
    else {
        panic!("an application: {instance:?}");
    };
    assert_eq!(
        arguments[0],
        k_rust_backend::term::Term::int(1),
        "{instance:?}"
    );
}

/// FZ-POLISH review B1 (`mapdup/b.k`): `m(K |-> _ M) => 1 requires K in_keys(M)` applies at no
/// defined map (in a well-formed `K |-> _ M`, `K` is never a key of `M`), so `m` is 0 everywhere.
/// An instance holding a map with a repeated key is `\bottom` and proves nothing: undecided.
#[test]
fn an_instance_with_a_repeated_map_key_is_not_genuine() {
    let definition = definition_importing(
        "  imports MAP",
        "  syntax Int ::= m(Map) [function, symbol(m)]
  rule [a]: m(K |-> _ M) => 1 requires K in_keys(M)
  rule [b]: m(_:Map) => 0",
        false,
    );
    let (reported, genuine) = genuine_between(&definition, "a", "b");
    assert!(reported);
    assert!(genuine.is_empty(), "{genuine:?}");
}

/// FZ-POLISH review round 3: `q(_) => a` beside `q(_) => bb`, with `a` and `bb` of the sorts `A`
/// and `B` below `AB`: at `q(0)` both equations apply and the input has two normal forms,
/// `inj{A,AB}(a)` and `inj{B,AB}(bb)` (different on k-rust's internal normal form, whatever a
/// model may identify), so the finding is genuine; with `a` and `bb` of one sort as well.
#[test]
fn values_injected_from_different_sorts_are_two_normal_forms() {
    for declarations in [
        r#"  syntax A ::= "a" [symbol(a)]
  syntax B ::= "bb" [symbol(bb)]
  syntax AB ::= A | B"#,
        r#"  syntax AB ::= "a" [symbol(a)] | "bb" [symbol(bb)]"#,
    ] {
        let definition = definition(
            &format!(
                "{declarations}
  syntax AB ::= q(Int) [function, total, symbol(q)]
  rule [a]: q(_) => a
  rule [b]: q(_) => bb"
            ),
            false,
        );
        let (reported, genuine) = genuine_between(&definition, "a", "b");
        assert!(reported, "{declarations}");
        assert_eq!(genuine.len(), 1, "{declarations}: {genuine:?}");
    }
}

/// FZ-POLISH review rounds 2 and 3 (`r2-mapkeys`): `mk((a |-> _) (bb |-> _)) => 1` beside
/// `mk(_:Map) => 0`. The instance's map is keyed by the distinct normal forms `inj{A,KItem}(a)`
/// and `inj{B,KItem}(bb)`, both equations apply there, and the input has the two normal forms 1
/// and 0: genuine, whether `a` and `bb` share a sort or not.
#[test]
fn an_instance_keyed_by_distinct_normal_forms_is_genuine() {
    for declarations in [
        r#"  syntax A ::= "a" [symbol(a)]
  syntax B ::= "bb" [symbol(bb)]"#,
        r#"  syntax AB ::= "a" [symbol(a)] | "bb" [symbol(bb)]"#,
    ] {
        let definition = definition_importing(
            "  imports MAP",
            &format!(
                "{declarations}
  syntax Int ::= mk(Map) [function, symbol(mk)]
  rule [a]: mk((a |-> _:Int) (bb |-> _:Int)) => 1
  rule [b]: mk(_:Map) => 0"
            ),
            false,
        );
        let (reported, genuine) = genuine_between(&definition, "a", "b");
        assert!(reported, "{declarations}");
        assert_eq!(genuine.len(), 1, "{declarations}: {genuine:?}");
    }
}

/// FZ-POLISH review round 3 (`r3-indirect`): `p(X) => g(X)` beside `p(_) => 1`, where
/// `g(X) => h(X)`, `h(a) => 1` and `h(_) => 0 [owise]`, and `q(X) => e(X)` beside
/// `q(_) => true`, where `e(X) => X ==K a`. At `p(bb)` the input has the normal forms 0 and 1,
/// at `q(bb)` false and true: genuine, as k-rust's evaluation reads them.
#[test]
fn an_input_with_two_normal_forms_through_other_equations_is_genuine() {
    let definition = definition(
        r#"  syntax A ::= "a" [symbol(a)]
  syntax B ::= "bb" [symbol(bb)]
  syntax AB ::= A | B
  syntax Int ::= h(AB) [function, total, symbol(h)]
  rule h(a) => 1
  rule h(_) => 0 [owise]
  syntax Int ::= g(AB) [function, total, symbol(g)]
  rule g(X) => h(X)
  syntax Int ::= p(AB) [function, total, symbol(p)]
  rule [p1]: p(X) => g(X)
  rule [p2]: p(_) => 1
  syntax Bool ::= e(AB) [function, total, symbol(e)]
  rule e(X) => X ==K a
  syntax Bool ::= qq(AB) [function, total, symbol(qq)]
  rule [q1]: qq(X) => e(X)
  rule [q2]: qq(_) => true"#,
        false,
    );
    for (first, second) in [("p1", "p2"), ("q1", "q2")] {
        let (reported, genuine) = genuine_between(&definition, first, second);
        assert!(reported, "{first}");
        assert_eq!(genuine.len(), 1, "{first}: {genuine:?}");
    }
}

/// Every executable equation `domains.md` writes at a hooked symbol, in a module importing every
/// domains module: each one at a hook the evaluator applies joins every equation of its hook's
/// written meaning, none is at an evaluated hook without one, and the nine at `STRING.findChar`,
/// `rfindChar`, `replaceFirst`, `replace` and `LIST.push`, hooks no builtin implements, are read
/// as their hooks' meaning and paired with nothing. `replaceAll`'s equation joins the guarded
/// lemma of its meaning, since `replace` is read by exactly domains.md's two equations here.
#[test]
fn the_domains_equations_at_hooked_symbols_agree_with_their_hooks() {
    let source = r#"module ALL-DOMAINS
  imports DOMAINS
  imports ARRAY
  imports RANGEMAP
  imports COLLECTIONS
  imports FLOAT
  imports STRING
  imports STRING-BUFFER
  imports BYTES
  imports ID
  imports K-EQUAL
  imports K-REFLECTION
  imports K-IO
  imports MINT
  syntax Prog ::= go(Int) [symbol(go)]
  configuration <k> $PGM:Prog </k>
endmodule
"#;
    let kore = compile(source, "ALL-DOMAINS");
    let mut backend = Backend::new(&kore, "ALL-DOMAINS", BackendOptions::default()).unwrap();
    let definition = backend.select_definition(None).unwrap();
    let all = definition.value_claims_in_scope(CheckScope::All);
    let counts = all.counts();
    assert!(all.unjoined().is_empty(), "{:#?}", all.unjoined());
    assert_eq!(
        (
            counts.hook.unevaluated,
            counts.hook.unmodelled,
            counts.hook.not_joined
        ),
        (9, 0, 0),
        "{:?}",
        counts.hook
    );
    assert_eq!(counts.hook.equations, 41, "{:?}", counts.hook);
    assert!(counts.hook.joined > 0);
}

/// Class C of the WASM pairs: two equations whose `requires` give one string term two different
/// literals (`unescape`'s `\t` and `\n` rules) are refuted, and so is one whose literal, put in
/// the other's condition, evaluates it to false (`findChar` of the hex digits on `"t"`). The
/// same literal on both sides is a genuine overlap, and a literal of a substring outside the valid
/// indices is not substituted into anything that decides it.
#[test]
fn string_equalities_refute_two_literals_and_substitute_one() {
    let declaration = "  syntax Int ::= un(String, Int) [function, symbol(un)]";
    assert_eq!(
        reasons_between_a_and_b(&format!(
            r#"{declaration}
  rule [a]: un(S, I) => 1 requires substrString(S, I, I +Int 1) ==K "t"
  rule [b]: un(S, I) => 2 requires substrString(S, I, I +Int 1) ==K "n""#
        )),
        []
    );
    assert_eq!(
        reasons_between_a_and_b(&format!(
            r#"{declaration}
  rule [a]: un(S, I) => 1 requires findChar("0123456789abcdefABCDEF", substrString(S, I, I +Int 1), 0) =/=Int -1
  rule [b]: un(S, I) => 2 requires substrString(S, I, I +Int 1) ==K "t""#
        )),
        []
    );
    assert_eq!(
        reasons_between_a_and_b(&format!(
            r#"{declaration}
  rule [a]: un(S, I) => 1 requires substrString(S, I, I +Int 1) ==String "t"
  rule [b]: un(S, I) => 2 requires substrString(S, I, I +Int 1) ==String "t""#
        )),
        [UnjoinedReason::ConditionOpen]
    );
    assert_eq!(
        reasons_between_a_and_b(&format!(
            r#"{declaration}
  rule [a]: un(S, I) => 1 requires I ==Int lengthString(S) -Int 1
  rule [b]: un(S, I) => 2 requires substrString(S, I +Int 1, I +Int 2) ==K "u""#
        )),
        [UnjoinedReason::ConditionOpen]
    );
}

/// Class B of the WASM pairs: comparisons over shared atoms read as linear forms. `unescape`'s end
/// rule (`I ==Int lengthString(S) -Int 1`) against its escape rules (`I <Int lengthString(S)
/// -Int 3`) is refuted (the simplifier substitutes `I`, leaving a constant comparison), and so is
/// `lengthBytes(B) <Int N` beside `lengthBytes(B) >Int N` (a negative cycle), and a size below
/// zero (a range fact). A shared atom with a satisfiable gap stays a genuine overlap.
#[test]
fn comparisons_over_shared_atoms_are_refuted_by_their_differences() {
    let strings = "  syntax Int ::= un(String, Int) [function, symbol(un)]";
    assert_eq!(
        reasons_between_a_and_b(&format!(
            r#"{strings}
  rule [a]: un(S, I) => 1 requires I ==Int lengthString(S) -Int 1
  rule [b]: un(S, I) => 2 requires I <Int lengthString(S) -Int 3"#
        )),
        []
    );
    assert_eq!(
        reasons_between_a_and_b(&format!(
            r#"{strings}
  rule [a]: un(S, N) => 1 requires lengthString(S) <Int N
  rule [b]: un(S, N) => 2 requires lengthString(S) >Int N"#
        )),
        []
    );
    assert_eq!(
        reasons_between_a_and_b(&format!(
            r#"{strings}
  rule [a]: un(S, N) => 1 requires lengthString(S) <Int 0
  rule [b]: un(S, N) => 2"#
        )),
        []
    );
    assert_eq!(
        reasons_between_a_and_b(&format!(
            r#"{strings}
  rule [a]: un(S, N) => 1 requires lengthString(S) <Int N
  rule [b]: un(S, N) => 2 requires lengthString(S) +Int 2 >Int N"#
        )),
        [UnjoinedReason::ConditionOpen]
    );
}

/// Class D of the WASM pairs: the unifier does not decide a list with fixed elements at both ends,
/// so it drops that equation, solves the rest, and the pair is refuted when the conditions fail at
/// every relaxed solution (`I = 0` beside `I <Int 0`); where they may hold (`I <=Int 0`), the pair
/// stays undecided.
#[test]
fn an_undecided_list_equation_is_deferred_and_the_conditions_refute_the_rest() {
    let declaration = "  syntax Int ::= gl(List, Int) [function, symbol(gl)]";
    assert_eq!(
        reasons_between_a_and_b(&format!(
            "{declaration}
  rule [a]: gl(ListItem(V:Int) _:List, 0) => V
  rule [b]: gl(_:List ListItem(V:Int), I) => V +Int 1 requires I <Int 0"
        )),
        []
    );
    assert_eq!(
        reasons_between_a_and_b(&format!(
            "{declaration}
  rule [a]: gl(ListItem(V:Int) _:List, 0) => V
  rule [b]: gl(_:List ListItem(V:Int), I) => V +Int 1 requires I <=Int 0"
        )),
        [UnjoinedReason::Unresolved(
            k_rust_backend::confluence::UnresolvedShape::Collection
        )]
    );
}

/// Class E of the WASM pairs: a disjunction in a condition is split into its cases, and the pair
/// is refuted when every case is (`S <Int 0 orBool E <Int S` beside `0 <=Int S andBool S <=Int
/// E`); when one case is satisfiable (`E <Int S` beside `0 <=Int S`), it stays a genuine overlap.
#[test]
fn a_disjunction_is_refuted_when_each_of_its_cases_is() {
    let declaration = "  syntax Int ::= gr(Int, Int) [function, symbol(gr)]";
    assert_eq!(
        reasons_between_a_and_b(&format!(
            "{declaration}
  rule [a]: gr(S, E) => 1 requires S <Int 0 orBool E <Int S
  rule [b]: gr(S, E) => 2 requires 0 <=Int S andBool S <=Int E"
        )),
        []
    );
    assert_eq!(
        reasons_between_a_and_b(&format!(
            "{declaration}
  rule [a]: gr(S, E) => 1 requires S <Int 0 orBool E <Int S
  rule [b]: gr(S, E) => 2 requires 0 <=Int S"
        )),
        [UnjoinedReason::ConditionOpen]
    );
}

/// The hook pairs of the full check whose first equation is labelled `label` in module `PAIRS`,
/// with their reasons, and the per-equation `UnmodelledHook` reports of it.
fn hook_findings(claims: &ValueClaims, label: &str) -> Vec<String> {
    let label = format!("PAIRS.{label}");
    claims
        .unjoined()
        .iter()
        .filter(|pair| pair.first.attributes.label.as_deref() == Some(label.as_str()))
        .filter(|pair| {
            pair.hook.is_some() || matches!(pair.reason, UnjoinedReason::UnmodelledHook(_))
        })
        .map(|pair| format!("{:?} {}", pair.hook, pair.reason))
        .collect()
}

/// Review A, B1: a written meaning may name only builtins the evaluator applies. `replaceAll`'s
/// meaning used to read `replace`, whose meaning is whatever the definition's equations say, so a
/// second symbol hooked to `STRING.replace` with a false equation made a false `replaceAll`
/// equation join its hook. The meaning is now written over `findString`, `substrString`,
/// `lengthString` and `+String`, and the false equation is named against it.
#[test]
fn a_written_meaning_reads_no_equation_of_the_definition() {
    let definition = definition(
        r##"  syntax String ::= "#aReplace" "(" String "," String "," String "," Int ")" [function, hook(STRING.replace)]
                  | myReplaceAll(String, String, String) [function, hook(STRING.replaceAll)]
  rule [twin]: #aReplace(S, _, _, _) => S
  rule [mine]: myReplaceAll(S, T, R) => #aReplace(S, T, R, countAllOccurrences(S, T))"##,
        false,
    );
    let all = definition.value_claims_in_scope(CheckScope::All);
    let findings = hook_findings(&all, "mine");
    assert!(!findings.is_empty(), "{:#?}", all.unjoined());
    // `#aReplace`'s equation is not domains.md's, so `replace` is still read by exactly
    // domains.md's equations, the guarded lemma is built, and domains.md's `replaceAll` equation
    // joins it: the only hook pairs named are `mine`'s.
    assert!(
        all.unjoined()
            .iter()
            .filter(|pair| pair.hook.is_some())
            .all(|pair| pair.first.attributes.label.as_deref() == Some("PAIRS.mine")),
        "{:#?}",
        all.unjoined()
    );
    assert!(
        findings
            .iter()
            .all(|finding| finding.starts_with("Some(\"STRING.replaceAll\")")),
        "{findings:?}"
    );
}

/// Review A, S1: helpers are found by hook, arity and argument and result sorts among every
/// candidate. A symbol hooked to `INT.lt` at another Bool-domain sort (whose values the builtin
/// never gives) is passed over for `_<Int_`, so `INT.min`'s meaning is built and a correct
/// `minInt`-style equation joins it.
#[test]
fn a_helper_of_another_result_sort_is_passed_over() {
    let definition = definition(
        r##"  syntax MyBool [hook(BOOL.Bool)]
  syntax MyBool ::= "#lt" "(" Int "," Int ")" [function, hook(INT.lt)]
  syntax Int ::= myMin(Int, Int) [function, hook(INT.min)]
  rule [mine]: myMin(X, Y) => Y requires X >=Int Y"##,
        false,
    );
    let all = definition.value_claims_in_scope(CheckScope::All);
    assert_eq!(hook_findings(&all, "mine"), Vec::<String>::new());
    assert!(
        !all.unjoined()
            .iter()
            .any(|pair| matches!(&pair.reason, UnjoinedReason::UnmodelledHook(hook) if hook.as_ref() == "INT.min")),
        "{:#?}",
        all.unjoined()
    );
}

/// Review A, N1: a symbol hooked at another arity than its hook's is no application of the
/// builtin, and gets no written meaning: its equation is reported as at an unmodelled hook.
#[test]
fn a_symbol_hooked_at_another_arity_gets_no_written_meaning() {
    let definition = definition(
        r#"  syntax Bool ::= myAnd(Bool, Bool, Bool) [function, hook(BOOL.and)]
  rule [mine]: myAnd(B, _, _) => B"#,
        false,
    );
    let all = definition.value_claims_in_scope(CheckScope::All);
    assert_eq!(
        hook_findings(&all, "mine"),
        vec![format!(
            "None {}",
            UnjoinedReason::UnmodelledHook("BOOL.and".into())
        )]
    );
}

/// Review B, item 1: the range facts of `minInt` and `maxInt` bound them by their operands in the
/// right direction. `minInt(X, Y) <Int X` beside `Y <Int X` holds at `X = 1, Y = 0`, a genuine
/// overlap with different results, and so does `maxInt(X, Y) >Int X` beside `Y >Int X`.
#[test]
fn min_and_max_bound_their_operands_in_the_right_direction() {
    let declaration = "  syntax Int ::= mm(Int, Int) [function, symbol(mm)]";
    assert_eq!(
        reasons_between_a_and_b(&format!(
            "{declaration}
  rule [a]: mm(X, Y) => 1 requires minInt(X, Y) <Int X
  rule [b]: mm(X, Y) => 2 requires Y <Int X"
        )),
        [UnjoinedReason::ConditionOpen]
    );
    assert_eq!(
        reasons_between_a_and_b(&format!(
            "{declaration}
  rule [a]: mm(X, Y) => 1 requires maxInt(X, Y) >Int X
  rule [b]: mm(X, Y) => 2 requires Y >Int X"
        )),
        [UnjoinedReason::ConditionOpen]
    );
    // With the operand outside the bound, the pair is refuted: `minInt(X, Y) >Int X` holds on no
    // instance.
    assert_eq!(
        reasons_between_a_and_b(&format!(
            "{declaration}
  rule [a]: mm(X, Y) => 1 requires minInt(X, Y) >Int X
  rule [b]: mm(X, Y) => 2"
        )),
        []
    );
}

/// Coordinator's decision on domains.md 1917: `replaceAll(S, T, R) = replace(S, T, R,
/// countAllOccurrences(S, T))` is part of `replaceAll`'s written meaning only while `replace` is
/// read by exactly domains.md's two equations. A higher-priority `replace` equation changes what
/// `replace` means, so the lemma is absent, and domains.md's `replaceAll` equation, which now
/// disagrees with the builtin, is named against the meaning written by `findString`,
/// `substrString`, `lengthString` and `+String`.
#[test]
fn a_redefined_replace_leaves_the_replace_all_equation_unshown() {
    let definition = definition(
        "  rule [mine]: replace(S, _, _, _) => S [priority(10)]",
        false,
    );
    let all = definition.value_claims_in_scope(CheckScope::All);
    let replace_all = all
        .unjoined()
        .iter()
        .filter(|pair| pair.hook.as_deref() == Some("STRING.replaceAll"))
        .map(|pair| pair.second.attributes.label.clone().unwrap_or_default())
        .collect::<Vec<_>>();
    assert!(!replace_all.is_empty(), "{:#?}", all.unjoined());
    assert!(
        replace_all
            .iter()
            .all(|label| label == "STRING.replaceAll meaning 1"
                || label == "STRING.replaceAll meaning 2"),
        "{replace_all:?}"
    );
}

/// Review A round 2: the guard on `replaceAll`'s lemma reads the content of `replace`'s
/// equations, not where they came from. A user's `replace`-hooked symbol with exactly
/// domains.md's two rows qualifies (it is the same function), so an equation stating the lemma
/// with it joins; with row A's `Count -Int 1` changed to `Count -Int 2`, or row B's `requires`
/// dropped, it does not, and the equation that reads it is reported.
#[test]
fn the_replace_all_lemma_is_guarded_by_the_content_of_the_replace_rows() {
    let rows = |step: &str, guard: &str| {
        format!(
            r#"  syntax String ::= myReplace(String, String, String, Int) [function, hook(STRING.replace)]
                  | myReplaceAll(String, String, String) [function, hook(STRING.replaceAll)]
  rule myReplace(Source:String, ToReplace:String, Replacement:String, Count:Int) =>
       substrString(Source, 0, findString(Source, ToReplace, 0)) +String Replacement +String
       myReplace(substrString(Source, findString(Source, ToReplace, 0) +Int lengthString(ToReplace), lengthString(Source)), ToReplace, Replacement, Count -Int {step})
        requires Count >Int 0 andBool findString(Source, ToReplace, 0) >=Int 0
  rule myReplace(Source:String, _, _, Count) => Source {guard} [owise]
  rule [mine]: myReplaceAll(S, T, R) => myReplace(S, T, R, countAllOccurrences(S, T))"#
        )
    };
    for (step, guard, joins) in [
        ("1", "requires Count >=Int 0", true),
        ("2", "requires Count >=Int 0", false),
        ("1", "", false),
    ] {
        let definition = definition(&rows(step, guard), false);
        let all = definition.value_claims_in_scope(CheckScope::All);
        let findings = hook_findings(&all, "mine");
        assert_eq!(findings.is_empty(), joins, "{step} {guard:?}: {findings:?}");
        // domains.md's own `replace` still qualifies, so its `replaceAll` equation joins.
        assert!(
            all.unjoined()
                .iter()
                .filter(|pair| pair.hook.is_some())
                .all(|pair| pair.first.attributes.label.as_deref() == Some("PAIRS.mine")),
            "{step} {guard:?}: {:#?}",
            all.unjoined()
        );
    }
}
