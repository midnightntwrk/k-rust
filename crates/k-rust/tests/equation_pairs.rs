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

/// FZ-POLISH review B1 (b) and S1: `q(_) => a` beside `q(_) => bb`, with `a` and `bb` of the
/// sorts `A` and `B` below `AB`, equate `inj{A,AB}(a)` with `inj{B,AB}(bb)`, which no axiom
/// keeps apart: the theory stays consistent, so the finding is undecided. With `a` and `bb`
/// constructors of one sort it is genuine.
#[test]
fn values_only_injections_from_different_sorts_separate_are_not_distinct() {
    let apart = definition(
        r#"  syntax A ::= "a" [symbol(a)]
  syntax B ::= "bb" [symbol(bb)]
  syntax AB ::= A | B
  syntax AB ::= q(Int) [function, total, symbol(q)]
  rule [a]: q(_) => a
  rule [b]: q(_) => bb"#,
        false,
    );
    let (reported, genuine) = genuine_between(&apart, "a", "b");
    assert!(reported);
    assert!(genuine.is_empty(), "{genuine:?}");
    let together = definition(
        r#"  syntax AB ::= "a" [symbol(a)] | "bb" [symbol(bb)]
  syntax AB ::= q(Int) [function, total, symbol(q)]
  rule [a]: q(_) => a
  rule [b]: q(_) => bb"#,
        false,
    );
    let (reported, genuine) = genuine_between(&together, "a", "b");
    assert!(reported);
    assert_eq!(genuine.len(), 1, "{genuine:?}");
}
