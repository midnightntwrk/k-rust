//! Whole-expression native gates and adversarial guard/value controls.

#![allow(clippy::wildcard_enum_match_arm)]

use super::*;
use crate::{
    definition::BackendDefinition,
    term::{Sort, Variable},
};
#[cfg(feature = "z3")]
use crate::{smt::SmtPrelude, substitution::Substitution};
use k_rust_kore::kore::parser::parse_definition;
use std::sync::Arc;

fn definition() -> BackendDefinition {
    BackendDefinition::internalize(&parse_definition(&definition_source()).unwrap(), "MAIN")
        .unwrap()
}

fn definition_source() -> String {
    let mut source = String::from(
        r#"[] module MAIN
      hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
      hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
    "#,
    );
    for (name, hook, smt) in [
        ("add", "INT.add", Some("+")),
        ("sub", "INT.sub", Some("-")),
        ("mul", "INT.mul", Some("*")),
        ("and", "INT.and", None),
        ("or", "INT.or", None),
        ("xor", "INT.xor", None),
        ("shl", "INT.shl", None),
        ("shr", "INT.shr", None),
        ("div", "INT.ediv", Some("div")),
        ("mod", "INT.emod", Some("mod")),
        ("tdiv", "INT.tdiv", None),
        ("tmod", "INT.tmod", None),
    ] {
        source.push_str(&format!(r#"hooked-symbol {name}{{}}(SortInt{{}},SortInt{{}}):SortInt{{}} [function{{}}(), hook{{}}("{hook}"){smt}]
        "#, smt=smt.map_or(String::new(), |s|format!(r#", smt-hook{{}}("{s}")"#))));
    }
    source.push_str(r#"hooked-symbol lt{}(SortInt{},SortInt{}):SortBool{} [function{}(),total{}(),hook{}("INT.lt"),smt-hook{}("<")]
      hooked-symbol le{}(SortInt{},SortInt{}):SortBool{} [function{}(),total{}(),hook{}("INT.le"),smt-hook{}("<=")]
      hooked-symbol bor{}(SortBool{},SortBool{}):SortBool{} [function{}(),total{}(),hook{}("BOOL.or"),smt-hook{}("or")]
      hooked-symbol ite{}(SortBool{},SortInt{},SortInt{}):SortInt{} [function{}(),total{}(),hook{}("KEQUAL.ite"),smt-hook{}("ite")]
      hooked-symbol bits{}(SortInt{},SortInt{},SortInt{}):SortInt{} [function{}(),hook{}("INT.bitRange")]
      endmodule []"#);
    source
}

fn int(n: impl ToString) -> Term {
    Term::raw_domain_value(Sort::simple("SortInt"), n.to_string())
}
fn var(name: &str) -> Term {
    Term::variable(Variable::new(name, Sort::simple("SortInt")))
}
fn call(d: &BackendDefinition, name: &str, args: Vec<Term>) -> Term {
    Term::application(d.symbols().get(name).unwrap().clone(), vec![], args)
}
fn binary(d: &BackendDefinition, name: &str, a: Term, b: Term) -> Term {
    call(d, name, vec![a, b])
}
fn limits(d: &BackendDefinition, variables: &[Term], lo: i64, hi: i64) -> Vec<Predicate> {
    variables
        .iter()
        .flat_map(|v| {
            [
                Predicate::Term(binary(d, "le", int(lo), v.clone())),
                Predicate::Term(binary(d, "lt", v.clone(), int(hi))),
            ]
        })
        .collect()
}

#[test]
fn intervals_and_exact_hint_endpoints_preserve_signed_value_ranges() {
    for (lo, hi, width) in [
        (-256, 255, 9),
        (-256, -1, 9),
        (-1, 0, 1),
        (0, 255, 8),
        (0, 256, 9),
        (-510, 510, 10),
    ] {
        assert_eq!(
            Interval {
                lo: lo.into(),
                hi: hi.into()
            }
            .width(),
            Some(width)
        );
    }
    let d = definition();
    let x = var("X");
    let mut remaining = WORK_LIMIT;
    let b = bounds(
        &limits(&d, std::slice::from_ref(&x), 0, 255),
        &mut remaining,
    )
    .unwrap();
    assert_eq!(
        b[&x],
        Interval {
            lo: 0.into(),
            hi: 254.into()
        }
    );
}

#[test]
fn cancellation_is_a_typed_stop_even_before_query_planning() {
    let token = crate::stop::CancellationToken::new();
    token.cancel();
    let answer = token.scope(|| prepare(&mut TranslationState::new(), &[], &[]));
    assert_eq!(
        answer.unwrap_err().into_cause(),
        crate::stop::StopCause::Cancelled
    );
}

fn plan(term: &Term, known: &[Predicate]) -> Option<Plan> {
    let mut remaining = WORK_LIMIT;
    let bounds = bounds(known, &mut remaining).unwrap();
    let mut planner = Planner {
        bounds: &bounds,
        registry: None,
        remaining: &mut remaining,
        memo: FxHashMap::default(),
        decisions: FxHashMap::default(),
        plan: Plan {
            nodes: Vec::new(),
            used: BTreeMap::new(),
            root: 0,
            interesting: false,
        },
    };
    planner.plan.root = planner.term(term, 0).unwrap()?;
    Some(planner.plan)
}

#[test]
fn limits_and_unsupported_shapes_fall_back_without_making_domain_claims() {
    let d = definition();
    let x = var("X");
    let known = limits(&d, std::slice::from_ref(&x), 0, 256);
    assert!(plan(&binary(&d, "shl", x.clone(), int(WIDTH_LIMIT + 1)), &known).is_none());
    assert!(plan(&binary(&d, "div", x.clone(), int(0)), &known).is_none());
    assert!(plan(&binary(&d, "mod", x.clone(), int(3)), &known).is_none());
    assert!(plan(&binary(&d, "shl", x.clone(), int(-1)), &known).is_none());
    assert!(plan(&int("9".repeat(100_000)), &known).is_none());
    let mut deep = x.clone();
    for _ in 0..DEPTH_LIMIT {
        deep = binary(&d, "add", deep, int(1));
    }
    assert!(plan(&deep, &known).is_none());
    let mut state = TranslationState::new();
    state.congruence = super::super::CongruencePolicy::from_definition(&d).map(Arc::new);
    let missing = Predicate::Equals(binary(&d, "or", x, var("Unbounded")), int(0));
    prepare(&mut state, &known, &[missing]).unwrap().unwrap();
    assert!(state.word_predicates.is_empty());
}

#[cfg(feature = "z3")]
#[test]
fn signed_and_projected_values_agree_with_actual_native_hooks() {
    let d = definition();
    let x = var("X");
    let y = var("Y");
    let known = limits(&d, &[x.clone(), y.clone()], -512, 512);
    let mut checks = Vec::new();
    let mut cases = Vec::new();
    for (name, hook) in [
        ("add", "INT.add"),
        ("sub", "INT.sub"),
        ("mul", "INT.mul"),
        ("and", "INT.and"),
        ("or", "INT.or"),
        ("xor", "INT.xor"),
    ] {
        cases.push((
            binary(&d, name, x.clone(), y.clone()),
            hook,
            vec![None, None],
        ));
    }
    for mask in [0, 1, 15, 255, 256] {
        for (name, hook) in [("and", "INT.and"), ("or", "INT.or"), ("xor", "INT.xor")] {
            cases.push((
                binary(&d, name, x.clone(), int(mask)),
                hook,
                vec![None, Some(mask)],
            ));
        }
    }
    for amount in [0, 1, 8, 32, 256] {
        for (name, hook) in [("shl", "INT.shl"), ("shr", "INT.shr")] {
            if name == "shl" && amount == 256 {
                continue;
            }
            cases.push((
                binary(&d, name, x.clone(), int(amount)),
                hook,
                vec![None, Some(amount)],
            ));
        }
        for length in [0, 1, 8, 16] {
            cases.push((
                call(&d, "bits", vec![x.clone(), int(amount), int(length)]),
                "INT.bitRange",
                vec![None, Some(amount), Some(length)],
            ));
        }
    }
    for exponent in [0, 1, 8, 16] {
        for (name, hook) in [
            ("div", "INT.ediv"),
            ("mod", "INT.emod"),
            ("tdiv", "INT.tdiv"),
            ("tmod", "INT.tmod"),
        ] {
            cases.push((
                binary(&d, name, x.clone(), int(1 << exponent)),
                hook,
                vec![None, Some(1 << exponent)],
            ));
        }
    }
    for (symbolic, hook, args) in cases {
        for (left, right) in [
            (-512, -511),
            (-257, 255),
            (-256, -1),
            (-1, 0),
            (0, -1),
            (1, 511),
            (255, 256),
            (511, 511),
        ] {
            let operands = args
                .iter()
                .enumerate()
                .map(|(index, fixed)| int(fixed.unwrap_or(if index == 0 { left } else { right })))
                .collect::<Vec<_>>();
            let expected = match crate::builtin::evaluate_hook(hook, &operands)
                .unwrap()
                .unwrap()
            {
                crate::builtin::BuiltinResult::Value(value) => value,
                other => panic!("{hook}: {other:?}"),
            };
            // Exercise the planned comparison as well as the term's interval and projection.
            let mut remaining = WORK_LIMIT;
            let ranges = bounds(&known, &mut remaining).unwrap();
            let mut planner = Planner {
                bounds: &ranges,
                registry: None,
                remaining: &mut remaining,
                memo: FxHashMap::default(),
                decisions: FxHashMap::default(),
                plan: Plan {
                    nodes: Vec::new(),
                    used: BTreeMap::new(),
                    root: 0,
                    interesting: false,
                },
            };
            let a = planner.term(&symbolic, 0).unwrap().unwrap();
            let b = planner.term(&expected, 0).unwrap().unwrap();
            planner.plan.root = planner.comparison("eq", a, b).unwrap();
            let mut state = TranslationState::new();
            let expr = planner.plan.emit(&mut state, atom(false)).unwrap().unwrap();
            let bindings = state
                .mappings
                .iter()
                .map(|(t, name)| format!("({name} {})", if t == &x { left } else { right }))
                .collect::<Vec<_>>()
                .join(" ");
            checks.push(format!("(let ({bindings}) (not {expr}))"));
        }
    }
    let solver = z3::Solver::new();
    solver.from_string(format!("(assert (or {}))", checks.join(" ")));
    assert_eq!(solver.check(), z3::SatResult::Unsat);
    eprintln!("signed word/native hook calibrations: {}", checks.len());
}

#[cfg(feature = "z3")]
#[test]
fn same_width_profiles_keep_exact_guards_and_shared_dags_stay_small() {
    let d = definition();
    let x = var("X");
    let y = var("Y");
    let claim = Predicate::Equals(binary(&d, "or", x.clone(), y.clone()), int(0));
    let narrow = query(
        &d,
        &limits(&d, &[x.clone(), y.clone()], 0, 255),
        std::slice::from_ref(&claim),
    );
    let wide = query(&d, &limits(&d, &[x.clone(), y.clone()], 0, 256), &[claim]);
    assert!(narrow.checked().to_string().contains("254"));
    assert!(!wide.checked().to_string().contains("254"));
    let mut diamond = binary(&d, "or", x.clone(), y.clone());
    for _ in 0..28 {
        diamond = binary(&d, "add", diamond.clone(), diamond);
    }
    let claim = Predicate::Equals(diamond.clone(), diamond);
    let built = query(&d, &limits(&d, &[x, y], 0, 256), &[claim]);
    assert!(built.checked().to_string().len() < 15_000);
}

#[cfg(feature = "z3")]
#[test]
fn original_definedness_atoms_remain_separate_from_word_value_plans() {
    let d = definition();
    let x = var("X");
    let y = var("Y");
    let expression = binary(&d, "or", x.clone(), y.clone());
    let ceil = Predicate::Ceil(expression.clone());
    let mut known = limits(&d, &[x, y], 0, 256);
    known.push(ceil.clone());
    let mut state = TranslationState::new();
    state.congruence = super::super::CongruencePolicy::from_definition(&d).map(Arc::new);
    prepare(&mut state, &known, &[Predicate::Equals(expression, int(0))])
        .unwrap()
        .unwrap();
    assert!(!state.word_predicates.contains_key(&ceil));
    let scalar_ceil = state.translate_predicate(&ceil).unwrap();
    assert!(matches!(scalar_ceil, SExpr::Atom(_)));
    assert_eq!(state.exactness(), super::super::Exactness::Approximate);
}

#[cfg(feature = "z3")]
fn query(
    d: &BackendDefinition,
    known: &[Predicate],
    checked: &[Predicate],
) -> super::super::TranslatedQuery {
    SmtPrelude::from_definition(d)
        .unwrap()
        .query(known, &Substitution::new(), checked, false)
        .unwrap()
        .unwrap()
}

#[cfg(feature = "z3")]
#[test]
fn actual_native_eight_and_sixteen_bit_mixed_expression_gate() {
    use crate::smt::{SmtSolver, Validity, Z3Solver};
    let d = definition();
    let x = var("X");
    let y = var("Y");
    for width in [8, 16] {
        let bound = 1_i64 << width;
        let known = limits(&d, &[x.clone(), y.clone()], 0, bound);
        let or = binary(&d, "or", x.clone(), y.clone());
        let and = binary(&d, "and", x.clone(), y.clone());
        let sum = binary(&d, "add", x.clone(), y.clone());
        let zero = Predicate::Iff(
            Arc::new(Predicate::Equals(or.clone(), int(0))),
            Arc::new(Predicate::And(
                vec![
                    Predicate::Equals(x.clone(), int(0)),
                    Predicate::Equals(y.clone(), int(0)),
                ]
                .into(),
            )),
        );
        let sum_claim = Predicate::Equals(sum.clone(), binary(&d, "add", or.clone(), and.clone()));
        let xor = Predicate::Equals(
            binary(&d, "xor", x.clone(), y.clone()),
            binary(&d, "sub", sum, binary(&d, "mul", int(2), and)),
        );
        let high = binary(&d, "div", x.clone(), int(bound / 2));
        let rotate = Predicate::Equals(
            binary(
                &d,
                "or",
                binary(&d, "mod", binary(&d, "shl", x.clone(), int(1)), int(bound)),
                high.clone(),
            ),
            binary(
                &d,
                "add",
                binary(
                    &d,
                    "mul",
                    int(2),
                    binary(&d, "mod", x.clone(), int(bound / 2)),
                ),
                high,
            ),
        );
        let mut digits = int(0);
        for bit in 0..width {
            let digit =
                |v: Term| binary(&d, "mod", binary(&d, "div", v, int(1_i64 << bit)), int(2));
            let test = call(
                &d,
                "bor",
                vec![
                    binary(&d, "lt", int(0), digit(x.clone())),
                    binary(&d, "lt", int(0), digit(y.clone())),
                ],
            );
            digits = binary(
                &d,
                "add",
                digits,
                call(&d, "ite", vec![test, int(1_i64 << bit), int(0)]),
            );
        }
        for (name, claim) in [
            ("zero", zero),
            ("sum", sum_claim),
            ("xor", xor),
            ("rotate", rotate),
            ("digit-spec", Predicate::Equals(or, digits)),
        ] {
            let started = std::time::Instant::now();
            let built = query(&d, &known, std::slice::from_ref(&claim));
            let construction = started.elapsed();
            assert!(built.checked().to_string().contains("KRUST-WORD"));
            let solver = Z3Solver::new(&d).unwrap();
            let started = std::time::Instant::now();
            let counters = k_rust_kore::measure::snapshot();
            let result = solver.check_predicates(&known, &Substitution::new(), &[claim]);
            let costs = k_rust_kore::measure::snapshot().delta(&counters);
            eprintln!(
                "word-costs {name}-{width}: runs={} rlimit={}",
                costs.get(k_rust_kore::measure::Counter::SmtSolverRuns),
                costs.get(k_rust_kore::measure::Counter::SmtRlimitCount)
            );
            eprintln!(
                "word-native {name}-{width}: {result:?}; construction={construction:?}; native={:?}; bytes={}",
                started.elapsed(),
                built.base().len() + built.checked().to_string().len()
            );
            assert_eq!(result, Ok(Ok(Validity::Valid)), "{name}-{width}");
        }
    }
}

#[cfg(feature = "z3")]
#[test]
fn overflow_negative_and_outside_guard_controls_do_not_become_theorems() {
    use crate::smt::{SmtSolver, Validity, Z3Solver};
    let d = definition();
    let x = var("X");
    let y = var("Y");
    for width in [8, 16] {
        let bound = 1_i64 << width;
        let known = limits(&d, &[x.clone(), y.clone()], 0, bound);
        let sum = binary(&d, "add", x.clone(), y.clone());
        let or = binary(&d, "or", x.clone(), y.clone());
        let claims = [
            Predicate::Equals(
                binary(
                    &d,
                    "add",
                    or.clone(),
                    binary(&d, "and", x.clone(), y.clone()),
                ),
                binary(&d, "mod", sum, int(bound)),
            ),
            Predicate::Equals(or.clone(), binary(&d, "sub", or, int(bound))),
        ];
        for claim in claims {
            assert!(
                query(&d, &known, std::slice::from_ref(&claim))
                    .checked()
                    .to_string()
                    .contains("KRUST-WORD")
            );
            assert_ne!(
                Z3Solver::new(&d)
                    .unwrap()
                    .check_predicates(&known, &Substitution::new(), &[claim]),
                Ok(Ok(Validity::Valid))
            );
        }
        // A plan selected with x<bound must keep its fallback when evaluated outside that guard.
        let claim = Predicate::Equals(binary(&d, "or", x.clone(), y.clone()), int(1));
        let built = query(&d, &known, &[claim]);
        let mut state = TranslationState::new();
        state.congruence = super::super::CongruencePolicy::from_definition(&d).map(Arc::new);
        let checked = Predicate::Equals(binary(&d, "or", x.clone(), y.clone()), int(1));
        prepare(&mut state, &known, std::slice::from_ref(&checked))
            .unwrap()
            .unwrap();
        let expr = state.translate_predicate(&checked).unwrap();
        let declarations = state.mapping_declarations().unwrap().join("\n");
        let x_name = state.mappings.get(&x).unwrap();
        let y_name = state.mappings.get(&y).unwrap();
        let script = format!(
            "{declarations}\n(assert (= {x_name} {bound}))\n(assert (= {y_name} 1))\n(assert (not {expr}))"
        );
        let solver = z3::Solver::new();
        solver.from_string(script);
        assert_eq!(solver.check(), z3::SatResult::Sat);
        assert_eq!(built.exactness(), super::super::Exactness::Approximate);
        assert!(built.model_mappings().is_none());
    }
}

#[cfg(feature = "z3")]
#[test]
fn a_quantified_copy_cannot_reuse_a_free_occurrences_word_plan() {
    let d = definition();
    let x = var("X");
    let y = var("Y");
    let atom = Predicate::Equals(binary(&d, "or", x.clone(), y.clone()), int(0));
    let binder = match x.kind() {
        TermKind::Variable(v) => v.clone(),
        _ => unreachable!(),
    };
    let checked = [atom.clone(), Predicate::Forall(binder, Arc::new(atom))];
    let built = query(&d, &limits(&d, &[x, y], 0, 256), &checked);
    let text = built.checked().to_string();
    let quantified = text.split("(forall").nth(1).unwrap();
    assert!(!quantified.contains("KRUST-WORD"), "{text}");
}

#[test]
fn application_effects_and_text_limits_are_checked_independently() {
    let source =
        definition_source().replace("hook{}(\"INT.or\")", "hook{}(\"INT.or\"), impure{}()");
    let d = BackendDefinition::internalize(&parse_definition(&source).unwrap(), "MAIN").unwrap();
    let x = var("X");
    let y = var("Y");
    let checked = Predicate::Equals(binary(&d, "or", x.clone(), y.clone()), int(0));
    let mut state = TranslationState::new();
    state.congruence = super::super::CongruencePolicy::from_definition(&d).map(Arc::new);
    prepare(&mut state, &limits(&d, &[x, y], 0, 256), &[checked])
        .unwrap()
        .unwrap();
    assert!(state.word_predicates.is_empty());
    let expression = app("and", vec![atom(true), atom(false)]);
    let length = expression.to_string().len();
    let mut exact = length;
    assert!(fits_text(&expression, &mut exact).unwrap());
    assert_eq!(exact, 0);
    let mut short = length - 1;
    assert!(!fits_text(&expression, &mut short).unwrap());
    let d = definition();
    let x = var("X");
    let y = var("Y");
    let repeated = Predicate::Equals(binary(&d, "or", x.clone(), y.clone()), int(0));
    let mut state = TranslationState::new();
    state.congruence = super::super::CongruencePolicy::from_definition(&d).map(Arc::new);
    prepare(
        &mut state,
        &limits(&d, &[x, y], 0, 256),
        &vec![repeated; 4096],
    )
    .unwrap()
    .unwrap();
    assert!(
        state.word_predicates.is_empty(),
        "repeated occurrences must consume the text budget"
    );
}
