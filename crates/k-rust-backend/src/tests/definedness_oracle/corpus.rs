//! V10 and V11 on checked-in fixtures extracted from the corpus.
//!
//! - **V10.** The FUN-shaped list family (`tests/fixtures/overloaded-list-owise.kore`: FUN's
//!   `Bottoms < Vals < Exps` overloads and its `getMatching` equations): the check reports no
//!   non-joined pair, and a `Vals` value gets an instance-normal token, a certificate and a
//!   `\ceil` discharge.
//! - **V11.** Precondition P6 on the prelude: every executable equation rooted at a hooked symbol
//!   in FUN's prelude (`tests/fixtures/fun-prelude-hooked-equations.kore`, the hooked symbols'
//!   equations of FUN's `definition.kore` with the symbols they mention, source locations
//!   stripped), instantiated over sampled domain values (both Booleans, the integers -3 to 3,
//!   two strings, three `K` sequences) where its `requires` holds, evaluates to the hook's result on the same
//!   arguments wherever the hook is defined.

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::{
    builtin::{BuiltinResult, evaluate_in_definition},
    definition::BackendDefinition,
    rule::{Predicate, RuleRhs},
    simplify::{SimplificationOptions, simplify, simplify_predicate_with_solver},
    smt::NoSolver,
    substitution::{Substitution, substitute},
    term::{Sort, Term, TermKind, head::certified_ground_normal_form},
};

const FUN_LISTS: &str = include_str!("../../../tests/fixtures/overloaded-list-owise.kore");
const FUN_PRELUDE: &str = include_str!("../../../tests/fixtures/fun-prelude-hooked-equations.kore");

fn load(source: &str, module: &str) -> BackendDefinition {
    let syntax = parse_definition(source).expect("the fixture parses");
    BackendDefinition::internalize(&syntax, module).expect("the fixture internalizes")
}

fn term(definition: &BackendDefinition, source: &str) -> Term {
    definition
        .internalize_term(&parse_pattern(source).expect("the term parses"), &[])
        .expect("the term internalizes")
}

#[test]
fn the_fun_list_family_is_accepted_and_its_values_keep_their_claims() {
    let definition = load(FUN_LISTS, "OVERLOADED-LIST-OWISE");
    let claims = definition.value_claims();
    assert!(claims.unjoined().is_empty(), "{:?}", claims.unjoined());
    assert!(claims.violations().is_empty(), "{:?}", claims.violations());
    assert!(claims.tainted_symbols().is_empty());
    let value = "vals{}(one{}(), inj{SortBottoms{}, SortVals{}}(dotBottoms{}()))";
    let subject = term(&definition, value);
    assert!(
        definition.instance_normal(&subject).is_some(),
        "{value} gets no token"
    );
    let simplified = simplify(&definition, &subject, SimplificationOptions::default())
        .expect("no stop is armed")
        .expect("the value simplifies");
    assert_eq!(simplified.term, subject);
    assert!(
        certified_ground_normal_form(&simplified.term),
        "{value} gets no certificate"
    );
    let ceil = format!(r"\ceil{{SortVals{{}}, SortVals{{}}}}({value})");
    let syntax = parse_pattern(&ceil).expect("the query parses");
    let (predicate, _) = definition
        .admit_unverified(&syntax, &[])
        .internalize_predicate()
        .expect("the query internalizes");
    let discharged = simplify_predicate_with_solver(
        &definition,
        &predicate,
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    )
    .expect("no stop is armed")
    .expect("the query simplifies");
    assert_eq!(discharged, Predicate::True, "{ceil}");
}

/// The sampled domain values of a builtin sort, as KORE.
fn samples(sort: &Sort) -> Option<Vec<String>> {
    let Sort::Application { name, arguments } = sort else {
        return None;
    };
    if !arguments.is_empty() {
        return None;
    }
    Some(match name.as_ref() {
        "SortBool" => ["true", "false"]
            .iter()
            .map(|value| format!(r#"\dv{{SortBool{{}}}}("{value}")"#))
            .collect(),
        "SortInt" => (-3..=3)
            .map(|value: i64| format!(r#"\dv{{SortInt{{}}}}("{value}")"#))
            .collect(),
        "SortString" => ["", "ab"]
            .iter()
            .map(|value| format!(r#"\dv{{SortString{{}}}}("{value}")"#))
            .collect(),
        "SortK" => ["1", "2"]
            .iter()
            .map(|value| {
                format!(
                    r#"kseq{{}}(inj{{SortInt{{}}, SortKItem{{}}}}(\dv{{SortInt{{}}}}("{value}")), dotk{{}}())"#
                )
            })
            .chain(std::iter::once("dotk{}()".to_owned()))
            .collect(),
        _ => return None,
    })
}

/// `term` with each `\and` of two equal conjuncts replaced by the conjunct; `None` when two
/// conjuncts differ.
fn collapse(term: &Term) -> Option<Term> {
    match term.kind() {
        TermKind::And(left, right) => {
            let (left, right) = (collapse(left)?, collapse(right)?);
            (left == right).then_some(left)
        }
        TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } => Some(Term::application(
            symbol.clone(),
            sort_arguments.clone(),
            arguments.iter().map(collapse).collect::<Option<Vec<_>>>()?,
        )),
        TermKind::Injection {
            source,
            target,
            term,
        } => Some(Term::injection(
            source.clone(),
            target.clone(),
            collapse(term)?,
        )),
        _ => Some(term.clone()),
    }
}

#[test]
fn the_preludes_hooked_equations_agree_with_their_hooks() {
    let definition = load(FUN_PRELUDE, "FUN-UNTYPED");
    let (mut equations, mut instances, mut skipped) = (0, 0, Vec::new());
    let mut failures = Vec::new();
    for groups in definition.function_theory().values() {
        for rule in groups.values().flatten() {
            let TermKind::Application { symbol, .. } = rule.lhs.kind() else {
                continue;
            };
            if symbol.attributes.hook.is_none() || rule.attributes.simplification {
                continue;
            }
            equations += 1;
            let RuleRhs::Term(rhs) = &rule.rhs else {
                skipped.push(format!("{}: right-hand side", symbol.name));
                continue;
            };
            let variables = rule
                .lhs
                .attributes()
                .variables
                .iter()
                .cloned()
                .collect::<Vec<_>>();
            let Some(choices) = variables
                .iter()
                .map(|variable| samples(&variable.sort))
                .collect::<Option<Vec<_>>>()
            else {
                skipped.push(format!(
                    "{}: a variable of a sort without samples",
                    symbol.name
                ));
                continue;
            };
            let mut valuations = vec![Substitution::new()];
            for (variable, values) in variables.iter().zip(&choices) {
                let mut next = Vec::new();
                for valuation in &valuations {
                    for value in values {
                        let mut extended = valuation.clone();
                        extended.insert(variable.clone(), term(&definition, value));
                        next.push(extended);
                    }
                }
                valuations = next;
            }
            for valuation in valuations {
                // An alias `\and(p, X)` binds `X` to `p`'s instance: other valuations are no
                // instances of the left-hand side.
                let Some(instance) = collapse(&substitute(&rule.lhs, &valuation)) else {
                    continue;
                };
                let hooked = match evaluate_in_definition(&instance, &definition) {
                    Ok(Ok(BuiltinResult::Value(value))) => value,
                    Ok(_) => continue,
                    Err(stop) => {
                        stop.into_cause();
                        continue;
                    }
                };
                let requires = rule
                    .requires
                    .instantiate(&valuation)
                    .with_definedness(&definition, &[]);
                if !requires.is_empty() {
                    let holds = simplify_predicate_with_solver(
                        &definition,
                        &Predicate::And(requires),
                        &[],
                        SimplificationOptions::default(),
                        &NoSolver,
                    );
                    match holds {
                        Ok(Ok(Predicate::True)) => {}
                        Ok(_) => continue,
                        Err(stop) => {
                            stop.into_cause();
                            continue;
                        }
                    }
                }
                instances += 1;
                let reduct = substitute(rhs, &valuation);
                let evaluated =
                    match simplify(&definition, &reduct, SimplificationOptions::default()) {
                        Ok(Ok(result)) if result.constraints().is_empty() => result.term,
                        Ok(_) => {
                            failures.push(format!(
                                "{instance:?}: the right-hand side does not evaluate"
                            ));
                            continue;
                        }
                        Err(stop) => {
                            stop.into_cause();
                            continue;
                        }
                    };
                if evaluated != hooked {
                    failures.push(format!(
                        "{}: the hook gives {hooked:?}, the equation {evaluated:?}",
                        crate::externalize::term(&instance)
                    ));
                }
            }
        }
    }
    eprintln!(
        "prelude hooked equations: {equations} equations, {instances} instances checked, skipped: {skipped:?}"
    );
    assert!(instances > 0, "no instance checked");
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// Relevance, the filter of the load's scope (`CheckScope::Gate`), is what it is defined as: an
/// equation is relevant exactly when the taint closure seeded by it alone holds a symbol some
/// gate site can be asked about, on every executable equation of the oracle's templates and of
/// the FUN list fixture, with the closure's rules intact and with each closure switch, so that
/// the backward pass follows every rule the closure follows.
#[test]
fn relevance_is_the_closure_of_each_equation_alone_meeting_the_gate() {
    use crate::confluence::switches::{self, Switches};
    let mut definitions = vec![(
        "fun lists".to_owned(),
        load(FUN_LISTS, "OVERLOADED-LIST-OWISE"),
    )];
    for (name, definition, _) in super::generator::templates() {
        let syntax = parse_definition(&definition.kore()).expect("the template parses");
        definitions.push((
            name,
            BackendDefinition::internalize(&syntax, "MAIN").expect("the template internalizes"),
        ));
    }
    let settings = [
        ("intact", Switches::default()),
        (
            "drop_t1",
            Switches {
                drop_t1: true,
                ..Switches::default()
            },
        ),
        (
            "drop_tsym_rhs",
            Switches {
                drop_tsym_rhs: true,
                ..Switches::default()
            },
        ),
        (
            "drop_tobs",
            Switches {
                drop_tobs: true,
                ..Switches::default()
            },
        ),
        (
            "seed_heads_only",
            Switches {
                seed_heads_only: true,
                ..Switches::default()
            },
        ),
    ];
    let mut failures = Vec::new();
    let (mut equations, mut relevant) = (0, 0);
    for (setting, active) in settings {
        for (name, definition) in &definitions {
            let (count, found, disagreements) = switches::with(active, || {
                crate::confluence::relevance_disagreements(definition)
            });
            if setting == "intact" {
                equations += count;
                relevant += found;
            }
            failures.extend(
                disagreements
                    .into_iter()
                    .map(|disagreement| format!("{name} ({setting}): {disagreement}")),
            );
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    // Both answers occur, so the comparison is not vacuous.
    assert!(
        relevant > 0 && relevant < equations,
        "{relevant} of {equations} equations relevant"
    );
}

/// The memo of condition simplifications (`ConditionMemo`) changes no verdict and no count but
/// its own hits, in both scopes, on the FUN list fixture and every template of the oracle; the
/// whole-definition form of this test is the corpus gate's (`tests/value_contract_corpus.rs`).
#[test]
fn the_condition_memo_changes_no_verdict_and_no_count() {
    use crate::confluence::{CheckScope, ConditionMemo};
    let mut definitions = vec![(
        "fun lists".to_owned(),
        load(FUN_LISTS, "OVERLOADED-LIST-OWISE"),
    )];
    for (name, definition, _) in super::generator::templates() {
        let syntax = parse_definition(&definition.kore()).expect("the template parses");
        definitions.push((
            name,
            BackendDefinition::internalize(&syntax, "MAIN").expect("the template internalizes"),
        ));
    }
    let mut failures = Vec::new();
    let (mut calls, mut hits) = (0, 0);
    for (name, definition) in &definitions {
        for scope in [CheckScope::Gate, CheckScope::All] {
            let on = definition.value_claims_checked(scope, ConditionMemo::On);
            let off = definition.value_claims_checked(scope, ConditionMemo::Off);
            failures.extend(
                on.verdict_differences(&off)
                    .into_iter()
                    .map(|difference| format!("{name} ({scope:?}): {difference}")),
            );
            failures.extend(
                super::checks::memo_count_difference(&on, &off)
                    .map(|difference| format!("{name} ({scope:?}): {difference}")),
            );
            calls += on.counts().simplifier_calls;
            hits += on.counts().condition_memo_hits;
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    // The memo answers some conditions here, so the comparison is not vacuous.
    assert!(
        hits > 0,
        "{hits} of {calls} conditions answered from the memo"
    );
}

/// The measure ratchet of the design's section 7: the check's four work counters on the FUN
/// list-family fixture and the oracle's feature templates, each pinned within 10 % (FUN's prelude
/// fixture declares no equation head, so the check stops at its precondition rows there). A change
/// beyond that is a cost change to explain and re-pin (print the measured values with
/// `KRUST_MEASURE_RATCHET_PRINT=1`). WASM's full definition is pinned exactly by the corpus gate
/// (`scripts/value-contract-corpus.toml`), which CI cannot run.
#[test]
fn the_checks_work_counters_stay_within_ten_percent_of_their_pins() {
    // (fixture, pairs, unifier branches, join steps, simplifier calls)
    const PINS: [(&str, usize, usize, usize, usize); 2] = [
        ("fun lists", 18, 236, 38, 0),
        ("oracle templates", 57, 124, 24, 6),
    ];
    let mut measured = Vec::new();
    let counts = load(FUN_LISTS, "OVERLOADED-LIST-OWISE")
        .value_claims()
        .counts();
    measured.push((
        "fun lists",
        counts.pairs,
        counts.unifier_branches,
        counts.join_steps,
        counts.simplifier_calls,
    ));
    let mut templates = (0, 0, 0, 0);
    for (_, definition, _) in super::generator::templates() {
        let syntax = parse_definition(&definition.kore()).expect("the template parses");
        let counts = BackendDefinition::internalize(&syntax, "MAIN")
            .expect("the template internalizes")
            .value_claims()
            .counts();
        templates.0 += counts.pairs;
        templates.1 += counts.unifier_branches;
        templates.2 += counts.join_steps;
        templates.3 += counts.simplifier_calls;
    }
    measured.push((
        "oracle templates",
        templates.0,
        templates.1,
        templates.2,
        templates.3,
    ));
    if std::env::var_os("KRUST_MEASURE_RATCHET_PRINT").is_some() {
        eprintln!("{measured:?}");
    }
    let within =
        |pinned: usize, value: usize| value * 10 <= pinned * 11 && value * 10 >= pinned * 9;
    for (pin, value) in PINS.iter().zip(&measured) {
        assert_eq!(pin.0, value.0);
        assert!(
            within(pin.1, value.1)
                && within(pin.2, value.2)
                && within(pin.3, value.3)
                && within(pin.4, value.4),
            "{}: measured (pairs, unifier branches, join steps, simplifier calls) = {:?}, pinned {:?}",
            pin.0,
            (value.1, value.2, value.3, value.4),
            (pin.1, pin.2, pin.3, pin.4)
        );
    }
}
