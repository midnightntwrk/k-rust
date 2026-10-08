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
