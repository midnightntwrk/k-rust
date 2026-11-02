//! GAP K19: a property test of the solver translation's guarantee.
//!
//! The requirement every solver answer is held to (designs/K15.md section 1.1): for every
//! predicate φ and every K valuation ρ of its free element variables, `I_ρ ⊨ T(φ)` iff `ρ ⊨ φ`,
//! where `I_ρ` interprets each symbol by a model of the definition. So an answer that claims
//! something about every valuation, or about none, is refuted by one valuation of one model of
//! the definition where the claim is false: `Valid` by a valuation where the known predicates
//! hold and the checked one does not; `Refuted` and `Unsat` by one where all of them hold;
//! `InconsistentGroundTruth` by one where the known predicates hold. A `Sat` answer claims only
//! that a valuation exists, and is checked only where the solver gives one (`model_of`'s model
//! of an exact query), by evaluating the original predicates at it. `Contingent` and `Unknown`
//! claim nothing and are only counted; so is a `Contingent` answer every domain valuation
//! decides one way, a completeness statistic that never fails.
//!
//! K truth, the tiny definition, the generator and the runner are shared with the simplifier's
//! equivalence test and live in `solver_oracle/mod.rs`, whose docs state how K truth is computed
//! and which models of the definition are enumerated.
//!
//! By default 512 cases from a fixed seed. Run deeper with `PROPTEST_CASES=20000`, from another
//! seed with `SOLVER_TRANSLATION_SEED=<u64>`, with a longer Z3 check bound with
//! `SOLVER_TRANSLATION_TIMEOUT_MS` (default 100), with symbolic `^Int` exponents (which can make
//! a Z3 check that no bound stops, see `power_exponent`) with
//! `SOLVER_TRANSLATION_SYMBOLIC_EXPONENTS=1`, and print every case and its time with
//! `SOLVER_TRANSLATION_TRACE=1`. A failure prints the shrunk case, the answer, and the
//! counter-valuation with each predicate's truth there.

#![cfg(feature = "z3")]

mod solver_oracle;

use std::{cell::Cell, collections::BTreeSet, fmt, sync::Arc};

use k_rust_backend::{
    model::model_of,
    rule::Predicate,
    simplify::{SimplificationOptions, simplify_predicate_with_solver},
    smt::{
        Exactness, ModelResult, NoSolver, Satisfiability, SmtSolver, Validity, Z3Solver,
        translation_exactness,
    },
    substitution::Substitution,
    term::{Term, TermKind},
};
use proptest::test_runner::{TestCaseError, TestError};
use solver_oracle::*;

/// The prefix of this target's knobs (`SOLVER_TRANSLATION_SEED`, `_TIMEOUT_MS`,
/// `_SYMBOLIC_EXPONENTS`, `_TRACE`).
const KNOBS: &str = "SOLVER_TRANSLATION";

// ---------------------------------------------------------------------------------------------
// The checks.

#[derive(Default)]
struct Stats {
    valid: Cell<usize>,
    refuted: Cell<usize>,
    inconsistent: Cell<usize>,
    contingent: Cell<usize>,
    unknown: Cell<usize>,
    errors: Cell<usize>,
    unknown_sat: Cell<usize>,
    errors_sat: Cell<usize>,
    unsat: Cell<usize>,
    sat: Cell<usize>,
    exact: Cell<usize>,
    models_checked: Cell<usize>,
    /// `Contingent` where every domain valuation of the known predicates makes the checked one
    /// true (or every one makes it false): a completeness gap on the domain, never a failure.
    contingent_but_decided_on_domain: Cell<usize>,
    vacuous: Cell<usize>,
}

fn bump(counter: &Cell<usize>) {
    counter.set(counter.get() + 1);
}

impl fmt::Display for Stats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "check_predicates: {} Valid, {} Refuted, {} InconsistentGroundTruth, {} Contingent \
             ({} of them decided on the domain), {} Unknown, {} errors; is_sat: {} Unsat, {} Sat, \
             {} Unknown, {} errors; {} exact queries, {} models checked; {} cases with no domain valuation of known",
            self.valid.get(),
            self.refuted.get(),
            self.inconsistent.get(),
            self.contingent.get(),
            self.contingent_but_decided_on_domain.get(),
            self.unknown.get(),
            self.errors.get(),
            self.unsat.get(),
            self.sat.get(),
            self.unknown_sat.get(),
            self.errors_sat.get(),
            self.exact.get(),
            self.models_checked.get(),
            self.vacuous.get(),
        )
    }
}

fn failure(case: &Case, free: &Free, answer: &str, env: &Env) -> TestCaseError {
    let mut lines = vec![
        format!("case: {case}"),
        format!("answer: {answer}"),
        format!("counter-valuation: {}", env.show(free)),
    ];
    for (index, predicate) in case.known.iter().enumerate() {
        lines.push(format!(
            "  known[{index}] is {:?} there",
            eval_pred(predicate, env)
        ));
    }
    if let Some((var, term)) = &case.binding {
        lines.push(format!(
            "  binding {} |-> {term}: the term is {:?} there",
            var.name(),
            eval_int(term, env)
        ));
    }
    lines.push(format!(
        "  checked is {:?} there",
        eval_pred(&case.checked, env)
    ));
    TestCaseError::fail(lines.join("\n"))
}

/// The model's integer and Boolean values of the case's variables, the variables it binds.
fn model_env(backend: &Backend, model: &Substitution) -> (Env, BTreeSet<IntVar>, Option<bool>) {
    let mut env = Env {
        ints: [0; 4],
        bool: false,
        map: 0,
        pf_total: false,
        alt_values: false,
    };
    let mut bound = BTreeSet::new();
    for var in INT_VARS {
        if let Some(value) = model.get(&backend.ints[var.index()]).and_then(domain_value)
            && let Ok(value) = value.parse::<i128>()
        {
            env.ints[var.index()] = value;
            bound.insert(var);
        }
    }
    let bool = model
        .get(&backend.bool)
        .and_then(domain_value)
        .and_then(|value| value.parse::<bool>().ok());
    if let Some(value) = bool {
        env.bool = value;
    }
    (env, bound, bool)
}

fn domain_value(term: &Term) -> Option<String> {
    match term.kind() {
        TermKind::DomainValue { value, .. } => value.as_utf8().ok().map(str::to_owned),
        _ => None,
    }
}

fn check_case(
    backend: &Backend,
    solver: &Z3Solver,
    case: &Case,
    stats: &Stats,
) -> Result<(), TestCaseError> {
    let free = case.free();
    let base = Env {
        ints: [0; 4],
        bool: false,
        map: 0,
        pf_total: false,
        alt_values: false,
    };
    let rows = valuations(&free, &base, &BTreeSet::new())
        .into_iter()
        .map(|env| {
            let (known, checked) = truths(case, &env);
            (env, known, checked)
        })
        .collect::<Vec<_>>();
    let find = |wanted: &dyn Fn(Truth, Truth) -> bool| {
        rows.iter()
            .find(|(_, known, checked)| wanted(*known, *checked))
            .map(|(env, ..)| env)
    };
    let known = case
        .known
        .iter()
        .map(|predicate| backend.predicate(predicate))
        .collect::<Vec<_>>();
    let checked = backend.predicate(&case.checked);
    let substitution = backend.substitution(case.binding.as_ref());

    let validity = solver
        .check_predicates(&known, &substitution, std::slice::from_ref(&checked))
        .map_err(|stop| {
            TestCaseError::fail(format!("case: {case}\ncheck_predicates stopped: {stop:?}"))
        })?;
    match validity {
        Ok(Validity::Valid) => {
            bump(&stats.valid);
            if let Some(env) = find(&|k, c| k == Truth::True && c == Truth::False) {
                return Err(failure(case, &free, "check_predicates: Valid", env));
            }
        }
        Ok(Validity::Refuted) => {
            bump(&stats.refuted);
            if let Some(env) = find(&|k, c| k == Truth::True && c == Truth::True) {
                return Err(failure(case, &free, "check_predicates: Refuted", env));
            }
        }
        Ok(Validity::InconsistentGroundTruth) => {
            bump(&stats.inconsistent);
            if let Some(env) = find(&|k, _| k == Truth::True) {
                return Err(failure(
                    case,
                    &free,
                    "check_predicates: InconsistentGroundTruth",
                    env,
                ));
            }
        }
        Ok(Validity::Contingent) => {
            bump(&stats.contingent);
            let mut under_known = rows
                .iter()
                .filter(|(_, known, _)| *known == Truth::True)
                .peekable();
            if under_known.peek().is_some() {
                let checked = under_known
                    .map(|(_, _, checked)| *checked)
                    .collect::<Vec<_>>();
                if checked.iter().all(|truth| *truth == Truth::True)
                    || checked.iter().all(|truth| *truth == Truth::False)
                {
                    bump(&stats.contingent_but_decided_on_domain);
                }
            }
        }
        Ok(Validity::Unknown(_)) => bump(&stats.unknown),
        Err(_) => bump(&stats.errors),
    }
    if !rows.iter().any(|(_, known, _)| *known == Truth::True) {
        bump(&stats.vacuous);
    }

    let mut all = known;
    all.push(checked);
    let satisfiability = solver
        .is_sat(&all, &substitution)
        .map_err(|stop| TestCaseError::fail(format!("case: {case}\nis_sat stopped: {stop:?}")))?;
    match satisfiability {
        Ok(Satisfiability::Unsat) => {
            bump(&stats.unsat);
            if let Some(env) = find(&|k, c| k == Truth::True && c == Truth::True) {
                return Err(failure(case, &free, "is_sat: Unsat", env));
            }
        }
        Ok(Satisfiability::Sat) => bump(&stats.sat),
        Ok(Satisfiability::Unknown(_)) => bump(&stats.unknown_sat),
        Err(_) => bump(&stats.errors_sat),
    }

    // A model is a K valuation only of an exact translation; check it where there is one.
    if let Some((var, term)) = &case.binding {
        all.push(Predicate::Equals(
            backend.term(&IntT::Var(*var).kore()),
            backend.term(&term.kore()),
        ));
    }
    // A model of a query over `pf` or `g` may give them values none of the evaluator's models
    // gives, so it is checked only over symbols whose model is unique.
    if !free.open && translation_exactness(&all) == Exactness::Exact {
        bump(&stats.exact);
        let conjunction = Predicate::And(Arc::from(all));
        let model = model_of(&backend.definition, &conjunction, solver).map_err(|stop| {
            TestCaseError::fail(format!("case: {case}\nmodel_of stopped: {stop:?}"))
        })?;
        match model {
            Ok(ModelResult::Sat(model)) => {
                bump(&stats.models_checked);
                let (env, bound, bool) = model_env(backend, &model);
                let mut rest = free.clone();
                if bool.is_some() {
                    rest.bool = false;
                }
                // Variables the model leaves out are completed over the domain; the model is
                // refuted only if no completion satisfies the case.
                let completions = valuations(&rest, &env, &bound);
                let satisfied = completions.iter().any(|env| {
                    let (known, checked) = truths(case, env);
                    known.and(checked) != Truth::False
                });
                if !satisfied {
                    return Err(failure(
                        case,
                        &free,
                        &format!("model_of: Sat {model:?}"),
                        &completions[0],
                    ));
                }
            }
            Ok(ModelResult::Unsat) => {
                if let Some(env) = find(&|k, c| k == Truth::True && c == Truth::True) {
                    return Err(failure(case, &free, "model_of: Unsat", env));
                }
            }
            Ok(ModelResult::Unknown(_)) | Err(_) => {}
        }
    }
    Ok(())
}

/// Every answer of `check_predicates` and `is_sat` that claims something about all valuations or
/// about none, and every model of an exact query, agrees with K truth at each valuation of the
/// domain in each model of the definition (module docs).
#[test]
fn every_decided_solver_answer_agrees_with_k_truth_on_the_domain() {
    let backend = Backend::new();
    let solver = solver(&backend.definition, KNOBS);
    let stats = Stats::default();
    let (mut runner, cases, seed) = configured_runner(KNOBS);
    let started = std::time::Instant::now();
    let trace = std::env::var_os("SOLVER_TRANSLATION_TRACE").is_some();
    // Cases run until the first failure, which counts generated cases: shrinking starts there.
    let (runs, first_failure) = (Cell::new(0usize), Cell::new(None));
    let outcome = runner.run(&case(symbolic_exponents(KNOBS)), |case| {
        let before = std::time::Instant::now();
        if trace {
            eprintln!("case: {case}");
        }
        runs.set(runs.get() + 1);
        let result = check_case(&backend, &solver, &case, &stats);
        if result.is_err() && first_failure.get().is_none() {
            first_failure.set(Some(runs.get()));
        }
        if trace {
            eprintln!("  {:.3} s", before.elapsed().as_secs_f64());
        }
        result
    });
    if let Some(first) = first_failure.get() {
        eprintln!("solver_translation: the first failure was generated case {first}");
    }
    eprintln!(
        "solver_translation: {cases} cases (seed {}), {:.1} s; {stats}",
        seed.map_or_else(|| "fixed".to_owned(), |seed| seed.to_string()),
        started.elapsed().as_secs_f64()
    );
    match outcome {
        Ok(()) => {}
        Err(TestError::Fail(reason, case)) => {
            panic!("a solver answer disagrees with K truth (shrunk case: {case})\n{reason}")
        }
        Err(TestError::Abort(reason)) => panic!("the property run aborted: {reason}"),
    }
}

/// The evaluator's model of each hooked symbol agrees with k-rust's ground evaluation where the
/// backend decides a ground application (a check of the oracle, not of the solver): a value it
/// computes is the evaluator's, and an application it finds undefined is undefined in the
/// evaluator. Symbols with no K hook (`half`, `pf`, `even`, `g`) have no ground evaluation to
/// compare with; their models are argued in the definition's doc.
#[test]
fn the_oracles_model_agrees_with_ground_evaluation_of_the_hooked_symbols() {
    let backend = Backend::new();
    let env = Env {
        ints: [0; 4],
        bool: false,
        map: 0,
        pf_total: false,
        alt_values: false,
    };
    let lit = |value: i128| Box::new(IntT::Lit(value));
    let map_literals = [
        MapT::Unit,
        MapT::Item(lit(0), lit(1)),
        MapT::Item(lit(1), lit(0)),
        MapT::Concat(
            Box::new(MapT::Item(lit(0), lit(1))),
            Box::new(MapT::Item(lit(1), lit(1))),
        ),
        MapT::Concat(
            Box::new(MapT::Item(lit(0), lit(1))),
            Box::new(MapT::Item(lit(0), lit(0))),
        ),
    ];
    let mut ground = Vec::new();
    for a in DOMAIN {
        for b in DOMAIN {
            for t in [
                IntT::Add(lit(a), lit(b)),
                IntT::Div(lit(a), lit(b)),
                IntT::Pow(lit(a), lit(b)),
                IntT::Ite(Box::new(BoolT::Lt(lit(a), lit(b))), lit(a), lit(b)),
                IntT::Ite(
                    Box::new(BoolT::Lit(true)),
                    lit(a),
                    Box::new(IntT::Div(lit(b), lit(0))),
                ),
            ] {
                ground.push(AnyT::Int(t));
            }
            ground.push(AnyT::Bool(BoolT::Eq(lit(a), lit(b))));
            ground.push(AnyT::Bool(BoolT::Lt(lit(a), lit(b))));
        }
        for map in &map_literals {
            ground.push(AnyT::Int(IntT::Lookup(Box::new(map.clone()), lit(a))));
            ground.push(AnyT::Bool(BoolT::InKeys(lit(a), Box::new(map.clone()))));
        }
    }
    for map in &map_literals {
        ground.push(AnyT::Map(map.clone()));
    }
    ground.push(AnyT::Bool(BoolT::Not(Box::new(BoolT::Lit(true)))));
    ground.push(AnyT::Bool(BoolT::Not(Box::new(BoolT::Lit(false)))));

    let simplified = |predicate: &Pred| {
        simplify_predicate_with_solver(
            &backend.definition,
            &backend.predicate(predicate),
            &[],
            SimplificationOptions::unbounded(),
            &NoSolver,
        )
        .expect("no stop is armed")
        .ok()
    };
    let (mut decided, mut disagreements) = (0, Vec::new());
    for term in &ground {
        let value = eval_any(term, &env).expect("ground values are small");
        let ceil = simplified(&Pred::Ceil(term.clone()));
        let expected_ceil = if value.is_some() {
            Predicate::True
        } else {
            Predicate::False
        };
        if let Some(answer @ (Predicate::True | Predicate::False)) = ceil {
            decided += 1;
            if answer != expected_ceil {
                disagreements.push(format!(
                    "\\ceil({term}): backend {answer:?}, oracle {value:?}"
                ));
            }
        }
        if let Some(value) = value {
            let literal = match value {
                Value::Int(value) => AnyT::Int(IntT::Lit(value)),
                Value::Bool(value) => AnyT::Bool(BoolT::Lit(value)),
                Value::Map(_) => continue,
            };
            if let Some(answer @ (Predicate::True | Predicate::False)) =
                simplified(&Pred::Eq(term.clone(), literal.clone()))
            {
                decided += 1;
                if answer != Predicate::True {
                    disagreements.push(format!("{term} = {literal}: backend {answer:?}"));
                }
            }
        }
    }
    eprintln!(
        "oracle sanity: {} ground terms, {decided} backend decisions",
        ground.len()
    );
    assert!(disagreements.is_empty(), "{disagreements:#?}");
    assert!(
        decided > ground.len(),
        "the backend decided too few ground applications: {decided}"
    );
}
