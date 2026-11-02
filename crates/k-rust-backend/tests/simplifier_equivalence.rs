//! GAP K33: the simplifier's output is equivalent to its input.
//!
//! The requirement (designs/FOLLOWUPS.md, K33): for predicates `P` and facts `F`,
//! `simplify_predicates_with_solver(P, F)` returns `P'` with `P' ∧ F ≡ P ∧ F` in K's semantics,
//! at every valuation in every model of the definition, under `NoSolver` and under Z3, with any
//! budget (a budget stop may return less simplified output, never a non-equivalent one). So one
//! valuation of one model where `P' ∧ F` and `P ∧ F` take different definite truth values
//! refutes the output. Equivalence is pointwise: the simplifier rewrites by the definition's
//! axioms and K's own laws, which hold in each of its models.
//!
//! The output is read back into the oracle's syntax (`solver_oracle`) over its closed symbol set
//! and evaluated there, so no k-rust function computes the truth the output is compared with; the
//! simplifier is not compared through the solver, which it consults, since a shared misreading
//! would then pass. An output that leaves the closed set (a symbol outside it, a variable the
//! oracle does not know, a construct it lacks) is counted as skipped, by reason, and the skip
//! rate is printed. The oracle's three-valued `\exists` keeps "unknown" out of the comparison.
//!
//! Each case runs the simplifier three times: under `NoSolver` with the default options, under
//! the Z3 solver `solver_translation` uses (100 ms, 256 MB, no retry) with the default options,
//! and under that solver with a small iteration budget kept partial (the case's `budget`).
//!
//! By default 512 cases from a fixed seed. Run deeper with `PROPTEST_CASES=20000`, from another
//! seed with `SIMPLIFIER_EQUIVALENCE_SEED=<u64>`, with a longer Z3 check bound with
//! `SIMPLIFIER_EQUIVALENCE_TIMEOUT_MS` (default 100), with symbolic `^Int` exponents (which can
//! make a Z3 check that no bound stops, `solver_oracle::power_exponent`) with
//! `SIMPLIFIER_EQUIVALENCE_SYMBOLIC_EXPONENTS=1`, and print every case, each output and its time
//! with `SIMPLIFIER_EQUIVALENCE_TRACE=1`. A failure prints the shrunk `P`, `F` and `P'`, the
//! valuation, and each conjunct's truth there. A run of at least 1,000 compared outputs also fails
//! when more than 40% of them are vacuous (no valuation where `F` holds and both sides are
//! definite).

#![cfg(feature = "z3")]

mod solver_oracle;

use std::{
    cell::{Cell, RefCell},
    collections::{BTreeMap, BTreeSet},
    fmt,
};

use k_rust_backend::{
    rule::Predicate,
    simplify::{SimplificationOptions, simplify_predicates_with_solver},
    smt::{NoSolver, SmtSolver},
    term::{Sort, Term, TermKind, Variable},
};
use proptest::{
    prelude::*,
    test_runner::{TestCaseError, TestError},
};
use solver_oracle::*;

/// The prefix of this target's knobs (`SIMPLIFIER_EQUIVALENCE_SEED`, `_TIMEOUT_MS`,
/// `_SYMBOLIC_EXPONENTS`, `_TRACE`).
const KNOBS: &str = "SIMPLIFIER_EQUIVALENCE";

/// One generated input: the predicates to simplify, the facts they are simplified under, and the
/// iteration budget of the third run.
#[derive(Clone, Debug)]
struct Input {
    predicates: Vec<Pred>,
    facts: Vec<Pred>,
    budget: usize,
}

fn conjunction(predicates: &[Pred]) -> String {
    if predicates.is_empty() {
        return r"\top".to_owned();
    }
    predicates
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join("; ")
}

impl fmt::Display for Input {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "P: [{}]; F: [{}]; budget {}",
            conjunction(&self.predicates),
            conjunction(&self.facts),
            self.budget
        )
    }
}

/// `P` is one to three predicates and `F` zero to two, drawn as `solver_translation` draws its
/// checked and known predicates, and, a quarter of the time, a binding `V = t` among the facts
/// (with `t` not mentioning `V`), which the simplifier can use as a substitution. A quarter of
/// `P`'s predicates are instead a reflexive atom over a partial term (`reflexive`).
fn input(symbolic_exponents: bool) -> impl Strategy<Value = Input> {
    let terms = terms(3, symbolic_exponents);
    let predicate = predicate(&terms);
    let checked = prop_oneof![
        3 => predicate.clone(),
        1 => reflexive(symbolic_exponents),
    ];
    let binding = (
        prop_oneof![Just(IntVar::X), Just(IntVar::Y), Just(IntVar::Z)],
        terms_at(2, symbolic_exponents),
    );
    (
        prop::collection::vec(checked, 1..=3),
        prop::collection::vec(predicate, 0..=2),
        prop::option::weighted(0.25, binding),
        1usize..=8,
    )
        .prop_map(|(predicates, mut facts, binding, budget)| {
            if let Some((var, term)) = binding.filter(|(var, term)| !term.mentions(*var)) {
                facts.push(Pred::Eq(AnyT::Int(IntT::Var(var)), AnyT::Int(term)));
            }
            Input {
                predicates,
                facts,
                budget,
            }
        })
}

/// A term with a partial head, so its domain is a proper part of the valuations: `half`,
/// `divInt` (by a term or by a literal, zero included), `pf`, a map lookup, or `^Int` with a
/// negative exponent, over an operand of depth at most 2.
fn partial_term(symbolic_exponents: bool) -> BoxedStrategy<IntT> {
    let operand = || terms_at(2, symbolic_exponents).prop_map(Box::new);
    let literal = || (-2i8..=2).prop_map(|value| Box::new(int_lit(value)));
    prop_oneof![
        2 => operand().prop_map(IntT::Half),
        2 => (operand(), operand()).prop_map(|(a, b)| IntT::Div(a, b)),
        1 => (operand(), literal()).prop_map(|(a, b)| IntT::Div(a, b)),
        2 => operand().prop_map(IntT::Pf),
        2 => (map_leaf().prop_map(Box::new), operand()).prop_map(|(m, k)| IntT::Lookup(m, k)),
        1 => (power_base(), (-2i8..=-1).prop_map(|value| Box::new(int_lit(value))))
            .prop_map(|(a, b)| IntT::Pow(a, b)),
    ]
    .boxed()
}

/// A comparison of a partial term `t` with itself. The K comparisons (`t ==Int t`, its negation,
/// `t <Int t`, `t <=Int t`, `t =/=Int t`, `t >=Int t`) are applications, strict in `t`: as
/// predicates they hold, for the true ones, exactly where `t` is defined. The ML equalities (`t =
/// t`, `t +Int 0 = t`) hold everywhere, `t`'s undefinedness included. So a reflexive rewrite that
/// drops `t`'s definedness, or adds it to an ML equality, is refuted at a valuation where `t` is
/// undefined.
fn reflexive(symbolic_exponents: bool) -> BoxedStrategy<Pred> {
    partial_term(symbolic_exponents)
        .prop_flat_map(|t| {
            let b = || Box::new(t.clone());
            prop_oneof![
                Just(Pred::Holds(BoolT::Eq(b(), b()))),
                Just(Pred::Holds(BoolT::Not(Box::new(BoolT::Eq(b(), b()))))),
                Just(Pred::Holds(BoolT::Lt(b(), b()))),
                Just(Pred::Holds(BoolT::Le(b(), b()))),
                Just(Pred::Holds(BoolT::Ne(b(), b()))),
                Just(Pred::Holds(BoolT::Ge(b(), b()))),
                Just(Pred::Eq(AnyT::Int(t.clone()), AnyT::Int(t.clone()))),
                Just(Pred::Eq(
                    AnyT::Int(IntT::Add(b(), Box::new(IntT::Lit(0)))),
                    AnyT::Int(t.clone()),
                )),
            ]
        })
        .boxed()
}

// ---------------------------------------------------------------------------------------------
// The read-back of the simplifier's output into the oracle's syntax.

/// Why an output was not read back: it is counted under this reason and not compared.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Skip(String);

type Read<T> = Result<T, Skip>;

fn skip<T>(reason: impl Into<String>) -> Read<T> {
    Err(Skip(reason.into()))
}

struct ReadBack<'a> {
    backend: &'a Backend,
    map_var: Variable,
    int: Sort,
    bool: Sort,
    map: Sort,
}

impl<'a> ReadBack<'a> {
    fn new(backend: &'a Backend) -> Self {
        let map_var = variable_of(&backend.term("M:SortMap{}"));
        Self {
            int: backend.term("X:SortInt{}").sort(),
            bool: backend.term("B:SortBool{}").sort(),
            map: map_var.sort,
            map_var,
            backend,
        }
    }

    fn int_var(&self, variable: &Variable) -> Option<IntVar> {
        INT_VARS
            .into_iter()
            .find(|var| self.backend.ints[var.index()] == *variable)
    }

    fn predicates(&self, predicates: &[Predicate]) -> Read<Vec<Pred>> {
        predicates.iter().map(|p| self.predicate(p)).collect()
    }

    fn predicate(&self, predicate: &Predicate) -> Read<Pred> {
        Ok(match predicate {
            Predicate::True => Pred::Top,
            Predicate::False => Pred::Bottom,
            Predicate::Term(term) => Pred::Holds(self.bool_term(term)?),
            Predicate::Equals(a, b) => Pred::Eq(self.any(a)?, self.any(b)?),
            // `Defined(t)` means exactly what `\ceil(t)` means.
            Predicate::Ceil(term) | Predicate::Defined(term) => Pred::Ceil(self.any(term)?),
            // Both sides denote at most one element: `a ∈ b` holds iff they are the same one.
            Predicate::In(a, b) => {
                let a = self.any(a)?;
                Pred::And(
                    Box::new(Pred::Ceil(a.clone())),
                    Box::new(Pred::Eq(a, self.any(b)?)),
                )
            }
            Predicate::Floor(_) => return skip(r"\floor"),
            Predicate::Not(p) => Pred::Not(Box::new(self.predicate(p)?)),
            Predicate::And(ps) => {
                self.fold(ps, Pred::Top, |p, q| Pred::And(Box::new(p), Box::new(q)))?
            }
            Predicate::Or(ps) => {
                self.fold(ps, Pred::Bottom, |p, q| Pred::Or(Box::new(p), Box::new(q)))?
            }
            Predicate::Implies(p, q) => {
                Pred::Implies(Box::new(self.predicate(p)?), Box::new(self.predicate(q)?))
            }
            Predicate::Iff(p, q) => {
                let (p, q) = (self.predicate(p)?, self.predicate(q)?);
                Pred::And(
                    Box::new(Pred::Implies(Box::new(p.clone()), Box::new(q.clone()))),
                    Box::new(Pred::Implies(Box::new(q), Box::new(p))),
                )
            }
            Predicate::Exists(variable, body) => {
                Pred::Exists(self.binder(variable)?, Box::new(self.predicate(body)?))
            }
            // `\forall v. p` is `\not \exists v. \not p`; the oracle's `\exists` over Int is
            // unknown without a witness outside the one-point form, so this is then false only
            // where a counterexample is found.
            Predicate::Forall(variable, body) => Pred::Not(Box::new(Pred::Exists(
                self.binder(variable)?,
                Box::new(Pred::Not(Box::new(self.predicate(body)?))),
            ))),
            // `key` and `rest` defined and `key` not a key of `rest`: exactly
            // `notBool(key in_keys(rest)) = true`, since `in_keys` is total on defined operands.
            Predicate::Absent(absence) => {
                if absence.rest().sort() != self.map {
                    return skip("absence from a set");
                }
                Pred::Holds(BoolT::Not(Box::new(BoolT::InKeys(
                    Box::new(self.int(absence.key())?),
                    Box::new(self.map_term(absence.rest())?),
                ))))
            }
        })
    }

    fn fold(
        &self,
        predicates: &[Predicate],
        unit: Pred,
        join: impl Fn(Pred, Pred) -> Pred,
    ) -> Read<Pred> {
        let mut read = self.predicates(predicates)?.into_iter();
        Ok(match read.next() {
            None => unit,
            Some(first) => read.fold(first, join),
        })
    }

    fn binder(&self, variable: &Variable) -> Read<Binder> {
        if *variable == self.backend.bool {
            Ok(Binder::Bool)
        } else if let Some(var) = self.int_var(variable) {
            Ok(Binder::Int(var))
        } else {
            skip("a binder outside X, Y, Z, N, B")
        }
    }

    fn any(&self, term: &Term) -> Read<AnyT> {
        let sort = term.sort();
        if sort == self.int {
            Ok(AnyT::Int(self.int(term)?))
        } else if sort == self.bool {
            Ok(AnyT::Bool(self.bool_term(term)?))
        } else if sort == self.map {
            Ok(AnyT::Map(self.map_term(term)?))
        } else {
            skip("a term of another sort")
        }
    }

    /// The application's symbol name and arguments, or the reason it is not one.
    fn application<'t>(&self, term: &'t Term) -> Read<(&'t str, &'t [Term])> {
        match term.kind() {
            TermKind::Application {
                symbol, arguments, ..
            } => Ok((symbol.name.as_ref(), arguments.as_slice())),
            TermKind::And(..) => skip(r"a term-level \and"),
            TermKind::Injection { .. } => skip("an injection"),
            TermKind::List { .. } | TermKind::Set { .. } => skip("a list or set"),
            TermKind::Variable(_) => skip("a variable outside X, Y, Z, N, B, M"),
            TermKind::DomainValue { .. } => skip("a domain value of another sort"),
            TermKind::Map { .. } => skip("a map where a scalar was expected"),
        }
    }

    fn int(&self, term: &Term) -> Read<IntT> {
        match term.kind() {
            TermKind::Variable(variable) => {
                if let Some(var) = self.int_var(variable) {
                    return Ok(IntT::Var(var));
                }
            }
            TermKind::DomainValue { value, .. } => {
                return value
                    .as_utf8()
                    .ok()
                    .and_then(|value| value.parse::<i128>().ok())
                    .map(IntT::Lit)
                    .ok_or_else(|| Skip("an Int literal beyond i128".to_owned()));
            }
            _ => {}
        }
        let (name, arguments) = self.application(term)?;
        let b = |index: usize| self.int(&arguments[index]).map(Box::new);
        Ok(match (name, arguments.len()) {
            ("plus", 2) => IntT::Add(b(0)?, b(1)?),
            ("half", 1) => IntT::Half(b(0)?),
            ("divInt", 2) => IntT::Div(b(0)?, b(1)?),
            ("pf", 1) => IntT::Pf(b(0)?),
            ("pow", 2) => IntT::Pow(b(0)?, b(1)?),
            ("ite", 3) => IntT::Ite(Box::new(self.bool_term(&arguments[0])?), b(1)?, b(2)?),
            ("g", 1) => IntT::G(b(0)?),
            ("lookup", 2) => IntT::Lookup(Box::new(self.map_term(&arguments[0])?), b(1)?),
            ("sel", 3) => IntT::Sel(Box::new(self.bool_term(&arguments[0])?), b(1)?, b(2)?),
            _ => return skip(format!("the Int symbol {name}")),
        })
    }

    fn bool_term(&self, term: &Term) -> Read<BoolT> {
        match term.kind() {
            TermKind::Variable(variable) if *variable == self.backend.bool => {
                return Ok(BoolT::Var);
            }
            TermKind::DomainValue { value, .. } => {
                return match value.as_utf8() {
                    Ok("true") => Ok(BoolT::Lit(true)),
                    Ok("false") => Ok(BoolT::Lit(false)),
                    _ => skip("a Bool literal of another spelling"),
                };
            }
            _ => {}
        }
        let (name, arguments) = self.application(term)?;
        let i = |index: usize| self.int(&arguments[index]).map(Box::new);
        let b = |index: usize| self.bool_term(&arguments[index]).map(Box::new);
        Ok(match (name, arguments.len()) {
            ("eqInt", 2) => BoolT::Eq(i(0)?, i(1)?),
            ("neInt", 2) => BoolT::Ne(i(0)?, i(1)?),
            ("ltInt", 2) => BoolT::Lt(i(0)?, i(1)?),
            ("leInt", 2) => BoolT::Le(i(0)?, i(1)?),
            ("gtInt", 2) => BoolT::Gt(i(0)?, i(1)?),
            ("geInt", 2) => BoolT::Ge(i(0)?, i(1)?),
            ("notBool", 1) => BoolT::Not(b(0)?),
            ("orBool", 2) => BoolT::Or(b(0)?, b(1)?),
            ("even", 1) => BoolT::Even(i(0)?),
            ("inKeys", 2) => BoolT::InKeys(i(0)?, Box::new(self.map_term(&arguments[1])?)),
            _ => return skip(format!("the Bool symbol {name}")),
        })
    }

    fn map_term(&self, term: &Term) -> Read<MapT> {
        match term.kind() {
            TermKind::Variable(variable) if *variable == self.map_var => Ok(MapT::Var),
            // The concatenation of one binding per entry and of `rest`, defined only where the
            // keys are pairwise distinct and none is a key of `rest`: the oracle's `concat` of the
            // items and the rest, whose definedness is the same disjointness.
            TermKind::Map { entries, rest, .. } => {
                let mut parts = entries
                    .iter()
                    .map(|(key, value)| {
                        Ok(MapT::Item(
                            Box::new(self.int(key)?),
                            Box::new(self.int(value)?),
                        ))
                    })
                    .collect::<Read<Vec<_>>>()?;
                if let Some(rest) = rest {
                    parts.push(self.map_term(rest)?);
                }
                let mut parts = parts.into_iter();
                Ok(match parts.next() {
                    None => MapT::Unit,
                    Some(first) => parts.fold(first, |a, b| MapT::Concat(Box::new(a), Box::new(b))),
                })
            }
            _ => {
                let (name, arguments) = self.application(term)?;
                Ok(match (name, arguments.len()) {
                    ("unit", 0) => MapT::Unit,
                    ("item", 2) => MapT::Item(
                        Box::new(self.int(&arguments[0])?),
                        Box::new(self.int(&arguments[1])?),
                    ),
                    ("concat", 2) => MapT::Concat(
                        Box::new(self.map_term(&arguments[0])?),
                        Box::new(self.map_term(&arguments[1])?),
                    ),
                    _ => return skip(format!("the Map symbol {name}")),
                })
            }
        }
    }
}

// ---------------------------------------------------------------------------------------------
// The check.

/// The three runs of each case.
#[derive(Clone, Copy, Debug)]
enum Run {
    NoSolver,
    Z3,
    Z3Budget,
}

const RUNS: [Run; 3] = [Run::NoSolver, Run::Z3, Run::Z3Budget];

impl fmt::Display for Run {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::NoSolver => "NoSolver, default options",
            Self::Z3 => "Z3, default options",
            Self::Z3Budget => "Z3, small budget kept partial",
        })
    }
}

#[derive(Default)]
struct Stats {
    /// Outputs read back and compared.
    compared: Cell<usize>,
    /// Of those, outputs that differ from the input.
    changed: Cell<usize>,
    /// Of those, outputs with no domain valuation where both sides are definite and `F` holds.
    vacuous: Cell<usize>,
    /// Valuations at which both sides were definite and compared.
    points: Cell<usize>,
    errors: Cell<usize>,
    skipped: RefCell<BTreeMap<Skip, usize>>,
}

fn bump(counter: &Cell<usize>) {
    counter.set(counter.get() + 1);
}

impl fmt::Display for Stats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let skipped = self.skipped.borrow();
        let skipped_total = skipped.values().sum::<usize>();
        let outputs = self.compared.get() + skipped_total;
        write!(
            f,
            "{} outputs: {} compared ({} changed by the simplifier, {} with no valuation where F \
             holds and both sides are definite; {} valuations compared), {} skipped ({:.1}%), {} \
             simplification errors",
            outputs,
            self.compared.get(),
            self.changed.get(),
            self.vacuous.get(),
            self.points.get(),
            skipped_total,
            if outputs == 0 {
                0.0
            } else {
                100.0 * skipped_total as f64 / outputs as f64
            },
            self.errors.get(),
        )?;
        for (Skip(reason), count) in skipped.iter() {
            write!(f, "\n  skipped: {count} for {reason}")?;
        }
        Ok(())
    }
}

fn all(predicates: &[Pred], env: &Env) -> Truth {
    predicates
        .iter()
        .map(|predicate| eval_pred(predicate, env))
        .fold(Truth::True, Truth::and)
}

fn free_of(predicates: &[&[Pred]]) -> Free {
    let mut free = Free::default();
    for predicate in predicates.iter().flat_map(|list| list.iter()) {
        predicate.free(&mut free);
    }
    free
}

fn failure(input: &Input, run: Run, output: &[Pred], free: &Free, env: &Env) -> TestCaseError {
    let mut lines = vec![
        format!("input: {input}"),
        format!("run: {run}"),
        format!("P': [{}]", conjunction(output)),
        format!("valuation: {}", env.show(free)),
        format!(
            "  P ∧ F is {:?} there, P' ∧ F is {:?}",
            all(&input.facts, env).and(all(&input.predicates, env)),
            all(&input.facts, env).and(all(output, env)),
        ),
    ];
    for (name, list) in [("P", &input.predicates), ("F", &input.facts)] {
        for (index, predicate) in list.iter().enumerate() {
            lines.push(format!(
                "  {name}[{index}] is {:?} there",
                eval_pred(predicate, env)
            ));
        }
    }
    for (index, predicate) in output.iter().enumerate() {
        lines.push(format!(
            "  P'[{index}] = {predicate} is {:?} there",
            eval_pred(predicate, env)
        ));
    }
    TestCaseError::fail(lines.join("\n"))
}

fn check_input(
    backend: &Backend,
    read_back: &ReadBack<'_>,
    z3: &dyn SmtSolver,
    input: &Input,
    stats: &Stats,
    trace: bool,
) -> Result<(), TestCaseError> {
    let predicates = input
        .predicates
        .iter()
        .map(|predicate| backend.predicate(predicate))
        .collect::<Vec<_>>();
    let facts = input
        .facts
        .iter()
        .map(|predicate| backend.predicate(predicate))
        .collect::<Vec<_>>();
    for run in RUNS {
        let (options, solver): (_, &dyn SmtSolver) = match run {
            Run::NoSolver => (SimplificationOptions::default(), &NoSolver),
            Run::Z3 => (SimplificationOptions::default(), z3),
            Run::Z3Budget => (SimplificationOptions::keep_partial(input.budget), z3),
        };
        let before = std::time::Instant::now();
        let simplified = simplify_predicates_with_solver(
            &backend.definition,
            &predicates,
            &facts,
            options,
            solver,
        )
        .map_err(|stop| {
            TestCaseError::fail(format!("input: {input}\nrun: {run}\nstopped: {stop:?}"))
        })?;
        let output = match simplified {
            Ok(output) => output,
            Err(error) => {
                bump(&stats.errors);
                if trace {
                    eprintln!("  {run}: error {error:?}");
                }
                continue;
            }
        };
        let changed = output != predicates;
        let output = match read_back.predicates(&output) {
            Ok(output) => output,
            Err(reason) => {
                if trace {
                    eprintln!("  {run}: skipped ({})", reason.0);
                }
                *stats.skipped.borrow_mut().entry(reason).or_default() += 1;
                continue;
            }
        };
        if trace {
            eprintln!(
                "  {run}: [{}] ({:.3} s)",
                conjunction(&output),
                before.elapsed().as_secs_f64()
            );
        }
        bump(&stats.compared);
        if changed {
            bump(&stats.changed);
        }
        let free = free_of(&[&input.predicates, &input.facts, &output]);
        let base = Env {
            ints: [0; 4],
            bool: false,
            map: 0,
            pf_total: false,
            alt_values: false,
        };
        let mut points = 0;
        for env in valuations(&free, &base, &BTreeSet::new()) {
            let facts = all(&input.facts, &env);
            let original = facts.and(all(&input.predicates, &env));
            let simplified = facts.and(all(&output, &env));
            if original == Truth::Unknown || simplified == Truth::Unknown {
                continue;
            }
            if original != simplified {
                return Err(failure(input, run, &output, &free, &env));
            }
            if facts == Truth::True {
                points += 1;
            }
        }
        stats.points.set(stats.points.get() + points);
        if points == 0 {
            bump(&stats.vacuous);
        }
    }
    Ok(())
}

/// Every output of the simplifier the oracle can read, under `NoSolver`, under Z3 and under a
/// small budget, is equivalent to its input under the facts at every valuation of the domain in
/// every model of the definition where both are definite (module docs).
#[test]
fn every_simplified_output_is_equivalent_to_its_input_under_the_facts() {
    let backend = Backend::new();
    let read_back = ReadBack::new(&backend);
    let z3 = solver(&backend.definition, KNOBS);
    let stats = Stats::default();
    let (mut runner, cases, seed) = configured_runner(KNOBS);
    let started = std::time::Instant::now();
    let trace = std::env::var_os(format!("{KNOBS}_TRACE")).is_some();
    let (runs, first_failure) = (Cell::new(0usize), Cell::new(None));
    let outcome = runner.run(&input(symbolic_exponents(KNOBS)), |input| {
        if trace {
            eprintln!("input: {input}");
        }
        runs.set(runs.get() + 1);
        let result = check_input(&backend, &read_back, &z3, &input, &stats, trace);
        if result.is_err() && first_failure.get().is_none() {
            first_failure.set(Some(runs.get()));
        }
        result
    });
    if let Some(first) = first_failure.get() {
        eprintln!("simplifier_equivalence: the first failure was generated case {first}");
    }
    eprintln!(
        "simplifier_equivalence: {cases} cases (seed {}), {:.1} s; {stats}",
        seed.map_or_else(|| "fixed".to_owned(), |seed| seed.to_string()),
        started.elapsed().as_secs_f64()
    );
    match outcome {
        Ok(()) => {}
        Err(TestError::Fail(reason, input)) => {
            panic!("a simplified output is not equivalent to its input (shrunk: {input})\n{reason}")
        }
        Err(TestError::Abort(reason)) => panic!("the property run aborted: {reason}"),
    }
    // A run that compares nothing passes vacuously, so a later generator or read-back change
    // must not make it so silently. Over seeds 1-5 and the fixed one (512 cases each) the share
    // is 29-35%, almost all of it facts false at every valuation; short runs are exempt.
    let (compared, vacuous) = (stats.compared.get(), stats.vacuous.get());
    assert!(
        compared < MIN_OUTPUTS_FOR_FLOOR || vacuous * 100 <= compared * MAX_VACUOUS_PERCENT,
        "{vacuous} of {compared} compared outputs had no valuation where F holds and both sides \
         are definite, over the {MAX_VACUOUS_PERCENT}% bound"
    );
}

/// The vacuous share's bound (`every_simplified_output_is_equivalent_to_its_input_under_the_facts`),
/// asserted on runs of at least `MIN_OUTPUTS_FOR_FLOOR` compared outputs.
const MAX_VACUOUS_PERCENT: usize = 40;
const MIN_OUTPUTS_FOR_FLOOR: usize = 1000;
