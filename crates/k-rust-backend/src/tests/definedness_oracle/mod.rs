//! A randomized differential test of the value contract against an independent oracle.
//!
//! The contract (`docs/compatibility.md`, "Anywhere rules"; the unit design
//! `value-contract-design.md`) reads a definition by its normal-form model `M_NF`: the ground
//! normal forms of the innermost relation `->E`, priority decided on normal-form arguments. Every
//! value claim of the backend (an instance-normal token, a normal-form certificate, an apartness
//! decision between certified terms, a `\ceil` discharge through a `value-production` head) is
//! made only at term indexes the load-time critical-pair check leaves untainted, and must hold
//! in one model of the definition.
//!
//! The oracle ([`language`], [`engine`], [`forced`]) evaluates the definition's axioms with no
//! backend code below its interface: its own matching modulo the injection and overload axioms,
//! its own evaluator of `M_NF`, its own taint closure, and its own derivation of what every model
//! must satisfy. It does not build the model `M'` of the closure's construction. [`checks`]
//! compares the backend's claims with it:
//!
//! - **V4.** On a definition the check accepts, every explored ground term whose evaluation ends
//!   has exactly one normal form.
//! - **V5.** There, every claim agrees with that normal form: a token or a certificate only on a
//!   normal form, `\ceil` discharged only on a defined term, apartness only between different
//!   normal forms, and a claim on a generalization (a constructor or literal subterm replaced by
//!   a variable) only when every explored instance satisfies it.
//! - **V6.** On a definition with non-joined pairs: (a) the oracle's closure of the reported pairs
//!   is the backend's taint set (a second implementation of the same rule, which shows the two
//!   agree, not that the rule is sound); (c) no claim is made on a term with a tainted
//!   application; and (b) the claims on an untainted term whose evaluation applies only
//!   untainted equations agree with its normal form, which is unique.
//! - **V6 (d).** On every definition the derivation does not show to have no model: no claim on
//!   a term that every model makes undefined, nor on a generalization of one by a subterm every
//!   model makes defined ([`forced`]). This is the test of property (B) that reads neither the
//!   closure nor `M_NF`, so a closure, vacuity or join rule that misses a class shows here.
//! - **V9.** On every definition, the load's verdict (`CheckScope::Gate`, which classifies only
//!   the pairs that can change a claim) and the full check's (`CheckScope::All`) admit the same
//!   claims at every gate site and warn about the same pairs. The expectations above (acceptance,
//!   V4's one normal form, the tainted set of V6) are read from the full check, the claims from
//!   the loaded definition.
//!
//! Preconditions are measured, never assumed away: a query whose evaluation does not end within
//! the bounds is outside P0 and counted (ceiling 10 % of queries), a definition that reaches a
//! total symbol undefined on defined arguments is outside P2 and counted (ceiling 25 % of
//! definitions), and a definition the backend does not internalize is a failure.
//!
//! The definitions are the reviewers' probes ([`probes`]), whose queries every model makes
//! undefined and which must keep their obligations; variants of each that write the same axioms
//! with other variable names and equation orders; one fixed template per feature class
//! ([`generator::templates`]); and seeded random ones. `KRUST_DEFINEDNESS_ORACLE_CASES` (default
//! [`DEFAULT_CASES`]), `KRUST_DEFINEDNESS_ORACLE_FIRST` and `KRUST_DEFINEDNESS_ORACLE_SEED` set
//! the random run, `KRUST_DEFINEDNESS_ORACLE_VARIANTS` the variants per probe; each accepts
//! decimal or `0x`-prefixed hexadecimal. Run with `--nocapture` for the summaries,
//! `KRUST_DEFINEDNESS_ORACLE_VERBOSE` for each query, `KRUST_DEFINEDNESS_ORACLE_KORE` for each
//! definition's KORE text, `KRUST_DEFINEDNESS_ORACLE_PROGRESS` for each definition's label as it
//! starts.

mod checks;
mod completeness;
mod corpus;
mod engine;
mod forced;
mod generator;
mod language;
mod mutations;
mod probes;
mod unifier;

use std::collections::BTreeMap;

use checks::{Class, Tally, check_definition};
use language::{Definition, pattern_variables, renamed};
use probes::Expect;

/// Random definitions in the default run.
const DEFAULT_CASES: u64 = 24;

/// The seed of the default run.
const DEFAULT_SEED: u64 = 0x5eed_0006;

/// Runs at least this long enforce the floors.
const FLOOR_CASES: u64 = 1_000;

pub(super) struct Rng(pub(super) u64);

impl Rng {
    pub(super) fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut mixed = self.0;
        mixed = (mixed ^ (mixed >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        mixed = (mixed ^ (mixed >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        mixed ^ (mixed >> 31)
    }

    pub(super) fn below(&mut self, bound: usize) -> usize {
        usize::try_from(self.next() % u64::try_from(bound).unwrap()).unwrap()
    }

    pub(super) fn percent(&mut self, chance: usize) -> bool {
        self.below(100) < chance
    }

    pub(super) fn pick<'a, T>(&mut self, items: &'a [T]) -> &'a T {
        &items[self.below(items.len())]
    }
}

/// A number written in decimal or with the `0x` prefix in hexadecimal (underscores allowed).
fn parse_number(text: &str) -> Result<u64, String> {
    let cleaned = text.trim().replace('_', "");
    let parsed = match cleaned
        .strip_prefix("0x")
        .or_else(|| cleaned.strip_prefix("0X"))
    {
        Some(digits) => u64::from_str_radix(digits, 16),
        None => cleaned.parse(),
    };
    parsed
        .map_err(|_| format!("`{text}` is neither a decimal nor a 0x-prefixed hexadecimal number"))
}

/// The value of the environment variable `name`, or `default` when it is unset; any other text
/// than a number fails the run.
fn environment(name: &str, default: u64) -> u64 {
    match std::env::var(name) {
        Err(_) => default,
        Ok(text) => parse_number(&text).unwrap_or_else(|error| panic!("{name}: {error}")),
    }
}

/// Runs `body` on a thread with a large stack: deep simplifications must not abort the run.
fn on_large_stack(body: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(512 << 20)
        .spawn(body)
        .expect("the test thread starts")
        .join()
        .unwrap_or_else(|panic| std::panic::resume_unwind(panic));
}

#[test]
fn the_seed_variables_accept_decimal_and_hexadecimal_numbers_only() {
    assert_eq!(parse_number("0x5eed0006"), Ok(0x5eed_0006));
    assert_eq!(parse_number("0x5eed_0006"), Ok(0x5eed_0006));
    assert_eq!(parse_number("7"), Ok(7));
    assert!(parse_number("seven").is_err());
    assert!(parse_number("0x").is_err());
    assert!(parse_number("").is_err());
}

/// The ceilings every run enforces, and the floors of the long runs.
fn assert_bounds(tally: &Tally, cases: u64, failures: &mut Vec<String>) {
    if tally.rejected > 0 {
        failures.push(format!(
            "{} definitions rejected (ceiling 0)",
            tally.rejected
        ));
    }
    if tally.nonterminating * 10 > tally.queries {
        failures.push(format!(
            "{} of {} queries outside P0 (ceiling 10 %)",
            tally.nonterminating, tally.queries
        ));
    }
    if tally.outside_totality * 4 > tally.definitions {
        failures.push(format!(
            "{} of {} definitions outside P2 (ceiling 25 %)",
            tally.outside_totality, tally.definitions
        ));
    }
    // V6 (d) must have something to check: queries every model of a definition with a model
    // makes undefined (the templates of review 1's classes give some in every run).
    if tally.forced_undefined == 0 {
        failures.push("no query undefined in every model of a definition with a model".into());
    }
    for class in Class::ALL {
        let count = tally.classes.get(&class).copied().unwrap_or(0);
        if count == 0 {
            failures.push(format!("no definition of class {class:?}"));
        }
        if cases >= FLOOR_CASES && count * 20 < tally.definitions {
            failures.push(format!(
                "{count} of {} definitions of class {class:?} (floor 5 %)",
                tally.definitions
            ));
        }
    }
    if cases >= FLOOR_CASES {
        if tally.accepted * 10 < tally.definitions * 3 {
            failures.push(format!(
                "{} of {} definitions accepted (floor 30 %)",
                tally.accepted, tally.definitions
            ));
        }
        if tally.partially_tainted * 5 < tally.definitions {
            failures.push(format!(
                "{} of {} definitions partially tainted (floor 20 %)",
                tally.partially_tainted, tally.definitions
            ));
        }
        for (kind, count) in [
            ("tokens", tally.tokens),
            ("certificates", tally.certificates),
            ("apartness decisions", tally.apartness),
            ("\\ceil discharges", tally.ceilings),
        ] {
            if count < tally.accepted * 5 {
                failures.push(format!(
                    "{count} {kind} checked over {} accepted definitions (floor 5 each)",
                    tally.accepted
                ));
            }
        }
    }
}

/// Runs the checks on the templates and `cases` random definitions from `seed`.
fn run_random(first: u64, cases: u64, seed: u64) -> Tally {
    let mut total = Tally::default();
    for (name, definition, seeds) in generator::templates() {
        let mut rng = Rng(seed);
        let (tally, _) = check_definition(&name, &definition, &seeds, &[], &mut rng);
        total.add(tally);
    }
    for case in first..first + cases {
        let mut rng = Rng(seed ^ case.wrapping_mul(0x9e37_79b9_7f4a_7c15));
        let (definition, seeds) = generator::random_definition(&mut rng);
        let (tally, _) = check_definition(
            &format!("case {case} (seed {seed:#x})"),
            &definition,
            &seeds,
            &[],
            &mut rng,
        );
        total.add(tally);
        if total.failures.len() >= 20 {
            break;
        }
    }
    total
}

#[test]
fn random_definitions_keep_the_value_contract() {
    on_large_stack(|| {
        let cases = environment("KRUST_DEFINEDNESS_ORACLE_CASES", DEFAULT_CASES);
        let first = environment("KRUST_DEFINEDNESS_ORACLE_FIRST", 0);
        let seed = environment("KRUST_DEFINEDNESS_ORACLE_SEED", DEFAULT_SEED);
        let total = run_random(first, cases, seed);
        eprintln!(
            "{}",
            total.summary(&format!("definedness oracle (seed {seed:#x})"))
        );
        for divergence in &total.divergences {
            eprintln!("  {divergence}");
        }
        let mut failures = total.failures.clone();
        assert_bounds(&total, cases, &mut failures);
        assert!(failures.is_empty(), "{}", failures.join("\n"));
    });
}

/// Runs every probe; returns the tally and the probes whose expectation failed.
fn run_probes() -> (Tally, Vec<String>) {
    let mut total = Tally::default();
    let mut unmet = Vec::new();
    for probe in probes::probes() {
        let mut rng = Rng(DEFAULT_SEED);
        let (tally, verdict) = check_definition(
            &probe.name,
            &probe.definition,
            &probe.seeds,
            &probe.undefined,
            &mut rng,
        );
        match probe.expect {
            Expect::Kept => {
                if tally.outside_totality > 0 {
                    unmet.push(format!("{}: the oracle finds it outside P2", probe.name));
                }
                if verdict.probes.len() != probe.undefined.len() {
                    unmet.push(format!(
                        "{}: {} of {} queries asked",
                        probe.name,
                        verdict.probes.len(),
                        probe.undefined.len()
                    ));
                }
                for (query, (kept, token)) in probe.undefined.iter().zip(&verdict.probes) {
                    let query = checks::show(query);
                    if !kept {
                        unmet.push(format!("{}: \\ceil({query}) is discharged", probe.name));
                    }
                    if *token {
                        unmet.push(format!("{}: {query} is instance-normal", probe.name));
                    }
                }
            }
            Expect::OutsideTotality => {
                if tally.outside_totality == 0 {
                    unmet.push(format!(
                        "{}: the oracle does not find it outside P2",
                        probe.name
                    ));
                }
            }
            Expect::OutsideTermination => {
                if tally.nonterminating == 0 {
                    unmet.push(format!(
                        "{}: the oracle does not find it outside P0",
                        probe.name
                    ));
                }
            }
        }
        total.add(tally);
    }
    (total, unmet)
}

/// Every reviewer probe: its queries keep their obligations (or the oracle places the
/// definition outside the precondition the probe violates), and every check holds.
#[test]
fn the_reviewers_probes_keep_the_value_contract() {
    on_large_stack(|| {
        let (total, unmet) = run_probes();
        eprintln!("{}", total.summary("definedness oracle, probes"));
        assert!(unmet.is_empty(), "{}", unmet.join("\n"));
        assert!(total.failures.is_empty(), "{}", total.failures.join("\n"));
    });
}

/// The variable names [`variant`] draws from: few, so that equations often share them.
const VARIANT_NAMES: [&str; 5] = ["VarX", "VarY", "VarZ", "VarU", "VarW"];

/// A definition with the axioms of `definition`, written differently: each equation's variables
/// renamed one-to-one to names drawn from [`VARIANT_NAMES`] (so that independent variables of
/// different equations often share a name), and the equations in another order. Each equation
/// quantifies its variables on its own, so this denotes the same theory.
fn variant(definition: &Definition, rng: &mut Rng) -> Definition {
    let mut variant = definition.clone();
    for equation in &mut variant.equations {
        if equation.overload.is_some() {
            continue;
        }
        let mut variables = BTreeMap::new();
        pattern_variables(&equation.lhs, &mut variables);
        pattern_variables(&equation.rhs, &mut variables);
        if variables.len() > VARIANT_NAMES.len() {
            continue;
        }
        let mut names = VARIANT_NAMES.to_vec();
        let renaming = variables
            .keys()
            .map(|name| {
                let chosen = names.remove(rng.below(names.len()));
                (name.clone(), chosen.to_owned())
            })
            .collect::<BTreeMap<_, _>>();
        equation.lhs = renamed(&equation.lhs, &renaming);
        equation.rhs = renamed(&equation.rhs, &renaming);
        for condition in [&mut equation.requires, &mut equation.ensures]
            .into_iter()
            .flatten()
        {
            *condition = renamed(condition, &renaming);
        }
    }
    for index in (1..variant.equations.len()).rev() {
        variant.equations.swap(index, rng.below(index + 1));
    }
    variant
}

/// Variants of every reviewer probe ([`variant`]): the checks hold for any way of writing the
/// same axioms. `KRUST_DEFINEDNESS_ORACLE_VARIANTS` (default 2) variants per probe.
#[test]
fn variants_of_the_reviewers_probes_keep_the_value_contract() {
    on_large_stack(|| {
        let variants = environment("KRUST_DEFINEDNESS_ORACLE_VARIANTS", 2);
        let seed = environment("KRUST_DEFINEDNESS_ORACLE_SEED", DEFAULT_SEED);
        let mut total = Tally::default();
        let mut unmet = Vec::new();
        for (index, probe) in probes::probes().into_iter().enumerate() {
            for number in 0..variants {
                let mut rng = Rng(seed
                    ^ u64::try_from(index)
                        .unwrap()
                        .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                    ^ number.wrapping_mul(0xbf58_476d_1ce4_e5b9));
                let definition = variant(&probe.definition, &mut rng);
                let (tally, verdict) = check_definition(
                    &format!("{} (variant {number})", probe.name),
                    &definition,
                    &probe.seeds,
                    &probe.undefined,
                    &mut rng,
                );
                if probe.expect == Expect::Kept {
                    for (query, (kept, token)) in probe.undefined.iter().zip(&verdict.probes) {
                        if !kept || *token {
                            unmet.push(format!(
                                "{} (variant {number}): {} claimed",
                                probe.name,
                                checks::show(query)
                            ));
                        }
                    }
                }
                total.add(tally);
            }
            if total.failures.len() >= 20 {
                break;
            }
        }
        eprintln!("{}", total.summary("definedness oracle, probe variants"));
        assert!(unmet.is_empty(), "{}", unmet.join("\n"));
        assert!(total.failures.is_empty(), "{}", total.failures.join("\n"));
    });
}

/// A definition outside P0 whose pair has a condition that evaluates without end
/// (`pf(Y) = pf(k(Y))`, and `h(X) = mk(1) requires pf(c) ==K c` beside `h(X) = mk(2)`) still
/// loads: the check's simplification of the condition stops at its deadline, decides nothing,
/// and the pair is not joined.
#[test]
fn a_condition_whose_evaluation_does_not_end_does_not_keep_a_definition_from_loading() {
    use language::{app, cons, int, var};
    on_large_stack(|| {
        let definition = Definition::new(&["A"])
            .constructor("c", &[], "A")
            .constructor("k", &["A"], "A")
            .function("pf", &["A"], "A")
            .equation(
                app("pf", vec![var("VarY", "A")]),
                app("pf", vec![app("k", vec![var("VarY", "A")])]),
            )
            .head("h", &["A"], "S")
            .conditional(
                app("h", vec![var("VarX", "A")]),
                app("mk", vec![int(1)]),
                Some(app("eqA", vec![app("pf", vec![cons("c")]), cons("c")])),
            )
            .equation(app("h", vec![var("VarX", "A")]), app("mk", vec![int(2)]));
        let started = std::time::Instant::now();
        let backend = checks::backend(&definition).expect("the definition loads");
        assert!(
            started.elapsed() < std::time::Duration::from_secs(60),
            "loading took {:?}",
            started.elapsed()
        );
        assert!(
            backend
                .value_claims()
                .tainted_symbols()
                .iter()
                .any(|symbol| symbol.as_ref() == "h"),
            "{:?}",
            backend.value_claims().unjoined()
        );
    });
}
