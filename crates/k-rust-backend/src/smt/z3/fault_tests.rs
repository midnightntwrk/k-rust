//! Z3's internal error on a cancelled rewrite of a bit-vector comparison, and what the backend
//! emits and does about it.
//!
//! Z3's bit-vector theory internalizes only `bvule` and `bvsle` comparison atoms, and rewrites
//! every other comparison to them first. When Z3 unfolds a `define-fun-rec` body during search
//! and the check's resource limit cancels the rewrite of the unfolded body, a `bvult` of the body
//! reaches internalization as written, an internal error (`UNREACHABLE` in
//! `theory_bv::internalize_atom`): Z3 4.12.5 ends the process with exit status 114, Z3 4.16.0
//! and 5.3.3 answer unknown with the reason `unreachable`. Under a resource limit the error is a
//! deterministic function of the script and the limit. The backend writes every reading's body
//! in operators the search internalizes as written (`word::internalized_operators`), so that
//! neither kind of definition it uses for readings, `define-fun` and `define-fun-rec`, can carry
//! such an operator into the search.
//!
//! The fixtures under `tests/fixtures/z3-internal-error` are two scripts as the backend wrote
//! them before it wrote readings as definitions and comparisons in the internalized shape:
//! `inflight.smt2`, a query of a proof of a Game Boy CPU specification during which Z3 4.12.5
//! ended the process, and `syn1.smt2`, a script of 18 lines built by hand to the same pattern
//! (one word reading with a `bvult`, applied under `bvsle` beside a nonlinear sum). [`INFLIGHT`]
//! and [`SYN1`] list the resource limits at which each meets the error, measured on each Z3
//! version by checking each script once at each of 3,000 and 1,200 random limits (the same
//! limits on every version). On Z3 5.3.3 `inflight.smt2` met it at none of its 3,000: that
//! version decides the script, `sat`, after 235,989 units (4.16.0 needs about 10.4 million), so
//! every limit above that answers and every one below is a cancellation before the search
//! unfolds the reading; `syn1.smt2` still meets it, at 3 of its 1,200. Where a script met the
//! error at no limit on the linked version, its emitted forms are checked at the limits measured
//! on the others, so that every version checks them through the search.
//!
//! A test that may meet the error runs its checks in a child process (this test binary, running
//! [`replay_child`] alone), so that the exit of Z3 4.12.5 ends the child and is read as its exit
//! status, and the harness goes on.

use std::{
    io::Write as _,
    process::{Command, Stdio},
};

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use super::*;
use crate::definition::BackendDefinition;

const SOURCE: &str = r#"[] module MAIN
  hooked-sort SortInt{} [hook{}("INT.Int"),hasDomainValues{}()]
  hooked-sort SortBool{} [hook{}("BOOL.Bool"),hasDomainValues{}()]
  hooked-symbol lt{}(SortInt{},SortInt{}) : SortBool{} [function{}(),total{}(),hook{}("INT.lt"),smt-hook{}("<")]
  hooked-symbol ge{}(SortInt{},SortInt{}) : SortBool{} [function{}(),total{}(),hook{}("INT.ge"),smt-hook{}(">=")]
  hooked-symbol minus{}(SortInt{},SortInt{}) : SortInt{} [function{}(),total{}(),hook{}("INT.sub"),smt-hook{}("-")]
  symbol signed{}(SortInt{}) : SortInt{} [function{}(),total{}()]
  axiom{R} \implies{R}(\equals{SortBool{},R}(lt{}(X:SortInt{},\dv{SortInt{}}("128")),\dv{SortBool{}}("true")), \equals{SortInt{},R}(signed{}(X:SortInt{}), \and{SortInt{}}(X:SortInt{},\top{SortInt{}}()))) [simplification{}()]
  axiom{R} \implies{R}(\equals{SortBool{},R}(ge{}(X:SortInt{},\dv{SortInt{}}("128")),\dv{SortBool{}}("true")), \equals{SortInt{},R}(signed{}(X:SortInt{}), \and{SortInt{}}(minus{}(X:SortInt{},\dv{SortInt{}}("256")),\top{SortInt{}}()))) [simplification{}()]
endmodule []"#;

/// The word reading of `signed` (a byte read as a two's-complement value) over a byte, as the
/// backend emits it: a definition, with its comparison in the internalized shape.
const SIGNED_READING: &str = "(define-fun SMT-WORD-0 ((KRUST-WORD-PARAM-0 (_ BitVec 8))) \
     (_ BitVec 9) (let ((KRUST-WORD-0 KRUST-WORD-PARAM-0) (KRUST-WORD-1 (_ bv128 8)) \
     (KRUST-WORD-3 (_ bv256 9))) (let ((KRUST-WORD-2 (not (bvule KRUST-WORD-1 KRUST-WORD-0))) \
     (KRUST-WORD-4 (bvsub ((_ zero_extend 1) KRUST-WORD-0) KRUST-WORD-3))) (let ((KRUST-WORD-5 \
     (ite KRUST-WORD-2 ((_ zero_extend 1) KRUST-WORD-0) KRUST-WORD-4))) KRUST-WORD-5))))";

const INFLIGHT_SCRIPT: &str =
    include_str!("../../../tests/fixtures/z3-internal-error/inflight.smt2");
const SYN1_SCRIPT: &str = include_str!("../../../tests/fixtures/z3-internal-error/syn1.smt2");

/// The resource limits at which `inflight.smt2` meets the internal error, per Z3 version (none
/// were found on 5.3.3).
const INFLIGHT: Limits = Limits {
    z3_4_12_5: &[425_466, 664_662, 935_437, 1_112_408, 1_365_786],
    z3_4_16_0: &[
        168_047, 241_274, 251_298, 370_079, 434_992, 748_270, 1_269_370, 1_452_641, 1_691_177,
        2_113_222, 2_216_665,
    ],
    z3_5_3_3: &[],
};

/// The resource limits at which `syn1.smt2` meets the internal error, per Z3 version (none were
/// found on 4.12.5).
const SYN1: Limits = Limits {
    z3_4_12_5: &[],
    z3_4_16_0: &[
        65_775, 68_506, 192_615, 445_412, 955_396, 979_468, 1_086_063, 1_092_157,
    ],
    z3_5_3_3: &[139_827, 533_135, 807_869],
};

struct Limits {
    z3_4_12_5: &'static [u32],
    z3_4_16_0: &'static [u32],
    z3_5_3_3: &'static [u32],
}

impl Limits {
    /// The limits measured on the linked Z3: none on a version none was measured on.
    fn linked(&self) -> &'static [u32] {
        match linked_version() {
            Some(Measured::Z3_4_12_5) => self.z3_4_12_5,
            Some(Measured::Z3_4_16_0) => self.z3_4_16_0,
            Some(Measured::Z3_5_3_3) => self.z3_5_3_3,
            None => &[],
        }
    }

    /// The limits a form of the script is checked at: those measured on the linked Z3, or,
    /// where the script met the error at none on it, every limit measured on another version.
    fn checked(&self) -> Vec<u32> {
        if !self.linked().is_empty() {
            return self.linked().to_vec();
        }
        let mut all = [self.z3_4_12_5, self.z3_4_16_0, self.z3_5_3_3].concat();
        all.sort_unstable();
        all.dedup();
        all
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Measured {
    Z3_4_12_5,
    Z3_4_16_0,
    Z3_5_3_3,
}

/// The measured version this build links, from Z3's full version (`Z3 4.16.0.0` from 4.16.0,
/// `4.12.5.0` from 4.12.5, `5.3.3.0` and the commit from 5.3.3).
fn linked_version() -> Option<Measured> {
    let version = z3_version();
    let version = version.strip_prefix("Z3 ").unwrap_or(version);
    if version.starts_with("4.12.5") {
        Some(Measured::Z3_4_12_5)
    } else if version.starts_with("4.16.0") {
        Some(Measured::Z3_4_16_0)
    } else if version.starts_with("5.3.3") {
        Some(Measured::Z3_5_3_3)
    } else {
        None
    }
}

fn definition() -> BackendDefinition {
    BackendDefinition::internalize(&parse_definition(SOURCE).unwrap(), "MAIN").unwrap()
}

fn term(d: &BackendDefinition, text: &str) -> Term {
    d.internalize_term(&parse_pattern(text).unwrap(), &[])
        .unwrap()
}

/// `0 <= name < 256`.
fn byte(d: &BackendDefinition, name: &str) -> [Predicate; 2] {
    [
        Predicate::Term(term(
            d,
            &format!(r#"ge{{}}({name}:SortInt{{}},\dv{{SortInt{{}}}}("0"))"#),
        )),
        Predicate::Term(term(
            d,
            &format!(r#"lt{{}}({name}:SortInt{{}},\dv{{SortInt{{}}}}("256"))"#),
        )),
    ]
}

/// The script of a query comparing `signed` of two bytes, as the backend prepares it.
fn signed_query() -> String {
    let d = definition();
    let known = [byte(&d, "X"), byte(&d, "Y")].concat();
    let checked = Predicate::Term(term(
        &d,
        "lt{}(signed{}(X:SortInt{}),signed{}(Y:SortInt{}))",
    ));
    let query = SmtPrelude::from_definition(&d)
        .unwrap()
        .query(&known, &Substitution::new(), &[checked], false)
        .unwrap()
        .unwrap();
    query.base().to_owned()
}

/// The definitions in `script` (one command per line, as the backend and the fixtures write
/// them).
fn definitions(script: &str) -> Vec<&str> {
    script
        .lines()
        .filter(|line| line.starts_with("(define-fun"))
        .collect()
}

/// A reading that applies no `define-fun` is itself a `define-fun`, and no reading writes a
/// comparison Z3's bit-vector theory does not internalize: `signed`'s scalar summary and its word
/// reading are both definitions, and the word reading's `x < 128` is `(not (bvule 128 x))`.
#[test]
fn a_reading_that_applies_no_definition_is_a_definition_in_the_internalized_shape() {
    let script = signed_query();
    let word = definitions(&script)
        .into_iter()
        .filter(|line| line.contains(" SMT-WORD-0 "))
        .collect::<Vec<_>>();
    assert_eq!(word, [SIGNED_READING], "{script}");
    let summaries = definitions(&script)
        .into_iter()
        .filter(|line| !line.contains("KRUST-POWER") && !line.contains("SMT-WORD-"))
        .collect::<Vec<_>>();
    assert!(!summaries.is_empty(), "{script}");
    for line in summaries {
        assert!(line.starts_with("(define-fun SMT-"), "{line}");
    }
    for line in definitions(&script) {
        for written in [
            "bvult", "bvslt", "bvugt", "bvsgt", "bvuge", "bvsge", "bvsdiv", "bvsrem", "=>",
            "distinct",
        ] {
            assert!(
                !line.contains(&format!("({written} ")),
                "{written} in {line}"
            );
        }
    }
}

/// `script` with the word reading it defines replaced by the backend's current reading of
/// `signed` (renamed to `name`), and every non-recursive reading's command as the backend now
/// writes it: the form of the script the backend emits.
fn emitted_form(script: &str, name: &str) -> String {
    let reading = definitions(&signed_query())
        .into_iter()
        .find(|line| line.contains(" SMT-WORD-0 "))
        .expect("the word reading of signed")
        .replacen(" SMT-WORD-0 ", &format!(" {name} "), 1);
    let mut replaced = false;
    let lines = script
        .lines()
        .map(|line| {
            let defines = |keyword: &str| line.starts_with(&format!("({keyword} {name} "));
            if defines("define-fun-rec") || defines("define-fun") {
                replaced = true;
                reading.clone()
            } else if line.starts_with("(define-fun-rec SMT-") {
                // The fixture's scalar summary of `signed`, which applies no reading: a
                // `define-fun`, as the emission test shows.
                line.replacen("(define-fun-rec ", "(define-fun ", 1)
            } else {
                line.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join("\n");
    assert!(replaced, "the script defines no {name}");
    assert!(!lines.contains("define-fun-rec"), "{lines}");
    lines
}

/// `script` with the word reading it defines replaced by the backend's current reading of
/// `signed` (renamed to `name`) kept a `define-fun-rec`, as the backend writes a reading that
/// applies a `define-fun` reading, and every other command as first written: the comparison's
/// shape alone protects that form.
fn recursive_form(script: &str, name: &str) -> String {
    let reading = definitions(&signed_query())
        .into_iter()
        .find(|line| line.contains(" SMT-WORD-0 "))
        .expect("the word reading of signed")
        .replacen(
            "(define-fun SMT-WORD-0 ",
            &format!("(define-fun-rec {name} "),
            1,
        );
    let mut replaced = false;
    let lines = script
        .lines()
        .map(|line| {
            if line.starts_with(&format!("(define-fun-rec {name} ")) {
                replaced = true;
                reading.clone()
            } else {
                line.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join("\n");
    assert!(replaced, "the script defines no {name} with define-fun-rec");
    assert!(!lines.contains("(bvult "), "{lines}");
    lines
}

/// The environment variable that makes [`replay_child`] check its standard input at the
/// comma-separated resource limits it names.
const LIMITS_VARIABLE: &str = "K_RUST_TEST_Z3_FAULT_LIMITS";
/// The environment variable holding the retries of each of [`replay_child`]'s queries.
const RETRIES_VARIABLE: &str = "K_RUST_TEST_Z3_FAULT_RETRIES";
/// The prefix of each line [`replay_child`] prints: `<limit> <outcome> <attempts>`.
const MARK: &str = "z3-fault-replay:";

/// Run by [`in_child`] alone, in a process of its own: solve the script on standard input once
/// per resource limit, as the solver solves an uncached query (`Z3Solver::solve_uncached`), and
/// print each outcome as soon as it is known.
#[test]
#[ignore = "run by the tests of this module in a child process, with its input"]
fn replay_child() {
    let Ok(limits) = std::env::var(LIMITS_VARIABLE) else {
        return;
    };
    let retries = std::env::var(RETRIES_VARIABLE).map_or(0, |r| r.parse().unwrap());
    let script = std::io::read_to_string(std::io::stdin()).unwrap();
    let d = definition();
    for limit in limits.split(',') {
        let limit: u32 = limit.parse().unwrap();
        let solver = Z3Solver::with_options(
            &d,
            Z3Options {
                budget: SmtBudget::Units(std::num::NonZeroU32::new(limit).unwrap()),
                retry_limit: retries,
            },
        )
        .unwrap();
        let outcome = match solver.solve_uncached(&script).expect("no stop is armed") {
            Ok(Satisfiability::Sat) => "sat".to_owned(),
            Ok(Satisfiability::Unsat) => "unsat".to_owned(),
            Ok(Satisfiability::Unknown(reason)) => format!("unknown:{reason}"),
            Err(Unanswered::Fault(reason)) => format!("fault:{reason}"),
            Err(Unanswered::Rejected(rejected)) => format!("rejected:{}", rejected.message),
        };
        let attempts = solver.attempt_limits().len();
        let mut out = std::io::stdout().lock();
        writeln!(
            out,
            "{MARK} {limit} {} {attempts}",
            outcome.replace(' ', "_")
        )
        .unwrap();
        out.flush().unwrap();
    }
}

/// What a child process running [`replay_child`] did.
#[derive(Debug)]
struct Child {
    /// Its exit status's code; `None` if a signal ended it.
    code: Option<i32>,
    /// `(limit, outcome, attempts)` per limit it finished.
    outcomes: Vec<(u32, String, usize)>,
    stderr: String,
}

/// Run [`replay_child`] in a child process on `script` at `limits`, with `retries` per query.
fn in_child(script: &str, limits: &[u32], retries: u32) -> Child {
    let module = module_path!()
        .split_once("::")
        .map_or(module_path!(), |(_, path)| path);
    let mut child = Command::new(std::env::current_exe().unwrap())
        .args([
            &format!("{module}::replay_child"),
            "--exact",
            "--ignored",
            "--nocapture",
            "--test-threads=1",
        ])
        .env(
            LIMITS_VARIABLE,
            limits
                .iter()
                .map(u32::to_string)
                .collect::<Vec<_>>()
                .join(","),
        )
        .env(RETRIES_VARIABLE, retries.to_string())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(script.as_bytes())
        .unwrap();
    let output = child.wait_with_output().unwrap();
    let outcomes = String::from_utf8_lossy(&output.stdout)
        .lines()
        // The harness writes the test's name on the line its first output continues.
        .filter_map(|line| line.split_once(MARK).map(|(_, line)| line))
        .map(|line| {
            let fields = line.split_whitespace().collect::<Vec<_>>();
            let [limit, outcome, attempts] = fields[..] else {
                panic!("{line}")
            };
            (
                limit.parse().unwrap(),
                outcome.to_owned(),
                attempts.parse().unwrap(),
            )
        })
        .collect();
    Child {
        code: output.status.code(),
        outcomes,
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
    }
}

/// The emitted form of each script answers at every limit at which the script as first written
/// met the internal error ([`Limits::checked`]): an answer or an ordinary unknown, never the
/// error, and the process does not end.
fn assert_answers_at_every_limit(script: &str, limits: &Limits) {
    let limits = limits.checked();
    let child = in_child(script, &limits, 0);
    assert_eq!(child.code, Some(0), "{child:?}");
    assert_eq!(
        child.outcomes.iter().map(|o| o.0).collect::<Vec<_>>(),
        limits,
        "{child:?}"
    );
    for (limit, outcome, _) in &child.outcomes {
        let reason = outcome.strip_prefix("unknown:");
        assert!(
            matches!(outcome.as_str(), "sat" | "unsat")
                || reason.is_some_and(|r| !internal_error(r)),
            "at {limit}: {outcome}; {child:?}"
        );
    }
}

#[test]
fn the_emitted_form_of_the_crashing_query_answers_at_every_limit_it_crashed_at() {
    assert_answers_at_every_limit(&emitted_form(INFLIGHT_SCRIPT, "SMT-WORD-0"), &INFLIGHT);
}

#[test]
fn the_emitted_form_of_the_minimized_script_answers_at_every_limit_it_crashed_at() {
    assert_answers_at_every_limit(&emitted_form(SYN1_SCRIPT, "w"), &SYN1);
}

/// A reading Z3 unfolds during search, with its comparison in the internalized shape, answers at
/// every limit at which the reading as first written met the internal error.
#[test]
fn the_recursive_form_of_the_crashing_query_with_internalized_comparisons_answers() {
    assert_answers_at_every_limit(&recursive_form(INFLIGHT_SCRIPT, "SMT-WORD-0"), &INFLIGHT);
}

#[test]
fn the_recursive_form_of_the_minimized_script_with_internalized_comparisons_answers() {
    assert_answers_at_every_limit(&recursive_form(SYN1_SCRIPT, "w"), &SYN1);
}

/// The scripts as first written meet the error at their first measured limit on the version it
/// was measured on: Z3 4.12.5 ends the process with status 114; on Z3 4.16.0 and 5.3.3 the query
/// ends at that attempt with the error, although three retries were allowed, and is no unknown.
/// This shows the limits still reach the error, so that the tests above show its absence. A
/// script with no limit measured on the linked version (`inflight.smt2` on 5.3.3) is skipped.
#[test]
fn the_scripts_as_first_written_meet_the_internal_error_at_their_first_limit() {
    let Some(version) = linked_version() else {
        eprintln!("no limits were measured on Z3 {}", z3_version());
        return;
    };
    for (script, limits) in [(INFLIGHT_SCRIPT, &INFLIGHT), (SYN1_SCRIPT, &SYN1)] {
        let Some(&limit) = limits.linked().first() else {
            continue;
        };
        let child = in_child(script, &[limit], 3);
        match version {
            Measured::Z3_4_12_5 => {
                assert_eq!(child.code, Some(114), "{child:?}");
                assert!(child.outcomes.is_empty(), "{child:?}");
                assert!(child.stderr.contains("theory_bv.cpp"), "{child:?}");
            }
            Measured::Z3_4_16_0 | Measured::Z3_5_3_3 => {
                assert_eq!(child.code, Some(0), "{child:?}");
                assert_eq!(
                    child.outcomes,
                    [(limit, "fault:unreachable".to_owned(), 1)],
                    "{child:?}"
                );
                assert!(child.stderr.contains("theory_bv.cpp"), "{child:?}");
            }
        }
    }
}

#[test]
fn only_z3s_internal_error_texts_are_internal_errors() {
    for reason in [
        "unreachable",
        "internal fatal",
        "not implemented yet",
        "formula has not been simplified",
        "formula has not been simplified : (=> a b)",
    ] {
        assert!(internal_error(reason), "{reason}");
    }
    for reason in [
        "timeout",
        "canceled",
        "max. resource limit exceeded",
        "interrupted",
        "(incomplete (theory arithmetic))",
        "unknown",
    ] {
        assert!(!internal_error(reason), "{reason}");
    }
}
