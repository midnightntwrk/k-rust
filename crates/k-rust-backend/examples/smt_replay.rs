//! Replay a script of the SMT trace (`K_RUST_SMT_TRACE`) on the Z3 library this build links.
//!
//! ```text
//! smt_replay SCRIPT.smt2 [--rlimit N] [--timeout MS] [--retries R]
//! ```
//!
//! The script's header states the attempt ladder it was traced under; without a header (a script
//! a minimizer wrote, say) the solver's default ladder applies. `--rlimit N` replays clock-free,
//! starting at `N` resource units, `--timeout MS` replays bounded by the clock, starting at `MS`
//! milliseconds, and `--retries R` sets the number of retries of an unknown answer. Each value is
//! a whole number that fits in 32 bits, written in decimal (`1000000000`) or in scientific
//! notation (`1e9`). Every attempt
//! runs on one fresh Z3 context, as the solver runs an uncached query, so an attempt starts from
//! the state the attempts before it left. The tool prints each attempt's answer, its limits and
//! the resource units it consumed, then the final answer.
//!
//! Build it once per Z3 library: with the dynamic library on `LIBRARY_PATH` and
//! `LD_LIBRARY_PATH`, `cargo run -p k-rust-backend --features z3 --example smt_replay -- ...`; with
//! another Z3, in a target directory of its own.

use std::{num::NonZeroU32, process::ExitCode};

use k_rust_backend::smt::{self, trace, z3_version};

fn usage() -> ExitCode {
    eprintln!("usage: smt_replay SCRIPT.smt2 [--rlimit N] [--timeout MS] [--retries R]");
    eprintln!("  N, MS and R are whole numbers below 2^32, as 1000000000 or 1e9");
    ExitCode::from(2)
}

/// A whole number below 2^32, in decimal or in scientific notation (`1e9`, `2.5e3`).
fn count(text: &str) -> Result<u32, String> {
    if let Ok(value) = text.parse::<u32>() {
        return Ok(value);
    }
    let not_a_count = || format!("`{text}` is not a whole number below 2^32");
    let (mantissa, exponent) = text.split_once(['e', 'E']).ok_or_else(not_a_count)?;
    let exponent = exponent.parse::<u32>().map_err(|_| not_a_count())?;
    let (whole, fraction) = mantissa.split_once('.').unwrap_or((mantissa, ""));
    if (whole.is_empty() && fraction.is_empty())
        || !whole
            .bytes()
            .chain(fraction.bytes())
            .all(|byte| byte.is_ascii_digit())
    {
        return Err(not_a_count());
    }
    // The value is `digits × 10^(exponent − fraction length)`, exactly, in integers.
    let digits = format!("{whole}{fraction}");
    let fraction_length = u32::try_from(fraction.len()).map_err(|_| not_a_count())?;
    let mut value = digits.parse::<u128>().map_err(|_| not_a_count())?;
    if exponent >= fraction_length {
        let scale = 10_u128
            .checked_pow(exponent - fraction_length)
            .ok_or_else(not_a_count)?;
        value = value.checked_mul(scale).ok_or_else(not_a_count)?;
    } else {
        let scale = 10_u128
            .checked_pow(fraction_length - exponent)
            .ok_or_else(not_a_count)?;
        if value % scale != 0 {
            return Err(not_a_count());
        }
        value /= scale;
    }
    u32::try_from(value).map_err(|_| not_a_count())
}

fn main() -> ExitCode {
    let mut arguments = std::env::args().skip(1);
    let mut path = None;
    let mut rlimit = None;
    let mut timeout = None;
    let mut retries = None;
    while let Some(argument) = arguments.next() {
        let mut value = |name: &str| -> Result<u32, ExitCode> {
            let Some(value) = arguments.next() else {
                eprintln!("{name} needs a value");
                return Err(usage());
            };
            count(&value).map_err(|error| {
                eprintln!("{name}: {error}");
                usage()
            })
        };
        let parsed = match argument.as_str() {
            "--rlimit" => value("--rlimit").map(|value| rlimit = Some(value)),
            "--timeout" => value("--timeout").map(|value| timeout = Some(value)),
            "--retries" => value("--retries").map(|value| retries = Some(value)),
            "--help" | "-h" => return usage(),
            _ if path.is_none() && !argument.starts_with("--") => {
                path = Some(argument);
                Ok(())
            }
            _ => return usage(),
        };
        if let Err(code) = parsed {
            return code;
        }
    }
    let Some(path) = path else {
        return usage();
    };
    let text = match std::fs::read_to_string(&path) {
        Ok(text) => text,
        Err(error) => {
            eprintln!("{path}: {error}");
            return ExitCode::from(2);
        }
    };
    let mut traced = match trace::TracedScript::parse(&text) {
        Ok(traced) => traced,
        Err(error) => {
            eprintln!("{path}: {error}");
            return ExitCode::from(2);
        }
    };
    let rlimit = match rlimit.map(NonZeroU32::new) {
        Some(None) => {
            eprintln!("--rlimit must be positive");
            return usage();
        }
        Some(Some(rlimit)) => Some(rlimit),
        None => None,
    };
    if rlimit.is_some() || timeout.is_some() {
        #[expect(
            clippy::disallowed_methods,
            reason = "`--timeout MS` asks to replay under the clock"
        )]
        let budget = smt::SmtBudget::requested(timeout, rlimit);
        match budget {
            Ok(budget) => traced.options.budget = budget,
            Err(_) => {
                eprintln!("--rlimit and --timeout choose different ladders; give one");
                return usage();
            }
        }
        traced.clocked = true;
    }
    if let Some(retries) = retries {
        traced.options.retry_limit = retries;
    }
    println!("linked: {}", z3_version());
    if let Some(z3) = &traced.z3 {
        println!("traced: {z3}");
    }
    if let Some(attempt) = traced.attempt {
        println!("in flight at attempt {attempt}");
    }
    match trace::replay(&traced.script, traced.options, traced.clocked) {
        Err(message) => {
            println!("rejected: {message}");
            ExitCode::from(1)
        }
        Ok(attempts) => {
            for attempt in &attempts {
                let timeout = attempt
                    .timeout_ms
                    .map_or_else(|| "none".to_owned(), |timeout| format!("{timeout} ms"));
                let reason = attempt
                    .reason
                    .as_deref()
                    .map_or_else(String::new, |reason| format!(" ({reason})"));
                println!(
                    "attempt {}: {}{reason}; rlimit {}, timeout {timeout}; used {} units in {} us",
                    attempt.attempt,
                    attempt.result,
                    attempt.rlimit,
                    attempt.rlimit_used,
                    attempt.wall.as_micros()
                );
            }
            let answer = attempts.last().map_or("unknown", |attempt| attempt.result);
            println!("answer: {answer}");
            ExitCode::SUCCESS
        }
    }
}
