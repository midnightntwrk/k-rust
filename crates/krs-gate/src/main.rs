//! Command-line entry point for the native gate.

use std::{env, error::Error, path::PathBuf};

const USAGE: &str = "usage:
  krs-gate compile [--timings FILE] DEFINITION-IR OUTPUT-KORE
  krs-gate session
  krs-gate kore-compare REFERENCE NATIVE MODULE [--label FROM=CANONICAL]... [--reference-claims PATH MODULE]
  krs-gate proof split DEFINITION OUTPUT-DIR MODULE SPEC-MODULE LABEL...
  krs-gate proof classify RESULT
  krs-gate proof assert-spec SPEC SPEC-MODULE MODULE LABEL
  krs-gate proof compare-patterns LEFT RIGHT";

fn run() -> Result<(), Box<dyn Error>> {
    let mut arguments = env::args_os().skip(1);
    match arguments.next().as_deref() {
        Some(command) if command == "compile" => {
            let mut timings = None;
            let mut positional = Vec::new();
            while let Some(argument) = arguments.next() {
                if argument == "--timings" {
                    timings = Some(PathBuf::from(arguments.next().ok_or(USAGE)?));
                } else {
                    positional.push(PathBuf::from(argument));
                }
            }
            let [input, output]: [PathBuf; 2] = positional.try_into().map_err(|_| USAGE)?;
            krs_gate::compile::run(input, output, timings)
        }
        Some(command) if command == "session" && arguments.next().is_none() => {
            krs_gate::session::run()
        }
        Some(command) if command == "kore-compare" => {
            krs_gate::kore_compare::run(env::args().skip(2))
        }
        Some(command) if command == "proof" => krs_gate::proof::run(arguments),
        _ => Err(USAGE.into()),
    }
}

fn main() {
    if let Err(error) = run() {
        let prefix = match env::args_os().nth(1).as_deref() {
            Some(command) if command == "kore-compare" => "krs-imp-native-comparator",
            Some(command) if command == "proof" => "krs-imp-proof-support",
            _ => "Error",
        };
        eprintln!("{prefix}: {error}");
        std::process::exit(1);
    }
}
