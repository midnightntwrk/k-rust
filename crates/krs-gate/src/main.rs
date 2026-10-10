//! Command-line entry point for the native gate.

use std::{env, error::Error, path::PathBuf};

const USAGE: &str = "usage:
  krs-gate compile [--timings FILE] DEFINITION-IR OUTPUT-KORE
  krs-gate collector-bundle COLLECTOR-STDOUT DESCRIPTOR-BUNDLE
  krs-gate session
  krs-gate kore-compare REFERENCE NATIVE MODULE [--label FROM=CANONICAL]... [--reference-claims PATH MODULE]
  krs-gate kore-canonicalize INPUT OUTPUT
  krs-gate proof split DEFINITION OUTPUT-DIR MODULE SPEC-MODULE LABEL...
  krs-gate proof classify RESULT
  krs-gate proof assert-spec SPEC SPEC-MODULE MODULE LABEL
  krs-gate proof compare-patterns LEFT RIGHT";

fn run() -> Result<(), Box<dyn Error>> {
    let mut arguments = env::args_os().skip(1);
    match arguments.next().as_deref() {
        Some(command) if command == "collector-bundle" => {
            let collector = PathBuf::from(arguments.next().ok_or(USAGE)?);
            let descriptor_bundle = PathBuf::from(arguments.next().ok_or(USAGE)?);
            if arguments.next().is_some() {
                return Err(USAGE.into());
            }
            let summary = krs_gate::collector_bundle::run(&collector, &descriptor_bundle)?;
            println!("{}", serde_json::to_string(&summary)?);
            Ok(())
        }
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
        Some(command) if command == "kore-compare" => krs_gate::kore_compare::run(arguments),
        Some(command) if command == "kore-canonicalize" => {
            krs_gate::kore_compare::run_canonicalize(arguments)
        }
        Some(command) if command == "proof" => krs_gate::proof::run(arguments),
        _ => Err(USAGE.into()),
    }
}

fn main() {
    if let Err(error) = run() {
        let prefix = match env::args_os().nth(1).as_deref() {
            Some(command) if command == "collector-bundle" => "krs-gate collector-bundle",
            Some(command) if command == "kore-compare" => "krs-gate kore-compare",
            Some(command) if command == "kore-canonicalize" => "krs-gate kore-canonicalize",
            Some(command) if command == "proof" => "krs-gate proof",
            _ => "Error",
        };
        eprintln!("{prefix}: {error}");
        std::process::exit(1);
    }
}
