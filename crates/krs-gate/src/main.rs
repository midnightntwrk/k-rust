//! Command-line entry point for the native gate.

use std::{env, error::Error, path::PathBuf};

const USAGE: &str =
    "usage: krs-gate compile [--timings FILE] DEFINITION-IR OUTPUT-KORE | krs-gate session";

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
        _ => Err(USAGE.into()),
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    run()
}
