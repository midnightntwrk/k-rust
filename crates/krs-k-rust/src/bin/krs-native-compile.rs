//! Compile KRS Definition IR directly through the pinned K-Rust frontend.
//!
//! `--timings FILE` writes a `krs-timings/1` document (see
//! `krs_ir::measure`) on success and on failure.

use krs_ir::DefinitionIr;
use krs_ir::measure::Timings;
use krs_k_rust::{Backend, CompileOptions, compile_definition_timed};
use std::path::PathBuf;
use std::{env, error::Error, fs};

const USAGE: &str = "usage: krs-native-compile [--timings FILE] DEFINITION-IR OUTPUT-KORE";

fn run(timings: &mut Timings, input: PathBuf, output: PathBuf) -> Result<(), Box<dyn Error>> {
    let definition_ir: DefinitionIr = timings.try_span("native.input", |_| {
        Ok::<_, Box<dyn Error>>(serde_json::from_slice(&fs::read(input)?)?)
    })?;
    let artifacts = compile_definition_timed(
        &definition_ir,
        CompileOptions {
            backend: Backend::Haskell,
            ..CompileOptions::default()
        },
        timings,
    )
    .map_err(|error| format!("{error:#?}"))?;
    timings.try_span("native.write", |_| {
        fs::write(output, artifacts.definition_kore)
    })?;
    Ok(())
}

fn parse() -> Result<(Option<PathBuf>, PathBuf, PathBuf), Box<dyn Error>> {
    let mut timings = None;
    let mut positional = Vec::new();
    let mut arguments = env::args_os().skip(1);
    while let Some(argument) = arguments.next() {
        if argument == "--timings" {
            timings = Some(PathBuf::from(arguments.next().ok_or(USAGE)?));
        } else {
            positional.push(PathBuf::from(argument));
        }
    }
    let [input, output]: [PathBuf; 2] = positional.try_into().map_err(|_| USAGE)?;
    Ok((timings, input, output))
}

fn main() -> Result<(), Box<dyn Error>> {
    let (timings_path, input, output) = parse()?;
    let result = std::thread::Builder::new()
        .name("krs-native-frontend".into())
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let mut timings = if timings_path.is_some() {
                Timings::enabled()
            } else {
                Timings::disabled()
            };
            let result = run(&mut timings, input, output).map_err(|error| error.to_string());
            let document = timings_path.map(|path| {
                let document = timings.document("native-compile", result.is_ok());
                (path, document)
            });
            (result, document)
        })?
        .join()
        .map_err(|_| "native frontend thread panicked")?;
    let (result, document) = result;
    if let Some((path, document)) = document {
        fs::write(&path, serde_json::to_vec_pretty(&document)?)
            .map_err(|error| format!("could not write `{}`: {error}", path.display()))?;
    }
    result.map_err(Into::into)
}
