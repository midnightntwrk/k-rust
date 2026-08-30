//! Compile KRS Definition IR directly through the pinned K-Rust frontend.

use krs_ir::DefinitionIr;
use krs_k_rust::{Backend, CompileOptions, compile_definition};
use std::{env, error::Error, fs};

fn run() -> Result<(), Box<dyn Error>> {
    let mut arguments = env::args_os().skip(1);
    let definition_ir_path = arguments
        .next()
        .ok_or("usage: krs-native-compile DEFINITION-IR OUTPUT-KORE")?;
    let output_path = arguments
        .next()
        .ok_or("usage: krs-native-compile DEFINITION-IR OUTPUT-KORE")?;
    if arguments.next().is_some() {
        return Err("usage: krs-native-compile DEFINITION-IR OUTPUT-KORE".into());
    }
    let definition_ir: DefinitionIr = serde_json::from_slice(&fs::read(definition_ir_path)?)?;
    let artifacts = compile_definition(
        &definition_ir,
        CompileOptions {
            backend: Backend::Haskell,
            ..CompileOptions::default()
        },
    )
    .map_err(|error| format!("{error:#?}"))?;
    fs::write(output_path, artifacts.definition_kore)?;
    Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
    let result = std::thread::Builder::new()
        .name("krs-native-frontend".into())
        .stack_size(64 * 1024 * 1024)
        .spawn(|| run().map_err(|error| error.to_string()))?
        .join()
        .map_err(|_| "native frontend thread panicked")?;
    result.map_err(Into::into)
}
