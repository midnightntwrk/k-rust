//! One-shot native compiler with optional timing output.

use krs_ir::measure::Timings;
use krs_ir_levels::DefinitionIr;
use krs_k_rust::{CompiledArtifacts, ConfigurationContext};
use std::path::{Path, PathBuf};
use std::{error::Error, fs};

/// Compile the emitted Definition IR with the options `krs-exec` uses for every route.
pub(crate) fn compile_ir(
    timings: &mut Timings,
    input: &Path,
) -> Result<(CompiledArtifacts, ConfigurationContext), Box<dyn Error>> {
    let definition_ir = read_ir(timings, input)?;
    krs_exec::compile_definition(&definition_ir, timings)
        .map_err(|error| format!("{error:#?}").into())
}

/// Read Definition IR through the canonical JSON reader.
pub(crate) fn read_ir(timings: &mut Timings, input: &Path) -> Result<DefinitionIr, Box<dyn Error>> {
    timings.try_span("native.input", |_| {
        Ok::<_, Box<dyn Error>>(krs_ir::json::from_slice(&fs::read(input)?)?)
    })
}

fn compile(timings: &mut Timings, input: &Path, output: &Path) -> Result<(), Box<dyn Error>> {
    let (artifacts, _) = compile_ir(timings, input)?;
    timings.try_span("native.write", |_| {
        fs::write(output, artifacts.definition_kore)
    })?;
    Ok(())
}

/// Run the native compiler in a 64 MiB stack worker.
///
/// The timing document is written on both compilation success and failure.
///
/// # Errors
///
/// Returns an error when reading, compiling, or writing fails, or when the worker fails.
pub fn run(
    input: PathBuf,
    output: PathBuf,
    timings_path: Option<PathBuf>,
) -> Result<(), Box<dyn Error>> {
    let result = std::thread::Builder::new()
        .name("krs-native-frontend".into())
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let mut timings = if timings_path.is_some() {
                Timings::enabled()
            } else {
                Timings::disabled()
            };
            let result = compile(&mut timings, &input, &output).map_err(|error| error.to_string());
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
