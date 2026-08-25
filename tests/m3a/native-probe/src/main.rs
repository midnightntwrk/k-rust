use std::{env, error::Error, fs, path::PathBuf};

use k_rust::{
    builtin,
    definition::json as definition_json,
    inner::ProgramParser,
    kast::{Sort, json as kast_json, printer::Printer},
    kompile::CompilationBackend,
    outer::{LoadOptions, ResolvedSource, load_with_options},
};

fn main() {
    if let Err(error) = run() {
        eprintln!("native-expression-probe: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn Error>> {
    let mut arguments = env::args_os().skip(1);
    let command = string_argument(arguments.next(), "COMMAND")?;
    let definition_path = PathBuf::from(arguments.next().ok_or("missing DEFINITION")?);
    let module = string_argument(arguments.next(), "MODULE")?;
    let source = fs::read_to_string(&definition_path)?;
    if command == "source" {
        if arguments.next().is_some() {
            return Err("source expects exactly DEFINITION MODULE".into());
        }
        let parsed = k_rust::outer::parse(definition_path.display().to_string(), &source)?;
        let lowered = k_rust::outer::lower(&parsed, &module)
            .map_err(|diagnostics| format!("outer lowering failed: {diagnostics:?}"))?;
        let serialized = definition_json::to_string_pretty(&lowered)?;
        definition_json::from_str(&serialized)?;
        println!("{serialized}");
        return Ok(());
    }
    let entry = ResolvedSource::new(definition_path.display().to_string(), source);
    let mut resolver = |_: &str, required: &str| {
        builtin::embedded(required).ok_or_else(|| format!("missing embedded source {required}"))
    };
    let prelude = builtin::embedded("prelude.md").ok_or("embedded prelude.md is unavailable")?;
    let loaded = load_with_options(
        entry,
        &module,
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![prelude],
            excluded_module_attributes: vec![
                CompilationBackend::Llvm.excluded_module_attribute().into(),
            ],
            ..LoadOptions::default()
        },
    )?;

    match command.as_str() {
        "resolve" => {
            if arguments.next().is_some() {
                return Err("resolve expects exactly DEFINITION MODULE".into());
            }
            let serialized = definition_json::to_string_pretty(&loaded.definition)?;
            definition_json::from_str(&serialized)?;
            println!("{serialized}");
        }
        "parse" => {
            let program = PathBuf::from(arguments.next().ok_or("missing PROGRAM")?);
            if arguments.next().is_some() {
                return Err("parse expects exactly DEFINITION MODULE PROGRAM".into());
            }
            let parser = ProgramParser::from_resolved(&loaded.resolved, &module)?;
            let term = parser.parse(&Sort::new("Expr"), &fs::read_to_string(program)?)?;
            let serialized = kast_json::to_string_pretty(&term)?;
            kast_json::from_str(&serialized)?;
            println!("{serialized}");
        }
        "roundtrip" => {
            let program = PathBuf::from(arguments.next().ok_or("missing PROGRAM")?);
            if arguments.next().is_some() {
                return Err("roundtrip expects exactly DEFINITION MODULE PROGRAM".into());
            }
            let parser = ProgramParser::from_resolved(&loaded.resolved, &module)?;
            let original = parser.parse(&Sort::new("Expr"), &fs::read_to_string(program)?)?;
            let printed = Printer::new().print_term(&original);
            let reparsed = parser.parse(&Sort::new("Expr"), &printed)?;
            if original != reparsed {
                return Err(format!("native KAST print/parse changed term: {printed}").into());
            }
            println!("{printed}");
        }
        _ => return Err(format!("unknown command {command:?}").into()),
    }
    Ok(())
}

fn string_argument(argument: Option<std::ffi::OsString>, name: &str) -> Result<String, Box<dyn Error>> {
    argument
        .ok_or_else(|| format!("missing {name}"))?
        .into_string()
        .map_err(|_| format!("{name} is not UTF-8").into())
}
