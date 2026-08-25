use std::{env, error::Error, fs, path::PathBuf};

use k_rust::{
    builtin,
    inner::ProgramParser,
    kast::Sort,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    kore::parser::parse_definition,
    outer::{LoadOptions, ResolvedSource, load_with_options},
};

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn Error>> {
    let mut arguments = env::args_os().skip(1);
    let command = string_argument(arguments.next(), "COMMAND")?;
    let definition_path = PathBuf::from(arguments.next().ok_or("missing DEFINITION")?);
    let module = string_argument(arguments.next(), "MODULE")?;
    let program = arguments.next().map(PathBuf::from);
    if arguments.next().is_some() {
        return Err("expected COMMAND DEFINITION MODULE [PROGRAM]".into());
    }

    let entry = ResolvedSource::new(
        definition_path.display().to_string(),
        fs::read_to_string(&definition_path)?,
    );
    let mut resolver = |_: &str, required: &str| {
        builtin::embedded(required).ok_or_else(|| format!("missing embedded source {required}"))
    };
    let prelude = builtin::embedded("prelude.md").ok_or("missing embedded prelude.md")?;
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
    )
    .map_err(|error| format!("load display: {error}\nload debug: {error:#?}"))?;

    match command.as_str() {
        "load" => {
            let sentence_count = loaded
                .definition
                .modules
                .iter()
                .map(|module| module.local_sentences.len())
                .sum::<usize>();
            println!(
                "loaded {} modules and {sentence_count} local sentences",
                loaded.definition.modules.len()
            );
        }
        "parse" => {
            let program = program.ok_or("parse requires PROGRAM")?;
            let parser = ProgramParser::from_resolved(&loaded.resolved, &module)?;
            let term = parser.parse(&Sort::new("Expr"), &fs::read_to_string(program)?)?;
            println!("{term}");
        }
        "compile" => {
            if program.is_some() {
                return Err("compile does not accept PROGRAM".into());
            }
            let artifacts = compile_loaded_definition(&loaded, CompileOptions::default())?;
            parse_definition(&artifacts.definition_kore)?;
            parse_definition(&artifacts.syntax_definition_kore)?;
            println!(
                "compiled and reparsed KORE: definition={} syntax={} macros={} bytes",
                artifacts.definition_kore.len(),
                artifacts.syntax_definition_kore.len(),
                artifacts.macros_kore.len()
            );
        }
        _ => return Err(format!("unknown command {command:?}").into()),
    }
    Ok(())
}

fn string_argument(
    argument: Option<std::ffi::OsString>,
    name: &str,
) -> Result<String, Box<dyn Error>> {
    argument
        .ok_or_else(|| format!("missing {name}"))?
        .into_string()
        .map_err(|_| format!("{name} is not UTF-8").into())
}
