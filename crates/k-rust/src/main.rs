use std::{
    env,
    error::Error,
    ffi::OsString,
    fs,
    io::{self, Read},
    path::{Path, PathBuf},
};

use k_rust::{
    definition::checks::check_definition,
    diagnostic::{Diagnostic, Severity},
    inner::ProgramParser,
    kast::{json as kast_json, parser::parse_sort, printer::Printer as KastPrinter},
    kompile::module_to_kore_from_resolved,
    kore::{
        ast::{Attributes, Definition as KoreDefinition},
        printer::Printer as KorePrinter,
    },
    native::FileResolver,
    outer::load,
};

const HELP: &str = "\
Rust frontend for the K Framework

Usage:
  krust kcompile <definition.k> --main-module <MODULE> [--output-directory <DIR>] [-I <DIR>]...
  krust kast <definition.k> --module <MODULE> --sort <SORT> [<program-file> | -e <PROGRAM>] [-I <DIR>]... [--output text|json]
  krust help
";

fn main() {
    if let Err(error) = run(env::args_os().skip(1).collect()) {
        eprintln!("error: {error}");
        std::process::exit(1);
    }
}

fn run(arguments: Vec<OsString>) -> Result<(), Box<dyn Error>> {
    let mut arguments = arguments.into_iter();
    let Some(command) = arguments.next() else {
        print!("{HELP}");
        return Ok(());
    };
    let rest = arguments.collect::<Vec<_>>();
    match command.to_string_lossy().as_ref() {
        "kcompile" => kcompile(parse_kcompile(rest)?),
        "kast" => kast(parse_kast(rest)?),
        "help" | "--help" | "-h" => {
            print!("{HELP}");
            Ok(())
        }
        command => Err(format!("unknown command {command:?}\n\n{HELP}").into()),
    }
}

#[derive(Debug)]
struct CommonOptions {
    definition: PathBuf,
    module: String,
    includes: Vec<PathBuf>,
}

#[derive(Debug)]
struct KcompileOptions {
    common: CommonOptions,
    output_directory: PathBuf,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum OutputFormat {
    Text,
    Json,
}

#[derive(Debug)]
struct KastOptions {
    common: CommonOptions,
    sort: String,
    expression: Option<String>,
    program_file: Option<PathBuf>,
    output: OutputFormat,
}

fn parse_kcompile(arguments: Vec<OsString>) -> Result<KcompileOptions, Box<dyn Error>> {
    let mut parser = Arguments::new(arguments);
    let module = parser.required_value(&["-m", "--main-module"])?;
    let output_directory = parser
        .value(&["-o", "--output-directory"])?
        .map_or_else(|| PathBuf::from("."), PathBuf::from);
    let includes = parser.repeated_paths(&["-I", "--include"])?;
    let definition = parser.positional("definition file")?;
    parser.finish()?;
    Ok(KcompileOptions {
        common: CommonOptions {
            definition: definition.into(),
            module,
            includes,
        },
        output_directory,
    })
}

fn parse_kast(arguments: Vec<OsString>) -> Result<KastOptions, Box<dyn Error>> {
    let mut parser = Arguments::new(arguments);
    let module = parser.required_value(&["-m", "--module"])?;
    let sort = parser.required_value(&["-s", "--sort"])?;
    let expression = parser.value(&["-e", "--expression"])?;
    let output = match parser.value(&["-o", "--output"])?.as_deref() {
        None | Some("text") => OutputFormat::Text,
        Some("json") => OutputFormat::Json,
        Some(value) => return Err(format!("unsupported output format {value:?}").into()),
    };
    let includes = parser.repeated_paths(&["-I", "--include"])?;
    let definition = parser.positional("definition file")?;
    let program_file = parser.optional_positional().map(PathBuf::from);
    parser.finish()?;
    if expression.is_some() && program_file.is_some() {
        return Err("a program file and --expression cannot be used together".into());
    }
    Ok(KastOptions {
        common: CommonOptions {
            definition: definition.into(),
            module,
            includes,
        },
        sort,
        expression,
        program_file,
        output,
    })
}

fn load_definition(
    options: &CommonOptions,
) -> Result<k_rust::outer::LoadedDefinition, Box<dyn Error>> {
    let mut resolver = FileResolver::from_current_directory(options.includes.clone())?;
    let entry = resolver.load_entry(&options.definition)?;
    let loaded = load(entry, &options.module, &mut resolver)?;
    let diagnostics = check_definition(&loaded.resolved)?;
    emit_diagnostics(&diagnostics);
    if diagnostics
        .iter()
        .any(|diagnostic| diagnostic.severity == Severity::Error)
    {
        return Err("definition checks failed".into());
    }
    Ok(loaded)
}

fn kcompile(options: KcompileOptions) -> Result<(), Box<dyn Error>> {
    let loaded = load_definition(&options.common)?;
    let generated = module_to_kore_from_resolved(&loaded.resolved, &options.common.module)?;
    fs::create_dir_all(&options.output_directory)?;
    let printer = KorePrinter::pretty(100);
    let semantics = KoreDefinition {
        attributes: Attributes::default(),
        modules: vec![generated.semantics],
    };
    let syntax = KoreDefinition {
        attributes: Attributes::default(),
        modules: vec![generated.syntax],
    };
    fs::write(
        options.output_directory.join("definition.kore"),
        with_newline(printer.print_definition(&semantics)),
    )?;
    fs::write(
        options.output_directory.join("syntaxDefinition.kore"),
        with_newline(printer.print_definition(&syntax)),
    )?;
    let macros = generated
        .macros
        .iter()
        .map(|sentence| printer.print_sentence(sentence))
        .collect::<Vec<_>>()
        .join("\n");
    fs::write(
        options.output_directory.join("macros.kore"),
        with_newline(macros),
    )?;
    Ok(())
}

fn kast(options: KastOptions) -> Result<(), Box<dyn Error>> {
    let loaded = load_definition(&options.common)?;
    let source = match (options.expression, options.program_file) {
        (Some(source), None) => source,
        (None, Some(path)) if path == Path::new("-") => read_stdin()?,
        (None, Some(path)) => fs::read_to_string(path)?,
        (None, None) => read_stdin()?,
        (Some(_), Some(_)) => unreachable!(),
    };
    let sort = parse_sort(&options.sort)?;
    let parser = ProgramParser::from_resolved(&loaded.resolved, &options.common.module)?;
    let term = parser.parse(&sort, &source)?;
    match options.output {
        OutputFormat::Text => println!("{}", KastPrinter::new().print_term(&term)),
        OutputFormat::Json => println!("{}", kast_json::to_string_pretty(&term)?),
    }
    Ok(())
}

fn read_stdin() -> io::Result<String> {
    let mut source = String::new();
    io::stdin().read_to_string(&mut source)?;
    Ok(source)
}

fn with_newline(mut text: String) -> String {
    if !text.ends_with('\n') {
        text.push('\n');
    }
    text
}

fn emit_diagnostics(diagnostics: &[Diagnostic]) {
    for diagnostic in diagnostics {
        let location = match (&diagnostic.source, diagnostic.location) {
            (Some(source), Some(location)) => format!(
                "{source}:{}:{}: ",
                location.start_line, location.start_column
            ),
            (Some(source), None) => format!("{source}: "),
            _ => String::new(),
        };
        eprintln!(
            "{location}{:?}[{:?}]: {}",
            diagnostic.severity, diagnostic.code, diagnostic.message
        );
    }
}

struct Arguments {
    values: Vec<OsString>,
    used: Vec<bool>,
}

impl Arguments {
    fn new(values: Vec<OsString>) -> Self {
        let used = vec![false; values.len()];
        Self { values, used }
    }

    fn value(&mut self, names: &[&str]) -> Result<Option<String>, Box<dyn Error>> {
        for index in 0..self.values.len() {
            if self.used[index] || !names.iter().any(|name| self.values[index] == *name) {
                continue;
            }
            self.used[index] = true;
            let value_index = index + 1;
            if value_index >= self.values.len() || self.used[value_index] {
                return Err(format!("{} requires a value", names.last().unwrap()).into());
            }
            self.used[value_index] = true;
            return Ok(Some(
                self.values[value_index].to_string_lossy().into_owned(),
            ));
        }
        Ok(None)
    }

    fn required_value(&mut self, names: &[&str]) -> Result<String, Box<dyn Error>> {
        self.value(names)?
            .ok_or_else(|| format!("{} is required", names.last().unwrap()).into())
    }

    fn repeated_paths(&mut self, names: &[&str]) -> Result<Vec<PathBuf>, Box<dyn Error>> {
        let mut paths = Vec::new();
        while let Some(path) = self.value(names)? {
            paths.push(path.into());
        }
        Ok(paths)
    }

    fn positional(&mut self, name: &str) -> Result<OsString, Box<dyn Error>> {
        self.optional_positional()
            .ok_or_else(|| format!("{name} is required").into())
    }

    fn optional_positional(&mut self) -> Option<OsString> {
        let index = self.values.iter().enumerate().position(|(index, value)| {
            !self.used[index] && (!value.to_string_lossy().starts_with('-') || value == "-")
        })?;
        self.used[index] = true;
        Some(self.values[index].clone())
    }

    fn finish(&self) -> Result<(), Box<dyn Error>> {
        let unexpected = self
            .values
            .iter()
            .zip(&self.used)
            .filter(|(_, used)| !*used)
            .map(|(value, _)| value.to_string_lossy())
            .collect::<Vec<_>>();
        if unexpected.is_empty() {
            Ok(())
        } else {
            Err(format!("unexpected arguments: {}", unexpected.join(" ")).into())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_kast_options_in_any_order() {
        let options = parse_kast(
            [
                "--sort",
                "Exp",
                "definition.k",
                "-I",
                "builtins",
                "--module",
                "MAIN",
                "-e",
                "1 + 2",
                "--output",
                "json",
            ]
            .into_iter()
            .map(OsString::from)
            .collect(),
        )
        .unwrap();
        assert_eq!(options.common.definition, Path::new("definition.k"));
        assert_eq!(options.common.module, "MAIN");
        assert_eq!(options.common.includes, [PathBuf::from("builtins")]);
        assert_eq!(options.sort, "Exp");
        assert_eq!(options.expression.as_deref(), Some("1 + 2"));
        assert_eq!(options.output, OutputFormat::Json);
    }
}
