//! Cargo-style command-line frontend for the KRS definition compiler.

use krs_cli::{
    Backend, CommandKind, CommandRequest, FacetSelector, KrsCfg, PackageSelector, execute_command,
};
use std::ffi::OsString;
use std::io::{self, Write};
use std::path::PathBuf;

const USAGE: &str = "\
KRS definition compiler

Usage:
  krs <check|expand|emit-k|build> --package PACKAGE --definition NAME [OPTIONS]

Options:
  --manifest-path PATH       Cargo manifest (default: Cargo.toml)
  --package PACKAGE          Root Cargo package name
  --package-id ID            Exact root Cargo package ID
  --definition NAME          Root package definition facet
  --dependency PACKAGE:NAME  Composed dependency facet; repeatable
  --cfg KEY[=VALUE]          KRS rustc cfg; repeatable
  --backend llvm|haskell     Native target dialect (default: llvm)
  --output DIRECTORY         Required for emit-k and build
  -h, --help                 Show this help
";

fn main() {
    match parse(std::env::args_os().skip(1).collect()) {
        Ok(ParseResult::Help) => print!("{USAGE}"),
        Ok(ParseResult::Run(request)) => match execute_command(&request) {
            Ok(outcome) => {
                if let Err(error) = io::stdout().lock().write_all(outcome.stdout()) {
                    eprintln!("krs: could not write stdout: {error}");
                    std::process::exit(1);
                }
            }
            Err(error) => {
                if let Some(diagnostics) = error.diagnostics() {
                    for diagnostic in diagnostics {
                        match diagnostic.to_json_line() {
                            Ok(line) => eprint!("{line}"),
                            Err(render_error) => {
                                eprintln!("krs: could not render diagnostic: {render_error}");
                            }
                        }
                    }
                } else {
                    eprintln!("krs: {error}");
                }
                std::process::exit(1);
            }
        },
        Err(error) => {
            eprintln!("krs: {error}\n\n{USAGE}");
            std::process::exit(2);
        }
    }
}

enum ParseResult {
    Help,
    Run(CommandRequest),
}

fn parse(arguments: Vec<OsString>) -> Result<ParseResult, String> {
    let mut arguments = arguments.into_iter();
    let Some(command) = arguments.next() else {
        return Err("missing command".to_owned());
    };
    if command == "-h" || command == "--help" {
        return Ok(ParseResult::Help);
    }
    let command = match utf8(command, "command")?.as_str() {
        "check" => CommandKind::Check,
        "expand" => CommandKind::Expand,
        "emit-k" => CommandKind::EmitK,
        "build" => CommandKind::Build,
        unknown => return Err(format!("unknown command `{unknown}`")),
    };

    let mut manifest_path = PathBuf::from("Cargo.toml");
    let mut root_package = None;
    let mut definition = None;
    let mut dependencies = Vec::new();
    let mut cfg = Vec::new();
    let mut backend = Backend::Llvm;
    let mut output_directory = None;

    while let Some(option) = arguments.next() {
        if option == "-h" || option == "--help" {
            return Ok(ParseResult::Help);
        }
        let option = utf8(option, "option")?;
        let value = arguments
            .next()
            .ok_or_else(|| format!("{option} requires a value"))?;
        match option.as_str() {
            "--manifest-path" => manifest_path = PathBuf::from(value),
            "--package" => {
                root_package = Some(PackageSelector::Name(utf8(value, "package")?));
            }
            "--package-id" => {
                root_package = Some(PackageSelector::Id(utf8(value, "package ID")?));
            }
            "--definition" => definition = Some(utf8(value, "definition")?),
            "--dependency" => dependencies.push(parse_dependency(value)?),
            "--cfg" => cfg.push(parse_cfg(value)?),
            "--backend" => {
                backend = match utf8(value, "backend")?.as_str() {
                    "llvm" => Backend::Llvm,
                    "haskell" => Backend::Haskell,
                    value => return Err(format!("unknown backend `{value}`")),
                };
            }
            "--output" => output_directory = Some(PathBuf::from(value)),
            _ => return Err(format!("unknown option `{option}`")),
        }
    }

    Ok(ParseResult::Run(CommandRequest {
        command,
        manifest_path,
        root: FacetSelector {
            package: root_package.ok_or("missing --package or --package-id")?,
            definition: definition.ok_or("missing --definition")?,
        },
        dependencies,
        cfg,
        backend,
        output_directory,
    }))
}

fn parse_dependency(value: OsString) -> Result<FacetSelector, String> {
    let value = utf8(value, "dependency")?;
    let (package, definition) = value.rsplit_once(':').ok_or_else(|| {
        format!("dependency `{value}` must have the form CargoPackage:definition")
    })?;
    if package.is_empty() || definition.is_empty() {
        return Err(format!(
            "dependency `{value}` must have non-empty package and definition names"
        ));
    }
    Ok(FacetSelector {
        package: PackageSelector::Name(package.to_owned()),
        definition: definition.to_owned(),
    })
}

fn parse_cfg(value: OsString) -> Result<KrsCfg, String> {
    let value = utf8(value, "cfg")?;
    let (key, value) = value
        .split_once('=')
        .map_or((value.as_str(), None), |(key, value)| {
            (key, Some(value.to_owned()))
        });
    if key.is_empty() {
        return Err("cfg key cannot be empty".to_owned());
    }
    Ok(KrsCfg {
        key: key.to_owned(),
        value,
    })
}

fn utf8(value: OsString, role: &str) -> Result<String, String> {
    value
        .into_string()
        .map_err(|_| format!("{role} is not valid UTF-8"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_complete_build() {
        let ParseResult::Run(request) = parse(
            [
                "build",
                "--package",
                "imp",
                "--definition",
                "main",
                "--dependency",
                "base:core",
                "--backend",
                "haskell",
                "--output",
                "out",
            ]
            .into_iter()
            .map(OsString::from)
            .collect(),
        )
        .unwrap() else {
            panic!("expected command")
        };
        assert_eq!(request.command, CommandKind::Build);
        assert_eq!(request.backend, Backend::Haskell);
        assert_eq!(request.dependencies.len(), 1);
        assert_eq!(request.output_directory, Some(PathBuf::from("out")));
    }

    #[test]
    fn rejects_ambiguous_dependency_spelling() {
        assert!(parse_dependency(OsString::from("base")).is_err());
        assert!(parse_dependency(OsString::from(":core")).is_err());
    }
}
