//! Cargo-style command-line frontend for the KRS definition compiler.

use krs_cli::{
    Backend, CommandKind, CommandRequest, FacetSelector, KrsCfg, PackageSelector, execute_command,
};
use krs_fmt::{FormatOptions, TrailingCommentStyle};
use std::ffi::OsString;
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};

const USAGE: &str = "\
KRS definition compiler

Usage:
  krs <check|expand|emit-k|build> --package PACKAGE --definition NAME [OPTIONS]
  krs fmt [--check] [--manifest-path PATH] [PATH ...]
  krs fmt --stdin

Options:
  --manifest-path PATH       Cargo manifest (default: Cargo.toml)
  --package PACKAGE          Root Cargo package name
  --package-id ID            Exact root Cargo package ID
  --definition NAME          Root package definition facet
  --dependency PACKAGE:NAME  Composed dependency facet; repeatable
  --cfg KEY[=VALUE]          KRS rustc cfg; repeatable
  --backend llvm|haskell     Native target dialect (default: llvm)
  --output DIRECTORY         Required for emit-k and build
  --stdin                    Format stdin and write the result to stdout
  --check                    Report files that are not canonically formatted
  --trailing-comments STYLE  aligned or gutter (default: aligned)
  -h, --help                 Show this help
";

fn main() {
    match parse(std::env::args_os().skip(1).collect()) {
        Ok(ParseResult::Help) => print!("{USAGE}"),
        Ok(ParseResult::Format(request)) => match execute_format(&request) {
            Ok(true) => {}
            Ok(false) => std::process::exit(1),
            Err(error) => {
                eprintln!("krs fmt: {error}");
                std::process::exit(1);
            }
        },
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
    Format(FormatRequest),
    Run(CommandRequest),
}

struct FormatRequest {
    stdin: bool,
    check: bool,
    manifest_path: Option<PathBuf>,
    paths: Vec<PathBuf>,
    trailing_comments: TrailingCommentStyle,
}

fn parse(arguments: Vec<OsString>) -> Result<ParseResult, String> {
    let mut arguments = arguments.into_iter();
    let Some(command) = arguments.next() else {
        return Err("missing command".to_owned());
    };
    if command == "-h" || command == "--help" {
        return Ok(ParseResult::Help);
    }
    let command = utf8(command, "command")?;
    if command == "fmt" {
        return parse_format(arguments.collect());
    }
    let command = match command.as_str() {
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

fn parse_format(arguments: Vec<OsString>) -> Result<ParseResult, String> {
    let mut arguments = arguments.into_iter();
    let mut stdin = false;
    let mut check = false;
    let mut manifest_path = None;
    let mut paths = Vec::new();
    let mut trailing_comments = TrailingCommentStyle::AlignedColumn;
    let mut positional_only = false;
    while let Some(argument) = arguments.next() {
        if positional_only {
            paths.push(PathBuf::from(argument));
            continue;
        }
        if argument == "--" {
            positional_only = true;
        } else if argument == "-h" || argument == "--help" {
            return Ok(ParseResult::Help);
        } else if argument == "--stdin" {
            stdin = true;
        } else if argument == "--check" {
            check = true;
        } else if argument == "--manifest-path" {
            let value = arguments.next().ok_or("--manifest-path requires a value")?;
            manifest_path = Some(PathBuf::from(value));
        } else if argument == "--trailing-comments" {
            let value = arguments
                .next()
                .ok_or("--trailing-comments requires a value")?;
            trailing_comments = match utf8(value, "trailing comment style")?.as_str() {
                "aligned" => TrailingCommentStyle::AlignedColumn,
                "gutter" => TrailingCommentStyle::FixedGutter,
                value => return Err(format!("unknown trailing comment style `{value}`")),
            };
        } else if argument.to_string_lossy().starts_with('-') {
            return Err(format!(
                "unknown fmt option `{}`",
                argument.to_string_lossy()
            ));
        } else {
            paths.push(PathBuf::from(argument));
        }
    }
    if stdin && (!paths.is_empty() || manifest_path.is_some()) {
        return Err("--stdin cannot be combined with paths or --manifest-path".to_owned());
    }
    Ok(ParseResult::Format(FormatRequest {
        stdin,
        check,
        manifest_path,
        paths,
        trailing_comments,
    }))
}

fn execute_format(request: &FormatRequest) -> Result<bool, String> {
    let options = FormatOptions {
        trailing_comments: request.trailing_comments,
        ..FormatOptions::default()
    };
    if request.stdin {
        let mut source = String::new();
        io::stdin()
            .read_to_string(&mut source)
            .map_err(|error| format!("cannot read stdin: {error}"))?;
        let output = krs_fmt::format_source(&source, options).map_err(|error| error.to_string())?;
        if request.check {
            if output != source {
                eprint!(
                    "{}",
                    krs_fmt::unified_diff(Path::new("<stdin>"), &source, &output)
                );
                return Ok(false);
            }
        } else {
            io::stdout()
                .lock()
                .write_all(output.as_bytes())
                .map_err(|error| format!("cannot write stdout: {error}"))?;
        }
        return Ok(true);
    }

    let files = if request.paths.is_empty() {
        krs_fmt::discover_rust_files(request.manifest_path.as_deref())
    } else {
        krs_fmt::expand_paths(&request.paths)
    }
    .map_err(|error| error.to_string())?;
    let mut formatted = Vec::with_capacity(files.len());
    let mut failed = false;
    for path in &files {
        match krs_fmt::format_file(path, options) {
            Ok(file) => formatted.push(file),
            Err(error) => {
                eprintln!("{}: {error}", path.display());
                failed = true;
            }
        }
    }
    if failed {
        return Ok(false);
    }
    if request.check {
        let mut changed = false;
        for file in formatted.iter().filter(|file| file.changed) {
            let before = std::fs::read_to_string(&file.path)
                .map_err(|error| format!("cannot reread `{}`: {error}", file.path.display()))?;
            eprint!(
                "{}",
                krs_fmt::unified_diff(&file.path, &before, &file.output)
            );
            changed = true;
        }
        return Ok(!changed);
    }
    for file in formatted.into_iter().filter(|file| file.changed) {
        std::fs::write(&file.path, file.output)
            .map_err(|error| format!("cannot write `{}`: {error}", file.path.display()))?;
    }
    Ok(true)
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

    #[test]
    fn parses_fmt_editor_mode() {
        let ParseResult::Format(request) = parse(
            ["fmt", "--stdin", "--trailing-comments", "gutter"]
                .into_iter()
                .map(OsString::from)
                .collect(),
        )
        .unwrap() else {
            panic!("expected fmt command")
        };
        assert!(request.stdin);
        assert_eq!(request.trailing_comments, TrailingCommentStyle::FixedGutter);
    }

    #[test]
    fn rejects_fmt_stdin_with_paths() {
        assert!(
            parse(
                ["fmt", "--stdin", "src"]
                    .into_iter()
                    .map(OsString::from)
                    .collect()
            )
            .is_err()
        );
    }
}
