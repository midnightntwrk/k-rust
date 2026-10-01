//! Cargo-style command-line frontend for the KRS definition compiler.

use krs_cli::{
    Backend, Command, CommandKind, CommandRequest, DiagnosticSources, FacetSelector, KrsCfg,
    MessageFormat, PackageSelector, RegistrationMode, execute_command_reported,
    valid_identifier_segment,
};
use krs_diagnostic::ToDiagnostic;
use krs_fmt::{Edition, FormatOptions, TrailingCommentStyle};
use krs_ir::measure::Measurement;
use lexopt::Arg::{Long, Short, Value};
use std::ffi::OsString;
use std::fmt;
use std::io::{self, IsTerminal, Read, Write};
use std::path::{Path, PathBuf};

const USAGE: &str = "\
KRS definition compiler

Usage:
  krs <check|expand|emit-k|build> --package PACKAGE --definition NAME [OPTIONS]
  krs fmt [--check] [--manifest-path PATH] [PATH ...]
  krs fmt --stdin [--edition YEAR]

Commands:
  check                     Build and run the collector; report Rust and theory errors
  expand                    Render the selected Rust reference surface
  emit-k                    Emit canonical K and shared artifacts
  build                     Compile native backend artifacts

Options:
  --manifest-path PATH       Cargo manifest (default: Cargo.toml)
  --package PACKAGE          Root Cargo package name
  --package-id ID            Exact root Cargo package ID
  --definition NAME          Root package definition facet
  --dependency PACKAGE:NAME  Composed dependency facet; repeatable
  --cfg KEY[=VALUE]          KRS rustc cfg; repeatable
  --backend llvm|haskell     Native target dialect (default: llvm)
  --output DIRECTORY         Required for emit-k and build
  --timings FILE             Write krs-timings/1 phase timings as JSON
  --counters FILE            Write krs-counters/1 work counters as JSON
  --message-format human|json Diagnostic output (default: human)
  --no-reuse                 Run the collector and compiler even on an unchanged input
  --stdin                    Format stdin and write the result to stdout
  --edition YEAR             Rust edition for --stdin (default: 2024)
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
        Ok(ParseResult::Run(request, measure)) => {
            let mut measurement =
                Measurement::new(measure.timings.is_some(), measure.counters.is_some());
            let (result, sources) = execute_command_reported(&request, &mut measurement);
            let measured = write_measurement(
                &measure,
                &measurement,
                request.command.kind(),
                result.is_ok(),
            );
            if !report_outcome(result, request.message_format, &sources) || !measured {
                std::process::exit(1);
            }
        }
        Err(error) => {
            eprintln!("krs: {error}\n\n{USAGE}");
            std::process::exit(2);
        }
    }
}

/// Measurement output paths requested on the command line.
#[derive(Default)]
struct MeasureOptions {
    timings: Option<PathBuf>,
    counters: Option<PathBuf>,
}

fn write_measurement(
    options: &MeasureOptions,
    measurement: &Measurement,
    command: CommandKind,
    succeeded: bool,
) -> bool {
    let mut ok = true;
    let mut write = |path: &Path, bytes: serde_json::Result<Vec<u8>>| {
        let result = bytes
            .map_err(|error| error.to_string())
            .and_then(|mut bytes| {
                bytes.push(b'\n');
                std::fs::write(path, bytes).map_err(|error| error.to_string())
            });
        if let Err(error) = result {
            eprintln!("krs: could not write `{}`: {error}", path.display());
            ok = false;
        }
    };
    if let Some(path) = &options.timings {
        let document = measurement.timings.document(command.as_str(), succeeded);
        write(path, serde_json::to_vec_pretty(&document));
    }
    if let Some(path) = &options.counters {
        let document = measurement.counters.document(command.as_str(), succeeded);
        write(path, serde_json::to_vec_pretty(&document));
    }
    ok
}

/// Print a command outcome; false when the command or stdout failed.
fn report_outcome(
    result: Result<krs_cli::CommandOutcome, krs_cli::CommandError>,
    format: MessageFormat,
    sources: &DiagnosticSources,
) -> bool {
    match result {
        Ok(outcome) => {
            report_diagnostics(
                &outcome.warnings().envelopes,
                &outcome.warnings().unlocated,
                format,
                sources,
            );
            if let Err(error) = io::stdout().lock().write_all(outcome.stdout()) {
                eprintln!("krs: could not write stdout: {error}");
                return false;
            }
            true
        }
        Err(error) => {
            if let Some(diagnostics) = error.diagnostics() {
                report_diagnostics(
                    &diagnostics,
                    &error.unlocated_diagnostics(),
                    format,
                    sources,
                );
            } else {
                eprintln!("krs: {error}");
            }
            false
        }
    }
}

fn report_diagnostics(
    envelopes: &[krs_cli::DiagnosticEnvelope],
    unlocated: &[krs_cli::UnlocatedDiagnostic],
    format: MessageFormat,
    sources: &DiagnosticSources,
) {
    let color = io::stderr().is_terminal() && std::env::var_os("NO_COLOR").is_none();
    if let Err(error) = write_diagnostics(
        &mut io::stderr().lock(),
        envelopes,
        unlocated,
        format,
        sources,
        color,
    ) {
        eprintln!("krs: could not render diagnostic: {error}");
    }
}

fn write_diagnostics(
    writer: &mut impl Write,
    envelopes: &[krs_cli::DiagnosticEnvelope],
    unlocated: &[krs_cli::UnlocatedDiagnostic],
    format: MessageFormat,
    sources: &DiagnosticSources,
    color: bool,
) -> io::Result<()> {
    for diagnostic in envelopes {
        match format {
            MessageFormat::Json => writer.write_all(diagnostic.to_json_line()?.as_bytes())?,
            MessageFormat::Human => {
                writeln!(writer, "{}", sources.render_envelope(diagnostic, color))?;
            }
        }
    }
    for diagnostic in unlocated {
        match format {
            MessageFormat::Json => writeln!(writer, "krs: {diagnostic}")?,
            MessageFormat::Human => writeln!(
                writer,
                "{}",
                sources.render_diagnostic(&diagnostic.to_diagnostic(), color)
            )?,
        }
    }
    Ok(())
}

enum ParseResult {
    Help,
    Format(FormatRequest),
    Run(CommandRequest, MeasureOptions),
}

struct FormatRequest {
    stdin: bool,
    edition: Edition,
    check: bool,
    manifest_path: Option<PathBuf>,
    paths: Vec<PathBuf>,
    trailing_comments: TrailingCommentStyle,
}

#[derive(Default)]
struct RunOptions {
    manifest_path: Option<PathBuf>,
    package: Option<String>,
    package_id: Option<String>,
    definition: Option<String>,
    dependencies: Vec<FacetSelector>,
    cfg: Vec<KrsCfg>,
    backend: Option<Backend>,
    output: Option<PathBuf>,
    registration: Option<RegistrationMode>,
    no_reuse: bool,
    message_format: Option<MessageFormat>,
    measure: MeasureOptions,
}

#[derive(Debug)]
enum UsageError {
    Argument(lexopt::Error),
    Message(String),
}

impl fmt::Display for UsageError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Argument(error) => error.fmt(formatter),
            Self::Message(message) => message.fmt(formatter),
        }
    }
}

impl From<lexopt::Error> for UsageError {
    fn from(error: lexopt::Error) -> Self {
        Self::Argument(error)
    }
}

fn usage(message: impl Into<String>) -> UsageError {
    UsageError::Message(message.into())
}

fn set_once<T>(slot: &mut Option<T>, value: T, option: &str) -> Result<(), UsageError> {
    if slot.replace(value).is_some() {
        return Err(usage(format!("{option} specified more than once")));
    }
    Ok(())
}

fn option_value(parser: &mut lexopt::Parser, role: &str) -> Result<String, UsageError> {
    utf8(parser.value()?, role)
}

fn parse(arguments: Vec<OsString>) -> Result<ParseResult, UsageError> {
    let mut parser = lexopt::Parser::from_args(arguments);
    let command = match parser.next()? {
        Some(Short('h') | Long("help")) => return Ok(ParseResult::Help),
        Some(Value(value)) => utf8(value, "command")?,
        Some(argument) => return Err(argument.unexpected().into()),
        None => return Err(usage("missing command")),
    };
    if command == "fmt" {
        return parse_format(&mut parser);
    }
    let kind = match command.as_str() {
        "check" => CommandKind::Check,
        "expand" => CommandKind::Expand,
        "emit-k" => CommandKind::EmitK,
        "build" => CommandKind::Build,
        unknown => return Err(usage(format!("unknown command `{unknown}`"))),
    };
    parse_run(&mut parser, kind)
}

fn parse_run(parser: &mut lexopt::Parser, kind: CommandKind) -> Result<ParseResult, UsageError> {
    let mut options = RunOptions::default();
    while let Some(argument) = parser.next()? {
        match argument {
            Short('h') | Long("help") => return Ok(ParseResult::Help),
            Long("no-reuse") => options.no_reuse = true,
            Long("message-format") => {
                let value = option_value(parser, "message format")?;
                let selected = match value.as_str() {
                    "human" => MessageFormat::Human,
                    "json" => MessageFormat::Json,
                    _ => return Err(usage(format!("unknown message format `{value}`"))),
                };
                set_once(&mut options.message_format, selected, "--message-format")?;
            }
            Long("manifest-path") => set_once(
                &mut options.manifest_path,
                PathBuf::from(option_value(parser, "manifest path")?),
                "--manifest-path",
            )?,
            Long("package") => set_once(
                &mut options.package,
                option_value(parser, "package")?,
                "--package",
            )?,
            Long("package-id") => set_once(
                &mut options.package_id,
                option_value(parser, "package ID")?,
                "--package-id",
            )?,
            Long("definition") => set_once(
                &mut options.definition,
                option_value(parser, "definition")?,
                "--definition",
            )?,
            Long("dependency") => options
                .dependencies
                .push(parse_dependency(parser.value()?)?),
            Long("cfg") => options.cfg.push(parse_cfg(parser.value()?)?),
            Long("backend") => {
                let value = option_value(parser, "backend")?;
                let selected = Backend::ALL
                    .into_iter()
                    .find(|backend| backend.as_str() == value)
                    .ok_or_else(|| usage(format!("unknown backend `{value}`")))?;
                set_once(&mut options.backend, selected, "--backend")?;
            }
            Long("output") => set_once(
                &mut options.output,
                PathBuf::from(option_value(parser, "output")?),
                "--output",
            )?,
            Long("timings") => set_once(
                &mut options.measure.timings,
                PathBuf::from(option_value(parser, "timings")?),
                "--timings",
            )?,
            Long("counters") => set_once(
                &mut options.measure.counters,
                PathBuf::from(option_value(parser, "counters")?),
                "--counters",
            )?,
            Long("registration") => {
                let value = option_value(parser, "registration")?;
                let selected = match value.as_str() {
                    "inventory" => RegistrationMode::Inventory,
                    "explicit" => RegistrationMode::Explicit,
                    _ => return Err(usage(format!("unknown registration mode `{value}`"))),
                };
                set_once(&mut options.registration, selected, "--registration")?;
            }
            _ => return Err(argument.unexpected().into()),
        }
    }
    finish_run(kind, options)
}

fn finish_run(kind: CommandKind, options: RunOptions) -> Result<ParseResult, UsageError> {
    let RunOptions {
        manifest_path,
        package,
        package_id,
        definition,
        dependencies,
        cfg,
        backend,
        output,
        registration,
        no_reuse,
        message_format,
        measure,
    } = options;
    if package.is_some() && package_id.is_some() {
        return Err(usage("--package and --package-id cannot be combined"));
    }
    let root = FacetSelector {
        package: match (package, package_id) {
            (Some(name), None) => PackageSelector::Name(name),
            (None, Some(id)) => PackageSelector::Id(id),
            _ => return Err(usage("missing --package or --package-id")),
        },
        definition: definition.ok_or_else(|| usage("missing --definition"))?,
    };
    let command = match kind {
        CommandKind::Check | CommandKind::Expand if output.is_some() => {
            return Err(usage(format!(
                "--output does not apply to {}",
                kind.as_str()
            )));
        }
        CommandKind::Check => Command::Check {
            backend: backend.unwrap_or(Backend::Llvm),
        },
        CommandKind::Expand => Command::Expand,
        CommandKind::EmitK => Command::EmitK {
            output: output.ok_or_else(|| usage("missing --output"))?,
        },
        CommandKind::Build => Command::Build {
            backend: backend.unwrap_or(Backend::Llvm),
            output: output.ok_or_else(|| usage("missing --output"))?,
        },
    };
    Ok(ParseResult::Run(
        CommandRequest {
            command,
            manifest_path: manifest_path.unwrap_or_else(|| PathBuf::from("Cargo.toml")),
            root,
            dependencies,
            cfg,
            registration: registration.unwrap_or(RegistrationMode::Inventory),
            no_reuse,
            message_format: message_format.unwrap_or_default(),
        },
        measure,
    ))
}

fn parse_format(parser: &mut lexopt::Parser) -> Result<ParseResult, UsageError> {
    let mut stdin = false;
    let mut edition = None;
    let mut check = false;
    let mut manifest_path = None;
    let mut paths = Vec::new();
    let mut trailing_comments = None;
    while let Some(argument) = parser.next()? {
        match argument {
            Short('h') | Long("help") => return Ok(ParseResult::Help),
            Long("stdin") => stdin = true,
            Long("edition") => {
                let value = option_value(parser, "Rust edition")?;
                set_once(
                    &mut edition,
                    value.parse::<Edition>().map_err(usage)?,
                    "--edition",
                )?;
            }
            Long("check") => check = true,
            Long("manifest-path") => set_once(
                &mut manifest_path,
                PathBuf::from(option_value(parser, "manifest path")?),
                "--manifest-path",
            )?,
            Long("trailing-comments") => {
                let value = option_value(parser, "trailing comment style")?;
                let selected = match value.as_str() {
                    "aligned" => TrailingCommentStyle::AlignedColumn,
                    "gutter" => TrailingCommentStyle::FixedGutter,
                    _ => return Err(usage(format!("unknown trailing comment style `{value}`"))),
                };
                set_once(&mut trailing_comments, selected, "--trailing-comments")?;
            }
            Value(path) => paths.push(PathBuf::from(path)),
            _ => return Err(argument.unexpected().into()),
        }
    }
    if stdin && (!paths.is_empty() || manifest_path.is_some()) {
        return Err(usage(
            "--stdin cannot be combined with paths or --manifest-path",
        ));
    }
    if edition.is_some() && !stdin {
        return Err(usage("--edition requires --stdin"));
    }
    Ok(ParseResult::Format(FormatRequest {
        stdin,
        edition: edition.unwrap_or_default(),
        check,
        manifest_path,
        paths,
        trailing_comments: trailing_comments.unwrap_or(TrailingCommentStyle::AlignedColumn),
    }))
}

fn execute_format(request: &FormatRequest) -> Result<bool, String> {
    let options = FormatOptions {
        trailing_comments: request.trailing_comments,
        edition: request.edition,
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

    let files = krs_cli::discover_format_inputs(request.manifest_path.as_deref(), &request.paths)?;
    let mut formatted = Vec::with_capacity(files.len());
    let mut failed = false;
    for input in &files {
        match krs_fmt::format_file(
            &input.path,
            FormatOptions {
                edition: input.edition,
                ..options
            },
        ) {
            Ok(file) => formatted.push(file),
            Err(error) => {
                eprintln!("{}: {error}", input.path.display());
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

fn parse_dependency(value: OsString) -> Result<FacetSelector, UsageError> {
    let value = utf8(value, "dependency")?;
    let (package, definition) = value.rsplit_once(':').ok_or_else(|| {
        usage(format!(
            "dependency `{value}` must have the form CargoPackage:definition"
        ))
    })?;
    if package.is_empty() || definition.is_empty() {
        return Err(usage(format!(
            "dependency `{value}` must have non-empty package and definition names"
        )));
    }
    Ok(FacetSelector {
        package: PackageSelector::Name(package.to_owned()),
        definition: definition.to_owned(),
    })
}

fn parse_cfg(value: OsString) -> Result<KrsCfg, UsageError> {
    let value = utf8(value, "cfg")?;
    let (key, value) = value
        .split_once('=')
        .map_or((value.as_str(), None), |(key, value)| {
            (key, Some(value.to_owned()))
        });
    if !valid_identifier_segment(key) {
        return Err(usage(format!("invalid cfg key `{key}`")));
    }
    Ok(KrsCfg {
        key: key.to_owned(),
        value,
    })
}

fn utf8(value: OsString, role: &str) -> Result<String, UsageError> {
    value
        .into_string()
        .map_err(|_| usage(format!("{role} is not valid UTF-8")))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reports_envelopes_and_unlocated_errors_and_warnings_together() {
        let package = krs_ir::PackageId::new("diag", "diag", "0.1.0", "workspace").unwrap();
        let file = krs_ir::SourceFileId::new(
            package,
            "src/lib.rs",
            krs_ir::Sha256Digest::new("11".repeat(32)).unwrap(),
        )
        .unwrap();
        let mut envelope = krs_cli::DiagnosticEnvelope::error(
            krs_cli::DiagnosticStage::Native,
            "UnusedVariable",
            "unused variable",
            krs_ir::SourceRange::new(file, 7, 16).unwrap(),
        );
        envelope.severity = krs_cli::DiagnosticSeverity::Warning;
        let error = krs_cli::UnlocatedDiagnostic {
            code: "UndefinedKLabel".to_owned(),
            severity: krs_cli::DiagnosticSeverity::Error,
            message: "undefined label".to_owned(),
            source: None,
            generated_range: None,
            notes: Vec::new(),
        };
        let mut warning = error.clone();
        warning.code = "UnusedVariable".to_owned();
        warning.severity = krs_cli::DiagnosticSeverity::Warning;
        warning.message = "unused variable".to_owned();
        let mut output = Vec::new();
        write_diagnostics(
            &mut output,
            &[envelope.clone()],
            &[error, warning],
            MessageFormat::Json,
            &DiagnosticSources::default(),
            false,
        )
        .unwrap();
        assert_eq!(
            String::from_utf8(output).unwrap(),
            format!(
                "{}krs: UndefinedKLabel: undefined label\nkrs: warning: UnusedVariable: unused variable\n",
                envelope.to_json_line().unwrap(),
            )
        );
    }

    fn parse_args(args: &[&str]) -> Result<ParseResult, UsageError> {
        parse(args.iter().map(OsString::from).collect())
    }

    fn error(args: &[&str]) -> String {
        match parse_args(args) {
            Err(error) => error.to_string(),
            Ok(_) => panic!("expected error for {args:?}"),
        }
    }

    fn run(args: &[&str]) -> (CommandRequest, MeasureOptions) {
        match parse_args(args).unwrap() {
            ParseResult::Run(request, measure) => (request, measure),
            _ => panic!("expected run command"),
        }
    }

    #[test]
    fn parses_message_format() {
        for command in ["check", "expand", "emit-k", "build"] {
            let mut args = vec![command, "--package", "imp", "--definition", "main"];
            if matches!(command, "emit-k" | "build") {
                args.extend(["--output", "out"]);
            }
            assert_eq!(run(&args).0.message_format, MessageFormat::Human);
            for spelling in [
                vec!["--message-format", "json"],
                vec!["--message-format=json"],
                vec!["--message-format=human"],
            ] {
                let mut selected = args.clone();
                selected.extend(&spelling);
                let expected = if spelling.last() == Some(&"--message-format=human") {
                    MessageFormat::Human
                } else {
                    MessageFormat::Json
                };
                assert_eq!(run(&selected).0.message_format, expected);
            }
        }
        assert_eq!(
            error(&["check", "--message-format=xml"]),
            "unknown message format `xml`"
        );
    }

    #[test]
    fn parses_value_options_with_equals() {
        let (request, measure) = run(&[
            "build",
            "--manifest-path=Cargo.toml",
            "--package=imp",
            "--definition=main",
            "--dependency=base:core",
            "--cfg=feature=enabled",
            "--backend=haskell",
            "--output=out",
            "--timings=timings.json",
            "--counters=counters.json",
            "--registration=explicit",
        ]);
        assert_eq!(
            request.command,
            Command::Build {
                backend: Backend::Haskell,
                output: PathBuf::from("out")
            }
        );
        assert_eq!(request.dependencies.len(), 1);
        assert_eq!(request.cfg[0].value.as_deref(), Some("enabled"));
        assert_eq!(request.registration, RegistrationMode::Explicit);
        assert_eq!(measure.timings, Some(PathBuf::from("timings.json")));
        assert_eq!(measure.counters, Some(PathBuf::from("counters.json")));
    }

    #[test]
    fn parses_command_variants_and_repeatable_values() {
        let (request, _) = run(&[
            "emit-k",
            "--package",
            "imp",
            "--definition",
            "main",
            "--backend",
            "haskell",
            "--output",
            "out",
            "--dependency",
            "a:b",
            "--dependency",
            "c:d",
            "--cfg",
            "flag",
            "--cfg",
            "mode=fast",
            "--no-reuse",
            "--no-reuse",
        ]);
        assert_eq!(
            request.command,
            Command::EmitK {
                output: "out".into()
            }
        );
        assert_eq!(request.dependencies.len(), 2);
        assert_eq!(request.cfg.len(), 2);
        assert_eq!(request.cfg[0].value, None);
        assert!(request.no_reuse);

        let (request, _) = run(&[
            "check",
            "--package-id",
            "exact-id",
            "--definition",
            "main",
            "--backend",
            "haskell",
        ]);
        assert_eq!(
            request.command,
            Command::Check {
                backend: Backend::Haskell
            }
        );
        assert_eq!(request.root.package, PackageSelector::Id("exact-id".into()));

        let (request, _) = run(&["expand", "--package", "imp", "--definition", "main"]);
        assert_eq!(request.command, Command::Expand);
    }

    #[test]
    fn rejects_repeated_singular_options() {
        let required = [
            "build",
            "--package-id",
            "id",
            "--definition",
            "main",
            "--output",
            "out",
        ];
        for (option, value) in [
            ("--manifest-path", "Cargo.toml"),
            ("--package", "imp"),
            ("--package-id", "id"),
            ("--definition", "main"),
            ("--backend", "llvm"),
            ("--output", "out"),
            ("--timings", "timings.json"),
            ("--counters", "counters.json"),
            ("--registration", "inventory"),
            ("--message-format", "json"),
        ] {
            let mut args = required.to_vec();
            if !args.contains(&option) {
                args.extend([option, value]);
            }
            args.extend([option, value]);
            assert_eq!(
                error(&args),
                format!("{option} specified more than once"),
                "{args:?}"
            );
        }
        for (option, value) in [
            ("--manifest-path", "Cargo.toml"),
            ("--trailing-comments", "gutter"),
        ] {
            assert_eq!(
                error(&["fmt", option, value, option, value]),
                format!("{option} specified more than once")
            );
        }
    }

    #[test]
    fn rejects_invalid_combinations_and_spellings() {
        let base = ["--package", "imp", "--definition", "main"];
        assert!(
            error(&[
                "check",
                "--package",
                "imp",
                "--package-id",
                "id",
                "--definition",
                "main"
            ])
            .contains("--package and --package-id")
        );
        for key in ["1abc", "a-b", "fn", ""] {
            assert!(
                error(&[
                    "check",
                    "--package",
                    "imp",
                    "--definition",
                    "main",
                    "--cfg",
                    key
                ])
                .contains("invalid cfg key")
            );
        }
        for command in ["check", "expand"] {
            assert!(
                error(&[
                    command, base[0], base[1], base[2], base[3], "--output", "out"
                ])
                .contains(&format!("--output does not apply to {command}"))
            );
        }
        for command in ["emit-k", "build"] {
            assert!(
                error(&[command, base[0], base[1], base[2], base[3]]).contains("missing --output")
            );
        }
        assert!(error(&["check", "--package", "imp"]).contains("missing --definition"));
        assert!(!error(&["check", "--wat"]).is_empty());
        assert!(error(&["wat"]).contains("unknown command"));
        assert!(error(&["check", "--backend", "unknown"]).contains("unknown backend"));
        for dependency in ["base", ":core", "base:"] {
            assert!(error(&["check", "--dependency", dependency]).contains("dependency"));
        }
    }

    #[test]
    fn parses_fmt_editor_mode() {
        let ParseResult::Format(request) = parse_args(&[
            "fmt",
            "--stdin",
            "--edition",
            "2021",
            "--trailing-comments",
            "gutter",
        ])
        .unwrap() else {
            panic!("expected fmt command")
        };
        assert!(request.stdin);
        assert_eq!(request.edition, Edition::E2021);
        assert_eq!(request.trailing_comments, TrailingCommentStyle::FixedGutter);
    }

    #[test]
    fn parses_fmt_modes() {
        let ParseResult::Format(request) = parse_args(&[
            "fmt",
            "--stdin",
            "--stdin",
            "--check",
            "--check",
            "--trailing-comments=gutter",
        ])
        .unwrap() else {
            panic!("expected fmt command")
        };
        assert!(request.stdin);
        assert!(request.check);
        assert_eq!(request.trailing_comments, TrailingCommentStyle::FixedGutter);
        let ParseResult::Format(request) =
            parse_args(&["fmt", "--", "--check", "--help", "src/lib.rs"]).unwrap()
        else {
            panic!("expected fmt command")
        };
        assert_eq!(
            request.paths,
            [
                PathBuf::from("--check"),
                PathBuf::from("--help"),
                PathBuf::from("src/lib.rs")
            ]
        );
        assert!(!request.check);
        let ParseResult::Format(request) =
            parse_args(&["fmt", "--manifest-path=Cargo.toml"]).unwrap()
        else {
            panic!("expected fmt command")
        };
        assert_eq!(request.manifest_path, Some(PathBuf::from("Cargo.toml")));
    }

    #[test]
    fn rejects_unknown_or_file_mode_edition() {
        assert!(error(&["fmt", "--stdin", "--edition", "2030"]).contains("unknown Rust edition"));
        assert!(error(&["fmt", "--edition", "2021", "src"]).contains("--edition requires --stdin"));
        assert!(
            error(&["fmt", "--stdin", "--edition", "2021", "--edition=2024"])
                .contains("--edition specified more than once")
        );
    }

    #[test]
    fn rejects_fmt_stdin_conflicts() {
        assert!(error(&["fmt", "--stdin", "src"]).contains("--stdin cannot"));
        assert!(
            error(&["fmt", "--stdin", "--manifest-path", "Cargo.toml"]).contains("--stdin cannot")
        );
    }

    #[test]
    fn help_and_missing_values() {
        for args in [vec!["--help"], vec!["check", "--help"], vec!["fmt", "-h"]] {
            assert!(matches!(parse_args(&args), Ok(ParseResult::Help)));
        }
        assert!(
            error(&["check", "--definition"])
                .contains("missing argument for option '--definition'")
        );
        assert!(
            error(&["fmt", "--trailing-comments"])
                .contains("missing argument for option '--trailing-comments'")
        );
    }

    #[cfg(unix)]
    #[test]
    fn rejects_non_utf8_option_values() {
        use std::os::unix::ffi::OsStringExt;
        let args = vec![
            OsString::from("check"),
            OsString::from("--definition"),
            OsString::from_vec(vec![0xff]),
        ];
        assert!(
            matches!(parse(args), Err(UsageError::Message(message)) if message.contains("UTF-8"))
        );
    }
}
