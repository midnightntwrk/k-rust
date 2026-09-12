use std::ffi::{OsStr, OsString};
use std::path::Path;
use std::process::Command;

use crate::kast::Sort;

use super::Error;

pub(super) fn compile(directory: &Path, start_sort: &Sort, executable: &Path) -> Result<(), Error> {
    let scanner = directory.join("scanner.l");
    let scanner_header = directory.join("scanner.h");
    let scanner_c = directory.join("lex.yy.c");
    let mut header_argument = OsString::from("--header-file=");
    header_argument.push(&scanner_header);
    run(
        "flex",
        tool("KRUST_FLEX", "flex"),
        directory,
        [
            header_argument,
            OsString::from("-w"),
            OsString::from("-o"),
            scanner_c.as_os_str().to_owned(),
            scanner.as_os_str().to_owned(),
        ],
    )?;

    let grammar = directory.join("parser.y");
    let parser_c = directory.join("parser.tab.c");
    run(
        "bison",
        tool("KRUST_BISON", "bison"),
        directory,
        [
            OsString::from("-d"),
            OsString::from("-Wno-other"),
            OsString::from("-Wno-conflicts-sr"),
            OsString::from("-Wno-conflicts-rr"),
            OsString::from("-o"),
            parser_c.as_os_str().to_owned(),
            grammar.as_os_str().to_owned(),
        ],
    )?;

    run(
        "C compiler",
        tool("KRUST_CC", "cc"),
        directory,
        [
            OsString::from(format!("-DK_BISON_PARSER_SORT={}", start_sort.name)),
            OsString::from("-DK_BISON_PARSER_MAIN"),
            directory.join("main.c").into_os_string(),
            scanner_c.into_os_string(),
            parser_c.into_os_string(),
            OsString::from("-iquote"),
            directory.as_os_str().to_owned(),
            OsString::from("-o"),
            executable.as_os_str().to_owned(),
        ],
    )
}

fn tool(variable: &str, default: &str) -> OsString {
    std::env::var_os(variable).unwrap_or_else(|| default.into())
}

fn run(
    description: &str,
    executable: impl AsRef<OsStr>,
    directory: &Path,
    arguments: impl IntoIterator<Item = OsString>,
) -> Result<(), Error> {
    let output = Command::new(executable)
        .args(arguments)
        .current_dir(directory)
        .output()
        .map_err(|error| Error::io(&format!("could not execute {description}"), error))?;
    if output.status.success() {
        return Ok(());
    }
    let status = output
        .status
        .code()
        .map_or_else(|| "signal".to_owned(), |code| format!("exit code {code}"));
    let stderr = String::from_utf8_lossy(&output.stderr);
    Err(Error::render(format!(
        "{description} failed with {status}: {}",
        stderr.trim_end()
    )))
}
