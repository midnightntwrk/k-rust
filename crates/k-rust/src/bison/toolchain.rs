use std::ffi::{OsStr, OsString};
use std::path::Path;
use std::process::Command;

use crate::kast::Sort;

use super::{Artifact, Error};

pub(super) fn compile(
    directory: &Path,
    start_sort: &Sort,
    output: &Path,
    artifact: Artifact,
) -> Result<(), Error> {
    let scanner = directory.join("scanner.l");
    let scanner_header = directory.join("scanner.h");
    let scanner_c = directory.join("lex.yy.c");
    let mut header_argument = OsString::from("--header-file=");
    header_argument.push(&scanner_header);
    run(
        "flex",
        tool("KRUST_FLEX", "flex"),
        start_sort,
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
        start_sort,
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

    let mut arguments = vec![OsString::from(format!(
        "-DK_BISON_PARSER_SORT={}",
        start_sort.name
    ))];
    match artifact {
        Artifact::Executable => arguments.push(OsString::from("-DK_BISON_PARSER_MAIN")),
        Artifact::SharedLibrary => {
            arguments.push(OsString::from("-fPIC"));
            arguments.push(OsString::from("-shared"));
        }
    }
    arguments.extend([
        directory.join("main.c").into_os_string(),
        scanner_c.into_os_string(),
        parser_c.into_os_string(),
        OsString::from("-iquote"),
        directory.as_os_str().to_owned(),
        OsString::from("-o"),
        output.as_os_str().to_owned(),
    ]);
    run(
        "C compiler",
        tool("KRUST_CC", "cc"),
        start_sort,
        directory,
        arguments,
    )
}

fn tool(variable: &str, default: &str) -> OsString {
    std::env::var_os(variable).unwrap_or_else(|| default.into())
}

/// Runs one tool of the parser build for `start_sort`. A tool that exits with a status rejects
/// its input and says why on standard error, which is reported as it is. A tool killed by a
/// signal stopped without deciding anything about its input (an internal assertion of the tool,
/// or an outside kill), so that is reported as deciding nothing about the grammar, with the
/// parser it was building and both possible causes, before whatever it wrote.
fn run(
    description: &str,
    executable: impl AsRef<OsStr>,
    start_sort: &Sort,
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
    let stderr = String::from_utf8_lossy(&output.stderr);
    let stderr = stderr.trim_end();
    if let Some(code) = output.status.code() {
        return Err(Error::render(format!(
            "{description} failed with exit code {code}: {stderr}"
        )));
    }
    #[cfg(unix)]
    let signal = std::os::unix::process::ExitStatusExt::signal(&output.status).map_or_else(
        || "a signal".to_owned(),
        |signal| format!("signal {signal}"),
    );
    #[cfg(not(unix))]
    let signal = "a signal";
    let mut message = format!(
        "{description} was killed by {signal} while building the parser of sort {start_sort}, \
         so it decided nothing about the grammar (an internal failure of {description}, such as \
         an assertion, or a kill from outside it)"
    );
    if !stderr.is_empty() {
        message.push_str(&format!(", and {description} wrote: {stderr}"));
    }
    Err(Error::render(message))
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;

    #[test]
    fn a_tool_killed_by_a_signal_is_reported_as_deciding_nothing_naming_the_start_sort() {
        let directory = std::env::temp_dir();
        let error = run(
            "bison",
            "sh",
            &Sort::new("Pgm"),
            &directory,
            [
                OsString::from("-c"),
                OsString::from("echo 'bison: src/X.c:1: f: Assertion failed.' >&2; kill -ABRT $$"),
            ],
        )
        .unwrap_err()
        .to_string();
        assert_eq!(
            error,
            "bison was killed by signal 6 while building the parser of sort Pgm, so it decided \
             nothing about the grammar (an internal failure of bison, such as an assertion, or a \
             kill from outside it), and bison wrote: bison: src/X.c:1: f: Assertion failed."
        );
        let error = run(
            "bison",
            "sh",
            &Sort::new("Pgm"),
            &directory,
            [
                OsString::from("-c"),
                OsString::from("echo rejected >&2; exit 1"),
            ],
        )
        .unwrap_err()
        .to_string();
        assert_eq!(error, "bison failed with exit code 1: rejected");
    }
}
