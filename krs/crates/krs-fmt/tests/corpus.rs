//! Formatting properties over the port specifications and the tours.
//!
//! For every Rust source under `krs/semantics/` and `krs/tests/tour-*/`:
//! formatting is idempotent and leaves the file's token stream unchanged.
//! `format_file` also checks the line comments and that direct Rustfmt
//! accepts the result as it is.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::str::FromStr;

use krs_fmt::{FormatOptions, format_file, format_source_in};
use proc_macro2::TokenStream;

fn sources(directory: &Path, output: &mut Vec<PathBuf>) {
    let mut entries = std::fs::read_dir(directory)
        .unwrap_or_else(|error| panic!("read `{}`: {error}", directory.display()))
        .map(|entry| entry.expect("directory entry").path())
        .collect::<Vec<_>>();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            if path.file_name().is_some_and(|name| name != "target") {
                sources(&path, output);
            }
        } else if path.extension().is_some_and(|extension| extension == "rs") {
            output.push(path);
        }
    }
}

fn tokens(source: &str, path: &Path) -> String {
    TokenStream::from_str(source)
        .unwrap_or_else(|error| panic!("tokenize `{}`: {error}", path.display()))
        .to_string()
}

#[test]
fn ports_and_tours_format_idempotently_without_changing_tokens() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut files = Vec::new();
    sources(&root.join("semantics"), &mut files);
    let ports = files.len();
    let mut tours = std::fs::read_dir(root.join("tests"))
        .expect("read the tests directory")
        .map(|entry| entry.expect("directory entry").path())
        .filter(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.starts_with("tour-"))
        })
        .collect::<Vec<_>>();
    tours.sort();
    for tour in tours {
        sources(&tour, &mut files);
    }
    assert!(ports >= 3, "the three ports have sources");
    assert!(files.len() > ports, "the tours have sources");

    let options = FormatOptions {
        // The composition tour renames its facade to `language_host`.
        facade_aliases: BTreeSet::from(["k".to_owned(), "language_host".to_owned()]),
        check_idempotence: false,
        ..FormatOptions::default()
    };
    for path in &files {
        let source = std::fs::read_to_string(path).expect("read source");
        let once = format_file(path, &options)
            .unwrap_or_else(|error| panic!("format `{}`: {error}", path.display()))
            .output;
        let directory = path.parent().expect("a source has a directory");
        let twice = format_source_in(&once, &options, directory)
            .unwrap_or_else(|error| panic!("reformat `{}`: {error}", path.display()));
        assert!(
            once == twice,
            "`{}` changed on a second pass",
            path.display()
        );
        assert_eq!(
            tokens(&source, path),
            tokens(&once, path),
            "formatting changed the tokens of `{}`",
            path.display()
        );
    }
    eprintln!(
        "checked {} files ({ports} under krs/semantics)",
        files.len()
    );
}
