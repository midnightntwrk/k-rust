//! Formatting properties over the port specifications and the tours.
//!
//! For every Rust source under `krs/semantics/` and `krs/tests/tour-*/`:
//! formatting is idempotent and leaves the file's token stream unchanged
//! modulo trailing commas, and every comma list of a DSL body ends with a
//! comma exactly when it is broken over lines, except where a comma is no
//! list's end. `format_file` also checks the line comments, that every
//! formatted body re-parses, and that direct Rustfmt accepts the result.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::str::FromStr;

use krs_fmt::{FormatOptions, format_file, format_source_in};
use proc_macro2::{Delimiter, Group, TokenStream, TokenTree};

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

fn parse(source: &str, path: &Path) -> TokenStream {
    TokenStream::from_str(source)
        .unwrap_or_else(|error| panic!("tokenize `{}`: {error}", path.display()))
}

/// The tokens without the commas directly before a closing delimiter or a
/// `;`, which the layout writes or removes.
fn without_trailing_commas(tokens: TokenStream) -> String {
    fn strip(tokens: TokenStream) -> TokenStream {
        let tokens = tokens.into_iter().collect::<Vec<_>>();
        let mut output = Vec::new();
        for (index, token) in tokens.iter().enumerate() {
            let ends = match tokens.get(index + 1) {
                None => true,
                Some(TokenTree::Punct(next)) => next.as_char() == ';',
                Some(_) => false,
            };
            if is_punct(token, ',') && ends {
                continue;
            }
            output.push(match token {
                TokenTree::Group(group) => {
                    TokenTree::Group(Group::new(group.delimiter(), strip(group.stream())))
                }
                other => other.clone(),
            });
        }
        output.into_iter().collect()
    }
    strip(tokens).to_string()
}

fn is_punct(token: &TokenTree, character: char) -> bool {
    matches!(token, TokenTree::Punct(punct) if punct.as_char() == character)
}

/// Checks the trailing comma of every comma list in the `rules!`,
/// `claims!`, and `equations!` bodies of `tokens`.
fn check_bodies(tokens: TokenStream, path: &Path) {
    let tokens = tokens.into_iter().collect::<Vec<_>>();
    for (index, token) in tokens.iter().enumerate() {
        let TokenTree::Group(group) = token else {
            continue;
        };
        let body = index >= 2
            && is_punct(&tokens[index - 1], '!')
            && matches!(&tokens[index - 2], TokenTree::Ident(name)
                if ["rules", "claims", "equations"].contains(&name.to_string().as_str()));
        if body {
            check_lists(group.stream(), path);
        } else {
            check_bodies(group.stream(), path);
        }
    }
}

/// Checks each group in `tokens`, then the groups inside it.
fn check_lists(tokens: TokenStream, path: &Path) {
    let tokens = tokens.into_iter().collect::<Vec<_>>();
    for (index, token) in tokens.iter().enumerate() {
        let TokenTree::Group(group) = token else {
            continue;
        };
        let previous = index.checked_sub(1).map(|previous| &tokens[previous]);
        // An attribute keeps the layout it is written with.
        if previous.is_some_and(|previous| is_punct(previous, '#')) {
            continue;
        }
        let headless = !matches!(
            previous,
            Some(TokenTree::Ident(_) | TokenTree::Group(_) | TokenTree::Literal(_))
        ) && !previous.is_some_and(|previous| is_punct(previous, '!'));
        let index_like = group.delimiter() == Delimiter::Bracket
            && matches!(previous, Some(TokenTree::Ident(_) | TokenTree::Group(_)));
        check_list(group, headless, index_like, path);
        check_lists(group.stream(), path);
    }
}

fn check_list(group: &Group, headless: bool, index_like: bool, path: &Path) {
    let tokens = group.stream().into_iter().collect::<Vec<_>>();
    if tokens.is_empty() || tokens.iter().any(|token| is_punct(token, ';')) {
        return;
    }
    let trailing = tokens.last().is_some_and(|token| is_punct(token, ','));
    let items = tokens
        .split(|token| is_punct(token, ','))
        .filter(|item| !item.is_empty())
        .collect::<Vec<_>>();
    let single = items.len() == 1;
    let delimiter = group.delimiter();
    let keep = delimiter == Delimiter::None
        || (headless && single && matches!(delimiter, Delimiter::Parenthesis | Delimiter::Brace))
        || index_like;
    if keep {
        return;
    }
    let line = |span: proc_macro2::Span| span.start().line;
    let broken = line(group.span_open()) != line(group.span_close());
    let last = items.last().expect("a nonempty group has an item");
    let rest = match *last {
        [TokenTree::Punct(first), TokenTree::Punct(second), ..] => {
            first.as_char() == '.' && second.as_char() == '.'
        }
        [
            TokenTree::Ident(_),
            at,
            TokenTree::Punct(first),
            TokenTree::Punct(second),
        ] => is_punct(at, '@') && first.as_char() == '.' && second.as_char() == '.',
        _ => false,
    };
    let hugged = single
        && matches!(last.last(), Some(TokenTree::Group(inner))
            if line(inner.span_open()) == line(group.span_open()));
    let expected = broken && !hugged && !(delimiter == Delimiter::Brace && rest);
    assert_eq!(
        trailing,
        expected,
        "`{}` line {}: a {} list {} a trailing comma",
        path.display(),
        line(group.span_open()),
        if broken { "broken" } else { "one-line" },
        if trailing { "has" } else { "lacks" },
    );
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
            without_trailing_commas(parse(&source, path)),
            without_trailing_commas(parse(&once, path)),
            "formatting changed the tokens of `{}`",
            path.display()
        );
        check_bodies(parse(&once, path), path);
    }
    eprintln!(
        "checked {} files ({ports} under krs/semantics)",
        files.len()
    );
}
