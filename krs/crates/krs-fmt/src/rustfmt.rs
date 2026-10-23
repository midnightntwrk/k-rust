use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};
use std::str::FromStr;

use krs_ir::LineIndex;
use krs_syntax::surface::{self, FacadeScope, FunctionMacro, InvocationKind};
use proc_macro2::{Span, TokenStream, TokenTree};

use crate::rules::{self, BodyLayout};
use crate::{Edition, FormatError, FormatErrorKind};

pub(crate) struct ElidedSource {
    pub(crate) source: String,
    pub(crate) bodies: Vec<RuleBody>,
}

pub(crate) struct RuleBody {
    entry: FunctionMacro,
    marker: String,
    source: String,
    source_start: usize,
}

#[derive(Clone, Copy)]
struct BodyRange {
    entry: FunctionMacro,
    start: usize,
    end: usize,
}

fn find_rule_bodies(source: &str, facade: &FacadeScope) -> Result<Vec<BodyRange>, FormatError> {
    let syntax = syn::parse_file(source).map_err(|error| {
        FormatError::new(
            FormatErrorKind::RustSyntax,
            format!("cannot parse Rust source before formatting: {error}"),
        )
    })?;
    let line_index = LineIndex::new(source);
    let mut ranges = Vec::new();
    for invocation in surface::invocations(&syntax, facade) {
        let InvocationKind::Function {
            entry: entry @ (FunctionMacro::Rules | FunctionMacro::Claims | FunctionMacro::Equations),
            delimiter: Some(delimiter),
            ..
        } = invocation.kind
        else {
            continue;
        };
        if !matches!(delimiter, syn::MacroDelimiter::Brace(_)) {
            return Err(FormatError::new(
                FormatErrorKind::NonBraceRules,
                format!(
                    "KRS `{}!` must use braces so `krs fmt` can enforce its block layout",
                    entry.name()
                ),
            ));
        }
        // `syn::parse_file` strips a shebang before assigning span byte ranges.
        let open = delimiter.span().open().end();
        let close = delimiter.span().close().start();
        let start = line_index
            .line_column_to_byte(open)
            .map_err(span_index_error)?;
        let end = line_index
            .line_column_to_byte(close)
            .map_err(span_index_error)?;
        source.get(start..end).ok_or_else(|| {
            FormatError::new(
                FormatErrorKind::RustSyntax,
                "a `rules!` body span escaped its source",
            )
        })?;
        ranges.push(BodyRange { entry, start, end });
    }
    ranges.sort_by_key(|range| range.start);
    Ok(ranges)
}

pub(crate) fn elide_rule_bodies(
    source: &str,
    facade: &FacadeScope,
) -> Result<ElidedSource, FormatError> {
    let ranges = find_rule_bodies(source, facade)?;
    let mut output = source.to_owned();
    let mut bodies = ranges
        .iter()
        .enumerate()
        .map(|(index, range)| {
            let body = source.get(range.start..range.end).ok_or_else(|| {
                FormatError::new(
                    FormatErrorKind::RustSyntax,
                    "a `rules!` body range escaped its source",
                )
            })?;
            Ok(RuleBody {
                entry: range.entry,
                marker: format!("__KRS_FMT_BODY_{index}"),
                source: body.to_owned(),
                source_start: range.start,
            })
        })
        .collect::<Result<Vec<_>, FormatError>>()?;
    for (range, body) in ranges.iter().zip(&bodies).rev() {
        output.replace_range(range.start..range.end, &body.marker);
    }
    bodies.shrink_to_fit();
    Ok(ElidedSource {
        source: output,
        bodies,
    })
}

pub(crate) fn splice_rule_bodies(
    source: &str,
    bodies: &[RuleBody],
    layout: BodyLayout,
    facade: &FacadeScope,
) -> Result<String, FormatError> {
    let ranges = find_rule_bodies(source, facade)?;
    if ranges.len() != bodies.len() {
        return Err(FormatError::new(
            FormatErrorKind::Rustfmt,
            format!(
                "Rustfmt changed the number of `rules!` invocations from {} to {}",
                bodies.len(),
                ranges.len()
            ),
        ));
    }
    let mut replacements = Vec::with_capacity(bodies.len());
    for range in &ranges {
        let marker = source
            .get(range.start..range.end)
            .ok_or_else(|| {
                FormatError::new(
                    FormatErrorKind::Rustfmt,
                    "a Rustfmt `rules!` body range escaped its source",
                )
            })?
            .trim();
        let body = bodies
            .iter()
            .find(|body| body.marker == marker)
            .ok_or_else(|| {
                FormatError::new(
                    FormatErrorKind::Rustfmt,
                    format!("Rustfmt lost formatter body marker `{marker}`"),
                )
            })?;
        let base_indent = line_indent(source, range.start);
        let body_indent = format!("{base_indent}    ");
        let format = match body.entry {
            FunctionMacro::Equations => rules::format_equation_body,
            FunctionMacro::Claims => rules::format_claim_body,
            _ => rules::format_rule_body,
        };
        let formatted = format(&body.source, body.source_start, &body_indent, layout)?;
        replacements.push(format!("\n{formatted}\n{base_indent}"));
    }
    let mut output = source.to_owned();
    for (range, replacement) in ranges.iter().zip(replacements).rev() {
        output.replace_range(range.start..range.end, &replacement);
    }
    Ok(output)
}

fn line_indent(source: &str, offset: usize) -> String {
    let line_start = source[..offset].rfind('\n').map_or(0, |index| index + 1);
    source[line_start..offset]
        .chars()
        .take_while(|character| matches!(character, ' ' | '\t'))
        .collect()
}

/// Rustfmt's `max_width` when no configuration sets it.
pub(crate) const DEFAULT_MAX_WIDTH: usize = 100;

fn command() -> Command {
    Command::new(std::env::var_os("RUSTFMT").unwrap_or_else(|| "rustfmt".into()))
}

/// The `max_width` of the Rustfmt configuration that applies in `directory`.
pub(crate) fn max_width(directory: &Path) -> Result<usize, FormatError> {
    // Rustfmt resolves the configuration of a file path from the file's
    // directory; the file need not exist.
    let output = command()
        .args(["--print-config", "current", "krs-fmt-config-probe.rs"])
        .current_dir(directory)
        .stdin(Stdio::null())
        .stderr(Stdio::piped())
        .output()
        .map_err(|error| {
            FormatError::new(
                FormatErrorKind::Rustfmt,
                format!("cannot start Rustfmt: {error}"),
            )
        })?;
    if !output.status.success() {
        return Err(FormatError::new(
            FormatErrorKind::Rustfmt,
            format!(
                "Rustfmt cannot resolve its configuration: {}",
                String::from_utf8_lossy(&output.stderr).trim()
            ),
        ));
    }
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .find_map(|line| {
            let (key, value) = line.split_once('=')?;
            (key.trim() == "max_width").then(|| value.trim().parse().ok())?
        })
        .ok_or_else(|| {
            FormatError::new(
                FormatErrorKind::Rustfmt,
                "Rustfmt's configuration has no `max_width`",
            )
        })
}

pub(crate) fn run(source: &str, edition: Edition, directory: &Path) -> Result<String, FormatError> {
    let mut command = command();
    command
        .arg("--edition")
        .arg(edition.to_string())
        .args(["--emit", "stdout"])
        .current_dir(directory)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut child = command.spawn().map_err(|error| {
        FormatError::new(
            FormatErrorKind::Rustfmt,
            format!("cannot start Rustfmt: {error}"),
        )
    })?;
    child
        .stdin
        .as_mut()
        .ok_or_else(|| FormatError::new(FormatErrorKind::Rustfmt, "Rustfmt stdin is unavailable"))?
        .write_all(source.as_bytes())
        .map_err(|error| {
            FormatError::new(
                FormatErrorKind::Rustfmt,
                format!("cannot write source to Rustfmt: {error}"),
            )
        })?;
    let output = child.wait_with_output().map_err(|error| {
        FormatError::new(
            FormatErrorKind::Rustfmt,
            format!("cannot wait for Rustfmt: {error}"),
        )
    })?;
    if !output.status.success() {
        return Err(FormatError::new(
            FormatErrorKind::Rustfmt,
            format!(
                "Rustfmt rejected the elided source: {}",
                String::from_utf8_lossy(&output.stderr).trim()
            ),
        ));
    }
    String::from_utf8(output.stdout).map_err(|error| {
        FormatError::new(
            FormatErrorKind::Rustfmt,
            format!("Rustfmt output is not UTF-8: {error}"),
        )
    })
}

/// Checks that formatting kept each DSL body's tokens, modulo trailing
/// commas (which the layout writes or removes), and that each formatted
/// body parses with the `krs-syntax` entry its macro formats with.
pub(crate) fn validate_token_payload(
    before: &str,
    after: &str,
    facade: &FacadeScope,
) -> Result<(), FormatError> {
    let before_ranges = find_rule_bodies(before, facade)?;
    let after_ranges = find_rule_bodies(after, facade)?;
    if before_ranges.len() != after_ranges.len() {
        return Err(FormatError::new(
            FormatErrorKind::TokenPayloadChanged,
            format!(
                "formatting changed the number of KRS DSL bodies from {} to {}",
                before_ranges.len(),
                after_ranges.len()
            ),
        ));
    }
    for (index, (before_range, after_range)) in before_ranges.iter().zip(&after_ranges).enumerate()
    {
        let before_body = TokenStream::from_str(&before[before_range.start..before_range.end])
            .map_err(|error| {
                FormatError::new(
                    FormatErrorKind::RustSyntax,
                    format!("cannot tokenize KRS DSL body {index} before formatting: {error}"),
                )
            })?;
        let after_source = &after[after_range.start..after_range.end];
        let after_body = TokenStream::from_str(after_source).map_err(|error| {
            FormatError::new(
                FormatErrorKind::OutputDoesNotParse,
                format!("cannot tokenize formatted KRS DSL body {index}: {error}"),
            )
        })?;
        reparse_body(after_range.entry, after_source).map_err(|error| {
            FormatError::new(
                FormatErrorKind::OutputDoesNotParse,
                format!(
                    "formatted `{}!` body {index} does not parse: {error}",
                    after_range.entry.name()
                ),
            )
        })?;
        if without_trailing_commas(before_body).to_string()
            != without_trailing_commas(after_body).to_string()
        {
            return Err(FormatError::new(
                FormatErrorKind::TokenPayloadChanged,
                format!("formatting changed the span-blind token payload of KRS DSL body {index}"),
            ));
        }
    }
    Ok(())
}

/// Parses a formatted body with the entry the formatter parsed it with.
fn reparse_body(entry: FunctionMacro, source: &str) -> Result<(), krs_syntax::SyntaxError> {
    match entry {
        FunctionMacro::Equations => {
            krs_syntax::parse_equation_table_source_with_trivia(source).map(drop)
        }
        FunctionMacro::Claims => krs_syntax::parse_claim_block_source_with_trivia(source).map(drop),
        _ => krs_syntax::parse_rule_block_source_with_trivia(source).map(drop),
    }
}

/// The tokens without the commas directly before a closing delimiter or a
/// `;`: a trailing comma adds no element, and the layout decides it.
fn without_trailing_commas(tokens: TokenStream) -> TokenStream {
    let tokens = tokens.into_iter().collect::<Vec<_>>();
    let mut output = Vec::with_capacity(tokens.len());
    for (index, token) in tokens.iter().enumerate() {
        let is_comma = matches!(token, TokenTree::Punct(punct) if punct.as_char() == ',');
        let ends = match tokens.get(index + 1) {
            None => true,
            Some(TokenTree::Punct(next)) => next.as_char() == ';',
            Some(_) => false,
        };
        if is_comma && ends {
            continue;
        }
        output.push(match token {
            TokenTree::Group(group) => {
                let mut stripped = proc_macro2::Group::new(
                    group.delimiter(),
                    without_trailing_commas(group.stream()),
                );
                stripped.set_span(group.span());
                TokenTree::Group(stripped)
            }
            other => other.clone(),
        });
    }
    output.into_iter().collect()
}

pub(crate) fn validate_comment_payload(before: &str, after: &str) -> Result<(), FormatError> {
    let before = line_comments(before)?;
    let after = line_comments(after)?;
    if before != after {
        return Err(FormatError::new(
            FormatErrorKind::CommentPayloadChanged,
            "formatting dropped, duplicated, or reordered a `//` comment payload",
        ));
    }
    Ok(())
}

fn line_comments(source: &str) -> Result<Vec<String>, FormatError> {
    let stream = TokenStream::from_str(source).map_err(|error| {
        FormatError::new(
            FormatErrorKind::RustSyntax,
            format!("cannot tokenize source for trivia validation: {error}"),
        )
    })?;
    let mut ranges = Vec::new();
    collect_ranges(source, stream, &mut ranges)?;
    let trivia = krs_syntax::lex_gaps(source, &ranges).map_err(|error| {
        FormatError::new(
            FormatErrorKind::RustSyntax,
            format!("cannot classify source trivia: {error}"),
        )
    })?;
    Ok(trivia
        .into_iter()
        .filter(|item| matches!(item.kind(), krs_syntax::TriviaKind::LineComment(_)))
        .filter_map(|item| item.range().text(source).map(ToOwned::to_owned))
        .collect())
}

fn collect_ranges(
    source: &str,
    stream: TokenStream,
    output: &mut Vec<krs_syntax::SourceRange>,
) -> Result<(), FormatError> {
    for token in stream {
        match token {
            TokenTree::Group(group) => {
                output.push(span_range(source, group.span_open())?);
                collect_ranges(source, group.stream(), output)?;
                output.push(span_range(source, group.span_close())?);
            }
            token => output.push(span_range(source, token.span())?),
        }
    }
    Ok(())
}

fn span_range(source: &str, span: Span) -> Result<krs_syntax::SourceRange, FormatError> {
    let range = span.byte_range();
    source.get(range.clone()).ok_or_else(|| {
        FormatError::new(
            FormatErrorKind::RustSyntax,
            "a token span escaped its source",
        )
    })?;
    krs_syntax::SourceRange::new(range.start, range.end).map_err(|_| {
        FormatError::new(
            FormatErrorKind::RustSyntax,
            "a token span has reversed byte offsets",
        )
    })
}

fn span_index_error(error: krs_ir::LineIndexError) -> FormatError {
    FormatError::new(FormatErrorKind::RustSyntax, error.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn syntax_rule_bodies_include_attributed_items_and_exclude_raw_tokens() {
        let source = r"k::rules! { item }
mod nested { k::rules! { module } }
fn f() {
    k::rules! { statement }
    let _ = k::rules! { expression };
    let k::rules! { pattern }: k::rules! { ty } = value;
}
#[k::function(k::rules!(opaque_argument))]
fn attributed() { k::rules! { attributed_body } }
#[k::unknown]
fn invalid_attribute() { k::rules! { invalid_attribute_body } }
#[other = k::rules! { attribute_expression }]
k::rules! { attributed_macro }
impl S { k::rules! { impl_item } }
trait T { k::rules! { trait_item } }
other! { k::rules!(opaque_other) }
k::id!(k::rules![opaque_krs]);
";
        let facade = FacadeScope::new(crate::FormatOptions::default().facade_aliases);
        let ranges = find_rule_bodies(source, &facade).unwrap();
        let bodies = ranges
            .iter()
            .map(|range| source[range.start..range.end].trim())
            .collect::<Vec<_>>();
        assert_eq!(
            bodies,
            [
                "item",
                "module",
                "statement",
                "expression",
                "pattern",
                "ty",
                "attributed_body",
                "invalid_attribute_body",
                "attribute_expression",
                "attributed_macro",
                "impl_item",
                "trait_item",
            ]
        );
    }

    #[test]
    fn module_aliases_and_shadowing_select_only_krs_bodies() {
        let source = r"extern crate k as host;
host::rules! { root }
mod nested {
    use k as lang;
    lang::rules! { renamed }
    mod shadowed {
        use other as k;
        k::rules!(opaque_shadowed);
    }
}
lang::rules!(opaque_outside);
";
        let facade = FacadeScope::new(crate::FormatOptions::default().facade_aliases);
        let ranges = find_rule_bodies(source, &facade).unwrap();
        assert_eq!(
            ranges
                .iter()
                .map(|range| source[range.start..range.end].trim())
                .collect::<Vec<_>>(),
            ["root", "renamed"]
        );
    }

    #[test]
    fn byte_ranges_follow_each_parsed_source_string() {
        let source =
            "#!/usr/bin/env rustx\nfn f() { let s = \"🦀\"; k::rules! { for Expr; one: A => A; } }";
        let facade = FacadeScope::new(crate::FormatOptions::default().facade_aliases);
        let bodies = find_rule_bodies(source, &facade).unwrap();
        assert_eq!(bodies.len(), 1);
        assert_eq!(
            &source[bodies[0].start..bodies[0].end],
            " for Expr; one: A => A; "
        );

        let fragment = "\"🦀\" + x";
        let tokens = TokenStream::from_str(fragment).unwrap();
        let first = tokens.into_iter().next().unwrap();
        let range = span_range(fragment, first.span()).unwrap();
        assert_eq!(range.text(fragment), Some("\"🦀\""));
    }
}
