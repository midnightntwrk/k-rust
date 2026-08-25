use std::io::Write;
use std::process::{Command, Stdio};
use std::str::FromStr;

use proc_macro2::{LineColumn, Span, TokenStream, TokenTree};
use syn::visit::Visit;

use crate::rules::{self, TrailingCommentStyle};
use crate::{FormatError, FormatErrorKind};

pub(crate) struct ElidedSource {
    pub(crate) source: String,
    pub(crate) bodies: Vec<RuleBody>,
}

pub(crate) struct RuleBody {
    marker: String,
    source: String,
    source_start: usize,
}

#[derive(Clone, Copy)]
struct BodyRange {
    start: usize,
    end: usize,
}

struct RuleBodyVisitor<'source> {
    source: &'source str,
    ranges: Vec<BodyRange>,
    error: Option<FormatError>,
}

impl<'ast> Visit<'ast> for RuleBodyVisitor<'_> {
    fn visit_macro(&mut self, invocation: &'ast syn::Macro) {
        if self.error.is_some() {
            return;
        }
        if invocation
            .path
            .segments
            .last()
            .is_none_or(|segment| segment.ident != "rules")
        {
            syn::visit::visit_macro(self, invocation);
            return;
        }
        if !matches!(invocation.delimiter, syn::MacroDelimiter::Brace(_)) {
            self.error = Some(FormatError::new(
                FormatErrorKind::NonBraceRules,
                "`k::rules!` must use braces so `krs fmt` can enforce its block layout",
            ));
            return;
        }
        let open = invocation.delimiter.span().open().end();
        let close = invocation.delimiter.span().close().start();
        let range = line_columns_to_range(self.source, open, close);
        match range {
            Ok((start, end)) => self.ranges.push(BodyRange { start, end }),
            Err(error) => self.error = Some(error),
        }
    }
}

fn find_rule_bodies(source: &str) -> Result<Vec<BodyRange>, FormatError> {
    let syntax = syn::parse_file(source).map_err(|error| {
        FormatError::new(
            FormatErrorKind::RustSyntax,
            format!("cannot parse Rust source before formatting: {error}"),
        )
    })?;
    let mut visitor = RuleBodyVisitor {
        source,
        ranges: Vec::new(),
        error: None,
    };
    visitor.visit_file(&syntax);
    if let Some(error) = visitor.error {
        return Err(error);
    }
    visitor.ranges.sort_by_key(|range| range.start);
    Ok(visitor.ranges)
}

pub(crate) fn elide_rule_bodies(source: &str) -> Result<ElidedSource, FormatError> {
    let ranges = find_rule_bodies(source)?;
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
    trailing_comments: TrailingCommentStyle,
) -> Result<String, FormatError> {
    let ranges = find_rule_bodies(source)?;
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
        let formatted = rules::format_rule_body(
            &body.source,
            body.source_start,
            &body_indent,
            trailing_comments,
        )?;
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

pub(crate) fn run(source: &str) -> Result<String, FormatError> {
    let mut command = Command::new("rustfmt");
    command
        .args(["--edition", "2024", "--emit", "stdout"])
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

pub(crate) fn validate_token_payload(before: &str, after: &str) -> Result<(), FormatError> {
    let before_ranges = find_rule_bodies(before)?;
    let after_ranges = find_rule_bodies(after)?;
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
            })?
            .to_string();
        let after_body = TokenStream::from_str(&after[after_range.start..after_range.end])
            .map_err(|error| {
                FormatError::new(
                    FormatErrorKind::OutputDoesNotParse,
                    format!("cannot tokenize formatted KRS DSL body {index}: {error}"),
                )
            })?
            .to_string();
        if before_body != after_body {
            return Err(FormatError::new(
                FormatErrorKind::TokenPayloadChanged,
                format!("formatting changed the span-blind token payload of KRS DSL body {index}"),
            ));
        }
    }
    Ok(())
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
    let (start, end) = line_columns_to_range(source, span.start(), span.end())?;
    Ok(krs_syntax::SourceRange::new(start, end))
}

fn line_columns_to_range(
    source: &str,
    start: LineColumn,
    end: LineColumn,
) -> Result<(usize, usize), FormatError> {
    Ok((
        line_column_to_byte(source, start)?,
        line_column_to_byte(source, end)?,
    ))
}

pub(crate) fn line_column_to_byte(
    source: &str,
    location: LineColumn,
) -> Result<usize, FormatError> {
    let line_start = if location.line == 1 {
        0
    } else {
        source
            .match_indices('\n')
            .nth(location.line - 2)
            .map(|(offset, _)| offset + 1)
            .ok_or_else(|| {
                FormatError::new(
                    FormatErrorKind::RustSyntax,
                    format!("span line {} is outside its source", location.line),
                )
            })?
    };
    let line_end = source[line_start..]
        .find('\n')
        .map_or(source.len(), |offset| line_start + offset);
    source[line_start..line_end]
        .char_indices()
        .nth(location.column)
        .map(|(offset, _)| line_start + offset)
        .or_else(|| {
            (location.column == source[line_start..line_end].chars().count()).then_some(line_end)
        })
        .ok_or_else(|| {
            FormatError::new(
                FormatErrorKind::RustSyntax,
                format!(
                    "span column {} is outside source line {}",
                    location.column, location.line
                ),
            )
        })
}
