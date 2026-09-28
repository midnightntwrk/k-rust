use std::fmt::Write as _;
use std::iter::FromIterator;
use std::str::FromStr;

use krs_syntax::{RuleBlock, SourceRange, TriviaKind, TriviaTable};
use pretty::RcDoc;
use proc_macro2::{Delimiter, Spacing, TokenStream, TokenTree};

use crate::rustfmt::line_column_to_byte;
use crate::{FormatError, FormatErrorKind};

/// Canonical placement policy for comments trailing rule clauses.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TrailingCommentStyle {
    /// Put every trailing comment in one table-wide aligned column.
    AlignedColumn,
    /// Put every trailing comment two spaces after its clause terminator.
    FixedGutter,
}

#[derive(Clone, Debug)]
enum GapEvent {
    Blank,
    Comment(String),
}

#[derive(Clone, Debug, Default)]
struct GapLayout {
    trailing: Option<String>,
    leading: Vec<GapEvent>,
}

#[derive(Clone, Debug)]
struct ClauseSource<'source> {
    start: usize,
    end: usize,
    name_start: usize,
    clause: &'source krs_syntax::RuleClause,
}

#[derive(Clone, Debug)]
struct RenderedClause {
    leading: Vec<GapEvent>,
    lines: Vec<String>,
    trailing: Option<String>,
}

/// Formats one complete `rules!` body at its Rustfmt-selected indentation.
#[allow(clippy::too_many_lines)] // One ordered pass preserves trivia geometry around every clause.
pub(crate) fn format_rule_body(
    source: &str,
    source_offset: usize,
    indent: &str,
    trailing_style: TrailingCommentStyle,
) -> Result<String, FormatError> {
    let (block, trivia) =
        krs_syntax::parse_rule_block_source_with_trivia(source).map_err(|error| {
            let range = error.source_range().map_or_else(String::new, |range| {
                format!(
                    " at bytes {}..{}",
                    source_offset + range.start(),
                    source_offset + range.end()
                )
            });
            FormatError::new(
                FormatErrorKind::DslSyntax,
                format!("cannot parse `k::rules!` body{range}: {error}"),
            )
        })?;
    let clauses = clause_sources(source, &block)?;
    let comments = line_comments(source, &trivia);
    let first_clause = clauses.first().ok_or_else(|| {
        FormatError::new(
            FormatErrorKind::DslSyntax,
            "a `k::rules!` block must contain at least one clause",
        )
    })?;
    let header_end = trivia
        .token_ranges()
        .iter()
        .filter(|range| range.end() <= first_clause.start)
        .map(|range| range.end())
        .max()
        .ok_or_else(|| {
            FormatError::new(
                FormatErrorKind::DslSyntax,
                "a `k::rules!` block has no parseable header",
            )
        })?;

    let mut header_lines = comments
        .iter()
        .filter(|comment| comment.end() <= header_end)
        .filter_map(|comment| comment.text(source))
        .map(|comment| comment.trim_start().to_owned())
        .collect::<Vec<_>>();
    header_lines.extend(render_header(&source[..header_end])?);
    let mut rendered: Vec<RenderedClause> = Vec::with_capacity(clauses.len());
    for (index, clause_source) in clauses.iter().enumerate() {
        let previous_end = if index == 0 {
            header_end
        } else {
            clauses[index - 1].end
        };
        let gap = render_gap(source, previous_end, clause_source.start, &comments);
        if index == 0 {
            if let Some(comment) = gap.trailing {
                append_comment(
                    &mut header_lines,
                    &comment,
                    TrailingCommentStyle::FixedGutter,
                );
            }
        } else if let Some(comment) = gap.trailing {
            rendered[index - 1].trailing = Some(comment);
        }

        let mut leading = gap.leading;
        leading.extend(
            comments
                .iter()
                .filter(|comment| {
                    comment.start() >= clause_source.start && comment.end() <= clause_source.end
                })
                .filter_map(|comment| comment.text(source))
                .map(|comment| GapEvent::Comment(comment.to_owned())),
        );
        let lines = render_clause(source, clause_source, &comments, &block)?;
        rendered.push(RenderedClause {
            leading,
            lines,
            trailing: None,
        });
    }

    let last = clauses.last().expect("the parser guarantees one clause");
    let footer = render_gap(source, last.end, source.len(), &comments);
    if let Some(comment) = footer.trailing {
        rendered
            .last_mut()
            .expect("the parser guarantees one clause")
            .trailing = Some(comment);
    }
    align_trailing_comments(&mut rendered, trailing_style);

    let mut lines = header_lines;
    for clause in rendered {
        for event in clause.leading {
            match event {
                GapEvent::Blank => lines.push(String::new()),
                GapEvent::Comment(comment) => lines.push(comment.trim_start().to_owned()),
            }
        }
        lines.extend(clause.lines);
    }
    for event in footer.leading {
        match event {
            GapEvent::Blank => lines.push(String::new()),
            GapEvent::Comment(comment) => lines.push(comment.trim_start().to_owned()),
        }
    }

    let docs: Vec<RcDoc<'static, ()>> = lines
        .into_iter()
        .map(|line| {
            if line.is_empty() {
                RcDoc::nil()
            } else {
                RcDoc::text(indent.to_owned()).append(RcDoc::text(line))
            }
        })
        .collect();
    let document = RcDoc::intersperse(docs, RcDoc::hardline());
    let mut output = Vec::new();
    document.render(100, &mut output).map_err(|error| {
        FormatError::new(
            FormatErrorKind::Io,
            format!("cannot render a `k::rules!` body: {error}"),
        )
    })?;
    String::from_utf8(output).map_err(|error| {
        FormatError::new(
            FormatErrorKind::Io,
            format!("formatter produced non-UTF-8 bytes: {error}"),
        )
    })
}

fn clause_sources<'source>(
    source: &str,
    block: &'source RuleBlock,
) -> Result<Vec<ClauseSource<'source>>, FormatError> {
    block
        .clauses()
        .iter()
        .map(|clause| {
            let range = clause.source_range();
            let start = line_column_to_byte(source, range.start())?;
            let end = line_column_to_byte(source, range.end())?;
            let name_start =
                line_column_to_byte(source, clause.rule().item().sig.ident.span().start())?;
            if !(start <= name_start && name_start < end) {
                return Err(FormatError::new(
                    FormatErrorKind::DslSyntax,
                    "a readable clause name escaped its complete source range",
                ));
            }
            Ok(ClauseSource {
                start,
                end,
                name_start,
                clause,
            })
        })
        .collect()
}

fn line_comments(_source: &str, trivia: &TriviaTable) -> Vec<SourceRange> {
    trivia
        .trivia()
        .iter()
        .filter(|item| matches!(item.kind(), TriviaKind::LineComment(_)))
        .map(|item| item.range())
        .collect()
}

fn render_header(source: &str) -> Result<Vec<String>, FormatError> {
    let stream = TokenStream::from_str(source).map_err(|error| {
        FormatError::new(
            FormatErrorKind::DslSyntax,
            format!("cannot tokenize a `k::rules!` header: {error}"),
        )
    })?;
    let mut statements = Vec::new();
    let mut current = Vec::new();
    for token in stream {
        let is_semicolon = matches!(&token, TokenTree::Punct(punct) if punct.as_char() == ';');
        current.push(token);
        if is_semicolon {
            statements.push(render_tokens(&current));
            current.clear();
        }
    }
    if !current.is_empty() {
        return Err(FormatError::new(
            FormatErrorKind::DslSyntax,
            "a `k::rules!` header has unterminated tokens",
        ));
    }
    Ok(statements)
}

fn render_clause(
    source: &str,
    clause_source: &ClauseSource<'_>,
    comments: &[SourceRange],
    block: &RuleBlock,
) -> Result<Vec<String>, FormatError> {
    let attributes = source_without_comments(
        source,
        clause_source.start,
        clause_source.name_start,
        comments,
    );
    let mut attribute_lines = attributes
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(ToOwned::to_owned)
        .collect::<Vec<_>>();
    let tokens = TokenStream::from_str(&source[clause_source.name_start..clause_source.end])
        .map_err(|error| {
            FormatError::new(
                FormatErrorKind::DslSyntax,
                format!("cannot tokenize a readable rule clause: {error}"),
            )
        })?;
    let parts = split_clause(tokens)?;
    let mut lines = if block.is_configuration() {
        render_machine_clause(&parts)?
    } else {
        vec![render_single_clause(&parts)]
    };
    attribute_lines.append(&mut lines);
    let _ = clause_source.clause;
    Ok(attribute_lines)
}

struct ClauseParts {
    label: Vec<TokenTree>,
    pattern: Vec<TokenTree>,
    result: Vec<TokenTree>,
    conditions: Option<Vec<TokenTree>>,
}

fn split_clause(stream: TokenStream) -> Result<ClauseParts, FormatError> {
    let mut tokens = stream.into_iter().collect::<Vec<_>>();
    if !matches!(tokens.last(), Some(TokenTree::Punct(punct)) if punct.as_char() == ';') {
        return Err(FormatError::new(
            FormatErrorKind::DslSyntax,
            "a readable rule clause does not end in `;`",
        ));
    }
    tokens.pop();
    let colon = tokens
        .iter()
        .position(|token| matches!(token, TokenTree::Punct(punct) if punct.as_char() == ':'))
        .ok_or_else(|| {
            FormatError::new(
                FormatErrorKind::DslSyntax,
                "a readable rule clause has no label colon",
            )
        })?;
    let arrow = tokens
        .windows(2)
        .position(|pair| {
            matches!(&pair[0], TokenTree::Punct(punct) if punct.as_char() == '=')
                && matches!(&pair[1], TokenTree::Punct(punct) if punct.as_char() == '>')
        })
        .ok_or_else(|| {
            FormatError::new(
                FormatErrorKind::DslSyntax,
                "a readable rule clause has no `=>`",
            )
        })?;
    if colon >= arrow {
        return Err(FormatError::new(
            FormatErrorKind::DslSyntax,
            "a readable rule clause has an invalid label or arrow",
        ));
    }
    let where_index = tokens[arrow + 2..]
        .iter()
        .position(|token| matches!(token, TokenTree::Ident(ident) if ident == "where"))
        .map(|index| arrow + 2 + index);
    let result_end = where_index.unwrap_or(tokens.len());
    Ok(ClauseParts {
        label: tokens[..colon].to_vec(),
        pattern: tokens[colon + 1..arrow].to_vec(),
        result: tokens[arrow + 2..result_end].to_vec(),
        conditions: where_index.map(|index| tokens[index + 1..].to_vec()),
    })
}

fn render_single_clause(parts: &ClauseParts) -> String {
    // Padding is completed table-wide after all single-cell rows are known.
    format!(
        "{}\u{0}{}\u{0}{}\u{0}{}",
        render_tokens(&parts.label),
        render_tokens(&parts.pattern),
        render_tokens(&parts.result),
        parts
            .conditions
            .as_ref()
            .map_or_else(String::new, |tokens| render_tokens(tokens))
    )
}

fn render_machine_clause(parts: &ClauseParts) -> Result<Vec<String>, FormatError> {
    let pattern = record_fields(&parts.pattern, "machine subject")?;
    let result = record_fields(&parts.result, "machine result")?;
    let mut lines = vec![format!("{}: {{", render_tokens(&parts.label))];
    lines.extend(pattern.into_iter().map(|field| format!("    {field}")));
    lines.push("} => {".to_owned());
    lines.extend(result.into_iter().map(|field| format!("    {field}")));
    lines.push("}".to_owned());
    if let Some(conditions) = &parts.conditions {
        lines.push(format!("where {};", render_tokens(conditions)));
    } else if let Some(last) = lines.last_mut() {
        last.push(';');
    }
    Ok(lines)
}

fn record_fields(tokens: &[TokenTree], context: &str) -> Result<Vec<String>, FormatError> {
    let [TokenTree::Group(group)] = tokens else {
        return Err(FormatError::new(
            FormatErrorKind::DslSyntax,
            format!("a {context} must be a brace-delimited cell record"),
        ));
    };
    if group.delimiter() != Delimiter::Brace {
        return Err(FormatError::new(
            FormatErrorKind::DslSyntax,
            format!("a {context} must use braces"),
        ));
    }
    let mut fields = Vec::new();
    let mut current = Vec::new();
    for token in group.stream() {
        let comma = matches!(&token, TokenTree::Punct(punct) if punct.as_char() == ',');
        current.push(token);
        if comma {
            fields.push(render_tokens(&current));
            current.clear();
        }
    }
    if !current.is_empty() {
        fields.push(render_tokens(&current));
    }
    Ok(fields)
}

fn align_single_clauses(clauses: &mut [RenderedClause]) {
    let rows = clauses
        .iter()
        .filter_map(|clause| clause.lines.last())
        .filter_map(|line| {
            let mut parts = line.split('\u{0}');
            Some((parts.next()?, parts.next()?, parts.next()?, parts.next()?))
        })
        .collect::<Vec<_>>();
    if rows.is_empty() {
        return;
    }
    let label_width = rows
        .iter()
        .map(|row| row.0.chars().count())
        .max()
        .unwrap_or(0);
    let pattern_width = rows
        .iter()
        .map(|row| row.1.chars().count())
        .max()
        .unwrap_or(0);
    let result_width = rows
        .iter()
        .map(|row| row.2.chars().count())
        .max()
        .unwrap_or(0);
    for clause in clauses {
        let Some(line) = clause.lines.last_mut() else {
            continue;
        };
        let fields = line.split('\u{0}').collect::<Vec<_>>();
        if fields.len() != 4 {
            continue;
        }
        let mut rendered = format!(
            "{:<label_width$}: {:<pattern_width$} => {}",
            fields[0], fields[1], fields[2]
        );
        if fields[3].is_empty() {
            rendered.push(';');
        } else {
            write!(
                rendered,
                "{:<padding$} where {};",
                "",
                fields[3],
                padding = result_width.saturating_sub(fields[2].chars().count())
            )
            .expect("writing to a String cannot fail");
        }
        *line = rendered;
    }
}

fn align_trailing_comments(clauses: &mut [RenderedClause], style: TrailingCommentStyle) {
    align_single_clauses(clauses);
    let target = clauses
        .iter()
        .filter(|clause| clause.trailing.is_some())
        .filter_map(|clause| clause.lines.last())
        .map(|line| line.chars().count())
        .max()
        .unwrap_or(0)
        + 2;
    for clause in clauses {
        let Some(comment) = clause.trailing.take() else {
            continue;
        };
        let Some(line) = clause.lines.last_mut() else {
            continue;
        };
        let spaces = match style {
            TrailingCommentStyle::AlignedColumn => target.saturating_sub(line.chars().count()),
            TrailingCommentStyle::FixedGutter => 2,
        };
        line.push_str(&" ".repeat(spaces));
        line.push_str(comment.trim_start());
    }
}

fn append_comment(lines: &mut [String], comment: &str, style: TrailingCommentStyle) {
    if let Some(line) = lines.last_mut() {
        let spaces = match style {
            TrailingCommentStyle::AlignedColumn | TrailingCommentStyle::FixedGutter => 2,
        };
        line.push_str(&" ".repeat(spaces));
        line.push_str(comment.trim_start());
    }
}

fn render_gap(source: &str, start: usize, end: usize, comments: &[SourceRange]) -> GapLayout {
    if start >= end {
        return GapLayout::default();
    }
    let mut layout = GapLayout::default();
    let mut line_start = start;
    for (line_index, line_end) in source[start..end]
        .match_indices('\n')
        .map(|(offset, _)| start + offset)
        .chain(std::iter::once(end))
        .enumerate()
    {
        let comment = comments
            .iter()
            .find(|comment| comment.start() >= line_start && comment.start() <= line_end)
            .and_then(|range| range.text(source))
            .map(ToOwned::to_owned);
        let is_last = line_end == end;
        if line_index == 0 {
            if let Some(comment) = comment {
                layout.trailing = Some(comment);
            }
        } else if let Some(comment) = comment {
            layout.leading.push(GapEvent::Comment(comment));
        } else if !is_last && source[line_start..line_end].trim().is_empty() {
            layout.leading.push(GapEvent::Blank);
        }
        if is_last {
            break;
        }
        line_start = line_end + 1;
    }
    layout
}

fn source_without_comments(
    source: &str,
    start: usize,
    end: usize,
    comments: &[SourceRange],
) -> String {
    let mut output = String::with_capacity(end.saturating_sub(start));
    let mut cursor = start;
    for comment in comments
        .iter()
        .filter(|comment| comment.start() >= start && comment.end() <= end)
    {
        output.push_str(&source[cursor..comment.start()]);
        output.extend(
            source[comment.start()..comment.end()]
                .chars()
                .map(|character| if character == '\n' { '\n' } else { ' ' }),
        );
        cursor = comment.end();
    }
    output.push_str(&source[cursor..end]);
    output
}

#[derive(Clone, Debug)]
enum AtomKind {
    Word,
    Group(Delimiter),
    Punctuation(String),
}

#[derive(Clone, Debug)]
struct Atom {
    text: String,
    kind: AtomKind,
}

fn render_tokens(tokens: &[TokenTree]) -> String {
    let stream = TokenStream::from_iter(tokens.iter().cloned());
    let atoms = atoms(stream);
    let mut output = String::new();
    for (index, atom) in atoms.iter().enumerate() {
        if index > 0 && needs_space(&atoms[index - 1], atom) {
            output.push(' ');
        }
        output.push_str(&atom.text);
    }
    output
}

fn atoms(stream: TokenStream) -> Vec<Atom> {
    let tokens = stream.into_iter().collect::<Vec<_>>();
    let mut output = Vec::new();
    let mut index = 0_usize;
    while index < tokens.len() {
        match &tokens[index] {
            TokenTree::Group(group) => {
                let inner = render_tokens(&group.stream().into_iter().collect::<Vec<_>>());
                let text = match group.delimiter() {
                    Delimiter::Parenthesis => format!("({inner})"),
                    Delimiter::Bracket => format!("[{inner}]"),
                    Delimiter::Brace if inner.is_empty() => "{}".to_owned(),
                    Delimiter::Brace => format!("{{ {inner} }}"),
                    Delimiter::None => inner,
                };
                output.push(Atom {
                    text,
                    kind: AtomKind::Group(group.delimiter()),
                });
                index += 1;
            }
            TokenTree::Ident(ident) => {
                output.push(Atom {
                    text: ident.to_string(),
                    kind: AtomKind::Word,
                });
                index += 1;
            }
            TokenTree::Literal(literal) => {
                output.push(Atom {
                    text: literal.to_string(),
                    kind: AtomKind::Word,
                });
                index += 1;
            }
            TokenTree::Punct(punct) => {
                let mut text = punct.as_char().to_string();
                index += 1;
                if punct.spacing() == Spacing::Joint
                    && let Some(TokenTree::Punct(next)) = tokens.get(index)
                    && punctuation_pair(punct.as_char(), next.as_char())
                {
                    text.push(next.as_char());
                    index += 1;
                    if text == ".."
                        && next.spacing() == Spacing::Joint
                        && matches!(tokens.get(index), Some(TokenTree::Punct(last)) if last.as_char() == '=')
                    {
                        text.push('=');
                        index += 1;
                    }
                }
                output.push(Atom {
                    kind: AtomKind::Punctuation(text.clone()),
                    text,
                });
            }
        }
    }
    output
}

fn punctuation_pair(first: char, second: char) -> bool {
    matches!(
        (first, second),
        (':', ':')
            | ('=' | '-', '>')
            | ('.', '.')
            | ('&', '&' | '=')
            | ('|', '|' | '=')
            | (
                '=' | '!' | '<' | '>' | '+' | '-' | '*' | '/' | '%' | '^',
                '='
            )
    )
}

fn needs_space(previous: &Atom, current: &Atom) -> bool {
    if matches!(&current.kind, AtomKind::Punctuation(value) if matches!(value.as_str(), "," | ";" | ":" | "::" | "." | "?"))
    {
        return false;
    }
    if matches!(&previous.kind, AtomKind::Punctuation(value) if matches!(value.as_str(), "::" | "." | "#" | "$" | "!"))
    {
        return false;
    }
    if matches!(&current.kind, AtomKind::Punctuation(value) if value == "!") {
        return false;
    }
    if matches!(
        (&previous.kind, &current.kind),
        (
            AtomKind::Word | AtomKind::Group(_),
            AtomKind::Group(Delimiter::Parenthesis | Delimiter::Bracket)
        )
    ) {
        return false;
    }
    if matches!(&previous.kind, AtomKind::Punctuation(value) if matches!(value.as_str(), "&" | "*"))
    {
        return false;
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn formats_single_cell_table_with_global_alignment() {
        let source = r"
            for Expr;
            use Op::*;

            tiny:A(x)=>x;
            longer: Pair(lhs,rhs)=>k![lhs,rhs] where lhs: Value;
        ";
        let output = format_rule_body(source, 0, "    ", TrailingCommentStyle::AlignedColumn)
            .expect("format body");
        let actual = format!("body:\n{output}");
        expect_test::expect![[r"
            body:
                for Expr;
                use Op::*;

                tiny  : A(x)           => x;
                longer: Pair(lhs, rhs) => k![lhs, rhs] where lhs: Value;"]]
        .assert_eq(&actual);
    }

    #[test]
    fn formats_machine_records_one_cell_per_line() {
        let source = r"
            for Machine;
            use Op::Pair;

            apply:{env:e,k:[Pair(name,value),..],}=>{k:[..],env:map::update(e,name,value),}where value:Value;
        ";
        let output = format_rule_body(source, 0, "    ", TrailingCommentStyle::AlignedColumn)
            .expect("format body");
        let actual = format!("body:\n{output}");
        expect_test::expect![[r"
            body:
                for Machine;
                use Op::Pair;

                apply: {
                    env: e,
                    k: [Pair(name, value), ..],
                } => {
                    k: [..],
                    env: map::update(e, name, value),
                }
                where value: Value;"]]
        .assert_eq(&actual);
    }
}
