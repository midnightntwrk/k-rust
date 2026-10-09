use std::iter::FromIterator;
use std::str::FromStr;

use krs_syntax::{RuleBlock, SourceRange, TokenRange, TriviaKind, TriviaTable};
use proc_macro2::{Delimiter, Spacing, TokenStream, TokenTree};
use unicode_width::UnicodeWidthStr;

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
struct TableRow {
    label: String,
    pattern: String,
    result: String,
    conditions: Option<String>,
}

#[derive(Clone, Debug)]
enum ClauseBody {
    Row(TableRow),
    Lines(Vec<String>),
}

#[derive(Clone, Debug)]
struct RenderedClause {
    leading: Vec<GapEvent>,
    attributes: Vec<String>,
    body: ClauseBody,
    trailing: Option<String>,
}

struct AlignedClause {
    leading: Vec<GapEvent>,
    lines: Vec<String>,
    trailing: Option<String>,
}

/// Formats one complete `rules!` body at its Rustfmt-selected indentation.
#[expect(
    clippy::too_many_lines,
    reason = "One ordered pass preserves trivia geometry around every clause."
)]
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
    let clauses = clause_sources(&block)?;
    let comments = line_comments(&trivia);
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
        let (attributes, body) = render_clause(source, clause_source, &comments, &block)?;
        rendered.push(RenderedClause {
            leading,
            attributes,
            body,
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
    let mut rendered = align_single_clauses(rendered);
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

    Ok(lines
        .into_iter()
        .map(|line| {
            if line.is_empty() {
                line
            } else {
                format!("{indent}{line}")
            }
        })
        .collect::<Vec<_>>()
        .join("\n"))
}

fn clause_sources(block: &RuleBlock) -> Result<Vec<ClauseSource<'_>>, FormatError> {
    block
        .clauses()
        .iter()
        .map(|clause| {
            let range = clause.source_range();
            let start = range.first().byte_range().start;
            let end = range.last().byte_range().end;
            let name_start = clause.layout().label.first().byte_range().start;
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

fn line_comments(trivia: &TriviaTable) -> Vec<SourceRange> {
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
) -> Result<(Vec<String>, ClauseBody), FormatError> {
    let attributes = source_without_comments(
        source,
        clause_source.start,
        clause_source.name_start,
        comments,
    );
    let attribute_lines = attributes
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(ToOwned::to_owned)
        .collect::<Vec<_>>();
    let layout = clause_source.clause.layout();
    let parts = ClauseParts {
        label: clause_tokens(source, layout.label)?,
        pattern: clause_tokens(source, layout.pattern)?,
        result: clause_tokens(source, layout.result)?,
        conditions: layout
            .conditions
            .map(|range| clause_tokens(source, range))
            .transpose()?,
    };
    let body = if block.is_configuration() {
        ClauseBody::Lines(render_machine_clause(&parts)?)
    } else {
        ClauseBody::Row(render_single_clause(&parts))
    };
    Ok((attribute_lines, body))
}

fn clause_tokens(source: &str, range: TokenRange) -> Result<Vec<TokenTree>, FormatError> {
    let bytes = range.first().byte_range().start..range.last().byte_range().end;
    TokenStream::from_str(&source[bytes])
        .map(|stream| stream.into_iter().collect())
        .map_err(|error| {
            FormatError::new(
                FormatErrorKind::DslSyntax,
                format!("cannot tokenize a readable rule clause component: {error}"),
            )
        })
}

struct ClauseParts {
    label: Vec<TokenTree>,
    pattern: Vec<TokenTree>,
    result: Vec<TokenTree>,
    conditions: Option<Vec<TokenTree>>,
}

fn render_single_clause(parts: &ClauseParts) -> TableRow {
    TableRow {
        label: render_tokens(&parts.label),
        pattern: render_tokens(&parts.pattern),
        result: render_tokens(&parts.result),
        conditions: parts
            .conditions
            .as_ref()
            .map(|tokens| render_tokens(tokens)),
    }
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

fn align_single_clauses(clauses: Vec<RenderedClause>) -> Vec<AlignedClause> {
    let mut label_width = 0;
    let mut pattern_width = 0;
    let mut result_width = 0;
    for clause in &clauses {
        if let ClauseBody::Row(row) = &clause.body {
            label_width = label_width.max(row.label.width());
            pattern_width = pattern_width.max(row.pattern.width());
            result_width = result_width.max(row.result.width());
        }
    }
    clauses
        .into_iter()
        .map(|clause| {
            let mut lines = clause.attributes;
            match clause.body {
                ClauseBody::Row(row) => {
                    let mut rendered = format!(
                        "{}{}: {}{} => {}",
                        row.label,
                        " ".repeat(label_width - row.label.width()),
                        row.pattern,
                        " ".repeat(pattern_width - row.pattern.width()),
                        row.result,
                    );
                    if let Some(conditions) = row.conditions {
                        rendered.push_str(&" ".repeat(result_width - row.result.width()));
                        rendered.push_str(" where ");
                        rendered.push_str(&conditions);
                    }
                    rendered.push(';');
                    lines.push(rendered);
                }
                ClauseBody::Lines(body) => lines.extend(body),
            }
            AlignedClause {
                leading: clause.leading,
                lines,
                trailing: clause.trailing,
            }
        })
        .collect()
}

fn align_trailing_comments(clauses: &mut [AlignedClause], style: TrailingCommentStyle) {
    let target = clauses
        .iter()
        .filter(|clause| clause.trailing.is_some())
        .filter_map(|clause| clause.lines.last())
        .map(|line| line.width())
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
            TrailingCommentStyle::AlignedColumn => target.saturating_sub(line.width()),
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
            // A minus after an operator or at the start, followed by a literal,
            // is the sign of a negative literal such as `-1`: keep it attached.
            TokenTree::Punct(punct)
                if punct.as_char() == '-'
                    && matches!(tokens.get(index + 1), Some(TokenTree::Literal(_)))
                    && output.last().is_none_or(|atom: &Atom| {
                        matches!(atom.kind, AtomKind::Punctuation(_))
                    }) =>
            {
                let Some(TokenTree::Literal(literal)) = tokens.get(index + 1) else {
                    unreachable!("the guard requires a following literal");
                };
                output.push(Atom {
                    text: format!("-{literal}"),
                    kind: AtomKind::Word,
                });
                index += 2;
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

    /// A term block (K's `#let`, KF-032) stays on its clause's line, its
    /// statements spaced like Rust, and formats idempotently.
    #[test]
    fn let_blocks_stay_in_the_table_and_format_idempotently() {
        let source = r"
            for Exp;
            use ExpSyntax::*;

            swap:Swap{e}=>{let Pair(x,y)=e;let z:Int=x;Pair(y,z)};
            shadow: Shadow { e } => Pair({ let e = Pair(e, e); e }, e);
        ";
        let output = format_rule_body(source, 0, "    ", TrailingCommentStyle::AlignedColumn)
            .expect("format body");
        let actual = format!("body:\n{output}");
        expect_test::expect![[r"
            body:
                for Exp;
                use ExpSyntax::*;

                swap  : Swap { e }   => { let Pair(x, y) = e; let z: Int = x; Pair(y, z) };
                shadow: Shadow { e } => Pair({ let e = Pair(e, e); e }, e);"]]
        .assert_eq(&actual);
        let again = format_rule_body(&output, 0, "    ", TrailingCommentStyle::AlignedColumn)
            .expect("format formatted body");
        assert_eq!(again, output);
    }

    #[test]
    fn negative_literals_keep_their_sign_attached_and_format_idempotently() {
        let source = r"
            for Expr;
            use Op::*;

            div_by_minus_one:Div{lhs,rhs:- 1}=>int::sub(0,lhs);
            sign: Sgn(-1) => -1;
        ";
        let output = format_rule_body(source, 0, "    ", TrailingCommentStyle::AlignedColumn)
            .expect("format body");
        let actual = format!("body:\n{output}");
        expect_test::expect![[r"
            body:
                for Expr;
                use Op::*;

                div_by_minus_one: Div { lhs, rhs: -1 } => int::sub(0, lhs);
                sign            : Sgn(-1)              => -1;"]]
        .assert_eq(&actual);
        let again = format_rule_body(&output, 0, "    ", TrailingCommentStyle::AlignedColumn)
            .expect("format formatted body");
        assert_eq!(again, output);
    }

    #[test]
    #[expect(
        clippy::unicode_not_nfc,
        reason = "Decomposed labels exercise zero-width combining marks."
    )]
    fn aligns_unicode_table_and_trailing_comments_by_display_width() {
        // Term validation rejects string literals, so this test exercises rendering and alignment directly.
        let tokens = |source: &str| {
            TokenStream::from_str(source)
                .expect("tokenize component")
                .into_iter()
                .collect::<Vec<_>>()
        };
        let row = |label, result, conditions: Option<&str>, comment: &str| RenderedClause {
            leading: Vec::new(),
            attributes: Vec::new(),
            body: ClauseBody::Row(render_single_clause(&ClauseParts {
                label: tokens(label),
                pattern: tokens("A(x)"),
                result: tokens(result),
                conditions: conditions.map(tokens),
            })),
            trailing: Some(comment.to_owned()),
        };
        let mut clauses = align_single_clauses(vec![
            row("wide", r#""漢字""#, Some("x: Value"), "// wide"),
            row("café", "x", Some("x: Value"), "// combining"),
            row("ascii", "x", None, "// ascii"),
        ]);
        align_trailing_comments(&mut clauses, TrailingCommentStyle::AlignedColumn);
        let output = clauses
            .into_iter()
            .flat_map(|clause| clause.lines)
            .collect::<Vec<_>>()
            .join("\n");
        expect_test::expect![[r#"
            wide : A(x) => "漢字" where x: Value;  // wide
            café : A(x) => x      where x: Value;  // combining
            ascii: A(x) => x;                      // ascii"#]]
        .assert_eq(&output);
    }

    #[test]
    #[expect(
        clippy::unicode_not_nfc,
        reason = "The parser must preserve the decomposed label."
    )]
    fn formats_wide_and_combining_labels_by_display_width() {
        let source = "for Expr;\n\
                      漢字: A(x) => x where x: Value; // wide\n\
                      cafe\u{301}: Pair(x, y) => y; // combining\n\
                      ascii: A(x) => Pair(x, x) where x: Value; // ascii\n";
        let output = format_rule_body(source, 0, "", TrailingCommentStyle::AlignedColumn)
            .expect("format body");
        expect_test::expect![[r"
            for Expr;
            漢字 : A(x)       => x          where x: Value;  // wide
            café : Pair(x, y) => y;                          // combining
            ascii: A(x)       => Pair(x, x) where x: Value;  // ascii"]]
        .assert_eq(&output);
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
