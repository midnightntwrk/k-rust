use std::str::FromStr;

use krs_syntax::{RuleBlock, RuleClauseLayout, SourceRange, TokenRange, TriviaKind, TriviaTable};
use proc_macro2::{Delimiter, TokenStream, TokenTree};
use unicode_width::UnicodeWidthStr;

use crate::layout::{self, Comments, Component, Context, Doc, INDENT};
use crate::{FormatError, FormatErrorKind};

/// Canonical placement policy for comments trailing rule clauses.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TrailingCommentStyle {
    /// Put every trailing comment in one table-wide aligned column.
    AlignedColumn,
    /// Put every trailing comment two spaces after its clause terminator.
    FixedGutter,
}

/// How a macro body is laid out: its trailing comments and its line width.
#[derive(Clone, Copy, Debug)]
pub(crate) struct BodyLayout {
    pub(crate) trailing_comments: TrailingCommentStyle,
    /// The maximum line width, indentation included.
    pub(crate) max_width: usize,
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
struct ClauseSource {
    start: usize,
    end: usize,
    name_start: usize,
    layout: RuleClauseLayout,
    /// A cell-record clause, laid out one cell per line.
    machine: bool,
}

/// One table row: its one-line components when it has no comment that
/// forces a break, and its layout when it does not fit on one line.
#[derive(Clone, Debug)]
struct TableRow {
    label: String,
    flat: Option<FlatRow>,
    lines: Doc,
}

#[derive(Clone, Debug)]
struct FlatRow {
    pattern: String,
    result: String,
    conditions: Option<String>,
}

impl TableRow {
    fn unaligned(&self, flat: &FlatRow) -> String {
        let mut line = format!("{}: {} => {}", self.label, flat.pattern, flat.result);
        if let Some(conditions) = &flat.conditions {
            line.push_str(" where ");
            line.push_str(conditions);
        }
        line.push(';');
        line
    }
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
pub(crate) fn format_rule_body(
    source: &str,
    source_offset: usize,
    indent: &str,
    layout: BodyLayout,
) -> Result<String, FormatError> {
    let (block, trivia) = krs_syntax::parse_rule_block_source_with_trivia(source)
        .map_err(|error| body_syntax_error("k::rules!", source_offset, &error))?;
    let clauses = clause_sources(&block)?;
    format_clauses(source, indent, layout, &trivia, &clauses, "k::rules!")
}

/// Formats one complete `claims!` body at its Rustfmt-selected indentation,
/// with the layout of a `rules!` block of cell records (F7).
pub(crate) fn format_claim_body(
    source: &str,
    source_offset: usize,
    indent: &str,
    layout: BodyLayout,
) -> Result<String, FormatError> {
    let (block, trivia) = krs_syntax::parse_claim_block_source_with_trivia(source)
        .map_err(|error| body_syntax_error("k::claims!", source_offset, &error))?;
    let clauses = clause_sources(block.block())?;
    format_clauses(source, indent, layout, &trivia, &clauses, "k::claims!")
}

/// Formats one complete `equations!` body at its Rustfmt-selected
/// indentation, with the `rules!` table layout: one row per line, labels,
/// `=>`, and results aligned across the table.
pub(crate) fn format_equation_body(
    source: &str,
    source_offset: usize,
    indent: &str,
    layout: BodyLayout,
) -> Result<String, FormatError> {
    let (table, trivia) = krs_syntax::parse_equation_table_source_with_trivia(source)
        .map_err(|error| body_syntax_error("k::equations!", source_offset, &error))?;
    let clauses = table
        .rows()
        .iter()
        .map(|row| {
            let range = row.source_range();
            let layout = row.layout();
            ClauseSource {
                start: range.first().byte_range().start,
                end: range.last().byte_range().end,
                name_start: layout.label.first().byte_range().start,
                layout,
                machine: false,
            }
        })
        .collect::<Vec<_>>();
    format_clauses(source, indent, layout, &trivia, &clauses, "k::equations!")
}

fn body_syntax_error(
    macro_name: &str,
    source_offset: usize,
    error: &krs_syntax::SyntaxError,
) -> FormatError {
    let range = error.source_range().map_or_else(String::new, |range| {
        format!(
            " at bytes {}..{}",
            source_offset + range.start(),
            source_offset + range.end()
        )
    });
    FormatError::new(
        FormatErrorKind::DslSyntax,
        format!("cannot parse `{macro_name}` body{range}: {error}"),
    )
}

/// The display width of an indentation, a tab counting as one level.
fn indent_width(indent: &str) -> usize {
    indent
        .chars()
        .map(|character| if character == '\t' { INDENT } else { 1 })
        .sum()
}

fn format_clauses(
    source: &str,
    indent: &str,
    body_layout: BodyLayout,
    trivia: &TriviaTable,
    clauses: &[ClauseSource],
    macro_name: &str,
) -> Result<String, FormatError> {
    let width = body_layout.max_width.saturating_sub(indent_width(indent));
    let comments = line_comments(trivia);
    let first_clause = clauses.first().ok_or_else(|| {
        FormatError::new(
            FormatErrorKind::DslSyntax,
            format!("a `{macro_name}` block must contain at least one clause"),
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
                format!("a `{macro_name}` block has no parseable header"),
            )
        })?;

    let mut header_lines = comments
        .iter()
        .filter(|comment| comment.end() <= header_end)
        .filter_map(|comment| comment.text(source))
        .map(|comment| comment.trim_start().to_owned())
        .collect::<Vec<_>>();
    header_lines.extend(render_header(&source[..header_end], width)?);
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

        let parts = clause_parts(source, clause_source.layout)?;
        let (moved, keep_in_place) = moved_comments(source, clause_source, &parts, &comments);
        let mut leading = gap.leading;
        leading.extend(moved);
        let attributes = render_attributes(source, clause_source, &comments, width);
        let in_place = if keep_in_place {
            Comments::new(source, &comments)
        } else {
            Comments::none()
        };
        let body = if clause_source.machine {
            ClauseBody::Lines(layout::print(&machine_clause(&parts, in_place)?, width))
        } else {
            ClauseBody::Row(table_row(&parts, in_place))
        };
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
    let mut rendered = align_single_clauses(rendered, width);
    align_trailing_comments(&mut rendered, body_layout.trailing_comments);

    Ok(join_lines(header_lines, rendered, footer.leading, indent))
}

/// The body's lines at `indent`: the header, then each clause after the
/// blank lines and comments before it, then those after the last.
fn join_lines(
    header: Vec<String>,
    clauses: Vec<AlignedClause>,
    footer: Vec<GapEvent>,
    indent: &str,
) -> String {
    let gap = |lines: &mut Vec<String>, events: Vec<GapEvent>| {
        for event in events {
            match event {
                GapEvent::Blank => lines.push(String::new()),
                GapEvent::Comment(comment) => lines.push(comment.trim_start().to_owned()),
            }
        }
    };
    let mut lines = header;
    for clause in clauses {
        gap(&mut lines, clause.leading);
        lines.extend(clause.lines);
    }
    gap(&mut lines, footer);
    lines
        .into_iter()
        .map(|line| {
            if line.is_empty() {
                line
            } else {
                format!("{indent}{line}")
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// The comments of a clause that move before it, and whether the others
/// keep their place. A comment inside a delimited group keeps its place
/// there; any other comment of the clause moves before it. When one of
/// those follows a comment kept in place, every comment of the clause moves,
/// so none is reordered.
fn moved_comments(
    source: &str,
    clause_source: &ClauseSource,
    parts: &ClauseParts,
    comments: &[SourceRange],
) -> (Vec<GapEvent>, bool) {
    let interiors = parts.group_interiors();
    let clause_comments = comments
        .iter()
        .filter(|comment| {
            comment.start() >= clause_source.start && comment.end() <= clause_source.end
        })
        .collect::<Vec<_>>();
    let kept = |comment: &SourceRange| {
        interiors
            .iter()
            .any(|&(start, end)| start <= comment.start() && comment.end() <= end)
    };
    let keep_in_place = clause_comments
        .iter()
        .position(|comment| kept(comment))
        .is_none_or(|first| clause_comments[first..].iter().all(|comment| kept(comment)));
    let moved = clause_comments
        .iter()
        .filter(|comment| !keep_in_place || !kept(comment))
        .filter_map(|comment| comment.text(source))
        .map(|comment| GapEvent::Comment(comment.to_owned()))
        .collect();
    (moved, keep_in_place)
}

fn clause_sources(block: &RuleBlock) -> Result<Vec<ClauseSource>, FormatError> {
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
                layout: clause.layout(),
                machine: block.is_configuration(),
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

fn render_header(source: &str, width: usize) -> Result<Vec<String>, FormatError> {
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
            let statement = Component {
                tokens: std::mem::take(&mut current),
                offset: 0,
            };
            statements.extend(layout::print(
                &layout::sequence(&statement, Context::Expression, Comments::none()),
                width,
            ));
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

/// A clause's attributes as written, their continuation lines keeping
/// their indentation relative to the clause, so a multi-line `requires`
/// keeps its layout at the table's indentation. A one-line attribute too
/// long for the width breaks inside its arguments.
fn render_attributes(
    source: &str,
    clause_source: &ClauseSource,
    comments: &[SourceRange],
    width: usize,
) -> Vec<String> {
    let attributes = source_without_comments(
        source,
        clause_source.start,
        clause_source.name_start,
        comments,
    );
    let line_start = source[..clause_source.start]
        .rfind('\n')
        .map_or(0, |newline| newline + 1);
    let column = clause_source.start - line_start;
    let lines = attributes
        .lines()
        .map(|line| strip_indentation(line, column).trim_end())
        .filter(|line| !line.is_empty())
        .map(ToOwned::to_owned)
        .collect::<Vec<_>>();
    lines
        .into_iter()
        .flat_map(|line| wrapped_attribute(&line, width).unwrap_or_else(|| vec![line]))
        .collect()
}

/// An attribute line `#[path(arguments)]` laid out in `width` columns, when
/// it is one attribute too long for them.
fn wrapped_attribute(line: &str, width: usize) -> Option<Vec<String>> {
    if line.width() <= width || !line.starts_with("#[") {
        return None;
    }
    let tokens = TokenStream::from_str(line)
        .ok()?
        .into_iter()
        .collect::<Vec<_>>();
    let [TokenTree::Punct(hash), TokenTree::Group(group)] = tokens.as_slice() else {
        return None;
    };
    if hash.as_char() != '#' || group.delimiter() != Delimiter::Bracket {
        return None;
    }
    let inner = Component {
        tokens: group.stream().into_iter().collect(),
        offset: 0,
    };
    let doc = Doc::Concat(vec![
        Doc::text("#["),
        layout::sequence(&inner, Context::Expression, Comments::none()),
        Doc::text("]"),
    ]);
    Some(layout::print(&doc, width))
}

fn clause_tokens(source: &str, range: TokenRange) -> Result<Component, FormatError> {
    let bytes = range.first().byte_range().start..range.last().byte_range().end;
    TokenStream::from_str(&source[bytes.clone()])
        .map(|stream| Component {
            tokens: stream.into_iter().collect(),
            offset: bytes.start,
        })
        .map_err(|error| {
            FormatError::new(
                FormatErrorKind::DslSyntax,
                format!("cannot tokenize a readable rule clause component: {error}"),
            )
        })
}

struct ClauseParts {
    label: Component,
    pattern: Component,
    result: Component,
    conditions: Option<Component>,
}

impl ClauseParts {
    fn group_interiors(&self) -> Vec<(usize, usize)> {
        [&self.pattern, &self.result]
            .into_iter()
            .chain(&self.conditions)
            .flat_map(Component::group_interiors)
            .collect()
    }
}

fn clause_parts(source: &str, layout: RuleClauseLayout) -> Result<ClauseParts, FormatError> {
    Ok(ClauseParts {
        label: clause_tokens(source, layout.label)?,
        pattern: clause_tokens(source, layout.pattern)?,
        result: clause_tokens(source, layout.result)?,
        conditions: layout
            .conditions
            .map(|range| clause_tokens(source, range))
            .transpose()?,
    })
}

/// `where` and its list, flat after a space or one binder per line.
fn conditions_doc(conditions: &Component, comments: Comments<'_>) -> Doc {
    Doc::Concat(vec![
        Doc::text("where"),
        layout::list(conditions, Context::Expression, comments),
    ])
}

fn table_row(parts: &ClauseParts, comments: Comments<'_>) -> TableRow {
    let label = layout::render(&parts.label.tokens);
    let pattern = layout::sequence(&parts.pattern, Context::Pattern, comments);
    let result = layout::sequence(&parts.result, Context::Expression, comments);
    let conditions = parts
        .conditions
        .as_ref()
        .map(|conditions| layout::list(conditions, Context::Expression, comments));
    let flat = (|| {
        Some(FlatRow {
            pattern: layout::flat(&pattern)?,
            result: layout::flat(&result)?,
            conditions: match &conditions {
                Some(conditions) => Some(layout::flat(conditions)?.trim_start().to_owned()),
                None => None,
            },
        })
    })();
    // A row too long for the table: the label on its own line, then the
    // pattern and result indented, `where` on a line of its own.
    let mut body = vec![Doc::Hard, pattern, Doc::Arm(Box::new(result))];
    if let Some(conditions) = &parts.conditions {
        body.push(Doc::Hard);
        body.push(conditions_doc(conditions, comments));
    }
    let lines = Doc::Concat(vec![
        Doc::text(format!("{label}:")),
        Doc::nest(INDENT, Doc::Concat(body)),
        Doc::text(";"),
    ]);
    TableRow { label, flat, lines }
}

/// A cell-record clause: each record one cell per line, `where` on a line
/// of its own.
fn machine_clause(parts: &ClauseParts, comments: Comments<'_>) -> Result<Doc, FormatError> {
    let record = |component: &Component, context, what: &str| {
        layout::delimited(component, context, comments, true)
            .filter(|_| {
                matches!(component.tokens.as_slice(), [TokenTree::Group(group)] if group.delimiter() == Delimiter::Brace)
            })
            .ok_or_else(|| {
                FormatError::new(
                    FormatErrorKind::DslSyntax,
                    format!("a machine {what} must be a brace-delimited cell record"),
                )
            })
    };
    let mut docs = vec![
        Doc::text(format!("{}: ", layout::render(&parts.label.tokens))),
        record(&parts.pattern, Context::Pattern, "subject")?,
        Doc::text(" => "),
        record(&parts.result, Context::Expression, "result")?,
    ];
    if let Some(conditions) = &parts.conditions {
        docs.push(Doc::Hard);
        docs.push(conditions_doc(conditions, comments));
    }
    docs.push(Doc::text(";"));
    Ok(Doc::Concat(docs))
}

/// Lays out a table's rows. A row that fits on one line joins the table's
/// alignment, unless aligning it would push it, or another row, past the
/// width: then the row whose removal narrows the columns most is set
/// unaligned on its own line, until every aligned row fits. A row that does
/// not fit on one line is laid out on its own and widens no column.
fn align_single_clauses(clauses: Vec<RenderedClause>, width: usize) -> Vec<AlignedClause> {
    let rows = clauses
        .iter()
        .map(|clause| match &clause.body {
            ClauseBody::Row(row) => row
                .flat
                .as_ref()
                .filter(|flat| row.unaligned(flat).width() <= width)
                .map(|flat| (row.label.width(), flat.clone())),
            ClauseBody::Lines(_) => None,
        })
        .collect::<Vec<_>>();
    let mut aligned = rows.iter().map(Option::is_some).collect::<Vec<_>>();
    let columns = |aligned: &[bool], skip: Option<usize>| {
        let mut widths = Columns::default();
        for (index, row) in rows.iter().enumerate() {
            if let Some((label, flat)) = row
                && aligned[index]
                && skip != Some(index)
            {
                widths.label = widths.label.max(*label);
                widths.pattern = widths.pattern.max(flat.pattern.width());
                widths.result = widths.result.max(flat.result.width());
            }
        }
        widths
    };
    loop {
        let widths = columns(&aligned, None);
        let overflows = rows.iter().enumerate().any(|(index, row)| {
            aligned[index]
                && row
                    .as_ref()
                    .is_some_and(|(_, flat)| widths.row_width(flat) > width)
        });
        if !overflows {
            break;
        }
        let narrowest = (0..rows.len())
            .filter(|&index| aligned[index])
            .min_by_key(|&index| columns(&aligned, Some(index)).sum())
            .expect("an overflowing row is aligned");
        aligned[narrowest] = false;
    }
    let widths = columns(&aligned, None);

    clauses
        .into_iter()
        .zip(aligned)
        .zip(rows.iter().map(Option::is_some))
        .map(|((clause, aligned), fits)| {
            let mut lines = clause.attributes;
            match clause.body {
                ClauseBody::Row(row) => match &row.flat {
                    Some(flat) if aligned => lines.push(widths.render(&row.label, flat)),
                    Some(flat) if fits => lines.push(row.unaligned(flat)),
                    _ => lines.extend(layout::print(&row.lines, width)),
                },
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

/// The column widths of a table's aligned rows.
#[derive(Clone, Copy, Debug, Default)]
struct Columns {
    label: usize,
    pattern: usize,
    result: usize,
}

impl Columns {
    fn sum(self) -> usize {
        self.label + self.pattern + self.result
    }

    fn row_width(self, flat: &FlatRow) -> usize {
        let head = self.label + ": ".len() + self.pattern + " => ".len();
        match &flat.conditions {
            Some(conditions) => head + self.result + " where ".len() + conditions.width() + 1,
            None => head + flat.result.width() + 1,
        }
    }

    fn render(self, label: &str, flat: &FlatRow) -> String {
        let mut rendered = format!(
            "{label}{}: {}{} => {}",
            " ".repeat(self.label - label.width()),
            flat.pattern,
            " ".repeat(self.pattern - flat.pattern.width()),
            flat.result,
        );
        if let Some(conditions) = &flat.conditions {
            rendered.push_str(&" ".repeat(self.result - flat.result.width()));
            rendered.push_str(" where ");
            rendered.push_str(conditions);
        }
        rendered.push(';');
        rendered
    }
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

/// `line` without up to `column` leading whitespace characters.
fn strip_indentation(line: &str, column: usize) -> &str {
    let mut rest = line;
    for _ in 0..column {
        match rest.strip_prefix(char::is_whitespace) {
            Some(stripped) => rest = stripped,
            None => break,
        }
    }
    rest
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

#[cfg(test)]
mod tests {
    use super::*;

    const LAYOUT: BodyLayout = BodyLayout {
        trailing_comments: TrailingCommentStyle::AlignedColumn,
        max_width: 100,
    };

    /// A turbofish on a parametric head (KF-027) keeps Rust's spelling,
    /// `Choose::<Exp>`, and formats idempotently.
    #[test]
    fn turbofish_heads_hug_their_sort_markers() {
        let source = r"
            for Exp;
            use ExpSyntax::*;

            pick: Pick(c, x, y) => crate::Choose :: < Exp > { cond: c, then_branch: x, else_branch: y };
            pair: Both(x) => Pair::<Int,dyn ExpSort>(x, x);
        ";
        let output = format_rule_body(source, 0, "    ", LAYOUT).expect("format body");
        let again = format_rule_body(&output, 0, "    ", LAYOUT).expect("format again");
        assert_eq!(output, again);
        let actual = format!("body:\n{output}");
        expect_test::expect![[r"
            body:
                for Exp;
                use ExpSyntax::*;

                pick: Pick(c, x, y) => crate::Choose::<Exp> { cond: c, then_branch: x, else_branch: y };
                pair: Both(x)       => Pair::<Int, dyn ExpSort>(x, x);"]].assert_eq(&actual);
    }

    #[test]
    fn formats_equation_tables_with_the_rule_table_layout() {
        let source = r"
            for R8;
            use Operand::*;
            use Register::*;
            r8_b:0=>Reg( B );
            // The pair.
            #[k::equation(owise)]
            r8_other : _ => HlIndirect;  // fallback
            pair:(0,-1)=>Reg(A);
        ";
        let output = format_equation_body(source, 0, "    ", LAYOUT).expect("format body");
        let again =
            format_equation_body(&output, 0, "    ", LAYOUT).expect("format formatted body");
        assert_eq!(output, again, "equation table formatting is idempotent");
        let actual = format!("body:\n{output}");
        expect_test::expect![[r"
            body:
                for R8;
                use Operand::*;
                use Register::*;
                r8_b    : 0       => Reg(B);
                // The pair.
                #[k::equation(owise)]
                r8_other: _       => HlIndirect;  // fallback
                pair    : (0, -1) => Reg(A);"]]
        .assert_eq(&actual);
    }

    /// A multi-line attribute keeps its own layout: its continuation lines
    /// keep their indentation relative to the row, at the table's.
    #[test]
    fn multi_line_attributes_keep_their_layout() {
        let source = r"
            for Code;
            #[k::requires(
                a.gt::<Int>(2)
                    || a.eq::<Int>(0)
            )]
            code_row: k::bits!('10 aa') => a;
            #[k::equation(owise)]
            code_other: n => 100;
        "
        .replace('\'', "\"");
        let output = format_equation_body(&source, 0, "    ", LAYOUT).expect("format body");
        let again =
            format_equation_body(&output, 0, "    ", LAYOUT).expect("format formatted body");
        assert_eq!(output, again, "attribute layout is idempotent");
        let actual = format!("body:\n{output}");
        expect_test::expect![[r#"
            body:
                for Code;
                #[k::requires(
                    a.gt::<Int>(2)
                        || a.eq::<Int>(0)
                )]
                code_row  : k::bits!("10 aa") => a;
                #[k::equation(owise)]
                code_other: n                 => 100;"#]]
        .assert_eq(&actual);
    }

    /// A bit template's field modifiers keep their bit ranges tight, as the
    /// ISA manuals write them.
    #[test]
    fn bit_template_modifiers_keep_tight_bit_ranges() {
        let source = r#"
            for Decode;
            beq: k::bits!("bbbbbbb sssss rrrrr 000 bbbbb 1100011", b : signed [ 12 | 10 : 5 | 4:1 | 11 ]) => Beq(r, s, b);
            addi: k::bits!("iiiiiiiiiiii rrrrr 000 ddddd 0010011", i: signed) => Addi(d, r, i);
        "#;
        let output = format_equation_body(source, 0, "    ", LAYOUT).expect("format body");
        let again =
            format_equation_body(&output, 0, "    ", LAYOUT).expect("format formatted body");
        assert_eq!(output, again, "modifier formatting is idempotent");
        let actual = format!("body:\n{output}");
        expect_test::expect![[r#"
            body:
                for Decode;
                beq:
                    k::bits!("bbbbbbb sssss rrrrr 000 bbbbb 1100011", b: signed[12 | 10:5 | 4:1 | 11])
                    => Beq(r, s, b);
                addi: k::bits!("iiiiiiiiiiii rrrrr 000 ddddd 0010011", i: signed) => Addi(d, r, i);"#]]
        .assert_eq(&actual);
    }

    #[test]
    fn formats_single_cell_table_with_global_alignment() {
        let source = r"
            for Expr;
            use Op::*;

            tiny:A(x)=>x;
            longer: Pair(lhs,rhs)=>k![lhs,rhs] where lhs: Value;
        ";
        let output = format_rule_body(source, 0, "    ", LAYOUT).expect("format body");
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
        let output = format_rule_body(source, 0, "    ", LAYOUT).expect("format body");
        let actual = format!("body:\n{output}");
        expect_test::expect![[r"
            body:
                for Exp;
                use ExpSyntax::*;

                swap  : Swap { e }   => { let Pair(x, y) = e; let z: Int = x; Pair(y, z) };
                shadow: Shadow { e } => Pair({ let e = Pair(e, e); e }, e);"]]
        .assert_eq(&actual);
        let again = format_rule_body(&output, 0, "    ", LAYOUT).expect("format formatted body");
        assert_eq!(again, output);
    }

    /// Expression notation keeps Rust's spelling: spaced connectives and
    /// method calls whose domain turbofish hugs its name and arguments.
    #[test]
    fn expression_notation_keeps_its_spelling_and_formats_idempotently() {
        let source = r"
            for Exp;
            use ExpSyntax::*;

            check:Check(n,t,c)=>n.gt :: < Int > (0)&&(t.lt::<Int>(c)||c.eq::<K>(t));
            chain: Chain(b, m) => b . bit_and::<Int>(m).ne::<Int>(b);
        ";
        let output = format_rule_body(source, 0, "    ", LAYOUT).expect("format body");
        let actual = format!("body:\n{output}");
        expect_test::expect![[r"
            body:
                for Exp;
                use ExpSyntax::*;

                check: Check(n, t, c) => n.gt::<Int>(0) && (t.lt::<Int>(c) || c.eq::<K>(t));
                chain: Chain(b, m)    => b.bit_and::<Int>(m).ne::<Int>(b);"]]
        .assert_eq(&actual);
        let again = format_rule_body(&output, 0, "    ", LAYOUT).expect("format formatted body");
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
        let output = format_rule_body(source, 0, "    ", LAYOUT).expect("format body");
        let actual = format!("body:\n{output}");
        expect_test::expect![[r"
            body:
                for Expr;
                use Op::*;

                div_by_minus_one: Div { lhs, rhs: -1 } => int::sub(0, lhs);
                sign            : Sgn(-1)              => -1;"]]
        .assert_eq(&actual);
        let again = format_rule_body(&output, 0, "    ", LAYOUT).expect("format formatted body");
        assert_eq!(again, output);
    }

    /// A record update's `..base` (F5) hugs its base, as Rust spells it.
    #[test]
    fn record_rests_hug_their_base_and_format_idempotently() {
        let source = r"
            for Machine;

            enter: { frame: saved @ Frame { pc: p, .. } } => { frame: Frame { pc: int::add(p, 1), .. saved } };
            reset: { k: [t @ Ctor { f: _, .. }, ..] } => { k: [Ctor { .. t }, ..] };
        ";
        let output = format_rule_body(source, 0, "    ", LAYOUT).expect("format body");
        assert!(
            output.contains("frame: Frame { pc: int::add(p, 1), ..saved }"),
            "{output}"
        );
        assert!(
            output.contains("frame: saved @ Frame { pc: p, .. }"),
            "{output}"
        );
        assert!(output.contains("k: [Ctor { ..t }, ..]"), "{output}");
        let again = format_rule_body(&output, 0, "    ", LAYOUT).expect("format formatted body");
        assert_eq!(again, output);
    }

    #[test]
    fn radix_literals_keep_their_spelling_and_format_idempotently() {
        let source = r"
            for Expr;
            use Op::*;

            load_if:Load(0xFF0F)=>0b1010_0101;
            negative: Sgn(-0x10) => 0o17;
        ";
        let output = format_rule_body(source, 0, "    ", LAYOUT).expect("format body");
        let actual = format!("body:\n{output}");
        expect_test::expect![[r"
            body:
                for Expr;
                use Op::*;

                load_if : Load(0xFF0F) => 0b1010_0101;
                negative: Sgn(-0x10)   => 0o17;"]]
        .assert_eq(&actual);
        let again = format_rule_body(&output, 0, "    ", LAYOUT).expect("format formatted body");
        assert_eq!(again, output);
    }

    #[test]
    #[expect(
        clippy::unicode_not_nfc,
        reason = "Decomposed labels exercise zero-width combining marks."
    )]
    fn aligns_unicode_table_and_trailing_comments_by_display_width() {
        // Term validation rejects string literals, so this test exercises rendering and alignment directly.
        let tokens = |source: &str| Component {
            tokens: TokenStream::from_str(source)
                .expect("tokenize component")
                .into_iter()
                .collect(),
            offset: 0,
        };
        let row = |label, result, conditions: Option<&str>, comment: &str| RenderedClause {
            leading: Vec::new(),
            attributes: Vec::new(),
            body: ClauseBody::Row(table_row(
                &ClauseParts {
                    label: tokens(label),
                    pattern: tokens("A(x)"),
                    result: tokens(result),
                    conditions: conditions.map(tokens),
                },
                Comments::none(),
            )),
            trailing: Some(comment.to_owned()),
        };
        let mut clauses = align_single_clauses(
            vec![
                row("wide", r#""漢字""#, Some("x: Value"), "// wide"),
                row("café", "x", Some("x: Value"), "// combining"),
                row("ascii", "x", None, "// ascii"),
            ],
            100,
        );
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
        let output = format_rule_body(source, 0, "", LAYOUT).expect("format body");
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
        let output = format_rule_body(source, 0, "    ", LAYOUT).expect("format body");
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
