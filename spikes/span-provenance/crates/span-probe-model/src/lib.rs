//! Runtime-safe snapshots of data captured while a procedural macro is running.

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Position {
    pub line: usize,
    pub column: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CapturedRange {
    pub label: &'static str,
    /// `proc_macro::Span::file()`, suitable for display and subject to path remapping.
    pub display_file: &'static str,
    /// Whether `proc_macro::Span::local_file()` was available at expansion time.
    /// The absolute local path itself is deliberately not embedded.
    pub had_local_file: bool,
    pub start: Position,
    pub end: Position,
    /// Best-effort text for the first and last leaf tokens. Stable Span cannot
    /// join a multi-token node, so this is not claimed to be the node text.
    pub first_token_text: Option<&'static str>,
    pub last_token_text: Option<&'static str>,
    /// What proc_macro2 1.0.107 exposed for the same endpoint spans. Its lines
    /// are one-based but its columns are zero-based, unlike proc_macro.
    pub proc_macro2_start: Position,
    pub proc_macro2_end: Position,
    pub proc_macro2_first_byte_range: (usize, usize),
    pub proc_macro2_last_byte_range: (usize, usize),
    pub proc_macro2_join_succeeded: bool,
}

/// Converts stable Span line/column locations to a byte range by indexing a
/// known source snapshot. Stable proc_macro columns are one-based Unicode-scalar
/// columns in the tested rustc, so source content is required for conversion.
pub fn byte_offset(source: &str, position: Position) -> Option<usize> {
    let line_start = if position.line == 1 {
        0
    } else {
        source
            .match_indices('\n')
            .nth(position.line.checked_sub(2)?)
            .map(|(offset, _)| offset + 1)?
    };
    let scalar_column = position.column.checked_sub(1)?;
    let remainder = &source[line_start..];
    let line = &remainder[..remainder.find('\n').unwrap_or(remainder.len())];
    let within_line = if scalar_column == 0 {
        0
    } else {
        line.char_indices()
            .nth(scalar_column)
            .map(|(offset, _)| offset)
            .or_else(|| (line.chars().count() == scalar_column).then_some(line.len()))?
    };
    line_start.checked_add(within_line)
}

pub fn byte_range(source: &str, range: CapturedRange) -> Option<std::ops::Range<usize>> {
    Some(byte_offset(source, range.start)?..byte_offset(source, range.end)?)
}

