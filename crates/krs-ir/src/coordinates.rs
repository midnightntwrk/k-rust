//! Source coordinates shared by expansion, collection, and generated sidecars.

use std::error::Error;
use std::fmt;
use std::ops::Range;

/// A normalized, slash-separated display path relative to a package root.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DisplayPath(String);

impl DisplayPath {
    /// Reports whether a spelling must be treated as absolute on any supported host.
    #[must_use]
    pub fn is_absolute_spelling(spelling: &str) -> bool {
        let bytes = spelling.as_bytes();
        spelling.starts_with(['/', '\\'])
            || spelling.starts_with("file:")
            || (bytes.len() >= 3
                && bytes[0].is_ascii_alphabetic()
                && bytes[1] == b':'
                && matches!(bytes[2], b'/' | b'\\'))
    }

    /// Normalizes separators and validates a package-relative display path.
    ///
    /// # Errors
    ///
    /// Returns an error for an empty, absolute, drive-relative, or non-normalized spelling.
    pub fn new(spelling: impl Into<String>) -> Result<Self, DisplayPathError> {
        let spelling = spelling.into();
        let normalized = spelling.replace('\\', "/");
        if normalized.is_empty() {
            return Err(DisplayPathError::Empty(spelling));
        }
        if Self::is_absolute_spelling(&spelling) {
            return Err(DisplayPathError::Absolute(spelling));
        }
        let bytes = normalized.as_bytes();
        if (bytes.len() >= 2 && bytes[0].is_ascii_alphabetic() && bytes[1] == b':')
            || normalized
                .split('/')
                .any(|component| component.is_empty() || component == "." || component == "..")
        {
            return Err(DisplayPathError::NotNormalized(spelling));
        }
        Ok(Self(normalized))
    }

    /// Returns the normalized spelling.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// A rejected display path spelling.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DisplayPathError {
    /// The spelling is empty.
    Empty(String),
    /// The spelling denotes an absolute path.
    Absolute(String),
    /// The spelling contains an empty, current, or parent component or a drive-relative prefix.
    NotNormalized(String),
}

impl DisplayPathError {
    /// Returns the spelling supplied to the constructor.
    #[must_use]
    pub fn spelling(&self) -> &str {
        match self {
            Self::Empty(spelling) | Self::Absolute(spelling) | Self::NotNormalized(spelling) => {
                spelling
            }
        }
    }
}

impl fmt::Display for DisplayPathError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty(spelling) => write!(formatter, "display path `{spelling}` is empty"),
            Self::Absolute(spelling) => write!(formatter, "display path `{spelling}` is absolute"),
            Self::NotNormalized(spelling) => {
                write!(formatter, "display path `{spelling}` is not normalized")
            }
        }
    }
}

impl Error for DisplayPathError {}

/// A half-open byte range whose end is at least its start.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ByteRange {
    start: usize,
    end: usize,
}

impl ByteRange {
    /// Creates a half-open byte range.
    ///
    /// # Errors
    ///
    /// Returns an error when the end precedes the start.
    pub const fn new(start: usize, end: usize) -> Result<Self, CoordinateError> {
        if start > end {
            return Err(CoordinateError::ReversedRange);
        }
        Ok(Self { start, end })
    }

    /// Returns the inclusive start byte.
    #[must_use]
    pub const fn start(self) -> usize {
        self.start
    }

    /// Returns the exclusive end byte.
    #[must_use]
    pub const fn end(self) -> usize {
        self.end
    }

    /// Returns the number of bytes in the range.
    #[must_use]
    pub const fn len(self) -> usize {
        self.end - self.start
    }

    /// Reports whether the range contains no bytes.
    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.start == self.end
    }

    /// Extracts the range from a source string when both offsets are UTF-8 boundaries.
    #[must_use]
    pub fn text(self, source: &str) -> Option<&str> {
        source.get(self.start..self.end)
    }

    /// Converts a `proc_macro2` span's byte range.
    ///
    /// # Errors
    ///
    /// Returns an error if the span reports reversed offsets.
    #[cfg(feature = "proc-macro2")]
    pub fn from_proc_macro2(span: proc_macro2::Span) -> Result<Self, CoordinateError> {
        Self::try_from(span.byte_range())
    }
}

impl From<ByteRange> for Range<usize> {
    fn from(range: ByteRange) -> Self {
        range.start..range.end
    }
}

impl TryFrom<Range<usize>> for ByteRange {
    type Error = CoordinateError;

    fn try_from(range: Range<usize>) -> Result<Self, Self::Error> {
        Self::new(range.start, range.end)
    }
}

/// One-based line and one-based Unicode-scalar column.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Position {
    line: u32,
    scalar_column: u32,
}

impl Position {
    /// Creates a position from one-based coordinates.
    ///
    /// # Errors
    ///
    /// Returns an error when either coordinate is zero.
    pub const fn new(line: u32, scalar_column: u32) -> Result<Self, CoordinateError> {
        if line == 0 {
            return Err(CoordinateError::ZeroLine);
        }
        if scalar_column == 0 {
            return Err(CoordinateError::ZeroColumn);
        }
        Ok(Self {
            line,
            scalar_column,
        })
    }

    /// Converts a `proc_macro2` line and zero-based scalar column.
    ///
    /// # Errors
    ///
    /// Returns an error for zero lines or coordinates beyond `u32`.
    #[cfg(feature = "proc-macro2")]
    pub fn from_proc_macro2(location: proc_macro2::LineColumn) -> Result<Self, CoordinateError> {
        let line = u32::try_from(location.line).map_err(|_| CoordinateError::LineOverflow)?;
        let column = location
            .column
            .checked_add(1)
            .and_then(|column| u32::try_from(column).ok())
            .ok_or(CoordinateError::ColumnOverflow)?;
        Self::new(line, column)
    }

    /// Converts stable `proc_macro::Span::line` and `column` values, both one-based.
    ///
    /// # Errors
    ///
    /// Returns an error for zero or coordinates beyond `u32`.
    pub fn from_proc_macro_values(line: usize, column: usize) -> Result<Self, CoordinateError> {
        let line = u32::try_from(line).map_err(|_| CoordinateError::LineOverflow)?;
        let column = u32::try_from(column).map_err(|_| CoordinateError::ColumnOverflow)?;
        Self::new(line, column)
    }

    /// Returns the one-based line.
    #[must_use]
    pub const fn line(self) -> u32 {
        self.line
    }

    /// Returns the one-based Unicode-scalar column.
    #[must_use]
    pub const fn scalar_column(self) -> u32 {
        self.scalar_column
    }
}

/// An invalid source coordinate or byte range.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CoordinateError {
    /// The line is zero.
    ZeroLine,
    /// The column is zero.
    ZeroColumn,
    /// The line exceeds `u32`.
    LineOverflow,
    /// The column exceeds `u32`.
    ColumnOverflow,
    /// A byte range is reversed.
    ReversedRange,
}

impl fmt::Display for CoordinateError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::ZeroLine => "source lines are one-based",
            Self::ZeroColumn => "source scalar columns are one-based",
            Self::LineOverflow => "source line exceeds protocol limits",
            Self::ColumnOverflow => "source scalar column exceeds protocol limits",
            Self::ReversedRange => "source byte range is reversed",
        })
    }
}

impl Error for CoordinateError {}

/// The line starts and exact text of one source revision.
#[derive(Debug)]
pub struct LineIndex {
    source: String,
    starts: Vec<usize>,
}

impl LineIndex {
    /// Indexes line-feed terminated lines in the supplied source revision.
    #[must_use]
    pub fn new(source: &str) -> Self {
        let mut starts = vec![0];
        starts.extend(source.match_indices('\n').map(|(offset, _)| offset + 1));
        Self {
            source: source.to_owned(),
            starts,
        }
    }

    /// Converts a one-based scalar position to a byte offset.
    ///
    /// The position just after the final scalar of a line is valid.
    ///
    /// # Errors
    ///
    /// Returns an error when the line or column lies outside the source.
    pub fn position_to_byte(&self, position: Position) -> Result<usize, LineIndexError> {
        let line = position.line() as usize;
        let column = position.scalar_column() as usize;
        let line_start = self
            .starts
            .get(line - 1)
            .copied()
            .ok_or(LineIndexError::LineOutOfBounds(position.line()))?;
        let line_end = self
            .starts
            .get(line)
            .map_or(self.source.len(), |next_start| next_start - 1);
        let line_text = &self.source[line_start..line_end];
        if column == 1 {
            return Ok(line_start);
        }
        line_text
            .char_indices()
            .nth(column - 1)
            .map(|(offset, _)| line_start + offset)
            .or_else(|| (column == line_text.chars().count() + 1).then_some(line_end))
            .ok_or(LineIndexError::ColumnOutOfBounds(position))
    }

    /// Converts a `proc_macro2` line and zero-based scalar column to a byte offset.
    ///
    /// # Errors
    ///
    /// Returns an error when the coordinate is invalid or lies outside the source.
    #[cfg(feature = "proc-macro2")]
    pub fn line_column_to_byte(
        &self,
        location: proc_macro2::LineColumn,
    ) -> Result<usize, LineIndexError> {
        let position = Position::from_proc_macro2(location).map_err(LineIndexError::Coordinate)?;
        self.position_to_byte(position)
    }

    /// Converts a UTF-8 boundary byte offset to a one-based scalar position.
    ///
    /// # Errors
    ///
    /// Returns an error when the offset is outside the source, splits a scalar, or exceeds protocol limits.
    pub fn byte_to_position(&self, offset: usize) -> Result<Position, LineIndexError> {
        if offset > self.source.len() {
            return Err(LineIndexError::ByteOutOfBounds(offset));
        }
        if !self.source.is_char_boundary(offset) {
            return Err(LineIndexError::NotCharBoundary(offset));
        }
        let line_index = self.starts.partition_point(|start| *start <= offset) - 1;
        let column = self.source[self.starts[line_index]..offset].chars().count() + 1;
        Position::from_proc_macro_values(line_index + 1, column).map_err(LineIndexError::Coordinate)
    }
}

/// A position outside the indexed source revision.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LineIndexError {
    /// The requested line is absent.
    LineOutOfBounds(u32),
    /// The requested scalar column is absent.
    ColumnOutOfBounds(Position),
    /// The byte offset exceeds the source length.
    ByteOutOfBounds(usize),
    /// The byte offset splits a UTF-8 scalar.
    NotCharBoundary(usize),
    /// The result exceeds protocol limits.
    Coordinate(CoordinateError),
}

impl fmt::Display for LineIndexError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LineOutOfBounds(line) => write!(
                formatter,
                "source line {line} is outside the exact file revision"
            ),
            Self::ColumnOutOfBounds(position) => write!(
                formatter,
                "source scalar column {} is outside line {} of the exact file revision",
                position.scalar_column(),
                position.line()
            ),
            Self::ByteOutOfBounds(offset) => write!(
                formatter,
                "source byte {offset} is outside the exact file revision"
            ),
            Self::NotCharBoundary(offset) => {
                write!(formatter, "source byte {offset} splits a Unicode scalar")
            }
            Self::Coordinate(error) => error.fmt(formatter),
        }
    }
}

impl Error for LineIndexError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn display_paths_are_normalized_and_host_independent() {
        assert_eq!(
            DisplayPath::new(r"src\nested\lib.rs").unwrap().as_str(),
            "src/nested/lib.rs"
        );
        assert_eq!(
            DisplayPath::new(""),
            Err(DisplayPathError::Empty(String::new()))
        );
        for spelling in [
            "/tmp/lib.rs",
            r"\lib.rs",
            "//server/share.rs",
            r"\\server\share.rs",
            "file:relative.rs",
            "file:///tmp/lib.rs",
            "C:/lib.rs",
            r"C:\lib.rs",
        ] {
            assert!(DisplayPath::is_absolute_spelling(spelling), "{spelling}");
            assert_eq!(
                DisplayPath::new(spelling),
                Err(DisplayPathError::Absolute(spelling.to_owned()))
            );
        }
        for spelling in [
            "src//lib.rs",
            "src/./lib.rs",
            "src/../lib.rs",
            "src/lib.rs/",
        ] {
            assert!(!DisplayPath::is_absolute_spelling(spelling));
            assert_eq!(
                DisplayPath::new(spelling),
                Err(DisplayPathError::NotNormalized(spelling.to_owned()))
            );
        }
        assert!(!DisplayPath::is_absolute_spelling("C:relative.rs"));
        assert_eq!(
            DisplayPath::new("C:relative.rs"),
            Err(DisplayPathError::NotNormalized("C:relative.rs".to_owned()))
        );
    }

    #[test]
    fn constructors_validate_bases_and_overflow() {
        assert_eq!(Position::new(0, 1), Err(CoordinateError::ZeroLine));
        assert_eq!(Position::new(1, 0), Err(CoordinateError::ZeroColumn));
        assert_eq!(
            Position::from_proc_macro_values(2, 3).unwrap(),
            Position::new(2, 3).unwrap()
        );
        assert_eq!(
            Position::from_proc_macro_values(1, 0),
            Err(CoordinateError::ZeroColumn)
        );
        assert_eq!(
            Position::from_proc_macro_values(1, usize::MAX),
            Err(CoordinateError::ColumnOverflow)
        );
        assert_eq!(ByteRange::new(2, 1), Err(CoordinateError::ReversedRange));
        assert_eq!(ByteRange::new(1, 2).unwrap().end(), 2);
    }

    #[test]
    fn byte_ranges_preserve_half_open_text_boundaries() {
        let range = ByteRange::new(2, 6).unwrap();
        assert_eq!(range.len(), 4);
        assert!(!range.is_empty());
        assert_eq!(range.text("é🦀z"), Some("🦀"));
        assert_eq!(range.text("short"), None);
        assert_eq!(ByteRange::new(2, 2).unwrap().len(), 0);
        assert!(ByteRange::new(2, 2).unwrap().is_empty());
        assert_eq!(Range::<usize>::from(range), 2..6);
        assert_eq!(ByteRange::try_from(2..6), Ok(range));
        let reversed = Range { start: 6, end: 2 };
        assert_eq!(
            ByteRange::try_from(reversed),
            Err(CoordinateError::ReversedRange)
        );
    }

    #[cfg(feature = "proc-macro2")]
    #[test]
    fn proc_macro2_columns_are_zero_based() {
        let location = proc_macro2::LineColumn { line: 2, column: 2 };
        assert_eq!(
            Position::from_proc_macro2(location).unwrap(),
            Position::from_proc_macro_values(2, 3).unwrap()
        );
        assert_eq!(
            Position::from_proc_macro2(proc_macro2::LineColumn { line: 0, column: 0 }),
            Err(CoordinateError::ZeroLine)
        );
        assert_eq!(
            Position::from_proc_macro2(proc_macro2::LineColumn {
                line: 1,
                column: usize::MAX
            }),
            Err(CoordinateError::ColumnOverflow)
        );
        let index = LineIndex::new("é\nx");
        assert_eq!(
            index.line_column_to_byte(proc_macro2::LineColumn { line: 1, column: 1 }),
            Ok(2)
        );
        assert_eq!(
            index.line_column_to_byte(proc_macro2::LineColumn { line: 0, column: 0 }),
            Err(LineIndexError::Coordinate(CoordinateError::ZeroLine))
        );
    }

    #[test]
    fn line_index_preserves_scalar_and_line_feed_semantics() {
        let index = LineIndex::new("é🦀\r\n界z\n");
        for (line, column, byte) in [
            (1, 1, 0),
            (1, 2, 2),
            (1, 3, 6),
            (1, 4, 7),
            (2, 1, 8),
            (2, 2, 11),
            (2, 3, 12),
            (3, 1, 13),
        ] {
            let position = Position::new(line, column).unwrap();
            assert_eq!(index.position_to_byte(position).unwrap(), byte);
            assert_eq!(index.byte_to_position(byte).unwrap(), position);
        }
        assert_eq!(
            index.byte_to_position(1),
            Err(LineIndexError::NotCharBoundary(1))
        );
        assert_eq!(
            index.byte_to_position(14),
            Err(LineIndexError::ByteOutOfBounds(14))
        );
        assert_eq!(
            index.position_to_byte(Position::new(4, 1).unwrap()),
            Err(LineIndexError::LineOutOfBounds(4))
        );
        assert!(matches!(
            index.position_to_byte(Position::new(2, 4).unwrap()),
            Err(LineIndexError::ColumnOutOfBounds(_))
        ));
        assert_eq!(
            LineIndex::new("").byte_to_position(0).unwrap(),
            Position::new(1, 1).unwrap()
        );
    }
}
