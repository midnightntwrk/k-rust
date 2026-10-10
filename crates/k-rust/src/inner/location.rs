//! ```toml algorithm
//! id = "parser.location.span"
//! name = "mapping parser byte spans to source locations"
//! sites = ["span_location", "text_location"]
//! variable = "B = bytes before the span boundaries"
//! counters = []
//! no_counter = "source-location mapping has no dedicated counter"
//!
//! [[cost]]
//! mode = "one span"
//! bound = "O(B)"
//! ```
//!
//! Maps parser byte spans back to source locations in O(prefix bytes) time.

use crate::definition::AttributeKey;
use crate::definition::{Attributes, Location};
use crate::inner::ParseError;
use crate::kast::TermSpan;
use crate::lines;

/// Locate in `contents` every subterm an ambiguity report names by its span.
pub(super) fn locate_ambiguity_places(
    error: &mut ParseError,
    attributes: &Attributes,
    contents: &str,
) {
    locate_places(error, |span| span_location(attributes, contents, span));
}

/// Locate every subterm an ambiguity report names by its span in `text`, a whole input whose
/// byte zero is line 1, column 1 (a program, or a configuration value), whatever source
/// identity its spans carry.
pub(super) fn locate_ambiguity_places_in_text(error: &mut ParseError, text: &str) {
    locate_places(error, |span| {
        text_location(text, span.start, span.end, 1, 1)
    });
}

fn locate_places(error: &mut ParseError, locate: impl Fn(TermSpan) -> Option<Location>) {
    if let ParseError::Ambiguous { places, .. } = error {
        for place in places {
            place.location = place.span.and_then(&locate);
        }
    }
}

pub(super) fn span_location(
    attributes: &Attributes,
    contents: &str,
    span: TermSpan,
) -> Option<Location> {
    let content_offset = attributes
        .value(AttributeKey::ContentStartOffset)
        .and_then(serde_json::Value::as_u64)
        .and_then(|offset| usize::try_from(offset).ok())
        .unwrap_or(0);
    let start = span.start.checked_sub(content_offset)?;
    let end = span.end.checked_sub(content_offset)?;
    let line = attributes
        .value(AttributeKey::ContentStartLine)
        .and_then(serde_json::Value::as_u64)
        .and_then(|line| u32::try_from(line).ok())?;
    let column = attributes
        .value(AttributeKey::ContentStartColumn)
        .and_then(serde_json::Value::as_u64)
        .and_then(|column| u32::try_from(column).ok())?;
    text_location(contents, start, end, line, column)
}

/// The location of bytes `start..end` of `contents`, whose first byte is at `line`:`column`.
fn text_location(
    contents: &str,
    start: usize,
    end: usize,
    mut line: u32,
    mut column: u32,
) -> Option<Location> {
    if start > end || !contents.is_char_boundary(start) || !contents.is_char_boundary(end) {
        return None;
    }
    let position = advance(&mut line, &mut column, contents, 0, start);
    let (start_line, start_column) = (line, column);
    advance(&mut line, &mut column, contents, position, end);
    Some(Location {
        start_line,
        start_column,
        end_line: line,
        end_column: column,
    })
}

/// Move `line`:`column` from byte `from` of `text` to byte `to`: a column per Unicode scalar
/// value, and a line per line terminator (`crate::lines`), which sets the column back to 1.
/// Returns where it stopped: `to`, or the end of a terminator that `to` lies inside, which has
/// already moved the location to the next line, so that the bytes left of that terminator move it
/// no further.
fn advance(line: &mut u32, column: &mut u32, text: &str, from: usize, to: usize) -> usize {
    let mut position = from;
    while position < to {
        if let Some(terminator) = lines::terminator_at(text, position) {
            *line = line.saturating_add(1);
            *column = 1;
            position += terminator.len();
        } else {
            *column = column.saturating_add(1);
            position += text[position..].chars().next().map_or(1, char::len_utf8);
        }
    }
    position
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use serde_json::json;

    use super::*;
    use crate::provenance::SourceId;

    #[test]
    fn location_counts_unicode_scalars_and_every_unicode_line_terminator() {
        let attributes = Attributes::new(BTreeMap::from([
            ("contentStartOffset".into(), json!(100)),
            ("contentStartLine".into(), json!(4)),
            ("contentStartColumn".into(), json!(3)),
        ]));
        for line_break in lines::LINE_TERMINATORS {
            let contents = format!("λ{line_break}bad");
            let start = contents.find("bad").unwrap();
            assert_eq!(
                span_location(
                    &attributes,
                    &contents,
                    TermSpan {
                        source: SourceId(7),
                        start: 100 + start,
                        end: 100 + start + 3,
                    },
                ),
                Some(Location {
                    start_line: 5,
                    start_column: 1,
                    end_line: 5,
                    end_column: 4,
                }),
                "line break {line_break:?}",
            );
        }

        let contents = "𐐀λbad";
        let start = contents.find('λ').unwrap();
        assert_eq!(
            span_location(
                &attributes,
                contents,
                TermSpan {
                    source: SourceId(7),
                    start: 100 + start,
                    end: 100 + start + "λb".len(),
                },
            ),
            Some(Location {
                start_line: 4,
                start_column: 4,
                end_line: 4,
                end_column: 6,
            })
        );
    }

    /// `\r\n` is one line terminator, so a span that starts or ends between its `\r` and its
    /// `\n` sees one line end there, not two.
    #[test]
    fn a_span_boundary_inside_crlf_counts_it_once() {
        let text = "a\r\nb";
        let location = |start, end| text_location(text, start, end, 1, 1).unwrap();
        let line_and_column = |location: Location| {
            (
                (location.start_line, location.start_column),
                (location.end_line, location.end_column),
            )
        };
        assert_eq!(line_and_column(location(2, 4)), ((2, 1), (2, 2)));
        assert_eq!(line_and_column(location(0, 2)), ((1, 1), (2, 1)));
        assert_eq!(line_and_column(location(0, 4)), ((1, 1), (2, 2)));
    }
}
