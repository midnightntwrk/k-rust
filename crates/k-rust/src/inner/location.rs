use crate::definition::{Attributes, Location};
use crate::kast::TermSpan;

pub(super) fn span_location(
    attributes: &Attributes,
    contents: &str,
    span: TermSpan,
) -> Option<Location> {
    let content_offset = attributes
        .get("contentStartOffset")
        .and_then(serde_json::Value::as_u64)
        .and_then(|offset| usize::try_from(offset).ok())
        .unwrap_or(0);
    let start = span.start.checked_sub(content_offset)?;
    let end = span.end.checked_sub(content_offset)?;
    let prefix = contents.get(..start)?;
    let through = contents.get(start..end)?;
    let mut line = attributes
        .get("contentStartLine")
        .and_then(serde_json::Value::as_u64)
        .and_then(|line| u32::try_from(line).ok())?;
    let mut column = attributes
        .get("contentStartColumn")
        .and_then(serde_json::Value::as_u64)
        .and_then(|column| u32::try_from(column).ok())?;
    advance(&mut line, &mut column, prefix);
    let (start_line, start_column) = (line, column);
    advance(&mut line, &mut column, through);
    Some(Location {
        start_line,
        start_column,
        end_line: line,
        end_column: column,
    })
}

fn advance(line: &mut u32, column: &mut u32, text: &str) {
    let mut characters = text.chars().peekable();
    while let Some(character) = characters.next() {
        if matches!(
            character,
            '\r' | '\n' | '\u{000b}' | '\u{000c}' | '\u{0085}' | '\u{2028}' | '\u{2029}'
        ) {
            if character == '\r' && characters.peek() == Some(&'\n') {
                characters.next();
            }
            *line = line.saturating_add(1);
            *column = 1;
        } else {
            *column = column.saturating_add(1);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use serde_json::json;

    use super::*;
    use crate::provenance::SourceId;

    #[test]
    fn location_counts_unicode_scalars_and_every_reference_line_break() {
        let attributes = Attributes::new(BTreeMap::from([
            ("contentStartOffset".into(), json!(100)),
            ("contentStartLine".into(), json!(4)),
            ("contentStartColumn".into(), json!(3)),
        ]));
        for line_break in [
            "\r\n", "\r", "\n", "\u{000b}", "\u{000c}", "\u{0085}", "\u{2028}", "\u{2029}",
        ] {
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
}
