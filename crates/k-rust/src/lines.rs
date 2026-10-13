//! Where lines end in a text that k-rust scans: one table, read by the source locations
//! (`inner::location`), the token-regex line anchors of the in-process scanner
//! (`inner::parser::scanner`), and printed into the C runtime of generated scanners
//! (`bison::scanner`), so a location, a `^` and a `$` all see the same lines.
//!
//! A text is a sequence of lines separated by line terminators. A position is a line start when
//! it is the start of the text or a terminator ends there, and a line end when a terminator starts
//! there; a position strictly inside a terminator (between the `\r` and the `\n` of `\r\n`) is
//! neither, because a terminator is one separator, not several. The end of the text is not a line
//! end: text after the last terminator is an unterminated line.

/// The line terminators: `\r\n`, `\n`, `\r`, vertical tab, form feed, U+0085 (next line),
/// U+2028 (line separator) and U+2029 (paragraph separator), the characters Unicode treats as
/// ending a line (UAX #14 mandatory breaks), with `\r\n` one terminator.
///
/// A terminator precedes every terminator that is a proper prefix or suffix of it, so the first
/// one in table order that a text starts (or ends) with is the longest; [`terminator_at`] relies
/// on it, as do the scanner, which finds the terminator a `$`-anchored match ends with, and the
/// generated C runtime, which reads the same order.
pub(crate) const LINE_TERMINATORS: [&str; 8] = [
    "\r\n", "\n", "\r", "\u{b}", "\u{c}", "\u{85}", "\u{2028}", "\u{2029}",
];

/// Whether `character` is the first character of a line terminator.
pub(crate) fn starts_terminator(character: char) -> bool {
    matches!(character, '\n'..='\r' | '\u{85}' | '\u{2028}' | '\u{2029}')
}

/// Whether `byte` may be the first byte of a line terminator: the first byte of the UTF-8
/// encoding of a character [`starts_terminator`] holds of.
pub(crate) fn may_start_terminator(byte: u8) -> bool {
    matches!(byte, b'\n'..=b'\r' | 0xC2 | 0xE2)
}

/// The longest line terminator `text` has at byte `index`, if any. It does not ask whether
/// `index` is itself inside a terminator (see [`ends_line`]).
pub(crate) fn terminator_at(text: &str, index: usize) -> Option<&'static str> {
    let rest = text.as_bytes().get(index..)?;
    LINE_TERMINATORS
        .into_iter()
        .find(|terminator| rest.starts_with(terminator.as_bytes()))
}

/// The lines of `text` in order, each with the line terminator that ends it, as
/// `str::split_inclusive` gives them for one separator: concatenated they are `text`, and the
/// text after the last terminator is the last line when it is not empty.
pub(crate) fn split_inclusive(text: &str) -> impl Iterator<Item = &str> {
    let mut start = 0;
    std::iter::from_fn(move || {
        if start == text.len() {
            return None;
        }
        let mut index = start;
        // Invariant: `index` is a character boundary and no line terminator starts in `text[start..index]`; each iteration returns the line a terminator at `index` ends, or moves to the next byte that may begin one (a character boundary, as no terminator begins with a continuation byte).
        while index < text.len() {
            if let Some(terminator) = terminator_at(text, index) {
                let line = &text[start..index + terminator.len()];
                start = index + terminator.len();
                return Some(line);
            }
            index += text.as_bytes()[index + 1..]
                .iter()
                .position(|byte| may_start_terminator(*byte))
                .map_or(text.len() - index, |offset| offset + 1);
        }
        let line = &text[start..];
        start = text.len();
        Some(line)
    })
}

/// `line` without the line terminator it ends with, if any: the longest one, so `\r\n` is
/// removed whole.
pub(crate) fn strip_terminator(line: &str) -> &str {
    LINE_TERMINATORS
        .into_iter()
        .find_map(|terminator| line.strip_suffix(terminator))
        .unwrap_or(line)
}

/// Whether byte `index` lies strictly inside a line terminator of `text`: one starts before it and
/// ends after it.
pub(crate) fn inside_terminator(text: &str, index: usize) -> bool {
    let bytes = text.as_bytes();
    LINE_TERMINATORS.into_iter().any(|terminator| {
        (1..terminator.len()).any(|offset| {
            index >= offset && bytes[index - offset..].starts_with(terminator.as_bytes())
        })
    })
}

/// Whether byte `index` of `text` starts a line: it is the start of the text, or a line terminator
/// ends there and `index` is not inside a longer one.
pub(crate) fn starts_line(text: &str, index: usize) -> bool {
    let before = &text.as_bytes()[..index];
    index == 0
        || (LINE_TERMINATORS
            .into_iter()
            .any(|terminator| before.ends_with(terminator.as_bytes()))
            && !inside_terminator(text, index))
}

/// Whether byte `index` of `text` ends a line: a line terminator starts there and `index` is not
/// inside another one. The scanner reads line ends through [`line_end_regex`], which a test checks
/// against this.
#[cfg(test)]
fn ends_line(text: &str, index: usize) -> bool {
    terminator_at(text, index).is_some() && !inside_terminator(text, index)
}

/// A regex (Rust `regex` syntax) matching one line terminator that starts at a line end, for a
/// pattern that reads the terminator after a match instead of asking [`ends_line`]: `(?:body)`
/// followed by this matches exactly where the body's match ends a line.
///
/// Every terminator may follow, except where it starts inside another: of the table, only `\n`
/// can (inside `\r\n`), and the CRLF-mode multi-line `$` before it holds before a `\n` exactly when
/// no `\r` precedes it. A test checks that no other terminator has such a position.
pub(crate) fn line_end_regex() -> String {
    let alternatives = LINE_TERMINATORS
        .into_iter()
        .map(|terminator| {
            let escaped = escape(terminator);
            if terminator == "\n" {
                format!("(?Rm:$){escaped}")
            } else {
                escaped
            }
        })
        .collect::<Vec<_>>();
    format!("(?:{})", alternatives.join("|"))
}

/// `terminator` as a Rust regex that matches exactly it.
fn escape(terminator: &str) -> String {
    terminator
        .chars()
        .map(|character| format!(r"\x{{{:X}}}", u32::from(character)))
        .collect()
}

#[cfg(test)]
mod tests {
    use regex::Regex;

    use super::*;

    #[test]
    fn the_first_characters_and_bytes_of_the_terminators_are_the_tables() {
        for character in (0..=0x10FFFF).filter_map(char::from_u32) {
            assert_eq!(
                starts_terminator(character),
                LINE_TERMINATORS
                    .into_iter()
                    .any(|terminator| terminator.starts_with(character)),
                "{character:?}"
            );
        }
        for byte in 0..=u8::MAX {
            if LINE_TERMINATORS
                .into_iter()
                .any(|terminator| terminator.as_bytes()[0] == byte)
            {
                assert!(may_start_terminator(byte), "{byte:#x}");
            }
        }
    }

    #[test]
    fn a_terminator_precedes_every_terminator_that_is_a_prefix_or_suffix_of_it() {
        for (index, terminator) in LINE_TERMINATORS.iter().enumerate() {
            for later in &LINE_TERMINATORS[index + 1..] {
                assert!(
                    !later.starts_with(terminator) && !later.ends_with(terminator),
                    "{later:?} must precede its prefix or suffix {terminator:?}"
                );
            }
        }
    }

    /// This is the only place one terminator can start or end inside another, which
    /// [`inside_terminator`] and the line-end regex's CRLF-mode anchor exclude.
    #[test]
    fn only_the_newline_of_crlf_starts_inside_another_terminator() {
        let mut interior = Vec::new();
        for outer in LINE_TERMINATORS {
            for (offset, _) in outer.char_indices().skip(1) {
                for inner in LINE_TERMINATORS {
                    if outer[offset..].starts_with(inner) || outer[..offset].ends_with(inner) {
                        interior.push((outer, offset, inner));
                    }
                }
            }
        }
        assert_eq!(
            interior,
            [("\r\n", 1, "\n"), ("\r\n", 1, "\r")],
            "a terminator inside another needs its own guard where line ends are read"
        );
    }

    #[test]
    fn lines_start_and_end_at_every_terminator_but_never_inside_one() {
        for terminator in LINE_TERMINATORS {
            let text = format!("a{terminator}b");
            let after = 1 + terminator.len();
            assert!(ends_line(&text, 1), "{terminator:?}");
            assert!(starts_line(&text, after), "{terminator:?}");
            assert!(!starts_line(&text, 1) && !ends_line(&text, after));
            for inside in 2..after {
                assert!(!starts_line(&text, inside) && !ends_line(&text, inside));
            }
        }
        assert!(starts_line("", 0) && !ends_line("a", 1));
        // `\r\r\n`: the first `\r` ends a line, and the next line is empty.
        assert!(starts_line("\r\r\n", 1) && ends_line("\r\r\n", 1));
    }

    #[test]
    fn split_inclusive_cuts_the_text_at_its_line_starts() {
        let pieces = LINE_TERMINATORS
            .into_iter()
            .chain(["a", "\u{e9}", "\u{2027}"])
            .collect::<Vec<_>>();
        for first in &pieces {
            for second in &pieces {
                for third in &pieces {
                    let text = format!("{first}{second}{third}");
                    let lines = split_inclusive(&text).collect::<Vec<_>>();
                    assert_eq!(lines.concat(), text, "{text:?}");
                    let cuts = lines
                        .iter()
                        .scan(0, |end, line| {
                            *end += line.len();
                            Some(*end)
                        })
                        .collect::<Vec<_>>();
                    let starts = (1..text.len())
                        .filter(|index| text.is_char_boundary(*index) && starts_line(&text, *index))
                        .collect::<Vec<_>>();
                    assert_eq!(cuts[..cuts.len() - 1], starts, "{text:?}");
                    for (index, line) in lines.iter().enumerate() {
                        let content = strip_terminator(line);
                        assert!(!content.chars().any(starts_terminator), "{text:?}");
                        assert!(index + 1 == lines.len() || content != *line, "{text:?}");
                    }
                }
            }
        }
        assert_eq!(split_inclusive("").count(), 0);
    }

    #[test]
    fn the_line_end_regex_holds_where_ends_line_does() {
        let texts = LINE_TERMINATORS
            .into_iter()
            .chain(["", "x", "\u{2027}"])
            .flat_map(|terminator| {
                [
                    format!("a{terminator}b"),
                    format!("a\r{terminator}b"),
                    format!("a{terminator}\nb"),
                ]
            })
            .collect::<Vec<_>>();
        // A body ending in `\r` probes the inside of `\r\n`.
        for end in ["a", "a\r"] {
            let ends = Regex::new(&format!(r"\A(?:{end}){}", line_end_regex())).unwrap();
            for text in &texts {
                assert_eq!(
                    ends.is_match(text),
                    text.starts_with(end) && ends_line(text, end.len()),
                    "{end:?} in {text:?}"
                );
            }
        }
    }
}
