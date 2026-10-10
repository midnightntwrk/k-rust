//! Where lines end in a text that k-rust scans: one table, read by the source locations
//! (`inner::location`), the token-regex line anchors and restriction anchors of the in-process
//! scanner (`inner::parser::scanner`), and printed into the C runtime of generated scanners
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

/// The longest line terminator `text` has at byte `index`, if any. It does not ask whether
/// `index` is itself inside a terminator (see [`ends_line`]).
pub(crate) fn terminator_at(text: &str, index: usize) -> Option<&'static str> {
    let rest = text.as_bytes().get(index..)?;
    LINE_TERMINATORS
        .into_iter()
        .find(|terminator| rest.starts_with(terminator.as_bytes()))
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
/// inside another one.
pub(crate) fn ends_line(text: &str, index: usize) -> bool {
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

/// A regex (Rust `regex` syntax) that holds at a line start of the matched text: the start of the
/// text, or after a line terminator it consumes. The CRLF-mode multi-line `^` after a consumed
/// `\r` holds unless a `\n` follows, where the `\r` is the start of `\r\n` and the position is
/// inside it.
pub(crate) fn line_start_regex() -> String {
    let alternatives = LINE_TERMINATORS
        .into_iter()
        .map(|terminator| {
            let escaped = escape(terminator);
            if terminator == "\r" {
                format!("{escaped}(?Rm:^)")
            } else {
                escaped
            }
        })
        .collect::<Vec<_>>();
    format!(r"(?:\A|{})", alternatives.join("|"))
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

    /// The two regexes special-case `\r` and `\n`; this is the only place one terminator can
    /// start or end inside another, which is what the CRLF-mode anchors exclude.
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
            "a terminator inside another needs its own guard in the line regexes"
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
    fn the_line_regexes_hold_where_the_position_functions_do() {
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
        // A body ending in `\r`, then one starting with `\n`, probes the inside of `\r\n`.
        for (end, start) in [("a", "b"), ("a\r", "b"), ("a", "\nb")] {
            let ends = Regex::new(&format!(r"\A(?:{end}){}", line_end_regex())).unwrap();
            let starts = Regex::new(&format!(r"{}(?:{start})\z", line_start_regex())).unwrap();
            for text in &texts {
                assert_eq!(
                    ends.is_match(text),
                    text.starts_with(end) && ends_line(text, end.len()),
                    "{end:?} in {text:?}"
                );
                let start_index = text.len() - start.len();
                assert_eq!(
                    starts.is_match(text),
                    text.ends_with(start) && starts_line(text, start_index),
                    "{start:?} in {text:?}"
                );
            }
        }
    }
}
