//! Drift pins of k-rust passages, located by an anchor and an opening instead of by line numbers.
//!
//! Integration tests include this file with
//! `#[path = "../../../testdata/k/passage.rs"] mod passage;`.
//!
//! A pin exists so that a change of the text kink relies on forces it to be read again; what kink
//! relies on is the passage's bytes, not the line it sits at. A passage is located by its anchor
//! (in a Markdown file the heading of the section that holds it, in a source file the declaration
//! of the item whose documentation or body holds it) and the text it opens with, and pinned by the
//! SHA-256 of its lines joined by newlines. An edit elsewhere in the file moves no pin; an edit of
//! the passage, or a move out of its section, fails it. A missing or ambiguous anchor or opening
//! is refused, never resolved by the first match, so a pin cannot hash another passage.
#![allow(dead_code)]

use std::collections::BTreeMap;
use std::path::Path;

/// One pinned passage: `lines` lines of `file` (relative to the k-rust tree), the first of which
/// begins with `opening` (after its indentation) within the scope of `anchor`, whose SHA-256 is
/// `digest`.
pub struct Passage {
    pub file: &'static str,
    pub anchor: &'static str,
    pub opening: &'static str,
    pub lines: usize,
    pub digest: &'static str,
}

/// 1-based first and last line of `passage` in `text`, or a message saying what moved.
pub fn check(text: &str, passage: &Passage) -> Result<(usize, usize), String> {
    let Passage {
        file,
        anchor,
        opening,
        lines: count,
        digest,
    } = *passage;
    assert!(
        !opening.is_empty() && !opening.starts_with(char::is_whitespace) && count >= 1,
        "{file} {anchor:?}: a malformed pin (an opening must be nonempty without leading \
         whitespace, and a passage at least one line)"
    );
    let lines = text.split('\n').collect::<Vec<_>>();
    let markdown = file.ends_with(".md");
    let headings = if markdown {
        markdown_headings(&lines)
    } else {
        Vec::new()
    };
    // Byte offset of the start of each line, so an opening may span lines.
    let mut starts = Vec::with_capacity(lines.len());
    let mut offset = 0;
    for line in &lines {
        starts.push(offset);
        offset += line.len() + 1;
    }
    let begins = |i: usize| {
        text[starts[i]..]
            .trim_start_matches(' ')
            .starts_with(opening)
    };
    // Where the opening is anywhere in the file, for the messages: "line N (under "heading")".
    let elsewhere = || {
        (0..lines.len())
            .filter(|&i| begins(i))
            .map(|i| match heading_above(&headings, i) {
                Some(h) => format!("line {} (under {:?})", i + 1, lines[h]),
                None => format!("line {}", i + 1),
            })
            .collect::<Vec<_>>()
            .join(", ")
    };

    // 1. Scope.
    let anchors = if markdown {
        headings
            .iter()
            .map(|&(i, _)| i)
            .filter(|&i| lines[i] == anchor)
            .collect::<Vec<_>>()
    } else {
        (0..lines.len())
            .filter(|&i| lines[i].trim_start().starts_with(anchor))
            .collect::<Vec<_>>()
    };
    let at = match anchors.as_slice() {
        [] => {
            let found = elsewhere();
            let at = if found.is_empty() {
                String::new()
            } else {
                format!("; the opening is now at {found}")
            };
            let kind = if markdown { "heading" } else { "item" };
            return Err(format!(
                "{file}: no {kind} {anchor:?}: renamed or removed{at}; read the passage beginning \
                 {opening:?} again and pin it under its new anchor"
            ));
        }
        [at] => *at,
        several => {
            return Err(format!(
                "{file}: {anchor:?} is at lines {}: pin a unique anchor",
                one_based(several)
            ));
        }
    };
    let (start, end) = if markdown {
        let level = heading_level(anchor).expect("a Markdown anchor is a heading");
        let end = headings
            .iter()
            .find(|&&(i, l)| i > at && l <= level)
            .map_or(lines.len() - 1, |&(i, _)| i - 1);
        (at, end)
    } else {
        let mut start = at;
        while start > 0 {
            let above = lines[start - 1].trim_start();
            if above.starts_with("///") || above.starts_with("#[") {
                start -= 1;
            } else {
                break;
            }
        }
        let end = if lines[at].trim_end().ends_with(';') {
            at
        } else {
            let indent = &lines[at][..lines[at].len() - lines[at].trim_start().len()];
            let closing = format!("{indent}}}");
            (at + 1..lines.len())
                .find(|&i| lines[i] == closing)
                .ok_or_else(|| {
                    format!(
                        "{file}: item {anchor:?} at line {} has no closing line {closing:?}",
                        at + 1
                    )
                })?
        };
        (start, end)
    };

    // 2. Opening.
    let candidates = (start..=end).filter(|&i| begins(i)).collect::<Vec<_>>();
    let first = match candidates.as_slice() {
        [] => {
            let found = elsewhere();
            let place = if found.is_empty() {
                "out of the file".to_string()
            } else {
                format!("to {found}")
            };
            return Err(format!(
                "{file} {anchor:?} (lines {}-{}): no line begins with {opening:?}: the passage was \
                 reworded, or moved {place}; read the k-rust contract again and re-pin",
                start + 1,
                end + 1
            ));
        }
        [first] => *first,
        several => {
            return Err(format!(
                "{file} {anchor:?}: lines {} begin with {opening:?}: lengthen the opening",
                one_based(several)
            ));
        }
    };

    // 3. Extent: the passage may run past the scope's end; the digest covers it.
    if first + count > lines.len() {
        return Err(format!(
            "{file} {anchor:?}: the passage at line {} needs {count} lines, the file ends at line \
             {}",
            first + 1,
            lines.len()
        ));
    }

    // 4. Digest.
    let last = first + count - 1;
    let actual = kink_patch::sha256(lines[first..=last].join("\n").as_bytes()).to_string();
    if actual != digest {
        return Err(format!(
            "{file} {anchor:?} lines {}-{} (beginning {opening:?}) changed: read the k-rust \
             contract again (sha256 now {actual}, pinned {digest})",
            first + 1,
            last + 1
        ));
    }
    Ok((first + 1, last + 1))
}

/// Reads each `file` under `k_rust`, checks every passage, panics once listing every failure.
pub fn assert_pinned(k_rust: &Path, passages: &[Passage]) {
    let mut texts = BTreeMap::new();
    let mut failures = Vec::new();
    for passage in passages {
        let text = texts
            .entry(passage.file)
            .or_insert_with(|| std::fs::read_to_string(k_rust.join(passage.file)));
        match text {
            Ok(text) => {
                if let Err(failure) = check(text, passage) {
                    failures.push(failure);
                }
            }
            Err(error) => failures.push(format!("{}: unreadable: {error}", passage.file)),
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {} pinned k-rust passages failed:\n{}",
        failures.len(),
        passages.len(),
        failures.join("\n")
    );
}

/// The level of a heading line (`#{1,6} ` at column 0), if it is one.
fn heading_level(line: &str) -> Option<usize> {
    let level = line.bytes().take_while(|&b| b == b'#').count();
    ((1..=6).contains(&level) && line[level..].starts_with(' ')).then_some(level)
}

/// The 0-based index and level of every heading line outside fenced code.
fn markdown_headings(lines: &[&str]) -> Vec<(usize, usize)> {
    let mut fenced = false;
    let mut headings = Vec::new();
    for (i, line) in lines.iter().enumerate() {
        if line.trim_start().starts_with("```") {
            fenced = !fenced;
        } else if !fenced && let Some(level) = heading_level(line) {
            headings.push((i, level));
        }
    }
    headings
}

/// The 0-based index of the nearest heading at or above line `i`.
fn heading_above(headings: &[(usize, usize)], i: usize) -> Option<usize> {
    headings
        .iter()
        .rev()
        .find(|&&(h, _)| h <= i)
        .map(|&(h, _)| h)
}

fn one_based(lines: &[usize]) -> String {
    lines
        .iter()
        .map(|i| (i + 1).to_string())
        .collect::<Vec<_>>()
        .join(", ")
}
