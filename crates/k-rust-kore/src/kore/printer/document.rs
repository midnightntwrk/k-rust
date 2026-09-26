//! ```toml algorithm
//! id = "kore.printer.fits"
//! name = "bounded look-ahead for the flat layout of a KORE document group"
//! sites = ["fits"]
//! variable = "w = remaining line width at the group; k = ops read ahead, which stops at the group's end, at a hard line, or at the first op whose flat width exceeds w"
//! counters = []
//! no_counter = "the fits look-ahead has no dedicated counter"
//! invariant = "remaining is the line width left after the flat widths of the ops scanned so far, and depth is the number of groups opened and not yet closed since the scanned group's start"
//! span = "none"
//!
//! [[cost]]
//! mode = "one group in broken context"
//! bound = "O(k)"
//! ```
//!
//! ```toml algorithm
//! id = "kore.printer.render"
//! name = "width-aware streaming rendering of KORE documents"
//! sites = ["render", "write_spaces"]
//! variable = "N = document ops; o = output characters; k = the longest fits look-ahead, at most N and, in the printer's documents, bounded by a constant times the line width; indentation is written in 16 KiB chunks"
//! counters = []
//! no_counter = "document rendering has no dedicated counter"
//! invariant = "every op taken from the source and not in the look-ahead queue has been written to output; modes holds the base mode plus one mode per open group; indentation is the sum of open nest amounts; column is the number of characters since the last written newline"
//! span = "per call"
//!
//! [[cost]]
//! mode = "compact or broken layout"
//! bound = "O(N * k + o)"
//! ```
//!
//! Wadler-style documents render with a mode stack whose height is the group nesting depth.
//! The renderer pulls ops from an iterator and writes each one to an `io::Write` as soon as its layout is decided, so neither the whole document nor the whole text has to be held in memory.
//! A group opened in broken context is laid out flat exactly when its flat width fits in the rest of the line; `fits` decides that by reading ahead only until the answer is known, which bounds the ops held in memory by the line width rather than by the document.
//! No dedicated counter measures printing.
//!

use std::{collections::VecDeque, io};

use crate::measure::{self, Algorithm};

#[derive(Clone, Debug)]
pub(super) struct Doc {
    ops: Vec<Op>,
}

#[derive(Clone, Debug)]
pub(super) enum Op {
    Text(String),
    Line(&'static str),
    HardLine,
    NestStart(usize),
    NestEnd(usize),
    GroupStart,
    GroupEnd,
}

impl Doc {
    pub(super) fn from_ops(ops: Vec<Op>) -> Self {
        Self { ops }
    }

    pub(super) fn text(value: impl Into<String>) -> Self {
        Self::from_ops(vec![Op::Text(value.into())])
    }

    pub(super) fn line() -> Self {
        Self {
            ops: vec![Op::Line(" ")],
        }
    }

    pub(super) fn line_break() -> Self {
        Self {
            ops: vec![Op::Line("")],
        }
    }

    pub(super) fn hard_line() -> Self {
        Self {
            ops: vec![Op::HardLine],
        }
    }

    pub(super) fn concat(documents: impl IntoIterator<Item = Self>) -> Self {
        let mut documents = documents.into_iter();
        let Some(mut document) = documents.next() else {
            return Self::from_ops(Vec::new());
        };
        for next in documents {
            document.ops.extend(next.ops);
        }
        document
    }

    pub(super) fn nest(mut self, amount: usize) -> Self {
        if !self.ops.is_empty() {
            self.ops.insert(0, Op::NestStart(amount));
            self.ops.push(Op::NestEnd(amount));
        }
        self
    }

    pub(super) fn into_ops(self) -> impl Iterator<Item = Op> {
        self.ops.into_iter()
    }

    pub(super) fn group(mut self) -> Self {
        if !self.ops.is_empty() {
            self.ops.insert(0, Op::GroupStart);
            self.ops.push(Op::GroupEnd);
        }
        self
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum RenderMode {
    Compact,
    Pretty,
}

/// Write the layout of `ops` to `output`.
///
/// The layout is the one a group-by-group decision gives: a `Line` prints its flat text inside
/// a flat group and a newline plus the current indentation otherwise, a `HardLine` always prints
/// a newline plus the indentation, and a group opened inside a flat group is flat, while a
/// group opened in broken context (the pretty base mode, or a broken group) is flat exactly
/// when it contains no `HardLine` and the sum of its ops' flat widths is at most
/// `width - column` at its start. `fits` computes that condition from the ops that follow the
/// group start; everything else depends only on ops already taken, so each op is written as
/// soon as it reaches the front of the queue.
pub(super) fn render<W: io::Write + ?Sized>(
    ops: impl IntoIterator<Item = Op>,
    mode: RenderMode,
    width: usize,
    output: &mut W,
) -> io::Result<()> {
    let _span = measure::algorithm_span(Algorithm::KorePrinterRender);
    let mut source = ops.into_iter();
    let mut lookahead = VecDeque::new();
    let mut column = 0usize;
    let mut indentation = 0usize;
    let mut modes = vec![match mode {
        RenderMode::Compact => Mode::Flat,
        RenderMode::Pretty => Mode::Break,
    }];

    // Invariant: every op taken from `source` and not in `lookahead` has been written to
    // `output`; `modes` holds the base mode plus one mode per open group; `indentation` is the
    // sum of open nest amounts; `column` counts the characters written since the last newline.
    while let Some(op) = lookahead.pop_front().or_else(|| source.next()) {
        match op {
            Op::Text(value) => {
                output.write_all(value.as_bytes())?;
                column += value.chars().count();
            }
            Op::Line(flat) if modes.last() == Some(&Mode::Flat) => {
                output.write_all(flat.as_bytes())?;
                column += flat.chars().count();
            }
            Op::Line(_) | Op::HardLine => {
                output.write_all(b"\n")?;
                write_spaces(output, indentation)?;
                column = indentation;
            }
            Op::NestStart(amount) => indentation += amount,
            Op::NestEnd(amount) => indentation -= amount,
            Op::GroupStart => {
                let group_mode = if modes.last() == Some(&Mode::Flat)
                    || width
                        .checked_sub(column)
                        .is_some_and(|remaining| fits(&mut lookahead, &mut source, remaining))
                {
                    Mode::Flat
                } else {
                    Mode::Break
                };
                modes.push(group_mode);
            }
            Op::GroupEnd => {
                modes.pop();
            }
        }
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Mode {
    Flat,
    Break,
}

/// Whether the group whose `GroupStart` was just taken is flat in broken context: it contains
/// no `HardLine` and its ops' flat widths sum to at most `remaining`.
///
/// The ops of the group are read in order from `lookahead` and then from `source`; ops taken
/// from `source` are appended to `lookahead`, so the caller renders them afterwards in the same
/// order. Flat widths are non-negative, so the partial sums never decrease: once one exceeds
/// `remaining`, the group's total does too, and the answer is `false` without reading further.
/// A `HardLine` also decides `false`. Otherwise the scan reaches the matching `GroupEnd` with
/// the total at most `remaining`, and the answer is `true`.
///
/// Memory: the scan stops at the first op that brings the sum above `remaining`, which is at
/// most the line width, so `lookahead` holds ops of total flat width at most the line width plus
/// that of one op, together with the zero-width ops among them (nest and group markers and
/// empty `Line`s). The printer emits those markers as a fixed sequence around each delimited,
/// grouped, or nested level, and every such level contains a text op that is non-empty for
/// non-empty identifiers, so the zero-width ops between two text ops are bounded in number and
/// the queue's length is bounded by a constant times the line width, independent of the
/// document's size.
fn fits(
    lookahead: &mut VecDeque<Op>,
    source: &mut impl Iterator<Item = Op>,
    mut remaining: usize,
) -> bool {
    let mut depth = 0usize;
    let mut index = 0usize;
    // Invariant: `remaining` is the line width left after the flat widths of
    // `lookahead[..index]`, which are the group's ops read so far, and `depth` is the number of
    // groups opened and not closed among them.
    loop {
        if index == lookahead.len() {
            let op = source.next().expect("group markers are balanced");
            lookahead.push_back(op);
        }
        let flat = match &lookahead[index] {
            Op::Text(value) => value.as_str(),
            Op::Line(flat) => flat,
            Op::HardLine => return false,
            Op::NestStart(_) | Op::NestEnd(_) => "",
            Op::GroupStart => {
                depth += 1;
                ""
            }
            Op::GroupEnd => {
                if depth == 0 {
                    return true;
                }
                depth -= 1;
                ""
            }
        };
        match remaining.checked_sub(flat.chars().count()) {
            Some(left) => remaining = left,
            None => return false,
        }
        index += 1;
    }
}

fn write_spaces<W: io::Write + ?Sized>(output: &mut W, count: usize) -> io::Result<()> {
    const SPACES: [u8; 16 * 1024] = [b' '; 16 * 1024];
    let mut left = count;
    while left > 0 {
        let chunk = left.min(SPACES.len());
        output.write_all(&SPACES[..chunk])?;
        left -= chunk;
    }
    Ok(())
}

/// The two-pass renderer this module used before rendering streamed: it computes every group's
/// flat width over the whole document first and then renders into one `String`. Kept as the
/// test oracle for `render`, which must give the same bytes.
#[cfg(test)]
pub(super) fn whole_document_render(document: &Doc, mode: RenderMode, width: usize) -> String {
    let flat_widths = whole_document_flat_widths(&document.ops);
    let mut output = String::new();
    let mut column = 0usize;
    let mut indentation = 0usize;
    let mut modes = vec![match mode {
        RenderMode::Compact => Mode::Flat,
        RenderMode::Pretty => Mode::Break,
    }];
    for (index, op) in document.ops.iter().enumerate() {
        match op {
            Op::Text(value) => {
                output.push_str(value);
                column += value.chars().count();
            }
            Op::Line(flat) if modes.last() == Some(&Mode::Flat) => {
                output.push_str(flat);
                column += flat.chars().count();
            }
            Op::Line(_) | Op::HardLine => {
                output.push('\n');
                output.extend(std::iter::repeat_n(' ', indentation));
                column = indentation;
            }
            Op::NestStart(amount) => indentation += amount,
            Op::NestEnd(amount) => indentation -= amount,
            Op::GroupStart => {
                let group_mode = if modes.last() == Some(&Mode::Flat)
                    || flat_widths[index].is_some_and(|group| column + group <= width)
                {
                    Mode::Flat
                } else {
                    Mode::Break
                };
                modes.push(group_mode);
            }
            Op::GroupEnd => {
                modes.pop();
            }
        }
    }
    output
}

#[cfg(test)]
fn whole_document_flat_widths(ops: &[Op]) -> Vec<Option<usize>> {
    let mut result = vec![None; ops.len()];
    let mut stack: Vec<(usize, Option<usize>)> = Vec::new();
    for (index, op) in ops.iter().enumerate() {
        let width = match op {
            Op::Text(value) => Some(value.chars().count()),
            Op::Line(flat) => Some(flat.chars().count()),
            Op::HardLine => None,
            Op::NestStart(_) | Op::NestEnd(_) => Some(0),
            Op::GroupStart => {
                stack.push((index, Some(0)));
                continue;
            }
            Op::GroupEnd => {
                let (start, width) = stack.pop().expect("group markers are balanced");
                result[start] = width;
                width
            }
        };
        if let Some((_, total)) = stack.last_mut() {
            *total = match (*total, width) {
                (Some(total), Some(width)) => total.checked_add(width),
                _ => None,
            };
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use std::io;

    use proptest::prelude::*;

    use super::{Doc, Op, RenderMode, render, whole_document_render, write_spaces};

    #[test]
    fn indentation_is_exact_across_chunk_boundaries_and_partial_writes() {
        for count in [
            0,
            1,
            16 * 1024 - 1,
            16 * 1024,
            16 * 1024 + 1,
            2 * 16 * 1024 + 7,
        ] {
            let mut output = Trickle {
                bytes: Vec::new(),
                limit: 7_000,
            };
            write_spaces(&mut output, count).unwrap();
            assert_eq!(output.bytes, vec![b' '; count]);
        }
    }

    /// A writer that accepts at most `limit` bytes per call, so `render` is exercised through
    /// partial writes as a pipe or socket gives them.
    struct Trickle {
        bytes: Vec<u8>,
        limit: usize,
    }

    impl io::Write for Trickle {
        fn write(&mut self, buffer: &[u8]) -> io::Result<usize> {
            let taken = buffer.len().min(self.limit);
            self.bytes.extend_from_slice(&buffer[..taken]);
            Ok(taken)
        }

        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    fn streamed(document: &Doc, mode: RenderMode, width: usize, limit: usize) -> String {
        let mut output = Trickle {
            bytes: Vec::new(),
            limit,
        };
        render(document.ops.iter().cloned(), mode, width, &mut output).unwrap();
        String::from_utf8(output.bytes).unwrap()
    }

    /// Balanced documents over every op kind, including shapes the printer never builds: empty
    /// groups, long runs of zero-width ops, hard lines inside groups, and multi-byte text.
    fn document() -> impl Strategy<Value = Doc> {
        let leaf = prop_oneof![
            4 => prop_oneof![
                "[a-z(),]{0,12}",
                "[a-z]{20,60}",
                prop::collection::vec(any::<char>(), 0..4).prop_map(String::from_iter),
            ]
            .prop_map(Doc::text),
            2 => Just(Doc::line()),
            2 => Just(Doc::line_break()),
            1 => Just(Doc::hard_line()),
            1 => Just(Doc::from_ops(Vec::new())),
        ];
        leaf.prop_recursive(8, 256, 6, |inner| {
            prop_oneof![
                prop::collection::vec(inner.clone(), 0..6).prop_map(Doc::concat),
                (inner.clone(), 0usize..5).prop_map(|(document, amount)| document.nest(amount)),
                inner.clone().prop_map(Doc::group),
                inner.prop_map(|document| {
                    // An empty group and nest pair that `Doc::group` and `Doc::nest` skip.
                    let mut ops = vec![Op::GroupStart, Op::NestStart(1)];
                    ops.extend(document.ops);
                    ops.extend([Op::NestEnd(1), Op::GroupEnd]);
                    Doc::from_ops(ops)
                }),
            ]
        })
    }

    proptest! {
        #[test]
        fn streaming_render_matches_whole_document_render(
            document in document(),
            width in prop_oneof![0usize..8, 8usize..120, Just(usize::MAX)],
            limit in 1usize..16,
        ) {
            for mode in [RenderMode::Pretty, RenderMode::Compact] {
                prop_assert_eq!(
                    streamed(&document, mode, width, limit),
                    whole_document_render(&document, mode, width)
                );
            }
        }
    }
}
