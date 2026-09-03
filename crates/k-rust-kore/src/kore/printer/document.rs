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

pub(super) fn render(document: &Doc, mode: RenderMode, width: usize) -> String {
    let flat_widths = flat_widths(&document.ops);
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Mode {
    Flat,
    Break,
}

fn flat_widths(ops: &[Op]) -> Vec<Option<usize>> {
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
    debug_assert!(stack.is_empty());
    result
}
