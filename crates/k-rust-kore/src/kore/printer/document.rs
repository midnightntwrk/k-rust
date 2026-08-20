#[derive(Clone, Debug)]
pub(super) enum Doc {
    Nil,
    Text(String),
    Line(&'static str),
    HardLine,
    Concat(Vec<Self>),
    Nest(usize, Box<Self>),
    Group(Box<Self>),
}

impl Doc {
    pub(super) fn text(value: impl Into<String>) -> Self {
        Self::Text(value.into())
    }

    pub(super) const fn line() -> Self {
        Self::Line(" ")
    }

    pub(super) const fn line_break() -> Self {
        Self::Line("")
    }

    pub(super) const fn hard_line() -> Self {
        Self::HardLine
    }

    pub(super) fn concat(documents: impl IntoIterator<Item = Self>) -> Self {
        let documents: Vec<_> = documents
            .into_iter()
            .filter(|document| !matches!(document, Self::Nil))
            .collect();
        match documents.len() {
            0 => Self::Nil,
            1 => documents.into_iter().next().expect("length checked"),
            _ => Self::Concat(documents),
        }
    }

    pub(super) fn nest(self, amount: usize) -> Self {
        Self::Nest(amount, Box::new(self))
    }

    pub(super) fn group(self) -> Self {
        Self::Group(Box::new(self))
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum RenderMode {
    Compact,
    Pretty,
}

pub(super) fn render(document: &Doc, mode: RenderMode, width: usize) -> String {
    let mut state = RenderState {
        output: String::new(),
        column: 0,
        width,
    };
    let initial_mode = match mode {
        RenderMode::Compact => Mode::Flat,
        RenderMode::Pretty => Mode::Break,
    };
    state.render(document, 0, initial_mode);
    state.output
}

#[derive(Clone, Copy)]
enum Mode {
    Flat,
    Break,
}

struct RenderState {
    output: String,
    column: usize,
    width: usize,
}

impl RenderState {
    fn render(&mut self, document: &Doc, indentation: usize, mode: Mode) {
        match document {
            Doc::Nil => {}
            Doc::Text(value) => {
                self.output.push_str(value);
                self.column += value.chars().count();
            }
            Doc::Line(flat) => match mode {
                Mode::Flat => {
                    self.output.push_str(flat);
                    self.column += flat.chars().count();
                }
                Mode::Break => self.newline(indentation),
            },
            Doc::HardLine => self.newline(indentation),
            Doc::Concat(documents) => {
                for document in documents {
                    self.render(document, indentation, mode);
                }
            }
            Doc::Nest(amount, document) => {
                self.render(document, indentation + amount, mode);
            }
            Doc::Group(document) => {
                let group_mode = match mode {
                    Mode::Flat => Mode::Flat,
                    Mode::Break if self.fits(document) => Mode::Flat,
                    Mode::Break => Mode::Break,
                };
                self.render(document, indentation, group_mode);
            }
        }
    }

    fn fits(&self, document: &Doc) -> bool {
        flat_width(document).is_some_and(|width| self.column + width <= self.width)
    }

    fn newline(&mut self, indentation: usize) {
        self.output.push('\n');
        self.output.extend(std::iter::repeat_n(' ', indentation));
        self.column = indentation;
    }
}

fn flat_width(document: &Doc) -> Option<usize> {
    match document {
        Doc::Nil => Some(0),
        Doc::Text(value) => Some(value.chars().count()),
        Doc::Line(flat) => Some(flat.chars().count()),
        Doc::HardLine => None,
        Doc::Concat(documents) => documents.iter().try_fold(0usize, |width, document| {
            width.checked_add(flat_width(document)?)
        }),
        Doc::Nest(_, document) | Doc::Group(document) => flat_width(document),
    }
}
