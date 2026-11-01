//! Whether a printed state reads back as the state.
//!
//! A printed term is a claim: "this is the state". It holds only where reading the text back,
//! with the grammar of the sort where it stands, gives the same term, instance and token sort
//! included. The check is made per cell, the unit a reader meets: the main cell's first item
//! (`<k> head`) and every other leaf cell's content, each printed alone and read back at its
//! sort.
//!
//! Which grammar reads a cell back is decided by what the state holds there:
//!
//! - **The program grammar** (the syntax module's, the one `krs run` reads a program with) reads
//!   a cell whose content is program text throughout: every symbol it applies has a production
//!   in that grammar, and every token's print reads back as the token where it stands. A `<k>`
//!   item is read at the sort it is injected from, then at `$PGM`'s (an alias of a wider sort
//!   reads back as a value of the item's). Its tokens compare with their sorts.
//! - **The main module's grammar** reads every other cell: one whose content applies a builtin
//!   collection's constructor (`SetItem`, `_|->_`) or a production the partition placed in the
//!   semantics module, and one of a sort the program grammar does not have (a `Map` cell). It
//!   holds every token sort of the definition, so its scanner reads `word` as an `Id` wherever
//!   it stands, also where the state holds a `Word`: its tokens compare by text alone. Such a
//!   cell is no program text, and the grammar may read its print several ways (`size ( .Map )`
//!   is the definition's own `size` over an item and the map's `size`): the print reads back
//!   where the term the state holds is one of the readings, which the parser lists up to
//!   [`k_rust::inner::LISTED_READINGS`]; past that the ambiguity fails. A program must read one
//!   way, so for the program grammar an ambiguity fails.
//!
//! A cell is not read back, for a stated reason ([`ReadBack::Skipped`]), where its print says it
//! is no program text (a warning: a symbol printed as KAST, an application whose instance no
//! text fixes printed as KORE), where it groups a child of a sort but `K` in K's default bracket
//! `( .. )`, which neither grammar has (a map whose key is a map: `_|->_` is non-associative and
//! no bracket groups a map, so neither grammar writes that term at all), where its sort has
//! parameters (no `--sort` names one), and where it holds a part no grammar of the definition
//! writes: a variable (a symbolic state's), a matching-logic connective, a cell, a token neither
//! grammar reads back as itself (the `Id` `$x`).

use std::collections::{BTreeMap, BTreeSet};

use k_rust::kore::ast::{Pattern, Sort};

use crate::configuration::Reader;
use crate::values::{Value, ValueIndex};
use crate::{ExecError, Printed, ProgramInput, Semantics, Term, reversal, unparse};

/// One cell of a state as a printer prints it, the unit a print is read back by.
#[derive(Clone, Debug)]
pub struct PrintedCell<'t> {
    /// Where the print stands: `<k> head` for the main cell's first item, else the cell
    /// (`<env>`).
    pub place: String,
    /// The cell's K name (`k`, `env`).
    cell: String,
    /// What the cell's content is read back at.
    at: At,
    /// The term the state holds there.
    pub content: &'t Pattern,
    /// Its print.
    pub printed: Printed,
}

/// What a printed cell is read back at.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum At {
    /// The main cell's first item: at the sort it is injected from, then at `$PGM`'s.
    Head,
    /// A leaf cell's content at its declared K sort.
    Sort(String),
    /// A leaf cell whose declared sort, here in KORE, has parameters.
    Parametric(String),
}

/// How a printed cell reads back.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ReadBack {
    /// It reads back as the term the state holds.
    Reads,
    /// It is not read back, for the reason stated.
    Skipped(String),
    /// It does not read back as the term the state holds: how.
    Fails(String),
}

/// What reading one printed text with one grammar gave, kept by [`Semantics::read_back`].
#[derive(Clone, Debug)]
pub(crate) enum Read {
    /// The terms the text reads as: one, or, for the main module's grammar, each reading of an
    /// ambiguous text the parser lists.
    Terms(Vec<Pattern>),
    /// The grammar has no syntax for the sort the text is read at.
    NoSort,
    /// The text does not parse: the first line of the error.
    Fails(String),
}

/// The key of a [`Read`]: the grammar, the cell, what it is read at, and the text.
pub(crate) type ReadKey = (Reader, String, String, String);

impl Semantics {
    /// Every cell of `state` that a print is read back by, printed by `printer` as `krs run`
    /// prints a state (pretty, without colour): first each main cell's first item, then every
    /// other leaf cell's content.
    #[must_use]
    pub fn printed_cells<'t>(
        &self,
        printer: &unparse::Unparser,
        state: &'t Term,
    ) -> Vec<PrintedCell<'t>> {
        let options = unparse::Options::new(unparse::Mode::Pretty);
        let main = self.main_cell().map(|cell| format!("<{cell}>"));
        let mut heads = Vec::new();
        let mut cells = Vec::new();
        for (symbol, content) in state.leaf_cells() {
            let label = unparse::label_name(symbol);
            let cell = label
                .trim_start_matches('<')
                .trim_end_matches('>')
                .to_owned();
            if main.as_deref() == Some(label.as_str()) {
                if let Some(item) = crate::report::first_item(content) {
                    heads.push(PrintedCell {
                        place: format!("{label} head"),
                        cell,
                        at: At::Head,
                        content: item,
                        printed: printer.print_kore(item, &options),
                    });
                }
                continue;
            }
            let Some(sort) = printer
                .argument_sorts(symbol)
                .and_then(<[Sort]>::first)
                .cloned()
            else {
                continue;
            };
            let at = match &sort {
                Sort::Application { name, arguments } if arguments.is_empty() => {
                    name.strip_prefix("Sort").map_or_else(
                        || At::Parametric(sort.to_string()),
                        |name| At::Sort(unparse::decode_kore(name)),
                    )
                }
                _ => At::Parametric(sort.to_string()),
            };
            cells.push(PrintedCell {
                place: label,
                cell,
                at,
                content,
                printed: printer.print_kore(content, &options),
            });
        }
        heads.extend(cells);
        heads
    }

    /// Every printed cell of `state`, as [`Self::printed_cells`] prints it with the printer
    /// `krs run` prints with, and how it reads back ([`Self::read_back`]).
    ///
    /// # Errors
    ///
    /// Fails as [`Self::read_back`] does.
    pub fn check_prints<'t>(
        &mut self,
        state: &'t Term,
    ) -> Result<Vec<(PrintedCell<'t>, ReadBack)>, ExecError> {
        let cells = self.printed_cells(&self.unparser, state);
        cells
            .into_iter()
            .map(|cell| {
                let read = self.read_back(&cell)?;
                Ok((cell, read))
            })
            .collect()
    }

    /// How `cell`'s print reads back: with the program grammar where its content is program
    /// text throughout, else with the main module's grammar, as the module documentation states.
    /// A text read once with a grammar is not parsed again (a search's states share most cells).
    ///
    /// # Errors
    ///
    /// Returns [`ExecError::Backend`] where a grammar's parser cannot be built.
    pub fn read_back(&mut self, cell: &PrintedCell<'_>) -> Result<ReadBack, ExecError> {
        if !cell.printed.warnings.is_empty() {
            let warnings = cell
                .printed
                .warnings
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join("; ");
            return Ok(ReadBack::Skipped(format!(
                "its print says it is no program text: {warnings}"
            )));
        }
        // The ground K-value grammar a `K` cell is read with has the bracket at `K`.
        if cell.printed.grouped.iter().any(|sort| sort != "K") {
            let sorts = cell
                .printed
                .grouped
                .iter()
                .map(|sort| format!("`{sort}`"))
                .collect::<Vec<_>>()
                .join(", ");
            return Ok(ReadBack::Skipped(format!(
                "its print groups {sorts} in K's default bracket `( .. )`, where the definition declares no bracket, which neither grammar it is read with has"
            )));
        }
        if let At::Parametric(sort) = &cell.at {
            return Ok(ReadBack::Skipped(format!(
                "its sort `{sort}` has parameters, which no sort to read text at names"
            )));
        }
        let k_cell = cell.at == At::Sort("K".to_owned());
        if self
            .unwritten(Reader::Program, cell.content, k_cell)?
            .is_none()
        {
            match self.read(Reader::Program, cell) {
                Read::Terms(read) => return Ok(self.compare(cell, &read, true)),
                Read::Fails(error) => return Ok(fails_to_read(cell, &error)),
                Read::NoSort => {}
            }
        }
        if let Some(part) = self.unwritten(Reader::Main, cell.content, k_cell)? {
            return Ok(ReadBack::Skipped(format!(
                "it holds {part}, which no grammar of the definition writes"
            )));
        }
        Ok(match self.read(Reader::Main, cell) {
            Read::Terms(read) => self.compare(cell, &read, false),
            Read::Fails(error) => fails_to_read(cell, &error),
            Read::NoSort => ReadBack::Fails(format!(
                "{} printed `{}`, which no grammar of the definition reads at its sort",
                cell.place, cell.printed.text
            )),
        })
    }

    /// `cell`'s print read with `reader`'s grammar, as [`Self::read_back`] states, kept by text.
    fn read(&mut self, reader: Reader, cell: &PrintedCell<'_>) -> Read {
        let at = match &cell.at {
            At::Head => injected_sort(cell.content),
            At::Sort(sort) => Some(sort.clone()),
            At::Parametric(_) => None,
        };
        let key = (
            reader,
            cell.cell.clone(),
            at.clone().unwrap_or_default(),
            cell.printed.text.clone(),
        );
        if let Some(read) = self.print_reads.get(&key) {
            return read.clone();
        }
        let read = self.read_uncached(reader, cell, at.as_deref());
        self.print_reads.insert(key, read.clone());
        read
    }

    fn read_uncached(&mut self, reader: Reader, cell: &PrintedCell<'_>, at: Option<&str>) -> Read {
        let text = &cell.printed.text;
        let read = match (reader, &cell.at) {
            (Reader::Program, _) => {
                let Some(at) = at else {
                    return Read::NoSort;
                };
                let input = ProgramInput {
                    name: format!("the printed <{}>", cell.cell),
                    text: text.clone(),
                };
                match self.parse(Some(at), &input) {
                    Ok(term) => Ok(vec![term.kore().clone()]),
                    Err(ExecError::UnknownSort { .. }) => return Read::NoSort,
                    // A `<k>` item is any term a program can write there: an alias of a wider
                    // sort reads back at `$PGM`'s.
                    Err(error) if cell.at == At::Head => self
                        .parse(None, &input)
                        .map(|term| vec![term.kore().clone()])
                        .map_err(|_| error),
                    Err(error) => Err(error),
                }
            }
            // A cell read with the main module's grammar is no program text: the grammar may
            // read the text several ways (a builtin collection's `size` beside the
            // definition's), and the print reads back where the term the state holds is one of
            // them.
            (Reader::Main, At::Head) => self.parse_computation_head_readings(text),
            (Reader::Main, _) => match at {
                Some(at) => self.parse_cell_readings(&cell.cell, at, text),
                None => return Read::NoSort,
            },
        };
        match read {
            Ok(terms) => Read::Terms(terms),
            Err(error) => Read::Fails(first_line(&error.to_string()).to_owned()),
        }
    }

    /// Whether one of `read`, the readings of `cell`'s print, is the term the state holds,
    /// value for value: with every instance and, where `typed`, every token's sort.
    fn compare(&self, cell: &PrintedCell<'_>, read: &[Pattern], typed: bool) -> ReadBack {
        let index = &self.values;
        let held = shape(index, cell.content, typed);
        if read
            .iter()
            .any(|reading| shape(index, reading, typed) == held)
        {
            return ReadBack::Reads;
        }
        let readings = read
            .iter()
            .map(|reading| format!("`{reading}`"))
            .collect::<Vec<_>>();
        let reads = match &readings[..] {
            [one] => format!("reads back as {one}"),
            several => format!("reads back as one of {}", several.join(", ")),
        };
        ReadBack::Fails(format!(
            "{} printed `{}`, which {reads}, where the state holds `{}`",
            cell.place, cell.printed.text, cell.content
        ))
    }

    /// The first part of `term`, a state's term, that `reader`'s grammar does not write, named:
    /// an application of a symbol it has no production for, a token whose printed text it does
    /// not read back as the token where it stands (the `Id` `$x`), each judged as alias reversal
    /// judges a clause's subject; or a variable, a matching-logic connective or another pattern
    /// no grammar writes. In a `K` cell (`k_cell`), read with the main module's grammar, `.K` and
    /// `~>` are written: that cell is read with the ground K-value grammar. `None` where `term`
    /// is that grammar's text throughout: then a faithful print of it reads back with that
    /// grammar.
    fn unwritten(
        &mut self,
        reader: Reader,
        term: &Pattern,
        k_cell: bool,
    ) -> Result<Option<String>, ExecError> {
        let grammar = |error: Box<dyn std::error::Error>| {
            ExecError::Backend(format!(
                "the grammar a printed state is read back with cannot be built: {error}"
            ))
        };
        // Each part beside the sort of the position it stands at exactly, where known; the
        // walk is iterative, since a `~>` sequence or a cons list can be deeper than the stack.
        let mut stack: Vec<(&Pattern, Option<&Sort>)> = vec![(term, None)];
        while let Some((part, position)) = stack.pop() {
            match part {
                Pattern::DomainValue { sort, .. } => {
                    let printed = self
                        .unparser
                        .print_kore(
                            part,
                            &unparse::Options {
                                reverse_aliases: false,
                                ..unparse::Options::new(unparse::Mode::Program)
                            },
                        )
                        .text;
                    let reads = self
                        .configuration
                        .read_token_in(reader, position.unwrap_or(sort), &printed)
                        .is_some_and(|read| {
                            reversal::same_token(&self.values, &read, part)
                                // The main module's grammar holds every token sort, and its
                                // tokens compare by text: the same text at another token sort
                                // is written.
                                || (reader == Reader::Main && same_text(&read, part))
                        });
                    if !reads {
                        return Ok(Some(format!("the token `{printed}`")));
                    }
                }
                Pattern::Application { symbol, arguments } if symbol.name == "inj" => {
                    if let Some(argument) = arguments.first() {
                        stack.push((argument, symbol.sort_parameters.get(1)));
                    }
                }
                Pattern::Application { symbol, arguments }
                | Pattern::AssociativeApplication {
                    symbol, arguments, ..
                } => {
                    let sequence = k_cell
                        && reader == Reader::Main
                        && matches!(symbol.name.as_str(), "kseq" | "dotk");
                    if !sequence
                        && !self
                            .configuration
                            .writes_symbol_in(reader, &symbol.name)
                            .map_err(grammar)?
                    {
                        return Ok(Some(format!("`{}`", unparse::label_name(&symbol.name))));
                    }
                    stack.extend(arguments.iter().rev().map(|argument| (argument, None)));
                }
                Pattern::Variable(variable) => {
                    return Ok(Some(format!("the variable `{}`", variable.name)));
                }
                other => return Ok(Some(format!("`{other}`"))),
            }
        }
        Ok(None)
    }
}

/// Whether `read` and `token` are domain values of one text, whatever their sorts.
fn same_text(read: &Pattern, token: &Pattern) -> bool {
    matches!((read, token), (
        Pattern::DomainValue { value: read, .. },
        Pattern::DomainValue { value: token, .. },
    ) if read.as_bytes() == token.as_bytes())
}

fn fails_to_read(cell: &PrintedCell<'_>, error: &str) -> ReadBack {
    ReadBack::Fails(format!(
        "{} printed `{}`, which does not read back: {error}",
        cell.place, cell.printed.text
    ))
}

fn first_line(text: &str) -> &str {
    text.lines().next().unwrap_or_default()
}

/// The K sort a `KItem` is injected from (`inj{SortStmt{}, SortKItem{}}(..)` is a `Stmt`).
fn injected_sort(item: &Pattern) -> Option<String> {
    match item {
        Pattern::Application { symbol, .. } if symbol.name == "inj" => {
            match symbol.sort_parameters.first() {
                Some(Sort::Application { name, arguments }) if arguments.is_empty() => {
                    name.strip_prefix("Sort").map(unparse::decode_kore)
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// A term as two prints of it are compared: its value, constructors with their instances,
/// collections as collections; an application no KRS declaration describes by its symbol, its
/// instance and its arguments, below the injections the reader puts around a term; a token by
/// its text, and by its sort where `typed`.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Shape {
    Ctor {
        decl: String,
        instance: Vec<String>,
        fields: Vec<Shape>,
    },
    /// An `Int`, `Bool`, `String`, `Bytes` or `Float`, whose value is its identity.
    Literal(Value),
    Token {
        sort: Option<String>,
        text: String,
    },
    Seq(Vec<Shape>),
    List(Vec<Shape>),
    Set(BTreeSet<Shape>),
    Map(BTreeMap<Shape, Shape>),
    Application {
        symbol: String,
        instance: Vec<String>,
        arguments: Vec<Shape>,
    },
    Pattern(String),
}

fn shape(index: &ValueIndex, pattern: &Pattern, typed: bool) -> Shape {
    match index.decode(pattern) {
        Ok(Value::Opaque(opaque)) => opaque_shape(index, &opaque, typed),
        Ok(value) => value_shape(index, &value, typed),
        Err(_) => opaque_shape(index, pattern, typed),
    }
}

fn value_shape(index: &ValueIndex, value: &Value, typed: bool) -> Shape {
    let all = |values: &[Value]| {
        values
            .iter()
            .map(|value| value_shape(index, value, typed))
            .collect()
    };
    match value {
        Value::Ctor(ctor) => Shape::Ctor {
            decl: ctor.decl().to_string(),
            instance: ctor.sort_args().iter().map(ToString::to_string).collect(),
            fields: ctor
                .fields()
                .iter()
                .map(|(_, value)| value_shape(index, value, typed))
                .collect(),
        },
        Value::Token { sort, text } => Shape::Token {
            sort: typed.then(|| sort.to_string()),
            text: text.clone(),
        },
        Value::Seq(items) => Shape::Seq(all(items)),
        Value::List(items) => Shape::List(all(items)),
        Value::Set(elements) => Shape::Set(
            elements
                .iter()
                .map(|value| value_shape(index, value, typed))
                .collect(),
        ),
        Value::Map(entries) => Shape::Map(
            entries
                .iter()
                .map(|(key, value)| {
                    (
                        value_shape(index, key, typed),
                        value_shape(index, value, typed),
                    )
                })
                .collect(),
        ),
        Value::Opaque(pattern) => opaque_shape(index, pattern, typed),
        literal => Shape::Literal(literal.clone()),
    }
}

/// A pattern with no KRS description: below an injection, its argument's shape; an
/// application by its symbol, instance and arguments; anything else by its text.
fn opaque_shape(index: &ValueIndex, pattern: &Pattern, typed: bool) -> Shape {
    match pattern {
        Pattern::Application { symbol, arguments } if symbol.name == "inj" => {
            match arguments.as_slice() {
                [argument] => shape(index, argument, typed),
                _ => Shape::Pattern(pattern.to_string()),
            }
        }
        Pattern::Application { symbol, arguments }
        | Pattern::AssociativeApplication {
            symbol, arguments, ..
        } => Shape::Application {
            symbol: symbol.name.clone(),
            instance: symbol
                .sort_parameters
                .iter()
                .map(ToString::to_string)
                .collect(),
            arguments: arguments
                .iter()
                .map(|argument| shape(index, argument, typed))
                .collect(),
        },
        Pattern::DomainValue { sort, value } => Shape::Token {
            sort: typed.then(|| sort.to_string()),
            text: String::from_utf8_lossy(value.as_bytes()).into_owned(),
        },
        other => Shape::Pattern(other.to_string()),
    }
}
