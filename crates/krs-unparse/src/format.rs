//! The formatter: `kore_composite_pattern::pretty_print` of the LLVM backend's `kprint`.
//!
//! A format is the production's `format` attribute as `syntaxDefinition.kore` records it: `%N`
//! prints argument N, `%n` a newline, `%i`/`%d` indent and dedent by two spaces, `%c` switches to
//! the production's next colour, `%r` resets the colour, and `%x` prints `x` (so `%%` prints `%`).
//! A child printed through `%N` that is an application of the same associative symbol is printed
//! with the parent's own indentation removed (K's "assoc dedent").

use std::collections::BTreeSet;
use std::fmt::Write as _;

use k_rust::kore::ast::Sort;

use crate::data::PrintData;
use crate::node::{App, Node};
use crate::program::{Item, ProgramProduction};

/// The authored formats of the program grammar, by KORE symbol name.
pub(crate) type ProgramFormats = std::collections::BTreeMap<String, ProgramProduction>;

/// The ANSI code K's printer writes for each colour name (`kprint`'s 256-colour table).
const COLORS: &[(&str, u8)] = &include!("colors.in");

const RESET: &str = "\x1b[0m";

/// The escape sequence for a colour name, or nothing for a name K does not know.
fn color_code(name: &str) -> Option<u8> {
    COLORS
        .iter()
        .find(|(known, _)| *known == name)
        .map(|(_, code)| *code)
}

/// Problems the formatter found; each degrades the output instead of failing the print.
#[derive(Debug, Default)]
pub(crate) struct Problems {
    /// Symbols without a printable production, printed as KAST.
    pub unprintable: BTreeSet<String>,
    /// Symbols whose `colors` list is shorter than their `%c` count.
    pub short_colors: BTreeSet<String>,
    /// Symbols whose format names an argument the symbol does not have, or ends in `%`.
    pub bad_formats: BTreeSet<String>,
    /// Symbols whose format names a regex terminal.
    pub regex_formats: BTreeSet<String>,
}

/// One printing pass: `kprint`'s global indentation state and output stream.
pub(crate) struct Printer<'a> {
    data: &'a PrintData,
    program: Option<&'a ProgramFormats>,
    color: bool,
    indent: i64,
    at_new_line: bool,
    out: Vec<u8>,
    pub problems: &'a mut Problems,
}

impl<'a> Printer<'a> {
    pub fn new(data: &'a PrintData, color: bool, problems: &'a mut Problems) -> Self {
        Self {
            data,
            program: None,
            color,
            indent: 0,
            at_new_line: true,
            out: Vec::new(),
            problems,
        }
    }

    /// A printer that starts mid-line, as `sort_collections` and `filter_substitution` print their keys.
    pub fn mid_line(data: &'a PrintData, problems: &'a mut Problems) -> Self {
        let mut printer = Self::new(data, false, problems);
        printer.at_new_line = false;
        printer
    }

    /// Format the productions of `program` as the Java frontend does (`kast --output program`).
    pub fn with_program(mut self, program: &'a ProgramFormats) -> Self {
        self.program = Some(program);
        self
    }

    pub fn finish(self) -> String {
        String::from_utf8_lossy(&self.out).into_owned()
    }

    fn print_indent(&mut self) {
        if self.at_new_line {
            for _ in 0..(2 * self.indent).max(0) {
                self.out.push(b' ');
            }
            self.at_new_line = false;
        }
    }

    fn append(&mut self, text: &[u8]) {
        self.print_indent();
        self.out.extend_from_slice(text);
    }

    fn newline(&mut self) {
        self.out.push(b'\n');
        self.at_new_line = true;
    }

    fn set_color(&mut self, name: &str) {
        if self.color {
            match color_code(name) {
                Some(code) => self.append(format!("\x1b[38;5;{code}m").as_bytes()),
                // `kprint` appends the empty string its table returns for an unknown name.
                None => self.print_indent(),
            }
        }
    }

    fn sort(&mut self, sort: &Sort) {
        match sort {
            Sort::Variable(name) => self.append(name.as_bytes()),
            Sort::Application { name, arguments } => {
                self.append(name.get(4..).unwrap_or("").as_bytes());
                if !arguments.is_empty() {
                    self.append(b"{");
                    for (index, argument) in arguments.iter().enumerate() {
                        if index > 0 {
                            self.append(b",");
                        }
                        self.sort(argument);
                    }
                    self.append(b"}");
                }
            }
        }
    }

    pub fn print(&mut self, node: &Node) {
        match node {
            Node::Var { name, set, sort } => {
                // `kprint` strips the first three characters (`Var`) of the KORE name, `@` included for a set variable.
                let full = if *set {
                    format!("@{name}")
                } else {
                    name.clone()
                };
                self.append(decode_kore(full.get(3..).unwrap_or("")).as_bytes());
                self.append(b":");
                self.sort(sort);
            }
            Node::Str(text) => {
                let quoted = enquote_string(text);
                self.append(quoted.as_bytes());
            }
            Node::App(app) if app.sym.name == "\\dv" => self.domain_value(app),
            Node::App(app) => self.application(app),
        }
    }

    fn domain_value(&mut self, app: &App) {
        let Some(Node::Str(text)) = app.args.first() else {
            return;
        };
        let hook = match app.sym.formals.first() {
            Some(Sort::Application { name, .. }) => self.data.hooks.get(name).map(String::as_str),
            _ => None,
        };
        match hook {
            Some("STRING.String") => {
                let quoted = enquote_string(text);
                self.append(quoted.as_bytes());
            }
            Some("BYTES.Bytes") => {
                let quoted = enquote(text);
                self.append(b"b");
                self.append(quoted.as_bytes());
            }
            _ => self.append(text),
        }
    }

    fn application(&mut self, app: &App) {
        let name = app.sym.name.as_str();
        if let Some(production) = self.program.and_then(|program| program.get(name)) {
            self.java_format(app, production);
            return;
        }
        let Some(format) = self.data.format.get(name) else {
            self.problems.unprintable.insert(name.to_owned());
            let text = crate::kast_text(&Node::App(app.clone()));
            self.append(text.as_bytes());
            return;
        };
        let format = format.as_bytes();
        let mut local_indent = 0_i64;
        let mut local_color = 0_usize;
        let mut index = 0;
        while index < format.len() {
            let character = format[index];
            if character != b'%' {
                self.append(&[character]);
                index += 1;
                continue;
            }
            let Some(&code) = format.get(index + 1) else {
                self.problems.bad_formats.insert(name.to_owned());
                return;
            };
            index += 2;
            match code {
                b'n' => self.newline(),
                b'i' => {
                    self.indent += 1;
                    local_indent += 1;
                }
                b'd' => {
                    self.indent -= 1;
                    local_indent -= 1;
                }
                b'c' => {
                    if let Some(colors) = self.data.colors.get(name) {
                        match colors.get(local_color) {
                            Some(color) => {
                                let color = color.clone();
                                self.set_color(&color);
                            }
                            None => {
                                self.problems.short_colors.insert(name.to_owned());
                            }
                        }
                        local_color += 1;
                    }
                }
                b'r' => {
                    if self.color {
                        self.append(RESET.as_bytes());
                    }
                }
                b'0'..=b'9' => {
                    let start = index - 1;
                    while index < format.len() && format[index].is_ascii_digit() {
                        index += 1;
                    }
                    let position = std::str::from_utf8(&format[start..index])
                        .ok()
                        .and_then(|digits| digits.parse::<usize>().ok())
                        .unwrap_or(0);
                    let Some(inner) = position.checked_sub(1).and_then(|at| app.args.get(at))
                    else {
                        self.problems.bad_formats.insert(name.to_owned());
                        continue;
                    };
                    let assoc = matches!(inner, Node::App(child) if child.sym.name == name)
                        && self.data.assoc.contains(name);
                    if assoc {
                        self.indent -= local_indent;
                    }
                    self.print(inner);
                    if assoc {
                        self.indent += local_indent;
                    }
                }
                other => self.append(&[other]),
            }
        }
    }
}

impl Printer<'_> {
    /// `Formatter.format` of the Java frontend: `%N` names a production item, any other `%x` prints `x`.
    fn java_format(&mut self, app: &App, production: &ProgramProduction) {
        let name = app.sym.name.as_str();
        let format = production.format.as_bytes();
        let mut local_indent = 0_i64;
        let mut terminal_index = 0_usize;
        let mut index = 0;
        while index < format.len() {
            let character = format[index];
            if character != b'%' {
                self.append(&[character]);
                index += 1;
                continue;
            }
            let Some(&code) = format.get(index + 1) else {
                self.problems.bad_formats.insert(name.to_owned());
                return;
            };
            index += 2;
            match code {
                b'n' => self.newline(),
                b'i' => {
                    self.indent += 1;
                    local_indent += 1;
                }
                b'd' => {
                    self.indent -= 1;
                    local_indent -= 1;
                }
                b'0'..=b'9' => {
                    let start = index - 1;
                    while index < format.len() && format[index].is_ascii_digit() {
                        index += 1;
                    }
                    let position = std::str::from_utf8(&format[start..index])
                        .ok()
                        .and_then(|digits| digits.parse::<usize>().ok())
                        .unwrap_or(0);
                    let Some(item) = position
                        .checked_sub(1)
                        .and_then(|at| production.items.get(at))
                    else {
                        self.problems.bad_formats.insert(name.to_owned());
                        continue;
                    };
                    match item {
                        Item::Terminal(text) => {
                            let color =
                                production.terminal_color(terminal_index).map(str::to_owned);
                            terminal_index += 1;
                            if let Some(color) = &color {
                                self.set_color(color);
                            }
                            self.append(text.as_bytes());
                            if color.is_some() && self.color {
                                self.append(RESET.as_bytes());
                            }
                        }
                        Item::NonTerminal => {
                            let nonterminal = production.items[..position - 1]
                                .iter()
                                .filter(|item| matches!(item, Item::NonTerminal))
                                .count();
                            let Some(inner) = app.args.get(nonterminal) else {
                                self.problems.bad_formats.insert(name.to_owned());
                                continue;
                            };
                            let assoc = matches!(inner, Node::App(child) if child.sym.name == name)
                                && self.data.assoc.contains(name);
                            if assoc {
                                self.indent -= local_indent;
                            }
                            self.print(inner);
                            if assoc {
                                self.indent += local_indent;
                            }
                        }
                        Item::Regex => {
                            self.problems.regex_formats.insert(name.to_owned());
                        }
                    }
                }
                other => self.append(&[other]),
            }
        }
    }
}

/// `kprint`'s `enquote` of a KORE string literal other than a `Bytes` value.
///
/// k-rust stores such a literal as the UTF-8 encoding of its code points, while
/// the LLVM backend holds a K string as one byte per code point (K strings are
/// Latin-1), so each code point up to U+00FF is quoted as that byte. A code point
/// above U+00FF, which a K string cannot hold, is written with K's `\u` or `\U`
/// escape, and a payload that is not UTF-8 is quoted byte by byte.
#[must_use]
pub fn enquote_string(text: &[u8]) -> String {
    let Ok(text) = std::str::from_utf8(text) else {
        return enquote(text);
    };
    if text.chars().all(|code_point| u32::from(code_point) <= 0xff) {
        let latin1 = text
            .chars()
            .map(|code_point| u8::try_from(u32::from(code_point)).unwrap_or(b'?'))
            .collect::<Vec<_>>();
        return enquote(&latin1);
    }
    let mut result = String::with_capacity(text.len() + 2);
    result.push('"');
    for code_point in text.chars() {
        match u32::from(code_point) {
            value @ 0..=0xff => {
                let quoted = enquote(&[u8::try_from(value).unwrap_or(b'?')]);
                result.push_str(&quoted[1..quoted.len() - 1]);
            }
            value @ 0x100..=0xffff => {
                let _ = write!(result, "\\u{value:04x}");
            }
            value => {
                let _ = write!(result, "\\U{value:08x}");
            }
        }
    }
    result.push('"');
    result
}

/// `kprint`'s `enquote`: K string syntax, escaping every byte outside printable ASCII.
#[must_use]
pub fn enquote(text: &[u8]) -> String {
    let mut result = String::with_capacity(text.len() + 2);
    result.push('"');
    for &byte in text {
        match byte {
            b'\\' => result.push_str("\\\\"),
            b'"' => result.push_str("\\\""),
            b'\n' => result.push_str("\\n"),
            b'\t' => result.push_str("\\t"),
            b'\r' => result.push_str("\\r"),
            b'\x0c' => result.push_str("\\f"),
            32..=126 => result.push(char::from(byte)),
            _ => {
                let _ = write!(result, "\\x{byte:02x}");
            }
        }
    }
    result.push('"');
    result
}

/// `kllvm::decode_kore`: undo K's KORE identifier escapes (`'Unds'` for `_`, ...).
///
/// `kprint` maps the escape `SCln` to `l`, not `;`; that is reproduced so printed names agree.
#[must_use]
pub fn decode_kore(kore: &str) -> String {
    const CODES: &[(&str, char)] = &[
        ("Spce", ' '),
        ("Bang", '!'),
        ("Quot", '"'),
        ("Hash", '#'),
        ("Dolr", '$'),
        ("Perc", '%'),
        ("And-", '&'),
        ("Apos", '\''),
        ("LPar", '('),
        ("RPar", ')'),
        ("Star", '*'),
        ("Plus", '+'),
        ("Comm", ','),
        ("Stop", '.'),
        ("Slsh", '/'),
        ("Coln", ':'),
        ("SCln", 'l'),
        ("-LT-", '<'),
        ("Eqls", '='),
        ("-GT-", '>'),
        ("Ques", '?'),
        ("-AT-", '@'),
        ("LSqB", '['),
        ("RSqB", ']'),
        ("Bash", '\\'),
        ("Xor-", '^'),
        ("Unds", '_'),
        ("BQuo", '`'),
        ("LBra", '{'),
        ("Pipe", '|'),
        ("RBra", '}'),
        ("Tild", '~'),
    ];
    let mut literal = true;
    let mut result = String::with_capacity(kore.len());
    let mut rest = kore;
    while let Some(character) = rest.chars().next() {
        if character == '\'' {
            literal = !literal;
            rest = &rest[1..];
        } else if literal {
            result.push(character);
            rest = &rest[character.len_utf8()..];
        } else {
            let end = rest
                .char_indices()
                .nth(4)
                .map_or(rest.len(), |(offset, _)| offset);
            let code = &rest[..end];
            result.push(
                CODES
                    .iter()
                    .find(|(known, _)| *known == code)
                    .map_or('\0', |(_, decoded)| *decoded),
            );
            rest = &rest[end..];
        }
    }
    result
}

/// Print `node` with a fresh mid-line printer and no colour, as `kprint` prints sort keys.
pub(crate) fn key_text(data: &PrintData, node: &Node, problems: &mut Problems) -> String {
    let mut printer = Printer::mid_line(data, problems);
    printer.print(node);
    printer.finish()
}

/// Print a variable as `filter_substitution` does: at the start of a line, without colour.
pub(crate) fn variable_text(data: &PrintData, node: &Node, problems: &mut Problems) -> String {
    let mut printer = Printer::new(data, false, problems);
    printer.print(node);
    printer.finish()
}
