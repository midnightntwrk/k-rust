//! ```toml algorithm
//! id = "definition.outer.parse"
//! name = "recursive-descent parsing of outer syntax"
//! sites = ["parse", "Parser::module", "Parser::sentence", "Parser::production"]
//! variable = "B = source bytes; u = bytes of one bubble; a = attribute-start candidates in that bubble"
//! counters = []
//! no_counter = "outer-syntax parsing has no dedicated counter"
//! produces = [{ type = "k_rust::outer::ast::SourceFile", role = "parsed source" }]
//!
//! [[cost]]
//! mode = "one source file"
//! bound = "O(B + sum over bubbles of u x a)"
//! ```
//!
//! Outer syntax uses recursive descent with save-and-restore lookahead over a finite token stream.
//! Complexity: O(B + sum u * a) over source bytes B, with u bytes and a trailing-attribute candidates per bubble.
//! Parsing is linear in consumed tokens apart from bounded alternatives; no dedicated counter.
//!
use std::{error::Error, fmt, rc::Rc, sync::LazyLock};

use regex::Regex;

use crate::definition::AttributeKey;
use crate::definition::attribute_keys::{KeyParameter, builtin_key};
use crate::kast::Sort;
use crate::kast::sort_role::{NumeralSpelling, is_numeral_spelling, numeral_spelling};
use crate::kast::string::{HEX_ESCAPES, NAMED_ESCAPES};
use crate::lines;

use super::*;

/// Whether `character` is whitespace of a definition's text: space, tab or a line end. This is the
/// whitespace of the default layout (`crate::inner::DEFAULT_LAYOUT`, which a test keeps equal),
/// the layout the bubbles are parsed with, so a character separates the tokens around a bubble
/// exactly when it separates the tokens inside one.
pub(super) fn is_whitespace(character: char) -> bool {
    matches!(character, ' ' | '\t') || is_line_end(character)
}

/// Whether `character` begins a line terminator of `crate::lines`, the line ends every location
/// counts.
fn is_line_end(character: char) -> bool {
    lines::LINE_TERMINATORS
        .into_iter()
        .any(|terminator| terminator.starts_with(character))
}

/// [`is_whitespace`] as the body of a `regex` character class.
const WHITESPACE_CLASS: &str = r" \t\n-\r\x{85}\x{2028}\x{2029}";

const BUBBLE_TERMINATORS: [&str; 6] = [
    "syntax",
    "endmodule",
    "rule",
    "claim",
    "configuration",
    "context",
];

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseError {
    pub message: String,
    pub position: Position,
    pub fatal: bool,
}

impl fmt::Display for ParseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "{} at {}:{}",
            self.message, self.position.line, self.position.column
        )
    }
}

impl Error for ParseError {}

pub fn parse(source: impl Into<String>, input: &str) -> Result<SourceFile, ParseError> {
    let source = source.into();
    let mut parser = Parser::new(input, 0, input.len());
    let mut requires = Vec::new();
    let mut modules = Vec::new();
    // Invariant: `requires` and `modules` hold, in source order, the declarations parsed before `parser.offset`; each iteration that neither breaks nor returns consumes one `requires` or `module` declaration, so `parser.offset` increases toward the end of `input`.
    while !parser.done() {
        parser.skip_trivia()?;
        if parser.done() {
            break;
        }
        if parser.consume_word("requires") {
            let start = parser.last_start;
            let path = parser.quoted()?;
            requires.push(Require {
                path,
                span: parser.span(start, parser.offset),
            });
        } else if parser.peek_word("module") {
            modules.push(parser.module()?);
        } else {
            return Err(parser.error("expected `requires` or `module`"));
        }
    }
    Ok(SourceFile {
        source,
        source_id: crate::provenance::SourceId(0),
        requires,
        modules,
    })
}

/// The byte offsets at which the lines of `input` start: 0 and the end of each line terminator.
fn line_starts(input: &str) -> Vec<usize> {
    let mut starts = vec![0];
    let mut index = 0;
    // Invariant: `starts` holds 0 and the end of every line terminator that ends at or before `index`, which is a character boundary; each iteration moves past one character or terminator.
    while index < input.len() {
        if let Some(terminator) = lines::terminator_at(input, index) {
            index += terminator.len();
            starts.push(index);
        } else {
            index += input[index..].chars().next().map_or(1, char::len_utf8);
        }
    }
    starts
}

struct Parser<'a> {
    input: &'a str,
    line_starts: Rc<Vec<usize>>,
    offset: usize,
    end: usize,
    last_start: usize,
}

impl<'a> Parser<'a> {
    fn new(input: &'a str, offset: usize, end: usize) -> Self {
        Self {
            input,
            line_starts: Rc::new(line_starts(input)),
            offset,
            end,
            last_start: offset,
        }
    }

    fn subparser(&self, offset: usize, end: usize) -> Self {
        Self {
            input: self.input,
            line_starts: Rc::clone(&self.line_starts),
            offset,
            end,
            last_start: offset,
        }
    }

    fn module(&mut self) -> Result<Module, ParseError> {
        self.expect_word("module")?;
        let start = self.last_start;
        let name = self.module_name()?;
        let attributes = if self.peek_char_after_trivia()? == Some('[') {
            self.attributes()?
        } else {
            Vec::new()
        };
        let module_is_private = attributes
            .iter()
            .any(|attribute| attribute.key == AttributeKey::Private.as_str());
        let mut imports = Vec::new();
        let mut sentences = Vec::new();
        // Invariant: `imports` and `sentences` hold, in source order, the declarations of this module parsed before `self.offset`; each iteration that does not return consumes one import or sentence, so `self.offset` increases toward `self.end`.
        loop {
            self.skip_trivia()?;
            if self.consume_word("endmodule") {
                return Ok(Module {
                    name,
                    attributes,
                    imports,
                    sentences,
                    span: self.span(start, self.offset),
                });
            }
            if self.done() {
                return Err(self.error("expected `endmodule`"));
            }
            if self.peek_word("imports") {
                if !sentences.is_empty() {
                    return Err(self.error("unexpected `imports` after the first sentence"));
                }
                imports.push(self.import(module_is_private)?);
                continue;
            }
            sentences.push(self.sentence()?);
        }
    }

    fn import(&mut self, module_is_private: bool) -> Result<Import, ParseError> {
        self.expect_word("imports")?;
        let start = self.last_start;
        self.skip_trivia()?;
        let public = if self.consume_word("public") {
            true
        } else if self.consume_word("private") {
            false
        } else {
            !module_is_private
        };
        let module = self.module_name()?;
        Ok(Import {
            module,
            public,
            span: self.span(start, self.offset),
        })
    }

    fn sentence(&mut self) -> Result<Sentence, ParseError> {
        self.skip_trivia()?;
        if self.peek_word("syntax") {
            self.syntax_sentence()
        } else {
            self.bubble_sentence()
        }
    }

    fn syntax_sentence(&mut self) -> Result<Sentence, ParseError> {
        self.expect_word("syntax")?;
        let start = self.last_start;
        if self.consume_word("priority") {
            let (groups, end) = self.raw_groups('>')?;
            return Ok(Sentence::Priority(SyntaxPriority {
                groups,
                span: self.span(start, end),
            }));
        }
        if let Some(associativity) = self.consume_associativity() {
            let (tags, end) = self.raw_words()?;
            return Ok(Sentence::Associativity(SyntaxAssociativity {
                associativity,
                tags,
                span: self.span(start, end),
            }));
        }
        if self.consume_word("lexical") {
            let name = std::mem::take(&mut self.sort_id()?.1.name);
            self.expect_char('=')?;
            let regex = self.regex()?;
            if self.peek_char_after_trivia()? == Some('[') {
                self.skip_trivia()?;
                return Err(self.error("syntax lexical does not accept attributes"));
            }
            return Ok(Sentence::Lexical(SyntaxLexical {
                name,
                regex,
                attributes: Vec::new(),
                span: self.span(start, self.offset),
            }));
        }

        let parameters = if self.peek_char_after_trivia()? == Some('{') {
            self.sort_list('{', '}')?
        } else {
            Vec::new()
        };
        let (name, sort) = self.sort_id()?;
        let sort_end = self.offset;
        self.skip_trivia()?;
        let (body, end) = if self.consume("::=") {
            let blocks = self.priority_blocks()?;
            (SyntaxBody::Productions(blocks), self.offset)
        } else if self.consume("=") {
            let old_sort = self.sort_id()?.1;
            let attributes = if self.peek_char_after_trivia()? == Some('[') {
                self.attributes()?
            } else {
                Vec::new()
            };
            (
                SyntaxBody::Synonym {
                    old_sort,
                    attributes,
                },
                self.offset,
            )
        } else {
            let (attributes, end) = if self.peek_char_after_trivia()? == Some('[') {
                let attributes = self.attributes()?;
                (attributes, self.offset)
            } else {
                (Vec::new(), sort_end)
            };
            (SyntaxBody::Sort(attributes), end)
        };
        let name = if matches!(&body, SyntaxBody::Synonym { .. }) {
            None
        } else {
            name
        };
        Ok(Sentence::Syntax(SyntaxDeclaration {
            name,
            parameters,
            sort,
            body,
            span: self.span(start, end),
        }))
    }

    fn priority_blocks(&mut self) -> Result<Vec<PriorityBlock>, ParseError> {
        let mut blocks = Vec::new();
        // Invariant: `blocks` holds the `>`-separated priority blocks parsed before `self.offset`; each iteration that continues consumes one block and its `>` separator, so `self.offset` increases.
        loop {
            self.skip_trivia()?;
            let start = self.offset;
            let saved = self.offset;
            let associativity = self
                .consume_associativity()
                .unwrap_or(Associativity::Unspecified);
            if associativity != Associativity::Unspecified {
                self.expect_char(':')?;
            } else {
                self.offset = saved;
            }
            let mut productions = Vec::new();
            // Invariant: `productions` holds the `|`-separated productions of the current block parsed before `self.offset`; each iteration that continues consumes one production and its `|` separator.
            loop {
                productions.push(self.production()?);
                if self.peek_char_after_trivia()? == Some('|') {
                    self.expect_char('|')?;
                    continue;
                }
                break;
            }
            let end = self.offset;
            blocks.push(PriorityBlock {
                associativity,
                productions,
                span: self.span(start, end),
            });
            if self.peek_char_after_trivia()? != Some('>') {
                break;
            }
            self.expect_char('>')?;
        }
        Ok(blocks)
    }

    fn production(&mut self) -> Result<Production, ParseError> {
        self.skip_trivia()?;
        let start = self.offset;
        let mut items = Vec::new();
        let mut function_style = false;
        // Invariant: `items` holds the production items parsed from `start` to `self.offset`, and `function_style` records whether they form a function-style production; each iteration that neither breaks nor returns consumes at least one item, so `self.offset` increases toward `self.end`.
        while !self.done() {
            let before_trivia = self.offset;
            self.skip_trivia()?;
            if self.at_default_sentence_boundary() {
                self.offset = before_trivia;
                break;
            }
            if function_style
                && !matches!(self.peek_char(), Some('|') | Some('>') | Some('[') | None)
            {
                return Err(self.error("function-style production must be the whole production"));
            }
            match self.peek_char() {
                Some('|') | Some('>') | Some('[') | None => {
                    self.offset = before_trivia;
                    break;
                }
                Some('"') => items.push(ProductionItem::Terminal(self.quoted()?)),
                Some('(') => {
                    self.expect_char('(')?;
                    items.push(ProductionItem::Terminal("(".into()));
                    let arguments = self.nonterminals_until(')')?;
                    if arguments.is_empty() {
                        return Err(self.error_at(
                            self.offset - ')'.len_utf8(),
                            "parenthesized production requires at least one sort",
                        ));
                    }
                    for (index, item) in arguments.into_iter().enumerate() {
                        if index > 0 {
                            items.push(ProductionItem::Terminal(",".into()));
                        }
                        items.push(item);
                    }
                    items.push(ProductionItem::Terminal(")".into()));
                }
                _ if self.peek_user_list("List") || self.peek_user_list("NeList") => {
                    let non_empty = self.consume_word("NeList");
                    if !non_empty {
                        self.expect_word("List")?;
                    }
                    self.expect_char('{')?;
                    self.skip_trivia()?;
                    let sort_start = self.offset;
                    let sort_name = self.word()?;
                    if !is_upper_identifier(&sort_name) {
                        return Err(self.error_at(sort_start, "invalid list element sort name"));
                    }
                    if self.peek_char_after_trivia()? == Some('{') {
                        self.skip_trivia()?;
                        return Err(self.error("list element sort cannot have parameters"));
                    }
                    self.expect_char(',')?;
                    let separator = self.quoted()?;
                    self.expect_char('}')?;
                    items.push(ProductionItem::UserList {
                        sort: Sort::new(sort_name),
                        separator,
                        non_empty,
                    });
                }
                _ if self.peek_regex() => items.push(ProductionItem::Regex(self.regex()?)),
                _ => {
                    let identifier_start = self.offset;
                    let first = self.word()?;
                    let after_first = self.offset;
                    self.skip_trivia()?;
                    if self.consume(":") {
                        if !is_outer_identifier(&first) {
                            return Err(self.error_at(identifier_start, "invalid nonterminal name"));
                        }
                        items.push(ProductionItem::NonTerminal {
                            name: Some(first),
                            sort: self.sort()?,
                        });
                    } else if self.consume("(") {
                        if !items.is_empty() {
                            return Err(self.error_at(
                                identifier_start,
                                "function-style production must be the whole production",
                            ));
                        }
                        if !is_outer_identifier(&first) {
                            return Err(self.error_at(identifier_start, "invalid production name"));
                        }
                        items.push(ProductionItem::Terminal(first));
                        items.push(ProductionItem::Terminal("(".into()));
                        let arguments = self.nonterminals_until(')')?;
                        for (index, argument) in arguments.into_iter().enumerate() {
                            if index > 0 {
                                items.push(ProductionItem::Terminal(",".into()));
                            }
                            items.push(argument);
                        }
                        items.push(ProductionItem::Terminal(")".into()));
                        function_style = true;
                    } else {
                        self.offset = after_first;
                        let sort = self.finish_sort(identifier_start, first)?;
                        items.push(ProductionItem::NonTerminal { name: None, sort });
                    }
                }
            }
        }
        if items.is_empty() {
            return Err(self.error("expected a production"));
        }
        let attributes = if self.peek_char_after_trivia()? == Some('[') {
            self.attributes()?
        } else {
            Vec::new()
        };
        Ok(Production {
            items,
            attributes,
            span: self.span(start, self.offset),
        })
    }

    fn bubble_sentence(&mut self) -> Result<Sentence, ParseError> {
        let (kind, start) = if self.consume_word("rule") {
            (BubbleKind::Rule, self.last_start)
        } else if self.consume_word("claim") {
            (BubbleKind::Claim, self.last_start)
        } else if self.consume_word("configuration") {
            (BubbleKind::Configuration, self.last_start)
        } else if self.consume_word("context") {
            let start = self.last_start;
            let alias_end = self
                .peek_run()
                .and_then(|(run, _, end)| (run == "alias").then_some(end));
            let kind = if let Some(end) = alias_end {
                self.offset = end;
                BubbleKind::ContextAlias
            } else {
                BubbleKind::Context
            };
            (kind, start)
        } else {
            return Err(self.error("expected a K sentence"));
        };
        let mut content_start = None;
        let mut content_end = self.offset;
        // Invariant: `content_start` is the start of the first run consumed after the sentence keyword and `content_end` the end of the last one, which is `self.offset` once a run is consumed; each iteration consumes one run until a `BUBBLE_TERMINATORS` word or the end of input.
        while let Some((run, start, end)) = self.peek_run() {
            if BUBBLE_TERMINATORS.contains(&run) {
                break;
            }
            content_start.get_or_insert(start);
            content_end = end;
            self.offset = end;
        }
        let content_start = content_start.unwrap_or(content_end);
        let sentence_end = content_end;
        let raw = &self.input[content_start..content_end];
        let (label, after_label) = split_label(raw);
        let body_start = content_start + (raw.len() - after_label.len());
        let (content, attributes, content_end) =
            self.split_trailing_attributes(after_label, body_start)?;
        Ok(Sentence::Bubble(Bubble {
            kind,
            content,
            label,
            attributes,
            content_span: self.span(body_start, content_end),
            span: self.span(start, sentence_end),
        }))
    }

    fn split_trailing_attributes(
        &self,
        raw: &str,
        raw_start: usize,
    ) -> Result<(String, Vec<Attribute>, usize), ParseError> {
        // Invariant: no `[` offset of `attribute_starts(raw)` after `index` begins an attribute list that parses to the end of `raw`; each iteration tries one candidate, from the last offset to the first, and the first success returns.
        for index in attribute_starts(raw).into_iter().rev() {
            let mut parser = self.subparser(raw_start + index, raw_start + raw.len());
            match parser.attributes() {
                Ok(attributes) => {
                    parser.skip_trivia()?;
                    if parser.done() {
                        return Ok((
                            raw[..index].trim_end_matches(is_whitespace).to_owned(),
                            attributes,
                            raw_start + index,
                        ));
                    }
                }
                Err(error) if error.fatal => return Err(error),
                Err(_) => {}
            }
        }
        Ok((raw.to_owned(), Vec::new(), raw_start + raw.len()))
    }

    fn attributes(&mut self) -> Result<Vec<Attribute>, ParseError> {
        self.expect_char('[')?;
        let mut attributes = Vec::new();
        // Invariant: `attributes` holds the attributes parsed after `[`, with pairwise distinct keys; each iteration that continues consumes one attribute and its `,`, and the duplicate check scans `attributes`, so a list of a attributes costs O(a^2) key comparisons.
        loop {
            self.skip_trivia()?;
            if self.consume("]") {
                break;
            }
            let key = self.unrestricted_word()?;
            if !is_attribute_key(&key) {
                return Err(self.error("invalid attribute key"));
            }
            self.skip_trivia()?;
            let value = if self.consume("(") {
                Some(self.attribute_value()?)
            } else {
                None
            };
            if attributes
                .iter()
                .any(|attribute: &Attribute| attribute.key == key)
            {
                return Err(self.fatal_error(format!("Duplicate attribute: {key}")));
            }
            if let Some(builtin) = builtin_key(&key) {
                let parameter_is_present = value.as_deref().is_some_and(|value| !value.is_empty());
                let message = match builtin.parameter {
                    KeyParameter::Forbidden if parameter_is_present => Some(format!(
                        "Parameters for the attribute '{key}' are forbidden."
                    )),
                    KeyParameter::Required if !parameter_is_present => Some(format!(
                        "Parameters for the attribute '{key}' are required."
                    )),
                    _ => None,
                };
                if let Some(message) = message {
                    return Err(self.fatal_error(message));
                }
            }
            attributes.push(Attribute { key, value });
            self.skip_trivia()?;
            if self.consume(",") {
                continue;
            }
            self.expect_char(']')?;
            break;
        }
        Ok(attributes)
    }

    fn attribute_value(&mut self) -> Result<String, ParseError> {
        if self.peek_char() == Some('"') {
            self.bump();
            let value = self.string_literal("attribute string")?;
            self.skip_trivia()?;
            self.expect_raw(')')?;
            return Ok(value);
        }

        let start = self.offset;
        let mut depth = 1usize;
        loop {
            let ch = self
                .bump()
                .ok_or_else(|| self.error("unterminated attribute value"))?;
            match ch {
                '"' => return Err(self.error("quote in unquoted attribute value")),
                ch if is_line_end(ch) => {
                    return Err(self.error("newline in unquoted attribute value"));
                }
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        return Ok(self.input[start..self.offset - 1].to_owned());
                    }
                }
                _ => {}
            }
        }
    }

    fn sort(&mut self) -> Result<Sort, ParseError> {
        self.skip_trivia()?;
        let start = self.offset;
        let name = self.word()?;
        self.finish_sort(start, name)
    }

    fn sort_id(&mut self) -> Result<(Option<String>, Sort), ParseError> {
        self.skip_trivia()?;
        let start = self.offset;
        let first = self.word()?;
        let after_first = self.offset;
        self.skip_trivia()?;
        if self.starts_with(":") && !self.starts_with("::=") {
            self.expect_raw(':')?;
            if !is_outer_identifier(&first) {
                return Err(self.error_at(start, "invalid nonterminal name"));
            }
            Ok((Some(first), self.sort()?))
        } else {
            self.offset = after_first;
            Ok((None, self.finish_sort(start, first)?))
        }
    }

    fn finish_sort(&mut self, start: usize, name: String) -> Result<Sort, ParseError> {
        if let NumeralSpelling::NonCanonical { canonical } = numeral_spelling(&name) {
            return Err(self.error_at(start, format!("numeral sort {name} is written with a leading zero; a width is spelled {canonical}")));
        }
        if !is_sort_name(&name) {
            return Err(self.error_at(start, "invalid sort name"));
        }
        let parameters = if self.peek_char_after_trivia()? == Some('{') {
            if is_numeral_spelling(&name) {
                self.skip_trivia()?;
                return Err(self.error("numeric sort cannot take parameters"));
            }
            self.sort_list('{', '}')?
        } else {
            Vec::new()
        };
        Ok(Sort::with_parameters(name, parameters))
    }

    fn sort_list(&mut self, open: char, close: char) -> Result<Vec<Sort>, ParseError> {
        self.expect_char(open)?;
        self.sorts_until(close)
    }

    fn sorts_until(&mut self, close: char) -> Result<Vec<Sort>, ParseError> {
        let mut sorts = Vec::new();
        self.skip_trivia()?;
        if self.consume(&close.to_string()) {
            return Err(self.error_at(
                self.offset - close.len_utf8(),
                "sort parameter list requires at least one sort",
            ));
        }
        loop {
            sorts.push(self.sort()?);
            self.skip_trivia()?;
            if self.consume(&close.to_string()) {
                break;
            }
            self.expect_char(',')?;
        }
        Ok(sorts)
    }

    fn nonterminals_until(&mut self, close: char) -> Result<Vec<ProductionItem>, ParseError> {
        let mut items = Vec::new();
        self.skip_trivia()?;
        if self.consume(&close.to_string()) {
            return Ok(items);
        }
        loop {
            self.skip_trivia()?;
            let identifier_start = self.offset;
            let first = self.word()?;
            self.skip_trivia()?;
            let (name, sort) = if self.consume(":") {
                if !is_outer_identifier(&first) {
                    return Err(self.error_at(identifier_start, "invalid nonterminal name"));
                }
                (Some(first), self.sort()?)
            } else {
                (None, self.finish_sort(identifier_start, first)?)
            };
            items.push(ProductionItem::NonTerminal { name, sort });
            self.skip_trivia()?;
            if self.consume(&close.to_string()) {
                break;
            }
            self.expect_char(',')?;
        }
        Ok(items)
    }

    fn raw_groups(&mut self, separator: char) -> Result<(Vec<Vec<String>>, usize), ParseError> {
        let mut groups = vec![Vec::new()];
        let mut last_end = self.offset;
        // Invariant: `groups` holds the runs consumed so far, split into a new group at each `separator` run, and `last_end` is the end of the last consumed run; each iteration consumes one run until a `BUBBLE_TERMINATORS` word or the end of input.
        while let Some((run, _, end)) = self.peek_run() {
            if BUBBLE_TERMINATORS.contains(&run) {
                break;
            }
            self.offset = end;
            last_end = end;
            if run.len() == separator.len_utf8() && run.starts_with(separator) {
                groups.push(Vec::new());
            } else {
                groups.last_mut().unwrap().push(run.to_owned());
            }
        }
        Ok((groups, last_end))
    }

    fn raw_words(&mut self) -> Result<(Vec<String>, usize), ParseError> {
        let mut words = Vec::new();
        let mut last_end = self.offset;
        // Invariant: `words` holds, in order, the runs consumed so far and `last_end` is the end of the last one; each iteration consumes one run until a `BUBBLE_TERMINATORS` word or the end of input.
        while let Some((run, _, end)) = self.peek_run() {
            if BUBBLE_TERMINATORS.contains(&run) {
                break;
            }
            words.push(run.to_owned());
            self.offset = end;
            last_end = end;
        }
        Ok((words, last_end))
    }

    fn run_len(&self, offset: usize) -> usize {
        let remaining = &self.input[offset..self.end];
        remaining.find(is_whitespace).unwrap_or(remaining.len())
    }

    /// The length of the comment at `offset`, 0 when none starts there: a `//` comment runs
    /// through the first line terminator, or to the end of the text on the last line; a `/*`
    /// comment through the first `*/`, and an unterminated one is none.
    fn comment_len(&self, offset: usize) -> usize {
        let text = &self.input[offset..self.end];
        let remaining = text.as_bytes();
        if remaining.starts_with(b"//") {
            return text
                .char_indices()
                .find_map(|(index, _)| {
                    lines::terminator_at(text, index).map(|terminator| index + terminator.len())
                })
                .unwrap_or(text.len());
        }
        if remaining.starts_with(b"/*") {
            return remaining[2..]
                .windows(2)
                .position(|window| window == b"*/")
                .map_or(0, |end| end + 4);
        }
        0
    }

    fn skip_bubble_trivia(&mut self) {
        // Invariant: the text skipped before `self.offset` is whitespace and comments; each iteration that continues skips one comment longer than the run at `self.offset`, so `self.offset` increases toward `self.end`.
        loop {
            while self.peek_char().is_some_and(is_whitespace) {
                self.bump();
            }
            let run_len = self.run_len(self.offset);
            let comment_len = self.comment_len(self.offset);
            if comment_len > run_len {
                self.offset += comment_len;
            } else {
                break;
            }
        }
    }

    fn peek_run(&mut self) -> Option<(&'a str, usize, usize)> {
        self.skip_bubble_trivia();
        let start = self.offset;
        let end = start + self.run_len(start);
        (start < end).then(|| (&self.input[start..end], start, end))
    }

    fn at_default_sentence_boundary(&self) -> bool {
        [
            "syntax",
            "endmodule",
            "rule",
            "claim",
            "configuration",
            "context",
            "imports",
            "module",
            "requires",
        ]
        .into_iter()
        .any(|word| self.word_at(self.offset, word))
    }

    fn consume_associativity(&mut self) -> Option<Associativity> {
        if self.consume_word("left") {
            Some(Associativity::Left)
        } else if self.consume_word("right") {
            Some(Associativity::Right)
        } else if self.consume_word("non-assoc") {
            Some(Associativity::NonAssoc)
        } else {
            None
        }
    }

    fn quoted(&mut self) -> Result<String, ParseError> {
        self.skip_trivia()?;
        self.expect_raw('"')?;
        self.string_literal("string")
    }

    /// The characters of the K `String` literal whose opening quote precedes `self.offset`,
    /// consuming it through its closing quote: any character but `"`, `\`, newline and carriage
    /// return stands for itself, and each escape `domains.md` defines for `String` names one code
    /// point (`crate::kast::string`'s tables). `what` names the literal in errors.
    fn string_literal(&mut self, what: &str) -> Result<String, ParseError> {
        let mut result = String::new();
        loop {
            let start = self.offset;
            let ch = self
                .bump()
                .ok_or_else(|| self.error(format!("unterminated {what}")))?;
            match ch {
                '"' => return Ok(result),
                '\n' | '\r' => return Err(self.error_at(start, format!("newline in {what}"))),
                '\\' => result.push(self.string_escape(start, what)?),
                other => result.push(other),
            }
        }
    }

    /// The code point the escape whose backslash is at `start` names, consuming the rest of it.
    fn string_escape(&mut self, start: usize, what: &str) -> Result<char, ParseError> {
        let letter = self
            .peek_char()
            .ok_or_else(|| self.error(format!("unterminated {what}")))?;
        if matches!(letter, '\n' | '\r') {
            return Err(self.error(format!("newline in {what}")));
        }
        self.bump();
        if let Some((_, character)) = NAMED_ESCAPES.iter().find(|(name, _)| *name == letter) {
            return Ok(*character);
        }
        let Some((_, digits)) = HEX_ESCAPES.iter().find(|(name, _)| *name == letter) else {
            return Err(self.error_at(start, format!("invalid escape `\\{letter}` in {what}")));
        };
        let mut value = 0u32;
        for _ in 0..*digits {
            let Some(digit) = self.peek_char().and_then(|ch| ch.to_digit(16)) else {
                return Err(self.error_at(
                    start,
                    format!(
                        "invalid escape `{}` in {what}: `\\{letter}` takes {digits} hexadecimal digits",
                        &self.input[start..self.offset]
                    ),
                ));
            };
            self.bump();
            value = value * 16 + digit;
        }
        char::from_u32(value).ok_or_else(|| {
            self.error_at(
                start,
                format!(
                    "escape `{}` in {what} names no Unicode scalar value",
                    &self.input[start..self.offset]
                ),
            )
        })
    }

    fn regex(&mut self) -> Result<String, ParseError> {
        self.skip_trivia()?;
        if !self.consume("r") {
            return Err(self.error("expected regex"));
        }
        self.quoted()
    }

    fn word(&mut self) -> Result<String, ParseError> {
        self.skip_trivia()?;
        if self.at_default_sentence_boundary() {
            return Err(self.error("expected identifier"));
        }
        self.unrestricted_word()
    }

    fn unrestricted_word(&mut self) -> Result<String, ParseError> {
        self.skip_trivia()?;
        let start = self.offset;
        // Invariant: `self.input[start..self.offset]` contains no word boundary; each iteration consumes one character until a word boundary or the end of input.
        while self.peek_char().is_some() {
            if self.at_word_boundary(self.offset) {
                break;
            }
            self.bump();
        }
        if start == self.offset {
            Err(self.error("expected identifier"))
        } else {
            Ok(self.input[start..self.offset].to_owned())
        }
    }

    fn module_name(&mut self) -> Result<String, ParseError> {
        self.skip_trivia()?;
        let start = self.offset;
        let name = self.unrestricted_word()?;
        if is_module_name(&name) {
            Ok(name)
        } else {
            Err(self.error_at(start, "invalid module name"))
        }
    }

    fn expect_word(&mut self, word: &str) -> Result<(), ParseError> {
        self.skip_trivia()?;
        if self.consume_word(word) {
            Ok(())
        } else {
            Err(self.error(format!("expected `{word}`")))
        }
    }

    fn consume_word(&mut self, word: &str) -> bool {
        let saved = self.offset;
        if self.skip_trivia().is_err() {
            return false;
        }
        if self.word_at(self.offset, word) {
            self.last_start = self.offset;
            self.offset += word.len();
            true
        } else {
            self.offset = saved;
            false
        }
    }

    fn peek_word(&mut self, word: &str) -> bool {
        let saved = self.offset;
        let result = self.consume_word(word);
        self.offset = saved;
        result
    }

    fn word_at(&self, offset: usize, word: &str) -> bool {
        self.input[offset..self.end].starts_with(word) && self.at_word_boundary(offset + word.len())
    }

    fn at_word_boundary(&self, offset: usize) -> bool {
        let remaining = &self.input[offset..self.end];
        remaining.is_empty()
            || self.comment_len(offset) > 0
            || remaining
                .chars()
                .next()
                .is_some_and(|ch| is_whitespace(ch) || "{}()[],|>=:\"".contains(ch))
    }

    fn expect_char(&mut self, ch: char) -> Result<(), ParseError> {
        self.skip_trivia()?;
        if self.consume(&ch.to_string()) {
            Ok(())
        } else {
            Err(self.error(format!("expected `{ch}`")))
        }
    }

    fn expect_raw(&mut self, ch: char) -> Result<(), ParseError> {
        if self.peek_char() == Some(ch) {
            self.bump();
            Ok(())
        } else {
            Err(self.error(format!("expected `{ch}`")))
        }
    }

    fn consume(&mut self, text: &str) -> bool {
        if self.starts_with(text) {
            self.last_start = self.offset;
            self.offset += text.len();
            true
        } else {
            false
        }
    }

    fn skip_trivia(&mut self) -> Result<(), ParseError> {
        // Invariant: the text skipped before `self.offset` is whitespace and complete comments; each iteration that continues skips one comment of positive length, so `self.offset` increases toward `self.end`.
        loop {
            while self.peek_char().is_some_and(is_whitespace) {
                self.bump();
            }
            let comment_len = self.comment_len(self.offset);
            if comment_len > 0 {
                self.offset += comment_len;
            } else if self.starts_with("/*") {
                return Err(self.error("unterminated block comment"));
            } else {
                return Ok(());
            }
        }
    }

    fn peek_char_after_trivia(&mut self) -> Result<Option<char>, ParseError> {
        let saved = self.offset;
        self.skip_trivia()?;
        let result = self.peek_char();
        self.offset = saved;
        Ok(result)
    }

    fn peek_regex(&mut self) -> bool {
        let saved = self.offset;
        let _ = self.skip_trivia();
        let result = self.starts_with("r\"");
        self.offset = saved;
        result
    }

    fn peek_user_list(&mut self, name: &str) -> bool {
        let saved = self.offset;
        let result =
            self.consume_word(name) && self.peek_char_after_trivia().ok().flatten() == Some('{');
        self.offset = saved;
        result
    }

    fn starts_with(&self, text: &str) -> bool {
        self.input[self.offset..self.end].starts_with(text)
    }
    fn peek_char(&self) -> Option<char> {
        self.input[self.offset..self.end].chars().next()
    }
    fn bump(&mut self) -> Option<char> {
        let ch = self.peek_char()?;
        self.offset += ch.len_utf8();
        Some(ch)
    }
    fn done(&self) -> bool {
        self.offset >= self.end
    }
    fn position(&self, offset: usize) -> Position {
        let line_index = self.line_starts.partition_point(|start| *start <= offset) - 1;
        let line_start = self.line_starts[line_index];
        Position {
            offset,
            line: line_index as u32 + 1,
            column: self.input[line_start..offset].chars().count() as u32 + 1,
        }
    }
    fn span(&self, start: usize, end: usize) -> Span {
        Span {
            start: self.position(start),
            end: self.position(end),
        }
    }
    fn error(&self, message: impl Into<String>) -> ParseError {
        ParseError {
            message: message.into(),
            position: self.position(self.offset),
            fatal: false,
        }
    }
    fn error_at(&self, offset: usize, message: impl Into<String>) -> ParseError {
        ParseError {
            message: message.into(),
            position: self.position(offset),
            fatal: false,
        }
    }
    fn fatal_error(&self, message: impl Into<String>) -> ParseError {
        ParseError {
            message: message.into(),
            position: self.position(self.offset),
            fatal: true,
        }
    }
}

fn without_optional_hash(identifier: &str) -> &str {
    identifier.strip_prefix('#').unwrap_or(identifier)
}

fn is_outer_identifier(identifier: &str) -> bool {
    let identifier = without_optional_hash(identifier);
    let mut chars = identifier.chars();
    chars.next().is_some_and(|ch| ch.is_ascii_alphabetic())
        && chars.all(|ch| ch.is_ascii_alphanumeric())
}

fn is_upper_identifier(identifier: &str) -> bool {
    let identifier = without_optional_hash(identifier);
    let mut chars = identifier.chars();
    chars.next().is_some_and(|ch| ch.is_ascii_uppercase())
        && chars.all(|ch| ch.is_ascii_alphanumeric())
}

fn is_sort_name(name: &str) -> bool {
    is_numeral_spelling(name) || is_upper_identifier(name)
}

fn is_module_name(name: &str) -> bool {
    if matches!(name, "private" | "public") {
        return false;
    }
    let mut segments = name.split('-');
    let Some(first) = segments.next() else {
        return false;
    };
    let mut first_chars = first.chars();
    first_chars
        .next()
        .is_some_and(|ch| ch.is_ascii_alphabetic())
        && first_chars.all(|ch| ch.is_ascii_alphanumeric() || ch == '_')
        && segments.all(|segment| {
            !segment.is_empty()
                && segment
                    .chars()
                    .all(|ch| ch.is_ascii_alphanumeric() || ch == '_')
        })
}

/// Return `[` offsets which occur in code rather than strings or comments.
///
/// Bubble boundaries are intentionally permissive, so trailing comments remain in `raw`. Looking
/// for attributes with a plain reverse substring search allowed a commented-out `[simplification]`
/// to replace the real attributes of the preceding rule.
fn attribute_starts(raw: &str) -> Vec<usize> {
    #[derive(Clone, Copy)]
    enum State {
        Code,
        String,
        LineComment,
        BlockComment,
    }

    let bytes = raw.as_bytes();
    let mut state = State::Code;
    let mut offsets = Vec::new();
    let mut index = 0;
    // Invariant: `state` is the lexical state of `raw` at `index`, and `offsets` holds, in increasing order, every `[` before `index` that lies in `State::Code`; each iteration advances `index` by at least one byte.
    while index < bytes.len() {
        match state {
            State::Code if bytes[index..].starts_with(b"//") => {
                state = State::LineComment;
                index += 2;
            }
            State::Code if bytes[index..].starts_with(b"/*") => {
                state = State::BlockComment;
                index += 2;
            }
            State::Code if bytes[index] == b'"' => {
                state = State::String;
                index += 1;
            }
            State::Code => {
                if bytes[index] == b'[' {
                    offsets.push(index);
                }
                index += 1;
            }
            State::String if bytes[index] == b'\\' => {
                index += usize::min(2, bytes.len() - index);
            }
            State::String if bytes[index] == b'"' => {
                state = State::Code;
                index += 1;
            }
            State::String => index += 1,
            State::LineComment => {
                if let Some(terminator) = lines::terminator_at(raw, index) {
                    state = State::Code;
                    index += terminator.len();
                } else {
                    index += 1;
                }
            }
            State::BlockComment if bytes[index..].starts_with(b"*/") => {
                state = State::Code;
                index += 2;
            }
            State::BlockComment => index += 1,
        }
    }
    offsets
}

fn is_attribute_key(key: &str) -> bool {
    let base = if let Some((base, parameter)) = key.split_once('<') {
        let Some(parameter) = parameter.strip_suffix('>') else {
            return false;
        };
        if parameter.is_empty()
            || !parameter
                .chars()
                .all(|character| character.is_ascii_alphanumeric() || character == '-')
        {
            return false;
        }
        base
    } else {
        key
    };
    let mut characters = base.chars();
    let Some(first) = characters.next() else {
        return false;
    };
    (first.is_ascii_lowercase() || ('1'..='9').contains(&first))
        && characters
            .all(|character| character.is_ascii_alphanumeric() || matches!(character, '-' | '.'))
}

fn split_label(raw: &str) -> (Option<String>, &str) {
    static LABEL: LazyLock<Regex> = LazyLock::new(|| {
        let space = format!("[{WHITESPACE_CLASS}]*");
        Regex::new(&format!(
            r"(?s)\A{space}\[{space}([^\[\]_{WHITESPACE_CLASS}]+){space}\]{space}:{space}(.*)\z"
        ))
        .expect("the bubble label pattern is valid")
    });
    if let Some(captures) = LABEL.captures(raw) {
        let label = captures.get(1).expect("the label capture exists");
        let content = captures.get(2).expect("the content capture exists");
        return (Some(label.as_str().to_owned()), content.as_str());
    }
    (None, raw)
}

// The default layout is reachable here only in the `cli` build, whose suite runs these tests.
#[cfg(all(test, feature = "cli"))]
mod tests {
    use super::*;

    /// Regex `index` of `crate::inner::DEFAULT_LAYOUT`, anchored to match a whole text.
    fn default_layout_regex(index: usize) -> Regex {
        let regex = k_rust_regex::parse(crate::inner::DEFAULT_LAYOUT[index])
            .expect("the default layout regexes are valid");
        Regex::new(&format!(
            r"\A(?:{})\z",
            regex
                .body
                .to_rust_string()
                .expect("the default layout names no lexical")
        ))
        .expect("the default layout prints as a valid regex")
    }

    /// A character separates outer tokens and bubble words exactly when the default layout, with
    /// which the bubbles are parsed, reads it as whitespace, and the class the label pattern uses
    /// holds the same characters.
    #[test]
    fn outer_whitespace_is_the_default_layouts_whitespace() {
        let layout = default_layout_regex(2);
        let class = Regex::new(&format!(r"\A[{WHITESPACE_CLASS}]\z")).unwrap();
        for character in (0..=0x10FFFF).filter_map(char::from_u32) {
            let text = character.to_string();
            assert_eq!(
                is_whitespace(character),
                layout.is_match(&text),
                "{character:?}"
            );
            assert_eq!(
                is_whitespace(character),
                class.is_match(&text),
                "{character:?}"
            );
        }
    }

    /// An outer `//` comment runs over a character exactly when the default layout's comment
    /// does, and a comment that meets no line end ends with the text.
    #[test]
    fn outer_line_comments_end_where_the_default_layouts_do() {
        let comment = default_layout_regex(1);
        for character in (0..=0x10FFFF).filter_map(char::from_u32) {
            let text = format!("// a{character}b");
            let parser = Parser::new(&text, 0, text.len());
            let runs_over = parser.comment_len(0) == text.len();
            assert_eq!(runs_over, comment.is_match(&text), "{character:?}");
        }
    }
}
