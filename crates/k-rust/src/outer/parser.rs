use std::{error::Error, fmt, rc::Rc};

use crate::kast::Sort;

use super::*;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseError {
    pub message: String,
    pub position: Position,
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
        requires,
        modules,
    })
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
        let line_starts = std::iter::once(0)
            .chain(
                input
                    .match_indices('\n')
                    .map(|(offset, _)| offset + '\n'.len_utf8()),
            )
            .collect();
        Self {
            input,
            line_starts: Rc::new(line_starts),
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
        let name = self.word()?;
        let attributes = if self.peek_char_after_trivia()? == Some('[') {
            self.attributes()?
        } else {
            Vec::new()
        };
        let mut imports = Vec::new();
        let mut sentences = Vec::new();
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
                imports.push(self.import()?);
                continue;
            }
            let sentence_start = self.offset;
            let sentence_end = self.next_sentence_boundary(sentence_start)?;
            let mut sentence_parser = self.subparser(sentence_start, sentence_end);
            let sentence = sentence_parser.sentence()?;
            sentence_parser.skip_trivia()?;
            if !sentence_parser.done() {
                return Err(sentence_parser.error("unexpected input after sentence"));
            }
            sentences.push(sentence);
            self.offset = sentence_end;
        }
    }

    fn import(&mut self) -> Result<Import, ParseError> {
        self.expect_word("imports")?;
        let start = self.last_start;
        self.skip_trivia()?;
        let public = self.consume_word("public") || !self.consume_word("private");
        let module = self.word()?;
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
            let groups = self.raw_groups('>')?;
            return Ok(Sentence::Priority(SyntaxPriority {
                groups,
                span: self.span(start, self.end),
            }));
        }
        if let Some(associativity) = self.consume_associativity() {
            let tags = self.raw_words()?;
            return Ok(Sentence::Associativity(SyntaxAssociativity {
                associativity,
                tags,
                span: self.span(start, self.end),
            }));
        }
        if self.consume_word("lexical") {
            let name = self.word()?;
            self.expect_char('=')?;
            let regex = self.regex()?;
            let attributes = if self.peek_char_after_trivia()? == Some('[') {
                self.attributes()?
            } else {
                Vec::new()
            };
            return Ok(Sentence::Lexical(SyntaxLexical {
                name,
                regex,
                attributes,
                span: self.span(start, self.end),
            }));
        }

        let parameters = if self.peek_char_after_trivia()? == Some('{') {
            self.sort_list('{', '}')?
        } else {
            Vec::new()
        };
        let sort = self.sort()?;
        self.skip_trivia()?;
        let body = if self.consume("::=") {
            SyntaxBody::Productions(self.priority_blocks()?)
        } else if self.consume("=") {
            let old_sort = self.sort()?;
            let attributes = if self.peek_char_after_trivia()? == Some('[') {
                self.attributes()?
            } else {
                Vec::new()
            };
            SyntaxBody::Synonym {
                old_sort,
                attributes,
            }
        } else {
            let attributes = if self.peek_char_after_trivia()? == Some('[') {
                self.attributes()?
            } else {
                Vec::new()
            };
            SyntaxBody::Sort(attributes)
        };
        Ok(Sentence::Syntax(SyntaxDeclaration {
            parameters,
            sort,
            body,
            span: self.span(start, self.end),
        }))
    }

    fn priority_blocks(&mut self) -> Result<Vec<PriorityBlock>, ParseError> {
        let mut blocks = Vec::new();
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
            loop {
                productions.push(self.production()?);
                self.skip_trivia()?;
                if self.consume("|") {
                    continue;
                }
                break;
            }
            blocks.push(PriorityBlock {
                associativity,
                productions,
                span: self.span(start, self.offset),
            });
            self.skip_trivia()?;
            if !self.consume(">") {
                break;
            }
        }
        Ok(blocks)
    }

    fn production(&mut self) -> Result<Production, ParseError> {
        self.skip_trivia()?;
        let start = self.offset;
        let mut items = Vec::new();
        while !self.done() {
            let before_trivia = self.offset;
            self.skip_trivia()?;
            match self.peek_char() {
                Some('|') | Some('>') | Some('[') | None => {
                    self.offset = before_trivia;
                    break;
                }
                Some('"') => items.push(ProductionItem::Terminal(self.quoted()?)),
                Some('(') => {
                    self.expect_char('(')?;
                    items.push(ProductionItem::Terminal("(".into()));
                    for (index, item) in self.nonterminals_until(')')?.into_iter().enumerate() {
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
                    let sort = self.sort()?;
                    self.expect_char(',')?;
                    let separator = self.quoted()?;
                    self.expect_char('}')?;
                    items.push(ProductionItem::UserList {
                        sort,
                        separator,
                        non_empty,
                    });
                }
                _ if self.peek_regex() => items.push(ProductionItem::Regex(self.regex()?)),
                _ => {
                    let first = self.word()?;
                    let after_first = self.offset;
                    self.skip_trivia()?;
                    if self.consume(":") {
                        items.push(ProductionItem::NonTerminal {
                            name: Some(first),
                            sort: self.sort()?,
                        });
                    } else if self.consume("(") {
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
                    } else {
                        self.offset = after_first;
                        let mut sort = Sort::new(first);
                        if self.peek_char_after_trivia()? == Some('{') {
                            sort.parameters = self.sort_list('{', '}')?;
                        }
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
            let kind = if self.consume_word("alias") {
                BubbleKind::ContextAlias
            } else {
                BubbleKind::Context
            };
            (kind, start)
        } else {
            return Err(self.error("expected a K sentence"));
        };
        self.skip_trivia()?;
        let content_start = self.offset;
        let raw = self.input[content_start..self.end].trim_end();
        let trimmed_end = content_start + raw.len();
        let (label, after_label) = split_label(raw);
        let body_start = content_start + (raw.len() - after_label.len());
        let (content, attributes, content_end) =
            self.split_trailing_attributes(after_label, body_start)?;
        self.offset = self.end;
        Ok(Sentence::Bubble(Bubble {
            kind,
            content: content.trim().to_owned(),
            label,
            attributes,
            content_span: self.span(body_start, content_end),
            span: self.span(start, trimmed_end),
        }))
    }

    fn split_trailing_attributes(
        &self,
        raw: &str,
        raw_start: usize,
    ) -> Result<(String, Vec<Attribute>, usize), ParseError> {
        for index in attribute_starts(raw).into_iter().rev() {
            let mut parser = self.subparser(raw_start + index, raw_start + raw.len());
            if let Ok(attributes) = parser.attributes() {
                parser.skip_trivia()?;
                if parser.done() {
                    return Ok((
                        raw[..index].trim_end().to_owned(),
                        attributes,
                        raw_start + index,
                    ));
                }
            }
        }
        Ok((raw.to_owned(), Vec::new(), raw_start + raw.len()))
    }

    fn attributes(&mut self) -> Result<Vec<Attribute>, ParseError> {
        self.expect_char('[')?;
        let mut attributes = Vec::new();
        loop {
            self.skip_trivia()?;
            if self.consume("]") {
                break;
            }
            let key = self.word()?;
            if !is_attribute_key(&key) {
                return Err(self.error("invalid attribute key"));
            }
            self.skip_trivia()?;
            let value = if self.consume("(") {
                let start = self.offset;
                let mut depth = 1usize;
                let mut quoted = false;
                let parsed = 'value: loop {
                    if self.offset >= self.end {
                        break 'value None;
                    }
                    let ch = self
                        .bump()
                        .ok_or_else(|| self.error("unterminated attribute"))?;
                    if ch == '"' && !self.is_escaped(self.offset - 1) {
                        quoted = !quoted;
                    }
                    if !quoted {
                        if ch == '(' {
                            depth += 1;
                        }
                        if ch == ')' {
                            depth -= 1;
                            if depth == 0 {
                                let end = self.offset - 1;
                                break 'value Some(self.input[start..end].to_owned());
                            }
                        }
                    }
                };
                let parsed = parsed.ok_or_else(|| self.error("unterminated attribute value"))?;
                Some(if parsed.starts_with('"') && parsed.ends_with('"') {
                    serde_json::from_str(&parsed).unwrap_or(parsed)
                } else {
                    parsed
                })
            } else {
                None
            };
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

    fn sort(&mut self) -> Result<Sort, ParseError> {
        let name = self.word()?;
        let parameters = if self.peek_char_after_trivia()? == Some('{') {
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
            return Ok(sorts);
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
            let first = self.word()?;
            self.skip_trivia()?;
            let (name, sort) = if self.consume(":") {
                (Some(first), self.sort()?)
            } else {
                let parameters = if self.peek_char_after_trivia()? == Some('{') {
                    self.sort_list('{', '}')?
                } else {
                    Vec::new()
                };
                (None, Sort::with_parameters(first, parameters))
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

    fn raw_groups(&mut self, separator: char) -> Result<Vec<Vec<String>>, ParseError> {
        let raw = self.remaining_without_comments()?;
        Ok(raw
            .split(separator)
            .map(|group| group.split_whitespace().map(str::to_owned).collect())
            .collect())
    }

    fn raw_words(&mut self) -> Result<Vec<String>, ParseError> {
        Ok(self
            .remaining_without_comments()?
            .split_whitespace()
            .map(str::to_owned)
            .collect())
    }

    fn remaining_without_comments(&mut self) -> Result<String, ParseError> {
        let mut result = String::new();
        while !self.done() {
            if self.starts_with("//") {
                while let Some(ch) = self.bump() {
                    if ch == '\n' {
                        result.push(' ');
                        break;
                    }
                }
            } else if self.starts_with("/*") {
                self.offset += 2;
                while !self.done() && !self.starts_with("*/") {
                    self.bump();
                }
                if self.done() {
                    return Err(self.error("unterminated block comment"));
                }
                self.offset += 2;
                result.push(' ');
            } else if let Some(ch) = self.bump() {
                result.push(ch);
            }
        }
        Ok(result.trim().to_owned())
    }

    fn next_sentence_boundary(&self, start: usize) -> Result<usize, ParseError> {
        let mut offset = start;
        let mut quoted = false;
        let mut block_comment = false;
        while offset < self.end {
            if block_comment {
                if self.input[offset..].starts_with("*/") {
                    block_comment = false;
                    offset += 2;
                } else {
                    offset += self.char_len(offset);
                }
                continue;
            }
            if !quoted && self.input[offset..].starts_with("/*") {
                block_comment = true;
                offset += 2;
                continue;
            }
            if !quoted && self.input[offset..].starts_with("//") {
                while offset < self.end && !self.input[offset..].starts_with('\n') {
                    offset += self.char_len(offset);
                }
                continue;
            }
            let ch = self.input[offset..]
                .chars()
                .next()
                .expect("offset is in range");
            if ch == '"' && !self.is_escaped(offset) {
                quoted = !quoted;
            }
            if !quoted && offset > start && self.is_line_prefix(offset) {
                for keyword in [
                    "syntax",
                    "rule",
                    "claim",
                    "context",
                    "configuration",
                    "imports",
                    "endmodule",
                ] {
                    if self.word_at(offset, keyword) {
                        return Ok(offset);
                    }
                }
            }
            offset += ch.len_utf8();
        }
        if block_comment {
            return Err(self.error("unterminated block comment"));
        }
        if quoted {
            return Err(self.error("unterminated string"));
        }
        Ok(self.end)
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
        let mut result = String::new();
        loop {
            let ch = self
                .bump()
                .ok_or_else(|| self.error("unterminated string"))?;
            match ch {
                '"' => return Ok(result),
                '\\' => {
                    let escaped = self
                        .bump()
                        .ok_or_else(|| self.error("unterminated escape"))?;
                    result.push(match escaped {
                        'n' => '\n',
                        'r' => '\r',
                        't' => '\t',
                        '\\' => '\\',
                        '"' => '"',
                        other => other,
                    });
                }
                other => result.push(other),
            }
        }
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
        let start = self.offset;
        while let Some(ch) = self.peek_char() {
            if ch.is_whitespace() || "{}()[],|>=:\"".contains(ch) {
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
        self.input[offset..self.end].starts_with(word)
            && self.input[offset + word.len()..self.end]
                .chars()
                .next()
                .is_none_or(|ch| ch.is_whitespace() || "{}()[],|>=:\"".contains(ch))
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
        loop {
            while self.peek_char().is_some_and(char::is_whitespace) {
                self.bump();
            }
            if self.starts_with("//") {
                while let Some(ch) = self.bump() {
                    if ch == '\n' {
                        break;
                    }
                }
            } else if self.starts_with("/*") {
                self.offset += 2;
                while !self.done() && !self.starts_with("*/") {
                    self.bump();
                }
                if self.done() {
                    return Err(self.error("unterminated block comment"));
                }
                self.offset += 2;
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
    fn char_len(&self, offset: usize) -> usize {
        self.input[offset..]
            .chars()
            .next()
            .map_or(1, char::len_utf8)
    }
    fn is_escaped(&self, offset: usize) -> bool {
        let mut slashes = 0;
        let mut cursor = offset;
        while cursor > 0 && self.input.as_bytes()[cursor - 1] == b'\\' {
            slashes += 1;
            cursor -= 1;
        }
        slashes % 2 == 1
    }
    fn is_line_prefix(&self, offset: usize) -> bool {
        let line_start = self.input[..offset]
            .rfind('\n')
            .map_or(0, |index| index + 1);
        self.input[line_start..offset]
            .chars()
            .all(char::is_whitespace)
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
        }
    }
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
            State::LineComment if bytes[index] == b'\n' => {
                state = State::Code;
                index += 1;
            }
            State::LineComment => index += 1,
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
    let (base, parameter) = match key.split_once('<') {
        Some((base, parameter)) => {
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
            (base, Some(parameter))
        }
        None => (key, None),
    };
    let mut characters = base.chars();
    let Some(first) = characters.next() else {
        return false;
    };
    let valid = (first.is_ascii_lowercase() || ('1'..='9').contains(&first))
        && characters
            .all(|character| character.is_ascii_alphanumeric() || matches!(character, '-' | '.'));
    valid && parameter.is_none_or(|_| !base.contains('>'))
}

fn split_label(raw: &str) -> (Option<String>, &str) {
    let trimmed = raw.trim_start();
    if let Some(rest) = trimmed.strip_prefix('[')
        && let Some(end) = rest.find(']')
        && let Some(after) = rest[end + 1..].trim_start().strip_prefix(':')
    {
        let label = rest[..end].trim();
        if !label.is_empty() && !label.chars().any(char::is_whitespace) {
            return (Some(label.to_owned()), after.trim_start());
        }
    }
    (None, raw)
}
