//! Parser for textual KAST.

use std::fmt::{self, Display, Formatter};

use super::ast::{Label, Sort, Term};
use super::string;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseError {
    pub offset: usize,
    pub message: String,
}

impl Display for ParseError {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        write!(formatter, "{} at byte {}", self.message, self.offset)
    }
}

impl std::error::Error for ParseError {}

pub fn parse_term(input: &str) -> Result<Term, ParseError> {
    let mut parser = Parser { input, cursor: 0 };
    let term = parser.term()?;
    parser.whitespace();
    if parser.cursor != input.len() {
        return Err(parser.error("unexpected trailing input"));
    }
    Ok(term)
}

struct Parser<'a> {
    input: &'a str,
    cursor: usize,
}

impl Parser<'_> {
    fn term(&mut self) -> Result<Term, ParseError> {
        let first = self.rewrite_or_as()?;
        let mut items = vec![first];
        while self.consume("~>") {
            items.push(self.rewrite_or_as()?);
        }
        Ok(if items.len() == 1 {
            items.pop().unwrap()
        } else {
            Term::sequence(items)
        })
    }

    fn rewrite_or_as(&mut self) -> Result<Term, ParseError> {
        let left = self.atom()?;
        if self.consume("=>") {
            return Ok(Term::Rewrite {
                left: Box::new(left),
                right: Box::new(self.rewrite_or_as()?),
            });
        }
        if self.consume("#as") {
            return Ok(Term::As {
                pattern: Box::new(left),
                alias: Box::new(self.rewrite_or_as()?),
            });
        }
        Ok(left)
    }

    fn atom(&mut self) -> Result<Term, ParseError> {
        self.whitespace();
        if self.consume_raw("``") {
            let term = self.term()?;
            self.expect("``")?;
            return Ok(term);
        }
        if self.consume(".K") || self.consume(".::K") {
            return Ok(Term::Sequence(Vec::new()));
        }
        if self.consume("#token") {
            return self.token();
        }
        if self.consume("#klabel") {
            self.expect("(")?;
            let label = self.label()?;
            self.expect(")")?;
            return Ok(Term::InjectedLabel(label));
        }
        if self.variable_follows() {
            return Ok(Term::variable(self.variable()?));
        }
        let label = self.label()?;
        self.expect("(")?;
        let arguments = if self.consume(".KList") || self.consume(".::KList") {
            Vec::new()
        } else {
            let mut arguments = vec![self.term()?];
            while self.consume(",") {
                // The historical grammar also accepts a doubled comma.
                self.consume(",");
                arguments.push(self.term()?);
            }
            arguments
        };
        self.expect(")")?;
        Ok(Term::Apply { label, arguments })
    }

    fn token(&mut self) -> Result<Term, ParseError> {
        self.expect("(")?;
        let token = self.quoted_string()?;
        self.expect(",")?;
        let sort =
            parse_sort_text(&self.quoted_string()?).map_err(|message| self.error(message))?;
        self.expect(")")?;
        Ok(Term::Token { token, sort })
    }

    fn label(&mut self) -> Result<Label, ParseError> {
        self.whitespace();
        let name = if self.peek() == Some('`') {
            let quoted = self.quoted('`')?;
            string::unquote_label(quoted).map_err(|message| self.error(message))?
        } else {
            let start = self.cursor;
            let first = self.peek().ok_or_else(|| self.error("expected K label"))?;
            if first != '#' && !first.is_ascii_lowercase() {
                return Err(self.error("expected K label"));
            }
            self.bump();
            while self
                .peek()
                .is_some_and(|character| character.is_ascii_alphanumeric())
            {
                self.bump();
            }
            self.input[start..self.cursor].to_owned()
        };
        let parameters = self.sort_parameters()?;
        Ok(Label { name, parameters })
    }

    fn sort_parameters(&mut self) -> Result<Vec<Sort>, ParseError> {
        if !self.consume("{") {
            return Ok(Vec::new());
        }
        let mut parameters = vec![self.sort()?];
        while self.consume(",") {
            parameters.push(self.sort()?);
        }
        self.expect("}")?;
        Ok(parameters)
    }

    fn sort(&mut self) -> Result<Sort, ParseError> {
        self.whitespace();
        let start = self.cursor;
        while self.peek().is_some_and(|character| {
            !character.is_whitespace() && !matches!(character, '{' | '}' | ',')
        }) {
            self.bump();
        }
        if start == self.cursor {
            return Err(self.error("expected sort"));
        }
        let name = self.input[start..self.cursor].to_owned();
        let parameters = self.sort_parameters()?;
        Ok(Sort { name, parameters })
    }

    fn quoted_string(&mut self) -> Result<String, ParseError> {
        let quoted = self.quoted('"')?;
        string::unquote(quoted).map_err(|message| self.error(message))
    }

    fn quoted(&mut self, delimiter: char) -> Result<&str, ParseError> {
        self.whitespace();
        let start = self.cursor;
        if self.peek() != Some(delimiter) {
            return Err(self.error(format!("expected {delimiter}")));
        }
        self.bump();
        while let Some(character) = self.peek() {
            self.bump();
            if character == '\\' {
                if self.peek().is_none() {
                    return Err(self.error("truncated escape"));
                }
                self.bump();
            } else if character == delimiter {
                return Ok(&self.input[start..self.cursor]);
            }
        }
        Err(self.error("unterminated quoted value"))
    }

    fn variable_follows(&mut self) -> bool {
        self.whitespace();
        self.peek()
            .is_some_and(|character| character == '_' || character.is_ascii_uppercase())
    }

    fn variable(&mut self) -> Result<String, ParseError> {
        self.whitespace();
        let start = self.cursor;
        self.bump();
        while self.peek().is_some_and(|character| {
            character.is_ascii_alphanumeric() || matches!(character, '\'' | '_')
        }) {
            self.bump();
        }
        Ok(self.input[start..self.cursor].to_owned())
    }

    fn whitespace(&mut self) {
        while self.peek().is_some_and(char::is_whitespace) {
            self.bump();
        }
    }

    fn consume(&mut self, expected: &str) -> bool {
        self.whitespace();
        self.consume_raw(expected)
    }

    fn consume_raw(&mut self, expected: &str) -> bool {
        if self.input[self.cursor..].starts_with(expected) {
            self.cursor += expected.len();
            true
        } else {
            false
        }
    }

    fn expect(&mut self, expected: &str) -> Result<(), ParseError> {
        if self.consume(expected) {
            Ok(())
        } else {
            Err(self.error(format!("expected {expected}")))
        }
    }

    fn peek(&self) -> Option<char> {
        self.input[self.cursor..].chars().next()
    }

    fn bump(&mut self) {
        self.cursor += self.peek().unwrap().len_utf8();
    }

    fn error(&self, message: impl Into<String>) -> ParseError {
        ParseError {
            offset: self.cursor,
            message: message.into(),
        }
    }
}

pub(crate) fn parse_sort_text(input: &str) -> Result<Sort, String> {
    let mut parser = Parser { input, cursor: 0 };
    let sort = parser.sort().map_err(|error| error.to_string())?;
    parser.whitespace();
    if parser.cursor != input.len() {
        return Err("trailing input in sort".into());
    }
    Ok(sort)
}

#[cfg(test)]
mod tests {
    use indoc::indoc;

    macro_rules! assert_kast_snapshot {
        ($source:expr) => {{
            let source = indoc!($source);
            let term = crate::kast::parser::parse_term(source).expect("KAST should parse");
            insta::with_settings!({
                description => format!("textual KAST:\n\n{source}"),
                omit_expression => true,
                prepend_module_to_snapshot => true,
            }, {
                insta::assert_debug_snapshot!(term);
            });
        }};
    }

    #[test]
    fn applications_tokens_and_sequences() {
        assert_kast_snapshot!(
            r#"
            `pair,_`{S}(
                #token("hello\\nworld", "String"),,
                X ~> foo(.::KList)
            )
        "#
        );
    }

    #[test]
    fn rewrites_aliases_and_injected_labels() {
        assert_kast_snapshot!(
            r#"
            ``foo(X) #as Y`` ~> #klabel(`_+_`)
        "#
        );
    }
}
