//! `${name}` placeholders and the integer expressions of `check.expect`.

use std::collections::BTreeMap;

/// Variable bindings for one expansion.
#[derive(Clone, Debug, Default)]
pub struct Vars(BTreeMap<String, String>);

impl Vars {
    pub fn set(&mut self, name: &str, value: impl Into<String>) {
        self.0.insert(name.to_owned(), value.into());
    }

    pub fn get(&self, name: &str) -> Option<&str> {
        self.0.get(name).map(String::as_str)
    }

    /// Replaces every `${name}`; an unbound name is an error.
    pub fn expand(&self, text: &str) -> Result<String, String> {
        let mut out = String::with_capacity(text.len());
        let mut rest = text;
        while let Some(start) = rest.find("${") {
            out.push_str(&rest[..start]);
            let after = &rest[start + 2..];
            let Some(end) = after.find('}') else {
                return Err(format!("unterminated placeholder in {text:?}"));
            };
            let name = &after[..end];
            match self.0.get(name) {
                Some(value) => out.push_str(value),
                None => return Err(format!("unbound placeholder ${{{name}}} in {text:?}")),
            }
            rest = &after[end + 1..];
        }
        out.push_str(rest);
        Ok(out)
    }

    pub fn expand_all(&self, items: &[String]) -> Result<Vec<String>, String> {
        items.iter().map(|item| self.expand(item)).collect()
    }
}

/// Evaluates `+ - * //` over integers, parentheses, and identifiers bound in `params`.
pub fn evaluate(expression: &str, params: &BTreeMap<String, i64>) -> Result<i128, String> {
    let tokens = tokenize(expression)?;
    let mut parser = Parser {
        tokens: &tokens,
        position: 0,
        params,
    };
    let value = parser.sum()?;
    if parser.position != tokens.len() {
        return Err(format!("trailing input in expression {expression:?}"));
    }
    Ok(value)
}

#[derive(Debug, PartialEq)]
enum Token {
    Number(i128),
    Name(String),
    Op(&'static str),
}

fn tokenize(text: &str) -> Result<Vec<Token>, String> {
    let bytes = text.as_bytes();
    let mut tokens = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let c = bytes[i];
        if c.is_ascii_whitespace() {
            i += 1;
        } else if c.is_ascii_digit() {
            let start = i;
            while i < bytes.len() && bytes[i].is_ascii_digit() {
                i += 1;
            }
            let number = text[start..i]
                .parse()
                .map_err(|error| format!("bad number in {text:?}: {error}"))?;
            tokens.push(Token::Number(number));
        } else if c.is_ascii_alphabetic() || c == b'_' {
            let start = i;
            while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
            }
            tokens.push(Token::Name(text[start..i].to_owned()));
        } else if text[i..].starts_with("//") {
            tokens.push(Token::Op("//"));
            i += 2;
        } else {
            let op = match c {
                b'+' => "+",
                b'-' => "-",
                b'*' => "*",
                b'(' => "(",
                b')' => ")",
                _ => return Err(format!("unexpected {:?} in expression {text:?}", c as char)),
            };
            tokens.push(Token::Op(op));
            i += 1;
        }
    }
    Ok(tokens)
}

struct Parser<'a> {
    tokens: &'a [Token],
    position: usize,
    params: &'a BTreeMap<String, i64>,
}

impl Parser<'_> {
    fn peek_op(&self) -> Option<&'static str> {
        match self.tokens.get(self.position) {
            Some(Token::Op(op)) => Some(op),
            _ => None,
        }
    }

    fn sum(&mut self) -> Result<i128, String> {
        let mut value = self.product()?;
        while let Some(op @ ("+" | "-")) = self.peek_op() {
            self.position += 1;
            let right = self.product()?;
            value = if op == "+" {
                value + right
            } else {
                value - right
            };
        }
        Ok(value)
    }

    fn product(&mut self) -> Result<i128, String> {
        let mut value = self.atom()?;
        while let Some(op @ ("*" | "//")) = self.peek_op() {
            self.position += 1;
            let right = self.atom()?;
            value = if op == "*" {
                value * right
            } else if right == 0 {
                return Err("division by zero".to_owned());
            } else {
                value.div_euclid(right)
            };
        }
        Ok(value)
    }

    fn atom(&mut self) -> Result<i128, String> {
        let token = self.tokens.get(self.position);
        self.position += 1;
        match token {
            Some(Token::Number(number)) => Ok(*number),
            Some(Token::Name(name)) => self
                .params
                .get(name)
                .map(|value| i128::from(*value))
                .ok_or_else(|| format!("unbound name {name} in expression")),
            Some(Token::Op("-")) => Ok(-self.atom()?),
            Some(Token::Op("(")) => {
                let value = self.sum()?;
                if self.peek_op() != Some(")") {
                    return Err("missing )".to_owned());
                }
                self.position += 1;
                Ok(value)
            }
            _ => Err("malformed expression".to_owned()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn expands_bound_placeholders_and_rejects_unbound_ones() {
        let mut vars = Vars::default();
        vars.set("n", "10");
        assert_eq!(vars.expand("x=${n};").unwrap(), "x=10;");
        assert!(vars.expand("${m}").is_err());
    }

    #[test]
    fn evaluates_the_sum_formula() {
        let params = BTreeMap::from([("n".to_owned(), 10_000)]);
        assert_eq!(evaluate("n * (n + 1) // 2", &params).unwrap(), 50_005_000);
        assert_eq!(evaluate("-3 + 2*2", &params).unwrap(), 1);
    }
}
