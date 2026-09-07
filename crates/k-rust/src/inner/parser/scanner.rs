//! Portable implementation of Scala's global scanner winner rules.

use std::collections::BTreeMap;

use regex::Regex as CompiledRegex;
use regex_automata::{MatchKind, meta::Regex as LongestRegex};

use crate::definition::{ProductionItem, Regex as KRegex, parse_regex};
use crate::kast::Sort;

use super::{ParseError, TokenPrecedenceDeclaration, expand_regex_body};

const DEFAULT_LAYOUT: [&str; 3] = [
    r"(\/\*([^\*]|(\*+([^\*\/])))*\*+\/)",
    r"(\/\/[^\n\r]*)",
    r"([\ \n\r\t])",
];

#[derive(Clone, Debug)]
pub(super) struct Layout {
    patterns: Vec<CompiledKRegex>,
}

impl Default for Layout {
    fn default() -> Self {
        Self::compile(DEFAULT_LAYOUT, &BTreeMap::new())
            .expect("the built-in DEFAULT-LAYOUT regular expressions must be valid")
    }
}

impl Layout {
    pub(super) fn disabled() -> Self {
        Self {
            patterns: Vec::new(),
        }
    }

    pub(super) fn compile(
        sources: impl IntoIterator<Item = impl AsRef<str>>,
        lexical: &BTreeMap<String, KRegex>,
    ) -> Result<Self, ParseError> {
        let patterns = sources
            .into_iter()
            .map(|source| compile_k_regex(source.as_ref(), lexical))
            .collect::<Result<Vec<_>, _>>()?;
        if patterns.is_empty() {
            return Ok(Self::disabled());
        }
        if patterns.iter().any(|regex| {
            regex
                .pattern
                .find("")
                .is_some_and(|matched| matched.is_empty())
        }) {
            return Err(ParseError::EmptyLayout);
        }
        Ok(Self { patterns })
    }

    pub(super) fn compile_with_default(
        sources: impl IntoIterator<Item = impl AsRef<str>>,
        lexical: &BTreeMap<String, KRegex>,
    ) -> Result<Self, ParseError> {
        Self::compile(
            DEFAULT_LAYOUT
                .into_iter()
                .map(str::to_owned)
                .chain(sources.into_iter().map(|source| source.as_ref().to_owned())),
            lexical,
        )
    }

    pub(super) fn skip(&self, input: &str, mut position: usize) -> usize {
        loop {
            let Some(end) = self
                .patterns
                .iter()
                .filter_map(|regex| match_k_regex(regex, input, position))
                .max()
            else {
                return position;
            };
            if end == position {
                return position;
            }
            position = end;
        }
    }
}

#[derive(Clone, Debug)]
pub(super) struct CompiledKRegex {
    canonical: String,
    rust_body: String,
    pattern: LongestRegex,
    start_line: bool,
    end_line: bool,
}

#[derive(Clone, Debug)]
pub(super) struct Restriction {
    canonical: String,
    pattern: CompiledRegex,
}

#[derive(Clone, Debug)]
pub(super) enum Item {
    NonTerminal(Sort),
    Terminal(String),
    Regex {
        source: String,
        regex: CompiledKRegex,
        precede: Option<Restriction>,
        follow: Option<Restriction>,
    },
}

impl Item {
    pub(super) fn description(&self) -> String {
        match self {
            Self::NonTerminal(sort) => sort.to_string(),
            Self::Terminal(terminal) => format!("{terminal:?}"),
            Self::Regex { source, .. } => format!("r{source:?}"),
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum LexemeKey {
    Terminal(String),
    Regex {
        canonical: String,
        precede: Option<String>,
        follow: Option<String>,
    },
}

#[derive(Clone, Debug)]
struct Lexeme {
    key: LexemeKey,
    item: Item,
    precedence: i32,
    declaration: TokenPrecedenceDeclaration,
}

#[derive(Clone, Debug, Default)]
pub(in crate::inner) struct Scanner {
    lexemes: Vec<Lexeme>,
    ids: BTreeMap<LexemeKey, usize>,
}

impl Scanner {
    pub(super) fn register(
        &mut self,
        item: &Item,
        precedence: Option<&str>,
        mut declaration: TokenPrecedenceDeclaration,
    ) -> Result<(), ParseError> {
        let Some(key) = lexeme_key(item) else {
            return Ok(());
        };
        if let Some(existing) = self.ids.get(&key).copied() {
            let candidate = token_precedence(item, precedence, true)?;
            declaration.precedence = candidate;
            if self.lexemes[existing].precedence != candidate {
                let mut declarations =
                    vec![self.lexemes[existing].declaration.clone(), declaration];
                declarations.sort();
                return Err(ParseError::InconsistentTokenPrecedence {
                    token: item.description(),
                    declarations,
                });
            }
            return Ok(());
        }

        let precedence = token_precedence(item, precedence, false)?;
        declaration.precedence = precedence;
        let index = self.lexemes.len();
        self.ids.insert(key.clone(), index);
        self.lexemes.push(Lexeme {
            key,
            item: item.clone(),
            precedence,
            declaration,
        });
        Ok(())
    }

    pub(super) fn matches(
        &self,
        item: &Item,
        input: &str,
        position: usize,
        cached: &mut Option<Option<(usize, usize)>>,
    ) -> Vec<usize> {
        let Some(target) = self.lexeme_id(item) else {
            return Vec::new();
        };
        self.winner(input, position, cached)
            .filter(|(index, _)| *index == target)
            .map(|(_, end)| end)
            .into_iter()
            .collect()
    }

    // IDs belong to this scanner and remain stable across append-only registration and clones.
    pub(super) fn lexeme_id(&self, item: &Item) -> Option<usize> {
        self.ids.get(&lexeme_key(item)?).copied()
    }

    pub(super) fn winner(
        &self,
        input: &str,
        position: usize,
        cached: &mut Option<Option<(usize, usize)>>,
    ) -> Option<(usize, usize)> {
        match cached {
            Some(winner) => *winner,
            None => {
                let winner = self
                    .lexemes
                    .iter()
                    .enumerate()
                    .filter_map(|(index, lexeme)| {
                        match_lexeme(&lexeme.item, input, position).map(|end| (index, lexeme, end))
                    })
                    .max_by(|(_, left, left_end), (_, right, right_end)| {
                        left_end
                            .cmp(right_end)
                            .then_with(|| left.precedence.cmp(&right.precedence))
                            .then_with(|| right.key.cmp(&left.key))
                    })
                    .map(|(index, _, end)| (index, end));
                *cached = Some(winner);
                winner
            }
        }
    }

    #[cfg(test)]
    pub(in crate::inner) fn winner_description(&self, input: &str) -> Option<String> {
        self.lexemes
            .iter()
            .filter_map(|lexeme| {
                match_lexeme(&lexeme.item, input, 0)
                    .and_then(|end| (end == input.len()).then_some((lexeme, end)))
            })
            .max_by(|(left, left_end), (right, right_end)| {
                left_end
                    .cmp(right_end)
                    .then_with(|| left.precedence.cmp(&right.precedence))
                    .then_with(|| right.key.cmp(&left.key))
            })
            .map(|(lexeme, _)| lexeme.item.description())
    }
}

pub(super) fn compile_item(
    item: &ProductionItem,
    lexical: &BTreeMap<String, KRegex>,
) -> Result<Item, ParseError> {
    match item {
        ProductionItem::NonTerminal { sort, .. } => Ok(Item::NonTerminal(sort.clone())),
        ProductionItem::Terminal(terminal) => Ok(Item::Terminal(terminal.clone())),
        ProductionItem::RegexTerminal {
            precede_regex,
            regex,
            follow_regex,
        } => Ok(Item::Regex {
            source: regex.clone(),
            regex: compile_k_regex(regex, lexical)?,
            precede: precede_regex
                .as_deref()
                .map(|regex| compile_restriction(regex, lexical, false))
                .transpose()?,
            follow: follow_regex
                .as_deref()
                .map(|regex| compile_restriction(regex, lexical, true))
                .transpose()?,
        }),
    }
}

fn compile_k_regex(
    source: &str,
    lexical: &BTreeMap<String, KRegex>,
) -> Result<CompiledKRegex, ParseError> {
    let parsed = parse_regex(source).map_err(|error| ParseError::InvalidRegex {
        regex: source.to_owned(),
        message: error.to_string(),
    })?;
    let canonical = parsed.to_java_string();
    let expanded = KRegex {
        start_line: parsed.start_line,
        body: expand_regex_body(&parsed.body, lexical, &mut Vec::new())?,
        end_line: parsed.end_line,
    };
    let flex = expanded
        .to_flex_pattern()
        .map_err(|error| ParseError::InvalidRegex {
            regex: source.to_owned(),
            message: error.to_string(),
        })?;
    let pattern = compile_longest_regex(&flex.body, source)?;
    Ok(CompiledKRegex {
        canonical,
        rust_body: flex.body,
        pattern,
        start_line: flex.start_line,
        end_line: flex.end_line,
    })
}

fn compile_longest_regex(source: &str, reported_source: &str) -> Result<LongestRegex, ParseError> {
    let pattern = format!(r"\A(?:{source})");
    LongestRegex::builder()
        .configure(LongestRegex::config().match_kind(MatchKind::All))
        .build(&pattern)
        .map_err(|error| ParseError::InvalidRegex {
            regex: reported_source.to_owned(),
            message: error.to_string(),
        })
}

fn compile_restriction(
    source: &str,
    lexical: &BTreeMap<String, KRegex>,
    start: bool,
) -> Result<Restriction, ParseError> {
    let compiled = compile_k_regex(source, lexical)?;
    let pattern = if start {
        format!(r"\A(?:{})", compiled.rust_body)
    } else {
        format!(r"(?:{})\z", compiled.rust_body)
    };
    let pattern = CompiledRegex::new(&pattern).map_err(|error| ParseError::InvalidRegex {
        regex: source.to_owned(),
        message: error.to_string(),
    })?;
    Ok(Restriction {
        canonical: compiled.canonical,
        pattern,
    })
}

fn lexeme_key(item: &Item) -> Option<LexemeKey> {
    match item {
        Item::NonTerminal(_) => None,
        Item::Terminal(value) => Some(LexemeKey::Terminal(value.clone())),
        Item::Regex {
            regex,
            precede,
            follow,
            ..
        } => Some(LexemeKey::Regex {
            canonical: regex.canonical.clone(),
            precede: precede
                .as_ref()
                .map(|restriction| restriction.canonical.clone()),
            follow: follow
                .as_ref()
                .map(|restriction| restriction.canonical.clone()),
        }),
    }
}

fn token_precedence(
    item: &Item,
    precedence: Option<&str>,
    repeated: bool,
) -> Result<i32, ParseError> {
    if matches!(item, Item::Terminal(_)) && (!repeated || precedence.is_none()) {
        return Ok(i32::MAX);
    }
    precedence
        .map(|value| {
            value
                .parse()
                .map_err(|_| ParseError::InvalidTokenPrecedence {
                    value: value.to_owned(),
                })
        })
        .unwrap_or(Ok(0))
}

fn match_lexeme(item: &Item, input: &str, position: usize) -> Option<usize> {
    match item {
        Item::Terminal(terminal) => input[position..]
            .starts_with(terminal)
            .then_some(position + terminal.len()),
        Item::Regex {
            regex,
            precede,
            follow,
            ..
        } => {
            if precede
                .as_ref()
                .is_some_and(|restriction| restriction.pattern.is_match(&input[..position]))
            {
                return None;
            }
            let end = match_k_regex(regex, input, position)?;
            if follow
                .as_ref()
                .is_some_and(|restriction| restriction.pattern.is_match(&input[end..]))
            {
                return None;
            }
            Some(end)
        }
        Item::NonTerminal(_) => None,
    }
}

fn match_k_regex(regex: &CompiledKRegex, input: &str, position: usize) -> Option<usize> {
    if regex.start_line && position != 0 && input.as_bytes().get(position - 1) != Some(&b'\n') {
        return None;
    }
    let found = regex.pattern.find(&input[position..])?;
    let end = position + found.end();
    if regex.end_line && input.as_bytes().get(end) != Some(&b'\n') {
        return None;
    }
    Some(end)
}

#[cfg(test)]
mod tests {
    use crate::{definition::Sentence, outer};

    use super::*;

    #[test]
    fn builtin_string_regex_matches_an_empty_quoted_string() {
        let source = r#"module STRING-SYNTAX
  syntax String ::= r"[\\\"](([^\\\"\\n\\r\\\\])|([\\\\][nrtf\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2})|([\\\\][u][0-9a-fA-F]{4})|([\\\\][U][0-9a-fA-F]{8}))*[\\\"]" [token]
endmodule"#;
        let file = outer::parse("string.k", source).unwrap();
        let definition = outer::lower(&file, "STRING-SYNTAX").unwrap();
        let Sentence::Production { items, .. } = &definition.modules[0].local_sentences[0] else {
            panic!("expected production")
        };
        let item = compile_item(&items[0], &BTreeMap::new()).unwrap();

        assert_eq!(match_lexeme(&item, "\"\"", 0), Some(2));
    }
}
