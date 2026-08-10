//! Portable implementation of Scala's global scanner winner rules.

use std::collections::BTreeMap;

use regex::Regex as CompiledRegex;
use regex_automata::{MatchKind, meta::Regex as LongestRegex};

use crate::definition::{ProductionItem, Regex as KRegex};
use crate::kast::Sort;

use super::{ParseError, expand_regex};

#[derive(Clone, Debug)]
pub(super) enum Item {
    NonTerminal(Sort),
    Terminal(String),
    Regex {
        source: String,
        pattern: LongestRegex,
        precede_source: Option<String>,
        precede: Option<CompiledRegex>,
        follow_source: Option<String>,
        follow: Option<CompiledRegex>,
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
        source: String,
        precede: Option<String>,
        follow: Option<String>,
    },
}

#[derive(Clone, Debug)]
struct Lexeme {
    key: LexemeKey,
    item: Item,
    precedence: i32,
}

#[derive(Clone, Debug, Default)]
pub(super) struct Scanner {
    lexemes: Vec<Lexeme>,
    ids: BTreeMap<LexemeKey, usize>,
}

impl Scanner {
    pub(super) fn register(
        &mut self,
        item: &Item,
        precedence: Option<&str>,
    ) -> Result<(), ParseError> {
        let Some(key) = lexeme_key(item) else {
            return Ok(());
        };
        if let Some(existing) = self.ids.get(&key).copied() {
            let candidate = token_precedence(item, precedence, true)?;
            if self.lexemes[existing].precedence != candidate {
                return Err(ParseError::InconsistentTokenPrecedence {
                    token: item.description(),
                });
            }
            return Ok(());
        }

        let precedence = token_precedence(item, precedence, false)?;
        let index = self.lexemes.len();
        self.ids.insert(key.clone(), index);
        self.lexemes.push(Lexeme {
            key,
            item: item.clone(),
            precedence,
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
        let Some(target_key) = lexeme_key(item) else {
            return Vec::new();
        };
        let Some(target) = self.ids.get(&target_key).copied() else {
            return Vec::new();
        };
        let winner = match cached {
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
        };
        matches!(winner, Some((index, _)) if index == target)
            .then(|| winner.expect("winner was matched").1)
            .into_iter()
            .collect()
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
            pattern: compile_longest_regex(&expand_regex(regex, lexical)?)?,
            precede_source: precede_regex.clone(),
            precede: precede_regex
                .as_deref()
                .map(|regex| {
                    expand_regex(regex, lexical)
                        .and_then(|regex| compile_restriction(&regex, false))
                })
                .transpose()?,
            follow_source: follow_regex.clone(),
            follow: follow_regex
                .as_deref()
                .map(|regex| {
                    expand_regex(regex, lexical).and_then(|regex| compile_restriction(&regex, true))
                })
                .transpose()?,
        }),
    }
}

fn compile_longest_regex(source: &str) -> Result<LongestRegex, ParseError> {
    let pattern = format!(r"\A(?:{source})");
    LongestRegex::builder()
        .configure(LongestRegex::config().match_kind(MatchKind::All))
        .build(&pattern)
        .map_err(|error| ParseError::InvalidRegex {
            regex: source.to_owned(),
            message: error.to_string(),
        })
}

fn compile_restriction(source: &str, start: bool) -> Result<CompiledRegex, ParseError> {
    let pattern = if start {
        format!(r"\A(?:{source})")
    } else {
        format!(r"(?:{source})\z")
    };
    CompiledRegex::new(&pattern).map_err(|error| ParseError::InvalidRegex {
        regex: source.to_owned(),
        message: error.to_string(),
    })
}

fn lexeme_key(item: &Item) -> Option<LexemeKey> {
    match item {
        Item::NonTerminal(_) => None,
        Item::Terminal(value) => Some(LexemeKey::Terminal(value.clone())),
        Item::Regex {
            source,
            precede_source,
            follow_source,
            ..
        } => Some(LexemeKey::Regex {
            source: source.clone(),
            precede: precede_source.clone(),
            follow: follow_source.clone(),
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
            pattern,
            precede,
            follow,
            ..
        } => {
            if precede
                .as_ref()
                .is_some_and(|restriction| restriction.is_match(&input[..position]))
            {
                return None;
            }
            let found = pattern.find(&input[position..])?;
            let end = position + found.end();
            if follow
                .as_ref()
                .is_some_and(|restriction| restriction.is_match(&input[end..]))
            {
                return None;
            }
            Some(end)
        }
        Item::NonTerminal(_) => None,
    }
}
