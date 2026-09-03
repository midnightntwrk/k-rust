//! Lexical checks shared by textual and JSON KORE readers.

use std::fmt;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Problem {
    Empty,
    IllegalInitial(char),
    IllegalChars(Vec<char>),
    MissingAt,
    NonLatin1(Vec<char>),
}

impl fmt::Display for Problem {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty => formatter.write_str("Empty"),
            Self::IllegalInitial(character) => {
                write!(formatter, "Illegal initial character {character:?}")
            }
            Self::IllegalChars(characters) => {
                let characters: String = characters.iter().collect();
                write!(formatter, "Contains illegal characters: {characters:?}")
            }
            Self::MissingAt => formatter.write_str("Must start with `@'"),
            Self::NonLatin1(characters) => {
                let characters: String = characters.iter().collect();
                write!(formatter, "Found non-latin1 characters: {characters:?}")
            }
        }
    }
}

pub const fn is_id_start(character: char) -> bool {
    character.is_ascii_alphabetic()
}

pub const fn is_id_char(character: char) -> bool {
    character.is_ascii_alphanumeric() || matches!(character, '\'' | '-')
}

pub fn identifier_problems(name: &str) -> Vec<Problem> {
    let Some(first) = name.chars().next() else {
        return vec![Problem::Empty];
    };
    let mut problems = Vec::new();
    if !is_id_start(first) {
        problems.push(Problem::IllegalInitial(first));
    }
    let illegal = unique_characters(
        name[first.len_utf8()..]
            .chars()
            .filter(|character| !is_id_char(*character)),
    );
    if !illegal.is_empty() {
        problems.push(Problem::IllegalChars(illegal));
    }
    problems
}

pub fn set_variable_problems(name: &str) -> Vec<Problem> {
    let Some(first) = name.chars().next() else {
        return vec![Problem::Empty];
    };
    let mut problems = Vec::new();
    if first != '@' {
        problems.push(Problem::MissingAt);
    }
    problems.extend(identifier_problems(&name[first.len_utf8()..]));
    problems
}

pub fn symbol_problems(name: &str) -> Vec<Problem> {
    name.strip_prefix('\\')
        .map_or_else(|| identifier_problems(name), identifier_problems)
}

pub fn latin1_problems(text: &str) -> Vec<Problem> {
    let illegal: Vec<_> = text
        .chars()
        .filter(|character| *character > '\u{ff}')
        .collect();
    if illegal.is_empty() {
        Vec::new()
    } else {
        vec![Problem::NonLatin1(illegal)]
    }
}

fn unique_characters(characters: impl IntoIterator<Item = char>) -> Vec<char> {
    let mut unique = Vec::new();
    for character in characters {
        if !unique.contains(&character) {
            unique.push(character);
        }
    }
    unique
}
