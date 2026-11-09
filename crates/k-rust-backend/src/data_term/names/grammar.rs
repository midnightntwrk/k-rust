//! The text of a finding's name (the parent module's documentation, "The grammar"): how a
//! name is printed from its parts ([`Readable::text`]) and read back from what an author wrote
//! ([`parse`]), so that printing and reading are one grammar.

use super::FindingKind;

/// The precondition rows a name writes by kind, with the symbols they name, because they name
/// no equation (`precondition:KIND:SYMBOL..`).
pub const ROW_KINDS: [&str; 6] = [
    "constructor-headed",
    "injection-headed",
    "indexed-at",
    "overload-shape",
    "no-least-common-overload",
    "pinned-by-injective-total",
];

/// The characters that separate a name's parts, which a word holds only quoted.
const SEPARATORS: &str = ",@#~\"\\";

/// `text` as one word of a name: bare when it is not empty and holds none of `,`, `@`, `#`,
/// `~`, `"`, `\`, whitespace, nor a `:` outside a `::` (a KRS path, `crate::plus_zero`, is
/// bare); otherwise in `"` with `"` and `\` escaped by `\`.
#[must_use]
pub fn word(text: &str) -> String {
    if bare(text) {
        return text.to_owned();
    }
    let mut out = String::from('"');
    for character in text.chars() {
        if character == '"' || character == '\\' {
            out.push('\\');
        }
        out.push(character);
    }
    out.push('"');
    out
}

/// Whether `text` is printed as a bare word ([`word`]).
fn bare(text: &str) -> bool {
    if text.is_empty()
        || text
            .chars()
            .any(|character| SEPARATORS.contains(character) || character.is_whitespace())
    {
        return false;
    }
    // Every run of `:` is exactly `::`.
    let bytes = text.as_bytes();
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] == b':' {
            let start = index;
            while index < bytes.len() && bytes[index] == b':' {
                index += 1;
            }
            if index - start != 2 {
                return false;
            }
        } else {
            index += 1;
        }
    }
    true
}

/// What one sentence of a finding is called, before a front end spells a label.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum SentenceBase {
    /// Its K label, as K stores it.
    Label(String),
    /// An unlabelled sentence's `UNIQUE_ID` (`id:`).
    Id(String),
    /// A compiler-generated overload axiom, by the K labels of its overloaded pair
    /// (`overload:GREATER:LESSER`).
    Overload(String, String),
    /// A witness equation the check adopted, by the text it is identified by (`witness:`).
    Witness(String),
}

/// One sentence of a name: what it is called and, for one of several equations internalized
/// from one axiom, which (`~N`).
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Sentence {
    pub base: SentenceBase,
    pub alternative: Option<usize>,
}

impl Sentence {
    /// The sentence as a name writes it, a label spelled by `spell` where it gives a spelling.
    #[must_use]
    pub fn text(&self, spell: &dyn Fn(&str) -> Option<String>) -> String {
        let base = match &self.base {
            SentenceBase::Label(label) => word(&spell(label).unwrap_or_else(|| label.clone())),
            SentenceBase::Id(id) => format!("id:{}", word(id)),
            SentenceBase::Overload(greater, lesser) => {
                format!("overload:{}:{}", word(greater), word(lesser))
            }
            SentenceBase::Witness(witness) => format!("witness:{}", word(witness)),
        };
        match self.alternative {
            Some(alternative) => format!("{base}~{alternative}"),
            None => base,
        }
    }

    /// Whether the sentence is an unlabelled one named by its `UNIQUE_ID`.
    #[must_use]
    pub const fn is_id(&self) -> bool {
        matches!(self.base, SentenceBase::Id(_))
    }
}

/// The readable part of a name, everything before `#`: its kind, its sentences, an inner
/// pair's position and a precondition row's kind and symbols.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Readable {
    pub kind: FindingKind,
    /// The sentences, in the order the kind reads them (a root pair's in either order: the
    /// text sorts them).
    pub sentences: Vec<Sentence>,
    /// An inner pair's position, the argument indexes in the first sentence's left-hand side.
    pub position: Option<Vec<usize>>,
    /// A precondition row that names no equation: its kind and the K labels it names, each a
    /// word.
    pub row: Option<Vec<String>>,
}

impl Readable {
    /// The readable part as a name writes it, each label spelled by `spell` where it gives a
    /// spelling; a root pair's two sentences sorted by their text.
    #[must_use]
    pub fn text(&self, spell: &dyn Fn(&str) -> Option<String>) -> String {
        let mut sentences = self
            .sentences
            .iter()
            .map(|sentence| sentence.text(spell))
            .collect::<Vec<_>>();
        if self.kind == FindingKind::Root {
            sentences.sort();
        }
        let mut text = format!("{}:", self.kind.keyword());
        match &self.row {
            Some(row) => text.push_str(
                &row.iter()
                    .map(|part| word(part))
                    .collect::<Vec<_>>()
                    .join(":"),
            ),
            None => text.push_str(&sentences.join(",")),
        }
        if let Some(position) = &self.position {
            text.push('@');
            text.push_str(&position_text(position));
        }
        text
    }

    /// Whether a sentence of it is an unlabelled one named by its `UNIQUE_ID`.
    #[must_use]
    pub fn has_id(&self) -> bool {
        self.sentences.iter().any(Sentence::is_id)
    }
}

/// `position` as a name writes it: `root`, or the argument indexes joined by `.`.
#[must_use]
pub fn position_text(position: &[usize]) -> String {
    if position.is_empty() {
        "root".to_owned()
    } else {
        position
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(".")
    }
}

/// What an author wrote, read by [`parse`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Given {
    /// A name of this grammar: its readable part and its digest, when it has one.
    Name {
        readable: Readable,
        digest: Option<String>,
    },
    /// A name of the former grammar, which named a finding by the generated K's positions
    /// (`FIRST,SECOND@POSITION`, `hook:FILE:LINE:COLUMN`, ...): another finding can occupy a
    /// position after an edit, so such a name is refused, with the findings there now.
    Position(PositionName),
}

/// A name of the former grammar ([`Given::Position`]): the kind it wrote (`None` for a pair,
/// which wrote none), its rule parts as written, and a pair's position.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PositionName {
    pub kind: Option<FindingKind>,
    pub parts: Vec<String>,
    pub position: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Token {
    /// A word, unquoted.
    Word(String),
    /// A separator: `,`, `:`, `@`, `#` or `~`.
    Separator(char),
}

/// `given` as words and separators: a word is bare (runs of characters other than the
/// separators, whitespace and quotes, `::` included) or quoted.
fn tokens(given: &str) -> Result<Vec<Token>, String> {
    let mut tokens = Vec::new();
    let mut characters = given.chars().peekable();
    let mut bare = String::new();
    let flush = |bare: &mut String, tokens: &mut Vec<Token>| {
        if !bare.is_empty() {
            tokens.push(Token::Word(std::mem::take(bare)));
        }
    };
    while let Some(character) = characters.next() {
        match character {
            '"' => {
                flush(&mut bare, &mut tokens);
                let mut quoted = String::new();
                let mut closed = false;
                while let Some(character) = characters.next() {
                    match character {
                        '\\' => match characters.next() {
                            Some(escaped) => quoted.push(escaped),
                            None => return Err("a `\\` ends the name".to_owned()),
                        },
                        '"' => {
                            closed = true;
                            break;
                        }
                        other => quoted.push(other),
                    }
                }
                if !closed {
                    return Err("a quote is not closed".to_owned());
                }
                tokens.push(Token::Word(quoted));
            }
            ':' if characters.peek() == Some(&':') => {
                characters.next();
                bare.push_str("::");
            }
            ',' | ':' | '@' | '#' | '~' => {
                flush(&mut bare, &mut tokens);
                tokens.push(Token::Separator(character));
            }
            '\\' => return Err("a `\\` outside quotes".to_owned()),
            other if other.is_whitespace() => {
                return Err("whitespace outside quotes".to_owned());
            }
            other => bare.push(other),
        }
    }
    flush(&mut bare, &mut tokens);
    Ok(tokens)
}

/// Whether `text` is a nonempty run of ASCII digits.
fn digits(text: &str) -> bool {
    !text.is_empty() && text.bytes().all(|byte| byte.is_ascii_digit())
}

/// The keyword's kind.
fn kind_of(keyword: &str) -> Option<FindingKind> {
    FindingKind::ALL
        .into_iter()
        .find(|kind| kind.keyword() == keyword)
}

/// Whether `tokens` hold a written position, `WORD:LINE:COLUMN` with a word that is not a
/// sentence prefix: the former grammar's way of naming an equation.
fn holds_position(tokens: &[Token]) -> bool {
    tokens.windows(5).any(|window| {
        matches!(
            window,
            [
                Token::Word(file),
                Token::Separator(':'),
                Token::Word(line),
                Token::Separator(':'),
                Token::Word(column),
            ] if !matches!(file.as_str(), "id" | "overload" | "witness")
                && digits(line)
                && digits(column)
        )
    })
}

/// One sentence at the start of `tokens`, and the tokens after it.
fn sentence(tokens: &[Token]) -> Result<(Sentence, &[Token]), String> {
    let (base, rest) = match tokens {
        [
            Token::Word(prefix),
            Token::Separator(':'),
            Token::Word(id),
            rest @ ..,
        ] if prefix == "id" => (SentenceBase::Id(id.clone()), rest),
        [
            Token::Word(prefix),
            Token::Separator(':'),
            Token::Word(witness),
            rest @ ..,
        ] if prefix == "witness" => (SentenceBase::Witness(witness.clone()), rest),
        [
            Token::Word(prefix),
            Token::Separator(':'),
            Token::Word(greater),
            Token::Separator(':'),
            Token::Word(lesser),
            rest @ ..,
        ] if prefix == "overload" => (
            SentenceBase::Overload(greater.clone(), lesser.clone()),
            rest,
        ),
        [Token::Word(label), rest @ ..] if !matches!(rest.first(), Some(Token::Separator(':'))) => {
            (SentenceBase::Label(label.clone()), rest)
        }
        _ => {
            return Err(
                "expected a sentence: a label, `id:`, `overload:` or `witness:`".to_owned(),
            );
        }
    };
    match rest {
        [Token::Separator('~'), Token::Word(alternative), rest @ ..] if digits(alternative) => {
            let alternative = alternative
                .parse()
                .map_err(|_| format!("the alternative `~{alternative}` is too large"))?;
            Ok((
                Sentence {
                    base,
                    alternative: Some(alternative),
                },
                rest,
            ))
        }
        [Token::Separator('~'), ..] => Err("`~` must be followed by digits".to_owned()),
        rest => Ok((
            Sentence {
                base,
                alternative: None,
            },
            rest,
        )),
    }
}

/// The readable part `tokens` after the kind keyword and its `:`, for `kind`.
fn readable(kind: FindingKind, tokens: &[Token]) -> Result<Readable, String> {
    let end = |rest: &[Token]| {
        if rest.is_empty() {
            Ok(())
        } else {
            Err(format!(
                "unexpected text after the {} name's sentences",
                kind.keyword()
            ))
        }
    };
    let mut readable = Readable {
        kind,
        sentences: Vec::new(),
        position: None,
        row: None,
    };
    match kind {
        FindingKind::Root | FindingKind::Inner => {
            let (first, rest) = sentence(tokens)?;
            let [Token::Separator(','), rest @ ..] = rest else {
                return Err(format!("a {} name has two sentences", kind.keyword()));
            };
            let (second, rest) = sentence(rest)?;
            readable.sentences = vec![first, second];
            if kind == FindingKind::Inner {
                let [Token::Separator('@'), Token::Word(position), rest @ ..] = rest else {
                    return Err("an inner name ends with `@POSITION`".to_owned());
                };
                let indexes = position
                    .split('.')
                    .map(|index| {
                        if digits(index) {
                            index.parse::<usize>().ok()
                        } else {
                            None
                        }
                    })
                    .collect::<Option<Vec<_>>>()
                    .filter(|indexes| !indexes.is_empty())
                    .ok_or_else(|| {
                        format!("`{position}` is no position: argument indexes joined by `.`")
                    })?;
                readable.position = Some(indexes);
                end(rest)?;
            } else {
                end(rest)?;
            }
        }
        FindingKind::SelfPair | FindingKind::Hook | FindingKind::Equation => {
            let (only, rest) = sentence(tokens)?;
            readable.sentences = vec![only];
            end(rest)?;
        }
        FindingKind::Precondition => match tokens {
            [Token::Word(row), rest @ ..]
                if ROW_KINDS.contains(&row.as_str())
                    && !matches!(rest.first(), Some(Token::Separator('~'))) =>
            {
                let mut parts = vec![row.clone()];
                let mut rest = rest;
                while let [Token::Separator(':'), Token::Word(part), after @ ..] = rest {
                    parts.push(part.clone());
                    rest = after;
                }
                end(rest)?;
                readable.row = Some(parts);
            }
            _ => {
                let (only, rest) = sentence(tokens)?;
                readable.sentences = vec![only];
                end(rest)?;
            }
        },
    }
    Ok(readable)
}

/// Whether `text` is a digest as a name writes it: 32 lowercase hexadecimal digits.
fn is_digest(text: &str) -> bool {
    text.len() == 32
        && text
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

/// What `given` is: a name of this grammar ([`Given::Name`]), or one of the former grammar
/// ([`Given::Position`]); an error saying why it is neither (`malformed`).
///
/// # Errors
///
/// When `given` is no name of either grammar.
pub fn parse(given: &str) -> Result<Given, String> {
    let given = given.trim();
    if given.is_empty() {
        return Err("the name is empty".to_owned());
    }
    let tokens = tokens(given)?;
    let hashes = tokens
        .iter()
        .filter(|token| **token == Token::Separator('#'))
        .count();
    let (readable_tokens, digest) = match tokens
        .iter()
        .position(|token| *token == Token::Separator('#'))
    {
        None => (&tokens[..], None),
        Some(_) if hashes > 1 => {
            return Err("a name has one `#`, before its digest".to_owned());
        }
        Some(at) => match &tokens[at + 1..] {
            [Token::Word(digest)] if is_digest(digest) => (&tokens[..at], Some(digest.clone())),
            _ => {
                return Err(
                    "the digest after `#` must be 32 lowercase hexadecimal digits".to_owned(),
                );
            }
        },
    };
    match readable_tokens {
        [Token::Word(keyword), Token::Separator(':'), rest @ ..] if kind_of(keyword).is_some() => {
            let kind = kind_of(keyword).expect("checked just above");
            match readable(kind, rest) {
                Ok(readable) => Ok(Given::Name { readable, digest }),
                Err(_)
                    if digest.is_none()
                        && matches!(
                            kind,
                            FindingKind::Hook | FindingKind::Equation | FindingKind::Precondition
                        )
                        && holds_position(rest) =>
                {
                    Ok(Given::Position(PositionName {
                        kind: Some(kind),
                        parts: vec![raw(rest)],
                        position: None,
                    }))
                }
                Err(why) => Err(why),
            }
        }
        _ if digest.is_none() => former_pair(readable_tokens)
            .map(Given::Position)
            .ok_or_else(|| {
                format!(
                    "a name starts with its kind ({})",
                    FindingKind::ALL
                        .iter()
                        .map(|kind| format!("`{}:`", kind.keyword()))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }),
        _ => Err(format!(
            "a name starts with its kind ({})",
            FindingKind::ALL
                .iter()
                .map(|kind| format!("`{}:`", kind.keyword()))
                .collect::<Vec<_>>()
                .join(", ")
        )),
    }
}

/// The former grammar's pair name `FIRST,SECOND@POSITION`, split at its one `,` and its last
/// `@`, when `tokens` have that shape.
fn former_pair(tokens: &[Token]) -> Option<PositionName> {
    let comma = tokens
        .iter()
        .position(|token| *token == Token::Separator(','))?;
    let at = tokens
        .iter()
        .rposition(|token| *token == Token::Separator('@'))?;
    if at < comma || tokens[comma + 1..].contains(&Token::Separator(',')) {
        return None;
    }
    let (first, second, position) = (&tokens[..comma], &tokens[comma + 1..at], &tokens[at + 1..]);
    (!first.is_empty() && !second.is_empty() && !position.is_empty()).then(|| PositionName {
        kind: None,
        parts: vec![raw(first), raw(second)],
        position: Some(raw(position)),
    })
}

/// `tokens` written back, words bare.
fn raw(tokens: &[Token]) -> String {
    tokens
        .iter()
        .map(|token| match token {
            Token::Word(word) => word.clone(),
            Token::Separator(separator) => separator.to_string(),
        })
        .collect()
}

/// `given` with every label of its sentences spelled by `spell` where it gives a spelling, the
/// rest as [`Readable::text`] prints it; `None` when `given` is no name of this grammar. A front
/// end that spells labels its own way (KRS spells a sentence by the item that wrote it) maps a
/// name between its spelling and the K labels' with this.
#[must_use]
pub fn respell(given: &str, spell: &dyn Fn(&str) -> Option<String>) -> Option<String> {
    match parse(given).ok()? {
        Given::Name { readable, digest } => Some(match digest {
            Some(digest) => format!("{}#{digest}", readable.text(spell)),
            None => readable.text(spell),
        }),
        Given::Position(_) => None,
    }
}
