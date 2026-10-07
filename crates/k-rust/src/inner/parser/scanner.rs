//! ```toml algorithm
//! id = "parser.scanner.winner"
//! name = "global-winner lexical scanning"
//! sites = ["Scanner::winner"]
//! variable = "B = input bytes; L = registered lexemes; Y = layout patterns; m = work of one regex attempt, including a precede-restriction match over the input prefix"
//! counters = ["ParserScannerWinnerComputations"]
//!
//! [[cost]]
//! mode = "one parse attempt"
//! bound = "O(B x (L + Y) x m)"
//! ```
//!
//! K global-winner scanning: longest match, then precedence, then lexeme key.
//!
//! A winner costs O(L) lexeme attempts (terminals only when they start with the input's next
//! byte) plus one attempt per layout pattern, each a regex match
//! whose precede restriction scans the input prefix; it is memoized per position, giving
//! O(input bytes * (L + layout patterns)) attempts per parse attempt.
//! `ParserScannerWinnerComputations` counts cache misses.

use std::collections::BTreeMap;

use regex::Regex as CompiledRegex;
use regex_automata::{MatchKind, meta::Regex as LongestRegex};

use k_rust_kore::measure::{self, Counter};

use crate::definition::{ProductionItem, Regex as KRegex, parse_regex};
use crate::kast::Sort;

use super::grammar::ProductionText;
use super::{ParseError, TokenPrecedenceDeclaration, expand_regex_body};

pub(crate) const DEFAULT_LAYOUT: [&str; 3] = [
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
        // A layout that may be empty somewhere would let the scanner stop without consuming
        // input, so its body may not match the empty string, whatever its anchors.
        if patterns.iter().any(CompiledKRegex::may_match_empty) {
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

    fn longest_match(&self, input: &str, position: usize) -> Option<usize> {
        self.patterns
            .iter()
            .filter_map(|regex| match_k_regex(regex, input, position))
            .max()
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ScanWinner {
    Layout { end: usize },
    Token { lexeme: usize, end: usize },
}

pub(super) type ScanCacheEntry = Option<Option<ScanWinner>>;

/// A token regex compiled for the scanner. Its line anchors are positions in the scanned text
/// (see [`KRegex::start_line`]): `^` is checked before matching, and `$` is compiled into
/// `pattern` as a trailing newline, so the longest match is taken among the body matches a newline
/// follows.
#[derive(Clone, Debug)]
pub(super) struct CompiledKRegex {
    canonical: String,
    rust_body: String,
    pattern: LongestRegex,
    start_line: bool,
    end_line: bool,
}

/// A precede or follow restriction: the token is rejected when the text before it ends (or the
/// text after it starts) with a match of the restriction, that match satisfying the
/// restriction's own line anchors in the whole scanned text.
#[derive(Clone, Debug)]
pub(super) struct Restriction {
    canonical: String,
    pattern: CompiledRegex,
    start_line: bool,
    end_line: bool,
}

#[derive(Clone, Debug)]
pub(super) struct Restrictions {
    precede: Option<Restriction>,
    follow: Option<Restriction>,
}

#[derive(Clone, Debug)]
pub(super) enum Item {
    NonTerminal(Sort),
    Terminal(String),
    Regex {
        source: String,
        regex: CompiledKRegex,
        restrictions: Option<Box<Restrictions>>,
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
struct RestrictionKey {
    precede: Option<String>,
    follow: Option<String>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum LexemeKey {
    Terminal(String),
    Regex {
        canonical: String,
        restrictions: Option<Box<RestrictionKey>>,
    },
}

#[derive(Clone, Debug)]
struct Lexeme {
    key: LexemeKey,
    item: Item,
    precedence: i32,
    declaration: DeclarationSite,
}

/// Where a lexeme was declared, for a token-precedence conflict; the production's text is
/// rendered only when a conflict reports it.
#[derive(Clone, Debug)]
pub(super) struct DeclarationSite {
    pub(super) source: Option<String>,
    pub(super) location: Option<crate::definition::Location>,
    pub(super) production: ProductionText,
}

impl DeclarationSite {
    fn declaration(&self, precedence: i32) -> TokenPrecedenceDeclaration {
        TokenPrecedenceDeclaration {
            source: self.source.clone(),
            location: self.location,
            production: self.production.as_str().to_owned(),
            precedence,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub(in crate::inner) struct Scanner {
    lexemes: Vec<Lexeme>,
    ids: BTreeMap<LexemeKey, usize>,
    // Invariant: every lexeme id is in exactly one of these: a nonempty terminal under its first
    // byte, any other lexeme (a regex, or an empty terminal) in `unindexed`.
    terminals_by_first_byte: BTreeMap<u8, Vec<usize>>,
    unindexed: Vec<usize>,
}

impl Scanner {
    /// Register the lexeme of a terminal or regex item and return its id; a nonterminal has none.
    pub(super) fn register(
        &mut self,
        item: &Item,
        precedence: Option<&str>,
        declaration: &DeclarationSite,
    ) -> Result<Option<usize>, ParseError> {
        let Some(key) = lexeme_key(item) else {
            return Ok(None);
        };
        if let Some(existing) = self.ids.get(&key).copied() {
            let candidate = token_precedence(item, precedence, true)?;
            let lexeme = &self.lexemes[existing];
            if lexeme.precedence != candidate {
                let mut declarations = vec![
                    lexeme.declaration.declaration(lexeme.precedence),
                    declaration.declaration(candidate),
                ];
                declarations.sort();
                return Err(ParseError::InconsistentTokenPrecedence {
                    token: item.description(),
                    declarations,
                });
            }
            return Ok(Some(existing));
        }

        let precedence = token_precedence(item, precedence, false)?;
        let index = self.lexemes.len();
        self.ids.insert(key.clone(), index);
        match item {
            Item::Terminal(terminal) if !terminal.is_empty() => self
                .terminals_by_first_byte
                .entry(terminal.as_bytes()[0])
                .or_default()
                .push(index),
            _ => self.unindexed.push(index),
        }
        self.lexemes.push(Lexeme {
            key,
            item: item.clone(),
            precedence,
            declaration: declaration.clone(),
        });
        Ok(Some(index))
    }

    /// The end of the scanner's winning token at `position` when that token is lexeme `target`.
    pub(super) fn matches(
        &self,
        layout: &Layout,
        target: usize,
        input: &str,
        position: usize,
        cached: &mut ScanCacheEntry,
    ) -> Option<usize> {
        self.winner(layout, input, position, cached)
            .and_then(|winner| match winner {
                ScanWinner::Token { lexeme, end } if lexeme == target => Some(end),
                _ => None,
            })
    }

    // IDs belong to this scanner and remain stable across append-only registration and clones.
    pub(super) fn lexeme_id(&self, item: &Item) -> Option<usize> {
        self.ids.get(&lexeme_key(item)?).copied()
    }

    pub(super) fn winner(
        &self,
        layout: &Layout,
        input: &str,
        position: usize,
        cached: &mut ScanCacheEntry,
    ) -> Option<ScanWinner> {
        match cached {
            Some(winner) => *winner,
            None => {
                measure::bump(Counter::ParserScannerWinnerComputations);
                // A terminal matches only where the input continues with its first byte, so only
                // that byte's terminals are attempted. The comparison below orders distinct
                // lexemes strictly (their keys differ), so the maximum does not depend on the
                // order in which candidates are attempted.
                let terminals = input
                    .as_bytes()
                    .get(position)
                    .and_then(|byte| self.terminals_by_first_byte.get(byte))
                    .map_or(&[][..], Vec::as_slice);
                let token = terminals
                    .iter()
                    .chain(&self.unindexed)
                    .map(|index| (*index, &self.lexemes[*index]))
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
                let winner = match (layout.longest_match(input, position), token) {
                    (Some(layout_end), Some((lexeme, token_end))) if token_end > layout_end => {
                        Some(ScanWinner::Token {
                            lexeme,
                            end: token_end,
                        })
                    }
                    (Some(end), _) => Some(ScanWinner::Layout { end }),
                    (None, Some((lexeme, end))) => Some(ScanWinner::Token { lexeme, end }),
                    (None, None) => None,
                };
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
        } => {
            let compiled_regex = compile_k_regex(regex, lexical)?;
            let precede = precede_regex
                .as_deref()
                .map(|regex| compile_restriction(regex, lexical, false))
                .transpose()?;
            let follow = follow_regex
                .as_deref()
                .map(|regex| compile_restriction(regex, lexical, true))
                .transpose()?;
            let restrictions = (precede.is_some() || follow.is_some())
                .then(|| Box::new(Restrictions { precede, follow }));
            Ok(Item::Regex {
                source: regex.clone(),
                regex: compiled_regex,
                restrictions,
            })
        }
    }
}

impl CompiledKRegex {
    /// The Rust regex syntax this regex compiles to, after named references are expanded.
    pub(super) fn rust_body(&self) -> &str {
        &self.rust_body
    }

    /// Whether the regex may match the empty string somewhere: its shortest match has length
    /// zero, whatever its line anchors and restrictions require of the surroundings.
    pub(super) fn may_match_empty(&self) -> bool {
        regex_automata::util::syntax::parse(&self.rust_body)
            .map_or(true, |hir| hir.properties().minimum_len() == Some(0))
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
    let canonical = parsed.to_canonical_string();
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
    let pattern = compile_longest_regex(&flex.body, flex.end_line, source)?;
    Ok(CompiledKRegex {
        canonical,
        rust_body: flex.body,
        pattern,
        start_line: flex.start_line,
        end_line: flex.end_line,
    })
}

fn compile_longest_regex(
    source: &str,
    end_line: bool,
    reported_source: &str,
) -> Result<LongestRegex, ParseError> {
    let pattern = if end_line {
        format!(r"\A(?:{source})\n")
    } else {
        format!(r"\A(?:{source})")
    };
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
    // A follow restriction is matched at the start of the text after the token, so its `$` is a
    // newline after the match; a precede restriction is matched against the text before the
    // token, a prefix of the scanned text, where multi-line `^` holds exactly at line starts.
    let pattern = match (start, compiled.start_line, compiled.end_line) {
        (true, _, false) => format!(r"\A(?:{})", compiled.rust_body),
        (true, _, true) => format!(r"\A(?:{})\n", compiled.rust_body),
        (false, false, _) => format!(r"(?:{})\z", compiled.rust_body),
        (false, true, _) => format!(r"(?m:^)(?:{})\z", compiled.rust_body),
    };
    let pattern = CompiledRegex::new(&pattern).map_err(|error| ParseError::InvalidRegex {
        regex: source.to_owned(),
        message: error.to_string(),
    })?;
    Ok(Restriction {
        canonical: compiled.canonical,
        pattern,
        // The anchors the pattern does not express are positions at the token's boundary.
        start_line: start && compiled.start_line,
        end_line: !start && compiled.end_line,
    })
}

/// Whether `position` starts a line of `input`: it is the start, or a newline precedes it.
fn at_line_start(input: &str, position: usize) -> bool {
    position == 0 || input.as_bytes()[position - 1] == b'\n'
}

/// Whether `position` ends a line of `input`: a newline follows it.
fn at_line_end(input: &str, position: usize) -> bool {
    input.as_bytes().get(position) == Some(&b'\n')
}

fn lexeme_key(item: &Item) -> Option<LexemeKey> {
    match item {
        Item::NonTerminal(_) => None,
        Item::Terminal(value) => Some(LexemeKey::Terminal(value.clone())),
        Item::Regex {
            regex,
            restrictions,
            ..
        } => Some(LexemeKey::Regex {
            canonical: regex.canonical.clone(),
            restrictions: restrictions.as_ref().map(|restrictions| {
                Box::new(RestrictionKey {
                    precede: restrictions
                        .precede
                        .as_ref()
                        .map(|restriction| restriction.canonical.clone()),
                    follow: restrictions
                        .follow
                        .as_ref()
                        .map(|restriction| restriction.canonical.clone()),
                })
            }),
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
            restrictions,
            ..
        } => {
            if restrictions
                .as_deref()
                .and_then(|restrictions| restrictions.precede.as_ref())
                .is_some_and(|restriction| {
                    (!restriction.end_line || at_line_end(input, position))
                        && restriction.pattern.is_match(&input[..position])
                })
            {
                return None;
            }
            let end = match_k_regex(regex, input, position)?;
            if restrictions
                .as_deref()
                .and_then(|restrictions| restrictions.follow.as_ref())
                .is_some_and(|restriction| {
                    (!restriction.start_line || at_line_start(input, end))
                        && restriction.pattern.is_match(&input[end..])
                })
            {
                return None;
            }
            Some(end)
        }
        Item::NonTerminal(_) => None,
    }
}

fn match_k_regex(regex: &CompiledKRegex, input: &str, position: usize) -> Option<usize> {
    if regex.start_line && !at_line_start(input, position) {
        return None;
    }
    let found = regex.pattern.find(&input[position..])?;
    // An end-anchored pattern's match ends with the newline after the token.
    Some(position + found.end() - usize::from(regex.end_line))
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    use crate::{definition::Sentence, outer};

    use super::*;

    fn declaration(terminal: &str) -> DeclarationSite {
        DeclarationSite {
            source: None,
            location: None,
            production: ProductionText::rendered(format!("syntax S ::= {terminal:?}")),
        }
    }

    fn semantic_winner(
        scanner: &Scanner,
        input: &str,
        position: usize,
    ) -> Option<(Option<LexemeKey>, usize)> {
        match scanner.winner(&Layout::disabled(), input, position, &mut None) {
            Some(ScanWinner::Layout { end }) => Some((None, end)),
            Some(ScanWinner::Token { lexeme, end }) => {
                Some((Some(scanner.lexemes[lexeme].key.clone()), end))
            }
            None => None,
        }
    }

    proptest! {
        #[test]
        fn scanner_winners_do_not_depend_on_registration_order(
            lexemes in prop::collection::btree_set("[abc]{1,3}", 1..8),
            order_keys in prop::collection::vec(any::<u8>(), 1..8),
            input in "[abc]{0,16}",
        ) {
            let canonical = lexemes.into_iter().collect::<Vec<_>>();
            let mut reordered = canonical.clone();
            reordered.sort_by_key(|terminal| {
                let index = canonical.binary_search(terminal).unwrap();
                (order_keys[index % order_keys.len()], index)
            });

            let scanner = |terminals: &[String]| {
                let mut scanner = Scanner::default();
                for terminal in terminals {
                    let item = Item::Terminal(terminal.clone());
                    scanner.register(&item, None, &declaration(terminal)).unwrap();
                }
                scanner
            };
            let canonical = scanner(&canonical);
            let reordered = scanner(&reordered);
            for position in 0..=input.len() {
                prop_assert_eq!(
                    semantic_winner(&canonical, &input, position),
                    semantic_winner(&reordered, &input, position),
                    "position {}",
                    position,
                );
            }
        }
    }

    fn restricted_regex(precede: Option<&str>, follow: Option<&str>) -> Item {
        compile_item(
            &ProductionItem::RegexTerminal {
                precede_regex: precede.map(str::to_owned),
                regex: "b".into(),
                follow_regex: follow.map(str::to_owned),
            },
            &BTreeMap::new(),
        )
        .unwrap()
    }

    #[test]
    fn regex_restrictions_reject_matching_prefixes_and_suffixes() {
        let precede = restricted_regex(Some("a"), None);
        assert_eq!(match_lexeme(&precede, "b", 0), Some(1));
        assert_eq!(match_lexeme(&precede, "ab", 1), None);

        let follow = restricted_regex(None, Some("c"));
        assert_eq!(match_lexeme(&follow, "b", 0), Some(1));
        assert_eq!(match_lexeme(&follow, "bc", 0), None);

        let both = restricted_regex(Some("a"), Some("c"));
        assert_eq!(match_lexeme(&both, "b", 0), Some(1));
        assert_eq!(match_lexeme(&both, "ab", 1), None);
        assert_eq!(match_lexeme(&both, "bc", 0), None);
    }

    #[test]
    fn regex_restriction_anchors_constrain_where_the_restriction_matches() {
        // `^a` before the token: only an `a` that starts a line rejects the `b`.
        let precede = restricted_regex(Some("^a"), None);
        assert_eq!(match_lexeme(&precede, "ab", 1), None);
        assert_eq!(match_lexeme(&precede, "x\nab", 3), None);
        assert_eq!(match_lexeme(&precede, "xab", 2), Some(3));

        // `c$` after the token: only a `c` that a newline follows rejects the `b`.
        let follow = restricted_regex(None, Some("c$"));
        assert_eq!(match_lexeme(&follow, "bc\n", 0), None);
        assert_eq!(match_lexeme(&follow, "bcd", 0), Some(1));
        assert_eq!(match_lexeme(&follow, "bc", 0), Some(1));

        // `a$` before the token ends at the token's start, so the token must start with a
        // newline, which `b` never does; likewise `^c` after it.
        let precede_end = restricted_regex(Some("a$"), None);
        assert_eq!(match_lexeme(&precede_end, "ab", 1), Some(2));
        let follow_start = restricted_regex(None, Some("^c"));
        assert_eq!(match_lexeme(&follow_start, "bc", 0), Some(1));
    }

    #[test]
    fn regex_line_anchors_are_part_of_the_lexeme_identity() {
        let key = |regex: &str| {
            lexeme_key(&compile_item(&ProductionItem::regex(regex), &BTreeMap::new()).unwrap())
                .unwrap()
        };
        let keys = ["a", "^a", "a$", "^a$"].map(key);
        for (index, left) in keys.iter().enumerate() {
            for right in &keys[index + 1..] {
                assert_ne!(left, right);
            }
        }
        assert_eq!(key("^(a)$"), key("^a$"));
    }

    #[test]
    fn regex_restrictions_preserve_scanner_identity_order() {
        let unrestricted = lexeme_key(&restricted_regex(None, None)).unwrap();
        let follow = lexeme_key(&restricted_regex(None, Some("c"))).unwrap();
        let precede = lexeme_key(&restricted_regex(Some("a"), None)).unwrap();

        assert_ne!(unrestricted, follow);
        assert_ne!(unrestricted, precede);
        assert_ne!(follow, precede);
        assert!(unrestricted < follow);
        assert!(follow < precede);
    }

    #[test]
    fn invalid_body_and_restriction_regexes_retain_their_source() {
        for item in [
            ProductionItem::RegexTerminal {
                precede_regex: None,
                regex: "(".into(),
                follow_regex: None,
            },
            ProductionItem::RegexTerminal {
                precede_regex: Some("(".into()),
                regex: "b".into(),
                follow_regex: None,
            },
            ProductionItem::RegexTerminal {
                precede_regex: None,
                regex: "b".into(),
                follow_regex: Some("(".into()),
            },
        ] {
            assert!(
                matches!(
                    compile_item(&item, &BTreeMap::new()),
                    Err(ParseError::InvalidRegex { regex, .. }) if regex == "("
                ),
                "{item:?}"
            );
        }

        let all_invalid = ProductionItem::RegexTerminal {
            precede_regex: Some("[".into()),
            regex: "(".into(),
            follow_regex: Some("{".into()),
        };
        assert!(matches!(
            compile_item(&all_invalid, &BTreeMap::new()),
            Err(ParseError::InvalidRegex { regex, .. }) if regex == "("
        ));
    }

    #[test]
    fn builtin_string_regex_matches_an_empty_quoted_string() {
        let source = r#"module STRING-SYNTAX
  syntax String ::= r"[\\\"](([^\\\"\\n\\r\\\\])|([\\\\][nrtf\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2})|([\\\\][u][0-9a-fA-F]{4})|([\\\\][U][0-9a-fA-F]{8}))*[\\\"]" [token]
endmodule"#;
        let file = outer::parse("string.k", source).unwrap();
        let definition = outer::lower(&file, "STRING-SYNTAX").unwrap();
        let Sentence::Production { items, .. } = &*definition.modules[0].local_sentences[0] else {
            panic!("expected production")
        };
        let item = compile_item(&items[0], &BTreeMap::new()).unwrap();

        assert_eq!(match_lexeme(&item, "\"\"", 0), Some(2));
    }
}
