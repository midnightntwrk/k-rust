//! Token spelling for emitted K.
//!
//! Emitted `.k` is a serialization that K's rule parser must read back into exactly the IR term.
//! A token is printed in bare concrete syntax only when that spelling is guaranteed to lex back to
//! the same token of the same sort in the emitted definition; every other token is printed as
//! `#token("<value>","<Sort>")`.
//!
//! The lexical classes below are the rule-grammar token productions of the pinned K 7.1.337
//! builtin modules (`domains.md`) that the printer imports for each sort.
//! K's scanner takes the longest match and breaks ties by lexical precedence; a terminal outranks
//! every regex token.
//! A bare spelling is therefore refused when it equals a terminal of the definition, or when the
//! definition declares a regex token production whose precedence is at least that of the builtin
//! token, since such a production may claim the same lexeme.

use std::collections::BTreeSet;

use krs_ir::{BuiltinSort, GrammarProductionItemKind, ProductionAttribute};
use krs_ir_levels::{
    DefinitionIr, DefinitionModule, DefinitionSentence, k_surface::definition_terminals,
};

/// Lexical facts of one definition that decide whether a builtin token may be printed bare.
#[derive(Default)]
pub(super) struct TokenLexicon {
    terminals: BTreeSet<String>,
    /// Highest `prec` among the definition's regex token productions, if it declares any.
    regex_precedence: Option<u32>,
}

impl TokenLexicon {
    pub(super) fn new(definition: &DefinitionIr) -> Self {
        let regex_precedence = definition
            .modules()
            .iter()
            .flat_map(DefinitionModule::sentences)
            .filter_map(|sentence| match sentence {
                // A terminal token production (`syntax Name ::= "main" [token]`)
                // is counted among the terminals, not the regex tokens.
                DefinitionSentence::Production(production)
                    if production.items().iter().any(|item| {
                        matches!(item.kind(), GrammarProductionItemKind::RegexTerminal { .. })
                    }) =>
                {
                    Some(production.attributes())
                }
                _ => None,
            })
            .flatten()
            .filter_map(|attribute| match attribute {
                ProductionAttribute::Token {
                    lexical_precedence, ..
                } => Some(lexical_precedence.unwrap_or(0)),
                _ => None,
            })
            .max();
        Self {
            terminals: definition_terminals(definition)
                .into_iter()
                .map(str::to_owned)
                .collect(),
            regex_precedence,
        }
    }

    /// Returns whether `value` may be printed bare as a token of the builtin `sort`.
    pub(super) fn is_bare(&self, sort: BuiltinSort, value: &str) -> bool {
        let Some(precedence) = builtin_token_precedence(sort, value) else {
            return false;
        };
        !self.terminals.contains(value)
            && self.regex_precedence.is_none_or(|regex| {
                precedence == Precedence::Terminal || regex < precedence.value()
            })
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Precedence {
    /// A builtin terminal, which outranks every regex token.
    Terminal,
    /// A builtin regex token with this K `prec`.
    Regex(u32),
}

impl Precedence {
    const fn value(self) -> u32 {
        match self {
            Self::Terminal => u32::MAX,
            Self::Regex(value) => value,
        }
    }
}

/// Returns the precedence of the builtin token production that lexes exactly `value` as `sort`.
///
/// `Id` has no rule-grammar lexical syntax: `ID-SYNTAX` declares `syntax Id [token]`, and its
/// identifier regex lives in `ID-SYNTAX-PROGRAM-PARSING`, which K adds only for program parsing.
fn builtin_token_precedence(sort: BuiltinSort, value: &str) -> Option<Precedence> {
    match sort {
        // INT-SYNTAX: r"[\\+\\-]?[0-9]+" [prefer, token, prec(2)]
        BuiltinSort::Int => is_int(value).then_some(Precedence::Regex(2)),
        // BOOL-SYNTAX: "true" [token] | "false" [token]
        BuiltinSort::Bool => matches!(value, "true" | "false").then_some(Precedence::Terminal),
        // STRING-SYNTAX: the string-literal regex [token]
        BuiltinSort::String => is_string(value).then_some(Precedence::Regex(0)),
        // BYTES-SYNTAX: the bytes-literal regex [token]
        BuiltinSort::Bytes => is_bytes(value).then_some(Precedence::Regex(0)),
        // FLOAT-SYNTAX: the numeric regex [token, prec(1)]; the `Infinity` and `NaN`
        // regexes [token, prec(3)]
        BuiltinSort::Float => float_precedence(value),
        BuiltinSort::Id
        | BuiltinSort::KSequence
        | BuiltinSort::Map
        | BuiltinSort::List
        | BuiltinSort::Set
        | BuiltinSort::Endianness
        | BuiltinSort::Signedness => None,
    }
}

/// The precedence of the `FLOAT-SYNTAX` token production that lexes exactly `value`.
///
/// Only canonical KRS Float tokens (`krs_ir::float_token`) are printed bare; each is matched in
/// full by exactly one of K's three Float regexes, and is longer than any `Int` prefix of it.
fn float_precedence(value: &str) -> Option<Precedence> {
    krs_ir::float_token::validate(value).ok()?;
    let unsigned = value.strip_prefix('-').unwrap_or(value);
    if unsigned.starts_with("Infinity") || unsigned.starts_with("NaN") {
        Some(Precedence::Regex(3))
    } else {
        Some(Precedence::Regex(1))
    }
}

fn is_int(value: &str) -> bool {
    let digits = value.strip_prefix(['+', '-']).unwrap_or(value);
    !digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_digit())
}

/// `[\"](([^\"\n\r\\])|([\\][nrtf\"\\])|([\\][x][0-9a-fA-F]{2})|([\\][u][0-9a-fA-F]{4})|([\\][U][0-9a-fA-F]{8}))*[\"]`
fn is_string(value: &str) -> bool {
    let Some(body) = value
        .strip_prefix('"')
        .and_then(|body| body.strip_suffix('"'))
    else {
        return false;
    };
    escaped_body(
        body,
        |character| !matches!(character, '"' | '\n' | '\r' | '\\'),
        |escape| match escape {
            'n' | 'r' | 't' | 'f' | '"' | '\\' => Some(0),
            'x' => Some(2),
            'u' => Some(4),
            'U' => Some(8),
            _ => None,
        },
    )
}

/// `b[\"](([ !#-\[\]-~])|([\\][tnfr\"\\])|([\\][x][0-9a-fA-F]{2}))*[\"]`
fn is_bytes(value: &str) -> bool {
    let Some(body) = value
        .strip_prefix("b\"")
        .and_then(|body| body.strip_suffix('"'))
    else {
        return false;
    };
    escaped_body(
        body,
        |character| matches!(character, ' '..='~') && !matches!(character, '"' | '\\'),
        |escape| match escape {
            't' | 'n' | 'f' | 'r' | '"' | '\\' => Some(0),
            'x' => Some(2),
            _ => None,
        },
    )
}

/// Matches a literal body of plain characters and `\` escapes; `escape` returns how many hex
/// digits follow an accepted escape letter.
fn escaped_body(
    body: &str,
    plain: impl Fn(char) -> bool,
    escape: impl Fn(char) -> Option<usize>,
) -> bool {
    let mut characters = body.chars();
    while let Some(character) = characters.next() {
        if character == '\\' {
            let Some(digits) = characters.next().and_then(&escape) else {
                return false;
            };
            for _ in 0..digits {
                if !characters
                    .next()
                    .is_some_and(|digit| digit.is_ascii_hexdigit())
                {
                    return false;
                }
            }
        } else if !plain(character) {
            return false;
        }
    }
    true
}

/// Spells `value` as the string argument of `#token(...)`, or returns `None` when no spelling
/// reads back as exactly `value`.
///
/// The argument must lex as K's `KString`, and K then keeps its text verbatim except that it
/// drops the enclosing quotes and replaces each `\"` with `"` (`TreeNodesToKORE`, pinned K
/// 7.1.337).
/// A quote is therefore escaped, a backslash must already begin a `KString` escape other than
/// `\"`, and a line break has no spelling.
pub(super) fn token_literal(value: &str) -> Option<String> {
    let mut output = String::with_capacity(value.len() + 2);
    output.push('"');
    let mut characters = value.chars();
    while let Some(character) = characters.next() {
        match character {
            '"' => output.push_str("\\\""),
            '\n' | '\r' => return None,
            '\\' => {
                let escape = characters.next()?;
                let digits = match escape {
                    '\\' | 'n' | 'r' | 't' | 'f' => 0,
                    'x' => 2,
                    'u' => 4,
                    'U' => 8,
                    _ => return None,
                };
                output.push('\\');
                output.push(escape);
                for _ in 0..digits {
                    let digit = characters.next().filter(char::is_ascii_hexdigit)?;
                    output.push(digit);
                }
            }
            character => output.push(character),
        }
    }
    output.push('"');
    Some(output)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn builtin_lexical_classes_match_the_pinned_productions() {
        for (sort, value, expected) in [
            (BuiltinSort::Int, "0", true),
            (BuiltinSort::Int, "-12", true),
            (BuiltinSort::Int, "+7", true),
            (BuiltinSort::Int, "-", false),
            (BuiltinSort::Int, "1_000", false),
            (BuiltinSort::Int, "0x10", false),
            (BuiltinSort::Bool, "true", true),
            (BuiltinSort::Bool, "false", true),
            (BuiltinSort::Bool, "True", false),
            (BuiltinSort::String, r#""""#, true),
            (
                BuiltinSort::String,
                r#""a\"b\\c\n\x41\u00e9\U0001F600é""#,
                true,
            ),
            (BuiltinSort::String, "\"line\nbreak\"", false),
            (BuiltinSort::String, r#""\q""#, false),
            (BuiltinSort::String, r#""\x4""#, false),
            (BuiltinSort::String, r#""unterminated"#, false),
            (BuiltinSort::Bytes, r#"b"""#, true),
            (BuiltinSort::Bytes, r#"b"\x00\xffAz \t\"""#, true),
            (BuiltinSort::Bytes, "b\"é\"", false),
            (BuiltinSort::Bytes, r#"b"\u0041""#, false),
            (BuiltinSort::Bytes, r#""\x00""#, false),
            (BuiltinSort::Id, "x", false),
            (BuiltinSort::Id, "$x", false),
            (BuiltinSort::KSequence, "x", false),
            (BuiltinSort::Float, "1.5", true),
            (BuiltinSort::Float, "-0.0", true),
            (BuiltinSort::Float, "0.1f", true),
            (BuiltinSort::Float, "1.5d", true),
            (BuiltinSort::Float, "1.0p113x15", true),
            (BuiltinSort::Float, "1e10", true),
            (BuiltinSort::Float, "NaN", true),
            (BuiltinSort::Float, "-Infinityf", true),
            (BuiltinSort::Float, "1", false),
            (BuiltinSort::Float, "1.5F", false),
            (BuiltinSort::Float, "-NaN", false),
        ] {
            assert_eq!(
                builtin_token_precedence(sort, value).is_some(),
                expected,
                "{sort:?} {value:?}"
            );
        }
    }

    fn lexicon(terminals: &[&str], regex_precedence: Option<u32>) -> TokenLexicon {
        TokenLexicon {
            terminals: terminals.iter().map(|value| (*value).to_owned()).collect(),
            regex_precedence,
        }
    }

    #[test]
    fn terminals_and_competing_regex_tokens_force_token_syntax() {
        let plain = lexicon(&[], None);
        assert!(plain.is_bare(BuiltinSort::Int, "1"));
        assert!(plain.is_bare(BuiltinSort::Bool, "true"));
        assert!(!plain.is_bare(BuiltinSort::Id, "x"));

        let keyword = lexicon(&["0", "true"], None);
        assert!(!keyword.is_bare(BuiltinSort::Int, "0"));
        assert!(keyword.is_bare(BuiltinSort::Int, "1"));
        assert!(!keyword.is_bare(BuiltinSort::Bool, "true"));
        assert!(keyword.is_bare(BuiltinSort::Bool, "false"));

        let low = lexicon(&[], Some(1));
        assert!(low.is_bare(BuiltinSort::Int, "1"));
        assert!(!low.is_bare(BuiltinSort::String, r#""s""#));
        assert!(low.is_bare(BuiltinSort::Bool, "true"));

        let high = lexicon(&[], Some(2));
        assert!(!high.is_bare(BuiltinSort::Int, "1"));
        assert!(high.is_bare(BuiltinSort::Bool, "false"));
        // A user regex at prec(2) may claim `1.5` but not `NaN`, which K lexes at prec(3).
        assert!(!high.is_bare(BuiltinSort::Float, "1.5"));
        assert!(high.is_bare(BuiltinSort::Float, "NaN"));
        assert!(!lexicon(&["NaN"], None).is_bare(BuiltinSort::Float, "NaN"));
    }

    #[test]
    fn canonical_string_tokens_lex_back_bare() {
        for value in [
            "",
            "plain",
            "say \"hi\"",
            "a\\b",
            "line\nbreak\t\r\u{c}",
            "\u{0}\u{7f}\u{c1}\u{ff}",
        ] {
            let token = krs_ir::string_token::encode(value).unwrap();
            assert!(is_string(&token), "{token}");
            assert_eq!(krs_ir::string_token::decode(&token).unwrap(), value);
            assert!(lexicon(&[], None).is_bare(BuiltinSort::String, &token));
        }
    }

    #[test]
    fn token_literals_read_back_exactly() {
        // Models K's `#KToken` conversion: drop the quotes, then replace `\"` with `"`.
        let read_back = |literal: &str| literal[1..literal.len() - 1].replace("\\\"", "\"");
        for value in [
            "$x",
            "plain",
            r#"say "hi""#,
            r"a\\b",
            r"\x41\u00e9\U0001F600\n\t",
            r#"\\""#,
            "é",
        ] {
            let literal = token_literal(value).expect("representable token");
            assert!(is_string(&literal), "{literal} is not a KString");
            assert_eq!(read_back(&literal), value);
        }
        assert_eq!(token_literal("$x").as_deref(), Some(r#""$x""#));
        for value in ["line\nbreak", r#"a\"b"#, r"a\q", r"\x4", "trailing\\"] {
            assert_eq!(token_literal(value), None, "{value:?}");
        }
    }
}
