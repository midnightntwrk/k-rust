use std::collections::BTreeMap;
use std::fmt::Write;

use crate::definition::AttributeKey;
use crate::definition::{ProductionItem, Sentence, parse_regex};
use crate::kast::FrontendSort;

use super::{Error, quote_c_string};

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) enum TokenKey {
    Literal(String),
    /// K's standalone Flex scanner identifies regex tokens by their body.
    ///
    /// The legacy KAST `precedeRegex` and `followRegex` fields are enforced by the in-process
    /// scanner, but the pinned standalone generator has no corresponding lookaround mechanism.
    Regex(String),
}

#[derive(Clone, Debug)]
pub(super) struct Token {
    pub key: TokenKey,
    pub kind: usize,
    pub precedence: i32,
}

#[derive(Clone, Debug)]
pub(super) struct Scanner {
    tokens: Vec<Token>,
    kinds: BTreeMap<TokenKey, usize>,
    lexical: Vec<(String, String)>,
    layout: Vec<FlexRule>,
    line_markers: Vec<FlexRule>,
}

/// One Flex rule's regex: its Flex body and its line anchors.
///
/// A `$`-anchored token (or layout) competes in the longest-match rule with the length of its
/// token, which does not include the newline `$` requires (K user manual, "`prec` attribute":
/// longer tokens win, and precedence orders tokens of equal length). Flex's own `$` is trailing
/// context, whose length Flex adds to the match it compares, so the rule is printed without `$`
/// and its action rejects the match when no newline follows it (see [`Scanner::render`]).
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct FlexRule {
    start_line: bool,
    body: String,
    end_line: bool,
}

impl Scanner {
    pub fn new(sentences: &[Sentence]) -> Result<Self, Error> {
        let mut precedences = BTreeMap::<TokenKey, i32>::new();
        let mut lexical = BTreeMap::<String, String>::new();
        let mut layout = Vec::new();
        let mut line_markers = Vec::new();
        let mut layout_declared = false;

        for sentence in sentences {
            match sentence {
                Sentence::SyntaxLexical { name, regex, .. } => {
                    let rendered = parse_regex(regex)
                        .map_err(|error| Error::render(format!("invalid lexical {name}: {error}")))?
                        .to_flex_string();
                    if let Some(existing) = lexical.get(name) {
                        if existing != &rendered {
                            return Err(Error::render(format!(
                                "conflicting definitions for lexical identifier {name}"
                            )));
                        }
                    } else {
                        lexical.insert(name.clone(), rendered);
                    }
                }
                Sentence::Production {
                    sort,
                    items,
                    attributes,
                    ..
                } => {
                    if sort.is_frontend(FrontendSort::Layout)
                        || sort.is_frontend(FrontendSort::LineMarker)
                    {
                        let [ProductionItem::RegexTerminal { regex, .. }] = items.as_slice() else {
                            return Err(Error::render(format!(
                                "productions of sort `{}` must contain exactly one regex terminal",
                                sort.name
                            )));
                        };
                        let rendered = render_rule(regex)?;
                        if sort.is_frontend(FrontendSort::Layout) {
                            layout_declared = true;
                            layout.push(rendered);
                        } else {
                            line_markers.push(rendered);
                        }
                    }

                    let declared = attributes
                        .string(AttributeKey::Prec)
                        .map(|value| {
                            value.parse::<i32>().map_err(|_| {
                                Error::render(format!("invalid token precedence {value:?}"))
                            })
                        })
                        .transpose()?;
                    for item in items {
                        let Some(key) = TokenKey::from_item(item) else {
                            continue;
                        };
                        let precedence = declared.unwrap_or(match key {
                            TokenKey::Literal(_) => i32::MAX,
                            TokenKey::Regex(_) => 0,
                        });
                        match precedences.get(&key) {
                            Some(existing) if *existing != precedence => {
                                return Err(Error::render(format!(
                                    "inconsistent token precedence for {}: {existing} and {precedence}",
                                    key.description()
                                )));
                            }
                            Some(_) => {}
                            None => {
                                precedences.insert(key, precedence);
                            }
                        }
                    }
                }
                Sentence::SyntaxSort { sort, .. } if sort.is_frontend(FrontendSort::Layout) => {
                    layout_declared = true;
                }
                Sentence::SyntaxSort { .. }
                | Sentence::SortSynonym { .. }
                | Sentence::SyntaxAssociativity { .. }
                | Sentence::SyntaxPriority { .. }
                | Sentence::ContextAlias { .. }
                | Sentence::Context { .. }
                | Sentence::Rule { .. }
                | Sentence::Claim { .. }
                | Sentence::Configuration { .. }
                | Sentence::Bubble { .. } => {}
            }
        }

        if !layout_declared {
            layout.extend(
                crate::inner::DEFAULT_LAYOUT
                    .into_iter()
                    .map(render_rule)
                    .collect::<Result<Vec<_>, _>>()?,
            );
        }

        let kinds = precedences
            .keys()
            .cloned()
            .enumerate()
            .map(|(index, key)| (key, index + 1))
            .collect::<BTreeMap<_, _>>();
        let mut tokens = precedences
            .into_iter()
            .map(|(key, precedence)| Token {
                kind: kinds[&key],
                key,
                precedence,
            })
            .collect::<Vec<_>>();
        tokens.sort_by(|left, right| {
            right
                .precedence
                .cmp(&left.precedence)
                .then_with(|| left.key.cmp(&right.key))
        });
        layout.sort();
        layout.dedup();
        line_markers.sort();
        line_markers.dedup();

        Ok(Self {
            tokens,
            kinds,
            lexical: lexical.into_iter().collect(),
            layout,
            line_markers,
        })
    }

    pub fn kind(&self, item: &ProductionItem) -> Result<usize, Error> {
        let key = TokenKey::from_item(item)
            .ok_or_else(|| Error::render("a nonterminal has no scanner token"))?;
        self.kinds.get(&key).copied().ok_or_else(|| {
            Error::render(format!("missing scanner token for {}", key.description()))
        })
    }

    pub fn tokens_by_kind(&self) -> Vec<&Token> {
        let mut tokens = self.tokens.iter().collect::<Vec<_>>();
        tokens.sort_by_key(|token| token.kind);
        tokens
    }

    /// Render the Flex scanner.
    ///
    /// Every action starts with `KRUST_LOCATE`, which counts the newlines of the matched text
    /// and sets the token's location; the default rule's `ECHO` runs it as well. The location is
    /// set in the action rather than by `YY_USER_ACTION` and `%option yylineno`, which Flex runs
    /// before the action, because a `$`-anchored rule's action may still reject its match, and a
    /// rejected match must not move the line or column.
    ///
    /// A `$`-anchored rule `R` is printed as `R` with an action that executes `REJECT` unless
    /// the character after the match is a newline; `REJECT` makes Flex take its next candidate
    /// (the same length later in the rule order, then shorter matches, of any rule), so the winner
    /// is the longest token among the candidates whose anchors hold, then the first in rule
    /// order. The rule `R(.|\n)`, whose action always rejects, follows it: it makes the scanner
    /// read the character after every match of `R` before choosing, so the character is in the
    /// buffer even when `R`'s match ends where Flex's last read ended.
    ///
    /// Only a scanner with a `$`-anchored rule contains `REJECT`, which Flex supports at a cost:
    /// it slows all of that scanner's matching, and that scanner stops with "input buffer
    /// overflow, can't enlarge buffer because scanner uses REJECT" on a single token at least as
    /// long as its 16 KiB input buffer.
    pub fn render(&self) -> Result<String, Error> {
        let mut output = String::from(
            "%{\n\
#include \"node.h\"\n\
#include \"parser.tab.h\"\n\
char *filename;\n\
#define KRUST_LOCATE do { \\\n\
  for (int krust_index = 0; krust_index < yyleng; ++krust_index) \\\n\
    if (yytext[krust_index] == '\\n') { yylineno++; yycolumn = 0; } \\\n\
  yylloc->first_line = yylloc->last_line = yylineno; \\\n\
  yylloc->first_column = yycolumn; yylloc->last_column = yycolumn + yyleng - 1; \\\n\
  yycolumn += yyleng; \\\n\
  yylloc->filename = filename; \\\n\
} while (0)\n\
#define KRUST_AT_LINE_END (yyg->yy_hold_char == '\\n')\n\
#define ECHO do {\\\n\
  KRUST_LOCATE;\\\n\
  fprintf (stderr, \"%d:%d:%d:%d:syntax error: unexpected %s\\n\", yylloc->first_line, yylloc->first_column, yylloc->last_line, yylloc->last_column, yytext);\\\n\
  exit(1);\\\n\
} while (0)\n\
void line_marker(char *, void *);\n\
%}\n\n\
%option reentrant bison-bridge\n\
%option bison-locations\n\
%option noyywrap\n",
        );
        for (name, regex) in &self.lexical {
            writeln!(
                output,
                "{} {regex}",
                crate::definition::regex::mangle_flex_identifier(name)
            )
            .expect("writing to a string cannot fail");
        }
        output.push_str("%%\n\n");
        for rule in &self.line_markers {
            rule.render(&mut output, "  line_marker(yytext, yyscanner);\n");
        }
        for rule in &self.layout {
            rule.render(&mut output, "");
        }
        for token in &self.tokens {
            token.key.rule()?.render(
                &mut output,
                &format!(
                    "  int kind = {};\n\
  *((char **)yylval) = malloc(strlen(yytext) + 1);\n\
  strcpy(*((char **)yylval), yytext);\n\
  return kind;\n",
                    token.kind + 1
                ),
            );
        }
        Ok(output)
    }
}

impl FlexRule {
    /// Write this rule with `action` after the anchor check and the location bookkeeping, and,
    /// for a `$`-anchored rule, the always-rejecting rule that follows it.
    fn render(&self, output: &mut String, action: &str) {
        let start = if self.start_line { "^" } else { "" };
        let body = &self.body;
        writeln!(output, "{start}{body} {{").expect("writing to a string cannot fail");
        if self.end_line {
            output.push_str("  if (!KRUST_AT_LINE_END) REJECT;\n");
        }
        output.push_str("  KRUST_LOCATE;\n");
        output.push_str(action);
        output.push_str(" }\n");
        if self.end_line {
            writeln!(output, "{start}({body})(.|\\n) REJECT;")
                .expect("writing to a string cannot fail");
        }
    }
}

impl TokenKey {
    fn from_item(item: &ProductionItem) -> Option<Self> {
        match item {
            ProductionItem::NonTerminal { .. } => None,
            ProductionItem::Terminal(value) => {
                (!value.is_empty()).then(|| Self::Literal(value.clone()))
            }
            ProductionItem::RegexTerminal { regex, .. } => Some(Self::Regex(regex.clone())),
        }
    }

    /// The token as Bison's diagnostics name it: the Flex form of the literal or regex, `$`
    /// included.
    pub fn pattern(&self) -> Result<String, Error> {
        match self {
            Self::Literal(value) => Ok(quote_c_string(value)),
            Self::Regex(source) => Ok(parse_flex_regex(source)?.to_flex_string()),
        }
    }

    fn rule(&self) -> Result<FlexRule, Error> {
        match self {
            Self::Literal(value) => Ok(FlexRule {
                start_line: false,
                body: quote_c_string(value),
                end_line: false,
            }),
            Self::Regex(source) => render_rule(source),
        }
    }

    pub fn description(&self) -> String {
        match self {
            Self::Literal(value) => format!("{value:?}"),
            Self::Regex(source) => format!("r{source:?}"),
        }
    }
}

fn parse_flex_regex(source: &str) -> Result<crate::definition::Regex, Error> {
    parse_regex(source).map_err(|error| Error::render(format!("invalid regex {source:?}: {error}")))
}

fn render_rule(source: &str) -> Result<FlexRule, Error> {
    let regex = parse_flex_regex(source)?;
    Ok(FlexRule {
        start_line: regex.start_line,
        body: regex.body.to_flex_string(),
        end_line: regex.end_line,
    })
}

#[cfg(test)]
mod tests {
    use crate::definition::{Attributes, ProductionItem, Sentence};
    use crate::kast::{Label, Sort};

    use super::Scanner;

    fn regex_production(
        label: &str,
        precede_regex: Option<&str>,
        follow_regex: Option<&str>,
    ) -> Sentence {
        Sentence::Production {
            label: Some(Label::new(label)),
            parameters: Vec::new(),
            sort: Sort::new("Token"),
            items: vec![ProductionItem::RegexTerminal {
                precede_regex: precede_regex.map(str::to_owned),
                regex: "[a-z]+".into(),
                follow_regex: follow_regex.map(str::to_owned),
            }],
            attributes: Attributes::default(),
        }
    }

    #[test]
    fn standalone_regex_identity_ignores_legacy_restrictions() {
        let left = regex_production("left", Some("[0-9]"), None);
        let right = regex_production("right", None, Some("[A-Z]"));
        let sentences = [left.clone(), right.clone()];

        let scanner = Scanner::new(&sentences).unwrap();

        assert_eq!(scanner.tokens_by_kind().len(), 1);
        let Sentence::Production {
            items: left_items, ..
        } = left
        else {
            unreachable!()
        };
        let Sentence::Production {
            items: right_items, ..
        } = right
        else {
            unreachable!()
        };
        assert_eq!(
            scanner.kind(&left_items[0]).unwrap(),
            scanner.kind(&right_items[0]).unwrap()
        );
        assert_eq!(scanner.render().unwrap().matches("return kind;").count(), 1);
    }

    #[test]
    fn conflicting_lexical_definitions_fail_in_every_order() {
        let first = Sentence::SyntaxLexical {
            name: "#word".into(),
            regex: "[a-z]+".into(),
            attributes: Attributes::default(),
        };
        let second = Sentence::SyntaxLexical {
            name: "#word".into(),
            regex: "[A-Z]+".into(),
            attributes: Attributes::default(),
        };

        for sentences in [
            [first.clone(), second.clone()],
            [second.clone(), first.clone()],
        ] {
            let error = Scanner::new(&sentences).unwrap_err();
            assert_eq!(
                error.to_string(),
                "conflicting definitions for lexical identifier #word"
            );
        }
    }
}
