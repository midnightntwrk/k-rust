use std::collections::BTreeMap;
use std::fmt::Write;

use crate::definition::AttributeKey;
use crate::definition::{ProductionItem, Sentence, parse_regex};
use crate::kast::FrontendSort;

use super::{Error, quote_c_string};

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) enum TokenKey {
    Literal(String),
    /// A regex token, identified and ordered by its canonical form
    /// ([`crate::definition::Regex::to_canonical_string`]), as the in-process scanner identifies
    /// and orders its regex lexemes: regexes with the same canonical form have the same syntax
    /// tree, so they are one token whatever their spelling, and two different regex tokens of
    /// equal precedence that match equal-length text are tried in the same order by both
    /// scanners (the token order is the Flex rule order, see [`Scanner::new`]).
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
                        let Some(key) = TokenKey::from_item(item)? else {
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
        let key = TokenKey::from_item(item)?
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
    /// Every action starts with `KRUST_LOCATE`, which sets the token's location and moves the
    /// line and column past the matched text (see [`LOCATE`]); the default rule's `ECHO` runs it
    /// as well. The location is
    /// set in the action rather than by `YY_USER_ACTION` and `%option yylineno`, which Flex runs
    /// before the action, because a `$`-anchored rule's action may still reject its match, and a
    /// rejected match must not move the line or column.
    ///
    /// A `$`-anchored rule `R` is printed as `R` with an action that executes `REJECT` unless
    /// the character after the match is a newline; `REJECT` makes Flex take its next candidate
    /// (the same length later in the rule order, then shorter matches, of any rule), so the winner
    /// is the longest token among the candidates whose anchors hold, then the first in rule
    /// order.
    ///
    /// Only a scanner with a `$`-anchored rule contains `REJECT`. Such a scanner keeps one DFA
    /// state per character scanned for the current match, in a state buffer Flex sizes for its
    /// input buffer; Flex therefore cannot enlarge that input buffer, and a scanner reading its
    /// input in chunks stops ("input buffer overflow, can't enlarge buffer because scanner uses
    /// REJECT") as soon as the text scanned for one match, which includes the lookahead for a
    /// longer candidate that then fails, outgrows the buffer. So this scanner reads its whole
    /// input into one buffer before scanning (`YY_USER_INIT`) and sizes the state buffer for it:
    /// no match can scan past that buffer, and the character after every match, the one the
    /// anchor check reads, is in it.
    /// It only stops on input that does not fit in memory or in Flex's `int` buffer sizes, with
    /// an error. `REJECT` also slows all of that scanner's matching.
    pub fn render(&self) -> Result<String, Error> {
        let rules = self
            .tokens
            .iter()
            .map(|token| token.key.rule())
            .collect::<Result<Vec<_>, _>>()?;
        let uses_reject = self
            .line_markers
            .iter()
            .chain(&self.layout)
            .chain(&rules)
            .any(|rule| rule.end_line);
        let mut output = String::from(
            "%{\n\
#include \"node.h\"\n\
#include \"parser.tab.h\"\n\
char *filename;\n\
static void krust_locate(yyscan_t yyscanner, YYLTYPE *location);\n\
#define KRUST_LOCATE krust_locate(yyscanner, yylloc)\n\
#define KRUST_AT_LINE_END (yyg->yy_hold_char == '\\n')\n\
#define ECHO do {\\\n\
  KRUST_LOCATE;\\\n\
  fprintf (stderr, \"%d:%d:%d:%d:syntax error: unexpected %s\\n\", yylloc->first_line, yylloc->first_column, yylloc->last_line, yylloc->last_column, yytext);\\\n\
  exit(1);\\\n\
} while (0)\n\
void line_marker(char *, void *);\n\
",
        );
        if uses_reject {
            output.push_str(
                "#include <limits.h>\n\
static void krust_scan_whole_input(yyscan_t yyscanner);\n\
#define YY_USER_INIT krust_scan_whole_input(yyscanner);\n",
            );
        }
        output.push_str(
            "%}\n\n\
%option reentrant bison-bridge\n\
%option bison-locations\n\
%option noyywrap\n\
%option extra-type=\"int\"\n",
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
        for (token, rule) in self.tokens.iter().zip(&rules) {
            rule.render(
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
        output.push_str("%%\n\n");
        output.push_str(LOCATE);
        if uses_reject {
            output.push_str(SCAN_WHOLE_INPUT);
        }
        Ok(output)
    }
}

/// The user-code function behind `KRUST_LOCATE` (see [`Scanner::render`]): set the location of
/// the matched text and move the line and column past it.
///
/// A location numbers lines and columns from 1, counts a column per Unicode scalar value (per
/// UTF-8 byte that does not continue a sequence), and ends at the column after the last character,
/// so an empty span starts where it ends and a one-line token's width is its end column minus its
/// start column; these are the locations the in-process parser gives (`inner::location`), on every
/// line alike. `\n`, `\r`, `\r\n`, vertical tab, form feed, U+0085, U+2028 and U+2029 each end a
/// line. `yycolumn` holds the number of columns already on the line, which is where Flex starts it
/// for a new buffer (0), and `yyextra` records that the last character located was `\r`, so the
/// `\n` of a `\r\n` that two tokens split (the default layout matches one character at a time)
/// does not end a second line.
const LOCATE: &str = "static void krust_locate(yyscan_t yyscanner, YYLTYPE *location) {\n\
  struct yyguts_t *yyg = (struct yyguts_t *)yyscanner;\n\
  const unsigned char *text = (const unsigned char *)yytext;\n\
  location->first_line = yylineno;\n\
  location->first_column = yycolumn + 1;\n\
  for (int index = 0; index < yyleng; ++index) {\n\
    unsigned char byte = text[index];\n\
    if (byte == '\\n' && yyextra) {\n\
      yyextra = 0;\n\
      continue;\n\
    }\n\
    yyextra = byte == '\\r';\n\
    int extra = 0;\n\
    if (byte == 0xC2 && index + 1 < yyleng && text[index + 1] == 0x85)\n\
      extra = 1;\n\
    else if (byte == 0xE2 && index + 2 < yyleng && text[index + 1] == 0x80 &&\n\
             (text[index + 2] == 0xA8 || text[index + 2] == 0xA9))\n\
      extra = 2;\n\
    if (extra || byte == '\\n' || byte == '\\r' || byte == '\\v' || byte == '\\f') {\n\
      yylineno++;\n\
      yycolumn = 0;\n\
      index += extra;\n\
    } else if ((byte & 0xC0) != 0x80) {\n\
      yycolumn++;\n\
    }\n\
  }\n\
  location->last_line = yylineno;\n\
  location->last_column = yycolumn + 1;\n\
  location->filename = filename;\n\
}\n";

/// The user-code section of a scanner that uses `REJECT` (see [`Scanner::render`]): read all of
/// `yyin` into one buffer that ends with Flex's two end-of-buffer characters, scan that buffer,
/// and give Flex a state buffer for it before `yylex` allocates its default one. One match pushes
/// a state for its start, one per character it reads, and one per end-of-buffer character it
/// reads (at most both), so `length + 3` states suffice; this is the bound Flex's own state buffer
/// keeps for its own buffers, which hold at most `YY_BUF_SIZE - 1` characters in
/// `YY_BUF_SIZE + 2` states. A buffer from `yy_scan_buffer` is never refilled, so Flex never has
/// to enlarge it; the buffer is marked as Flex's own so that `yylex_destroy` frees it, and the
/// line and column start where `yy_create_buffer` would start them.
const SCAN_WHOLE_INPUT: &str = "\n\
static void krust_scan_whole_input(yyscan_t yyscanner) {\n\
  struct yyguts_t *yyg = (struct yyguts_t *)yyscanner;\n\
  FILE *input = yyin ? yyin : stdin;\n\
  size_t capacity = 65536, length = 0;\n\
  char *buffer = (char *)yyalloc(capacity, yyscanner);\n\
  if (!buffer)\n\
    YY_FATAL_ERROR(\"out of dynamic memory in krust_scan_whole_input()\");\n\
  for (;;) {\n\
    if (capacity - length <= 2) {\n\
      if (capacity > (size_t)INT_MAX)\n\
        YY_FATAL_ERROR(\"input too large for the scanner\");\n\
      capacity *= 2;\n\
      buffer = (char *)yyrealloc(buffer, capacity, yyscanner);\n\
      if (!buffer)\n\
        YY_FATAL_ERROR(\"out of dynamic memory in krust_scan_whole_input()\");\n\
    }\n\
    size_t count = fread(buffer + length, 1, capacity - length - 2, input);\n\
    if (count == 0) {\n\
      if (ferror(input))\n\
        YY_FATAL_ERROR(\"input in flex scanner failed\");\n\
      break;\n\
    }\n\
    length += count;\n\
  }\n\
  if (length > (size_t)INT_MAX - 3)\n\
    YY_FATAL_ERROR(\"input too large for the scanner\");\n\
  buffer[length] = YY_END_OF_BUFFER_CHAR;\n\
  buffer[length + 1] = YY_END_OF_BUFFER_CHAR;\n\
  YY_BUFFER_STATE state = yy_scan_buffer(buffer, length + 2, yyscanner);\n\
  if (!state)\n\
    YY_FATAL_ERROR(\"could not scan the input buffer\");\n\
  state->yy_is_our_buffer = 1;\n\
  yyset_lineno(1, yyscanner);\n\
  yyset_column(0, yyscanner);\n\
  yyg->yy_state_buf =\n\
      (yy_state_type *)yyalloc((length + 3) * sizeof(yy_state_type), yyscanner);\n\
  if (!yyg->yy_state_buf)\n\
    YY_FATAL_ERROR(\"out of dynamic memory in krust_scan_whole_input()\");\n\
}\n";

impl FlexRule {
    /// Write this rule with `action` after the anchor check and the location bookkeeping.
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
    }
}

impl TokenKey {
    fn from_item(item: &ProductionItem) -> Result<Option<Self>, Error> {
        match item {
            ProductionItem::NonTerminal { .. } => Ok(None),
            ProductionItem::Terminal(value) => {
                Ok((!value.is_empty()).then(|| Self::Literal(value.clone())))
            }
            ProductionItem::RegexTerminal { regex, .. } => Ok(Some(Self::Regex(
                parse_flex_regex(regex)?.to_canonical_string(),
            ))),
        }
    }

    /// The token as Bison's diagnostics name it: the Flex form of the literal or regex, `$`
    /// included.
    pub fn pattern(&self) -> Result<String, Error> {
        match self {
            Self::Literal(value) => Ok(quote_c_string(value)),
            Self::Regex(canonical) => Ok(parse_flex_regex(canonical)?.to_flex_string()),
        }
    }

    fn rule(&self) -> Result<FlexRule, Error> {
        match self {
            Self::Literal(value) => Ok(FlexRule {
                start_line: false,
                body: quote_c_string(value),
                end_line: false,
            }),
            Self::Regex(canonical) => render_rule(canonical),
        }
    }

    pub fn description(&self) -> String {
        match self {
            Self::Literal(value) => format!("{value:?}"),
            Self::Regex(canonical) => format!("r{canonical:?}"),
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

    fn token_production(regex: &str) -> Sentence {
        Sentence::Production {
            label: None,
            parameters: Vec::new(),
            sort: Sort::new("Token"),
            items: vec![ProductionItem::RegexTerminal {
                precede_regex: None,
                regex: regex.into(),
                follow_regex: None,
            }],
            attributes: Attributes::default(),
        }
    }

    /// Only a scanner with a `$`-anchored rule uses `REJECT`, and only such a scanner reads its
    /// whole input before scanning; any other scanner keeps Flex's chunked reading.
    #[test]
    fn only_a_scanner_with_an_end_anchored_rule_rejects_and_reads_its_whole_input() {
        for (regex, anchored) in [("[a-z]+", false), ("^[a-z]+", false), ("[a-z]+$", true)] {
            let rendered = Scanner::new(&[token_production(regex)])
                .unwrap()
                .render()
                .unwrap();
            assert_eq!(rendered.contains("REJECT"), anchored, "{regex}");
            assert_eq!(
                rendered.contains("#define YY_USER_INIT krust_scan_whole_input(yyscanner);"),
                anchored,
                "{regex}"
            );
            assert_eq!(
                rendered.contains("static void krust_scan_whole_input(yyscan_t yyscanner) {"),
                anchored,
                "{regex}"
            );
        }
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
