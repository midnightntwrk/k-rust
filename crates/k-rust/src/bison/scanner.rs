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
    /// A regex token's text is a match of its regex, whatever text surrounds it: a regex terminal
    /// holds no restriction on its neighbours (the KAST JSON reader refuses a document that states
    /// a precede or follow restriction), so the canonical form is the whole token language.
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
}

/// One Flex rule's regex: its Flex body and its line anchors.
///
/// The anchors are checked by the rule's action, not printed as Flex's `^` and `$`: those see
/// only `\n` as a line end, where a K anchor sees every line terminator a location counts
/// (`crate::lines`). Flex's `$` is also trailing context, whose length Flex adds to the match it
/// compares, while a `$`-anchored token (or layout) competes in the longest-match rule with the
/// length of its token, which does not include the line terminator `$` requires (K user manual,
/// "`prec` attribute": longer tokens win, and precedence orders tokens of equal length). So the
/// rule is printed as its body, and its action rejects the match where an anchor does not hold
/// (see [`Scanner::render`]).
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
                    if sort.is_frontend(FrontendSort::Layout) {
                        let [ProductionItem::RegexTerminal { regex, .. }] = items.as_slice() else {
                            return Err(Error::render(format!(
                                "productions of sort `{}` must contain exactly one regex terminal",
                                sort.name
                            )));
                        };
                        layout_declared = true;
                        layout.push(render_rule(regex)?);
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
                        // The in-process scanner's rule (`inner::parser::scanner::token_precedence`):
                        // the production's `prec`, else the largest precedence for a literal and 0
                        // for a regex; every mention must agree.
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

        Ok(Self {
            tokens,
            kinds,
            lexical: lexical.into_iter().collect(),
            layout,
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
    /// as well (see [`UNEXPECTED`]). The location is
    /// set in the action rather than by `YY_USER_ACTION` and `%option yylineno`, which Flex runs
    /// before the action, because an anchored rule's action may still reject its match, and a
    /// rejected match must not move the line or column.
    ///
    /// An anchored rule `^R`, `R$` or `^R$` is printed as `R` with an action that executes
    /// `REJECT` unless the match starts a line (`KRUST_AT_LINE_START`) or ends one
    /// (`KRUST_AT_LINE_END`), as [`LINE_ANCHORS`] decides; `REJECT` makes Flex take its next
    /// candidate (the same length later in the rule order, then shorter matches, of any rule), so
    /// the winner is the longest token among the candidates whose anchors hold, then the first in
    /// rule order.
    ///
    /// Only a scanner with an anchored rule contains `REJECT`. Such a scanner keeps one DFA
    /// state per character scanned for the current match, in a state buffer Flex sizes for its
    /// input buffer; Flex therefore cannot enlarge that input buffer, and a scanner reading its
    /// input in chunks stops ("input buffer overflow, can't enlarge buffer because scanner uses
    /// REJECT") as soon as the text scanned for one match, which includes the lookahead for a
    /// longer candidate that then fails, outgrows the buffer. So this scanner reads its whole
    /// input into one buffer before scanning (`YY_USER_INIT`) and sizes the state buffer for it:
    /// no match can scan past that buffer, and the characters around every match, the ones the
    /// anchor checks read, are in it.
    /// It only stops on input that does not fit in memory or in Flex's `int` buffer sizes, with
    /// an error. `REJECT` also slows all of that scanner's matching.
    pub fn render(&self) -> Result<String, Error> {
        let rules = self
            .tokens
            .iter()
            .map(|token| token.key.rule())
            .collect::<Result<Vec<_>, _>>()?;
        let uses_reject = self
            .layout
            .iter()
            .chain(&rules)
            .any(|rule| rule.start_line || rule.end_line);
        let mut output = String::from(
            "%{\n\
#include \"node.h\"\n\
#include \"parser.tab.h\"\n\
char *filename;\n\
static void krust_locate(yyscan_t yyscanner, YYLTYPE *location);\n\
#define KRUST_LOCATE krust_locate(yyscanner, yylloc)\n\
static void krust_unexpected(yyscan_t yyscanner, YYLTYPE *location);\n\
#define ECHO krust_unexpected(yyscanner, yylloc)\n",
        );
        if uses_reject {
            output.push_str(
                "#include <limits.h>\n\
static void krust_scan_whole_input(yyscan_t yyscanner);\n\
#define YY_USER_INIT krust_scan_whole_input(yyscanner);\n\
static int krust_at_line_start(yyscan_t yyscanner);\n\
static int krust_at_line_end(yyscan_t yyscanner);\n\
#define KRUST_AT_LINE_START krust_at_line_start(yyscanner)\n\
#define KRUST_AT_LINE_END krust_at_line_end(yyscanner)\n",
            );
        }
        output.push_str(
            "%}\n\n\
%option reentrant bison-bridge\n\
%option bison-locations\n\
%option noyywrap\n\
%option 8bit\n\
%option extra-type=\"const char *\"\n",
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
        for rule in &self.layout {
            rule.render(&mut output, "");
        }
        for (token, rule) in self.tokens.iter().zip(&rules) {
            rule.render(&mut output, &format!("  return {};\n", token.kind + 1));
        }
        output.push_str("%%\n\n");
        output.push_str(&line_terminator_table());
        output.push_str(LOCATE);
        output.push_str(UNEXPECTED);
        if uses_reject {
            output.push_str(SCAN_WHOLE_INPUT);
            output.push_str(LINE_ANCHORS);
        }
        Ok(output)
    }
}

/// The line terminators of `crate::lines`, in its order, as a C array of byte strings, and
/// `krust_terminator_at`, the length of the first of them in that order (so the longest) that a
/// NUL-terminated text starts with, or 0, and `krust_terminator_rest`, the rest of the first
/// terminator strictly longer than the `length` bytes at `text` that starts with them, or `NULL`.
/// No terminator holds a NUL byte, so a comparison stops at the end of `yytext` or of a buffer.
fn line_terminator_table() -> String {
    let terminators = crate::lines::LINE_TERMINATORS
        .into_iter()
        .map(|terminator| {
            let escaped = terminator
                .bytes()
                .map(|byte| format!("\\x{byte:02X}"))
                .collect::<String>();
            format!("\"{escaped}\"")
        })
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "static const char *const krust_line_terminators[] = {{{terminators}}};\n\
#define KRUST_LINE_TERMINATORS (sizeof krust_line_terminators / sizeof *krust_line_terminators)\n\
static size_t krust_terminator_at(const unsigned char *text) {{\n\
  for (size_t index = 0; index < KRUST_LINE_TERMINATORS; ++index) {{\n\
    size_t length = strlen(krust_line_terminators[index]);\n\
    if (strncmp((const char *)text, krust_line_terminators[index], length) == 0)\n\
      return length;\n\
  }}\n\
  return 0;\n\
}}\n\
static const char *krust_terminator_rest(const unsigned char *text, size_t length) {{\n\
  for (size_t index = 0; index < KRUST_LINE_TERMINATORS; ++index) {{\n\
    const char *terminator = krust_line_terminators[index];\n\
    if (strlen(terminator) > length && strncmp(terminator, (const char *)text, length) == 0)\n\
      return terminator + length;\n\
  }}\n\
  return NULL;\n\
}}\n"
    )
}

/// The user-code function behind `KRUST_LOCATE` (see [`Scanner::render`]): set the location of
/// the matched text and move the line and column past it. Every byte of the input is matched by
/// exactly one action that runs it (a rejected match does not run it), so `krust_read` keeps the
/// input in order and gives the location its byte span there.
///
/// A location numbers lines and columns from 1, counts a column per Unicode scalar value (per
/// UTF-8 byte that does not continue a sequence), and ends at the column after the last character,
/// so an empty span starts where it ends and a one-line token's width is its end column minus its
/// start column; these are the locations the in-process parser gives (`inner::location`), on every
/// line alike. Each line terminator of `crate::lines` ends a line (see
/// [`line_terminator_table`]). `yycolumn` holds the number of columns already on the line, which
/// is where Flex starts it for a new buffer (0). A token that ends with a terminator that a
/// longer one extends (`\r`, which `\r\n` extends) leaves the rest of the longer one in
/// `yyextra`, so that rest at the start of the next token (the `\n` of a `\r\n` that two tokens
/// split, as the default layout matching one character at a time does) does not end a second
/// line.
const LOCATE: &str = "static void krust_locate(yyscan_t yyscanner, YYLTYPE *location) {\n\
  struct yyguts_t *yyg = (struct yyguts_t *)yyscanner;\n\
  const unsigned char *text = (const unsigned char *)yytext;\n\
  int index = 0;\n\
  location->first_line = yylineno;\n\
  location->first_column = yycolumn + 1;\n\
  krust_read(location, yytext, (size_t)yyleng);\n\
  if (yyextra) {\n\
    size_t rest = strlen(yyextra);\n\
    if (strncmp(yytext, yyextra, rest) == 0)\n\
      index = (int)rest;\n\
    yyextra = NULL;\n\
  }\n\
  while (index < yyleng) {\n\
    size_t length = krust_terminator_at(text + index);\n\
    if (length) {\n\
      yylineno++;\n\
      yycolumn = 0;\n\
      if (index + (int)length == yyleng)\n\
        yyextra = krust_terminator_rest(text + index, length);\n\
      index += (int)length;\n\
    } else {\n\
      if ((text[index] & 0xC0) != 0x80)\n\
        yycolumn++;\n\
      index++;\n\
    }\n\
  }\n\
  location->last_line = yylineno;\n\
  location->last_column = yycolumn + 1;\n\
  location->filename = filename;\n\
}\n";

/// The user-code function behind the default rule's `ECHO` (see [`Scanner::render`]), which runs
/// on a byte that no rule matches: locate that byte, report it as unexpected and stop. The location
/// spans the byte's column, and a column holds a byte that does not continue a UTF-8 sequence and
/// the continuation bytes after it (see [`LOCATE`]), so the report writes the whole character in
/// that column: the matched byte and the continuation bytes that `input` reads after it, which
/// refills the buffer when the character continues past it. The bytes are written as they are, so
/// a NUL byte is written too.
const UNEXPECTED: &str = "static void krust_unexpected(yyscan_t yyscanner, YYLTYPE *location) {\n\
  struct yyguts_t *yyg = (struct yyguts_t *)yyscanner;\n\
  int byte;\n\
  krust_locate(yyscanner, location);\n\
  fprintf(stderr, \"%d:%d:%d:%d:syntax error: unexpected \", location->first_line,\n\
          location->first_column, location->last_line, location->last_column);\n\
  fwrite(yytext, 1, (size_t)yyleng, stderr);\n\
  while (((byte = input(yyscanner)) & 0xC0) == 0x80)\n\
    fputc(byte, stderr);\n\
  fputc('\\n', stderr);\n\
  exit(1);\n\
}\n";

/// The user-code functions behind `KRUST_AT_LINE_START` and `KRUST_AT_LINE_END` (see
/// [`Scanner::render`]), which hold where `crate::lines::starts_line` and `ends_line` hold at the
/// start and the end of the match. Only a scanner that reads its whole input into one buffer uses
/// them, so the text around the match, before it included, is in that buffer, which ends with
/// Flex's NUL end-of-buffer characters. Flex puts a NUL after the match while its action runs;
/// the checks put the character back for their reading and the NUL again after it.
const LINE_ANCHORS: &str = "\n\
static int krust_inside_terminator(const unsigned char *start, const unsigned char *position) {\n\
  for (size_t index = 0; index < KRUST_LINE_TERMINATORS; ++index) {\n\
    const char *terminator = krust_line_terminators[index];\n\
    size_t length = strlen(terminator);\n\
    for (size_t offset = 1; offset < length; ++offset)\n\
      if ((size_t)(position - start) >= offset &&\n\
          strncmp((const char *)position - offset, terminator, length) == 0)\n\
        return 1;\n\
  }\n\
  return 0;\n\
}\n\
static int krust_starts_line(const unsigned char *start, const unsigned char *position) {\n\
  if (position == start)\n\
    return 1;\n\
  for (size_t index = 0; index < KRUST_LINE_TERMINATORS; ++index) {\n\
    const char *terminator = krust_line_terminators[index];\n\
    size_t length = strlen(terminator);\n\
    if ((size_t)(position - start) >= length &&\n\
        strncmp((const char *)position - length, terminator, length) == 0)\n\
      return !krust_inside_terminator(start, position);\n\
  }\n\
  return 0;\n\
}\n\
static int krust_at_line_boundary(yyscan_t yyscanner, int end) {\n\
  struct yyguts_t *yyg = (struct yyguts_t *)yyscanner;\n\
  const unsigned char *start = (const unsigned char *)YY_CURRENT_BUFFER_LVALUE->yy_ch_buf;\n\
  const unsigned char *position = (const unsigned char *)yytext + (end ? yyleng : 0);\n\
  int result;\n\
  yytext[yyleng] = yyg->yy_hold_char;\n\
  result = end ? krust_terminator_at(position) && !krust_inside_terminator(start, position)\n\
               : krust_starts_line(start, position);\n\
  yytext[yyleng] = '\\0';\n\
  return result;\n\
}\n\
static int krust_at_line_start(yyscan_t yyscanner) { return krust_at_line_boundary(yyscanner, 0); }\n\
static int krust_at_line_end(yyscan_t yyscanner) { return krust_at_line_boundary(yyscanner, 1); }\n";

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
        let body = &self.body;
        writeln!(output, "{body} {{").expect("writing to a string cannot fail");
        if self.start_line {
            output.push_str("  if (!KRUST_AT_LINE_START) REJECT;\n");
        }
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
    /// included, with its classes as written (see `Regex::to_flex_name`).
    pub fn pattern(&self) -> Result<String, Error> {
        match self {
            Self::Literal(value) => Ok(quote_c_string(value)),
            Self::Regex(canonical) => Ok(parse_flex_regex(canonical)?.to_flex_name()),
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

    fn regex_production(label: &str, regex: &str) -> Sentence {
        Sentence::Production {
            label: Some(Label::new(label)),
            parameters: Vec::new(),
            sort: Sort::new("Token"),
            items: vec![ProductionItem::regex(regex)],
            attributes: Attributes::default(),
        }
    }

    #[test]
    fn regexes_with_one_canonical_form_are_one_token() {
        let left = regex_production("left", "[a-z]+");
        let right = regex_production("right", "([a-z]+)");
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
        assert_eq!(
            scanner
                .render()
                .unwrap()
                .matches("KRUST_LOCATE;\n  return ")
                .count(),
            1
        );
    }

    fn token_production(regex: &str) -> Sentence {
        Sentence::Production {
            label: None,
            parameters: Vec::new(),
            sort: Sort::new("Token"),
            items: vec![ProductionItem::regex(regex)],
            attributes: Attributes::default(),
        }
    }

    /// Only a scanner with an anchored rule uses `REJECT`, and only such a scanner reads its
    /// whole input before scanning; any other scanner keeps Flex's chunked reading.
    #[test]
    fn only_a_scanner_with_an_anchored_rule_rejects_and_reads_its_whole_input() {
        for (regex, anchored) in [
            ("[a-z]+", false),
            ("^[a-z]+", true),
            ("[a-z]+$", true),
            ("^[a-z]+$", true),
        ] {
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

    /// The export gives a literal the in-process scanner's precedence: its production's `prec`,
    /// or the largest precedence, and rejects a literal two productions order differently.
    #[test]
    fn literal_precedence_is_declared_or_largest_and_must_agree() {
        let literal = |prec: Option<&str>| {
            let mut attributes = Attributes::default();
            if let Some(prec) = prec {
                attributes.insert("prec", serde_json::json!(prec));
            }
            Sentence::Production {
                label: None,
                parameters: Vec::new(),
                sort: Sort::new("Token"),
                items: vec![ProductionItem::Terminal("ab".into())],
                attributes,
            }
        };
        let precedence = |sentences: &[Sentence]| {
            Scanner::new(sentences)
                .map(|scanner| scanner.tokens_by_kind()[0].precedence)
                .map_err(|error| error.to_string())
        };

        assert_eq!(precedence(&[literal(Some("-1"))]), Ok(-1));
        assert_eq!(precedence(&[literal(None)]), Ok(i32::MAX));
        for sentences in [
            [literal(Some("-1")), literal(None)],
            [literal(None), literal(Some("-1"))],
        ] {
            assert!(
                precedence(&sentences)
                    .unwrap_err()
                    .starts_with("inconsistent token precedence for \"ab\"")
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
