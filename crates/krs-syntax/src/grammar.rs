use std::collections::BTreeSet;

use krs_ir::AtLeastTwo;
use proc_macro2::{Span, TokenStream};
use syn::parse::ParseStream;
use syn::spanned::Spanned;
use syn::{Fields, Ident, ItemImpl, ItemStruct, ItemType, LitInt, LitStr, Path, Token, Type};

use crate::parse::{
    KrsSyntax, ParseError, ProvenanceAnchors, checked_ordinal, duplicate, invalid_argument,
    missing, structured, unknown,
};
use crate::path::{is_plain_path, path_text, unqualified_path_ident};
use crate::{ProvenanceAnchor, ProvenanceRole, SyntaxError, SyntaxErrorKind, TokenRange};

/// One checked fragment of a nominal or bracket concrete-syntax template.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SyntaxTemplateItem {
    /// Literal object-language terminal text.
    Terminal(String),
    /// Named nonterminal placeholder, without its surrounding braces.
    Field(String),
}

/// A checked concrete-syntax string split into ordered grammar items.
#[derive(Clone, Debug)]
pub struct SyntaxTemplate {
    literal: LitStr,
    items: Vec<SyntaxTemplateItem>,
}

impl SyntaxTemplate {
    /// Parses the deliberately small KRS template grammar.
    ///
    /// `{{` and `}}` spell literal braces. A placeholder is one Rust field
    /// identifier between braces. Empty templates, unmatched braces, and empty
    /// placeholders are rejected.
    ///
    /// # Errors
    ///
    /// Returns a structured template error at the string literal.
    pub fn parse(literal: LitStr) -> Result<Self, SyntaxError> {
        let text = literal.value();
        if text.is_empty() {
            return Err(invalid_template(
                "the template must not be empty",
                literal.span(),
            ));
        }

        let chars = text.char_indices().collect::<Vec<_>>();
        let mut items = Vec::new();
        let mut terminal = String::new();
        let mut cursor = 0;
        while cursor < chars.len() {
            let (_, character) = chars[cursor];
            match character {
                '{' if chars.get(cursor + 1).is_some_and(|(_, next)| *next == '{') => {
                    terminal.push('{');
                    cursor += 2;
                }
                '}' if chars.get(cursor + 1).is_some_and(|(_, next)| *next == '}') => {
                    terminal.push('}');
                    cursor += 2;
                }
                '{' => {
                    push_terminal(&mut items, &mut terminal);
                    let start = cursor + 1;
                    let mut end = start;
                    while end < chars.len() && chars[end].1 != '}' {
                        if chars[end].1 == '{' {
                            return Err(invalid_template(
                                "nested `{` is not allowed in a placeholder",
                                literal.span(),
                            ));
                        }
                        end += 1;
                    }
                    if end == chars.len() {
                        return Err(invalid_template(
                            "an opening `{` has no closing `}`; did you mean `{{` for a literal opening brace?",
                            literal.span(),
                        ));
                    }
                    let name = chars[start..end]
                        .iter()
                        .map(|(_, value)| value)
                        .collect::<String>();
                    if name.is_empty() || syn::parse_str::<Ident>(&name).is_err() {
                        return Err(invalid_template(
                            "a placeholder must contain one Rust field identifier",
                            literal.span(),
                        ));
                    }
                    items.push(SyntaxTemplateItem::Field(name));
                    cursor = end + 1;
                }
                '}' => {
                    return Err(invalid_template(
                        "an unmatched `}` must be escaped as `}}`",
                        literal.span(),
                    ));
                }
                other => {
                    terminal.push(other);
                    cursor += 1;
                }
            }
        }
        push_terminal(&mut items, &mut terminal);
        if items.is_empty() {
            return Err(invalid_template(
                "the template must emit an item",
                literal.span(),
            ));
        }
        Ok(Self { literal, items })
    }

    /// Returns the original Rust string literal.
    #[must_use]
    pub const fn literal(&self) -> &LitStr {
        &self.literal
    }

    /// Returns ordered terminal and named-nonterminal fragments.
    #[must_use]
    pub fn items(&self) -> &[SyntaxTemplateItem] {
        &self.items
    }

    /// Validates exact one-to-one occurrence of the supplied field names.
    ///
    /// # Errors
    ///
    /// Rejects unknown, omitted, and repeated placeholders.
    pub fn validate_fields<'a>(
        &self,
        fields: impl IntoIterator<Item = &'a Ident>,
    ) -> Result<(), SyntaxError> {
        let fields = fields
            .into_iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>();
        for item in &self.items {
            let SyntaxTemplateItem::Field(name) = item else {
                continue;
            };
            if !fields.iter().any(|field| field == name) {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::UnknownTemplateField { name: name.clone() },
                    self.literal.span(),
                ));
            }
        }
        for field in fields {
            let count = self
                .items
                .iter()
                .filter(|item| matches!(item, SyntaxTemplateItem::Field(name) if name == &field))
                .count();
            if count != 1 {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::InvalidTemplateFieldOccurrence {
                        name: field,
                        expected: 1,
                        actual: u32::try_from(count).unwrap_or(u32::MAX),
                    },
                    self.literal.span(),
                ));
            }
        }
        Ok(())
    }

    pub(crate) fn provenance(
        &self,
        item_role: ProvenanceRole,
        field_role: ProvenanceRole,
    ) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let range = TokenRange::for_tokens(&self.literal)?;
        let mut ordinals = ProvenanceAnchors::default();
        let mut anchors = Vec::new();
        for item in &self.items {
            anchors.push(ProvenanceAnchor::new(
                item_role,
                ordinals.next(item_role, self.literal.span())?,
                range,
            ));
            if matches!(item, SyntaxTemplateItem::Field(_)) {
                anchors.push(ProvenanceAnchor::new(
                    field_role,
                    ordinals.next(field_role, self.literal.span())?,
                    range,
                ));
            }
        }
        Ok(anchors)
    }
}

fn push_terminal(items: &mut Vec<SyntaxTemplateItem>, terminal: &mut String) {
    let text = std::mem::take(terminal);
    let mut index = 0_usize;
    while index < text.len() {
        let character = text[index..]
            .chars()
            .next()
            .expect("index is on a character boundary");
        if character.is_whitespace() {
            index += character.len_utf8();
            continue;
        }
        let start = index;
        let word = character.is_alphanumeric() || character == '_';
        let singleton = matches!(character, '(' | ')' | '[' | ']' | '{' | '}' | ',' | ';');
        index += character.len_utf8();
        if !singleton {
            while index < text.len() {
                let next = text[index..]
                    .chars()
                    .next()
                    .expect("index is on a character boundary");
                let next_word = next.is_alphanumeric() || next == '_';
                if next.is_whitespace()
                    || matches!(next, '(' | ')' | '[' | ']' | '{' | '}' | ',' | ';')
                    || next_word != word
                {
                    break;
                }
                index += next.len_utf8();
            }
        }
        items.push(SyntaxTemplateItem::Terminal(text[start..index].to_owned()));
    }
}

fn invalid_template(reason: &'static str, span: Span) -> SyntaxError {
    SyntaxError::new(SyntaxErrorKind::InvalidSyntaxTemplate { reason }, span)
}

/// One checked fragment of K's compact `%N` unparse format language.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StructuredFormatFragment {
    /// Literal text; `%%` in source becomes one percent character.
    Literal(String),
    /// One-based grammar-production item position.
    Item(u16),
    /// K's `%n` newline control.
    Newline,
    /// K's `%i` indentation-increase control.
    Indent,
    /// K's `%d` indentation-decrease control.
    Dedent,
    /// K's `%c` control: print in the production's next colour.
    ColorNext,
    /// K's `%r` control: reset the printing colour.
    ColorReset,
}

/// A checked structured unparse format.
#[derive(Clone, Debug)]
pub struct StructuredFormat {
    literal: LitStr,
    fragments: Vec<StructuredFormatFragment>,
}

impl StructuredFormat {
    /// Parses literal text, `%%`, `%n`/`%i`/`%d` controls, and `%N` references.
    ///
    /// # Errors
    ///
    /// Rejects empty formats, dangling percent signs, `%0`, and positions that
    /// do not fit the target-neutral `u16` representation.
    pub fn parse(literal: LitStr) -> Result<Self, SyntaxError> {
        let text = literal.value();
        if text.is_empty() {
            return Err(invalid_format(
                "the format must not be empty",
                literal.span(),
            ));
        }
        let mut chars = text.chars().peekable();
        let mut fragments = Vec::new();
        let mut literal_text = String::new();
        while let Some(character) = chars.next() {
            if character != '%' {
                literal_text.push(character);
                continue;
            }
            if chars.peek() == Some(&'%') {
                chars.next();
                literal_text.push('%');
                continue;
            }
            if !literal_text.is_empty() {
                fragments.push(StructuredFormatFragment::Literal(std::mem::take(
                    &mut literal_text,
                )));
            }
            let control = match chars.peek().copied() {
                Some('n') => Some(StructuredFormatFragment::Newline),
                Some('i') => Some(StructuredFormatFragment::Indent),
                Some('d') => Some(StructuredFormatFragment::Dedent),
                Some('c') => Some(StructuredFormatFragment::ColorNext),
                Some('r') => Some(StructuredFormatFragment::ColorReset),
                _ => None,
            };
            if let Some(control) = control {
                chars.next();
                fragments.push(control);
                continue;
            }
            let mut digits = String::new();
            while chars.peek().is_some_and(char::is_ascii_digit) {
                if let Some(digit) = chars.next() {
                    digits.push(digit);
                }
            }
            if digits.is_empty() {
                return Err(invalid_format(
                    "`%` must be followed by `%n`, `%i`, `%d`, `%c`, `%r`, `%%`, or a one-based item position",
                    literal.span(),
                ));
            }
            let position = digits.parse::<u16>().map_err(|_| {
                invalid_format("an item position must fit in `u16`", literal.span())
            })?;
            if position == 0 {
                return Err(invalid_format(
                    "item positions are one-based and `%0` is invalid",
                    literal.span(),
                ));
            }
            fragments.push(StructuredFormatFragment::Item(position));
        }
        if !literal_text.is_empty() {
            fragments.push(StructuredFormatFragment::Literal(literal_text));
        }
        Ok(Self { literal, fragments })
    }

    /// Builds the readable named-placeholder format used by open constructor
    /// families. Field placeholders are translated to their one-based syntax
    /// item positions; all other text, including spacing, is preserved.
    #[expect(
        clippy::too_many_lines,
        reason = "One ordered format parser preserves placeholder positions and authored spacing."
    )]
    pub(crate) fn parse_named(
        literal: LitStr,
        template: &SyntaxTemplate,
        controls: bool,
    ) -> Result<Self, SyntaxError> {
        let text = literal.value();
        if text.is_empty() {
            return Err(invalid_format(
                "the format must not be empty",
                literal.span(),
            ));
        }
        let characters = text.char_indices().collect::<Vec<_>>();
        let mut cursor = 0_usize;
        let mut literal_text = String::new();
        let mut fragments = Vec::new();
        while cursor < characters.len() {
            let character = characters[cursor].1;
            match character {
                '{' if characters.get(cursor + 1).is_some_and(|next| next.1 == '{') => {
                    literal_text.push('{');
                    cursor += 2;
                }
                '}' if characters.get(cursor + 1).is_some_and(|next| next.1 == '}') => {
                    literal_text.push('}');
                    cursor += 2;
                }
                '{' => {
                    push_format_literal(&mut fragments, &mut literal_text);
                    let start = cursor + 1;
                    let mut end = start;
                    while end < characters.len() && characters[end].1 != '}' {
                        if characters[end].1 == '{' {
                            return Err(invalid_format(
                                "nested `{` is not allowed in a named format placeholder",
                                literal.span(),
                            ));
                        }
                        end += 1;
                    }
                    if end == characters.len() {
                        return Err(invalid_format(
                            "an opening `{` has no closing `}`",
                            literal.span(),
                        ));
                    }
                    let name = characters[start..end]
                        .iter()
                        .map(|(_, value)| value)
                        .collect::<String>();
                    let position = template
                        .items()
                        .iter()
                        .position(|item| matches!(item, SyntaxTemplateItem::Field(field) if field == &name))
                        .ok_or_else(|| {
                            invalid_format(
                                "a named format placeholder must name a syntax field",
                                literal.span(),
                            )
                        })?;
                    let position = u16::try_from(position + 1).map_err(|_| {
                        invalid_format("a format item position exceeds `u16`", literal.span())
                    })?;
                    fragments.push(StructuredFormatFragment::Item(position));
                    cursor = end + 1;
                }
                '}' => {
                    return Err(invalid_format(
                        "an unmatched `}` must be escaped as `}}`",
                        literal.span(),
                    ));
                }
                '%' if controls => {
                    let Some(next) = characters.get(cursor + 1).map(|next| next.1) else {
                        return Err(invalid_format(
                            "a percent sign must introduce `%n`, `%i`, `%d`, `%c`, `%r`, or `%%`",
                            literal.span(),
                        ));
                    };
                    let fragment = match next {
                        '%' => {
                            literal_text.push('%');
                            cursor += 2;
                            continue;
                        }
                        'n' => StructuredFormatFragment::Newline,
                        'i' => StructuredFormatFragment::Indent,
                        'd' => StructuredFormatFragment::Dedent,
                        'c' => StructuredFormatFragment::ColorNext,
                        'r' => StructuredFormatFragment::ColorReset,
                        _ => {
                            return Err(invalid_format(
                                "a percent sign must introduce `%n`, `%i`, `%d`, `%c`, `%r`, or `%%`",
                                literal.span(),
                            ));
                        }
                    };
                    push_format_literal(&mut fragments, &mut literal_text);
                    fragments.push(fragment);
                    cursor += 2;
                }
                other => {
                    literal_text.push(other);
                    cursor += 1;
                }
            }
        }
        push_format_literal(&mut fragments, &mut literal_text);
        if fragments.is_empty() {
            return Err(invalid_format(
                "the format must emit a fragment",
                literal.span(),
            ));
        }
        Ok(Self { literal, fragments })
    }

    /// Returns the original Rust string literal.
    #[must_use]
    pub const fn literal(&self) -> &LitStr {
        &self.literal
    }

    /// Returns ordered typed format fragments.
    #[must_use]
    pub fn fragments(&self) -> &[StructuredFormatFragment] {
        &self.fragments
    }

    /// Refers to the template's terminals by position, as K's own formats do
    /// (`format(%1 %2%3%4 %5)` for `while ({condition}) {body}`).
    ///
    /// Literal runs are matched greedily, in order, against the terminals:
    /// a matched run becomes `Item(position)` and unmatched text stays
    /// literal. An item reference moves the search past its position, so a
    /// later terminal is never matched before an earlier item. The K codes are
    /// still generated here, from the template (decision C5).
    pub(crate) fn number_terminals(&mut self, template: &SyntaxTemplate) {
        let terminals = template
            .items()
            .iter()
            .enumerate()
            .filter_map(|(index, item)| match item {
                SyntaxTemplateItem::Terminal(text) => {
                    Some((u16::try_from(index + 1).ok()?, text.as_str()))
                }
                SyntaxTemplateItem::Field(_) => None,
            })
            .collect::<Vec<_>>();
        let mut next = 0_usize;
        let mut fragments = Vec::with_capacity(self.fragments.len());
        for fragment in std::mem::take(&mut self.fragments) {
            match fragment {
                StructuredFormatFragment::Literal(text) => {
                    let mut literal = String::new();
                    let mut rest = text.as_str();
                    while !rest.is_empty() {
                        if let Some((position, terminal)) = terminals.get(next)
                            && rest.starts_with(terminal)
                        {
                            push_format_literal(&mut fragments, &mut literal);
                            fragments.push(StructuredFormatFragment::Item(*position));
                            rest = &rest[terminal.len()..];
                            next += 1;
                            continue;
                        }
                        let character = rest.chars().next().expect("rest is not empty");
                        literal.push(character);
                        rest = &rest[character.len_utf8()..];
                    }
                    push_format_literal(&mut fragments, &mut literal);
                }
                StructuredFormatFragment::Item(position) => {
                    while terminals
                        .get(next)
                        .is_some_and(|(terminal, _)| *terminal <= position)
                    {
                        next += 1;
                    }
                    fragments.push(StructuredFormatFragment::Item(position));
                }
                control => fragments.push(control),
            }
        }
        self.fragments = fragments;
    }

    /// Returns the number of `%c` controls.
    #[must_use]
    pub fn color_next_count(&self) -> usize {
        self.fragments
            .iter()
            .filter(|fragment| matches!(fragment, StructuredFormatFragment::ColorNext))
            .count()
    }

    /// Whether the format uses `%c` or `%r`.
    #[must_use]
    pub fn uses_colors(&self) -> bool {
        self.fragments.iter().any(|fragment| {
            matches!(
                fragment,
                StructuredFormatFragment::ColorNext | StructuredFormatFragment::ColorReset
            )
        })
    }

    /// Checks all `%N` references against a concrete production item count.
    ///
    /// # Errors
    ///
    /// Rejects a position beyond `item_count`.
    pub fn validate_item_count(&self, item_count: usize) -> Result<(), SyntaxError> {
        if self.fragments.iter().any(|fragment| {
            matches!(fragment, StructuredFormatFragment::Item(position) if usize::from(*position) > item_count)
        }) {
            return Err(invalid_format(
                "an item position exceeds the syntax production length",
                self.literal.span(),
            ));
        }
        Ok(())
    }

    pub(crate) fn provenance(
        &self,
        role: ProvenanceRole,
    ) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let range = TokenRange::for_tokens(&self.literal)?;
        self.fragments
            .iter()
            .enumerate()
            .map(|(ordinal, _)| {
                checked_ordinal(ordinal, role, self.literal.span())
                    .map(|ordinal| ProvenanceAnchor::new(role, ordinal, range))
            })
            .collect()
    }
}

fn push_format_literal(fragments: &mut Vec<StructuredFormatFragment>, literal_text: &mut String) {
    if !literal_text.is_empty() {
        fragments.push(StructuredFormatFragment::Literal(std::mem::take(
            literal_text,
        )));
    }
}

fn invalid_format(reason: &'static str, span: Span) -> SyntaxError {
    SyntaxError::new(SyntaxErrorKind::InvalidFormat { reason }, span)
}

/// The content of one token production: `regex = r".."` or `terminal = ".."`.
#[derive(Clone, Debug)]
pub enum TokenContent {
    /// `regex = r".."`: `syntax S ::= r".." [token]`.
    Regex(LitStr),
    /// `terminal = ".."`: `syntax S ::= ".." [token]`.
    Terminal(LitStr),
}

impl TokenContent {
    /// Returns the authored literal.
    #[must_use]
    pub const fn literal(&self) -> &LitStr {
        match self {
            Self::Regex(literal) | Self::Terminal(literal) => literal,
        }
    }

    /// Returns the provenance role of the literal.
    #[must_use]
    pub const fn role(&self) -> ProvenanceRole {
        match self {
            Self::Regex(_) => ProvenanceRole::TokenRegex,
            Self::Terminal(_) => ProvenanceRole::TokenTerminal,
        }
    }
}

/// Validated arguments of one `#[k::token(regex = r"...", prec = N)]` or
/// `#[k::token(terminal = "...")]` attribute: one K token production.
#[derive(Clone, Debug)]
pub struct TokenAttribute {
    content: TokenContent,
    lexical_precedence: Option<(LitInt, u32)>,
}

impl TokenAttribute {
    /// Returns the production content.
    #[must_use]
    pub const fn content(&self) -> &TokenContent {
        &self.content
    }

    /// Returns the authored regex literal of a regex production.
    #[must_use]
    pub const fn regex(&self) -> Option<&LitStr> {
        match &self.content {
            TokenContent::Regex(literal) => Some(literal),
            TokenContent::Terminal(_) => None,
        }
    }

    /// Returns the authored terminal literal of a terminal production.
    #[must_use]
    pub const fn terminal(&self) -> Option<&LitStr> {
        match &self.content {
            TokenContent::Terminal(literal) => Some(literal),
            TokenContent::Regex(_) => None,
        }
    }

    /// Returns the optional lexical precedence.
    #[must_use]
    pub const fn lexical_precedence(&self) -> Option<u32> {
        match self.lexical_precedence {
            Some((_, value)) => Some(value),
            None => None,
        }
    }

    /// Returns the content anchor and the optional precedence anchor, at
    /// `ordinal`, this attribute's position among the stacked attributes of
    /// its kind (regex or terminal).
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only for a tokenless parsed Rust node.
    pub fn provenance(&self, ordinal: u32) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = vec![ProvenanceAnchor::new(
            self.content.role(),
            ordinal,
            TokenRange::for_tokens(self.content.literal())?,
        )];
        if let Some((literal, _)) = &self.lexical_precedence {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::TokenLexicalPrecedence,
                ordinal,
                TokenRange::for_tokens(literal)?,
            ));
        }
        Ok(anchors)
    }
}

impl KrsSyntax for TokenAttribute {
    /// Parses a token attribute payload from proc-macro tokens.
    ///
    /// # Errors
    ///
    /// The payload must contain exactly one of a nonempty checked `regex`
    /// string or a nonempty single-terminal `terminal` string, and at most
    /// one unsuffixed `u32` `prec` value, which requires `regex`.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        structured(tokens, parse_token_attribute_stream)
    }
}

/// The ordered, nonempty stack of `#[k::token]` attributes on one carrier.
#[derive(Clone, Debug)]
pub struct TokenStack {
    attributes: Vec<TokenAttribute>,
}

impl TokenStack {
    /// Checks a stack of token attributes in source order.
    ///
    /// # Errors
    ///
    /// Rejects an empty stack and two attributes that declare the same
    /// production (the same regex, or the same terminal).
    pub fn new(attributes: Vec<TokenAttribute>) -> Result<Self, SyntaxError> {
        if attributes.is_empty() {
            return Err(invalid_token_attribute(
                "a token carrier needs at least one `#[k::token(..)]` attribute",
                Span::call_site(),
            ));
        }
        let mut seen = BTreeSet::new();
        for attribute in &attributes {
            let literal = attribute.content.literal();
            let identity = (
                matches!(attribute.content, TokenContent::Terminal(_)),
                literal.value(),
            );
            if !seen.insert(identity) {
                return Err(invalid_token_attribute(
                    "this `#[k::token]` attribute repeats an earlier one on the same item; each attribute declares one K token production",
                    literal.span(),
                ));
            }
        }
        Ok(Self { attributes })
    }

    /// Returns the attributes in source order.
    #[must_use]
    pub fn attributes(&self) -> &[TokenAttribute] {
        &self.attributes
    }

    /// Returns each attribute with its ordinal among the attributes of its
    /// kind, in source order.
    #[must_use]
    pub fn ordinals(&self) -> Vec<(u32, &TokenAttribute)> {
        let mut regex = 0_u32;
        let mut terminal = 0_u32;
        self.attributes
            .iter()
            .map(|attribute| {
                let counter = match attribute.content {
                    TokenContent::Regex(_) => &mut regex,
                    TokenContent::Terminal(_) => &mut terminal,
                };
                let ordinal = *counter;
                *counter += 1;
                (ordinal, attribute)
            })
            .collect()
    }

    /// Returns every content and precedence anchor of the stack.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only for a tokenless parsed Rust node.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = Vec::new();
        for (ordinal, attribute) in self.ordinals() {
            anchors.extend(attribute.provenance(ordinal)?);
        }
        Ok(anchors)
    }
}

fn invalid_token_attribute(reason: &'static str, span: Span) -> SyntaxError {
    SyntaxError::new(SyntaxErrorKind::InvalidTokenAttribute { reason }, span)
}

fn parse_token_attribute_stream(input: ParseStream<'_>) -> ParseResult<TokenAttribute> {
    let missing_span = input.span();
    let mut content: Option<TokenContent> = None;
    let mut precedence = None;
    while !input.is_empty() {
        let key: Ident = input.parse()?;
        let name = key.to_string();
        input.parse::<Token![=]>()?;
        match name.as_str() {
            "regex" if matches!(content, Some(TokenContent::Regex(_))) => {
                return Err(duplicate("regex", key.span()));
            }
            "terminal" if matches!(content, Some(TokenContent::Terminal(_))) => {
                return Err(duplicate("terminal", key.span()));
            }
            "regex" | "terminal" if content.is_some() => {
                return Err(ParseError::Structured(invalid_token_attribute(
                    "a token attribute takes exactly one of `regex = r\"..\"` or `terminal = \"..\"`; stack one `#[k::token]` attribute per production",
                    key.span(),
                )));
            }
            "regex" => {
                let literal: LitStr = input.parse()?;
                validate_regex(&literal)?;
                content = Some(TokenContent::Regex(literal));
            }
            "terminal" => {
                let literal: LitStr = input.parse()?;
                validate_token_terminal(&literal)?;
                content = Some(TokenContent::Terminal(literal));
            }
            "prec" if precedence.is_some() => return Err(duplicate("prec", key.span())),
            "prec" => {
                let literal: LitInt = input.parse()?;
                if !literal.suffix().is_empty() {
                    return Err(invalid_argument(
                        "prec",
                        "an unsuffixed nonnegative `u32` integer literal",
                        literal.span(),
                    ));
                }
                let value = literal.base10_parse::<u32>().map_err(|_| {
                    invalid_argument(
                        "prec",
                        "an unsuffixed nonnegative `u32` integer literal",
                        literal.span(),
                    )
                })?;
                precedence = Some((literal, value));
            }
            _ => return Err(unknown(name, key.span())),
        }
        parse_optional_trailing_comma(input)?;
    }
    let Some(content) = content else {
        return Err(ParseError::Structured(invalid_token_attribute(
            "a token attribute takes exactly one of `regex = r\"..\"` or `terminal = \"..\"`",
            missing_span,
        )));
    };
    if let (TokenContent::Terminal(_), Some((literal, _))) = (&content, &precedence) {
        return Err(ParseError::Structured(invalid_token_attribute(
            "`prec` orders regex tokens only; a terminal already outranks every regex token",
            literal.span(),
        )));
    }
    Ok(TokenAttribute {
        content,
        lexical_precedence: precedence,
    })
}

/// A token terminal must be one K terminal, as a syntax template would split it.
fn validate_token_terminal(literal: &LitStr) -> ParseResult<()> {
    let text = literal.value();
    if text.is_empty() {
        return Err(ParseError::Structured(invalid_token_attribute(
            "the token terminal must not be empty",
            literal.span(),
        )));
    }
    let mut items = Vec::new();
    let mut terminal = text.clone();
    push_terminal(&mut items, &mut terminal);
    if !matches!(items.as_slice(), [SyntaxTemplateItem::Terminal(only)] if *only == text) {
        return Err(ParseError::Structured(invalid_token_attribute(
            "a token terminal must be exactly one K terminal: no whitespace, and no mix of word and symbol characters",
            literal.span(),
        )));
    }
    Ok(())
}

pub(crate) fn validate_regex(literal: &LitStr) -> ParseResult<()> {
    let text = literal.value();
    if text.is_empty() {
        return Err(ParseError::Structured(SyntaxError::new(
            SyntaxErrorKind::InvalidTokenRegex {
                reason: "the regex must not be empty",
            },
            literal.span(),
        )));
    }
    let mut escaped = false;
    let mut character_class = false;
    let mut class_has_content = false;
    let mut parentheses = Vec::new();
    for character in text.chars() {
        if escaped {
            escaped = false;
            if character_class {
                class_has_content = true;
            }
            continue;
        }
        if character == '\\' {
            escaped = true;
            continue;
        }
        if character == '"' {
            // K's scanner (flex) reads an unescaped quote as the start of a
            // quoted literal string, and both K and k-rust reject it.
            return Err(invalid_regex(
                "a literal quote is written `\\\"`; an unescaped `\"` starts a quoted string in K's regex syntax",
                literal.span(),
            ));
        }
        if character_class {
            match character {
                ']' if !class_has_content => {
                    return Err(invalid_regex("empty character class", literal.span()));
                }
                ']' => character_class = false,
                _ => class_has_content = true,
            }
            continue;
        }
        match character {
            '[' => {
                character_class = true;
                class_has_content = false;
            }
            ']' => {
                return Err(invalid_regex(
                    "unmatched closing character class",
                    literal.span(),
                ));
            }
            '(' => parentheses.push(character),
            ')' if parentheses.pop().is_none() => {
                return Err(invalid_regex(
                    "unmatched closing parenthesis",
                    literal.span(),
                ));
            }
            _ => {}
        }
    }
    if escaped {
        return Err(invalid_regex("dangling escape", literal.span()));
    }
    if character_class {
        return Err(invalid_regex("unclosed character class", literal.span()));
    }
    if !parentheses.is_empty() {
        return Err(invalid_regex("unclosed parenthesis", literal.span()));
    }
    Ok(())
}

fn invalid_regex(reason: &'static str, span: Span) -> ParseError {
    ParseError::Structured(SyntaxError::new(
        SyntaxErrorKind::InvalidTokenRegex { reason },
        span,
    ))
}

/// The Rust item that carries `#[k::token]` attributes.
#[derive(Clone, Debug)]
pub enum TokenCarrier {
    /// `struct Name(String);`: declares a new closed token sort.
    Struct(ItemStruct),
    /// `type Alias = Sort;`: adds token productions to an existing sort.
    Alias(ItemType),
}

/// Validated token carrier: a nominal token newtype, or a type alias that
/// adds token productions to an existing sort.
#[derive(Clone, Debug)]
pub struct TokenDeclaration {
    carrier: TokenCarrier,
}

impl TokenDeclaration {
    /// Validates the exact token representation `struct Name(String);`.
    ///
    /// # Errors
    ///
    /// Rejects generic, record, unit, multi-field, attributed-field, and
    /// non-`String` representations.
    pub fn from_item(item: ItemStruct) -> Result<Self, SyntaxError> {
        if !item.generics.params.is_empty() || item.generics.where_clause.is_some() {
            return Err(unsupported_token(
                "token newtypes cannot have generics or a where clause",
                item.generics.span(),
            ));
        }
        let Fields::Unnamed(fields) = &item.fields else {
            return Err(unsupported_token(
                "a token must be a one-field tuple newtype",
                item.fields.span(),
            ));
        };
        if fields.unnamed.len() != 1 {
            return Err(unsupported_token(
                "a token must contain exactly one representation field",
                fields.span(),
            ));
        }
        let Some(field) = fields.unnamed.first() else {
            return Err(unsupported_token(
                "a token must contain exactly one representation field",
                fields.span(),
            ));
        };
        if !field.attrs.is_empty() {
            return Err(unsupported_token(
                "the token representation field cannot have attributes",
                field.attrs[0].span(),
            ));
        }
        let Type::Path(representation) = &field.ty else {
            return Err(unsupported_token(
                "the initial token representation must be `String`",
                field.ty.span(),
            ));
        };
        if representation.qself.is_some()
            || !is_plain_path(&representation.path)
            || representation
                .path
                .segments
                .last()
                .is_none_or(|segment| segment.ident != "String")
        {
            return Err(unsupported_token(
                "the initial token representation must be `String`",
                field.ty.span(),
            ));
        }
        Ok(Self {
            carrier: TokenCarrier::Struct(item),
        })
    }

    /// Validates a type-alias carrier `type Alias = path::to::Sort;`.
    ///
    /// # Errors
    ///
    /// Rejects generic aliases and aliases of anything but a plain sort path.
    pub fn from_alias(item: ItemType) -> Result<Self, SyntaxError> {
        if !item.generics.params.is_empty() || item.generics.where_clause.is_some() {
            return Err(unsupported_token(
                "a token type alias cannot have generics or a where clause",
                item.generics.span(),
            ));
        }
        let Type::Path(target) = item.ty.as_ref() else {
            return Err(unsupported_token(
                "a token type alias must name an existing sort by path",
                item.ty.span(),
            ));
        };
        if target.qself.is_some() || !is_plain_path(&target.path) {
            return Err(unsupported_token(
                "a token type alias must name an existing sort by path",
                item.ty.span(),
            ));
        }
        Ok(Self {
            carrier: TokenCarrier::Alias(item),
        })
    }

    /// Returns the carrier item.
    #[must_use]
    pub const fn carrier(&self) -> &TokenCarrier {
        &self.carrier
    }

    /// Returns the struct carrier, or `None` for a type alias.
    #[must_use]
    pub const fn item(&self) -> Option<&ItemStruct> {
        match &self.carrier {
            TokenCarrier::Struct(item) => Some(item),
            TokenCarrier::Alias(_) => None,
        }
    }

    /// Returns the struct or alias name.
    #[must_use]
    pub const fn name(&self) -> &Ident {
        match &self.carrier {
            TokenCarrier::Struct(item) => &item.ident,
            TokenCarrier::Alias(item) => &item.ident,
        }
    }

    /// Returns the outer attributes of the carrier item.
    #[must_use]
    pub fn attributes(&self) -> &[syn::Attribute] {
        match &self.carrier {
            TokenCarrier::Struct(item) => &item.attrs,
            TokenCarrier::Alias(item) => &item.attrs,
        }
    }

    /// Returns the token declaration anchor.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only for a tokenless name.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(vec![ProvenanceAnchor::new(
            ProvenanceRole::TokenDeclaration,
            0,
            TokenRange::for_tokens(self.name())?,
        )])
    }
}

impl KrsSyntax for TokenDeclaration {
    /// Parses a token newtype or type alias from proc-macro tokens.
    ///
    /// # Errors
    ///
    /// Returns Rust syntax, [`TokenDeclaration::from_item`], or
    /// [`TokenDeclaration::from_alias`] errors.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        match syn::parse2::<syn::Item>(tokens)? {
            syn::Item::Struct(item) => Self::from_item(item),
            syn::Item::Type(item) => Self::from_alias(item),
            other => Err(unsupported_token(
                "`#[k::token]` applies to a `struct Name(String);` token sort or a `type Alias = Sort;` alias of an existing sort",
                other.span(),
            )),
        }
    }
}

fn unsupported_token(reason: &'static str, span: Span) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::UnsupportedTokenDeclaration { reason },
        span,
    )
}

/// Checked payload of a syntax-only bracket declaration.
#[derive(Clone, Debug)]
pub struct BracketAttribute {
    template: SyntaxTemplate,
    delimiter_tokens: Option<TokenStream>,
}

impl BracketAttribute {
    /// Returns the checked same-sort bracket template.
    #[must_use]
    pub const fn template(&self) -> &SyntaxTemplate {
        &self.template
    }

    /// Returns bracket declaration/item/value-reference anchors.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only for a tokenless literal.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        if let Some(tokens) = &self.delimiter_tokens {
            let range = TokenRange::for_tokens(tokens)?;
            return Ok(vec![
                ProvenanceAnchor::new(ProvenanceRole::BracketDeclaration, 0, range),
                ProvenanceAnchor::new(ProvenanceRole::BracketSyntaxItem, 0, range),
                ProvenanceAnchor::new(ProvenanceRole::BracketSyntaxItem, 1, range),
                ProvenanceAnchor::new(ProvenanceRole::BracketSyntaxItem, 2, range),
                ProvenanceAnchor::new(ProvenanceRole::BracketValueReference, 0, range),
            ]);
        }
        let mut anchors = vec![ProvenanceAnchor::new(
            ProvenanceRole::BracketDeclaration,
            0,
            TokenRange::for_tokens(self.template.literal())?,
        )];
        anchors.extend(self.template.provenance(
            ProvenanceRole::BracketSyntaxItem,
            ProvenanceRole::BracketValueReference,
        )?);
        Ok(anchors)
    }
}

impl KrsSyntax for BracketAttribute {
    /// Parses a syntax-only bracket payload from proc-macro tokens.
    ///
    /// # Errors
    ///
    /// The payload may use the compatibility template form (`"({value})"`) or the two-delimiter form (`"(", ")"`).
    /// Both forms must produce exactly one same-sort value and at least one terminal.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        let delimiter_tokens = tokens.clone();
        structured(tokens, |input| {
            let first: LitStr = input.parse()?;
            let (literal, delimiter_tokens) = if input.is_empty() {
                (first, None)
            } else {
                input.parse::<Token![,]>()?;
                let close: LitStr = input.parse()?;
                if !input.is_empty() {
                    return Err(ParseError::Syn(
                        input.error("expected exactly two bracket delimiter literals"),
                    ));
                }
                if first.value().is_empty() || close.value().is_empty() {
                    return Err(ParseError::Structured(invalid_template(
                        "bracket delimiters must not be empty",
                        first.span(),
                    )));
                }
                (
                    LitStr::new(
                        &format!("{}{{value}}{}", first.value(), close.value()),
                        first.span(),
                    ),
                    Some(delimiter_tokens.clone()),
                )
            };
            let template = SyntaxTemplate::parse(literal).map_err(ParseError::Structured)?;
            template
                .validate_fields([&Ident::new("value", template.literal().span())])
                .map_err(ParseError::Structured)?;
            if !template
                .items()
                .iter()
                .any(|item| matches!(item, SyntaxTemplateItem::Terminal(_)))
            {
                return Err(ParseError::Structured(invalid_template(
                    "a bracket must contain terminal text around `{value}`",
                    template.literal().span(),
                )));
            }
            Ok(BracketAttribute {
                template,
                delimiter_tokens,
            })
        })
    }
}

/// Strict versus authored-order sequential strictness.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StrictnessKind {
    /// Fields may heat independently.
    Strict,
    /// Fields heat in the authored sequence.
    SeqStrict,
}

/// Checked payload shared by `#[k::strict(...)]` and `#[k::seqstrict(...)]`.
#[derive(Clone, Debug)]
pub struct StrictnessAttribute {
    kind: StrictnessKind,
    using: Option<Ident>,
    fields: Vec<Ident>,
    result_sort: Path,
    readable_result: bool,
    range: TokenRange,
}

impl StrictnessAttribute {
    /// Returns the evaluation strategy.
    #[must_use]
    pub const fn kind(&self) -> StrictnessKind {
        self.kind
    }

    /// Returns the selected context-alias name, when explicitly authored.
    #[must_use]
    pub const fn using(&self) -> Option<&Ident> {
        self.using.as_ref()
    }

    /// Returns selected fields in authored order.
    #[must_use]
    pub fn fields(&self) -> &[Ident] {
        &self.fields
    }

    /// Returns the explicit result-predicate sort path.
    #[must_use]
    pub const fn result_sort(&self) -> &Path {
        &self.result_sort
    }

    /// Whether the result path is a readable sort alias rather than a legacy
    /// marker trait path.
    #[must_use]
    pub const fn has_readable_result(&self) -> bool {
        self.readable_result
    }

    pub(crate) fn parse_readable(
        kind: StrictnessKind,
        tokens: TokenStream,
        marker: &Ident,
        result_sort: Path,
        available_fields: &[Ident],
    ) -> Result<Self, SyntaxError> {
        let (using, fields) = structured(tokens, |input| {
            let mut using = None;
            let mut fields = Vec::new();
            while !input.is_empty() {
                let candidate = input.parse::<Ident>()?;
                if fields.is_empty()
                    && using.is_none()
                    && candidate == "using"
                    && input.peek(Token![=])
                {
                    input.parse::<Token![=]>()?;
                    using = Some(parse_context_alias_reference(input)?);
                } else {
                    fields.push(candidate);
                }
                if input.is_empty() {
                    break;
                }
                input.parse::<Token![,]>()?;
                if input.is_empty() {
                    break;
                }
            }
            Ok::<_, ParseError>((using, fields))
        })?;
        let fields = if fields.is_empty() {
            available_fields.to_vec()
        } else {
            fields
        };
        if fields.is_empty() {
            return Err(SyntaxError::new(
                SyntaxErrorKind::InvalidStrictness {
                    reason: "strictness requires at least one production field",
                },
                marker.span(),
            ));
        }
        let mut seen = BTreeSet::new();
        for field in &fields {
            if !seen.insert(field.to_string()) {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::InvalidStrictness {
                        reason: "the field list must not contain duplicates",
                    },
                    field.span(),
                ));
            }
        }
        let parsed = Self {
            kind,
            using,
            fields,
            result_sort,
            readable_result: true,
            range: TokenRange::for_tokens(marker)?,
        };
        parsed.validate_fields(available_fields)?;
        Ok(parsed)
    }

    /// Parses the fully explicit strictness carrier emitted by layer-2
    /// reference projection.
    ///
    /// Unlike legacy structured strictness, the result path names the
    /// readable sort alias directly. Selected fields are checked immediately
    /// against the enclosing production.
    pub(crate) fn parse_reference(
        kind: StrictnessKind,
        tokens: TokenStream,
        available_fields: &[Ident],
    ) -> Result<Self, SyntaxError> {
        let mut parsed = parse_strictness(tokens, kind)?;
        parsed.validate_fields(available_fields)?;
        parsed.readable_result = true;
        Ok(parsed)
    }

    /// Validates selected names against a nominal constructor declaration.
    ///
    /// # Errors
    ///
    /// Rejects a selected field absent from `fields`.
    pub fn validate_fields<'a>(
        &self,
        fields: impl IntoIterator<Item = &'a Ident>,
    ) -> Result<(), SyntaxError> {
        let available = fields
            .into_iter()
            .map(ToString::to_string)
            .collect::<BTreeSet<_>>();
        for field in &self.fields {
            if !available.contains(&field.to_string()) {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::InvalidStrictness {
                        reason: "strictness names a field absent from the production",
                    },
                    field.span(),
                ));
            }
        }
        Ok(())
    }

    /// Returns declaration, optional context-alias, ordered field-reference,
    /// and result-sort anchors.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only for a tokenless parsed Rust node.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = vec![ProvenanceAnchor::new(
            ProvenanceRole::StrictnessDeclaration,
            0,
            self.range,
        )];
        if let Some(using) = &self.using {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::StrictnessContextAliasReference,
                0,
                TokenRange::for_tokens(using)?,
            ));
        }
        for (ordinal, field) in self.fields.iter().enumerate() {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::StrictnessFieldReference,
                checked_ordinal(
                    ordinal,
                    ProvenanceRole::StrictnessFieldReference,
                    field.span(),
                )?,
                TokenRange::for_tokens(field)?,
            ));
        }
        anchors.push(ProvenanceAnchor::new(
            ProvenanceRole::StrictnessResultSort,
            0,
            TokenRange::for_tokens(&self.result_sort)?,
        ));
        Ok(anchors)
    }
}

/// Parses `#[k::strict([using = alias,] sequence = [...], result = SortPath)]`
/// tokens.
///
/// # Errors
///
/// Rejects missing, empty, repeated, unknown, or malformed arguments.
pub fn parse_strict_attribute(tokens: TokenStream) -> Result<StrictnessAttribute, SyntaxError> {
    parse_strictness(tokens, StrictnessKind::Strict)
}

/// Parses `#[k::seqstrict([using = alias,] sequence = [...], result = SortPath)]`
/// tokens.
///
/// # Errors
///
/// Rejects missing, empty, repeated, unknown, or malformed arguments.
pub fn parse_seqstrict_attribute(tokens: TokenStream) -> Result<StrictnessAttribute, SyntaxError> {
    parse_strictness(tokens, StrictnessKind::SeqStrict)
}

fn parse_strictness(
    tokens: TokenStream,
    kind: StrictnessKind,
) -> Result<StrictnessAttribute, SyntaxError> {
    let complete_range = TokenRange::for_tokens(&tokens).map_err(|_| {
        SyntaxError::new(
            SyntaxErrorKind::MissingArgument { name: "sequence" },
            Span::call_site(),
        )
    })?;
    structured(tokens, move |input| {
        let missing_span = input.span();
        let mut using = None;
        let mut fields = None;
        let mut result_sort = None;
        while !input.is_empty() {
            let key: Ident = input.parse()?;
            let name = key.to_string();
            input.parse::<Token![=]>()?;
            match name.as_str() {
                "using" if using.is_some() => return Err(duplicate("using", key.span())),
                "using" => {
                    using = Some(parse_context_alias_reference(input)?);
                }
                "sequence" if fields.is_some() => return Err(duplicate("sequence", key.span())),
                "sequence" => {
                    let array: syn::ExprArray = input.parse()?;
                    let mut parsed = Vec::with_capacity(array.elems.len());
                    for element in array.elems {
                        let syn::Expr::Path(path) = element else {
                            return Err(invalid_argument(
                                "sequence",
                                "an array of unqualified Rust field identifiers",
                                element.span(),
                            ));
                        };
                        let ident = (path.qself.is_none())
                            .then(|| unqualified_path_ident(&path.path))
                            .flatten();
                        let Some(ident) = ident else {
                            return Err(invalid_argument(
                                "sequence",
                                "an array of unqualified Rust field identifiers",
                                path.span(),
                            ));
                        };
                        parsed.push(ident.clone());
                    }
                    if parsed.is_empty() {
                        return Err(ParseError::Structured(SyntaxError::new(
                            SyntaxErrorKind::InvalidStrictness {
                                reason: "the field sequence must not be empty",
                            },
                            key.span(),
                        )));
                    }
                    let mut seen = BTreeSet::new();
                    for field in &parsed {
                        if !seen.insert(field.to_string()) {
                            return Err(ParseError::Structured(SyntaxError::new(
                                SyntaxErrorKind::InvalidStrictness {
                                    reason: "the field sequence must not contain duplicates",
                                },
                                field.span(),
                            )));
                        }
                    }
                    fields = Some(parsed);
                }
                "result" if result_sort.is_some() => return Err(duplicate("result", key.span())),
                "result" => {
                    let path: Path = input.parse()?;
                    if !is_plain_path(&path) {
                        return Err(invalid_argument(
                            "result",
                            "a plain Rust sort path",
                            path.span(),
                        ));
                    }
                    result_sort = Some(path);
                }
                _ => return Err(unknown(name, key.span())),
            }
            parse_optional_trailing_comma(input)?;
        }
        Ok(StrictnessAttribute {
            kind,
            using,
            fields: fields.ok_or_else(|| missing("sequence", missing_span))?,
            result_sort: result_sort.ok_or_else(|| missing("result", missing_span))?,
            readable_result: false,
            range: complete_range,
        })
    })
}

fn parse_context_alias_reference(input: ParseStream<'_>) -> ParseResult<Ident> {
    let path: Path = input.parse()?;
    let Some(ident) = unqualified_path_ident(&path) else {
        return Err(invalid_argument(
            "using",
            "an unqualified Rust context-alias identifier",
            path.span(),
        ));
    };
    Ok(ident.clone())
}

/// One direct adjacent edge in an authored precedence chain.
#[derive(Clone, Debug)]
pub struct PrecedenceEdge {
    higher: Ident,
    lower: Ident,
}

impl PrecedenceEdge {
    /// Returns the tighter-binding group.
    #[must_use]
    pub const fn higher(&self) -> &Ident {
        &self.higher
    }

    /// Returns the looser-binding group.
    #[must_use]
    pub const fn lower(&self) -> &Ident {
        &self.lower
    }
}

/// One unrelated `a > b > c` precedence chain.
#[derive(Clone, Debug)]
pub struct PrecedenceChain {
    groups: AtLeastTwo<Ident>,
    range: TokenRange,
}

impl PrecedenceChain {
    /// Returns production groups from tightest to loosest.
    #[must_use]
    pub const fn groups(&self) -> &AtLeastTwo<Ident> {
        &self.groups
    }

    /// Returns direct adjacent edges represented by the chain.
    pub fn edges(&self) -> impl Iterator<Item = PrecedenceEdge> + '_ {
        self.groups
            .iter()
            .zip(self.groups.tail())
            .map(|(higher, lower)| PrecedenceEdge {
                higher: higher.clone(),
                lower: lower.clone(),
            })
    }
}

/// Checked item-macro payload for `k::precedence!`.
#[derive(Clone, Debug)]
pub struct PrecedenceDeclaration {
    owner: Option<Ident>,
    chains: Vec<PrecedenceChain>,
    range: TokenRange,
}

impl PrecedenceDeclaration {
    /// Returns the optional constructor-family owner.
    #[must_use]
    pub const fn owner(&self) -> Option<&Ident> {
        self.owner.as_ref()
    }

    /// Returns unrelated chains in source order.
    #[must_use]
    pub fn chains(&self) -> &[PrecedenceChain] {
        &self.chains
    }

    /// Returns declaration, chain, and flattened group-reference anchors.
    ///
    /// # Errors
    ///
    /// Returns an overflow error for more than `u32::MAX` occurrences.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = vec![ProvenanceAnchor::new(
            ProvenanceRole::PrecedenceDeclaration,
            0,
            self.range,
        )];
        let mut group_ordinal = 0_usize;
        for (chain_ordinal, chain) in self.chains.iter().enumerate() {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::PrecedenceChain,
                checked_ordinal(
                    chain_ordinal,
                    ProvenanceRole::PrecedenceChain,
                    chain.range.first(),
                )?,
                chain.range,
            ));
            for group in &chain.groups {
                anchors.push(ProvenanceAnchor::new(
                    ProvenanceRole::PrecedenceGroupReference,
                    checked_ordinal(
                        group_ordinal,
                        ProvenanceRole::PrecedenceGroupReference,
                        group.span(),
                    )?,
                    TokenRange::for_tokens(group)?,
                ));
                group_ordinal += 1;
            }
        }
        Ok(anchors)
    }
}

impl KrsSyntax for PrecedenceDeclaration {
    /// Parses an optional `for Owner;` followed by one or more semicolon-separated precedence chains.
    ///
    /// # Errors
    ///
    /// Every chain must contain at least two identifiers separated by `>`.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        let range = TokenRange::for_tokens(&tokens).map_err(|_| {
            SyntaxError::new(
                SyntaxErrorKind::InvalidGrammarMacro {
                    reason: "precedence must contain at least one chain",
                },
                Span::call_site(),
            )
        })?;
        structured(tokens, move |input| {
            let owner = parse_optional_grammar_owner(input)?;
            if input.is_empty() {
                return Err(invalid_grammar(
                    "precedence must contain at least one chain",
                    owner.as_ref().map_or_else(|| input.span(), Ident::span),
                ));
            }
            let mut chains = Vec::new();
            while !input.is_empty() {
                let first: Ident = input.parse()?;
                if !input.peek(Token![>]) {
                    return Err(invalid_grammar(
                        "a precedence chain must contain at least one `>`",
                        first.span(),
                    ));
                }
                input.parse::<Token![>]>()?;
                let second: Ident = input.parse()?;
                let mut last_span = second.span();
                let mut rest = Vec::new();
                while input.peek(Token![>]) {
                    input.parse::<Token![>]>()?;
                    let group: Ident = input.parse()?;
                    last_span = group.span();
                    rest.push(group);
                }
                let chain_range = TokenRange::new(first.span(), last_span);
                let groups = AtLeastTwo::new(first, second, rest);
                chains.push(PrecedenceChain {
                    groups,
                    range: chain_range,
                });
                if input.is_empty() {
                    break;
                }
                input.parse::<Token![;]>()?;
            }
            Ok(PrecedenceDeclaration {
                owner,
                chains,
                range,
            })
        })
    }
}

/// Typed group associativity in a grammar macro.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum GroupAssociativity {
    /// Left associative.
    Left,
    /// Right associative.
    Right,
    /// Neither side may associate.
    NonAssociative,
}

/// One typed associativity sentence.
#[derive(Clone, Debug)]
pub struct AssociativitySentence {
    associativity: GroupAssociativity,
    groups: Vec<Ident>,
    range: TokenRange,
}

impl AssociativitySentence {
    /// Returns the typed associativity.
    #[must_use]
    pub const fn associativity(&self) -> GroupAssociativity {
        self.associativity
    }

    /// Returns referenced groups in source order.
    #[must_use]
    pub fn groups(&self) -> &[Ident] {
        &self.groups
    }
}

/// Checked item-macro payload for `k::associativity!`.
#[derive(Clone, Debug)]
pub struct AssociativityDeclaration {
    owner: Option<Ident>,
    sentences: Vec<AssociativitySentence>,
    range: TokenRange,
}

impl AssociativityDeclaration {
    /// Returns the optional constructor-family owner.
    #[must_use]
    pub const fn owner(&self) -> Option<&Ident> {
        self.owner.as_ref()
    }

    /// Returns typed sentences in source order.
    #[must_use]
    pub fn sentences(&self) -> &[AssociativitySentence] {
        &self.sentences
    }

    /// Returns declaration, sentence, and flattened group-reference anchors.
    ///
    /// # Errors
    ///
    /// Returns an overflow error for more than `u32::MAX` occurrences.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = vec![ProvenanceAnchor::new(
            ProvenanceRole::AssociativityDeclaration,
            0,
            self.range,
        )];
        let mut group_ordinal = 0_usize;
        for (sentence_ordinal, sentence) in self.sentences.iter().enumerate() {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::AssociativitySentence,
                checked_ordinal(
                    sentence_ordinal,
                    ProvenanceRole::AssociativitySentence,
                    sentence.range.first(),
                )?,
                sentence.range,
            ));
            for group in &sentence.groups {
                anchors.push(ProvenanceAnchor::new(
                    ProvenanceRole::AssociativityGroupReference,
                    checked_ordinal(
                        group_ordinal,
                        ProvenanceRole::AssociativityGroupReference,
                        group.span(),
                    )?,
                    TokenRange::for_tokens(group)?,
                ));
                group_ordinal += 1;
            }
        }
        Ok(anchors)
    }
}

impl KrsSyntax for AssociativityDeclaration {
    /// Parses an optional `for Owner;` followed by semicolon-terminated typed associativity sentences.
    ///
    /// # Errors
    ///
    /// A sentence must start with `left:`, `right:`, or `non_associative:` followed by a nonempty, duplicate-free comma-separated group list.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        let range = TokenRange::for_tokens(&tokens).map_err(|_| {
            SyntaxError::new(
                SyntaxErrorKind::InvalidGrammarMacro {
                    reason: "associativity must contain at least one sentence",
                },
                Span::call_site(),
            )
        })?;
        structured(tokens, move |input| {
            let owner = parse_optional_grammar_owner(input)?;
            if input.is_empty() {
                return Err(invalid_grammar(
                    "associativity must contain at least one sentence",
                    owner.as_ref().map_or_else(|| input.span(), Ident::span),
                ));
            }
            let mut sentences = Vec::new();
            while !input.is_empty() {
                let keyword: Ident = input.parse()?;
                let associativity = match keyword.to_string().as_str() {
                    "left" => GroupAssociativity::Left,
                    "right" => GroupAssociativity::Right,
                    "non_associative" => GroupAssociativity::NonAssociative,
                    _ => {
                        return Err(invalid_grammar(
                            "expected `left`, `right`, or `non_associative`",
                            keyword.span(),
                        ));
                    }
                };
                input.parse::<Token![:]>()?;
                if input.peek(Token![;]) || input.is_empty() {
                    return Err(invalid_grammar(
                        "an associativity sentence must name at least one group",
                        keyword.span(),
                    ));
                }
                let mut groups = Vec::<Ident>::new();
                loop {
                    groups.push(input.parse()?);
                    if !input.peek(Token![,]) {
                        break;
                    }
                    input.parse::<Token![,]>()?;
                    if input.peek(Token![;]) || input.is_empty() {
                        break;
                    }
                }
                let mut seen = BTreeSet::new();
                for group in &groups {
                    if !seen.insert(group.to_string()) {
                        return Err(invalid_grammar(
                            "an associativity sentence must not repeat a group",
                            group.span(),
                        ));
                    }
                }
                let Some(last) = groups.last() else {
                    return Err(invalid_grammar(
                        "an associativity sentence must name at least one group",
                        keyword.span(),
                    ));
                };
                let sentence_range = TokenRange::new(keyword.span(), last.span());
                sentences.push(AssociativitySentence {
                    associativity,
                    groups,
                    range: sentence_range,
                });
                if input.is_empty() {
                    break;
                }
                input.parse::<Token![;]>()?;
            }
            Ok(AssociativityDeclaration {
                owner,
                sentences,
                range,
            })
        })
    }
}

fn invalid_grammar(reason: &'static str, span: Span) -> ParseError {
    ParseError::Structured(SyntaxError::new(
        SyntaxErrorKind::InvalidGrammarMacro { reason },
        span,
    ))
}

fn parse_optional_grammar_owner(input: ParseStream<'_>) -> ParseResult<Option<Ident>> {
    if !input.peek(Token![for]) {
        return Ok(None);
    }
    input.parse::<Token![for]>()?;
    let owner = input.parse()?;
    input.parse::<Token![;]>()?;
    Ok(Some(owner))
}

/// Checked explicit `impl SuperSort for SubSort {}` subsort declaration.
#[derive(Clone, Debug)]
pub struct SubsortDeclaration {
    item: ItemImpl,
    super_sort: Path,
    sub_sort: Path,
}

impl SubsortDeclaration {
    /// Validates an empty, positive, safe, non-generic trait implementation.
    ///
    /// # Errors
    ///
    /// Rejects inherent, negative, unsafe, default, generic, nonempty, and
    /// non-path endpoint forms.
    pub fn from_item(item: ItemImpl) -> Result<Self, SyntaxError> {
        if item.defaultness.is_some() {
            return Err(unsupported_subsort(
                "subsort impls cannot be `default`",
                item.defaultness.span(),
            ));
        }
        if let Some(unsafety) = item.unsafety {
            return Err(unsupported_subsort(
                "subsort impls cannot be `unsafe`",
                unsafety.span,
            ));
        }
        if !item.generics.params.is_empty() || item.generics.where_clause.is_some() {
            return Err(unsupported_subsort(
                "subsort impls cannot have generics or a where clause",
                item.generics.span(),
            ));
        }
        if !item.items.is_empty() {
            return Err(unsupported_subsort(
                "subsort impls must have an empty body",
                item.items[0].span(),
            ));
        }
        let Some((polarity, super_sort, _)) = &item.trait_ else {
            return Err(unsupported_subsort(
                "a subsort declaration must be a trait impl",
                item.impl_token.span,
            ));
        };
        if let Some(negative) = polarity {
            return Err(unsupported_subsort(
                "negative subsort impls are not supported",
                negative.span,
            ));
        }
        if !is_plain_path(super_sort) {
            return Err(unsupported_subsort(
                "the super-sort must be a plain Rust path",
                super_sort.span(),
            ));
        }
        let Type::Path(sub_sort) = &*item.self_ty else {
            return Err(unsupported_subsort(
                "the sub-sort must be a plain Rust path",
                item.self_ty.span(),
            ));
        };
        if sub_sort.qself.is_some() || !is_plain_path(&sub_sort.path) {
            return Err(unsupported_subsort(
                "the sub-sort must be a plain Rust path",
                sub_sort.span(),
            ));
        }
        Ok(Self {
            super_sort: super_sort.clone(),
            sub_sort: sub_sort.path.clone(),
            item,
        })
    }

    /// Returns the original span-preserving impl.
    #[must_use]
    pub const fn item(&self) -> &ItemImpl {
        &self.item
    }

    /// Returns the declared super-sort path.
    #[must_use]
    pub const fn super_sort(&self) -> &Path {
        &self.super_sort
    }

    /// Returns the declared or builtin sub-sort path.
    #[must_use]
    pub const fn sub_sort(&self) -> &Path {
        &self.sub_sort
    }

    /// Returns a stable syntax-level sentence spelling.
    #[must_use]
    pub fn spelling(&self) -> String {
        format!(
            "{} for {}",
            path_text(&self.super_sort),
            path_text(&self.sub_sort)
        )
    }

    /// Returns declaration and exact endpoint anchors.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only for a tokenless parsed Rust node.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(vec![
            ProvenanceAnchor::new(
                ProvenanceRole::SubsortDeclaration,
                0,
                TokenRange::for_tokens(&self.item)?,
            ),
            ProvenanceAnchor::new(
                ProvenanceRole::SubsortSuperSort,
                0,
                TokenRange::for_tokens(&self.super_sort)?,
            ),
            ProvenanceAnchor::new(
                ProvenanceRole::SubsortSubSort,
                0,
                TokenRange::for_tokens(&self.sub_sort)?,
            ),
        ])
    }
}

impl KrsSyntax for SubsortDeclaration {
    /// Parses an explicit subsort impl from proc-macro tokens.
    ///
    /// # Errors
    ///
    /// Returns Rust syntax or [`SubsortDeclaration::from_item`] errors.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        Self::from_item(syn::parse2(tokens)?)
    }
}

fn unsupported_subsort(reason: &'static str, span: Span) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::UnsupportedSubsortDeclaration { reason },
        span,
    )
}

type ParseResult<T> = Result<T, ParseError>;

fn parse_optional_trailing_comma(input: ParseStream<'_>) -> ParseResult<()> {
    if input.is_empty() {
        return Ok(());
    }
    input.parse::<Token![,]>()?;
    Ok(())
}
