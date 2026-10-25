use std::collections::BTreeSet;

use krs_ir::{AtLeastTwo, ProvenanceKey};
use proc_macro2::{Span, TokenStream};
use syn::parse::ParseStream;
use syn::spanned::Spanned;
use syn::{Fields, Ident, ItemImpl, ItemStruct, ItemType, LitInt, LitStr, Path, Token, Type};

use crate::parse::{
    KeyAllocator, KrsSyntax, ParseError, duplicate, first_non_doc_attribute, invalid_argument,
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
    item_keys: Vec<Vec<ProvenanceKey>>,
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

        let mut items = Vec::new();
        for piece in
            scan_placeholders(&text).map_err(|reason| invalid_template(reason, literal.span()))?
        {
            match piece {
                TemplatePiece::Text(mut terminal) => push_terminal(&mut items, &mut terminal),
                TemplatePiece::Field(name) => items.push(SyntaxTemplateItem::Field(name)),
            }
        }
        if items.is_empty() {
            return Err(invalid_template(
                "the template must emit an item",
                literal.span(),
            ));
        }
        Ok(Self {
            literal,
            items,
            item_keys: Vec::new(),
        })
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

    /// Every key the enclosing sentence gave the item at `index` in
    /// [`Self::items`]: its item key, then, for a field, its value
    /// reference's.
    #[must_use]
    pub fn item_keys(&self, index: usize) -> &[ProvenanceKey] {
        self.item_keys.get(index).map_or(&[], Vec::as_slice)
    }

    /// Keys each item, and each field's value reference after its item, at
    /// the template literal.
    pub(crate) fn allocate_keys(
        &mut self,
        keys: &mut KeyAllocator,
        item_role: ProvenanceRole,
        field_role: ProvenanceRole,
    ) -> Result<(), SyntaxError> {
        let range = TokenRange::for_tokens(&self.literal)?;
        self.item_keys = Vec::with_capacity(self.items.len());
        for item in &self.items {
            let mut item_keys = vec![keys.key(item_role, range)?];
            if matches!(item, SyntaxTemplateItem::Field(_)) {
                item_keys.push(keys.key(field_role, range)?);
            }
            self.item_keys.push(item_keys);
        }
        Ok(())
    }
}

/// One piece of a template string: literal text or a `{field}` placeholder.
enum TemplatePiece {
    Text(String),
    Field(String),
}

/// Splits a template into text and named placeholders, with std `format!`
/// escaping: `{{` and `}}` spell literal braces, and a placeholder is one Rust
/// identifier between braces. Shared by syntax and SMT-LIB templates.
fn scan_placeholders(text: &str) -> Result<Vec<TemplatePiece>, &'static str> {
    let chars = text.chars().collect::<Vec<_>>();
    let mut pieces = Vec::new();
    let mut literal = String::new();
    let mut cursor = 0;
    while cursor < chars.len() {
        match chars[cursor] {
            '{' if chars.get(cursor + 1) == Some(&'{') => {
                literal.push('{');
                cursor += 2;
            }
            '}' if chars.get(cursor + 1) == Some(&'}') => {
                literal.push('}');
                cursor += 2;
            }
            '{' => {
                if !literal.is_empty() {
                    pieces.push(TemplatePiece::Text(std::mem::take(&mut literal)));
                }
                let start = cursor + 1;
                let mut end = start;
                while end < chars.len() && chars[end] != '}' {
                    if chars[end] == '{' {
                        return Err("nested `{` is not allowed in a placeholder");
                    }
                    end += 1;
                }
                if end == chars.len() {
                    return Err(
                        "an opening `{` has no closing `}`; did you mean `{{` for a literal opening brace?",
                    );
                }
                let name = chars[start..end].iter().collect::<String>();
                if name.is_empty() || syn::parse_str::<Ident>(&name).is_err() {
                    return Err("a placeholder must contain one Rust field identifier");
                }
                pieces.push(TemplatePiece::Field(name));
                cursor = end + 1;
            }
            '}' => return Err("an unmatched `}` must be escaped as `}}`"),
            other => {
                literal.push(other);
                cursor += 1;
            }
        }
    }
    if !literal.is_empty() {
        pieces.push(TemplatePiece::Text(literal));
    }
    Ok(pieces)
}

/// One checked fragment of a function's `smt_hook` SMT-LIB template.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SmtTemplateFragment {
    /// Literal SMT-LIB text.
    Text(String),
    /// A named field placeholder, without its surrounding braces.
    Field(String),
}

/// A checked `smt_hook` SMT-LIB template (KF-044).
///
/// It is a checked foreign-language template like `#[k::syntax]`: `{field}`
/// placeholders name constructor fields and use std `format!` escaping, and
/// the text is checked to be a balanced S-expression. K's positional `#N`
/// and a `"` are rejected.
#[derive(Clone, Debug)]
pub struct SmtTemplate {
    literal: LitStr,
    fragments: Vec<SmtTemplateFragment>,
    hook_key: Option<ProvenanceKey>,
    placeholder_keys: Vec<ProvenanceKey>,
}

impl SmtTemplate {
    /// Parses and checks one `smt_hook` literal.
    ///
    /// # Errors
    ///
    /// Rejects an empty template, malformed braces or placeholders, a `"`,
    /// and unbalanced parentheses.
    pub fn parse(literal: LitStr) -> Result<Self, SyntaxError> {
        let text = literal.value();
        let error = |reason: String| {
            SyntaxError::new(
                SyntaxErrorKind::InvalidSmtMetadata { reason },
                literal.span(),
            )
        };
        if text.trim().is_empty() {
            return Err(error("an `smt_hook` template must not be empty".to_owned()));
        }
        if text.contains('"') {
            return Err(error(
                "an `smt_hook` template cannot contain `\"`: K's attribute value would end there; use an SMT-LIB term without string literals".to_owned(),
            ));
        }
        let pieces = scan_placeholders(&text)
            .map_err(|reason| error(format!("invalid `smt_hook` template: {reason}")))?;
        let mut depth = 0_usize;
        for piece in &pieces {
            let TemplatePiece::Text(text) = piece else {
                continue;
            };
            for character in text.chars() {
                match character {
                    '(' => depth += 1,
                    ')' => {
                        depth = depth.checked_sub(1).ok_or_else(|| {
                            error("the `smt_hook` template has an unmatched `)`: it must be one balanced S-expression".to_owned())
                        })?;
                    }
                    _ => {}
                }
            }
        }
        if depth != 0 {
            return Err(error(
                "the `smt_hook` template has an unclosed `(`: it must be one balanced S-expression"
                    .to_owned(),
            ));
        }
        let fragments = pieces
            .into_iter()
            .map(|piece| match piece {
                TemplatePiece::Text(text) => SmtTemplateFragment::Text(text),
                TemplatePiece::Field(name) => SmtTemplateFragment::Field(name),
            })
            .collect();
        Ok(Self {
            literal,
            fragments,
            hook_key: None,
            placeholder_keys: Vec::new(),
        })
    }

    /// Returns the original Rust string literal.
    #[must_use]
    pub const fn literal(&self) -> &LitStr {
        &self.literal
    }

    /// The key of the hook, from the function that declares it.
    #[must_use]
    pub const fn hook_key(&self) -> Option<&ProvenanceKey> {
        self.hook_key.as_ref()
    }

    /// The keys of the placeholders, one per field fragment in source order.
    #[must_use]
    pub fn placeholder_keys(&self) -> &[ProvenanceKey] {
        &self.placeholder_keys
    }

    /// Returns the text and placeholder fragments in source order.
    #[must_use]
    pub fn fragments(&self) -> &[SmtTemplateFragment] {
        &self.fragments
    }

    /// Checks every placeholder against the production's fields, and rejects
    /// K's positional `#N` with the `{field}` spelling it stands for.
    ///
    /// A field may occur any number of times, including not at all: the
    /// template is the function's meaning, not its concrete syntax.
    ///
    /// # Errors
    ///
    /// Rejects a placeholder naming no field (with the closest field name)
    /// and a literal `#N`.
    pub fn validate_fields<'a>(
        &self,
        fields: impl IntoIterator<Item = &'a Ident>,
    ) -> Result<(), SyntaxError> {
        let fields = fields
            .into_iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>();
        let error = |reason: String| {
            SyntaxError::new(
                SyntaxErrorKind::InvalidSmtMetadata { reason },
                self.literal.span(),
            )
        };
        for fragment in &self.fragments {
            match fragment {
                SmtTemplateFragment::Field(name) if !fields.contains(name) => {
                    let hint = crate::enum_constructor::closest_variant(name, &fields).map_or_else(
                        || {
                            format!(
                                "; the fields are {}",
                                fields
                                    .iter()
                                    .map(|field| format!("`{{{field}}}`"))
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            )
                        },
                        |closest| format!("; did you mean `{{{closest}}}`?"),
                    );
                    return Err(error(format!(
                        "`smt_hook` placeholder `{{{name}}}` names no field of this function{hint}"
                    )));
                }
                SmtTemplateFragment::Text(text) => {
                    if let Some(position) = positional_placeholder(text) {
                        let hint = position
                            .checked_sub(1)
                            .and_then(|index| fields.get(index))
                            .map_or_else(
                                || "a `{field}` placeholder".to_owned(),
                                |field| format!("`{{{field}}}`"),
                            );
                        return Err(error(format!(
                            "`#{position}` is K's positional placeholder; name the field instead: did you mean {hint}?"
                        )));
                    }
                }
                SmtTemplateFragment::Field(_) => {}
            }
        }
        Ok(())
    }

    /// Keys the hook and each placeholder, at the template literal.
    pub(crate) fn allocate_keys(&mut self, keys: &mut KeyAllocator) -> Result<(), SyntaxError> {
        let range = TokenRange::for_tokens(&self.literal)?;
        self.hook_key = Some(keys.key(ProvenanceRole::FunctionSmtHook, range)?);
        self.placeholder_keys.clear();
        for fragment in &self.fragments {
            if matches!(fragment, SmtTemplateFragment::Field(_)) {
                self.placeholder_keys
                    .push(keys.key(ProvenanceRole::SmtHookPlaceholder, range)?);
            }
        }
        Ok(())
    }
}

/// The `N` of the first `#N` (a `#` followed by a decimal digit) in `text`.
fn positional_placeholder(text: &str) -> Option<usize> {
    let mut rest = text;
    while let Some(index) = rest.find('#') {
        rest = &rest[index + 1..];
        let digits = rest
            .chars()
            .take_while(char::is_ascii_digit)
            .collect::<String>();
        if !digits.is_empty() {
            return Some(digits.parse().unwrap_or(usize::MAX));
        }
    }
    None
}

pub(crate) fn push_terminal(items: &mut Vec<SyntaxTemplateItem>, terminal: &mut String) {
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
    fragment_keys: Vec<ProvenanceKey>,
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
        Ok(Self {
            literal,
            fragments,
            fragment_keys: Vec::new(),
        })
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
        Ok(Self {
            literal,
            fragments,
            fragment_keys: Vec::new(),
        })
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

    /// The keys of the fragments, indexed as the fragments, from the
    /// production that declares the format.
    #[must_use]
    pub fn fragment_keys(&self) -> &[ProvenanceKey] {
        &self.fragment_keys
    }

    /// Keys each fragment, at the format literal.
    pub(crate) fn allocate_keys(
        &mut self,
        keys: &mut KeyAllocator,
        role: ProvenanceRole,
    ) -> Result<(), SyntaxError> {
        let range = TokenRange::for_tokens(&self.literal)?;
        self.fragment_keys = self
            .fragments
            .iter()
            .map(|_| keys.key(role, range))
            .collect::<Result<_, _>>()?;
        Ok(())
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
    content_key: Option<ProvenanceKey>,
    precedence_key: Option<ProvenanceKey>,
    /// The anchors of the attribute's standalone keying, which
    /// [`Self::provenance`] returns.
    anchors: Vec<ProvenanceAnchor>,
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

    /// Returns the content anchor and the optional precedence anchor of this
    /// attribute alone, the first of its kind.
    ///
    /// # Errors
    ///
    /// None: the attribute was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    /// The key of the regex or terminal literal, from the attribute alone or
    /// from its stack.
    #[must_use]
    pub const fn content_key(&self) -> Option<&ProvenanceKey> {
        self.content_key.as_ref()
    }

    /// The key of the `prec` literal, numbered as the regex is.
    #[must_use]
    pub const fn precedence_key(&self) -> Option<&ProvenanceKey> {
        self.precedence_key.as_ref()
    }

    /// Keys the attribute as a sentence of its own.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        self.allocate_keys(&mut keys)?;
        self.anchors = keys.into_anchors();
        Ok(self)
    }

    /// Keys the content, as the next of its kind, and its lexical
    /// precedence, which is numbered as its regex is.
    pub(crate) fn allocate_keys(&mut self, keys: &mut KeyAllocator) -> Result<(), SyntaxError> {
        let content = keys.key(
            self.content.role(),
            TokenRange::for_tokens(self.content.literal())?,
        )?;
        self.precedence_key = match &self.lexical_precedence {
            Some((literal, _)) => Some(keys.paired(
                ProvenanceRole::TokenLexicalPrecedence,
                &content,
                TokenRange::for_tokens(literal)?,
            )),
            None => None,
        };
        self.content_key = Some(content);
        Ok(())
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
    /// The anchors of the stack's keying, which [`Self::provenance`]
    /// returns.
    anchors: Vec<ProvenanceAnchor>,
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
        Self {
            attributes,
            anchors: Vec::new(),
        }
        .keyed()
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
    /// None: the stack was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    /// Keys every attribute of the stack again, as one sentence: each
    /// content role numbers its own kind, regexes and terminals apart, as
    /// [`Self::ordinals`] does.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        for attribute in &mut self.attributes {
            attribute.allocate_keys(&mut keys)?;
        }
        self.anchors = keys.into_anchors();
        Ok(self)
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
        content_key: None,
        precedence_key: None,
        anchors: Vec::new(),
    }
    .keyed()?)
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

// upstream k-rust/standalone-token-regex (fixed): the pinned `k-rust-regex` crate
// can replace this hand-written scan.
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
    name_key: Option<ProvenanceKey>,
    sort_key: Option<ProvenanceKey>,
    /// The anchors of the declaration's keying, which [`Self::provenance`]
    /// returns.
    anchors: Vec<ProvenanceAnchor>,
    /// The anchors of a struct carrier's sort declaration.
    sort_anchors: Vec<ProvenanceAnchor>,
}

impl TokenDeclaration {
    /// Validates the exact token representation `struct Name(String);`.
    ///
    /// # Errors
    ///
    /// Rejects generic, record, unit, and multi-field representations, a
    /// field attribute other than a doc comment, and non-`String`
    /// representations.
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
        if let Some(attribute) = first_non_doc_attribute(&field.attrs) {
            return Err(unsupported_token(
                "the token representation field takes only doc comments",
                attribute.span(),
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
        Self {
            carrier: TokenCarrier::Struct(item),
            name_key: None,
            sort_key: None,
            anchors: Vec::new(),
            sort_anchors: Vec::new(),
        }
        .keyed()
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
        Self {
            carrier: TokenCarrier::Alias(item),
            name_key: None,
            sort_key: None,
            anchors: Vec::new(),
            sort_anchors: Vec::new(),
        }
        .keyed()
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
    /// None: the declaration was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    /// The key of the carrier's name.
    #[must_use]
    pub const fn name_key(&self) -> Option<&ProvenanceKey> {
        self.name_key.as_ref()
    }

    /// The key of a struct carrier's name as the declaration of the token
    /// sort it introduces.
    #[must_use]
    pub const fn sort_key(&self) -> Option<&ProvenanceKey> {
        self.sort_key.as_ref()
    }

    /// Returns the anchors of the token sort a struct carrier declares: its
    /// name. A type alias adds productions to an existing sort and declares
    /// none, so it has no such anchors.
    ///
    /// # Errors
    ///
    /// None: the declaration was keyed when it was parsed.
    pub fn sort_provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.sort_anchors.clone())
    }

    /// Keys the carrier's name, as a sentence of its own, and a struct
    /// carrier's name as the declaration of its sort, another.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        let name = TokenRange::for_tokens(self.name())?;
        let mut keys = KeyAllocator::default();
        self.name_key = Some(keys.key(ProvenanceRole::TokenDeclaration, name)?);
        self.anchors = keys.into_anchors();
        if let TokenCarrier::Struct(_) = &self.carrier {
            let mut keys = KeyAllocator::default();
            self.sort_key = Some(keys.key(ProvenanceRole::SortDeclaration, name)?);
            self.sort_anchors = keys.into_anchors();
        }
        Ok(self)
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
    key: Option<ProvenanceKey>,
    delimiter_keys: Vec<ProvenanceKey>,
    /// The anchors of the bracket's keying, which [`Self::provenance`]
    /// returns.
    anchors: Vec<ProvenanceAnchor>,
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
    /// None: the bracket was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    /// The key of the bracket declaration.
    #[must_use]
    pub const fn key(&self) -> Option<&ProvenanceKey> {
        self.key.as_ref()
    }

    /// The keys of a two-delimiter bracket's items, the two delimiters and
    /// the value between them, then of its value reference, all at the
    /// pair; empty for a template bracket, whose template holds its item
    /// keys.
    #[must_use]
    pub fn delimiter_keys(&self) -> &[ProvenanceKey] {
        &self.delimiter_keys
    }

    /// Keys the bracket as a sentence of its own: the declaration, then the
    /// template's items and value reference.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        if let Some(tokens) = &self.delimiter_tokens {
            // The two delimiters and the value between them, all at the pair.
            let range = TokenRange::for_tokens(tokens)?;
            self.key = Some(keys.key(ProvenanceRole::BracketDeclaration, range)?);
            for _ in 0..3 {
                self.delimiter_keys
                    .push(keys.key(ProvenanceRole::BracketSyntaxItem, range)?);
            }
            self.delimiter_keys
                .push(keys.key(ProvenanceRole::BracketValueReference, range)?);
        } else {
            self.key = Some(keys.key(
                ProvenanceRole::BracketDeclaration,
                TokenRange::for_tokens(self.template.literal())?,
            )?);
            self.template.allocate_keys(
                &mut keys,
                ProvenanceRole::BracketSyntaxItem,
                ProvenanceRole::BracketValueReference,
            )?;
        }
        self.anchors = keys.into_anchors();
        Ok(self)
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
        let tokens = crate::parse::strip_trailing_comma(tokens);
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
                key: None,
                delimiter_keys: Vec::new(),
                anchors: Vec::new(),
            }
            .keyed()?)
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
    range: TokenRange,
    key: Option<ProvenanceKey>,
    using_key: Option<ProvenanceKey>,
    field_keys: Vec<ProvenanceKey>,
    result_sort_key: Option<ProvenanceKey>,
    /// The anchors of the attribute's standalone keying, which
    /// [`Self::provenance`] returns.
    anchors: Vec<ProvenanceAnchor>,
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

    /// Returns the explicit result-predicate sort path, a sort's alias such
    /// as `k::KResult`.
    #[must_use]
    pub const fn result_sort(&self) -> &Path {
        &self.result_sort
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
        let parsed = Self::keyed(
            kind,
            using,
            fields,
            result_sort,
            TokenRange::for_tokens(marker)?,
        )?;
        parsed.validate_fields(available_fields)?;
        Ok(parsed)
    }

    /// Parses the fully explicit strictness carrier emitted by layer-2
    /// reference projection.
    ///
    /// Selected fields are checked immediately against the enclosing
    /// production.
    pub(crate) fn parse_reference(
        kind: StrictnessKind,
        tokens: TokenStream,
        available_fields: &[Ident],
    ) -> Result<Self, SyntaxError> {
        let parsed = parse_strictness(tokens, kind)?;
        parsed.validate_fields(available_fields)?;
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
    /// None: the attribute was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    /// The key of the whole attribute.
    #[must_use]
    pub const fn key(&self) -> Option<&ProvenanceKey> {
        self.key.as_ref()
    }

    /// The key of the `using` context-alias name, when authored.
    #[must_use]
    pub const fn using_key(&self) -> Option<&ProvenanceKey> {
        self.using_key.as_ref()
    }

    /// The keys of the field references, indexed as [`Self::fields`].
    #[must_use]
    pub fn field_keys(&self) -> &[ProvenanceKey] {
        &self.field_keys
    }

    /// The key of the result sort.
    #[must_use]
    pub const fn result_sort_key(&self) -> Option<&ProvenanceKey> {
        self.result_sort_key.as_ref()
    }

    /// An attribute keyed as a sentence of its own.
    fn keyed(
        kind: StrictnessKind,
        using: Option<Ident>,
        fields: Vec<Ident>,
        result_sort: Path,
        range: TokenRange,
    ) -> Result<Self, SyntaxError> {
        let mut attribute = Self {
            kind,
            using,
            fields,
            result_sort,
            range,
            key: None,
            using_key: None,
            field_keys: Vec::new(),
            result_sort_key: None,
            anchors: Vec::new(),
        };
        let mut keys = KeyAllocator::default();
        attribute.allocate_keys(&mut keys)?;
        attribute.anchors = keys.into_anchors();
        Ok(attribute)
    }

    /// Keys the declaration, the optional context alias, each field
    /// reference, then the result sort.
    pub(crate) fn allocate_keys(&mut self, keys: &mut KeyAllocator) -> Result<(), SyntaxError> {
        self.key = Some(keys.key(ProvenanceRole::StrictnessDeclaration, self.range)?);
        self.using_key = match &self.using {
            Some(using) => Some(keys.key(
                ProvenanceRole::StrictnessContextAliasReference,
                TokenRange::for_tokens(using)?,
            )?),
            None => None,
        };
        self.field_keys = self
            .fields
            .iter()
            .map(|field| {
                keys.key(
                    ProvenanceRole::StrictnessFieldReference,
                    TokenRange::for_tokens(field)?,
                )
            })
            .collect::<Result<_, _>>()?;
        self.result_sort_key = Some(keys.key(
            ProvenanceRole::StrictnessResultSort,
            TokenRange::for_tokens(&self.result_sort)?,
        )?);
        Ok(())
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
        Ok(StrictnessAttribute::keyed(
            kind,
            using,
            fields.ok_or_else(|| missing("sequence", missing_span))?,
            result_sort.ok_or_else(|| missing("result", missing_span))?,
            complete_range,
        )?)
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
    key: Option<ProvenanceKey>,
    group_keys: Vec<ProvenanceKey>,
}

impl PrecedenceChain {
    /// Returns the chain's first and last authored leaves.
    #[must_use]
    pub const fn range(&self) -> TokenRange {
        self.range
    }

    /// Returns production groups from tightest to loosest.
    #[must_use]
    pub const fn groups(&self) -> &AtLeastTwo<Ident> {
        &self.groups
    }

    /// The key of the chain.
    #[must_use]
    pub const fn key(&self) -> Option<&ProvenanceKey> {
        self.key.as_ref()
    }

    /// The keys of the group references, indexed as [`Self::groups`].
    #[must_use]
    pub fn group_keys(&self) -> &[ProvenanceKey] {
        &self.group_keys
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
    key: Option<ProvenanceKey>,
    /// The anchors of the declaration's keying, which [`Self::provenance`]
    /// returns.
    anchors: Vec<ProvenanceAnchor>,
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
    /// None: the declaration was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    /// The key of the whole declaration.
    #[must_use]
    pub const fn key(&self) -> Option<&ProvenanceKey> {
        self.key.as_ref()
    }

    /// Keys the declaration, then each chain and its group references; the
    /// group references are numbered across the chains.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        self.key = Some(keys.key(ProvenanceRole::PrecedenceDeclaration, self.range)?);
        for chain in &mut self.chains {
            chain.key = Some(keys.key(ProvenanceRole::PrecedenceChain, chain.range)?);
            chain.group_keys = chain
                .groups
                .iter()
                .map(|group| {
                    keys.key(
                        ProvenanceRole::PrecedenceGroupReference,
                        TokenRange::for_tokens(group)?,
                    )
                })
                .collect::<Result<_, _>>()?;
        }
        self.anchors = keys.into_anchors();
        Ok(self)
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
                    key: None,
                    group_keys: Vec::new(),
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
                key: None,
                anchors: Vec::new(),
            }
            .keyed()?)
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
    key: Option<ProvenanceKey>,
    group_keys: Vec<ProvenanceKey>,
}

impl AssociativitySentence {
    /// Returns the sentence's first and last authored leaves.
    #[must_use]
    pub const fn range(&self) -> TokenRange {
        self.range
    }

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

    /// The key of the sentence.
    #[must_use]
    pub const fn key(&self) -> Option<&ProvenanceKey> {
        self.key.as_ref()
    }

    /// The keys of the group references, indexed as [`Self::groups`].
    #[must_use]
    pub fn group_keys(&self) -> &[ProvenanceKey] {
        &self.group_keys
    }
}

/// Checked item-macro payload for `k::associativity!`.
#[derive(Clone, Debug)]
pub struct AssociativityDeclaration {
    owner: Option<Ident>,
    sentences: Vec<AssociativitySentence>,
    range: TokenRange,
    key: Option<ProvenanceKey>,
    /// The anchors of the declaration's keying, which [`Self::provenance`]
    /// returns.
    anchors: Vec<ProvenanceAnchor>,
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
    /// None: the declaration was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    /// The key of the whole declaration.
    #[must_use]
    pub const fn key(&self) -> Option<&ProvenanceKey> {
        self.key.as_ref()
    }

    /// Keys the declaration, then each sentence and its group references;
    /// the group references are numbered across the sentences.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        self.key = Some(keys.key(ProvenanceRole::AssociativityDeclaration, self.range)?);
        for sentence in &mut self.sentences {
            sentence.key = Some(keys.key(ProvenanceRole::AssociativitySentence, sentence.range)?);
            sentence.group_keys = sentence
                .groups
                .iter()
                .map(|group| {
                    keys.key(
                        ProvenanceRole::AssociativityGroupReference,
                        TokenRange::for_tokens(group)?,
                    )
                })
                .collect::<Result<_, _>>()?;
        }
        self.anchors = keys.into_anchors();
        Ok(self)
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
                    key: None,
                    group_keys: Vec::new(),
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
                key: None,
                anchors: Vec::new(),
            }
            .keyed()?)
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
    key: Option<ProvenanceKey>,
    sub_sort_key: Option<ProvenanceKey>,
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
        Self {
            super_sort: super_sort.clone(),
            sub_sort: sub_sort.path.clone(),
            item,
            key: None,
            sub_sort_key: None,
        }
        .keyed()
    }

    /// Keys the impl and its sub-sort, the parts of the subsort's descriptor
    /// the impl holds; the supersort is the alias of the `#[k::subsort]`
    /// attribute, which [`Self::provenance`] takes. Each is the first of its
    /// role in the descriptor.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        self.key = Some(keys.key(
            ProvenanceRole::SubsortDeclaration,
            TokenRange::for_tokens(&self.item)?,
        )?);
        self.sub_sort_key = Some(keys.key(
            ProvenanceRole::SubsortSubSort,
            TokenRange::for_tokens(&self.sub_sort)?,
        )?);
        Ok(self)
    }

    /// The key of the impl, the subsort declaration.
    #[must_use]
    pub const fn key(&self) -> Option<&ProvenanceKey> {
        self.key.as_ref()
    }

    /// The key of the sub-sort path.
    #[must_use]
    pub const fn sub_sort_key(&self) -> Option<&ProvenanceKey> {
        self.sub_sort_key.as_ref()
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

    /// The error for a `#[k::subsort]` impl without `sort = ..`: the
    /// supersort is named by its alias, and the impl populates the alias's
    /// marker trait (B2), as in `#[k::subsort(sort = Value)] impl ValueSort
    /// for Int {}`.
    #[must_use]
    pub fn unaliased_error(&self) -> SyntaxError {
        let marker = path_text(&self.super_sort);
        let (alias, marker) = match marker.strip_suffix("Sort") {
            Some(alias) if !alias.is_empty() && !alias.ends_with("::") => {
                (alias.to_owned(), marker.clone())
            }
            _ => (marker.clone(), format!("{marker}Sort")),
        };
        SyntaxError::new(
            SyntaxErrorKind::UnaliasedSubsort {
                reason: format!(
                    "`#[k::subsort]` names the supersort's alias and implements its marker trait: write `#[k::subsort(sort = {alias})] impl {marker} for {} {{}}`",
                    path_text(&self.sub_sort)
                ),
            },
            self.super_sort.span(),
        )
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

    /// Returns declaration and exact endpoint anchors; the supersort is the
    /// alias `attribute` names.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only for a tokenless parsed Rust node.
    pub fn provenance(
        &self,
        attribute: &crate::SubsortAttribute,
    ) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut keys = KeyAllocator::default();
        keys.key(
            ProvenanceRole::SubsortDeclaration,
            TokenRange::for_tokens(&self.item)?,
        )?;
        keys.key(
            ProvenanceRole::SubsortSuperSort,
            TokenRange::for_tokens(attribute.sort())?,
        )?;
        keys.key(
            ProvenanceRole::SubsortSubSort,
            TokenRange::for_tokens(&self.sub_sort)?,
        )?;
        Ok(keys.into_anchors())
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

#[cfg(test)]
mod keyed {
    use super::{
        AssociativityDeclaration, BracketAttribute, PrecedenceDeclaration, SmtTemplate,
        SmtTemplateFragment, StrictnessAttribute, StructuredFormat, SubsortDeclaration,
        SyntaxTemplate, SyntaxTemplateItem, TokenAttribute, TokenCarrier, TokenDeclaration,
        TokenStack,
    };
    use crate::keyed_nodes::KeyedNodes;
    use crate::{SyntaxError, TokenRange};

    impl SyntaxTemplate {
        /// Records the keys of each item, and of each field's value
        /// reference, at the template literal.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            assert!(self.item_keys.len() <= self.items.len());
            let range = TokenRange::for_tokens(&self.literal)?;
            for (item, keys) in self.items.iter().zip(&self.item_keys) {
                let expected = 1 + usize::from(matches!(item, SyntaxTemplateItem::Field(_)));
                assert_eq!(keys.len(), expected, "an item's keys are its own");
                nodes.push_all(keys, range);
            }
            Ok(())
        }
    }

    impl SmtTemplate {
        /// Records the keys of the hook and of each placeholder, at the
        /// template literal.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            let range = TokenRange::for_tokens(&self.literal)?;
            nodes.push(self.hook_key.as_ref(), range);
            let placeholders = self
                .fragments
                .iter()
                .filter(|fragment| matches!(fragment, SmtTemplateFragment::Field(_)))
                .count();
            assert!(self.placeholder_keys.len() <= placeholders);
            nodes.push_all(&self.placeholder_keys, range);
            Ok(())
        }
    }

    impl StructuredFormat {
        /// Records the keys of the fragments, at the format literal.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            assert!(self.fragment_keys.len() <= self.fragments.len());
            nodes.push_all(&self.fragment_keys, TokenRange::for_tokens(&self.literal)?);
            Ok(())
        }
    }

    impl TokenAttribute {
        /// Records the keys of the content literal and of its lexical
        /// precedence.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            nodes.push_tokens(self.content_key.as_ref(), self.content.literal())?;
            if let Some((literal, _)) = &self.lexical_precedence {
                nodes.push_tokens(self.precedence_key.as_ref(), literal)?;
            }
            Ok(())
        }
    }

    impl TokenStack {
        /// Records the keys of each attribute of the stack.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            for attribute in &self.attributes {
                attribute.keyed_nodes(nodes)?;
            }
            Ok(())
        }
    }

    impl TokenDeclaration {
        /// Records the key of the carrier's name as the token declaration.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            nodes.push_tokens(self.name_key.as_ref(), self.name())
        }

        /// Records the key of a token struct's name as its sort's
        /// declaration.
        pub(crate) fn keyed_sort_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            if let TokenCarrier::Struct(_) = &self.carrier {
                nodes.push_tokens(self.sort_key.as_ref(), self.name())?;
            } else {
                assert!(self.sort_key.is_none(), "an alias declares no sort");
            }
            Ok(())
        }
    }

    impl BracketAttribute {
        /// Records the keys of the bracket and of its delimiters and value,
        /// all at the delimiter pair, or of its template.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            if let Some(tokens) = &self.delimiter_tokens {
                let range = TokenRange::for_tokens(tokens)?;
                nodes.push(self.key.as_ref(), range);
                assert!(self.delimiter_keys.len() <= 4);
                nodes.push_all(&self.delimiter_keys, range);
            } else {
                nodes.push_tokens(self.key.as_ref(), self.template.literal())?;
                assert!(self.delimiter_keys.is_empty());
                self.template.keyed_nodes(nodes)?;
            }
            Ok(())
        }
    }

    impl StrictnessAttribute {
        /// Records the keys of the declaration, the context alias, each
        /// field reference and the result sort.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            nodes.push(self.key.as_ref(), self.range);
            if let Some(using) = &self.using {
                nodes.push_tokens(self.using_key.as_ref(), using)?;
            }
            assert!(self.field_keys.len() <= self.fields.len());
            for (key, field) in self.field_keys.iter().zip(&self.fields) {
                nodes.push_tokens(Some(key), field)?;
            }
            nodes.push_tokens(self.result_sort_key.as_ref(), &self.result_sort)
        }
    }

    impl PrecedenceDeclaration {
        /// Records the keys of the declaration, then of each chain and its
        /// group references.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            nodes.push(self.key.as_ref(), self.range);
            for chain in &self.chains {
                nodes.push(chain.key.as_ref(), chain.range);
                assert!(chain.group_keys.len() <= chain.groups.iter().count());
                for (key, group) in chain.group_keys.iter().zip(chain.groups.iter()) {
                    nodes.push_tokens(Some(key), group)?;
                }
            }
            Ok(())
        }
    }

    impl AssociativityDeclaration {
        /// Records the keys of the declaration, then of each sentence and
        /// its group references.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            nodes.push(self.key.as_ref(), self.range);
            for sentence in &self.sentences {
                nodes.push(sentence.key.as_ref(), sentence.range);
                assert!(sentence.group_keys.len() <= sentence.groups.len());
                for (key, group) in sentence.group_keys.iter().zip(&sentence.groups) {
                    nodes.push_tokens(Some(key), group)?;
                }
            }
            Ok(())
        }
    }

    impl SubsortDeclaration {
        /// Records the keys of the impl and of its sub-sort.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            nodes.push_tokens(self.key.as_ref(), &self.item)?;
            nodes.push_tokens(self.sub_sort_key.as_ref(), &self.sub_sort)
        }
    }
}
