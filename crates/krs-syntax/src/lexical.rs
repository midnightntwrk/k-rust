//! Item-macro payloads for `k::lexical!` and `k::layout!` (KF-004).
//!
//! `k::lexical! { Alpha = r"[a-zA-Z]"; }` names a regex fragment, K's
//! `syntax lexical Alpha = r"[a-zA-Z]"`; it adds no syntax, and token,
//! layout, and lexical regexes refer to it as `{Alpha}`.
//! `k::layout! { r"(;[^\n\r]*)", r"([\ \n\r\t])" }` declares what the scanner
//! throws away, K's `syntax #Layout ::= r".." [token]`; declaring any layout
//! replaces K's default layout, so whitespace must be declared too.

use std::collections::BTreeSet;

use proc_macro2::{Span, TokenStream};
use syn::{Attribute, Ident, LitStr, Token};

use crate::grammar::validate_regex;
use crate::parse::{KrsSyntax, ParseError, checked_ordinal, structured};
use crate::{ProvenanceAnchor, ProvenanceRole, SyntaxError, SyntaxErrorKind, TokenRange};

/// One `Name = r"..";` entry of a `k::lexical!` block.
#[derive(Clone, Debug)]
pub struct LexicalEntry {
    attributes: Vec<Attribute>,
    name: Ident,
    regex: LitStr,
    range: TokenRange,
}

impl LexicalEntry {
    /// Returns the entry's outer attributes (doc comments only).
    #[must_use]
    pub fn attributes(&self) -> &[Attribute] {
        &self.attributes
    }

    /// Returns the lexical name.
    #[must_use]
    pub const fn name(&self) -> &Ident {
        &self.name
    }

    /// Returns the regex literal.
    #[must_use]
    pub const fn regex(&self) -> &LitStr {
        &self.regex
    }
}

/// Checked item-macro payload for `k::lexical!`.
#[derive(Clone, Debug)]
pub struct LexicalDeclaration {
    entries: Vec<LexicalEntry>,
}

impl LexicalDeclaration {
    /// Returns the entries in source order.
    #[must_use]
    pub fn entries(&self) -> &[LexicalEntry] {
        &self.entries
    }

    /// Returns one `lexical_declaration` and one `lexical_regex` anchor per
    /// entry, in source order.
    ///
    /// # Errors
    ///
    /// Returns an overflow error for more than `u32::MAX` entries.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = Vec::with_capacity(self.entries.len() * 2);
        for (index, entry) in self.entries.iter().enumerate() {
            let ordinal =
                checked_ordinal(index, ProvenanceRole::LexicalDeclaration, entry.name.span())?;
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::LexicalDeclaration,
                ordinal,
                entry.range,
            ));
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::LexicalRegex,
                ordinal,
                TokenRange::for_tokens(&entry.regex)?,
            ));
        }
        Ok(anchors)
    }
}

impl KrsSyntax for LexicalDeclaration {
    /// Parses one or more `Name = "regex";` entries, each optionally preceded
    /// by doc comments.
    ///
    /// # Errors
    ///
    /// A name must match `[A-Z][A-Za-z0-9]*` and be unique in the block; a
    /// regex must be nonempty and well formed; the block must not be empty.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        structured(tokens, |input| {
            if input.is_empty() {
                return Err(invalid(
                    "`k::lexical!` must declare at least one `Name = r\"..\";` entry",
                    Span::call_site(),
                ));
            }
            let mut entries = Vec::new();
            let mut seen = BTreeSet::new();
            while !input.is_empty() {
                let attributes = input.call(Attribute::parse_outer)?;
                if let Some(attribute) = attributes
                    .iter()
                    .find(|attribute| !attribute.path().is_ident("doc"))
                {
                    return Err(invalid(
                        "a `k::lexical!` entry takes only doc comments",
                        attribute.pound_token.span,
                    ));
                }
                let name: Ident = input.parse()?;
                validate_name(&name)?;
                if !seen.insert(name.to_string()) {
                    return Err(invalid(
                        "a lexical name is declared once in a `k::lexical!` block",
                        name.span(),
                    ));
                }
                input.parse::<Token![=]>()?;
                let regex: LitStr = input.parse()?;
                validate_regex(&regex)?;
                let semicolon = input.parse::<Token![;]>()?;
                let range = TokenRange::new(name.span(), semicolon.span);
                entries.push(LexicalEntry {
                    attributes,
                    name,
                    regex,
                    range,
                });
            }
            Ok::<_, ParseError>(Self { entries })
        })
    }
}

/// Checked item-macro payload for `k::layout!`.
#[derive(Clone, Debug)]
pub struct LayoutDeclaration {
    regexes: Vec<LitStr>,
}

impl LayoutDeclaration {
    /// Returns the layout regexes in source order.
    #[must_use]
    pub fn regexes(&self) -> &[LitStr] {
        &self.regexes
    }

    /// Returns one `layout_regex` anchor per regex, in source order.
    ///
    /// # Errors
    ///
    /// Returns an overflow error for more than `u32::MAX` regexes.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        self.regexes
            .iter()
            .enumerate()
            .map(|(index, regex)| {
                Ok(ProvenanceAnchor::new(
                    ProvenanceRole::LayoutRegex,
                    checked_ordinal(index, ProvenanceRole::LayoutRegex, regex.span())?,
                    TokenRange::for_tokens(regex)?,
                ))
            })
            .collect()
    }
}

impl KrsSyntax for LayoutDeclaration {
    /// Parses a nonempty comma-separated list of regex literals.
    ///
    /// # Errors
    ///
    /// The block must not be empty, and every regex must be nonempty and well
    /// formed.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        structured(tokens, |input| {
            if input.is_empty() {
                return Err(invalid(
                    "`k::layout!` must declare at least one regex; declaring layout replaces K's default whitespace and comments",
                    Span::call_site(),
                ));
            }
            let mut regexes = Vec::new();
            while !input.is_empty() {
                let regex: LitStr = input.parse()?;
                validate_regex(&regex)?;
                regexes.push(regex);
                if input.is_empty() {
                    break;
                }
                input.parse::<Token![,]>()?;
            }
            Ok::<_, ParseError>(Self { regexes })
        })
    }
}

/// The `{Name}` lexical references of a K regex, in source order, without
/// duplicates.
///
/// Escaped braces and braces inside a character class are literal, and a
/// `{n}` or `{n,m}` repetition count is not a reference.
///
/// upstream k-rust/standalone-token-regex (fixed): the pinned `k-rust-regex`
/// crate can replace this hand-written scan.
#[must_use]
pub fn regex_references(regex: &str) -> Vec<String> {
    let mut references = Vec::<String>::new();
    let mut characters = regex.chars();
    let mut character_class = false;
    while let Some(character) = characters.next() {
        match character {
            '\\' => {
                characters.next();
            }
            '[' if !character_class => character_class = true,
            ']' if character_class => character_class = false,
            '{' if !character_class => {
                let mut name = String::new();
                let mut closed = false;
                for next in characters.by_ref() {
                    if next == '}' {
                        closed = true;
                        break;
                    }
                    name.push(next);
                }
                let is_count = !name.is_empty()
                    && name
                        .chars()
                        .all(|character| character.is_ascii_digit() || character == ',');
                if closed && !is_count && !references.contains(&name) {
                    references.push(name);
                }
            }
            _ => {}
        }
    }
    references
}

fn validate_name(name: &Ident) -> Result<(), ParseError> {
    let text = name.to_string();
    let mut characters = text.chars();
    let valid = characters
        .next()
        .is_some_and(|first| first.is_ascii_uppercase())
        && characters.all(|character| character.is_ascii_alphanumeric());
    if valid {
        Ok(())
    } else {
        Err(invalid(
            "a lexical name matches `[A-Z][A-Za-z0-9]*`, the identifiers K accepts in a `{Name}` reference",
            name.span(),
        ))
    }
}

fn invalid(reason: &'static str, span: Span) -> ParseError {
    ParseError::Structured(SyntaxError::new(
        SyntaxErrorKind::InvalidLexicalMacro { reason },
        span,
    ))
}

#[cfg(test)]
mod tests {
    use super::regex_references;

    #[test]
    fn references_skip_escapes_classes_and_counts() {
        assert_eq!(
            regex_references(r"{Alpha}{AlphaNum}*\{Not\}[{]{3}{1,2}{Alpha}"),
            vec!["Alpha".to_owned(), "AlphaNum".to_owned()]
        );
    }
}
