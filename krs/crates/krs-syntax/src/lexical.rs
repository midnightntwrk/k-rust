//! Item-macro payloads for `k::lexical!` and `k::layout!` (KF-004).
//!
//! `k::lexical! { Alpha = r"[a-zA-Z]"; }` names a regex fragment, K's
//! `syntax lexical Alpha = r"[a-zA-Z]"`; it adds no syntax, and token,
//! layout, and lexical regexes refer to it as `{Alpha}`.
//! `k::layout! { r"(;[^\n\r]*)", r"([\ \n\r\t])" }` declares what the scanner
//! throws away, K's `syntax #Layout ::= r".." [token]`; declaring any layout
//! replaces K's default layout, so whitespace must be declared too.

use std::collections::BTreeSet;

use krs_ir::ProvenanceKey;
use proc_macro2::{Span, TokenStream};
use syn::{Attribute, Ident, LitStr, Token};

use crate::grammar::validate_regex;
use crate::parse::{KeyAllocator, KrsSyntax, ParseError, first_non_doc_attribute, structured};
use crate::{ProvenanceAnchor, ProvenanceRole, SyntaxError, SyntaxErrorKind, TokenRange};

/// One `Name = r"..";` entry of a `k::lexical!` block.
#[derive(Clone, Debug)]
pub struct LexicalEntry {
    attributes: Vec<Attribute>,
    name: Ident,
    regex: LitStr,
    range: TokenRange,
    key: Option<ProvenanceKey>,
    regex_key: Option<ProvenanceKey>,
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

    /// The key of the entry, from its name to its `;`.
    #[must_use]
    pub const fn key(&self) -> Option<&ProvenanceKey> {
        self.key.as_ref()
    }

    /// The key of the regex literal.
    #[must_use]
    pub const fn regex_key(&self) -> Option<&ProvenanceKey> {
        self.regex_key.as_ref()
    }
}

/// Checked item-macro payload for `k::lexical!`.
#[derive(Clone, Debug)]
pub struct LexicalDeclaration {
    entries: Vec<LexicalEntry>,
    /// The anchors of the block's keying, which [`Self::provenance`] returns.
    anchors: Vec<ProvenanceAnchor>,
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
    /// None: the block was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    /// Keys each entry, then its regex, in source order.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        for entry in &mut self.entries {
            entry.key = Some(keys.key(ProvenanceRole::LexicalDeclaration, entry.range)?);
            entry.regex_key = Some(keys.key(
                ProvenanceRole::LexicalRegex,
                TokenRange::for_tokens(&entry.regex)?,
            )?);
        }
        self.anchors = keys.into_anchors();
        Ok(self)
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
                if let Some(attribute) = first_non_doc_attribute(&attributes) {
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
                    key: None,
                    regex_key: None,
                });
            }
            Ok::<_, ParseError>(
                Self {
                    entries,
                    anchors: Vec::new(),
                }
                .keyed()?,
            )
        })
    }
}

/// Checked item-macro payload for `k::layout!`.
#[derive(Clone, Debug)]
pub struct LayoutDeclaration {
    regexes: Vec<LitStr>,
    regex_keys: Vec<ProvenanceKey>,
    /// The anchors of the block's keying, which [`Self::provenance`] returns.
    anchors: Vec<ProvenanceAnchor>,
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
    /// None: the block was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    /// The keys of the regexes, indexed as [`Self::regexes`].
    #[must_use]
    pub fn regex_keys(&self) -> &[ProvenanceKey] {
        &self.regex_keys
    }

    /// Keys each regex in source order.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        self.regex_keys = self
            .regexes
            .iter()
            .map(|regex| keys.key(ProvenanceRole::LayoutRegex, TokenRange::for_tokens(regex)?))
            .collect::<Result<_, _>>()?;
        self.anchors = keys.into_anchors();
        Ok(self)
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
            Ok::<_, ParseError>(
                Self {
                    regexes,
                    regex_keys: Vec::new(),
                    anchors: Vec::new(),
                }
                .keyed()?,
            )
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

#[cfg(test)]
mod keyed {
    use super::{LayoutDeclaration, LexicalDeclaration};
    use crate::SyntaxError;
    use crate::keyed_nodes::KeyedNodes;

    impl LexicalDeclaration {
        /// Records the keys of each entry and its regex.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            for entry in &self.entries {
                nodes.push(entry.key.as_ref(), entry.range);
                nodes.push_tokens(entry.regex_key.as_ref(), &entry.regex)?;
            }
            Ok(())
        }
    }

    impl LayoutDeclaration {
        /// Records the key of each regex.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            assert!(self.regex_keys.len() <= self.regexes.len());
            for (key, regex) in self.regex_keys.iter().zip(&self.regexes) {
                nodes.push_tokens(Some(key), regex)?;
            }
            Ok(())
        }
    }
}
