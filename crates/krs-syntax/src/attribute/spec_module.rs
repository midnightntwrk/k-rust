//! `#[k::spec_module(name = "..", imports = [path, ..])]`: author K proof modules (KF-041).
//!
//! ```text
//! #[k::spec_module(name = "IMP-SUM-SPEC", imports = [lemmas])]
//! mod sum_spec {
//!     use super::*;
//!     #[k::claim(all_paths, label = "sum-spec", circularity)]
//!     fn sum_spec(..) -> Machine { .. }
//! }
//! ```
//!
//! The attribute goes on an inline Rust `mod`. Its K name defaults to
//! `<k-namespace>-<UPPER-KEBAB(mod name)>`; `imports` lists Rust paths (`crate`,
//! a dependency crate root, or another spec module), which rustc checks.

use proc_macro2::{Span, TokenStream};
use syn::parse::ParseStream;
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::{Ident, Item, ItemMod, LitStr, Path, Token};

use crate::parse::{KrsSyntax, ParseError, duplicate, structured, unknown};
use crate::{ProvenanceAnchor, ProvenanceRole, SyntaxError, SyntaxErrorKind, TokenRange};

/// The reserved suffix of program-syntax modules (X12).
const PROGRAM_SYNTAX_SUFFIX: &str = "-SYNTAX";

/// Checked payload of `#[k::spec_module(name = "..", imports = [path, ..])]`.
#[derive(Clone, Debug)]
pub struct SpecModuleAttribute {
    name: Option<LitStr>,
    imports: Vec<Path>,
}

impl SpecModuleAttribute {
    /// Returns the explicit K module name, when authored.
    #[must_use]
    pub const fn name(&self) -> Option<&LitStr> {
        self.name.as_ref()
    }

    /// Returns the imported Rust paths, in authored order.
    #[must_use]
    pub fn imports(&self) -> &[Path] {
        &self.imports
    }

    /// Returns the name and import anchors (the declaration anchor belongs to the module item).
    ///
    /// # Errors
    ///
    /// Returns a syntax error when an import path has no tokens.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = Vec::new();
        if let Some(name) = &self.name {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::SpecModuleName,
                0,
                TokenRange::new(name.span(), name.span()),
            ));
        }
        for (ordinal, import) in self.imports.iter().enumerate() {
            let ordinal = u32::try_from(ordinal).map_err(|_| {
                SyntaxError::new(
                    SyntaxErrorKind::TooManyProvenanceOccurrences {
                        role: "spec_module_import",
                    },
                    import.span(),
                )
            })?;
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::SpecModuleImport,
                ordinal,
                TokenRange::for_tokens(import)?,
            ));
        }
        Ok(anchors)
    }
}

impl KrsSyntax for SpecModuleAttribute {
    /// Parses the attribute payload from proc-macro tokens.
    ///
    /// # Errors
    ///
    /// Accepts at most one each of `name = ".."` (a K module name that does
    /// not end in `-SYNTAX`) and `imports = [path, ..]`; rejects every other key.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        structured(tokens, parse_attribute_stream)
    }
}

fn parse_attribute_stream(input: ParseStream<'_>) -> Result<SpecModuleAttribute, ParseError> {
    let mut name = None;
    let mut imports: Option<Vec<Path>> = None;
    while !input.is_empty() {
        let key: Ident = input.parse()?;
        match key.to_string().as_str() {
            "name" if name.is_some() => return Err(duplicate("name", key.span())),
            "name" => {
                input.parse::<Token![=]>()?;
                let literal: LitStr = input.parse()?;
                validate_module_name(&literal.value(), literal.span())?;
                name = Some(literal);
            }
            "imports" if imports.is_some() => return Err(duplicate("imports", key.span())),
            "imports" => {
                input.parse::<Token![=]>()?;
                let paths = parse_import_list(input)?;
                for path in &paths {
                    if let Some(segment) = path
                        .segments
                        .iter()
                        .find(|segment| !segment.arguments.is_none())
                    {
                        return Err(invalid(
                            "a spec-module import is a plain Rust module path without generic arguments",
                            segment.span(),
                        )
                        .into());
                    }
                }
                imports = Some(paths);
            }
            other => return Err(unknown(other.to_owned(), key.span())),
        }
        if input.is_empty() {
            break;
        }
        input.parse::<Token![,]>()?;
    }
    Ok(SpecModuleAttribute {
        name,
        imports: imports.unwrap_or_default(),
    })
}

fn parse_import_list(input: ParseStream<'_>) -> syn::Result<Vec<Path>> {
    let content;
    syn::bracketed!(content in input);
    let paths = Punctuated::<Path, Token![,]>::parse_terminated(&content)?;
    Ok(paths.into_iter().collect())
}

/// Checks a K module name: an uppercase letter, then uppercase letters, digits,
/// and single inner `-`, not ending in the reserved `-SYNTAX` suffix.
///
/// # Errors
///
/// Returns [`SyntaxErrorKind::InvalidSpecModule`] naming the fix.
pub fn validate_spec_module_name(name: &str, span: Span) -> Result<(), SyntaxError> {
    validate_module_name(name, span)
}

fn validate_module_name(name: &str, span: Span) -> Result<(), SyntaxError> {
    let well_formed = name
        .bytes()
        .next()
        .is_some_and(|byte| byte.is_ascii_uppercase())
        && name
            .bytes()
            .all(|byte| byte.is_ascii_uppercase() || byte.is_ascii_digit() || byte == b'-')
        && !name.ends_with('-')
        && !name.contains("--");
    if !well_formed {
        return Err(invalid(
            format!(
                "`{name}` is not a K module name: write uppercase letters, digits, and single `-` separators, starting with a letter"
            ),
            span,
        ));
    }
    if name.ends_with(PROGRAM_SYNTAX_SUFFIX) {
        return Err(invalid(
            format!(
                "`{name}` ends in `{PROGRAM_SYNTAX_SUFFIX}`, which KRS reserves for program-syntax modules; choose another spec-module name"
            ),
            span,
        ));
    }
    Ok(())
}

fn invalid(reason: impl Into<String>, span: Span) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::InvalidSpecModule {
            reason: reason.into(),
        },
        span,
    )
}

/// The inline Rust module a `#[k::spec_module]` attribute annotates.
#[derive(Clone, Debug)]
pub struct SpecModuleItem {
    item: ItemMod,
    items: Vec<Item>,
}

impl SpecModuleItem {
    /// Returns the module item, including its body.
    #[must_use]
    pub const fn item(&self) -> &ItemMod {
        &self.item
    }

    /// Returns the module's name.
    #[must_use]
    pub const fn ident(&self) -> &Ident {
        &self.item.ident
    }

    /// Returns the items of the module body, in authored order.
    #[must_use]
    pub fn items(&self) -> &[Item] {
        &self.items
    }

    /// Returns the declaration anchor: the module name.
    #[must_use]
    pub fn provenance(&self) -> Vec<ProvenanceAnchor> {
        vec![ProvenanceAnchor::new(
            ProvenanceRole::SpecModuleDeclaration,
            0,
            TokenRange::new(self.item.ident.span(), self.item.ident.span()),
        )]
    }
}

impl KrsSyntax for SpecModuleItem {
    /// Parses the annotated item.
    ///
    /// # Errors
    ///
    /// Rejects anything but an inline `mod name { .. }` without generics-like
    /// syntax: a `mod name;` file module, or any other item.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        let item: Item = syn::parse2(tokens)?;
        let Item::Mod(item) = item else {
            return Err(invalid(
                "`#[k::spec_module]` applies to an inline `mod name { .. }`, which holds the spec module's claims, lemmas, and tokens",
                item.span(),
            ));
        };
        Self::from_item(item)
    }
}

impl SpecModuleItem {
    /// Validates an already parsed module item.
    ///
    /// # Errors
    ///
    /// Rejects a `mod name;` file module.
    pub fn from_item(item: ItemMod) -> Result<Self, SyntaxError> {
        let Some((_, items)) = &item.content else {
            return Err(invalid(
                format!(
                    "`#[k::spec_module]` needs the module body inline: write `mod {} {{ .. }}` instead of `mod {};`",
                    item.ident, item.ident
                ),
                item.span(),
            ));
        };
        let items = items.clone();
        Ok(Self { item, items })
    }
}
