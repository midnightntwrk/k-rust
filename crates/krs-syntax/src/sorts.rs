use proc_macro2::TokenStream;
use syn::parse::{Parse, ParseStream};
use syn::spanned::Spanned;
use syn::{Attribute, Ident, Path, Token};

use crate::parse::checked_ordinal;
use crate::{
    BracketAttribute, ProvenanceAnchor, ProvenanceRole, SyntaxError, TokenRange,
    parse_bracket_attribute,
};

/// One declaration or membership sentence in `k::sorts!`.
#[derive(Clone, Debug)]
pub enum SortsEntry {
    /// Declares an open object-language sort and its direct parents.
    Sort(SortsSort),
    /// Declares one or more concrete members of an existing sort.
    Membership(SortsMembership),
}

/// One terse sort declaration such as `Value: Expr + KResult;`.
#[derive(Clone, Debug)]
pub struct SortsSort {
    name: Ident,
    parents: Vec<Path>,
    brackets: Vec<BracketAttribute>,
}

impl SortsSort {
    /// Returns the authored sort name.
    #[must_use]
    pub const fn name(&self) -> &Ident {
        &self.name
    }

    /// Returns direct parent-sort paths in authored order.
    #[must_use]
    pub fn parents(&self) -> &[Path] {
        &self.parents
    }

    /// Returns syntax-only bracket declarations attached to this sort.
    #[must_use]
    pub fn brackets(&self) -> &[BracketAttribute] {
        &self.brackets
    }

    /// Returns the declaration name and parent-path anchors.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if a parsed node emits no token leaves.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = vec![ProvenanceAnchor::new(
            ProvenanceRole::SortDeclaration,
            0,
            TokenRange::for_tokens(&self.name)?,
        )];
        for (ordinal, parent) in self.parents.iter().enumerate() {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::SortParent,
                checked_ordinal(ordinal, ProvenanceRole::SortParent, parent.span())?,
                TokenRange::for_tokens(parent)?,
            ));
        }
        Ok(anchors)
    }

    /// Returns one bracket descriptor's anchors plus its owning sort anchor.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if a parsed node emits no token leaves.
    pub fn bracket_provenance(
        &self,
        bracket: &BracketAttribute,
    ) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = bracket.provenance()?;
        anchors.push(ProvenanceAnchor::new(
            ProvenanceRole::SortDeclaration,
            0,
            TokenRange::for_tokens(&self.name)?,
        ));
        Ok(anchors)
    }
}

/// A comma-compressed membership sentence such as `impl Value for Int, Bool;`.
#[derive(Clone, Debug)]
pub struct SortsMembership {
    supersort: Path,
    members: Vec<Path>,
}

impl SortsMembership {
    /// Returns the populated sort path.
    #[must_use]
    pub const fn supersort(&self) -> &Path {
        &self.supersort
    }

    /// Returns member type paths in authored order.
    #[must_use]
    pub fn members(&self) -> &[Path] {
        &self.members
    }

    /// Returns the three explicit-subsort anchors for one comma-list member.
    ///
    /// The member path is the declaration anchor because it is the unique leaf
    /// for each relation in a compressed sentence.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if a parsed path emits no token leaves.
    pub fn member_provenance(&self, member: &Path) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(vec![
            ProvenanceAnchor::new(
                ProvenanceRole::SubsortDeclaration,
                0,
                TokenRange::for_tokens(member)?,
            ),
            ProvenanceAnchor::new(
                ProvenanceRole::SubsortSuperSort,
                0,
                TokenRange::for_tokens(&self.supersort)?,
            ),
            ProvenanceAnchor::new(
                ProvenanceRole::SubsortSubSort,
                0,
                TokenRange::for_tokens(member)?,
            ),
        ])
    }
}

/// Parsed contents of one folded sort declaration/membership block.
#[derive(Clone, Debug)]
pub struct SortsDeclaration {
    entries: Vec<SortsEntry>,
}

impl SortsDeclaration {
    /// Returns declarations and memberships in authored order.
    #[must_use]
    pub fn entries(&self) -> &[SortsEntry] {
        &self.entries
    }
}

/// Parses a `k::sorts!` body from proc-macro tokens.
///
/// # Errors
///
/// Rejects malformed declarations, unsupported attributes, non-path
/// endpoints, empty comma lists, and missing semicolons.
pub fn parse_sorts_declaration(tokens: TokenStream) -> Result<SortsDeclaration, SyntaxError> {
    syn::parse2(tokens).map_err(Into::into)
}

/// Parses a `k::sorts!` body from source text.
///
/// # Errors
///
/// Returns the same failures as [`parse_sorts_declaration`].
pub fn parse_sorts_declaration_source(source: &str) -> Result<SortsDeclaration, SyntaxError> {
    syn::parse_str(source).map_err(Into::into)
}

impl Parse for SortsDeclaration {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let mut entries = Vec::new();
        while !input.is_empty() {
            let attributes = input.call(Attribute::parse_outer)?;
            if input.peek(Token![impl]) {
                if let Some(attribute) = attributes.first() {
                    return Err(syn::Error::new_spanned(
                        attribute,
                        "membership lines in `sorts!` do not accept attributes",
                    ));
                }
                entries.push(SortsEntry::Membership(input.parse()?));
            } else {
                entries.push(SortsEntry::Sort(parse_sort(input, attributes)?));
            }
        }
        if entries.is_empty() {
            return Err(input.error("`sorts!` requires at least one sort or membership line"));
        }
        Ok(Self { entries })
    }
}

fn parse_sort(input: ParseStream<'_>, attributes: Vec<Attribute>) -> syn::Result<SortsSort> {
    let name: Ident = input.parse()?;
    let mut parents = Vec::new();
    if input.peek(Token![:]) {
        input.parse::<Token![:]>()?;
        loop {
            parents.push(parse_plain_path(input, "parent sort")?);
            if !input.peek(Token![+]) {
                break;
            }
            input.parse::<Token![+]>()?;
        }
    }
    input.parse::<Token![;]>()?;

    let mut brackets = Vec::new();
    for attribute in attributes {
        let Some(segment) = attribute.path().segments.last() else {
            return Err(syn::Error::new_spanned(
                attribute,
                "invalid `sorts!` attribute",
            ));
        };
        if segment.ident != "bracket" {
            return Err(syn::Error::new_spanned(
                attribute,
                "only `#[k::bracket(...)]` is supported on a `sorts!` declaration",
            ));
        }
        let syn::Meta::List(list) = &attribute.meta else {
            return Err(syn::Error::new_spanned(
                attribute,
                "`#[k::bracket]` requires delimiter arguments",
            ));
        };
        brackets.push(parse_bracket_attribute(list.tokens.clone())?);
    }

    Ok(SortsSort {
        name,
        parents,
        brackets,
    })
}

impl Parse for SortsMembership {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        input.parse::<Token![impl]>()?;
        let supersort = parse_plain_path(input, "membership sort")?;
        input.parse::<Token![for]>()?;
        let mut members = Vec::new();
        loop {
            members.push(parse_plain_path(input, "member type")?);
            if !input.peek(Token![,]) {
                break;
            }
            input.parse::<Token![,]>()?;
            if input.peek(Token![;]) {
                return Err(input.error("expected a member type after `,`"));
            }
        }
        input.parse::<Token![;]>()?;
        Ok(Self { supersort, members })
    }
}

fn parse_plain_path(input: ParseStream<'_>, role: &str) -> syn::Result<Path> {
    let path = input.call(Path::parse_mod_style)?;
    if path
        .segments
        .iter()
        .any(|segment| !segment.arguments.is_none())
    {
        return Err(syn::Error::new_spanned(
            path,
            format!("the {role} must be a plain Rust path without generic arguments"),
        ));
    }
    Ok(path)
}
