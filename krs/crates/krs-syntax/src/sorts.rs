use krs_ir::ProvenanceKey;
use proc_macro2::TokenStream;
use syn::parse::{Parse, ParseStream};
use syn::{Attribute, Ident, Path, Token};

use crate::parse::{KeyAllocator, KrsSyntax};
use crate::{BracketAttribute, ProvenanceAnchor, ProvenanceRole, SyntaxError, TokenRange};

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
    name_key: Option<ProvenanceKey>,
    parent_keys: Vec<ProvenanceKey>,
    /// The anchors of the sort's keying, which [`Self::provenance`] returns.
    anchors: Vec<ProvenanceAnchor>,
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

    /// The key of the sort name, which is the same in the sort's descriptor
    /// and in each of its brackets'.
    #[must_use]
    pub const fn name_key(&self) -> Option<&ProvenanceKey> {
        self.name_key.as_ref()
    }

    /// The keys of the parent paths, indexed as [`Self::parents`].
    #[must_use]
    pub fn parent_keys(&self) -> &[ProvenanceKey] {
        &self.parent_keys
    }

    /// Returns the declaration name and parent-path anchors.
    ///
    /// # Errors
    ///
    /// None: the sort was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    /// Keys the sort name, then each parent path, as a sentence of its own.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        self.name_key = Some(keys.key(
            ProvenanceRole::SortDeclaration,
            TokenRange::for_tokens(&self.name)?,
        )?);
        self.parent_keys = Vec::with_capacity(self.parents.len());
        for parent in &self.parents {
            self.parent_keys
                .push(keys.key(ProvenanceRole::SortParent, TokenRange::for_tokens(parent)?)?);
        }
        self.anchors = keys.into_anchors();
        Ok(self)
    }

    /// Returns one bracket descriptor's anchors plus its owning sort anchor:
    /// the bracket's own keying, continued by the sort name's key.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if a parsed node emits no token leaves.
    pub fn bracket_provenance(
        &self,
        bracket: &BracketAttribute,
    ) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut keys = KeyAllocator::continuing(bracket.provenance()?);
        keys.key(
            ProvenanceRole::SortDeclaration,
            TokenRange::for_tokens(&self.name)?,
        )?;
        Ok(keys.into_anchors())
    }
}

/// A comma-compressed membership sentence such as `impl Value for Int, Bool;`.
#[derive(Clone, Debug)]
pub struct SortsMembership {
    supersort: Path,
    members: Vec<Path>,
    supersort_key: Option<ProvenanceKey>,
    member_keys: Vec<Vec<ProvenanceKey>>,
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

    /// The key of the supersort path, which is the same in every member's
    /// descriptor.
    #[must_use]
    pub const fn supersort_key(&self) -> Option<&ProvenanceKey> {
        self.supersort_key.as_ref()
    }

    /// Every key of the member path at `index` in [`Self::members`]: its
    /// subsort declaration's, then its subsort's. Each member is its own
    /// descriptor, so each key is the first of its role.
    #[must_use]
    pub fn member_keys(&self, index: usize) -> &[ProvenanceKey] {
        self.member_keys.get(index).map_or(&[], Vec::as_slice)
    }

    /// Keys the supersort and each member, each member in a descriptor of
    /// its own: its declaration, the supersort, then the member as the
    /// subsort, which is the member's declaration key's ordinal.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        self.member_keys = Vec::with_capacity(self.members.len());
        for member in &self.members {
            let mut keys = KeyAllocator::default();
            let range = TokenRange::for_tokens(member)?;
            let member_key = keys.key(ProvenanceRole::SubsortDeclaration, range)?;
            self.supersort_key = Some(keys.key(
                ProvenanceRole::SubsortSuperSort,
                TokenRange::for_tokens(&self.supersort)?,
            )?);
            let subsort_key = keys.key(ProvenanceRole::SubsortSubSort, range)?;
            self.member_keys.push(vec![member_key, subsort_key]);
        }
        Ok(self)
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
        let mut keys = KeyAllocator::default();
        keys.key(
            ProvenanceRole::SubsortDeclaration,
            TokenRange::for_tokens(member)?,
        )?;
        keys.key(
            ProvenanceRole::SubsortSuperSort,
            TokenRange::for_tokens(&self.supersort)?,
        )?;
        keys.key(
            ProvenanceRole::SubsortSubSort,
            TokenRange::for_tokens(member)?,
        )?;
        Ok(keys.into_anchors())
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

impl KrsSyntax for SortsDeclaration {
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        syn::parse2(tokens).map_err(Into::into)
    }
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
        brackets.push(BracketAttribute::parse_tokens(list.tokens.clone())?);
    }

    Ok(SortsSort {
        name,
        parents,
        brackets,
        name_key: None,
        parent_keys: Vec::new(),
        anchors: Vec::new(),
    }
    .keyed()?)
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
            // A trailing comma before the `;` ends the list.
            if input.peek(Token![;]) {
                break;
            }
        }
        input.parse::<Token![;]>()?;
        Ok(Self {
            supersort,
            members,
            supersort_key: None,
            member_keys: Vec::new(),
        }
        .keyed()?)
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
