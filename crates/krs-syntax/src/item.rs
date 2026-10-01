use proc_macro2::TokenStream;
use syn::spanned::Spanned;
use syn::{
    Attribute, Expr, Field, Fields, Ident, ItemStruct, ItemTrait, Lit, Meta, TraitBoundModifier,
    TypeParamBound,
};

use crate::attribute::is_plain_path;
use crate::parse::{KrsSyntax, checked_ordinal};
use crate::term_sort::{TermSort, parse_term_sort};
use crate::{ProvenanceAnchor, ProvenanceRole, SyntaxError, SyntaxErrorKind, TokenRange};

/// One validated named field of a record constructor.
///
/// The parser deliberately accepts only symbolic `Term<SortPath>` and
/// `Term<dyn SortPath>` fields. Bare token and builtin field types need the
/// later builtin catalog to distinguish an object-language sort from an
/// ordinary Rust representation type, so they are not guessed here.
#[derive(Clone, Debug)]
pub struct ConstructorField {
    pub(crate) field: Field,
    pub(crate) name: Ident,
    pub(crate) term_sort: TermSort,
}

impl ConstructorField {
    /// Returns the original span-preserving Rust field.
    #[must_use]
    pub const fn field(&self) -> &Field {
        &self.field
    }

    /// Returns the field name.
    #[must_use]
    pub const fn name(&self) -> &Ident {
        &self.name
    }

    /// Returns the symbolic field type and its object-language sort path.
    #[must_use]
    pub const fn term_sort(&self) -> &TermSort {
        &self.term_sort
    }
}

/// One literal Rust documentation line attached to an object-language
/// production.
///
/// Rust lowers `/// text` to `#[doc = " text"]`; the optional conventional
/// leading space is removed here so target emitters receive the text rustdoc
/// presents to readers.
#[derive(Clone, Debug)]
pub struct ProductionDocumentation {
    literal: syn::LitStr,
    text: String,
}

impl ProductionDocumentation {
    /// Returns the normalized documentation text.
    #[must_use]
    pub fn text(&self) -> &str {
        &self.text
    }

    /// Returns the original span-bearing Rust string literal.
    #[must_use]
    pub const fn literal(&self) -> &syn::LitStr {
        &self.literal
    }
}

/// Validated unit or named-field record constructor declaration.
#[derive(Clone, Debug)]
pub struct ConstructorDeclaration {
    item: ItemStruct,
    fields: Vec<ConstructorField>,
    documentation: Vec<ProductionDocumentation>,
}

impl ConstructorDeclaration {
    /// Validates a previously parsed Rust struct as a constructor.
    ///
    /// # Errors
    ///
    /// Rejects generic and where-clause declarations, tuple structs, field
    /// attributes, and record fields not typed as `Term<SortPath>` or
    /// `Term<dyn SortPath>` at the responsible token.
    pub fn from_item(item: ItemStruct) -> Result<Self, SyntaxError> {
        if !item.generics.params.is_empty() {
            return Err(unsupported_constructor(
                "constructors cannot have generic parameters",
                item.generics.params.span(),
            ));
        }
        if let Some(where_clause) = &item.generics.where_clause {
            return Err(unsupported_constructor(
                "constructors cannot have a where clause",
                where_clause.span(),
            ));
        }

        let fields = match &item.fields {
            Fields::Unit => Vec::new(),
            Fields::Named(named) => {
                let mut parsed = Vec::with_capacity(named.named.len());
                for field in &named.named {
                    if let Some(attribute) = field.attrs.first() {
                        return Err(unsupported_constructor(
                            "constructor field attributes are not supported",
                            attribute.span(),
                        ));
                    }
                    let Some(name) = field.ident.clone() else {
                        return Err(unsupported_constructor(
                            "record constructor fields must be named",
                            field.span(),
                        ));
                    };
                    let term_sort = parse_term_sort(field.ty.clone())?;
                    parsed.push(ConstructorField {
                        field: field.clone(),
                        name,
                        term_sort,
                    });
                }
                parsed
            }
            Fields::Unnamed(unnamed) => {
                return Err(unsupported_constructor(
                    "tuple structs are not supported; use a unit or named-field struct",
                    unnamed.span(),
                ));
            }
        };

        let documentation = production_documentation(&item.attrs)?;

        Ok(Self {
            item,
            fields,
            documentation,
        })
    }

    /// Returns the original span-preserving Rust struct.
    #[must_use]
    pub const fn item(&self) -> &ItemStruct {
        &self.item
    }

    /// Returns the constructor name.
    #[must_use]
    pub const fn name(&self) -> &Ident {
        &self.item.ident
    }

    /// Returns named record fields in authored order; unit constructors are empty.
    #[must_use]
    pub fn fields(&self) -> &[ConstructorField] {
        &self.fields
    }

    /// Returns literal rustdoc lines carried by this production.
    #[must_use]
    pub fn documentation(&self) -> &[ProductionDocumentation] {
        &self.documentation
    }

    /// Returns the declaration and ordered field-sort anchors.
    ///
    /// Field anchors cover the inner rustc-resolvable object-language sort
    /// path, not the surrounding `Term` wrapper.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if a parsed Rust node emits no leaves.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = Vec::with_capacity(self.fields.len() + 1);
        anchors.push(ProvenanceAnchor::new(
            ProvenanceRole::ConstructorDeclaration,
            0,
            TokenRange::for_tokens(&self.item.ident)?,
        ));
        for (ordinal, field) in self.fields.iter().enumerate() {
            let range = TokenRange::for_tokens(field.term_sort.sort())?;
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConstructorFieldSort,
                checked_ordinal(ordinal, ProvenanceRole::ConstructorFieldSort, range.first())?,
                range,
            ));
        }
        Ok(anchors)
    }

    /// Returns the compact anchors plus each constructor field declaration name.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if a parsed node emits no leaves.
    pub fn full_provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = self.provenance()?;
        for (ordinal, field) in self.fields.iter().enumerate() {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConstructorFieldDeclaration,
                checked_ordinal(
                    ordinal,
                    ProvenanceRole::ConstructorFieldDeclaration,
                    field.name.span(),
                )?,
                TokenRange::for_tokens(&field.name)?,
            ));
        }
        for (ordinal, documentation) in self.documentation.iter().enumerate() {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConstructorDocumentation,
                checked_ordinal(
                    ordinal,
                    ProvenanceRole::ConstructorDocumentation,
                    documentation.literal.span(),
                )?,
                TokenRange::for_tokens(&documentation.literal)?,
            ));
        }
        Ok(anchors)
    }
}

pub(crate) fn production_documentation(
    attributes: &[Attribute],
) -> Result<Vec<ProductionDocumentation>, SyntaxError> {
    attributes
        .iter()
        .filter(|attribute| attribute.path().is_ident("doc"))
        .filter_map(|attribute| match &attribute.meta {
            Meta::NameValue(name_value) => Some((&name_value.value, attribute.span())),
            Meta::Path(_) | Meta::List(_) => None,
        })
        .map(|(value, span)| {
            let Expr::Lit(expression) = value else {
                return Err(unsupported_constructor(
                    "production documentation must be a literal Rust string",
                    span,
                ));
            };
            let Lit::Str(literal) = &expression.lit else {
                return Err(unsupported_constructor(
                    "production documentation must be a literal Rust string",
                    span,
                ));
            };
            let value = literal.value();
            let text = value.strip_prefix(' ').unwrap_or(&value).to_owned();
            Ok(ProductionDocumentation {
                literal: literal.clone(),
                text,
            })
        })
        .collect()
}

impl KrsSyntax for ConstructorDeclaration {
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        Self::from_item(syn::parse2::<ItemStruct>(tokens)?)
    }
}

/// Validated marker-trait sort declaration.
#[derive(Clone, Debug)]
pub struct SortDeclaration {
    item: ItemTrait,
    parents: Vec<syn::Path>,
}

impl SortDeclaration {
    /// Validates a previously parsed Rust trait as an open sort.
    ///
    /// # Errors
    ///
    /// Rejects unsafe, auto, generic, nonempty, lifetime-bounded, optional, or
    /// otherwise non-marker trait shapes at the responsible token.
    pub fn from_item(item: ItemTrait) -> Result<Self, SyntaxError> {
        if let Some(unsafety) = item.unsafety {
            return Err(unsupported_sort(
                "sort traits cannot be unsafe",
                unsafety.span,
            ));
        }
        if let Some(auto) = item.auto_token {
            return Err(unsupported_sort(
                "sort traits cannot be auto traits",
                auto.span,
            ));
        }
        if !item.generics.params.is_empty() {
            return Err(unsupported_sort(
                "sort traits cannot have generic parameters",
                item.generics.params.span(),
            ));
        }
        if let Some(where_clause) = &item.generics.where_clause {
            return Err(unsupported_sort(
                "sort traits cannot have a where clause",
                where_clause.span(),
            ));
        }
        if !item.items.is_empty() {
            return Err(unsupported_sort(
                "sort traits must not declare associated items",
                item.items[0].span(),
            ));
        }

        let mut parents = Vec::with_capacity(item.supertraits.len());
        for bound in &item.supertraits {
            let TypeParamBound::Trait(parent) = bound else {
                return Err(unsupported_sort(
                    "direct sort parents must be Rust trait paths, not lifetimes",
                    bound.span(),
                ));
            };
            if !matches!(parent.modifier, TraitBoundModifier::None)
                || parent.lifetimes.is_some()
                || !is_plain_path(&parent.path)
            {
                return Err(unsupported_sort(
                    "direct sort parents must be plain, required trait paths",
                    parent.span(),
                ));
            }
            parents.push(parent.path.clone());
        }

        Ok(Self { item, parents })
    }

    /// Returns the original span-preserving Rust trait.
    #[must_use]
    pub const fn item(&self) -> &ItemTrait {
        &self.item
    }

    /// Returns direct parent sort paths in authored order.
    #[must_use]
    pub fn parents(&self) -> &[syn::Path] {
        &self.parents
    }

    /// Returns canonical name and parent anchors.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if a parsed node emits no leaves.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = Vec::with_capacity(self.parents.len() + 1);
        anchors.push(ProvenanceAnchor::new(
            ProvenanceRole::SortDeclaration,
            0,
            TokenRange::for_tokens(&self.item.ident)?,
        ));
        for (ordinal, parent) in self.parents.iter().enumerate() {
            let ordinal = checked_ordinal(ordinal, ProvenanceRole::SortParent, parent.span())?;
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::SortParent,
                ordinal,
                TokenRange::for_tokens(parent)?,
            ));
        }
        Ok(anchors)
    }
}

impl KrsSyntax for SortDeclaration {
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        Self::from_item(syn::parse2::<ItemTrait>(tokens)?)
    }
}

fn unsupported_sort(reason: &'static str, span: proc_macro2::Span) -> SyntaxError {
    SyntaxError::new(SyntaxErrorKind::UnsupportedSortDeclaration { reason }, span)
}

fn unsupported_constructor(reason: &'static str, span: proc_macro2::Span) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::UnsupportedConstructorDeclaration { reason },
        span,
    )
}
