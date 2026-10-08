//! `#[k::syntax_list]`: K's syntactic lists `List{Elem, "sep"}` (KF-020).
//!
//! ```text
//! #[k::syntax_list(separator = ",")]
//! pub enum Ints { Cons { head: Int, tail: Ints }, Nil() }
//! ```
//!
//! The enum is the whole definition of a closed sort: one cons variant with
//! exactly two fields, whose second field is the enum itself, and one
//! zero-field tuple terminator variant. Programs write `1, 2, 3` and the empty
//! text for the empty list; rules match the variants, which K prints as
//! `I , Is` and `.Ints`. The readable layer writes field sorts and inherits a
//! strictness result from `result = R`; the reference layer (`reference`)
//! writes `k::Term<..>` field types and puts `result` on the strictness
//! attribute.

use proc_macro2::{Span, TokenStream};
use syn::parse::ParseStream;
use syn::spanned::Spanned;
use syn::{Attribute, Fields, Ident, ItemEnum, LitStr, Meta, Path, Token, Variant};

use crate::grammar::{StrictnessAttribute, StrictnessKind, push_terminal};
use crate::item::{ConstructorField, ProductionDocumentation, production_documentation};
use crate::parse::{KrsSyntax, ParseError, checked_ordinal, duplicate, structured, unknown};
use crate::term_sort::{parse_readable_sort, parse_term_sort};
use crate::{
    ProvenanceAnchor, ProvenanceRole, SyntaxError, SyntaxErrorKind, SyntaxTemplateItem, TokenRange,
};

/// Checked payload of `#[k::syntax_list(separator = "..", non_empty, result = R, reference)]`.
#[derive(Clone, Debug)]
pub struct SyntaxListAttribute {
    separator: LitStr,
    non_empty: Option<Ident>,
    result: Option<Path>,
    reference: Option<Ident>,
    range: TokenRange,
}

impl SyntaxListAttribute {
    /// Returns the separator literal; its value is empty or one K terminal.
    #[must_use]
    pub const fn separator(&self) -> &LitStr {
        &self.separator
    }

    /// Returns the `non_empty` flag (K's `NeList`), when present.
    #[must_use]
    pub const fn non_empty(&self) -> Option<&Ident> {
        self.non_empty.as_ref()
    }

    /// Returns the readable strictness result sort, when present.
    #[must_use]
    pub const fn result(&self) -> Option<&Path> {
        self.result.as_ref()
    }

    /// Whether this is the materialized reference form.
    #[must_use]
    pub const fn is_reference(&self) -> bool {
        self.reference.is_some()
    }

    /// Returns the list-declaration, separator, and `non_empty` anchors.
    #[must_use]
    pub fn provenance(&self) -> Vec<ProvenanceAnchor> {
        let mut anchors = vec![
            ProvenanceAnchor::new(ProvenanceRole::ListDeclaration, 0, self.range),
            ProvenanceAnchor::new(
                ProvenanceRole::ListSeparator,
                0,
                TokenRange::new(self.separator.span(), self.separator.span()),
            ),
        ];
        if let Some(flag) = &self.non_empty {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ListNonEmpty,
                0,
                TokenRange::new(flag.span(), flag.span()),
            ));
        }
        anchors
    }
}

impl KrsSyntax for SyntaxListAttribute {
    /// Parses the attribute payload from proc-macro tokens.
    ///
    /// # Errors
    ///
    /// Requires `separator = ".."` (empty or one K terminal) and accepts at
    /// most one each of `non_empty`, `result = Path`, and `reference`;
    /// `result` and `reference` exclude each other.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        let range = TokenRange::for_tokens(&tokens).map_err(|_| {
            invalid(
                "`#[k::syntax_list]` requires `separator = \"..\"`",
                Span::call_site(),
            )
        })?;
        let mut parsed = structured(tokens, parse_attribute_stream)?;
        parsed.range = range;
        Ok(parsed)
    }
}

fn invalid(reason: &'static str, span: Span) -> SyntaxError {
    SyntaxError::new(SyntaxErrorKind::InvalidSyntaxList { reason }, span)
}

fn parse_attribute_stream(input: ParseStream<'_>) -> Result<SyntaxListAttribute, ParseError> {
    let missing_span = input.span();
    let mut separator = None;
    let mut non_empty = None;
    let mut result = None;
    let mut reference = None;
    while !input.is_empty() {
        let key: Ident = input.parse()?;
        let name = key.to_string();
        match name.as_str() {
            "separator" if separator.is_some() => return Err(duplicate("separator", key.span())),
            "separator" => {
                input.parse::<Token![=]>()?;
                let literal: LitStr = input.parse()?;
                validate_separator(&literal)?;
                separator = Some(literal);
            }
            "non_empty" if non_empty.is_some() => {
                return Err(invalid(
                    "`non_empty` is written once: it makes the list K's `NeList`",
                    key.span(),
                )
                .into());
            }
            "non_empty" => non_empty = Some(key),
            "result" if result.is_some() => return Err(duplicate("result", key.span())),
            "result" => {
                input.parse::<Token![=]>()?;
                result = Some(input.parse::<Path>()?);
            }
            "reference" if reference.is_some() => return Err(duplicate("reference", key.span())),
            "reference" => reference = Some(key),
            _ => return Err(unknown(name, key.span())),
        }
        if input.is_empty() {
            break;
        }
        input.parse::<Token![,]>()?;
    }
    let Some(separator) = separator else {
        return Err(invalid(
            "`#[k::syntax_list]` requires `separator = \"..\"`; write `separator = \"\"` for a list without separator",
            missing_span,
        )
        .into());
    };
    if let (Some(result), Some(_)) = (&result, &reference) {
        return Err(invalid(
            "a reference syntactic list writes `result = ..` on the cons variant's strictness attribute, not on `#[k::syntax_list]`",
            result.span(),
        )
        .into());
    }
    Ok(SyntaxListAttribute {
        separator,
        non_empty,
        result,
        reference,
        range: TokenRange::new(missing_span, missing_span),
    })
}

fn validate_separator(literal: &LitStr) -> Result<(), ParseError> {
    let text = literal.value();
    if text.is_empty() {
        return Ok(());
    }
    let mut items = Vec::new();
    let mut terminal = text.clone();
    push_terminal(&mut items, &mut terminal);
    if !matches!(items.as_slice(), [SyntaxTemplateItem::Terminal(only)] if *only == text) {
        return Err(invalid(
            "a list separator is empty or exactly one K terminal: no whitespace, and no mix of word and symbol characters",
            literal.span(),
        )
        .into());
    }
    Ok(())
}

/// The cons variant of a syntactic list: `Cons { head: Elem, tail: List }`.
#[derive(Clone, Debug)]
pub struct SyntaxListCons {
    variant: Variant,
    head: ConstructorField,
    tail: ConstructorField,
    strictness: Option<StrictnessAttribute>,
    documentation: Vec<ProductionDocumentation>,
}

impl SyntaxListCons {
    /// Returns the variant with its KRS helpers removed.
    #[must_use]
    pub const fn variant(&self) -> &Variant {
        &self.variant
    }

    /// Returns the variant name.
    #[must_use]
    pub const fn name(&self) -> &Ident {
        &self.variant.ident
    }

    /// Returns the element field.
    #[must_use]
    pub const fn head(&self) -> &ConstructorField {
        &self.head
    }

    /// Returns the tail field, whose sort is the list itself.
    #[must_use]
    pub const fn tail(&self) -> &ConstructorField {
        &self.tail
    }

    /// Returns the head and tail fields in declaration order.
    #[must_use]
    pub fn fields(&self) -> [&ConstructorField; 2] {
        [&self.head, &self.tail]
    }

    /// Returns the variant's strictness, when declared.
    #[must_use]
    pub const fn strictness(&self) -> Option<&StrictnessAttribute> {
        self.strictness.as_ref()
    }

    /// Returns the variant's rustdoc lines.
    #[must_use]
    pub fn documentation(&self) -> &[ProductionDocumentation] {
        &self.documentation
    }
}

/// The terminator variant of a syntactic list: `Nil()`.
#[derive(Clone, Debug)]
pub struct SyntaxListTerminator {
    variant: Variant,
}

impl SyntaxListTerminator {
    /// Returns the variant.
    #[must_use]
    pub const fn variant(&self) -> &Variant {
        &self.variant
    }

    /// Returns the variant name.
    #[must_use]
    pub const fn name(&self) -> &Ident {
        &self.variant.ident
    }
}

/// A checked `#[k::syntax_list]` enum.
#[derive(Clone, Debug)]
pub struct SyntaxListDeclaration {
    attribute: SyntaxListAttribute,
    item: ItemEnum,
    cons: SyntaxListCons,
    terminator: SyntaxListTerminator,
}

impl SyntaxListDeclaration {
    /// Validates an enum whose invoking attribute payload has been split
    /// from the item by a procedural macro.
    ///
    /// # Errors
    ///
    /// Rejects generics, a variant count other than two, a cons variant that
    /// is not exactly two named fields with the enum as the second field's
    /// sort, a terminator that is not a zero-field tuple variant,
    /// discriminants, `#[k::syntax]` or other KRS helpers on variants,
    /// strictness on the terminator, and readable strictness without
    /// `result = R`.
    pub fn from_parts(
        attribute: &SyntaxListAttribute,
        item: ItemEnum,
    ) -> Result<Self, SyntaxError> {
        validate(attribute.clone(), item)
    }

    /// Validates a source-reparsed enum carrying its own
    /// `#[k::syntax_list(..)]` attribute.
    ///
    /// # Errors
    ///
    /// In addition to [`Self::from_parts`] failures, requires exactly one
    /// `k::syntax_list` attribute.
    pub fn from_attributed_item(mut item: ItemEnum) -> Result<Self, SyntaxError> {
        let mut attribute = None;
        let mut retained = Vec::with_capacity(item.attrs.len());
        for candidate in std::mem::take(&mut item.attrs) {
            if is_syntax_list_attribute(&candidate) {
                if attribute.is_some() {
                    return Err(invalid(
                        "an enum carries one `#[k::syntax_list]` attribute",
                        candidate.span(),
                    ));
                }
                let tokens = match &candidate.meta {
                    Meta::List(list) => list.tokens.clone(),
                    Meta::Path(_) | Meta::NameValue(_) => TokenStream::new(),
                };
                attribute = Some(SyntaxListAttribute::parse_tokens(tokens)?);
            } else {
                retained.push(candidate);
            }
        }
        item.attrs = retained;
        let attribute = attribute.ok_or_else(|| {
            invalid(
                "the enum requires `#[k::syntax_list(separator = \"..\")]`",
                item.ident.span(),
            )
        })?;
        validate(attribute, item)
    }

    /// Returns the checked attribute.
    #[must_use]
    pub const fn attribute(&self) -> &SyntaxListAttribute {
        &self.attribute
    }

    /// Returns the enum with variant KRS helpers removed.
    #[must_use]
    pub const fn item(&self) -> &ItemEnum {
        &self.item
    }

    /// Returns the enum name, which is the list sort.
    #[must_use]
    pub const fn name(&self) -> &Ident {
        &self.item.ident
    }

    /// Returns the cons variant.
    #[must_use]
    pub const fn cons(&self) -> &SyntaxListCons {
        &self.cons
    }

    /// Returns the terminator variant.
    #[must_use]
    pub const fn terminator(&self) -> &SyntaxListTerminator {
        &self.terminator
    }

    /// Returns the cons production's anchors: the list sort, the variant,
    /// its fields, its rustdoc, its strictness, and the list attribute.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only for a tokenless parsed Rust node.
    pub fn cons_provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = self.variant_anchors(&self.cons.variant)?;
        for (ordinal, field) in self.cons.fields().into_iter().enumerate() {
            let range = TokenRange::for_tokens(field.term_sort().sort())?;
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConstructorFieldSort,
                checked_ordinal(ordinal, ProvenanceRole::ConstructorFieldSort, range.first())?,
                range,
            ));
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConstructorFieldDeclaration,
                checked_ordinal(
                    ordinal,
                    ProvenanceRole::ConstructorFieldDeclaration,
                    field.name().span(),
                )?,
                TokenRange::for_tokens(field.name())?,
            ));
        }
        for (ordinal, documentation) in self.cons.documentation.iter().enumerate() {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConstructorDocumentation,
                checked_ordinal(
                    ordinal,
                    ProvenanceRole::ConstructorDocumentation,
                    documentation.literal().span(),
                )?,
                TokenRange::for_tokens(documentation.literal())?,
            ));
        }
        if let Some(strictness) = &self.cons.strictness {
            anchors.extend(strictness.provenance()?);
        }
        anchors.extend(self.attribute.provenance());
        Ok(anchors)
    }

    /// Returns the terminator production's anchors: the list sort, the
    /// variant, and the list attribute.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only for a tokenless parsed Rust node.
    pub fn terminator_provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = self.variant_anchors(&self.terminator.variant)?;
        anchors.extend(
            self.attribute
                .provenance()
                .into_iter()
                .filter(|anchor| anchor.role() == ProvenanceRole::ListDeclaration),
        );
        Ok(anchors)
    }

    fn variant_anchors(&self, variant: &Variant) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(vec![
            ProvenanceAnchor::new(
                ProvenanceRole::ConstructorSort,
                0,
                TokenRange::for_tokens(&self.item.ident)?,
            ),
            ProvenanceAnchor::new(
                ProvenanceRole::ConstructorDeclaration,
                0,
                TokenRange::for_tokens(&variant.ident)?,
            ),
        ])
    }
}

fn is_syntax_list_attribute(attribute: &Attribute) -> bool {
    attribute
        .path()
        .segments
        .last()
        .is_some_and(|segment| segment.ident == "syntax_list")
}

fn is_k_helper(attribute: &Attribute) -> bool {
    attribute.path().segments.len() >= 2
        && attribute
            .path()
            .segments
            .first()
            .is_some_and(|segment| segment.ident == "k")
}

fn strictness_kind(attribute: &Attribute) -> Option<(StrictnessKind, Ident)> {
    if !is_k_helper(attribute) {
        return None;
    }
    let last = attribute.path().segments.last()?;
    if last.ident == "strict" {
        Some((StrictnessKind::Strict, last.ident.clone()))
    } else if last.ident == "seqstrict" {
        Some((StrictnessKind::SeqStrict, last.ident.clone()))
    } else {
        None
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "One ordered validation pass keeps every list diagnostic at its source span."
)]
fn validate(
    attribute: SyntaxListAttribute,
    mut item: ItemEnum,
) -> Result<SyntaxListDeclaration, SyntaxError> {
    if !item.generics.params.is_empty() || item.generics.where_clause.is_some() {
        return Err(invalid(
            "a syntactic list cannot have generic parameters or a where clause",
            item.generics.span(),
        ));
    }
    if item.variants.len() != 2 {
        return Err(invalid(
            "a syntactic list has exactly two variants: a cons variant `Cons { head: Elem, tail: List }` and a terminator `Nil()`",
            item.ident.span(),
        ));
    }
    let enum_name = item.ident.clone();
    let mut cons = None;
    let mut terminator = None;
    for variant in &mut item.variants {
        if let Some((_, expression)) = &variant.discriminant {
            return Err(invalid(
                "syntactic-list variants cannot declare discriminants",
                expression.span(),
            ));
        }
        let mut strictness = None;
        let mut retained = Vec::with_capacity(variant.attrs.len());
        for helper in std::mem::take(&mut variant.attrs) {
            if let Some((kind, marker)) = strictness_kind(&helper) {
                if strictness.is_some() {
                    return Err(invalid(
                        "a list variant declares at most one `strict` or `seqstrict` strategy",
                        helper.span(),
                    ));
                }
                let tokens = match &helper.meta {
                    Meta::Path(_) => TokenStream::new(),
                    Meta::List(list) => list.tokens.clone(),
                    Meta::NameValue(_) => {
                        return Err(invalid(
                            "strictness uses marker or list syntax",
                            helper.span(),
                        ));
                    }
                };
                strictness = Some((kind, marker, tokens, helper.span()));
            } else if is_k_helper(&helper) {
                return Err(invalid(
                    "syntactic-list variants take no `#[k::syntax]` or other KRS helper except `strict`: K generates the list syntax and its symbols from the enum",
                    helper.span(),
                ));
            } else {
                retained.push(helper);
            }
        }
        variant.attrs = retained;
        match &variant.fields {
            Fields::Unnamed(fields) if fields.unnamed.is_empty() => {
                if terminator.is_some() {
                    return Err(invalid(
                        "a syntactic list has one terminator variant `Nil()`",
                        variant.ident.span(),
                    ));
                }
                if let Some((_, _, _, span)) = strictness {
                    return Err(invalid(
                        "the terminator variant has no fields to evaluate; put strictness on the cons variant",
                        span,
                    ));
                }
                terminator = Some(SyntaxListTerminator {
                    variant: variant.clone(),
                });
            }
            Fields::Named(named) if named.named.len() == 2 => {
                if cons.is_some() {
                    return Err(invalid(
                        "a syntactic list has one cons variant with two fields",
                        variant.ident.span(),
                    ));
                }
                let mut fields = Vec::with_capacity(2);
                for field in &named.named {
                    if let Some(attribute) = field.attrs.first() {
                        return Err(invalid(
                            "syntactic-list fields take no attributes",
                            attribute.span(),
                        ));
                    }
                    let name = field.ident.clone().expect("named fields have names");
                    let term_sort = if attribute.is_reference() {
                        parse_term_sort(field.ty.clone())?
                    } else {
                        parse_readable_sort(field.ty.clone())?
                    };
                    fields.push(ConstructorField {
                        field: field.clone(),
                        name,
                        term_sort,
                    });
                }
                let tail = fields.pop().expect("two fields");
                let head = fields.pop().expect("two fields");
                let tail_is_list = !tail.term_sort().is_dynamic()
                    && tail
                        .term_sort()
                        .sort()
                        .segments
                        .last()
                        .is_some_and(|segment| segment.ident == enum_name);
                if !tail_is_list {
                    return Err(invalid(
                        "the second field of the cons variant is the list itself: write `tail: Ints` for `enum Ints`",
                        tail.field().ty.span(),
                    ));
                }
                let available = [head.name().clone(), tail.name().clone()];
                let strictness = match strictness {
                    None => None,
                    Some((kind, _, tokens, _)) if attribute.is_reference() => Some(
                        StrictnessAttribute::parse_reference(kind, tokens, &available)?,
                    ),
                    Some((kind, marker, tokens, span)) => {
                        let Some(result) = attribute.result() else {
                            return Err(invalid(
                                "a readable strict list variant inherits its result sort from `#[k::syntax_list(.., result = R)]`",
                                span,
                            ));
                        };
                        Some(StrictnessAttribute::parse_readable(
                            kind,
                            tokens,
                            &marker,
                            result.clone(),
                            &available,
                        )?)
                    }
                };
                cons = Some(SyntaxListCons {
                    documentation: production_documentation(&variant.attrs)?,
                    variant: variant.clone(),
                    head,
                    tail,
                    strictness,
                });
            }
            _ => {
                return Err(invalid(
                    "a syntactic list has a cons variant with exactly two named fields `{ head: Elem, tail: List }` and a zero-field tuple terminator `Nil()`",
                    variant.ident.span(),
                ));
            }
        }
    }
    let (Some(cons), Some(terminator)) = (cons, terminator) else {
        return Err(invalid(
            "a syntactic list has exactly one cons variant `Cons { head: Elem, tail: List }` and one terminator `Nil()`",
            item.ident.span(),
        ));
    };
    if attribute.result().is_some() && cons.strictness.is_none() {
        return Err(invalid(
            "`result = R` names the result sort of the cons variant's `#[k::strict]`; add the strictness or drop `result`",
            attribute.range.first(),
        ));
    }
    Ok(SyntaxListDeclaration {
        attribute,
        item,
        cons,
        terminator,
    })
}
