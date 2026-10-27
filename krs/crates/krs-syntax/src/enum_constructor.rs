use std::collections::{BTreeMap, BTreeSet};

use krs_ir::AtLeastTwo;
use proc_macro2::{Span, TokenStream};
use syn::parse::{Parse, ParseStream};
use syn::spanned::Spanned;
use syn::{Attribute, Fields, Ident, ItemEnum, LitStr, Meta, Path, Token, Variant, parenthesized};

use crate::attribute::{
    ConstructorFamilyMode, ConstructorsAttribute, PlacementFlag, StaticMode,
    StaticProductionAttribute, SymbolAttribute, VariantSyntaxAttribute,
};
use crate::grammar::{GroupAssociativity, StrictnessAttribute, StrictnessKind};
use crate::item::{ConstructorField, ProductionDocumentation, production_documentation};
use krs_ir::ProvenanceKey;

use crate::parse::{KeyAllocator, KrsSyntax, first_non_doc_attribute};
use crate::term_sort::{parse_typed_readable_sort, parse_typed_term_sort};
use crate::{ProvenanceAnchor, ProvenanceRole, SyntaxError, SyntaxErrorKind, TokenRange};

/// The keys of a tier in its family's associativity descriptor: its
/// sentence, and its reference in that sentence.
#[derive(Clone, Debug)]
struct AssociativityKeys {
    sentence: ProvenanceKey,
    reference: ProvenanceKey,
}

/// One tier in an exhaustive enum-level readable-family precedence chain.
#[derive(Clone, Debug)]
pub struct EnumPrecedenceGroup {
    range: TokenRange,
    reference_range: TokenRange,
    associativity: Option<GroupAssociativity>,
    name: Option<Ident>,
    variants: Vec<Ident>,
    precedence_key: Option<ProvenanceKey>,
    associativity_keys: Option<AssociativityKeys>,
}

impl EnumPrecedenceGroup {
    /// Returns the tier's explicitly authored yacc-style associativity.
    ///
    /// A bare tier returns `None` and preserves K's unconstrained bare
    /// priority-block semantics. `Some(GroupAssociativity::NonAssociative)`
    /// is produced only by the explicit `non_assoc` keyword and lowers to
    /// K's distinct `non-assoc` sentence.
    #[must_use]
    pub const fn associativity(&self) -> Option<GroupAssociativity> {
        self.associativity
    }

    /// Returns an optional authored production-group identity.
    #[must_use]
    pub const fn name(&self) -> Option<&Ident> {
        self.name.as_ref()
    }

    /// Returns the exhaustively listed enum variants in source order.
    #[must_use]
    pub fn variants(&self) -> &[Ident] {
        &self.variants
    }

    /// Returns the stable production-group identity. Explicit names are kept;
    /// unnamed tiers derive `<family>_tierN` from chain position.
    #[must_use]
    pub fn emitted_name(&self, family: &Ident, ordinal: usize) -> String {
        self.name.as_ref().map_or_else(
            || format!("{}_tier{ordinal}", family.to_string().to_ascii_lowercase()),
            ToString::to_string,
        )
    }

    /// The key of the tier's reference in its family's precedence
    /// descriptor; `None` outside a chain.
    #[must_use]
    pub const fn precedence_key(&self) -> Option<&ProvenanceKey> {
        self.precedence_key.as_ref()
    }

    /// The key of the tier's sentence in its family's associativity
    /// descriptor; `None` for a bare tier.
    #[must_use]
    pub fn associativity_sentence_key(&self) -> Option<&ProvenanceKey> {
        self.associativity_keys.as_ref().map(|keys| &keys.sentence)
    }

    /// The key of the tier's reference in its own associativity sentence;
    /// `None` for a bare tier.
    #[must_use]
    pub fn associativity_reference_key(&self) -> Option<&ProvenanceKey> {
        self.associativity_keys.as_ref().map(|keys| &keys.reference)
    }

    /// Returns the complete tier's exact authored range.
    #[must_use]
    pub const fn range(&self) -> TokenRange {
        self.range
    }
}

/// One validated constructor production in a readable or reference Rust enum
/// family.
#[derive(Clone, Debug)]
pub struct EnumConstructorVariant {
    variant: Variant,
    fields: Vec<ConstructorField>,
    syntax: Option<VariantSyntaxAttribute>,
    constructor_sort: Path,
    strictness: Option<StrictnessAttribute>,
    documentation: Vec<ProductionDocumentation>,
    static_marker: Option<VariantStaticMarker>,
    precedence_group: Option<usize>,
    precedence_member_range: Option<TokenRange>,
    explicit_symbol: Option<SymbolAttribute>,
    /// The enum's `#[k::cons_list]` marker, on its cons variant (F6).
    cons_list_range: Option<TokenRange>,
    sort_key: Option<ProvenanceKey>,
    key: Option<ProvenanceKey>,
    group_key: Option<ProvenanceKey>,
    cons_list_key: Option<ProvenanceKey>,
    static_key: Option<ProvenanceKey>,
    /// The anchors of the variant's production descriptor.
    anchors: Vec<ProvenanceAnchor>,
    /// The anchors of the variant's field-sort argument view.
    argument_anchors: Vec<ProvenanceAnchor>,
}

impl EnumConstructorVariant {
    /// Returns one anchor per element type of a typed collection field sort,
    /// which only the variant's constructor descriptor references.
    ///
    /// # Errors
    ///
    /// None: the variant was keyed when it was parsed.
    pub fn argument_provenance(&self) -> Result<Vec<crate::ProvenanceAnchor>, SyntaxError> {
        Ok(self.argument_anchors.clone())
    }

    /// The key of the constructed sort, the first of its role in the
    /// variant's descriptor.
    #[must_use]
    pub const fn sort_key(&self) -> Option<&ProvenanceKey> {
        self.sort_key.as_ref()
    }

    /// The key of the variant name, the production's declaration.
    #[must_use]
    pub const fn key(&self) -> Option<&ProvenanceKey> {
        self.key.as_ref()
    }

    /// The key of the variant's membership in a precedence tier.
    #[must_use]
    pub const fn group_key(&self) -> Option<&ProvenanceKey> {
        self.group_key.as_ref()
    }

    /// The key of the enum's `#[k::cons_list]` marker, on its cons variant.
    #[must_use]
    pub const fn cons_list_key(&self) -> Option<&ProvenanceKey> {
        self.cons_list_key.as_ref()
    }

    /// The key of the `#[k::alias]` or `#[k::desugar]` marker.
    #[must_use]
    pub const fn static_key(&self) -> Option<&ProvenanceKey> {
        self.static_key.as_ref()
    }

    /// Keys the variant's two descriptors, each a sentence of its own. The
    /// production keys the constructed sort, the syntax attribute, the
    /// variant, each field's sort, each field's name, each rustdoc line, the
    /// tier membership, the cons-list marker, the strictness, the static
    /// marker and its payload, and the symbol override; the argument view
    /// keys each element type of the field sorts.
    fn rekey(&mut self) -> Result<(), SyntaxError> {
        let mut keys = KeyAllocator::default();
        self.sort_key = Some(keys.key(
            ProvenanceRole::ConstructorSort,
            TokenRange::for_tokens(&self.constructor_sort)?,
        )?);
        if let Some(syntax) = &mut self.syntax {
            syntax.allocate_keys(&mut keys)?;
        }
        self.key = Some(keys.key(
            ProvenanceRole::ConstructorDeclaration,
            TokenRange::for_tokens(&self.variant.ident)?,
        )?);
        for field in &mut self.fields {
            field.sort_key = Some(keys.key(
                ProvenanceRole::ConstructorFieldSort,
                TokenRange::for_tokens(field.term_sort().sort())?,
            )?);
        }
        for field in &mut self.fields {
            field.name_key = Some(keys.key(
                ProvenanceRole::ConstructorFieldDeclaration,
                TokenRange::for_tokens(field.name())?,
            )?);
        }
        for documentation in &mut self.documentation {
            documentation.key = Some(keys.key(
                ProvenanceRole::ConstructorDocumentation,
                TokenRange::for_tokens(documentation.literal())?,
            )?);
        }
        self.group_key = self
            .precedence_member_range
            .map(|range| keys.key(ProvenanceRole::ConstructorGroup, range))
            .transpose()?;
        self.cons_list_key = self
            .cons_list_range
            .map(|range| keys.key(ProvenanceRole::ConsListDeclaration, range))
            .transpose()?;
        if let Some(strictness) = &mut self.strictness {
            strictness.allocate_keys(&mut keys)?;
        }
        self.static_key = None;
        if let Some(marker) = &mut self.static_marker {
            self.static_key =
                Some(keys.key(marker.attribute.mode().production_role(), marker.range)?);
            marker.attribute.allocate_keys(&mut keys)?;
        }
        if let Some(symbol) = &mut self.explicit_symbol {
            symbol.allocate_keys(&mut keys)?;
        }
        self.anchors = keys.into_anchors();
        let mut keys = KeyAllocator::default();
        for field in &mut self.fields {
            crate::SortArgument::allocate_keys(
                field.term_sort.arguments_mut(),
                &mut keys,
                ProvenanceRole::ConstructorFieldSortArgument,
            )?;
        }
        self.argument_anchors = keys.into_anchors();
        Ok(())
    }

    /// Returns the variant's `#[k::symbol("path::Name")]` override: a pinned
    /// public identity whose final component names the emitted symbol in
    /// place of the default `lowerCamel(Enum)` + `Variant`.
    #[must_use]
    pub const fn explicit_symbol(&self) -> Option<&SymbolAttribute> {
        self.explicit_symbol.as_ref()
    }

    /// Returns the span-preserving Rust variant after KRS helper attributes
    /// have been consumed.
    #[must_use]
    pub const fn variant(&self) -> &Variant {
        &self.variant
    }

    /// Returns the variant identifier.
    #[must_use]
    pub const fn name(&self) -> &Ident {
        &self.variant.ident
    }

    /// Returns the sort constructed by the variant: the family's `sort`, not
    /// the enum's Rust name.
    #[must_use]
    pub const fn constructor_sort(&self) -> &Path {
        &self.constructor_sort
    }

    /// Returns named fields in Rust declaration order; unit variants are
    /// empty.
    #[must_use]
    pub fn fields(&self) -> &[ConstructorField] {
        &self.fields
    }

    /// Returns checked concrete-syntax and production metadata when the
    /// variant explicitly carries `#[k::syntax]`.
    #[must_use]
    pub const fn syntax(&self) -> Option<&VariantSyntaxAttribute> {
        self.syntax.as_ref()
    }

    /// Returns inherited readable strictness metadata, when present.
    #[must_use]
    pub const fn strictness(&self) -> Option<&StrictnessAttribute> {
        self.strictness.as_ref()
    }

    /// Returns literal rustdoc lines carried by this production.
    #[must_use]
    pub fn documentation(&self) -> &[ProductionDocumentation] {
        &self.documentation
    }

    /// Whether this constructor is headed by a static alias clause.
    #[must_use]
    pub fn is_alias(&self) -> bool {
        self.static_mode() == Some(StaticMode::Alias)
    }

    /// The static rewriting mode of the variant's `#[k::alias]` or
    /// `#[k::desugar]` marker, if any (KF-028).
    #[must_use]
    pub fn static_mode(&self) -> Option<StaticMode> {
        self.static_marker
            .as_ref()
            .map(|marker| marker.attribute.mode())
    }

    /// The variant's checked `#[k::alias]` or `#[k::desugar]` marker payload.
    #[must_use]
    pub fn static_attribute(&self) -> Option<&StaticProductionAttribute> {
        self.static_marker.as_ref().map(|marker| &marker.attribute)
    }

    /// Returns the enum-level precedence group ordinal in readable mode.
    #[must_use]
    pub const fn precedence_group(&self) -> Option<usize> {
        self.precedence_group
    }

    /// Returns the complete provenance catalog for this production descriptor.
    ///
    /// The enum identifier is the rustc-resolvable result-sort anchor. Field
    /// sorts and names remain in declaration order even when the concrete
    /// syntax template presents them in a different order.
    ///
    /// # Errors
    ///
    /// None: the variant was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }
}

/// A precedence chain and the provenance needed to emit its descriptor.
#[derive(Clone, Debug)]
pub struct EnumPrecedenceDescriptor<'a> {
    /// Groups from tightest to weakest binding.
    pub groups: &'a AtLeastTwo<EnumPrecedenceGroup>,
    /// Declaration, chain, and group-reference provenance in source order.
    pub provenance: Vec<ProvenanceAnchor>,
}

#[derive(Clone, Debug)]
enum EnumPrecedenceGroups {
    Single(Box<EnumPrecedenceGroup>),
    Chain(AtLeastTwo<EnumPrecedenceGroup>),
}

impl EnumPrecedenceGroups {
    fn iter(&self) -> impl Iterator<Item = &EnumPrecedenceGroup> {
        let (single, chain) = match self {
            Self::Single(group) => (Some(group.as_ref()), None),
            Self::Chain(groups) => (None, Some(groups)),
        };
        single
            .into_iter()
            .chain(chain.into_iter().flat_map(AtLeastTwo::iter))
    }

    fn into_vec(self) -> Vec<EnumPrecedenceGroup> {
        match self {
            Self::Single(group) => vec![*group],
            Self::Chain(groups) => {
                let (first, rest) = groups.into_head_tail();
                std::iter::once(first).chain(rest).collect()
            }
        }
    }

    fn from_vec(groups: Vec<EnumPrecedenceGroup>) -> Option<Self> {
        let mut groups = groups.into_iter();
        let first = groups.next()?;
        Some(match groups.next() {
            Some(second) => Self::Chain(AtLeastTwo::new(first, second, groups.collect())),
            None => Self::Single(Box::new(first)),
        })
    }
}

/// A validated constructor family: an enum whose variants construct one
/// declared sort.
#[derive(Clone, Debug)]
pub struct EnumConstructorDeclaration {
    item: ItemEnum,
    sort: Path,
    variants: Vec<EnumConstructorVariant>,
    reference_family: bool,
    precedence_groups: Option<EnumPrecedenceGroups>,
    precedence_declaration_range: Option<TokenRange>,
    precedence_chain_range: Option<TokenRange>,
    /// The indices of the cons and the empty variant of a `#[k::cons_list]`
    /// enum (F6).
    cons_list: Option<(usize, usize)>,
    precedence_declaration_key: Option<ProvenanceKey>,
    precedence_chain_key: Option<ProvenanceKey>,
    associativity_declaration_key: Option<ProvenanceKey>,
    /// The anchors of the family's precedence descriptor, when it has one.
    precedence_anchors: Option<Vec<ProvenanceAnchor>>,
    /// The anchors of the family's associativity descriptor, when it has
    /// one.
    associativity_anchors: Option<Vec<ProvenanceAnchor>>,
}

impl EnumConstructorDeclaration {
    /// Validates an enum after its invoking attribute payload has already been
    /// split from the item by a procedural macro.
    ///
    /// Non-KRS Rust attributes are retained. Recognized variant `k::syntax`
    /// helpers are consumed into typed metadata, while every other `k::`
    /// helper is rejected locally.
    ///
    /// # Errors
    ///
    /// Rejects generic enums, tuple variants, discriminants, unsupported KRS
    /// helpers, field attributes, and non-`Term<SortPath>` record fields.
    pub fn from_parts(
        attribute: &ConstructorsAttribute,
        item: ItemEnum,
    ) -> Result<Self, SyntaxError> {
        Self::validate(attribute, item, false)
    }

    /// Validates a source-reparsed enum containing its own
    /// `#[k::constructors(...)]` attribute.
    ///
    /// # Errors
    ///
    /// In addition to [`Self::from_parts`] failures, requires exactly one
    /// correctly formed outer `k::constructors` helper.
    pub fn from_attributed_item(mut item: ItemEnum) -> Result<Self, SyntaxError> {
        let mut constructors = None;
        let mut retained = Vec::with_capacity(item.attrs.len());
        for attribute in std::mem::take(&mut item.attrs) {
            if is_helper_named(&attribute, "constructors") {
                if constructors.is_some() {
                    return Err(unsupported_enum(
                        "an enum may carry only one `#[k::constructors]` attribute",
                        attribute.span(),
                    ));
                }
                constructors = Some(parse_outer_attribute(&attribute)?);
            } else {
                retained.push(attribute);
            }
        }
        item.attrs = retained;
        let attribute = constructors.ok_or_else(|| {
            unsupported_enum(
                "the enum requires `#[k::constructors(sort = Sort, result = KResult)]` or `#[k::constructors(sort = Sort, reference)]`",
                item.ident.span(),
            )
        })?;
        Self::validate(&attribute, item, true)
    }

    #[expect(
        clippy::too_many_lines,
        reason = "One ordered validation pass keeps enum and variant diagnostics at their source spans."
    )]
    fn validate(
        attribute: &ConstructorsAttribute,
        mut item: ItemEnum,
        _invoking_attribute_consumed: bool,
    ) -> Result<Self, SyntaxError> {
        if !item.generics.params.is_empty() {
            return Err(unsupported_enum(
                "enum constructor families cannot have generic parameters: a K sort parameter belongs to one production, so declare a parametric production as a struct (`#[k::constructor] struct Wrap<S: ?Sized>` or `#[k::function] struct Choose<S: ?Sized>`)",
                item.generics.params.span(),
            ));
        }
        if let Some(where_clause) = &item.generics.where_clause {
            return Err(unsupported_enum(
                "enum constructor families cannot have a where clause",
                where_clause.span(),
            ));
        }
        let reference_family = attribute.is_reference();
        let EnumHelpers {
            precedence,
            cons_list,
        } = take_enum_helpers(&mut item.attrs)?;
        if reference_family && precedence.is_some() {
            return Err(invalid_enum_precedence(
                "a reference constructor family carries precedence in freestanding family-owned grammar blocks",
                item.ident.span(),
            ));
        }
        let constructor_sort = attribute.sort().clone();
        let mut variants = Vec::with_capacity(item.variants.len());
        for variant in &mut item.variants {
            if let Some((_, expression)) = &variant.discriminant {
                return Err(unsupported_enum(
                    "enum constructor variants cannot declare discriminants",
                    expression.span(),
                ));
            }
            let helpers = take_variant_helpers(&mut variant.attrs, attribute.mode())?;
            let fields = parse_variant_fields(&variant.fields, reference_family)?;
            let documentation = production_documentation(&variant.attrs)?;
            let mut syntax = helpers.syntax;
            if let Some(syntax) = &mut syntax {
                syntax.validate_fields(fields.iter().map(ConstructorField::name))?;
                if let Some(internal) = attribute.internal() {
                    syntax.inherit_placement(PlacementFlag::Internal, internal.clone())?;
                }
                if reference_family && helpers.format.is_some() {
                    return Err(unsupported_enum(
                        "a reference variant materializes format inside `syntax`, not as a sibling helper",
                        variant.ident.span(),
                    ));
                }
                if reference_family && syntax.format().is_none() {
                    return Err(unsupported_enum(
                        "a reference variant requires an explicit `format` in `syntax`",
                        variant.ident.span(),
                    ));
                }
                if syntax.structured_format().is_some() && helpers.format.is_some() {
                    return Err(unsupported_enum(
                        "a readable variant cannot declare format both inside `syntax` and as a sibling helper",
                        variant.ident.span(),
                    ));
                }
                let explicit = helpers.format.or_else(|| syntax.format().cloned());
                syntax.apply_readable_format(explicit)?;
            } else if helpers.format.is_some() {
                return Err(unsupported_enum(
                    "a sibling `format` requires `syntax` on the same variant",
                    variant.ident.span(),
                ));
            }
            let available_fields = fields
                .iter()
                .map(|field| field.name().clone())
                .collect::<Vec<_>>();
            let strictness = match helpers.strictness {
                Some(VariantStrictness { kind, tokens, mode }) => Some(match mode {
                    VariantStrictnessMode::Reference => {
                        StrictnessAttribute::parse_reference(kind, tokens, &available_fields)?
                    }
                    VariantStrictnessMode::Readable { result, marker } => {
                        StrictnessAttribute::parse_readable(
                            kind,
                            tokens,
                            &marker,
                            result,
                            &available_fields,
                        )?
                    }
                }),
                None => None,
            };
            variants.push(EnumConstructorVariant {
                variant: variant.clone(),
                fields,
                syntax,
                constructor_sort: constructor_sort.clone(),
                strictness,
                documentation,
                static_marker: helpers.static_marker,
                precedence_group: None,
                precedence_member_range: None,
                explicit_symbol: helpers.symbol,
                cons_list_range: None,
                sort_key: None,
                key: None,
                group_key: None,
                cons_list_key: None,
                static_key: None,
                anchors: Vec::new(),
                argument_anchors: Vec::new(),
            });
        }
        if variants.is_empty() {
            return Err(unsupported_enum(
                "a readable constructor family must contain at least one variant",
                item.ident.span(),
            ));
        }

        // A chain is optional: without one the variants belong to no
        // production group. Whether the family needs one depends on the
        // assembled sort order, so `krs::analysis::missing-precedence-chain`
        // checks it over the whole definition.
        let (precedence_groups, precedence_declaration_range, precedence_chain_range) =
            match precedence {
                Some(precedence) => {
                    validate_precedence_members(&precedence, &item.ident, &mut variants)?;
                    (
                        EnumPrecedenceGroups::from_vec(precedence.groups),
                        Some(precedence.declaration_range),
                        Some(precedence.chain_range),
                    )
                }
                None if reference_family => {
                    validate_reference_groups(&item.ident, &variants)?;
                    (None, None, None)
                }
                None => {
                    validate_chainless_groups(&item.ident, &variants)?;
                    (None, None, None)
                }
            };

        let cons_list = match cons_list {
            Some(range) => {
                let (cons, empty) = cons_list_shape(&item.ident, &variants, range)?;
                variants[cons].cons_list_range = Some(range);
                Some((cons, empty))
            }
            None => None,
        };

        Self {
            item,
            sort: attribute.sort().clone(),
            variants,
            reference_family,
            precedence_groups,
            precedence_declaration_range,
            precedence_chain_range,
            cons_list,
            precedence_declaration_key: None,
            precedence_chain_key: None,
            associativity_declaration_key: None,
            precedence_anchors: None,
            associativity_anchors: None,
        }
        .keyed()
    }

    /// Keys the family's descriptors, each a sentence of its own: every
    /// variant's production and argument views, then the precedence chain
    /// (its declaration, the chain, each tier's reference) and the
    /// associativity sentences (the declaration, then each associative
    /// tier's sentence and reference).
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        for variant in &mut self.variants {
            variant.rekey()?;
        }
        let Some(declaration) = self.precedence_declaration_range else {
            return Ok(self);
        };
        let Some(groups) = self.precedence_groups.take() else {
            return Ok(self);
        };
        let chain = matches!(groups, EnumPrecedenceGroups::Chain(_));
        let mut groups = groups.into_vec();
        if chain && let Some(chain_range) = self.precedence_chain_range {
            let mut keys = KeyAllocator::default();
            self.precedence_declaration_key =
                Some(keys.key(ProvenanceRole::PrecedenceDeclaration, declaration)?);
            self.precedence_chain_key =
                Some(keys.key(ProvenanceRole::PrecedenceChain, chain_range)?);
            for group in &mut groups {
                group.precedence_key = Some(keys.key(
                    ProvenanceRole::PrecedenceGroupReference,
                    group.reference_range,
                )?);
            }
            self.precedence_anchors = Some(keys.into_anchors());
        }
        if groups.iter().any(|group| group.associativity.is_some()) {
            let mut keys = KeyAllocator::default();
            self.associativity_declaration_key =
                Some(keys.key(ProvenanceRole::AssociativityDeclaration, declaration)?);
            for group in &mut groups {
                if group.associativity.is_none() {
                    continue;
                }
                group.associativity_keys = Some(AssociativityKeys {
                    sentence: keys.key(ProvenanceRole::AssociativitySentence, group.range)?,
                    reference: keys.key(
                        ProvenanceRole::AssociativityGroupReference,
                        group.reference_range,
                    )?,
                });
            }
            self.associativity_anchors = Some(keys.into_anchors());
        }
        self.precedence_groups = EnumPrecedenceGroups::from_vec(groups);
        Ok(self)
    }

    /// The key of the precedence chain's declaration, when the family has
    /// a chain.
    #[must_use]
    pub const fn precedence_declaration_key(&self) -> Option<&ProvenanceKey> {
        self.precedence_declaration_key.as_ref()
    }

    /// The key of the precedence chain.
    #[must_use]
    pub const fn precedence_chain_key(&self) -> Option<&ProvenanceKey> {
        self.precedence_chain_key.as_ref()
    }

    /// The key of the associativity declaration, when a tier is
    /// associative.
    #[must_use]
    pub const fn associativity_declaration_key(&self) -> Option<&ProvenanceKey> {
        self.associativity_declaration_key.as_ref()
    }

    /// Returns the indices, in [`Self::variants`], of the cons and the empty
    /// variant of a `#[k::cons_list]` enum (F6).
    #[must_use]
    pub const fn cons_list(&self) -> Option<(usize, usize)> {
        self.cons_list
    }

    /// Returns the span-preserving Rust enum after consuming only KRS helper
    /// attributes.
    #[must_use]
    pub const fn item(&self) -> &ItemEnum {
        &self.item
    }

    /// Returns the enum identifier, which names the family's generated
    /// precedence groups and keys; it is not a sort.
    #[must_use]
    pub const fn enum_name(&self) -> &Ident {
        &self.item.ident
    }

    /// Returns the authored sort every variant constructs.
    #[must_use]
    pub const fn sort(&self) -> &Path {
        &self.sort
    }

    /// Returns constructor variants in Rust declaration order.
    #[must_use]
    pub fn variants(&self) -> &[EnumConstructorVariant] {
        &self.variants
    }

    /// Whether this is a fully materialized deterministic-reference family.
    #[must_use]
    pub const fn is_reference_family(&self) -> bool {
        self.reference_family
    }

    /// Returns exhaustive precedence groups in tightest-to-weakest order; none
    /// when the family has no chain.
    pub fn precedence_groups(&self) -> impl Iterator<Item = &EnumPrecedenceGroup> {
        self.precedence_groups
            .iter()
            .flat_map(EnumPrecedenceGroups::iter)
    }

    /// Returns the precedence chain when at least two groups exist.
    #[must_use]
    pub const fn precedence_chain_groups(&self) -> Option<&AtLeastTwo<EnumPrecedenceGroup>> {
        match &self.precedence_groups {
            Some(EnumPrecedenceGroups::Chain(groups)) => Some(groups),
            Some(EnumPrecedenceGroups::Single(_)) | None => None,
        }
    }

    /// Returns complete production provenance, including its exact member
    /// reference in the exhaustive enum-level chain.
    ///
    /// # Errors
    ///
    /// None: the family was keyed when it was parsed.
    pub fn variant_provenance(
        &self,
        variant: &EnumConstructorVariant,
    ) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        variant.provenance()
    }

    /// Returns precedence declaration provenance derived from the exhaustive
    /// enum-level chain, when at least two groups exist.
    ///
    /// # Errors
    ///
    /// None: the family was keyed when it was parsed.
    pub fn precedence_provenance(&self) -> Result<Option<Vec<ProvenanceAnchor>>, SyntaxError> {
        Ok(self
            .precedence_descriptor()?
            .map(|descriptor| descriptor.provenance))
    }

    /// Returns the refined precedence chain and its descriptor provenance.
    ///
    /// # Errors
    ///
    /// None: the family was keyed when it was parsed.
    pub fn precedence_descriptor(
        &self,
    ) -> Result<Option<EnumPrecedenceDescriptor<'_>>, SyntaxError> {
        let (Some(groups), Some(anchors)) =
            (self.precedence_chain_groups(), &self.precedence_anchors)
        else {
            return Ok(None);
        };
        Ok(Some(EnumPrecedenceDescriptor {
            groups,
            provenance: anchors.clone(),
        }))
    }

    /// Returns the associativity descriptor's anchors, when a tier is
    /// associative.
    ///
    /// # Errors
    ///
    /// None: the family was keyed when it was parsed.
    pub fn associativity_provenance(&self) -> Result<Option<Vec<ProvenanceAnchor>>, SyntaxError> {
        Ok(self.associativity_anchors.clone())
    }
}

impl KrsSyntax for EnumConstructorDeclaration {
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        Self::from_attributed_item(syn::parse2(tokens)?)
    }
}

fn parse_outer_attribute(attribute: &Attribute) -> Result<ConstructorsAttribute, SyntaxError> {
    let Meta::List(list) = &attribute.meta else {
        return Err(unsupported_enum(
            "`k::constructors` requires `(sort = Sort, result = KResult)` or `(sort = Sort, reference)`",
            attribute.span(),
        ));
    };
    ConstructorsAttribute::parse_tokens(list.tokens.clone())
}

#[derive(Clone, Debug)]
struct EnumPrecedenceChain {
    declaration_range: TokenRange,
    chain_range: TokenRange,
    groups: Vec<EnumPrecedenceGroup>,
}

#[derive(Debug)]
struct ParsedEnumPrecedenceChain {
    chain_range: TokenRange,
    groups: Vec<EnumPrecedenceGroup>,
}

impl Parse for ParsedEnumPrecedenceChain {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        if input.is_empty() {
            return Err(input.error("precedence requires at least one parenthesized variant group"));
        }
        let first_group = parse_enum_precedence_group(input)?;
        let first_span = first_group.range.first();
        let mut last_span = first_group.range.last();
        let mut groups = vec![first_group];
        while !input.is_empty() {
            input.parse::<Token![>]>().map_err(|_| {
                input.error("precedence groups must be separated by `>` (binds tighter than)")
            })?;
            if input.is_empty() {
                return Err(input.error("`>` must be followed by a precedence group"));
            }
            let group = parse_enum_precedence_group(input)?;
            last_span = group.range.last();
            groups.push(group);
        }
        Ok(Self {
            chain_range: TokenRange::new(first_span, last_span),
            groups,
        })
    }
}

fn parse_enum_precedence_group(input: ParseStream<'_>) -> syn::Result<EnumPrecedenceGroup> {
    let mut associativity = None;
    let mut name = None;
    let mut first_span = None;
    if input.peek(Ident) {
        let first: Ident = input.parse()?;
        first_span = Some(first.span());
        match first.to_string().as_str() {
            "left" => associativity = Some(GroupAssociativity::Left),
            "right" => associativity = Some(GroupAssociativity::Right),
            "non_assoc" => associativity = Some(GroupAssociativity::NonAssociative),
            _ => name = Some(first),
        }
        if name.is_none() && input.peek(Ident) {
            let group_name: Ident = input.parse()?;
            if matches!(
                group_name.to_string().as_str(),
                "left" | "right" | "non_assoc"
            ) {
                return Err(syn::Error::new(
                    group_name.span(),
                    "`left`, `right`, and `non_assoc` are reserved associativity keywords and cannot name a precedence group",
                ));
            }
            name = Some(group_name);
        }
    }

    let content;
    let parentheses = parenthesized!(content in input);
    let variants = content
        .parse_terminated(Ident::parse, Token![,])?
        .into_iter()
        .collect::<Vec<_>>();
    let Some(first_variant) = variants.first() else {
        return Err(syn::Error::new(
            parentheses.span.open(),
            "a precedence group must name at least one enum variant",
        ));
    };
    let reference_range = if let Some(name) = &name {
        TokenRange::for_tokens(name)?
    } else {
        TokenRange::for_tokens(first_variant)?
    };
    let range = TokenRange::new(
        first_span.unwrap_or_else(|| parentheses.span.open()),
        parentheses.span.close(),
    );
    Ok(EnumPrecedenceGroup {
        range,
        reference_range,
        associativity,
        name,
        variants,
        precedence_key: None,
        associativity_keys: None,
    })
}

/// The enum-level helpers `#[k::constructors]` consumes.
struct EnumHelpers {
    precedence: Option<EnumPrecedenceChain>,
    /// The `#[k::cons_list]` marker's range (F6).
    cons_list: Option<TokenRange>,
}

fn take_enum_helpers(attributes: &mut Vec<Attribute>) -> Result<EnumHelpers, SyntaxError> {
    let mut precedence = None;
    let mut cons_list = None;
    let mut retained = Vec::with_capacity(attributes.len());
    for attribute in std::mem::take(attributes) {
        if let Some(marker) = helper_marker(&attribute, "cons_list") {
            if cons_list.is_some() {
                return Err(invalid_cons_list(
                    "an enum carries one `#[k::cons_list]` attribute",
                    attribute.span(),
                ));
            }
            if !matches!(attribute.meta, Meta::Path(_)) {
                return Err(invalid_cons_list(
                    "`#[k::cons_list]` takes no arguments: the constructors' shapes say which is the empty list and which the cons",
                    attribute.span(),
                ));
            }
            cons_list = Some(TokenRange::for_tokens(marker)?);
        } else if let Some(marker) = helper_marker(&attribute, "precedence") {
            if precedence.is_some() {
                return Err(invalid_enum_precedence(
                    "a readable constructor family may declare only one precedence chain",
                    attribute.span(),
                ));
            }
            let Meta::List(list) = &attribute.meta else {
                return Err(invalid_enum_precedence(
                    "`precedence` requires one parenthesized chain payload",
                    attribute.span(),
                ));
            };
            let parsed = syn::parse2::<ParsedEnumPrecedenceChain>(list.tokens.clone())
                .map_err(SyntaxError::from)?;
            precedence = Some(EnumPrecedenceChain {
                declaration_range: TokenRange::for_tokens(marker)?,
                chain_range: parsed.chain_range,
                groups: parsed.groups,
            });
        } else if is_k_helper(&attribute) {
            return Err(unsupported_enum(
                "readable constructor-family enums support only the invoking `constructors` attribute, one enum-level `precedence` chain, and `cons_list`",
                attribute.span(),
            ));
        } else {
            retained.push(attribute);
        }
    }
    *attributes = retained;
    Ok(EnumHelpers {
        precedence,
        cons_list,
    })
}

/// Checks the shape a `#[k::cons_list]` enum declares (F6): exactly two
/// constructors, one with no field (the empty list) and one with two (the
/// head and the tail), and returns their indices, cons first. That the tail
/// has the enum's own sort is checked once sorts are resolved.
fn cons_list_shape(
    name: &Ident,
    variants: &[EnumConstructorVariant],
    range: TokenRange,
) -> Result<(usize, usize), SyntaxError> {
    const SHAPE: &str = "a cons list has one constructor with no field, the empty list, and one with two, the head and the tail";
    if let Some(variant) = variants
        .iter()
        .find(|variant| !matches!(variant.fields.len(), 0 | 2))
    {
        let count = variant.fields.len();
        return Err(invalid_cons_list(
            format!(
                "`{}` has {count} field{}: {SHAPE}",
                variant.name(),
                if count == 1 { "" } else { "s" }
            ),
            variant.name().span(),
        ));
    }
    if let [_, _, third, ..] = variants {
        return Err(invalid_cons_list(
            format!(
                "`{}` is a third constructor of `{name}`: {SHAPE}, and nothing else",
                third.name()
            ),
            third.name().span(),
        ));
    }
    match variants {
        [first, second] if first.fields.len() == second.fields.len() => {
            let shape = if first.fields.is_empty() {
                "no field"
            } else {
                "two fields"
            };
            Err(invalid_cons_list(
                format!(
                    "`{}` and `{}` both have {shape}: {SHAPE}",
                    first.name(),
                    second.name()
                ),
                second.name().span(),
            ))
        }
        [first, _] if first.fields.len() == 2 => Ok((0, 1)),
        [_, _] => Ok((1, 0)),
        _ => Err(invalid_cons_list(
            format!("`{name}` has one constructor: {SHAPE}"),
            range.first(),
        )),
    }
}

fn invalid_cons_list(reason: impl Into<String>, span: Span) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::InvalidConsList {
            reason: reason.into(),
        },
        span,
    )
}

/// A readable variant's group comes from the chain, so a family without one
/// names no group.
fn validate_chainless_groups(
    family: &Ident,
    variants: &[EnumConstructorVariant],
) -> Result<(), SyntaxError> {
    if let Some(group) = variants
        .iter()
        .find_map(|variant| variant.syntax().and_then(VariantSyntaxAttribute::group))
    {
        return Err(invalid_enum_precedence(
            format!(
                "variant group `{}` needs a chain: `{family}` has no `#[k::precedence]`, and a readable variant's group comes from it (a one-tier chain `name (A, B)` names a group)",
                group.value()
            ),
            group.span(),
        ));
    }
    Ok(())
}

/// A reference family is the materialized form of a readable one, whose
/// variants are either all grouped (a chain) or none (no chain).
fn validate_reference_groups(
    family: &Ident,
    variants: &[EnumConstructorVariant],
) -> Result<(), SyntaxError> {
    let mut syntax = variants
        .iter()
        .filter_map(|variant| variant.syntax().map(|syntax| (variant, syntax)));
    let Some((_, first)) = syntax.clone().next() else {
        return Ok(());
    };
    let grouped = first.group().is_some();
    if let Some((variant, _)) = syntax.find(|(_, syntax)| syntax.group().is_some() != grouped) {
        return Err(invalid_enum_precedence(
            format!(
                "reference family `{family}` gives `group` to some variants but not to `{}`: either every variant with `syntax` names its group or none does",
                variant.name()
            ),
            variant.name().span(),
        ));
    }
    Ok(())
}

fn validate_precedence_members(
    precedence: &EnumPrecedenceChain,
    family: &Ident,
    variants: &mut [EnumConstructorVariant],
) -> Result<(), SyntaxError> {
    let variant_indices = variants
        .iter()
        .enumerate()
        .map(|(index, variant)| (variant.name().to_string(), index))
        .collect::<BTreeMap<_, _>>();
    let variant_names = variant_indices.keys().cloned().collect::<Vec<_>>();
    let mut seen_variants = BTreeSet::new();
    let mut emitted_groups = BTreeSet::new();

    for (group_ordinal, group) in precedence.groups.iter().enumerate() {
        let emitted_name = group.emitted_name(family, group_ordinal);
        if !emitted_groups.insert(emitted_name.clone()) {
            let span = group
                .name
                .as_ref()
                .map_or_else(|| group.variants[0].span(), Ident::span);
            return Err(invalid_enum_precedence(
                format!("production-group identity `{emitted_name}` is repeated"),
                span,
            ));
        }
        for member in &group.variants {
            let name = member.to_string();
            let Some(&variant_index) = variant_indices.get(&name) else {
                let suggestion = closest_variant(&name, &variant_names)
                    .map(|candidate| format!("; did you mean `{candidate}`?"))
                    .unwrap_or_default();
                return Err(invalid_enum_precedence(
                    format!("unknown enum variant `{name}`{suggestion}"),
                    member.span(),
                ));
            };
            if !seen_variants.insert(name.clone()) {
                return Err(invalid_enum_precedence(
                    format!("enum variant `{name}` appears more than once"),
                    member.span(),
                ));
            }
            if let Some(explicit_group) = variants[variant_index]
                .syntax()
                .and_then(VariantSyntaxAttribute::group)
                && explicit_group.value() != emitted_name
            {
                return Err(invalid_enum_precedence(
                    format!(
                        "variant `{name}` materializes group `{}` but the exhaustive chain assigns `{emitted_name}`",
                        explicit_group.value()
                    ),
                    explicit_group.span(),
                ));
            }
            variants[variant_index].precedence_group = Some(group_ordinal);
            if variants[variant_index]
                .syntax()
                .and_then(VariantSyntaxAttribute::group)
                .is_none()
            {
                variants[variant_index].precedence_member_range =
                    Some(TokenRange::for_tokens(member)?);
            }
        }
    }

    if let Some(missing) = variants
        .iter()
        .find(|variant| !seen_variants.contains(&variant.name().to_string()))
    {
        return Err(invalid_enum_precedence(
            format!(
                "enum variant `{}` is missing from the exhaustive chain",
                missing.name()
            ),
            missing.name().span(),
        ));
    }
    Ok(())
}

pub(crate) fn closest_variant<'a>(unknown: &str, variants: &'a [String]) -> Option<&'a str> {
    let (candidate, distance) = variants
        .iter()
        .map(|candidate| (candidate.as_str(), edit_distance(unknown, candidate)))
        .min_by_key(|(_, distance)| *distance)?;
    let limit = unknown.chars().count().max(candidate.chars().count()) / 3 + 1;
    (distance <= limit).then_some(candidate)
}

fn edit_distance(left: &str, right: &str) -> usize {
    let right = right.chars().collect::<Vec<_>>();
    let mut previous = (0..=right.len()).collect::<Vec<_>>();
    for (left_index, left_character) in left.chars().enumerate() {
        let mut current = Vec::with_capacity(right.len() + 1);
        current.push(left_index + 1);
        for (right_index, right_character) in right.iter().enumerate() {
            let substitution =
                previous[right_index] + usize::from(left_character != *right_character);
            current.push(
                (current[right_index] + 1)
                    .min(previous[right_index + 1] + 1)
                    .min(substitution),
            );
        }
        previous = current;
    }
    previous[right.len()]
}

#[derive(Default)]
struct VariantHelpers {
    syntax: Option<VariantSyntaxAttribute>,
    format: Option<LitStr>,
    strictness: Option<VariantStrictness>,
    static_marker: Option<VariantStaticMarker>,
    symbol: Option<SymbolAttribute>,
}

/// A variant's `#[k::alias]` or `#[k::desugar]` marker (KF-028).
#[derive(Clone, Debug)]
struct VariantStaticMarker {
    range: TokenRange,
    attribute: StaticProductionAttribute,
}

struct VariantStrictness {
    kind: StrictnessKind,
    tokens: TokenStream,
    mode: VariantStrictnessMode,
}

enum VariantStrictnessMode {
    Readable { result: Path, marker: Ident },
    Reference,
}

fn variant_strictness_helper(
    attribute: &Attribute,
    family: &ConstructorFamilyMode,
) -> Option<(StrictnessKind, VariantStrictnessMode)> {
    let (kind, marker) = helper_marker(attribute, "strict")
        .map(|marker| (StrictnessKind::Strict, marker))
        .or_else(|| {
            helper_marker(attribute, "seqstrict").map(|marker| (StrictnessKind::SeqStrict, marker))
        })?;
    let mode = match family {
        ConstructorFamilyMode::Readable { result } => VariantStrictnessMode::Readable {
            result: result.clone(),
            marker: marker.clone(),
        },
        ConstructorFamilyMode::Reference => VariantStrictnessMode::Reference,
    };
    Some((kind, mode))
}

fn take_variant_helpers(
    attributes: &mut Vec<Attribute>,
    family: &ConstructorFamilyMode,
) -> Result<VariantHelpers, SyntaxError> {
    let mut helpers = VariantHelpers::default();
    let mut retained = Vec::with_capacity(attributes.len());
    for attribute in std::mem::take(attributes) {
        if is_helper_named(&attribute, "syntax") {
            if helpers.syntax.is_some() {
                return Err(unsupported_enum(
                    "an enum constructor variant may carry only one `#[k::syntax]` helper",
                    attribute.span(),
                ));
            }
            let Meta::List(list) = &attribute.meta else {
                return Err(unsupported_enum(
                    "`k::syntax` requires a parenthesized syntax template",
                    attribute.span(),
                ));
            };
            helpers.syntax = Some(VariantSyntaxAttribute::parse_tokens(list.tokens.clone())?);
        } else if is_helper_named(&attribute, "symbol") {
            helpers.symbol = Some(variant_symbol(&attribute, helpers.symbol.is_some())?);
        } else if is_helper_named(&attribute, "format") {
            if helpers.format.is_some() {
                return Err(unsupported_enum(
                    "an enum constructor variant may carry only one `#[k::format]` helper",
                    attribute.span(),
                ));
            }
            let Meta::List(list) = &attribute.meta else {
                return Err(unsupported_enum(
                    "`k::format` requires one parenthesized string literal",
                    attribute.span(),
                ));
            };
            helpers.format = Some(
                syn::parse2::<LitStr>(crate::parse::strip_trailing_comma(list.tokens.clone()))
                    .map_err(|_| {
                        unsupported_enum(
                            "`k::format` requires exactly one string literal",
                            list.tokens.span(),
                        )
                    })?,
            );
        } else if let Some((kind, mode)) = variant_strictness_helper(&attribute, family) {
            if helpers.strictness.is_some() {
                return Err(unsupported_enum(
                    "a variant may declare only one `strict` or `seqstrict` strategy",
                    attribute.span(),
                ));
            }
            let tokens = marker_tokens(&attribute)?;
            helpers.strictness = Some(VariantStrictness { kind, tokens, mode });
        } else if let Some(mode) = variant_static_mode(&attribute) {
            if let Some(previous) = &helpers.static_marker {
                return Err(unsupported_enum(
                    if previous.attribute.mode() == mode {
                        match mode {
                            StaticMode::Alias => "a variant may declare `alias` only once",
                            StaticMode::Desugar => "a variant may declare `desugar` only once",
                        }
                    } else {
                        "a production is an alias or a desugar, not both: `alias` also prints backwards, `desugar` only expands"
                    },
                    attribute
                        .path()
                        .segments
                        .last()
                        .map_or_else(|| attribute.span(), |segment| segment.ident.span()),
                ));
            }
            let (range, tokens) = match &attribute.meta {
                Meta::Path(path) => (TokenRange::for_tokens(path)?, TokenStream::new()),
                Meta::List(list) => (TokenRange::for_tokens(&list.path)?, list.tokens.clone()),
                Meta::NameValue(_) => {
                    return Err(unsupported_enum(
                        match mode {
                            StaticMode::Alias => "`alias` must use marker syntax",
                            StaticMode::Desugar => "`desugar` must use marker syntax",
                        },
                        attribute.span(),
                    ));
                }
            };
            helpers.static_marker = Some(VariantStaticMarker {
                range,
                attribute: StaticProductionAttribute::parse_marker(mode, tokens)?,
            });
        } else if is_k_helper(&attribute) {
            return Err(unsupported_enum(
                "enum constructor variants support only `syntax`, `format`, `strict`, `seqstrict`, `alias`, `desugar`, and `symbol` KRS helpers; precedence belongs on the enum",
                attribute.span(),
            ));
        } else {
            retained.push(attribute);
        }
    }
    *attributes = retained;
    Ok(helpers)
}

/// A variant's `#[k::symbol("path::Name")]` helper; `duplicate` when the
/// variant already carries one.
fn variant_symbol(attribute: &Attribute, duplicate: bool) -> Result<SymbolAttribute, SyntaxError> {
    if duplicate {
        return Err(unsupported_enum(
            "an enum constructor variant may carry only one `#[k::symbol]` helper",
            attribute.span(),
        ));
    }
    let Meta::List(list) = &attribute.meta else {
        return Err(unsupported_enum(
            "`k::symbol` requires one parenthesized string literal, such as `#[k::symbol(\"api::Name\")]`",
            attribute.span(),
        ));
    };
    SymbolAttribute::parse_tokens(list.tokens.clone())
}

fn marker_tokens(attribute: &Attribute) -> Result<TokenStream, SyntaxError> {
    match &attribute.meta {
        Meta::Path(_) => Ok(TokenStream::new()),
        Meta::List(list) => Ok(list.tokens.clone()),
        Meta::NameValue(_) => Err(unsupported_enum(
            "a constructor-family marker must use path or list syntax",
            attribute.span(),
        )),
    }
}

fn parse_variant_fields(
    fields: &Fields,
    reference_family: bool,
) -> Result<Vec<ConstructorField>, SyntaxError> {
    match fields {
        Fields::Unit => Ok(Vec::new()),
        Fields::Named(named) => {
            let mut parsed = Vec::with_capacity(named.named.len());
            for field in &named.named {
                if let Some(attribute) = first_non_doc_attribute(&field.attrs) {
                    return Err(unsupported_enum(
                        "an enum constructor field takes only doc comments",
                        attribute.span(),
                    ));
                }
                let Some(name) = field.ident.clone() else {
                    return Err(unsupported_enum(
                        "record enum constructor fields must be named",
                        field.span(),
                    ));
                };
                let term_sort = if reference_family {
                    parse_typed_term_sort(field.ty.clone())?
                } else {
                    parse_typed_readable_sort(field.ty.clone())?
                };
                parsed.push(ConstructorField {
                    field: field.clone(),
                    name,
                    term_sort,
                    parameter: None,
                    sort_key: None,
                    name_key: None,
                });
            }
            Ok(parsed)
        }
        Fields::Unnamed(fields) if fields.unnamed.is_empty() => Ok(Vec::new()),
        Fields::Unnamed(fields) => Err(unsupported_enum(
            "tuple enum constructor variants are unsupported; readable families permit only zero-field tuple variants",
            fields.span(),
        )),
    }
}

fn helper_marker<'a>(attribute: &'a Attribute, helper: &str) -> Option<&'a Ident> {
    let path = attribute.path();
    if path.segments.len() < 2 {
        return None;
    }
    path.segments
        .last()
        .filter(|segment| segment.ident == helper)
        .map(|segment| &segment.ident)
}

fn is_helper_named(attribute: &Attribute, helper: &str) -> bool {
    helper_marker(attribute, helper).is_some()
}

/// The static mode a variant helper names: `alias` or `desugar`.
fn variant_static_mode(attribute: &Attribute) -> Option<StaticMode> {
    if is_helper_named(attribute, "alias") {
        Some(StaticMode::Alias)
    } else if is_helper_named(attribute, "desugar") {
        Some(StaticMode::Desugar)
    } else {
        None
    }
}

fn is_k_helper(attribute: &Attribute) -> bool {
    const HELPERS: &[&str] = &[
        "syntax",
        "format",
        "precedence",
        "cons_list",
        "strict",
        "seqstrict",
        "constructors",
    ];
    attribute.path().segments.len() >= 2
        && (attribute
            .path()
            .segments
            .first()
            .is_some_and(|segment| segment.ident == "k")
            || attribute
                .path()
                .segments
                .last()
                .is_some_and(|segment| HELPERS.iter().any(|helper| segment.ident == helper)))
}

fn unsupported_enum(reason: &'static str, span: Span) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::UnsupportedEnumConstructorDeclaration { reason },
        span,
    )
}

fn invalid_enum_precedence(reason: impl Into<String>, span: Span) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::InvalidEnumPrecedence {
            reason: reason.into(),
        },
        span,
    )
}

#[cfg(test)]
mod keyed {
    use super::{EnumConstructorDeclaration, EnumConstructorVariant};
    use crate::keyed_nodes::KeyedNodes;
    use crate::{SortArgument, SyntaxError};

    impl EnumConstructorVariant {
        /// Records the keys of the production view: the constructed sort,
        /// the syntax attribute, the variant, each field's sort and name,
        /// each rustdoc line, the tier membership, the cons-list marker, the
        /// strictness, the static marker and its payload, and the symbol
        /// override.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            nodes.push_tokens(self.sort_key.as_ref(), &self.constructor_sort)?;
            if let Some(syntax) = &self.syntax {
                syntax.keyed_nodes(nodes)?;
            }
            nodes.push_tokens(self.key.as_ref(), &self.variant.ident)?;
            for field in &self.fields {
                nodes.push_tokens(field.sort_key.as_ref(), field.term_sort().sort())?;
                nodes.push_tokens(field.name_key.as_ref(), field.name())?;
            }
            for documentation in &self.documentation {
                nodes.push_tokens(documentation.key.as_ref(), documentation.literal())?;
            }
            if let Some(range) = self.precedence_member_range {
                nodes.push(self.group_key.as_ref(), range);
            }
            if let Some(range) = self.cons_list_range {
                nodes.push(self.cons_list_key.as_ref(), range);
            }
            if let Some(strictness) = &self.strictness {
                strictness.keyed_nodes(nodes)?;
            }
            if let Some(marker) = &self.static_marker {
                nodes.push(self.static_key.as_ref(), marker.range);
                marker.attribute.keyed_nodes(nodes);
            }
            if let Some(symbol) = &self.explicit_symbol {
                symbol.keyed_nodes(nodes)?;
            }
            Ok(())
        }

        /// Records the keys of the constructor descriptor's nodes of the
        /// production view: the constructed sort, each field's sort, and the
        /// symbol override.
        pub(crate) fn keyed_constructor_nodes(
            &self,
            nodes: &mut KeyedNodes,
        ) -> Result<(), SyntaxError> {
            nodes.push_tokens(self.sort_key.as_ref(), &self.constructor_sort)?;
            for field in &self.fields {
                nodes.push_tokens(field.sort_key.as_ref(), field.term_sort().sort())?;
            }
            if let Some(symbol) = &self.explicit_symbol {
                symbol.keyed_nodes(nodes)?;
            }
            Ok(())
        }

        /// Records the keys of the element types of the field sorts, the
        /// sentence of [`Self::argument_provenance`].
        pub(crate) fn keyed_argument_nodes(
            &self,
            nodes: &mut KeyedNodes,
        ) -> Result<(), SyntaxError> {
            for field in &self.fields {
                SortArgument::keyed_nodes(field.term_sort().arguments(), nodes)?;
            }
            Ok(())
        }
    }

    impl EnumConstructorDeclaration {
        /// Records the keys of the precedence descriptor: its declaration,
        /// the chain and each tier's reference.
        pub(crate) fn keyed_precedence_nodes(&self, nodes: &mut KeyedNodes) {
            if let Some(range) = self.precedence_declaration_range {
                nodes.push(self.precedence_declaration_key.as_ref(), range);
            }
            if let Some(range) = self.precedence_chain_range {
                nodes.push(self.precedence_chain_key.as_ref(), range);
            }
            for group in self.precedence_groups() {
                nodes.push(group.precedence_key.as_ref(), group.reference_range);
            }
        }

        /// Records the keys of the associativity descriptor: its
        /// declaration, then each associative tier's sentence and reference.
        pub(crate) fn keyed_associativity_nodes(&self, nodes: &mut KeyedNodes) {
            if let Some(range) = self.precedence_declaration_range {
                nodes.push(self.associativity_declaration_key.as_ref(), range);
            }
            for group in self.precedence_groups() {
                nodes.push(group.associativity_sentence_key(), group.range);
                nodes.push(group.associativity_reference_key(), group.reference_range);
            }
        }
    }
}
