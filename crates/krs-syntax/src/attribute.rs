use proc_macro2::{Span, TokenStream};
use quote::ToTokens;
use std::cell::RefCell;
use syn::parse::{Parse, ParseStream, Parser};
use syn::spanned::Spanned;
use syn::{Expr, ExprLit, ExprPath, Ident, Lit, LitBool, LitInt, LitStr, Path, Token};

use crate::grammar::{StructuredFormat, SyntaxTemplate};
use crate::{
    ConstructorDeclaration, ProvenanceAnchor, ProvenanceRole, SyntaxError, SyntaxErrorKind,
    TokenRange,
};

/// Checked payload of `#[k::sort]`.
///
/// The empty legacy form declares the attributed trait directly. Reference
/// Rust may instead name the public term alias represented by a generated
/// marker trait and materialize the authored semantic parent paths.
#[derive(Clone, Debug, Default)]
pub struct SortAttribute {
    alias: Option<Ident>,
    parents: Vec<Path>,
}

impl SortAttribute {
    /// Returns the reference-surface term alias represented by the marker.
    #[must_use]
    pub const fn alias(&self) -> Option<&Ident> {
        self.alias.as_ref()
    }

    /// Returns explicitly materialized semantic parent-sort paths.
    #[must_use]
    pub fn parents(&self) -> &[Path] {
        &self.parents
    }

    /// Whether this is the explicit alias-carrying reference form.
    #[must_use]
    pub const fn is_reference(&self) -> bool {
        self.alias.is_some()
    }
}

/// Checked payload of reference-surface `#[k::subsort(sort = ...)]`.
#[derive(Clone, Debug)]
pub struct SubsortAttribute {
    sort: Path,
}

impl SubsortAttribute {
    /// Returns the public semantic supersort alias populated by the impl.
    #[must_use]
    pub const fn sort(&self) -> &Path {
        &self.sort
    }
}

/// Checked payload of `#[k::symbol("...")]`.
#[derive(Clone, Debug)]
pub struct SymbolAttribute {
    literal: LitStr,
    value: krs_ir::ExplicitSymbol,
}

impl SymbolAttribute {
    /// Returns the original string literal with its authored span.
    #[must_use]
    pub const fn literal(&self) -> &LitStr {
        &self.literal
    }

    /// Returns the validated logical public symbol identity.
    #[must_use]
    pub const fn value(&self) -> &krs_ir::ExplicitSymbol {
        &self.value
    }

    /// Returns exact provenance for the authored override literal.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if the literal has no tokens.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(vec![ProvenanceAnchor::new(
            ProvenanceRole::StableSymbol,
            0,
            TokenRange::for_tokens(&self.literal)?,
        )])
    }
}

/// Validated empty payload of `#[k::equation]`.
#[derive(Clone, Copy, Debug, Default)]
pub struct EquationAttribute;

/// Checked payload of `#[k::simplification]` or `#[k::simplification(priority = N)]`.
#[derive(Clone, Debug, Default)]
pub struct SimplificationAttribute {
    priority: Option<(LitInt, u32)>,
}

impl SimplificationAttribute {
    /// Returns the optional simplifier ordering hint.
    #[must_use]
    pub fn priority(&self) -> Option<u32> {
        self.priority.as_ref().map(|(_, value)| *value)
    }

    /// Returns exact provenance for an authored priority literal.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if an authored literal has no tokens.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        self.priority
            .as_ref()
            .map(|(literal, _)| {
                TokenRange::for_tokens(literal).map(|range| {
                    vec![ProvenanceAnchor::new(
                        ProvenanceRole::SimplificationPriority,
                        0,
                        range,
                    )]
                })
            })
            .transpose()
            .map(Option::unwrap_or_default)
    }
}

/// Validated empty payload of `#[k::alias]`.
#[derive(Clone, Copy, Debug, Default)]
pub struct AliasAttribute;

/// Checked payload of `#[k::context_alias(name = alias, here = binding)]`.
#[derive(Clone, Debug)]
pub struct ContextAliasAttribute {
    name: Ident,
    here: Ident,
}

impl ContextAliasAttribute {
    /// Returns the shared, target-neutral context-alias name.
    #[must_use]
    pub const fn name(&self) -> &Ident {
        &self.name
    }

    /// Returns the function binding designated as the alias's `HERE` node.
    #[must_use]
    pub const fn here(&self) -> &Ident {
        &self.here
    }

    /// Returns exact anchors for the authored alias name and `HERE` binding.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if a parsed identifier emits no tokens.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(vec![
            ProvenanceAnchor::new(
                ProvenanceRole::ContextAliasName,
                0,
                TokenRange::for_tokens(&self.name)?,
            ),
            ProvenanceAnchor::new(
                ProvenanceRole::ContextAliasHere,
                0,
                TokenRange::for_tokens(&self.here)?,
            ),
        ])
    }
}

/// Explicit numeric equation priority.
#[derive(Clone, Debug)]
pub struct PriorityAttribute {
    literal: LitInt,
    value: u32,
}

impl PriorityAttribute {
    /// Returns the parsed priority.
    #[must_use]
    pub const fn value(&self) -> u32 {
        self.value
    }
    /// Returns exact literal provenance.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if the literal has no tokens.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(vec![ProvenanceAnchor::new(
            ProvenanceRole::EquationPriority,
            0,
            TokenRange::for_tokens(&self.literal)?,
        )])
    }
}

impl Parse for SortAttribute {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        parse_sort_stream(input).map_err(|error| match error {
            ParseConstructorError::Structured(error) => error.into_syn_error(),
            ParseConstructorError::Syn(error) => error,
        })
    }
}

impl Parse for SubsortAttribute {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        parse_subsort_stream(input).map_err(|error| match error {
            ParseConstructorError::Structured(error) => error.into_syn_error(),
            ParseConstructorError::Syn(error) => error,
        })
    }
}

impl Parse for ContextAliasAttribute {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        parse_context_alias_stream(input).map_err(|error| match error {
            ParseConstructorError::Structured(error) => error.into_syn_error(),
            ParseConstructorError::Syn(error) => error,
        })
    }
}

/// Optional explicit emitted label of `#[k::rule(label = "...")]`.
#[derive(Clone, Debug, Default)]
pub struct RuleAttribute {
    label: Option<LitStr>,
}

/// Explicit reachability modality of a Rust-authored claim.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ClaimModality {
    /// K's default all-path reachability claim.
    AllPaths,
    /// One-path reachability claim.
    OnePath,
}

/// Checked payload of `#[k::claim(...)]`.
#[derive(Clone, Debug)]
pub struct ClaimAttribute {
    modality: ClaimModality,
    modality_ident: Ident,
    label: LitStr,
    circularity: Option<Ident>,
}

impl ClaimAttribute {
    /// Returns the exactly one authored modality.
    #[must_use]
    pub const fn modality(&self) -> ClaimModality {
        self.modality
    }
    /// Returns the required explicit label.
    #[must_use]
    pub const fn label(&self) -> &LitStr {
        &self.label
    }
    /// Whether the claim carries the circularity modifier.
    #[must_use]
    pub const fn circularity(&self) -> bool {
        self.circularity.is_some()
    }
    /// Returns exact payload-token provenance.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error if an authored token has no recoverable range.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = vec![
            ProvenanceAnchor::new(
                ProvenanceRole::ClaimModality,
                0,
                TokenRange::for_tokens(&self.modality_ident)?,
            ),
            ProvenanceAnchor::new(
                ProvenanceRole::ClaimLabel,
                0,
                TokenRange::for_tokens(&self.label)?,
            ),
        ];
        if let Some(marker) = &self.circularity {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ClaimCircularity,
                0,
                TokenRange::for_tokens(marker)?,
            ));
        }
        Ok(anchors)
    }
}

/// One binder declared by `#[k::exists(name: Sort, ...)]`.
#[derive(Clone, Debug)]
pub struct ClaimBinder {
    name: Ident,
    sort: Path,
}

impl ClaimBinder {
    /// Returns the source binder name.
    #[must_use]
    pub const fn name(&self) -> &Ident {
        &self.name
    }
    /// Returns the Rust-resolved sort path.
    #[must_use]
    pub const fn sort(&self) -> &Path {
        &self.sort
    }
}

/// Checked existential-binder helper payload.
#[derive(Clone, Debug)]
pub struct ExistsAttribute {
    binders: Vec<ClaimBinder>,
}

impl ExistsAttribute {
    /// Returns declared binders in source order.
    #[must_use]
    pub fn binders(&self) -> &[ClaimBinder] {
        &self.binders
    }
    /// Returns exact declaration/name/sort anchors.
    ///
    /// # Errors
    ///
    /// Returns an endpoint or occurrence-overflow error if exact provenance
    /// cannot be represented.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut output = Vec::new();
        for (index, binder) in self.binders.iter().enumerate() {
            let ordinal = u32::try_from(index).map_err(|_| {
                SyntaxError::new(
                    SyntaxErrorKind::TooManyProvenanceOccurrences {
                        role: "claim_existential_binder",
                    },
                    binder.name.span(),
                )
            })?;
            output.push(ProvenanceAnchor::new(
                ProvenanceRole::ClaimExistentialBinder,
                ordinal,
                TokenRange::for_tokens(&binder.name)?,
            ));
            output.push(ProvenanceAnchor::new(
                ProvenanceRole::ClaimBinderName,
                ordinal,
                TokenRange::for_tokens(&binder.name)?,
            ));
            output.push(ProvenanceAnchor::new(
                ProvenanceRole::ClaimBinderSort,
                ordinal,
                TokenRange::for_tokens(&binder.sort)?,
            ));
        }
        Ok(output)
    }
}

impl RuleAttribute {
    /// Returns the explicit emitted K label, when authored.
    #[must_use]
    pub const fn label(&self) -> Option<&LitStr> {
        self.label.as_ref()
    }

    /// Returns the exact explicit-label provenance anchor.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if the parsed literal emits no tokens.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        self.label
            .as_ref()
            .map(|label| {
                TokenRange::for_tokens(label)
                    .map(|range| vec![ProvenanceAnchor::new(ProvenanceRole::RuleLabel, 0, range)])
            })
            .transpose()
            .map(Option::unwrap_or_default)
    }
}

impl Parse for RuleAttribute {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        parse_rule_stream(input).map_err(|error| match error {
            ParseConstructorError::Structured(error) => error.into_syn_error(),
            ParseConstructorError::Syn(error) => error,
        })
    }
}

/// Parses the frozen explicit claim metadata contract.
///
/// # Errors
///
/// Rejects missing, duplicate, unknown, or incompatible claim arguments and
/// labels outside the portable K label subset.
pub fn parse_claim_attribute(tokens: TokenStream) -> Result<ClaimAttribute, SyntaxError> {
    let parser = |input: ParseStream<'_>| -> syn::Result<ClaimAttribute> {
        let mut modality = None;
        let mut label = None;
        let mut circularity = None;
        while !input.is_empty() {
            let key: Ident = input.parse()?;
            match key.to_string().as_str() {
                "all_paths" | "one_path" => {
                    if modality.is_some() {
                        return Err(syn::Error::new(
                            key.span(),
                            "a claim requires exactly one modality",
                        ));
                    }
                    let value = if key == "all_paths" {
                        ClaimModality::AllPaths
                    } else {
                        ClaimModality::OnePath
                    };
                    modality = Some((value, key));
                }
                "label" => {
                    if label.is_some() {
                        return Err(syn::Error::new(key.span(), "duplicate claim label"));
                    }
                    input.parse::<Token![=]>()?;
                    let literal: LitStr = input.parse()?;
                    if !valid_claim_label(&literal.value()) {
                        return Err(syn::Error::new(
                            literal.span(),
                            "invalid portable K claim label",
                        ));
                    }
                    label = Some(literal);
                }
                "circularity" => {
                    if circularity.is_some() {
                        return Err(syn::Error::new(
                            key.span(),
                            "duplicate circularity modifier",
                        ));
                    }
                    circularity = Some(key);
                }
                _ => return Err(syn::Error::new(key.span(), "unknown claim argument")),
            }
            if input.is_empty() {
                break;
            }
            input.parse::<Token![,]>()?;
        }
        let (modality, modality_ident) =
            modality.ok_or_else(|| input.error("claim requires `all_paths` or `one_path`"))?;
        let label =
            label.ok_or_else(|| input.error("claim requires an explicit `label = \"...\"`"))?;
        if modality == ClaimModality::OnePath
            && let Some(circularity) = &circularity
        {
            return Err(syn::Error::new(
                circularity.span(),
                "circularity is valid only on an all-path claim",
            ));
        }
        Ok(ClaimAttribute {
            modality,
            modality_ident,
            label,
            circularity,
        })
    };
    parser.parse2(tokens).map_err(SyntaxError::from)
}

fn valid_claim_label(value: &str) -> bool {
    !value.trim().is_empty()
        && !value.chars().any(char::is_whitespace)
        && !value.contains(['[', ']', ':'])
}

/// Parses claim metadata from source text.
///
/// # Errors
///
/// Returns the same errors as [`parse_claim_attribute`], plus tokenization
/// errors for malformed Rust source.
pub fn parse_claim_attribute_source(source: &str) -> Result<ClaimAttribute, SyntaxError> {
    parse_claim_attribute(parse_source_tokens(source)?)
}

/// Parses one or more typed existential binders.
///
/// # Errors
///
/// Rejects an empty payload, duplicate names, and malformed `name: Sort`
/// entries.
pub fn parse_exists_attribute(tokens: TokenStream) -> Result<ExistsAttribute, SyntaxError> {
    let parser = |input: ParseStream<'_>| -> syn::Result<ExistsAttribute> {
        let mut binders = Vec::new();
        while !input.is_empty() {
            let name: Ident = input.parse()?;
            input.parse::<Token![:]>()?;
            let sort: Path = input.parse()?;
            if binders
                .iter()
                .any(|binder: &ClaimBinder| binder.name == name)
            {
                return Err(syn::Error::new(name.span(), "duplicate existential binder"));
            }
            binders.push(ClaimBinder { name, sort });
            if input.is_empty() {
                break;
            }
            input.parse::<Token![,]>()?;
        }
        if binders.is_empty() {
            return Err(input.error("exists requires at least one `name: Sort` binder"));
        }
        Ok(ExistsAttribute { binders })
    };
    parser.parse2(tokens).map_err(SyntaxError::from)
}

/// Parses existential binders from source text.
///
/// # Errors
///
/// Returns the same errors as [`parse_exists_attribute`], plus tokenization
/// errors for malformed Rust source.
pub fn parse_exists_attribute_source(source: &str) -> Result<ExistsAttribute, SyntaxError> {
    parse_exists_attribute(parse_source_tokens(source)?)
}

/// Generated-top or explicit named-root configuration metadata.
#[derive(Clone, Debug)]
pub struct ConfigurationAttribute {
    root: Option<LitStr>,
}

impl ConfigurationAttribute {
    /// Returns the authored K root-cell name literal.
    ///
    /// # Panics
    ///
    /// Panics for a generated-top configuration. Schema-v3 consumers should
    /// use [`Self::optional_root`] when either root policy is accepted.
    #[must_use]
    pub fn root(&self) -> &LitStr {
        self.root
            .as_ref()
            .expect("generated-top configurations have no named root")
    }

    /// Returns the optional authored root without assuming named-root policy.
    #[must_use]
    pub const fn optional_root(&self) -> Option<&LitStr> {
        self.root.as_ref()
    }

    /// Whether the frontend should use K's generated top cell.
    #[must_use]
    pub const fn is_generated_top(&self) -> bool {
        self.root.is_none()
    }

    /// Returns the canonical root-name anchor.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if the parsed literal emits no tokens.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        self.root
            .as_ref()
            .map(|root| {
                TokenRange::for_tokens(root).map(|range| {
                    vec![ProvenanceAnchor::new(
                        ProvenanceRole::ConfigurationRoot,
                        0,
                        range,
                    )]
                })
            })
            .transpose()
            .map(Option::unwrap_or_default)
    }
}

/// Classified payload of `#[k::cell(name = "...", color = "...")]`.
#[derive(Clone, Debug, Default)]
pub struct CellAttributePayload {
    name: Option<LitStr>,
    color: Option<LitStr>,
}

impl CellAttributePayload {
    /// Optional exact emitted cell name.
    #[must_use]
    pub const fn name(&self) -> Option<&LitStr> {
        self.name.as_ref()
    }

    /// Optional target-neutral cell color.
    #[must_use]
    pub const fn color(&self) -> Option<&LitStr> {
        self.color.as_ref()
    }

    /// Returns exact value anchors in stable name-then-color order.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if an authored literal has no leaves.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = Vec::with_capacity(2);
        if let Some(name) = &self.name {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConfigurationCellName,
                0,
                TokenRange::for_tokens(name)?,
            ));
        }
        if let Some(color) = &self.color {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConfigurationCellColor,
                0,
                TokenRange::for_tokens(color)?,
            ));
        }
        Ok(anchors)
    }
}

impl Parse for ConfigurationAttribute {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        parse_configuration_stream(input).map_err(|error| match error {
            ParseConstructorError::Structured(error) => error.into_syn_error(),
            ParseConstructorError::Syn(error) => error,
        })
    }
}

/// Validated empty payload of `#[k::init]`.
#[derive(Clone, Copy, Debug, Default)]
pub struct InitAttribute;

impl Parse for InitAttribute {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        parse_empty_attribute(input, "init")?;
        Ok(Self)
    }
}

/// M1 arguments of `#[k::constructor(...)]`.
#[derive(Clone, Debug)]
pub struct ConstructorAttribute {
    /// Required Rust-resolved sort trait path.
    pub sort: Path,
    /// Optional checked concrete-syntax template literal.
    pub syntax: Option<LitStr>,
    /// Optional stable production-group name.
    pub group: Option<LitStr>,
    /// Typed K parser preference.
    pub avoid: bool,
    /// Optional authored structured-format literal.
    pub format: Option<LitStr>,
    syntax_template: Option<SyntaxTemplate>,
    structured_format: Option<StructuredFormat>,
    avoid_literal: Option<LitBool>,
}

/// Arguments of `#[k::function(total, sort = ..., syntax = "...")]`.
#[derive(Clone, Debug)]
pub struct FunctionAttribute {
    constructor: ConstructorAttribute,
    totality: FunctionTotality,
}

/// Explicit K function definedness.
#[derive(Clone, Debug)]
pub enum FunctionTotality {
    /// Function equations must cover every input.
    Total(Ident),
    /// Function equations may be guarded or incomplete.
    Partial(Ident),
}

impl FunctionAttribute {
    /// Returns the shared checked production arguments.
    #[must_use]
    pub const fn production(&self) -> &ConstructorAttribute {
        &self.constructor
    }

    /// Whether the authored function is total.
    #[must_use]
    pub const fn is_total(&self) -> bool {
        matches!(self.totality, FunctionTotality::Total(_))
    }

    /// Returns complete production and totality provenance.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if a parsed token-bearing node emits no
    /// leaves.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = self.constructor.m3a_provenance()?;
        let (role, marker) = match &self.totality {
            FunctionTotality::Total(marker) => (ProvenanceRole::FunctionTotal, marker),
            FunctionTotality::Partial(marker) => (ProvenanceRole::FunctionPartial, marker),
        };
        anchors.push(ProvenanceAnchor::new(
            role,
            0,
            TokenRange::for_tokens(marker)?,
        ));
        Ok(anchors)
    }
}

impl Parse for FunctionAttribute {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        parse_function_stream(input).map_err(|error| match error {
            ParseConstructorError::Structured(error) => error.into_syn_error(),
            ParseConstructorError::Syn(error) => error,
        })
    }
}

/// Checked payload of `#[k::constructors(sort = ...[, result = ...])]`.
///
/// Without `result`, the attributed enum retains the legacy closed-sort
/// behavior and `sort` is its membership supersort. With `result`, the enum is
/// only a Rust authoring family: every variant constructs `sort` directly and
/// `result` is inherited by readable strictness helpers. The mutually
/// exclusive bare `reference` marker selects the materialized open-family
/// layer-2 form, where each variant already carries explicit metadata.
#[derive(Clone, Debug)]
pub struct ConstructorsAttribute {
    sort: Path,
    result: Option<Path>,
    reference: bool,
}

impl ConstructorsAttribute {
    /// Returns the authored outer membership-sort path.
    #[must_use]
    pub const fn sort(&self) -> &Path {
        &self.sort
    }

    /// Returns the inherited strictness-result sort in readable open-family
    /// mode.
    #[must_use]
    pub const fn result(&self) -> Option<&Path> {
        self.result.as_ref()
    }

    /// Whether this is the materialized reference-family form.
    #[must_use]
    pub const fn is_reference(&self) -> bool {
        self.reference
    }

    /// Whether variants construct the outer sort directly.
    #[must_use]
    pub const fn is_open_family(&self) -> bool {
        self.result.is_some() || self.reference
    }
}

impl Parse for ConstructorsAttribute {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        parse_constructors_stream(input).map_err(|error| match error {
            ParseConstructorError::Structured(error) => error.into_syn_error(),
            ParseConstructorError::Syn(error) => error,
        })
    }
}

/// Checked production metadata carried by an enum variant's `#[k::syntax]`.
///
/// The first positional string is the concrete-syntax template. The optional
/// keyed arguments intentionally match the production metadata accepted by a
/// struct constructor: `group`, `avoid`, and `format`.
#[derive(Clone, Debug)]
pub struct VariantSyntaxAttribute {
    syntax: LitStr,
    group: Option<LitStr>,
    avoid: bool,
    format: Option<LitStr>,
    syntax_template: SyntaxTemplate,
    structured_format: Option<StructuredFormat>,
    avoid_literal: Option<LitBool>,
}

impl VariantSyntaxAttribute {
    /// Returns the authored syntax literal.
    #[must_use]
    pub const fn syntax(&self) -> &LitStr {
        &self.syntax
    }

    /// Returns the checked syntax template.
    #[must_use]
    pub const fn syntax_template(&self) -> &SyntaxTemplate {
        &self.syntax_template
    }

    /// Returns the optional stable production-group name.
    #[must_use]
    pub const fn group(&self) -> Option<&LitStr> {
        self.group.as_ref()
    }

    /// Returns whether the production carries K's parser `avoid` preference.
    #[must_use]
    pub const fn avoid(&self) -> bool {
        self.avoid
    }

    /// Returns the authored structured-format literal, when present.
    #[must_use]
    pub const fn format(&self) -> Option<&LitStr> {
        self.format.as_ref()
    }

    /// Returns the parsed structured unparse format, when present.
    #[must_use]
    pub const fn structured_format(&self) -> Option<&StructuredFormat> {
        self.structured_format.as_ref()
    }

    pub(crate) fn apply_readable_format(
        &mut self,
        explicit: Option<LitStr>,
    ) -> Result<(), SyntaxError> {
        let (literal, controls) =
            explicit.map_or_else(|| (self.syntax.clone(), false), |literal| (literal, true));
        self.format = Some(literal.clone());
        self.structured_format = Some(StructuredFormat::parse_named(
            literal,
            &self.syntax_template,
            controls,
        )?);
        Ok(())
    }

    /// Checks template fields and structured-format positions.
    ///
    /// # Errors
    ///
    /// Rejects an unknown, omitted, or repeated field and an out-of-range
    /// structured-format item position.
    pub fn validate_fields<'a>(
        &self,
        fields: impl IntoIterator<Item = &'a Ident>,
    ) -> Result<(), SyntaxError> {
        self.syntax_template.validate_fields(fields)?;
        if let Some(format) = &self.structured_format {
            format.validate_item_count(self.syntax_template.items().len())?;
        }
        Ok(())
    }

    /// Returns the variant production's syntax and metadata anchors.
    ///
    /// The result does not contain the result-sort, declaration, or field
    /// anchors; [`crate::EnumConstructorVariant::provenance`] supplies those.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if a parsed token-bearing node emits no
    /// leaves.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = vec![ProvenanceAnchor::new(
            ProvenanceRole::ConstructorSyntax,
            0,
            TokenRange::for_tokens(&self.syntax)?,
        )];
        anchors.extend(self.syntax_template.provenance(
            ProvenanceRole::ConstructorSyntaxItem,
            ProvenanceRole::ConstructorSyntaxFieldReference,
        )?);
        if let Some(group) = &self.group {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConstructorGroup,
                0,
                TokenRange::for_tokens(group)?,
            ));
        }
        if let Some(avoid) = &self.avoid_literal {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConstructorAvoid,
                0,
                TokenRange::for_tokens(avoid)?,
            ));
        }
        if let Some(format) = &self.structured_format {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConstructorFormat,
                0,
                TokenRange::for_tokens(format.literal())?,
            ));
            anchors.extend(format.provenance(ProvenanceRole::ConstructorFormatFragment)?);
        }
        Ok(anchors)
    }
}

impl ConstructorAttribute {
    /// Returns the checked syntax template, when explicitly authored.
    #[must_use]
    pub const fn syntax_template(&self) -> Option<&SyntaxTemplate> {
        self.syntax_template.as_ref()
    }

    /// Returns the checked structured unparse format, when authored.
    #[must_use]
    pub const fn structured_format(&self) -> Option<&StructuredFormat> {
        self.structured_format.as_ref()
    }

    /// Checks field placeholders and format item positions against a nominal
    /// constructor declaration.
    ///
    /// # Errors
    ///
    /// Rejects unknown, omitted, or repeated fields and out-of-range format
    /// positions. An explicit format currently requires explicit syntax.
    pub fn validate_declaration(
        &self,
        declaration: &ConstructorDeclaration,
    ) -> Result<(), SyntaxError> {
        if let Some(template) = &self.syntax_template {
            template.validate_fields(
                declaration
                    .fields()
                    .iter()
                    .map(crate::ConstructorField::name),
            )?;
        }
        if let Some(format) = &self.structured_format {
            let Some(template) = &self.syntax_template else {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::InvalidFormat {
                        reason: "an explicit format requires an explicit syntax template",
                    },
                    format.literal().span(),
                ));
            };
            format.validate_item_count(template.items().len())?;
        }
        Ok(())
    }

    /// Returns canonical anchors in descriptor field order.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if a parsed Rust node emits no tokens.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = vec![ProvenanceAnchor::new(
            ProvenanceRole::ConstructorSort,
            0,
            TokenRange::for_tokens(&self.sort)?,
        )];
        if let Some(syntax) = &self.syntax {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConstructorSyntax,
                0,
                TokenRange::for_tokens(syntax)?,
            ));
        }
        Ok(anchors)
    }

    /// Returns the complete M3A anchor catalog while preserving the compact
    /// M1 [`Self::provenance`] result for protocol-v5 consumers.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if a parsed Rust node emits no tokens.
    pub fn m3a_provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = self.provenance()?;
        if let Some(template) = &self.syntax_template {
            anchors.extend(template.provenance(
                ProvenanceRole::ConstructorSyntaxItem,
                ProvenanceRole::ConstructorSyntaxFieldReference,
            )?);
        }
        if let Some(group) = &self.group {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConstructorGroup,
                0,
                TokenRange::for_tokens(group)?,
            ));
        }
        if let Some(avoid) = &self.avoid_literal {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConstructorAvoid,
                0,
                TokenRange::for_tokens(avoid)?,
            ));
        }
        if let Some(format) = &self.structured_format {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConstructorFormat,
                0,
                TokenRange::for_tokens(format.literal())?,
            ));
            anchors.extend(format.provenance(ProvenanceRole::ConstructorFormatFragment)?);
        }
        Ok(anchors)
    }
}

impl Parse for ConstructorAttribute {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        parse_constructor_stream(input).map_err(|error| match error {
            ParseConstructorError::Structured(error) => error.into_syn_error(),
            ParseConstructorError::Syn(error) => error,
        })
    }
}

/// Parses a legacy empty or explicit reference sort-attribute payload.
///
/// # Errors
///
/// Rejects unknown, repeated, or incorrectly typed arguments and requires
/// `alias` whenever `parents` is present.
pub fn parse_sort_attribute(tokens: TokenStream) -> Result<SortAttribute, SyntaxError> {
    parse_structured_attribute(tokens, parse_sort_stream)
}

/// Parses a sort-attribute payload directly from source text.
///
/// # Errors
///
/// Returns the same failures as [`parse_sort_attribute`], plus tokenization
/// failures.
pub fn parse_sort_attribute_source(source: &str) -> Result<SortAttribute, SyntaxError> {
    parse_sort_attribute(parse_source_tokens(source)?)
}

/// Parses the explicit supersort alias carried by a reference subsort impl.
///
/// # Errors
///
/// Requires exactly one plain Rust path-valued `sort` argument and rejects
/// missing, unknown, repeated, or incorrectly typed arguments.
pub fn parse_subsort_attribute(tokens: TokenStream) -> Result<SubsortAttribute, SyntaxError> {
    parse_structured_attribute(tokens, parse_subsort_stream)
}

/// Parses a reference subsort-attribute payload from source text.
///
/// # Errors
///
/// Returns the same failures as [`parse_subsort_attribute`].
pub fn parse_subsort_attribute_source(source: &str) -> Result<SubsortAttribute, SyntaxError> {
    parse_subsort_attribute(parse_source_tokens(source)?)
}

/// Parses exactly one string literal as a stable public symbol identity.
///
/// # Errors
///
/// Rejects missing or additional tokens, non-string values, and malformed
/// logical symbol paths.
pub fn parse_symbol_attribute(tokens: TokenStream) -> Result<SymbolAttribute, SyntaxError> {
    let parser = |input: ParseStream<'_>| -> syn::Result<SymbolAttribute> {
        let literal: LitStr = input.parse()?;
        if !input.is_empty() {
            return Err(input.error("symbol accepts exactly one string literal"));
        }
        let value = krs_ir::ExplicitSymbol::new(literal.value())
            .map_err(|error| syn::Error::new(literal.span(), error))?;
        Ok(SymbolAttribute { literal, value })
    };
    parser.parse2(tokens).map_err(SyntaxError::from)
}

/// Parses an explicit stable symbol identity from source text.
///
/// # Errors
///
/// Returns the same failures as [`parse_symbol_attribute`].
pub fn parse_symbol_attribute_source(source: &str) -> Result<SymbolAttribute, SyntaxError> {
    parse_symbol_attribute(parse_source_tokens(source)?)
}

/// Parses the intentionally empty equation payload.
///
/// # Errors
///
/// Rejects labels and every other payload at its first token.
pub fn parse_equation_attribute(tokens: TokenStream) -> Result<EquationAttribute, SyntaxError> {
    parse_empty_tokens(tokens, "equation").map(|()| EquationAttribute)
}

/// Parses an equation payload from source text.
///
/// # Errors
///
/// Returns the same failures as [`parse_equation_attribute`].
pub fn parse_equation_attribute_source(source: &str) -> Result<EquationAttribute, SyntaxError> {
    parse_equation_attribute(parse_source_tokens(source)?)
}

/// Parses an empty simplification payload or exactly `priority = N`.
///
/// # Errors
///
/// Rejects unknown, malformed, repeated, or out-of-range payloads.
pub fn parse_simplification_attribute(
    tokens: TokenStream,
) -> Result<SimplificationAttribute, SyntaxError> {
    let parser = |input: ParseStream<'_>| -> syn::Result<SimplificationAttribute> {
        if input.is_empty() {
            return Ok(SimplificationAttribute::default());
        }
        let key: Ident = input.parse()?;
        if key != "priority" {
            return Err(syn::Error::new(key.span(), "expected `priority = N`"));
        }
        input.parse::<Token![=]>()?;
        let literal: LitInt = input.parse()?;
        if !input.is_empty() {
            return Err(input.error("simplification accepts only `priority = N`"));
        }
        let value = literal.base10_parse::<u32>()?;
        Ok(SimplificationAttribute {
            priority: Some((literal, value)),
        })
    };
    parser.parse2(tokens).map_err(SyntaxError::from)
}

/// Parses a simplification payload from source text.
///
/// # Errors
///
/// Returns the same failures as [`parse_simplification_attribute`].
pub fn parse_simplification_attribute_source(
    source: &str,
) -> Result<SimplificationAttribute, SyntaxError> {
    parse_simplification_attribute(parse_source_tokens(source)?)
}

/// Parses the intentionally empty alias payload.
///
/// # Errors
///
/// Rejects recursive mode and every other payload at its first token.
pub fn parse_alias_attribute(tokens: TokenStream) -> Result<AliasAttribute, SyntaxError> {
    parse_empty_tokens(tokens, "alias").map(|()| AliasAttribute)
}

/// Parses an alias payload from source text.
///
/// # Errors
///
/// Returns the same failures as [`parse_alias_attribute`].
pub fn parse_alias_attribute_source(source: &str) -> Result<AliasAttribute, SyntaxError> {
    parse_alias_attribute(parse_source_tokens(source)?)
}

/// Parses a checked context-alias payload.
///
/// # Errors
///
/// Requires exactly one unqualified identifier for each of `name` and `here`,
/// and rejects unknown or repeated arguments at their own tokens.
pub fn parse_context_alias_attribute(
    tokens: TokenStream,
) -> Result<ContextAliasAttribute, SyntaxError> {
    parse_structured_attribute(tokens, parse_context_alias_stream)
}

/// Parses a context-alias payload directly from source text.
///
/// # Errors
///
/// Returns the same failures as [`parse_context_alias_attribute`].
pub fn parse_context_alias_attribute_source(
    source: &str,
) -> Result<ContextAliasAttribute, SyntaxError> {
    parse_context_alias_attribute(parse_source_tokens(source)?)
}

/// Parses one exact unsigned equation priority.
///
/// # Errors
///
/// Rejects missing, noninteger, repeated, or out-of-range values.
pub fn parse_priority_attribute(tokens: TokenStream) -> Result<PriorityAttribute, SyntaxError> {
    let parser = |input: ParseStream<'_>| -> syn::Result<PriorityAttribute> {
        let literal: LitInt = input.parse()?;
        if !input.is_empty() {
            return Err(input.error("priority accepts exactly one integer"));
        }
        let value = literal.base10_parse::<u32>()?;
        Ok(PriorityAttribute { literal, value })
    };
    parser.parse2(tokens).map_err(SyntaxError::from)
}

/// Parses an equation priority from source text.
///
/// # Errors
///
/// Returns the same failures as [`parse_priority_attribute`].
pub fn parse_priority_attribute_source(source: &str) -> Result<PriorityAttribute, SyntaxError> {
    parse_priority_attribute(parse_source_tokens(source)?)
}

/// Parses an optional explicit rule-label payload.
///
/// # Errors
///
/// Accepts empty payloads and exactly `label = "..."`.
pub fn parse_rule_attribute(tokens: TokenStream) -> Result<RuleAttribute, SyntaxError> {
    parse_structured_attribute(tokens, parse_rule_stream)
}

/// Parses a rule-attribute payload directly from source text.
///
/// # Errors
///
/// Returns a structured error for invalid payloads or tokenization failures.
pub fn parse_rule_attribute_source(source: &str) -> Result<RuleAttribute, SyntaxError> {
    parse_rule_attribute(parse_source_tokens(source)?)
}

/// Parses the generated-top or named-root configuration attribute payload.
///
/// # Errors
///
/// Requires exactly one string-valued `root` argument and rejects unknown or
/// repeated arguments at their own tokens.
pub fn parse_configuration_attribute(
    tokens: TokenStream,
) -> Result<ConfigurationAttribute, SyntaxError> {
    let structured = RefCell::new(None);
    let parser = |input: ParseStream<'_>| match parse_configuration_stream(input) {
        Ok(attribute) => Ok(attribute),
        Err(ParseConstructorError::Structured(error)) => {
            let diagnostic = syn::Error::new(error.span(), error.to_string());
            structured.replace(Some(error));
            Err(diagnostic)
        }
        Err(ParseConstructorError::Syn(error)) => Err(error),
    };
    parser.parse2(tokens).map_err(|error| {
        structured
            .borrow_mut()
            .take()
            .unwrap_or_else(|| SyntaxError::from(error))
    })
}

/// Parses a configuration payload from source text.
///
/// # Errors
///
/// Returns the same failures as [`parse_configuration_attribute`].
pub fn parse_configuration_attribute_source(
    source: &str,
) -> Result<ConfigurationAttribute, SyntaxError> {
    parse_configuration_attribute(parse_source_tokens(source)?)
}

/// Parses a fixed-cell helper payload.
///
/// # Errors
///
/// Rejects unknown/repeated keys and empty or non-string values locally.
pub fn parse_cell_attribute(tokens: TokenStream) -> Result<CellAttributePayload, SyntaxError> {
    parse_structured_attribute(tokens, parse_cell_stream)
}

/// Parses a fixed-cell helper payload from source text.
///
/// # Errors
///
/// Returns the same failures as [`parse_cell_attribute`].
pub fn parse_cell_attribute_source(source: &str) -> Result<CellAttributePayload, SyntaxError> {
    parse_cell_attribute(parse_source_tokens(source)?)
}

/// Parses the empty initializer attribute payload.
///
/// # Errors
///
/// Rejects any payload at its first token.
pub fn parse_init_attribute(tokens: TokenStream) -> Result<InitAttribute, SyntaxError> {
    parse_empty_tokens(tokens, "init").map(|()| InitAttribute)
}

/// Parses the empty initializer payload from source text.
///
/// # Errors
///
/// Returns the same failures as [`parse_init_attribute`].
pub fn parse_init_attribute_source(source: &str) -> Result<InitAttribute, SyntaxError> {
    parse_init_attribute(parse_source_tokens(source)?)
}

/// Parses constructor arguments from proc-macro or reparsed tokens.
///
/// # Errors
///
/// Rejects missing or duplicate `sort`, duplicate `syntax`, unknown keys,
/// non-path sorts, non-string templates, and malformed comma syntax.
pub fn parse_constructor_attribute(
    tokens: TokenStream,
) -> Result<ConstructorAttribute, SyntaxError> {
    let structured = RefCell::new(None);
    let parser = |input: ParseStream<'_>| match parse_constructor_stream(input) {
        Ok(attribute) => Ok(attribute),
        Err(ParseConstructorError::Structured(error)) => {
            let diagnostic = syn::Error::new(error.span(), error.to_string());
            structured.replace(Some(error));
            Err(diagnostic)
        }
        Err(ParseConstructorError::Syn(error)) => Err(error),
    };
    let result = parser.parse2(tokens);
    result.map_err(|error| {
        structured
            .borrow_mut()
            .take()
            .unwrap_or_else(|| SyntaxError::from(error))
    })
}

/// Parses constructor arguments from source text using the same parser.
///
/// # Errors
///
/// Returns the same structured failures as [`parse_constructor_attribute`].
pub fn parse_constructor_attribute_source(
    source: &str,
) -> Result<ConstructorAttribute, SyntaxError> {
    parse_constructor_attribute(parse_source_tokens(source)?)
}

/// Parses one total-function production attribute.
///
/// # Errors
///
/// Requires the bare `total` marker plus `sort` and `syntax`, and rejects
/// unknown, repeated, or incorrectly typed arguments at their own tokens.
pub fn parse_function_attribute(tokens: TokenStream) -> Result<FunctionAttribute, SyntaxError> {
    parse_structured_attribute(tokens, parse_function_stream)
}

/// Parses total-function arguments from source text using the same parser.
///
/// # Errors
///
/// Returns the same structured failures as [`parse_function_attribute`].
pub fn parse_function_attribute_source(source: &str) -> Result<FunctionAttribute, SyntaxError> {
    parse_function_attribute(parse_source_tokens(source)?)
}

/// Parses the payload of `#[k::constructors(sort = OuterSort)]`.
///
/// # Errors
///
/// Requires exactly one plain Rust path-valued `sort` argument, accepts either
/// `result = ResultSort` or bare `reference` open-family mode, and rejects
/// unknown, repeated, or mutually exclusive arguments at their own tokens.
pub fn parse_constructors_attribute(
    tokens: TokenStream,
) -> Result<ConstructorsAttribute, SyntaxError> {
    parse_structured_attribute(tokens, parse_constructors_stream)
}

/// Parses a `constructors` payload directly from source text.
///
/// # Errors
///
/// Returns the same failures as [`parse_constructors_attribute`].
pub fn parse_constructors_attribute_source(
    source: &str,
) -> Result<ConstructorsAttribute, SyntaxError> {
    parse_constructors_attribute(parse_source_tokens(source)?)
}

/// Parses one enum-variant `#[k::syntax("...", ...)]` payload.
///
/// # Errors
///
/// Requires a leading string template and accepts only the closed `group`,
/// `avoid`, and `format` metadata catalog after it.
pub fn parse_variant_syntax_attribute(
    tokens: TokenStream,
) -> Result<VariantSyntaxAttribute, SyntaxError> {
    parse_structured_attribute(tokens, parse_variant_syntax_stream)
}

/// Parses enum-variant syntax metadata directly from source text.
///
/// # Errors
///
/// Returns the same failures as [`parse_variant_syntax_attribute`].
pub fn parse_variant_syntax_attribute_source(
    source: &str,
) -> Result<VariantSyntaxAttribute, SyntaxError> {
    parse_variant_syntax_attribute(parse_source_tokens(source)?)
}

fn parse_source_tokens(source: &str) -> Result<TokenStream, SyntaxError> {
    source.parse::<TokenStream>().map_err(|error| {
        SyntaxError::new(
            SyntaxErrorKind::RustSyntax(error.to_string()),
            Span::call_site(),
        )
    })
}

fn parse_empty_tokens(tokens: TokenStream, attribute: &'static str) -> Result<(), SyntaxError> {
    if let Some(first) = tokens.into_iter().next() {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnexpectedAttributePayload { attribute },
            first.span(),
        ));
    }
    Ok(())
}

fn parse_empty_attribute(input: ParseStream<'_>, attribute: &'static str) -> syn::Result<()> {
    if input.is_empty() {
        Ok(())
    } else {
        Err(SyntaxError::new(
            SyntaxErrorKind::UnexpectedAttributePayload { attribute },
            input.span(),
        )
        .into_syn_error())
    }
}

enum ParseConstructorError {
    Structured(SyntaxError),
    Syn(syn::Error),
}

fn parse_structured_attribute<T>(
    tokens: TokenStream,
    parser: impl Fn(ParseStream<'_>) -> Result<T, ParseConstructorError>,
) -> Result<T, SyntaxError> {
    let structured = RefCell::new(None);
    let parser = |input: ParseStream<'_>| match parser(input) {
        Ok(value) => Ok(value),
        Err(ParseConstructorError::Structured(error)) => {
            let diagnostic = syn::Error::new(error.span(), error.to_string());
            structured.replace(Some(error));
            Err(diagnostic)
        }
        Err(ParseConstructorError::Syn(error)) => Err(error),
    };
    parser.parse2(tokens).map_err(|error| {
        structured
            .borrow_mut()
            .take()
            .unwrap_or_else(|| SyntaxError::from(error))
    })
}

impl From<SyntaxError> for ParseConstructorError {
    fn from(error: SyntaxError) -> Self {
        Self::Structured(error)
    }
}

impl From<syn::Error> for ParseConstructorError {
    fn from(error: syn::Error) -> Self {
        Self::Syn(error)
    }
}

fn parse_sort_stream(input: ParseStream<'_>) -> Result<SortAttribute, ParseConstructorError> {
    if input.is_empty() {
        return Ok(SortAttribute::default());
    }

    let missing_span = input.span();
    let mut alias = None;
    let mut parents = None;
    while !input.is_empty() {
        let key: Ident = input.parse()?;
        let key_name = key.to_string();
        match key_name.as_str() {
            "alias" if alias.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "alias" },
                    key.span(),
                )
                .into());
            }
            "parents" if parents.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "parents" },
                    key.span(),
                )
                .into());
            }
            "alias" | "parents" => {}
            _ => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::UnknownArgument { name: key_name },
                    key.span(),
                )
                .into());
            }
        }
        input.parse::<Token![=]>()?;
        let value: Expr = input.parse()?;
        if key == "alias" {
            alias = Some(parse_unqualified_identifier_value("alias", value)?);
        } else {
            parents = Some(parse_parent_paths_value(value)?);
        }
        if input.is_empty() {
            break;
        }
        input.parse::<Token![,]>()?;
        if input.is_empty() {
            break;
        }
    }

    if parents.is_some() && alias.is_none() {
        return Err(SyntaxError::new(
            SyntaxErrorKind::MissingArgument { name: "alias" },
            missing_span,
        )
        .into());
    }
    Ok(SortAttribute {
        alias,
        parents: parents.unwrap_or_default(),
    })
}

fn parse_subsort_stream(input: ParseStream<'_>) -> Result<SubsortAttribute, ParseConstructorError> {
    let missing_span = input.span();
    let mut sort = None;
    while !input.is_empty() {
        let key: Ident = input.parse()?;
        let key_name = key.to_string();
        match key_name.as_str() {
            "sort" if sort.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "sort" },
                    key.span(),
                )
                .into());
            }
            "sort" => {}
            _ => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::UnknownArgument { name: key_name },
                    key.span(),
                )
                .into());
            }
        }
        input.parse::<Token![=]>()?;
        sort = Some(parse_sort_value(input.parse()?)?);
        if input.is_empty() {
            break;
        }
        input.parse::<Token![,]>()?;
        if input.is_empty() {
            break;
        }
    }
    Ok(SubsortAttribute {
        sort: sort.ok_or_else(|| {
            SyntaxError::new(
                SyntaxErrorKind::MissingArgument { name: "sort" },
                missing_span,
            )
        })?,
    })
}

fn parse_context_alias_stream(
    input: ParseStream<'_>,
) -> Result<ContextAliasAttribute, ParseConstructorError> {
    let missing_span = input.span();
    let mut name = None;
    let mut here = None;
    while !input.is_empty() {
        let key: Ident = input.parse()?;
        let key_name = key.to_string();
        let argument = match key_name.as_str() {
            "name" if name.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "name" },
                    key.span(),
                )
                .into());
            }
            "name" => "name",
            "here" if here.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "here" },
                    key.span(),
                )
                .into());
            }
            "here" => "here",
            _ => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::UnknownArgument { name: key_name },
                    key.span(),
                )
                .into());
            }
        };
        input.parse::<Token![=]>()?;
        let value: Expr = input.parse()?;
        let identifier = parse_unqualified_identifier_value(argument, value)?;
        if argument == "name" {
            name = Some(identifier);
        } else {
            here = Some(identifier);
        }
        if input.is_empty() {
            break;
        }
        input.parse::<Token![,]>()?;
        if input.is_empty() {
            break;
        }
    }
    Ok(ContextAliasAttribute {
        name: name.ok_or_else(|| {
            SyntaxError::new(
                SyntaxErrorKind::MissingArgument { name: "name" },
                missing_span,
            )
        })?,
        here: here.ok_or_else(|| {
            SyntaxError::new(
                SyntaxErrorKind::MissingArgument { name: "here" },
                missing_span,
            )
        })?,
    })
}

fn parse_constructor_stream(
    input: ParseStream<'_>,
) -> Result<ConstructorAttribute, ParseConstructorError> {
    let missing_span = input.span();
    let mut sort = None;
    let mut syntax = None;
    let mut group = None;
    let mut avoid = None;
    let mut format = None;

    while !input.is_empty() {
        let key: Ident = input.parse()?;
        let key_name = key.to_string();
        match key_name.as_str() {
            "sort" if sort.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "sort" },
                    key.span(),
                )
                .into());
            }
            "syntax" if syntax.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "syntax" },
                    key.span(),
                )
                .into());
            }
            "group" if group.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "group" },
                    key.span(),
                )
                .into());
            }
            "avoid" if avoid.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "avoid" },
                    key.span(),
                )
                .into());
            }
            "format" if format.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "format" },
                    key.span(),
                )
                .into());
            }
            "sort" | "syntax" | "group" | "avoid" | "format" => {}
            _ => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::UnknownArgument { name: key_name },
                    key.span(),
                )
                .into());
            }
        }
        input.parse::<Token![=]>()?;
        let value: Expr = input.parse()?;

        match key_name.as_str() {
            "sort" => sort = Some(parse_sort_value(value)?),
            "syntax" => syntax = Some(parse_syntax_value(value)?),
            "group" => group = Some(parse_group_value(value)?),
            "avoid" => avoid = Some(parse_avoid_value(value)?),
            "format" => format = Some(parse_format_value(value)?),
            _ => unreachable!("argument name was validated before its value"),
        }

        if input.is_empty() {
            break;
        }
        input.parse::<Token![,]>()?;
        if input.is_empty() {
            break;
        }
    }

    let sort = sort.ok_or_else(|| {
        SyntaxError::new(
            SyntaxErrorKind::MissingArgument { name: "sort" },
            missing_span,
        )
    })?;
    let syntax_template = syntax
        .clone()
        .map(SyntaxTemplate::parse)
        .transpose()
        .map_err(ParseConstructorError::Structured)?;
    let structured_format = format
        .clone()
        .map(StructuredFormat::parse)
        .transpose()
        .map_err(ParseConstructorError::Structured)?;
    Ok(ConstructorAttribute {
        sort,
        syntax,
        group,
        avoid: avoid.as_ref().is_some_and(LitBool::value),
        format,
        syntax_template,
        structured_format,
        avoid_literal: avoid,
    })
}

fn parse_function_stream(
    input: ParseStream<'_>,
) -> Result<FunctionAttribute, ParseConstructorError> {
    let missing_span = input.span();
    let mut totality = None;
    let mut sort = None;
    let mut syntax = None;

    while !input.is_empty() {
        let key: Ident = input.parse()?;
        let key_name = key.to_string();
        match key_name.as_str() {
            "total" | "partial" if totality.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "totality" },
                    key.span(),
                )
                .into());
            }
            "total" => totality = Some(FunctionTotality::Total(key)),
            "partial" => totality = Some(FunctionTotality::Partial(key)),
            "sort" if sort.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "sort" },
                    key.span(),
                )
                .into());
            }
            "syntax" if syntax.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "syntax" },
                    key.span(),
                )
                .into());
            }
            "sort" | "syntax" => {
                input.parse::<Token![=]>()?;
                let value: Expr = input.parse()?;
                if key_name == "sort" {
                    sort = Some(parse_sort_value(value)?);
                } else {
                    syntax = Some(parse_syntax_value(value)?);
                }
            }
            _ => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::UnknownArgument { name: key_name },
                    key.span(),
                )
                .into());
            }
        }
        if input.is_empty() {
            break;
        }
        input.parse::<Token![,]>()?;
        if input.is_empty() {
            break;
        }
    }

    let totality = totality.ok_or_else(|| {
        SyntaxError::new(
            SyntaxErrorKind::MissingArgument { name: "total" },
            missing_span,
        )
    })?;
    let sort = sort.ok_or_else(|| {
        SyntaxError::new(
            SyntaxErrorKind::MissingArgument { name: "sort" },
            missing_span,
        )
    })?;
    let syntax = syntax.ok_or_else(|| {
        SyntaxError::new(
            SyntaxErrorKind::MissingArgument { name: "syntax" },
            missing_span,
        )
    })?;
    let syntax_template = SyntaxTemplate::parse(syntax.clone())?;
    Ok(FunctionAttribute {
        constructor: ConstructorAttribute {
            sort,
            syntax: Some(syntax),
            group: None,
            avoid: false,
            format: None,
            syntax_template: Some(syntax_template),
            structured_format: None,
            avoid_literal: None,
        },
        totality,
    })
}

fn parse_rule_stream(input: ParseStream<'_>) -> Result<RuleAttribute, ParseConstructorError> {
    let mut label = None;
    while !input.is_empty() {
        let key: Ident = input.parse()?;
        let key_name = key.to_string();
        match key_name.as_str() {
            "label" if label.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "label" },
                    key.span(),
                )
                .into());
            }
            "label" => {}
            _ => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::UnknownArgument { name: key_name },
                    key.span(),
                )
                .into());
            }
        }
        input.parse::<Token![=]>()?;
        let value: Expr = input.parse()?;
        label = Some(parse_rule_label_value(value)?);
        if input.is_empty() {
            break;
        }
        input.parse::<Token![,]>()?;
        if input.is_empty() {
            break;
        }
    }
    Ok(RuleAttribute { label })
}

fn parse_constructors_stream(
    input: ParseStream<'_>,
) -> Result<ConstructorsAttribute, ParseConstructorError> {
    let missing_span = input.span();
    let mut sort = None;
    let mut result = None;
    let mut reference = None;
    while !input.is_empty() {
        let key: Ident = input.parse()?;
        let key_name = key.to_string();
        match key_name.as_str() {
            "sort" if sort.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "sort" },
                    key.span(),
                )
                .into());
            }
            "result" if result.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "result" },
                    key.span(),
                )
                .into());
            }
            "reference" if reference.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "reference" },
                    key.span(),
                )
                .into());
            }
            "reference" if result.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::InvalidArgumentValue {
                        name: "reference",
                        expected: "omitted when `result = ...` is present",
                    },
                    key.span(),
                )
                .into());
            }
            "result" if reference.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::InvalidArgumentValue {
                        name: "result",
                        expected: "omitted when bare `reference` is present",
                    },
                    key.span(),
                )
                .into());
            }
            "reference" => {
                reference = Some(key);
                if input.is_empty() {
                    break;
                }
                input.parse::<Token![,]>()?;
                if input.is_empty() {
                    break;
                }
                continue;
            }
            "sort" | "result" => {}
            _ => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::UnknownArgument { name: key_name },
                    key.span(),
                )
                .into());
            }
        }
        input.parse::<Token![=]>()?;
        let value = parse_sort_value(input.parse()?)?;
        if key_name == "sort" {
            sort = Some(value);
        } else {
            result = Some(value);
        }
        if input.is_empty() {
            break;
        }
        input.parse::<Token![,]>()?;
        if input.is_empty() {
            break;
        }
    }
    Ok(ConstructorsAttribute {
        sort: sort.ok_or_else(|| {
            SyntaxError::new(
                SyntaxErrorKind::MissingArgument { name: "sort" },
                missing_span,
            )
        })?,
        result,
        reference: reference.is_some(),
    })
}

fn parse_variant_syntax_stream(
    input: ParseStream<'_>,
) -> Result<VariantSyntaxAttribute, ParseConstructorError> {
    let missing_span = input.span();
    if input.is_empty() {
        return Err(SyntaxError::new(
            SyntaxErrorKind::MissingArgument { name: "syntax" },
            missing_span,
        )
        .into());
    }
    let syntax = parse_syntax_value(input.parse()?)?;
    let mut group = None;
    let mut avoid = None;
    let mut format = None;

    if !input.is_empty() {
        input.parse::<Token![,]>()?;
    }
    while !input.is_empty() {
        let key: Ident = input.parse()?;
        let key_name = key.to_string();
        match key_name.as_str() {
            "group" if group.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "group" },
                    key.span(),
                )
                .into());
            }
            "avoid" if avoid.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "avoid" },
                    key.span(),
                )
                .into());
            }
            "format" if format.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "format" },
                    key.span(),
                )
                .into());
            }
            "group" | "avoid" | "format" => {}
            _ => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::UnknownArgument { name: key_name },
                    key.span(),
                )
                .into());
            }
        }
        if key_name == "avoid" && !input.peek(Token![=]) {
            avoid = Some(LitBool::new(true, key.span()));
        } else {
            input.parse::<Token![=]>()?;
            let value: Expr = input.parse()?;
            match key_name.as_str() {
                "group" => group = Some(parse_group_value(value)?),
                "avoid" => avoid = Some(parse_avoid_value(value)?),
                "format" => format = Some(parse_format_value(value)?),
                _ => unreachable!("variant syntax argument was validated before its value"),
            }
        }
        if input.is_empty() {
            break;
        }
        input.parse::<Token![,]>()?;
    }

    let syntax_template = SyntaxTemplate::parse(syntax.clone())?;
    let structured_format = format.clone().map(StructuredFormat::parse).transpose()?;
    Ok(VariantSyntaxAttribute {
        syntax,
        group,
        avoid: avoid.as_ref().is_some_and(LitBool::value),
        format,
        syntax_template,
        structured_format,
        avoid_literal: avoid,
    })
}

fn parse_configuration_stream(
    input: ParseStream<'_>,
) -> Result<ConfigurationAttribute, ParseConstructorError> {
    let missing_span = input.span();
    let mut root = None;
    while !input.is_empty() {
        let key: Ident = input.parse()?;
        let key_name = key.to_string();
        match key_name.as_str() {
            "root" if root.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "root" },
                    key.span(),
                )
                .into());
            }
            "root" => {}
            _ => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::UnknownArgument { name: key_name },
                    key.span(),
                )
                .into());
            }
        }
        input.parse::<Token![=]>()?;
        let value: Expr = input.parse()?;
        let literal = parse_string_value("root", value)?;
        if literal.value().is_empty() {
            return Err(SyntaxError::new(
                SyntaxErrorKind::InvalidArgumentValue {
                    name: "root",
                    expected: "a nonempty Rust string literal",
                },
                literal.span(),
            )
            .into());
        }
        root = Some(literal);
        if input.is_empty() {
            break;
        }
        input.parse::<Token![,]>()?;
        if input.is_empty() {
            break;
        }
    }
    let _ = missing_span;
    Ok(ConfigurationAttribute { root })
}

fn parse_cell_stream(
    input: ParseStream<'_>,
) -> Result<CellAttributePayload, ParseConstructorError> {
    let mut name = None;
    let mut color = None;
    while !input.is_empty() {
        let key: Ident = input.parse()?;
        let key_name = key.to_string();
        let slot = match key_name.as_str() {
            "name" => &mut name,
            "color" => &mut color,
            _ => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::UnknownArgument { name: key_name },
                    key.span(),
                )
                .into());
            }
        };
        if slot.is_some() {
            return Err(SyntaxError::new(
                SyntaxErrorKind::DuplicateArgument {
                    name: if key == "name" { "name" } else { "color" },
                },
                key.span(),
            )
            .into());
        }
        input.parse::<Token![=]>()?;
        let value: Expr = input.parse()?;
        let literal = parse_string_value(if key == "name" { "name" } else { "color" }, value)?;
        if literal.value().trim().is_empty() {
            return Err(SyntaxError::new(
                SyntaxErrorKind::InvalidCellAttribute {
                    reason: "cell names and colors must be nonempty strings",
                },
                literal.span(),
            )
            .into());
        }
        *slot = Some(literal);
        if input.is_empty() {
            break;
        }
        input.parse::<Token![,]>()?;
    }
    Ok(CellAttributePayload { name, color })
}

fn parse_string_value(name: &'static str, value: Expr) -> Result<LitStr, ParseConstructorError> {
    let Expr::Lit(ExprLit {
        attrs,
        lit: Lit::Str(literal),
    }) = value
    else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name,
                expected: "a Rust string literal",
            },
            value.span(),
        )
        .into());
    };
    if !attrs.is_empty() {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name,
                expected: "an unadorned Rust string literal",
            },
            literal.span(),
        )
        .into());
    }
    Ok(literal)
}

fn parse_unqualified_identifier_value(
    name: &'static str,
    value: Expr,
) -> Result<Ident, ParseConstructorError> {
    let Expr::Path(ExprPath {
        attrs,
        qself: None,
        path,
    }) = value
    else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name,
                expected: "an unqualified Rust identifier",
            },
            value.span(),
        )
        .into());
    };
    if !attrs.is_empty()
        || path.leading_colon.is_some()
        || path.segments.len() != 1
        || !is_plain_path(&path)
    {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name,
                expected: "an unqualified Rust identifier",
            },
            path.span(),
        )
        .into());
    }
    Ok(path
        .segments
        .first()
        .expect("one path segment checked")
        .ident
        .clone())
}

fn parse_sort_value(value: Expr) -> Result<Path, ParseConstructorError> {
    let Expr::Path(ExprPath {
        attrs,
        qself: None,
        path,
    }) = value
    else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name: "sort",
                expected: "a Rust trait path",
            },
            value.span(),
        )
        .into());
    };
    if !attrs.is_empty() || !is_plain_path(&path) {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name: "sort",
                expected: "a plain Rust trait path without generic arguments",
            },
            path.span(),
        )
        .into());
    }
    Ok(path)
}

fn parse_parent_paths_value(value: Expr) -> Result<Vec<Path>, ParseConstructorError> {
    let Expr::Array(array) = value else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name: "parents",
                expected: "an array of plain Rust sort paths",
            },
            value.span(),
        )
        .into());
    };
    if !array.attrs.is_empty() {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name: "parents",
                expected: "an unadorned array of plain Rust sort paths",
            },
            array.span(),
        )
        .into());
    }
    array
        .elems
        .into_iter()
        .map(|value| {
            let span = value.span();
            let Expr::Path(ExprPath {
                attrs,
                qself: None,
                path,
            }) = value
            else {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::InvalidArgumentValue {
                        name: "parents",
                        expected: "an array of plain Rust sort paths",
                    },
                    span,
                )
                .into());
            };
            if !attrs.is_empty() || !is_plain_path(&path) {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::InvalidArgumentValue {
                        name: "parents",
                        expected: "an array of plain Rust sort paths without generic arguments",
                    },
                    path.span(),
                )
                .into());
            }
            Ok(path)
        })
        .collect()
}

fn parse_syntax_value(value: Expr) -> Result<LitStr, ParseConstructorError> {
    let Expr::Lit(ExprLit {
        attrs,
        lit: Lit::Str(literal),
    }) = value
    else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name: "syntax",
                expected: "a Rust string literal",
            },
            value.span(),
        )
        .into());
    };
    if !attrs.is_empty() {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name: "syntax",
                expected: "an unadorned Rust string literal",
            },
            literal.span(),
        )
        .into());
    }
    Ok(literal)
}

fn parse_group_value(value: Expr) -> Result<LitStr, ParseConstructorError> {
    let literal = parse_string_value("group", value)?;
    let spelling = literal.value();
    let mut characters = spelling.chars();
    let valid = characters
        .next()
        .is_some_and(|character| character == '_' || character.is_ascii_alphabetic())
        && characters.all(|character| character == '_' || character.is_ascii_alphanumeric());
    if !valid {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name: "group",
                expected: "a nonempty identifier-shaped Rust string literal",
            },
            literal.span(),
        )
        .into());
    }
    Ok(literal)
}

fn parse_rule_label_value(value: Expr) -> Result<LitStr, ParseConstructorError> {
    let literal = parse_string_value("label", value)?;
    let spelling = literal.value();
    let valid = spelling
        .bytes()
        .next()
        .is_some_and(|byte| byte.is_ascii_alphabetic())
        && spelling
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-'));
    if !valid {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name: "label",
                expected: "a nonempty K rule label using ASCII letters, digits, `_`, or `-` and beginning with a letter",
            },
            literal.span(),
        )
        .into());
    }
    Ok(literal)
}

fn parse_avoid_value(value: Expr) -> Result<LitBool, ParseConstructorError> {
    let Expr::Lit(ExprLit {
        attrs,
        lit: Lit::Bool(literal),
    }) = value
    else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name: "avoid",
                expected: "a Rust Boolean literal",
            },
            value.span(),
        )
        .into());
    };
    if !attrs.is_empty() {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name: "avoid",
                expected: "an unadorned Rust Boolean literal",
            },
            literal.span(),
        )
        .into());
    }
    if !literal.value {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name: "avoid",
                expected: "the Rust Boolean literal `true`",
            },
            literal.span(),
        )
        .into());
    }
    Ok(literal)
}

fn parse_format_value(value: Expr) -> Result<LitStr, ParseConstructorError> {
    parse_string_value("format", value)
}

pub(crate) fn is_plain_path(path: &Path) -> bool {
    !path.segments.is_empty()
        && path
            .segments
            .iter()
            .all(|segment| matches!(segment.arguments, syn::PathArguments::None))
}

pub(crate) fn path_spelling(path: &Path) -> String {
    path.to_token_stream().to_string()
}
