use proc_macro2::TokenStream;
use syn::parse::{Parse, ParseStream};
use syn::{Expr, Ident, LitBool, LitStr, Path, Token};

use crate::grammar::{StructuredFormat, SyntaxTemplate};
use crate::parse::{KrsSyntax, ParseError, structured};
use crate::{
    ConstructorDeclaration, ProvenanceAnchor, ProvenanceRole, SyntaxError, SyntaxErrorKind,
    TokenRange,
};

use super::value::{
    parse_avoid_value, parse_format_value, parse_group_value, parse_sort_value, parse_syntax_value,
};

/// Arguments of `#[k::constructor(...)]`.
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
    hook: Option<Path>,
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

    /// Optional closed hook selector path.
    #[must_use]
    pub const fn hook(&self) -> Option<&Path> {
        self.hook.as_ref()
    }

    /// Returns complete production and totality provenance.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if a parsed token-bearing node emits no
    /// leaves.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = self.constructor.full_provenance()?;
        let (role, marker) = match &self.totality {
            FunctionTotality::Total(marker) => (ProvenanceRole::FunctionTotal, marker),
            FunctionTotality::Partial(marker) => (ProvenanceRole::FunctionPartial, marker),
        };
        anchors.push(ProvenanceAnchor::new(
            role,
            0,
            TokenRange::for_tokens(marker)?,
        ));
        if let Some(hook) = &self.hook {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::FunctionHook,
                0,
                TokenRange::for_tokens(hook)?,
            ));
        }
        Ok(anchors)
    }
}

impl Parse for FunctionAttribute {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        parse_function_stream(input).map_err(syn::Error::from)
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
    mode: ConstructorFamilyMode,
}

#[derive(Clone, Debug)]
pub(crate) enum ConstructorFamilyMode {
    Legacy,
    Readable { result: Path },
    Reference,
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
        match &self.mode {
            ConstructorFamilyMode::Readable { result } => Some(result),
            ConstructorFamilyMode::Legacy | ConstructorFamilyMode::Reference => None,
        }
    }

    /// Whether this is the materialized reference-family form.
    #[must_use]
    pub const fn is_reference(&self) -> bool {
        matches!(self.mode, ConstructorFamilyMode::Reference)
    }

    /// Whether variants construct the outer sort directly.
    #[must_use]
    pub const fn is_open_family(&self) -> bool {
        !matches!(self.mode, ConstructorFamilyMode::Legacy)
    }

    pub(crate) const fn mode(&self) -> &ConstructorFamilyMode {
        &self.mode
    }
}

impl Parse for ConstructorsAttribute {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        parse_constructors_stream(input).map_err(syn::Error::from)
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

    /// Returns the complete anchor catalog, including syntax-template, group,
    /// and avoid anchors; [`Self::provenance`] keeps the compact protocol-v5 catalog.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if a parsed Rust node emits no tokens.
    pub fn full_provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
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
        parse_constructor_stream(input).map_err(syn::Error::from)
    }
}

impl KrsSyntax for ConstructorAttribute {
    /// Parses constructor arguments from proc-macro or reparsed tokens.
    ///
    /// # Errors
    ///
    /// Rejects missing or duplicate `sort`, duplicate `syntax`, unknown keys,
    /// non-path sorts, non-string templates, and malformed comma syntax.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        structured(tokens, parse_constructor_stream)
    }
}

impl KrsSyntax for FunctionAttribute {
    /// Parses one total-function production attribute.
    ///
    /// # Errors
    ///
    /// Requires the bare `total` marker plus `sort` and `syntax`, and rejects
    /// unknown, repeated, or incorrectly typed arguments at their own tokens.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        structured(tokens, parse_function_stream)
    }
}

impl KrsSyntax for ConstructorsAttribute {
    /// Parses the payload of `#[k::constructors(sort = OuterSort)]`.
    ///
    /// # Errors
    ///
    /// Requires exactly one plain Rust path-valued `sort` argument, accepts either
    /// `result = ResultSort` or bare `reference` open-family mode, and rejects
    /// unknown, repeated, or mutually exclusive arguments at their own tokens.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        structured(tokens, parse_constructors_stream)
    }
}

impl KrsSyntax for VariantSyntaxAttribute {
    /// Parses one enum-variant `#[k::syntax("...", ...)]` payload.
    ///
    /// # Errors
    ///
    /// Requires a leading string template and accepts only the closed `group`,
    /// `avoid`, and `format` metadata catalog after it.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        structured(tokens, parse_variant_syntax_stream)
    }
}

#[derive(Clone, Copy)]
enum ConstructorKey {
    Sort,
    Syntax,
    Group,
    Avoid,
    Format,
}

impl ConstructorKey {
    fn parse(key: &Ident) -> Result<Self, ParseError> {
        match key.to_string().as_str() {
            "sort" => Ok(Self::Sort),
            "syntax" => Ok(Self::Syntax),
            "group" => Ok(Self::Group),
            "avoid" => Ok(Self::Avoid),
            "format" => Ok(Self::Format),
            _ => Err(SyntaxError::new(
                SyntaxErrorKind::UnknownArgument {
                    name: key.to_string(),
                },
                key.span(),
            )
            .into()),
        }
    }
}

#[derive(Clone, Copy)]
enum VariantSyntaxKey {
    Group,
    Avoid,
    Format,
}

impl VariantSyntaxKey {
    fn parse(key: &Ident) -> Result<Self, ParseError> {
        match key.to_string().as_str() {
            "group" => Ok(Self::Group),
            "avoid" => Ok(Self::Avoid),
            "format" => Ok(Self::Format),
            _ => Err(SyntaxError::new(
                SyntaxErrorKind::UnknownArgument {
                    name: key.to_string(),
                },
                key.span(),
            )
            .into()),
        }
    }
}

fn parse_constructor_stream(input: ParseStream<'_>) -> Result<ConstructorAttribute, ParseError> {
    let missing_span = input.span();
    let mut sort = None;
    let mut syntax = None;
    let mut group = None;
    let mut avoid = None;
    let mut format = None;

    while !input.is_empty() {
        let key: Ident = input.parse()?;
        let key_kind = ConstructorKey::parse(&key)?;
        match key_kind {
            ConstructorKey::Sort if sort.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "sort" },
                    key.span(),
                )
                .into());
            }
            ConstructorKey::Syntax if syntax.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "syntax" },
                    key.span(),
                )
                .into());
            }
            ConstructorKey::Group if group.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "group" },
                    key.span(),
                )
                .into());
            }
            ConstructorKey::Avoid if avoid.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "avoid" },
                    key.span(),
                )
                .into());
            }
            ConstructorKey::Format if format.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "format" },
                    key.span(),
                )
                .into());
            }
            _ => {}
        }
        input.parse::<Token![=]>()?;
        let value: Expr = input.parse()?;

        match key_kind {
            ConstructorKey::Sort => sort = Some(parse_sort_value(value)?),
            ConstructorKey::Syntax => syntax = Some(parse_syntax_value(value)?),
            ConstructorKey::Group => group = Some(parse_group_value(value)?),
            ConstructorKey::Avoid => avoid = Some(parse_avoid_value(value)?),
            ConstructorKey::Format => format = Some(parse_format_value(value)?),
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
        .map_err(ParseError::Structured)?;
    let structured_format = format
        .clone()
        .map(StructuredFormat::parse)
        .transpose()
        .map_err(ParseError::Structured)?;
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

fn parse_function_stream(input: ParseStream<'_>) -> Result<FunctionAttribute, ParseError> {
    let missing_span = input.span();
    let mut totality = None;
    let mut sort = None;
    let mut syntax = None;
    let mut hook = None;

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
            "hook" if hook.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "hook" },
                    key.span(),
                )
                .into());
            }
            "sort" | "syntax" | "hook" => {
                input.parse::<Token![=]>()?;
                let value: Expr = input.parse()?;
                if key_name == "sort" {
                    sort = Some(parse_sort_value(value)?);
                } else if key_name == "syntax" {
                    syntax = Some(parse_syntax_value(value)?);
                } else {
                    hook = Some(parse_sort_value(value)?);
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
        hook,
    })
}

fn parse_constructors_stream(input: ParseStream<'_>) -> Result<ConstructorsAttribute, ParseError> {
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
        mode: if let Some(result) = result {
            ConstructorFamilyMode::Readable { result }
        } else if reference.is_some() {
            ConstructorFamilyMode::Reference
        } else {
            ConstructorFamilyMode::Legacy
        },
    })
}

fn parse_variant_syntax_stream(
    input: ParseStream<'_>,
) -> Result<VariantSyntaxAttribute, ParseError> {
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
        let key_kind = VariantSyntaxKey::parse(&key)?;
        match key_kind {
            VariantSyntaxKey::Group if group.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "group" },
                    key.span(),
                )
                .into());
            }
            VariantSyntaxKey::Avoid if avoid.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "avoid" },
                    key.span(),
                )
                .into());
            }
            VariantSyntaxKey::Format if format.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "format" },
                    key.span(),
                )
                .into());
            }
            _ => {}
        }
        if matches!(key_kind, VariantSyntaxKey::Avoid) && !input.peek(Token![=]) {
            avoid = Some(LitBool::new(true, key.span()));
        } else {
            input.parse::<Token![=]>()?;
            let value: Expr = input.parse()?;
            match key_kind {
                VariantSyntaxKey::Group => group = Some(parse_group_value(value)?),
                VariantSyntaxKey::Avoid => avoid = Some(parse_avoid_value(value)?),
                VariantSyntaxKey::Format => format = Some(parse_format_value(value)?),
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
