use proc_macro2::TokenStream;
use syn::parse::{Parse, ParseStream};
use syn::spanned::Spanned;
use syn::{Expr, Ident, LitBool, LitStr, Path, Token};

use crate::grammar::{StructuredFormat, SyntaxTemplate};
use crate::parse::{KrsSyntax, ParseError, structured};
use crate::{
    ConstructorDeclaration, ProvenanceAnchor, ProvenanceRole, SyntaxError, SyntaxErrorKind,
    TokenRange,
};

use super::value::{
    parse_avoid_value, parse_format_value, parse_group_value, parse_overload_value,
    parse_prefer_value, parse_sort_value, parse_syntax_value,
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
    prefer_literal: Option<LitBool>,
    placement: PlacementFlags,
    overload: Option<Path>,
    colors: ProductionColors,
}

/// Which module a production asks to be placed in.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PlacementFlag {
    /// `internal`: usable in rules, including by dependents, but not program syntax.
    Internal,
    /// `program`: asserts that the production is program syntax.
    Program,
}

impl PlacementFlag {
    /// Returns the flag's spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Internal => "internal",
            Self::Program => "program",
        }
    }

    /// Returns the provenance role of the flag.
    #[must_use]
    pub const fn role(self) -> ProvenanceRole {
        match self {
            Self::Internal => ProvenanceRole::ConstructorInternal,
            Self::Program => ProvenanceRole::ConstructorProgram,
        }
    }
}

/// The optional `internal` or `program` flag of one production attribute,
/// anchored at its key.
#[derive(Clone, Debug, Default)]
pub(crate) struct PlacementFlags {
    flag: Option<(PlacementFlag, Ident)>,
}

impl PlacementFlags {
    /// Parses one `internal` or `program` key whose identifier was consumed.
    /// The reference spelling `key = true` is accepted when `assignment` is
    /// allowed; `key = false` is rejected because it is not metadata.
    fn parse(
        &mut self,
        flag: PlacementFlag,
        key: Ident,
        input: ParseStream<'_>,
        assignment: bool,
    ) -> Result<(), ParseError> {
        match &self.flag {
            Some((existing, _)) if *existing == flag => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument {
                        name: flag.as_str(),
                    },
                    key.span(),
                )
                .into());
            }
            Some(_) => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::InvalidArgumentValue {
                        name: flag.as_str(),
                        expected: "omitted: a production is either `internal` or `program`, not both",
                    },
                    key.span(),
                )
                .into());
            }
            None => {}
        }
        if input.peek(Token![=]) {
            if !assignment {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::InvalidArgumentValue {
                        name: flag.as_str(),
                        expected: "a bare flag in `#[k::function]`",
                    },
                    key.span(),
                )
                .into());
            }
            input.parse::<Token![=]>()?;
            parse_flag_value(flag.as_str(), input.parse()?)?;
        }
        self.flag = Some((flag, key));
        Ok(())
    }

    /// Sets a flag inherited from an enclosing family attribute.
    pub(crate) fn inherit(&mut self, flag: PlacementFlag, key: Ident) -> Result<(), SyntaxError> {
        match &self.flag {
            None => {
                self.flag = Some((flag, key));
                Ok(())
            }
            Some((existing, own)) => Err(SyntaxError::new(
                if *existing == flag {
                    SyntaxErrorKind::DuplicateArgument {
                        name: flag.as_str(),
                    }
                } else {
                    SyntaxErrorKind::InvalidArgumentValue {
                        name: existing.as_str(),
                        expected: "omitted in an `internal` family: a production is either `internal` or `program`, not both",
                    }
                },
                own.span(),
            )),
        }
    }

    pub(crate) fn flag(&self) -> Option<PlacementFlag> {
        self.flag.as_ref().map(|(flag, _)| *flag)
    }

    pub(crate) fn key(&self) -> Option<&Ident> {
        self.flag.as_ref().map(|(_, key)| key)
    }

    pub(crate) fn anchors(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        self.flag
            .iter()
            .map(|(flag, key)| {
                Ok(ProvenanceAnchor::new(
                    flag.role(),
                    0,
                    TokenRange::for_tokens(key)?,
                ))
            })
            .collect()
    }
}

fn parse_flag_value(name: &'static str, value: Expr) -> Result<(), ParseError> {
    match value {
        Expr::Lit(syn::ExprLit {
            attrs,
            lit: syn::Lit::Bool(literal),
        }) if attrs.is_empty() && literal.value => Ok(()),
        value => Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name,
                expected: "omitted or the Rust Boolean literal `true`",
            },
            value.span(),
        )
        .into()),
    }
}

/// The optional `color = "c"` or `colors = ["c", ..]` of one production.
#[derive(Clone, Debug, Default)]
pub(crate) struct ProductionColors {
    color: Option<LitStr>,
    colors: Option<(syn::ExprArray, Vec<LitStr>)>,
}

impl ProductionColors {
    /// Parses the value of a `color` or `colors` key whose identifier was consumed.
    fn parse(&mut self, key: &Ident, value: Expr) -> Result<(), ParseError> {
        let name = if key == "color" { "color" } else { "colors" };
        if self.color.is_some() && name == "color" || self.colors.is_some() && name == "colors" {
            return Err(
                SyntaxError::new(SyntaxErrorKind::DuplicateArgument { name }, key.span()).into(),
            );
        }
        if self.color.is_some() || self.colors.is_some() {
            return Err(
                invalid_color("`color` and `colors` cannot be combined", key.span()).into(),
            );
        }
        if name == "color" {
            let literal = super::value::parse_string_value("color", value)?;
            check_color(&literal)?;
            self.color = Some(literal);
            return Ok(());
        }
        let Expr::Array(array) = value else {
            return Err(SyntaxError::new(
                SyntaxErrorKind::InvalidArgumentValue {
                    name: "colors",
                    expected: "an array of Rust string literals",
                },
                value.span(),
            )
            .into());
        };
        if array.elems.is_empty() {
            return Err(
                invalid_color("`colors` must name at least one colour", array.span()).into(),
            );
        }
        let literals = array
            .elems
            .iter()
            .cloned()
            .map(|element| {
                let literal = super::value::parse_string_value("colors", element)?;
                check_color(&literal)?;
                Ok(literal)
            })
            .collect::<Result<Vec<_>, ParseError>>()?;
        self.colors = Some((array, literals));
        Ok(())
    }

    /// Checks the colours against the production's printed terminals and
    /// format controls (K's `CheckAtt` rule): `colors` names one colour per
    /// terminal and per `%c`, and `%c`/`%r` require a colour.
    fn validate(
        &self,
        template: Option<&SyntaxTemplate>,
        format: Option<&StructuredFormat>,
        span: proc_macro2::Span,
    ) -> Result<(), SyntaxError> {
        if self.color.is_none() && self.colors.is_none() {
            if let Some(format) = format
                && format.uses_colors()
            {
                return Err(invalid_color(
                    "`%c` and `%r` need a `color` or `colors` key",
                    format.literal().span(),
                ));
            }
            return Ok(());
        }
        let Some(template) = template else {
            return Err(invalid_color(
                "colours need an explicit syntax template",
                span,
            ));
        };
        if let Some((array, literals)) = &self.colors {
            let terminals = template
                .items()
                .iter()
                .filter(|item| matches!(item, crate::grammar::SyntaxTemplateItem::Terminal(_)))
                .count();
            let expected = terminals + format.map_or(0, StructuredFormat::color_next_count);
            if literals.len() != expected {
                return Err(invalid_color(
                    "`colors` needs one colour per terminal of the syntax template plus one per `%c`",
                    array.span(),
                ));
            }
        }
        Ok(())
    }

    pub(crate) fn color(&self) -> Option<&LitStr> {
        self.color.as_ref()
    }

    pub(crate) fn colors(&self) -> Option<&[LitStr]> {
        self.colors
            .as_ref()
            .map(|(_, literals)| literals.as_slice())
    }

    pub(crate) fn anchors(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = Vec::new();
        if let Some(color) = &self.color {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConstructorColor,
                0,
                TokenRange::for_tokens(color)?,
            ));
        }
        if let Some((array, literals)) = &self.colors {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConstructorColor,
                0,
                TokenRange::for_tokens(array)?,
            ));
            for (ordinal, literal) in literals.iter().enumerate() {
                anchors.push(ProvenanceAnchor::new(
                    ProvenanceRole::ConstructorColorsEntry,
                    crate::parse::checked_ordinal(
                        ordinal,
                        ProvenanceRole::ConstructorColorsEntry,
                        literal.span(),
                    )?,
                    TokenRange::for_tokens(literal)?,
                ));
            }
        }
        Ok(anchors)
    }
}

fn check_color(literal: &LitStr) -> Result<(), SyntaxError> {
    let value = literal.value();
    if value.is_empty() || value.contains([',', ')']) {
        return Err(invalid_color(
            "a colour must be nonempty and must not contain `,` or `)`",
            literal.span(),
        ));
    }
    Ok(())
}

fn invalid_color(reason: &'static str, span: proc_macro2::Span) -> SyntaxError {
    SyntaxError::new(SyntaxErrorKind::InvalidColor { reason }, span)
}

/// Arguments of `#[k::function(total, sort = ..., syntax = "...")]`.
#[derive(Clone, Debug)]
pub struct FunctionAttribute {
    constructor: ConstructorAttribute,
    totality: FunctionTotality,
    memo: Option<Ident>,
    fresh_generator: Option<Ident>,
    hook: Option<FunctionHook>,
}

/// The `hook` value of `#[k::function]`.
#[derive(Clone, Debug)]
pub enum FunctionHook {
    /// A typed catalog path, such as `krypto::sha256_raw`.
    Catalog(Path),
    /// A quoted K hook name, such as `"KRYPTO.keccak256"`: an escape from A4
    /// that the package must allow.
    Quoted(LitStr),
}

impl FunctionHook {
    /// Returns the provenance range of the authored value.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if the value emits no tokens.
    pub fn range(&self) -> Result<TokenRange, SyntaxError> {
        match self {
            Self::Catalog(path) => TokenRange::for_tokens(path),
            Self::Quoted(literal) => TokenRange::for_tokens(literal),
        }
    }
}

impl quote::ToTokens for FunctionHook {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            Self::Catalog(path) => path.to_tokens(tokens),
            Self::Quoted(literal) => literal.to_tokens(tokens),
        }
    }
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

    /// Optional hook: a closed catalog path or a quoted K hook name.
    #[must_use]
    pub const fn hook(&self) -> Option<&FunctionHook> {
        self.hook.as_ref()
    }

    /// The bare `memo` flag, K's memoization hint.
    #[must_use]
    pub const fn memo(&self) -> Option<&Ident> {
        self.memo.as_ref()
    }

    /// The bare `fresh_generator` flag: K's `freshGenerator`, the function a
    /// fresh binder (`#[k::fresh(x: S)]`) of the result sort draws from.
    #[must_use]
    pub const fn fresh_generator(&self) -> Option<&Ident> {
        self.fresh_generator.as_ref()
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
        if let Some(memo) = &self.memo {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::FunctionMemo,
                0,
                TokenRange::for_tokens(memo)?,
            ));
        }
        if let Some(flag) = &self.fresh_generator {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::FunctionFreshGenerator,
                0,
                TokenRange::for_tokens(flag)?,
            ));
        }
        if let Some(hook) = &self.hook {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::FunctionHook,
                0,
                hook.range()?,
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
    internal: Option<Ident>,
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

    /// Returns the readable family flag `internal`, which makes every variant
    /// production `internal`.
    #[must_use]
    pub const fn internal(&self) -> Option<&Ident> {
        self.internal.as_ref()
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
    prefer_literal: Option<LitBool>,
    placement: PlacementFlags,
    overload: Option<Path>,
    colors: ProductionColors,
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

    /// Returns whether the production carries K's parser `prefer` preference.
    #[must_use]
    pub const fn prefer(&self) -> bool {
        self.prefer_literal.is_some()
    }

    /// Returns the target path of the production's `overload` key.
    #[must_use]
    pub const fn overload(&self) -> Option<&Path> {
        self.overload.as_ref()
    }

    /// Returns the authored structured-format literal, when present.
    #[must_use]
    pub const fn format(&self) -> Option<&LitStr> {
        self.format.as_ref()
    }

    /// Returns the production's `internal` or `program` flag, including an
    /// `internal` inherited from the family attribute.
    #[must_use]
    pub fn placement(&self) -> Option<PlacementFlag> {
        self.placement.flag()
    }

    /// Returns the key the placement flag is anchored at.
    #[must_use]
    pub fn placement_key(&self) -> Option<&Ident> {
        self.placement.key()
    }

    /// Returns the `color` literal, when present.
    #[must_use]
    pub fn color(&self) -> Option<&LitStr> {
        self.colors.color()
    }

    /// Returns the `colors` literals in source order, when present.
    #[must_use]
    pub fn colors(&self) -> Option<&[LitStr]> {
        self.colors.colors()
    }

    pub(crate) fn inherit_placement(
        &mut self,
        flag: PlacementFlag,
        key: Ident,
    ) -> Result<(), SyntaxError> {
        self.placement.inherit(flag, key)
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
        let mut format = StructuredFormat::parse_named(literal, &self.syntax_template, controls)?;
        format.number_terminals(&self.syntax_template);
        self.colors.validate(
            Some(&self.syntax_template),
            Some(&format),
            self.syntax.span(),
        )?;
        self.structured_format = Some(format);
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
        if let Some(prefer) = &self.prefer_literal {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConstructorPrefer,
                0,
                TokenRange::for_tokens(prefer)?,
            ));
        }
        anchors.extend(self.placement.anchors()?);
        if let Some(overload) = &self.overload {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConstructorOverload,
                0,
                TokenRange::for_tokens(overload)?,
            ));
        }
        anchors.extend(self.colors.anchors()?);
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
    /// Returns whether the production carries K's parser `prefer` preference.
    #[must_use]
    pub const fn prefer(&self) -> bool {
        self.prefer_literal.is_some()
    }

    /// Returns the target path of the production's `overload` key.
    #[must_use]
    pub const fn overload(&self) -> Option<&Path> {
        self.overload.as_ref()
    }

    /// Returns the production's `internal` or `program` flag.
    #[must_use]
    pub fn placement(&self) -> Option<PlacementFlag> {
        self.placement.flag()
    }

    /// Returns the key the placement flag is anchored at.
    #[must_use]
    pub fn placement_key(&self) -> Option<&Ident> {
        self.placement.key()
    }

    /// Returns the `color` literal, when present.
    #[must_use]
    pub fn color(&self) -> Option<&LitStr> {
        self.colors.color()
    }

    /// Returns the `colors` literals in source order, when present.
    #[must_use]
    pub fn colors(&self) -> Option<&[LitStr]> {
        self.colors.colors()
    }

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
        if let Some(prefer) = &self.prefer_literal {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConstructorPrefer,
                0,
                TokenRange::for_tokens(prefer)?,
            ));
        }
        anchors.extend(self.placement.anchors()?);
        if let Some(overload) = &self.overload {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ConstructorOverload,
                0,
                TokenRange::for_tokens(overload)?,
            ));
        }
        anchors.extend(self.colors.anchors()?);
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
    Prefer,
    Overload,
    Format,
}

impl ConstructorKey {
    fn parse(key: &Ident) -> Result<Self, ParseError> {
        match key.to_string().as_str() {
            "sort" => Ok(Self::Sort),
            "syntax" => Ok(Self::Syntax),
            "group" => Ok(Self::Group),
            "avoid" => Ok(Self::Avoid),
            "prefer" => Ok(Self::Prefer),
            "overload" => Ok(Self::Overload),
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
    Prefer,
    Overload,
    Format,
}

impl VariantSyntaxKey {
    fn parse(key: &Ident) -> Result<Self, ParseError> {
        match key.to_string().as_str() {
            "group" => Ok(Self::Group),
            "avoid" => Ok(Self::Avoid),
            "prefer" => Ok(Self::Prefer),
            "overload" => Ok(Self::Overload),
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

#[expect(
    clippy::too_many_lines,
    reason = "One keyed loop parses every constructor production argument."
)]
fn parse_constructor_stream(input: ParseStream<'_>) -> Result<ConstructorAttribute, ParseError> {
    let missing_span = input.span();
    let mut sort = None;
    let mut syntax = None;
    let mut group = None;
    let mut avoid = None;
    let mut prefer = None;
    let mut overload = None;
    let mut format = None;
    let mut placement = PlacementFlags::default();
    let mut colors = ProductionColors::default();

    while !input.is_empty() {
        let key: Ident = input.parse()?;
        if let Some(flag) = placement_flag(&key) {
            placement.parse(flag, key, input, true)?;
            if input.is_empty() {
                break;
            }
            input.parse::<Token![,]>()?;
            continue;
        }
        if key == "color" || key == "colors" {
            input.parse::<Token![=]>()?;
            colors.parse(&key, input.parse()?)?;
            if input.is_empty() {
                break;
            }
            input.parse::<Token![,]>()?;
            continue;
        }
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
            ConstructorKey::Prefer if prefer.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "prefer" },
                    key.span(),
                )
                .into());
            }
            ConstructorKey::Avoid | ConstructorKey::Prefer
                if avoid.is_some() || prefer.is_some() =>
            {
                return Err(preference_conflict(&key).into());
            }
            ConstructorKey::Overload if overload.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "overload" },
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
            ConstructorKey::Prefer => prefer = Some(parse_prefer_value(value)?),
            ConstructorKey::Overload => overload = Some(parse_overload_value(value)?),
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
    let mut structured_format = format
        .clone()
        .map(StructuredFormat::parse)
        .transpose()
        .map_err(ParseError::Structured)?;
    if let (Some(format), Some(template)) = (&mut structured_format, &syntax_template) {
        format.number_terminals(template);
    }
    colors
        .validate(
            syntax_template.as_ref(),
            structured_format.as_ref(),
            missing_span,
        )
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
        prefer_literal: prefer,
        overload,
        placement,
        colors,
    })
}

/// K applies `prefer` and `avoid` as one pair of parse-forest filters and
/// lets `prefer` win silently, so a production takes at most one of them.
fn preference_conflict(key: &Ident) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::InvalidArgumentValue {
            name: if key == "prefer" { "prefer" } else { "avoid" },
            expected: "omitted: a production is either preferred or avoided, not both",
        },
        key.span(),
    )
}

fn placement_flag(key: &Ident) -> Option<PlacementFlag> {
    match key.to_string().as_str() {
        "internal" => Some(PlacementFlag::Internal),
        "program" => Some(PlacementFlag::Program),
        _ => None,
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "One keyed loop parses every function production argument."
)]
fn parse_function_stream(input: ParseStream<'_>) -> Result<FunctionAttribute, ParseError> {
    let missing_span = input.span();
    let mut totality = None;
    let mut memo = None;
    let mut fresh_generator = None;
    let mut sort = None;
    let mut syntax = None;
    let mut hook = None;
    let mut placement = PlacementFlags::default();

    while !input.is_empty() {
        let key: Ident = input.parse()?;
        let key_name = key.to_string();
        if let Some(flag) = placement_flag(&key) {
            placement.parse(flag, key, input, false)?;
            if input.is_empty() {
                break;
            }
            input.parse::<Token![,]>()?;
            continue;
        }
        match key_name.as_str() {
            "total" | "partial" if totality.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "totality" },
                    key.span(),
                )
                .into());
            }
            "total" => totality = Some(FunctionTotality::Total(key)),
            "memo" if memo.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "memo" },
                    key.span(),
                )
                .into());
            }
            "memo" if input.peek(Token![=]) => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::InvalidArgumentValue {
                        name: "memo",
                        expected: "a bare flag in `#[k::function]`",
                    },
                    key.span(),
                )
                .into());
            }
            "memo" => memo = Some(key),
            "fresh_generator" if fresh_generator.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument {
                        name: "fresh_generator",
                    },
                    key.span(),
                )
                .into());
            }
            "fresh_generator" if input.peek(Token![=]) => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::InvalidArgumentValue {
                        name: "fresh_generator",
                        expected: "a bare flag in `#[k::function]`",
                    },
                    key.span(),
                )
                .into());
            }
            "fresh_generator" => fresh_generator = Some(key),
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
                } else if let Expr::Lit(syn::ExprLit {
                    lit: syn::Lit::Str(literal),
                    attrs,
                }) = &value
                    && attrs.is_empty()
                {
                    hook = Some(FunctionHook::Quoted(literal.clone()));
                } else {
                    hook = Some(FunctionHook::Catalog(parse_sort_value(value)?));
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
            prefer_literal: None,
            overload: None,
            placement,
            colors: ProductionColors::default(),
        },
        totality,
        memo,
        fresh_generator,
        hook,
    })
}

#[expect(
    clippy::too_many_lines,
    reason = "One keyed loop parses every family argument and its exclusions."
)]
fn parse_constructors_stream(input: ParseStream<'_>) -> Result<ConstructorsAttribute, ParseError> {
    let missing_span = input.span();
    let mut sort = None;
    let mut result = None;
    let mut reference = None;
    let mut internal = None;
    while !input.is_empty() {
        let key: Ident = input.parse()?;
        let key_name = key.to_string();
        match key_name.as_str() {
            "internal" if internal.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "internal" },
                    key.span(),
                )
                .into());
            }
            "internal" => {
                if input.peek(Token![=]) {
                    return Err(SyntaxError::new(
                        SyntaxErrorKind::InvalidArgumentValue {
                            name: "internal",
                            expected: "a bare family flag in `#[k::constructors]`",
                        },
                        key.span(),
                    )
                    .into());
                }
                internal = Some(key);
                if input.is_empty() {
                    break;
                }
                input.parse::<Token![,]>()?;
                if input.is_empty() {
                    break;
                }
                continue;
            }
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
        internal,
    })
}

#[expect(
    clippy::too_many_lines,
    reason = "One keyed loop parses every variant production argument."
)]
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
    let mut prefer = None;
    let mut overload = None;
    let mut format = None;
    let mut placement = PlacementFlags::default();
    let mut colors = ProductionColors::default();

    if !input.is_empty() {
        input.parse::<Token![,]>()?;
    }
    while !input.is_empty() {
        let key: Ident = input.parse()?;
        if let Some(flag) = placement_flag(&key) {
            placement.parse(flag, key, input, true)?;
            if input.is_empty() {
                break;
            }
            input.parse::<Token![,]>()?;
            continue;
        }
        if key == "color" || key == "colors" {
            input.parse::<Token![=]>()?;
            colors.parse(&key, input.parse()?)?;
            if input.is_empty() {
                break;
            }
            input.parse::<Token![,]>()?;
            continue;
        }
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
            VariantSyntaxKey::Prefer if prefer.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "prefer" },
                    key.span(),
                )
                .into());
            }
            VariantSyntaxKey::Avoid | VariantSyntaxKey::Prefer
                if avoid.is_some() || prefer.is_some() =>
            {
                return Err(preference_conflict(&key).into());
            }
            VariantSyntaxKey::Overload if overload.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "overload" },
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
        } else if matches!(key_kind, VariantSyntaxKey::Prefer) && !input.peek(Token![=]) {
            prefer = Some(LitBool::new(true, key.span()));
        } else {
            input.parse::<Token![=]>()?;
            let value: Expr = input.parse()?;
            match key_kind {
                VariantSyntaxKey::Group => group = Some(parse_group_value(value)?),
                VariantSyntaxKey::Avoid => avoid = Some(parse_avoid_value(value)?),
                VariantSyntaxKey::Prefer => prefer = Some(parse_prefer_value(value)?),
                VariantSyntaxKey::Overload => overload = Some(parse_overload_value(value)?),
                VariantSyntaxKey::Format => format = Some(parse_format_value(value)?),
            }
        }
        if input.is_empty() {
            break;
        }
        input.parse::<Token![,]>()?;
    }

    let syntax_template = SyntaxTemplate::parse(syntax.clone())?;
    let mut structured_format = format.clone().map(StructuredFormat::parse).transpose()?;
    if let Some(format) = &mut structured_format {
        format.number_terminals(&syntax_template);
        colors.validate(Some(&syntax_template), Some(format), syntax.span())?;
    }
    // Without an inline format, a readable variant validates its colours once
    // its format is known (`apply_readable_format`); semantic validation
    // repeats the check for every production.
    Ok(VariantSyntaxAttribute {
        syntax,
        group,
        avoid: avoid.as_ref().is_some_and(LitBool::value),
        format,
        syntax_template,
        structured_format,
        avoid_literal: avoid,
        prefer_literal: prefer,
        overload,
        placement,
        colors,
    })
}
