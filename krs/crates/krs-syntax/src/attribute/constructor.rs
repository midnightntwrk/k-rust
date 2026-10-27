use krs_ir::ProvenanceKey;
use proc_macro2::TokenStream;
use syn::ext::IdentExt;
use syn::parse::{Parse, ParseStream};
use syn::spanned::Spanned;
use syn::{Expr, Ident, LitBool, LitStr, Path, Token};

use crate::grammar::{StructuredFormat, SyntaxTemplate};
use crate::parse::{KeyAllocator, KrsSyntax, ParseError, structured};
use crate::provenance::denoted_anchors;
use crate::{
    ConstructorDeclaration, ProvenanceAnchor, ProvenanceRole, SortArgument, SyntaxError,
    SyntaxErrorKind, TokenRange,
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
    /// The element types of a function's typed collection result
    /// (`sort = Set<Int>`, or `-> k::Term<Set<Int>>` on a `fn`); empty for
    /// every other production.
    pub sort_arguments: Vec<SortArgument>,
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
    sort_key: Option<ProvenanceKey>,
    keys: ProductionKeys,
    /// The anchors of the full view's keying.
    anchors: Vec<ProvenanceAnchor>,
    /// The anchors of the sort-argument view's keying.
    sort_argument_anchors: Vec<ProvenanceAnchor>,
}

/// The keys of a production's syntax and metadata values, one slot per
/// value; a template's items and a format's fragments hold their own.
#[derive(Clone, Debug, Default)]
pub struct ProductionKeys {
    syntax: Option<ProvenanceKey>,
    group: Option<ProvenanceKey>,
    avoid: Option<ProvenanceKey>,
    prefer: Option<ProvenanceKey>,
    placement: Option<ProvenanceKey>,
    overload: Option<ProvenanceKey>,
    color: Option<ProvenanceKey>,
    color_entries: Vec<ProvenanceKey>,
    format: Option<ProvenanceKey>,
}

impl ProductionKeys {
    /// The key of the `syntax` literal.
    #[must_use]
    pub const fn syntax(&self) -> Option<&ProvenanceKey> {
        self.syntax.as_ref()
    }

    /// The key of the `group` literal.
    #[must_use]
    pub const fn group(&self) -> Option<&ProvenanceKey> {
        self.group.as_ref()
    }

    /// The key of the `avoid` literal.
    #[must_use]
    pub const fn avoid(&self) -> Option<&ProvenanceKey> {
        self.avoid.as_ref()
    }

    /// The key of the `prefer` literal.
    #[must_use]
    pub const fn prefer(&self) -> Option<&ProvenanceKey> {
        self.prefer.as_ref()
    }

    /// The key of the `internal` or `program` flag.
    #[must_use]
    pub const fn placement(&self) -> Option<&ProvenanceKey> {
        self.placement.as_ref()
    }

    /// The key of the `overload` path.
    #[must_use]
    pub const fn overload(&self) -> Option<&ProvenanceKey> {
        self.overload.as_ref()
    }

    /// The key of the `color` literal or of the `colors` array.
    #[must_use]
    pub const fn color(&self) -> Option<&ProvenanceKey> {
        self.color.as_ref()
    }

    /// The keys of the `colors` array's entries, in order.
    #[must_use]
    pub fn color_entries(&self) -> &[ProvenanceKey] {
        &self.color_entries
    }

    /// The key of the `format` literal.
    #[must_use]
    pub const fn format(&self) -> Option<&ProvenanceKey> {
        self.format.as_ref()
    }

    /// Keys the production metadata after its syntax: the template's items,
    /// the group, avoid and prefer literals, the placement flag, the
    /// overload, the colours, then the format and its fragments.
    #[expect(
        clippy::too_many_arguments,
        reason = "The two production attributes hold the same metadata in their own fields."
    )]
    fn allocate_metadata(
        &mut self,
        keys: &mut KeyAllocator,
        template: Option<&mut SyntaxTemplate>,
        group: Option<&LitStr>,
        avoid: Option<&LitBool>,
        prefer: Option<&LitBool>,
        placement: &PlacementFlags,
        overload: Option<&Path>,
        colors: &ProductionColors,
        format: Option<&mut StructuredFormat>,
    ) -> Result<(), SyntaxError> {
        if let Some(template) = template {
            template.allocate_keys(
                keys,
                ProvenanceRole::ConstructorSyntaxItem,
                ProvenanceRole::ConstructorSyntaxFieldReference,
            )?;
        }
        self.group = optional_key(keys, ProvenanceRole::ConstructorGroup, group)?;
        self.avoid = optional_key(keys, ProvenanceRole::ConstructorAvoid, avoid)?;
        self.prefer = optional_key(keys, ProvenanceRole::ConstructorPrefer, prefer)?;
        self.placement = placement.allocate_keys(keys)?;
        self.overload = optional_key(keys, ProvenanceRole::ConstructorOverload, overload)?;
        (self.color, self.color_entries) = colors.allocate_keys(keys)?;
        self.format = match format {
            Some(format) => {
                let key = keys.key(
                    ProvenanceRole::ConstructorFormat,
                    TokenRange::for_tokens(format.literal())?,
                )?;
                format.allocate_keys(keys, ProvenanceRole::ConstructorFormatFragment)?;
                Some(key)
            }
            None => None,
        };
        Ok(())
    }
}

/// Hands out the next key of `role` to `node`, when it is authored.
fn optional_key(
    keys: &mut KeyAllocator,
    role: ProvenanceRole,
    node: Option<&impl quote::ToTokens>,
) -> Result<Option<ProvenanceKey>, SyntaxError> {
    node.map(|node| keys.key(role, TokenRange::for_tokens(node)?))
        .transpose()
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

    /// Keys the placement flag's key, if any.
    pub(crate) fn allocate_keys(
        &self,
        keys: &mut KeyAllocator,
    ) -> Result<Option<ProvenanceKey>, SyntaxError> {
        self.flag
            .as_ref()
            .map(|(flag, key)| keys.key(flag.role(), TokenRange::for_tokens(key)?))
            .transpose()
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

    /// Keys the `color` value or the `colors` array and each of its entries;
    /// a production has at most one of the two.
    /// Returns the key of the value or array and the keys of the entries.
    pub(crate) fn allocate_keys(
        &self,
        keys: &mut KeyAllocator,
    ) -> Result<(Option<ProvenanceKey>, Vec<ProvenanceKey>), SyntaxError> {
        let mut color = None;
        if let Some(literal) = &self.color {
            color = Some(keys.key(
                ProvenanceRole::ConstructorColor,
                TokenRange::for_tokens(literal)?,
            )?);
        }
        let mut entries = Vec::new();
        if let Some((array, literals)) = &self.colors {
            color = Some(keys.key(
                ProvenanceRole::ConstructorColor,
                TokenRange::for_tokens(array)?,
            )?);
            for literal in literals {
                entries.push(keys.key(
                    ProvenanceRole::ConstructorColorsEntry,
                    TokenRange::for_tokens(literal)?,
                )?);
            }
        }
        Ok((color, entries))
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
    /// Whether `syntax` is the completed default rather than authored.
    default_syntax: bool,
    totality: FunctionTotality,
    memo: Option<Ident>,
    fresh_generator: Option<Ident>,
    hook: Option<FunctionHook>,
    smt: Option<FunctionSmt>,
    /// `underspecified = "reason"`: the equations leave some arguments of
    /// this total function without a value on purpose.
    underspecified: Option<LitStr>,
    totality_key: Option<ProvenanceKey>,
    memo_key: Option<ProvenanceKey>,
    fresh_generator_key: Option<ProvenanceKey>,
    hook_key: Option<ProvenanceKey>,
    smtlib_key: Option<ProvenanceKey>,
    underspecified_key: Option<ProvenanceKey>,
    /// The anchors of the function's keying, which [`Self::provenance`]
    /// returns.
    anchors: Vec<ProvenanceAnchor>,
    /// How many of [`Self::anchors`] are the production's full view.
    production: usize,
}

/// A function's SMT-LIB translation (KF-044): `smtlib` and `smt_hook` are
/// mutually exclusive.
#[derive(Clone, Debug)]
pub enum FunctionSmt {
    /// `smtlib = "sym"`: the solver sees an uninterpreted SMT-LIB symbol.
    Smtlib(LitStr),
    /// `smt_hook = "tmpl"`: the solver sees the SMT-LIB term `tmpl`.
    Hook(crate::SmtTemplate),
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
    /// Parses the keys of `#[k::function]` on a `fn`, whose return type gives
    /// the sort `sort`; a `sort` key is rejected.
    ///
    /// # Errors
    ///
    /// The errors of [`KrsSyntax::parse_tokens`] except a missing `sort`, and
    /// an authored `sort` key.
    pub fn parse_shorthand_tokens(
        tokens: TokenStream,
        sort: &Path,
        sort_arguments: &[SortArgument],
    ) -> Result<Self, SyntaxError> {
        let mut attribute = structured(tokens, |input| {
            parse_function_keys(input, Some(sort.clone()))
        })?;
        attribute.constructor.sort_arguments = sort_arguments.to_vec();
        attribute.rekey()?;
        Ok(attribute)
    }

    /// Whether the function's `syntax` key was written.
    #[must_use]
    pub const fn has_authored_syntax(&self) -> bool {
        self.constructor.syntax.is_some() && !self.default_syntax
    }

    /// Completes an omitted `syntax` with the default template
    /// `symbol({field}, ..)`, where `symbol` is the production's K symbol
    /// (the name with a lowercase first letter). A default is allowed only on
    /// a production that is not program syntax, one marked `internal` or not
    /// `pub`: in a program a default terminal would shadow an object-language
    /// token. The default is anchored at the declaration's name.
    ///
    /// # Errors
    ///
    /// Rejects an omitted `syntax` on a `pub` production that is not
    /// `internal`.
    pub fn complete_default_syntax(
        &mut self,
        declaration: &ConstructorDeclaration,
    ) -> Result<(), SyntaxError> {
        if self.constructor.syntax.is_some() {
            return Ok(());
        }
        let name = declaration.name();
        let program = matches!(declaration.item().vis, syn::Visibility::Public(_))
            && self.constructor.placement() != Some(PlacementFlag::Internal);
        if program {
            return Err(SyntaxError::new(
                SyntaxErrorKind::MissingFunctionSyntax,
                name.span(),
            ));
        }
        let literal = LitStr::new(
            &default_function_syntax(
                &name.unraw().to_string(),
                declaration
                    .fields()
                    .iter()
                    .map(crate::ConstructorField::name),
            ),
            name.span(),
        );
        self.constructor.syntax_template = Some(SyntaxTemplate::parse(literal.clone())?);
        self.constructor.syntax = Some(literal);
        self.default_syntax = true;
        self.rekey()
    }

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

    /// The function's SMT-LIB translation, `smtlib` or `smt_hook`.
    #[must_use]
    pub const fn smt(&self) -> Option<&FunctionSmt> {
        self.smt.as_ref()
    }

    /// Checks `smt_hook` placeholders against the function's fields.
    ///
    /// # Errors
    ///
    /// Rejects a placeholder naming no field and a positional `#N`.
    pub fn validate_smt_fields<'a>(
        &self,
        fields: impl IntoIterator<Item = &'a Ident>,
    ) -> Result<(), SyntaxError> {
        match &self.smt {
            Some(FunctionSmt::Hook(template)) => template.validate_fields(fields),
            Some(FunctionSmt::Smtlib(_)) | None => Ok(()),
        }
    }

    /// The `underspecified = "reason"` statement of an intended coverage gap.
    #[must_use]
    pub const fn underspecified(&self) -> Option<&LitStr> {
        self.underspecified.as_ref()
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
    /// None: the function was keyed when it was parsed, and again when its
    /// syntax or result arguments were completed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    /// The anchors of the function's own keys, which follow its
    /// production's full view: the totality marker, `memo`,
    /// `fresh_generator`, `hook`, the SMT translation and `underspecified`.
    pub(crate) fn function_anchors(&self) -> &[ProvenanceAnchor] {
        &self.anchors[self.production..]
    }

    /// The key of the `total` or `partial` marker.
    #[must_use]
    pub const fn totality_key(&self) -> Option<&ProvenanceKey> {
        self.totality_key.as_ref()
    }

    /// The key of the `memo` flag.
    #[must_use]
    pub const fn memo_key(&self) -> Option<&ProvenanceKey> {
        self.memo_key.as_ref()
    }

    /// The key of the `fresh_generator` flag.
    #[must_use]
    pub const fn fresh_generator_key(&self) -> Option<&ProvenanceKey> {
        self.fresh_generator_key.as_ref()
    }

    /// The key of the `hook` value.
    #[must_use]
    pub const fn hook_key(&self) -> Option<&ProvenanceKey> {
        self.hook_key.as_ref()
    }

    /// The key of the `smtlib` literal; an `smt_hook` template holds its
    /// own keys.
    #[must_use]
    pub const fn smtlib_key(&self) -> Option<&ProvenanceKey> {
        self.smtlib_key.as_ref()
    }

    /// The key of the `underspecified` reason.
    #[must_use]
    pub const fn underspecified_key(&self) -> Option<&ProvenanceKey> {
        self.underspecified_key.as_ref()
    }

    /// The function keyed as a sentence of its own.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        self.rekey()?;
        Ok(self)
    }

    /// Keys the function as a sentence of its own: its production's full
    /// view, then the totality marker, `memo`, `fresh_generator`, `hook`,
    /// the SMT translation and `underspecified`. The production is keyed
    /// alone, which gives its full and sort-argument views; its full view
    /// starts the function's sentence, whose keying records the keys the
    /// production's nodes hold and continues after them.
    fn rekey(&mut self) -> Result<(), SyntaxError> {
        self.constructor.rekey()?;
        let mut keys = KeyAllocator::default();
        keys.append(&self.constructor.full_provenance()?)?;
        self.production = keys.anchors().len();
        let (role, marker) = match &self.totality {
            FunctionTotality::Total(marker) => (ProvenanceRole::FunctionTotal, marker),
            FunctionTotality::Partial(marker) => (ProvenanceRole::FunctionPartial, marker),
        };
        self.totality_key = Some(keys.key(role, TokenRange::for_tokens(marker)?)?);
        self.memo_key = optional_key(&mut keys, ProvenanceRole::FunctionMemo, self.memo.as_ref())?;
        self.fresh_generator_key = optional_key(
            &mut keys,
            ProvenanceRole::FunctionFreshGenerator,
            self.fresh_generator.as_ref(),
        )?;
        self.hook_key = match &self.hook {
            Some(hook) => Some(keys.key(ProvenanceRole::FunctionHook, hook.range()?)?),
            None => None,
        };
        self.smtlib_key = None;
        match &mut self.smt {
            Some(FunctionSmt::Smtlib(literal)) => {
                self.smtlib_key = Some(keys.key(
                    ProvenanceRole::FunctionSmtlib,
                    TokenRange::for_tokens(&*literal)?,
                )?);
            }
            Some(FunctionSmt::Hook(template)) => template.allocate_keys(&mut keys)?,
            None => {}
        }
        self.underspecified_key = optional_key(
            &mut keys,
            ProvenanceRole::FunctionUnderspecified,
            self.underspecified.as_ref(),
        )?;
        self.anchors = keys.into_anchors();
        Ok(())
    }
}

impl Parse for FunctionAttribute {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        parse_function_stream(input).map_err(syn::Error::from)
    }
}

/// Checked payload of `#[k::constructors(sort = ..., result = ... | reference)]`.
///
/// The enum is only a Rust authoring family: every variant constructs `sort`
/// directly. With `result`, the family is readable and `result` is inherited
/// by its strictness helpers. The mutually exclusive bare `reference` marker
/// selects the materialized layer-2 form, where each variant already carries
/// explicit metadata. One of the two is required: a family that needs a sort
/// of its own declares that sort in `k::sorts!` and names it with `sort`.
#[derive(Clone, Debug)]
pub struct ConstructorsAttribute {
    sort: Path,
    mode: ConstructorFamilyMode,
    internal: Option<Ident>,
}

#[derive(Clone, Debug)]
pub(crate) enum ConstructorFamilyMode {
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
            ConstructorFamilyMode::Reference => None,
        }
    }

    /// Whether this is the materialized reference-family form.
    #[must_use]
    pub const fn is_reference(&self) -> bool {
        matches!(self.mode, ConstructorFamilyMode::Reference)
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
    keys: ProductionKeys,
    /// The anchors of the attribute's standalone keying, which
    /// [`Self::provenance`] returns.
    anchors: Vec<ProvenanceAnchor>,
}

impl VariantSyntaxAttribute {
    /// The keys of the syntax and metadata values, from the attribute alone
    /// or from its variant's production.
    #[must_use]
    pub const fn keys(&self) -> &ProductionKeys {
        &self.keys
    }

    /// Keys the attribute as a sentence of its own.
    fn rekey(&mut self) -> Result<(), SyntaxError> {
        let mut keys = KeyAllocator::default();
        self.allocate_keys(&mut keys)?;
        self.anchors = keys.into_anchors();
        Ok(())
    }

    /// The attribute keyed as a sentence of its own.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        self.rekey()?;
        Ok(self)
    }

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
        self.placement.inherit(flag, key)?;
        self.rekey()
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
        self.rekey()
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
    /// None: the attribute was keyed when it was parsed, and again when its
    /// placement or format was completed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    /// Keys the syntax, its template, then the metadata.
    /// The anchors of the attribute's own keying are forgotten here and
    /// recorded again by that keying: an enclosing sentence's pass leaves
    /// the attribute with that sentence's keys and no anchors of its own.
    pub(crate) fn allocate_keys(&mut self, keys: &mut KeyAllocator) -> Result<(), SyntaxError> {
        self.anchors.clear();
        self.keys = ProductionKeys::default();
        self.keys.syntax = Some(keys.key(
            ProvenanceRole::ConstructorSyntax,
            TokenRange::for_tokens(&self.syntax)?,
        )?);
        self.keys.allocate_metadata(
            keys,
            Some(&mut self.syntax_template),
            self.group.as_ref(),
            self.avoid_literal.as_ref(),
            self.prefer_literal.as_ref(),
            &self.placement,
            self.overload.as_ref(),
            &self.colors,
            self.structured_format.as_mut(),
        )
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

    /// Returns the anchor of the production's sort, the one node of the
    /// attribute that the constructor descriptor denotes: the syntax and the
    /// metadata are the grammar descriptor's.
    ///
    /// # Errors
    ///
    /// None: the attribute was keyed when it was parsed.
    pub fn constructor_sort_provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(denoted_anchors(&self.anchors, &[self.sort_key.as_ref()]))
    }

    /// The key of the sort path.
    #[must_use]
    pub const fn sort_key(&self) -> Option<&ProvenanceKey> {
        self.sort_key.as_ref()
    }

    /// The keys of the syntax and metadata values.
    #[must_use]
    pub const fn keys(&self) -> &ProductionKeys {
        &self.keys
    }

    /// Keys the attribute's two views, each a sentence of its own: the full
    /// view keys the sort, the syntax and the metadata; the sort-argument
    /// view keys the result's element types on its own.
    fn rekey(&mut self) -> Result<(), SyntaxError> {
        let mut keys = KeyAllocator::default();
        self.allocate_keys(&mut keys)?;
        self.allocate_metadata_keys(&mut keys)?;
        self.anchors = keys.into_anchors();
        let mut keys = KeyAllocator::default();
        SortArgument::allocate_keys(
            &mut self.sort_arguments,
            &mut keys,
            ProvenanceRole::ConstructorSortArgument,
        )?;
        self.sort_argument_anchors = keys.into_anchors();
        Ok(())
    }

    /// The attribute keyed as a sentence of its own.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        self.rekey()?;
        Ok(self)
    }

    /// Keys the sort and the optional syntax.
    fn allocate_keys(&mut self, keys: &mut KeyAllocator) -> Result<(), SyntaxError> {
        self.keys = ProductionKeys::default();
        self.sort_key = Some(keys.key(
            ProvenanceRole::ConstructorSort,
            TokenRange::for_tokens(&self.sort)?,
        )?);
        self.keys.syntax = optional_key(
            keys,
            ProvenanceRole::ConstructorSyntax,
            self.syntax.as_ref(),
        )?;
        Ok(())
    }

    /// Keys the syntax template and the metadata, after the sort and the
    /// syntax that [`Self::allocate_keys`] keys.
    fn allocate_metadata_keys(&mut self, keys: &mut KeyAllocator) -> Result<(), SyntaxError> {
        self.keys.allocate_metadata(
            keys,
            self.syntax_template.as_mut(),
            self.group.as_ref(),
            self.avoid_literal.as_ref(),
            self.prefer_literal.as_ref(),
            &self.placement,
            self.overload.as_ref(),
            &self.colors,
            self.structured_format.as_mut(),
        )
    }

    /// Returns one anchor per element type of a function's typed collection
    /// result, which only the constructor descriptor references.
    ///
    /// # Errors
    ///
    /// None: the attribute was keyed when it was parsed.
    pub fn sort_argument_provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.sort_argument_anchors.clone())
    }

    /// Returns the complete anchor catalog: the sort, the syntax and its
    /// template, and the metadata.
    ///
    /// # Errors
    ///
    /// None: the attribute was keyed when it was parsed.
    pub fn full_provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
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
    /// Parses the payload of `#[k::constructors(sort = OuterSort, result = R)]`.
    ///
    /// # Errors
    ///
    /// Requires exactly one plain Rust path-valued `sort` argument and exactly
    /// one of `result = ResultSort` or bare `reference`, and rejects unknown,
    /// repeated, or mutually exclusive arguments at their own tokens.
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
        sort_arguments: Vec::new(),
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
        sort_key: None,
        keys: ProductionKeys::default(),
        anchors: Vec::new(),
        sort_argument_anchors: Vec::new(),
    }
    .keyed()?)
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

fn parse_function_stream(input: ParseStream<'_>) -> Result<FunctionAttribute, ParseError> {
    parse_function_keys(input, None)
}

/// Parses the keys of `#[k::function]`. A function declared by a `fn`
/// (`shorthand_sort` is its return type's sort) takes its sort from the
/// signature, so a `sort` key is rejected there.
#[expect(
    clippy::too_many_lines,
    reason = "One keyed loop parses every function production argument."
)]
fn parse_function_keys(
    input: ParseStream<'_>,
    shorthand_sort: Option<Path>,
) -> Result<FunctionAttribute, ParseError> {
    let missing_span = input.span();
    let mut totality = None;
    let mut memo = None;
    let mut fresh_generator = None;
    let mut sort = None;
    let mut sort_arguments = Vec::new();
    let mut syntax = None;
    let mut hook = None;
    let mut smt = None;
    let mut underspecified: Option<LitStr> = None;
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
            "sort" if shorthand_sort.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::InvalidFunctionShorthand {
                        reason: "a function declared by a `fn` takes its sort from the return type; remove `sort`".to_owned(),
                    },
                    key.span(),
                )
                .into());
            }
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
            "smtlib" | "smt_hook" => {
                smt = Some(parse_function_smt(&key, input, smt.as_ref())?);
            }
            "underspecified" if underspecified.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument {
                        name: "underspecified",
                    },
                    key.span(),
                )
                .into());
            }
            "underspecified" => underspecified = Some(parse_underspecified(&key, input)?),
            "sort" => {
                input.parse::<Token![=]>()?;
                let (path, arguments) = parse_function_sort_value(input.parse()?)?;
                sort = Some(path);
                sort_arguments = arguments;
            }
            "syntax" | "hook" => {
                input.parse::<Token![=]>()?;
                let value: Expr = input.parse()?;
                if key_name == "syntax" {
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
    if let (Some(reason), FunctionTotality::Partial(_)) = (&underspecified, &totality) {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidUnderspecified {
                reason: "`underspecified` states a gap in a `total` function's equations; a `partial` function has no value where no equation applies, so remove `underspecified`".to_owned(),
            },
            reason.span(),
        )
        .into());
    }
    let sort = match shorthand_sort {
        Some(sort) => sort,
        None => sort.ok_or_else(|| {
            SyntaxError::new(
                SyntaxErrorKind::MissingArgument { name: "sort" },
                missing_span,
            )
        })?,
    };
    // An omitted `syntax` is completed from the declaration by
    // [`FunctionAttribute::complete_default_syntax`], which knows whether the
    // production is program syntax.
    let syntax_template = syntax.clone().map(SyntaxTemplate::parse).transpose()?;
    Ok(FunctionAttribute {
        constructor: ConstructorAttribute {
            sort,
            sort_arguments,
            syntax,
            group: None,
            avoid: false,
            format: None,
            syntax_template,
            structured_format: None,
            avoid_literal: None,
            prefer_literal: None,
            overload: None,
            placement,
            colors: ProductionColors::default(),
            sort_key: None,
            keys: ProductionKeys::default(),
            anchors: Vec::new(),
            sort_argument_anchors: Vec::new(),
        },
        default_syntax: false,
        totality,
        memo,
        fresh_generator,
        hook,
        smt,
        underspecified,
        totality_key: None,
        memo_key: None,
        fresh_generator_key: None,
        hook_key: None,
        smtlib_key: None,
        underspecified_key: None,
        anchors: Vec::new(),
        production: 0,
    }
    .keyed()?)
}

/// Parses the `sort` of `#[k::function]`: a plain path, or a typed
/// collection `Set<Int>` whose element types are the function's result
/// types.
fn parse_function_sort_value(ty: syn::Type) -> Result<(Path, Vec<SortArgument>), ParseError> {
    if let syn::Type::Path(path) = &ty
        && path.qself.is_none()
        && crate::path::parametric_collection(&path.path).is_some()
    {
        let arguments = crate::configuration::collection_arguments(&ty, |span| {
            SyntaxError::new(SyntaxErrorKind::InvalidCollectionArgument, span)
        })?;
        return Ok((crate::path::without_last_arguments(&path.path), arguments));
    }
    let value = match ty {
        syn::Type::Path(path) if path.qself.is_none() => Expr::Path(syn::ExprPath {
            attrs: Vec::new(),
            qself: None,
            path: path.path,
        }),
        other => {
            return Err(SyntaxError::new(
                SyntaxErrorKind::InvalidArgumentValue {
                    name: "sort",
                    expected: "a Rust trait path",
                },
                other.span(),
            )
            .into());
        }
    };
    Ok((parse_sort_value(value)?, Vec::new()))
}

/// Parses `underspecified = "reason"`: a nonempty string literal.
fn parse_underspecified(key: &Ident, input: ParseStream<'_>) -> Result<LitStr, ParseError> {
    if !input.peek(Token![=]) {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidUnderspecified {
                reason: "`underspecified` takes a reason: write `underspecified = \"why some arguments have no equation\"`".to_owned(),
            },
            key.span(),
        )
        .into());
    }
    input.parse::<Token![=]>()?;
    let value: Expr = input.parse()?;
    match &value {
        Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(literal),
            attrs,
        }) if attrs.is_empty() => {
            if literal.value().trim().is_empty() {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::InvalidUnderspecified {
                        reason: "an `underspecified` reason must not be empty; say why some arguments have no equation".to_owned(),
                    },
                    literal.span(),
                )
                .into());
            }
            Ok(literal.clone())
        }
        _ => Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name: "underspecified",
                expected: "a string literal",
            },
            value.span(),
        )
        .into()),
    }
}

/// Parses `smtlib = "sym"` or `smt_hook = "tmpl"` (KF-044).
fn parse_function_smt(
    key: &Ident,
    input: ParseStream<'_>,
    previous: Option<&FunctionSmt>,
) -> Result<FunctionSmt, ParseError> {
    let smt_error = |reason: String, span: proc_macro2::Span| {
        SyntaxError::new(SyntaxErrorKind::InvalidSmtMetadata { reason }, span)
    };
    let name = key.to_string();
    match previous {
        Some(FunctionSmt::Smtlib(_)) if name == "smtlib" => {
            return Err(SyntaxError::new(
                SyntaxErrorKind::DuplicateArgument { name: "smtlib" },
                key.span(),
            )
            .into());
        }
        Some(FunctionSmt::Hook(_)) if name == "smt_hook" => {
            return Err(SyntaxError::new(
                SyntaxErrorKind::DuplicateArgument { name: "smt_hook" },
                key.span(),
            )
            .into());
        }
        Some(_) => {
            return Err(smt_error(
                "`smtlib` and `smt_hook` are mutually exclusive: K would let `smt-hook` win silently; give the function a name in Z3 (`smtlib`) or a meaning (`smt_hook`), not both".to_owned(),
                key.span(),
            )
            .into());
        }
        None => {}
    }
    input.parse::<Token![=]>()?;
    let value: Expr = input.parse()?;
    let Expr::Lit(syn::ExprLit {
        lit: syn::Lit::Str(literal),
        attrs,
    }) = &value
    else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name: if name == "smtlib" {
                    "smtlib"
                } else {
                    "smt_hook"
                },
                expected: "a string literal",
            },
            value.span(),
        )
        .into());
    };
    if !attrs.is_empty() {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name: if name == "smtlib" {
                    "smtlib"
                } else {
                    "smt_hook"
                },
                expected: "a string literal",
            },
            value.span(),
        )
        .into());
    }
    if name == "smt_hook" {
        return Ok(FunctionSmt::Hook(crate::SmtTemplate::parse(
            literal.clone(),
        )?));
    }
    let symbol = literal.value();
    if symbol.is_empty() {
        return Err(smt_error(
            "an `smtlib` symbol must not be empty; write the SMT-LIB name Z3 should give this function"
                .to_owned(),
            literal.span(),
        )
        .into());
    }
    if !krs_ir::is_smtlib_simple_symbol(&symbol) {
        return Err(smt_error(
            format!(
                "`{symbol}` is not an SMT-LIB simple symbol: use ASCII letters, digits, and `~!@$%^&*_+=<>.?/-`, not starting with a digit"
            ),
            literal.span(),
        )
        .into());
    }
    Ok(FunctionSmt::Smtlib(literal.clone()))
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
    let sort = sort.ok_or_else(|| {
        SyntaxError::new(
            SyntaxErrorKind::MissingArgument { name: "sort" },
            missing_span,
        )
    })?;
    let mode = if let Some(result) = result {
        ConstructorFamilyMode::Readable { result }
    } else if reference.is_some() {
        ConstructorFamilyMode::Reference
    } else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedEnumConstructorDeclaration {
                reason: "a constructor family is readable (`result = KResult`) or reference (`reference`); a family that needs a sort of its own declares it in `k::sorts!` (`Name: Outer;`) and names it with `sort = Name`",
            },
            sort.span(),
        )
        .into());
    };
    Ok(ConstructorsAttribute {
        sort,
        mode,
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
        keys: ProductionKeys::default(),
        anchors: Vec::new(),
    }
    .keyed()?)
}

/// The default syntax template of a function production that is not program
/// syntax: its K symbol, the name with a lowercase first letter, applied to
/// its fields, `byte({value})`.
#[must_use]
pub fn default_function_syntax<'a>(
    name: &str,
    fields: impl IntoIterator<Item = &'a Ident>,
) -> String {
    let mut characters = name.chars();
    let symbol = characters
        .next()
        .map(|first| first.to_lowercase().chain(characters).collect::<String>())
        .unwrap_or_default();
    let fields = fields
        .into_iter()
        .map(|field| format!("{{{}}}", field.unraw()))
        .collect::<Vec<_>>()
        .join(", ");
    format!("{symbol}({fields})")
}

#[cfg(test)]
mod keyed {
    use super::{
        ConstructorAttribute, FunctionAttribute, FunctionSmt, FunctionTotality, PlacementFlags,
        ProductionColors, ProductionKeys, VariantSyntaxAttribute,
    };
    use crate::grammar::{StructuredFormat, SyntaxTemplate};
    use crate::keyed_nodes::KeyedNodes;
    use crate::{SortArgument, SyntaxError};
    use syn::{LitBool, LitStr, Path};

    /// A production's metadata, with the keys its sentence gave it.
    struct Metadata<'a> {
        keys: &'a ProductionKeys,
        syntax: Option<&'a LitStr>,
        template: Option<&'a SyntaxTemplate>,
        group: Option<&'a LitStr>,
        avoid: Option<&'a LitBool>,
        prefer: Option<&'a LitBool>,
        placement: &'a PlacementFlags,
        overload: Option<&'a Path>,
        colors: &'a ProductionColors,
        format: Option<&'a StructuredFormat>,
    }

    impl Metadata<'_> {
        /// Records the keys of the syntax, its template, the group,
        /// `avoid`, `prefer`, the placement flag, the overload, the colours
        /// and the format with its fragments.
        fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            let keys = self.keys;
            if let Some(syntax) = self.syntax {
                nodes.push_tokens(keys.syntax.as_ref(), syntax)?;
            }
            if let Some(template) = self.template {
                template.keyed_nodes(nodes)?;
            }
            if let Some(group) = self.group {
                nodes.push_tokens(keys.group.as_ref(), group)?;
            }
            if let Some(avoid) = self.avoid {
                nodes.push_tokens(keys.avoid.as_ref(), avoid)?;
            }
            if let Some(prefer) = self.prefer {
                nodes.push_tokens(keys.prefer.as_ref(), prefer)?;
            }
            if let Some(placement) = self.placement.key() {
                nodes.push_tokens(keys.placement.as_ref(), placement)?;
            }
            if let Some(overload) = self.overload {
                nodes.push_tokens(keys.overload.as_ref(), overload)?;
            }
            if let Some(color) = &self.colors.color {
                nodes.push_tokens(keys.color.as_ref(), color)?;
            }
            if let Some((array, literals)) = &self.colors.colors {
                nodes.push_tokens(keys.color.as_ref(), array)?;
                assert!(keys.color_entries.len() <= literals.len());
                for (key, literal) in keys.color_entries.iter().zip(literals) {
                    nodes.push_tokens(Some(key), literal)?;
                }
            } else {
                assert!(keys.color_entries.is_empty());
            }
            if let Some(format) = self.format {
                nodes.push_tokens(keys.format.as_ref(), format.literal())?;
                format.keyed_nodes(nodes)?;
            }
            Ok(())
        }
    }

    impl ConstructorAttribute {
        /// Records the key of the sort, the node of
        /// [`Self::constructor_sort_provenance`].
        pub(crate) fn keyed_constructor_sort_nodes(
            &self,
            nodes: &mut KeyedNodes,
        ) -> Result<(), SyntaxError> {
            nodes.push_tokens(self.sort_key.as_ref(), &self.sort)
        }

        /// Records the keys of the full view: the sort, the syntax, then the
        /// metadata.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            self.keyed_constructor_sort_nodes(nodes)?;
            if let Some(syntax) = &self.syntax {
                nodes.push_tokens(self.keys.syntax.as_ref(), syntax)?;
            }
            Metadata {
                keys: &self.keys,
                syntax: None,
                template: self.syntax_template.as_ref(),
                group: self.group.as_ref(),
                avoid: self.avoid_literal.as_ref(),
                prefer: self.prefer_literal.as_ref(),
                placement: &self.placement,
                overload: self.overload.as_ref(),
                colors: &self.colors,
                format: self.structured_format.as_ref(),
            }
            .keyed_nodes(nodes)
        }

        /// Records the keys of the sort arguments, the sentence of
        /// [`Self::sort_argument_provenance`].
        pub(crate) fn keyed_sort_argument_nodes(
            &self,
            nodes: &mut KeyedNodes,
        ) -> Result<(), SyntaxError> {
            SortArgument::keyed_nodes(&self.sort_arguments, nodes)
        }
    }

    impl FunctionAttribute {
        /// Records the keys of the production's full view, then the
        /// function's own.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            self.constructor.keyed_nodes(nodes)?;
            self.keyed_function_nodes(nodes)
        }

        /// Records the keys of the function's own nodes: its totality
        /// marker, `memo`, `fresh_generator`, the hook, the SMT translation
        /// and `underspecified`.
        pub(crate) fn keyed_function_nodes(
            &self,
            nodes: &mut KeyedNodes,
        ) -> Result<(), SyntaxError> {
            let (FunctionTotality::Total(marker) | FunctionTotality::Partial(marker)) =
                &self.totality;
            nodes.push_tokens(self.totality_key.as_ref(), marker)?;
            if let Some(memo) = &self.memo {
                nodes.push_tokens(self.memo_key.as_ref(), memo)?;
            }
            if let Some(fresh_generator) = &self.fresh_generator {
                nodes.push_tokens(self.fresh_generator_key.as_ref(), fresh_generator)?;
            }
            if let Some(hook) = &self.hook {
                nodes.push(self.hook_key.as_ref(), hook.range()?);
            }
            match &self.smt {
                Some(FunctionSmt::Smtlib(literal)) => {
                    nodes.push_tokens(self.smtlib_key.as_ref(), literal)?;
                }
                Some(FunctionSmt::Hook(template)) => template.keyed_nodes(nodes)?,
                None => {}
            }
            if let Some(underspecified) = &self.underspecified {
                nodes.push_tokens(self.underspecified_key.as_ref(), underspecified)?;
            }
            Ok(())
        }
    }

    impl VariantSyntaxAttribute {
        /// Records the keys of the syntax, its template, then the metadata.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            Metadata {
                keys: &self.keys,
                syntax: Some(&self.syntax),
                template: Some(&self.syntax_template),
                group: self.group.as_ref(),
                avoid: self.avoid_literal.as_ref(),
                prefer: self.prefer_literal.as_ref(),
                placement: &self.placement,
                overload: self.overload.as_ref(),
                colors: &self.colors,
                format: self.structured_format.as_ref(),
            }
            .keyed_nodes(nodes)
        }
    }
}
