use proc_macro2::TokenStream;
use syn::parse::{Parse, ParseStream, Parser};
use syn::{Expr, Ident, LitInt, LitStr, Path, Token};

use crate::parse::{KrsSyntax, ParseError, structured};
use crate::{ProvenanceAnchor, ProvenanceRole, SyntaxError, SyntaxErrorKind, TokenRange};

use super::rule::{
    NONDET_ON_FUNCTION, OWISE_ON_SIMPLIFICATION, OWISE_PRIORITY, OWISE_WITH_PRIORITY,
    PRIORITY_ON_STATIC_RULE, PriorityValue, parse_priority_value, rule_key_error,
};

use super::value::{
    parse_empty_tokens, parse_parent_paths_value, parse_sort_value,
    parse_unqualified_identifier_value,
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

/// Checked payload of `#[k::equation]`, `#[k::equation(owise)]`, or
/// `#[k::equation(priority = N)]`.
#[derive(Clone, Debug, Default)]
pub struct EquationAttribute {
    owise: Option<Ident>,
    priority: Option<PriorityValue>,
}

impl EquationAttribute {
    /// Whether this equation is an ordered fallback (priority 200).
    #[must_use]
    pub const fn is_owise(&self) -> bool {
        self.owise.is_some()
    }

    /// Returns the explicit `priority = N` value, when authored.
    #[must_use]
    pub fn priority(&self) -> Option<u32> {
        self.priority.as_ref().map(|priority| priority.value)
    }

    /// Returns the effective authored equation priority and the role that
    /// anchors it: `owise` is priority 200 under [`ProvenanceRole::EquationOwise`],
    /// and `priority = N` is N under [`ProvenanceRole::EquationPriority`].
    #[must_use]
    pub fn equation_priority(&self) -> Option<(ProvenanceRole, u32)> {
        if self.owise.is_some() {
            return Some((ProvenanceRole::EquationOwise, OWISE_PRIORITY));
        }
        self.priority
            .as_ref()
            .map(|priority| (ProvenanceRole::EquationPriority, priority.value))
    }

    /// Returns exact provenance for an authored `owise` marker or priority literal.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if an authored token has no range.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = Vec::new();
        if let Some(owise) = &self.owise {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::EquationOwise,
                0,
                TokenRange::for_tokens(owise)?,
            ));
        }
        if let Some(priority) = &self.priority {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::EquationPriority,
                0,
                TokenRange::for_tokens(&priority.literal)?,
            ));
        }
        Ok(anchors)
    }
}

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

/// The retired standalone `#[k::priority(N)]` attribute.
///
/// Its only parse result is the retirement diagnostic, which names the
/// replacement `#[k::equation(priority = N)]` with the authored value.
#[derive(Clone, Copy, Debug)]
pub struct PriorityAttribute;

impl Parse for SortAttribute {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        parse_sort_stream(input).map_err(syn::Error::from)
    }
}

impl Parse for SubsortAttribute {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        parse_subsort_stream(input).map_err(syn::Error::from)
    }
}

impl Parse for ContextAliasAttribute {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        parse_context_alias_stream(input).map_err(syn::Error::from)
    }
}

impl KrsSyntax for SortAttribute {
    /// Parses a legacy empty or explicit reference sort-attribute payload.
    ///
    /// # Errors
    ///
    /// Rejects unknown, repeated, or incorrectly typed arguments and requires
    /// `alias` whenever `parents` is present.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        structured(tokens, parse_sort_stream)
    }
}

impl KrsSyntax for SubsortAttribute {
    /// Parses the explicit supersort alias carried by a reference subsort impl.
    ///
    /// # Errors
    ///
    /// Requires exactly one plain Rust path-valued `sort` argument and rejects
    /// missing, unknown, repeated, or incorrectly typed arguments.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        structured(tokens, parse_subsort_stream)
    }
}

impl KrsSyntax for SymbolAttribute {
    /// Parses exactly one string literal as a stable public symbol identity.
    ///
    /// # Errors
    ///
    /// Rejects missing or additional tokens, non-string values, and malformed
    /// logical symbol paths.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
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
}

impl KrsSyntax for EquationAttribute {
    /// Parses an empty equation payload, `owise`, or `priority = N`.
    ///
    /// # Errors
    ///
    /// Rejects labels and other unknown keys, repeated keys, `owise` with
    /// `priority`, and priorities outside `0..=254`.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        structured(tokens, parse_equation_stream)
    }
}

fn parse_equation_stream(input: ParseStream<'_>) -> Result<EquationAttribute, ParseError> {
    let mut owise: Option<Ident> = None;
    let mut priority: Option<PriorityValue> = None;
    while !input.is_empty() {
        let key: Ident = input.parse()?;
        let key_name = key.to_string();
        match key_name.as_str() {
            "owise" if owise.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "owise" },
                    key.span(),
                )
                .into());
            }
            "priority" if priority.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "priority" },
                    key.span(),
                )
                .into());
            }
            "owise" if priority.is_some() => {
                return Err(rule_key_error(OWISE_WITH_PRIORITY, key.span()));
            }
            "owise" => owise = Some(key),
            "priority" if owise.is_some() => {
                return Err(rule_key_error(OWISE_WITH_PRIORITY, key.span()));
            }
            "priority" => {
                input.parse::<Token![=]>()?;
                priority = Some(parse_priority_value(input.parse()?)?);
            }
            "nondet" => return Err(rule_key_error(NONDET_ON_FUNCTION, key.span())),
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
    }
    Ok(EquationAttribute { owise, priority })
}

impl KrsSyntax for SimplificationAttribute {
    /// Parses an empty simplification payload or exactly `priority = N`.
    ///
    /// # Errors
    ///
    /// Rejects `owise`, and unknown, malformed, repeated, or out-of-range payloads.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        structured(
            tokens,
            |input: ParseStream<'_>| -> Result<SimplificationAttribute, ParseError> {
                if input.is_empty() {
                    return Ok(SimplificationAttribute::default());
                }
                let key: Ident = input.parse()?;
                if key == "owise" {
                    return Err(rule_key_error(OWISE_ON_SIMPLIFICATION, key.span()));
                }
                if key == "nondet" {
                    return Err(rule_key_error(NONDET_ON_FUNCTION, key.span()));
                }
                if key != "priority" {
                    return Err(syn::Error::new(key.span(), "expected `priority = N`").into());
                }
                input.parse::<Token![=]>()?;
                let literal: LitInt = input.parse()?;
                if !input.is_empty() {
                    return Err(input
                        .error("simplification accepts only `priority = N`")
                        .into());
                }
                let value = literal.base10_parse::<u32>()?;
                Ok(SimplificationAttribute {
                    priority: Some((literal, value)),
                })
            },
        )
    }
}

impl KrsSyntax for AliasAttribute {
    /// Parses the intentionally empty alias payload.
    ///
    /// # Errors
    ///
    /// Rejects `priority` and `owise` (static rules have no priority),
    /// `nondet`, recursive mode, and every other payload at its first token.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        if let Some(proc_macro2::TokenTree::Ident(first)) = tokens.clone().into_iter().next() {
            let reason = if first == "priority" || first == "owise" {
                Some(PRIORITY_ON_STATIC_RULE)
            } else if first == "nondet" {
                Some(NONDET_ON_FUNCTION)
            } else {
                None
            };
            if let Some(reason) = reason {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::InvalidRuleKey { reason },
                    first.span(),
                ));
            }
        }
        parse_empty_tokens(tokens, "alias").map(|()| AliasAttribute)
    }
}

impl KrsSyntax for ContextAliasAttribute {
    /// Parses a checked context-alias payload.
    ///
    /// # Errors
    ///
    /// Requires exactly one unqualified identifier for each of `name` and `here`,
    /// and rejects unknown or repeated arguments at their own tokens.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        structured(tokens, parse_context_alias_stream)
    }
}

impl KrsSyntax for PriorityAttribute {
    /// Rejects the retired standalone priority attribute.
    ///
    /// # Errors
    ///
    /// Always returns [`SyntaxErrorKind::RetiredAttribute`], naming
    /// `#[k::equation(priority = N)]` with the authored value, at the payload.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        let span = tokens
            .clone()
            .into_iter()
            .next()
            .map_or_else(proc_macro2::Span::call_site, |token| token.span());
        let value = tokens.to_string();
        let value = if value.trim().is_empty() {
            "N".to_owned()
        } else {
            value.trim().to_owned()
        };
        Err(SyntaxError::new(
            SyntaxErrorKind::RetiredAttribute {
                attribute: "#[k::priority(..)]",
                replacement: format!("#[k::equation(priority = {value})]"),
            },
            span,
        ))
    }
}

fn parse_sort_stream(input: ParseStream<'_>) -> Result<SortAttribute, ParseError> {
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

fn parse_subsort_stream(input: ParseStream<'_>) -> Result<SubsortAttribute, ParseError> {
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

fn parse_context_alias_stream(input: ParseStream<'_>) -> Result<ContextAliasAttribute, ParseError> {
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
