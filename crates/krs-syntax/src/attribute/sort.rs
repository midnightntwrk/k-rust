use proc_macro2::TokenStream;
use syn::parse::{Parse, ParseStream, Parser};
use syn::{Expr, Ident, LitInt, LitStr, Path, Token};

use crate::parse::{KrsSyntax, ParseError, structured};
use crate::{ProvenanceAnchor, ProvenanceRole, SyntaxError, SyntaxErrorKind, TokenRange};

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
    /// Parses the intentionally empty equation payload.
    ///
    /// # Errors
    ///
    /// Rejects labels and every other payload at its first token.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        parse_empty_tokens(tokens, "equation").map(|()| EquationAttribute)
    }
}

impl KrsSyntax for SimplificationAttribute {
    /// Parses an empty simplification payload or exactly `priority = N`.
    ///
    /// # Errors
    ///
    /// Rejects unknown, malformed, repeated, or out-of-range payloads.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
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
}

impl KrsSyntax for AliasAttribute {
    /// Parses the intentionally empty alias payload.
    ///
    /// # Errors
    ///
    /// Rejects recursive mode and every other payload at its first token.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
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
    /// Parses one exact unsigned equation priority.
    ///
    /// # Errors
    ///
    /// Rejects missing, noninteger, repeated, or out-of-range values.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
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
