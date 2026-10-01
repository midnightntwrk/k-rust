use proc_macro2::TokenStream;
use syn::parse::{Parse, ParseStream, Parser};
use syn::{Expr, Ident, LitStr, Path, Token};

use crate::parse::{KrsSyntax, ParseError, checked_ordinal, structured};
use crate::{ProvenanceAnchor, ProvenanceRole, SyntaxError, SyntaxErrorKind, TokenRange};

use super::value::parse_rule_label_value;

/// Typed metadata of `#[k::rule(label = "...", owise)]`.
#[derive(Clone, Debug, Default)]
pub struct RuleAttribute {
    label: Option<LitStr>,
    owise: Option<Ident>,
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
            let ordinal = checked_ordinal(
                index,
                ProvenanceRole::ClaimExistentialBinder,
                binder.name.span(),
            )?;
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

    /// Whether this transition is an ordered fallback (`[owise]` in K).
    #[must_use]
    pub const fn is_owise(&self) -> bool {
        self.owise.is_some()
    }

    /// Returns the exact explicit-label provenance anchor.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if the parsed literal emits no tokens.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = Vec::with_capacity(2);
        if let Some(label) = &self.label {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::RuleLabel,
                0,
                TokenRange::for_tokens(label)?,
            ));
        }
        if let Some(owise) = &self.owise {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::RuleOwise,
                0,
                TokenRange::for_tokens(owise)?,
            ));
        }
        Ok(anchors)
    }
}

impl Parse for RuleAttribute {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        parse_rule_stream(input).map_err(syn::Error::from)
    }
}

impl KrsSyntax for ClaimAttribute {
    /// Parses the frozen explicit claim metadata contract.
    ///
    /// # Errors
    ///
    /// Rejects missing, duplicate, unknown, or incompatible claim arguments and
    /// labels outside the portable K label subset.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
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
}

fn valid_claim_label(value: &str) -> bool {
    !value.trim().is_empty()
        && !value.chars().any(char::is_whitespace)
        && !value.contains(['[', ']', ':'])
}

impl KrsSyntax for ExistsAttribute {
    /// Parses one or more typed existential binders.
    ///
    /// # Errors
    ///
    /// Rejects an empty payload, duplicate names, and malformed `name: Sort`
    /// entries.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
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
}

impl KrsSyntax for RuleAttribute {
    /// Parses an optional explicit rule-label payload.
    ///
    /// # Errors
    ///
    /// Accepts empty payloads and exactly `label = "..."`.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        structured(tokens, parse_rule_stream)
    }
}

fn parse_rule_stream(input: ParseStream<'_>) -> Result<RuleAttribute, ParseError> {
    let mut label = None;
    let mut owise = None;
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
            "label" => {
                input.parse::<Token![=]>()?;
                let value: Expr = input.parse()?;
                label = Some(parse_rule_label_value(value)?);
            }
            "owise" if owise.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "owise" },
                    key.span(),
                )
                .into());
            }
            "owise" => owise = Some(key),
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
    Ok(RuleAttribute { label, owise })
}
