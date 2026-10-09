use proc_macro2::TokenStream;
use syn::parse::{Parse, ParseStream, Parser};
use syn::spanned::Spanned;
use syn::{Expr, ExprLit, Ident, Lit, LitInt, LitStr, Path, Token};

use crate::parse::{KrsSyntax, ParseError, checked_ordinal, structured};
use crate::{ProvenanceAnchor, ProvenanceRole, SyntaxError, SyntaxErrorKind, TokenRange};

use super::value::parse_rule_label_value;

/// Typed metadata of `#[k::rule(owise | priority = N, heat | cool, hole = x,
/// result = S, anywhere, nondet = group, label = "...")]`.
#[derive(Clone, Debug, Default)]
pub struct RuleAttribute {
    label: Option<LitStr>,
    owise: Option<Ident>,
    priority: Option<PriorityValue>,
    nondet: Option<Ident>,
    anywhere: Option<Ident>,
    evaluation: Option<(krs_ir::EvaluationKind, Ident)>,
    hole: Option<Ident>,
    result: Option<Path>,
}

/// One authored `priority = N` integer and its parsed value.
#[derive(Clone, Debug)]
pub(crate) struct PriorityValue {
    pub(crate) literal: LitInt,
    pub(crate) value: u32,
}

/// The priority K gives an `owise` rule or equation.
pub const OWISE_PRIORITY: u32 = 200;

/// The largest rule priority k-rust ranks.
pub const MAX_RULE_PRIORITY: u32 = 254;

pub(crate) const OWISE_WITH_PRIORITY: &str = "owise is priority 200; write one of them";
pub(crate) const PRIORITY_RANGE: &str = "k-rust ranks rule priorities 0..=254";
pub(crate) const OWISE_ON_SIMPLIFICATION: &str =
    "a simplification has its own `priority = N`, a simplifier hint; owise has no meaning there";
pub(crate) const PRIORITY_ON_STATIC_RULE: &str = "static rules have no priority";
pub(crate) const RESTRICTION_ON_RULE: &str = "restrictions apply to equations and simplifications: `concrete`, `symbolic`, and `smt_lemma` are keys of #[k::equation] and #[k::simplification]";
pub(crate) const NONDET_ON_FUNCTION: &str =
    "functions are deterministic in K; overlapping equations make the function ill-defined";
pub(crate) const ANYWHERE_WITH_ORDER: &str = "an anywhere rule applies to any subterm, outside rule priority and the overlap check; it takes no `owise`, `priority`, or `nondet`";
pub(crate) const HEAT_WITH_COOL: &str =
    "a rule is a heating step or a cooling step, not both; write `heat` or `cool`";
pub(crate) const EVALUATION_WITHOUT_HOLE: &str = "a heat or cool rule names the subterm it moves with `hole = x`, K's HOLE; bind `x` on the left side";
pub(crate) const HOLE_WITHOUT_EVALUATION: &str =
    "`hole` and `result` are keys of a heat or cool rule; add `heat` or `cool`";
pub(crate) const EVALUATION_WITH_ORDER: &str = "a heat or cool rule is ordered by its hole: K adds `requires notBool isKResult(HOLE)` to heating and `requires isKResult(HOLE)` to cooling; it takes no `owise`, `priority`, `nondet`, or `anywhere`";
/// The diagnostic for `anywhere` on a readable clause or a `cells!` rule.
pub const ANYWHERE_NOT_TERM_SHAPED: &str =
    "an anywhere rule applies to any subterm; write it term-shaped with #[k::rule(anywhere)] fn";

/// Parses the value of one `priority = N` key.
pub(crate) fn parse_priority_value(value: Expr) -> Result<PriorityValue, ParseError> {
    let Expr::Lit(ExprLit {
        attrs,
        lit: Lit::Int(literal),
    }) = value
    else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name: "priority",
                expected: "an unsuffixed integer literal",
            },
            value.span(),
        )
        .into());
    };
    if !attrs.is_empty() || !literal.suffix().is_empty() {
        return Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name: "priority",
                expected: "an unsuffixed integer literal",
            },
            literal.span(),
        )
        .into());
    }
    let value = literal
        .base10_parse::<u32>()
        .ok()
        .filter(|value| *value <= MAX_RULE_PRIORITY)
        .ok_or_else(|| {
            SyntaxError::new(
                SyntaxErrorKind::InvalidRuleKey {
                    reason: PRIORITY_RANGE,
                },
                literal.span(),
            )
        })?;
    Ok(PriorityValue { literal, value })
}

pub(crate) fn rule_key_error(reason: &'static str, span: proc_macro2::Span) -> ParseError {
    SyntaxError::new(SyntaxErrorKind::InvalidRuleKey { reason }, span).into()
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
    trusted: Option<Ident>,
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
    /// Whether the claim carries the trusted modifier: it is assumed without
    /// proof.
    #[must_use]
    pub const fn trusted(&self) -> bool {
        self.trusted.is_some()
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
        if let Some(marker) = &self.trusted {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::ClaimTrusted,
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

    /// Returns the explicit `priority = N` value, when authored.
    #[must_use]
    pub fn priority(&self) -> Option<u32> {
        self.priority.as_ref().map(|priority| priority.value)
    }

    /// Returns the `nondet = group` identifier, when authored.
    #[must_use]
    pub const fn nondet(&self) -> Option<&Ident> {
        self.nondet.as_ref()
    }

    /// Returns the `anywhere` marker, when authored.
    #[must_use]
    pub const fn anywhere(&self) -> Option<&Ident> {
        self.anywhere.as_ref()
    }

    /// Returns the `heat` or `cool` marker of an evaluation step (KF-014).
    #[must_use]
    pub fn evaluation(&self) -> Option<(krs_ir::EvaluationKind, &Ident)> {
        self.evaluation
            .as_ref()
            .map(|(kind, marker)| (*kind, marker))
    }

    /// Returns the binder named by `hole = x` on a heat or cool rule.
    #[must_use]
    pub const fn hole(&self) -> Option<&Ident> {
        self.hole.as_ref()
    }

    /// Returns the sort path of `result = S` on a heat or cool rule.
    #[must_use]
    pub const fn result_sort(&self) -> Option<&Path> {
        self.result.as_ref()
    }

    /// Returns the effective authored transition priority and the role that
    /// anchors it: `owise` is priority 200 under [`ProvenanceRole::RuleOwise`],
    /// and `priority = N` is N under [`ProvenanceRole::RulePriority`].
    #[must_use]
    pub fn transition_priority(&self) -> Option<(ProvenanceRole, u32)> {
        if self.owise.is_some() {
            return Some((ProvenanceRole::RuleOwise, OWISE_PRIORITY));
        }
        self.priority
            .as_ref()
            .map(|priority| (ProvenanceRole::RulePriority, priority.value))
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
        if let Some(priority) = &self.priority {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::RulePriority,
                0,
                TokenRange::for_tokens(&priority.literal)?,
            ));
        }
        if let Some(nondet) = &self.nondet {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::RuleNondetGroup,
                0,
                TokenRange::for_tokens(nondet)?,
            ));
        }
        if let Some(anywhere) = &self.anywhere {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::RuleAnywhere,
                0,
                TokenRange::for_tokens(anywhere)?,
            ));
        }
        if let Some((kind, marker)) = &self.evaluation {
            anchors.push(ProvenanceAnchor::new(
                kind.role(),
                0,
                TokenRange::for_tokens(marker)?,
            ));
        }
        if let Some(hole) = &self.hole {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::RuleHole,
                0,
                TokenRange::for_tokens(hole)?,
            ));
        }
        if let Some(result) = &self.result {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::RuleResultSort,
                0,
                TokenRange::for_tokens(result)?,
            ));
        }
        Ok(anchors)
    }
}

impl RuleAttribute {
    /// An anywhere rule is outside rule priority and the overlap check.
    fn reject_ordered_anywhere(&self) -> Result<(), ParseError> {
        if self.anywhere.is_none() {
            return Ok(());
        }
        let ordered = self
            .owise
            .as_ref()
            .map(Ident::span)
            .or_else(|| {
                self.priority
                    .as_ref()
                    .map(|priority| priority.literal.span())
            })
            .or_else(|| self.nondet.as_ref().map(Ident::span));
        ordered.map_or(Ok(()), |span| {
            Err(rule_key_error(ANYWHERE_WITH_ORDER, span))
        })
    }

    /// A heat or cool rule names its hole and is ordered by K's
    /// result-sort condition on it, never by priority (KF-014).
    fn check_evaluation(&self) -> Result<(), ParseError> {
        let Some((_, marker)) = &self.evaluation else {
            let stray = self
                .hole
                .as_ref()
                .map(Ident::span)
                .or_else(|| self.result.as_ref().map(Spanned::span));
            return stray.map_or(Ok(()), |span| {
                Err(rule_key_error(HOLE_WITHOUT_EVALUATION, span))
            });
        };
        if self.hole.is_none() {
            return Err(rule_key_error(EVALUATION_WITHOUT_HOLE, marker.span()));
        }
        let ordered = self
            .owise
            .as_ref()
            .map(Ident::span)
            .or_else(|| {
                self.priority
                    .as_ref()
                    .map(|priority| priority.literal.span())
            })
            .or_else(|| self.nondet.as_ref().map(Ident::span))
            .or_else(|| self.anywhere.as_ref().map(Ident::span));
        ordered.map_or(Ok(()), |span| {
            Err(rule_key_error(EVALUATION_WITH_ORDER, span))
        })
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
            let mut trusted = None;
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
                    "trusted" => {
                        if trusted.is_some() {
                            return Err(syn::Error::new(key.span(), "duplicate trusted modifier"));
                        }
                        if input.peek(Token![=]) {
                            return Err(syn::Error::new(
                                key.span(),
                                "`trusted` is a bare flag; write `trusted` without a value",
                            ));
                        }
                        trusted = Some(key);
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
            if let (Some(trusted), Some(_)) = (&trusted, &circularity) {
                return Err(syn::Error::new(
                    trusted.span(),
                    "a trusted claim is assumed, not proved; circularity has no effect",
                ));
            }
            Ok(ClaimAttribute {
                modality,
                modality_ident,
                label,
                circularity,
                trusted,
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
        let exists = parser.parse2(tokens).map_err(SyntaxError::from)?;
        for binder in &exists.binders {
            crate::parse::validate_authored_binder(&binder.name.to_string(), binder.name.span())?;
        }
        Ok(exists)
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

#[expect(
    clippy::too_many_lines,
    reason = "Each rule key keeps its duplicate and value checks beside its match arm."
)]
fn parse_rule_stream(input: ParseStream<'_>) -> Result<RuleAttribute, ParseError> {
    let mut label = None;
    let mut owise = None;
    let mut priority: Option<PriorityValue> = None;
    let mut nondet = None;
    let mut anywhere: Option<Ident> = None;
    let mut evaluation: Option<(krs_ir::EvaluationKind, Ident)> = None;
    let mut hole: Option<Ident> = None;
    let mut result: Option<Path> = None;
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
            "owise" if priority.is_some() => {
                return Err(rule_key_error(OWISE_WITH_PRIORITY, key.span()));
            }
            "owise" => owise = Some(key),
            "priority" if priority.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "priority" },
                    key.span(),
                )
                .into());
            }
            "priority" if owise.is_some() => {
                return Err(rule_key_error(OWISE_WITH_PRIORITY, key.span()));
            }
            "priority" => {
                input.parse::<Token![=]>()?;
                priority = Some(parse_priority_value(input.parse()?)?);
            }
            "anywhere" if anywhere.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "anywhere" },
                    key.span(),
                )
                .into());
            }
            "anywhere" => anywhere = Some(key),
            "heat" | "cool" if evaluation.is_some() => {
                return Err(rule_key_error(HEAT_WITH_COOL, key.span()));
            }
            "heat" => evaluation = Some((krs_ir::EvaluationKind::Heat, key)),
            "cool" => evaluation = Some((krs_ir::EvaluationKind::Cool, key)),
            "hole" if hole.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "hole" },
                    key.span(),
                )
                .into());
            }
            "hole" => {
                input.parse::<Token![=]>()?;
                let value: Expr = input.parse()?;
                hole = Some(super::value::parse_unqualified_identifier_value(
                    "hole", value,
                )?);
            }
            "result" if result.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "result" },
                    key.span(),
                )
                .into());
            }
            "result" => {
                input.parse::<Token![=]>()?;
                result = Some(parse_result_sort(input.parse()?)?);
            }
            "nondet" if nondet.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "nondet" },
                    key.span(),
                )
                .into());
            }
            "nondet" => {
                input.parse::<Token![=]>()?;
                let value: Expr = input.parse()?;
                nondet = Some(super::value::parse_unqualified_identifier_value(
                    "nondet", value,
                )?);
            }
            "concrete" | "symbolic" | "smt_lemma" => {
                return Err(rule_key_error(RESTRICTION_ON_RULE, key.span()));
            }
            "unbound_variables" => {
                return Err(super::sort::unbound_variables_outside_desugar(key.span()).into());
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
    let attribute = RuleAttribute {
        label,
        owise,
        priority,
        nondet,
        anywhere,
        evaluation,
        hole,
        result,
    };
    attribute.check_evaluation()?;
    attribute.reject_ordered_anywhere()?;
    Ok(attribute)
}

/// Parses the sort path of `result = S`: a plain Rust path, as in
/// `#[k::strict(result = S)]`.
fn parse_result_sort(value: Expr) -> Result<Path, ParseError> {
    match value {
        Expr::Path(syn::ExprPath {
            attrs,
            qself: None,
            path,
        }) if attrs.is_empty() => Ok(path),
        value => Err(SyntaxError::new(
            SyntaxErrorKind::InvalidArgumentValue {
                name: "result",
                expected: "a sort path",
            },
            value.span(),
        )
        .into()),
    }
}
