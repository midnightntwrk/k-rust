use proc_macro2::TokenStream;
use syn::ext::IdentExt;
use syn::parse::{Parse, ParseStream, Parser};
use syn::spanned::Spanned;
use syn::{Expr, ExprLit, Ident, Lit, LitInt, LitStr, Path, Token};

use crate::parse::{KeyAllocator, KrsSyntax, ParseError, structured};
use crate::{ProvenanceAnchor, ProvenanceRole, SyntaxError, SyntaxErrorKind, TokenRange};
use krs_ir::ProvenanceKey;

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
    label_key: Option<ProvenanceKey>,
    owise_key: Option<ProvenanceKey>,
    priority_key: Option<ProvenanceKey>,
    nondet_key: Option<ProvenanceKey>,
    anywhere_key: Option<ProvenanceKey>,
    evaluation_key: Option<ProvenanceKey>,
    hole_key: Option<ProvenanceKey>,
    result_key: Option<ProvenanceKey>,
    /// The anchors of the attribute's keying, which [`Self::provenance`]
    /// returns.
    anchors: Vec<ProvenanceAnchor>,
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
    modality_key: Option<ProvenanceKey>,
    label_key: Option<ProvenanceKey>,
    circularity_key: Option<ProvenanceKey>,
    trusted_key: Option<ProvenanceKey>,
    /// The anchors of the attribute's keying, which [`Self::provenance`]
    /// returns.
    anchors: Vec<ProvenanceAnchor>,
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
    /// None: the attribute was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    /// The key of the modality identifier.
    #[must_use]
    pub const fn modality_key(&self) -> Option<&ProvenanceKey> {
        self.modality_key.as_ref()
    }

    /// The key of the label.
    #[must_use]
    pub const fn label_key(&self) -> Option<&ProvenanceKey> {
        self.label_key.as_ref()
    }

    /// The key of the `circularity` marker.
    #[must_use]
    pub const fn circularity_key(&self) -> Option<&ProvenanceKey> {
        self.circularity_key.as_ref()
    }

    /// The key of the `trusted` marker.
    #[must_use]
    pub const fn trusted_key(&self) -> Option<&ProvenanceKey> {
        self.trusted_key.as_ref()
    }

    /// Keys the modality, the label, then the modifiers.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        self.modality_key = Some(keys.key(
            ProvenanceRole::ClaimModality,
            TokenRange::for_tokens(&self.modality_ident)?,
        )?);
        self.label_key = Some(keys.key(
            ProvenanceRole::ClaimLabel,
            TokenRange::for_tokens(&self.label)?,
        )?);
        self.circularity_key = optional_key(
            &mut keys,
            ProvenanceRole::ClaimCircularity,
            self.circularity.as_ref(),
        )?;
        self.trusted_key = optional_key(
            &mut keys,
            ProvenanceRole::ClaimTrusted,
            self.trusted.as_ref(),
        )?;
        self.anchors = keys.into_anchors();
        Ok(self)
    }
}

/// One binder declared by `#[k::exists(name: Sort, ...)]`.
#[derive(Clone, Debug)]
pub struct ClaimBinder {
    name: Ident,
    sort: Path,
    key: Option<ProvenanceKey>,
    name_key: Option<ProvenanceKey>,
    sort_key: Option<ProvenanceKey>,
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

    /// The key of the binder declaration, given by the sentence that
    /// declares it (a rule's existential or fresh binder).
    #[must_use]
    pub const fn key(&self) -> Option<&ProvenanceKey> {
        self.key.as_ref()
    }

    /// The key of the binder's name.
    #[must_use]
    pub const fn name_key(&self) -> Option<&ProvenanceKey> {
        self.name_key.as_ref()
    }

    /// The key of the binder's sort.
    #[must_use]
    pub const fn sort_key(&self) -> Option<&ProvenanceKey> {
        self.sort_key.as_ref()
    }

    /// Forgets the binder's keys, before a sentence's pass keys it.
    pub(crate) fn clear_keys(&mut self) {
        self.key = None;
        self.name_key = None;
        self.sort_key = None;
    }

    /// Keys the binder declaration as the next of `role`.
    pub(crate) fn allocate_binder_key(
        &mut self,
        keys: &mut KeyAllocator,
        role: ProvenanceRole,
    ) -> Result<(), SyntaxError> {
        self.key = Some(keys.key(role, TokenRange::for_tokens(&self.name)?)?);
        Ok(())
    }

    /// Keys the binder's name, then its sort, each as the next of its role.
    pub(crate) fn allocate_name_and_sort_keys(
        &mut self,
        keys: &mut KeyAllocator,
        name_role: ProvenanceRole,
        sort_role: ProvenanceRole,
    ) -> Result<(), SyntaxError> {
        self.name_key = Some(keys.key(name_role, TokenRange::for_tokens(&self.name)?)?);
        self.sort_key = Some(keys.key(sort_role, TokenRange::for_tokens(&self.sort)?)?);
        Ok(())
    }

    /// Keys the binder, its name and its sort, each as the next of its role.
    pub(crate) fn allocate_keys(
        &mut self,
        keys: &mut KeyAllocator,
        binder_role: ProvenanceRole,
        name_role: ProvenanceRole,
        sort_role: ProvenanceRole,
    ) -> Result<(), SyntaxError> {
        let name = TokenRange::for_tokens(&self.name)?;
        self.key = Some(keys.key(binder_role, name)?);
        self.name_key = Some(keys.key(name_role, name)?);
        self.sort_key = Some(keys.key(sort_role, TokenRange::for_tokens(&self.sort)?)?);
        Ok(())
    }
}

/// Checked existential-binder helper payload.
#[derive(Clone, Debug)]
pub struct ExistsAttribute {
    binders: Vec<ClaimBinder>,
    /// The anchors of the attribute's keying, which [`Self::provenance`]
    /// returns.
    anchors: Vec<ProvenanceAnchor>,
}

impl ExistsAttribute {
    /// Returns declared binders in source order.
    #[must_use]
    pub fn binders(&self) -> &[ClaimBinder] {
        &self.binders
    }

    /// Declared binders in source order, for a pass that keys them.
    pub(crate) fn binders_mut(&mut self) -> &mut [ClaimBinder] {
        &mut self.binders
    }

    /// Forgets the binders' keys and the attribute's anchors, before the
    /// sentence that declares the binders keys them.
    pub(crate) fn clear_keys(&mut self) {
        for binder in &mut self.binders {
            binder.clear_keys();
        }
        self.anchors.clear();
    }

    /// Returns exact declaration/name/sort anchors.
    ///
    /// # Errors
    ///
    /// None: the attribute was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    /// Keys each binder, its name and its sort, as a sentence of its own.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        for binder in &mut self.binders {
            binder.allocate_keys(
                &mut keys,
                ProvenanceRole::ClaimExistentialBinder,
                ProvenanceRole::ClaimBinderName,
                ProvenanceRole::ClaimBinderSort,
            )?;
        }
        self.anchors = keys.into_anchors();
        Ok(self)
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
    /// None: the attribute was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    /// The key of the label.
    #[must_use]
    pub const fn label_key(&self) -> Option<&ProvenanceKey> {
        self.label_key.as_ref()
    }

    /// The key of the `owise` flag.
    #[must_use]
    pub const fn owise_key(&self) -> Option<&ProvenanceKey> {
        self.owise_key.as_ref()
    }

    /// The key of the `priority` value.
    #[must_use]
    pub const fn priority_key(&self) -> Option<&ProvenanceKey> {
        self.priority_key.as_ref()
    }

    /// The key of the `nondet` group.
    #[must_use]
    pub const fn nondet_key(&self) -> Option<&ProvenanceKey> {
        self.nondet_key.as_ref()
    }

    /// The key of the `anywhere` flag.
    #[must_use]
    pub const fn anywhere_key(&self) -> Option<&ProvenanceKey> {
        self.anywhere_key.as_ref()
    }

    /// The key of the `heat`/`cool` marker, or of a context's name.
    #[must_use]
    pub const fn evaluation_key(&self) -> Option<&ProvenanceKey> {
        self.evaluation_key.as_ref()
    }

    /// The key of the `hole` binder.
    #[must_use]
    pub const fn hole_key(&self) -> Option<&ProvenanceKey> {
        self.hole_key.as_ref()
    }

    /// The key of the `result` sort.
    #[must_use]
    pub const fn result_key(&self) -> Option<&ProvenanceKey> {
        self.result_key.as_ref()
    }

    /// Keys the label, `owise`, the priority, `nondet`, `anywhere`, the
    /// evaluation marker, the hole and the result, as a sentence of its own.
    /// A context (KF-021) keys its label, hole and result under the context
    /// roles.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        let kind = self.evaluation.as_ref().map(|(kind, _)| *kind);
        self.label_key = optional_key(
            &mut keys,
            if kind == Some(krs_ir::EvaluationKind::Context) {
                ProvenanceRole::ContextLabel
            } else {
                ProvenanceRole::RuleLabel
            },
            self.label.as_ref(),
        )?;
        self.owise_key = optional_key(&mut keys, ProvenanceRole::RuleOwise, self.owise.as_ref())?;
        self.priority_key = optional_key(
            &mut keys,
            ProvenanceRole::RulePriority,
            self.priority.as_ref().map(|priority| &priority.literal),
        )?;
        self.nondet_key = optional_key(
            &mut keys,
            ProvenanceRole::RuleNondetGroup,
            self.nondet.as_ref(),
        )?;
        self.anywhere_key = optional_key(
            &mut keys,
            ProvenanceRole::RuleAnywhere,
            self.anywhere.as_ref(),
        )?;
        self.evaluation_key = match &self.evaluation {
            Some((kind, marker)) => Some(keys.key(kind.role(), TokenRange::for_tokens(marker)?)?),
            None => None,
        };
        let kind = kind.unwrap_or(krs_ir::EvaluationKind::Heat);
        self.hole_key = optional_key(&mut keys, kind.hole_role(), self.hole.as_ref())?;
        self.result_key = optional_key(&mut keys, kind.result_role(), self.result.as_ref())?;
        self.anchors = keys.into_anchors();
        Ok(self)
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
        Self::parse_with_label(tokens, None)
    }
}

impl ClaimAttribute {
    /// Parses the `#[k::claim(..)]` of a `k::claims!` clause (F7), whose
    /// label is the clause name with `_` written `-`, as a readable rule's
    /// is: the attribute gives the modality and flags only.
    ///
    /// # Errors
    ///
    /// The errors of [`KrsSyntax::parse_tokens`], a `label` key, and a clause
    /// name that is no portable K label.
    pub fn parse_clause_tokens(tokens: TokenStream, name: &Ident) -> Result<Self, SyntaxError> {
        Self::parse_with_label(tokens, Some(name))
    }

    #[expect(
        clippy::too_many_lines,
        reason = "Every claim key is checked in one pass that keeps its diagnostic at its token."
    )]
    fn parse_with_label(tokens: TokenStream, clause: Option<&Ident>) -> Result<Self, SyntaxError> {
        let error = |span, message| ParseError::from(syn::Error::new(span, message));
        let parser = |input: ParseStream<'_>| -> Result<ClaimAttribute, ParseError> {
            let mut modality = None;
            let mut label = None;
            let mut circularity = None;
            let mut trusted = None;
            while !input.is_empty() {
                let key: Ident = input.parse()?;
                match key.to_string().as_str() {
                    "all_paths" | "one_path" => {
                        if modality.is_some() {
                            return Err(error(key.span(), "a claim requires exactly one modality"));
                        }
                        let value = if key == "all_paths" {
                            ClaimModality::AllPaths
                        } else {
                            ClaimModality::OnePath
                        };
                        modality = Some((value, key));
                    }
                    "label" if clause.is_some() => {
                        return Err(error(
                            key.span(),
                            "a `k::claims!` clause is labelled by its name: rename the clause instead of writing `label`",
                        ));
                    }
                    "label" => {
                        if label.is_some() {
                            return Err(error(key.span(), "duplicate claim label"));
                        }
                        input.parse::<Token![=]>()?;
                        let literal: LitStr = input.parse()?;
                        if !valid_claim_label(&literal.value()) {
                            return Err(error(literal.span(), "invalid portable K claim label"));
                        }
                        label = Some(literal);
                    }
                    "circularity" => {
                        if circularity.is_some() {
                            return Err(error(key.span(), "duplicate circularity modifier"));
                        }
                        circularity = Some(key);
                    }
                    "trusted" => {
                        if trusted.is_some() {
                            return Err(error(key.span(), "duplicate trusted modifier"));
                        }
                        if input.peek(Token![=]) {
                            return Err(error(
                                key.span(),
                                "`trusted` is a bare flag; write `trusted` without a value",
                            ));
                        }
                        trusted = Some(key);
                    }
                    "unbound_variables" => {
                        return Err(
                            super::sort::unbound_variables_outside_desugar(key.span()).into()
                        );
                    }
                    _ => {
                        return Err(error(key.span(), "unknown claim argument"));
                    }
                }
                if input.is_empty() {
                    break;
                }
                input.parse::<Token![,]>()?;
            }
            let (modality, modality_ident) =
                modality.ok_or_else(|| input.error("claim requires `all_paths` or `one_path`"))?;
            let label = match clause {
                Some(name) => {
                    let spelling = name.unraw().to_string().replace('_', "-");
                    if !valid_claim_label(&spelling) {
                        return Err(error(name.span(), "invalid portable K claim label"));
                    }
                    LitStr::new(&spelling, name.span())
                }
                None => label
                    .ok_or_else(|| input.error("claim requires an explicit `label = \"...\"`"))?,
            };
            if modality == ClaimModality::OnePath
                && let Some(circularity) = &circularity
            {
                return Err(error(
                    circularity.span(),
                    "circularity is valid only on an all-path claim",
                ));
            }
            if let (Some(trusted), Some(_)) = (&trusted, &circularity) {
                return Err(error(
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
                modality_key: None,
                label_key: None,
                circularity_key: None,
                trusted_key: None,
                anchors: Vec::new(),
            }
            .keyed()?)
        };
        structured(tokens, parser)
    }
}

fn valid_claim_label(value: &str) -> bool {
    !value.trim().is_empty()
        && !value.chars().any(char::is_whitespace)
        // K's outer `[label]:` syntax excludes `_`; otherwise native structured
        // proving accepts a label whose emitted K cannot be parsed back.
        && !value.contains(['[', ']', ':', '_'])
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
                binders.push(ClaimBinder {
                    name,
                    sort,
                    key: None,
                    name_key: None,
                    sort_key: None,
                });
                if input.is_empty() {
                    break;
                }
                input.parse::<Token![,]>()?;
            }
            if binders.is_empty() {
                return Err(input.error("exists requires at least one `name: Sort` binder"));
            }
            Ok(ExistsAttribute {
                binders,
                anchors: Vec::new(),
            })
        };
        let exists = parser.parse2(tokens).map_err(SyntaxError::from)?;
        for binder in &exists.binders {
            crate::parse::validate_authored_binder(&binder.name.to_string(), binder.name.span())?;
        }
        exists.keyed()
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
        ..RuleAttribute::default()
    };
    attribute.check_evaluation()?;
    attribute.reject_ordered_anywhere()?;
    Ok(attribute.keyed()?)
}

/// Typed metadata of `#[k::context(hole = x, result = S, label = "...")]`
/// (KF-021): K's `context`, which says where evaluation may happen.
#[derive(Clone, Debug)]
pub struct ContextAttribute {
    hole: Ident,
    result: Option<Path>,
    label: Option<LitStr>,
    label_key: Option<ProvenanceKey>,
    hole_key: Option<ProvenanceKey>,
    result_key: Option<ProvenanceKey>,
}

impl ContextAttribute {
    /// Returns the binder named by `hole = x`, K's `HOLE`.
    #[must_use]
    pub const fn hole(&self) -> &Ident {
        &self.hole
    }

    /// Returns the sort path of `result = S`, K's `result(S)`.
    #[must_use]
    pub const fn result_sort(&self) -> Option<&Path> {
        self.result.as_ref()
    }

    /// Returns the explicit `label = "..."`.
    #[must_use]
    pub const fn label(&self) -> Option<&LitStr> {
        self.label.as_ref()
    }

    /// The key of the label, in the context's rule-attribute view.
    #[must_use]
    pub const fn label_key(&self) -> Option<&ProvenanceKey> {
        self.label_key.as_ref()
    }

    /// The key of the hole binder, in the context's rule-attribute view.
    #[must_use]
    pub const fn hole_key(&self) -> Option<&ProvenanceKey> {
        self.hole_key.as_ref()
    }

    /// The key of the result sort, in the context's rule-attribute view.
    #[must_use]
    pub const fn result_key(&self) -> Option<&ProvenanceKey> {
        self.result_key.as_ref()
    }

    /// The rule-attribute view of this context, whose evaluation step is
    /// marked by the context fn's name: the expansion of a context shares
    /// the rule expansion, under the context roles. The view is keyed as a
    /// sentence of its own; the label, hole and result hold the same keys
    /// there as in the context, each the first of its role.
    ///
    /// # Panics
    ///
    /// Never: the label, the hole, the result and `name` are parsed tokens,
    /// and each is the first of its role.
    #[must_use]
    pub fn rule_attribute(&self, name: &Ident) -> RuleAttribute {
        RuleAttribute {
            label: self.label.clone(),
            evaluation: Some((krs_ir::EvaluationKind::Context, name.clone())),
            hole: Some(self.hole.clone()),
            result: self.result.clone(),
            ..RuleAttribute::default()
        }
        .keyed()
        .expect("a context's rule attribute keys parsed tokens")
    }

    /// Keys the label, the hole and the result under the context roles, as
    /// the context's rule-attribute view keys them.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        let kind = krs_ir::EvaluationKind::Context;
        self.label_key =
            optional_key(&mut keys, ProvenanceRole::ContextLabel, self.label.as_ref())?;
        self.hole_key = Some(keys.key(kind.hole_role(), TokenRange::for_tokens(&self.hole)?)?);
        self.result_key = optional_key(&mut keys, kind.result_role(), self.result.as_ref())?;
        Ok(self)
    }
}

impl Parse for ContextAttribute {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        parse_context_stream(input).map_err(syn::Error::from)
    }
}

impl KrsSyntax for ContextAttribute {
    /// Parses `hole = x`, an optional `result = S`, and an optional
    /// `label = "..."`.
    ///
    /// # Errors
    ///
    /// Rejects unknown or repeated keys, a malformed value, and a missing
    /// `hole`.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        structured(tokens, parse_context_stream)
    }
}

fn parse_context_stream(input: ParseStream<'_>) -> Result<ContextAttribute, ParseError> {
    let missing_span = input.span();
    let mut hole: Option<Ident> = None;
    let mut result: Option<Path> = None;
    let mut label: Option<LitStr> = None;
    while !input.is_empty() {
        let key: Ident = input.parse()?;
        let key_name = key.to_string();
        let duplicate = match key_name.as_str() {
            "hole" => hole.is_some().then_some("hole"),
            "result" => result.is_some().then_some("result"),
            "label" => label.is_some().then_some("label"),
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
        };
        if let Some(name) = duplicate {
            return Err(
                SyntaxError::new(SyntaxErrorKind::DuplicateArgument { name }, key.span()).into(),
            );
        }
        input.parse::<Token![=]>()?;
        let value: Expr = input.parse()?;
        match key_name.as_str() {
            "hole" => {
                hole = Some(super::value::parse_unqualified_identifier_value(
                    "hole", value,
                )?);
            }
            "result" => result = Some(parse_result_sort(value)?),
            _ => label = Some(parse_rule_label_value(value)?),
        }
        if input.is_empty() {
            break;
        }
        input.parse::<Token![,]>()?;
    }
    Ok(ContextAttribute {
        hole: hole.ok_or_else(|| {
            SyntaxError::new(
                SyntaxErrorKind::MissingArgument { name: "hole" },
                missing_span,
            )
        })?,
        result,
        label,
        label_key: None,
        hole_key: None,
        result_key: None,
    }
    .keyed()?)
}

/// Parses the sort path of `result = S`: a plain Rust path, as in
/// `#[k::strict(result = S)]`.
pub(super) fn parse_result_sort(value: Expr) -> Result<Path, ParseError> {
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

#[cfg(test)]
impl ClaimBinder {
    /// Records the keys of the binder and its name, at the name, and of its
    /// sort.
    pub(crate) fn keyed_nodes(
        &self,
        nodes: &mut crate::keyed_nodes::KeyedNodes,
    ) -> Result<(), SyntaxError> {
        nodes.push_tokens(self.key.as_ref(), &self.name)?;
        nodes.push_tokens(self.name_key.as_ref(), &self.name)?;
        nodes.push_tokens(self.sort_key.as_ref(), &self.sort)
    }
}

#[cfg(test)]
impl RuleAttribute {
    /// Records the keys of the label, `owise`, the priority, `nondet`,
    /// `anywhere`, the evaluation marker, the hole and the result.
    pub(crate) fn keyed_nodes(
        &self,
        nodes: &mut crate::keyed_nodes::KeyedNodes,
    ) -> Result<(), SyntaxError> {
        if let Some(label) = &self.label {
            nodes.push_tokens(self.label_key.as_ref(), label)?;
        }
        if let Some(owise) = &self.owise {
            nodes.push_tokens(self.owise_key.as_ref(), owise)?;
        }
        if let Some(priority) = &self.priority {
            nodes.push_tokens(self.priority_key.as_ref(), &priority.literal)?;
        }
        if let Some(nondet) = &self.nondet {
            nodes.push_tokens(self.nondet_key.as_ref(), nondet)?;
        }
        if let Some(anywhere) = &self.anywhere {
            nodes.push_tokens(self.anywhere_key.as_ref(), anywhere)?;
        }
        if let Some((_, marker)) = &self.evaluation {
            nodes.push_tokens(self.evaluation_key.as_ref(), marker)?;
        }
        if let Some(hole) = &self.hole {
            nodes.push_tokens(self.hole_key.as_ref(), hole)?;
        }
        if let Some(result) = &self.result {
            nodes.push_tokens(self.result_key.as_ref(), result)?;
        }
        Ok(())
    }
}

#[cfg(test)]
impl ClaimAttribute {
    /// Records the keys of the modality, the label and the modifiers.
    pub(crate) fn keyed_nodes(
        &self,
        nodes: &mut crate::keyed_nodes::KeyedNodes,
    ) -> Result<(), SyntaxError> {
        nodes.push_tokens(self.modality_key.as_ref(), &self.modality_ident)?;
        nodes.push_tokens(self.label_key.as_ref(), &self.label)?;
        if let Some(circularity) = &self.circularity {
            nodes.push_tokens(self.circularity_key.as_ref(), circularity)?;
        }
        if let Some(trusted) = &self.trusted {
            nodes.push_tokens(self.trusted_key.as_ref(), trusted)?;
        }
        Ok(())
    }
}

#[cfg(test)]
impl ExistsAttribute {
    /// Records the keys of each binder, its name and its sort.
    pub(crate) fn keyed_nodes(
        &self,
        nodes: &mut crate::keyed_nodes::KeyedNodes,
    ) -> Result<(), SyntaxError> {
        for binder in &self.binders {
            binder.keyed_nodes(nodes)?;
        }
        Ok(())
    }
}

#[cfg(test)]
impl ContextAttribute {
    /// Records the keys of the label, the hole and the result, which they
    /// hold in the context's rule-attribute view.
    pub(crate) fn keyed_nodes(
        &self,
        nodes: &mut crate::keyed_nodes::KeyedNodes,
    ) -> Result<(), SyntaxError> {
        if let Some(label) = &self.label {
            nodes.push_tokens(self.label_key.as_ref(), label)?;
        }
        nodes.push_tokens(self.hole_key.as_ref(), &self.hole)?;
        if let Some(result) = &self.result {
            nodes.push_tokens(self.result_key.as_ref(), result)?;
        }
        Ok(())
    }
}
