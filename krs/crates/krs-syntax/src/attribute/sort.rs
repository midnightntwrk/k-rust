use krs_ir::ProvenanceKey;
use proc_macro2::TokenStream;
use syn::ext::IdentExt as _;
use syn::parse::{Parse, ParseStream, Parser};
use syn::{Expr, Ident, LitInt, LitStr, Path, Token};

use crate::parse::{KeyAllocator, KrsSyntax, ParseError, structured};
use crate::{ProvenanceAnchor, ProvenanceRole, SyntaxError, SyntaxErrorKind, TokenRange};

use super::rule::{
    NONDET_ON_FUNCTION, OWISE_ON_SIMPLIFICATION, OWISE_PRIORITY, OWISE_WITH_PRIORITY,
    PRIORITY_ON_STATIC_RULE, PriorityValue, parse_priority_value, rule_key_error,
};

use super::value::{
    parse_empty_tokens, parse_parent_paths_value, parse_sort_value,
    parse_unqualified_identifier_value,
};

/// Checked payload of `#[k::sort(alias = Expr[, parents = [..]])]`.
///
/// The attributed marker trait `ExprSort` represents the sort, and the
/// public alias `pub type Expr = k::Term<dyn ExprSort>;` beside it names it
/// (B2). `parents` materializes one semantic parent path for each marker
/// supertrait.
#[derive(Clone, Debug)]
pub struct SortAttribute {
    alias: Option<Ident>,
    parents: Vec<Path>,
    alias_key: Option<ProvenanceKey>,
    parent_keys: Vec<ProvenanceKey>,
    /// The anchors of the sort's keying, which [`Self::provenance`] returns.
    anchors: Vec<ProvenanceAnchor>,
}

impl SortAttribute {
    /// Returns the sort's alias as authored, if any; [`Self::checked_alias`]
    /// requires one.
    #[must_use]
    pub const fn alias(&self) -> Option<&Ident> {
        self.alias.as_ref()
    }

    /// Returns explicitly materialized semantic parent-sort paths.
    #[must_use]
    pub fn parents(&self) -> &[Path] {
        &self.parents
    }

    /// Returns the sort's alias, checked against the attributed marker
    /// trait: `#[k::sort(alias = Expr)]` sits on `trait ExprSort`.
    ///
    /// # Errors
    ///
    /// Rejects a missing `alias` and a marker trait whose name is not the
    /// alias followed by `Sort`, naming the expected spelling.
    pub fn checked_alias(&self, marker: &Ident) -> Result<&Ident, SyntaxError> {
        let marker_name = marker.unraw().to_string();
        let Some(alias) = &self.alias else {
            let stem = marker_name
                .strip_suffix("Sort")
                .filter(|stem| !stem.is_empty())
                .unwrap_or(&marker_name);
            return Err(SyntaxError::new(
                SyntaxErrorKind::UnaliasedSort {
                    reason: format!(
                        "`#[k::sort]` names the sort's alias on its marker trait: write `#[k::sort(alias = {stem})] pub trait {stem}Sort {{}}` with `pub type {stem} = k::Term<dyn {stem}Sort>;`, or declare `{stem}` in `k::sorts!`"
                    ),
                },
                marker.span(),
            ));
        };
        let expected = format!("{}Sort", alias.unraw());
        if marker_name != expected {
            return Err(SyntaxError::new(
                SyntaxErrorKind::UnaliasedSort {
                    reason: format!(
                        "the marker trait of the sort alias `{alias}` is named `{expected}`, so that `dyn {expected}` names the sort"
                    ),
                },
                marker.span(),
            ));
        }
        Ok(alias)
    }

    /// Returns the sort-declaration anchor at the alias and one parent
    /// anchor per materialized parent path.
    ///
    /// # Errors
    ///
    /// Rejects a missing alias as [`Self::checked_alias`] does, and returns
    /// an endpoint error only if a parsed node emits no leaves.
    pub fn provenance(&self, marker: &Ident) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        self.checked_alias(marker)?;
        Ok(self.anchors.clone())
    }

    /// The key of the alias, the sort declaration.
    #[must_use]
    pub const fn alias_key(&self) -> Option<&ProvenanceKey> {
        self.alias_key.as_ref()
    }

    /// The keys of the parent paths, indexed as [`Self::parents`].
    #[must_use]
    pub fn parent_keys(&self) -> &[ProvenanceKey] {
        &self.parent_keys
    }

    /// Keys the alias and each parent path, as the sort's descriptor. The
    /// marker trait [`Self::provenance`] takes only checks the alias, so an
    /// attribute without one keys nothing: it has no descriptor.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        let Some(alias) = &self.alias else {
            return Ok(self);
        };
        let mut keys = KeyAllocator::default();
        self.alias_key = Some(keys.key(
            ProvenanceRole::SortDeclaration,
            TokenRange::for_tokens(alias)?,
        )?);
        self.parent_keys = self
            .parents
            .iter()
            .map(|parent| keys.key(ProvenanceRole::SortParent, TokenRange::for_tokens(parent)?))
            .collect::<Result<_, _>>()?;
        self.anchors = keys.into_anchors();
        Ok(self)
    }
}

/// Checked payload of reference-surface `#[k::subsort(sort = ...)]`.
#[derive(Clone, Debug)]
pub struct SubsortAttribute {
    sort: Path,
    sort_key: Option<ProvenanceKey>,
}

impl SubsortAttribute {
    /// Returns the public semantic supersort alias populated by the impl.
    #[must_use]
    pub const fn sort(&self) -> &Path {
        &self.sort
    }

    /// The key of the supersort alias in its subsort's descriptor, where it
    /// is the first of its role.
    #[must_use]
    pub const fn sort_key(&self) -> Option<&ProvenanceKey> {
        self.sort_key.as_ref()
    }

    /// Keys the supersort alias as the first of its role, which no other
    /// piece of the subsort's descriptor keys; the descriptor records it
    /// between the impl's keys ([`crate::SubsortDeclaration::provenance`]).
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        self.sort_key = Some(KeyAllocator::default().key(
            ProvenanceRole::SubsortSuperSort,
            TokenRange::for_tokens(&self.sort)?,
        )?);
        Ok(self)
    }
}

/// Checked payload of `#[k::symbol("...")]`.
#[derive(Clone, Debug)]
pub struct SymbolAttribute {
    literal: LitStr,
    value: krs_ir::ExplicitSymbol,
    key: Option<ProvenanceKey>,
    /// The anchors of the attribute's standalone keying, which
    /// [`Self::provenance`] returns.
    anchors: Vec<ProvenanceAnchor>,
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
    /// None: the attribute was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    /// The key of the override literal.
    #[must_use]
    pub const fn key(&self) -> Option<&ProvenanceKey> {
        self.key.as_ref()
    }

    /// Keys the attribute as a sentence of its own.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        self.allocate_keys(&mut keys)?;
        self.anchors = keys.into_anchors();
        Ok(self)
    }

    /// Keys the override literal.
    /// The anchors of the attribute's own keying are forgotten here and
    /// recorded again by that keying: an enclosing sentence's pass leaves
    /// the attribute with that sentence's keys and no anchors of its own.
    pub(crate) fn allocate_keys(&mut self, keys: &mut KeyAllocator) -> Result<(), SyntaxError> {
        self.anchors.clear();
        self.key = Some(keys.key(
            ProvenanceRole::StableSymbol,
            TokenRange::for_tokens(&self.literal)?,
        )?);
        Ok(())
    }
}

/// One `concrete` or `symbolic` key: bare, or with a list of left-hand binders.
#[derive(Clone, Debug)]
pub struct RestrictionKey {
    key: Ident,
    variables: Option<Vec<Ident>>,
    provenance_key: Option<ProvenanceKey>,
    variable_keys: Vec<ProvenanceKey>,
}

impl RestrictionKey {
    /// Returns the authored key identifier.
    #[must_use]
    pub const fn key(&self) -> &Ident {
        &self.key
    }

    /// The key of the `concrete` or `symbolic` identifier.
    #[must_use]
    pub const fn provenance_key(&self) -> Option<&ProvenanceKey> {
        self.provenance_key.as_ref()
    }

    /// The keys of the listed binders, in order.
    #[must_use]
    pub fn variable_keys(&self) -> &[ProvenanceKey] {
        &self.variable_keys
    }

    /// Returns the listed binders, or `None` for the bare key (every binder).
    #[must_use]
    pub fn variables(&self) -> Option<&[Ident]> {
        self.variables.as_deref()
    }
}

/// The `concrete`, `symbolic`, and `smt_lemma` keys shared by
/// `#[k::equation]` and `#[k::simplification]` (KF-043).
///
/// `concrete` restricts the sentence to ground values of the named left-hand
/// binders (every binder when bare), `symbolic` to values containing a
/// variable, and `smt_lemma` hands the equation to Z3 as an axiom.
#[derive(Clone, Debug, Default)]
pub struct MatchRestriction {
    concrete: Option<RestrictionKey>,
    symbolic: Option<RestrictionKey>,
    smt_lemma: Option<Ident>,
    smt_lemma_key: Option<ProvenanceKey>,
}

impl MatchRestriction {
    /// Returns the `concrete` key.
    #[must_use]
    pub const fn concrete(&self) -> Option<&RestrictionKey> {
        self.concrete.as_ref()
    }

    /// Returns the `symbolic` key.
    #[must_use]
    pub const fn symbolic(&self) -> Option<&RestrictionKey> {
        self.symbolic.as_ref()
    }

    /// Returns the `smt_lemma` flag.
    #[must_use]
    pub const fn smt_lemma(&self) -> Option<&Ident> {
        self.smt_lemma.as_ref()
    }

    /// Whether no key was authored.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.concrete.is_none() && self.symbolic.is_none() && self.smt_lemma.is_none()
    }

    /// The key of the `smt_lemma` flag.
    #[must_use]
    pub const fn smt_lemma_key(&self) -> Option<&ProvenanceKey> {
        self.smt_lemma_key.as_ref()
    }

    /// Keys each written restriction key with its variables, numbered across
    /// both restrictions, then the `smt_lemma` key.
    pub(crate) fn allocate_keys(&mut self, keys: &mut KeyAllocator) -> Result<(), SyntaxError> {
        for (restriction, role) in [
            (&mut self.concrete, ProvenanceRole::RestrictionConcrete),
            (&mut self.symbolic, ProvenanceRole::RestrictionSymbolic),
        ] {
            let Some(restriction) = restriction else {
                continue;
            };
            restriction.provenance_key =
                Some(keys.key(role, TokenRange::for_tokens(&restriction.key)?)?);
            restriction.variable_keys = restriction
                .variables
                .as_deref()
                .unwrap_or_default()
                .iter()
                .map(|variable| {
                    keys.key(
                        ProvenanceRole::RestrictionVariable,
                        TokenRange::for_tokens(variable)?,
                    )
                })
                .collect::<Result<_, _>>()?;
        }
        self.smt_lemma_key = match &self.smt_lemma {
            Some(smt_lemma) => {
                Some(keys.key(ProvenanceRole::SmtLemma, TokenRange::for_tokens(smt_lemma)?)?)
            }
            None => None,
        };
        Ok(())
    }

    /// Parses `key` when it is `concrete`, `symbolic`, or `smt_lemma`, with
    /// its optional binder list; returns whether it was one of them.
    fn parse_key(&mut self, key: &Ident, input: ParseStream<'_>) -> Result<bool, ParseError> {
        let name = key.to_string();
        let slot = match name.as_str() {
            "concrete" => &mut self.concrete,
            "symbolic" => &mut self.symbolic,
            "smt_lemma" => {
                if input.peek(Token![=]) || input.peek(syn::token::Paren) {
                    return Err(restriction_error(
                        "`smt_lemma` is a bare flag; write `smt_lemma` without a value".into(),
                        key.span(),
                    ));
                }
                if self.smt_lemma.is_some() {
                    return Err(SyntaxError::new(
                        SyntaxErrorKind::DuplicateArgument { name: "smt_lemma" },
                        key.span(),
                    )
                    .into());
                }
                self.smt_lemma = Some(key.clone());
                return Ok(true);
            }
            _ => return Ok(false),
        };
        if input.peek(Token![=]) {
            return Err(restriction_error(
                format!(
                    "`{name}` takes no value; write bare `{name}` for every binder or `{name}(x, ..)` for some"
                ),
                key.span(),
            ));
        }
        let variables = if input.peek(syn::token::Paren) {
            let content = parenthesized(input)?;
            let list = syn::punctuated::Punctuated::<Ident, Token![,]>::parse_terminated(&content)?;
            if list.is_empty() {
                return Err(restriction_error(
                    format!(
                        "`{name}()` lists no binder; write bare `{name}` to restrict every binder"
                    ),
                    key.span(),
                ));
            }
            let mut seen = std::collections::BTreeSet::new();
            for variable in &list {
                if !seen.insert(variable.to_string()) {
                    return Err(restriction_error(
                        format!("`{variable}` is listed twice in `{name}(..)`"),
                        variable.span(),
                    ));
                }
            }
            Some(list.into_iter().collect::<Vec<_>>())
        } else {
            None
        };
        if let Some(previous) = slot {
            if previous.variables.is_some() == variables.is_some() {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument {
                        name: if name == "concrete" {
                            "concrete"
                        } else {
                            "symbolic"
                        },
                    },
                    key.span(),
                )
                .into());
            }
            return Err(restriction_error(
                format!(
                    "`{name}` is written bare (every binder) or with a list of binders, not both"
                ),
                key.span(),
            ));
        }
        *slot = Some(RestrictionKey {
            key: key.clone(),
            variables,
            provenance_key: None,
            variable_keys: Vec::new(),
        });
        Ok(true)
    }
}

fn bracketed(input: ParseStream<'_>) -> syn::Result<syn::parse::ParseBuffer<'_>> {
    let content;
    syn::bracketed!(content in input);
    Ok(content)
}

fn parenthesized(input: ParseStream<'_>) -> syn::Result<syn::parse::ParseBuffer<'_>> {
    let content;
    syn::parenthesized!(content in input);
    Ok(content)
}

fn restriction_error(reason: String, span: proc_macro2::Span) -> ParseError {
    SyntaxError::new(SyntaxErrorKind::InvalidMatchRestriction { reason }, span).into()
}

/// Checked payload of `#[k::equation]`, `#[k::equation(owise)]`, or
/// `#[k::equation(priority = N)]`, with optional `concrete`, `symbolic`, and
/// `smt_lemma` keys.
#[derive(Clone, Debug, Default)]
pub struct EquationAttribute {
    owise: Option<Ident>,
    priority: Option<PriorityValue>,
    restriction: MatchRestriction,
    owise_key: Option<ProvenanceKey>,
    priority_key: Option<ProvenanceKey>,
    /// The anchors of the attribute's standalone keying, which
    /// [`Self::provenance`] returns.
    anchors: Vec<ProvenanceAnchor>,
}

impl EquationAttribute {
    /// Returns the `concrete`, `symbolic`, and `smt_lemma` keys.
    #[must_use]
    pub const fn restriction(&self) -> &MatchRestriction {
        &self.restriction
    }

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
    /// None: the attribute was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
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

    /// Keys the attribute as a sentence of its own.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        self.allocate_keys(&mut keys)?;
        self.anchors = keys.into_anchors();
        Ok(self)
    }

    /// Keys `owise`, the priority, then the restriction.
    pub(crate) fn allocate_keys(&mut self, keys: &mut KeyAllocator) -> Result<(), SyntaxError> {
        self.owise_key = match &self.owise {
            Some(owise) => Some(keys.key(
                ProvenanceRole::EquationOwise,
                TokenRange::for_tokens(owise)?,
            )?),
            None => None,
        };
        self.priority_key = match &self.priority {
            Some(priority) => Some(keys.key(
                ProvenanceRole::EquationPriority,
                TokenRange::for_tokens(&priority.literal)?,
            )?),
            None => None,
        };
        self.restriction.allocate_keys(keys)
    }
}

/// Checked payload of `#[k::simplification]` or `#[k::simplification(priority = N)]`,
/// with optional `concrete`, `symbolic`, and `smt_lemma` keys.
#[derive(Clone, Debug, Default)]
pub struct SimplificationAttribute {
    priority: Option<(LitInt, u32)>,
    restriction: MatchRestriction,
    priority_key: Option<ProvenanceKey>,
    /// The anchors of the attribute's keying, which [`Self::provenance`]
    /// returns.
    anchors: Vec<ProvenanceAnchor>,
}

impl SimplificationAttribute {
    /// Returns the `concrete`, `symbolic`, and `smt_lemma` keys.
    #[must_use]
    pub const fn restriction(&self) -> &MatchRestriction {
        &self.restriction
    }

    /// Returns the optional simplifier ordering hint.
    #[must_use]
    pub fn priority(&self) -> Option<u32> {
        self.priority.as_ref().map(|(_, value)| *value)
    }

    /// Returns exact provenance for an authored priority literal.
    ///
    /// # Errors
    ///
    /// None: the attribute was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    /// The key of the `priority` value.
    #[must_use]
    pub const fn priority_key(&self) -> Option<&ProvenanceKey> {
        self.priority_key.as_ref()
    }

    /// Keys the priority, then the restriction.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        self.priority_key = match &self.priority {
            Some((literal, _)) => Some(keys.key(
                ProvenanceRole::SimplificationPriority,
                TokenRange::for_tokens(literal)?,
            )?),
            None => None,
        };
        self.restriction.allocate_keys(&mut keys)?;
        self.anchors = keys.into_anchors();
        Ok(self)
    }
}

/// Validated empty payload of `#[k::alias]` on an alias clause fn.
///
/// The production marker, which may say `recursive`, is
/// [`StaticProductionAttribute`].
#[derive(Clone, Copy, Debug, Default)]
pub struct AliasAttribute;

/// Validated payload of `#[k::desugar]` on a desugar clause fn (KF-028):
/// empty, or `unbound_variables = [x, _]` (KF-046).
///
/// The production marker, which may say `recursive`, is
/// [`StaticProductionAttribute`].
#[derive(Clone, Debug, Default)]
pub struct DesugarAttribute {
    unbound_variables: Option<UnboundVariables>,
    /// The anchors of the attribute's keying, which [`Self::provenance`]
    /// returns.
    anchors: Vec<ProvenanceAnchor>,
}

impl DesugarAttribute {
    /// Returns `unbound_variables = [..]`, when written.
    #[must_use]
    pub const fn unbound_variables(&self) -> Option<&UnboundVariables> {
        self.unbound_variables.as_ref()
    }

    /// Returns exact provenance: the `unbound_variables` key and each listed
    /// entry, in authored order.
    ///
    /// # Errors
    ///
    /// None: the attribute was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    /// Keys the `unbound_variables` identifier, then each entry.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        let Some(unbound) = &mut self.unbound_variables else {
            return Ok(self);
        };
        let mut keys = KeyAllocator::default();
        unbound.provenance_keys = vec![keys.key(
            ProvenanceRole::UnboundVariables,
            TokenRange::for_tokens(&unbound.key)?,
        )?];
        for variable in &unbound.variables {
            let range = match variable {
                UnboundVariable::Named(name) => TokenRange::for_tokens(name)?,
                UnboundVariable::Wildcard(wildcard) => TokenRange::for_tokens(wildcard)?,
            };
            unbound
                .provenance_keys
                .push(keys.key(ProvenanceRole::UnboundVariable, range)?);
        }
        self.anchors = keys.into_anchors();
        Ok(self)
    }
}

/// `unbound_variables = [x, _]` on a desugar clause (KF-046): right-hand
/// names the clause's pattern does not bind, K's `unboundVariables`. A
/// desugar is expanded inside other rules, where such a name is bound by the
/// rule that uses it; `_` admits wildcards in the result.
#[derive(Clone, Debug)]
pub struct UnboundVariables {
    key: Ident,
    variables: Vec<UnboundVariable>,
    provenance_keys: Vec<ProvenanceKey>,
}

/// One entry of `unbound_variables = [..]`.
#[derive(Clone, Debug)]
pub enum UnboundVariable {
    /// A right-hand name the pattern does not bind.
    Named(Ident),
    /// `_`: every wildcard of the result.
    Wildcard(Token![_]),
}

impl UnboundVariables {
    /// The key of the `unbound_variables` identifier, then the key of each
    /// entry in order.
    #[must_use]
    pub fn provenance_keys(&self) -> &[ProvenanceKey] {
        &self.provenance_keys
    }

    /// Returns the authored `unbound_variables` identifier.
    #[must_use]
    pub const fn key(&self) -> &Ident {
        &self.key
    }

    /// Returns the entries in authored order.
    #[must_use]
    pub fn variables(&self) -> &[UnboundVariable] {
        &self.variables
    }

    /// Returns the listed names other than `_`.
    pub fn names(&self) -> impl Iterator<Item = &Ident> {
        self.variables.iter().filter_map(|variable| match variable {
            UnboundVariable::Named(name) => Some(name),
            UnboundVariable::Wildcard(_) => None,
        })
    }

    /// Returns the `_` entry, when listed.
    #[must_use]
    pub fn wildcard(&self) -> Option<&Token![_]> {
        self.variables.iter().find_map(|variable| match variable {
            UnboundVariable::Wildcard(wildcard) => Some(wildcard),
            UnboundVariable::Named(_) => None,
        })
    }
}

impl Parse for UnboundVariable {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        if input.peek(Token![_]) {
            input.parse().map(Self::Wildcard)
        } else {
            input.parse().map(Self::Named)
        }
    }
}

/// The diagnostic for `unbound_variables` anywhere but a desugar clause.
pub const UNBOUND_VARIABLES_OUTSIDE_DESUGAR_CLAUSE: &str = "unbound_variables applies only to desugar clauses: write it in the `#[k::desugar(..)]` of a clause fn, `#[k::desugar(unbound_variables = [x, _])]`";

/// The error for `unbound_variables` anywhere but a desugar clause.
pub(crate) fn unbound_variables_outside_desugar(span: proc_macro2::Span) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::InvalidUnboundVariables {
            reason: UNBOUND_VARIABLES_OUTSIDE_DESUGAR_CLAUSE.to_owned(),
        },
        span,
    )
}

fn unbound_variables_error(reason: String, span: proc_macro2::Span) -> ParseError {
    SyntaxError::new(SyntaxErrorKind::InvalidUnboundVariables { reason }, span).into()
}

/// Parses `unbound_variables = [x, _]` after its key.
fn parse_unbound_variables(
    key: Ident,
    input: ParseStream<'_>,
) -> Result<UnboundVariables, ParseError> {
    input.parse::<Token![=]>()?;
    let content = bracketed(input)?;
    let list =
        syn::punctuated::Punctuated::<UnboundVariable, Token![,]>::parse_terminated(&content)?;
    if list.is_empty() {
        return Err(unbound_variables_error(
            "`unbound_variables = []` lists nothing; list the result's names the pattern does not bind, or omit the key".into(),
            key.span(),
        ));
    }
    let mut seen = std::collections::BTreeSet::new();
    for variable in &list {
        let (text, span) = match variable {
            UnboundVariable::Named(name) => (name.unraw().to_string(), name.span()),
            UnboundVariable::Wildcard(wildcard) => ("_".to_owned(), wildcard.span),
        };
        if !seen.insert(text.clone()) {
            return Err(unbound_variables_error(
                format!("`{text}` is listed twice in `unbound_variables`"),
                span,
            ));
        }
    }
    Ok(UnboundVariables {
        key,
        variables: list.into_iter().collect(),
        provenance_keys: Vec::new(),
    })
}

/// The static rewriting mode a production marker declares (KF-028): K's
/// `alias`, which also runs backwards when K prints, or a one-way `macro`,
/// which KRS spells `desugar`.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum StaticMode {
    /// `#[k::alias]`: K's `alias` or `alias-rec`.
    Alias,
    /// `#[k::desugar]`: K's `macro` or `macro-rec`.
    Desugar,
}

impl StaticMode {
    /// The attribute name, `alias` or `desugar`.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Alias => "alias",
            Self::Desugar => "desugar",
        }
    }

    /// The provenance role of the production marker.
    #[must_use]
    pub const fn production_role(self) -> ProvenanceRole {
        match self {
            Self::Alias => ProvenanceRole::AliasProduction,
            Self::Desugar => ProvenanceRole::DesugarProduction,
        }
    }

    /// The provenance role of a clause fn's name.
    #[must_use]
    pub const fn clause_role(self) -> ProvenanceRole {
        match self {
            Self::Alias => ProvenanceRole::AliasClause,
            Self::Desugar => ProvenanceRole::DesugarClause,
        }
    }
}

/// The diagnostic for `recursive` on an alias or desugar clause.
pub const RECURSIVE_ON_CLAUSE: &str = "recursion is a property of the production: write `recursive` on the production's `#[k::alias]` or `#[k::desugar]` marker, and a plain marker on its clauses";

/// The diagnostic for `#[k::requires]` on a desugar clause.
pub const REQUIRES_ON_DESUGAR_CLAUSE: &str = "a desugar clause has no `#[k::requires]`: K rewrites the definition and the program with it once, before anything runs, so there is nothing to test a condition against";

/// Validated payload of a static production marker (KF-028): `#[k::alias]`,
/// `#[k::alias(recursive)]`, `#[k::desugar]`, or `#[k::desugar(recursive)]`
/// on a variant or after `#[k::constructor(...)]`.
#[derive(Clone, Debug)]
pub struct StaticProductionAttribute {
    mode: StaticMode,
    recursive: Option<TokenRange>,
    recursive_key: Option<ProvenanceKey>,
    /// The anchors of the marker's standalone keying, which
    /// [`Self::provenance`] returns.
    anchors: Vec<ProvenanceAnchor>,
}

impl StaticProductionAttribute {
    /// Parses the payload of the `mode` marker: empty or `recursive`.
    ///
    /// # Errors
    ///
    /// Rejects `priority`/`owise` (static rules have no priority) and every
    /// payload other than one `recursive`.
    pub fn parse_marker(mode: StaticMode, tokens: TokenStream) -> Result<Self, SyntaxError> {
        let mut iter = crate::parse::strip_trailing_comma(tokens).into_iter();
        let Some(first) = iter.next() else {
            return Self {
                mode,
                recursive: None,
                recursive_key: None,
                anchors: Vec::new(),
            }
            .keyed();
        };
        if let proc_macro2::TokenTree::Ident(ident) = &first {
            if ident == "priority" || ident == "owise" {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::InvalidRuleKey {
                        reason: PRIORITY_ON_STATIC_RULE,
                    },
                    ident.span(),
                ));
            }
            if ident == "unbound_variables" {
                return Err(unbound_variables_outside_desugar(ident.span()));
            }
            if ident == "recursive" {
                if let Some(extra) = iter.next() {
                    return Err(SyntaxError::new(
                        SyntaxErrorKind::UnexpectedAttributePayload {
                            attribute: "recursive",
                        },
                        extra.span(),
                    ));
                }
                return Self {
                    mode,
                    recursive: Some(TokenRange::for_tokens(ident)?),
                    recursive_key: None,
                    anchors: Vec::new(),
                }
                .keyed();
            }
            return Err(SyntaxError::new(
                SyntaxErrorKind::UnknownArgument {
                    name: ident.to_string(),
                },
                ident.span(),
            ));
        }
        Err(SyntaxError::new(
            SyntaxErrorKind::UnexpectedAttributePayload {
                attribute: mode.name(),
            },
            first.span(),
        ))
    }

    /// The marker's mode.
    #[must_use]
    pub const fn mode(&self) -> StaticMode {
        self.mode
    }

    /// Whether the production is `recursive` (K's `alias-rec`/`macro-rec`).
    #[must_use]
    pub const fn is_recursive(&self) -> bool {
        self.recursive.is_some()
    }

    /// The anchor of the `recursive` keyword, when written.
    #[must_use]
    pub fn provenance(&self) -> Vec<ProvenanceAnchor> {
        self.anchors.clone()
    }

    /// The key of the `recursive` flag.
    #[must_use]
    pub const fn recursive_key(&self) -> Option<&ProvenanceKey> {
        self.recursive_key.as_ref()
    }

    /// Keys the marker as a sentence of its own.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        self.allocate_keys(&mut keys)?;
        self.anchors = keys.into_anchors();
        Ok(self)
    }

    /// Keys the `recursive` keyword, when written.
    /// The anchors of the attribute's own keying are forgotten here and
    /// recorded again by that keying: an enclosing sentence's pass leaves
    /// the attribute with that sentence's keys and no anchors of its own.
    pub(crate) fn allocate_keys(&mut self, keys: &mut KeyAllocator) -> Result<(), SyntaxError> {
        self.anchors.clear();
        self.recursive_key = match self.recursive {
            Some(range) => Some(keys.key(ProvenanceRole::StaticRecursive, range)?),
            None => None,
        };
        Ok(())
    }
}

/// Checked payload of
/// `#[k::context_alias(name = alias, here = binding, result = S)]`.
#[derive(Clone, Debug)]
pub struct ContextAliasAttribute {
    name: Ident,
    here: Ident,
    result: Option<syn::Path>,
    name_key: Option<ProvenanceKey>,
    here_key: Option<ProvenanceKey>,
    result_key: Option<ProvenanceKey>,
    /// The anchors of the attribute's keying, which [`Self::provenance`]
    /// returns.
    anchors: Vec<ProvenanceAnchor>,
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

    /// Returns the sort path of `result = S`, K's `result(S)` (KF-021).
    #[must_use]
    pub const fn result_sort(&self) -> Option<&syn::Path> {
        self.result.as_ref()
    }

    /// Returns exact anchors for the authored alias name and `HERE` binding.
    ///
    /// # Errors
    ///
    /// None: the attribute was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    /// The key of the alias name.
    #[must_use]
    pub const fn name_key(&self) -> Option<&ProvenanceKey> {
        self.name_key.as_ref()
    }

    /// The key of the `here` identifier.
    #[must_use]
    pub const fn here_key(&self) -> Option<&ProvenanceKey> {
        self.here_key.as_ref()
    }

    /// The key of the result sort, when authored.
    #[must_use]
    pub const fn result_key(&self) -> Option<&ProvenanceKey> {
        self.result_key.as_ref()
    }

    /// Keys the name, `here`, then the result sort.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        self.name_key = Some(keys.key(
            ProvenanceRole::ContextAliasName,
            TokenRange::for_tokens(&self.name)?,
        )?);
        self.here_key = Some(keys.key(
            ProvenanceRole::ContextAliasHere,
            TokenRange::for_tokens(&self.here)?,
        )?);
        self.result_key = match &self.result {
            Some(result) => Some(keys.key(
                ProvenanceRole::ContextAliasResult,
                TokenRange::for_tokens(result)?,
            )?),
            None => None,
        };
        self.anchors = keys.into_anchors();
        Ok(self)
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
    /// Parses a sort-attribute payload; [`SortAttribute::checked_alias`]
    /// then requires its `alias`.
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
        let tokens = crate::parse::strip_trailing_comma(tokens);
        let parser = |input: ParseStream<'_>| -> syn::Result<SymbolAttribute> {
            let literal: LitStr = input.parse()?;
            if !input.is_empty() {
                return Err(input.error("symbol accepts exactly one string literal"));
            }
            let value = krs_ir::ExplicitSymbol::new(literal.value())
                .map_err(|error| syn::Error::new(literal.span(), error))?;
            SymbolAttribute {
                literal,
                value,
                key: None,
                anchors: Vec::new(),
            }
            .keyed()
            .map_err(syn::Error::from)
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
    let mut restriction = MatchRestriction::default();
    while !input.is_empty() {
        let key: Ident = input.parse()?;
        let key_name = key.to_string();
        if restriction.parse_key(&key, input)? {
            if input.is_empty() {
                break;
            }
            input.parse::<Token![,]>()?;
            continue;
        }
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
            "unbound_variables" => {
                return Err(unbound_variables_outside_desugar(key.span()).into());
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
    }
    Ok(EquationAttribute {
        owise,
        priority,
        restriction,
        owise_key: None,
        priority_key: None,
        anchors: Vec::new(),
    }
    .keyed()?)
}

impl KrsSyntax for SimplificationAttribute {
    /// Parses an empty simplification payload, `priority = N`, and the
    /// `concrete`, `symbolic`, and `smt_lemma` keys.
    ///
    /// # Errors
    ///
    /// Rejects `owise`, `nondet`, and unknown, malformed, repeated, or
    /// out-of-range keys.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        structured(tokens, parse_simplification_stream)
    }
}

fn parse_simplification_stream(
    input: ParseStream<'_>,
) -> Result<SimplificationAttribute, ParseError> {
    let mut priority: Option<(LitInt, u32)> = None;
    let mut restriction = MatchRestriction::default();
    while !input.is_empty() {
        let key: Ident = input.parse()?;
        let consumed = restriction.parse_key(&key, input)?;
        if consumed {
            // A `concrete`, `symbolic`, or `smt_lemma` key.
        } else if key == "owise" {
            return Err(rule_key_error(OWISE_ON_SIMPLIFICATION, key.span()));
        } else if key == "nondet" {
            return Err(rule_key_error(NONDET_ON_FUNCTION, key.span()));
        } else if key == "unbound_variables" {
            return Err(unbound_variables_outside_desugar(key.span()).into());
        } else if key == "priority" {
            if priority.is_some() {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "priority" },
                    key.span(),
                )
                .into());
            }
            input.parse::<Token![=]>()?;
            let literal: LitInt = input.parse()?;
            let value = literal.base10_parse::<u32>()?;
            priority = Some((literal, value));
        } else {
            return Err(SyntaxError::new(
                SyntaxErrorKind::UnknownArgument {
                    name: key.to_string(),
                },
                key.span(),
            )
            .into());
        }
        if input.is_empty() {
            break;
        }
        input.parse::<Token![,]>()?;
    }
    Ok(SimplificationAttribute {
        priority,
        restriction,
        priority_key: None,
        anchors: Vec::new(),
    }
    .keyed()?)
}

/// Rejects the payload of a static clause marker at its first token.
fn parse_static_clause_tokens(
    tokens: TokenStream,
    attribute: &'static str,
) -> Result<(), SyntaxError> {
    if let Some(proc_macro2::TokenTree::Ident(first)) = tokens.clone().into_iter().next() {
        let reason = if first == "priority" || first == "owise" {
            Some(PRIORITY_ON_STATIC_RULE)
        } else if first == "nondet" {
            Some(NONDET_ON_FUNCTION)
        } else if first == "recursive" {
            Some(RECURSIVE_ON_CLAUSE)
        } else if first == "unbound_variables" {
            return Err(unbound_variables_outside_desugar(first.span()));
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
    parse_empty_tokens(tokens, attribute)
}

impl KrsSyntax for AliasAttribute {
    /// Parses the intentionally empty alias clause payload.
    ///
    /// # Errors
    ///
    /// Rejects `priority` and `owise` (static rules have no priority),
    /// `nondet`, `recursive` (a property of the production), and every other
    /// payload at its first token.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        parse_static_clause_tokens(tokens, "alias").map(|()| AliasAttribute)
    }
}

impl KrsSyntax for DesugarAttribute {
    /// Parses the desugar clause payload: empty, or
    /// `unbound_variables = [x, _]`.
    ///
    /// # Errors
    ///
    /// Rejects `priority` and `owise` (static rules have no priority),
    /// `nondet`, `recursive` (a property of the production), a malformed
    /// `unbound_variables` list, and every other payload at its first token.
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        let tokens = crate::parse::strip_trailing_comma(tokens);
        let first = tokens.clone().into_iter().next();
        let Some(proc_macro2::TokenTree::Ident(first)) = first else {
            return parse_static_clause_tokens(tokens, "desugar")
                .map(|()| DesugarAttribute::default());
        };
        if first != "unbound_variables" {
            return parse_static_clause_tokens(tokens, "desugar")
                .map(|()| DesugarAttribute::default());
        }
        structured(
            tokens,
            |input: ParseStream<'_>| -> Result<Self, ParseError> {
                let key = input.parse::<Ident>()?;
                let unbound = parse_unbound_variables(key, input)?;
                if !input.is_empty() {
                    let next: proc_macro2::TokenTree = input.parse()?;
                    return Err(unbound_variables_error(
                        "a desugar clause takes only `unbound_variables = [..]`".into(),
                        next.span(),
                    ));
                }
                Ok(DesugarAttribute {
                    unbound_variables: Some(unbound),
                    anchors: Vec::new(),
                }
                .keyed()?)
            },
        )
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
        return Ok(SortAttribute {
            alias: None,
            parents: Vec::new(),
            alias_key: None,
            parent_keys: Vec::new(),
            anchors: Vec::new(),
        });
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
        alias_key: None,
        parent_keys: Vec::new(),
        anchors: Vec::new(),
    }
    .keyed()?)
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
        sort_key: None,
    }
    .keyed()?)
}

fn parse_context_alias_stream(input: ParseStream<'_>) -> Result<ContextAliasAttribute, ParseError> {
    let missing_span = input.span();
    let mut name = None;
    let mut here = None;
    let mut result = None;
    while !input.is_empty() {
        let key: Ident = input.parse()?;
        let key_name = key.to_string();
        let argument = match key_name.as_str() {
            "result" if result.is_some() => {
                return Err(SyntaxError::new(
                    SyntaxErrorKind::DuplicateArgument { name: "result" },
                    key.span(),
                )
                .into());
            }
            "result" => {
                input.parse::<Token![=]>()?;
                result = Some(super::rule::parse_result_sort(input.parse()?)?);
                if input.is_empty() {
                    break;
                }
                input.parse::<Token![,]>()?;
                continue;
            }
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
            "unbound_variables" => return Err(unbound_variables_outside_desugar(key.span()).into()),
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
        result,
        name_key: None,
        here_key: None,
        result_key: None,
        anchors: Vec::new(),
    }
    .keyed()?)
}

#[cfg(test)]
mod keyed {
    use super::{
        ContextAliasAttribute, DesugarAttribute, EquationAttribute, MatchRestriction,
        SimplificationAttribute, SortAttribute, StaticProductionAttribute, SubsortAttribute,
        SymbolAttribute, UnboundVariable,
    };
    use crate::SyntaxError;
    use crate::keyed_nodes::KeyedNodes;

    impl SortAttribute {
        /// Records the keys of the alias and of each parent path.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            if let Some(alias) = &self.alias {
                nodes.push_tokens(self.alias_key.as_ref(), alias)?;
            }
            assert!(self.parent_keys.len() <= self.parents.len());
            for (key, parent) in self.parent_keys.iter().zip(&self.parents) {
                nodes.push_tokens(Some(key), parent)?;
            }
            Ok(())
        }
    }

    impl SortAttribute {
        /// Records the key of the alias, which names the sort in the
        /// descriptor of a bracket on the sort's marker trait.
        pub(crate) fn keyed_alias_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            if let Some(alias) = &self.alias {
                nodes.push_tokens(self.alias_key.as_ref(), alias)?;
            }
            Ok(())
        }
    }

    impl SubsortAttribute {
        /// Records the key of the supersort alias.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            nodes.push_tokens(self.sort_key.as_ref(), &self.sort)
        }
    }

    impl SymbolAttribute {
        /// Records the key of the override literal.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            nodes.push_tokens(self.key.as_ref(), &self.literal)
        }
    }

    impl MatchRestriction {
        /// Records the keys of the `concrete` and `symbolic` identifiers and
        /// their variables, then of `smt_lemma`.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            for restriction in self.concrete.iter().chain(&self.symbolic) {
                nodes.push_tokens(restriction.provenance_key.as_ref(), &restriction.key)?;
                let variables = restriction.variables.as_deref().unwrap_or_default();
                assert!(restriction.variable_keys.len() <= variables.len());
                for (key, variable) in restriction.variable_keys.iter().zip(variables) {
                    nodes.push_tokens(Some(key), variable)?;
                }
            }
            if let Some(smt_lemma) = &self.smt_lemma {
                nodes.push_tokens(self.smt_lemma_key.as_ref(), smt_lemma)?;
            }
            Ok(())
        }
    }

    impl EquationAttribute {
        /// Records the keys of `owise`, the priority and the restriction.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            if let Some(owise) = &self.owise {
                nodes.push_tokens(self.owise_key.as_ref(), owise)?;
            }
            if let Some(priority) = &self.priority {
                nodes.push_tokens(self.priority_key.as_ref(), &priority.literal)?;
            }
            self.restriction.keyed_nodes(nodes)
        }
    }

    impl SimplificationAttribute {
        /// Records the keys of the priority and the restriction.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            if let Some((literal, _)) = &self.priority {
                nodes.push_tokens(self.priority_key.as_ref(), literal)?;
            }
            self.restriction.keyed_nodes(nodes)
        }
    }

    impl DesugarAttribute {
        /// Records the keys of the `unbound_variables` key and of each
        /// variable it lists.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            let Some(unbound) = &self.unbound_variables else {
                return Ok(());
            };
            let mut keys = unbound.provenance_keys.iter();
            nodes.push_tokens(keys.next(), &unbound.key)?;
            assert!(keys.len() <= unbound.variables.len());
            for (key, variable) in keys.zip(&unbound.variables) {
                match variable {
                    UnboundVariable::Named(name) => nodes.push_tokens(Some(key), name),
                    UnboundVariable::Wildcard(wildcard) => nodes.push_tokens(Some(key), wildcard),
                }?;
            }
            Ok(())
        }
    }

    impl StaticProductionAttribute {
        /// Records the key of the `recursive` flag.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) {
            if let Some(range) = self.recursive {
                nodes.push(self.recursive_key.as_ref(), range);
            }
        }
    }

    impl ContextAliasAttribute {
        /// Records the keys of the name, `here` and the result sort.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            nodes.push_tokens(self.name_key.as_ref(), &self.name)?;
            nodes.push_tokens(self.here_key.as_ref(), &self.here)?;
            if let Some(result) = &self.result {
                nodes.push_tokens(self.result_key.as_ref(), result)?;
            }
            Ok(())
        }
    }
}
