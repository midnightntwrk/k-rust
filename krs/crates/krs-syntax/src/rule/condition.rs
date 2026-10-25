use proc_macro2::{TokenStream, TokenTree};
use syn::ext::IdentExt;
use syn::parse::ParseStream;
use syn::spanned::Spanned;
use syn::{Attribute, Expr, ExprCall, Ident, Meta, Token, bracketed};

use super::machine::parse_expression_before_arrow;
use super::pattern::{RulePattern, allocate_term_node_keys, push_term_reference_candidates};
use crate::parse::{
    KeyAllocator, KrsSyntax, ParseError, unsupported_rule_signature as unsupported_signature,
    validate_authored_binder,
};
use crate::path::is_plain_path;
use crate::term::allocate_record_field_keys;
use krs_ir::ProvenanceKey;

use crate::{
    ProvenanceAnchor, ProvenanceRole, ReferenceCandidate, SyntaxError, TermExpression,
    TermSymbolKind, TermTree, TokenRange,
};

/// One parsed object-language Boolean condition from `#[k::requires(...)]`.
#[derive(Clone, Debug)]
pub struct RuleCondition {
    term: TermExpression,
    /// The anchors of the condition's standalone keying.
    anchors: Vec<ProvenanceAnchor>,
}

impl RuleCondition {
    /// A condition over `term`, keyed as a sentence of its own.
    fn keyed(term: TermExpression) -> Result<Self, SyntaxError> {
        let mut condition = Self {
            term,
            anchors: Vec::new(),
        };
        let mut keys = KeyAllocator::default();
        condition.clear_keys();
        condition.allocate_keys(&mut keys)?;
        condition.anchors = keys.into_anchors();
        Ok(condition)
    }

    /// Returns the complete structured condition term.
    #[must_use]
    pub const fn term(&self) -> &TermExpression {
        &self.term
    }

    /// Returns the condition term, for a pass that keys it.
    pub(crate) const fn term_mut(&mut self) -> &mut TermExpression {
        &mut self.term
    }

    /// Returns complete and nested parser-owned condition anchors of the
    /// condition's standalone keying.
    ///
    /// # Errors
    ///
    /// None: the condition was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    /// Forgets the keys of the condition's term, before a sentence's pass
    /// keys it.
    pub(crate) fn clear_keys(&mut self) {
        self.term.clear_keys();
    }

    /// A copy without keys, for a producer that computes its anchors on
    /// demand; the copy's keys are discarded with it.
    pub(crate) fn unkeyed(&self) -> Self {
        let mut copy = self.clone();
        copy.clear_keys();
        copy
    }

    /// Keys the condition (its term's payload), then its paths, its
    /// application head, reference, and literal nodes, and its record field
    /// names.
    pub(crate) fn allocate_keys(&mut self, keys: &mut KeyAllocator) -> Result<(), SyntaxError> {
        self.term.allocate_keys(
            keys,
            ProvenanceRole::RuleRequires,
            ProvenanceRole::RuleRequiresPath,
        )?;
        let (nodes, tree, term_keys) = self.term.keying();
        allocate_term_node_keys(
            keys,
            nodes,
            term_keys,
            ProvenanceRole::RuleRequiresApplicationHead,
            ProvenanceRole::RuleRequiresReference,
            ProvenanceRole::RuleRequiresLiteral,
        )?;
        allocate_record_field_keys(
            keys,
            tree,
            term_keys,
            ProvenanceRole::RuleRequiresRecordFieldName,
        )
    }

    /// Returns rustc-resolvable condition references, excluding pre-bindings.
    ///
    /// # Errors
    ///
    /// Returns an occurrence-overflow error for pathological inputs.
    pub fn reference_candidates(
        &self,
        bindings: &[Ident],
    ) -> Result<Vec<ReferenceCandidate<TermSymbolKind>>, SyntaxError> {
        let mut candidates = Vec::new();
        push_term_reference_candidates(
            &mut candidates,
            self.term.nodes(),
            self.term.keys(),
            bindings,
        );
        Ok(candidates)
    }
}

/// One explicit gradual extra-cell clause in a readable rule.
#[derive(Clone, Debug)]
pub enum RuleExtra {
    /// Failable preserved read of one or more entries of a map cell.
    HaveMap {
        /// Named fixed cell.
        cell: Ident,
        /// The read entries, at least one, in authored order; their keys are
        /// pairwise distinct terms.
        entries: Vec<RuleMapEntry>,
    },
    /// Simultaneous map update.
    UpdateMap {
        /// Named fixed cell and implicit pre-state map binder.
        cell: Ident,
        /// Authored whole-map binding from the subject record.
        base: Ident,
        /// Complete ordinary three-argument update term.
        update: Box<RuleMapUpdate>,
    },
    /// Exact match of one ordinary fixed cell, simultaneously rewritten when
    /// the result record restates it and read only when the result leaves it
    /// out.
    RewriteCell {
        /// Named fixed cell.
        cell: Ident,
        /// Complete constructor or binding pattern before the rewrite.
        before: Box<RulePattern>,
        /// Parser-owned subject tree for descriptor expansion and provenance.
        before_tree: Box<TermTree>,
        /// Complete replacement term after the rewrite, absent when the
        /// result leaves the cell out (the cell is then read only).
        after: Option<Box<TermExpression>>,
    },
    /// An optional (`?`) or collection (`*`) cell (KF-023): `Some(p)` or
    /// `None`, or an instance list, and its result when the record restates
    /// the cell.
    RewriteState {
        /// Named cell, in the subject record.
        cell: Ident,
        /// The subject state.
        before: Box<crate::StateTerm>,
        /// The same cell in the result record, absent when the result
        /// leaves it out (the cell is then read only).
        result_cell: Option<Ident>,
        /// The result state.
        after: Option<Box<crate::StateTerm>>,
    },
    /// A cell of a list sort in list notation (F6), `stack: [a, b, ..]`,
    /// and its rewritten list when the result record restates the cell.
    /// Whether the cell's sort is the builtin `List` or a cons list is
    /// checked once sorts resolve.
    RewriteList {
        /// Named cell, in the subject record.
        cell: Ident,
        /// The matched list.
        before: Box<super::RuleListPattern>,
        /// The same cell in the result record, absent when the result
        /// leaves it out (the cell is then read only).
        result_cell: Option<Ident>,
        /// The rewritten list.
        after: Option<Box<super::RuleListResult>>,
    },
}

impl RuleExtra {
    /// Returns the named fixed cell.
    #[must_use]
    pub const fn cell(&self) -> &Ident {
        match self {
            Self::HaveMap { cell, .. }
            | Self::UpdateMap { cell, .. }
            | Self::RewriteCell { cell, .. }
            | Self::RewriteState { cell, .. }
            | Self::RewriteList { cell, .. } => cell,
        }
    }
}

pub(super) fn condition_token_range(input: ParseStream<'_>) -> syn::Result<TokenRange> {
    let fork = input.fork();
    let mut tokens = TokenStream::new();
    while !fork.is_empty() && !fork.peek(Token![;]) {
        tokens.extend([fork.parse::<TokenTree>()?]);
    }
    if tokens.is_empty() {
        return Err(input.error("expected a rule condition after `where`"));
    }
    Ok(TokenRange::for_tokens(&tokens)?)
}

/// One entry of a map read: the rule applies only where the map holds an
/// entry for `key`, and `value` binds what that entry maps to.
#[derive(Clone, Debug)]
pub struct RuleMapEntry {
    /// Required key term; its key is the term's payload key.
    pub key: Box<TermExpression>,
    /// Value binder introduced only when the map item is present.
    pub value: Ident,
    pub(super) value_key: Option<ProvenanceKey>,
}

impl RuleMapEntry {
    pub(super) const fn new(key: Box<TermExpression>, value: Ident) -> Self {
        Self {
            key,
            value,
            value_key: None,
        }
    }

    /// The key of the value binder, given by the clause that reads the entry.
    #[must_use]
    pub const fn value_key(&self) -> Option<&ProvenanceKey> {
        self.value_key.as_ref()
    }
}

/// One validated ordinary three-argument map update.
#[derive(Clone, Debug)]
pub struct RuleMapUpdate {
    term: TermExpression,
    arguments: [Expr; 3],
    argument_keys: [Option<ProvenanceKey>; 3],
}

impl RuleMapUpdate {
    /// Returns the complete structured update term.
    #[must_use]
    pub const fn term(&self) -> &TermExpression {
        &self.term
    }

    /// Returns the update term, for a pass that keys it.
    pub(super) const fn term_mut(&mut self) -> &mut TermExpression {
        &mut self.term
    }

    /// Returns the authored base, key, and value expressions.
    #[must_use]
    pub fn arguments(&self) -> [&Expr; 3] {
        self.arguments.each_ref()
    }

    /// The keys of the base, key, and value expressions, given by the clause
    /// that writes the update; each has the ordinal of the updated cell's
    /// result field.
    #[must_use]
    pub fn argument_keys(&self) -> [Option<&ProvenanceKey>; 3] {
        self.argument_keys.each_ref().map(Option::as_ref)
    }

    /// Records the keys of the base, key, and value expressions.
    pub(super) fn set_argument_keys(&mut self, keys: [ProvenanceKey; 3]) {
        self.argument_keys = keys.map(Some);
    }

    /// Forgets the keys of the update, before a clause's pass keys it.
    pub(super) fn clear_keys(&mut self) {
        self.term.clear_keys();
        self.argument_keys = [None, None, None];
    }
}

pub(super) struct HaveMapExtra {
    pub(super) cell: Ident,
    pub(super) key: Box<TermExpression>,
    pub(super) value: Ident,
}

impl From<HaveMapExtra> for RuleExtra {
    fn from(extra: HaveMapExtra) -> Self {
        Self::HaveMap {
            cell: extra.cell,
            entries: vec![RuleMapEntry::new(extra.key, extra.value)],
        }
    }
}

pub(super) struct MapUpdateExtra {
    pub(super) cell: Ident,
    pub(super) base: Ident,
    update: Box<RuleMapUpdate>,
}

impl From<MapUpdateExtra> for RuleExtra {
    fn from(extra: MapUpdateExtra) -> Self {
        Self::UpdateMap {
            cell: extra.cell,
            base: extra.base,
            update: extra.update,
        }
    }
}

pub(super) fn parse_have_extra(input: ParseStream<'_>) -> Result<HaveMapExtra, ParseError> {
    let cell = input.call(Ident::parse_any)?;
    let content = input.call(|input| {
        let content;
        bracketed!(content in input);
        Ok(content)
    })?;
    let key = parse_expression_before_arrow(&content)?;
    content.parse::<Token![->]>()?;
    content.parse::<Token![let]>()?;
    let value = content.call(Ident::parse_any)?;
    validate_authored_binder(&value.to_string(), value.span())?;
    if !content.is_empty() {
        return Err(content
            .error("unexpected tokens after map binding value")
            .into());
    }
    Ok(HaveMapExtra {
        cell,
        key: Box::new(TermExpression::from_expression(key)?),
        value,
    })
}

pub(super) fn parse_update_extra(input: ParseStream<'_>) -> Result<MapUpdateExtra, ParseError> {
    let cell = input.call(Ident::parse_any)?;
    validate_authored_binder(&cell.to_string(), cell.span())?;
    input.parse::<Token![=]>()?;
    let expression: Expr = input.parse()?;
    parse_map_update(
        &cell,
        &cell,
        &expression,
        "the update base must be the cell",
    )
}

pub(super) fn parse_map_update(
    cell: &Ident,
    expected_base: &Ident,
    expression: &Expr,
    base_error: &str,
) -> Result<MapUpdateExtra, ParseError> {
    let Expr::Call(ExprCall { func, args, .. }) = expression else {
        return Err(syn::Error::new(
            expression.span(),
            "a changed map cell requires one ordinary three-argument update term",
        )
        .into());
    };
    let Expr::Path(function) = func.as_ref() else {
        return Err(syn::Error::new(
            func.span(),
            "a changed map cell update must have a plain path head",
        )
        .into());
    };
    if function.qself.is_some() || !is_plain_path(&function.path) {
        return Err(syn::Error::new(
            function.path.span(),
            "a changed map cell update must have a plain path head",
        )
        .into());
    }
    let arguments = args.iter().collect::<Vec<_>>();
    let [base, key, value] = arguments.as_slice() else {
        return Err(syn::Error::new(
            args.span(),
            "a map update term requires exactly three arguments",
        )
        .into());
    };
    let base_expression = *base;
    let Expr::Path(base) = base else {
        return Err(syn::Error::new(
            base.span(),
            "the first map update argument must be the matched whole-map binding",
        )
        .into());
    };
    if base.path.leading_colon.is_some()
        || base.path.segments.len() != 1
        || base.path.segments[0].ident.unraw() != expected_base.unraw()
    {
        return Err(syn::Error::new(
            base.path.span(),
            format!("{base_error} `{}`", expected_base.unraw()),
        )
        .into());
    }
    let update = TermExpression::from_expression(expression.clone())?;
    Ok(MapUpdateExtra {
        cell: cell.clone(),
        base: base.path.segments[0].ident.clone(),
        update: Box::new(RuleMapUpdate {
            term: update,
            arguments: [base_expression.clone(), (*key).clone(), (*value).clone()],
            argument_keys: [None, None, None],
        }),
    })
}

pub(crate) fn take_requires_helper(
    attributes: &mut Vec<Attribute>,
) -> Result<Option<RuleCondition>, SyntaxError> {
    let mut condition = None;
    let mut retained = Vec::with_capacity(attributes.len());
    for attribute in std::mem::take(attributes) {
        let is_requires = attribute.path().segments.len() >= 2
            && attribute
                .path()
                .segments
                .last()
                .is_some_and(|segment| segment.ident == "requires");
        if !is_requires {
            retained.push(attribute);
            continue;
        }
        if condition.is_some() {
            return Err(unsupported_signature(
                "a rule may declare only one `#[k::requires(...)]` condition",
                attribute.span(),
            ));
        }
        let Meta::List(list) = attribute.meta else {
            return Err(unsupported_signature(
                "`#[k::requires]` requires one parenthesized object-Bool term",
                attribute.span(),
            ));
        };
        let term = TermExpression::parse_tokens(crate::parse::strip_trailing_comma(list.tokens))?;
        if term.root_kind() == crate::TermRootKind::Literal {
            return Err(unsupported_signature(
                "a rule condition must be an object-Bool term constructor, not a host literal",
                term.expression().span(),
            ));
        }
        condition = Some(RuleCondition::keyed(term)?);
    }
    *attributes = retained;
    Ok(condition)
}
