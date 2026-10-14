use proc_macro2::{TokenStream, TokenTree};
use syn::ext::IdentExt;
use syn::parse::ParseStream;
use syn::spanned::Spanned;
use syn::{Attribute, Expr, ExprCall, Ident, Meta, Token, bracketed};

use super::machine::parse_expression_before_arrow;
use super::pattern::{RulePattern, push_term_node_anchors, push_term_reference_candidates};
use crate::parse::{
    KrsSyntax, ParseError, checked_ordinal, unsupported_rule_signature as unsupported_signature,
    validate_authored_binder,
};
use crate::path::is_plain_path;
use crate::term::push_record_field_anchors;
use crate::{
    ProvenanceAnchor, ProvenanceRole, ReferenceCandidate, SyntaxError, TermExpression,
    TermSymbolKind, TermTree, TokenRange,
};

/// One parsed object-language Boolean condition from `#[k::requires(...)]`.
#[derive(Clone, Debug)]
pub struct RuleCondition {
    term: TermExpression,
}

impl RuleCondition {
    /// Returns the complete structured condition term.
    #[must_use]
    pub const fn term(&self) -> &TermExpression {
        &self.term
    }

    /// Returns complete and nested parser-owned condition anchors.
    ///
    /// # Errors
    ///
    /// Returns endpoint or occurrence-overflow errors only.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = vec![ProvenanceAnchor::new(
            ProvenanceRole::RuleRequires,
            0,
            TokenRange::for_tokens(self.term.expression())?,
        )];
        for (ordinal, symbol) in self.term.symbols().iter().enumerate() {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::RuleRequiresPath,
                checked_ordinal(
                    ordinal,
                    ProvenanceRole::RuleRequiresPath,
                    symbol.path().span(),
                )?,
                TokenRange::for_tokens(symbol.path())?,
            ));
        }
        push_term_node_anchors(
            &mut anchors,
            self.term.nodes(),
            ProvenanceRole::RuleRequiresApplicationHead,
            ProvenanceRole::RuleRequiresReference,
            ProvenanceRole::RuleRequiresLiteral,
        )?;
        push_record_field_anchors(
            &mut anchors,
            self.term.tree(),
            ProvenanceRole::RuleRequiresRecordFieldName,
        )?;
        Ok(anchors)
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
            bindings,
            ProvenanceRole::RuleRequiresApplicationHead,
            ProvenanceRole::RuleRequiresReference,
        )?;
        Ok(candidates)
    }
}

/// One explicit gradual extra-cell clause in a readable rule.
#[derive(Clone, Debug)]
pub enum RuleExtra {
    /// Failable preserved map binding read.
    HaveMap {
        /// Named fixed cell.
        cell: Ident,
        /// Required key term.
        key: Box<TermExpression>,
        /// Value binder introduced only when the map item is present.
        value: Ident,
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
    /// Simultaneous exact rewrite of one ordinary fixed leaf cell.
    RewriteCell {
        /// Named fixed cell.
        cell: Ident,
        /// Complete constructor or binding pattern before the rewrite.
        before: Box<RulePattern>,
        /// Parser-owned subject tree for descriptor expansion and provenance.
        before_tree: Box<TermTree>,
        /// Complete replacement term after the rewrite.
        after: Box<TermExpression>,
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
}

impl RuleExtra {
    /// Returns the named fixed cell.
    #[must_use]
    pub const fn cell(&self) -> &Ident {
        match self {
            Self::HaveMap { cell, .. }
            | Self::UpdateMap { cell, .. }
            | Self::RewriteCell { cell, .. }
            | Self::RewriteState { cell, .. } => cell,
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

/// One validated ordinary three-argument map update.
#[derive(Clone, Debug)]
pub struct RuleMapUpdate {
    term: TermExpression,
    arguments: [Expr; 3],
}

impl RuleMapUpdate {
    /// Returns the complete structured update term.
    #[must_use]
    pub const fn term(&self) -> &TermExpression {
        &self.term
    }

    /// Returns the authored base, key, and value expressions.
    #[must_use]
    pub fn arguments(&self) -> [&Expr; 3] {
        self.arguments.each_ref()
    }
}

pub(super) struct HaveMapExtra {
    pub(super) cell: Ident,
    key: Box<TermExpression>,
    pub(super) value: Ident,
}

impl From<HaveMapExtra> for RuleExtra {
    fn from(extra: HaveMapExtra) -> Self {
        Self::HaveMap {
            cell: extra.cell,
            key: extra.key,
            value: extra.value,
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
        let term = TermExpression::parse_tokens(list.tokens)?;
        if term.root_kind() == crate::TermRootKind::Literal {
            return Err(unsupported_signature(
                "a rule condition must be an object-Bool term constructor, not a host literal",
                term.expression().span(),
            ));
        }
        condition = Some(RuleCondition { term });
    }
    *attributes = retained;
    Ok(condition)
}
