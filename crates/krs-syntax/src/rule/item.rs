use proc_macro2::TokenStream;
use syn::spanned::Spanned;
use syn::{Expr, FnArg, ItemFn, ReturnType, Stmt, Type};

use super::condition::{RuleCondition, take_requires_helper};
use super::pattern::{
    NegativeLiteralSpans, RulePattern, canonical_key, is_bound_path, is_bound_reference,
    parse_rule_pattern, push_candidate, push_term_node_anchors, push_term_reference_candidates,
    push_wildcard_anchors,
};
use crate::parse::{
    KrsSyntax, checked_ordinal, unsupported_rule_signature as unsupported_signature,
};
use crate::term::{
    is_term_macro, push_lexeme_anchors, push_record_field_anchors, unexpected_macro,
};
use crate::term_sort::{TermSort, parse_readable_sort, parse_term_sort};
use crate::{
    ProvenanceAnchor, ProvenanceRole, ReferenceCandidate, SyntaxError, SyntaxErrorKind,
    TermExpression, TermNode, TermSymbolKind, TermTree, TokenRange,
};

/// The one typed subject parameter of a rule clause.
#[derive(Clone, Debug)]
pub struct RuleParameter {
    /// Validated named-constructor subject pattern.
    pub pattern: RulePattern,
    /// Rust-resolved term sort.
    pub term_sort: TermSort,
}

/// Validated one-clause rule function.
#[derive(Clone, Debug)]
pub struct RuleItem {
    pub(super) item: ItemFn,
    pub(super) parameter: RuleParameter,
    result_sort: TermSort,
    result: TermExpression,
    subject_tree: TermTree,
    requires: Option<RuleCondition>,
}

impl RuleItem {
    /// Validates a previously parsed Rust function as a rule clause.
    ///
    /// # Errors
    ///
    /// Rejects signature modifiers, arity other than one, receivers, non-term
    /// types, unsupported patterns, and bodies other than one named term.
    pub fn from_item(item: ItemFn) -> Result<Self, SyntaxError> {
        Self::from_item_with_signs(item, NegativeLiteralSpans::default())
    }

    /// [`Self::from_item`] with the negative-literal spans of the item's source tokens.
    fn from_item_with_signs(
        mut item: ItemFn,
        signs: NegativeLiteralSpans,
    ) -> Result<Self, SyntaxError> {
        Self::from_item_with_sort_parser(&mut item, parse_term_sort, false, false, signs)
    }

    pub(super) fn from_readable_item(
        mut item: ItemFn,
        signs: NegativeLiteralSpans,
    ) -> Result<Self, SyntaxError> {
        Self::from_item_with_sort_parser(&mut item, parse_readable_sort, true, true, signs)
    }

    fn from_item_with_sort_parser(
        item: &mut ItemFn,
        sort_parser: fn(Type) -> Result<TermSort, SyntaxError>,
        allow_record_rest: bool,
        root_identifier_is_binding: bool,
        signs: NegativeLiteralSpans,
    ) -> Result<Self, SyntaxError> {
        validate_signature_features(item)?;
        let argument = item.sig.inputs.first().ok_or_else(|| {
            unsupported_signature(
                "a rule must have exactly one subject parameter",
                item.sig.span(),
            )
        })?;
        let FnArg::Typed(argument) = argument else {
            return Err(unsupported_signature(
                "rules cannot have a `self` receiver",
                argument.span(),
            ));
        };
        if !argument.attrs.is_empty() {
            return Err(unsupported_signature(
                "parameter attributes are outside the rule shape",
                argument.attrs[0].span(),
            ));
        }
        let (pattern, subject_tree) = parse_rule_pattern(
            (*argument.pat).clone(),
            allow_record_rest,
            root_identifier_is_binding,
            signs,
        )?;
        let parameter_sort = sort_parser((*argument.ty).clone())?;

        let ReturnType::Type(_, result_type) = &item.sig.output else {
            return Err(unsupported_signature(
                "a rule must declare a `Term<SortPath>` result",
                item.sig.ident.span(),
            ));
        };
        let result_sort = sort_parser((**result_type).clone())?;
        let result = parse_rule_body(item)?;
        let requires = take_requires_helper(&mut item.attrs)?;

        Ok(Self {
            item: item.clone(),
            parameter: RuleParameter {
                pattern,
                term_sort: parameter_sort,
            },
            result_sort,
            result,
            subject_tree,
            requires,
        })
    }

    /// Returns the original Rust function with authored spans.
    #[must_use]
    pub const fn item(&self) -> &ItemFn {
        &self.item
    }

    /// Returns the single subject parameter.
    #[must_use]
    pub const fn parameter(&self) -> &RuleParameter {
        &self.parameter
    }

    /// Returns the rule's result sort.
    #[must_use]
    pub const fn result_sort(&self) -> &TermSort {
        &self.result_sort
    }

    /// Returns the validated right-hand term payload.
    #[must_use]
    pub const fn result(&self) -> &TermExpression {
        &self.result
    }

    /// Returns the structured argument-preserving rule-subject tree.
    #[must_use]
    pub const fn subject_tree(&self) -> &TermTree {
        &self.subject_tree
    }

    /// Returns the optional object-language Boolean applicability condition.
    #[must_use]
    pub const fn requires(&self) -> Option<&RuleCondition> {
        self.requires.as_ref()
    }

    /// Returns canonical rule node anchors and nested path anchors.
    ///
    /// # Errors
    ///
    /// Returns an endpoint error only if a parsed Rust node emits no leaves.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = vec![
            ProvenanceAnchor::new(
                ProvenanceRole::RuleDeclaration,
                0,
                TokenRange::for_tokens(&self.item.sig.ident)?,
            ),
            ProvenanceAnchor::new(
                ProvenanceRole::RulePattern,
                0,
                self.parameter.pattern.range()?,
            ),
            ProvenanceAnchor::new(
                ProvenanceRole::RuleType,
                0,
                TokenRange::for_tokens(self.parameter.term_sort.ty())?,
            ),
            ProvenanceAnchor::new(
                ProvenanceRole::RuleResultType,
                0,
                TokenRange::for_tokens(self.result_sort.ty())?,
            ),
            ProvenanceAnchor::new(
                ProvenanceRole::RuleResult,
                0,
                TokenRange::for_tokens(self.result.expression())?,
            ),
        ];
        for (ordinal, range) in self
            .parameter
            .pattern
            .path_ranges()?
            .into_iter()
            .enumerate()
        {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::RuleLeftPath,
                checked_ordinal(ordinal, ProvenanceRole::RuleLeftPath, range.first())?,
                range,
            ));
        }
        for (ordinal, symbol) in self.result.symbols().iter().enumerate() {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::RuleRightPath,
                checked_ordinal(ordinal, ProvenanceRole::RuleRightPath, symbol.path().span())?,
                TokenRange::for_tokens(symbol.path())?,
            ));
        }
        Ok(anchors)
    }

    /// Returns the compact catalog plus typed subject/result term-node
    /// anchors required by protocol v6.
    ///
    /// # Errors
    ///
    /// Returns endpoint or occurrence-overflow errors.
    pub fn full_provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut anchors = self.provenance()?;
        push_term_node_anchors(
            &mut anchors,
            self.parameter.pattern.nodes(),
            ProvenanceRole::RuleLeftApplicationHead,
            ProvenanceRole::RuleLeftReference,
            ProvenanceRole::RuleLeftLiteral,
        )?;
        push_record_field_anchors(
            &mut anchors,
            &self.subject_tree,
            ProvenanceRole::RuleLeftRecordFieldName,
        )?;
        push_wildcard_anchors(&mut anchors, &self.subject_tree)?;
        push_term_node_anchors(
            &mut anchors,
            self.result.nodes(),
            ProvenanceRole::RuleRightApplicationHead,
            ProvenanceRole::RuleRightReference,
            ProvenanceRole::RuleRightLiteral,
        )?;
        push_record_field_anchors(
            &mut anchors,
            self.result.tree(),
            ProvenanceRole::RuleRightRecordFieldName,
        )?;
        if let Some(requires) = &self.requires {
            anchors.extend(requires.provenance()?);
        }
        let mut lexemes = 0_usize;
        push_lexeme_anchors(&mut anchors, self.parameter.pattern.nodes(), &mut lexemes)?;
        push_lexeme_anchors(&mut anchors, self.result.nodes(), &mut lexemes)?;
        if let Some(requires) = &self.requires {
            push_lexeme_anchors(&mut anchors, requires.term().nodes(), &mut lexemes)?;
        }
        Ok(anchors)
    }

    /// Returns rustc-resolvable type and constructor references in canonical order.
    ///
    /// The order is parameter type, result type, subject paths in preorder,
    /// then result paths in preorder. Each path retains the ordinal assigned by
    /// [`Self::provenance`]. Skipping a bare bound variable therefore leaves an
    /// ordinal gap rather than renumbering later references.
    ///
    /// # Errors
    ///
    /// Returns a structured overflow error if one path role has more than
    /// `u32::MAX` occurrences.
    pub fn reference_candidates(&self) -> Result<Vec<ReferenceCandidate>, SyntaxError> {
        let mut candidates = vec![
            ReferenceCandidate {
                key: canonical_key(ProvenanceRole::RuleType, 0),
                path: self.parameter.term_sort.sort().clone(),
                kind: (),
            },
            ReferenceCandidate {
                key: canonical_key(ProvenanceRole::RuleResultType, 0),
                path: self.result_sort.sort().clone(),
                kind: (),
            },
        ];

        match &self.parameter.pattern {
            RulePattern::Native {
                nodes, bindings, ..
            } => {
                let mut ordinal = 0_usize;
                for node in nodes {
                    let path = match node {
                        TermNode::ApplicationHead(path) => path,
                        TermNode::Reference(path) => {
                            let current = ordinal;
                            ordinal += 1;
                            if is_bound_path(path, bindings) {
                                continue;
                            }
                            push_candidate(
                                &mut candidates,
                                ProvenanceRole::RuleLeftPath,
                                current,
                                path,
                            )?;
                            continue;
                        }
                        TermNode::Literal(_)
                        | TermNode::IdToken(_)
                        | TermNode::BytesToken(_)
                        | TermNode::Anonymous { .. }
                        | TermNode::OrBool(_)
                        | TermNode::Lexeme { .. } => continue,
                    };
                    push_candidate(&mut candidates, ProvenanceRole::RuleLeftPath, ordinal, path)?;
                    ordinal += 1;
                }
            }
            RulePattern::TermMacro { term, bindings, .. } => {
                for (ordinal, symbol) in term.symbols().iter().enumerate() {
                    if is_bound_reference(symbol, bindings) {
                        continue;
                    }
                    push_candidate(
                        &mut candidates,
                        ProvenanceRole::RuleLeftPath,
                        ordinal,
                        symbol.path(),
                    )?;
                }
            }
        }

        let bindings = self.parameter.pattern.bindings();
        for (ordinal, symbol) in self.result.symbols().iter().enumerate() {
            if is_bound_reference(symbol, bindings) {
                continue;
            }
            push_candidate(
                &mut candidates,
                ProvenanceRole::RuleRightPath,
                ordinal,
                symbol.path(),
            )?;
        }
        Ok(candidates)
    }

    /// Returns only rule-term application/reference candidates under the
    /// typed protocol-v6 role catalog. Bound bare paths remain absent without
    /// renumbering later same-kind occurrences.
    ///
    /// Resolution to a declared production or a builtin operation remains a
    /// compiler responsibility based on the exact retained Rust path.
    ///
    /// # Errors
    ///
    /// Returns an occurrence-overflow error for pathological input.
    pub fn term_reference_candidates(
        &self,
    ) -> Result<Vec<ReferenceCandidate<TermSymbolKind>>, SyntaxError> {
        let mut candidates = Vec::new();
        push_term_reference_candidates(
            &mut candidates,
            self.parameter.pattern.nodes(),
            self.parameter.pattern.bindings(),
            ProvenanceRole::RuleLeftApplicationHead,
            ProvenanceRole::RuleLeftReference,
        )?;
        push_term_reference_candidates(
            &mut candidates,
            self.result.nodes(),
            self.parameter.pattern.bindings(),
            ProvenanceRole::RuleRightApplicationHead,
            ProvenanceRole::RuleRightReference,
        )?;
        if let Some(requires) = &self.requires {
            candidates.extend(requires.reference_candidates(self.parameter.pattern.bindings())?);
        }
        Ok(candidates)
    }
}

impl KrsSyntax for RuleItem {
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        let signs = NegativeLiteralSpans::of_fn_parameters(tokens.clone());
        Self::from_item_with_signs(syn::parse2::<ItemFn>(tokens)?, signs)
    }
}

fn validate_signature_features(item: &ItemFn) -> Result<(), SyntaxError> {
    let signature = &item.sig;
    if signature.inputs.len() != 1 {
        return Err(unsupported_signature(
            "a rule must have exactly one subject parameter",
            signature.inputs.span(),
        ));
    }
    if let Some(token) = signature.constness {
        return Err(unsupported_signature("rules cannot be `const`", token.span));
    }
    if let Some(token) = signature.asyncness {
        return Err(unsupported_signature("rules cannot be `async`", token.span));
    }
    if let Some(token) = signature.unsafety {
        return Err(unsupported_signature(
            "rules cannot be `unsafe`",
            token.span,
        ));
    }
    if let Some(abi) = &signature.abi {
        return Err(unsupported_signature(
            "rules cannot declare an extern ABI",
            abi.span(),
        ));
    }
    if !signature.generics.params.is_empty() {
        return Err(unsupported_signature(
            "rule generics are not supported",
            signature.generics.params.span(),
        ));
    }
    if let Some(where_clause) = &signature.generics.where_clause {
        return Err(unsupported_signature(
            "rule where clauses are not supported",
            where_clause.span(),
        ));
    }
    if let Some(variadic) = &signature.variadic {
        return Err(unsupported_signature(
            "variadic rules are not supported",
            variadic.span(),
        ));
    }
    Ok(())
}

fn parse_rule_body(item: &ItemFn) -> Result<TermExpression, SyntaxError> {
    if item.block.stmts.len() != 1 {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedRuleBody {
                reason: "the body must contain exactly one term expression",
            },
            item.block.span(),
        ));
    }
    let Stmt::Expr(expression, None) = &item.block.stmts[0] else {
        return Err(SyntaxError::new(
            SyntaxErrorKind::UnsupportedRuleBody {
                reason: "the sole result term must not have a trailing semicolon",
            },
            item.block.stmts[0].span(),
        ));
    };
    match expression {
        Expr::Macro(expression_macro) => {
            if !is_term_macro(&expression_macro.mac.path) {
                return Err(unexpected_macro(&expression_macro.mac.path));
            }
            TermExpression::parse_tokens(expression_macro.mac.tokens.clone())
        }
        expression => TermExpression::from_expression(expression.clone()),
    }
}
