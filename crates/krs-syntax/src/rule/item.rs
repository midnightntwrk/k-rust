use proc_macro2::TokenStream;
use syn::ext::IdentExt;
use syn::spanned::Spanned;
use syn::{Expr, FnArg, Ident, ItemFn, Pat, PatType, ReturnType, Stmt, Type};

use super::condition::{RuleCondition, take_requires_helper};
use super::existentials::RuleExistentials;
use super::pattern::{
    NegativeLiteralSpans, RulePattern, canonical_key, is_bound_path, is_bound_reference,
    parse_rule_pattern, push_candidate, push_term_node_anchors, push_term_reference_candidates,
    push_wildcard_anchors,
};
use crate::parse::{
    KrsSyntax, checked_ordinal, unsupported_rule_signature as unsupported_signature,
};
use crate::term::{
    is_term_macro, push_lexeme_anchors, push_record_field_anchors, push_sort_test_anchors,
    unexpected_macro,
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

/// The binder-list contract shared by every fn-shaped sentence (X5), as a
/// diagnostic reason.
pub const BINDER_LIST_CONTRACT: &str = "typed term parameters must declare every term binder of the subject and function context, in first-occurrence order (hole binders included; `_`, remainders, HERE, instance labels and local binders excluded)";

/// One declared typed binder `name: Sort` before the subject of a rule fn
/// (KF-009): K's sort-restricted variable `NAME:Sort`.
#[derive(Clone, Debug)]
pub struct RuleBinder {
    name: Ident,
    term_sort: TermSort,
    parameter: PatType,
}

impl RuleBinder {
    /// Returns the declared binding name.
    #[must_use]
    pub const fn name(&self) -> &Ident {
        &self.name
    }

    /// Returns the declared sort, which may be narrower than inference would choose.
    #[must_use]
    pub const fn term_sort(&self) -> &TermSort {
        &self.term_sort
    }

    /// Returns the complete authored `name: Type` parameter.
    #[must_use]
    pub const fn parameter(&self) -> &PatType {
        &self.parameter
    }
}

/// Validated one-clause rule function.
#[derive(Clone, Debug)]
pub struct RuleItem {
    pub(super) item: ItemFn,
    pub(super) binders: Vec<RuleBinder>,
    pub(super) parameter: RuleParameter,
    result_sort: TermSort,
    result: TermExpression,
    subject_tree: TermTree,
    requires: Option<RuleCondition>,
    existentials: RuleExistentials,
    /// Result names a desugar clause's `unbound_variables` lists (KF-046).
    unbound: Vec<Ident>,
}

impl RuleItem {
    /// Validates a previously parsed Rust function as a rule clause.
    ///
    /// # Errors
    ///
    /// Rejects signature modifiers, a missing subject, receivers, non-term
    /// types, unsupported patterns, binder lists that break the binder-list
    /// contract, and bodies other than one named term.
    pub fn from_item(item: ItemFn) -> Result<Self, SyntaxError> {
        Self::from_item_with_signs(item, NegativeLiteralSpans::default())
    }

    /// [`Self::from_item`] with the negative-literal spans of the item's source tokens.
    fn from_item_with_signs(
        mut item: ItemFn,
        signs: NegativeLiteralSpans,
    ) -> Result<Self, SyntaxError> {
        Self::from_item_with_sort_parser(&mut item, parse_term_sort, false, false, signs, false)
    }

    /// Validates a desugar clause fn with its `#[k::desugar(..)]` payload
    /// (KF-046): the names `unbound_variables` lists are result variables the
    /// pattern does not bind, and `_` admits wildcards in the result.
    ///
    /// # Errors
    ///
    /// Everything [`Self::from_item`] rejects, a listed name the pattern
    /// binds or the result does not use, and `_` when the result has no
    /// wildcard.
    pub fn from_desugar_item(
        item: ItemFn,
        attribute: &crate::DesugarAttribute,
    ) -> Result<Self, SyntaxError> {
        Self::desugar_with_signs(item, attribute, NegativeLiteralSpans::default())
    }

    /// [`Self::from_desugar_item`] from the clause fn's source tokens.
    ///
    /// # Errors
    ///
    /// As [`Self::from_desugar_item`], and Rust syntax errors.
    pub fn parse_desugar_tokens(
        tokens: TokenStream,
        attribute: &crate::DesugarAttribute,
    ) -> Result<Self, SyntaxError> {
        let signs = NegativeLiteralSpans::of_fn_parameters(tokens.clone());
        Self::desugar_with_signs(syn::parse2::<ItemFn>(tokens)?, attribute, signs)
    }

    fn desugar_with_signs(
        mut item: ItemFn,
        attribute: &crate::DesugarAttribute,
        signs: NegativeLiteralSpans,
    ) -> Result<Self, SyntaxError> {
        let wildcards = attribute
            .unbound_variables()
            .is_some_and(|unbound| unbound.wildcard().is_some());
        Self::from_item_with_sort_parser(
            &mut item,
            parse_term_sort,
            false,
            false,
            signs,
            wildcards,
        )?
        .apply_unbound_variables(attribute)
    }

    pub(super) fn from_readable_item(
        mut item: ItemFn,
        signs: NegativeLiteralSpans,
    ) -> Result<Self, SyntaxError> {
        Self::from_item_with_sort_parser(&mut item, parse_readable_sort, true, true, signs, false)
    }

    fn from_item_with_sort_parser(
        item: &mut ItemFn,
        sort_parser: fn(Type) -> Result<TermSort, SyntaxError>,
        allow_record_rest: bool,
        root_identifier_is_binding: bool,
        signs: NegativeLiteralSpans,
        result_wildcards: bool,
    ) -> Result<Self, SyntaxError> {
        validate_signature_features(item)?;
        let binders = parse_rule_binders(item)?;
        let argument = item.sig.inputs.last().ok_or_else(|| {
            unsupported_signature(
                "a rule must end with one subject parameter",
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
        validate_binder_list(&binders, pattern.bindings())?;

        let ReturnType::Type(_, result_type) = &item.sig.output else {
            return Err(unsupported_signature(
                "a rule must declare a `Term<SortPath>` result",
                item.sig.ident.span(),
            ));
        };
        let result_sort = sort_parser((**result_type).clone())?;
        let result = if result_wildcards {
            parse_rule_body_with_wildcards(item)?
        } else {
            parse_rule_body(item)?
        };
        let requires = take_requires_helper(&mut item.attrs)?;
        let existentials = RuleExistentials::take(&mut item.attrs)?;
        // A readable clause checks its existentials against every cell it
        // writes (`RuleClause::check_existentials`); its item has only the head.
        if !root_identifier_is_binding {
            existentials.check_shadowing(pattern.bindings())?;
            existentials.check_scope(requires.as_ref().map(RuleCondition::term), &[&result])?;
        }

        Ok(Self {
            item: item.clone(),
            binders,
            parameter: RuleParameter {
                pattern,
                term_sort: parameter_sort,
            },
            result_sort,
            result,
            subject_tree,
            requires,
            existentials,
            unbound: Vec::new(),
        })
    }

    /// Checks a desugar clause's `unbound_variables = [x, _]` against the
    /// parsed clause and records the listed names as result bindings.
    fn apply_unbound_variables(
        mut self,
        attribute: &crate::DesugarAttribute,
    ) -> Result<Self, SyntaxError> {
        let Some(unbound) = attribute.unbound_variables() else {
            return Ok(self);
        };
        if let Some(wildcard) = unbound.wildcard() {
            let mut ranges = Vec::new();
            self.result.tree().wildcard_ranges_preorder(&mut ranges);
            if ranges.is_empty() {
                return Err(unbound_variables_error(
                    "`_` is listed in `unbound_variables`, but the result has no `_`; list `_` only for a result with wildcards",
                    wildcard.span,
                ));
            }
        }
        for name in unbound.names() {
            if self
                .parameter
                .pattern
                .bindings()
                .iter()
                .any(|binding| binding.unraw() == name.unraw())
            {
                return Err(unbound_variables_error(
                    &format!(
                        "`{}` is bound by the pattern; `unbound_variables` lists only result names the pattern does not bind",
                        name.unraw()
                    ),
                    name.span(),
                ));
            }
            if !super::existentials::references(&self.result, name) {
                return Err(unbound_variables_error(
                    &format!(
                        "`{}` does not occur in the result; `unbound_variables` lists result names the pattern does not bind",
                        name.unraw()
                    ),
                    name.span(),
                ));
            }
            self.unbound.push(name.clone());
        }
        Ok(self)
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

    /// Returns the declared typed binders: empty, or every subject binding in
    /// first-occurrence order.
    #[must_use]
    pub fn binders(&self) -> &[RuleBinder] {
        &self.binders
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

    /// Returns the `#[k::exists]` and `#[k::ensures]` helpers of a transition.
    #[must_use]
    pub const fn existentials(&self) -> &RuleExistentials {
        &self.existentials
    }

    /// Subject bindings followed by the existentials: every name the result
    /// and the ensures condition may reference.
    #[must_use]
    pub fn result_bindings(&self) -> Vec<syn::Ident> {
        let mut bindings = self.parameter.pattern.bindings().to_vec();
        bindings.extend(self.existentials.names());
        bindings.extend(self.unbound.iter().cloned());
        bindings
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
        for (ordinal, binder) in self.binders.iter().enumerate() {
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::RuleBindingParameter,
                checked_ordinal(
                    ordinal,
                    ProvenanceRole::RuleBindingParameter,
                    binder.name.span(),
                )?,
                TokenRange::for_tokens(&binder.parameter)?,
            ));
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::RuleBindingType,
                checked_ordinal(
                    ordinal,
                    ProvenanceRole::RuleBindingType,
                    binder.term_sort.sort().span(),
                )?,
                TokenRange::for_tokens(binder.term_sort.sort())?,
            ));
        }
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
        push_wildcard_anchors(
            &mut anchors,
            &self.subject_tree,
            ProvenanceRole::RuleLeftWildcard,
        )?;
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
        push_wildcard_anchors(
            &mut anchors,
            self.result.tree(),
            ProvenanceRole::RuleRightWildcard,
        )?;
        if let Some(requires) = &self.requires {
            anchors.extend(requires.provenance()?);
        }
        anchors.extend(self.existentials.provenance()?);
        let mut lexemes = 0_usize;
        push_lexeme_anchors(&mut anchors, self.parameter.pattern.nodes(), &mut lexemes)?;
        push_lexeme_anchors(&mut anchors, self.result.nodes(), &mut lexemes)?;
        if let Some(requires) = &self.requires {
            push_lexeme_anchors(&mut anchors, requires.term().nodes(), &mut lexemes)?;
        }
        if let Some(ensures) = self.existentials.ensures() {
            push_lexeme_anchors(&mut anchors, ensures.nodes(), &mut lexemes)?;
        }
        let mut aliases = 0_usize;
        crate::term::push_pattern_as_anchors(
            &mut anchors,
            self.parameter.pattern.nodes(),
            &mut aliases,
        )?;
        let mut alternatives = 0_usize;
        crate::term::push_pattern_or_anchors(
            &mut anchors,
            self.parameter.pattern.nodes(),
            &mut alternatives,
        )?;
        let mut sort_tests = 0_usize;
        push_sort_test_anchors(
            &mut anchors,
            self.parameter.pattern.nodes(),
            &mut sort_tests,
        )?;
        push_sort_test_anchors(&mut anchors, self.result.nodes(), &mut sort_tests)?;
        if let Some(requires) = &self.requires {
            push_sort_test_anchors(&mut anchors, requires.term().nodes(), &mut sort_tests)?;
        }
        if let Some(ensures) = self.existentials.ensures() {
            push_sort_test_anchors(&mut anchors, ensures.nodes(), &mut sort_tests)?;
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
                        | TermNode::Lexeme { .. }
                        | TermNode::SortTest { .. }
                        | TermNode::As { .. }
                        | TermNode::Or(_) => continue,
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

        let bindings = self.result_bindings();
        for (ordinal, symbol) in self.result.symbols().iter().enumerate() {
            if is_bound_reference(symbol, &bindings) {
                continue;
            }
            push_candidate(
                &mut candidates,
                ProvenanceRole::RuleRightPath,
                ordinal,
                symbol.path(),
            )?;
        }
        for (ordinal, binder) in self.binders.iter().enumerate() {
            push_candidate(
                &mut candidates,
                ProvenanceRole::RuleBindingType,
                ordinal,
                binder.term_sort.sort(),
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
        let result_bindings = self.result_bindings();
        push_term_reference_candidates(
            &mut candidates,
            self.result.nodes(),
            &result_bindings,
            ProvenanceRole::RuleRightApplicationHead,
            ProvenanceRole::RuleRightReference,
        )?;
        if let Some(requires) = &self.requires {
            candidates.extend(requires.reference_candidates(self.parameter.pattern.bindings())?);
        }
        candidates.extend(self.existentials.reference_candidates(&result_bindings)?);
        Ok(candidates)
    }
}

impl KrsSyntax for RuleItem {
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        let signs = NegativeLiteralSpans::of_fn_parameters(tokens.clone());
        crate::term::reject_pattern_alias_in_fn_body(&tokens)?;
        Self::from_item_with_signs(syn::parse2::<ItemFn>(tokens)?, signs)
    }
}

fn validate_signature_features(item: &ItemFn) -> Result<(), SyntaxError> {
    let signature = &item.sig;
    if signature.inputs.is_empty() {
        return Err(unsupported_signature(
            "a rule must end with one subject parameter",
            signature.span(),
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

fn binder_error(reason: String, span: proc_macro2::Span) -> SyntaxError {
    SyntaxError::new(SyntaxErrorKind::InvalidBinderList { reason }, span)
}

/// Parses the typed binder parameters before the subject (KF-009, X5).
fn parse_rule_binders(item: &ItemFn) -> Result<Vec<RuleBinder>, SyntaxError> {
    let mut binders = Vec::<RuleBinder>::new();
    let count = item.sig.inputs.len().saturating_sub(1);
    for argument in item.sig.inputs.iter().take(count) {
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
        let Pat::Ident(pattern) = &*argument.pat else {
            return Err(binder_error(
                "a typed binder must be a plain immutable identifier, as in `x: Int`; the subject parameter comes last".to_owned(),
                argument.pat.span(),
            ));
        };
        if pattern.by_ref.is_some() || pattern.mutability.is_some() || pattern.subpat.is_some() {
            return Err(binder_error(
                "a typed binder must be a plain immutable identifier, as in `x: Int`, without `ref`, `mut`, or `@`".to_owned(),
                pattern.span(),
            ));
        }
        crate::parse::validate_authored_binder(&pattern.ident.to_string(), pattern.ident.span())?;
        if binders
            .iter()
            .any(|existing| existing.name.unraw() == pattern.ident.unraw())
        {
            return Err(binder_error(
                format!("binder `{}` is declared twice", pattern.ident.unraw()),
                pattern.ident.span(),
            ));
        }
        let authored = (*argument.ty).clone();
        let term_sort =
            parse_term_sort(authored.clone()).or_else(|_| parse_readable_sort(authored))?;
        binders.push(RuleBinder {
            name: pattern.ident.clone(),
            term_sort,
            parameter: argument.clone(),
        });
    }
    Ok(binders)
}

/// Checks the term-sentence binder-list contract (X5.2): no binder list, or
/// every subject binding exactly once in first-occurrence order.
fn validate_binder_list(binders: &[RuleBinder], bindings: &[Ident]) -> Result<(), SyntaxError> {
    if binders.is_empty() {
        return Ok(());
    }
    for binder in binders {
        if !bindings
            .iter()
            .any(|binding| binding.unraw() == binder.name.unraw())
        {
            return Err(binder_error(
                format!(
                    "binder `{}` is declared but does not occur in the subject",
                    binder.name.unraw()
                ),
                binder.name.span(),
            ));
        }
    }
    let mismatch = binders
        .iter()
        .zip(bindings)
        .find(|(binder, binding)| binder.name.unraw() != binding.unraw())
        .map(|(binder, _)| binder.name.span());
    if binders.len() != bindings.len() || mismatch.is_some() {
        let expected = bindings
            .iter()
            .map(|binding| binding.unraw().to_string())
            .collect::<Vec<_>>()
            .join(", ");
        return Err(binder_error(
            format!(
                "{BINDER_LIST_CONTRACT}; a term sentence declares no binders or all of them, here `{expected}`"
            ),
            mismatch.unwrap_or_else(|| binders[0].name.span()),
        ));
    }
    Ok(())
}

fn unbound_variables_error(reason: &str, span: proc_macro2::Span) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::InvalidUnboundVariables {
            reason: reason.to_owned(),
        },
        span,
    )
}

/// [`parse_rule_body`] for a desugar clause that lists `_` in
/// `unbound_variables`: the result may contain wildcards.
fn parse_rule_body_with_wildcards(item: &ItemFn) -> Result<TermExpression, SyntaxError> {
    parse_rule_body_context(item, true)
}

fn parse_rule_body(item: &ItemFn) -> Result<TermExpression, SyntaxError> {
    parse_rule_body_context(item, false)
}

fn parse_rule_body_context(item: &ItemFn, wildcards: bool) -> Result<TermExpression, SyntaxError> {
    let term = |expression: Expr| {
        if wildcards {
            TermExpression::from_pattern_expression(expression)
        } else {
            TermExpression::from_expression(expression)
        }
    };
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
        Expr::Macro(expression_macro)
            if crate::term::is_sort_test_macro(&expression_macro.mac.path) =>
        {
            TermExpression::from_expression(expression.clone())
        }
        Expr::Macro(expression_macro) => {
            if !is_term_macro(&expression_macro.mac.path) {
                return Err(unexpected_macro(&expression_macro.mac.path));
            }
            crate::term::reject_pattern_alias(&expression_macro.mac.tokens)?;
            term(syn::parse2::<Expr>(expression_macro.mac.tokens.clone())?)
        }
        expression => term(expression.clone()),
    }
}
