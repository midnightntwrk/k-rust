use krs_ir::ProvenanceKey;
use proc_macro2::TokenStream;
use syn::ext::IdentExt;
use syn::parse::Parser as _;
use syn::spanned::Spanned;
use syn::{Expr, FnArg, Ident, ItemFn, Pat, PatType, ReturnType, Stmt, Type};

use super::condition::{RuleCondition, take_requires_helper};
use super::existentials::RuleExistentials;
use super::pattern::{
    NegativeLiteralSpans, PatternRoot, RulePattern, allocate_term_node_keys,
    allocate_wildcard_keys, is_bound_path, is_bound_reference, parse_rule_pattern, push_candidate,
    push_term_reference_candidates,
};
use crate::parse::{KeyAllocator, KrsSyntax, unsupported_rule_signature as unsupported_signature};
use crate::state_rule::{FUNCTION_CONTEXT_ONLY_ON_EQUATIONS, FunctionContext, is_cells_parameter};
use crate::term::{
    allocate_lexeme_keys, allocate_record_field_keys, allocate_sort_test_keys, is_term_macro,
    unexpected_macro,
};
use crate::term_sort::{
    TermSort, parse_readable_sort, parse_rule_term_sort, parse_term_or_readable_sort,
    parse_term_sort,
};
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
    pattern_key: Option<ProvenanceKey>,
    type_key: Option<ProvenanceKey>,
}

impl RuleParameter {
    /// The key of the whole subject pattern; its nodes hold their own keys
    /// ([`RulePattern::keys`]).
    #[must_use]
    pub const fn pattern_key(&self) -> Option<&ProvenanceKey> {
        self.pattern_key.as_ref()
    }

    /// The key of the subject's type.
    #[must_use]
    pub const fn type_key(&self) -> Option<&ProvenanceKey> {
        self.type_key.as_ref()
    }
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
    parameter_key: Option<ProvenanceKey>,
    sort_key: Option<ProvenanceKey>,
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

    /// The key of the `name: Type` parameter.
    #[must_use]
    pub const fn parameter_key(&self) -> Option<&ProvenanceKey> {
        self.parameter_key.as_ref()
    }

    /// The key of the declared sort path.
    #[must_use]
    pub const fn sort_key(&self) -> Option<&ProvenanceKey> {
        self.sort_key.as_ref()
    }
}

/// Validated one-clause rule function.
#[derive(Clone, Debug)]
pub struct RuleItem {
    pub(super) item: ItemFn,
    pub(super) binders: Vec<RuleBinder>,
    pub(super) parameter: RuleParameter,
    /// The result sort and term; both absent exactly for a single-body rule
    /// (KF-011), whose subject's `k::rewrite!` islands say what changes.
    result_sort: Option<TermSort>,
    result: Option<TermExpression>,
    subject_tree: TermTree,
    requires: Option<RuleCondition>,
    existentials: RuleExistentials,
    /// Result names a desugar clause's `unbound_variables` lists (KF-046).
    unbound: Vec<Ident>,
    function_context: Option<FunctionContext>,
    declaration_key: Option<ProvenanceKey>,
    result_type_key: Option<ProvenanceKey>,
    /// The anchors of the catalog view ([`Self::provenance`]).
    anchors: Vec<ProvenanceAnchor>,
    /// The anchors of the full view ([`Self::full_provenance`]).
    full_anchors: Vec<ProvenanceAnchor>,
    /// The refusal of a single-body rule whose subject marks no change, a
    /// mistake of the whole sentence ([`Self::check_changes`]).
    unchanged: Option<SyntaxError>,
}

/// Which sentence keys a rule item.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ItemView {
    /// The rule is a sentence of its own.
    Rule,
    /// The item of a readable clause, which keys the item's nodes it anchors
    /// in the item's order: the declaration under `declaration`, the
    /// subject only when it is the clause's first computation item
    /// (`subject`; otherwise it is a placeholder and the clause anchors its
    /// whole subject record), the types and binders, the function context
    /// and the conditions. The clause keys the islands of every term across
    /// all its cells, and its own head result: the item's result term (and
    /// a placeholder subject) is no node of the clause and keeps the keys of
    /// the rule's own keying.
    Clause {
        declaration: ProvenanceRole,
        subject: bool,
    },
}

impl ItemView {
    const fn declaration(self) -> ProvenanceRole {
        match self {
            Self::Rule => ProvenanceRole::RuleDeclaration,
            Self::Clause { declaration, .. } => declaration,
        }
    }

    const fn keys_subject(self) -> bool {
        match self {
            Self::Rule => true,
            Self::Clause { subject, .. } => subject,
        }
    }
}

/// Which fn sentence a rule item is parsed as.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ClauseForm {
    /// A readable clause, desugar clause, or other result-returning fn.
    Plain,
    /// An equation, which may end with a function context (KF-025).
    Equation,
    /// A `#[k::rule]` fn, which may be a single-body rule (KF-011).
    Transition,
    /// A `#[k::context]` fn (KF-021): unit-returning, with at most one
    /// `k::rewrite!`, of its hole.
    Context,
}

impl RuleItem {
    /// Validates a previously parsed Rust function as a rule clause; a
    /// unit-returning fn is a single-body rule (KF-011).
    ///
    /// # Errors
    ///
    /// Rejects signature modifiers, a missing subject, receivers, non-term
    /// types, unsupported patterns, binder lists that break the binder-list
    /// contract, and bodies other than one named term.
    pub fn from_item(item: ItemFn) -> Result<Self, SyntaxError> {
        Self::from_item_with_signs(
            item,
            NegativeLiteralSpans::default(),
            ClauseForm::Transition,
        )
    }

    /// Validates a previously parsed Rust function as an equation, which may
    /// end with a function context (KF-025).
    ///
    /// # Errors
    ///
    /// The errors of [`Self::from_item`], plus a malformed function context.
    pub fn from_equation_item(item: ItemFn) -> Result<Self, SyntaxError> {
        Self::from_item_with_signs(item, NegativeLiteralSpans::default(), ClauseForm::Equation)
    }

    /// Validates an equation that a function shorthand's body defines, with
    /// the negative-literal spans of the patterns its subject takes from the
    /// body's match arms; an arm may leave a record's other fields out with
    /// `..`, as a match arm does.
    pub(crate) fn from_shorthand_item(
        mut item: ItemFn,
        signs: NegativeLiteralSpans,
    ) -> Result<Self, SyntaxError> {
        Self::from_item_with_sort_parser(
            &mut item,
            parse_rule_term_sort,
            PatternRoot::Subject,
            signs,
            false,
            ClauseForm::Equation,
        )
    }

    /// Parses an equation's tokens, which may end with a function context.
    ///
    /// # Errors
    ///
    /// The errors of [`Self::from_equation_item`].
    pub fn parse_equation_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        let signs = NegativeLiteralSpans::of_fn_parameters(tokens.clone());
        Self::from_item_with_signs(
            crate::term::parse_fn_item(tokens)?,
            signs,
            ClauseForm::Equation,
        )
    }

    /// Parses a term-shaped `#[k::context]` fn (KF-021): it returns `()`,
    /// has an empty body, and its subject holds at most one `k::rewrite!`.
    ///
    /// # Errors
    ///
    /// The errors of [`Self::from_item`], a result, a body, more than one
    /// rewrite, and `#[k::exists]`, `#[k::ensures]`, or `#[k::fresh]`.
    pub fn parse_context_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        let signs = NegativeLiteralSpans::of_fn_parameters(tokens.clone());
        Self::from_item_with_signs(syn::parse2::<ItemFn>(tokens)?, signs, ClauseForm::Context)
    }

    /// Validates a previously parsed Rust function as a term-shaped
    /// `#[k::context]` fn (KF-021).
    ///
    /// # Errors
    ///
    /// The errors of [`Self::parse_context_tokens`].
    pub fn from_context_item(item: ItemFn) -> Result<Self, SyntaxError> {
        Self::from_item_with_signs(item, NegativeLiteralSpans::default(), ClauseForm::Context)
    }

    /// Parses an equation's source text, which may end with a function context.
    ///
    /// # Errors
    ///
    /// The errors of [`Self::parse_equation_tokens`], plus Rust lexing errors.
    pub fn parse_equation_source(source: &str) -> Result<Self, SyntaxError> {
        Self::parse_equation_tokens(crate::parse::tokens_from_source(source)?)
    }

    /// [`Self::from_item`] with the negative-literal spans of the item's source tokens.
    fn from_item_with_signs(
        item: ItemFn,
        signs: NegativeLiteralSpans,
        form: ClauseForm,
    ) -> Result<Self, SyntaxError> {
        let rule = Self::from_item_judging_changes_later(item, signs, form)?;
        rule.check_changes()?;
        Ok(rule)
    }

    /// [`Self::from_item_with_signs`], except that a single-body rule whose
    /// subject marks no change is refused only by [`Self::check_changes`].
    fn from_item_judging_changes_later(
        mut item: ItemFn,
        signs: NegativeLiteralSpans,
        form: ClauseForm,
    ) -> Result<Self, SyntaxError> {
        Self::from_item_with_sort_parser(
            &mut item,
            parse_rule_term_sort,
            PatternRoot::Subject,
            signs,
            false,
            form,
        )
    }

    /// Parses a `#[k::rule]` fn's tokens as [`KrsSyntax::parse_tokens`] does,
    /// except that a single-body rule whose subject marks no change is
    /// refused only by [`Self::check_changes`]: that is a mistake of the
    /// whole sentence, told by its spelling alone, which the expansion tells
    /// after a construct the subject may not hold where it stands (told at
    /// the construct, which must go whatever the rule changes) and before a
    /// name the subject reads but nothing binds.
    ///
    /// # Errors
    ///
    /// The errors of [`KrsSyntax::parse_tokens`] but that one.
    pub fn parse_rule_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        let signs = NegativeLiteralSpans::of_fn_parameters(tokens.clone());
        Self::from_item_judging_changes_later(
            crate::term::parse_fn_item(tokens)?,
            signs,
            ClauseForm::Transition,
        )
    }

    /// Refuses a single-body rule whose subject marks no change.
    ///
    /// # Errors
    ///
    /// Returns [`SyntaxErrorKind::InvalidLocalRewrite`] at the fn's name for
    /// a single-body rule whose subject holds no `k::rewrite!`.
    pub fn check_changes(&self) -> Result<(), SyntaxError> {
        self.unchanged.clone().map_or(Ok(()), Err)
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
            PatternRoot::Subject,
            signs,
            wildcards,
            ClauseForm::Plain,
        )?
        .apply_unbound_variables(attribute)
    }

    /// Validates one `k::equations!` row, lowered to `fn label(F(args): F)
    /// -> F { result }`: its sort is the result sort of the header's function
    /// `F`. A row is readable notation, so its records may end in `..`, as a
    /// readable rule's do; `krs expand` writes the omitted fields as `_`.
    pub(super) fn from_table_item(
        mut item: ItemFn,
        signs: NegativeLiteralSpans,
    ) -> Result<Self, SyntaxError> {
        Self::from_item_with_sort_parser(
            &mut item,
            crate::term_sort::parse_function_result_sort,
            PatternRoot::Subject,
            signs,
            false,
            ClauseForm::Equation,
        )
    }

    /// Validates a readable `for Sort` clause, whose subject's root is the
    /// matched constructor.
    pub(super) fn from_readable_item(
        item: ItemFn,
        signs: NegativeLiteralSpans,
    ) -> Result<Self, SyntaxError> {
        Self::from_readable_item_with_root(item, PatternRoot::Clause, signs)
    }

    /// Validates a readable machine record's head, whose subject is its
    /// first computation item: a readable value, not a rule subject.
    pub(super) fn from_readable_value_item(
        item: ItemFn,
        signs: NegativeLiteralSpans,
    ) -> Result<Self, SyntaxError> {
        Self::from_readable_item_with_root(item, PatternRoot::Value, signs)
    }

    fn from_readable_item_with_root(
        mut item: ItemFn,
        root: PatternRoot,
        signs: NegativeLiteralSpans,
    ) -> Result<Self, SyntaxError> {
        Self::from_item_with_sort_parser(
            &mut item,
            parse_readable_sort,
            root,
            signs,
            false,
            ClauseForm::Plain,
        )
    }

    #[expect(
        clippy::too_many_lines,
        reason = "The signature, subject, result or single body, and helpers are validated in one ordered pass."
    )]
    fn from_item_with_sort_parser(
        item: &mut ItemFn,
        sort_parser: fn(Type) -> Result<TermSort, SyntaxError>,
        root: PatternRoot,
        signs: NegativeLiteralSpans,
        result_wildcards: bool,
        form: ClauseForm,
    ) -> Result<Self, SyntaxError> {
        validate_signature_features(item)?;
        // `k::bits!` templates are sugar: the item is parsed as its long form.
        let hidden = super::bits::desugar(item, form != ClauseForm::Context)?;
        let _hidden = super::bits::GeneratedBinders::allow(hidden.unwrap_or_default());
        let function_context = parse_function_context(item, form == ClauseForm::Equation)?;
        let binders = parse_rule_binders(item, usize::from(function_context.is_some()))?;
        let subject_index = item
            .sig
            .inputs
            .len()
            .saturating_sub(1 + usize::from(function_context.is_some()));
        let argument = item.sig.inputs.iter().nth(subject_index).ok_or_else(|| {
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
        let (pattern, subject_tree) = parse_rule_pattern((*argument.pat).clone(), root, signs)?;
        // A unit-returning `#[k::rule]` fn is a single-body rule (KF-011):
        // its subject's `k::rewrite!` islands say what changes.
        let rewrite = pattern
            .nodes()
            .iter()
            .find(|node| matches!(node, TermNode::Rewrite { .. }));
        let returns_unit = match &item.sig.output {
            ReturnType::Default => true,
            ReturnType::Type(_, ty) => crate::state_rule::is_unit_type(ty),
        };
        if form == ClauseForm::Context {
            crate::state_rule::check_context_shape(
                item,
                returns_unit,
                pattern
                    .nodes()
                    .iter()
                    .filter(|node| matches!(node, TermNode::Rewrite { .. }))
                    .map(|node| Ok(node.range()?.first()))
                    .collect::<Result<Vec<_>, SyntaxError>>()?
                    .as_slice(),
            )?;
        }
        // A fn with statements and no rewrite meant to return a result.
        let single_body = form == ClauseForm::Transition
            && returns_unit
            && (item.block.stmts.is_empty() || rewrite.is_some());
        let single_body = single_body || form == ClauseForm::Context;
        let mut unchanged = None;
        match (single_body, rewrite) {
            (false, Some(rewrite)) => {
                return Err(crate::term::local_rewrite_error(
                    crate::state_rule::REWRITE_WITH_RESULT.to_owned(),
                    rewrite.range()?.first(),
                ));
            }
            (true, None) if form == ClauseForm::Context => {}
            (true, None) => {
                unchanged = Some(crate::term::local_rewrite_error(
                    crate::state_rule::SINGLE_BODY_WITHOUT_REWRITE.to_owned(),
                    item.sig.ident.span(),
                ));
            }
            (true, Some(_)) => {
                crate::term::check_rewrite_right_bindings(&subject_tree, pattern.bindings())?;
            }
            (false, None) => {}
        }
        let parameter_sort = sort_parser((*argument.ty).clone())?;
        let mut function_context = function_context;
        if let Some(context) = &mut function_context {
            validate_context_binder_list(item, &binders, pattern.bindings(), context)?;
            let declared = binders
                .iter()
                .map(|binder| (binder.name.clone(), binder.term_sort.clone()))
                .collect::<Vec<_>>();
            context.attach_sorts(pattern.bindings(), &declared)?;
        } else {
            validate_binder_list(&binders, pattern.bindings())?;
        }

        let (result_sort, result) = if single_body {
            if !item.block.stmts.is_empty() {
                return Err(crate::term::local_rewrite_error(
                    crate::state_rule::SINGLE_BODY_BODY.to_owned(),
                    item.block.span(),
                ));
            }
            (None, None)
        } else {
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
            (Some(result_sort), Some(result))
        };
        let requires = take_requires_helper(&mut item.attrs)?;
        let existentials = RuleExistentials::take(&mut item.attrs)?;
        if single_body && let Some(helper) = existentials.attributes().first() {
            return Err(crate::term::local_rewrite_error(
                if form == ClauseForm::Context {
                    crate::state_rule::CONTEXT_BINDERS
                } else {
                    crate::state_rule::SINGLE_BODY_BINDERS
                }
                .to_owned(),
                helper.path().span(),
            ));
        }
        // A readable clause checks its existentials against every cell it
        // writes (`RuleClause::check_existentials`); its item has only the head.
        if root == PatternRoot::Subject {
            existentials.check_shadowing(pattern.bindings())?;
            existentials.check_scope(
                requires.as_ref().map(RuleCondition::term),
                &result.iter().collect::<Vec<_>>(),
            )?;
        }

        Self {
            item: item.clone(),
            binders,
            parameter: RuleParameter {
                pattern,
                term_sort: parameter_sort,
                pattern_key: None,
                type_key: None,
            },
            result_sort,
            result,
            subject_tree,
            requires,
            existentials,
            unbound: Vec::new(),
            function_context,
            declaration_key: None,
            result_type_key: None,
            anchors: Vec::new(),
            full_anchors: Vec::new(),
            unchanged,
        }
        .keyed()
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
        let Some(result) = &self.result else {
            return Ok(self);
        };
        if let Some(wildcard) = unbound.wildcard() {
            let mut ranges = Vec::new();
            result.tree().wildcard_ranges_preorder(&mut ranges);
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
            if !super::existentials::references(result, name) {
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

    /// Returns the equation's read-only configuration context (KF-025).
    #[must_use]
    pub const fn function_context(&self) -> Option<&FunctionContext> {
        self.function_context.as_ref()
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

    /// Returns the rule's result sort, or `None` for a single-body rule
    /// (KF-011).
    #[must_use]
    pub const fn result_sort(&self) -> Option<&TermSort> {
        self.result_sort.as_ref()
    }

    /// Returns the validated right-hand term payload, or `None` for a
    /// single-body rule (KF-011).
    #[must_use]
    pub const fn result(&self) -> Option<&TermExpression> {
        self.result.as_ref()
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

    /// Subject and function-context bindings followed by the existentials:
    /// every name the result and the ensures condition may reference.
    #[must_use]
    pub fn result_bindings(&self) -> Vec<syn::Ident> {
        let mut bindings = self.condition_bindings();
        bindings.extend(self.existentials.names());
        bindings.extend(self.unbound.iter().cloned());
        bindings
    }

    /// The subject's bindings followed by the function context's new ones:
    /// every name the requires condition may reference.
    #[must_use]
    pub fn condition_bindings(&self) -> Vec<syn::Ident> {
        let mut bindings = self.parameter.pattern.bindings().to_vec();
        if let Some(context) = &self.function_context {
            for binding in context.bindings() {
                if !bindings.contains(binding.name()) {
                    bindings.push(binding.name().clone());
                }
            }
        }
        bindings
    }

    /// The key of the rule's name, its declaration.
    #[must_use]
    pub const fn declaration_key(&self) -> Option<&ProvenanceKey> {
        self.declaration_key.as_ref()
    }

    /// The key of the result type; the result term's key is its payload key.
    #[must_use]
    pub const fn result_type_key(&self) -> Option<&ProvenanceKey> {
        self.result_type_key.as_ref()
    }

    /// Keys the rule as a sentence of its own. The catalog view is a prefix
    /// of the full view, so one pass keys both: every node holds the same key
    /// in each view, and the catalog's anchors are those recorded before the
    /// subject's nodes.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        self.clear_keys();
        self.allocate_catalog_keys(&mut keys, ItemView::Rule)?;
        self.anchors = keys.anchors().to_vec();
        self.allocate_term_keys(&mut keys, ItemView::Rule)?;
        self.full_anchors = keys.into_anchors();
        Ok(self)
    }

    /// Keys the rule as the item of a readable clause, with the clause's
    /// allocator: the declaration under `declaration` (`RuleDeclaration`, or
    /// `ClaimDeclaration` for a claim clause), then, in the rule's own order,
    /// every node of the item that the clause anchors (see
    /// [`ItemView::Clause`]).
    pub(super) fn allocate_clause_keys(
        &mut self,
        keys: &mut KeyAllocator,
        declaration: ProvenanceRole,
        subject: bool,
    ) -> Result<(), SyntaxError> {
        let view = ItemView::Clause {
            declaration,
            subject,
        };
        self.clear_keys();
        self.allocate_catalog_keys(keys, view)?;
        self.allocate_term_keys(keys, view)
    }

    /// Forgets every key of the rule and the anchors of its keying, before a
    /// sentence's pass keys it. A readable clause's pass leaves the nodes it
    /// does not anchor without keys (the result term and a placeholder
    /// subject), and the rule without anchors of its own: the clause's are
    /// the anchors of its keys.
    pub(crate) fn clear_keys(&mut self) {
        self.anchors.clear();
        self.full_anchors.clear();
        self.declaration_key = None;
        self.result_type_key = None;
        self.parameter.type_key = None;
        self.parameter.pattern_key = None;
        self.parameter.pattern.clear_keys();
        for binder in &mut self.binders {
            binder.parameter_key = None;
            binder.sort_key = None;
        }
        if let Some(result) = &mut self.result {
            result.clear_keys();
        }
        if let Some(requires) = &mut self.requires {
            requires.clear_keys();
        }
        self.existentials.clear_keys();
        if let Some(context) = &mut self.function_context {
            context.clear_keys();
        }
    }

    /// Returns canonical rule node anchors and nested path anchors: the
    /// catalog view of the rule's keying.
    ///
    /// # Errors
    ///
    /// None: the rule was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    /// Keys the declaration, pattern, and types, the result, each binder's
    /// parameter and type, then the subject's and the result's paths.
    fn allocate_catalog_keys(
        &mut self,
        keys: &mut KeyAllocator,
        view: ItemView,
    ) -> Result<(), SyntaxError> {
        self.declaration_key = Some(keys.key(
            view.declaration(),
            TokenRange::for_tokens(&self.item.sig.ident)?,
        )?);
        let parameter = &mut self.parameter;
        if view.keys_subject() {
            parameter.pattern_key =
                Some(keys.key(ProvenanceRole::RulePattern, parameter.pattern.range()?)?);
        }
        parameter.type_key = Some(keys.key(
            ProvenanceRole::RuleType,
            TokenRange::for_tokens(parameter.term_sort.ty())?,
        )?);
        if let (Some(result_sort), Some(result)) = (&self.result_sort, &mut self.result) {
            self.result_type_key = Some(keys.key(
                ProvenanceRole::RuleResultType,
                TokenRange::for_tokens(result_sort.ty())?,
            )?);
            if view == ItemView::Rule {
                result.allocate_payload_key(keys, ProvenanceRole::RuleResult)?;
            }
        }
        for binder in &mut self.binders {
            binder.parameter_key = Some(keys.key(
                ProvenanceRole::RuleBindingParameter,
                TokenRange::for_tokens(&binder.parameter)?,
            )?);
            binder.sort_key = Some(keys.key(
                ProvenanceRole::RuleBindingType,
                TokenRange::for_tokens(binder.term_sort.sort())?,
            )?);
        }
        if view.keys_subject() {
            self.parameter
                .pattern
                .allocate_path_keys(keys, ProvenanceRole::RuleLeftPath)?;
        }
        if view == ItemView::Rule
            && let Some(result) = &mut self.result
        {
            result.allocate_symbol_keys(keys, ProvenanceRole::RuleRightPath)?;
        }
        Ok(())
    }

    /// Returns the compact catalog plus typed subject/result term-node
    /// anchors required by protocol v6: the full view of the rule's keying.
    ///
    /// # Errors
    ///
    /// None: the rule was keyed when it was parsed.
    pub fn full_provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.full_anchors.clone())
    }

    /// Keys the subject's nodes, record field names and wildcards, the
    /// function context, the result's, the conditions, then the islands of
    /// every term in expansion order.
    fn allocate_term_keys(
        &mut self,
        keys: &mut KeyAllocator,
        view: ItemView,
    ) -> Result<(), SyntaxError> {
        if view.keys_subject() {
            let (nodes, term_keys) = self.parameter.pattern.keying();
            allocate_term_node_keys(
                keys,
                nodes,
                term_keys,
                ProvenanceRole::RuleLeftApplicationHead,
                ProvenanceRole::RuleLeftReference,
                ProvenanceRole::RuleLeftLiteral,
            )?;
            allocate_record_field_keys(
                keys,
                &self.subject_tree,
                term_keys,
                ProvenanceRole::RuleLeftRecordFieldName,
            )?;
            allocate_wildcard_keys(
                keys,
                &self.subject_tree,
                term_keys,
                ProvenanceRole::RuleLeftWildcard,
            )?;
        }
        // A function context's cells continue the subject's left-hand
        // ordinals: they are expanded right after it (KF-025).
        if let Some(context) = &mut self.function_context {
            context.allocate_keys(keys)?;
        }
        if view == ItemView::Rule
            && let Some(result) = &mut self.result
        {
            let (nodes, tree, term_keys) = result.keying();
            allocate_term_node_keys(
                keys,
                nodes,
                term_keys,
                ProvenanceRole::RuleRightApplicationHead,
                ProvenanceRole::RuleRightReference,
                ProvenanceRole::RuleRightLiteral,
            )?;
            allocate_record_field_keys(
                keys,
                tree,
                term_keys,
                ProvenanceRole::RuleRightRecordFieldName,
            )?;
            allocate_wildcard_keys(keys, tree, term_keys, ProvenanceRole::RuleRightWildcard)?;
        }
        if let Some(requires) = &mut self.requires {
            requires.allocate_keys(keys)?;
        }
        self.existentials.allocate_keys(keys)?;
        if view == ItemView::Rule {
            self.allocate_island_keys(keys)?;
        }
        Ok(())
    }

    /// The `#[k::requires]` condition, for a pass that keys it.
    pub(super) const fn requires_mut(&mut self) -> Option<&mut RuleCondition> {
        self.requires.as_mut()
    }

    /// The `#[k::exists]`, `#[k::fresh]` and `#[k::ensures]` helpers, for a
    /// pass that keys them.
    pub(super) const fn existentials_mut(&mut self) -> &mut RuleExistentials {
        &mut self.existentials
    }

    /// Keys the islands of the subject, the function context, the result,
    /// the condition, then the ensures condition, which is the order they
    /// expand in.
    fn allocate_island_keys(&mut self, keys: &mut KeyAllocator) -> Result<(), SyntaxError> {
        // Each term's nodes with its keys, in expansion order; the subject,
        // the function context, and the result come before the conditions.
        let mut sides = vec![self.parameter.pattern.keying()];
        if let Some(context) = &mut self.function_context {
            sides.extend(context.terms_mut().into_iter().map(|term| {
                let (nodes, _, term_keys) = term.keying();
                (nodes, term_keys)
            }));
        }
        if let Some(result) = &mut self.result {
            let (nodes, _, term_keys) = result.keying();
            sides.push((nodes, term_keys));
        }
        let before_conditions = sides.len();
        if let Some(requires) = &mut self.requires {
            let (nodes, _, term_keys) = requires.term_mut().keying();
            sides.push((nodes, term_keys));
        }
        if let Some(ensures) = self.existentials.ensures_mut() {
            let (nodes, _, term_keys) = ensures.keying();
            sides.push((nodes, term_keys));
        }
        for (nodes, term_keys) in &mut sides {
            allocate_lexeme_keys(keys, nodes, term_keys)?;
        }
        // `name @ ..` and `A | B` occur in the subject, the function context,
        // and in `k::matches!` patterns; with `k::matches!` shells and pattern
        // wildcards (KF-031) they are numbered in expansion order: the
        // subject, the function context, the result, the condition, then the
        // ensures condition.
        // Builtin `Id` and `Bytes` literals, each kind numbered in one
        // sequence in expansion order (the claim-only islands never reach a
        // rule's descriptor: expansion rejects them).
        crate::state_rule::allocate_claim_node_keys(
            keys,
            sides
                .iter_mut()
                .map(|(nodes, term_keys)| (*nodes, &mut **term_keys)),
        )?;
        for (nodes, term_keys) in &mut sides {
            crate::term::allocate_pattern_as_keys(keys, nodes, term_keys)?;
        }
        for (nodes, term_keys) in &mut sides {
            crate::term::allocate_pattern_or_keys(keys, nodes, term_keys)?;
        }
        for (nodes, term_keys) in &mut sides {
            crate::term::allocate_matches_keys(keys, nodes, term_keys)?;
        }
        for (nodes, term_keys) in &mut sides {
            crate::term::allocate_let_keys(keys, nodes, term_keys)?;
        }
        for (nodes, term_keys) in &mut sides {
            crate::term::allocate_ml_binder_keys(keys, nodes, term_keys)?;
        }
        let (unconditioned, conditions) = sides.split_at_mut(before_conditions);
        for (nodes, term_keys) in unconditioned.iter_mut() {
            allocate_sort_test_keys(keys, nodes, term_keys)?;
        }
        // `k::rewrite!` shells and sides of a single-body rule (KF-011).
        let (subject_nodes, subject_keys) = &mut unconditioned[0];
        crate::term::allocate_rewrite_keys(keys, subject_nodes, subject_keys)?;
        for (nodes, term_keys) in conditions.iter_mut() {
            allocate_sort_test_keys(keys, nodes, term_keys)?;
        }
        for (nodes, term_keys) in &mut sides {
            crate::term::allocate_application_instance_keys(keys, nodes, term_keys)?;
        }
        Ok(())
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
    ///
    /// # Panics
    ///
    /// Never: parsing keys every type, sort and path a candidate names.
    pub fn reference_candidates(&self) -> Result<Vec<ReferenceCandidate>, SyntaxError> {
        let keyed = "a rule is keyed when it is parsed";
        let mut candidates = vec![ReferenceCandidate {
            key: self.parameter.type_key().expect(keyed).clone(),
            path: self.parameter.term_sort.sort().clone(),
            kind: (),
        }];
        if let Some(result_sort) = &self.result_sort {
            candidates.push(ReferenceCandidate {
                key: self.result_type_key().expect(keyed).clone(),
                path: result_sort.sort().clone(),
                kind: (),
            });
        }

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
                        | TermNode::Or(_)
                        | TermNode::Matches(_)
                        | TermNode::MatchesWildcard(_)
                        | TermNode::Let { .. }
                        | TermNode::Closure { .. }
                        | TermNode::LetWildcard(_)
                        | TermNode::Rewrite { .. } => continue,
                    };
                    push_candidate(&mut candidates, ProvenanceRole::RuleLeftPath, ordinal, path)?;
                    ordinal += 1;
                }
            }
            RulePattern::TermMacro { term, bindings, .. } => {
                push_symbol_candidates(&mut candidates, term, bindings);
            }
        }

        if let Some(result) = &self.result {
            push_symbol_candidates(&mut candidates, result, &self.result_bindings());
        }
        for binder in &self.binders {
            candidates.push(ReferenceCandidate {
                key: binder.sort_key().expect(keyed).clone(),
                path: binder.term_sort.sort().clone(),
                kind: (),
            });
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
            self.parameter.pattern.keys(),
            self.parameter.pattern.bindings(),
        );
        let result_bindings = self.result_bindings();
        if let Some(result) = &self.result {
            push_term_reference_candidates(
                &mut candidates,
                result.nodes(),
                result.keys(),
                &result_bindings,
            );
        }
        if let Some(requires) = &self.requires {
            candidates.extend(requires.reference_candidates(self.parameter.pattern.bindings())?);
        }
        candidates.extend(self.existentials.reference_candidates(&result_bindings)?);
        Ok(candidates)
    }
}

/// Pushes a candidate for each path of `term` that is not a bare reference
/// to one of `bindings`, keyed as the rule keyed the path.
fn push_symbol_candidates(
    candidates: &mut Vec<ReferenceCandidate>,
    term: &TermExpression,
    bindings: &[Ident],
) {
    for (index, symbol) in term.symbols().iter().enumerate() {
        if is_bound_reference(symbol, bindings) {
            continue;
        }
        let key = term
            .keys()
            .symbol(index)
            .expect("a rule keys every path of its subject and result");
        candidates.push(ReferenceCandidate {
            key: key.clone(),
            path: symbol.path().clone(),
            kind: (),
        });
    }
}

/// The fn item a clause of a `k::rules!`, `k::claims!` or `k::equations!`
/// block is read as: `#(#retained)* #visibility fn #name(subject: #ty) -> #ty
/// { result }`. The subject and the result are put in place after the item
/// parses, so they keep their authored tokens: a top-level `A | B`, which a
/// parameter takes only in parentheses, and a term that is no Rust pattern
/// or expression ([`crate::term::parse_term_pattern`],
/// [`crate::term::parse_term_expression`]), which the position table judges
/// where it stands.
pub(super) fn clause_item(
    retained: &[syn::Attribute],
    visibility: &TokenStream,
    name: &Ident,
    ty: &dyn quote::ToTokens,
    subject: Pat,
    result: Expr,
) -> syn::Result<ItemFn> {
    let mut item: ItemFn = syn::parse2(quote::quote! {
        #(#retained)*
        #visibility fn #name(_: #ty) -> #ty { true }
    })?;
    if let Some(FnArg::Typed(typed)) = item.sig.inputs.first_mut() {
        *typed.pat = subject;
    }
    item.block.stmts = vec![Stmt::Expr(result, None)];
    Ok(item)
}

impl KrsSyntax for RuleItem {
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        let signs = NegativeLiteralSpans::of_fn_parameters(tokens.clone());
        Self::from_item_with_signs(
            crate::term::parse_fn_item(tokens)?,
            signs,
            ClauseForm::Transition,
        )
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
            "K rules never quantify over sorts; write one equation per instance with a turbofish, such as `Choose::<k::builtin::Int> { .. }`",
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

/// Parses an equation's final function-context parameter (KF-025), or
/// rejects one on another sentence.
///
/// A final `k::cells! { .. }` parameter after a subject is a function context;
/// on an equation, so is any final parameter that follows a subject pattern
/// (a parameter that is not a plain binder).
fn parse_function_context(
    item: &ItemFn,
    allow_context: bool,
) -> Result<Option<FunctionContext>, SyntaxError> {
    let inputs = item.sig.inputs.iter().collect::<Vec<_>>();
    let [.., previous, last] = inputs.as_slice() else {
        return Ok(None);
    };
    let follows_subject =
        matches!(previous, FnArg::Typed(previous) if !matches!(&*previous.pat, Pat::Ident(_)));
    if is_cells_parameter(last) {
        if !allow_context {
            return Err(SyntaxError::new(
                SyntaxErrorKind::InvalidFunctionContext {
                    reason: FUNCTION_CONTEXT_ONLY_ON_EQUATIONS.to_owned(),
                },
                last.span(),
            ));
        }
        return FunctionContext::parse(last).map(Some);
    }
    if allow_context && follows_subject {
        return FunctionContext::parse(last).map(Some);
    }
    Ok(None)
}

/// Parses the typed binder parameters before the subject (KF-009, X5), and
/// before the function context when there is one (`trailing` is then 1).
fn parse_rule_binders(item: &ItemFn, trailing: usize) -> Result<Vec<RuleBinder>, SyntaxError> {
    let mut binders = Vec::<RuleBinder>::new();
    let count = item.sig.inputs.len().saturating_sub(1 + trailing);
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
        let term_sort = parse_term_or_readable_sort(authored)?;
        binders.push(RuleBinder {
            name: pattern.ident.clone(),
            term_sort,
            parameter: argument.clone(),
            parameter_key: None,
            sort_key: None,
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

/// Checks the binder-list contract of a sentence with a function context
/// (X5.1): mandatory and exhaustive, the subject's binders then the context's
/// new term binders, each in first-occurrence order.
fn validate_context_binder_list(
    item: &ItemFn,
    binders: &[RuleBinder],
    subject: &[Ident],
    context: &FunctionContext,
) -> Result<(), SyntaxError> {
    let mut expected = subject.iter().map(Ident::unraw).collect::<Vec<_>>();
    for binding in context.term_bindings() {
        let binding = binding.unraw();
        if !expected.contains(&binding) {
            expected.push(binding);
        }
    }
    for binder in binders {
        if !expected.contains(&binder.name.unraw()) {
            return Err(binder_error(
                format!(
                    "binder `{}` is declared but does not occur in the subject or function context",
                    binder.name.unraw()
                ),
                binder.name.span(),
            ));
        }
    }
    let mismatch = binders
        .iter()
        .zip(&expected)
        .find(|(binder, expected)| binder.name.unraw() != **expected)
        .map(|(binder, _)| binder.name.span());
    if binders.len() != expected.len() || mismatch.is_some() {
        let listed = expected
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(", ");
        return Err(binder_error(
            format!(
                "{BINDER_LIST_CONTRACT}; a sentence with a function context declares every binder, here `{listed}`"
            ),
            mismatch
                .or_else(|| binders.first().map(|binder| binder.name.span()))
                .unwrap_or_else(|| item.sig.ident.span()),
        ));
    }
    Ok(())
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
    // A body with `let` statements is a term block (K's `#let`, KF-032).
    // A desugar result with wildcards admits no let block.
    if !wildcards
        && item
            .block
            .stmts
            .iter()
            .any(|statement| matches!(statement, Stmt::Local(_)))
    {
        return TermExpression::from_expression(Expr::Block(syn::ExprBlock {
            attrs: Vec::new(),
            label: None,
            block: (*item.block).clone(),
        }));
    }
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
        // A compiler-owned island is a whole result term, as it is anywhere
        // below the root.
        Expr::Macro(expression_macro)
            if crate::term::is_island_macro(&expression_macro.mac.path) =>
        {
            TermExpression::from_expression(expression.clone())
        }
        // A `k::bits!(value, "..")` test is a `Bool` term.
        Expr::Macro(expression_macro) if crate::rule::is_bits_macro(&expression_macro.mac.path) => {
            term(expression.clone())
        }
        Expr::Macro(expression_macro) => {
            if !is_term_macro(&expression_macro.mac.path) {
                return Err(unexpected_macro(&expression_macro.mac.path));
            }
            term(
                crate::term::parse_term_expression.parse2(crate::parse::strip_trailing_comma(
                    expression_macro.mac.tokens.clone(),
                ))?,
            )
        }
        expression => term(expression.clone()),
    }
}

#[cfg(test)]
impl RuleItem {
    /// Records the rule's keyed nodes: those of the full view, of which the
    /// catalog view is a prefix, or, in a readable clause, those the clause
    /// keys (its result term and a placeholder subject hold no keys).
    pub(crate) fn keyed_nodes(
        &self,
        nodes: &mut crate::keyed_nodes::KeyedNodes,
    ) -> Result<(), SyntaxError> {
        nodes.push_tokens(self.declaration_key.as_ref(), &self.item.sig.ident)?;
        let parameter = &self.parameter;
        // A readable clause's placeholder subject has no authored tokens and
        // no keys.
        if let Some(key) = &parameter.pattern_key {
            nodes.push(Some(key), parameter.pattern.range()?);
        }
        parameter.pattern.keyed_nodes(nodes, &self.subject_tree)?;
        nodes.push_tokens(parameter.type_key.as_ref(), parameter.term_sort.ty())?;
        if let Some(result_sort) = &self.result_sort {
            nodes.push_tokens(self.result_type_key.as_ref(), result_sort.ty())?;
        }
        for binder in &self.binders {
            nodes.push_tokens(binder.parameter_key.as_ref(), &binder.parameter)?;
            nodes.push_tokens(binder.sort_key.as_ref(), binder.term_sort.sort())?;
        }
        if let Some(context) = &self.function_context {
            context.keyed_nodes(nodes)?;
        }
        if let Some(requires) = &self.requires {
            requires.term().keyed_nodes(nodes)?;
        }
        self.existentials.keyed_nodes(nodes)?;
        if let Some(result) = &self.result {
            result.keyed_nodes(nodes)?;
        }
        Ok(())
    }
}
