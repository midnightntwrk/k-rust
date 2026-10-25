use krs_ir::ProvenanceKey;
use proc_macro2::TokenStream;
use syn::spanned::Spanned;
use syn::{
    Attribute, Expr, FnArg, Ident, ItemFn, Macro, Meta, Pat, PatMacro, Path, ReturnType, Stmt, Type,
};

use crate::ReferenceCandidate;
use crate::attribute::{ClaimBinder, ExistsAttribute};
use crate::parse::{
    KeyAllocator, KrsSyntax, unsupported_rule_pattern as pattern_error,
    unsupported_rule_signature as signature_error,
};
use crate::path::{is_plain_path, unqualified_path_ident as bare_ident};
use crate::provenance::RuleSide;
use crate::rule::{BINDER_LIST_CONTRACT, RuleCondition, RuleExistentials, take_requires_helper};
use crate::state_macro::StatePosition;
use crate::term::{IslandKeys, TermKeys, TermVisit};
use crate::term::{
    allocate_lexeme_keys, allocate_record_field_keys, allocate_sort_test_keys, local_rewrite_error,
};
use crate::term_sort::{TermSort, parse_term_or_readable_sort};
use crate::{
    CellsExpression, MapBody, MapExpression, ProvenanceAnchor, ProvenanceRole, StateMacroRemainder,
    StateTerm, SyntaxError, SyntaxErrorKind, TermExpression, TermNode, TokenRange,
    parse_cells_expression, parse_cells_pattern,
};

/// Semantic class of one binding introduced by a configuration-rule subject.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StateRuleBindingKind {
    /// An object-language term with an explicit authored Rust sort.
    Term,
    /// A named tail of a K sequence.
    KSequenceFrame,
    /// A named associative-map remainder.
    MapFrame,
    /// A named remainder of the complete fixed configuration.
    ConfigurationFrame,
    /// A named rest of a collection cell's instances (KF-023).
    InstancesFrame,
}

/// One typed or structurally classified configuration-rule binding.
#[derive(Clone, Debug)]
pub struct StateRuleBinding {
    name: Ident,
    kind: StateRuleBindingKind,
    sort: Option<TermSort>,
    sort_key: Option<ProvenanceKey>,
    universal_key: Option<ProvenanceKey>,
    binder_name_key: Option<ProvenanceKey>,
    binder_sort_key: Option<ProvenanceKey>,
}

impl StateRuleBinding {
    /// The key of the explicit sort path, as the binder list types it.
    #[must_use]
    pub const fn sort_key(&self) -> Option<&ProvenanceKey> {
        self.sort_key.as_ref()
    }

    /// The key of a claim's term binding as a universal binder, given by
    /// the claim.
    #[must_use]
    pub const fn universal_key(&self) -> Option<&ProvenanceKey> {
        self.universal_key.as_ref()
    }

    /// The key of a claim's term binding's name as a claim binder name,
    /// given by the claim.
    #[must_use]
    pub const fn binder_name_key(&self) -> Option<&ProvenanceKey> {
        self.binder_name_key.as_ref()
    }

    /// The key of a claim's term binding's sort as a claim binder sort,
    /// given by the claim.
    #[must_use]
    pub const fn binder_sort_key(&self) -> Option<&ProvenanceKey> {
        self.binder_sort_key.as_ref()
    }

    /// Forgets the binding's keys, before a sentence's pass keys it.
    fn clear_keys(&mut self) {
        self.sort_key = None;
        self.universal_key = None;
        self.binder_name_key = None;
        self.binder_sort_key = None;
    }

    /// Returns the authored binding name.
    #[must_use]
    pub const fn name(&self) -> &Ident {
        &self.name
    }

    /// Returns the binding's exact semantic class.
    #[must_use]
    pub const fn kind(&self) -> StateRuleBindingKind {
        self.kind
    }

    /// Returns the explicit term sort, or `None` for structural frames.
    #[must_use]
    pub const fn term_sort(&self) -> Option<&TermSort> {
        self.sort.as_ref()
    }
}

/// Semantic class of one rustc-resolvable path in a configuration rule.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StateRuleReferenceKind {
    /// Explicit sort path of a typed term binding.
    BindingSort,
    /// Subject or result fixed-configuration type.
    Configuration,
    /// `Cell` or `KCell` wrapper path.
    CellWrapper,
    /// Constructor or builtin operation application head.
    ApplicationHead,
    /// Bare nonbinding path, normally a qualified unit constructor.
    Reference,
}

/// One complete simultaneous fixed-configuration rule.
#[derive(Clone, Debug)]
pub struct StateRuleItem {
    item: ItemFn,
    subject_macro: PatMacro,
    subject_type: Path,
    subject: CellsExpression,
    /// The result, absent exactly for a single-body rule (KF-011).
    result: Option<StateRuleResult>,
    bindings: Vec<StateRuleBinding>,
    requires: Option<RuleCondition>,
    existentials: RuleExistentials,
    declaration_key: Option<ProvenanceKey>,
    pattern_key: Option<ProvenanceKey>,
    type_key: Option<ProvenanceKey>,
    /// The anchors of the rule's own keying.
    anchors: Vec<ProvenanceAnchor>,
}

/// The `-> Machine { cells!{..} }` result of a two-sided configuration rule.
#[derive(Clone, Debug)]
struct StateRuleResult {
    result_macro: Macro,
    result_type: Path,
    result: CellsExpression,
    key: Option<ProvenanceKey>,
    type_key: Option<ProvenanceKey>,
}

/// Object-language Boolean postcondition consumed only by a claim.
#[derive(Clone, Debug)]
pub struct ClaimEnsures {
    term: TermExpression,
}

impl ClaimEnsures {
    /// Returns the structured postcondition.
    #[must_use]
    pub const fn term(&self) -> &TermExpression {
        &self.term
    }

    /// Keys the postcondition's payload and paths, then its application
    /// head, reference, and literal nodes and its record field names.
    fn allocate_keys(&mut self, keys: &mut KeyAllocator) -> Result<(), SyntaxError> {
        self.term.allocate_keys(
            keys,
            ProvenanceRole::ClaimEnsures,
            ProvenanceRole::ClaimEnsuresPath,
        )?;
        self.term.allocate_node_keys(
            keys,
            ProvenanceRole::ClaimEnsuresApplicationHead,
            ProvenanceRole::ClaimEnsuresReference,
            ProvenanceRole::ClaimEnsuresLiteral,
            ProvenanceRole::ClaimEnsuresRecordFieldName,
        )
    }
}

/// One rustc-resolvable claim-only sort occurrence.
#[derive(Clone, Debug)]
pub struct ClaimSortCandidate {
    key: ProvenanceKey,
    path: Path,
}

impl ClaimSortCandidate {
    /// Returns its parser-owned key.
    #[must_use]
    pub const fn key(&self) -> &ProvenanceKey {
        &self.key
    }
    /// Returns the exact sort path.
    #[must_use]
    pub const fn path(&self) -> &Path {
        &self.path
    }
}

/// A whole-configuration claim with scoped existential metadata.
#[derive(Clone, Debug)]
pub struct StateClaimItem {
    rule: StateRuleItem,
    exists: Option<ExistsAttribute>,
    ensures: Option<ClaimEnsures>,
    /// The anchors of the claim's keying.
    anchors: Vec<ProvenanceAnchor>,
}

impl StateClaimItem {
    /// Parses the frozen relational claim body and consumes its helper attributes.
    ///
    /// # Errors
    ///
    /// Rejects malformed helper attributes, invalid configuration-rule shape,
    /// or an existential which shadows a subject binding.
    pub fn from_item(mut item: ItemFn) -> Result<Self, SyntaxError> {
        let exists = take_exists_helper(&mut item.attrs)?;
        let ensures = take_ensures_helper(&mut item.attrs)?;
        let rule = StateRuleItem::from_item_with(item, StateRuleForm::Claim)?;
        let universal = rule
            .bindings
            .iter()
            .map(|binding| binding.name.to_string())
            .collect::<std::collections::BTreeSet<_>>();
        for binder in exists
            .as_ref()
            .into_iter()
            .flat_map(ExistsAttribute::binders)
        {
            if universal.contains(&binder.name().to_string()) {
                return Err(signature_error(
                    "an existential cannot shadow a universal or structural binding",
                    binder.name().span(),
                ));
            }
        }
        Self {
            rule,
            exists,
            ensures,
            anchors: Vec::new(),
        }
        .keyed()
    }

    /// Keys the claim as a sentence of its own and stores its anchors. The
    /// claim keys its rule's nodes with the rule's own walk, except the
    /// rule's declaration, which it keys as the claim's, and its claim-only
    /// literals, which it numbers with its ensures condition's.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        self.clear_keys();
        self.allocate_keys(&mut keys)?;
        self.anchors = keys.into_anchors();
        Ok(self)
    }

    /// Forgets every key of the claim, before its pass keys it.
    fn clear_keys(&mut self) {
        self.rule.clear_keys();
        for binder in self
            .exists
            .iter_mut()
            .flat_map(ExistsAttribute::binders_mut)
        {
            binder.clear_keys();
        }
        if let Some(ensures) = &mut self.ensures {
            ensures.term.clear_keys();
        }
    }

    /// Keys the rule's nodes but its declaration and claim-only literals,
    /// the declaration as the claim's, each universal term binding as a
    /// binder with its name and sort, each existential binder, then their
    /// names and sorts, which number on after the universal binders', the
    /// ensures condition, the claim-only literals of the cells, the
    /// condition and the ensures condition, and the ensures condition's
    /// islands, which number on after the rule's.
    fn allocate_keys(&mut self, keys: &mut KeyAllocator) -> Result<(), SyntaxError> {
        self.rule.allocate_body_keys(keys)?;
        self.rule.declaration_key = Some(keys.key(
            ProvenanceRole::ClaimDeclaration,
            TokenRange::for_tokens(&self.rule.item.sig.ident)?,
        )?);
        for binding in &mut self.rule.bindings {
            if binding.kind == StateRuleBindingKind::Term {
                let name = TokenRange::for_tokens(&binding.name)?;
                binding.universal_key = Some(keys.key(ProvenanceRole::ClaimUniversalBinder, name)?);
                binding.binder_name_key = Some(keys.key(ProvenanceRole::ClaimBinderName, name)?);
                let Some(sort) = binding.term_sort() else {
                    return Err(signature_error(
                        "term claim binding is missing its sort",
                        binding.name.span(),
                    ));
                };
                binding.binder_sort_key = Some(keys.key(
                    ProvenanceRole::ClaimBinderSort,
                    TokenRange::for_tokens(sort.sort())?,
                )?);
            }
        }
        if let Some(exists) = &mut self.exists {
            for binder in exists.binders_mut() {
                binder.allocate_binder_key(keys, ProvenanceRole::ClaimExistentialBinder)?;
            }
            for binder in exists.binders_mut() {
                binder.allocate_name_and_sort_keys(
                    keys,
                    ProvenanceRole::ClaimBinderName,
                    ProvenanceRole::ClaimBinderSort,
                )?;
            }
        }
        if let Some(ensures) = &mut self.ensures {
            ensures.allocate_keys(keys)?;
        }
        self.rule.visit_terms(&mut |nodes, term_keys| {
            allocate_claim_node_keys(keys, [(nodes, term_keys)])
        })?;
        if let Some(ensures) = &mut self.ensures {
            let (nodes, _, term_keys) = ensures.term.keying();
            allocate_claim_node_keys(keys, [(nodes, &mut *term_keys)])?;
            allocate_claim_ensures_keys(keys, nodes, term_keys)?;
        }
        Ok(())
    }
    /// Returns the shared configuration rewrite parser result.
    #[must_use]
    pub const fn rule(&self) -> &StateRuleItem {
        &self.rule
    }
    /// Returns existential declarations in source order.
    #[must_use]
    pub fn existentials(&self) -> &[ClaimBinder] {
        self.exists.as_ref().map_or(&[], ExistsAttribute::binders)
    }
    /// Returns the optional postcondition.
    #[must_use]
    pub const fn ensures(&self) -> Option<&ClaimEnsures> {
        self.ensures.as_ref()
    }
    /// Returns claim-only parser-owned anchors: the anchors of the claim's
    /// keying.
    ///
    /// # Errors
    ///
    /// None: the claim was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }
    /// Returns claim-only sort paths needing rustc/collector resolution,
    /// each with the key its node holds: the existential binders' sorts,
    /// which the claim numbers after its universal binders' sorts, then the
    /// anonymous nodes' sorts.
    ///
    /// # Errors
    ///
    /// None: the claim was keyed when it was parsed.
    ///
    /// # Panics
    ///
    /// Never: parsing keys every existential and anonymous sort.
    pub fn sort_candidates(&self) -> Result<Vec<ClaimSortCandidate>, SyntaxError> {
        let mut output = self
            .existentials()
            .iter()
            .map(|binder| ClaimSortCandidate {
                key: binder
                    .sort_key()
                    .expect("a claim keys every existential sort")
                    .clone(),
                path: binder.sort().clone(),
            })
            .collect::<Vec<_>>();
        // An anonymous node's keys are its own, its sort's and its
        // spelling's.
        for term in claim_terms(&self.rule, self.ensures.as_ref()) {
            for (index, node) in term.nodes().iter().enumerate() {
                if let TermNode::Anonymous { sort, .. } = node {
                    output.push(ClaimSortCandidate {
                        key: term
                            .keys()
                            .node(index)
                            .get(1)
                            .expect("a claim keys every anonymous sort")
                            .clone(),
                        path: sort.clone(),
                    });
                }
            }
        }
        Ok(output)
    }
}

impl KrsSyntax for StateClaimItem {
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        Self::from_item(syn::parse2(tokens)?)
    }
}

/// One zero-return, one-sided fixed-configuration context-alias declaration.
#[derive(Clone, Debug)]
pub struct StateContextAliasItem {
    item: ItemFn,
    pattern_macro: PatMacro,
    configuration_type: Path,
    pattern: CellsExpression,
    bindings: Vec<StateRuleBinding>,
    here: Ident,
    declaration_key: Option<ProvenanceKey>,
    pattern_key: Option<ProvenanceKey>,
    type_key: Option<ProvenanceKey>,
    /// The anchors of the alias's keying.
    anchors: Vec<ProvenanceAnchor>,
}

impl StateContextAliasItem {
    /// Parses the frozen context-alias function shape.
    ///
    /// # Errors
    ///
    /// Rejects a return type/body, a non-`cells!` pattern, or a `here`
    /// selection which is absent, duplicated, or structural rather than an
    /// ordinary term binding.
    pub fn from_item(item: ItemFn, here: &Ident) -> Result<Self, SyntaxError> {
        validate_signature(&item)?;
        if !matches!(item.sig.output, ReturnType::Default) || !item.block.stmts.is_empty() {
            return Err(body_error(
                "a context alias must return `()` and have an empty body",
                item.block.span(),
            ));
        }
        let Some(argument) = item.sig.inputs.last() else {
            return Err(signature_error(
                "a context alias requires a final `cells!` pattern",
                item.sig.span(),
            ));
        };
        let FnArg::Typed(argument) = argument else {
            return Err(signature_error(
                "context aliases cannot have a self receiver",
                argument.span(),
            ));
        };
        let Pat::Macro(pattern_macro) = &*argument.pat else {
            return Err(pattern_error(
                "a context alias subject must be `cells! { ... }`",
                argument.pat.span(),
            ));
        };
        let pattern_macro = pattern_macro.clone();
        validate_cells_path(&pattern_macro.mac.path, pattern_macro.span())?;
        let pattern = parse_cells_pattern(pattern_macro.mac.tokens.clone())?;
        let configuration_type = parse_configuration_type(&argument.ty)?;
        let mut bindings = Vec::new();
        collect_cells_bindings(&pattern, &mut bindings)?;
        let here_matches = count_term_binding_occurrences_in_cells(&pattern, here);
        if here_matches != 1
            || bindings
                .iter()
                .find(|binding| binding.name == *here)
                .is_none_or(|binding| binding.kind != StateRuleBindingKind::Term)
        {
            return Err(pattern_error(
                "`here` must select exactly one ordinary term binding",
                here.span(),
            ));
        }
        let typed = parse_typed_bindings(&item)?;
        require_declared_binders_occur(&bindings, &typed)?;
        let ordinary_names = bindings
            .iter()
            .filter(|binding| binding.kind == StateRuleBindingKind::Term && binding.name != *here)
            .map(|binding| &binding.name)
            .collect::<Vec<_>>();
        if typed.len() != ordinary_names.len()
            || typed
                .iter()
                .zip(ordinary_names)
                .any(|((name, _), expected)| name != expected)
        {
            return Err(signature_error(BINDER_LIST_CONTRACT, item.sig.span()));
        }
        for ((_, sort), binding) in
            typed.into_iter().zip(bindings.iter_mut().filter(|binding| {
                binding.kind == StateRuleBindingKind::Term && binding.name != *here
            }))
        {
            binding.sort = Some(sort);
        }
        Self {
            item,
            pattern_macro,
            configuration_type,
            pattern,
            bindings,
            here: here.clone(),
            declaration_key: None,
            pattern_key: None,
            type_key: None,
            anchors: Vec::new(),
        }
        .keyed()
    }

    /// Keys the alias as a sentence of its own and stores its anchors: the
    /// pattern and its type, each binding's sort, then the pattern's cells.
    /// The fn's name, the alias's declaration, holds the first key of its
    /// role, which the descriptor records after the attribute's keys
    /// ([`Self::descriptor_provenance`] checks that the attribute keys no
    /// node of that role).
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        self.declaration_key = Some(KeyAllocator::default().key(
            ProvenanceRole::ContextAliasDeclaration,
            TokenRange::for_tokens(&self.item.sig.ident)?,
        )?);
        let mut keys = KeyAllocator::default();
        self.pattern.clear_keys();
        for binding in &mut self.bindings {
            binding.clear_keys();
        }
        self.pattern_key = Some(keys.key(
            ProvenanceRole::RulePattern,
            TokenRange::for_tokens(&self.pattern_macro)?,
        )?);
        self.type_key = Some(keys.key(
            ProvenanceRole::RuleType,
            TokenRange::for_tokens(&self.configuration_type)?,
        )?);
        allocate_binding_sort_keys(&mut keys, &mut self.bindings)?;
        allocate_cells_keys(&mut keys, &mut self.pattern, RuleSide::Left)?;
        self.anchors = keys.into_anchors();
        Ok(self)
    }

    /// The key of the `cells!` pattern; its nodes hold their own keys.
    #[must_use]
    pub const fn pattern_key(&self) -> Option<&ProvenanceKey> {
        self.pattern_key.as_ref()
    }

    /// The key of the configuration type.
    #[must_use]
    pub const fn configuration_type_key(&self) -> Option<&ProvenanceKey> {
        self.type_key.as_ref()
    }

    /// The key of the fn's name, the alias's declaration in its descriptor.
    #[must_use]
    pub const fn declaration_key(&self) -> Option<&ProvenanceKey> {
        self.declaration_key.as_ref()
    }

    /// Returns the original function item.
    #[must_use]
    pub const fn item(&self) -> &ItemFn {
        &self.item
    }
    /// Returns the fixed-configuration type.
    #[must_use]
    pub const fn configuration_type(&self) -> &Path {
        &self.configuration_type
    }
    /// Returns the complete one-sided cells pattern.
    #[must_use]
    pub const fn pattern(&self) -> &CellsExpression {
        &self.pattern
    }
    /// Returns bindings in first-occurrence preorder.
    #[must_use]
    pub fn bindings(&self) -> &[StateRuleBinding] {
        &self.bindings
    }
    /// Returns the distinguished HERE binding.
    #[must_use]
    pub const fn here(&self) -> &Ident {
        &self.here
    }

    /// Returns parser-owned pattern/type/cell/frame origins: the anchors of
    /// the alias's keying.
    ///
    /// # Errors
    ///
    /// None: the alias was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    /// Returns rustc-resolvable paths with the keys of the nodes they name.
    ///
    /// # Errors
    ///
    /// None: the alias was keyed when it was parsed.
    ///
    /// # Panics
    ///
    /// Never: parsing keys every sort, type, wrapper, and term node a
    /// candidate names.
    pub fn reference_candidates(
        &self,
    ) -> Result<Vec<ReferenceCandidate<StateRuleReferenceKind>>, SyntaxError> {
        let mut output = binding_sort_candidates(&self.bindings);
        output.push(ReferenceCandidate {
            key: self.type_key.clone().expect(KEYED),
            path: self.configuration_type.clone(),
            kind: StateRuleReferenceKind::Configuration,
        });
        append_cells_candidates(&self.pattern, &self.bindings, &mut output);
        Ok(output)
    }
}

impl StateRuleItem {
    /// Parses a function whose subject and result are `cells!` islands.
    ///
    /// # Errors
    ///
    /// Rejects non-rule signature features, non-configuration types, any
    /// subject/result shell other than `cells!`, and result frame reuses that
    /// were not introduced in the complete subject pattern.
    pub fn from_item(item: ItemFn) -> Result<Self, SyntaxError> {
        Self::from_item_with(item, StateRuleForm::Rule)
    }

    /// Parses a `cells!`-shaped `#[k::context]` fn (KF-021): it returns
    /// `()`, has an empty body, and its subject holds at most one
    /// `k::rewrite!`.
    ///
    /// # Errors
    ///
    /// The shape errors of [`Self::from_item`], a result, a body, more than
    /// one rewrite, and `#[k::exists]`, `#[k::ensures]`, or `#[k::fresh]`.
    pub fn parse_context_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        Self::from_context_item(syn::parse2(tokens)?)
    }

    /// Validates a previously parsed Rust function as a `cells!`-shaped
    /// `#[k::context]` fn (KF-021).
    ///
    /// # Errors
    ///
    /// The errors of [`Self::parse_context_tokens`].
    pub fn from_context_item(item: ItemFn) -> Result<Self, SyntaxError> {
        Self::from_item_with(item, StateRuleForm::Context)
    }

    /// Parses a configuration rule; a unit-returning fn is a single-body
    /// rule (KF-011) only for a `#[k::rule]` fn, and a context for a
    /// `#[k::context]` fn.
    #[expect(
        clippy::too_many_lines,
        reason = "The signature, subject, result or single body, bindings, and helpers are validated in one ordered pass."
    )]
    fn from_item_with(mut item: ItemFn, form: StateRuleForm) -> Result<Self, SyntaxError> {
        let single_body = form != StateRuleForm::Claim;
        validate_signature(&item)?;
        let Some(argument) = item.sig.inputs.last() else {
            return Err(signature_error(
                "a configuration rule must have a final `cells!` subject",
                item.sig.inputs.span(),
            ));
        };
        let FnArg::Typed(argument) = argument else {
            return Err(signature_error(
                "configuration rules cannot have a `self` receiver",
                argument.span(),
            ));
        };
        if !argument.attrs.is_empty() {
            return Err(signature_error(
                "configuration-rule parameters cannot have helper attributes",
                argument.attrs[0].span(),
            ));
        }
        let Pat::Macro(subject_macro) = &*argument.pat else {
            return Err(pattern_error(
                "a configuration-rule subject must be `cells! { ... }`",
                argument.pat.span(),
            ));
        };
        let subject_macro = subject_macro.clone();
        validate_cells_path(&subject_macro.mac.path, subject_macro.span())?;
        let subject = parse_cells_pattern(subject_macro.mac.tokens.clone())?;
        let subject_type = parse_configuration_type(&argument.ty)?;
        if form == StateRuleForm::Context {
            check_context_shape(
                &item,
                match &item.sig.output {
                    ReturnType::Default => true,
                    ReturnType::Type(_, ty) => is_unit_type(ty),
                },
                &cells_rewrite_spans(&subject),
            )?;
        }

        // A unit-returning rule is a single-body rule (KF-011): its
        // subject's `k::rewrite!` islands mark what changes.
        let result = match &item.sig.output {
            ReturnType::Type(_, result_type) if !is_unit_type(result_type) => {
                let result_type = parse_configuration_type(result_type)?;
                let result_macro = parse_result_macro(&item)?;
                validate_cells_path(&result_macro.path, result_macro.span())?;
                let result = parse_cells_expression(result_macro.tokens.clone())?;
                Some(StateRuleResult {
                    result_macro,
                    result_type,
                    result,
                    key: None,
                    type_key: None,
                })
            }
            // A fn with statements and no rewrite meant to return a result.
            _ if !single_body
                || (!item.block.stmts.is_empty() && cells_rewrite_spans(&subject).is_empty()) =>
            {
                return Err(signature_error(
                    "a configuration rule must declare its configuration result type",
                    item.sig.ident.span(),
                ));
            }
            _ => {
                if !item.block.stmts.is_empty() {
                    return Err(local_rewrite_error(
                        SINGLE_BODY_BODY.to_owned(),
                        item.block.span(),
                    ));
                }
                None
            }
        };
        let rewrites = cells_rewrite_spans(&subject);
        match (&result, rewrites.first()) {
            (None, None) if form == StateRuleForm::Context => {}
            (None, None) => {
                return Err(local_rewrite_error(
                    SINGLE_BODY_WITHOUT_REWRITE.to_owned(),
                    item.sig.ident.span(),
                ));
            }
            (Some(_), Some(span)) => {
                return Err(local_rewrite_error(REWRITE_WITH_RESULT.to_owned(), *span));
            }
            _ => {}
        }

        let typed_bindings = parse_typed_bindings(&item)?;
        let mut bindings = Vec::new();
        collect_cells_bindings(&subject, &mut bindings)?;
        validate_rewrite_right_sides(&subject, &bindings)?;
        attach_typed_binding_sorts(&mut bindings, typed_bindings)?;
        if let Some(result) = &result {
            validate_result_reuses(&result.result, &bindings)?;
        }
        let requires = take_requires_helper(&mut item.attrs)?;
        let existentials = RuleExistentials::take(&mut item.attrs)?;
        if result.is_none()
            && let Some(helper) = existentials.attributes().first()
        {
            return Err(local_rewrite_error(
                if form == StateRuleForm::Context {
                    CONTEXT_BINDERS
                } else {
                    SINGLE_BODY_BINDERS
                }
                .to_owned(),
                helper.path().span(),
            ));
        }
        for condition in requires
            .as_ref()
            .map(RuleCondition::term)
            .into_iter()
            .chain(existentials.ensures())
        {
            validate_condition_reuses(condition, &bindings)?;
        }
        let subject_names = bindings
            .iter()
            .map(|binding| binding.name.clone())
            .collect::<Vec<_>>();
        existentials.check_shadowing(&subject_names)?;
        let mut result_terms = Vec::new();
        if let Some(result) = &result {
            append_cells_terms(&result.result, &mut result_terms);
        }
        existentials.check_scope(requires.as_ref().map(RuleCondition::term), &result_terms)?;
        Self {
            item,
            subject_macro,
            subject_type,
            subject,
            result,
            bindings,
            requires,
            existentials,
            declaration_key: None,
            pattern_key: None,
            type_key: None,
            anchors: Vec::new(),
        }
        .keyed()
    }

    /// Returns the original span-preserving Rust function.
    #[must_use]
    pub const fn item(&self) -> &ItemFn {
        &self.item
    }

    /// Returns the subject configuration type path.
    #[must_use]
    pub const fn subject_type(&self) -> &Path {
        &self.subject_type
    }

    /// Returns the complete subject `cells!` AST.
    #[must_use]
    pub const fn subject(&self) -> &CellsExpression {
        &self.subject
    }

    /// Returns the result configuration type path, or `None` for a
    /// single-body rule (KF-011).
    #[must_use]
    pub fn result_type(&self) -> Option<&Path> {
        self.result.as_ref().map(|result| &result.result_type)
    }

    /// Returns the complete result `cells!` AST, or `None` for a single-body
    /// rule (KF-011).
    #[must_use]
    pub fn result(&self) -> Option<&CellsExpression> {
        self.result.as_ref().map(|result| &result.result)
    }

    /// Returns subject bindings in first-occurrence structural preorder.
    ///
    /// Repeated bare names in different cells denote the same binding, as in
    /// IMP's variable lookup rule; they are not duplicate declarations.
    #[must_use]
    pub fn bindings(&self) -> &[StateRuleBinding] {
        &self.bindings
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

    /// Returns one collision-free descriptor-wide provenance table: the
    /// anchors of the rule's own keying.
    ///
    /// # Errors
    ///
    /// None: the rule was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    /// Keys the rule as a sentence of its own and stores its anchors: the
    /// declaration, the rule's nodes, then the claim-only literals of the
    /// cells, the condition, and the ensures condition.
    fn keyed(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        self.clear_keys();
        self.declaration_key = Some(keys.key(
            ProvenanceRole::RuleDeclaration,
            TokenRange::for_tokens(&self.item.sig.ident)?,
        )?);
        self.allocate_body_keys(&mut keys)?;
        // Builtin `Id` and `Bytes` literals, each kind numbered across the
        // cells, the condition, then the ensures condition (a claim numbers
        // its own, with its claim-only islands).
        self.visit_terms(&mut |nodes, term_keys| {
            allocate_claim_node_keys(&mut keys, [(nodes, term_keys)])
        })?;
        if let Some(ensures) = self.existentials.ensures_mut() {
            let (nodes, _, term_keys) = ensures.keying();
            allocate_claim_node_keys(&mut keys, [(nodes, term_keys)])?;
        }
        self.anchors = keys.into_anchors();
        Ok(self)
    }

    /// Forgets every key of the rule, before a sentence's pass keys it.
    fn clear_keys(&mut self) {
        self.declaration_key = None;
        self.pattern_key = None;
        self.type_key = None;
        self.subject.clear_keys();
        if let Some(result) = &mut self.result {
            result.key = None;
            result.type_key = None;
            result.result.clear_keys();
        }
        for binding in &mut self.bindings {
            binding.clear_keys();
        }
        if let Some(requires) = &mut self.requires {
            requires.clear_keys();
        }
        self.existentials.clear_keys();
    }

    /// Keys the rule's nodes between its declaration and its claim-only
    /// literals: the subject pattern and type, the result type and result,
    /// each binding's sort, the subject's and the result's cells, the
    /// conditions and binders, then the islands of every term in expansion
    /// order.
    fn allocate_body_keys(&mut self, keys: &mut KeyAllocator) -> Result<(), SyntaxError> {
        self.pattern_key = Some(keys.key(
            ProvenanceRole::RulePattern,
            TokenRange::for_tokens(&self.subject_macro)?,
        )?);
        self.type_key = Some(keys.key(
            ProvenanceRole::RuleType,
            TokenRange::for_tokens(&self.subject_type)?,
        )?);
        if let Some(result) = &mut self.result {
            result.type_key = Some(keys.key(
                ProvenanceRole::RuleResultType,
                TokenRange::for_tokens(&result.result_type)?,
            )?);
            result.key = Some(keys.key(
                ProvenanceRole::RuleResult,
                TokenRange::for_tokens(&result.result_macro)?,
            )?);
        }
        allocate_binding_sort_keys(keys, &mut self.bindings)?;
        allocate_cells_keys(keys, &mut self.subject, RuleSide::Left)?;
        if let Some(result) = &mut self.result {
            allocate_cells_keys(keys, &mut result.result, RuleSide::Right)?;
        }
        if let Some(requires) = &mut self.requires {
            requires.allocate_keys(keys)?;
        }
        self.existentials.allocate_keys(keys)?;
        // `k::rewrite!` shells and sides (KF-011), in subject order.
        self.visit_terms(&mut |nodes, term_keys| {
            crate::term::allocate_rewrite_keys(keys, nodes, term_keys)
        })?;
        self.visit_terms(&mut |nodes, term_keys| allocate_lexeme_keys(keys, nodes, term_keys))?;
        self.visit_ensures(&mut |nodes, term_keys| allocate_lexeme_keys(keys, nodes, term_keys))?;
        self.visit_terms(&mut |nodes, term_keys| allocate_sort_test_keys(keys, nodes, term_keys))?;
        self.visit_terms(&mut |nodes, term_keys| {
            crate::term::allocate_pattern_as_keys(keys, nodes, term_keys)
        })?;
        self.visit_terms(&mut |nodes, term_keys| {
            crate::term::allocate_pattern_or_keys(keys, nodes, term_keys)
        })?;
        self.visit_ensures(&mut |nodes, term_keys| {
            allocate_sort_test_keys(keys, nodes, term_keys)?;
            crate::term::allocate_pattern_as_keys(keys, nodes, term_keys)?;
            crate::term::allocate_pattern_or_keys(keys, nodes, term_keys)
        })?;
        // Turbofish sort markers (KF-027), `k::matches!` shells and pattern
        // wildcards (KF-031), `let` statements and their pattern wildcards
        // (KF-032), and `ml::exists` closures (KF-039), each kind in
        // expansion order: the cells, the condition, then the ensures
        // condition.
        let islands: [IslandKeys; 4] = [
            crate::term::allocate_application_instance_keys,
            crate::term::allocate_matches_keys,
            crate::term::allocate_let_keys,
            crate::term::allocate_ml_binder_keys,
        ];
        for island in islands {
            self.visit_terms(&mut |nodes, term_keys| island(keys, nodes, term_keys))?;
            self.visit_ensures(&mut |nodes, term_keys| island(keys, nodes, term_keys))?;
        }
        Ok(())
    }

    /// Calls `visit` on the nodes and keys of each term of the subject's
    /// cells, then the result's, then the condition's.
    fn visit_terms(&mut self, visit: &mut TermVisit<'_>) -> Result<(), SyntaxError> {
        let results = self.result.iter_mut().map(|result| &mut result.result);
        for cells in std::iter::once(&mut self.subject).chain(results) {
            for entry in cells.entries_mut() {
                for term in entry.value_mut().terms_mut() {
                    let (nodes, _, term_keys) = term.keying();
                    visit(nodes, term_keys)?;
                }
            }
        }
        if let Some(requires) = &mut self.requires {
            let (nodes, _, term_keys) = requires.term_mut().keying();
            visit(nodes, term_keys)?;
        }
        Ok(())
    }

    /// Calls `visit` on the nodes and keys of the `#[k::ensures]` condition.
    fn visit_ensures(&mut self, visit: &mut TermVisit<'_>) -> Result<(), SyntaxError> {
        if let Some(ensures) = self.existentials.ensures_mut() {
            let (nodes, _, term_keys) = ensures.keying();
            visit(nodes, term_keys)?;
        }
        Ok(())
    }

    /// The key of the rule's name: its declaration, or a claim's.
    #[must_use]
    pub const fn declaration_key(&self) -> Option<&ProvenanceKey> {
        self.declaration_key.as_ref()
    }

    /// The key of the subject's `cells!` pattern; its nodes hold their own
    /// keys.
    #[must_use]
    pub const fn pattern_key(&self) -> Option<&ProvenanceKey> {
        self.pattern_key.as_ref()
    }

    /// The key of the subject's configuration type.
    #[must_use]
    pub const fn subject_type_key(&self) -> Option<&ProvenanceKey> {
        self.type_key.as_ref()
    }

    /// The key of the result's `cells!` expression, absent for a
    /// single-body rule.
    #[must_use]
    pub fn result_key(&self) -> Option<&ProvenanceKey> {
        self.result.as_ref().and_then(|result| result.key.as_ref())
    }

    /// The key of the result's configuration type, absent for a single-body
    /// rule.
    #[must_use]
    pub fn result_type_key(&self) -> Option<&ProvenanceKey> {
        self.result
            .as_ref()
            .and_then(|result| result.type_key.as_ref())
    }

    /// Returns every rustc-resolvable type/wrapper/term path with the same
    /// descriptor-wide keys as [`Self::provenance`].
    ///
    /// Bare subject references are bindings. Bare result references equal to
    /// a subject binding are reuse sites and therefore omitted; other result
    /// references remain candidates so qualified or unit constructors are
    /// resolved by rustc rather than guessed by spelling.
    ///
    /// # Errors
    ///
    /// None: the rule was keyed when it was parsed.
    ///
    /// # Panics
    ///
    /// Never: parsing keys every sort, type, wrapper, and term node a
    /// candidate names.
    pub fn reference_candidates(
        &self,
    ) -> Result<Vec<ReferenceCandidate<StateRuleReferenceKind>>, SyntaxError> {
        let mut output = binding_sort_candidates(&self.bindings);
        output.push(ReferenceCandidate {
            key: self.type_key.clone().expect(KEYED),
            path: self.subject_type.clone(),
            kind: StateRuleReferenceKind::Configuration,
        });
        if let Some(result) = &self.result {
            output.push(ReferenceCandidate {
                key: result.type_key.clone().expect(KEYED),
                path: result.result_type.clone(),
                kind: StateRuleReferenceKind::Configuration,
            });
        }
        append_cells_candidates(&self.subject, &self.bindings, &mut output);
        if let Some(result) = &self.result {
            append_cells_candidates(&result.result, &self.bindings, &mut output);
        }
        Ok(output)
    }
}

/// The diagnostic for a function context on a sentence other than an
/// equation (KF-025).
pub const FUNCTION_CONTEXT_ONLY_ON_EQUATIONS: &str =
    "a configuration context belongs only on #[k::equation] (K's [[ ]] function context)";

/// The diagnostic for a function context that is not a `cells!` pattern typed
/// by the configuration struct (KF-025).
pub const FUNCTION_CONTEXT_SHAPE: &str = "a function context is a final `k::cells! { cell: .., .. }` parameter typed by the configuration struct";

/// The diagnostic for a function context without its trailing anonymous `..`
/// (KF-025).
pub const FUNCTION_CONTEXT_REMAINDER: &str =
    "a function context frames the rest of the configuration with an anonymous `..`";

fn function_context_error(reason: &str, span: proc_macro2::Span) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::InvalidFunctionContext {
            reason: reason.to_owned(),
        },
        span,
    )
}

/// Whether a fn parameter is written `k::cells! { .. }`, the shape of a
/// function context (or of a `cells!` rule's subject).
#[must_use]
pub fn is_cells_parameter(argument: &FnArg) -> bool {
    let FnArg::Typed(argument) = argument else {
        return false;
    };
    let Pat::Macro(pattern) = &*argument.pat else {
        return false;
    };
    pattern
        .mac
        .path
        .segments
        .last()
        .is_some_and(|segment| segment.ident == "cells")
}

/// The read-only configuration context of an equation (KF-025): a final
/// `k::cells! { cell: .., .. }: Machine` parameter, K's `[[ .. ]]` cells.
#[derive(Clone, Debug)]
pub struct FunctionContext {
    parameter: syn::PatType,
    pattern_macro: PatMacro,
    configuration_type: Path,
    pattern: CellsExpression,
    bindings: Vec<StateRuleBinding>,
    key: Option<ProvenanceKey>,
    type_key: Option<ProvenanceKey>,
}

impl FunctionContext {
    /// Parses the final parameter of an equation as a function context.
    ///
    /// # Errors
    ///
    /// Rejects a parameter that is not `k::cells! { .. }` typed by a plain
    /// configuration path, a context without its trailing anonymous `..`, and
    /// malformed cell patterns.
    pub(crate) fn parse(argument: &FnArg) -> Result<Self, SyntaxError> {
        let FnArg::Typed(argument) = argument else {
            return Err(function_context_error(
                FUNCTION_CONTEXT_SHAPE,
                argument.span(),
            ));
        };
        if !argument.attrs.is_empty() {
            return Err(function_context_error(
                FUNCTION_CONTEXT_SHAPE,
                argument.attrs[0].span(),
            ));
        }
        let Pat::Macro(pattern_macro) = &*argument.pat else {
            return Err(function_context_error(
                FUNCTION_CONTEXT_SHAPE,
                argument.pat.span(),
            ));
        };
        if !is_plain_path(&pattern_macro.mac.path)
            || pattern_macro
                .mac
                .path
                .segments
                .last()
                .is_none_or(|segment| segment.ident != "cells")
        {
            return Err(function_context_error(
                FUNCTION_CONTEXT_SHAPE,
                pattern_macro.span(),
            ));
        }
        let Type::Path(path) = &*argument.ty else {
            return Err(function_context_error(
                FUNCTION_CONTEXT_SHAPE,
                argument.ty.span(),
            ));
        };
        if path.qself.is_some() || !is_plain_path(&path.path) {
            return Err(function_context_error(
                FUNCTION_CONTEXT_SHAPE,
                argument.ty.span(),
            ));
        }
        let pattern = parse_cells_pattern(pattern_macro.mac.tokens.clone())?;
        match pattern.remainder() {
            StateMacroRemainder::Anonymous(_) => {}
            StateMacroRemainder::Bind { range, .. } | StateMacroRemainder::Reuse { range, .. } => {
                return Err(function_context_error(
                    FUNCTION_CONTEXT_REMAINDER,
                    range.first(),
                ));
            }
            StateMacroRemainder::Exact => {
                return Err(function_context_error(
                    FUNCTION_CONTEXT_REMAINDER,
                    pattern_macro.mac.delimiter.span().close(),
                ));
            }
        }
        let mut bindings = Vec::new();
        collect_cells_bindings(&pattern, &mut bindings)?;
        Ok(Self {
            parameter: argument.clone(),
            pattern_macro: pattern_macro.clone(),
            configuration_type: path.path.clone(),
            pattern,
            bindings,
            key: None,
            type_key: None,
        })
    }

    /// Returns the complete authored `k::cells! { .. }: Machine` parameter.
    #[must_use]
    pub const fn parameter(&self) -> &syn::PatType {
        &self.parameter
    }

    /// Returns the configuration type path.
    #[must_use]
    pub const fn configuration_type(&self) -> &Path {
        &self.configuration_type
    }

    /// Returns the one-sided `cells!` pattern.
    #[must_use]
    pub const fn pattern(&self) -> &CellsExpression {
        &self.pattern
    }

    /// Returns the context's bindings in first-occurrence preorder; a term
    /// binding carries its declared sort.
    #[must_use]
    pub fn bindings(&self) -> &[StateRuleBinding] {
        &self.bindings
    }

    /// The context's term bindings in first-occurrence preorder.
    pub(crate) fn term_bindings(&self) -> impl Iterator<Item = &Ident> {
        self.bindings
            .iter()
            .filter(|binding| binding.kind == StateRuleBindingKind::Term)
            .map(|binding| &binding.name)
    }

    /// Rejects a structural frame name that is also a subject binder, and
    /// attaches each term binding's declared sort.
    pub(crate) fn attach_sorts(
        &mut self,
        subject: &[Ident],
        declared: &[(Ident, TermSort)],
    ) -> Result<(), SyntaxError> {
        for binding in &mut self.bindings {
            if binding.kind != StateRuleBindingKind::Term {
                if subject.iter().any(|name| name == &binding.name) {
                    return Err(pattern_error(
                        "a configuration-rule binding cannot be reused as a different frame or term kind",
                        binding.name.span(),
                    ));
                }
                continue;
            }
            binding.sort = declared
                .iter()
                .find(|(name, _)| name == &binding.name)
                .map(|(_, sort)| sort.clone());
        }
        Ok(())
    }

    /// The context's cell terms in expansion order.
    #[must_use]
    pub fn terms(&self) -> Vec<&TermExpression> {
        let mut output = Vec::new();
        append_cells_terms(&self.pattern, &mut output);
        output
    }

    /// The `Cell`/`KCell` wrapper paths, which rustc resolves.
    #[must_use]
    pub fn wrapper_paths(&self) -> Vec<&Path> {
        self.pattern
            .entries()
            .iter()
            .filter_map(crate::CellsEntry::wrapper)
            .collect()
    }

    /// The key of the `k::cells! { .. }` parameter pattern; its cells hold
    /// their own keys.
    #[must_use]
    pub const fn key(&self) -> Option<&ProvenanceKey> {
        self.key.as_ref()
    }

    /// The key of the configuration type.
    #[must_use]
    pub const fn type_key(&self) -> Option<&ProvenanceKey> {
        self.type_key.as_ref()
    }

    /// The context's cell terms in expansion order, for a pass that keys
    /// them.
    pub(crate) fn terms_mut(&mut self) -> Vec<&mut TermExpression> {
        self.pattern
            .entries_mut()
            .iter_mut()
            .flat_map(|entry| entry.value_mut().terms_mut())
            .collect()
    }

    /// Forgets the keys of the parameter and of its cells, before the
    /// equation's pass keys them.
    pub(crate) fn clear_keys(&mut self) {
        self.key = None;
        self.type_key = None;
        self.pattern.clear_keys();
    }

    /// Keys the parameter (`function_context`, `function_context_type`), then
    /// the cells, whose left-hand term ordinals continue after the subject's.
    pub(crate) fn allocate_keys(&mut self, keys: &mut KeyAllocator) -> Result<(), SyntaxError> {
        self.key = Some(keys.key(
            ProvenanceRole::FunctionContext,
            TokenRange::for_tokens(&self.pattern_macro)?,
        )?);
        self.type_key = Some(keys.key(
            ProvenanceRole::FunctionContextType,
            TokenRange::for_tokens(&self.configuration_type)?,
        )?);
        allocate_cells_keys(keys, &mut self.pattern, RuleSide::Left)
    }
}

impl KrsSyntax for StateRuleItem {
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        Self::from_item(syn::parse2(tokens)?)
    }
}

/// Parses a one-sided context-alias function item.
///
/// # Errors
///
/// Returns Rust parsing or [`StateContextAliasItem`] shape errors.
pub fn parse_state_context_alias_item(
    tokens: TokenStream,
    here: &Ident,
) -> Result<StateContextAliasItem, SyntaxError> {
    StateContextAliasItem::from_item(syn::parse2(tokens)?, here)
}

/// Which fn sentence a `cells!` rule item is parsed as.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum StateRuleForm {
    /// A claim, which always has a result.
    Claim,
    /// A `#[k::rule]` fn, which may be a single-body rule (KF-011).
    Rule,
    /// A `#[k::context]` fn (KF-021).
    Context,
}

/// The reason given for a context with a result.
pub(crate) const CONTEXT_RESULT: &str = "a context returns `()`: it says where evaluation may happen and has no after-state; K turns it into a heat rule and a cool rule";

/// The reason given for a context with statements in its body.
pub(crate) const CONTEXT_BODY: &str =
    "a context has an empty body `{}`; its subject is the whole context";

/// The reason given for more than one rewrite in a context.
pub(crate) const CONTEXT_REWRITES: &str =
    "a context rewrites at most its hole, once: `k::rewrite!(h => f(h))`, K's `HOLE => f(HOLE)`";

/// The reason given for result binders on a context.
pub(crate) const CONTEXT_BINDERS: &str =
    "a context takes no `#[k::exists]`, `#[k::ensures]`, or `#[k::fresh]`: it has no after-state";

/// Checks the shape of a `#[k::context]` fn (KF-021): a unit return, an
/// empty body, and at most one `k::rewrite!` (at `rewrites`).
pub(crate) fn check_context_shape(
    item: &ItemFn,
    returns_unit: bool,
    rewrites: &[proc_macro2::Span],
) -> Result<(), SyntaxError> {
    if !returns_unit {
        let span = match &item.sig.output {
            ReturnType::Type(_, ty) => ty.span(),
            ReturnType::Default => item.sig.span(),
        };
        return Err(signature_error(CONTEXT_RESULT, span));
    }
    if !item.block.stmts.is_empty() {
        return Err(signature_error(CONTEXT_BODY, item.block.span()));
    }
    if let Some(span) = rewrites.get(1) {
        return Err(local_rewrite_error(CONTEXT_REWRITES.to_owned(), *span));
    }
    Ok(())
}

/// The reason given for a single-body rule with statements in its body.
pub(crate) const SINGLE_BODY_BODY: &str = "a single-body rule (one that returns `()`) has an empty body `{}`; its subject's `k::rewrite!` islands say what changes";

/// The reason given for a single-body rule without a rewrite.
pub(crate) const SINGLE_BODY_WITHOUT_REWRITE: &str = "a single-body rule must change something: mark what changes in its subject with `k::rewrite!(from => to)`, or return a result";

/// The reason given for result binders on a single-body rule.
pub(crate) const SINGLE_BODY_BINDERS: &str = "a single-body rule takes no `#[k::exists]`, `#[k::ensures]`, or `#[k::fresh]`: write a rule with a result to introduce new values";

/// The reason given for a rewrite in a rule that has a result.
pub(crate) const REWRITE_WITH_RESULT: &str = "`k::rewrite!` belongs to a single-body rule, which returns `()`; a rule with a result already states the whole after-state";

/// Whether `ty` is `()`.
pub(crate) fn is_unit_type(ty: &Type) -> bool {
    matches!(ty, Type::Tuple(tuple) if tuple.elems.is_empty())
}

/// The spans of the `k::rewrite!` islands of a `cells!` pattern, in order.
fn cells_rewrite_spans(cells: &CellsExpression) -> Vec<proc_macro2::Span> {
    let mut terms = Vec::new();
    append_cells_terms(cells, &mut terms);
    terms
        .into_iter()
        .flat_map(TermExpression::nodes)
        .filter_map(|node| match node {
            TermNode::Rewrite { range, .. } => Some(range.first()),
            _ => None,
        })
        .collect()
}

/// Checks the right side of every `k::rewrite!` (KF-011): each bare name
/// there is a term binding of the left image, and a map key holds no
/// rewrite.
fn validate_rewrite_right_sides(
    cells: &CellsExpression,
    bindings: &[StateRuleBinding],
) -> Result<(), SyntaxError> {
    for entry in cells.entries() {
        if let StateTerm::Map(map) = entry.value()
            && let MapBody::Items { items, .. } = map.body()
        {
            for item in items {
                if let Some(TermNode::Rewrite { range, .. }) = item
                    .key()
                    .nodes()
                    .iter()
                    .find(|node| matches!(node, TermNode::Rewrite { .. }))
                {
                    return Err(local_rewrite_error(
                        crate::term::REWRITE_IN_MAP_KEY.to_owned(),
                        range.first(),
                    ));
                }
            }
        }
    }
    let mut terms = Vec::new();
    append_cells_terms(cells, &mut terms);
    let names = bindings
        .iter()
        .filter(|binding| binding.kind == StateRuleBindingKind::Term)
        .map(|binding| binding.name.clone())
        .collect::<Vec<_>>();
    for term in terms {
        crate::term::check_rewrite_right_bindings(term.nodes(), &names)?;
    }
    Ok(())
}

fn validate_signature(item: &ItemFn) -> Result<(), SyntaxError> {
    let signature = &item.sig;
    if signature.inputs.is_empty() {
        return Err(signature_error(
            "a configuration rule must have a final `cells!` subject",
            signature.inputs.span(),
        ));
    }
    if signature.constness.is_some()
        || signature.asyncness.is_some()
        || signature.unsafety.is_some()
        || signature.abi.is_some()
        || !signature.generics.params.is_empty()
        || signature.generics.where_clause.is_some()
        || signature.variadic.is_some()
    {
        return Err(signature_error(
            "configuration rules cannot use qualifiers, generics, where clauses, or variadics",
            signature.span(),
        ));
    }
    Ok(())
}

fn parse_typed_bindings(item: &ItemFn) -> Result<Vec<(Ident, TermSort)>, SyntaxError> {
    let mut output = Vec::new();
    for argument in item
        .sig
        .inputs
        .iter()
        .take(item.sig.inputs.len().saturating_sub(1))
    {
        let FnArg::Typed(argument) = argument else {
            return Err(signature_error(
                "configuration rules cannot have a `self` receiver",
                argument.span(),
            ));
        };
        if !argument.attrs.is_empty() {
            return Err(signature_error(
                "configuration-rule parameters cannot have helper attributes",
                argument.attrs[0].span(),
            ));
        }
        let Pat::Ident(pattern) = &*argument.pat else {
            return Err(signature_error(
                "configuration-rule term parameters must be plain bindings",
                argument.pat.span(),
            ));
        };
        if pattern.by_ref.is_some()
            || pattern.mutability.is_some()
            || pattern.subpat.is_some()
            || output
                .iter()
                .any(|(existing, _): &(Ident, TermSort)| existing == &pattern.ident)
        {
            return Err(signature_error(
                "configuration-rule term parameters must be unique immutable bindings",
                pattern.span(),
            ));
        }
        let authored_type = (*argument.ty).clone();
        crate::parse::validate_authored_binder(&pattern.ident.to_string(), pattern.ident.span())?;
        let sort = parse_term_or_readable_sort(authored_type)?;
        output.push((pattern.ident.clone(), sort));
    }
    Ok(output)
}

fn parse_configuration_type(ty: &Type) -> Result<Path, SyntaxError> {
    let Type::Path(path) = ty else {
        return Err(signature_error(
            "configuration-rule types must be plain nominal Rust paths",
            ty.span(),
        ));
    };
    if path.qself.is_some() || !is_plain_path(&path.path) {
        return Err(signature_error(
            "configuration-rule types must be plain nominal Rust paths",
            ty.span(),
        ));
    }
    Ok(path.path.clone())
}

fn parse_result_macro(item: &ItemFn) -> Result<Macro, SyntaxError> {
    if item.block.stmts.len() != 1 {
        return Err(body_error(
            "a configuration-rule body must contain exactly one `cells!` expression",
            item.block.span(),
        ));
    }
    match &item.block.stmts[0] {
        Stmt::Expr(Expr::Macro(expression), None) => Ok(expression.mac.clone()),
        Stmt::Macro(statement) if statement.attrs.is_empty() && statement.semi_token.is_none() => {
            Ok(statement.mac.clone())
        }
        statement => Err(body_error(
            "a configuration-rule body must be one unterminated `cells!` expression",
            statement.span(),
        )),
    }
}

fn validate_cells_path(path: &Path, span: proc_macro2::Span) -> Result<(), SyntaxError> {
    if !is_plain_path(path)
        || path
            .segments
            .last()
            .is_none_or(|segment| segment.ident != "cells")
    {
        return Err(pattern_error(
            "configuration rules require the compiler-owned `cells!` island",
            span,
        ));
    }
    Ok(())
}

/// The term binders a `cells!` pattern introduces, in the first-occurrence
/// preorder that a rule's typed term parameters follow.
///
/// # Errors
///
/// Returns the binding error a `cells!` rule subject would report.
pub fn cells_pattern_term_binders(cells: &CellsExpression) -> Result<Vec<Ident>, SyntaxError> {
    let mut bindings = Vec::new();
    collect_cells_bindings(cells, &mut bindings)?;
    Ok(bindings
        .into_iter()
        .filter(|binding| binding.kind == StateRuleBindingKind::Term)
        .map(|binding| binding.name)
        .collect())
}

fn collect_cells_bindings(
    cells: &CellsExpression,
    output: &mut Vec<StateRuleBinding>,
) -> Result<(), SyntaxError> {
    for entry in cells.entries() {
        collect_state_term_bindings(entry.value(), output)?;
    }
    collect_remainder_binding(
        cells.remainder(),
        StateRuleBindingKind::ConfigurationFrame,
        output,
    )
}

fn count_term_binding_occurrences_in_cells(cells: &CellsExpression, binding: &Ident) -> usize {
    cells
        .entries()
        .iter()
        .map(|entry| count_term_binding_occurrences_in_state(entry.value(), binding))
        .sum()
}

fn count_term_binding_occurrences_in_state(state: &StateTerm, binding: &Ident) -> usize {
    match state {
        StateTerm::Present(_) | StateTerm::Absent(_) | StateTerm::Instances(_) => state
            .nested_states()
            .into_iter()
            .map(|nested| count_term_binding_occurrences_in_state(nested, binding))
            .sum(),
        StateTerm::Term(term) | StateTerm::Group(term) => {
            count_term_binding_occurrences(term, binding)
        }
        StateTerm::KSequence(sequence) => sequence
            .items()
            .iter()
            .map(|term| count_term_binding_occurrences(term, binding))
            .sum(),
        StateTerm::Map(map) => match map.body() {
            MapBody::Empty { .. } | MapBody::Update { .. } => 0,
            MapBody::Items { items, .. } => items
                .iter()
                .map(|item| {
                    count_term_binding_occurrences(item.key(), binding)
                        + count_term_binding_occurrences(item.value(), binding)
                })
                .sum(),
        },
    }
}

fn count_term_binding_occurrences(term: &TermExpression, binding: &Ident) -> usize {
    term.nodes()
        .iter()
        .filter(|node| match node {
            TermNode::Reference(path) => bare_ident(path) == Some(binding),
            TermNode::As { binding: alias, .. } => alias == binding,
            _ => false,
        })
        .count()
}

fn collect_state_term_bindings(
    term: &StateTerm,
    output: &mut Vec<StateRuleBinding>,
) -> Result<(), SyntaxError> {
    match term {
        StateTerm::Present(inner) => collect_state_term_bindings(inner, output),
        StateTerm::Absent(_) => Ok(()),
        StateTerm::Instances(list) => {
            for instance in list.front() {
                for field in instance.fields() {
                    collect_state_term_bindings(field.value(), output)?;
                }
            }
            collect_remainder_binding(list.rest(), StateRuleBindingKind::InstancesFrame, output)?;
            for instance in list.back() {
                for field in instance.fields() {
                    collect_state_term_bindings(field.value(), output)?;
                }
            }
            Ok(())
        }
        StateTerm::Term(term) | StateTerm::Group(term) => collect_term_bindings(term, output),
        StateTerm::KSequence(sequence) => {
            for item in sequence.items() {
                collect_term_bindings(item, output)?;
            }
            collect_remainder_binding(
                sequence.tail(),
                StateRuleBindingKind::KSequenceFrame,
                output,
            )
        }
        StateTerm::Map(map) => {
            if let Some(bindings) = map.pattern_bindings() {
                for binding in &bindings.terms {
                    push_binding(binding, StateRuleBindingKind::Term, output)?;
                }
                if let Some(binding) = &bindings.frame {
                    push_binding(binding, StateRuleBindingKind::MapFrame, output)?;
                }
            }
            Ok(())
        }
    }
}

fn collect_term_bindings(
    term: &TermExpression,
    output: &mut Vec<StateRuleBinding>,
) -> Result<(), SyntaxError> {
    // Only the left image binds (KF-011): the right side of a `k::rewrite!`
    // uses the subject's bindings.
    let (left, _) = crate::term::split_rewrite_images(term.nodes());
    for node in left {
        let binding = match node {
            TermNode::Reference(path) => crate::path::pattern_binder(path),
            TermNode::As { binding, .. } => Some(binding),
            _ => None,
        };
        if let Some(binding) = binding {
            push_binding(binding, StateRuleBindingKind::Term, output)?;
        }
    }
    Ok(())
}

fn collect_remainder_binding(
    remainder: &StateMacroRemainder,
    kind: StateRuleBindingKind,
    output: &mut Vec<StateRuleBinding>,
) -> Result<(), SyntaxError> {
    if let StateMacroRemainder::Bind { binding, .. } = remainder {
        push_binding(binding, kind, output)?;
    }
    Ok(())
}

fn push_binding(
    binding: &Ident,
    kind: StateRuleBindingKind,
    output: &mut Vec<StateRuleBinding>,
) -> Result<(), SyntaxError> {
    crate::parse::validate_authored_binder(&binding.to_string(), binding.span())?;
    if let Some(existing) = output.iter().find(|existing| existing.name == *binding) {
        if existing.kind != kind {
            return Err(pattern_error(
                "a configuration-rule binding cannot be reused as a different frame or term kind",
                binding.span(),
            ));
        }
        return Ok(());
    }
    output.push(StateRuleBinding {
        name: binding.clone(),
        kind,
        sort: None,
        sort_key: None,
        universal_key: None,
        binder_name_key: None,
        binder_sort_key: None,
    });
    Ok(())
}

/// Rejects a declared binder that the subject never binds (X5.6).
fn require_declared_binders_occur(
    bindings: &[StateRuleBinding],
    typed: &[(Ident, TermSort)],
) -> Result<(), SyntaxError> {
    for (name, _) in typed {
        if !bindings.iter().any(|binding| &binding.name == name) {
            return Err(SyntaxError::new(
                SyntaxErrorKind::InvalidBinderList {
                    reason: format!(
                        "binder `{name}` is declared but does not occur in the subject"
                    ),
                },
                name.span(),
            ));
        }
    }
    Ok(())
}

fn attach_typed_binding_sorts(
    bindings: &mut [StateRuleBinding],
    typed: Vec<(Ident, TermSort)>,
) -> Result<(), SyntaxError> {
    require_declared_binders_occur(bindings, &typed)?;
    let subject_terms = bindings
        .iter()
        .filter(|binding| binding.kind == StateRuleBindingKind::Term)
        .map(|binding| &binding.name)
        .collect::<Vec<_>>();
    if typed.len() != subject_terms.len()
        || typed
            .iter()
            .zip(subject_terms)
            .any(|((typed, _), subject)| typed != subject)
    {
        let span = typed
            .first()
            .map_or_else(proc_macro2::Span::call_site, |(name, _)| name.span());
        return Err(signature_error(BINDER_LIST_CONTRACT, span));
    }
    for ((_, sort), binding) in typed.into_iter().zip(
        bindings
            .iter_mut()
            .filter(|binding| binding.kind == StateRuleBindingKind::Term),
    ) {
        binding.sort = Some(sort);
    }
    Ok(())
}

fn validate_result_reuses(
    cells: &CellsExpression,
    bindings: &[StateRuleBinding],
) -> Result<(), SyntaxError> {
    validate_remainder_reuse(
        cells.remainder(),
        StateRuleBindingKind::ConfigurationFrame,
        bindings,
    )?;
    for entry in cells.entries() {
        validate_state_reuses(entry.value(), bindings)?;
    }
    Ok(())
}

fn validate_state_reuses(
    state: &StateTerm,
    bindings: &[StateRuleBinding],
) -> Result<(), SyntaxError> {
    {
        match state {
            StateTerm::Present(inner) => validate_state_reuses(inner, bindings)?,
            StateTerm::Absent(_) => {}
            StateTerm::Instances(list) => {
                for nested in state.nested_states() {
                    validate_state_reuses(nested, bindings)?;
                }
                validate_remainder_reuse(
                    list.rest(),
                    StateRuleBindingKind::InstancesFrame,
                    bindings,
                )?;
            }
            StateTerm::Term(term) | StateTerm::Group(term) => {
                validate_term_reuses(term, bindings)?;
            }
            StateTerm::KSequence(sequence) => {
                for item in sequence.items() {
                    validate_term_reuses(item, bindings)?;
                }
                validate_remainder_reuse(
                    sequence.tail(),
                    StateRuleBindingKind::KSequenceFrame,
                    bindings,
                )?;
            }
            StateTerm::Map(map) => {
                for term in map_terms(map) {
                    validate_term_reuses(term, bindings)?;
                }
                if let MapBody::Items { remainder, .. } = map.body() {
                    validate_remainder_reuse(remainder, StateRuleBindingKind::MapFrame, bindings)?;
                }
            }
        }
    }
    Ok(())
}

fn validate_remainder_reuse(
    remainder: &StateMacroRemainder,
    expected: StateRuleBindingKind,
    bindings: &[StateRuleBinding],
) -> Result<(), SyntaxError> {
    if let StateMacroRemainder::Reuse { binding, range } = remainder
        && !bindings
            .iter()
            .any(|existing| existing.name == *binding && existing.kind == expected)
    {
        return Err(body_error(
            "a result remainder must reuse a subject frame of the same kind",
            range.first(),
        ));
    }
    Ok(())
}

fn validate_term_reuses(
    term: &TermExpression,
    bindings: &[StateRuleBinding],
) -> Result<(), SyntaxError> {
    // A result may write the computation and map remainders as terms (the
    // variables `Tail:K` and `Rest:Map`); the configuration and instance
    // remainders bind no variable.
    for node in term.nodes() {
        if let TermNode::Reference(path) = node
            && let Some(name) = bare_ident(path)
            && let Some(binding) = bindings.iter().find(|binding| binding.name == *name)
        {
            match binding.kind {
                StateRuleBindingKind::ConfigurationFrame => {
                    return Err(body_error(CONFIGURATION_REMAINDER_IN_RESULT, name.span()));
                }
                StateRuleBindingKind::InstancesFrame => {
                    return Err(body_error(INSTANCES_REMAINDER_IN_RESULT, name.span()));
                }
                StateRuleBindingKind::Term
                | StateRuleBindingKind::KSequenceFrame
                | StateRuleBindingKind::MapFrame => {}
            }
        }
    }
    Ok(())
}

/// The configuration remainder written as a result term.
const CONFIGURATION_REMAINDER_IN_RESULT: &str = "this name is the remainder of the configuration: it stands for the cells this rule leaves out, which K completes from the declaration, so it is not a term a result can write";

/// A collection's instance remainder written as a result term.
const INSTANCES_REMAINDER_IN_RESULT: &str = "this name is the remainder of a collection's instances: it stands for the instances this rule leaves out, so it is not a term a result can write";

/// The configuration remainder named in a condition.
const CONFIGURATION_REMAINDER_IN_CONDITION: &str = "this name is the remainder of the configuration: it stands for the cells this rule leaves out, which K completes from the declaration, so it is not a term a condition can test";

/// A collection's instance remainder named in a condition.
const INSTANCES_REMAINDER_IN_CONDITION: &str = "this name is the remainder of a collection's instances: it stands for the instances this rule leaves out, which stay as they are, so it is not a term a condition can test";

/// A condition sees the variables the rule's left side binds: its term
/// binders and its computation and map remainders. The configuration and
/// instance remainders bind no variable, so a condition cannot name them.
fn validate_condition_reuses(
    term: &TermExpression,
    bindings: &[StateRuleBinding],
) -> Result<(), SyntaxError> {
    for node in term.nodes() {
        if let TermNode::Reference(path) = node
            && let Some(name) = bare_ident(path)
            && let Some(binding) = bindings.iter().find(|binding| binding.name == *name)
        {
            match binding.kind {
                StateRuleBindingKind::ConfigurationFrame => {
                    return Err(body_error(
                        CONFIGURATION_REMAINDER_IN_CONDITION,
                        name.span(),
                    ));
                }
                StateRuleBindingKind::InstancesFrame => {
                    return Err(body_error(INSTANCES_REMAINDER_IN_CONDITION, name.span()));
                }
                StateRuleBindingKind::Term
                | StateRuleBindingKind::KSequenceFrame
                | StateRuleBindingKind::MapFrame => {}
            }
        }
    }
    Ok(())
}

/// Keys a `cells!` expression's own nodes under `side`'s roles, then each
/// entry's state. The cells are keyed as part of the rule: the caller clears
/// their keys first.
pub(crate) fn allocate_cells_keys(
    keys: &mut KeyAllocator,
    cells: &mut CellsExpression,
    side: RuleSide,
) -> Result<(), SyntaxError> {
    cells.allocate_keys(keys, StatePosition::Rule(side))?;
    for entry in cells.entries_mut() {
        allocate_state_term_keys(keys, entry.value_mut(), side)?;
    }
    Ok(())
}

/// Keys a state's own nodes under `side`'s roles, then the terms and states
/// inside it.
fn allocate_state_term_keys(
    keys: &mut KeyAllocator,
    term: &mut StateTerm,
    side: RuleSide,
) -> Result<(), SyntaxError> {
    let position = StatePosition::Rule(side);
    match term {
        StateTerm::Present(inner) => allocate_state_term_keys(keys, inner, side),
        StateTerm::Absent(_) => Ok(()),
        StateTerm::Instances(list) => {
            // The instance, child-field, and rest roles each count in
            // traversal order; the children's own keys follow.
            list.allocate_keys(keys, position)?;
            for nested in list.nested_states_mut() {
                allocate_state_term_keys(keys, nested, side)?;
            }
            Ok(())
        }
        StateTerm::Term(term) | StateTerm::Group(term) => allocate_term_keys(keys, term, side),
        StateTerm::KSequence(sequence) => {
            sequence.allocate_keys(keys, position)?;
            for item in sequence.items_mut() {
                allocate_term_keys(keys, item, side)?;
            }
            Ok(())
        }
        StateTerm::Map(map) => {
            map.allocate_keys(keys, position)?;
            for term in map.terms_mut() {
                allocate_term_keys(keys, term, side)?;
            }
            Ok(())
        }
    }
}

/// Keys a cell term's application head, reference, and literal nodes, its
/// record field names, and, on the left, its wildcards.
fn allocate_term_keys(
    keys: &mut KeyAllocator,
    term: &mut TermExpression,
    side: RuleSide,
) -> Result<(), SyntaxError> {
    let (application_role, reference_role, literal_role, field_role) = match side {
        RuleSide::Left => (
            ProvenanceRole::RuleLeftApplicationHead,
            ProvenanceRole::RuleLeftReference,
            ProvenanceRole::RuleLeftLiteral,
            ProvenanceRole::RuleLeftRecordFieldName,
        ),
        RuleSide::Right => (
            ProvenanceRole::RuleRightApplicationHead,
            ProvenanceRole::RuleRightReference,
            ProvenanceRole::RuleRightLiteral,
            ProvenanceRole::RuleRightRecordFieldName,
        ),
    };
    let (nodes, tree, term_keys) = term.keying();
    crate::rule::allocate_term_node_keys(
        keys,
        nodes,
        term_keys,
        application_role,
        reference_role,
        literal_role,
    )?;
    allocate_record_field_keys(keys, tree, term_keys, field_role)?;
    if matches!(side, RuleSide::Left) {
        crate::rule::allocate_wildcard_keys(
            keys,
            tree,
            term_keys,
            ProvenanceRole::RuleLeftWildcard,
        )?;
    }
    Ok(())
}

/// Why a candidate's node has a key: its sentence was keyed when it was
/// parsed.
const KEYED: &str = "a configuration rule is keyed when it is parsed";

/// Keys each binding's explicit sort, as the binder list types it.
fn allocate_binding_sort_keys(
    keys: &mut KeyAllocator,
    bindings: &mut [StateRuleBinding],
) -> Result<(), SyntaxError> {
    for binding in bindings {
        if let Some(sort) = &binding.sort {
            binding.sort_key = Some(keys.key(
                ProvenanceRole::RuleBindingType,
                TokenRange::for_tokens(sort.sort())?,
            )?);
        }
    }
    Ok(())
}

/// A candidate for each binding's explicit sort.
fn binding_sort_candidates(
    bindings: &[StateRuleBinding],
) -> Vec<ReferenceCandidate<StateRuleReferenceKind>> {
    bindings
        .iter()
        .filter_map(|binding| {
            let sort = binding.term_sort()?;
            Some(ReferenceCandidate {
                key: binding.sort_key.clone().expect(KEYED),
                path: sort.sort().clone(),
                kind: StateRuleReferenceKind::BindingSort,
            })
        })
        .collect()
}

/// Pushes a candidate for each cell wrapper of `cells`, and for each
/// application head and nonbinding reference of its terms, keyed as the
/// rule keyed the node.
fn append_cells_candidates(
    cells: &CellsExpression,
    bindings: &[StateRuleBinding],
    output: &mut Vec<ReferenceCandidate<StateRuleReferenceKind>>,
) {
    for entry in cells.entries() {
        if let Some(wrapper) = entry.wrapper() {
            output.push(ReferenceCandidate {
                key: entry.wrapper_key().expect(KEYED).clone(),
                path: wrapper.clone(),
                kind: StateRuleReferenceKind::CellWrapper,
            });
        }
        for term in entry.value().terms() {
            append_term_candidates(term, bindings, output);
        }
    }
}

fn append_term_candidates(
    term: &TermExpression,
    bindings: &[StateRuleBinding],
    output: &mut Vec<ReferenceCandidate<StateRuleReferenceKind>>,
) {
    for (index, node) in term.nodes().iter().enumerate() {
        let (path, kind) = match node {
            TermNode::ApplicationHead(path) => (path, StateRuleReferenceKind::ApplicationHead),
            TermNode::Reference(path) => {
                let bound = bare_ident(path).is_some_and(|candidate| {
                    bindings.iter().any(|binding| {
                        binding.name == *candidate && binding.kind == StateRuleBindingKind::Term
                    })
                });
                if bound {
                    continue;
                }
                (path, StateRuleReferenceKind::Reference)
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
        output.push(ReferenceCandidate {
            key: term.keys().node(index).first().expect(KEYED).clone(),
            path: path.clone(),
            kind,
        });
    }
}

fn map_terms(map: &MapExpression) -> Vec<&TermExpression> {
    match map.body() {
        MapBody::Empty { .. } => Vec::new(),
        MapBody::Items { items, .. } => items
            .iter()
            .flat_map(|item| [item.key(), item.value()])
            .collect(),
        MapBody::Update { base, key, value } => vec![base, key, value],
    }
}

fn helper_name(attribute: &Attribute) -> Option<&Ident> {
    attribute
        .path()
        .segments
        .last()
        .map(|segment| &segment.ident)
}

fn helper_payload(attribute: &Attribute, name: &str) -> Result<TokenStream, SyntaxError> {
    let Meta::List(list) = &attribute.meta else {
        return Err(signature_error(
            "claim helpers require parenthesized payloads",
            attribute.span(),
        ));
    };
    if list.tokens.is_empty() {
        return Err(signature_error(
            "claim helper payload must not be empty",
            attribute.span(),
        ));
    }
    let _ = name;
    Ok(list.tokens.clone())
}

fn take_exists_helper(
    attributes: &mut Vec<Attribute>,
) -> Result<Option<ExistsAttribute>, SyntaxError> {
    let mut found = None;
    let mut retained = Vec::with_capacity(attributes.len());
    for attribute in std::mem::take(attributes) {
        if helper_name(&attribute).is_some_and(|name| name == "exists") {
            if found.is_some() {
                return Err(signature_error(
                    "a claim may declare only one `exists` helper",
                    attribute.span(),
                ));
            }
            found = Some(ExistsAttribute::parse_tokens(helper_payload(
                &attribute, "exists",
            )?)?);
        } else {
            retained.push(attribute);
        }
    }
    *attributes = retained;
    Ok(found)
}

fn take_ensures_helper(
    attributes: &mut Vec<Attribute>,
) -> Result<Option<ClaimEnsures>, SyntaxError> {
    let mut found = None;
    let mut retained = Vec::with_capacity(attributes.len());
    for attribute in std::mem::take(attributes) {
        if helper_name(&attribute).is_some_and(|name| name == "ensures") {
            if found.is_some() {
                return Err(signature_error(
                    "a claim may declare only one `ensures` helper",
                    attribute.span(),
                ));
            }
            let payload =
                crate::parse::strip_trailing_comma(helper_payload(&attribute, "ensures")?);
            crate::term::reject_pattern_alias(&payload)?;
            let expression: Expr = syn::parse2(payload)?;
            found = Some(ClaimEnsures {
                term: TermExpression::from_expression(expression)?,
            });
        } else {
            retained.push(attribute);
        }
    }
    *attributes = retained;
    Ok(found)
}

/// Keys the lexeme, sort-test, `name @ ..`, `A | B`, `k::matches!`, `let`,
/// `ml::exists`, and turbofish nodes of a claim's ensures condition, whose
/// ordinals continue after the rule's subject, result, and condition (the
/// rule's own keys number those).
fn allocate_claim_ensures_keys(
    keys: &mut KeyAllocator,
    nodes: &[TermNode],
    term_keys: &mut TermKeys,
) -> Result<(), SyntaxError> {
    allocate_lexeme_keys(keys, nodes, term_keys)?;
    allocate_sort_test_keys(keys, nodes, term_keys)?;
    crate::term::allocate_pattern_as_keys(keys, nodes, term_keys)?;
    crate::term::allocate_pattern_or_keys(keys, nodes, term_keys)?;
    crate::term::allocate_matches_keys(keys, nodes, term_keys)?;
    crate::term::allocate_let_keys(keys, nodes, term_keys)?;
    crate::term::allocate_ml_binder_keys(keys, nodes, term_keys)?;
    crate::term::allocate_application_instance_keys(keys, nodes, term_keys)
}

fn claim_terms<'a>(
    rule: &'a StateRuleItem,
    ensures: Option<&'a ClaimEnsures>,
) -> Vec<&'a TermExpression> {
    let mut output = Vec::new();
    append_cells_terms(rule.subject(), &mut output);
    if let Some(result) = rule.result() {
        append_cells_terms(result, &mut output);
    }
    if let Some(requires) = rule.requires() {
        output.push(requires.term());
    }
    if let Some(ensures) = ensures {
        output.push(ensures.term());
    }
    output
}

fn append_cells_terms<'a>(cells: &'a CellsExpression, output: &mut Vec<&'a TermExpression>) {
    for entry in cells.entries() {
        append_state_terms(entry.value(), output);
    }
}

fn append_state_terms<'a>(state: &'a StateTerm, output: &mut Vec<&'a TermExpression>) {
    match state {
        StateTerm::Term(term) | StateTerm::Group(term) => output.push(term),
        StateTerm::KSequence(sequence) => output.extend(sequence.items().iter()),
        StateTerm::Map(map) => output.extend(map_terms(map)),
        StateTerm::Present(_) | StateTerm::Absent(_) | StateTerm::Instances(_) => {
            for nested in state.nested_states() {
                append_state_terms(nested, output);
            }
        }
    }
}

/// Keys the claim-only nodes (`k::id!`, `k::bytes!`, `k::anonymous!`,
/// `k::or_bool!`) of a claim's terms, each kind numbered in one sequence in
/// the order of `terms`, which is the order expansion visits them.
pub(crate) fn allocate_claim_node_keys<'a, K: std::borrow::BorrowMut<TermKeys>>(
    keys: &mut KeyAllocator,
    terms: impl IntoIterator<Item = (&'a [TermNode], K)>,
) -> Result<(), SyntaxError> {
    for (nodes, mut term_keys) in terms {
        let term_keys = term_keys.borrow_mut();
        for (index, node) in nodes.iter().enumerate() {
            match node {
                TermNode::IdToken(literal) => {
                    let key = keys.key(
                        ProvenanceRole::ClaimIdToken,
                        TokenRange::for_tokens(literal)?,
                    )?;
                    term_keys.push_node(index, key);
                }
                TermNode::BytesToken(literal) => {
                    let key = keys.key(
                        ProvenanceRole::ClaimBytesToken,
                        TokenRange::for_tokens(literal)?,
                    )?;
                    term_keys.push_node(index, key);
                }
                TermNode::Anonymous { sort, spelling } => {
                    let spelling = TokenRange::for_tokens(spelling)?;
                    term_keys.push_node(index, keys.key(ProvenanceRole::ClaimAnonymous, spelling)?);
                    let sort = keys.key(
                        ProvenanceRole::ClaimAnonymousSort,
                        TokenRange::for_tokens(sort)?,
                    )?;
                    term_keys.push_node(index, sort);
                    let spelling = keys.key(ProvenanceRole::ClaimAnonymousSpelling, spelling)?;
                    term_keys.push_node(index, spelling);
                }
                TermNode::OrBool(range) => {
                    term_keys.push_node(index, keys.key(ProvenanceRole::ClaimOrBool, *range)?);
                }
                TermNode::ApplicationHead(_)
                | TermNode::Reference(_)
                | TermNode::Literal(_)
                | TermNode::Lexeme { .. }
                | TermNode::SortTest { .. }
                | TermNode::As { .. }
                | TermNode::Or(_)
                | TermNode::Matches(_)
                | TermNode::MatchesWildcard(_)
                | TermNode::Let { .. }
                | TermNode::Closure { .. }
                | TermNode::LetWildcard(_)
                | TermNode::Rewrite { .. } => {}
            }
        }
    }
    Ok(())
}

fn body_error(reason: &'static str, span: proc_macro2::Span) -> SyntaxError {
    SyntaxError::new(SyntaxErrorKind::UnsupportedRuleBody { reason }, span)
}

#[cfg(test)]
impl FunctionContext {
    /// Records the keys of the parameter's pattern and configuration type,
    /// then of its cells and their states.
    pub(crate) fn keyed_nodes(
        &self,
        nodes: &mut crate::keyed_nodes::KeyedNodes,
    ) -> Result<(), SyntaxError> {
        nodes.push_tokens(self.key.as_ref(), &self.pattern_macro)?;
        nodes.push_tokens(self.type_key.as_ref(), &self.configuration_type)?;
        self.pattern.keyed_nodes(nodes)?;
        self.pattern.keyed_values(nodes)
    }
}

#[cfg(test)]
impl StateRuleBinding {
    /// Records the keys of the binding's sort and, in a claim, of the
    /// universal binder and its name, at the name, and of its sort.
    fn keyed_nodes(&self, nodes: &mut crate::keyed_nodes::KeyedNodes) -> Result<(), SyntaxError> {
        if let Some(sort) = &self.sort {
            nodes.push_tokens(self.sort_key.as_ref(), sort.sort())?;
            nodes.push_tokens(self.binder_sort_key.as_ref(), sort.sort())?;
        }
        nodes.push_tokens(self.universal_key.as_ref(), &self.name)?;
        nodes.push_tokens(self.binder_name_key.as_ref(), &self.name)
    }
}

#[cfg(test)]
impl StateRuleItem {
    /// Records the rule's keyed nodes: its declaration, subject and result
    /// shells and types, its bindings, its cells and their states, then its
    /// conditions and binders.
    pub(crate) fn keyed_nodes(
        &self,
        nodes: &mut crate::keyed_nodes::KeyedNodes,
    ) -> Result<(), SyntaxError> {
        nodes.push_tokens(self.declaration_key.as_ref(), &self.item.sig.ident)?;
        nodes.push_tokens(self.pattern_key.as_ref(), &self.subject_macro)?;
        nodes.push_tokens(self.type_key.as_ref(), &self.subject_type)?;
        for binding in &self.bindings {
            binding.keyed_nodes(nodes)?;
        }
        self.subject.keyed_nodes(nodes)?;
        self.subject.keyed_values(nodes)?;
        if let Some(result) = &self.result {
            nodes.push_tokens(result.type_key.as_ref(), &result.result_type)?;
            nodes.push_tokens(result.key.as_ref(), &result.result_macro)?;
            result.result.keyed_nodes(nodes)?;
            result.result.keyed_values(nodes)?;
        }
        if let Some(requires) = &self.requires {
            requires.term().keyed_nodes(nodes)?;
        }
        self.existentials.keyed_nodes(nodes)
    }
}

#[cfg(test)]
impl StateClaimItem {
    /// Records the claim's keyed nodes: its rule's, then its existential
    /// binders and its ensures condition.
    pub(crate) fn keyed_nodes(
        &self,
        nodes: &mut crate::keyed_nodes::KeyedNodes,
    ) -> Result<(), SyntaxError> {
        self.rule.keyed_nodes(nodes)?;
        for binder in self.existentials() {
            binder.keyed_nodes(nodes)?;
        }
        if let Some(ensures) = &self.ensures {
            ensures.term.keyed_nodes(nodes)?;
        }
        Ok(())
    }
}

#[cfg(test)]
impl StateContextAliasItem {
    /// Records the alias's keyed nodes: its pattern and type, its bindings'
    /// sorts, then its cells and their states.
    pub(crate) fn keyed_nodes(
        &self,
        nodes: &mut crate::keyed_nodes::KeyedNodes,
    ) -> Result<(), SyntaxError> {
        nodes.push_tokens(self.pattern_key.as_ref(), &self.pattern_macro)?;
        nodes.push_tokens(self.type_key.as_ref(), &self.configuration_type)?;
        for binding in &self.bindings {
            binding.keyed_nodes(nodes)?;
        }
        self.pattern.keyed_nodes(nodes)?;
        self.pattern.keyed_values(nodes)
    }

    /// Records the key of the fn's name, which the alias's descriptor
    /// anchors.
    pub(crate) fn keyed_declaration_nodes(
        &self,
        nodes: &mut crate::keyed_nodes::KeyedNodes,
    ) -> Result<(), SyntaxError> {
        nodes.push_tokens(self.declaration_key.as_ref(), &self.item.sig.ident)
    }
}
