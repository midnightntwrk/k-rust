use krs_ir::ProvenanceKey;
use proc_macro2::TokenStream;
use syn::spanned::Spanned;
use syn::{
    Attribute, Expr, FnArg, Ident, ItemFn, Macro, Meta, Pat, PatMacro, Path, ReturnType, Stmt, Type,
};

use crate::ReferenceCandidate;
use crate::attribute::{ClaimBinder, ExistsAttribute};
use crate::parse::{
    KrsSyntax, ProvenanceAnchors, checked_ordinal, unsupported_rule_pattern as pattern_error,
    unsupported_rule_signature as signature_error,
};
use crate::path::is_plain_path;
use crate::provenance::RuleSide;
use crate::rule::{RuleCondition, take_requires_helper};
use crate::term::push_record_field_anchors;
use crate::term_sort::{TermSort, parse_readable_sort, parse_term_sort};
use crate::{
    CellsExpression, MapBody, MapExpression, ProvenanceAnchor, ProvenanceRole, RuleRole,
    StateMacroRemainder, StateTerm, SyntaxError, SyntaxErrorKind, TermExpression, TermLiteral,
    TermNode, TokenRange, parse_cells_expression, parse_cells_pattern,
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
}

/// One typed or structurally classified configuration-rule binding.
#[derive(Clone, Debug)]
pub struct StateRuleBinding {
    name: Ident,
    kind: StateRuleBindingKind,
    sort: Option<TermSort>,
}

impl StateRuleBinding {
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
    result_macro: Macro,
    result_type: Path,
    result: CellsExpression,
    bindings: Vec<StateRuleBinding>,
    requires: Option<RuleCondition>,
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
        let rule = StateRuleItem::from_item(item)?;
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
        Ok(Self {
            rule,
            exists,
            ensures,
        })
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
    /// Returns claim-only parser-owned anchors.
    ///
    /// # Errors
    ///
    /// Returns an error when an authored endpoint or provenance occurrence
    /// cannot be represented.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut output = self.rule.provenance()?;
        output.retain(|anchor| anchor.role() != ProvenanceRole::RuleDeclaration);
        output.push(ProvenanceAnchor::new(
            ProvenanceRole::ClaimDeclaration,
            0,
            TokenRange::for_tokens(&self.rule.item.sig.ident)?,
        ));
        let mut universal_ordinal = 0_u32;
        for binding in &self.rule.bindings {
            if binding.kind == StateRuleBindingKind::Term {
                output.push(ProvenanceAnchor::new(
                    ProvenanceRole::ClaimUniversalBinder,
                    universal_ordinal,
                    TokenRange::for_tokens(&binding.name)?,
                ));
                output.push(ProvenanceAnchor::new(
                    ProvenanceRole::ClaimBinderName,
                    universal_ordinal,
                    TokenRange::for_tokens(&binding.name)?,
                ));
                let Some(sort) = binding.term_sort() else {
                    return Err(signature_error(
                        "term claim binding is missing its sort",
                        binding.name.span(),
                    ));
                };
                output.push(ProvenanceAnchor::new(
                    ProvenanceRole::ClaimBinderSort,
                    universal_ordinal,
                    TokenRange::for_tokens(sort.sort())?,
                ));
                universal_ordinal = universal_ordinal.checked_add(1).ok_or_else(|| {
                    signature_error("too many universal claim binders", binding.name.span())
                })?;
            }
        }
        if let Some(exists) = &self.exists {
            let mut anchors = exists.provenance()?;
            anchors.retain(|anchor| {
                !matches!(
                    anchor.role(),
                    ProvenanceRole::ClaimBinderName | ProvenanceRole::ClaimBinderSort
                )
            });
            output.extend(anchors);
            for (index, binder) in exists.binders().iter().enumerate() {
                let ordinal = universal_ordinal
                    .checked_add(u32::try_from(index).map_err(|_| {
                        signature_error("too many existential binders", binder.name().span())
                    })?)
                    .ok_or_else(|| {
                        signature_error("too many claim binders", binder.name().span())
                    })?;
                output.push(ProvenanceAnchor::new(
                    ProvenanceRole::ClaimBinderName,
                    ordinal,
                    TokenRange::for_tokens(binder.name())?,
                ));
                output.push(ProvenanceAnchor::new(
                    ProvenanceRole::ClaimBinderSort,
                    ordinal,
                    TokenRange::for_tokens(binder.sort())?,
                ));
            }
        }
        if let Some(ensures) = &self.ensures {
            output.extend(ensures.term.provenance_with_roles(
                ProvenanceRole::ClaimEnsures,
                ProvenanceRole::ClaimEnsuresPath,
            )?);
            output.extend(
                ensures
                    .term
                    .full_provenance_with_roles(
                        ProvenanceRole::ClaimEnsures,
                        ProvenanceRole::ClaimEnsuresApplicationHead,
                        ProvenanceRole::ClaimEnsuresReference,
                        ProvenanceRole::ClaimEnsuresLiteral,
                        ProvenanceRole::ClaimEnsuresRecordFieldName,
                    )?
                    .into_iter()
                    .skip(1),
            );
        }
        append_claim_special_anchors(&self.rule, self.ensures.as_ref(), &mut output)?;
        Ok(output)
    }
    /// Returns claim-only sort paths needing rustc/collector resolution.
    ///
    /// # Errors
    ///
    /// Returns an occurrence-overflow error if claim sort provenance cannot be
    /// represented.
    pub fn sort_candidates(&self) -> Result<Vec<ClaimSortCandidate>, SyntaxError> {
        let mut output = self
            .existentials()
            .iter()
            .enumerate()
            .map(|(index, binder)| {
                Ok(ClaimSortCandidate {
                    key: key(
                        ProvenanceRole::ClaimBinderSort,
                        u32::try_from(index).map_err(|_| {
                            signature_error("too many existential binders", binder.name().span())
                        })?,
                    ),
                    path: binder.sort().clone(),
                })
            })
            .collect::<Result<Vec<_>, SyntaxError>>()?;
        let mut ordinal = 0_u32;
        for term in claim_terms(&self.rule, self.ensures.as_ref()) {
            for node in term.nodes() {
                if let TermNode::Anonymous { sort, .. } = node {
                    output.push(ClaimSortCandidate {
                        key: key(ProvenanceRole::ClaimAnonymousSort, ordinal),
                        path: sort.clone(),
                    });
                    ordinal = ordinal.checked_add(1).ok_or_else(|| {
                        signature_error("too many anonymous occurrences", sort.span())
                    })?;
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
            return Err(signature_error(
                "typed term parameters must exactly match non-HERE term bindings",
                item.sig.span(),
            ));
        }
        for ((_, sort), binding) in
            typed.into_iter().zip(bindings.iter_mut().filter(|binding| {
                binding.kind == StateRuleBindingKind::Term && binding.name != *here
            }))
        {
            binding.sort = Some(sort);
        }
        Ok(Self {
            item,
            pattern_macro,
            configuration_type,
            pattern,
            bindings,
            here: here.clone(),
        })
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

    /// Returns parser-owned pattern/type/cell/frame origins.
    ///
    /// # Errors
    ///
    /// Returns endpoint or ordinal overflow failures only.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut output = vec![
            ProvenanceAnchor::new(
                ProvenanceRole::RulePattern,
                0,
                TokenRange::for_tokens(&self.pattern_macro)?,
            ),
            ProvenanceAnchor::new(
                ProvenanceRole::RuleType,
                0,
                TokenRange::for_tokens(&self.configuration_type)?,
            ),
        ];
        for (ordinal, sort) in self
            .bindings
            .iter()
            .filter_map(StateRuleBinding::term_sort)
            .enumerate()
        {
            output.push(ProvenanceAnchor::new(
                ProvenanceRole::RuleBindingType,
                checked_ordinal(ordinal, ProvenanceRole::RuleBindingType, sort.sort().span())?,
                TokenRange::for_tokens(sort.sort())?,
            ));
        }
        append_cells_provenance(&self.pattern, RuleSide::Left, &mut output)?;
        Ok(output)
    }

    /// Returns rustc-resolvable paths with parser-owned keys.
    ///
    /// # Errors
    ///
    /// Returns occurrence overflow failures only.
    pub fn reference_candidates(
        &self,
    ) -> Result<Vec<ReferenceCandidate<StateRuleReferenceKind>>, SyntaxError> {
        let mut output = self
            .bindings
            .iter()
            .filter_map(StateRuleBinding::term_sort)
            .enumerate()
            .map(|(ordinal, sort)| {
                Ok(ReferenceCandidate {
                    key: key(
                        ProvenanceRole::RuleBindingType,
                        checked_ordinal(
                            ordinal,
                            ProvenanceRole::RuleBindingType,
                            sort.sort().span(),
                        )?,
                    ),
                    path: sort.sort().clone(),
                    kind: StateRuleReferenceKind::BindingSort,
                })
            })
            .collect::<Result<Vec<_>, SyntaxError>>()?;
        output.push(ReferenceCandidate {
            key: key(ProvenanceRole::RuleType, 0),
            path: self.configuration_type.clone(),
            kind: StateRuleReferenceKind::Configuration,
        });
        append_cells_candidates(&self.pattern, RuleSide::Left, &self.bindings, &mut output)?;
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
    pub fn from_item(mut item: ItemFn) -> Result<Self, SyntaxError> {
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

        let ReturnType::Type(_, result_type) = &item.sig.output else {
            return Err(signature_error(
                "a configuration rule must declare its configuration result type",
                item.sig.ident.span(),
            ));
        };
        let result_type = parse_configuration_type(result_type)?;
        let result_macro = parse_result_macro(&item)?;
        validate_cells_path(&result_macro.path, result_macro.span())?;
        let result = parse_cells_expression(result_macro.tokens.clone())?;

        let typed_bindings = parse_typed_bindings(&item)?;
        let mut bindings = Vec::new();
        collect_cells_bindings(&subject, &mut bindings)?;
        attach_typed_binding_sorts(&mut bindings, typed_bindings)?;
        validate_result_reuses(&result, &bindings)?;
        let requires = take_requires_helper(&mut item.attrs)?;
        Ok(Self {
            item,
            subject_macro,
            subject_type,
            subject,
            result_macro,
            result_type,
            result,
            bindings,
            requires,
        })
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

    /// Returns the result configuration type path.
    #[must_use]
    pub const fn result_type(&self) -> &Path {
        &self.result_type
    }

    /// Returns the complete result `cells!` AST.
    #[must_use]
    pub const fn result(&self) -> &CellsExpression {
        &self.result
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

    /// Returns one collision-free descriptor-wide provenance table.
    ///
    /// # Errors
    ///
    /// Returns endpoint or ordinal-overflow errors only.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        let mut output = vec![
            ProvenanceAnchor::new(
                ProvenanceRole::RuleDeclaration,
                0,
                TokenRange::for_tokens(&self.item.sig.ident)?,
            ),
            ProvenanceAnchor::new(
                ProvenanceRole::RulePattern,
                0,
                TokenRange::for_tokens(&self.subject_macro)?,
            ),
            ProvenanceAnchor::new(
                ProvenanceRole::RuleType,
                0,
                TokenRange::for_tokens(&self.subject_type)?,
            ),
            ProvenanceAnchor::new(
                ProvenanceRole::RuleResultType,
                0,
                TokenRange::for_tokens(&self.result_type)?,
            ),
            ProvenanceAnchor::new(
                ProvenanceRole::RuleResult,
                0,
                TokenRange::for_tokens(&self.result_macro)?,
            ),
        ];
        for (ordinal, sort) in self
            .bindings
            .iter()
            .filter_map(StateRuleBinding::term_sort)
            .enumerate()
        {
            output.push(ProvenanceAnchor::new(
                ProvenanceRole::RuleBindingType,
                checked_ordinal(ordinal, ProvenanceRole::RuleBindingType, sort.sort().span())?,
                TokenRange::for_tokens(sort.sort())?,
            ));
        }
        append_cells_provenance(&self.subject, RuleSide::Left, &mut output)?;
        append_cells_provenance(&self.result, RuleSide::Right, &mut output)?;
        if let Some(requires) = &self.requires {
            output.extend(requires.provenance()?);
        }
        Ok(output)
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
    /// Returns an occurrence-overflow error for pathological inputs.
    pub fn reference_candidates(
        &self,
    ) -> Result<Vec<ReferenceCandidate<StateRuleReferenceKind>>, SyntaxError> {
        let mut output = self
            .bindings
            .iter()
            .filter_map(StateRuleBinding::term_sort)
            .enumerate()
            .map(|(ordinal, sort)| {
                Ok(ReferenceCandidate {
                    key: key(
                        ProvenanceRole::RuleBindingType,
                        checked_ordinal(
                            ordinal,
                            ProvenanceRole::RuleBindingType,
                            sort.sort().span(),
                        )?,
                    ),
                    path: sort.sort().clone(),
                    kind: StateRuleReferenceKind::BindingSort,
                })
            })
            .collect::<Result<Vec<_>, SyntaxError>>()?;
        output.extend([
            ReferenceCandidate {
                key: key(ProvenanceRole::RuleType, 0),
                path: self.subject_type.clone(),
                kind: StateRuleReferenceKind::Configuration,
            },
            ReferenceCandidate {
                key: key(ProvenanceRole::RuleResultType, 0),
                path: self.result_type.clone(),
                kind: StateRuleReferenceKind::Configuration,
            },
        ]);
        append_cells_candidates(&self.subject, RuleSide::Left, &self.bindings, &mut output)?;
        append_cells_candidates(&self.result, RuleSide::Right, &self.bindings, &mut output)?;
        Ok(output)
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
        let sort = parse_term_sort(authored_type.clone())
            .or_else(|_| parse_readable_sort(authored_type))?;
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
        StateTerm::Term(term) => count_term_binding_occurrences(term, binding),
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
        .filter(
            |node| matches!(node, TermNode::Reference(path) if bare_ident(path) == Some(binding)),
        )
        .count()
}

fn collect_state_term_bindings(
    term: &StateTerm,
    output: &mut Vec<StateRuleBinding>,
) -> Result<(), SyntaxError> {
    match term {
        StateTerm::Term(term) => collect_term_bindings(term, output),
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
        StateTerm::Map(map) => match map.body() {
            MapBody::Empty { .. } => Ok(()),
            MapBody::Items { items, remainder } => {
                for item in items {
                    collect_term_bindings(item.key(), output)?;
                    collect_term_bindings(item.value(), output)?;
                }
                collect_remainder_binding(remainder, StateRuleBindingKind::MapFrame, output)
            }
            MapBody::Update { .. } => unreachable!("map updates are rejected in patterns"),
        },
    }
}

fn collect_term_bindings(
    term: &TermExpression,
    output: &mut Vec<StateRuleBinding>,
) -> Result<(), SyntaxError> {
    for node in term.nodes() {
        if let TermNode::Reference(path) = node
            && let Some(binding) = bare_ident(path)
        {
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
    });
    Ok(())
}

fn attach_typed_binding_sorts(
    bindings: &mut [StateRuleBinding],
    typed: Vec<(Ident, TermSort)>,
) -> Result<(), SyntaxError> {
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
        return Err(signature_error(
            "typed term parameters must exactly match subject term bindings in first-occurrence order",
            span,
        ));
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
        match entry.value() {
            StateTerm::Term(term) => validate_term_reuses(term, bindings)?,
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
    for node in term.nodes() {
        if let TermNode::Reference(path) = node
            && let Some(name) = bare_ident(path)
            && let Some(binding) = bindings.iter().find(|binding| binding.name == *name)
            && binding.kind != StateRuleBindingKind::Term
        {
            return Err(body_error(
                "a structural frame cannot be reused as an object-language term",
                name.span(),
            ));
        }
    }
    Ok(())
}

fn append_cells_provenance(
    cells: &CellsExpression,
    side: RuleSide,
    output: &mut Vec<ProvenanceAnchor>,
) -> Result<(), SyntaxError> {
    let mut counters = ProvenanceAnchors::default();
    append_remapped(cells.provenance()?, side, &mut counters, output)?;
    for entry in cells.entries() {
        append_state_term_provenance(entry.value(), side, &mut counters, output)?;
    }
    Ok(())
}

fn append_state_term_provenance(
    term: &StateTerm,
    side: RuleSide,
    counters: &mut ProvenanceAnchors,
    output: &mut Vec<ProvenanceAnchor>,
) -> Result<(), SyntaxError> {
    match term {
        StateTerm::Term(term) => append_term_provenance(term, side, counters, output),
        StateTerm::KSequence(sequence) => {
            append_remapped(sequence.provenance()?, side, counters, output)?;
            for item in sequence.items() {
                append_term_provenance(item, side, counters, output)?;
            }
            Ok(())
        }
        StateTerm::Map(map) => {
            append_remapped(map.provenance()?, side, counters, output)?;
            for term in map_terms(map) {
                append_term_provenance(term, side, counters, output)?;
            }
            Ok(())
        }
    }
}

fn append_term_provenance(
    term: &TermExpression,
    side: RuleSide,
    counters: &mut ProvenanceAnchors,
    output: &mut Vec<ProvenanceAnchor>,
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
    for node in term.nodes() {
        let role = match node {
            TermNode::ApplicationHead(_) => application_role,
            TermNode::Reference(_) => reference_role,
            TermNode::Literal(_) => literal_role,
            TermNode::IdToken(_)
            | TermNode::BytesToken(_)
            | TermNode::Anonymous { .. }
            | TermNode::OrBool(_) => continue,
        };
        output.push(ProvenanceAnchor::new(
            role,
            counters.next(role, node_span(node))?,
            node_range(node)?,
        ));
    }
    let mut fields = Vec::new();
    push_record_field_anchors(&mut fields, term.tree(), field_role)?;
    for field in fields {
        output.push(ProvenanceAnchor::new(
            field_role,
            counters.next(field_role, field.range().first())?,
            field.range(),
        ));
    }
    if matches!(side, RuleSide::Left) {
        let mut wildcards = Vec::new();
        term.tree().wildcard_ranges_preorder(&mut wildcards);
        for range in wildcards {
            output.push(ProvenanceAnchor::new(
                ProvenanceRole::RuleLeftWildcard,
                counters.next(ProvenanceRole::RuleLeftWildcard, range.first())?,
                range,
            ));
        }
    }
    Ok(())
}

fn append_remapped(
    anchors: Vec<ProvenanceAnchor>,
    side: RuleSide,
    counters: &mut ProvenanceAnchors,
    output: &mut Vec<ProvenanceAnchor>,
) -> Result<(), SyntaxError> {
    for anchor in anchors {
        let Some(role) = RuleRole::from_standalone(anchor.role()) else {
            continue;
        };
        let role = role.on_side(side);
        output.push(ProvenanceAnchor::new(
            role,
            counters.next(role, anchor.range().first())?,
            anchor.range(),
        ));
    }
    Ok(())
}

fn append_cells_candidates(
    cells: &CellsExpression,
    side: RuleSide,
    bindings: &[StateRuleBinding],
    output: &mut Vec<ReferenceCandidate<StateRuleReferenceKind>>,
) -> Result<(), SyntaxError> {
    let mut counters = ProvenanceAnchors::default();
    for entry in cells.entries() {
        let wrapper_role = match side {
            RuleSide::Left => ProvenanceRole::RuleLeftCellsWrapper,
            RuleSide::Right => ProvenanceRole::RuleRightCellsWrapper,
        };
        let ordinal = counters.next(wrapper_role, entry.wrapper().span())?;
        output.push(ReferenceCandidate {
            key: key(wrapper_role, ordinal),
            path: entry.wrapper().clone(),
            kind: StateRuleReferenceKind::CellWrapper,
        });
        append_state_term_candidates(entry.value(), side, bindings, &mut counters, output)?;
    }
    Ok(())
}

fn append_state_term_candidates(
    state: &StateTerm,
    side: RuleSide,
    bindings: &[StateRuleBinding],
    counters: &mut ProvenanceAnchors,
    output: &mut Vec<ReferenceCandidate<StateRuleReferenceKind>>,
) -> Result<(), SyntaxError> {
    match state {
        StateTerm::Term(term) => append_term_candidates(term, side, bindings, counters, output),
        StateTerm::KSequence(sequence) => {
            for term in sequence.items() {
                append_term_candidates(term, side, bindings, counters, output)?;
            }
            Ok(())
        }
        StateTerm::Map(map) => {
            for term in map_terms(map) {
                append_term_candidates(term, side, bindings, counters, output)?;
            }
            Ok(())
        }
    }
}

fn append_term_candidates(
    term: &TermExpression,
    side: RuleSide,
    bindings: &[StateRuleBinding],
    counters: &mut ProvenanceAnchors,
    output: &mut Vec<ReferenceCandidate<StateRuleReferenceKind>>,
) -> Result<(), SyntaxError> {
    let (application_role, reference_role) = match side {
        RuleSide::Left => (
            ProvenanceRole::RuleLeftApplicationHead,
            ProvenanceRole::RuleLeftReference,
        ),
        RuleSide::Right => (
            ProvenanceRole::RuleRightApplicationHead,
            ProvenanceRole::RuleRightReference,
        ),
    };
    for node in term.nodes() {
        match node {
            TermNode::ApplicationHead(path) => {
                let ordinal = counters.next(application_role, path.span())?;
                output.push(ReferenceCandidate {
                    key: key(application_role, ordinal),
                    path: path.clone(),
                    kind: StateRuleReferenceKind::ApplicationHead,
                });
            }
            TermNode::Reference(path) => {
                let ordinal = counters.next(reference_role, path.span())?;
                let bound = bare_ident(path).is_some_and(|candidate| {
                    bindings.iter().any(|binding| {
                        binding.name == *candidate && binding.kind == StateRuleBindingKind::Term
                    })
                });
                if !bound {
                    output.push(ReferenceCandidate {
                        key: key(reference_role, ordinal),
                        path: path.clone(),
                        kind: StateRuleReferenceKind::Reference,
                    });
                }
            }
            TermNode::Literal(_)
            | TermNode::IdToken(_)
            | TermNode::BytesToken(_)
            | TermNode::Anonymous { .. }
            | TermNode::OrBool(_) => {}
        }
    }
    Ok(())
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

fn node_range(node: &TermNode) -> Result<TokenRange, SyntaxError> {
    match node {
        TermNode::ApplicationHead(path) | TermNode::Reference(path) => TokenRange::for_tokens(path),
        TermNode::Literal(TermLiteral::Integer(value)) => TokenRange::for_tokens(value),
        TermNode::Literal(TermLiteral::Boolean(value)) => TokenRange::for_tokens(value),
        TermNode::IdToken(value) => TokenRange::for_tokens(value),
        TermNode::BytesToken(value) => TokenRange::for_tokens(value),
        TermNode::Anonymous { spelling, .. } => TokenRange::for_tokens(spelling),
        TermNode::OrBool(range) => Ok(*range),
    }
}

fn node_span(node: &TermNode) -> proc_macro2::Span {
    match node {
        TermNode::ApplicationHead(path) | TermNode::Reference(path) => path.span(),
        TermNode::Literal(TermLiteral::Integer(value)) => value.span(),
        TermNode::Literal(TermLiteral::Boolean(value)) => value.span(),
        TermNode::IdToken(value) => value.span(),
        TermNode::BytesToken(value) => value.span(),
        TermNode::Anonymous { spelling, .. } => spelling.span(),
        TermNode::OrBool(range) => range.first(),
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
            let expression: Expr = syn::parse2(helper_payload(&attribute, "ensures")?)?;
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

fn claim_terms<'a>(
    rule: &'a StateRuleItem,
    ensures: Option<&'a ClaimEnsures>,
) -> Vec<&'a TermExpression> {
    let mut output = Vec::new();
    append_cells_terms(rule.subject(), &mut output);
    append_cells_terms(rule.result(), &mut output);
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
        match entry.value() {
            StateTerm::Term(term) => output.push(term),
            StateTerm::KSequence(sequence) => output.extend(sequence.items().iter()),
            StateTerm::Map(map) => output.extend(map_terms(map)),
        }
    }
}

fn append_claim_special_anchors(
    rule: &StateRuleItem,
    ensures: Option<&ClaimEnsures>,
    output: &mut Vec<ProvenanceAnchor>,
) -> Result<(), SyntaxError> {
    let mut id_ordinal = 0_u32;
    let mut bytes_ordinal = 0_u32;
    let mut anonymous_ordinal = 0_u32;
    let mut or_ordinal = 0_u32;
    for term in claim_terms(rule, ensures) {
        for node in term.nodes() {
            match node {
                TermNode::IdToken(literal) => {
                    output.push(ProvenanceAnchor::new(
                        ProvenanceRole::ClaimIdToken,
                        id_ordinal,
                        TokenRange::for_tokens(literal)?,
                    ));
                    id_ordinal = id_ordinal
                        .checked_add(1)
                        .ok_or_else(|| signature_error("too many Id tokens", literal.span()))?;
                }
                TermNode::BytesToken(literal) => {
                    output.push(ProvenanceAnchor::new(
                        ProvenanceRole::ClaimBytesToken,
                        bytes_ordinal,
                        TokenRange::for_tokens(literal)?,
                    ));
                    bytes_ordinal = bytes_ordinal
                        .checked_add(1)
                        .ok_or_else(|| signature_error("too many Bytes tokens", literal.span()))?;
                }
                TermNode::Anonymous { sort, spelling } => {
                    output.push(ProvenanceAnchor::new(
                        ProvenanceRole::ClaimAnonymous,
                        anonymous_ordinal,
                        TokenRange::for_tokens(spelling)?,
                    ));
                    output.push(ProvenanceAnchor::new(
                        ProvenanceRole::ClaimAnonymousSort,
                        anonymous_ordinal,
                        TokenRange::for_tokens(sort)?,
                    ));
                    output.push(ProvenanceAnchor::new(
                        ProvenanceRole::ClaimAnonymousSpelling,
                        anonymous_ordinal,
                        TokenRange::for_tokens(spelling)?,
                    ));
                    anonymous_ordinal = anonymous_ordinal.checked_add(1).ok_or_else(|| {
                        signature_error("too many anonymous occurrences", spelling.span())
                    })?;
                }
                TermNode::OrBool(range) => {
                    output.push(ProvenanceAnchor::new(
                        ProvenanceRole::ClaimOrBool,
                        or_ordinal,
                        *range,
                    ));
                    or_ordinal = or_ordinal.checked_add(1).ok_or_else(|| {
                        signature_error("too many Boolean disjunctions", range.first())
                    })?;
                }
                TermNode::ApplicationHead(_) | TermNode::Reference(_) | TermNode::Literal(_) => {}
            }
        }
    }
    Ok(())
}

fn bare_ident(path: &Path) -> Option<&Ident> {
    (path.leading_colon.is_none() && path.segments.len() == 1).then(|| {
        &path
            .segments
            .first()
            .expect("one segment was checked")
            .ident
    })
}

fn key(role: ProvenanceRole, ordinal: u32) -> ProvenanceKey {
    role.key(ordinal)
}

fn body_error(reason: &'static str, span: proc_macro2::Span) -> SyntaxError {
    SyntaxError::new(SyntaxErrorKind::UnsupportedRuleBody { reason }, span)
}
