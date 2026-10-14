//! Transition existentials, fresh binders, and ensures conditions:
//! `#[k::exists]` and `#[k::ensures]` (KF-040) and `#[k::fresh]` (KF-022)
//! after `#[k::rule]`, and the `heat`/`cool` evaluation step of
//! `#[k::rule]` (KF-014).

use crate::ExpandError;
use krs_diagnostic::codes::expand;
use krs_ir::wire::{WireClaimBinder, WireEvaluationStep, WireRuleCondition};
use krs_syntax::{ClaimBinder, ProvenanceRole, RuleExistentials};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{Attribute, Path};

use super::terms::{TermBuilder, TermSide, WireSlots, wire_key, wire_sort_reference};
use super::tokens::{call_site_path, spelling};

/// The wire binders of a transition's existentials and the hidden sort-key
/// functions that let rustc resolve each binder's sort.
pub(super) fn existential_binders(
    existentials: &RuleExistentials,
    facade: &Path,
    nonce: u64,
    cfg: &[Attribute],
    slots: &mut WireSlots,
) -> crate::Result<(Vec<WireClaimBinder>, Vec<TokenStream>)> {
    scoped_binders(
        existentials.binders(),
        [
            ProvenanceRole::RuleExistentialBinder,
            ProvenanceRole::RuleExistentialBinderName,
            ProvenanceRole::RuleExistentialBinderSort,
        ],
        "existential",
        (facade, nonce, cfg),
        slots,
    )
}

/// The wire form of a rule's `heat` or `cool` key (KF-014) and the hidden
/// sort-key function of its `result = S` sort. A heat or cool rule takes no
/// `#[k::fresh]`: K's heating and cooling steps cannot allocate a fresh value.
pub(super) fn evaluation_step(
    attribute: &krs_syntax::RuleAttribute,
    existentials: &RuleExistentials,
    (facade, nonce, cfg): (&Path, u64, &[Attribute]),
    slots: &mut WireSlots,
) -> crate::Result<(Option<WireEvaluationStep>, Option<TokenStream>)> {
    let Some((kind, _)) = attribute.evaluation() else {
        return Ok((None, None));
    };
    if let Some(binder) = existentials.fresh().first() {
        return Err(super::rules::misplaced_fresh(binder.name().span()));
    }
    let hole = attribute
        .hole()
        .expect("the rule attribute requires a hole on a heat or cool rule");
    let (result, key_function) = match attribute.result_sort() {
        Some(sort) => {
            let path = call_site_path(sort)?;
            let key_fn = format_ident!("__krs_rule_evaluation_result_{nonce:016x}");
            (
                Some(wire_sort_reference(
                    slots,
                    facade,
                    kind.result_role(),
                    0,
                    &key_fn,
                    &spelling(sort),
                )),
                Some(quote! {
                    #(#cfg)*
                    #[doc(hidden)]
                    fn #key_fn() -> ::core::any::TypeId { ::core::any::TypeId::of::<#path>() }
                }),
            )
        }
        None => (None, None),
    };
    Ok((
        Some(WireEvaluationStep {
            kind,
            key: wire_key(kind.role(), 0),
            hole_key: wire_key(kind.hole_role(), 0),
            hole: hole.to_string(),
            result,
        }),
        key_function,
    ))
}

/// The wire binders of a transition's fresh binders (`#[k::fresh]`, KF-022)
/// and their hidden sort-key functions.
pub(super) fn fresh_binders(
    existentials: &RuleExistentials,
    facade: &Path,
    nonce: u64,
    cfg: &[Attribute],
    slots: &mut WireSlots,
) -> crate::Result<(Vec<WireClaimBinder>, Vec<TokenStream>)> {
    scoped_binders(
        existentials.fresh(),
        [
            ProvenanceRole::RuleFreshBinder,
            ProvenanceRole::RuleFreshBinderName,
            ProvenanceRole::RuleFreshBinderSort,
        ],
        "fresh",
        (facade, nonce, cfg),
        slots,
    )
}

/// Wire binders under `[declaration, name, sort]` roles, with one sort-key
/// function per binder named after `kind`.
fn scoped_binders(
    declared: &[ClaimBinder],
    [declaration_role, name_role, sort_role]: [ProvenanceRole; 3],
    kind: &str,
    (facade, nonce, cfg): (&Path, u64, &[Attribute]),
    slots: &mut WireSlots,
) -> crate::Result<(Vec<WireClaimBinder>, Vec<TokenStream>)> {
    let mut binders = Vec::new();
    let mut key_functions = Vec::new();
    for (index, binder) in declared.iter().enumerate() {
        let ordinal = u32::try_from(index).map_err(|_| {
            ExpandError::new(
                expand::DESCRIPTOR_CAPACITY,
                binder.name().span(),
                format!("too many {kind} binders"),
            )
        })?;
        let path = call_site_path(binder.sort())?;
        let key_fn = format_ident!("__krs_rule_{kind}_sort_{nonce:016x}_{ordinal}");
        key_functions.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #key_fn() -> ::core::any::TypeId { ::core::any::TypeId::of::<#path>() }
        });
        binders.push(WireClaimBinder {
            declaration_key: wire_key(declaration_role, ordinal),
            name_key: wire_key(name_role, ordinal),
            name: binder.name().to_string(),
            sort: wire_sort_reference(
                slots,
                facade,
                sort_role,
                ordinal,
                &key_fn,
                &spelling(binder.sort()),
            ),
        });
    }
    Ok((binders, key_functions))
}

/// The wire form of a transition's ensures condition, built by `builder`
/// (whose bindings are the subject bindings followed by the existentials).
pub(super) fn ensures_condition(
    existentials: &RuleExistentials,
    builder: &mut TermBuilder<'_>,
    slots: &mut WireSlots,
) -> crate::Result<Option<WireRuleCondition>> {
    existentials
        .ensures()
        .map(|condition| {
            Ok(WireRuleCondition {
                key: wire_key(ProvenanceRole::RuleEnsures, 0),
                term: builder.expand_wire(condition.tree(), TermSide::RuleEnsures, slots)?,
            })
        })
        .transpose()
}
