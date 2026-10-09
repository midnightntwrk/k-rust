//! Whole-configuration reachability claims: `#[k::claim]`.

use crate::ExpandError;
use krs_diagnostic::codes::expand;
use krs_ir::wire::{
    WireClaim, WireClaimBinder, WireConfigurationReference, WireConfigurationRule, WirePayload,
    WireRuleCondition, WireTypeReference,
};
use krs_ir::{ClaimModality, DescriptorRuleLabel, ProtocolRuleBinding, ProtocolRuleBindingKind};
use krs_syntax::KrsSyntax;
use krs_syntax::{
    ClaimModality as SyntaxClaimModality, ProvenanceRole, RuleSide, StateRuleBindingKind,
    StateRuleReferenceKind, TokenRange,
};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use super::factory::{DescriptorFactory, FactoryPayload};
use super::island_checks::{consumed_state_island_import_checks, wrapper_type_check};
use super::nonce::expansion_nonce;
use super::state_rules::StateRuleBuilder;
use super::terms::{TermBuilder, TermSide, WireSlots, wire_key, wire_sort_reference};
use super::tokens::{call_site_cfg_attributes, call_site_path, sort_type_tokens, spelling};
use crate::environment::MacroEnvironment;
use crate::provenance::host_provenance;

/// Expands one whole-configuration reachability claim.
pub(crate) fn claim(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> crate::Result<TokenStream> {
    let attribute = krs_syntax::ClaimAttribute::parse_tokens(attributes)?;
    super::rules::reject_fresh_helper(&item)?;
    configuration_claim(env, item, &attribute)
}

#[expect(
    clippy::too_many_lines,
    reason = "Claim metadata and both structured sides are lowered together."
)]
fn configuration_claim(
    env: &dyn MacroEnvironment,
    item: TokenStream,
    attribute: &krs_syntax::ClaimAttribute,
) -> crate::Result<TokenStream> {
    let claim = krs_syntax::StateClaimItem::parse_tokens(item)?;
    let rule = claim.rule();
    let facade = env.facade_path()?;
    let mut anchors = claim.provenance()?;
    anchors.extend(attribute.provenance()?);
    let fallback = TokenRange::for_tokens(rule.item())?;
    let provenance = host_provenance(env, &facade, fallback, &anchors);
    let nonce = expansion_nonce(env, "configuration_claim", &rule.item().sig.ident, fallback);
    let factory = format_ident!("__krs_configuration_claim_{nonce:016x}");
    let subject_key = format_ident!("__krs_claim_configuration_left_{nonce:016x}");
    let result_key = format_ident!("__krs_claim_configuration_right_{nonce:016x}");
    let cfg = call_site_cfg_attributes(&rule.item().attrs)?;
    let subject_type = call_site_path(rule.subject_type())?;
    let declared_result_type = rule
        .result_type()
        .expect("a claim parses only with a result");
    let result_type = call_site_path(declared_result_type)?;
    let subject_spelling = spelling(rule.subject_type());
    let result_spelling = spelling(declared_result_type);

    let universal_idents = rule
        .bindings()
        .iter()
        .filter(|binding| binding.kind() == StateRuleBindingKind::Term)
        .map(|binding| binding.name().clone())
        .collect::<Vec<_>>();
    let existential_idents = claim
        .existentials()
        .iter()
        .map(|binder| binder.name().clone())
        .collect::<Vec<_>>();
    let all_idents = universal_idents
        .iter()
        .chain(&existential_idents)
        .cloned()
        .collect::<Vec<_>>();
    let mut slots = WireSlots::new(&facade);
    let mut bindings = Vec::new();
    let mut key_functions = Vec::new();
    let mut universal_metadata = Vec::new();
    let mut term_ordinal = 0_u32;
    for binding in rule.bindings() {
        let name = binding.name().to_string();
        let kind = match binding.kind() {
            StateRuleBindingKind::Term => {
                let sort = binding.term_sort().expect("term binding sort");
                let path = call_site_path(sort.sort())?;
                let ty = sort_type_tokens(&path, sort.is_dynamic());
                let key_fn =
                    format_ident!("__krs_claim_universal_sort_{nonce:016x}_{term_ordinal}");
                key_functions.push(quote! { #(#cfg)* #[doc(hidden)] fn #key_fn() -> ::core::any::TypeId { ::core::any::TypeId::of::<#ty>() } });
                let authored = sort.sort_token_text();
                let ordinal = term_ordinal;
                term_ordinal += 1;
                let sort_ref = wire_sort_reference(
                    &mut slots,
                    &facade,
                    ProvenanceRole::RuleBindingType,
                    ordinal,
                    &key_fn,
                    &authored,
                );
                let claim_sort_ref = wire_sort_reference(
                    &mut slots,
                    &facade,
                    ProvenanceRole::ClaimBinderSort,
                    ordinal,
                    &key_fn,
                    &authored,
                );
                universal_metadata.push(WireClaimBinder {
                    declaration_key: wire_key(ProvenanceRole::ClaimUniversalBinder, ordinal),
                    name_key: wire_key(ProvenanceRole::ClaimBinderName, ordinal),
                    name: name.clone(),
                    sort: claim_sort_ref,
                });
                ProtocolRuleBindingKind::Term { sort: sort_ref }
            }
            StateRuleBindingKind::KSequenceFrame => ProtocolRuleBindingKind::KSequenceFrame,
            StateRuleBindingKind::MapFrame => ProtocolRuleBindingKind::MapFrame,
            StateRuleBindingKind::ConfigurationFrame => ProtocolRuleBindingKind::ConfigurationFrame,
            StateRuleBindingKind::InstancesFrame => ProtocolRuleBindingKind::InstancesFrame,
        };
        bindings.push(ProtocolRuleBinding { name, kind });
    }
    let mut existential_metadata = Vec::new();
    for (index, binder) in claim.existentials().iter().enumerate() {
        let ordinal = u32::try_from(index).map_err(|_| {
            ExpandError::new(
                expand::DESCRIPTOR_CAPACITY,
                binder.name().span(),
                "too many existential binders",
            )
        })?;
        let binder_ordinal = term_ordinal.checked_add(ordinal).ok_or_else(|| {
            ExpandError::new(
                expand::DESCRIPTOR_CAPACITY,
                binder.name().span(),
                "too many claim binders",
            )
        })?;
        let path = call_site_path(binder.sort())?;
        let key_fn = format_ident!("__krs_claim_existential_sort_{nonce:016x}_{ordinal}");
        key_functions.push(quote! { #(#cfg)* #[doc(hidden)] fn #key_fn() -> ::core::any::TypeId { ::core::any::TypeId::of::<#path>() } });
        let authored = spelling(binder.sort());
        let name = binder.name().to_string();
        let sort_ref = wire_sort_reference(
            &mut slots,
            &facade,
            ProvenanceRole::ClaimBinderSort,
            binder_ordinal,
            &key_fn,
            &authored,
        );
        existential_metadata.push(WireClaimBinder {
            declaration_key: wire_key(ProvenanceRole::ClaimExistentialBinder, ordinal),
            name_key: wire_key(ProvenanceRole::ClaimBinderName, binder_ordinal),
            name,
            sort: sort_ref,
        });
    }

    let mut left =
        StateRuleBuilder::new(&facade, nonce, &cfg, &universal_idents, RuleSide::Left).for_claim();
    let subject = left.expand_cells(rule.subject(), &subject_type, &mut slots)?;
    let mut right = StateRuleBuilder::new(
        &facade,
        nonce ^ 0x8000_0000_0000_0000,
        &cfg,
        &all_idents,
        RuleSide::Right,
    )
    .for_claim();
    right.counters.id_token = left.counters.id_token;
    right.counters.bytes_token = left.counters.bytes_token;
    right.counters.anonymous = left.counters.anonymous;
    right.counters.or_bool = left.counters.or_bool;
    right.terms.continue_ordinals(&left.terms);
    let result = right.expand_cells(
        rule.result().expect("a claim parses only with a result"),
        &result_type,
        &mut slots,
    )?;
    let mut condition_builder = TermBuilder::new(
        &facade,
        nonce ^ 0x4000_0000_0000_0000,
        &cfg,
        &universal_idents,
    )
    .for_claim();
    condition_builder.id_token_ordinal = right.counters.id_token;
    condition_builder.bytes_token_ordinal = right.counters.bytes_token;
    condition_builder.or_bool_ordinal = right.counters.or_bool;
    condition_builder.continue_ordinals(&right.terms);
    let requires = if let Some(condition) = rule.requires() {
        let term = condition_builder.expand_wire(
            condition.term().tree(),
            TermSide::Requires,
            &mut slots,
        )?;
        Some(WireRuleCondition {
            key: wire_key(ProvenanceRole::RuleRequires, 0),
            term,
        })
    } else {
        None
    };
    let mut ensures_builder =
        TermBuilder::new(&facade, nonce ^ 0x2000_0000_0000_0000, &cfg, &all_idents).for_claim();
    ensures_builder.id_token_ordinal = condition_builder.id_token_ordinal;
    ensures_builder.bytes_token_ordinal = condition_builder.bytes_token_ordinal;
    ensures_builder.or_bool_ordinal = condition_builder.or_bool_ordinal;
    ensures_builder.continue_ordinals(&condition_builder);
    let ensures = if let Some(condition) = claim.ensures() {
        let term =
            ensures_builder.expand_wire(condition.term().tree(), TermSide::Ensures, &mut slots)?;
        Some(WireRuleCondition {
            key: wire_key(ProvenanceRole::ClaimEnsures, 0),
            term,
        })
    } else {
        None
    };
    key_functions.extend(left.terms.key_functions);
    key_functions.extend(right.terms.key_functions);
    key_functions.extend(condition_builder.key_functions);
    key_functions.extend(ensures_builder.key_functions);
    let original = rule.item();
    let attrs = &original.attrs;
    let visibility = &original.vis;
    let fn_token = original.sig.fn_token;
    let name_ident = &original.sig.ident;
    let ordinary_inputs = original
        .sig
        .inputs
        .iter()
        .take(original.sig.inputs.len() - 1);
    let name = name_ident.to_string();
    let label_name = attribute.label().value();
    let modality = match attribute.modality() {
        SyntaxClaimModality::AllPaths => ClaimModality::AllPaths,
        SyntaxClaimModality::OnePath => ClaimModality::OnePath,
    };
    let circularity = if attribute.circularity() {
        Some(wire_key(ProvenanceRole::ClaimCircularity, 0))
    } else {
        None
    };
    let trusted = attribute
        .trusted()
        .then(|| wire_key(ProvenanceRole::ClaimTrusted, 0));
    let or_bool_count = anchors
        .iter()
        .filter(|anchor| anchor.role() == ProvenanceRole::ClaimOrBool)
        .count();
    let or_bool_keys = (0..or_bool_count)
        .map(|index| {
            let index = u32::try_from(index).unwrap();
            wire_key(ProvenanceRole::ClaimOrBool, index)
        })
        .collect();
    let mut wrapper_checks = Vec::new();
    for candidate in rule.reference_candidates()? {
        if candidate.kind() == StateRuleReferenceKind::CellWrapper {
            let path = call_site_path(candidate.path())?;
            wrapper_checks.push(wrapper_type_check(&path));
        }
    }
    let island_import_checks = consumed_state_island_import_checks(original);
    let wire = WirePayload::ConfigurationRule(Box::new(WireConfigurationRule {
        sentence_kind: krs_ir::ConfigurationSentenceKind::Claim,
        label: Some(DescriptorRuleLabel {
            key: wire_key(ProvenanceRole::ClaimLabel, 0),
            name: label_name,
        }),
        priority: None,
        nondet: None,
        requires,
        claim: Some(WireClaim {
            declaration_key: wire_key(ProvenanceRole::ClaimDeclaration, 0),
            modality_key: wire_key(ProvenanceRole::ClaimModality, 0),
            modality,
            circularity_key: circularity,
            trusted_key: trusted,
            universals: universal_metadata,
            existentials: existential_metadata,
            ensures,
            or_bool_keys,
        }),
        pattern_key: wire_key(ProvenanceRole::RulePattern, 0),
        subject_configuration: WireConfigurationReference {
            key: wire_key(ProvenanceRole::RuleType, 0),
            configuration: WireTypeReference {
                slot: slots.type_slot(quote!(#facade::HostTypeKey(#subject_key))),
                authored_path: subject_spelling,
            },
        },
        result_key: Some(wire_key(ProvenanceRole::RuleResult, 0)),
        result_configuration: Some(WireConfigurationReference {
            key: wire_key(ProvenanceRole::RuleResultType, 0),
            configuration: WireTypeReference {
                slot: slots.type_slot(quote!(#facade::HostTypeKey(#result_key))),
                authored_path: result_spelling,
            },
        }),
        bindings,
        subject,
        result: Some(result),
        existentials: Vec::new(),
        ensures: None,
        fresh: Vec::new(),
        evaluation: None,
    }));
    let wire = serde_json::to_string(&wire).expect("KRS wire values serialize");
    let slot_tokens = slots.tokens();

    let factory_tokens = DescriptorFactory {
        facade: &facade,
        factory: &factory,
        name: quote!(#name),
        item_kind: quote!(#facade::ItemKind::Claim),
        disambiguator: quote!(""),
        identity_label: "Cargo and Rust macro context form a valid claim identity",
        declared_type: quote!(None),
        payload: FactoryPayload::wire(wire, slot_tokens),
        cfg: quote!(Default::default()),
        attributes: quote!(#(#cfg)*),
        provenance: quote!(#provenance),
        prelude: TokenStream::new(),
    }
    .render();

    Ok(quote! {
        #(#attrs)* #visibility #fn_token #name_ident(#(#ordinary_inputs,)* __krs_symbolic_configuration: #subject_type) -> #result_type {
            let _krs_path_check = || {
                #(#wrapper_checks)*
                #(#island_import_checks)*
            };
            #(let _ = &#universal_idents;)* let _ = __krs_symbolic_configuration;
            ::core::panic!("KRS claim declarations have no runtime implementation")
        }
        #(#cfg)* #[doc(hidden)] fn #subject_key() -> ::core::any::TypeId { ::core::any::TypeId::of::<#subject_type>() }
        #(#cfg)* #[doc(hidden)] fn #result_key() -> ::core::any::TypeId { ::core::any::TypeId::of::<#result_type>() }
        #(#key_functions)*
        #factory_tokens
    })
}
