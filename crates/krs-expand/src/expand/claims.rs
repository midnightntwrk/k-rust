//! Whole-configuration reachability claims: `#[k::claim]`.

use krs_syntax::{
    ClaimModality as SyntaxClaimModality, ProvenanceRole, RuleSide, StateRuleBindingKind,
    StateRuleReferenceKind, TokenRange, parse_claim_attribute, parse_state_claim_item, role_tokens,
};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use super::island_checks::{consumed_state_island_import_checks, wrapper_type_check};
use super::nonce::expansion_nonce;
use super::state_rules::StateRuleBuilder;
use super::terms::{TermBuilder, TermSide};
use super::tokens::{
    call_site_cfg_attributes, call_site_path, host_sort_reference, sort_type_tokens, spelling,
};
use crate::environment::MacroEnvironment;
use crate::provenance::host_provenance;

/// Expands one whole-configuration reachability claim.
pub(crate) fn claim(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let attribute = parse_claim_attribute(attributes)?;
    configuration_claim(env, item, &attribute)
}

#[allow(clippy::too_many_lines)]
fn configuration_claim(
    env: &dyn MacroEnvironment,
    item: TokenStream,
    attribute: &krs_syntax::ClaimAttribute,
) -> syn::Result<TokenStream> {
    let claim_universal_binder_role = ProvenanceRole::ClaimUniversalBinder;
    let claim_binder_name_role = ProvenanceRole::ClaimBinderName;
    let claim_existential_binder_role = ProvenanceRole::ClaimExistentialBinder;
    let rule_requires_role = ProvenanceRole::RuleRequires;
    let claim_ensures_role = ProvenanceRole::ClaimEnsures;
    let claim_circularity_role = ProvenanceRole::ClaimCircularity;
    let claim_or_bool_role = ProvenanceRole::ClaimOrBool;
    let claim_label_role = ProvenanceRole::ClaimLabel;
    let claim_declaration_role = ProvenanceRole::ClaimDeclaration;
    let claim_modality_role = ProvenanceRole::ClaimModality;
    let rule_pattern_role = ProvenanceRole::RulePattern;
    let rule_type_role = ProvenanceRole::RuleType;
    let rule_result_role = ProvenanceRole::RuleResult;
    let rule_result_type_role = ProvenanceRole::RuleResultType;
    let claim = parse_state_claim_item(item)?;
    let rule = claim.rule();
    let facade = env.facade_path()?;
    let claim_universal_binder_role = role_tokens(claim_universal_binder_role, &facade);
    let claim_binder_name_role = role_tokens(claim_binder_name_role, &facade);
    let claim_existential_binder_role = role_tokens(claim_existential_binder_role, &facade);
    let rule_requires_role = role_tokens(rule_requires_role, &facade);
    let claim_ensures_role = role_tokens(claim_ensures_role, &facade);
    let claim_circularity_role = role_tokens(claim_circularity_role, &facade);
    let claim_or_bool_role = role_tokens(claim_or_bool_role, &facade);
    let claim_label_role = role_tokens(claim_label_role, &facade);
    let claim_declaration_role = role_tokens(claim_declaration_role, &facade);
    let claim_modality_role = role_tokens(claim_modality_role, &facade);
    let rule_pattern_role = role_tokens(rule_pattern_role, &facade);
    let rule_type_role = role_tokens(rule_type_role, &facade);
    let rule_result_role = role_tokens(rule_result_role, &facade);
    let rule_result_type_role = role_tokens(rule_result_type_role, &facade);
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
    let result_type = call_site_path(rule.result_type())?;
    let subject_spelling = spelling(rule.subject_type());
    let result_spelling = spelling(rule.result_type());

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
                let authored = sort.sort_spelling();
                let ordinal = term_ordinal;
                term_ordinal += 1;
                let sort_ref = host_sort_reference(
                    &facade,
                    ProvenanceRole::RuleBindingType,
                    ordinal,
                    &key_fn,
                    &authored,
                );
                let claim_sort_ref = host_sort_reference(
                    &facade,
                    ProvenanceRole::ClaimBinderSort,
                    ordinal,
                    &key_fn,
                    &authored,
                );
                universal_metadata.push(quote!(#facade::HostClaimBinder {
                    declaration_key: #facade::ProvenanceKey::new(#claim_universal_binder_role, #ordinal),
                    name_key: #facade::ProvenanceKey::new(#claim_binder_name_role, #ordinal),
                    name: #name.to_owned(), sort: #claim_sort_ref,
                }));
                quote!(#facade::ProtocolRuleBindingKind::Term { sort: #sort_ref })
            }
            StateRuleBindingKind::KSequenceFrame => {
                quote!(#facade::ProtocolRuleBindingKind::KSequenceFrame)
            }
            StateRuleBindingKind::MapFrame => quote!(#facade::ProtocolRuleBindingKind::MapFrame),
            StateRuleBindingKind::ConfigurationFrame => {
                quote!(#facade::ProtocolRuleBindingKind::ConfigurationFrame)
            }
        };
        bindings.push(quote!(#facade::HostRuleBinding { name: #name.to_owned(), kind: #kind }));
    }
    let mut existential_metadata = Vec::new();
    for (index, binder) in claim.existentials().iter().enumerate() {
        let ordinal = u32::try_from(index)
            .map_err(|_| syn::Error::new(binder.name().span(), "too many existential binders"))?;
        let binder_ordinal = term_ordinal
            .checked_add(ordinal)
            .ok_or_else(|| syn::Error::new(binder.name().span(), "too many claim binders"))?;
        let path = call_site_path(binder.sort())?;
        let key_fn = format_ident!("__krs_claim_existential_sort_{nonce:016x}_{ordinal}");
        key_functions.push(quote! { #(#cfg)* #[doc(hidden)] fn #key_fn() -> ::core::any::TypeId { ::core::any::TypeId::of::<#path>() } });
        let authored = spelling(binder.sort());
        let name = binder.name().to_string();
        let sort_ref = host_sort_reference(
            &facade,
            ProvenanceRole::ClaimBinderSort,
            binder_ordinal,
            &key_fn,
            &authored,
        );
        existential_metadata.push(quote!(#facade::HostClaimBinder {
            declaration_key: #facade::ProvenanceKey::new(#claim_existential_binder_role, #ordinal),
            name_key: #facade::ProvenanceKey::new(#claim_binder_name_role, #binder_ordinal),
            name: #name.to_owned(), sort: #sort_ref,
        }));
    }

    let mut left =
        StateRuleBuilder::new(&facade, nonce, &cfg, &universal_idents, RuleSide::Left).for_claim();
    let subject = left.expand_cells(rule.subject(), &subject_type)?;
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
    let result = right.expand_cells(rule.result(), &result_type)?;
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
    let requires = if let Some(condition) = rule.requires() {
        let term = condition_builder.expand(condition.term().tree(), TermSide::Requires)?;
        quote!(::core::option::Option::Some(#facade::HostRuleCondition { key: #facade::ProvenanceKey::new(#rule_requires_role, 0), term: #term }))
    } else {
        quote!(::core::option::Option::None)
    };
    let mut ensures_builder =
        TermBuilder::new(&facade, nonce ^ 0x2000_0000_0000_0000, &cfg, &all_idents).for_claim();
    ensures_builder.id_token_ordinal = condition_builder.id_token_ordinal;
    ensures_builder.bytes_token_ordinal = condition_builder.bytes_token_ordinal;
    ensures_builder.or_bool_ordinal = condition_builder.or_bool_ordinal;
    let ensures = if let Some(condition) = claim.ensures() {
        let term = ensures_builder.expand(condition.term().tree(), TermSide::Ensures)?;
        quote!(::core::option::Option::Some(#facade::HostRuleCondition { key: #facade::ProvenanceKey::new(#claim_ensures_role, 0), term: #term }))
    } else {
        quote!(::core::option::Option::None)
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
        SyntaxClaimModality::AllPaths => quote!(#facade::ClaimModality::AllPaths),
        SyntaxClaimModality::OnePath => quote!(#facade::ClaimModality::OnePath),
    };
    let circularity = if attribute.circularity() {
        quote!(::core::option::Option::Some(#facade::ProvenanceKey::new(#claim_circularity_role, 0)))
    } else {
        quote!(::core::option::Option::None)
    };
    let or_bool_count = anchors
        .iter()
        .filter(|anchor| anchor.role() == ProvenanceRole::ClaimOrBool)
        .count();
    let or_bool_keys = (0..or_bool_count).map(|index| {
        let index = u32::try_from(index).unwrap();
        quote!(#facade::ProvenanceKey::new(#claim_or_bool_role, #index))
    });
    let mut wrapper_checks = Vec::new();
    for candidate in rule.reference_candidates()? {
        if candidate.kind() == StateRuleReferenceKind::CellWrapper {
            let path = call_site_path(candidate.path())?;
            wrapper_checks.push(wrapper_type_check(&path));
        }
    }
    let island_import_checks = consumed_state_island_import_checks(original);
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
        #(#cfg)* #[doc(hidden)] fn #factory() -> #facade::HostDescriptor {
            #facade::HostDescriptor {
                protocol_version: #facade::SchemaVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"), env!("CARGO_MANIFEST_DIR"), module_path!(), #name, #facade::ItemKind::Claim, "").unwrap(),
                declared_type: None,
                payload: #facade::HostDescriptorPayload::ConfigurationRule(Box::new(#facade::HostConfigurationRule {
                    sentence_kind: #facade::SentenceKind::Claim,
                    label: Some(#facade::DescriptorRuleLabel { key: #facade::ProvenanceKey::new(#claim_label_role, 0), name: #label_name.to_owned() }),
                    priority: None,
                    requires: #requires,
                    claim: Some(#facade::HostClaim { declaration_key: #facade::ProvenanceKey::new(#claim_declaration_role, 0), modality_key: #facade::ProvenanceKey::new(#claim_modality_role, 0), modality: #modality, circularity_key: #circularity, universals: vec![#(#universal_metadata),*], existentials: vec![#(#existential_metadata),*], ensures: #ensures, or_bool_keys: vec![#(#or_bool_keys),*] }),
                    pattern_key: #facade::ProvenanceKey::new(#rule_pattern_role, 0),
                    subject_configuration: #facade::HostConfigurationReference { key: #facade::ProvenanceKey::new(#rule_type_role, 0), configuration: #facade::HostTypeReference { key: #facade::HostTypeKey(#subject_key), authored_path: #subject_spelling.to_owned() } },
                    result_key: #facade::ProvenanceKey::new(#rule_result_role, 0),
                    result_configuration: #facade::HostConfigurationReference { key: #facade::ProvenanceKey::new(#rule_result_type_role, 0), configuration: #facade::HostTypeReference { key: #facade::HostTypeKey(#result_key), authored_path: #result_spelling.to_owned() } },
                    bindings: vec![#(#bindings),*], subject: #subject, result: #result,
                })), cfg: Default::default(), provenance: #provenance,
            }
        }
        #(#cfg)* #facade::__register_host_descriptor!(#factory);
    })
}
