//! Whole-configuration rules and named contexts: cells-form `#[k::rule]` and `#[k::context_alias]`.

use crate::ExpandError;
use krs_diagnostic::codes::expand;
use krs_ir::bytes_token;
use krs_ir::wire::{
    WireApplicationReference, WireCellIdentity, WireCellReference, WireCellTermField,
    WireConfigurationReference, WireConfigurationRule, WireContextAlias, WirePayload,
    WireRuleCells, WireRuleCondition, WireSortReference, WireTerm, WireTypeReference,
};
use krs_ir::{
    BuiltinSort, CellWrapper, DescriptorApplicationHeadClass, DescriptorKSequenceNotation,
    DescriptorRuleLabel, DescriptorRulePriority, ProductionFieldId, ProtocolContextAliasBinding,
    ProtocolContextAliasBindingKind, ProtocolRuleBinding, ProtocolRuleBindingKind,
    ProtocolRuleCell, ProtocolRuleFrame, ProtocolRuleKSequence, ProtocolRuleKSequenceItem,
    ProtocolRuleMap, ProtocolRuleMapBody, ProtocolRuleMapItem, ProtocolRuleStateTerm,
    ProvenanceKey,
};
use krs_syntax::KrsSyntax;
use krs_syntax::{
    KSequence, KSequenceNotation, MapBody, MapExpression, ProvenanceAnchor, ProvenanceRole,
    RuleRole, RuleSide, StateMacroRemainder, StateRuleBindingKind, StateRuleReferenceKind,
    StateTerm, TermArguments, TermTree, TokenRange, parse_state_context_alias_item,
};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::spanned::Spanned;
use syn::{Attribute, Ident, Path};

use super::configuration::cell_marker_function;
use super::existentials::{ensures_condition, existential_binders, fresh_binders};
use super::factory::{DescriptorFactory, FactoryPayload};
use super::island_checks::{consumed_state_island_import_checks, wrapper_type_check};
use super::nonce::expansion_nonce;
use super::terms::{TermBuilder, TermRole, TermSide, WireSlots, wire_key, wire_sort_reference};
use super::tokens::{
    call_site_cfg_attributes, call_site_path, is_bound_ident_path, map_has_role, sequence_has_role,
    sort_type_tokens, spelling, take_counter, wire_literal,
};
use crate::environment::MacroEnvironment;
use crate::provenance::host_provenance;

#[expect(
    clippy::too_many_lines,
    reason = "The context alias and its complete provenance are expanded together."
)]
pub(crate) fn context_alias(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> crate::Result<TokenStream> {
    let attribute = krs_syntax::ContextAliasAttribute::parse_tokens(attributes)?;
    super::rules::reject_fresh_helper(&item)?;
    let alias = parse_state_context_alias_item(item, attribute.here())?;
    let facade = env.facade_path()?;
    let mut anchors = attribute.provenance()?;
    anchors.push(ProvenanceAnchor::new(
        ProvenanceRole::ContextAliasDeclaration,
        0,
        TokenRange::for_tokens(&alias.item().sig.ident)?,
    ));
    anchors.extend(alias.provenance()?);
    let fallback = TokenRange::for_tokens(alias.item())?;
    let provenance = host_provenance(env, &facade, fallback, &anchors);
    let nonce = expansion_nonce(env, "context_alias", &alias.item().sig.ident, fallback);
    let factory = format_ident!("__krs_context_alias_{nonce:016x}");
    let configuration_key = format_ident!("__krs_context_alias_configuration_{nonce:016x}");
    let cfg = call_site_cfg_attributes(&alias.item().attrs)?;
    let configuration_type = call_site_path(alias.configuration_type())?;
    let configuration_spelling = spelling(alias.configuration_type());
    let binding_idents = alias
        .bindings()
        .iter()
        .filter(|binding| binding.kind() == StateRuleBindingKind::Term)
        .map(|binding| binding.name().clone())
        .collect::<Vec<_>>();
    let mut slots = WireSlots::new(&facade);
    let mut bindings = Vec::new();
    let mut key_functions = Vec::new();
    let mut term_ordinal = 0_u32;
    for binding in alias.bindings() {
        let binding_name = binding.name().to_string();
        let kind = if binding.name() == alias.here() {
            ProtocolContextAliasBindingKind::Here
        } else {
            match binding.kind() {
                StateRuleBindingKind::Term => {
                    let sort = binding
                        .term_sort()
                        .expect("non-HERE terms retain explicit sorts");
                    let path = call_site_path(sort.sort())?;
                    let ty = sort_type_tokens(&path, sort.is_dynamic());
                    let key_fn =
                        format_ident!("__krs_context_alias_binding_{nonce:016x}_{term_ordinal}");
                    key_functions.push(quote! {
                        #(#cfg)*
                        #[doc(hidden)]
                        fn #key_fn() -> ::core::any::TypeId { ::core::any::TypeId::of::<#ty>() }
                    });
                    let sort_spelling = sort.sort_token_text();
                    let ordinal = term_ordinal;
                    term_ordinal = term_ordinal.checked_add(1).ok_or_else(|| {
                        ExpandError::new(
                            expand::DESCRIPTOR_CAPACITY,
                            binding.name().span(),
                            "too many context bindings",
                        )
                    })?;
                    ProtocolContextAliasBindingKind::Term {
                        sort: wire_sort_reference(
                            &mut slots,
                            &facade,
                            ProvenanceRole::RuleBindingType,
                            ordinal,
                            &key_fn,
                            &sort_spelling,
                        ),
                    }
                }
                StateRuleBindingKind::KSequenceFrame => {
                    ProtocolContextAliasBindingKind::KSequenceFrame
                }
                StateRuleBindingKind::MapFrame => ProtocolContextAliasBindingKind::MapFrame,
                StateRuleBindingKind::ConfigurationFrame => {
                    ProtocolContextAliasBindingKind::ConfigurationFrame
                }
            }
        };
        bindings.push(ProtocolContextAliasBinding {
            name: binding_name,
            kind,
        });
    }
    let mut builder = StateRuleBuilder::new(&facade, nonce, &cfg, &binding_idents, RuleSide::Left);
    let pattern = builder.expand_cells(alias.pattern(), &configuration_type, &mut slots)?;
    key_functions.extend(builder.terms.key_functions);
    let mut wrapper_checks = Vec::new();
    for candidate in alias.reference_candidates()? {
        if candidate.kind() == StateRuleReferenceKind::CellWrapper {
            let path = call_site_path(candidate.path())?;
            wrapper_checks.push(wrapper_type_check(&path));
        }
    }
    let original = alias.item();
    let island_import_checks = consumed_state_island_import_checks(original);
    let attrs = &original.attrs;
    let visibility = &original.vis;
    let fn_token = original.sig.fn_token;
    let name_ident = &original.sig.ident;
    let rust_name = name_ident.to_string();
    let alias_name = attribute.name().to_string();
    let here_name = attribute.here().to_string();

    let wire = WirePayload::ContextAlias(Box::new(WireContextAlias {
        declaration_key: wire_key(ProvenanceRole::ContextAliasDeclaration, 0),
        name_key: wire_key(ProvenanceRole::ContextAliasName, 0),
        name: alias_name,
        here_key: wire_key(ProvenanceRole::ContextAliasHere, 0),
        here: here_name,
        pattern_key: wire_key(ProvenanceRole::RulePattern, 0),
        configuration: WireConfigurationReference {
            key: wire_key(ProvenanceRole::RuleType, 0),
            configuration: WireTypeReference {
                slot: slots.type_slot(quote!(#facade::HostTypeKey(#configuration_key))),
                authored_path: configuration_spelling,
            },
        },
        bindings,
        pattern,
    }));
    let wire = serde_json::to_string(&wire).expect("KRS wire values serialize");
    let slot_tokens = slots.tokens();

    let factory_tokens = DescriptorFactory {
        facade: &facade,
        factory: &factory,
        name: quote!(#rust_name),
        item_kind: quote!(#facade::ItemKind::ContextAlias),
        disambiguator: quote!(""),
        identity_label: "Cargo and Rust macro context form a valid context alias identity",
        declared_type: quote!(::core::option::Option::None),
        payload: FactoryPayload::wire(wire, slot_tokens),
        cfg: quote!(::core::default::Default::default()),
        attributes: quote!(#(#cfg)*),
        provenance: quote!(#provenance),
        prelude: TokenStream::new(),
    }
    .render();

    Ok(quote! {
        #(#attrs)*
        #visibility #fn_token #name_ident(__krs_symbolic_configuration: #configuration_type) {
            let _krs_path_check = || {
                #(#wrapper_checks)*
                #(#island_import_checks)*
            };
            let _ = __krs_symbolic_configuration;
            ::core::panic!("KRS context-alias declarations have no runtime implementation")
        }
        #(#cfg)*
        #[doc(hidden)]
        fn #configuration_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#configuration_type>()
        }
        #(#key_functions)*
        #factory_tokens
    })
}

#[expect(
    clippy::too_many_lines,
    reason = "The configuration rule and its complete provenance are expanded together."
)]
pub(super) fn configuration_rule(
    env: &dyn MacroEnvironment,
    item: TokenStream,
    attribute: &krs_syntax::RuleAttribute,
) -> crate::Result<TokenStream> {
    let rule = krs_syntax::StateRuleItem::parse_tokens(item)?;
    let facade = env.facade_path()?;
    let mut anchors = rule.provenance()?;
    anchors.extend(attribute.provenance()?);
    let fallback = TokenRange::for_tokens(rule.item())?;
    let provenance = host_provenance(env, &facade, fallback, &anchors);
    let nonce = expansion_nonce(env, "configuration_rule", &rule.item().sig.ident, fallback);
    let factory = format_ident!("__krs_configuration_rule_{nonce:016x}");
    let subject_key = format_ident!("__krs_rule_configuration_left_{nonce:016x}");
    let result_key = format_ident!("__krs_rule_configuration_right_{nonce:016x}");
    let cfg = call_site_cfg_attributes(&rule.item().attrs)?;
    let subject_type = call_site_path(rule.subject_type())?;
    let result_type = call_site_path(rule.result_type())?;
    let subject_spelling = spelling(rule.subject_type());
    let result_spelling = spelling(rule.result_type());
    let binding_idents = rule
        .bindings()
        .iter()
        .filter(|binding| binding.kind() == StateRuleBindingKind::Term)
        .map(|binding| binding.name().clone())
        .collect::<Vec<_>>();
    let mut slots = WireSlots::new(&facade);
    let mut bindings = Vec::new();
    let mut binding_key_functions = Vec::new();
    let mut term_ordinal = 0_u32;
    for binding in rule.bindings() {
        let name = binding.name().to_string();
        let kind = match binding.kind() {
            StateRuleBindingKind::Term => {
                let sort = binding
                    .term_sort()
                    .expect("term bindings retain explicit sorts");
                let path = call_site_path(sort.sort())?;
                let ty = sort_type_tokens(&path, sort.is_dynamic());
                let key_fn = format_ident!("__krs_rule_binding_sort_{nonce:016x}_{term_ordinal}");
                binding_key_functions.push(quote! {
                    #(#cfg)*
                    #[doc(hidden)]
                    fn #key_fn() -> ::core::any::TypeId {
                        ::core::any::TypeId::of::<#ty>()
                    }
                });
                let authored = sort.sort_token_text();
                let ordinal = term_ordinal;
                term_ordinal = term_ordinal.checked_add(1).ok_or_else(|| {
                    ExpandError::new(
                        expand::DESCRIPTOR_CAPACITY,
                        binding.name().span(),
                        "too many term bindings",
                    )
                })?;
                ProtocolRuleBindingKind::Term {
                    sort: wire_sort_reference(
                        &mut slots,
                        &facade,
                        ProvenanceRole::RuleBindingType,
                        ordinal,
                        &key_fn,
                        &authored,
                    ),
                }
            }
            StateRuleBindingKind::KSequenceFrame => ProtocolRuleBindingKind::KSequenceFrame,
            StateRuleBindingKind::MapFrame => ProtocolRuleBindingKind::MapFrame,
            StateRuleBindingKind::ConfigurationFrame => ProtocolRuleBindingKind::ConfigurationFrame,
        };
        bindings.push(ProtocolRuleBinding { name, kind });
    }
    // The result and the ensures condition also see the existentials.
    let result_idents = binding_idents
        .iter()
        .cloned()
        .chain(rule.existentials().names())
        .collect::<Vec<_>>();
    let (existentials, existential_key_functions) =
        existential_binders(rule.existentials(), &facade, nonce, &cfg, &mut slots)?;
    let (fresh, fresh_key_functions) =
        fresh_binders(rule.existentials(), &facade, nonce, &cfg, &mut slots)?;
    let mut left = StateRuleBuilder::new(&facade, nonce, &cfg, &binding_idents, RuleSide::Left);
    let subject = left.expand_cells(rule.subject(), &subject_type, &mut slots)?;
    let mut right = StateRuleBuilder::new(
        &facade,
        nonce ^ 0x8000_0000_0000_0000,
        &cfg,
        &result_idents,
        RuleSide::Right,
    );
    right.terms.continue_ordinals(&left.terms);
    let result = right.expand_cells(rule.result(), &result_type, &mut slots)?;
    let mut condition_builder = TermBuilder::new(
        &facade,
        nonce ^ 0x4000_0000_0000_0000,
        &cfg,
        &binding_idents,
    );
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
        TermBuilder::new(&facade, nonce ^ 0x2000_0000_0000_0000, &cfg, &result_idents);
    ensures_builder.id_token_ordinal = condition_builder.id_token_ordinal;
    ensures_builder.bytes_token_ordinal = condition_builder.bytes_token_ordinal;
    ensures_builder.or_bool_ordinal = condition_builder.or_bool_ordinal;
    ensures_builder.continue_ordinals(&condition_builder);
    let ensures = ensures_condition(rule.existentials(), &mut ensures_builder, &mut slots)?;
    let mut key_functions = left.terms.key_functions;
    key_functions.extend(right.terms.key_functions);
    key_functions.extend(condition_builder.key_functions);
    key_functions.extend(ensures_builder.key_functions);
    key_functions.extend(binding_key_functions);
    key_functions.extend(existential_key_functions);
    key_functions.extend(fresh_key_functions);
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
    let label = attribute.label().map(|label| DescriptorRuleLabel {
        key: wire_key(ProvenanceRole::RuleLabel, 0),
        name: label.value(),
    });
    let priority = attribute
        .transition_priority()
        .map(|(role, value)| DescriptorRulePriority {
            key: wire_key(role, 0),
            value,
        });
    let mut wrapper_checks = Vec::new();
    for candidate in rule.reference_candidates()? {
        if candidate.kind() == StateRuleReferenceKind::CellWrapper {
            let path = call_site_path(candidate.path())?;
            wrapper_checks.push(wrapper_type_check(&path));
        }
    }
    let island_import_checks = consumed_state_island_import_checks(original);

    let nondet = attribute
        .nondet()
        .map(|group| krs_ir::DescriptorNondetGroup {
            key: ProvenanceRole::RuleNondetGroup.key(0),
            name: syn::ext::IdentExt::unraw(group).to_string(),
        });
    let wire = WirePayload::ConfigurationRule(Box::new(WireConfigurationRule {
        sentence_kind: krs_ir::ConfigurationSentenceKind::Transition,
        label,
        priority,
        nondet,
        requires,
        claim: None,
        pattern_key: wire_key(ProvenanceRole::RulePattern, 0),
        subject_configuration: WireConfigurationReference {
            key: wire_key(ProvenanceRole::RuleType, 0),
            configuration: WireTypeReference {
                slot: slots.type_slot(quote!(#facade::HostTypeKey(#subject_key))),
                authored_path: subject_spelling,
            },
        },
        result_key: wire_key(ProvenanceRole::RuleResult, 0),
        result_configuration: WireConfigurationReference {
            key: wire_key(ProvenanceRole::RuleResultType, 0),
            configuration: WireTypeReference {
                slot: slots.type_slot(quote!(#facade::HostTypeKey(#result_key))),
                authored_path: result_spelling,
            },
        },
        bindings,
        subject,
        result,
        existentials,
        ensures,
        fresh,
    }));
    let wire = serde_json::to_string(&wire).expect("KRS wire values serialize");
    let slot_tokens = slots.tokens();

    let factory_tokens = DescriptorFactory {
        facade: &facade,
        factory: &factory,
        name: quote!(#name),
        item_kind: quote!(#facade::ItemKind::Rule),
        disambiguator: quote!(""),
        identity_label: "Cargo and Rust macro context form a valid host identity",
        declared_type: quote!(::core::option::Option::None),
        payload: FactoryPayload::wire(wire, slot_tokens),
        cfg: quote!(::core::default::Default::default()),
        attributes: quote!(#(#cfg)*),
        provenance: quote!(#provenance),
        prelude: TokenStream::new(),
    }
    .render();

    Ok(quote! {
        #(#attrs)*
        #visibility #fn_token #name_ident(
            #(#ordinary_inputs,)*
            __krs_symbolic_configuration: #subject_type,
        ) -> #result_type {
            let _krs_path_check = || {
                #(#wrapper_checks)*
                #(#island_import_checks)*
            };
            #(let _ = &#binding_idents;)*
            let _ = __krs_symbolic_configuration;
            ::core::panic!("KRS rule declarations have no runtime implementation")
        }

        #(#cfg)*
        #[doc(hidden)]
        fn #subject_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#subject_type>()
        }

        #(#cfg)*
        #[doc(hidden)]
        fn #result_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#result_type>()
        }

        #(#key_functions)*

        #factory_tokens
    })
}

#[derive(Default)]
pub(super) struct StateRuleCounters {
    field: u32,
    wrapper: u32,
    remainder: u32,
    k_payload: u32,
    k_item: u32,
    k_tail: u32,
    map_payload: u32,
    map_key: u32,
    map_value: u32,
    map_remainder: u32,
    map_update_base: u32,
    application: u32,
    reference: u32,
    literal: u32,
    record_field: u32,
    wildcard: u32,
    pub(super) id_token: u32,
    pub(super) bytes_token: u32,
    pub(super) anonymous: u32,
    pub(super) or_bool: u32,
}

pub(super) struct StateRuleBuilder<'a> {
    facade: &'a Path,
    bindings: &'a [Ident],
    side: RuleSide,
    pub(super) counters: StateRuleCounters,
    pub(super) terms: TermBuilder<'a>,
    claim: bool,
}

impl<'a> StateRuleBuilder<'a> {
    pub(super) fn new(
        facade: &'a Path,
        nonce: u64,
        cfg: &'a [Attribute],
        bindings: &'a [Ident],
        side: RuleSide,
    ) -> Self {
        Self {
            facade,
            bindings,
            side,
            counters: StateRuleCounters::default(),
            terms: TermBuilder::new(facade, nonce, cfg, bindings),
            claim: false,
        }
    }

    pub(super) fn for_claim(mut self) -> Self {
        self.claim = true;
        self.terms = self.terms.for_claim();
        self
    }

    /// This side's role of a standalone `cells!`, `k!`, or `map!` role.
    fn side_role(&self, role: RuleRole) -> ProvenanceRole {
        role.on_side(self.side)
    }

    fn key(&self, role: RuleRole, ordinal: u32) -> ProvenanceKey {
        wire_key(self.side_role(role), ordinal)
    }

    fn term_key(&self, role: TermRole, ordinal: u32) -> ProvenanceKey {
        let side = match self.side {
            RuleSide::Left => TermSide::Left,
            RuleSide::Right => TermSide::Right,
        };
        wire_key(side.role(role), ordinal)
    }

    pub(super) fn expand_cells(
        &mut self,
        cells: &krs_syntax::CellsExpression,
        owner: &Path,
        slots: &mut WireSlots,
    ) -> crate::Result<WireRuleCells> {
        let facade = self.facade;
        let mut output = Vec::new();
        for entry in cells.entries() {
            let field_ordinal = take_counter(&mut self.counters.field)?;
            let field_key = self.key(RuleRole::CellsField, field_ordinal);
            let marker = cell_marker_function(entry.name());
            let cell_owner = entry.owner().unwrap_or(owner);
            let (wrapper_key, wrapper) = if let Some(path) = entry.wrapper() {
                let wrapper_ordinal = take_counter(&mut self.counters.wrapper)?;
                let computation = path.segments.iter().any(|segment| segment.ident == "KCell");
                if computation != matches!(entry.value(), StateTerm::KSequence(_)) {
                    return Err(ExpandError::new(
                        expand::CELL_STATE_FAMILY_MISMATCH,
                        path.span(),
                        "cell wrapper and rule state family disagree",
                    ));
                }
                let wrapper = if computation {
                    CellWrapper::KCell
                } else {
                    CellWrapper::Cell
                };
                (
                    Some(self.key(RuleRole::CellsWrapper, wrapper_ordinal)),
                    Some(wrapper),
                )
            } else {
                // A whole nested-cell entry has no wrapper (KF-016).
                (None, None)
            };
            let value = self.expand_state(entry.value(), slots)?;
            output.push(ProtocolRuleCell {
                field: WireCellReference {
                    key: field_key,
                    cell: WireCellIdentity {
                        owner: slots.type_slot(
                            quote!(#facade::HostTypeKey(#cell_owner::__krs_configuration_type_key)),
                        ),
                        field: slots.type_slot(quote!(#facade::HostTypeKey(#cell_owner::#marker))),
                    },
                },
                wrapper_key,
                wrapper,
                value,
            });
        }
        let remainder = self.expand_frame(cells.remainder(), RuleRole::CellsRemainder)?;
        Ok(WireRuleCells {
            key: self.key(RuleRole::CellsPayload, 0),
            cells: output,
            remainder,
        })
    }

    fn expand_state(
        &mut self,
        state: &StateTerm,
        slots: &mut WireSlots,
    ) -> crate::Result<ProtocolRuleStateTerm<WireTerm>> {
        match state {
            StateTerm::Term(term) => Ok(ProtocolRuleStateTerm::Term(
                self.expand_term(term.tree(), slots)?,
            )),
            StateTerm::KSequence(sequence) => Ok(ProtocolRuleStateTerm::KSequence(
                self.expand_k(sequence, slots)?,
            )),
            StateTerm::Map(map) => Ok(ProtocolRuleStateTerm::Map(self.expand_map(map, slots)?)),
            StateTerm::Group(term) => Ok(ProtocolRuleStateTerm::Group(
                self.expand_term(term.tree(), slots)?,
            )),
        }
    }

    fn expand_k(
        &mut self,
        sequence: &KSequence,
        slots: &mut WireSlots,
    ) -> crate::Result<ProtocolRuleKSequence<WireTerm>> {
        let payload_key = if sequence_has_role(sequence, ProvenanceRole::KSequencePayload)? {
            let ordinal = take_counter(&mut self.counters.k_payload)?;
            Some(self.key(RuleRole::KSequencePayload, ordinal))
        } else {
            None
        };
        let dot_k_key = if sequence.notation() == KSequenceNotation::DotK {
            let ordinal = take_counter(&mut self.counters.k_tail)?;
            Some(self.key(RuleRole::KSequenceTail, ordinal))
        } else {
            None
        };
        let notation = match sequence.notation() {
            KSequenceNotation::DotK => DescriptorKSequenceNotation::DotK,
            KSequenceNotation::Comma => DescriptorKSequenceNotation::Comma,
            KSequenceNotation::Operator => DescriptorKSequenceNotation::Operator,
        };
        let mut items = Vec::new();
        for item in sequence.items() {
            let ordinal = take_counter(&mut self.counters.k_item)?;
            items.push(ProtocolRuleKSequenceItem {
                key: self.key(RuleRole::KSequenceItem, ordinal),
                value: self.expand_term(item.tree(), slots)?,
            });
        }
        let tail = if sequence.notation() == KSequenceNotation::DotK {
            ProtocolRuleFrame::Exact
        } else {
            self.expand_frame(sequence.tail(), RuleRole::KSequenceTail)?
        };
        Ok(ProtocolRuleKSequence {
            payload_key,
            dot_k_key,
            notation,
            items,
            tail,
        })
    }

    fn expand_map(
        &mut self,
        map: &MapExpression,
        slots: &mut WireSlots,
    ) -> crate::Result<ProtocolRuleMap<WireTerm>> {
        let payload_key = if map_has_role(map, ProvenanceRole::MapPayload)? {
            let ordinal = take_counter(&mut self.counters.map_payload)?;
            Some(self.key(RuleRole::MapPayload, ordinal))
        } else {
            None
        };
        let body = match map.body() {
            MapBody::Empty { explicit_dot } => ProtocolRuleMapBody::Empty {
                explicit_dot: *explicit_dot,
            },
            MapBody::Items { items, remainder } => {
                let mut values = Vec::new();
                for item in items {
                    let ko = take_counter(&mut self.counters.map_key)?;
                    let vo = take_counter(&mut self.counters.map_value)?;
                    values.push(ProtocolRuleMapItem {
                        key_key: self.key(RuleRole::MapKey, ko),
                        key: self.expand_term(item.key().tree(), slots)?,
                        value_key: self.key(RuleRole::MapValue, vo),
                        value: self.expand_term(item.value().tree(), slots)?,
                    });
                }
                ProtocolRuleMapBody::Items {
                    items: values,
                    remainder: self.expand_frame(remainder, RuleRole::MapRemainder)?,
                }
            }
            MapBody::Update { base, key, value } => {
                let bo = take_counter(&mut self.counters.map_update_base)?;
                let ko = take_counter(&mut self.counters.map_key)?;
                let vo = take_counter(&mut self.counters.map_value)?;
                ProtocolRuleMapBody::Update {
                    base_key: self.key(RuleRole::MapUpdateBase, bo),
                    base: self.expand_term(base.tree(), slots)?,
                    key_key: self.key(RuleRole::MapKey, ko),
                    key: self.expand_term(key.tree(), slots)?,
                    value_key: self.key(RuleRole::MapValue, vo),
                    value: self.expand_term(value.tree(), slots)?,
                }
            }
        };
        Ok(ProtocolRuleMap { payload_key, body })
    }

    fn expand_frame(
        &mut self,
        frame: &StateMacroRemainder,
        role: RuleRole,
    ) -> crate::Result<ProtocolRuleFrame> {
        let side_role = self.side_role(role);
        let counter = match role {
            RuleRole::CellsRemainder => &mut self.counters.remainder,
            RuleRole::KSequenceTail => &mut self.counters.k_tail,
            RuleRole::MapRemainder => &mut self.counters.map_remainder,
            _ => unreachable!(),
        };
        match frame {
            StateMacroRemainder::Exact => Ok(ProtocolRuleFrame::Exact),
            StateMacroRemainder::Anonymous(_) => {
                let ordinal = take_counter(counter)?;
                Ok(ProtocolRuleFrame::Anonymous {
                    key: wire_key(side_role, ordinal),
                })
            }
            StateMacroRemainder::Bind { binding, .. } => {
                let ordinal = take_counter(counter)?;
                Ok(ProtocolRuleFrame::Bind {
                    key: wire_key(side_role, ordinal),
                    binding: binding.to_string(),
                })
            }
            StateMacroRemainder::Reuse { binding, .. } => {
                let ordinal = take_counter(counter)?;
                Ok(ProtocolRuleFrame::Reuse {
                    key: wire_key(side_role, ordinal),
                    binding: binding.to_string(),
                })
            }
        }
    }

    #[expect(
        clippy::too_many_lines,
        reason = "Exhaustive transport for the closed structured-term grammar."
    )]
    fn expand_term(&mut self, tree: &TermTree, slots: &mut WireSlots) -> crate::Result<WireTerm> {
        let facade = self.facade;
        match tree {
            TermTree::Application(application) => {
                let ordinal = take_counter(&mut self.counters.application)?;
                let key = self.term_key(TermRole::ApplicationHead, ordinal);
                let target = self
                    .terms
                    .application_wire_slot(application.head(), slots)?;
                let authored_path = self.terms.application_authored_path(application.head());
                let arguments = match application.arguments() {
                    TermArguments::Positional(values) => {
                        let mut arguments = Vec::new();
                        for value in values {
                            arguments.push(Box::new(self.expand_term(value, slots)?));
                        }
                        krs_ir::Arguments::Positional(arguments)
                    }
                    TermArguments::Named(values) => {
                        let mut arguments = Vec::new();
                        for argument in values {
                            let ordinal = take_counter(&mut self.counters.record_field)?;
                            arguments.push(krs_ir::NamedTermArgument {
                                key: self.term_key(TermRole::RecordFieldName, ordinal),
                                field: ProductionFieldId::new(argument.name().to_string())
                                    .expect("Rust field identifiers are valid production fields"),
                                value: Box::new(self.expand_term(argument.value(), slots)?),
                            });
                        }
                        krs_ir::Arguments::named(arguments)
                    }
                };
                Ok(WireTerm::Application {
                    head_class: DescriptorApplicationHeadClass::Applied,
                    reference: WireApplicationReference {
                        key: key.clone(),
                        target,
                        authored_path,
                    },
                    path_key: key,
                    arguments,
                })
            }
            TermTree::Reference(path) => {
                let ordinal = take_counter(&mut self.counters.reference)?;
                let key = self.term_key(TermRole::Reference, ordinal);
                if is_bound_ident_path(path, self.bindings) {
                    Ok(WireTerm::Variable {
                        key: key.clone(),
                        path_key: key,
                        name: spelling(path),
                    })
                } else {
                    let target = self.terms.application_wire_slot(path, slots)?;
                    Ok(WireTerm::Application {
                        head_class: DescriptorApplicationHeadClass::BareReference,
                        reference: WireApplicationReference {
                            key: key.clone(),
                            target,
                            authored_path: self.terms.application_authored_path(path),
                        },
                        path_key: key,
                        arguments: krs_ir::Arguments::default(),
                    })
                }
            }
            TermTree::Literal(literal) => {
                let ordinal = take_counter(&mut self.counters.literal)?;
                Ok(WireTerm::Literal {
                    key: self.term_key(TermRole::Literal, ordinal),
                    literal: wire_literal(literal),
                })
            }
            TermTree::Wildcard(_) => {
                if matches!(self.side, RuleSide::Right) {
                    return Err(ExpandError::new(
                        expand::RULE_RESULT_WILDCARD,
                        Span::call_site(),
                        "rule results cannot contain wildcards",
                    ));
                }
                let ordinal = take_counter(&mut self.counters.wildcard)?;
                Ok(WireTerm::Wildcard {
                    key: self.term_key(TermRole::Wildcard, ordinal),
                })
            }
            TermTree::IdToken { literal } => {
                if !self.claim {
                    return Err(ExpandError::new(
                        expand::CLAIM_ONLY_TERM,
                        literal.span(),
                        "id! is currently claim-only",
                    ));
                }
                let ordinal = take_counter(&mut self.counters.id_token)?;
                Ok(WireTerm::BuiltinToken {
                    key: wire_key(ProvenanceRole::ClaimIdToken, ordinal),
                    sort: BuiltinSort::Id,
                    value: literal.value(),
                })
            }
            TermTree::BytesToken { literal } => {
                if !self.claim {
                    return Err(ExpandError::new(
                        expand::CLAIM_ONLY_TERM,
                        literal.span(),
                        "bytes! is currently claim-only",
                    ));
                }
                let ordinal = take_counter(&mut self.counters.bytes_token)?;
                Ok(WireTerm::BuiltinToken {
                    key: wire_key(ProvenanceRole::ClaimBytesToken, ordinal),
                    sort: BuiltinSort::Bytes,
                    value: bytes_token::encode(&literal.value()),
                })
            }
            TermTree::Lexeme { sort, text } => self.terms.lexeme_wire(sort, text, slots),
            TermTree::SortTest {
                range,
                kind,
                sort,
                operand,
            } => {
                let (key, sort) = self.terms.sort_test_reference(*range, sort, slots)?;
                Ok(WireTerm::SortTest {
                    key,
                    kind: *kind,
                    sort,
                    operand: Box::new(self.expand_term(operand, slots)?),
                })
            }
            TermTree::As { binding, pattern } => {
                if matches!(self.side, RuleSide::Right) {
                    return Err(ExpandError::new(
                        expand::PATTERN_AS_OUTSIDE_LHS,
                        binding.span(),
                        format!(
                            "`{binding} @ pattern` binds only on a left-hand side (K's #as is LHS-only)"
                        ),
                    ));
                }
                let (key, binding_key) = self.terms.take_pattern_as(binding)?;
                Ok(WireTerm::As {
                    key,
                    binding_key,
                    name: binding.to_string(),
                    pattern: Box::new(self.expand_term(pattern, slots)?),
                })
            }
            TermTree::Or {
                range,
                alternatives,
            } => {
                if matches!(self.side, RuleSide::Right) {
                    return Err(ExpandError::new(
                        expand::PATTERN_OR_OUTSIDE_LHS,
                        range.first(),
                        "`A | B` alternatives occur only on a left-hand side (K's #Or); for Bool disjunction use bool::or or k::or_bool!",
                    ));
                }
                let key = self.terms.take_pattern_or(range.first())?;
                Ok(WireTerm::Or {
                    key,
                    alternatives: alternatives
                        .try_map_ref(|alternative| self.expand_term(alternative, slots))?,
                })
            }
            TermTree::Anonymous {
                sort,
                spelling: display_literal,
            } => {
                if !self.claim || matches!(self.side, RuleSide::Right) {
                    return Err(ExpandError::new(
                        expand::CLAIM_SUBJECT_ONLY_TERM,
                        display_literal.span(),
                        "anonymous! is allowed only in claim subjects",
                    ));
                }
                let ordinal = take_counter(&mut self.counters.anonymous)?;
                let path = call_site_path(sort)?;
                let key_fn = format_ident!(
                    "__krs_claim_anonymous_sort_{:016x}_{}",
                    self.terms.nonce,
                    self.terms.next_key,
                );
                self.terms.next_key += 1;
                let cfg = self.terms.cfg;
                self.terms.key_functions.push(quote! { #(#cfg)* #[doc(hidden)] fn #key_fn() -> ::core::any::TypeId { ::core::any::TypeId::of::<#path>() } });
                Ok(WireTerm::Anonymous {
                    key: wire_key(ProvenanceRole::ClaimAnonymous, ordinal),
                    sort: WireSortReference {
                        key: wire_key(ProvenanceRole::ClaimAnonymousSort, ordinal),
                        target: WireTypeReference {
                            slot: slots.type_slot(quote!(#facade::HostTypeKey(#key_fn))),
                            authored_path: spelling(sort),
                        },
                    },
                    spelling: display_literal.value(),
                })
            }
            TermTree::Matches { range, .. } => Err(ExpandError::new(
                expand::MATCHES_OUTSIDE_CONDITION,
                range.first(),
                "`k::matches!` is supported in requires and ensures conditions and in term results; in a cell value, test the cell's binder in `#[k::requires]`",
            )),
            TermTree::OrBool { arguments, .. } => {
                if !self.claim {
                    return Err(ExpandError::new(
                        expand::CLAIM_ONLY_TERM,
                        Span::call_site(),
                        "or_bool! is currently claim-only",
                    ));
                }
                let ordinal = take_counter(&mut self.counters.or_bool)?;
                let arguments =
                    arguments.try_map_ref(|argument| self.expand_term(argument, slots))?;
                Ok(WireTerm::OrBool {
                    key: wire_key(ProvenanceRole::ClaimOrBool, ordinal),
                    arguments,
                })
            }
            TermTree::Cell(cell) => {
                let ordinal = take_counter(&mut self.counters.application)?;
                let key = self.term_key(TermRole::ApplicationHead, ordinal);
                let declaration = self.terms.cell_declaration_reference(cell.owner(), slots)?;
                let mut fields = Vec::new();
                for field in cell.fields() {
                    let ordinal = take_counter(&mut self.counters.record_field)?;
                    fields.push(WireCellTermField {
                        key: self.term_key(TermRole::RecordFieldName, ordinal),
                        field: ProductionFieldId::new(field.name().to_string())
                            .expect("Rust fields are valid cell-field identities"),
                        value: Box::new(self.expand_term(field.value(), slots)?),
                    });
                }
                Ok(WireTerm::Cell {
                    key,
                    declaration,
                    fields,
                })
            }
        }
    }
}
