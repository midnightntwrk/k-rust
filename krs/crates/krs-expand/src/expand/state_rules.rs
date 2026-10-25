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
    KSequence, KSequenceNotation, MapBody, MapExpression, ProvenanceRole, RuleSide,
    StateMacroRemainder, StateRuleBindingKind, StateRuleReferenceKind, StateTerm, TermArguments,
    TermTree, TokenRange, parse_state_context_alias_item,
};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::ext::IdentExt;
use syn::spanned::Spanned;
use syn::{Attribute, Ident, Path};

use super::configuration::cell_marker_function;
use super::existentials::{ensures_condition, evaluation_step, existential_binders, fresh_binders};
use super::factory::{DescriptorFactory, FactoryPayload};
use super::island_checks::{consumed_state_island_import_checks, wrapper_type_check};
use super::nonce::expansion_nonce;
use super::terms::{
    KeyedTerm, NodeKind, TermBuilder, TermKeyReader, TermRole, TermSide, WireSlots, held_key,
    wire_sort_reference,
};
use super::tokens::{
    call_site_cfg_attributes, call_site_path, is_bound_ident_path, sort_type_tokens, spelling,
    wire_literal,
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
    let anchors = alias.descriptor_provenance(&attribute)?;
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
        let binding_name = binding.name().unraw().to_string();
        let kind = if binding.name() == alias.here() {
            ProtocolContextAliasBindingKind::Here
        } else {
            match binding.kind() {
                StateRuleBindingKind::Term => {
                    let sort = binding
                        .term_sort()
                        .expect("non-HERE terms retain explicit sorts");
                    let path = call_site_path(sort.sort())?;
                    let ty = sort_type_tokens(&facade, &path, sort.is_dynamic());
                    let key_fn =
                        format_ident!("__krs_context_alias_binding_{nonce:016x}_{term_ordinal}");
                    key_functions.push(quote! {
                        #(#cfg)*
                        #[doc(hidden)]
                        fn #key_fn() -> ::core::any::TypeId { ::core::any::TypeId::of::<#ty>() }
                    });
                    let sort_spelling = sort.sort_token_text();
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
                            binding.sort_key(),
                            &key_fn,
                            &sort_spelling,
                        )?,
                    }
                }
                StateRuleBindingKind::KSequenceFrame => {
                    ProtocolContextAliasBindingKind::KSequenceFrame
                }
                StateRuleBindingKind::MapFrame => ProtocolContextAliasBindingKind::MapFrame,
                StateRuleBindingKind::ConfigurationFrame => {
                    ProtocolContextAliasBindingKind::ConfigurationFrame
                }
                StateRuleBindingKind::InstancesFrame => {
                    return Err(super::rules::collection_placement(binding.name().span()));
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
    // `result = S`, K's `result(S)` (KF-021).
    let result = match attribute.result_sort() {
        Some(sort) => {
            let path = call_site_path(sort)?;
            let key_fn = format_ident!("__krs_context_alias_result_{nonce:016x}");
            key_functions.push(quote! {
                #(#cfg)*
                #[doc(hidden)]
                fn #key_fn() -> ::core::any::TypeId { ::core::any::TypeId::of::<#path>() }
            });
            Some(wire_sort_reference(
                &mut slots,
                &facade,
                attribute.result_key(),
                &key_fn,
                &spelling(sort),
            )?)
        }
        None => None,
    };

    let wire = WirePayload::ContextAlias(Box::new(WireContextAlias {
        declaration_key: held_key(alias.declaration_key())?,
        name_key: held_key(attribute.name_key())?,
        name: alias_name,
        here_key: held_key(attribute.here_key())?,
        here: here_name,
        pattern_key: held_key(alias.pattern_key())?,
        configuration: WireConfigurationReference {
            key: held_key(alias.configuration_type_key())?,
            configuration: WireTypeReference {
                slot: slots.type_slot(quote!(#facade::HostTypeKey(#configuration_key))),
                authored_path: configuration_spelling,
            },
        },
        bindings,
        pattern,
        result,
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

/// Expands a rule fn whose sides are `cells!` configurations: a
/// transition, or a context (KF-021), which shares the rule expansion
/// through its rule-attribute view.
///
/// # Panics
///
/// For another sentence than a transition or a context: no other sentence
/// has a `cells!` subject, and the callers dispatch on it.
#[expect(
    clippy::too_many_lines,
    reason = "The configuration rule and its complete provenance are expanded together."
)]
pub(super) fn configuration_rule(
    env: &dyn MacroEnvironment,
    item: TokenStream,
    sentence: krs_syntax::RuleSentence<'_>,
) -> crate::Result<TokenStream> {
    let context_view;
    let (rule, attribute, sentence_kind) = match sentence {
        krs_syntax::RuleSentence::Transition(attribute) => (
            krs_syntax::StateRuleItem::parse_tokens(item)?,
            attribute,
            krs_ir::ConfigurationSentenceKind::Transition,
        ),
        krs_syntax::RuleSentence::Context(context) => {
            let rule = krs_syntax::StateRuleItem::parse_context_tokens(item)?;
            context_view = context.rule_attribute(&rule.item().sig.ident);
            (
                rule,
                &context_view,
                krs_ir::ConfigurationSentenceKind::Context,
            )
        }
        krs_syntax::RuleSentence::Equation(_)
        | krs_syntax::RuleSentence::Simplification(_)
        | krs_syntax::RuleSentence::Alias
        | krs_syntax::RuleSentence::Desugar(_) => {
            unreachable!("only a transition or a context has a `cells!` subject")
        }
    };
    let context = sentence_kind == krs_ir::ConfigurationSentenceKind::Context;
    let facade = env.facade_path()?;
    let descriptor = krs_syntax::RuleDescriptor::state(&rule, sentence)?;
    let fallback = TokenRange::for_tokens(rule.item())?;
    let provenance = host_provenance(env, &facade, fallback, descriptor.anchors());
    let nonce = expansion_nonce(env, "configuration_rule", &rule.item().sig.ident, fallback);
    let factory = format_ident!("__krs_configuration_rule_{nonce:016x}");
    let subject_key = format_ident!("__krs_rule_configuration_left_{nonce:016x}");
    let result_key = format_ident!("__krs_rule_configuration_right_{nonce:016x}");
    let cfg = call_site_cfg_attributes(&rule.item().attrs)?;
    let subject_type = call_site_path(rule.subject_type())?;
    // A single-body rule (KF-011) has no result; its fn returns `()`.
    let result_type = rule.result_type().map(call_site_path).transpose()?;
    let subject_spelling = spelling(rule.subject_type());
    let result_spelling = rule.result_type().map(spelling);
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
        let name = binding.name().unraw().to_string();
        let kind = match binding.kind() {
            StateRuleBindingKind::Term => {
                let sort = binding
                    .term_sort()
                    .expect("term bindings retain explicit sorts");
                let path = call_site_path(sort.sort())?;
                let ty = sort_type_tokens(&facade, &path, sort.is_dynamic());
                let key_fn = format_ident!("__krs_rule_binding_sort_{nonce:016x}_{term_ordinal}");
                binding_key_functions.push(quote! {
                    #(#cfg)*
                    #[doc(hidden)]
                    fn #key_fn() -> ::core::any::TypeId {
                        ::core::any::TypeId::of::<#ty>()
                    }
                });
                let authored = sort.sort_token_text();
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
                        binding.sort_key(),
                        &key_fn,
                        &authored,
                    )?,
                }
            }
            StateRuleBindingKind::KSequenceFrame => ProtocolRuleBindingKind::KSequenceFrame,
            StateRuleBindingKind::MapFrame => ProtocolRuleBindingKind::MapFrame,
            StateRuleBindingKind::ConfigurationFrame => ProtocolRuleBindingKind::ConfigurationFrame,
            StateRuleBindingKind::InstancesFrame => ProtocolRuleBindingKind::InstancesFrame,
        };
        bindings.push(ProtocolRuleBinding { name, kind });
    }
    // A result and a condition see every variable the left side binds: the
    // term binders and the computation and map remainders (`Tail:K`,
    // `Rest:Map`). The configuration and instance remainders bind none.
    let remainder_idents = rule
        .bindings()
        .iter()
        .filter(|binding| {
            matches!(
                binding.kind(),
                StateRuleBindingKind::KSequenceFrame | StateRuleBindingKind::MapFrame
            )
        })
        .map(|binding| binding.name().clone())
        .collect::<Vec<_>>();
    let requires_idents = binding_idents
        .iter()
        .chain(&remainder_idents)
        .cloned()
        .collect::<Vec<_>>();
    // The result and the ensures condition also see the existentials.
    let result_idents = requires_idents
        .iter()
        .cloned()
        .chain(rule.existentials().names())
        .collect::<Vec<_>>();
    let (existentials, existential_key_functions) =
        existential_binders(rule.existentials(), &facade, nonce, &cfg, &mut slots)?;
    let (fresh, fresh_key_functions) =
        fresh_binders(rule.existentials(), &facade, nonce, &cfg, &mut slots)?;
    let (evaluation, evaluation_key_function) = evaluation_step(
        attribute,
        rule.existentials(),
        (&facade, nonce, &cfg),
        &mut slots,
    )?;
    let mut left = StateRuleBuilder::new(&facade, nonce, &cfg, &binding_idents, RuleSide::Left);
    left.terms.set_rewrites(rule.result().is_none());
    let subject = left.expand_cells(rule.subject(), &subject_type, &mut slots)?;
    let mut right = StateRuleBuilder::new(
        &facade,
        nonce ^ 0x8000_0000_0000_0000,
        &cfg,
        &result_idents,
        RuleSide::Right,
    );
    let result = match (rule.result(), &result_type) {
        (Some(result), Some(result_type)) => {
            Some(right.expand_cells(result, result_type, &mut slots)?)
        }
        _ => None,
    };
    let mut condition_builder = TermBuilder::new(
        &facade,
        nonce ^ 0x4000_0000_0000_0000,
        &cfg,
        &requires_idents,
    );
    let requires = if let Some(condition) = rule.requires() {
        let term = condition_builder.expand_wire(
            KeyedTerm::of(condition.term()),
            TermSide::Requires,
            &mut slots,
        )?;
        Some(WireRuleCondition {
            key: held_key(condition.term().keys().payload())?,
            term,
        })
    } else {
        None
    };
    let mut ensures_builder =
        TermBuilder::new(&facade, nonce ^ 0x2000_0000_0000_0000, &cfg, &result_idents);
    let ensures = ensures_condition(rule.existentials(), &mut ensures_builder, &mut slots)?;
    let mut key_functions = left.terms.key_functions;
    key_functions.extend(right.terms.key_functions);
    key_functions.extend(condition_builder.key_functions);
    key_functions.extend(ensures_builder.key_functions);
    key_functions.extend(binding_key_functions);
    key_functions.extend(existential_key_functions);
    key_functions.extend(fresh_key_functions);
    key_functions.extend(evaluation_key_function);
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
    let label = attribute
        .label()
        .map(|label| -> crate::Result<_> {
            Ok(DescriptorRuleLabel {
                key: held_key(attribute.label_key())?,
                name: label.value(),
            })
        })
        .transpose()?;
    let priority = attribute
        .transition_priority()
        .map(|(_, value)| -> crate::Result<_> {
            Ok(DescriptorRulePriority {
                key: held_key(attribute.owise_key().or_else(|| attribute.priority_key()))?,
                value,
            })
        })
        .transpose()?;
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
        .map(|group| -> crate::Result<_> {
            Ok(krs_ir::DescriptorNondetGroup {
                key: held_key(attribute.nondet_key())?,
                name: syn::ext::IdentExt::unraw(group).to_string(),
            })
        })
        .transpose()?;
    let wire = WirePayload::ConfigurationRule(Box::new(WireConfigurationRule {
        sentence_kind,
        label,
        priority,
        nondet,
        requires,
        claim: None,
        pattern_key: held_key(rule.pattern_key())?,
        subject_configuration: WireConfigurationReference {
            key: held_key(rule.subject_type_key())?,
            configuration: WireTypeReference {
                slot: slots.type_slot(quote!(#facade::HostTypeKey(#subject_key))),
                authored_path: subject_spelling,
            },
        },
        result_key: result
            .is_some()
            .then(|| held_key(rule.result_key()))
            .transpose()?,
        result_configuration: result_spelling
            .map(|authored_path| -> crate::Result<_> {
                Ok(WireConfigurationReference {
                    key: held_key(rule.result_type_key())?,
                    configuration: WireTypeReference {
                        slot: slots.type_slot(quote!(#facade::HostTypeKey(#result_key))),
                        authored_path,
                    },
                })
            })
            .transpose()?,
        bindings,
        subject,
        result,
        existentials,
        ensures,
        fresh,
        evaluation,
    }));
    let wire = serde_json::to_string(&wire).expect("KRS wire values serialize");
    let slot_tokens = slots.tokens();

    let factory_tokens = DescriptorFactory {
        facade: &facade,
        factory: &factory,
        name: quote!(#name),
        item_kind: if context {
            quote!(#facade::ItemKind::Context)
        } else {
            quote!(#facade::ItemKind::Rule)
        },
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

    let (output_type, result_key_function) = match &result_type {
        Some(result_type) => (
            quote!(-> #result_type),
            quote! {
                #(#cfg)*
                #[doc(hidden)]
                fn #result_key() -> ::core::any::TypeId {
                    ::core::any::TypeId::of::<#result_type>()
                }
            },
        ),
        None => (TokenStream::new(), TokenStream::new()),
    };
    Ok(quote! {
        #(#attrs)*
        #visibility #fn_token #name_ident(
            #(#ordinary_inputs,)*
            __krs_symbolic_configuration: #subject_type,
        ) #output_type {
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

        #result_key_function

        #(#key_functions)*

        #factory_tokens
    })
}

pub(super) struct StateRuleBuilder<'a> {
    facade: &'a Path,
    bindings: &'a [Ident],
    side: RuleSide,
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
            terms: TermBuilder::new(facade, nonce, cfg, bindings),
            claim: false,
        }
    }

    /// Continues the key-function numbering of `previous`, a term subject
    /// expanded before this `cells!` pattern (an equation's function context,
    /// KF-025).
    pub(super) fn continue_subject(&mut self, previous: &TermBuilder<'_>) {
        self.terms.next_key = previous.next_key;
    }

    pub(super) fn for_claim(mut self) -> Self {
        self.claim = true;
        self.terms = self.terms.for_claim();
        self
    }

    fn term_role(&self, role: TermRole) -> ProvenanceRole {
        let side = match self.side {
            RuleSide::Left => TermSide::Left,
            RuleSide::Right => TermSide::Right,
        };
        side.role(role)
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
            let field_key = held_key(entry.name_key())?;
            let marker = cell_marker_function(entry.name());
            let cell_owner = entry.owner().unwrap_or(owner);
            let (wrapper_key, wrapper) = if let Some(path) = entry.wrapper() {
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
                (Some(held_key(entry.wrapper_key())?), Some(wrapper))
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
        let remainder = Self::expand_frame(cells.remainder(), cells.remainder_key())?;
        Ok(WireRuleCells {
            key: held_key(cells.payload_key())?,
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
                self.expand_keyed(KeyedTerm::of(term), slots)?,
            )),
            StateTerm::KSequence(sequence) => Ok(ProtocolRuleStateTerm::KSequence(
                self.expand_k(sequence, slots)?,
            )),
            StateTerm::Map(map) => Ok(ProtocolRuleStateTerm::Map(self.expand_map(map, slots)?)),
            StateTerm::Group(term) => Ok(ProtocolRuleStateTerm::Group(
                self.expand_keyed(KeyedTerm::of(term), slots)?,
            )),
            StateTerm::Present(inner) => Ok(ProtocolRuleStateTerm::Present {
                value: Box::new(self.expand_state(inner, slots)?),
            }),
            StateTerm::Absent(_) => Ok(ProtocolRuleStateTerm::Absent),
            StateTerm::Instances(list) => Ok(ProtocolRuleStateTerm::Instances(
                self.expand_instances(list, slots)?,
            )),
        }
    }

    /// Expands a collection entry (KF-023): instance, child-field, and rest
    /// keys follow the parser's traversal order.
    fn expand_instances(
        &mut self,
        list: &krs_syntax::InstanceList,
        slots: &mut WireSlots,
    ) -> crate::Result<krs_ir::ProtocolRuleInstances<WireTerm>> {
        let front = list
            .front()
            .iter()
            .map(|item| self.expand_instance(item, slots))
            .collect::<crate::Result<Vec<_>>>()?;
        let rest = Self::expand_frame(list.rest(), list.rest_key())?;
        let back = list
            .back()
            .iter()
            .map(|item| self.expand_instance(item, slots))
            .collect::<crate::Result<Vec<_>>>()?;
        Ok(krs_ir::ProtocolRuleInstances {
            delimiter: match list.delimiter() {
                krs_syntax::InstanceListDelimiter::Brace => krs_ir::InstanceDelimiter::Brace,
                krs_syntax::InstanceListDelimiter::Bracket => krs_ir::InstanceDelimiter::Bracket,
            },
            front,
            rest,
            back,
        })
    }

    fn expand_instance(
        &mut self,
        item: &krs_syntax::InstanceItem,
        slots: &mut WireSlots,
    ) -> crate::Result<krs_ir::ProtocolRuleInstance<WireTerm>> {
        let key = held_key(item.key())?;
        let mut fields = Vec::new();
        for field in item.fields() {
            fields.push(krs_ir::ProtocolRuleInstanceField {
                key: held_key(field.name_key())?,
                field: field.name().to_string(),
                value: self.expand_state(field.value(), slots)?,
            });
        }
        Ok(krs_ir::ProtocolRuleInstance {
            key,
            label: item.label().map(ToString::to_string),
            fields,
            rest: instance_rest(item.rest()),
        })
    }

    fn expand_k(
        &mut self,
        sequence: &KSequence,
        slots: &mut WireSlots,
    ) -> crate::Result<ProtocolRuleKSequence<WireTerm>> {
        let payload_key = if sequence.payload_key().is_some() {
            Some(held_key(sequence.payload_key())?)
        } else {
            None
        };
        let dot_k_key = if sequence.notation() == KSequenceNotation::DotK {
            Some(held_key(sequence.tail_key())?)
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
            items.push(ProtocolRuleKSequenceItem {
                key: held_key(item.keys().payload())?,
                value: self.expand_keyed(KeyedTerm::of(item), slots)?,
            });
        }
        let tail = if sequence.notation() == KSequenceNotation::DotK {
            ProtocolRuleFrame::Exact
        } else {
            Self::expand_frame(sequence.tail(), sequence.tail_key())?
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
        let payload_key = if map.payload_key().is_some() {
            Some(held_key(map.payload_key())?)
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
                    values.push(ProtocolRuleMapItem {
                        key_key: held_key(item.key().keys().payload())?,
                        key: self.expand_keyed(KeyedTerm::of(item.key()), slots)?,
                        value_key: held_key(item.value().keys().payload())?,
                        value: self.expand_keyed(KeyedTerm::of(item.value()), slots)?,
                    });
                }
                ProtocolRuleMapBody::Items {
                    items: values,
                    remainder: Self::expand_frame(remainder, map.remainder_key())?,
                }
            }
            MapBody::Update { base, key, value } => ProtocolRuleMapBody::Update {
                base_key: held_key(base.keys().payload())?,
                base: self.expand_keyed(KeyedTerm::of(base), slots)?,
                key_key: held_key(key.keys().payload())?,
                key: self.expand_keyed(KeyedTerm::of(key), slots)?,
                value_key: held_key(value.keys().payload())?,
                value: self.expand_keyed(KeyedTerm::of(value), slots)?,
            },
        };
        Ok(ProtocolRuleMap { payload_key, body })
    }

    /// A remainder, keyed `read`, the remainder's own key.
    fn expand_frame(
        frame: &StateMacroRemainder,
        read: Option<&ProvenanceKey>,
    ) -> crate::Result<ProtocolRuleFrame> {
        match frame {
            StateMacroRemainder::Exact => Ok(ProtocolRuleFrame::Exact),
            StateMacroRemainder::Anonymous(_) => Ok(ProtocolRuleFrame::Anonymous {
                key: held_key(read)?,
            }),
            StateMacroRemainder::Bind { binding, .. } => Ok(ProtocolRuleFrame::Bind {
                key: held_key(read)?,
                binding: binding.unraw().to_string(),
            }),
            StateMacroRemainder::Reuse { binding, .. } => Ok(ProtocolRuleFrame::Reuse {
                key: held_key(read)?,
                binding: binding.unraw().to_string(),
            }),
        }
    }

    fn expand_keyed(
        &mut self,
        term: KeyedTerm<'_>,
        slots: &mut WireSlots,
    ) -> crate::Result<WireTerm> {
        self.expand_term(term.tree(), &mut term.reader(), slots)
    }

    #[expect(
        clippy::too_many_lines,
        reason = "Exhaustive transport for the closed structured-term grammar."
    )]
    fn expand_term(
        &mut self,
        tree: &TermTree,
        keys: &mut TermKeyReader<'_>,
        slots: &mut WireSlots,
    ) -> crate::Result<WireTerm> {
        let facade = self.facade;
        match tree {
            TermTree::Application(application) => {
                // A `cells!` term keys no path: the head's key stands for it.
                keys.pass_path(application.head())?;
                let node = keys.node(
                    NodeKind::ApplicationHead,
                    TokenRange::for_tokens(application.head())?,
                )?;
                let key = node.key(self.term_role(TermRole::ApplicationHead))?;
                let target = self.terms.application_wire_slot(
                    application.head(),
                    application.is_notation(),
                    slots,
                )?;
                let authored_path = spelling(application.head());
                let instance = self
                    .terms
                    .application_instance_wire(application, node, slots)?;
                let arguments = match application.arguments() {
                    TermArguments::Positional(values) => {
                        let mut arguments = Vec::new();
                        for value in values {
                            arguments.push(Box::new(self.expand_term(value, keys, slots)?));
                        }
                        krs_ir::Arguments::Positional(arguments)
                    }
                    TermArguments::Named(values) => {
                        let mut arguments = Vec::new();
                        for argument in values {
                            arguments.push(krs_ir::NamedTermArgument {
                                key: keys.record_field(argument.name())?,
                                field: ProductionFieldId::new(argument.name().to_string())
                                    .expect("Rust field identifiers are valid production fields"),
                                value: Box::new(self.expand_term(argument.value(), keys, slots)?),
                            });
                        }
                        krs_ir::Arguments::named(arguments)
                    }
                };
                if let Some(base) = application.update() {
                    return Err(reference_record_update(base_span(base, application.head())));
                }
                Ok(WireTerm::Application {
                    instance,
                    head_class: DescriptorApplicationHeadClass::Applied,
                    reference: WireApplicationReference {
                        key: key.clone(),
                        target,
                        authored_path,
                    },
                    path_key: key,
                    arguments,
                    update: None,
                    open: application.is_open(),
                })
            }
            TermTree::Reference(path) => {
                keys.pass_path(path)?;
                let key = keys
                    .node(NodeKind::Reference, TokenRange::for_tokens(path)?)?
                    .key(self.term_role(TermRole::Reference))?;
                if is_bound_ident_path(path, self.bindings) {
                    Ok(WireTerm::Variable {
                        key: key.clone(),
                        path_key: key,
                        name: super::terms::binder_spelling(path),
                    })
                } else {
                    let target = self.terms.application_wire_slot(path, false, slots)?;
                    Ok(WireTerm::Application {
                        instance: Vec::new(),
                        head_class: DescriptorApplicationHeadClass::BareReference,
                        reference: WireApplicationReference {
                            key: key.clone(),
                            target,
                            authored_path: spelling(path),
                        },
                        path_key: key,
                        arguments: krs_ir::Arguments::default(),
                        update: None,
                        open: false,
                    })
                }
            }
            TermTree::Literal(literal) => Ok(WireTerm::Literal {
                key: keys
                    .node(NodeKind::Literal, literal.range()?)?
                    .key(self.term_role(TermRole::Literal))?,
                literal: wire_literal(literal),
            }),
            TermTree::Wildcard(range) => {
                if matches!(self.side, RuleSide::Right) {
                    return Err(ExpandError::at_range(
                        expand::RULE_RESULT_WILDCARD,
                        *range,
                        "rule results cannot contain wildcards",
                    ));
                }
                Ok(WireTerm::Wildcard {
                    key: keys.wildcard(*range)?,
                })
            }
            TermTree::IdToken { literal } => Ok(WireTerm::BuiltinToken {
                key: keys
                    .node(NodeKind::IdToken, TokenRange::for_tokens(literal)?)?
                    .key(ProvenanceRole::ClaimIdToken)?,
                sort: BuiltinSort::Id,
                value: literal.value(),
            }),
            TermTree::BytesToken { literal } => Ok(WireTerm::BuiltinToken {
                key: keys
                    .node(NodeKind::BytesToken, TokenRange::for_tokens(literal)?)?
                    .key(ProvenanceRole::ClaimBytesToken)?,
                sort: BuiltinSort::Bytes,
                value: bytes_token::encode(&literal.value()),
            }),
            TermTree::Lexeme { sort, text } => {
                let node = keys.node(NodeKind::Lexeme, TokenRange::for_tokens(text)?)?;
                self.terms.lexeme_wire(sort, text, node, slots)
            }
            TermTree::SortTest {
                range,
                kind,
                sort,
                operand,
            } => {
                let node = keys.node(NodeKind::SortTest, *range)?;
                let (key, sort) = self.terms.sort_test_reference(sort, node, slots)?;
                Ok(WireTerm::SortTest {
                    key,
                    kind: *kind,
                    sort,
                    operand: Box::new(self.expand_term(operand, keys, slots)?),
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
                let node = keys.node(NodeKind::As, TokenRange::for_tokens(binding)?)?;
                let (key, binding_key) = self.terms.take_pattern_as(binding, node)?;
                Ok(WireTerm::As {
                    key,
                    binding_key,
                    name: binding.unraw().to_string(),
                    pattern: Box::new(self.expand_term(pattern, keys, slots)?),
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
                        "`A | B` alternatives occur only on a left-hand side (K's #Or); for Bool disjunction use `||`, bool::or, or k::or_bool!",
                    ));
                }
                let node = keys.node(NodeKind::Or, *range)?;
                let key = TermBuilder::take_pattern_or(node)?;
                Ok(WireTerm::Or {
                    key,
                    alternatives: alternatives
                        .try_map_ref(|alternative| self.expand_term(alternative, keys, slots))?,
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
                let node = keys.node(
                    NodeKind::Anonymous,
                    TokenRange::for_tokens(display_literal)?,
                )?;
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
                    key: node.key(ProvenanceRole::ClaimAnonymous)?,
                    sort: WireSortReference {
                        key: node.key(ProvenanceRole::ClaimAnonymousSort)?,
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
            TermTree::Let { range, .. } => Err(ExpandError::new(
                expand::LET_OUTSIDE_TERM,
                range.first(),
                "`let` blocks (K's #let) are supported in requires and ensures conditions and in term results; in a cell value, compute the value with a function",
            )),
            TermTree::Closure { range, .. } => Err(ExpandError::new(
                expand::ML_PLACEMENT,
                range.first(),
                "an `ml::exists` closure is a predicate (K's #Exists); it belongs in a claim's requires or ensures condition, not in a cell value",
            )),
            TermTree::Rewrite {
                range, from, to, ..
            } => {
                let node = keys.node(NodeKind::Rewrite, *range)?;
                self.terms
                    .enter_rewrite(*range, matches!(self.side, RuleSide::Left))?;
                let from = self.expand_term(from, keys, slots);
                let to = match (from.is_ok(), to) {
                    (true, Some(to)) => {
                        Some(self.expand_term(to, keys, slots).map(Box::new)).transpose()
                    }
                    _ => Ok(None),
                };
                self.terms.leave_rewrite();
                super::terms::rewrite_wire(node, from?, to?)
            }
            TermTree::OrBool { range, arguments } => {
                if !self.claim {
                    return Err(ExpandError::at_range(
                        expand::CLAIM_ONLY_TERM,
                        *range,
                        "or_bool! is currently claim-only",
                    ));
                }
                let node = keys.node(NodeKind::OrBool, *range)?;
                let arguments =
                    arguments.try_map_ref(|argument| self.expand_term(argument, keys, slots))?;
                Ok(WireTerm::OrBool {
                    key: node.key(ProvenanceRole::ClaimOrBool)?,
                    arguments,
                })
            }
            TermTree::Cell(cell) => {
                keys.pass_path(cell.owner())?;
                let key = keys
                    .node(
                        NodeKind::ApplicationHead,
                        TokenRange::for_tokens(cell.owner())?,
                    )?
                    .key(self.term_role(TermRole::ApplicationHead))?;
                let declaration = self.terms.cell_declaration_reference(cell.owner(), slots)?;
                let mut fields = Vec::new();
                for field in cell.fields() {
                    fields.push(WireCellTermField {
                        key: keys.record_field(field.name())?,
                        field: ProductionFieldId::new(field.name().to_string())
                            .expect("Rust fields are valid cell-field identities"),
                        value: Box::new(self.expand_term(field.value(), keys, slots)?),
                    });
                }
                // A reference `cells!` term names every child: the readable
                // forms that leave some out are written in full by `krs
                // expand`.
                if cell.is_open() || cell.update().is_some() {
                    return Err(reference_record_update(cell.range().first()));
                }
                Ok(WireTerm::Cell {
                    key,
                    declaration,
                    fields,
                    open: false,
                    update: None,
                })
            }
        }
    }
}

/// The wire form of an instance record's rest (KF-023).
pub(super) fn instance_rest(rest: &krs_syntax::InstanceRest) -> krs_ir::ProtocolInstanceRest {
    match rest {
        krs_syntax::InstanceRest::Exact => krs_ir::ProtocolInstanceRest::Exact,
        krs_syntax::InstanceRest::Open(_) => krs_ir::ProtocolInstanceRest::Open,
        krs_syntax::InstanceRest::Update { label, .. } => krs_ir::ProtocolInstanceRest::Update {
            label: label.to_string(),
        },
    }
}

/// A record update or a `..` group pattern in a reference `cells!` term,
/// which names every field: the readable spellings are written in full by
/// `krs expand`.
fn reference_record_update(span: proc_macro2::Span) -> ExpandError {
    ExpandError::new(
        expand::INVALID_RECORD_UPDATE,
        span,
        "a `cells!` term names every field: write each one (`_` for a field a pattern leaves unconstrained); `Ctor { f: e, ..t }` and a `..` group pattern are readable-record notation",
    )
}

/// The update's base when it is a name, and the record's constructor otherwise.
fn base_span(base: &TermTree, head: &syn::Path) -> proc_macro2::Span {
    match base {
        TermTree::Reference(path) => syn::spanned::Spanned::span(path),
        _ => syn::spanned::Spanned::span(head),
    }
}
