//! Whole-configuration rules and named contexts: cells-form `#[k::rule]` and `#[k::context_alias]`.

use krs_ir::bytes_token;
use krs_syntax::KrsSyntax;
use krs_syntax::{
    KSequence, KSequenceNotation, MapBody, MapExpression, ProvenanceAnchor, ProvenanceRole,
    RuleRole, RuleSide, StateMacroRemainder, StateRuleBindingKind, StateRuleReferenceKind,
    StateTerm, TermArguments, TermTree, TokenRange, parse_state_context_alias_item, role_tokens,
};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::spanned::Spanned;
use syn::{Attribute, Ident, Path};

use super::configuration::cell_marker_function;
use super::factory::{DescriptorFactory, IdentityCheck};
use super::island_checks::{consumed_state_island_import_checks, wrapper_type_check};
use super::nonce::expansion_nonce;
use super::rules::{rule_label_tokens, rule_owise_tokens};
use super::terms::{TermBuilder, TermRole, TermSide};
use super::tokens::{
    call_site_cfg_attributes, call_site_path, is_bound_ident_path, k_notation, literal_tokens,
    map_has_role, option_key, provenance_key, sequence_has_role, sort_type_tokens, spelling,
    take_counter,
};
use crate::environment::MacroEnvironment;
use crate::provenance::host_provenance;

#[allow(clippy::too_many_lines)]
pub(crate) fn context_alias(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let rule_binding_type_role = ProvenanceRole::RuleBindingType;
    let context_alias_declaration_role = ProvenanceRole::ContextAliasDeclaration;
    let context_alias_name_role = ProvenanceRole::ContextAliasName;
    let context_alias_here_role = ProvenanceRole::ContextAliasHere;
    let rule_pattern_role = ProvenanceRole::RulePattern;
    let rule_type_role = ProvenanceRole::RuleType;
    let attribute = krs_syntax::ContextAliasAttribute::parse_tokens(attributes)?;
    let alias = parse_state_context_alias_item(item, attribute.here())?;
    let facade = env.facade_path()?;
    let rule_binding_type_role = role_tokens(rule_binding_type_role, &facade);
    let context_alias_declaration_role = role_tokens(context_alias_declaration_role, &facade);
    let context_alias_name_role = role_tokens(context_alias_name_role, &facade);
    let context_alias_here_role = role_tokens(context_alias_here_role, &facade);
    let rule_pattern_role = role_tokens(rule_pattern_role, &facade);
    let rule_type_role = role_tokens(rule_type_role, &facade);
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
    let mut bindings = Vec::new();
    let mut key_functions = Vec::new();
    let mut term_ordinal = 0_u32;
    for binding in alias.bindings() {
        let binding_name = binding.name().to_string();
        let kind = if binding.name() == alias.here() {
            quote!(#facade::ProtocolContextAliasBindingKind::Here)
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
                        syn::Error::new(binding.name().span(), "too many context bindings")
                    })?;
                    quote!(#facade::ProtocolContextAliasBindingKind::Term {
                        sort: #facade::HostSortReference {
                            key: #facade::ProvenanceKey::new(#rule_binding_type_role, #ordinal),
                            target: #facade::HostTypeReference {
                                key: #facade::HostTypeKey(#key_fn),
                                authored_path: #sort_spelling.to_owned(),
                            },
                        },
                    })
                }
                StateRuleBindingKind::KSequenceFrame => {
                    quote!(#facade::ProtocolContextAliasBindingKind::KSequenceFrame)
                }
                StateRuleBindingKind::MapFrame => {
                    quote!(#facade::ProtocolContextAliasBindingKind::MapFrame)
                }
                StateRuleBindingKind::ConfigurationFrame => {
                    quote!(#facade::ProtocolContextAliasBindingKind::ConfigurationFrame)
                }
            }
        };
        bindings.push(quote!(#facade::ProtocolContextAliasBinding {
            name: #binding_name.to_owned(), kind: #kind
        }));
    }
    let mut builder = StateRuleBuilder::new(&facade, nonce, &cfg, &binding_idents, RuleSide::Left);
    let pattern = builder.expand_cells(alias.pattern(), &configuration_type)?;
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

    let factory_tokens = DescriptorFactory {
        facade: &facade,
        factory: &factory,
        name: quote!(#rust_name),
        item_kind: quote!(#facade::ItemKind::ContextAlias),
        disambiguator: quote!(""),
        identity_check: IdentityCheck::Expect(
            "Cargo and Rust macro context form a valid context alias identity",
        ),
        declared_type: quote!(::core::option::Option::None),
        payload: quote! {
            #facade::HostDescriptorPayload::ContextAlias(::std::boxed::Box::new(
                #facade::HostContextAlias {
                    declaration_key: #facade::ProvenanceKey::new(#context_alias_declaration_role, 0),
                    name_key: #facade::ProvenanceKey::new(#context_alias_name_role, 0),
                    name: #alias_name.to_owned(),
                    here_key: #facade::ProvenanceKey::new(#context_alias_here_role, 0),
                    here: #here_name.to_owned(),
                    pattern_key: #facade::ProvenanceKey::new(#rule_pattern_role, 0),
                    configuration: #facade::HostConfigurationReference {
                        key: #facade::ProvenanceKey::new(#rule_type_role, 0),
                        configuration: #facade::HostTypeReference {
                            key: #facade::HostTypeKey(#configuration_key),
                            authored_path: #configuration_spelling.to_owned(),
                        },
                    },
                    bindings: ::std::vec![#(#bindings),*],
                    pattern: #pattern,
                }
            ))
        },
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

#[allow(clippy::too_many_lines)]
pub(super) fn configuration_rule(
    env: &dyn MacroEnvironment,
    item: TokenStream,
    attribute: &krs_syntax::RuleAttribute,
) -> syn::Result<TokenStream> {
    let rule_binding_type_role = ProvenanceRole::RuleBindingType;
    let rule_requires_role = ProvenanceRole::RuleRequires;
    let rule_pattern_role = ProvenanceRole::RulePattern;
    let rule_type_role = ProvenanceRole::RuleType;
    let rule_result_role = ProvenanceRole::RuleResult;
    let rule_result_type_role = ProvenanceRole::RuleResultType;
    let rule = krs_syntax::StateRuleItem::parse_tokens(item)?;
    let facade = env.facade_path()?;
    let rule_binding_type_role = role_tokens(rule_binding_type_role, &facade);
    let rule_requires_role = role_tokens(rule_requires_role, &facade);
    let rule_pattern_role = role_tokens(rule_pattern_role, &facade);
    let rule_type_role = role_tokens(rule_type_role, &facade);
    let rule_result_role = role_tokens(rule_result_role, &facade);
    let rule_result_type_role = role_tokens(rule_result_type_role, &facade);
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
                    syn::Error::new(binding.name().span(), "too many term bindings")
                })?;
                quote! {
                    #facade::ProtocolRuleBindingKind::Term {
                        sort: #facade::HostSortReference {
                            key: #facade::ProvenanceKey::new(#rule_binding_type_role, #ordinal),
                            target: #facade::HostTypeReference {
                                key: #facade::HostTypeKey(#key_fn),
                                authored_path: #authored.to_owned(),
                            },
                        },
                    }
                }
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
    let mut left = StateRuleBuilder::new(&facade, nonce, &cfg, &binding_idents, RuleSide::Left);
    let subject = left.expand_cells(rule.subject(), &subject_type)?;
    let mut right = StateRuleBuilder::new(
        &facade,
        nonce ^ 0x8000_0000_0000_0000,
        &cfg,
        &binding_idents,
        RuleSide::Right,
    );
    let result = right.expand_cells(rule.result(), &result_type)?;
    let mut condition_builder = TermBuilder::new(
        &facade,
        nonce ^ 0x4000_0000_0000_0000,
        &cfg,
        &binding_idents,
    );
    let requires = if let Some(condition) = rule.requires() {
        let term = condition_builder.expand(condition.term().tree(), TermSide::Requires)?;
        quote! {
            ::core::option::Option::Some(#facade::HostRuleCondition {
                key: #facade::ProvenanceKey::new(#rule_requires_role, 0),
                term: #term,
            })
        }
    } else {
        quote!(::core::option::Option::None)
    };
    let mut key_functions = left.terms.key_functions;
    key_functions.extend(right.terms.key_functions);
    key_functions.extend(condition_builder.key_functions);
    key_functions.extend(binding_key_functions);
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
    let label = rule_label_tokens(&facade, attribute);
    let priority = rule_owise_tokens(&facade, attribute);
    let mut wrapper_checks = Vec::new();
    for candidate in rule.reference_candidates()? {
        if candidate.kind() == StateRuleReferenceKind::CellWrapper {
            let path = call_site_path(candidate.path())?;
            wrapper_checks.push(wrapper_type_check(&path));
        }
    }
    let island_import_checks = consumed_state_island_import_checks(original);

    let factory_tokens = DescriptorFactory {
        facade: &facade,
        factory: &factory,
        name: quote!(#name),
        item_kind: quote!(#facade::ItemKind::Rule),
        disambiguator: quote!(""),
        identity_check: IdentityCheck::Expect(
            "Cargo and Rust macro context form a valid host identity",
        ),
        declared_type: quote!(::core::option::Option::None),
        payload: quote! {
            #facade::HostDescriptorPayload::ConfigurationRule(
                ::std::boxed::Box::new(#facade::HostConfigurationRule {
                    sentence_kind: #facade::SentenceKind::Transition,
                    label: #label,
                    priority: #priority,
                    requires: #requires,
                    claim: ::core::option::Option::None,
                    pattern_key: #facade::ProvenanceKey::new(#rule_pattern_role, 0),
                    subject_configuration: #facade::HostConfigurationReference {
                        key: #facade::ProvenanceKey::new(#rule_type_role, 0),
                        configuration: #facade::HostTypeReference {
                            key: #facade::HostTypeKey(#subject_key),
                            authored_path: #subject_spelling.to_owned(),
                        },
                    },
                    result_key: #facade::ProvenanceKey::new(#rule_result_role, 0),
                    result_configuration: #facade::HostConfigurationReference {
                        key: #facade::ProvenanceKey::new(#rule_result_type_role, 0),
                        configuration: #facade::HostTypeReference {
                            key: #facade::HostTypeKey(#result_key),
                            authored_path: #result_spelling.to_owned(),
                        },
                    },
                    bindings: ::std::vec![#(#bindings),*],
                    subject: #subject,
                    result: #result,
                })
            )
        },
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

    fn key(&self, role: RuleRole, ordinal: u32) -> TokenStream {
        provenance_key(self.facade, self.side_role(role), ordinal)
    }

    fn term_key(&self, role: TermRole, ordinal: u32) -> TokenStream {
        let side = match self.side {
            RuleSide::Left => TermSide::Left,
            RuleSide::Right => TermSide::Right,
        };
        provenance_key(self.facade, side.role(role), ordinal)
    }

    pub(super) fn expand_cells(
        &mut self,
        cells: &krs_syntax::CellsExpression,
        owner: &Path,
    ) -> syn::Result<TokenStream> {
        let facade = self.facade;
        let mut output = Vec::new();
        for entry in cells.entries() {
            let field_ordinal = take_counter(&mut self.counters.field)?;
            let wrapper_ordinal = take_counter(&mut self.counters.wrapper)?;
            let field_key = self.key(RuleRole::CellsField, field_ordinal);
            let wrapper_key = self.key(RuleRole::CellsWrapper, wrapper_ordinal);
            let marker = cell_marker_function(entry.name());
            let cell_owner = entry.owner().unwrap_or(owner);
            let computation = entry
                .wrapper()
                .segments
                .iter()
                .any(|segment| segment.ident == "KCell");
            if computation != matches!(entry.value(), StateTerm::KSequence(_)) {
                return Err(syn::Error::new(
                    entry.wrapper().span(),
                    "cell wrapper and rule state family disagree",
                ));
            }
            let wrapper = if computation {
                quote!(#facade::CellWrapper::KCell)
            } else {
                quote!(#facade::CellWrapper::Cell)
            };
            let value = self.expand_state(entry.value())?;
            output.push(quote! {
                #facade::ProtocolRuleCell {
                    field: #facade::HostCellReference {
                        key: #field_key,
                        cell: #facade::HostCellIdentity {
                            owner: #facade::HostTypeKey(#cell_owner::__krs_configuration_type_key),
                            field: #facade::HostTypeKey(#cell_owner::#marker),
                        },
                    },
                    wrapper_key: #wrapper_key,
                    wrapper: #wrapper,
                    value: #value,
                }
            });
        }
        let remainder = self.expand_frame(cells.remainder(), RuleRole::CellsRemainder)?;
        let payload = self.key(RuleRole::CellsPayload, 0);
        Ok(quote!(#facade::HostRuleCells {
            key: #payload, cells: ::std::vec![#(#output),*], remainder: #remainder,
        }))
    }

    fn expand_state(&mut self, state: &StateTerm) -> syn::Result<TokenStream> {
        let facade = self.facade;
        match state {
            StateTerm::Term(term) => {
                let term = self.expand_term(term.tree())?;
                Ok(quote!(#facade::ProtocolRuleStateTerm::Term(#term)))
            }
            StateTerm::KSequence(sequence) => {
                let sequence = self.expand_k(sequence)?;
                Ok(quote!(#facade::ProtocolRuleStateTerm::KSequence(#sequence)))
            }
            StateTerm::Map(map) => {
                let map = self.expand_map(map)?;
                Ok(quote!(#facade::ProtocolRuleStateTerm::Map(#map)))
            }
        }
    }

    fn expand_k(&mut self, sequence: &KSequence) -> syn::Result<TokenStream> {
        let facade = self.facade;
        let payload_key = if sequence_has_role(sequence, ProvenanceRole::KSequencePayload)? {
            let ordinal = take_counter(&mut self.counters.k_payload)?;
            option_key(facade, self.side_role(RuleRole::KSequencePayload), ordinal)
        } else {
            quote!(::core::option::Option::None)
        };
        let dot_k_key = if sequence.notation() == KSequenceNotation::DotK {
            let ordinal = take_counter(&mut self.counters.k_tail)?;
            option_key(facade, self.side_role(RuleRole::KSequenceTail), ordinal)
        } else {
            quote!(::core::option::Option::None)
        };
        let notation = k_notation(facade, sequence.notation());
        let mut items = Vec::new();
        for item in sequence.items() {
            let ordinal = take_counter(&mut self.counters.k_item)?;
            let key = self.key(RuleRole::KSequenceItem, ordinal);
            let value = self.expand_term(item.tree())?;
            items.push(quote!(#facade::ProtocolRuleKSequenceItem { key: #key, value: #value }));
        }
        let tail = if sequence.notation() == KSequenceNotation::DotK {
            quote!(#facade::ProtocolRuleFrame::Exact)
        } else {
            self.expand_frame(sequence.tail(), RuleRole::KSequenceTail)?
        };
        Ok(quote!(#facade::ProtocolRuleKSequence {
            payload_key: #payload_key, dot_k_key: #dot_k_key,
            notation: #notation, items: ::std::vec![#(#items),*], tail: #tail,
        }))
    }

    fn expand_map(&mut self, map: &MapExpression) -> syn::Result<TokenStream> {
        let facade = self.facade;
        let payload_key = if map_has_role(map, ProvenanceRole::MapPayload)? {
            let ordinal = take_counter(&mut self.counters.map_payload)?;
            option_key(facade, self.side_role(RuleRole::MapPayload), ordinal)
        } else {
            quote!(::core::option::Option::None)
        };
        let body = match map.body() {
            MapBody::Empty { explicit_dot } => quote!(#facade::ProtocolRuleMapBody::Empty {
                explicit_dot: #explicit_dot,
            }),
            MapBody::Items { items, remainder } => {
                let mut values = Vec::new();
                for item in items {
                    let ko = take_counter(&mut self.counters.map_key)?;
                    let vo = take_counter(&mut self.counters.map_value)?;
                    let key_key = self.key(RuleRole::MapKey, ko);
                    let value_key = self.key(RuleRole::MapValue, vo);
                    let key = self.expand_term(item.key().tree())?;
                    let value = self.expand_term(item.value().tree())?;
                    values.push(quote!(#facade::ProtocolRuleMapItem {
                        key_key: #key_key, key: #key, value_key: #value_key, value: #value,
                    }));
                }
                let remainder = self.expand_frame(remainder, RuleRole::MapRemainder)?;
                quote!(#facade::ProtocolRuleMapBody::Items {
                    items: ::std::vec![#(#values),*], remainder: #remainder,
                })
            }
            MapBody::Update { base, key, value } => {
                let bo = take_counter(&mut self.counters.map_update_base)?;
                let ko = take_counter(&mut self.counters.map_key)?;
                let vo = take_counter(&mut self.counters.map_value)?;
                let base_key = self.key(RuleRole::MapUpdateBase, bo);
                let key_key = self.key(RuleRole::MapKey, ko);
                let value_key = self.key(RuleRole::MapValue, vo);
                let base = self.expand_term(base.tree())?;
                let key = self.expand_term(key.tree())?;
                let value = self.expand_term(value.tree())?;
                quote!(#facade::ProtocolRuleMapBody::Update {
                    base_key: #base_key, base: #base, key_key: #key_key, key: #key,
                    value_key: #value_key, value: #value,
                })
            }
        };
        Ok(quote!(#facade::ProtocolRuleMap { payload_key: #payload_key, body: #body }))
    }

    fn expand_frame(
        &mut self,
        frame: &StateMacroRemainder,
        role: RuleRole,
    ) -> syn::Result<TokenStream> {
        let facade = self.facade;
        let side_role = self.side_role(role);
        let counter = match role {
            RuleRole::CellsRemainder => &mut self.counters.remainder,
            RuleRole::KSequenceTail => &mut self.counters.k_tail,
            RuleRole::MapRemainder => &mut self.counters.map_remainder,
            _ => unreachable!(),
        };
        match frame {
            StateMacroRemainder::Exact => Ok(quote!(#facade::ProtocolRuleFrame::Exact)),
            StateMacroRemainder::Anonymous(_) => {
                let ordinal = take_counter(counter)?;
                let key = provenance_key(facade, side_role, ordinal);
                Ok(quote!(#facade::ProtocolRuleFrame::Anonymous { key: #key }))
            }
            StateMacroRemainder::Bind { binding, .. } => {
                let ordinal = take_counter(counter)?;
                let key = provenance_key(facade, side_role, ordinal);
                let binding = binding.to_string();
                Ok(
                    quote!(#facade::ProtocolRuleFrame::Bind { key: #key, binding: #binding.to_owned() }),
                )
            }
            StateMacroRemainder::Reuse { binding, .. } => {
                let ordinal = take_counter(counter)?;
                let key = provenance_key(facade, side_role, ordinal);
                let binding = binding.to_string();
                Ok(
                    quote!(#facade::ProtocolRuleFrame::Reuse { key: #key, binding: #binding.to_owned() }),
                )
            }
        }
    }

    #[allow(clippy::too_many_lines)] // Exhaustive transport for the closed structured-term grammar.
    fn expand_term(&mut self, tree: &TermTree) -> syn::Result<TokenStream> {
        let facade = self.facade;
        match tree {
            TermTree::Application(application) => {
                let ordinal = take_counter(&mut self.counters.application)?;
                let key = self.term_key(TermRole::ApplicationHead, ordinal);
                let target = self.terms.application_target(application.head())?;
                let mut arguments = Vec::new();
                match application.arguments() {
                    TermArguments::Positional(values) => {
                        for value in values {
                            let value = self.expand_term(value)?;
                            arguments.push(quote!(#facade::HostTermArgument::Positional {
                                value: ::std::boxed::Box::new(#value),
                            }));
                        }
                    }
                    TermArguments::Named(values) => {
                        for argument in values {
                            let ordinal = take_counter(&mut self.counters.record_field)?;
                            let field_key = self.term_key(TermRole::RecordFieldName, ordinal);
                            let field = argument.name().to_string();
                            let value = self.expand_term(argument.value())?;
                            arguments.push(quote!(#facade::HostTermArgument::Named {
                                key: #field_key,
                                field: #facade::ProductionFieldId::new(#field)
                                    .expect("Rust field identifiers are valid production fields"),
                                value: ::std::boxed::Box::new(#value),
                            }));
                        }
                    }
                }
                Ok(quote!(#facade::HostTerm::Application {
                    head_class: #facade::DescriptorApplicationHeadClass::Applied,
                    reference: #facade::HostApplicationReference { key: #key, target: #target },
                    path_key: #key, arguments: ::std::vec![#(#arguments),*],
                }))
            }
            TermTree::Reference(path) => {
                let ordinal = take_counter(&mut self.counters.reference)?;
                let key = self.term_key(TermRole::Reference, ordinal);
                let name = spelling(path);
                if is_bound_ident_path(path, self.bindings) {
                    Ok(quote!(#facade::HostTerm::Variable {
                        key: #key, path_key: #key, name: #name.to_owned(),
                    }))
                } else {
                    let target = self.terms.application_target(path)?;
                    Ok(quote!(#facade::HostTerm::Application {
                        head_class: #facade::DescriptorApplicationHeadClass::BareReference,
                        reference: #facade::HostApplicationReference { key: #key, target: #target },
                        path_key: #key, arguments: ::std::vec![],
                    }))
                }
            }
            TermTree::Literal(literal) => {
                let ordinal = take_counter(&mut self.counters.literal)?;
                let key = self.term_key(TermRole::Literal, ordinal);
                let literal = literal_tokens(facade, literal);
                Ok(quote!(#facade::HostTerm::Literal { key: #key, literal: #literal }))
            }
            TermTree::Wildcard(_) => {
                if matches!(self.side, RuleSide::Right) {
                    return Err(syn::Error::new(
                        Span::call_site(),
                        "rule results cannot contain wildcards",
                    ));
                }
                let ordinal = take_counter(&mut self.counters.wildcard)?;
                let key = self.term_key(TermRole::Wildcard, ordinal);
                Ok(quote!(#facade::HostTerm::Wildcard { key: #key }))
            }
            TermTree::IdToken { literal } => {
                if !self.claim {
                    return Err(syn::Error::new(
                        literal.span(),
                        "id! is currently claim-only",
                    ));
                }
                let ordinal = take_counter(&mut self.counters.id_token)?;
                let key = provenance_key(facade, ProvenanceRole::ClaimIdToken, ordinal);
                let value = literal.value();
                Ok(
                    quote!(#facade::HostTerm::BuiltinToken { key: #key, sort: #facade::BuiltinSort::Id, value: #value.to_owned() }),
                )
            }
            TermTree::BytesToken { literal } => {
                if !self.claim {
                    return Err(syn::Error::new(
                        literal.span(),
                        "bytes! is currently claim-only",
                    ));
                }
                let ordinal = take_counter(&mut self.counters.bytes_token)?;
                let key = provenance_key(facade, ProvenanceRole::ClaimBytesToken, ordinal);
                let value = bytes_token::encode(&literal.value());
                Ok(
                    quote!(#facade::HostTerm::BuiltinToken { key: #key, sort: #facade::BuiltinSort::Bytes, value: #value.to_owned() }),
                )
            }
            TermTree::Anonymous {
                sort,
                spelling: display_literal,
            } => {
                if !self.claim || matches!(self.side, RuleSide::Right) {
                    return Err(syn::Error::new(
                        display_literal.span(),
                        "anonymous! is allowed only in claim subjects",
                    ));
                }
                let ordinal = take_counter(&mut self.counters.anonymous)?;
                let key = provenance_key(facade, ProvenanceRole::ClaimAnonymous, ordinal);
                let sort_key = provenance_key(facade, ProvenanceRole::ClaimAnonymousSort, ordinal);
                let path = call_site_path(sort)?;
                let key_fn = format_ident!(
                    "__krs_claim_anonymous_sort_{:016x}_{}",
                    self.terms.nonce,
                    self.terms.next_key
                );
                self.terms.next_key += 1;
                let cfg = self.terms.cfg;
                self.terms.key_functions.push(quote! { #(#cfg)* #[doc(hidden)] fn #key_fn() -> ::core::any::TypeId { ::core::any::TypeId::of::<#path>() } });
                let authored = spelling(sort);
                let display = display_literal.value();
                Ok(
                    quote!(#facade::HostTerm::Anonymous { key: #key, sort: #facade::HostSortReference { key: #sort_key, target: #facade::HostTypeReference { key: #facade::HostTypeKey(#key_fn), authored_path: #authored.to_owned() } }, spelling: #display.to_owned() }),
                )
            }
            TermTree::OrBool { arguments, .. } => {
                if !self.claim {
                    return Err(syn::Error::new(
                        Span::call_site(),
                        "or_bool! is currently claim-only",
                    ));
                }
                let ordinal = take_counter(&mut self.counters.or_bool)?;
                let key = provenance_key(facade, ProvenanceRole::ClaimOrBool, ordinal);
                let values = arguments
                    .iter()
                    .map(|argument| self.expand_term(argument))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(quote!(#facade::HostTerm::OrBool { key: #key, arguments: vec![#(#values),*] }))
            }
            TermTree::Cell(cell) => {
                let ordinal = take_counter(&mut self.counters.application)?;
                let key = self.term_key(TermRole::ApplicationHead, ordinal);
                let declaration = self.terms.cell_declaration_target(cell.owner())?;
                let mut fields = Vec::new();
                for field in cell.fields() {
                    let ordinal = take_counter(&mut self.counters.record_field)?;
                    let field_key = self.term_key(TermRole::RecordFieldName, ordinal);
                    let name = field.name().to_string();
                    let value = self.expand_term(field.value())?;
                    fields.push(quote!(#facade::HostCellTermField {
                        key: #field_key,
                        field: #facade::ProductionFieldId::new(#name)
                            .expect("Rust fields are valid cell-field identities"),
                        value: ::std::boxed::Box::new(#value),
                    }));
                }
                Ok(quote!(#facade::HostTerm::Cell {
                    key: #key, declaration: #declaration,
                    fields: ::std::vec![#(#fields),*],
                }))
            }
        }
    }
}
