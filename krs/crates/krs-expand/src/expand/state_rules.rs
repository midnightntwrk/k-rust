//! Whole-configuration rules and named contexts: cells-form `#[k::rule]` and `#[k::context_alias]`.

use crate::ExpandError;
use krs_diagnostic::codes::expand;
use krs_ir::wire::{
    WireCellIdentity, WireCellReference, WireConfigurationReference, WireConfigurationRule,
    WireContextAlias, WirePayload, WireRuleCells, WireRuleCondition, WireTerm, WireTypeReference,
};
use krs_ir::{
    CellWrapper, DescriptorKSequenceNotation, DescriptorRuleLabel, DescriptorRulePriority,
    ProtocolContextAliasBinding, ProtocolContextAliasBindingKind, ProtocolRuleBinding,
    ProtocolRuleBindingKind, ProtocolRuleCell, ProtocolRuleFrame, ProtocolRuleKSequence,
    ProtocolRuleKSequenceItem, ProtocolRuleMap, ProtocolRuleMapBody, ProtocolRuleMapItem,
    ProtocolRuleStateTerm, ProvenanceKey,
};
use krs_syntax::KrsSyntax;
use krs_syntax::positions::Form;
use krs_syntax::{
    KSequence, KSequenceNotation, MapBody, MapExpression, RuleSide, StateMacroRemainder,
    StateRuleBindingKind, StateRuleReferenceKind, StateTerm, TokenRange,
    parse_state_context_alias_item,
};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::ext::IdentExt;
use syn::spanned::Spanned;
use syn::{Attribute, Ident, Path};

use super::configuration::cell_field_identity;
use super::existentials::{ensures_condition, evaluation_step, existential_binders, fresh_binders};
use super::factory::{DescriptorFactory, FactoryPayload};
use super::island_checks::{consumed_state_island_import_checks, wrapper_type_check};
use super::ledger::KeyLedger;
use super::nonce::expansion_nonce;
use super::terms::{KeyedTerm, TermBuilder, TermSide, WireSlots, wire_sort_reference};
use super::tokens::{call_site_cfg_attributes, respanned, sort_type_tokens, spelling};
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
    // The alias's declaration key is its wire node's own.
    let ledger = KeyLedger::new(&anchors, &[]);
    let nonce = expansion_nonce(env, "context_alias", &alias.item().sig.ident, fallback);
    let factory = format_ident!("__krs_context_alias_{nonce:016x}");
    let configuration_key = format_ident!("__krs_context_alias_configuration_{nonce:016x}");
    let cfg = call_site_cfg_attributes(&alias.item().attrs)?;
    let configuration_type = alias.configuration_type();
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
                    let path = sort.sort();
                    let ty = sort_type_tokens(&facade, path, sort.is_dynamic());
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
                            ledger.define(binding.sort_key())?,
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
    let mut builder = StateRuleBuilder::new(
        &facade,
        &ledger,
        nonce,
        &cfg,
        &binding_idents,
        RuleSide::Left,
        Form::ContextAlias,
    );
    let pattern = builder.expand_cells(alias.pattern(), configuration_type, &mut slots)?;
    key_functions.extend(builder.terms.key_functions);
    let mut wrapper_checks = Vec::new();
    for candidate in alias.reference_candidates()? {
        if candidate.kind() == StateRuleReferenceKind::CellWrapper {
            let path = candidate.path();
            wrapper_checks.push(wrapper_type_check(path));
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
            let path = sort;
            let key_fn = format_ident!("__krs_context_alias_result_{nonce:016x}");
            key_functions.push(quote! {
                #(#cfg)*
                #[doc(hidden)]
                fn #key_fn() -> ::core::any::TypeId { ::core::any::TypeId::of::<#path>() }
            });
            Some(wire_sort_reference(
                &mut slots,
                &facade,
                ledger.define(attribute.result_key())?,
                &key_fn,
                &spelling(sort),
            ))
        }
        None => None,
    };

    let wire = WirePayload::ContextAlias(Box::new(WireContextAlias {
        declaration_key: ledger.define(alias.declaration_key())?,
        name_key: ledger.define(attribute.name_key())?,
        name: alias_name,
        here_key: ledger.define(attribute.here_key())?,
        here: here_name,
        pattern_key: ledger.define(alias.pattern_key())?,
        configuration: WireConfigurationReference {
            key: ledger.define(alias.configuration_type_key())?,
            configuration: WireTypeReference {
                slot: slots.type_slot(quote!(#facade::HostTypeKey(#configuration_key))),
                authored_path: configuration_spelling,
            },
        },
        bindings,
        pattern,
        result,
    }));
    ledger.finish()?;
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
    // A rule's declaration key is its own; no wire field carries it.
    let ledger = KeyLedger::new(
        descriptor.anchors(),
        &[krs_syntax::ProvenanceRole::RuleDeclaration],
    );
    let nonce = expansion_nonce(env, "configuration_rule", &rule.item().sig.ident, fallback);
    let factory = format_ident!("__krs_configuration_rule_{nonce:016x}");
    let subject_key = format_ident!("__krs_rule_configuration_left_{nonce:016x}");
    let result_key = format_ident!("__krs_rule_configuration_right_{nonce:016x}");
    let cfg = call_site_cfg_attributes(&rule.item().attrs)?;
    let subject_type = rule.subject_type();
    // A single-body rule (KF-011) has no result; its fn returns `()`.
    let result_type = rule.result_type().cloned();
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
                let path = sort.sort();
                let ty = sort_type_tokens(&facade, path, sort.is_dynamic());
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
                        ledger.define(binding.sort_key())?,
                        &key_fn,
                        &authored,
                    ),
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
    let (existentials, existential_key_functions) = existential_binders(
        rule.existentials(),
        (&facade, &ledger),
        nonce,
        &cfg,
        &mut slots,
    )?;
    let (fresh, fresh_key_functions) = fresh_binders(
        rule.existentials(),
        (&facade, &ledger),
        nonce,
        &cfg,
        &mut slots,
    )?;
    let (evaluation, evaluation_key_function) = evaluation_step(
        attribute,
        rule.existentials(),
        (&facade, &ledger, nonce, &cfg),
        &mut slots,
    )?;
    // A single-body rule (KF-011): its subject's `k::rewrite!` islands say
    // what changes.
    let form = if rule.result().is_none() {
        Form::CellsLocalRule
    } else {
        Form::CellsRule
    };
    let mut left = StateRuleBuilder::new(
        &facade,
        &ledger,
        nonce,
        &cfg,
        &binding_idents,
        RuleSide::Left,
        form,
    );
    let subject = left.expand_cells(rule.subject(), subject_type, &mut slots)?;
    let mut right = StateRuleBuilder::new(
        &facade,
        &ledger,
        nonce ^ 0x8000_0000_0000_0000,
        &cfg,
        &result_idents,
        RuleSide::Right,
        form,
    );
    let result = match (rule.result(), &result_type) {
        (Some(result), Some(result_type)) => {
            Some(right.expand_cells(result, result_type, &mut slots)?)
        }
        _ => None,
    };
    let mut condition_builder = TermBuilder::new(
        &facade,
        &ledger,
        nonce ^ 0x4000_0000_0000_0000,
        &cfg,
        &requires_idents,
        form,
    );
    let requires = if let Some(condition) = rule.requires() {
        let term = condition_builder.expand_wire(
            KeyedTerm::of(condition.term()),
            TermSide::Requires,
            &mut slots,
        )?;
        Some(WireRuleCondition {
            key: ledger.define(condition.term().keys().payload())?,
            term,
        })
    } else {
        None
    };
    let mut ensures_builder = TermBuilder::new(
        &facade,
        &ledger,
        nonce ^ 0x2000_0000_0000_0000,
        &cfg,
        &result_idents,
        form,
    );
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
                key: ledger.define(attribute.label_key())?,
                name: label.value(),
            })
        })
        .transpose()?;
    let priority = attribute
        .transition_priority()
        .map(|(_, value)| -> crate::Result<_> {
            Ok(DescriptorRulePriority {
                key: ledger.define(attribute.owise_key().or_else(|| attribute.priority_key()))?,
                value,
            })
        })
        .transpose()?;
    let mut wrapper_checks = Vec::new();
    for candidate in rule.reference_candidates()? {
        if candidate.kind() == StateRuleReferenceKind::CellWrapper {
            let path = candidate.path();
            wrapper_checks.push(wrapper_type_check(path));
        }
    }
    let island_import_checks = consumed_state_island_import_checks(original);

    let nondet = attribute
        .nondet()
        .map(|group| -> crate::Result<_> {
            Ok(krs_ir::DescriptorNondetGroup {
                key: ledger.define(attribute.nondet_key())?,
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
        pattern_key: ledger.define(rule.pattern_key())?,
        subject_configuration: WireConfigurationReference {
            key: ledger.define(rule.subject_type_key())?,
            configuration: WireTypeReference {
                slot: slots.type_slot(quote!(#facade::HostTypeKey(#subject_key))),
                authored_path: subject_spelling,
            },
        },
        result_key: result
            .is_some()
            .then(|| ledger.define(rule.result_key()))
            .transpose()?,
        result_configuration: result_spelling
            .map(|authored_path| -> crate::Result<_> {
                Ok(WireConfigurationReference {
                    key: ledger.define(rule.result_type_key())?,
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
    ledger.finish()?;
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

/// Expands `cells!` configurations: their cells, `k!` sequences, maps and
/// instances, handing every term they hold to the term walker at the side's
/// slot of the sentence form.
pub(super) struct StateRuleBuilder<'a> {
    facade: &'a Path,
    side: RuleSide,
    pub(super) terms: TermBuilder<'a>,
}

impl<'a> StateRuleBuilder<'a> {
    pub(super) fn new(
        facade: &'a Path,
        ledger: &'a KeyLedger<'a>,
        nonce: u64,
        cfg: &'a [Attribute],
        bindings: &'a [Ident],
        side: RuleSide,
        form: Form,
    ) -> Self {
        Self {
            facade,
            side,
            terms: TermBuilder::new(facade, ledger, nonce, cfg, bindings, form),
        }
    }

    /// Continues the key-function numbering of `previous`, a term subject
    /// expanded before this `cells!` pattern (an equation's function context,
    /// KF-025).
    pub(super) fn continue_subject(&mut self, previous: &TermBuilder<'_>) {
        self.terms.next_key = previous.next_key;
    }

    const fn term_side(&self) -> TermSide {
        match self.side {
            RuleSide::Left => TermSide::Left,
            RuleSide::Right => TermSide::Right,
        }
    }

    pub(super) fn expand_cells(
        &mut self,
        cells: &krs_syntax::CellsExpression,
        owner: &Path,
        slots: &mut WireSlots,
    ) -> crate::Result<WireRuleCells> {
        let facade = self.facade;
        let ledger = self.terms.ledger;
        let mut output = Vec::new();
        for entry in cells.entries() {
            let field_key = ledger.define(entry.name_key())?;
            let cell_owner = entry.owner().unwrap_or(owner);
            // A cell the owner does not declare is reported at the entry's
            // owner path when the entry writes one (`Group::cell`), and at
            // the cell's name otherwise.
            let field_owner = match entry.owner() {
                Some(path) => quote!(#path),
                None => respanned(owner, entry.name().span()),
            };
            let identity =
                cell_field_identity(facade, &field_owner, entry.name(), entry.name().span());
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
                (Some(ledger.define(entry.wrapper_key())?), Some(wrapper))
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
                        field: slots.type_slot(quote!(#facade::HostTypeKey(#identity))),
                    },
                },
                wrapper_key,
                wrapper,
                value,
            });
        }
        let remainder = expand_frame(ledger, cells.remainder(), cells.remainder_key())?;
        Ok(WireRuleCells {
            key: ledger.define(cells.payload_key())?,
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
        let rest = expand_frame(self.terms.ledger, list.rest(), list.rest_key())?;
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
        let ledger = self.terms.ledger;
        let key = ledger.define(item.key())?;
        let mut fields = Vec::new();
        for field in item.fields() {
            fields.push(krs_ir::ProtocolRuleInstanceField {
                key: ledger.define(field.name_key())?,
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
        let ledger = self.terms.ledger;
        // Every shell has its payload key: an empty one is anchored at
        // its invocation.
        let payload_key = ledger.define(sequence.payload_key())?;
        let dot_k_key = if sequence.notation() == KSequenceNotation::DotK {
            Some(ledger.define(sequence.tail_key())?)
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
                key: ledger.define(item.keys().payload())?,
                value: self.expand_keyed(KeyedTerm::of(item), slots)?,
            });
        }
        let tail = if sequence.notation() == KSequenceNotation::DotK {
            ProtocolRuleFrame::Exact
        } else {
            expand_frame(ledger, sequence.tail(), sequence.tail_key())?
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
        let ledger = self.terms.ledger;
        // Every shell has its payload key: an empty one is anchored at
        // its invocation.
        let payload_key = ledger.define(map.payload_key())?;
        let body = match map.body() {
            MapBody::Empty { explicit_dot } => ProtocolRuleMapBody::Empty {
                explicit_dot: *explicit_dot,
            },
            MapBody::Items { items, remainder } => {
                let mut values = Vec::new();
                for item in items {
                    values.push(ProtocolRuleMapItem {
                        key_key: ledger.define(item.key().keys().payload())?,
                        key: self.expand_key(KeyedTerm::of(item.key()), slots)?,
                        value_key: ledger.define(item.value().keys().payload())?,
                        value: self.expand_entry(KeyedTerm::of(item.value()), slots)?,
                    });
                }
                ProtocolRuleMapBody::Items {
                    items: values,
                    remainder: expand_frame(ledger, remainder, map.remainder_key())?,
                }
            }
            MapBody::Update { base, key, value } => ProtocolRuleMapBody::Update {
                base_key: ledger.define(base.keys().payload())?,
                base: self.expand_keyed(KeyedTerm::of(base), slots)?,
                key_key: ledger.define(key.keys().payload())?,
                key: self.expand_key(KeyedTerm::of(key), slots)?,
                value_key: ledger.define(value.keys().payload())?,
                value: self.expand_entry(KeyedTerm::of(value), slots)?,
            },
        };
        Ok(ProtocolRuleMap { payload_key, body })
    }

    /// Expands one term the configuration holds, at the side's slot.
    fn expand_keyed(
        &mut self,
        term: KeyedTerm<'_>,
        slots: &mut WireSlots,
    ) -> crate::Result<WireTerm> {
        self.terms.expand_wire(term, self.term_side(), slots)
    }

    /// Expands a map's value, a collection entry.
    fn expand_entry(
        &mut self,
        term: KeyedTerm<'_>,
        slots: &mut WireSlots,
    ) -> crate::Result<WireTerm> {
        self.terms.expand_entry_wire(term, self.term_side(), slots)
    }

    /// Expands a map's key, a collection entry the map is looked up by.
    fn expand_key(
        &mut self,
        term: KeyedTerm<'_>,
        slots: &mut WireSlots,
    ) -> crate::Result<WireTerm> {
        self.terms.expand_key_wire(term, self.term_side(), slots)
    }
}

/// A remainder, keyed `read`, the remainder's own key.
fn expand_frame(
    ledger: &KeyLedger<'_>,
    frame: &StateMacroRemainder,
    read: Option<&ProvenanceKey>,
) -> crate::Result<ProtocolRuleFrame> {
    match frame {
        StateMacroRemainder::Exact => Ok(ProtocolRuleFrame::Exact),
        StateMacroRemainder::Anonymous(_) => Ok(ProtocolRuleFrame::Anonymous {
            key: ledger.define(read)?,
        }),
        StateMacroRemainder::Bind { binding, .. } => Ok(ProtocolRuleFrame::Bind {
            key: ledger.define(read)?,
            binding: binding.unraw().to_string(),
        }),
        StateMacroRemainder::Reuse { binding, .. } => Ok(ProtocolRuleFrame::Reuse {
            key: ledger.define(read)?,
            binding: binding.unraw().to_string(),
        }),
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
