//! Syntactic lists: `#[k::syntax_list]` (KF-020).
//!
//! The enum declares a closed sort and its two variants are that sort's
//! constructors: the cons production `[head, separator, tail]` with
//! `ListCons` metadata and the terminator production `[".Sort"]` with
//! `ListTerminator` metadata, each naming the other variant.

use krs_ir::ENUM_VARIANT_DISAMBIGUATOR_PREFIX;
use krs_ir::wire::{
    WireApplicationReference, WireConstructorDescriptor, WireConstructorFieldDescriptor,
    WireGrammarDescriptor, WirePayload, WireProduction, WireProductionAttribute,
    WireProductionItem, WireProductionOwner, WireSortReference, WireTypeReference,
};
use krs_syntax::{KrsSyntax, ProvenanceAnchor, ProvenanceRole, TokenRange};
use proc_macro2::TokenStream;
use quote::{ToTokens, format_ident, quote};
use syn::{Attribute, Fields, Ident, ItemEnum, Path};

use super::factory::{DescriptorFactory, FactoryPayload};
use super::nonce::{expansion_nonce, rule_application_selector};
use super::productions::{production_documentation_wire, strictness_key_function, strictness_wire};
use super::terms::{WireSlots, wire_key, wire_sort_reference};
use super::tokens::{
    call_site_cfg_attributes, call_site_ident, call_site_path, sort_type_tokens,
    variant_marker_function,
};
use crate::environment::MacroEnvironment;
use crate::provenance::host_provenance;

struct ListContext<'a> {
    env: &'a dyn MacroEnvironment,
    facade: Path,
    declaration: krs_syntax::SyntaxListDeclaration,
    nonce: u64,
    cfg: Vec<Attribute>,
    enum_name: String,
    enum_key: Ident,
    fallback: TokenRange,
}

/// Which list variant a descriptor describes.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Role {
    Cons,
    Terminator,
}

impl Role {
    const fn index(self) -> usize {
        match self {
            Self::Cons => 0,
            Self::Terminator => 1,
        }
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "The list sort and both variants share one descriptor expansion."
)]
pub(crate) fn syntax_list(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> crate::Result<TokenStream> {
    let attribute = krs_syntax::SyntaxListAttribute::parse_tokens(attributes)?;
    let item: ItemEnum = syn::parse2(item)?;
    let declaration = krs_syntax::SyntaxListDeclaration::from_parts(&attribute, item)?;
    let facade = env.facade_path()?;
    let fallback = TokenRange::for_tokens(declaration.item())?;
    let nonce = expansion_nonce(env, "syntax_list", declaration.name(), fallback);
    let cfg = call_site_cfg_attributes(&declaration.item().attrs)?;
    let enum_ident = call_site_ident(declaration.name())?;
    let enum_name = declaration.name().to_string();
    let context = ListContext {
        env,
        facade,
        nonce,
        cfg,
        enum_name,
        enum_key: format_ident!("__krs_list_type_{nonce:016x}"),
        fallback,
        declaration,
    };
    let ListContext {
        facade,
        cfg,
        enum_name,
        enum_key,
        ..
    } = &context;

    let mut marker_types = Vec::new();
    let mut associated_keys = Vec::new();
    let mut rule_applications = Vec::new();
    for role in [Role::Cons, Role::Terminator] {
        let index = role.index();
        let name = context.variant_name(role);
        let marker = format_ident!("__KrsListVariant_{nonce:016x}_{index}");
        let variant_key = context.variant_key(role);
        let associated = variant_marker_function(name);
        marker_types.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            struct #marker;

            #(#cfg)*
            #[doc(hidden)]
            fn #variant_key() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#marker>()
            }
        });
        associated_keys.push(quote! {
            #[doc(hidden)]
            #[allow(non_snake_case)]
            pub fn #associated() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#marker>()
            }
        });
        let selector = rule_application_selector(name);
        let application_path = format!("{enum_name}::{name}");
        rule_applications.push(quote! {
            #(#cfg)*
            impl #facade::__KrsRuleApplication<#selector> for #enum_ident {
                fn __krs_rule_application(
                    _authored_path: &str,
                ) -> #facade::HostApplicationTarget {
                    #facade::HostApplicationTarget::EnumVariant(
                        #facade::HostEnumVariantReference::new(
                            #facade::HostTypeReference {
                                key: #facade::HostTypeKey(#enum_key),
                                authored_path: #enum_name.to_owned(),
                            },
                            #facade::HostTypeKey(#variant_key),
                            #application_path,
                        )
                        .expect("generated list variants retain their owning enum path"),
                    )
                }
            }
        });
    }

    let sort_factory = format_ident!("__krs_list_sort_descriptor_{nonce:016x}");
    let sort_anchors = vec![ProvenanceAnchor::new(
        ProvenanceRole::SortDeclaration,
        0,
        TokenRange::for_tokens(context.declaration.name())?,
    )];
    let sort_provenance = host_provenance(env, facade, context.fallback, &sort_anchors);
    let sort_wire = serde_json::to_string(&WirePayload::Sort(krs_ir::wire::WireSortDescriptor {
        parents: Vec::new(),
    }))
    .expect("KRS wire values serialize");
    let sort_factory_tokens = DescriptorFactory {
        facade,
        factory: &sort_factory,
        name: quote!(#enum_name),
        item_kind: quote!(#facade::ItemKind::Sort),
        disambiguator: quote!(""),
        identity_label: "Cargo and Rust macro context form a valid list-sort identity",
        declared_type: quote! {
            ::core::option::Option::Some(
                #facade::HostDeclarationIdentity::Nominal(#facade::HostTypeKey(#enum_key)),
            )
        },
        payload: FactoryPayload::wire(sort_wire, quote!(#facade::__KrsSlots::default())),
        cfg: quote!(::core::default::Default::default()),
        attributes: quote!(#(#cfg)*),
        provenance: quote!(#sort_provenance),
        prelude: TokenStream::new(),
    }
    .render();

    let cons = context.variant_expansion(Role::Cons)?;
    let terminator = context.variant_expansion(Role::Terminator)?;
    let item = context.rust_item()?;

    Ok(quote! {
        #item

        #(#cfg)*
        #[doc(hidden)]
        fn #enum_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#enum_ident>()
        }

        #(#marker_types)*

        #(#cfg)*
        impl #enum_ident {
            #(#associated_keys)*
        }

        #(#rule_applications)*

        #sort_factory_tokens

        #cons
        #terminator
    })
}

impl ListContext<'_> {
    fn variant_name(&self, role: Role) -> &Ident {
        match role {
            Role::Cons => self.declaration.cons().name(),
            Role::Terminator => self.declaration.terminator().name(),
        }
    }

    fn variant_key(&self, role: Role) -> Ident {
        let nonce = self.nonce;
        let index = role.index();
        format_ident!("__krs_list_variant_{nonce:016x}_{index}")
    }

    /// The enum as rustc sees it: a readable tail field `tail: Ints` is
    /// wrapped as `k::Term<Ints>`, since `Term` is a zero-sized marker and
    /// the enum would otherwise contain itself.
    fn rust_item(&self) -> crate::Result<ItemEnum> {
        let mut item = self.declaration.item().clone();
        if self.declaration.attribute().is_reference() {
            return Ok(item);
        }
        let facade = &self.facade;
        let cons_name = self.declaration.cons().name();
        for variant in &mut item.variants {
            if &variant.ident != cons_name {
                continue;
            }
            if let Fields::Named(fields) = &mut variant.fields
                && let Some(tail) = fields.named.iter_mut().nth(1)
            {
                let ty = &tail.ty;
                tail.ty = syn::parse2(quote!(#facade::Term<#ty>))?;
            }
        }
        Ok(item)
    }

    fn anchors(&self, role: Role) -> crate::Result<Vec<ProvenanceAnchor>> {
        Ok(match role {
            Role::Cons => self.declaration.cons_provenance()?,
            Role::Terminator => self.declaration.terminator_provenance()?,
        })
    }

    fn partner(&self, role: Role, slots: &mut WireSlots) -> WireApplicationReference {
        let partner = match role {
            Role::Cons => Role::Terminator,
            Role::Terminator => Role::Cons,
        };
        let facade = &self.facade;
        let enum_key = &self.enum_key;
        let partner_key = self.variant_key(partner);
        WireApplicationReference {
            key: wire_key(ProvenanceRole::ListDeclaration, 0),
            target: slots.variant_slot_for_grammar(
                &quote!(#facade::HostTypeKey(#enum_key)),
                &quote!(#facade::HostTypeKey(#partner_key)),
            ),
            authored_path: format!("{}::{}", self.enum_name, self.variant_name(partner)),
        }
    }

    #[expect(
        clippy::too_many_lines,
        reason = "One variant's constructor and production descriptors are built together."
    )]
    fn variant_expansion(&self, role: Role) -> crate::Result<TokenStream> {
        let facade = &self.facade;
        let cfg = &self.cfg;
        let nonce = self.nonce;
        let index = role.index();
        let enum_key = &self.enum_key;
        let enum_name = &self.enum_name;
        let variant_name = self.variant_name(role).to_string();
        let variant_key = self.variant_key(role);
        let descriptor_factory = format_ident!("__krs_list_constructor_{nonce:016x}_{index}");
        let grammar_factory = format_ident!("__krs_list_grammar_{nonce:016x}_{index}");
        let disambiguator = format!("{ENUM_VARIANT_DISAMBIGUATOR_PREFIX}{enum_name}");
        let grammar_name = format!("__krs_grammar_{enum_name}_{variant_name}");
        let anchors = self.anchors(role)?;
        let provenance = host_provenance(self.env, facade, self.fallback, &anchors);

        let mut slots = WireSlots::new(facade);
        let result_slot = slots.type_slot(quote!(#facade::HostTypeKey(#enum_key)));
        let mut grammar_slots = WireSlots::new(facade);
        let mut field_key_functions = Vec::new();
        let mut fields = Vec::new();
        let mut items = Vec::new();
        let attribute = self.declaration.attribute();
        let mut attributes = Vec::new();
        let mut strictness_key = TokenStream::new();
        match role {
            Role::Cons => {
                let cons = self.declaration.cons();
                for (ordinal, field) in cons.fields().into_iter().enumerate() {
                    let key = format_ident!("__krs_list_field_{nonce:016x}_{ordinal}");
                    let ty = if field.term_sort().is_dynamic() {
                        field.term_sort().ty().to_token_stream()
                    } else {
                        let path = call_site_path(field.term_sort().sort())?;
                        sort_type_tokens(&path, false)
                    };
                    field_key_functions.push(quote! {
                        #(#cfg)*
                        #[doc(hidden)]
                        fn #key() -> ::core::any::TypeId {
                            ::core::any::TypeId::of::<#ty>()
                        }
                    });
                    let spelling = field.term_sort().sort_token_text();
                    fields.push(WireConstructorFieldDescriptor {
                        name: field.name().to_string(),
                        sort: WireTypeReference {
                            slot: slots.type_slot(quote!(#facade::HostTypeKey(#key))),
                            authored_path: spelling.clone(),
                        },
                    });
                    let ordinal = u32::try_from(ordinal).expect("a list has two fields");
                    let field_key = wire_key(ProvenanceRole::ConstructorFieldDeclaration, ordinal);
                    if ordinal == 1 && !attribute.separator().value().is_empty() {
                        items.push(WireProductionItem::Terminal {
                            key: wire_key(ProvenanceRole::ListSeparator, 0),
                            text: attribute.separator().value(),
                        });
                    }
                    items.push(WireProductionItem::NonTerminal {
                        key: field_key.clone(),
                        field_key: field_key.clone(),
                        declaration_key: Some(field_key),
                        field: krs_ir::ProductionFieldId::new(field.name().to_string())
                            .expect("Rust fields are valid production fields"),
                        sort: Box::new(wire_sort_reference(
                            &mut grammar_slots,
                            facade,
                            ProvenanceRole::ConstructorFieldSort,
                            ordinal,
                            &key,
                            &spelling,
                        )),
                    });
                }
                attributes.extend(production_documentation_wire(cons.documentation())?);
                attributes.push(WireProductionAttribute::ListCons {
                    key: wire_key(ProvenanceRole::ListDeclaration, 0),
                    separator_key: wire_key(ProvenanceRole::ListSeparator, 0),
                    separator: attribute.separator().value(),
                    non_empty: attribute
                        .non_empty()
                        .map(|_| wire_key(ProvenanceRole::ListNonEmpty, 0)),
                    terminator: self.partner(role, &mut grammar_slots),
                });
                let strictness_nonce = expansion_nonce(
                    self.env,
                    "list_strictness",
                    self.declaration.name(),
                    self.fallback,
                );
                strictness_key = strictness_key_function(
                    cons.strictness(),
                    cons.fields()
                        .into_iter()
                        .map(krs_syntax::ConstructorField::name),
                    strictness_nonce,
                    cfg,
                )?;
                if let Some(strictness) = strictness_wire(
                    facade,
                    cons.strictness(),
                    strictness_nonce,
                    &mut grammar_slots,
                ) {
                    attributes.push(strictness);
                }
            }
            Role::Terminator => {
                items.push(WireProductionItem::Terminal {
                    key: wire_key(ProvenanceRole::ListDeclaration, 0),
                    text: format!(".{enum_name}"),
                });
                attributes.push(WireProductionAttribute::ListTerminator {
                    cons: self.partner(role, &mut grammar_slots),
                });
            }
        }
        let application_path = format!("{enum_name}::{variant_name}");
        let result_sort = wire_sort_reference(
            &mut grammar_slots,
            facade,
            ProvenanceRole::ConstructorSort,
            0,
            enum_key,
            enum_name,
        );
        let variant_slot = grammar_slots.variant_slot_for_grammar(
            &quote!(#facade::HostTypeKey(#enum_key)),
            &quote!(#facade::HostTypeKey(#variant_key)),
        );
        let grammar_wire = WirePayload::Grammar(Box::new(WireGrammarDescriptor::Production(
            WireProduction {
                key: wire_key(ProvenanceRole::ConstructorDeclaration, 0),
                template_key: None,
                owner: WireProductionOwner::Constructor {
                    constructor: WireApplicationReference {
                        key: wire_key(ProvenanceRole::ConstructorDeclaration, 0),
                        target: variant_slot,
                        authored_path: application_path,
                    },
                },
                result_sort,
                items,
                attributes,
            },
        )));
        let grammar_wire = serde_json::to_string(&grammar_wire).expect("KRS wire values serialize");
        let grammar_slot_tokens = grammar_slots.tokens();
        let constructor_wire = WirePayload::Constructor(WireConstructorDescriptor {
            sort: WireSortReference {
                key: wire_key(ProvenanceRole::ConstructorSort, 0),
                target: WireTypeReference {
                    slot: result_slot,
                    authored_path: enum_name.clone(),
                },
            },
            fields,
        });
        let constructor_wire = serde_json::to_string(&constructor_wire)
            .expect("list-constructor wire is serializable");
        let slot_tokens = slots.tokens();

        let descriptor_factory_tokens = DescriptorFactory {
            facade,
            factory: &descriptor_factory,
            name: quote!(#variant_name),
            item_kind: quote!(#facade::ItemKind::Constructor),
            disambiguator: quote!(#disambiguator),
            identity_label: "Cargo and Rust macro context form a valid list-variant identity",
            declared_type: quote! {
                ::core::option::Option::Some(
                    #facade::HostDeclarationIdentity::EnumVariant(
                        #facade::HostEnumVariantKey::new(
                            #facade::HostTypeKey(#enum_key),
                            #facade::HostTypeKey(#variant_key),
                        ),
                    ),
                )
            },
            payload: FactoryPayload::wire(constructor_wire, slot_tokens),
            cfg: quote!(::core::default::Default::default()),
            attributes: quote!(#(#cfg)*),
            provenance: quote!(#provenance),
            prelude: TokenStream::new(),
        }
        .render();
        let grammar_factory_tokens = DescriptorFactory {
            facade,
            factory: &grammar_factory,
            name: quote!(#grammar_name),
            item_kind: quote!(#facade::ItemKind::Grammar),
            disambiguator: quote!(#disambiguator),
            identity_label: "Cargo and Rust macro context form a valid list-grammar identity",
            declared_type: quote!(::core::option::Option::None),
            payload: FactoryPayload::wire(grammar_wire, grammar_slot_tokens),
            cfg: quote!(::core::default::Default::default()),
            attributes: quote!(#(#cfg)*),
            provenance: quote!(#provenance),
            prelude: TokenStream::new(),
        }
        .render();

        Ok(quote! {
            #(#field_key_functions)*
            #strictness_key

            #descriptor_factory_tokens

            #grammar_factory_tokens
        })
    }
}
