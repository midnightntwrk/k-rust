//! `#[k::constant]`: a named ground constructor term.
//!
//! The `const` item becomes a unit struct of the same name, so the name
//! keeps Rust's scoping, imports, and visibility, and a use resolves through
//! rustc as a constructor's name does: by `TypeId` where the path is
//! qualified, and through the readable-rule witness where a block's or a
//! table's imports are in scope. The descriptor carries the declared sort and
//! the value; the compiler substitutes the value at every use.

use krs_ir::wire::{WireConstant, WirePayload, WireSortReference, WireTypeReference};
use krs_syntax::{KrsSyntax, ProvenanceRole};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};

use super::factory::{DescriptorFactory, FactoryPayload};
use super::ledger::KeyLedger;
use super::nonce::expansion_nonce;
use super::terms::{KeyedTerm, TermBuilder, TermSide, WireSlots};
use super::tokens::{call_site_cfg_attributes, call_site_ident, call_site_path, sort_type_tokens};
use crate::environment::MacroEnvironment;
use crate::provenance::host_provenance;

pub(crate) fn constant(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> crate::Result<TokenStream> {
    if let Some(first) = attributes.into_iter().next() {
        return Err(krs_syntax::SyntaxError::new(
            krs_syntax::SyntaxErrorKind::UnexpectedAttributePayload {
                attribute: "constant",
            },
            first.span(),
        )
        .into());
    }
    let constant = krs_syntax::ConstantItem::parse_tokens(item)?;
    let facade = env.facade_path()?;
    let item = constant.item();
    let fallback = krs_syntax::TokenRange::for_tokens(item)?;
    let anchors = constant.provenance()?;
    let provenance = host_provenance(env, &facade, fallback, &anchors);
    // The name is the descriptor's own key.
    let ledger = KeyLedger::new(&anchors, &[ProvenanceRole::ConstantDeclaration]);
    let nonce = expansion_nonce(env, "constant", constant.name(), fallback);
    let factory = format_ident!(
        "__krs_constant_descriptor_{nonce:016x}",
        span = Span::call_site()
    );
    let declared_key = format_ident!("__krs_constant_type_{nonce:016x}", span = Span::call_site());
    let sort_key = format_ident!("__krs_constant_sort_{nonce:016x}", span = Span::call_site());
    let cfg = call_site_cfg_attributes(&item.attrs)?;
    let declared = call_site_ident(constant.name())?;
    let sort = constant.sort();
    let sort_type = sort_type_tokens(&facade, &call_site_path(sort.sort())?, sort.is_dynamic());

    let mut slots = WireSlots::new(&facade);
    let sort_reference = WireSortReference {
        key: ledger.define(constant.type_key())?,
        target: WireTypeReference {
            slot: slots.type_slot(quote!(#facade::HostTypeKey(#sort_key))),
            authored_path: sort.sort_token_text(),
        },
    };
    // A constant binds nothing, so every name in its value is a path that
    // rustc resolves: another constant or a constructor.
    let mut builder = TermBuilder::new(&facade, &ledger, nonce, &cfg, &[]);
    // The value's payload key carries no field on the wire: the value term
    // denotes the whole value expression, and the transport pairs the
    // constant's one value with it.
    ledger.define(constant.value().keys().payload())?;
    let value =
        builder.expand_wire(KeyedTerm::of(constant.value()), TermSide::Right, &mut slots)?;
    let key_functions = std::mem::take(&mut builder.key_functions);
    ledger.finish()?;
    let wire = WirePayload::Constant(Box::new(WireConstant {
        sort: sort_reference,
        value,
    }));
    let wire = serde_json::to_string(&wire).expect("constant wire is serializable");
    let name = constant.name().to_string();
    let factory_tokens = DescriptorFactory {
        facade: &facade,
        factory: &factory,
        name: quote!(#name),
        item_kind: quote!(#facade::ItemKind::Constant),
        disambiguator: quote!(""),
        identity_label: "Cargo and Rust macro context form a valid host identity",
        declared_type: quote! {
            ::core::option::Option::Some(
                #facade::HostDeclarationIdentity::Nominal(#facade::HostTypeKey(#declared_key)),
            )
        },
        payload: FactoryPayload::wire(wire, slots.tokens()),
        cfg: quote!(::core::default::Default::default()),
        attributes: quote!(#(#cfg)*),
        provenance: quote!(#provenance),
        prelude: TokenStream::new(),
    }
    .render();

    let attrs = &item.attrs;
    let vis = &item.vis;
    let ident = &item.ident;
    let authored_sort = sort.ty();
    Ok(quote! {
        // The constant is a name, not a Rust value: a unit struct keeps the
        // name in Rust's type and value namespaces for resolution, and no
        // Rust code constructs it.
        #(#attrs)*
        #[allow(non_camel_case_types, dead_code, clippy::upper_case_acronyms)]
        #vis struct #ident;

        #(#cfg)*
        const _: ::core::marker::PhantomData<#authored_sort> = ::core::marker::PhantomData;

        #(#cfg)*
        #[doc(hidden)]
        fn #declared_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#declared>()
        }

        #(#cfg)*
        #[doc(hidden)]
        fn #sort_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#sort_type>()
        }

        // A one-segment use under a block's or a table's imports resolves
        // through the readable-rule witness, as a constructor's name does.
        #(#cfg)*
        impl<const __KRS_SELECTOR: u64> #facade::__KrsRuleApplication<__KRS_SELECTOR> for #declared {
            fn __krs_rule_application(authored_path: &str) -> #facade::HostApplicationTarget {
                #facade::HostApplicationTarget::Nominal(#facade::HostTypeReference {
                    key: #facade::HostTypeKey(#declared_key),
                    authored_path: authored_path.to_owned(),
                })
            }
        }

        #(#key_functions)*

        #factory_tokens
    })
}
