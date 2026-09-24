//! Grammar ordering declarations: `precedence!` and `associativity!`.

use krs_syntax::{
    GroupAssociativity as SyntaxGroupAssociativity, ProvenanceAnchor, ProvenanceRole,
    parse_associativity_declaration, parse_precedence_declaration,
};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::{Ident, Path};

use super::nonce::expansion_nonce;
use crate::environment::MacroEnvironment;
use crate::provenance::host_provenance;

pub(crate) fn precedence(
    env: &dyn MacroEnvironment,
    input: TokenStream,
) -> syn::Result<TokenStream> {
    let precedence_group_reference_role = ProvenanceRole::PrecedenceGroupReference;
    let precedence_chain_role = ProvenanceRole::PrecedenceChain;
    let precedence_declaration_role = ProvenanceRole::PrecedenceDeclaration;
    let declaration =
        parse_precedence_declaration(input).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let facade = env.facade_path()?;
    let anchors = declaration
        .provenance()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let fallback = anchors
        .first()
        .map(ProvenanceAnchor::range)
        .ok_or_else(|| syn::Error::new(Span::call_site(), "empty precedence declaration"))?;
    let provenance = host_provenance(env, &facade, fallback, &anchors)?;
    let nonce = expansion_nonce(
        env,
        "precedence",
        &Ident::new("precedence", Span::call_site()),
        fallback,
    );
    let factory = format_ident!("__krs_precedence_descriptor_{nonce:016x}");
    let grammar_name = declaration.owner().map_or_else(
        || format!("__krs_grammar_precedence_{nonce:016x}"),
        |owner| format!("__krs_grammar_{owner}_precedence"),
    );
    let disambiguator = declaration.owner().map_or_else(
        || "precedence".to_owned(),
        |owner| format!("enum-precedence:{owner}"),
    );
    let mut group_ordinal = 0_u32;
    let mut chains = Vec::new();
    for (chain_index, chain) in declaration.chains().iter().enumerate() {
        let chain_ordinal = u32::try_from(chain_index)
            .map_err(|_| syn::Error::new(Span::call_site(), "too many precedence chains"))?;
        let mut groups = Vec::new();
        for group in chain.groups() {
            let name = group.to_string();
            let ordinal = group_ordinal;
            group_ordinal = group_ordinal
                .checked_add(1)
                .ok_or_else(|| syn::Error::new(group.span(), "too many precedence groups"))?;
            groups.push(quote! {
                #facade::DescriptorGroupReference {
                    key: #facade::ProvenanceKey::new(#precedence_group_reference_role, #ordinal)
                        .expect("KRS parser roles are nonempty"),
                    group: #facade::ProductionGroupId::new(#name)
                        .expect("Rust identifiers are valid production groups"),
                }
            });
        }
        chains.push(quote! {
            #facade::DescriptorPrecedenceChain {
                key: #facade::ProvenanceKey::new(#precedence_chain_role, #chain_ordinal)
                    .expect("KRS parser roles are nonempty"),
                groups: ::std::vec![#(#groups),*],
            }
        });
    }
    let grammar = quote! {
        #facade::HostGrammarDescriptor::Precedence {
            key: #facade::ProvenanceKey::new(#precedence_declaration_role, 0)
                .expect("KRS parser roles are nonempty"),
            chains: ::std::vec![#(#chains),*],
        }
    };
    Ok(grammar_macro_descriptor(
        &facade,
        &factory,
        &grammar_name,
        &disambiguator,
        &grammar,
        &provenance,
        declaration.owner(),
    ))
}

pub(crate) fn associativity(
    env: &dyn MacroEnvironment,
    input: TokenStream,
) -> syn::Result<TokenStream> {
    let associativity_group_reference_role = ProvenanceRole::AssociativityGroupReference;
    let associativity_sentence_role = ProvenanceRole::AssociativitySentence;
    let associativity_declaration_role = ProvenanceRole::AssociativityDeclaration;
    let declaration =
        parse_associativity_declaration(input).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let facade = env.facade_path()?;
    let anchors = declaration
        .provenance()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let fallback = anchors
        .first()
        .map(ProvenanceAnchor::range)
        .ok_or_else(|| syn::Error::new(Span::call_site(), "empty associativity declaration"))?;
    let provenance = host_provenance(env, &facade, fallback, &anchors)?;
    let nonce = expansion_nonce(
        env,
        "associativity",
        &Ident::new("associativity", Span::call_site()),
        fallback,
    );
    let factory = format_ident!("__krs_associativity_descriptor_{nonce:016x}");
    let grammar_name = declaration.owner().map_or_else(
        || format!("__krs_grammar_associativity_{nonce:016x}"),
        |owner| format!("__krs_grammar_{owner}_associativity"),
    );
    let disambiguator = declaration.owner().map_or_else(
        || "associativity".to_owned(),
        |owner| format!("enum-associativity:{owner}"),
    );
    let mut group_ordinal = 0_u32;
    let mut sentences = Vec::new();
    for (sentence_index, sentence) in declaration.sentences().iter().enumerate() {
        let sentence_ordinal = u32::try_from(sentence_index)
            .map_err(|_| syn::Error::new(Span::call_site(), "too many associativity sentences"))?;
        let associativity = match sentence.associativity() {
            SyntaxGroupAssociativity::Left => quote!(#facade::GroupAssociativity::Left),
            SyntaxGroupAssociativity::Right => quote!(#facade::GroupAssociativity::Right),
            SyntaxGroupAssociativity::NonAssociative => {
                quote!(#facade::GroupAssociativity::NonAssociative)
            }
        };
        let mut groups = Vec::new();
        for group in sentence.groups() {
            let name = group.to_string();
            let ordinal = group_ordinal;
            group_ordinal = group_ordinal
                .checked_add(1)
                .ok_or_else(|| syn::Error::new(group.span(), "too many associativity groups"))?;
            groups.push(quote! {
                #facade::DescriptorGroupReference {
                    key: #facade::ProvenanceKey::new(#associativity_group_reference_role, #ordinal)
                        .expect("KRS parser roles are nonempty"),
                    group: #facade::ProductionGroupId::new(#name)
                        .expect("Rust identifiers are valid production groups"),
                }
            });
        }
        sentences.push(quote! {
            #facade::DescriptorAssociativitySentence {
                key: #facade::ProvenanceKey::new(#associativity_sentence_role, #sentence_ordinal)
                    .expect("KRS parser roles are nonempty"),
                associativity: #associativity,
                groups: ::std::vec![#(#groups),*],
            }
        });
    }
    let grammar = quote! {
        #facade::HostGrammarDescriptor::Associativity {
            key: #facade::ProvenanceKey::new(#associativity_declaration_role, 0)
                .expect("KRS parser roles are nonempty"),
            sentences: ::std::vec![#(#sentences),*],
        }
    };
    Ok(grammar_macro_descriptor(
        &facade,
        &factory,
        &grammar_name,
        &disambiguator,
        &grammar,
        &provenance,
        declaration.owner(),
    ))
}

pub(super) fn grammar_macro_descriptor(
    facade: &Path,
    factory: &Ident,
    name: &str,
    disambiguator: &str,
    grammar: &TokenStream,
    provenance: &TokenStream,
    owner: Option<&Ident>,
) -> TokenStream {
    let owner_check = owner.map(|owner| {
        quote! {
            let _ = ::core::any::TypeId::of::<#owner>();
        }
    });
    quote! {
        #[doc(hidden)]
        fn #factory() -> #facade::HostDescriptor {
            #owner_check
            #facade::HostDescriptor {
                protocol_version: #facade::ProtocolVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"),
                    env!("CARGO_MANIFEST_DIR"), module_path!(), #name,
                    #facade::ItemKind::Grammar, #disambiguator,
                ).expect("Cargo and Rust macro context form a valid grammar identity"),
                declared_type: ::core::option::Option::None,
                payload: #facade::HostDescriptorPayload::Grammar(
                    ::std::boxed::Box::new(#grammar),
                ),
                cfg: ::core::default::Default::default(),
                provenance: #provenance,
            }
        }

        #facade::__register_host_descriptor!(#factory);
    }
}
