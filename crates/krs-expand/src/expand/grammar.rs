//! Grammar ordering declarations: `precedence!` and `associativity!`.

use crate::ExpandError;
use krs_diagnostic::codes::expand;
use krs_ir::wire::{WireGrammarDescriptor, WirePayload};
use krs_ir::{
    DescriptorAssociativitySentence, DescriptorGroupReference, DescriptorPrecedenceChain,
    GroupAssociativity, ProductionGroupId,
};
use krs_syntax::KrsSyntax;
use krs_syntax::{
    GroupAssociativity as SyntaxGroupAssociativity, ProvenanceAnchor, ProvenanceRole,
};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::{Ident, Path};

use super::factory::{DescriptorFactory, FactoryPayload};
use super::nonce::expansion_nonce;
use super::terms::wire_key;
use crate::environment::MacroEnvironment;
use crate::provenance::host_provenance;

pub(crate) fn precedence(
    env: &dyn MacroEnvironment,
    input: TokenStream,
) -> crate::Result<TokenStream> {
    let precedence_group_reference_role = ProvenanceRole::PrecedenceGroupReference;
    let precedence_chain_role = ProvenanceRole::PrecedenceChain;
    let precedence_declaration_role = ProvenanceRole::PrecedenceDeclaration;
    let declaration = krs_syntax::PrecedenceDeclaration::parse_tokens(input)?;
    let facade = env.facade_path()?;
    let anchors = declaration.provenance()?;
    let fallback = anchors
        .first()
        .map(ProvenanceAnchor::range)
        .ok_or_else(|| {
            ExpandError::new(
                expand::EMPTY_GRAMMAR_DECLARATION,
                Span::call_site(),
                "empty precedence declaration",
            )
        })?;
    let provenance = host_provenance(env, &facade, fallback, &anchors);
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
        let chain_ordinal = u32::try_from(chain_index).map_err(|_| {
            ExpandError::new(
                expand::DESCRIPTOR_CAPACITY,
                Span::call_site(),
                "too many precedence chains",
            )
        })?;
        let mut groups = Vec::new();
        for group in chain.groups() {
            let name = group.to_string();
            let ordinal = group_ordinal;
            group_ordinal = group_ordinal.checked_add(1).ok_or_else(|| {
                ExpandError::new(
                    expand::DESCRIPTOR_CAPACITY,
                    group.span(),
                    "too many precedence groups",
                )
            })?;
            groups.push(DescriptorGroupReference {
                key: wire_key(precedence_group_reference_role, ordinal),
                group: ProductionGroupId::new(name)
                    .expect("Rust identifiers are valid production groups"),
            });
        }
        chains.push(DescriptorPrecedenceChain {
            key: wire_key(precedence_chain_role, chain_ordinal),
            groups,
        });
    }
    let grammar = WireGrammarDescriptor::Precedence {
        key: wire_key(precedence_declaration_role, 0),
        chains,
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
) -> crate::Result<TokenStream> {
    let associativity_group_reference_role = ProvenanceRole::AssociativityGroupReference;
    let associativity_sentence_role = ProvenanceRole::AssociativitySentence;
    let associativity_declaration_role = ProvenanceRole::AssociativityDeclaration;
    let declaration = krs_syntax::AssociativityDeclaration::parse_tokens(input)?;
    let facade = env.facade_path()?;
    let anchors = declaration.provenance()?;
    let fallback = anchors
        .first()
        .map(ProvenanceAnchor::range)
        .ok_or_else(|| {
            ExpandError::new(
                expand::EMPTY_GRAMMAR_DECLARATION,
                Span::call_site(),
                "empty associativity declaration",
            )
        })?;
    let provenance = host_provenance(env, &facade, fallback, &anchors);
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
        let sentence_ordinal = u32::try_from(sentence_index).map_err(|_| {
            ExpandError::new(
                expand::DESCRIPTOR_CAPACITY,
                Span::call_site(),
                "too many associativity sentences",
            )
        })?;
        let associativity = match sentence.associativity() {
            SyntaxGroupAssociativity::Left => GroupAssociativity::Left,
            SyntaxGroupAssociativity::Right => GroupAssociativity::Right,
            SyntaxGroupAssociativity::NonAssociative => GroupAssociativity::NonAssociative,
        };
        let mut groups = Vec::new();
        for group in sentence.groups() {
            let name = group.to_string();
            let ordinal = group_ordinal;
            group_ordinal = group_ordinal.checked_add(1).ok_or_else(|| {
                ExpandError::new(
                    expand::DESCRIPTOR_CAPACITY,
                    group.span(),
                    "too many associativity groups",
                )
            })?;
            groups.push(DescriptorGroupReference {
                key: wire_key(associativity_group_reference_role, ordinal),
                group: ProductionGroupId::new(name)
                    .expect("Rust identifiers are valid production groups"),
            });
        }
        sentences.push(DescriptorAssociativitySentence {
            key: wire_key(associativity_sentence_role, sentence_ordinal),
            associativity,
            groups,
        });
    }
    let grammar = WireGrammarDescriptor::Associativity {
        key: wire_key(associativity_declaration_role, 0),
        sentences,
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
    grammar: &WireGrammarDescriptor,
    provenance: &TokenStream,
    owner: Option<&Ident>,
) -> TokenStream {
    let wire = serde_json::to_string(&WirePayload::Grammar(Box::new(grammar.clone())))
        .expect("KRS wire values serialize");
    let owner_check = owner.map(|owner| {
        quote! {
            let _ = ::core::any::TypeId::of::<#owner>();
        }
    });
    DescriptorFactory {
        facade,
        factory,
        name: quote!(#name),
        item_kind: quote!(#facade::ItemKind::Grammar),
        disambiguator: quote!(#disambiguator),
        identity_label: "Cargo and Rust macro context form a valid grammar identity",
        declared_type: quote!(::core::option::Option::None),
        payload: FactoryPayload::wire(wire, quote!(#facade::__KrsSlots::default())),
        cfg: quote!(::core::default::Default::default()),
        attributes: TokenStream::new(),
        provenance: quote!(#provenance),
        prelude: quote!(#owner_check),
    }
    .render()
}
