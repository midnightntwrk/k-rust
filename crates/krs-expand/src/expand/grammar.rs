//! Grammar declarations: `precedence!`, `associativity!`, `lexical!`, and `layout!`.

use crate::ExpandError;
use krs_diagnostic::codes::expand;
use krs_ir::wire::{WireGrammarDescriptor, WirePayload};
use krs_ir::{
    DescriptorAssociativitySentence, DescriptorGroupReference, DescriptorLayoutRegex,
    DescriptorLexical, DescriptorPrecedenceChain, GroupAssociativity, ProductionGroupId,
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
        let groups = chain.groups().try_map_ref(|group| -> crate::Result<_> {
            let name = group.to_string();
            let ordinal = group_ordinal;
            group_ordinal = group_ordinal.checked_add(1).ok_or_else(|| {
                ExpandError::new(
                    expand::DESCRIPTOR_CAPACITY,
                    group.span(),
                    "too many precedence groups",
                )
            })?;
            Ok(DescriptorGroupReference {
                key: wire_key(precedence_group_reference_role, ordinal),
                group: ProductionGroupId::new(name)
                    .expect("Rust identifiers are valid production groups"),
            })
        })?;
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

pub(crate) fn lexical(
    env: &dyn MacroEnvironment,
    input: TokenStream,
) -> crate::Result<TokenStream> {
    let declaration = krs_syntax::LexicalDeclaration::parse_tokens(input)?;
    let lexicals = declaration
        .entries()
        .iter()
        .enumerate()
        .map(|(index, entry)| -> crate::Result<_> {
            let ordinal = u32::try_from(index).map_err(|_| {
                ExpandError::new(
                    expand::DESCRIPTOR_CAPACITY,
                    entry.name().span(),
                    "too many lexical entries",
                )
            })?;
            Ok(DescriptorLexical {
                key: wire_key(ProvenanceRole::LexicalDeclaration, ordinal),
                name: entry.name().to_string(),
                regex_key: wire_key(ProvenanceRole::LexicalRegex, ordinal),
                regex: entry.regex().value(),
            })
        })
        .collect::<crate::Result<Vec<_>>>()?;
    lexing_descriptor(
        env,
        "lexical",
        &declaration.provenance()?,
        &WireGrammarDescriptor::Lexical { lexicals },
    )
}

pub(crate) fn layout(env: &dyn MacroEnvironment, input: TokenStream) -> crate::Result<TokenStream> {
    let declaration = krs_syntax::LayoutDeclaration::parse_tokens(input)?;
    let regexes = declaration
        .regexes()
        .iter()
        .enumerate()
        .map(|(index, regex)| -> crate::Result<_> {
            let ordinal = u32::try_from(index).map_err(|_| {
                ExpandError::new(
                    expand::DESCRIPTOR_CAPACITY,
                    regex.span(),
                    "too many layout regexes",
                )
            })?;
            Ok(DescriptorLayoutRegex {
                key: wire_key(ProvenanceRole::LayoutRegex, ordinal),
                regex: regex.value(),
            })
        })
        .collect::<crate::Result<Vec<_>>>()?;
    lexing_descriptor(
        env,
        "layout",
        &declaration.provenance()?,
        &WireGrammarDescriptor::Layout { regexes },
    )
}

/// Registers one `k::lexical!` or `k::layout!` block as a grammar descriptor.
fn lexing_descriptor(
    env: &dyn MacroEnvironment,
    kind: &str,
    anchors: &[ProvenanceAnchor],
    grammar: &WireGrammarDescriptor,
) -> crate::Result<TokenStream> {
    let facade = env.facade_path()?;
    let fallback = anchors
        .first()
        .map(ProvenanceAnchor::range)
        .ok_or_else(|| {
            ExpandError::new(
                expand::EMPTY_GRAMMAR_DECLARATION,
                Span::call_site(),
                format!("empty {kind} declaration"),
            )
        })?;
    let provenance = host_provenance(env, &facade, fallback, anchors);
    let nonce = expansion_nonce(env, kind, &Ident::new(kind, Span::call_site()), fallback);
    let factory = format_ident!("__krs_{kind}_descriptor_{nonce:016x}");
    Ok(grammar_macro_descriptor(
        &facade,
        &factory,
        &format!("__krs_grammar_{kind}_{nonce:016x}"),
        kind,
        grammar,
        &provenance,
        None,
    ))
}

/// Expands `k::raw_k!("...")` into a grammar descriptor carrying the
/// unchecked sentence text. Whether the package may use raw K is decided after
/// collection, where its metadata and `krs --profile` are known.
pub(crate) fn raw_k(env: &dyn MacroEnvironment, input: TokenStream) -> crate::Result<TokenStream> {
    let raw = krs_syntax::RawKItem::parse_tokens(input)?;
    let facade = env.facade_path()?;
    let anchors = raw.provenance()?;
    let fallback = anchors[0].range();
    let provenance = host_provenance(env, &facade, fallback, &anchors);
    let nonce = expansion_nonce(
        env,
        "raw_k",
        &Ident::new("raw_k", Span::call_site()),
        fallback,
    );
    let factory = format_ident!("__krs_raw_k_descriptor_{nonce:016x}");
    let position = env
        .call_site()
        .and_then(|span| env.span_start(span))
        .or_else(|| env.span_start(raw.literal().span()));
    let (line, column) = position.map_or((1, 1), |position| (position.line, position.column));
    let grammar = WireGrammarDescriptor::RawSentence {
        key: wire_key(ProvenanceRole::RawKDeclaration, 0),
        kind: raw.kind(),
        text: raw.text(),
        line,
        column,
    };
    Ok(grammar_macro_descriptor(
        &facade,
        &factory,
        &format!("__krs_raw_k_{nonce:016x}"),
        "raw_k",
        &grammar,
        &provenance,
        None,
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
