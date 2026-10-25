//! Grammar declarations: `precedence!`, `associativity!`, `lexical!`, and `layout!`.

use crate::ExpandError;
use krs_diagnostic::codes::expand;
use krs_ir::wire::{WireGrammarDescriptor, WirePayload};
use krs_ir::{
    DescriptorAssociativitySentence, DescriptorGroupReference, DescriptorLayoutRegex,
    DescriptorLexical, DescriptorPrecedenceChain, GroupAssociativity, ProductionGroupId,
};
use krs_syntax::KrsSyntax;
use krs_syntax::{GroupAssociativity as SyntaxGroupAssociativity, ProvenanceAnchor};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::{Ident, Path};

use super::factory::{DescriptorFactory, FactoryPayload};
use super::nonce::expansion_nonce;
use super::terms::held_key;
use crate::environment::MacroEnvironment;
use crate::provenance::host_provenance;

pub(crate) fn precedence(
    env: &dyn MacroEnvironment,
    input: TokenStream,
) -> crate::Result<TokenStream> {
    let declaration = krs_syntax::PrecedenceDeclaration::parse_tokens(input)?;
    let facade = env.facade_path()?;
    let anchors = declaration.provenance()?;
    let fallback = anchors
        .first()
        .map(ProvenanceAnchor::range)
        // An empty declaration has no part to point at.
        .ok_or_else(|| {
            ExpandError::at_invocation(
                expand::EMPTY_GRAMMAR_DECLARATION,
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
    let mut chains = Vec::new();
    for chain in declaration.chains() {
        let mut group_keys = chain.group_keys().iter();
        let groups = chain.groups().try_map_ref(|group| -> crate::Result<_> {
            let name = group.to_string();
            Ok(DescriptorGroupReference {
                key: held_key(group_keys.next())?,
                group: ProductionGroupId::new(name)
                    .expect("Rust identifiers are valid production groups"),
            })
        })?;
        chains.push(DescriptorPrecedenceChain {
            key: held_key(chain.key())?,
            groups,
        });
    }
    let grammar = WireGrammarDescriptor::Precedence {
        key: held_key(declaration.key())?,
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
    let declaration = krs_syntax::AssociativityDeclaration::parse_tokens(input)?;
    let facade = env.facade_path()?;
    let anchors = declaration.provenance()?;
    let fallback = anchors
        .first()
        .map(ProvenanceAnchor::range)
        // An empty declaration has no part to point at.
        .ok_or_else(|| {
            ExpandError::at_invocation(
                expand::EMPTY_GRAMMAR_DECLARATION,
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
    let mut sentences = Vec::new();
    for sentence in declaration.sentences() {
        let associativity = match sentence.associativity() {
            SyntaxGroupAssociativity::Left => GroupAssociativity::Left,
            SyntaxGroupAssociativity::Right => GroupAssociativity::Right,
            SyntaxGroupAssociativity::NonAssociative => GroupAssociativity::NonAssociative,
        };
        let mut groups = Vec::new();
        for (group, read) in sentence.groups().iter().zip(
            sentence
                .group_keys()
                .iter()
                .map(Some)
                .chain(std::iter::repeat(None)),
        ) {
            let name = group.to_string();
            groups.push(DescriptorGroupReference {
                key: held_key(read)?,
                group: ProductionGroupId::new(name)
                    .expect("Rust identifiers are valid production groups"),
            });
        }
        sentences.push(DescriptorAssociativitySentence {
            key: held_key(sentence.key())?,
            associativity,
            groups,
        });
    }
    let grammar = WireGrammarDescriptor::Associativity {
        key: held_key(declaration.key())?,
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
        .map(|entry| -> crate::Result<_> {
            Ok(DescriptorLexical {
                key: held_key(entry.key())?,
                name: entry.name().to_string(),
                regex_key: held_key(entry.regex_key())?,
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
            Ok(DescriptorLayoutRegex {
                key: held_key(declaration.regex_keys().get(index))?,
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
        // An empty declaration has no part to point at.
        .ok_or_else(|| {
            ExpandError::at_invocation(
                expand::EMPTY_GRAMMAR_DECLARATION,
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
        key: held_key(raw.key())?,
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
