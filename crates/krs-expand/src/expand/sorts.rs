//! Sort declarations: `#[k::sort]`, `sorts!`, the facade's framework sort block, `#[k::bracket]`, and `#[k::subsort]`.

use std::collections::{BTreeMap, BTreeSet};

use super::terms::{WireSlots, wire_key, wire_sort_reference};
use krs_ir::wire::{WireGrammarDescriptor, WirePayload};
use krs_syntax::surface::{AttributeMacro, helper_entry};
use krs_syntax::{
    ProvenanceAnchor, ProvenanceRole, SyntaxTemplateItem, TokenRange, parse_bracket_attribute,
    parse_sort_attribute, parse_sort_declaration, parse_sorts_declaration, parse_subsort_attribute,
    parse_subsort_declaration,
};
use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{ToTokens, format_ident, quote};
use syn::spanned::Spanned;
use syn::{Attribute, Ident, ItemTrait, Path, parse_quote};

use super::constructors::{reject_unexpanded_symbol, take_explicit_symbol_helper};
use super::nonce::expansion_nonce;
use super::tokens::{
    call_site_cfg_attributes, call_site_ident, call_site_path, helper_tokens, spelling,
    type_reference,
};
use crate::environment::MacroEnvironment;
use crate::provenance::host_provenance;

#[allow(clippy::too_many_lines)] // Legacy and aliased carriers share one descriptor expansion.
pub(crate) fn sort(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let attribute =
        parse_sort_attribute(attributes).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let mut item: ItemTrait = syn::parse2(item)?;
    reject_unexpanded_symbol(&item.attrs)?;
    let explicit_symbol = take_explicit_symbol_helper(&mut item.attrs)?;
    let brackets = take_bracket_helpers(&mut item.attrs)?;
    let declaration = parse_sort_declaration(item.to_token_stream())
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let facade = env.facade_path()?;
    if attribute.is_reference() && attribute.parents().len() != declaration.parents().len() {
        return Err(syn::Error::new(
            declaration.item().ident.span(),
            "a reference sort must materialize one semantic parent path for each Rust marker supertrait",
        ));
    }
    let semantic_sort_range =
        TokenRange::for_tokens(attribute.alias().unwrap_or(&declaration.item().ident))
            .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let mut anchors = if attribute.is_reference() {
        let mut anchors = vec![ProvenanceAnchor::new(
            ProvenanceRole::SortDeclaration,
            0,
            semantic_sort_range,
        )];
        for (ordinal, parent) in attribute.parents().iter().enumerate() {
            let ordinal = u32::try_from(ordinal)
                .map_err(|_| syn::Error::new(parent.span(), "too many sort parents"))?;
            anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::SortParent,
                ordinal,
                TokenRange::for_tokens(parent).map_err(krs_syntax::SyntaxError::into_syn_error)?,
            ));
        }
        anchors
    } else {
        declaration
            .provenance()
            .map_err(krs_syntax::SyntaxError::into_syn_error)?
    };
    if let Some(symbol) = &explicit_symbol {
        anchors.extend(
            symbol
                .provenance()
                .map_err(krs_syntax::SyntaxError::into_syn_error)?,
        );
    }
    let fallback = krs_syntax::TokenRange::for_tokens(declaration.item())
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let provenance = host_provenance(env, &facade, fallback, &anchors);
    let nonce = expansion_nonce(env, "sort", &declaration.item().ident, fallback);
    let factory = format_ident!(
        "__krs_sort_descriptor_{nonce:016x}",
        span = Span::call_site()
    );
    let declared_key = format_ident!("__krs_sort_type_{nonce:016x}", span = Span::call_site());
    let item = declaration.item();
    let name = attribute
        .alias()
        .map_or_else(|| declaration.item().ident.to_string(), ToString::to_string);
    let declared = call_site_ident(&declaration.item().ident)?;
    let declared_type = if let Some(alias) = attribute.alias() {
        let alias = call_site_ident(alias)?;
        quote!(#alias)
    } else {
        quote!(dyn #declared)
    };
    let cfg = call_site_cfg_attributes(&item.attrs)?;

    let mut key_functions = Vec::new();
    let mut parents = Vec::new();
    let semantic_parents = if attribute.is_reference() {
        attribute.parents()
    } else {
        declaration.parents()
    };
    for (index, parent) in semantic_parents.iter().enumerate() {
        let key = format_ident!(
            "__krs_sort_parent_{nonce:016x}_{index}",
            span = Span::call_site()
        );
        let generated = call_site_path(parent)?;
        let spelling = spelling(parent);
        let parent_type = if attribute.is_reference() {
            quote!(#generated)
        } else {
            quote!(dyn #generated)
        };
        key_functions.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #key() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#parent_type>()
            }
        });
        parents.push(type_reference(&facade, &key, &spelling));
    }

    let mut grammar = Vec::new();
    for (index, bracket) in brackets.iter().enumerate() {
        grammar.push(expand_bracket_grammar(
            env,
            &facade,
            &name,
            semantic_sort_range,
            bracket,
            nonce,
            index,
            &cfg,
        )?);
    }
    let framework_request = (attribute.is_reference()
        && semantic_parents.iter().any(is_framework_sort_path))
    .then(|| quote!(#facade::__request_framework_sorts!();));

    Ok(quote! {
        #item

        #framework_request

        #(#cfg)*
        #[doc(hidden)]
        fn #declared_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#declared_type>()
        }

        #(#key_functions)*

        #(#cfg)*
        #[doc(hidden)]
        fn #factory() -> #facade::HostDescriptor {
            #facade::HostDescriptor {
                protocol_version: #facade::SchemaVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"),
                    env!("CARGO_PKG_VERSION"),
                    env!("CARGO_MANIFEST_DIR"),
                    module_path!(),
                    #name,
                    #facade::ItemKind::Sort,
                    "",
                )
                .expect("Cargo and Rust macro context form a valid host identity"),
                declared_type: ::core::option::Option::Some(
                    #facade::HostDeclarationIdentity::Nominal(
                        #facade::HostTypeKey(#declared_key),
                    ),
                ),
                payload: #facade::HostDescriptorPayload::Sort(#facade::HostSortDescriptor {
                    parents: ::std::vec![#(#parents),*],
                }),
                cfg: ::core::default::Default::default(),
                provenance: #provenance,
            }
        }

        #(#cfg)*
        #facade::__register_host_descriptor!(#factory);

        #(#grammar)*
    })
}

/// Expands the readable sort block into marker/alias pairs and semantic edges.
///
/// A direct member also receives every local ancestor marker required by the
/// generated Rust supertrait graph. The pair set is deduplicated so diamonds
/// produce exactly one Rust impl for their shared ancestor; only the authored
/// direct edge is registered as an object-language subsort descriptor.
pub(crate) fn sorts(env: &dyn MacroEnvironment, input: TokenStream) -> syn::Result<TokenStream> {
    let declaration =
        parse_sorts_declaration(input).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let facade = env.facade_path()?;
    let local_parents = declaration
        .entries()
        .iter()
        .filter_map(|entry| match entry {
            krs_syntax::SortsEntry::Sort(sort) => {
                Some((sort.name().to_string(), sort.parents().to_vec()))
            }
            krs_syntax::SortsEntry::Membership(_) => None,
        })
        .collect::<BTreeMap<_, _>>();
    let mut output = Vec::new();
    let mut rust_memberships = Vec::new();
    let mut emitted_rust_memberships = BTreeSet::new();
    let mut readable_memberships = BTreeMap::new();
    let mut requests_framework_sorts = false;
    for entry in declaration.entries() {
        match entry {
            krs_syntax::SortsEntry::Sort(sort) => {
                requests_framework_sorts |= sort.parents().iter().any(is_framework_sort_path);
                output.push(expand_readable_sort(env, &facade, sort)?);
            }
            krs_syntax::SortsEntry::Membership(membership) => {
                requests_framework_sorts |= is_framework_sort_path(membership.supersort());
                for member in membership.members() {
                    let identity = ReadableMembershipIdentity::new(membership.supersort(), member);
                    if let Some(first_span) =
                        readable_memberships.insert(identity.item_name.clone(), member.span())
                    {
                        let mut error = syn::Error::new(
                            member.span(),
                            format!(
                                "duplicate readable membership relation `{}`",
                                identity.relation
                            ),
                        );
                        error.combine(syn::Error::new(first_span, "first declared here"));
                        return Err(error);
                    }
                    let mut supersorts = vec![membership.supersort().clone()];
                    push_local_sort_ancestors(
                        membership.supersort(),
                        &local_parents,
                        &mut BTreeSet::new(),
                        &mut supersorts,
                    );
                    for supersort in supersorts {
                        let marker = readable_sort_marker_path(&facade, &supersort)?;
                        let marker_key = spelling(&marker);
                        let member_key = spelling(member);
                        if emitted_rust_memberships.insert((marker_key, member_key)) {
                            let member = call_site_path(member)?;
                            rust_memberships.push(quote!(impl #marker for #member {}));
                        }
                    }
                    output.push(expand_readable_membership(
                        env, &facade, membership, member, &identity,
                    )?);
                }
            }
        }
    }
    let request = requests_framework_sorts.then(|| {
        quote! {
            #facade::__request_framework_sorts!();
        }
    });
    Ok(quote!(#request #(#output)* #(#rust_memberships)*))
}

/// Expands the facade's own framework sort block and lists its factories.
///
/// The output is exactly the [`sorts`] expansion followed by a crate-private
/// `FRAMEWORK_FACTORIES` table of that invocation's descriptor factories, so a
/// collector without linker-section registration can still obtain the
/// framework descriptors. A procedural macro sees only its own invocation;
/// this per-invocation table is the only registration table it can write.
pub(crate) fn framework_sorts(
    env: &dyn MacroEnvironment,
    input: TokenStream,
) -> syn::Result<TokenStream> {
    let facade = env.facade_path()?;
    let expansion = sorts(env, input)?;
    let factories = registered_factories(&expansion);
    if factories.is_empty() {
        return Err(syn::Error::new(
            Span::call_site(),
            "framework sort block registered no descriptors",
        ));
    }
    Ok(quote! {
        #expansion

        #[doc(hidden)]
        pub(crate) const FRAMEWORK_FACTORIES: &[fn() -> #facade::HostDescriptor] =
            &[#(#factories),*];
    })
}

/// Collects the factories of the top-level `__register_host_descriptor!`
/// invocations in one expansion.
///
/// `sorts!` never places `#[cfg]` attributes on readable sort or membership
/// registrations, so every collected factory is unconditional.
fn registered_factories(expansion: &TokenStream) -> Vec<Ident> {
    let tokens = expansion.clone().into_iter().collect::<Vec<_>>();
    tokens
        .windows(3)
        .filter_map(|window| match window {
            [
                TokenTree::Ident(name),
                TokenTree::Punct(bang),
                TokenTree::Group(arguments),
            ] if name == "__register_host_descriptor"
                && bang.as_char() == '!'
                && arguments.delimiter() == proc_macro2::Delimiter::Parenthesis =>
            {
                let mut arguments = arguments.stream().into_iter();
                match (arguments.next(), arguments.next()) {
                    (Some(TokenTree::Ident(factory)), None) => Some(factory),
                    _ => None,
                }
            }
            _ => None,
        })
        .collect()
}

fn push_local_sort_ancestors(
    sort: &Path,
    local_parents: &BTreeMap<String, Vec<Path>>,
    visited: &mut BTreeSet<String>,
    output: &mut Vec<Path>,
) {
    let Some(name) = local_sort_name(sort) else {
        return;
    };
    if !visited.insert(name.clone()) {
        return;
    }
    let Some(parents) = local_parents.get(&name) else {
        return;
    };
    for parent in parents {
        if local_sort_name(parent).is_some_and(|parent| local_parents.contains_key(&parent)) {
            output.push(parent.clone());
            push_local_sort_ancestors(parent, local_parents, visited, output);
        }
    }
}

fn local_sort_name(path: &Path) -> Option<String> {
    (path.leading_colon.is_none() && path.segments.len() == 1)
        .then(|| path.segments[0].ident.to_string())
}

fn is_framework_sort_path(path: &Path) -> bool {
    path.segments
        .last()
        .is_some_and(|segment| matches!(segment.ident.to_string().as_str(), "KItem" | "KResult"))
}

fn expand_readable_sort(
    env: &dyn MacroEnvironment,
    facade: &Path,
    declaration: &krs_syntax::SortsSort,
) -> syn::Result<TokenStream> {
    let anchors = declaration
        .provenance()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let fallback = anchors
        .first()
        .map(ProvenanceAnchor::range)
        .ok_or_else(|| syn::Error::new(declaration.name().span(), "empty sort declaration"))?;
    let provenance = host_provenance(env, facade, fallback, &anchors);
    let nonce = expansion_nonce(env, "readable_sort", declaration.name(), fallback);
    let factory = format_ident!("__krs_sort_descriptor_{nonce:016x}");
    let declared_key = format_ident!("__krs_sort_type_{nonce:016x}");
    let name = declaration.name().to_string();
    // Preserve the declaration token so references resolved through the
    // generated alias navigate back to the readable `Sort;` declaration.
    let alias = declaration.name();
    let marker = format_ident!("{}Sort", declaration.name(), span = Span::call_site());
    let parent_markers = declaration
        .parents()
        .iter()
        .map(|parent| readable_sort_marker_path(facade, parent))
        .collect::<Result<Vec<_>, _>>()?;

    let mut parent_functions = Vec::new();
    let mut parents = Vec::new();
    for (index, parent) in declaration.parents().iter().enumerate() {
        let key = format_ident!("__krs_sort_parent_{nonce:016x}_{index}");
        // This hidden reference gives language tooling a real use of the
        // authored parent path while retaining its input span.
        let path = parent;
        let authored = spelling(parent);
        parent_functions.push(quote! {
            #[doc(hidden)]
            fn #key() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#path>()
            }
        });
        parents.push(type_reference(facade, &key, &authored));
    }

    let mut brackets = Vec::new();
    for (index, bracket) in declaration.brackets().iter().enumerate() {
        let anchors = declaration
            .bracket_provenance(bracket)
            .map_err(krs_syntax::SyntaxError::into_syn_error)?;
        brackets.push(expand_bracket_grammar_parts(
            env,
            facade,
            &name,
            &declared_key,
            bracket,
            &anchors,
            nonce,
            index,
            &[],
        )?);
    }

    Ok(quote! {
        #[doc = concat!("Membership marker generated for the `", #name, "` K sort.")]
        pub trait #marker: #(#parent_markers)+* {}
        #[doc = concat!("Symbolic term type generated for the `", #name, "` K sort.")]
        pub type #alias = #facade::Term<dyn #marker>;

        #[doc(hidden)]
        fn #declared_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#alias>()
        }

        #(#parent_functions)*

        #[doc(hidden)]
        fn #factory() -> #facade::HostDescriptor {
            #facade::HostDescriptor {
                protocol_version: #facade::SchemaVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"),
                    env!("CARGO_PKG_VERSION"),
                    env!("CARGO_MANIFEST_DIR"),
                    module_path!(),
                    #name,
                    #facade::ItemKind::Sort,
                    "",
                )
                .expect("Cargo and Rust macro context form a valid host identity"),
                declared_type: ::core::option::Option::Some(
                    #facade::HostDeclarationIdentity::Nominal(#facade::HostTypeKey(#declared_key)),
                ),
                payload: #facade::HostDescriptorPayload::Sort(#facade::HostSortDescriptor {
                    parents: ::std::vec![#(#parents),*],
                }),
                cfg: ::core::default::Default::default(),
                provenance: #provenance,
            }
        }

        #facade::__register_host_descriptor!(#factory);
        #(#brackets)*
    })
}

fn expand_readable_membership(
    env: &dyn MacroEnvironment,
    facade: &Path,
    declaration: &krs_syntax::SortsMembership,
    member: &Path,
    identity: &ReadableMembershipIdentity,
) -> syn::Result<TokenStream> {
    let subsort_declaration_role = ProvenanceRole::SubsortDeclaration;
    let anchors = declaration
        .member_provenance(member)
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let fallback = anchors[0].range();
    let provenance = host_provenance(env, facade, fallback, &anchors);
    let rust_key = &identity.rust_key;
    let super_key = format_ident!("__krs_subsort_super_{rust_key}", span = Span::call_site());
    let sub_key = format_ident!("__krs_subsort_sub_{rust_key}", span = Span::call_site());
    let factory = format_ident!(
        "__krs_subsort_descriptor_{rust_key}",
        span = Span::call_site()
    );
    let grammar_name = &identity.item_name;
    // Keep these descriptor-only references attached to the authored
    // membership paths. rust-analyzer can then map definition, hover, and
    // rename requests through the proc-macro expansion; reparsing them with
    // call-site spans severs that mapping. The emitted Rust meaning is
    // unchanged because both paths already parsed successfully above.
    let supersort_alias = declaration.supersort();
    let member_path = member;
    let super_spelling = spelling(declaration.supersort());
    let sub_spelling = spelling(member);
    let mut slots = WireSlots::new(facade);
    let supersort = wire_sort_reference(
        &mut slots,
        facade,
        ProvenanceRole::SubsortSuperSort,
        0,
        &super_key,
        &super_spelling,
    );
    let subsort = wire_sort_reference(
        &mut slots,
        facade,
        ProvenanceRole::SubsortSubSort,
        0,
        &sub_key,
        &sub_spelling,
    );
    let wire = WirePayload::Grammar(Box::new(WireGrammarDescriptor::Subsort {
        key: wire_key(subsort_declaration_role, 0),
        subsort,
        supersort,
    }));
    let wire = serde_json::to_string(&wire).expect("KRS wire values serialize");
    let slot_tokens = slots.tokens();
    Ok(quote! {
        #[doc(hidden)]
        fn #super_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#supersort_alias>()
        }

        #[doc(hidden)]
        fn #sub_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#member_path>()
        }

        #[doc(hidden)]
        fn #factory() -> #facade::HostDescriptor {
            #facade::HostDescriptor {
                protocol_version: #facade::SchemaVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"),
                    env!("CARGO_MANIFEST_DIR"), module_path!(), #grammar_name,
                    #facade::ItemKind::Grammar, "subsort",
                ).expect("Cargo and Rust macro context form a valid subsort identity"),
                declared_type: ::core::option::Option::None,
                payload: #facade::__krs_host_payload(#wire, #slot_tokens),
                cfg: ::core::default::Default::default(),
                provenance: #provenance,
            }
        }

        #facade::__register_host_descriptor!(#factory);
    })
}

struct ReadableMembershipIdentity {
    item_name: String,
    relation: String,
    rust_key: String,
}

impl ReadableMembershipIdentity {
    fn new(supersort: &Path, member: &Path) -> Self {
        let member = canonical_readable_path(member);
        let supersort = canonical_readable_path(supersort);
        let relation = format!("{member} -> {supersort}");
        let item_name = format!("__krs_grammar_subsort(member={member};supersort={supersort})");
        let rust_key = rust_identifier_key(&item_name);
        Self {
            item_name,
            relation,
            rust_key,
        }
    }
}

fn canonical_readable_path(path: &Path) -> String {
    let root = if path.leading_colon.is_some() {
        "absolute"
    } else {
        "relative"
    };
    let segments = path
        .segments
        .iter()
        .map(|segment| segment.ident.to_string())
        .collect::<Vec<_>>()
        .join(".");
    format!("{root}:{segments}")
}

fn rust_identifier_key(value: &str) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(value.len().saturating_mul(2));
    for byte in value.bytes() {
        encoded.push(char::from(HEX[usize::from(byte >> 4)]));
        encoded.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    encoded
}

fn readable_sort_marker_path(facade: &Path, path: &Path) -> syn::Result<Path> {
    if is_framework_sort_path(path) {
        let name = path
            .segments
            .last()
            .expect("a framework sort path is nonempty")
            .ident
            .clone();
        let marker = format_ident!("{name}Sort", span = Span::call_site());
        return Ok(parse_quote!(#facade::#marker));
    }
    let mut marker = call_site_path(path)?;
    let Some(last) = marker.segments.last_mut() else {
        return Err(syn::Error::new(path.span(), "sort path must not be empty"));
    };
    last.ident = format_ident!("{}Sort", last.ident, span = Span::call_site());
    Ok(marker)
}

fn take_bracket_helpers(
    attributes: &mut Vec<Attribute>,
) -> syn::Result<Vec<krs_syntax::BracketAttribute>> {
    let mut brackets = Vec::new();
    let mut retained = Vec::with_capacity(attributes.len());
    for attribute in std::mem::take(attributes) {
        if helper_entry(attribute.path()) == Some(AttributeMacro::Bracket) {
            brackets.push(
                parse_bracket_attribute(helper_tokens(&attribute, AttributeMacro::Bracket.name())?)
                    .map_err(krs_syntax::SyntaxError::into_syn_error)?,
            );
        } else {
            retained.push(attribute);
        }
    }
    *attributes = retained;
    Ok(brackets)
}

pub(crate) fn bracket(attributes: TokenStream, _item: TokenStream) -> syn::Result<TokenStream> {
    parse_bracket_attribute(attributes).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    Err(syn::Error::new(
        Span::call_site(),
        "`#[k::bracket]` is a sort helper; place `#[k::sort]` before it",
    ))
}

#[allow(clippy::too_many_lines)] // Both identity carriers deliberately emit the same payload shape.
pub(crate) fn subsort(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let subsort_declaration_role = ProvenanceRole::SubsortDeclaration;
    let reference = (!attributes.is_empty())
        .then(|| parse_subsort_attribute(attributes))
        .transpose()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let declaration =
        parse_subsort_declaration(item).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let facade = env.facade_path()?;
    let fallback = TokenRange::for_tokens(declaration.item())
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let anchors = if let Some(reference) = &reference {
        vec![
            ProvenanceAnchor::new(ProvenanceRole::SubsortDeclaration, 0, fallback),
            ProvenanceAnchor::new(
                ProvenanceRole::SubsortSuperSort,
                0,
                TokenRange::for_tokens(reference.sort())
                    .map_err(krs_syntax::SyntaxError::into_syn_error)?,
            ),
            ProvenanceAnchor::new(
                ProvenanceRole::SubsortSubSort,
                0,
                TokenRange::for_tokens(declaration.sub_sort())
                    .map_err(krs_syntax::SyntaxError::into_syn_error)?,
            ),
        ]
    } else {
        declaration
            .provenance()
            .map_err(krs_syntax::SyntaxError::into_syn_error)?
    };
    let provenance = host_provenance(env, &facade, fallback, &anchors);
    let (super_key, sub_key, factory, grammar_name) = if let Some(reference) = &reference {
        let identity = ReadableMembershipIdentity::new(reference.sort(), declaration.sub_sort());
        (
            format_ident!("__krs_subsort_super_{}", identity.rust_key),
            format_ident!("__krs_subsort_sub_{}", identity.rust_key),
            format_ident!("__krs_subsort_descriptor_{}", identity.rust_key),
            identity.item_name,
        )
    } else {
        let synthetic = Ident::new("subsort", Span::call_site());
        let nonce = expansion_nonce(env, "subsort", &synthetic, fallback);
        (
            format_ident!("__krs_subsort_super_{nonce:016x}"),
            format_ident!("__krs_subsort_sub_{nonce:016x}"),
            format_ident!("__krs_subsort_descriptor_{nonce:016x}"),
            format!("__krs_grammar_subsort_{nonce:016x}"),
        )
    };
    let semantic_super = reference
        .as_ref()
        .map_or_else(|| declaration.super_sort(), |attribute| attribute.sort());
    let super_path = call_site_path(semantic_super)?;
    let sub_path = call_site_path(declaration.sub_sort())?;
    let super_spelling = spelling(semantic_super);
    let sub_spelling = spelling(declaration.sub_sort());
    let item = declaration.item();
    let cfg = call_site_cfg_attributes(&item.attrs)?;
    let mut slots = WireSlots::new(&facade);
    let supersort = wire_sort_reference(
        &mut slots,
        &facade,
        ProvenanceRole::SubsortSuperSort,
        0,
        &super_key,
        &super_spelling,
    );
    let subsort = wire_sort_reference(
        &mut slots,
        &facade,
        ProvenanceRole::SubsortSubSort,
        0,
        &sub_key,
        &sub_spelling,
    );
    let wire = WirePayload::Grammar(Box::new(WireGrammarDescriptor::Subsort {
        key: wire_key(subsort_declaration_role, 0),
        subsort,
        supersort,
    }));
    let wire = serde_json::to_string(&wire).expect("KRS wire values serialize");
    let slot_tokens = slots.tokens();
    let super_type = if reference.is_some() {
        quote!(#super_path)
    } else {
        quote!(dyn #super_path)
    };
    let framework_request = reference
        .as_ref()
        .is_some_and(|attribute| is_framework_sort_path(attribute.sort()))
        .then(|| quote!(#facade::__request_framework_sorts!();));

    Ok(quote! {
        #item

        #framework_request

        #(#cfg)*
        #[doc(hidden)]
        fn #super_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#super_type>()
        }

        #(#cfg)*
        #[doc(hidden)]
        fn #sub_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#sub_path>()
        }

        #(#cfg)*
        #[doc(hidden)]
        fn #factory() -> #facade::HostDescriptor {
            #facade::HostDescriptor {
                protocol_version: #facade::SchemaVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"),
                    env!("CARGO_MANIFEST_DIR"), module_path!(), #grammar_name,
                    #facade::ItemKind::Grammar, "subsort",
                ).expect("Cargo and Rust macro context form a valid subsort identity"),
                declared_type: ::core::option::Option::None,
                payload: #facade::__krs_host_payload(#wire, #slot_tokens),
                cfg: ::core::default::Default::default(),
                provenance: #provenance,
            }
        }

        #(#cfg)*
        #facade::__register_host_descriptor!(#factory);
    })
}

#[allow(clippy::too_many_arguments)]
fn expand_bracket_grammar(
    env: &dyn MacroEnvironment,
    facade: &Path,
    semantic_sort_name: &str,
    semantic_sort_range: TokenRange,
    bracket: &krs_syntax::BracketAttribute,
    nonce: u64,
    index: usize,
    cfg: &[Attribute],
) -> syn::Result<TokenStream> {
    let mut anchors = bracket
        .provenance()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    anchors.push(ProvenanceAnchor::new(
        ProvenanceRole::SortDeclaration,
        0,
        semantic_sort_range,
    ));
    let sort_key = format_ident!("__krs_sort_type_{nonce:016x}");
    expand_bracket_grammar_parts(
        env,
        facade,
        semantic_sort_name,
        &sort_key,
        bracket,
        &anchors,
        nonce,
        index,
        cfg,
    )
}

#[allow(clippy::too_many_arguments)]
fn expand_bracket_grammar_parts(
    env: &dyn MacroEnvironment,
    facade: &Path,
    sort_name: &str,
    sort_key: &Ident,
    bracket: &krs_syntax::BracketAttribute,
    anchors: &[ProvenanceAnchor],
    nonce: u64,
    index: usize,
    cfg: &[Attribute],
) -> syn::Result<TokenStream> {
    let bracket_declaration_role = ProvenanceRole::BracketDeclaration;
    let fallback = anchors
        .first()
        .map(ProvenanceAnchor::range)
        .ok_or_else(|| syn::Error::new(bracket.template().literal().span(), "empty bracket"))?;
    let provenance = host_provenance(env, facade, fallback, anchors);
    let factory = format_ident!("__krs_bracket_descriptor_{nonce:016x}_{index}");
    let grammar_name = format!("__krs_grammar_bracket_{sort_name}_{index}");
    let mut slots = WireSlots::new(facade);
    let sort_reference = wire_sort_reference(
        &mut slots,
        facade,
        ProvenanceRole::SortDeclaration,
        0,
        sort_key,
        sort_name,
    );
    let mut items = Vec::new();
    let mut value_ordinal = 0_u32;
    for (item_index, item) in bracket.template().items().iter().enumerate() {
        let ordinal = u32::try_from(item_index).map_err(|_| {
            syn::Error::new(
                bracket.template().literal().span(),
                "too many bracket items",
            )
        })?;
        let key = wire_key(ProvenanceRole::BracketSyntaxItem, ordinal);
        match item {
            SyntaxTemplateItem::Terminal(text) => {
                items.push(krs_ir::wire::WireProductionItem::Terminal {
                    key,
                    text: text.to_owned(),
                });
            }
            SyntaxTemplateItem::Field(_) => {
                let field_key = wire_key(ProvenanceRole::BracketValueReference, value_ordinal);
                value_ordinal = value_ordinal.checked_add(1).ok_or_else(|| {
                    syn::Error::new(
                        bracket.template().literal().span(),
                        "too many bracket values",
                    )
                })?;
                items.push(krs_ir::wire::WireProductionItem::NonTerminal {
                    key,
                    field_key,
                    declaration_key: None,
                    field: krs_ir::ProductionFieldId::new("value")
                        .expect("the bracket value field is valid"),
                    sort: Box::new(sort_reference.clone()),
                });
            }
        }
    }
    let disambiguator = format!("bracket:{index}");
    let wire = WirePayload::Grammar(Box::new(WireGrammarDescriptor::Production(
        krs_ir::wire::WireProduction {
            key: wire_key(bracket_declaration_role, 0),
            template_key: None,
            owner: krs_ir::wire::WireProductionOwner::BracketSort {
                sort: sort_reference.clone(),
            },
            result_sort: sort_reference,
            items,
            attributes: vec![krs_ir::wire::WireProductionAttribute::Bracket {
                key: wire_key(bracket_declaration_role, 0),
            }],
        },
    )));
    let wire = serde_json::to_string(&wire).expect("KRS wire values serialize");
    let slot_tokens = slots.tokens();
    Ok(quote! {
        #(#cfg)*
        #[doc(hidden)]
        fn #factory() -> #facade::HostDescriptor {
            #facade::HostDescriptor {
                protocol_version: #facade::SchemaVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"),
                    env!("CARGO_MANIFEST_DIR"), module_path!(), #grammar_name,
                    #facade::ItemKind::Grammar, #disambiguator,
                ).expect("Cargo and Rust macro context form a valid bracket identity"),
                declared_type: ::core::option::Option::None,
                payload: #facade::__krs_host_payload(#wire, #slot_tokens),
                cfg: ::core::default::Default::default(),
                provenance: #provenance,
            }
        }

        #(#cfg)*
        #facade::__register_host_descriptor!(#factory);
    })
}

#[cfg(test)]
mod tests {
    use super::ReadableMembershipIdentity;

    fn membership_identity_bytes(source: &str) -> Vec<Vec<u8>> {
        let declaration = krs_syntax::parse_sorts_declaration_source(source).unwrap();
        let mut identities = Vec::new();
        for entry in declaration.entries() {
            let krs_syntax::SortsEntry::Membership(membership) = entry else {
                continue;
            };
            for member in membership.members() {
                identities.push(
                    ReadableMembershipIdentity::new(membership.supersort(), member)
                        .item_name
                        .into_bytes(),
                );
            }
        }
        identities.sort();
        identities
    }

    #[test]
    fn readable_membership_identity_ignores_layout_and_unrelated_order() {
        let baseline = membership_identity_bytes(
            r"
                Target;
                Alpha;
                impl Target for domain::First, domain::Second;
                Tail;
                impl external::Target for ::rooted::Member;
            ",
        );
        let reformatted_and_reordered = membership_identity_bytes(
            r"
                Tail ;

                impl external::Target
                    for ::rooted::Member;
                Alpha;
                Target;
                impl Target for domain::Second,
                    domain::First;
            ",
        );

        assert_eq!(baseline, reformatted_and_reordered);
        let mut expected = vec![
            b"__krs_grammar_subsort(member=absolute:rooted.Member;supersort=relative:external.Target)"
                .to_vec(),
            b"__krs_grammar_subsort(member=relative:domain.First;supersort=relative:Target)"
                .to_vec(),
            b"__krs_grammar_subsort(member=relative:domain.Second;supersort=relative:Target)"
                .to_vec(),
        ];
        expected.sort();
        assert_eq!(baseline, expected);
    }

    #[test]
    fn readable_membership_identity_retains_full_paths_without_helper_collisions() {
        let first_member: syn::Path = syn::parse_str("alpha::Member").unwrap();
        let first_sort: syn::Path = syn::parse_str("alpha::Target").unwrap();
        let second_member: syn::Path = syn::parse_str("beta::Member").unwrap();
        let second_sort: syn::Path = syn::parse_str("beta::Target").unwrap();
        let first = ReadableMembershipIdentity::new(&first_sort, &first_member);
        let second = ReadableMembershipIdentity::new(&second_sort, &second_member);
        let crossed = ReadableMembershipIdentity::new(&first_sort, &second_member);

        assert_eq!(
            first.item_name,
            "__krs_grammar_subsort(member=relative:alpha.Member;supersort=relative:alpha.Target)"
        );
        assert_ne!(first.item_name, second.item_name);
        assert_ne!(first.item_name, crossed.item_name);
        assert_ne!(first.rust_key, second.rust_key);
        assert_ne!(first.rust_key, crossed.rust_key);
        assert!(
            [first.rust_key, second.rust_key, crossed.rust_key]
                .iter()
                .all(|key| key.bytes().all(|byte| byte.is_ascii_hexdigit()))
        );
    }
}
