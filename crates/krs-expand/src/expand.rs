use std::collections::{BTreeMap, BTreeSet};
use std::hash::{Hash, Hasher};

use krs_syntax::surface::{AttributeMacro, helper_entry, last_segment_entry};
use krs_syntax::{
    ClaimModality as SyntaxClaimModality, ConfigurationCellContent, FixedCellInitializer,
    GroupAssociativity as SyntaxGroupAssociativity, InitializerCellContent, KSequence,
    KSequenceNotation, MapBody, MapExpression, ProvenanceAnchor, ProvenanceRole, RuleSide,
    StateMacroRemainder, StateRuleBindingKind, StateRuleReferenceKind, StateTerm,
    StrictnessAttribute, StrictnessKind as SyntaxStrictnessKind, StructuredFormatFragment,
    SyntaxTemplateItem, TermArguments, TermExpression, TermLiteral, TermTree, TokenRange,
    parse_alias_attribute, parse_associativity_declaration, parse_bracket_attribute,
    parse_cells_expression, parse_claim_attribute, parse_configuration_attribute,
    parse_configuration_declaration, parse_constructor_attribute, parse_constructor_declaration,
    parse_constructors_attribute, parse_context_alias_attribute, parse_equation_attribute,
    parse_function_attribute, parse_init_attribute, parse_initializer_function,
    parse_k_sequence_expression, parse_map_expression, parse_precedence_declaration,
    parse_priority_attribute, parse_rule_attribute, parse_rule_block, parse_rule_item,
    parse_seqstrict_attribute, parse_simplification_attribute, parse_sort_attribute,
    parse_sort_declaration, parse_sorts_declaration, parse_state_claim_item,
    parse_state_context_alias_item, parse_state_rule_item, parse_strict_attribute,
    parse_subsort_attribute, parse_subsort_declaration, parse_symbol_attribute,
    parse_term_expression, parse_token_attribute, parse_token_declaration,
};
use proc_macro2::{Span, TokenStream, TokenTree};
use quote::{ToTokens, format_ident, quote};
use syn::ext::IdentExt;
use syn::parse::Parser;
use syn::spanned::Spanned;
use syn::{
    Attribute, FnArg, Ident, Item, ItemEnum, ItemFn, ItemStruct, ItemTrait, Meta, Pat, Path,
    parse_quote,
};

use crate::environment::{MacroEnvironment, SourcePosition};
use crate::provenance::host_provenance;

pub(crate) fn symbol(attributes: TokenStream, item: TokenStream) -> syn::Result<TokenStream> {
    let symbol =
        parse_symbol_attribute(attributes).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let mut item: Item = syn::parse2(item)?;
    let (attrs, span) = match &mut item {
        Item::Trait(item) => (&mut item.attrs, item.ident.span()),
        Item::Struct(item) => (&mut item.attrs, item.ident.span()),
        _ => {
            return Err(syn::Error::new(
                item.span(),
                "#[k::symbol] currently supports sort traits and constructor structs",
            ));
        }
    };
    if attrs
        .iter()
        .any(|attribute| last_segment_entry(attribute.path()) == Some(AttributeMacro::Symbol))
    {
        return Err(syn::Error::new(span, "duplicate #[k::symbol] attribute"));
    }
    let targets = attrs
        .iter()
        .enumerate()
        .filter(|(_, attribute)| {
            matches!(
                last_segment_entry(attribute.path()),
                Some(AttributeMacro::Sort | AttributeMacro::Constructor)
            )
        })
        .map(|(index, _)| index)
        .collect::<Vec<_>>();
    let [target] = targets.as_slice() else {
        return Err(syn::Error::new(
            span,
            "#[k::symbol] must immediately precede exactly one #[k::sort] or #[k::constructor] declaration",
        ));
    };
    let literal = symbol.literal();
    attrs.insert(
        *target + 1,
        parse_quote!(#[__krs_explicit_symbol(#literal)]),
    );
    Ok(item.into_token_stream())
}

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
    let provenance = host_provenance(env, &facade, fallback, &anchors)?;
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
                protocol_version: #facade::ProtocolVersion::CURRENT,
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
    let provenance = host_provenance(env, facade, fallback, &anchors)?;
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
                protocol_version: #facade::ProtocolVersion::CURRENT,
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
    let provenance = host_provenance(env, facade, fallback, &anchors)?;
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
    let supersort = host_sort_reference(
        facade,
        ProvenanceRole::SubsortSuperSort,
        0,
        &super_key,
        &super_spelling,
    );
    let subsort = host_sort_reference(
        facade,
        ProvenanceRole::SubsortSubSort,
        0,
        &sub_key,
        &sub_spelling,
    );

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
                protocol_version: #facade::ProtocolVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"),
                    env!("CARGO_MANIFEST_DIR"), module_path!(), #grammar_name,
                    #facade::ItemKind::Grammar, "subsort",
                ).expect("Cargo and Rust macro context form a valid subsort identity"),
                declared_type: ::core::option::Option::None,
                payload: #facade::HostDescriptorPayload::Grammar(::std::boxed::Box::new(
                    #facade::HostGrammarDescriptor::Subsort {
                        key: #facade::ProvenanceKey::new(#subsort_declaration_role, 0)
                            .expect("KRS parser roles are nonempty"),
                        subsort: #subsort,
                        supersort: #supersort,
                    },
                )),
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

#[allow(clippy::too_many_lines)]
pub(crate) fn constructor(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let attribute =
        parse_constructor_attribute(attributes).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    constructor_like(env, attribute, item, None, None)
}

pub(crate) fn function(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let function =
        parse_function_attribute(attributes).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let totality_anchor = function
        .provenance()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?
        .into_iter()
        .find(|anchor| {
            matches!(
                anchor.role(),
                ProvenanceRole::FunctionTotal | ProvenanceRole::FunctionPartial
            )
        })
        .expect("a parsed function retains its totality marker");
    let hook = function
        .hook()
        .map(|path| -> syn::Result<(ProvenanceAnchor, TokenStream)> {
            let segments = path
                .segments
                .iter()
                .map(|segment| segment.ident.to_string())
                .collect::<Vec<_>>();
            let operation = match segments.as_slice() {
                [module, name] if module == "krypto" && name == "keccak256_raw" => {
                    let facade = env.facade_path()?;
                    quote!(#facade::HookOperation::KryptoKeccak256Raw)
                }
                [module, name] if module == "krypto" && name == "sha256_raw" => {
                    let facade = env.facade_path()?;
                    quote!(#facade::HookOperation::KryptoSha256Raw)
                }
                [module, name] if module == "krypto" && name == "ripemd160_raw" => {
                    let facade = env.facade_path()?;
                    quote!(#facade::HookOperation::KryptoRipemd160Raw)
                }
                [module, name] if module == "krypto" && name == "ecdsa_recover" => {
                    let facade = env.facade_path()?;
                    quote!(#facade::HookOperation::KryptoEcdsaRecover)
                }
                [module, name] if module == "krypto" && name == "bn128_valid" => {
                    let facade = env.facade_path()?;
                    quote!(#facade::HookOperation::KryptoBn128Valid)
                }
                [module, name] if module == "krypto" && name == "bn128_add" => {
                    let facade = env.facade_path()?;
                    quote!(#facade::HookOperation::KryptoBn128Add)
                }
                [module, name] if module == "krypto" && name == "bn128_mul" => {
                    let facade = env.facade_path()?;
                    quote!(#facade::HookOperation::KryptoBn128Mul)
                }
                [module, name] if module == "krypto" && name == "bn128_g2_valid" => {
                    let facade = env.facade_path()?;
                    quote!(#facade::HookOperation::KryptoBn128G2Valid)
                }
                [module, name] if module == "krypto" && name == "bn128_ate" => {
                    let facade = env.facade_path()?;
                    quote!(#facade::HookOperation::KryptoBn128Ate)
                }
                _ => {
                    return Err(syn::Error::new(
                        path.span(),
                        "unknown KRS hook; expected `krypto::keccak256_raw`, `krypto::sha256_raw`, `krypto::ripemd160_raw`, `krypto::ecdsa_recover`, `krypto::bn128_valid`, `krypto::bn128_add`, `krypto::bn128_mul`, `krypto::bn128_g2_valid`, or `krypto::bn128_ate`",
                    ));
                }
            };
            Ok((
                ProvenanceAnchor::new(
                    ProvenanceRole::FunctionHook,
                    0,
                    TokenRange::for_tokens(path)
                        .map_err(krs_syntax::SyntaxError::into_syn_error)?,
                ),
                operation,
            ))
        })
        .transpose()?;
    constructor_like(
        env,
        function.production().clone(),
        item,
        Some((totality_anchor, function.is_total())),
        hook,
    )
}

#[allow(clippy::needless_pass_by_value, clippy::too_many_lines)]
fn constructor_like(
    env: &dyn MacroEnvironment,
    attribute: krs_syntax::ConstructorAttribute,
    item: TokenStream,
    totality: Option<(ProvenanceAnchor, bool)>,
    hook: Option<(ProvenanceAnchor, TokenStream)>,
) -> syn::Result<TokenStream> {
    let functional = totality.is_some();
    let total = totality.as_ref().is_some_and(|(_, total)| *total);
    let mut raw_item: ItemStruct = syn::parse2(item)?;
    reject_unexpanded_symbol(&raw_item.attrs)?;
    let explicit_symbol = take_explicit_symbol_helper(&mut raw_item.attrs)?;
    let strictness = take_strictness_helpers(&mut raw_item.attrs)?;
    let alias = take_alias_helper(&mut raw_item.attrs)?;
    if functional && alias.is_some() {
        return Err(syn::Error::new(
            raw_item.ident.span(),
            "a function production cannot also be a static alias",
        ));
    }
    let declaration = parse_constructor_declaration(raw_item.to_token_stream())
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    attribute
        .validate_declaration(&declaration)
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    if let Some(strictness) = &strictness {
        strictness
            .validate_fields(
                declaration
                    .fields()
                    .iter()
                    .map(krs_syntax::ConstructorField::name),
            )
            .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    }
    let facade = env.facade_path()?;
    let mut declaration_anchors = attribute
        .provenance()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    declaration_anchors.extend(
        declaration
            .provenance()
            .map_err(krs_syntax::SyntaxError::into_syn_error)?,
    );
    if let Some(symbol) = &explicit_symbol {
        declaration_anchors.extend(
            symbol
                .provenance()
                .map_err(krs_syntax::SyntaxError::into_syn_error)?,
        );
    }
    let fallback = krs_syntax::TokenRange::for_tokens(declaration.item())
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let provenance = host_provenance(env, &facade, fallback, &declaration_anchors)?;
    let mut grammar_anchors = attribute
        .full_provenance()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    if !attribute.avoid
        && grammar_anchors
            .iter()
            .any(|anchor| anchor.role() == ProvenanceRole::ConstructorAvoid)
    {
        return Err(syn::Error::new(
            declaration.name().span(),
            "`avoid = false` is not metadata; omit the argument instead",
        ));
    }
    grammar_anchors.extend(
        declaration
            .full_provenance()
            .map_err(krs_syntax::SyntaxError::into_syn_error)?,
    );
    if let Some(symbol) = &explicit_symbol {
        grammar_anchors.extend(
            symbol
                .provenance()
                .map_err(krs_syntax::SyntaxError::into_syn_error)?,
        );
    }
    if let Some(alias) = &alias {
        grammar_anchors.push(alias.clone());
    }
    if functional {
        if total {
            grammar_anchors.push(ProvenanceAnchor::new(
                ProvenanceRole::FunctionDeclaration,
                0,
                TokenRange::for_tokens(declaration.name())
                    .map_err(krs_syntax::SyntaxError::into_syn_error)?,
            ));
        }
        grammar_anchors.push(
            totality
                .as_ref()
                .expect("functional constructors retain totality provenance")
                .0
                .clone(),
        );
    }
    if let Some((anchor, _)) = &hook {
        grammar_anchors.push(anchor.clone());
    }
    if let Some(strictness) = &strictness {
        grammar_anchors.extend(
            strictness
                .provenance()
                .map_err(krs_syntax::SyntaxError::into_syn_error)?,
        );
    }
    let grammar_provenance = host_provenance(env, &facade, fallback, &grammar_anchors)?;
    let nonce = expansion_nonce(env, "constructor", declaration.name(), fallback);
    let factory = format_ident!(
        "__krs_constructor_descriptor_{nonce:016x}",
        span = Span::call_site()
    );
    let declared_key = format_ident!(
        "__krs_constructor_type_{nonce:016x}",
        span = Span::call_site()
    );
    let sort_key = format_ident!(
        "__krs_constructor_sort_{nonce:016x}",
        span = Span::call_site()
    );
    let item = declaration.item();
    let cfg = call_site_cfg_attributes(&item.attrs)?;
    let name = declaration.name().to_string();
    let declared = call_site_ident(declaration.name())?;
    let authored_sort = &attribute.sort;
    let generated_sort = call_site_path(&attribute.sort)?;
    let authored_sort_type = if functional {
        quote!(#authored_sort)
    } else {
        quote!(dyn #authored_sort)
    };
    let generated_sort_type = if functional {
        quote!(#generated_sort)
    } else {
        quote!(dyn #generated_sort)
    };
    let sort_spelling = spelling(&attribute.sort);
    let sort_reference = host_sort_reference(
        &facade,
        ProvenanceRole::ConstructorSort,
        0,
        &sort_key,
        &sort_spelling,
    );
    let syntax = option_owned_string(attribute.syntax.as_ref().map(syn::LitStr::value));

    let mut field_key_functions = Vec::new();
    let mut fields = Vec::new();
    for (index, field) in declaration.fields().iter().enumerate() {
        let key = format_ident!(
            "__krs_constructor_field_{nonce:016x}_{index}",
            span = Span::call_site()
        );
        let generated = call_site_path(field.term_sort().sort())?;
        let generated = sort_type_tokens(&generated, field.term_sort().is_dynamic());
        let spelling = field.term_sort().sort_spelling();
        let field_name = field.name().to_string();
        field_key_functions.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #key() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#generated>()
            }
        });
        let reference = type_reference(&facade, &key, &spelling);
        fields.push(quote! {
            #facade::HostConstructorFieldDescriptor {
                name: #field_name.to_owned(),
                sort: #reference,
            }
        });
    }

    let owner_target = quote!(#facade::HostApplicationTarget::Nominal(#facade::HostTypeReference {
        key: #facade::HostTypeKey(#declared_key),
        authored_path: #name.to_owned(),
    }));
    let rule_application = quote! {
        #(#cfg)*
        impl<const __KRS_SELECTOR: u64> #facade::__KrsRuleApplication<__KRS_SELECTOR>
            for #declared
        {
            fn __krs_rule_application(authored_path: &str) -> #facade::HostApplicationTarget {
                #facade::HostApplicationTarget::Nominal(#facade::HostTypeReference {
                    key: #facade::HostTypeKey(#declared_key),
                    authored_path: authored_path.to_owned(),
                })
            }
        }
    };
    let grammar = constructor_grammar(
        &facade,
        &attribute,
        &declaration,
        strictness.as_ref(),
        &declared_key,
        &sort_key,
        nonce,
        &cfg,
        &grammar_provenance,
        &owner_target,
        "",
        functional,
        total,
        hook.as_ref().map(|(_, operation)| operation),
        alias.is_some(),
    )?;

    Ok(quote! {
        #item

        #(#cfg)*
        const _: ::core::marker::PhantomData<#authored_sort_type> =
            ::core::marker::PhantomData;

        #(#cfg)*
        #[doc(hidden)]
        fn #declared_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#declared>()
        }

        #(#cfg)*
        #[doc(hidden)]
        fn #sort_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#generated_sort_type>()
        }

        #(#field_key_functions)*

        #rule_application

        #(#cfg)*
        #[doc(hidden)]
        fn #factory() -> #facade::HostDescriptor {
            #facade::HostDescriptor {
                protocol_version: #facade::ProtocolVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"),
                    env!("CARGO_PKG_VERSION"),
                    env!("CARGO_MANIFEST_DIR"),
                    module_path!(),
                    #name,
                    #facade::ItemKind::Constructor,
                    "",
                )
                .expect("Cargo and Rust macro context form a valid host identity"),
                declared_type: ::core::option::Option::Some(
                    #facade::HostDeclarationIdentity::Nominal(
                        #facade::HostTypeKey(#declared_key),
                    ),
                ),
                payload: #facade::HostDescriptorPayload::Constructor(
                    #facade::HostConstructorDescriptor {
                        sort: #sort_reference,
                        syntax: #syntax,
                        fields: ::std::vec![#(#fields),*],
                    },
                ),
                cfg: ::core::default::Default::default(),
                provenance: #provenance,
            }
        }

        #(#cfg)*
        #facade::__register_host_descriptor!(#factory);

        #grammar
    })
}

#[allow(clippy::too_many_lines)]
pub(crate) fn configuration(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let configuration_declaration_role = ProvenanceRole::ConfigurationDeclaration;
    let attribute = parse_configuration_attribute(attributes)
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let declaration =
        parse_configuration_declaration(item).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let facade = env.facade_path()?;
    let mut anchors = declaration
        .provenance()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    anchors.extend(
        attribute
            .provenance()
            .map_err(krs_syntax::SyntaxError::into_syn_error)?,
    );
    let fallback = krs_syntax::TokenRange::for_tokens(declaration.item())
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let provenance = host_provenance(env, &facade, fallback, &anchors)?;
    let nonce = expansion_nonce(env, "configuration", declaration.name(), fallback);
    let declared_key = format_ident!(
        "__krs_configuration_type_{nonce:016x}",
        span = Span::call_site()
    );
    let factory = format_ident!(
        "__krs_configuration_descriptor_{nonce:016x}",
        span = Span::call_site()
    );
    let mut item = declaration.item().clone();
    inject_inferred_cell_wrappers(&mut item, &declaration, &facade)?;
    strip_cell_helpers(&mut item);
    let cfg = call_site_cfg_attributes(&item.attrs)?;
    let name = declaration.name().to_string();
    let declared = call_site_ident(declaration.name())?;
    let root = configuration_root(&facade, &attribute);
    let (field_helpers, fields) =
        configuration_fields(&facade, &declaration, &declared, &declared_key)?;

    Ok(quote! {
        #item

        #(#cfg)*
        impl #declared {
            #[doc(hidden)]
            pub fn __krs_configuration_type_key() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<Self>()
            }
            #(#field_helpers)*
        }

        #(#cfg)*
        #[doc(hidden)]
        fn #declared_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#declared>()
        }

        #(#cfg)*
        #[doc(hidden)]
        fn #factory() -> #facade::HostDescriptor {
            let (initializer, initializer_provenance) = #declared::__krs_initializer_payload();
            #facade::HostDescriptor {
                protocol_version: #facade::ProtocolVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"),
                    env!("CARGO_PKG_VERSION"),
                    env!("CARGO_MANIFEST_DIR"),
                    module_path!(),
                    #name,
                    #facade::ItemKind::Configuration,
                    "",
                )
                .expect("Cargo and Rust macro context form a valid host identity"),
                declared_type: ::core::option::Option::Some(
                    #facade::HostDeclarationIdentity::Nominal(
                        #facade::HostTypeKey(#declared_key),
                    ),
                ),
                payload: #facade::HostDescriptorPayload::FixedConfiguration(
                    ::std::boxed::Box::new(#facade::HostFixedConfiguration {
                        root: #root,
                        declaration: #facade::HostConfigurationDeclaration {
                            key: #facade::ProvenanceKey::new(#configuration_declaration_role, 0)
                                .expect("KRS parser roles are nonempty"),
                            fields: ::std::vec![#(#fields),*],
                        },
                        initializer,
                    }),
                ),
                cfg: ::core::default::Default::default(),
                provenance: #provenance
                    .merge(initializer_provenance)
                    .expect("configuration and initializer provenance keys are disjoint"),
            }
        }

        #(#cfg)*
        #facade::__register_host_descriptor!(#factory);
    })
}

pub(crate) fn cell(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let configuration_declaration_role = ProvenanceRole::ConfigurationDeclaration;
    krs_syntax::parse_cell_attribute(attributes)
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let declaration =
        parse_configuration_declaration(item).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let facade = env.facade_path()?;
    let anchors = declaration
        .provenance()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let fallback = TokenRange::for_tokens(declaration.item())
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let provenance = host_provenance(env, &facade, fallback, &anchors)?;
    let nonce = expansion_nonce(env, "cell", declaration.name(), fallback);
    let declared_key = format_ident!("__krs_cell_type_{nonce:016x}");
    let factory = format_ident!("__krs_cell_descriptor_{nonce:016x}");
    let mut item = declaration.item().clone();
    inject_inferred_cell_wrappers(&mut item, &declaration, &facade)?;
    strip_cell_helpers(&mut item);
    let cfg = call_site_cfg_attributes(&item.attrs)?;
    let declared = call_site_ident(declaration.name())?;
    let name = declaration.name().to_string();
    let (field_helpers, fields) =
        configuration_fields(&facade, &declaration, &declared, &declared_key)?;

    Ok(quote! {
        #item

        #(#cfg)*
        impl #declared {
            #[doc(hidden)]
            pub fn __krs_configuration_type_key() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<Self>()
            }
            #(#field_helpers)*
        }

        #(#cfg)*
        #[doc(hidden)]
        fn #declared_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#declared>()
        }

        #(#cfg)*
        #[doc(hidden)]
        fn #factory() -> #facade::HostDescriptor {
            #facade::HostDescriptor {
                protocol_version: #facade::ProtocolVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"),
                    env!("CARGO_MANIFEST_DIR"), module_path!(), #name,
                    #facade::ItemKind::Cell, "",
                ).expect("Cargo and Rust macro context form a valid host identity"),
                declared_type: ::core::option::Option::Some(
                    #facade::HostDeclarationIdentity::Nominal(#facade::HostTypeKey(#declared_key)),
                ),
                payload: #facade::HostDescriptorPayload::Cell(::std::boxed::Box::new(
                    #facade::HostCellDeclaration {
                        key: #facade::ProvenanceKey::new(#configuration_declaration_role, 0)
                            .expect("KRS parser roles are nonempty"),
                        fields: ::std::vec![#(#fields),*],
                    }
                )),
                cfg: ::core::default::Default::default(),
                provenance: #provenance,
            }
        }

        #(#cfg)*
        #facade::__register_host_descriptor!(#factory);
    })
}

fn strip_cell_helpers(item: &mut ItemStruct) {
    if let syn::Fields::Named(fields) = &mut item.fields {
        for field in &mut fields.named {
            field.attrs.retain(|attribute| {
                attribute
                    .path()
                    .segments
                    .last()
                    .is_none_or(|segment| segment.ident != "cell")
            });
        }
    }
}

fn inject_inferred_cell_wrappers(
    item: &mut ItemStruct,
    declaration: &krs_syntax::ConfigurationDeclaration,
    facade: &Path,
) -> syn::Result<()> {
    let syn::Fields::Named(fields) = &mut item.fields else {
        return Err(syn::Error::new(
            item.fields.span(),
            "a fixed configuration must be a named-field struct",
        ));
    };
    for field in &mut fields.named {
        let Some(name) = &field.ident else {
            continue;
        };
        let Some(cell) = declaration.cells().iter().find(|cell| cell.name() == name) else {
            return Err(syn::Error::new(
                name.span(),
                "configuration field disappeared during wrapper injection",
            ));
        };
        if !cell.has_inferred_wrapper() {
            continue;
        }
        let content = field.ty.clone();
        field.ty = if cell.is_computation_cell() {
            parse_quote!(#facade::configuration::KCell<#content>)
        } else {
            parse_quote!(#facade::configuration::Cell<#content>)
        };
    }
    Ok(())
}

fn cell_marker_function(field: &Ident) -> Ident {
    format_ident!("__krs_cell_field_type_id_{}", field)
}

fn configuration_root(
    facade: &Path,
    attribute: &krs_syntax::ConfigurationAttribute,
) -> TokenStream {
    let configuration_root_role = ProvenanceRole::ConfigurationRoot;
    if let Some(root) = attribute.optional_root() {
        let value = root.value();
        quote! {
            #facade::DescriptorConfigurationRoot::Named {
                key: #facade::ProvenanceKey::new(#configuration_root_role, 0)
                    .expect("KRS parser roles are nonempty"),
                name: #value.to_owned(),
            }
        }
    } else {
        quote!(#facade::DescriptorConfigurationRoot::GeneratedTop)
    }
}

#[allow(clippy::too_many_lines)]
fn configuration_fields(
    facade: &Path,
    declaration: &krs_syntax::ConfigurationDeclaration,
    owner: &Ident,
    owner_key: &Ident,
) -> syn::Result<(Vec<TokenStream>, Vec<TokenStream>)> {
    let configuration_cell_name_role = ProvenanceRole::ConfigurationCellName;
    let configuration_cell_color_role = ProvenanceRole::ConfigurationCellColor;
    let configuration_cell_multiplicity_role = ProvenanceRole::ConfigurationCellMultiplicity;
    let configuration_cell_type_role = ProvenanceRole::ConfigurationCellType;
    let configuration_cell_content_argument_role = ProvenanceRole::ConfigurationCellContentArgument;
    let configuration_cell_wrapper_role = ProvenanceRole::ConfigurationCellWrapper;
    let configuration_cell_content_role = ProvenanceRole::ConfigurationCellContent;
    let configuration_field_role = ProvenanceRole::ConfigurationField;
    let mut helpers = Vec::new();
    let mut fields = Vec::new();
    let mut argument_ordinal = 0_u32;
    for (index, field) in declaration.cells().iter().enumerate() {
        let ordinal = u32::try_from(index)
            .map_err(|_| syn::Error::new(field.name().span(), "too many fixed cells"))?;
        let marker = cell_marker_function(field.name());
        helpers.push(quote! {
            #[doc(hidden)]
            pub fn #marker() -> ::core::any::TypeId {
                struct __KrsCellFieldMarker;
                ::core::any::TypeId::of::<__KrsCellFieldMarker>()
            }
        });
        let rust_field = field.name().to_string();
        let emitted_name = field.attribute().name().map_or_else(
            || quote!(::core::option::Option::None),
            |name| {
                let value = name.value();
                quote! {
                    ::core::option::Option::Some(#facade::DescriptorCellName {
                        key: #facade::ProvenanceKey::new(#configuration_cell_name_role, #ordinal)
                            .expect("KRS parser roles are nonempty"),
                        value: #value.to_owned(),
                    })
                }
            },
        );
        let color = field.attribute().color().map_or_else(
            || quote!(::core::option::Option::None),
            |color| {
                let value = color.value();
                quote! {
                    ::core::option::Option::Some(#facade::DescriptorCellColor {
                        key: #facade::ProvenanceKey::new(#configuration_cell_color_role, #ordinal)
                            .expect("KRS parser roles are nonempty"),
                        value: #value.to_owned(),
                    })
                }
            },
        );
        let multiplicity = field.attribute().multiplicity().map_or_else(
            || quote!(::core::option::Option::None),
            |multiplicity| {
                let value = multiplicity.value();
                quote! {
                    ::core::option::Option::Some(#facade::DescriptorCellMultiplicity {
                        key: #facade::ProvenanceKey::new(
                            #configuration_cell_multiplicity_role, #ordinal,
                        ).expect("KRS parser roles are nonempty"),
                        value: #value.to_owned(),
                    })
                }
            },
        );
        let cell_type = field.attribute().cell_type().map_or_else(
            || quote!(::core::option::Option::None),
            |cell_type| {
                let value = cell_type.value();
                quote! {
                    ::core::option::Option::Some(#facade::DescriptorCellType {
                        key: #facade::ProvenanceKey::new(
                            #configuration_cell_type_role, #ordinal,
                        ).expect("KRS parser roles are nonempty"),
                        value: #value.to_owned(),
                    })
                }
            },
        );
        let content = match field.cell_content() {
            ConfigurationCellContent::Leaf {
                sort,
                arguments,
                computation,
                ..
            } => {
                let sort = call_site_path(sort)?;
                let authored = spelling(&sort);
                let sort_key = format_ident!("__krs_configuration_sort_{}_{}", owner_key, index);
                helpers.push(quote! {
                    #[doc(hidden)]
                    pub fn #sort_key() -> ::core::any::TypeId {
                        ::core::any::TypeId::of::<#sort>()
                    }
                });
                let wrapper = if *computation {
                    quote!(#facade::CellWrapper::KCell)
                } else {
                    quote!(#facade::CellWrapper::Cell)
                };
                let mut argument_references = Vec::new();
                for argument in arguments {
                    let generated = call_site_path(argument)?;
                    let authored = spelling(argument);
                    let key = format_ident!(
                        "__krs_configuration_sort_argument_{}_{}",
                        owner_key,
                        argument_ordinal
                    );
                    helpers.push(quote! {
                        #[doc(hidden)]
                        pub fn #key() -> ::core::any::TypeId {
                            ::core::any::TypeId::of::<#generated>()
                        }
                    });
                    let ordinal = argument_ordinal;
                    argument_ordinal = argument_ordinal.checked_add(1).ok_or_else(|| {
                        syn::Error::new(argument.span(), "too many configuration sort arguments")
                    })?;
                    argument_references.push(quote! {
                        #facade::HostSortReference {
                            key: #facade::ProvenanceKey::new(
                                #configuration_cell_content_argument_role, #ordinal,
                            ).expect("KRS parser roles are nonempty"),
                            target: #facade::HostTypeReference {
                                key: #facade::HostTypeKey(#owner::#key),
                                authored_path: #authored.to_owned(),
                            },
                        }
                    });
                }
                quote! {
                    #facade::ProtocolCellContent::Leaf {
                        wrapper_key: #facade::ProvenanceKey::new(
                            #configuration_cell_wrapper_role, #ordinal,
                        ).expect("KRS parser roles are nonempty"),
                        wrapper: #wrapper,
                        sort: #facade::HostSortReference {
                            key: #facade::ProvenanceKey::new(
                                #configuration_cell_content_role, #ordinal,
                            ).expect("KRS parser roles are nonempty"),
                            target: #facade::HostTypeReference {
                                key: #facade::HostTypeKey(#owner::#sort_key),
                                authored_path: #authored.to_owned(),
                            },
                        },
                        arguments: ::std::vec![#(#argument_references),*],
                    }
                }
            }
            ConfigurationCellContent::Nested { declaration } => {
                let generated = call_site_path(declaration)?;
                let authored = spelling(declaration);
                let nested_key =
                    format_ident!("__krs_configuration_nested_{}_{}", owner_key, index);
                helpers.push(quote! {
                    #[doc(hidden)]
                    pub fn #nested_key() -> ::core::any::TypeId {
                        ::core::any::TypeId::of::<#generated>()
                    }
                });
                quote! {
                    #facade::ProtocolCellContent::Nested {
                        declaration: #facade::HostCellDeclarationReference {
                            key: #facade::ProvenanceKey::new(
                                #configuration_cell_content_role, #ordinal,
                            ).expect("KRS parser roles are nonempty"),
                            declaration: #facade::HostTypeReference {
                                key: #facade::HostTypeKey(#owner::#nested_key),
                                authored_path: #authored.to_owned(),
                            },
                        },
                    }
                }
            }
        };
        fields.push(quote! {
            #facade::HostCellField {
                reference: #facade::HostCellReference {
                    key: #facade::ProvenanceKey::new(#configuration_field_role, #ordinal)
                        .expect("KRS parser roles are nonempty"),
                    cell: #facade::HostCellIdentity {
                        owner: #facade::HostTypeKey(#owner_key),
                        field: #facade::HostTypeKey(#owner::#marker),
                    },
                },
                rust_field: #rust_field.to_owned(),
                emitted_name: #emitted_name,
                color: #color,
                multiplicity: #multiplicity,
                cell_type: #cell_type,
                content: #content,
            }
        });
    }
    Ok((helpers, fields))
}

#[allow(clippy::too_many_lines)]
pub(crate) fn init(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let configuration_variable_main_role = ProvenanceRole::ConfigurationVariableMain;
    let configuration_variable_role = ProvenanceRole::ConfigurationVariable;
    let configuration_variable_name_role = ProvenanceRole::ConfigurationVariableName;
    let configuration_variable_type_role = ProvenanceRole::ConfigurationVariableType;
    let initializer_declaration_role = ProvenanceRole::InitializerDeclaration;
    let initializer_result_type_role = ProvenanceRole::InitializerResultType;
    let initializer_body_role = ProvenanceRole::InitializerBody;
    parse_init_attribute(attributes).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let initializer =
        parse_initializer_function(item).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let facade = env.facade_path()?;
    let anchors = initializer
        .provenance()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let fallback = krs_syntax::TokenRange::for_tokens(initializer.item())
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let provenance = host_provenance(env, &facade, fallback, &anchors)?;

    let bindings = initializer
        .variables()
        .iter()
        .map(|variable| variable.binding().clone())
        .collect::<Vec<_>>();
    let cfg = call_site_cfg_attributes(&initializer.item().attrs)?;
    let nonce = expansion_nonce(env, "initializer", &initializer.item().sig.ident, fallback);
    let mut builder = InitializerBuilder::new(&facade, nonce, &cfg, &bindings);
    let mut variables = Vec::new();
    for (index, variable) in initializer.variables().iter().enumerate() {
        let ordinal = u32::try_from(index)
            .map_err(|_| syn::Error::new(variable.binding().span(), "too many variables"))?;
        let sort_path = call_site_path(variable.sort())?;
        let sort_type = variable.optional_term_sort().map_or_else(
            || quote!(#sort_path),
            |term_sort| sort_type_tokens(&sort_path, term_sort.is_dynamic()),
        );
        let sort_key = format_ident!("__krs_initializer_variable_{nonce:016x}_{index}");
        builder.key_functions.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #sort_key() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#sort_type>()
            }
        });
        let binding = variable.binding().to_string();
        let external_name = variable.attribute().name().value();
        let main_key = if variable.attribute().is_main() {
            quote!(::core::option::Option::Some(
                #facade::ProvenanceKey::new(#configuration_variable_main_role, #ordinal)
                    .expect("KRS parser roles are nonempty")
            ))
        } else {
            quote!(::core::option::Option::None)
        };
        let authored = spelling(variable.sort());
        variables.push(quote! {
            #facade::HostConfigurationVariable {
                binding_key: #facade::ProvenanceKey::new(#configuration_variable_role, #ordinal)
                    .expect("KRS parser roles are nonempty"),
                binding: #binding.to_owned(),
                external_name_key: #facade::ProvenanceKey::new(
                    #configuration_variable_name_role, #ordinal,
                ).expect("KRS parser roles are nonempty"),
                external_name: #external_name.to_owned(),
                sort: #facade::HostSortReference {
                    key: #facade::ProvenanceKey::new(
                        #configuration_variable_type_role, #ordinal,
                    ).expect("KRS parser roles are nonempty"),
                    target: #facade::HostTypeReference {
                        key: #facade::HostTypeKey(Self::#sort_key),
                        authored_path: #authored.to_owned(),
                    },
                },
                main_key: #main_key,
            }
        });
    }
    let cells = builder.expand_cells(initializer.cells(), &quote!(Self))?;
    let island_import_checks = initializer_state_island_import_checks(initializer.cells());
    builder
        .key_functions
        .append(&mut builder.terms.key_functions);
    let key_functions = builder.key_functions;

    // The shared parser has validated every parameter attribute as the sole
    // `config_var` helper. The outer proc macro consumes it so stable rustc
    // sees an ordinary associated method signature.
    let mut method = initializer.item().clone();
    for input in &mut method.sig.inputs {
        if let FnArg::Typed(parameter) = input {
            parameter.attrs.clear();
        }
    }
    inject_inferred_initializer_wrappers(&mut method, &initializer, &facade)?;
    method.attrs.push(parse_quote!(
        #[allow(clippy::must_use_candidate, clippy::needless_pass_by_value)]
    ));

    Ok(quote! {
        #method

        #(#key_functions)*

        #[doc(hidden)]
        pub(crate) fn __krs_initializer_payload() -> (
            #facade::HostConfigurationInitializer,
            #facade::HostProvenance,
        ) {
            let _krs_path_check = || {
                #(#island_import_checks)*
            };
            fn __krs_type_key<T: ?Sized + 'static>() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<T>()
            }
            let initializer = #facade::HostConfigurationInitializer {
                key: #facade::ProvenanceKey::new(#initializer_declaration_role, 0)
                    .expect("KRS parser roles are nonempty"),
                owner_key: #facade::ProvenanceKey::new(#initializer_result_type_role, 0)
                    .expect("KRS parser roles are nonempty"),
                owner: #facade::HostTypeKey(__krs_type_key::<Self>),
                variables: ::std::vec![#(#variables),*],
                body_key: #facade::ProvenanceKey::new(#initializer_body_role, 0)
                    .expect("KRS parser roles are nonempty"),
                cells: ::std::vec![#(#cells),*],
            };
            (initializer, #provenance)
        }
    })
}

fn inject_inferred_initializer_wrappers(
    method: &mut syn::ImplItemFn,
    initializer: &krs_syntax::InitializerFunction,
    facade: &Path,
) -> syn::Result<()> {
    let [syn::Stmt::Expr(syn::Expr::Struct(body), None)] = method.block.stmts.as_mut_slice() else {
        return Err(syn::Error::new(
            method.block.span(),
            "a fixed initializer must contain exactly one struct expression",
        ));
    };
    inject_initializer_cell_list(body, initializer.cells(), facade)
}

fn inject_initializer_cell_list(
    body: &mut syn::ExprStruct,
    cells: &[FixedCellInitializer],
    facade: &Path,
) -> syn::Result<()> {
    for cell in cells {
        let Some(field) = body
            .fields
            .iter_mut()
            .find(|field| matches!(&field.member, syn::Member::Named(name) if name == cell.name()))
        else {
            return Err(syn::Error::new(
                cell.name().span(),
                "initializer field disappeared during wrapper injection",
            ));
        };
        qualify_initializer_state_macro(&mut field.expr, facade)?;
        match cell.content() {
            InitializerCellContent::Leaf {
                computation,
                inferred_constructor: true,
                ..
            } => {
                let value = field.expr.clone();
                field.expr = if *computation {
                    parse_quote!(#facade::configuration::KCell::new(#value))
                } else {
                    parse_quote!(#facade::configuration::Cell::new(#value))
                };
                field.colon_token = Some(syn::token::Colon::default());
            }
            InitializerCellContent::Leaf {
                inferred_constructor: false,
                ..
            } => {}
            InitializerCellContent::Nested { children, .. } => {
                let syn::Expr::Struct(nested) = &mut field.expr else {
                    return Err(syn::Error::new(
                        field.expr.span(),
                        "a nested fixed-cell initializer must be a struct expression",
                    ));
                };
                inject_initializer_cell_list(nested, children, facade)?;
            }
        }
    }
    Ok(())
}

fn qualify_initializer_state_macro(expression: &mut syn::Expr, facade: &Path) -> syn::Result<()> {
    let macro_expression = match expression {
        syn::Expr::Macro(expression) => Some(expression),
        syn::Expr::Call(call) => call.args.first_mut().and_then(|argument| match argument {
            syn::Expr::Macro(expression) => Some(expression),
            _ => None,
        }),
        _ => None,
    };
    let Some(expression) = macro_expression else {
        return Ok(());
    };
    if expression.mac.path.leading_colon.is_some() || expression.mac.path.segments.len() != 1 {
        return Ok(());
    }
    let name = expression.mac.path.segments[0].ident.clone();
    if !matches!(name.to_string().as_str(), "k" | "map") {
        return Ok(());
    }
    expression.mac.path = syn::parse2(quote!(#facade::#name))?;
    Ok(())
}

#[derive(Default)]
struct InitializerCounters {
    cell: u32,
    constructor: u32,
    term: u32,
    term_path: u32,
    k_payload: u32,
    k_item: u32,
    k_tail: u32,
    map_payload: u32,
    map_key: u32,
    map_value: u32,
    map_update_base: u32,
}

struct InitializerBuilder<'a> {
    facade: &'a Path,
    bindings: &'a [Ident],
    counters: InitializerCounters,
    terms: TermBuilder<'a>,
    key_functions: Vec<TokenStream>,
}

impl<'a> InitializerBuilder<'a> {
    fn new(facade: &'a Path, nonce: u64, cfg: &'a [Attribute], bindings: &'a [Ident]) -> Self {
        Self {
            facade,
            bindings,
            counters: InitializerCounters::default(),
            terms: TermBuilder::new(facade, nonce, cfg, bindings).with_associated_keys(),
            key_functions: Vec::new(),
        }
    }

    fn expand_cells(
        &mut self,
        cells: &[FixedCellInitializer],
        owner: &TokenStream,
    ) -> syn::Result<Vec<TokenStream>> {
        let initializer_field_role = ProvenanceRole::InitializerField;
        let initializer_cell_constructor_role = ProvenanceRole::InitializerCellConstructor;
        let initializer_nested_constructor_role = ProvenanceRole::InitializerNestedConstructor;
        let initializer_cell_role = ProvenanceRole::InitializerCell;
        let facade = self.facade;
        let mut output = Vec::new();
        for cell in cells {
            let cell_ordinal = take_counter(&mut self.counters.cell)?;
            let constructor_ordinal = take_counter(&mut self.counters.constructor)?;
            let marker = cell_marker_function(cell.name());
            let field = quote! {
                #facade::HostCellReference {
                    key: #facade::ProvenanceKey::new(#initializer_field_role, #cell_ordinal)
                        .expect("KRS parser roles are nonempty"),
                    cell: #facade::HostCellIdentity {
                        owner: #facade::HostTypeKey(__krs_type_key::<#owner>),
                        field: #facade::HostTypeKey(#owner::#marker),
                    },
                }
            };
            let content = match cell.content() {
                InitializerCellContent::Leaf {
                    constructor,
                    value,
                    computation,
                    ..
                } => {
                    if *computation != matches!(value, StateTerm::KSequence(_)) {
                        return Err(syn::Error::new(
                            constructor.span(),
                            "cell wrapper and initializer state family disagree",
                        ));
                    }
                    let wrapper = if *computation {
                        quote!(#facade::CellWrapper::KCell)
                    } else {
                        quote!(#facade::CellWrapper::Cell)
                    };
                    let value = self.expand_state(value)?;
                    quote! {
                        #facade::ProtocolInitializerCellContent::Leaf {
                            constructor_key: #facade::ProvenanceKey::new(
                                #initializer_cell_constructor_role, #constructor_ordinal,
                            ).expect("KRS parser roles are nonempty"),
                            wrapper: #wrapper,
                            value: #value,
                        }
                    }
                }
                InitializerCellContent::Nested {
                    constructor,
                    children,
                } => {
                    let path = call_site_path(constructor)?;
                    let authored = spelling(constructor);
                    let declaration = quote! {
                        #facade::HostCellDeclarationReference {
                            key: #facade::ProvenanceKey::new(
                                #initializer_nested_constructor_role, #constructor_ordinal,
                            ).expect("KRS parser roles are nonempty"),
                            declaration: #facade::HostTypeReference {
                                key: #facade::HostTypeKey(__krs_type_key::<#path>),
                                authored_path: #authored.to_owned(),
                            },
                        }
                    };
                    let children = self.expand_cells(children, &quote!(#path))?;
                    quote! {
                        #facade::ProtocolInitializerCellContent::Nested {
                            declaration: #declaration,
                            children: ::std::vec![#(#children),*],
                        }
                    }
                }
            };
            let facade = self.facade;
            output.push(quote! {
                #facade::HostInitializerCell {
                    key: #facade::ProvenanceKey::new(#initializer_cell_role, #cell_ordinal)
                        .expect("KRS parser roles are nonempty"),
                    field: #field,
                    content: #content,
                }
            });
        }
        Ok(output)
    }

    fn expand_state(&mut self, state: &StateTerm) -> syn::Result<TokenStream> {
        let facade = self.facade;
        match state {
            StateTerm::Term(term) => {
                let term = self.expand_term(term, None)?;
                Ok(quote!(#facade::ProtocolInitializerStateTerm::Term(#term)))
            }
            StateTerm::KSequence(sequence) => {
                let sequence = self.expand_k(sequence)?;
                Ok(quote!(#facade::ProtocolInitializerStateTerm::KSequence(#sequence)))
            }
            StateTerm::Map(map) => {
                let map = self.expand_map(map)?;
                Ok(quote!(#facade::ProtocolInitializerStateTerm::Map(#map)))
            }
        }
    }

    fn expand_k(&mut self, sequence: &KSequence) -> syn::Result<TokenStream> {
        let facade = self.facade;
        let payload_key = if sequence_has_role(sequence, ProvenanceRole::KSequencePayload)? {
            let ordinal = take_counter(&mut self.counters.k_payload)?;
            option_key(facade, ProvenanceRole::KSequencePayload, ordinal)
        } else {
            quote!(::core::option::Option::None)
        };
        let dot_k_key = if sequence.notation() == KSequenceNotation::DotK {
            let ordinal = take_counter(&mut self.counters.k_tail)?;
            option_key(facade, ProvenanceRole::KSequenceTail, ordinal)
        } else {
            quote!(::core::option::Option::None)
        };
        let notation = k_notation(facade, sequence.notation());
        let mut items = Vec::new();
        for item in sequence.items() {
            let ordinal = take_counter(&mut self.counters.k_item)?;
            let structural = provenance_key(facade, ProvenanceRole::KSequenceItem, ordinal);
            let value = self.expand_term(item, Some(structural.clone()))?;
            items.push(quote! {
                #facade::ProtocolKSequenceItem { key: #structural, value: #value }
            });
        }
        Ok(quote! {
            #facade::ProtocolKSequence {
                payload_key: #payload_key,
                dot_k_key: #dot_k_key,
                notation: #notation,
                items: ::std::vec![#(#items),*],
            }
        })
    }

    fn expand_map(&mut self, map: &MapExpression) -> syn::Result<TokenStream> {
        let facade = self.facade;
        let payload_key = if map_has_role(map, ProvenanceRole::MapPayload)? {
            let ordinal = take_counter(&mut self.counters.map_payload)?;
            option_key(facade, ProvenanceRole::MapPayload, ordinal)
        } else {
            quote!(::core::option::Option::None)
        };
        let body = match map.body() {
            MapBody::Empty { explicit_dot } => quote! {
                #facade::ProtocolMapBody::Empty { explicit_dot: #explicit_dot }
            },
            MapBody::Items { items, .. } => {
                let mut output = Vec::new();
                for item in items {
                    let key_ordinal = take_counter(&mut self.counters.map_key)?;
                    let value_ordinal = take_counter(&mut self.counters.map_value)?;
                    let key_key = provenance_key(facade, ProvenanceRole::MapKey, key_ordinal);
                    let value_key = provenance_key(facade, ProvenanceRole::MapValue, value_ordinal);
                    let key = self.expand_term(item.key(), Some(key_key.clone()))?;
                    let value = self.expand_term(item.value(), Some(value_key.clone()))?;
                    output.push(quote! {
                        #facade::ProtocolMapItem {
                            key_key: #key_key, key: #key,
                            value_key: #value_key, value: #value,
                        }
                    });
                }
                quote!(#facade::ProtocolMapBody::Items { items: ::std::vec![#(#output),*] })
            }
            MapBody::Update { base, key, value } => {
                let base_ordinal = take_counter(&mut self.counters.map_update_base)?;
                let key_ordinal = take_counter(&mut self.counters.map_key)?;
                let value_ordinal = take_counter(&mut self.counters.map_value)?;
                let base_key = provenance_key(facade, ProvenanceRole::MapUpdateBase, base_ordinal);
                let key_key = provenance_key(facade, ProvenanceRole::MapKey, key_ordinal);
                let value_key = provenance_key(facade, ProvenanceRole::MapValue, value_ordinal);
                let base = self.expand_term(base, Some(base_key.clone()))?;
                let key = self.expand_term(key, Some(key_key.clone()))?;
                let value = self.expand_term(value, Some(value_key.clone()))?;
                quote! {
                    #facade::ProtocolMapBody::Update {
                        base_key: #base_key, base: #base,
                        key_key: #key_key, key: #key,
                        value_key: #value_key, value: #value,
                    }
                }
            }
        };
        Ok(quote!(#facade::ProtocolMap { payload_key: #payload_key, body: #body }))
    }

    fn expand_term(
        &mut self,
        term: &TermExpression,
        structural_key: Option<TokenStream>,
    ) -> syn::Result<TokenStream> {
        let ordinal = take_counter(&mut self.counters.term)?;
        let key = provenance_key(self.facade, ProvenanceRole::InitializerTerm, ordinal);
        let structural = structural_key.unwrap_or_else(|| key.clone());
        let term = self.expand_term_tree(term.tree(), &structural)?;
        let facade = self.facade;
        Ok(quote!(#facade::ProtocolInitializerTerm { key: #key, term: #term }))
    }

    fn expand_term_tree(
        &mut self,
        tree: &TermTree,
        structural_key: &TokenStream,
    ) -> syn::Result<TokenStream> {
        let facade = self.facade;
        match tree {
            TermTree::Application(application) => {
                let ordinal = take_counter(&mut self.counters.term_path)?;
                let key = provenance_key(facade, ProvenanceRole::InitializerTermPath, ordinal);
                let target = self.terms.application_target(application.head())?;
                let TermArguments::Positional(values) = application.arguments() else {
                    return Err(syn::Error::new(
                        application.head().span(),
                        "initializer terms cannot use named record arguments",
                    ));
                };
                let arguments = values
                    .iter()
                    .map(|value| {
                        self.expand_term_tree(value, structural_key).map(|value| {
                            quote! {
                                #facade::HostTermArgument::Positional {
                                    value: ::std::boxed::Box::new(#value),
                                }
                            }
                        })
                    })
                    .collect::<syn::Result<Vec<_>>>()?;
                Ok(quote! {
                    #facade::HostTerm::Application {
                        head_class: #facade::DescriptorApplicationHeadClass::Applied,
                        reference: #facade::HostApplicationReference { key: #key, target: #target },
                        path_key: #key,
                        arguments: ::std::vec![#(#arguments),*],
                    }
                })
            }
            TermTree::Reference(path) => {
                let ordinal = take_counter(&mut self.counters.term_path)?;
                let key = provenance_key(facade, ProvenanceRole::InitializerTermPath, ordinal);
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
                        path_key: #key,
                        arguments: ::std::vec![],
                    }))
                }
            }
            TermTree::Literal(literal) => {
                let literal = literal_tokens(facade, literal);
                Ok(quote!(#facade::HostTerm::Literal { key: #structural_key, literal: #literal }))
            }
            TermTree::Wildcard(_) => Err(syn::Error::new(
                Span::call_site(),
                "initializer terms cannot contain wildcards",
            )),
            TermTree::IdToken { .. }
            | TermTree::BytesToken { .. }
            | TermTree::Anonymous { .. }
            | TermTree::OrBool { .. } => Err(syn::Error::new(
                Span::call_site(),
                "claim-only terms cannot occur in initializers",
            )),
            TermTree::Cell(cell) => Err(syn::Error::new(
                cell.owner().span(),
                "fragment! is not an initializer term; construct nested initializer cells directly",
            )),
        }
    }
}

fn option_key(facade: &Path, role: ProvenanceRole, ordinal: u32) -> TokenStream {
    let key = provenance_key(facade, role, ordinal);
    quote!(::core::option::Option::Some(#key))
}

fn sequence_has_role(sequence: &KSequence, role: ProvenanceRole) -> syn::Result<bool> {
    sequence
        .provenance()
        .map(|anchors| anchors.iter().any(|anchor| anchor.role() == role))
        .map_err(krs_syntax::SyntaxError::into_syn_error)
}

fn map_has_role(map: &MapExpression, role: ProvenanceRole) -> syn::Result<bool> {
    map.provenance()
        .map(|anchors| anchors.iter().any(|anchor| anchor.role() == role))
        .map_err(krs_syntax::SyntaxError::into_syn_error)
}

fn k_notation(facade: &Path, notation: KSequenceNotation) -> TokenStream {
    match notation {
        KSequenceNotation::Comma => quote!(#facade::DescriptorKSequenceNotation::Comma),
        KSequenceNotation::Operator => quote!(#facade::DescriptorKSequenceNotation::Operator),
        KSequenceNotation::DotK => quote!(#facade::DescriptorKSequenceNotation::DotK),
    }
}

fn literal_tokens(facade: &Path, literal: &TermLiteral) -> TokenStream {
    match literal {
        TermLiteral::Integer(value) => {
            let value = value.base10_digits().replace('_', "");
            quote!(#facade::DescriptorLiteral::Int(#value.to_owned()))
        }
        TermLiteral::Boolean(value) => {
            let value = value.value;
            quote!(#facade::DescriptorLiteral::Bool(#value))
        }
    }
}

fn bytes_token_value(literal: &syn::LitByteStr) -> String {
    use std::fmt::Write as _;

    let mut value = String::from("b\"");
    for byte in literal.value() {
        write!(&mut value, "\\x{byte:02x}").expect("writing to a String cannot fail");
    }
    value.push('"');
    value
}

fn rule_label_tokens(facade: &Path, attribute: &krs_syntax::RuleAttribute) -> TokenStream {
    let rule_label_role = ProvenanceRole::RuleLabel;
    attribute.label().map_or_else(
        || quote!(::core::option::Option::None),
        |label| {
            let name = label.value();
            quote! {
                ::core::option::Option::Some(#facade::DescriptorRuleLabel {
                    key: #facade::ProvenanceKey::new(#rule_label_role, 0)
                        .expect("KRS parser roles are nonempty"),
                    name: #name.to_owned(),
                })
            }
        },
    )
}

fn rule_owise_tokens(facade: &Path, attribute: &krs_syntax::RuleAttribute) -> TokenStream {
    let rule_owise_role = ProvenanceRole::RuleOwise;
    if attribute.is_owise() {
        quote!(::core::option::Option::Some(#facade::DescriptorRulePriority {
            key: #facade::ProvenanceKey::new(#rule_owise_role, 0)
                .expect("KRS parser roles are nonempty"),
            value: 200,
        }))
    } else {
        quote!(::core::option::Option::None)
    }
}

#[allow(clippy::too_many_lines)]
pub(crate) fn rule(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let attribute =
        parse_rule_attribute(attributes).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let parsed: ItemFn = syn::parse2(item.clone())?;
    let is_cells_rule = parsed.sig.inputs.last().is_some_and(|argument| {
        let FnArg::Typed(argument) = argument else {
            return false;
        };
        let Pat::Macro(pattern) = &*argument.pat else {
            return false;
        };
        pattern
            .mac
            .path
            .segments
            .last()
            .is_some_and(|segment| segment.ident == "cells")
    });
    if is_cells_rule {
        return configuration_rule(env, item, &attribute);
    }
    ordinary_rule(
        env,
        item,
        &attribute,
        krs_ir::SentenceKind::Transition,
        None,
        None,
    )
}

pub(crate) fn equation(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    parse_equation_attribute(attributes).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let attribute = krs_syntax::RuleAttribute::default();
    ordinary_rule(
        env,
        item,
        &attribute,
        krs_ir::SentenceKind::Equation,
        None,
        None,
    )
}

pub(crate) fn simplification(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let attribute = parse_simplification_attribute(attributes)
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    ordinary_rule(
        env,
        item,
        &krs_syntax::RuleAttribute::default(),
        krs_ir::SentenceKind::Simplification,
        None,
        Some(&attribute),
    )
}

/// Expands one whole-configuration reachability claim.
pub(crate) fn claim(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let attribute =
        parse_claim_attribute(attributes).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    configuration_claim(env, item, &attribute)
}

pub(crate) fn alias(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    parse_alias_attribute(attributes).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    if syn::parse2::<ItemFn>(item.clone()).is_ok() {
        return ordinary_rule(
            env,
            item,
            &krs_syntax::RuleAttribute::default(),
            krs_ir::SentenceKind::Alias,
            None,
            None,
        );
    }
    Err(syn::Error::new(
        Span::call_site(),
        "`#[k::alias]` on a production is a constructor helper; place `#[k::constructor(...)]` before it",
    ))
}

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
    let attribute = parse_context_alias_attribute(attributes)
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let alias = parse_state_context_alias_item(item, attribute.here())
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let facade = env.facade_path()?;
    let mut anchors = attribute
        .provenance()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    anchors.push(ProvenanceAnchor::new(
        ProvenanceRole::ContextAliasDeclaration,
        0,
        TokenRange::for_tokens(&alias.item().sig.ident)
            .map_err(krs_syntax::SyntaxError::into_syn_error)?,
    ));
    anchors.extend(
        alias
            .provenance()
            .map_err(krs_syntax::SyntaxError::into_syn_error)?,
    );
    let fallback =
        TokenRange::for_tokens(alias.item()).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let provenance = host_provenance(env, &facade, fallback, &anchors)?;
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
                    let sort_spelling = sort.sort_spelling();
                    let ordinal = term_ordinal;
                    term_ordinal = term_ordinal.checked_add(1).ok_or_else(|| {
                        syn::Error::new(binding.name().span(), "too many context bindings")
                    })?;
                    quote!(#facade::ProtocolContextAliasBindingKind::Term {
                        sort: #facade::HostSortReference {
                            key: #facade::ProvenanceKey::new(#rule_binding_type_role, #ordinal)
                                .expect("KRS parser roles are nonempty"),
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
    for candidate in alias
        .reference_candidates()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?
    {
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
        #(#cfg)*
        #[doc(hidden)]
        fn #factory() -> #facade::HostDescriptor {
            #facade::HostDescriptor {
                protocol_version: #facade::ProtocolVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"), env!("CARGO_MANIFEST_DIR"),
                    module_path!(), #rust_name, #facade::ItemKind::ContextAlias, "",
                ).expect("Cargo and Rust macro context form a valid context alias identity"),
                declared_type: ::core::option::Option::None,
                payload: #facade::HostDescriptorPayload::ContextAlias(::std::boxed::Box::new(
                    #facade::HostContextAlias {
                        declaration_key: #facade::ProvenanceKey::new(#context_alias_declaration_role, 0).unwrap(),
                        name_key: #facade::ProvenanceKey::new(#context_alias_name_role, 0).unwrap(),
                        name: #alias_name.to_owned(),
                        here_key: #facade::ProvenanceKey::new(#context_alias_here_role, 0).unwrap(),
                        here: #here_name.to_owned(),
                        pattern_key: #facade::ProvenanceKey::new(#rule_pattern_role, 0).unwrap(),
                        configuration: #facade::HostConfigurationReference {
                            key: #facade::ProvenanceKey::new(#rule_type_role, 0).unwrap(),
                            configuration: #facade::HostTypeReference {
                                key: #facade::HostTypeKey(#configuration_key),
                                authored_path: #configuration_spelling.to_owned(),
                            },
                        },
                        bindings: ::std::vec![#(#bindings),*],
                        pattern: #pattern,
                    }
                )),
                cfg: ::core::default::Default::default(),
                provenance: #provenance,
            }
        }
        #(#cfg)*
        #facade::__register_host_descriptor!(#factory);
    })
}

pub(crate) fn priority(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let priority =
        parse_priority_attribute(attributes).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let mut function: ItemFn = syn::parse2(item)?;
    let Some(index) = function
        .attrs
        .iter()
        .position(|attribute| helper_entry(attribute.path()) == Some(AttributeMacro::Equation))
    else {
        return Err(syn::Error::new(
            Span::call_site(),
            "`#[k::priority]` is an equation helper; place it immediately before `#[k::equation]`",
        ));
    };
    function.attrs.remove(index);
    ordinary_rule(
        env,
        function.to_token_stream(),
        &krs_syntax::RuleAttribute::default(),
        krs_ir::SentenceKind::Equation,
        Some(&priority),
        None,
    )
}

#[allow(clippy::too_many_lines)]
fn ordinary_rule(
    env: &dyn MacroEnvironment,
    item: TokenStream,
    attribute: &krs_syntax::RuleAttribute,
    sentence_kind: krs_ir::SentenceKind,
    priority: Option<&krs_syntax::PriorityAttribute>,
    simplification: Option<&krs_syntax::SimplificationAttribute>,
) -> syn::Result<TokenStream> {
    let rule = parse_rule_item(item).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    expand_ordinary_rule(
        env,
        &rule,
        attribute,
        sentence_kind,
        priority,
        simplification,
        None,
        &[],
    )
}

/// Expands a readable block into independent ordinary rule declarations.
pub(crate) fn rules(env: &dyn MacroEnvironment, input: TokenStream) -> syn::Result<TokenStream> {
    let block = parse_rule_block(input).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let enum_owner = block.imports().first().map(krs_syntax::RuleImport::owner);
    let enum_variant = block
        .imports()
        .first()
        .and_then(krs_syntax::RuleImport::variant);
    let import_checks = block.imports().iter().map(|import| {
        let item = import.item();
        quote! {
            const _: () = {
                #[allow(unused_imports)]
                #item
            };
        }
    });
    let mut clauses = Vec::with_capacity(block.clauses().len());
    for clause in block.clauses() {
        clauses.push(expand_head_rule(
            env,
            clause,
            enum_owner,
            enum_variant,
            block.is_configuration(),
        )?);
    }
    Ok(quote! {
        #(#import_checks)*
        #(#clauses)*
    })
}

#[allow(clippy::too_many_lines)]
fn expand_head_rule(
    env: &dyn MacroEnvironment,
    clause: &krs_syntax::RuleClause,
    enum_owner: Option<&Path>,
    enum_variant: Option<&Ident>,
    configuration_owned: bool,
) -> syn::Result<TokenStream> {
    let rule_left_cells_field_role = ProvenanceRole::RuleLeftCellsField;
    let rule_right_cells_field_role = ProvenanceRole::RuleRightCellsField;
    let rule_requires_role = ProvenanceRole::RuleRequires;
    let rule_label_role = ProvenanceRole::RuleLabel;
    let rule_type_role = ProvenanceRole::RuleType;
    let rule_pattern_role = ProvenanceRole::RulePattern;
    let rule_result_role = ProvenanceRole::RuleResult;
    let facade = env.facade_path()?;
    let rule = clause.rule();
    let mut anchors = clause
        .provenance()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    anchors.extend(
        clause
            .attribute()
            .provenance()
            .map_err(krs_syntax::SyntaxError::into_syn_error)?,
    );
    let fallback =
        TokenRange::for_tokens(rule.item()).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let provenance = host_provenance(env, &facade, fallback, &anchors)?;
    let nonce = expansion_nonce(env, "head_rule", &rule.item().sig.ident, fallback);
    let factory = format_ident!("__krs_head_rule_descriptor_{nonce:016x}");
    let sort_key = format_ident!("__krs_head_rule_sort_{nonce:016x}");
    let cfg = call_site_cfg_attributes(&rule.item().attrs)?;
    let sort_path = call_site_path(rule.parameter().term_sort.sort())?;
    let sort_type = sort_type_tokens(&sort_path, rule.parameter().term_sort.is_dynamic());
    let sort_spelling = rule.parameter().term_sort.sort_spelling();
    let head_sort = host_sort_reference(
        &facade,
        ProvenanceRole::RuleType,
        0,
        &sort_key,
        &sort_spelling,
    );
    let binding_idents = clause.bindings().to_vec();
    let mut builder = TermBuilder::new(&facade, nonce, &cfg, &binding_idents)
        .with_enum_import(enum_owner, enum_variant)
        .with_lexical_rule_head(enum_owner.is_none());
    let subject = builder.expand(rule.subject_tree(), TermSide::Left)?;

    let mut have_ordinal = 0_u32;
    let mut update_ordinal = 0_u32;
    let mut have_extras = Vec::new();
    let mut rewrite_befores = Vec::new();
    for extra in clause.extras() {
        match extra {
            krs_syntax::RuleExtra::HaveMap { cell, key, value } => {
                let cell_name = cell.unraw().to_string();
                let value_binding = value.unraw().to_string();
                let key = builder.expand(key.tree(), TermSide::Left)?;
                let ordinal = have_ordinal;
                have_ordinal = have_ordinal
                    .checked_add(1)
                    .ok_or_else(|| syn::Error::new(cell.span(), "too many readable cell reads"))?;
                have_extras.push(quote! {
                    #facade::ProtocolHeadRuleExtra::HaveMap {
                        cell: #facade::HostHeadRuleCellReference {
                            key: #facade::ProvenanceKey::new(#rule_left_cells_field_role, #ordinal).unwrap(),
                            name: #cell_name.to_owned(),
                        },
                        key: #key,
                        value_binding: #value_binding.to_owned(),
                    }
                });
            }
            krs_syntax::RuleExtra::RewriteCell {
                cell, before_tree, ..
            } => {
                let before = builder.expand(before_tree, TermSide::Left)?;
                let ordinal = have_ordinal;
                have_ordinal = have_ordinal
                    .checked_add(1)
                    .ok_or_else(|| syn::Error::new(cell.span(), "too many readable cell reads"))?;
                rewrite_befores.push((cell.unraw().to_string(), ordinal, before));
            }
            krs_syntax::RuleExtra::UpdateMap { .. } => {}
        }
    }

    builder.reset_side();
    let result = match clause.head_result() {
        krs_syntax::RuleHeadResult::Replace(term) => {
            let term = builder.expand(term.tree(), TermSide::Right)?;
            quote!(#facade::ProtocolHeadRuleResult::Replace(#term))
        }
        krs_syntax::RuleHeadResult::Splice { items, .. } => {
            let items = items
                .iter()
                .map(|item| builder.expand(item.tree(), TermSide::Right))
                .collect::<Result<Vec<_>, _>>()?;
            quote!(#facade::ProtocolHeadRuleResult::Splice(::std::vec![#(#items),*]))
        }
        krs_syntax::RuleHeadResult::Erase(_) => {
            quote!(#facade::ProtocolHeadRuleResult::Erase)
        }
    };
    let mut update_extras = Vec::new();
    let mut rewrite_index = 0_usize;
    for extra in clause.extras() {
        match extra {
            krs_syntax::RuleExtra::UpdateMap { cell, base, update } => {
                let cell_name = cell.unraw().to_string();
                let base_binding = base.unraw().to_string();
                let update = builder.expand(update.tree(), TermSide::Right)?;
                let ordinal = update_ordinal;
                update_ordinal = update_ordinal.checked_add(1).ok_or_else(|| {
                    syn::Error::new(cell.span(), "too many readable cell updates")
                })?;
                update_extras.push(quote! {
                    #facade::ProtocolHeadRuleExtra::UpdateMap {
                        cell: #facade::HostHeadRuleCellReference {
                            key: #facade::ProvenanceKey::new(#rule_right_cells_field_role, #ordinal).unwrap(),
                            name: #cell_name.to_owned(),
                        },
                        base_binding: #base_binding.to_owned(),
                        update: #update,
                    }
                });
            }
            krs_syntax::RuleExtra::RewriteCell { cell, after, .. } => {
                let (cell_name, left_ordinal, before) = &rewrite_befores[rewrite_index];
                rewrite_index += 1;
                debug_assert_eq!(cell_name, &cell.unraw().to_string());
                let after = builder.expand(after.tree(), TermSide::Right)?;
                let right_ordinal = update_ordinal;
                update_ordinal = update_ordinal.checked_add(1).ok_or_else(|| {
                    syn::Error::new(cell.span(), "too many readable cell updates")
                })?;
                update_extras.push(quote! {
                    #facade::ProtocolHeadRuleExtra::RewriteCell {
                        cell: #facade::HostHeadRuleCellReference {
                            key: #facade::ProvenanceKey::new(#rule_left_cells_field_role, #left_ordinal).unwrap(),
                            name: #cell_name.to_owned(),
                        },
                        result_key: #facade::ProvenanceKey::new(#rule_right_cells_field_role, #right_ordinal).unwrap(),
                        before: #before,
                        after: #after,
                    }
                });
            }
            krs_syntax::RuleExtra::HaveMap { .. } => {}
        }
    }
    let mut extras = have_extras;
    extras.extend(update_extras);
    builder.reset_side();
    let requires = if let Some(condition) = rule.requires() {
        let term = builder.expand(condition.term().tree(), TermSide::Requires)?;
        quote! {
            ::core::option::Option::Some(#facade::HostRuleCondition {
                key: #facade::ProvenanceKey::new(#rule_requires_role, 0).unwrap(),
                term: #term,
            })
        }
    } else {
        quote!(::core::option::Option::None)
    };
    let key_functions = builder.key_functions;
    let tooling_binding_references = builder.tooling_binding_references;

    let mut refinement_functions = Vec::new();
    let mut bindings = Vec::new();
    let mut binding_checks = Vec::new();
    for binding in clause.bindings() {
        let name = binding.unraw().to_string();
        binding_checks.push(quote! {
            let #binding = ();
        });
        let refinement = if let Some((ordinal, narrowing)) = clause
            .narrowings()
            .iter()
            .enumerate()
            .find(|(_, narrowing)| narrowing.binding().unraw() == binding.unraw())
        {
            let ordinal = u32::try_from(ordinal)
                .map_err(|_| syn::Error::new(binding.span(), "too many rule refinements"))?;
            let key_fn = format_ident!("__krs_head_rule_refinement_{nonce:016x}_{ordinal}");
            // Keep the authored narrowing path visible to language tooling.
            let path = narrowing.sort();
            let authored = spelling(narrowing.sort());
            binding_checks.push(quote! {
                let _: ::core::marker::PhantomData<#path> = ::core::marker::PhantomData;
            });
            refinement_functions.push(quote! {
                #(#cfg)*
                #[doc(hidden)]
                fn #key_fn() -> ::core::any::TypeId {
                    ::core::any::TypeId::of::<#path>()
                }
            });
            let reference = host_sort_reference(
                &facade,
                ProvenanceRole::RuleBindingType,
                ordinal,
                &key_fn,
                &authored,
            );
            quote!(::core::option::Option::Some(#reference))
        } else {
            quote!(::core::option::Option::None)
        };
        bindings.push(quote! {
            #facade::ProtocolHeadRuleBinding {
                name: #name.to_owned(),
                refinement: #refinement,
            }
        });
    }
    binding_checks.push(quote! {
        #(let _ = &#tooling_binding_references;)*
    });
    let label = clause.attribute().label().map_or_else(
        || {
            let name = rule.item().sig.ident.unraw().to_string().replace('_', "-");
            quote! {
                ::core::option::Option::Some(#facade::DescriptorRuleLabel {
                    key: #facade::ProvenanceKey::new(#rule_label_role, 0)
                        .expect("KRS parser roles are nonempty"),
                    name: #name.to_owned(),
                })
            }
        },
        |_| rule_label_tokens(&facade, clause.attribute()),
    );
    let priority = rule_owise_tokens(&facade, clause.attribute());
    let original = rule.item();
    let attrs = &original.attrs;
    let visibility = &original.vis;
    let fn_token = original.sig.fn_token;
    let name_ident = &original.sig.ident;
    let name = name_ident.unraw().to_string();
    let parameter_type = rule.parameter().term_sort.ty();
    let header = if configuration_owned {
        let computation_cell = clause.computation_cell().ok_or_else(|| {
            syn::Error::new(
                rule.item().sig.ident.span(),
                "a configuration-owned rule is missing its computation-cell field",
            )
        })?;
        let computation_cell = computation_cell.unraw().to_string();
        quote! {
            head_sort: ::core::option::Option::None,
            configuration: ::core::option::Option::Some(#facade::HostConfigurationReference {
                key: #facade::ProvenanceKey::new(#rule_type_role, 0).unwrap(),
                configuration: #facade::HostTypeReference {
                    key: #facade::HostTypeKey(#sort_key),
                    authored_path: #sort_spelling.to_owned(),
                },
            }),
            computation_cell_name: ::core::option::Option::Some(#computation_cell.to_owned()),
        }
    } else {
        quote! {
            head_sort: ::core::option::Option::Some(#head_sort),
            configuration: ::core::option::Option::None,
            computation_cell_name: ::core::option::Option::None,
        }
    };

    Ok(quote! {
        #(#attrs)*
        #visibility #fn_token #name_ident(__krs_symbolic_subject: #parameter_type) -> #parameter_type {
            let _krs_binding_check = || { #(#binding_checks)* };
            let _ = __krs_symbolic_subject;
            ::core::panic!("KRS rule declarations have no runtime implementation")
        }

        #(#cfg)*
        #[doc(hidden)]
        fn #sort_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#sort_type>()
        }
        #(#refinement_functions)*
        #(#key_functions)*

        #(#cfg)*
        #[doc(hidden)]
        fn #factory() -> #facade::HostDescriptor {
            #facade::HostDescriptor {
                protocol_version: #facade::ProtocolVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"), env!("CARGO_MANIFEST_DIR"),
                    module_path!(), #name, #facade::ItemKind::Rule, "",
                ).expect("Cargo and Rust macro context form a valid host identity"),
                declared_type: ::core::option::Option::None,
                payload: #facade::HostDescriptorPayload::HeadRule(::std::boxed::Box::new(
                    #facade::HostHeadRule {
                        sentence_kind: #facade::SentenceKind::Transition,
                        label: #label,
                        priority: #priority,
                        pattern_key: #facade::ProvenanceKey::new(#rule_pattern_role, 0).unwrap(),
                        result_key: #facade::ProvenanceKey::new(#rule_result_role, 0).unwrap(),
                        #header
                        bindings: ::std::vec![#(#bindings),*],
                        subject: #subject,
                        result: #result,
                        requires: #requires,
                        extras: ::std::vec![#(#extras),*],
                    }
                )),
                cfg: ::core::default::Default::default(),
                provenance: #provenance,
            }
        }
        #(#cfg)*
        #facade::__register_host_descriptor!(#factory);
    })
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn expand_ordinary_rule(
    env: &dyn MacroEnvironment,
    rule: &krs_syntax::RuleItem,
    attribute: &krs_syntax::RuleAttribute,
    sentence_kind: krs_ir::SentenceKind,
    priority: Option<&krs_syntax::PriorityAttribute>,
    simplification: Option<&krs_syntax::SimplificationAttribute>,
    enum_glob: Option<&Path>,
    narrowings: &[krs_syntax::RuleNarrowing],
) -> syn::Result<TokenStream> {
    let rule_requires_role = ProvenanceRole::RuleRequires;
    let equation_priority_role = ProvenanceRole::EquationPriority;
    let simplification_priority_role = ProvenanceRole::SimplificationPriority;
    let simplification_marker_role = ProvenanceRole::SimplificationMarker;
    let rule_pattern_role = ProvenanceRole::RulePattern;
    let rule_result_role = ProvenanceRole::RuleResult;
    let facade = env.facade_path()?;
    let mut anchors = rule
        .full_provenance()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    anchors.extend(
        attribute
            .provenance()
            .map_err(krs_syntax::SyntaxError::into_syn_error)?,
    );
    if sentence_kind == krs_ir::SentenceKind::Alias {
        anchors.push(ProvenanceAnchor::new(
            ProvenanceRole::AliasClause,
            0,
            TokenRange::for_tokens(&rule.item().sig.ident)
                .map_err(krs_syntax::SyntaxError::into_syn_error)?,
        ));
    }
    if let Some(priority) = priority {
        anchors.extend(
            priority
                .provenance()
                .map_err(krs_syntax::SyntaxError::into_syn_error)?,
        );
    }
    if let Some(simplification) = simplification {
        anchors.push(ProvenanceAnchor::new(
            ProvenanceRole::SimplificationMarker,
            0,
            TokenRange::for_tokens(&rule.item().sig.ident)
                .map_err(krs_syntax::SyntaxError::into_syn_error)?,
        ));
        anchors.extend(
            simplification
                .provenance()
                .map_err(krs_syntax::SyntaxError::into_syn_error)?,
        );
    }
    let fallback = krs_syntax::TokenRange::for_tokens(rule.item())
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let provenance = host_provenance(env, &facade, fallback, &anchors)?;
    let sentence_name = match sentence_kind {
        krs_ir::SentenceKind::Transition => "rule",
        krs_ir::SentenceKind::Equation => "equation",
        krs_ir::SentenceKind::Simplification => "simplification",
        krs_ir::SentenceKind::Alias => "alias",
        krs_ir::SentenceKind::Claim => unreachable!("claims have a separate authoring form"),
    };
    let nonce = expansion_nonce(env, sentence_name, &rule.item().sig.ident, fallback);
    let factory = format_ident!(
        "__krs_rule_descriptor_{nonce:016x}",
        span = Span::call_site()
    );
    let cfg = call_site_cfg_attributes(&rule.item().attrs)?;
    let parameter_key = format_ident!("__krs_rule_subject_sort_{nonce:016x}");
    let result_key = format_ident!("__krs_rule_result_sort_{nonce:016x}");
    let parameter_sort_path = call_site_path(rule.parameter().term_sort.sort())?;
    let result_sort_path = call_site_path(rule.result_sort().sort())?;
    let parameter_sort_type = sort_type_tokens(
        &parameter_sort_path,
        rule.parameter().term_sort.is_dynamic(),
    );
    let result_sort_type = sort_type_tokens(&result_sort_path, rule.result_sort().is_dynamic());

    let original = rule.item();
    let attrs = &original.attrs;
    let visibility = &original.vis;
    let fn_token = original.sig.fn_token;
    let name_ident = &original.sig.ident;
    let parameter_type = rule.parameter().term_sort.ty();
    let result_type = rule.result_sort().ty();
    let name = name_ident.unraw().to_string();
    let label = rule_label_tokens(&facade, attribute);
    let parameter_sort_spelling = rule.parameter().term_sort.sort_spelling();
    let result_sort_spelling = rule.result_sort().sort_spelling();
    let bindings = rule
        .parameter()
        .pattern
        .bindings()
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    let mut binding_checks = Vec::new();
    for binding in rule.parameter().pattern.bindings() {
        let generated = call_site_ident(binding)?;
        binding_checks.push(quote! {
            let #binding = ();
            let _ = &#generated;
        });
    }
    for narrowing in narrowings {
        let sort = call_site_path(narrowing.sort())?;
        binding_checks.push(quote! {
            let _: ::core::marker::PhantomData<#sort> = ::core::marker::PhantomData;
        });
    }
    let parameter_reference = host_sort_reference(
        &facade,
        ProvenanceRole::RuleType,
        0,
        &parameter_key,
        &parameter_sort_spelling,
    );
    let result_reference = host_sort_reference(
        &facade,
        ProvenanceRole::RuleResultType,
        0,
        &result_key,
        &result_sort_spelling,
    );
    let binding_idents = rule.parameter().pattern.bindings().to_vec();
    let mut term_builder =
        TermBuilder::new(&facade, nonce, &cfg, &binding_idents).with_enum_glob(enum_glob);
    let subject = term_builder.expand(rule.subject_tree(), TermSide::Left)?;
    term_builder.reset_side();
    let result = term_builder.expand(rule.result().tree(), TermSide::Right)?;
    term_builder.reset_side();
    let requires = if let Some(condition) = rule.requires() {
        let term = term_builder.expand(condition.term().tree(), TermSide::Requires)?;
        quote! {
            ::core::option::Option::Some(#facade::HostRuleCondition {
                key: #facade::ProvenanceKey::new(#rule_requires_role, 0)
                    .expect("KRS parser roles are nonempty"),
                term: #term,
            })
        }
    } else {
        quote!(::core::option::Option::None)
    };
    let term_key_functions = term_builder.key_functions;
    let priority = if attribute.is_owise() {
        rule_owise_tokens(&facade, attribute)
    } else {
        priority.map_or_else(
            || quote!(::core::option::Option::None),
            |priority| {
                let value = priority.value();
                quote!(::core::option::Option::Some(#facade::DescriptorRulePriority {
                    key: #facade::ProvenanceKey::new(#equation_priority_role, 0)
                        .expect("KRS parser roles are nonempty"),
                    value: #value,
                }))
            },
        )
    };
    let simplification = simplification.map_or_else(
        || quote!(::core::option::Option::None),
        |simplification| {
            let priority = simplification.priority().map_or_else(
                || quote!(::core::option::Option::None),
                |value| {
                    quote!(::core::option::Option::Some(
                        #facade::DescriptorSimplificationPriority {
                            key: #facade::ProvenanceKey::new(#simplification_priority_role, 0)
                                .expect("KRS parser roles are nonempty"),
                            value: #value,
                        }
                    ))
                },
            );
            quote!(::core::option::Option::Some(#facade::DescriptorSimplification {
                key: #facade::ProvenanceKey::new(#simplification_marker_role, 0)
                    .expect("KRS parser roles are nonempty"),
                priority: #priority,
            }))
        },
    );
    let (sentence_kind, item_kind) = match sentence_kind {
        krs_ir::SentenceKind::Transition => (
            quote!(#facade::SentenceKind::Transition),
            quote!(#facade::ItemKind::Rule),
        ),
        krs_ir::SentenceKind::Equation => (
            quote!(#facade::SentenceKind::Equation),
            quote!(#facade::ItemKind::Equation),
        ),
        krs_ir::SentenceKind::Simplification => (
            quote!(#facade::SentenceKind::Simplification),
            quote!(#facade::ItemKind::Simplification),
        ),
        krs_ir::SentenceKind::Alias => (
            quote!(#facade::SentenceKind::Alias),
            quote!(#facade::ItemKind::Alias),
        ),
        krs_ir::SentenceKind::Claim => unreachable!("claims have a separate authoring form"),
    };

    Ok(quote! {
        #(#attrs)*
        #visibility #fn_token #name_ident(
            __krs_symbolic_subject: #parameter_type,
        ) -> #result_type {
            let _krs_binding_check = || {
                #(#binding_checks)*
            };
            let _ = __krs_symbolic_subject;
            ::core::panic!("KRS rule declarations have no runtime implementation")
        }

        #(#cfg)*
        #[doc(hidden)]
        fn #parameter_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#parameter_sort_type>()
        }

        #(#cfg)*
        #[doc(hidden)]
        fn #result_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#result_sort_type>()
        }

        #(#term_key_functions)*

        #(#cfg)*
        #[doc(hidden)]
        fn #factory() -> #facade::HostDescriptor {
            let rule = #facade::HostStructuredRuleDescriptor {
                sentence_kind: #sentence_kind,
                label: #label,
                requires: #requires,
                priority: #priority,
                simplification: #simplification,
                pattern_key: #facade::ProvenanceKey::new(#rule_pattern_role, 0)
                    .expect("KRS parser roles are nonempty"),
                result_key: #facade::ProvenanceKey::new(#rule_result_role, 0)
                    .expect("KRS parser roles are nonempty"),
                subject_sort: #parameter_reference,
                result_sort: #result_reference,
                bindings: ::std::vec![#(#bindings.to_owned()),*],
                subject: #subject,
                result: #result,
            };
            #facade::HostDescriptor {
                protocol_version: #facade::ProtocolVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"),
                    env!("CARGO_PKG_VERSION"),
                    env!("CARGO_MANIFEST_DIR"),
                    module_path!(),
                    #name,
                    #item_kind,
                    "",
                )
                .expect("Cargo and Rust macro context form a valid host identity"),
                declared_type: ::core::option::Option::None,
                payload: #facade::HostDescriptorPayload::StructuredRule(::std::boxed::Box::new(rule)),
                cfg: ::core::default::Default::default(),
                provenance: #provenance,
            }
        }

        #(#cfg)*
        #facade::__register_host_descriptor!(#factory);
    })
}

#[allow(clippy::too_many_lines)]
fn configuration_rule(
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
    let rule = parse_state_rule_item(item).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let facade = env.facade_path()?;
    let mut anchors = rule
        .provenance()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    anchors.extend(
        attribute
            .provenance()
            .map_err(krs_syntax::SyntaxError::into_syn_error)?,
    );
    let fallback =
        TokenRange::for_tokens(rule.item()).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let provenance = host_provenance(env, &facade, fallback, &anchors)?;
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
                let authored = sort.sort_spelling();
                let ordinal = term_ordinal;
                term_ordinal = term_ordinal.checked_add(1).ok_or_else(|| {
                    syn::Error::new(binding.name().span(), "too many term bindings")
                })?;
                quote! {
                    #facade::ProtocolRuleBindingKind::Term {
                        sort: #facade::HostSortReference {
                            key: #facade::ProvenanceKey::new(#rule_binding_type_role, #ordinal)
                                .expect("KRS parser roles are nonempty"),
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
                key: #facade::ProvenanceKey::new(#rule_requires_role, 0)
                    .expect("KRS parser roles are nonempty"),
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
    for candidate in rule
        .reference_candidates()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?
    {
        if candidate.kind() == StateRuleReferenceKind::CellWrapper {
            let path = call_site_path(candidate.path())?;
            wrapper_checks.push(wrapper_type_check(&path));
        }
    }
    let island_import_checks = consumed_state_island_import_checks(original);

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

        #(#cfg)*
        #[doc(hidden)]
        fn #factory() -> #facade::HostDescriptor {
            #facade::HostDescriptor {
                protocol_version: #facade::ProtocolVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"),
                    env!("CARGO_MANIFEST_DIR"), module_path!(), #name,
                    #facade::ItemKind::Rule, "",
                ).expect("Cargo and Rust macro context form a valid host identity"),
                declared_type: ::core::option::Option::None,
                payload: #facade::HostDescriptorPayload::ConfigurationRule(
                    ::std::boxed::Box::new(#facade::HostConfigurationRule {
                        sentence_kind: #facade::SentenceKind::Transition,
                        label: #label,
                        priority: #priority,
                        requires: #requires,
                        claim: ::core::option::Option::None,
                        pattern_key: #facade::ProvenanceKey::new(#rule_pattern_role, 0)
                            .expect("KRS parser roles are nonempty"),
                        subject_configuration: #facade::HostConfigurationReference {
                            key: #facade::ProvenanceKey::new(#rule_type_role, 0)
                                .expect("KRS parser roles are nonempty"),
                            configuration: #facade::HostTypeReference {
                                key: #facade::HostTypeKey(#subject_key),
                                authored_path: #subject_spelling.to_owned(),
                            },
                        },
                        result_key: #facade::ProvenanceKey::new(#rule_result_role, 0)
                            .expect("KRS parser roles are nonempty"),
                        result_configuration: #facade::HostConfigurationReference {
                            key: #facade::ProvenanceKey::new(#rule_result_type_role, 0)
                                .expect("KRS parser roles are nonempty"),
                            configuration: #facade::HostTypeReference {
                                key: #facade::HostTypeKey(#result_key),
                                authored_path: #result_spelling.to_owned(),
                            },
                        },
                        bindings: ::std::vec![#(#bindings),*],
                        subject: #subject,
                        result: #result,
                    })
                ),
                cfg: ::core::default::Default::default(),
                provenance: #provenance,
            }
        }

        #(#cfg)*
        #facade::__register_host_descriptor!(#factory);
    })
}

#[allow(clippy::too_many_lines)]
fn configuration_claim(
    env: &dyn MacroEnvironment,
    item: TokenStream,
    attribute: &krs_syntax::ClaimAttribute,
) -> syn::Result<TokenStream> {
    let claim_universal_binder_role = ProvenanceRole::ClaimUniversalBinder;
    let claim_binder_name_role = ProvenanceRole::ClaimBinderName;
    let claim_existential_binder_role = ProvenanceRole::ClaimExistentialBinder;
    let rule_requires_role = ProvenanceRole::RuleRequires;
    let claim_ensures_role = ProvenanceRole::ClaimEnsures;
    let claim_circularity_role = ProvenanceRole::ClaimCircularity;
    let claim_or_bool_role = ProvenanceRole::ClaimOrBool;
    let claim_label_role = ProvenanceRole::ClaimLabel;
    let claim_declaration_role = ProvenanceRole::ClaimDeclaration;
    let claim_modality_role = ProvenanceRole::ClaimModality;
    let rule_pattern_role = ProvenanceRole::RulePattern;
    let rule_type_role = ProvenanceRole::RuleType;
    let rule_result_role = ProvenanceRole::RuleResult;
    let rule_result_type_role = ProvenanceRole::RuleResultType;
    let claim = parse_state_claim_item(item).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let rule = claim.rule();
    let facade = env.facade_path()?;
    let mut anchors = claim
        .provenance()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    anchors.extend(
        attribute
            .provenance()
            .map_err(krs_syntax::SyntaxError::into_syn_error)?,
    );
    let fallback =
        TokenRange::for_tokens(rule.item()).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let provenance = host_provenance(env, &facade, fallback, &anchors)?;
    let nonce = expansion_nonce(env, "configuration_claim", &rule.item().sig.ident, fallback);
    let factory = format_ident!("__krs_configuration_claim_{nonce:016x}");
    let subject_key = format_ident!("__krs_claim_configuration_left_{nonce:016x}");
    let result_key = format_ident!("__krs_claim_configuration_right_{nonce:016x}");
    let cfg = call_site_cfg_attributes(&rule.item().attrs)?;
    let subject_type = call_site_path(rule.subject_type())?;
    let result_type = call_site_path(rule.result_type())?;
    let subject_spelling = spelling(rule.subject_type());
    let result_spelling = spelling(rule.result_type());

    let universal_idents = rule
        .bindings()
        .iter()
        .filter(|binding| binding.kind() == StateRuleBindingKind::Term)
        .map(|binding| binding.name().clone())
        .collect::<Vec<_>>();
    let existential_idents = claim
        .existentials()
        .iter()
        .map(|binder| binder.name().clone())
        .collect::<Vec<_>>();
    let all_idents = universal_idents
        .iter()
        .chain(&existential_idents)
        .cloned()
        .collect::<Vec<_>>();
    let mut bindings = Vec::new();
    let mut key_functions = Vec::new();
    let mut universal_metadata = Vec::new();
    let mut term_ordinal = 0_u32;
    for binding in rule.bindings() {
        let name = binding.name().to_string();
        let kind = match binding.kind() {
            StateRuleBindingKind::Term => {
                let sort = binding.term_sort().expect("term binding sort");
                let path = call_site_path(sort.sort())?;
                let ty = sort_type_tokens(&path, sort.is_dynamic());
                let key_fn =
                    format_ident!("__krs_claim_universal_sort_{nonce:016x}_{term_ordinal}");
                key_functions.push(quote! { #(#cfg)* #[doc(hidden)] fn #key_fn() -> ::core::any::TypeId { ::core::any::TypeId::of::<#ty>() } });
                let authored = sort.sort_spelling();
                let ordinal = term_ordinal;
                term_ordinal += 1;
                let sort_ref = host_sort_reference(
                    &facade,
                    ProvenanceRole::RuleBindingType,
                    ordinal,
                    &key_fn,
                    &authored,
                );
                let claim_sort_ref = host_sort_reference(
                    &facade,
                    ProvenanceRole::ClaimBinderSort,
                    ordinal,
                    &key_fn,
                    &authored,
                );
                universal_metadata.push(quote!(#facade::HostClaimBinder {
                    declaration_key: #facade::ProvenanceKey::new(#claim_universal_binder_role, #ordinal).unwrap(),
                    name_key: #facade::ProvenanceKey::new(#claim_binder_name_role, #ordinal).unwrap(),
                    name: #name.to_owned(), sort: #claim_sort_ref,
                }));
                quote!(#facade::ProtocolRuleBindingKind::Term { sort: #sort_ref })
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
    let mut existential_metadata = Vec::new();
    for (index, binder) in claim.existentials().iter().enumerate() {
        let ordinal = u32::try_from(index)
            .map_err(|_| syn::Error::new(binder.name().span(), "too many existential binders"))?;
        let binder_ordinal = term_ordinal
            .checked_add(ordinal)
            .ok_or_else(|| syn::Error::new(binder.name().span(), "too many claim binders"))?;
        let path = call_site_path(binder.sort())?;
        let key_fn = format_ident!("__krs_claim_existential_sort_{nonce:016x}_{ordinal}");
        key_functions.push(quote! { #(#cfg)* #[doc(hidden)] fn #key_fn() -> ::core::any::TypeId { ::core::any::TypeId::of::<#path>() } });
        let authored = spelling(binder.sort());
        let name = binder.name().to_string();
        let sort_ref = host_sort_reference(
            &facade,
            ProvenanceRole::ClaimBinderSort,
            binder_ordinal,
            &key_fn,
            &authored,
        );
        existential_metadata.push(quote!(#facade::HostClaimBinder {
            declaration_key: #facade::ProvenanceKey::new(#claim_existential_binder_role, #ordinal).unwrap(),
            name_key: #facade::ProvenanceKey::new(#claim_binder_name_role, #binder_ordinal).unwrap(),
            name: #name.to_owned(), sort: #sort_ref,
        }));
    }

    let mut left =
        StateRuleBuilder::new(&facade, nonce, &cfg, &universal_idents, RuleSide::Left).for_claim();
    let subject = left.expand_cells(rule.subject(), &subject_type)?;
    let mut right = StateRuleBuilder::new(
        &facade,
        nonce ^ 0x8000_0000_0000_0000,
        &cfg,
        &all_idents,
        RuleSide::Right,
    )
    .for_claim();
    right.counters.id_token = left.counters.id_token;
    right.counters.bytes_token = left.counters.bytes_token;
    right.counters.anonymous = left.counters.anonymous;
    right.counters.or_bool = left.counters.or_bool;
    let result = right.expand_cells(rule.result(), &result_type)?;
    let mut condition_builder = TermBuilder::new(
        &facade,
        nonce ^ 0x4000_0000_0000_0000,
        &cfg,
        &universal_idents,
    )
    .for_claim();
    condition_builder.id_token_ordinal = right.counters.id_token;
    condition_builder.bytes_token_ordinal = right.counters.bytes_token;
    condition_builder.or_bool_ordinal = right.counters.or_bool;
    let requires = if let Some(condition) = rule.requires() {
        let term = condition_builder.expand(condition.term().tree(), TermSide::Requires)?;
        quote!(::core::option::Option::Some(#facade::HostRuleCondition { key: #facade::ProvenanceKey::new(#rule_requires_role, 0).unwrap(), term: #term }))
    } else {
        quote!(::core::option::Option::None)
    };
    let mut ensures_builder =
        TermBuilder::new(&facade, nonce ^ 0x2000_0000_0000_0000, &cfg, &all_idents).for_claim();
    ensures_builder.id_token_ordinal = condition_builder.id_token_ordinal;
    ensures_builder.bytes_token_ordinal = condition_builder.bytes_token_ordinal;
    ensures_builder.or_bool_ordinal = condition_builder.or_bool_ordinal;
    let ensures = if let Some(condition) = claim.ensures() {
        let term = ensures_builder.expand(condition.term().tree(), TermSide::Ensures)?;
        quote!(::core::option::Option::Some(#facade::HostRuleCondition { key: #facade::ProvenanceKey::new(#claim_ensures_role, 0).unwrap(), term: #term }))
    } else {
        quote!(::core::option::Option::None)
    };
    key_functions.extend(left.terms.key_functions);
    key_functions.extend(right.terms.key_functions);
    key_functions.extend(condition_builder.key_functions);
    key_functions.extend(ensures_builder.key_functions);
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
    let label_name = attribute.label().value();
    let modality = match attribute.modality() {
        SyntaxClaimModality::AllPaths => quote!(#facade::ClaimModality::AllPaths),
        SyntaxClaimModality::OnePath => quote!(#facade::ClaimModality::OnePath),
    };
    let circularity = if attribute.circularity() {
        quote!(::core::option::Option::Some(#facade::ProvenanceKey::new(#claim_circularity_role, 0).unwrap()))
    } else {
        quote!(::core::option::Option::None)
    };
    let or_bool_count = anchors
        .iter()
        .filter(|anchor| anchor.role() == ProvenanceRole::ClaimOrBool)
        .count();
    let or_bool_keys = (0..or_bool_count).map(|index| {
        let index = u32::try_from(index).unwrap();
        quote!(#facade::ProvenanceKey::new(#claim_or_bool_role, #index).unwrap())
    });
    let mut wrapper_checks = Vec::new();
    for candidate in rule
        .reference_candidates()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?
    {
        if candidate.kind() == StateRuleReferenceKind::CellWrapper {
            let path = call_site_path(candidate.path())?;
            wrapper_checks.push(wrapper_type_check(&path));
        }
    }
    let island_import_checks = consumed_state_island_import_checks(original);
    Ok(quote! {
        #(#attrs)* #visibility #fn_token #name_ident(#(#ordinary_inputs,)* __krs_symbolic_configuration: #subject_type) -> #result_type {
            let _krs_path_check = || {
                #(#wrapper_checks)*
                #(#island_import_checks)*
            };
            #(let _ = &#universal_idents;)* let _ = __krs_symbolic_configuration;
            ::core::panic!("KRS claim declarations have no runtime implementation")
        }
        #(#cfg)* #[doc(hidden)] fn #subject_key() -> ::core::any::TypeId { ::core::any::TypeId::of::<#subject_type>() }
        #(#cfg)* #[doc(hidden)] fn #result_key() -> ::core::any::TypeId { ::core::any::TypeId::of::<#result_type>() }
        #(#key_functions)*
        #(#cfg)* #[doc(hidden)] fn #factory() -> #facade::HostDescriptor {
            #facade::HostDescriptor {
                protocol_version: #facade::ProtocolVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"), env!("CARGO_MANIFEST_DIR"), module_path!(), #name, #facade::ItemKind::Claim, "").unwrap(),
                declared_type: None,
                payload: #facade::HostDescriptorPayload::ConfigurationRule(Box::new(#facade::HostConfigurationRule {
                    sentence_kind: #facade::SentenceKind::Claim,
                    label: Some(#facade::DescriptorRuleLabel { key: #facade::ProvenanceKey::new(#claim_label_role, 0).unwrap(), name: #label_name.to_owned() }),
                    priority: None,
                    requires: #requires,
                    claim: Some(#facade::HostClaim { declaration_key: #facade::ProvenanceKey::new(#claim_declaration_role, 0).unwrap(), modality_key: #facade::ProvenanceKey::new(#claim_modality_role, 0).unwrap(), modality: #modality, circularity_key: #circularity, universals: vec![#(#universal_metadata),*], existentials: vec![#(#existential_metadata),*], ensures: #ensures, or_bool_keys: vec![#(#or_bool_keys),*] }),
                    pattern_key: #facade::ProvenanceKey::new(#rule_pattern_role, 0).unwrap(),
                    subject_configuration: #facade::HostConfigurationReference { key: #facade::ProvenanceKey::new(#rule_type_role, 0).unwrap(), configuration: #facade::HostTypeReference { key: #facade::HostTypeKey(#subject_key), authored_path: #subject_spelling.to_owned() } },
                    result_key: #facade::ProvenanceKey::new(#rule_result_role, 0).unwrap(),
                    result_configuration: #facade::HostConfigurationReference { key: #facade::ProvenanceKey::new(#rule_result_type_role, 0).unwrap(), configuration: #facade::HostTypeReference { key: #facade::HostTypeKey(#result_key), authored_path: #result_spelling.to_owned() } },
                    bindings: vec![#(#bindings),*], subject: #subject, result: #result,
                })), cfg: Default::default(), provenance: #provenance,
            }
        }
        #(#cfg)* #facade::__register_host_descriptor!(#factory);
    })
}

#[derive(Default)]
struct StateRuleCounters {
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
    id_token: u32,
    bytes_token: u32,
    anonymous: u32,
    or_bool: u32,
}

struct StateRuleBuilder<'a> {
    facade: &'a Path,
    bindings: &'a [Ident],
    side: RuleSide,
    counters: StateRuleCounters,
    terms: TermBuilder<'a>,
    claim: bool,
}

impl<'a> StateRuleBuilder<'a> {
    fn new(
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

    fn for_claim(mut self) -> Self {
        self.claim = true;
        self.terms = self.terms.for_claim();
        self
    }

    /// This side's role of a standalone `cells!`, `k!`, or `map!` role.
    fn side_role(&self, role: ProvenanceRole) -> ProvenanceRole {
        role.on_rule_side(self.side)
            .expect("state-rule keys name standalone state-macro roles")
    }

    fn key(&self, role: ProvenanceRole, ordinal: u32) -> TokenStream {
        provenance_key(self.facade, self.side_role(role), ordinal)
    }

    fn term_key(&self, role: TermRole, ordinal: u32) -> TokenStream {
        let side = match self.side {
            RuleSide::Left => TermSide::Left,
            RuleSide::Right => TermSide::Right,
        };
        provenance_key(self.facade, side.role(role), ordinal)
    }

    fn expand_cells(
        &mut self,
        cells: &krs_syntax::CellsExpression,
        owner: &Path,
    ) -> syn::Result<TokenStream> {
        let facade = self.facade;
        let mut output = Vec::new();
        for entry in cells.entries() {
            let field_ordinal = take_counter(&mut self.counters.field)?;
            let wrapper_ordinal = take_counter(&mut self.counters.wrapper)?;
            let field_key = self.key(ProvenanceRole::CellsField, field_ordinal);
            let wrapper_key = self.key(ProvenanceRole::CellsWrapper, wrapper_ordinal);
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
        let remainder = self.expand_frame(cells.remainder(), ProvenanceRole::CellsRemainder)?;
        let payload = self.key(ProvenanceRole::CellsPayload, 0);
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
            option_key(
                facade,
                self.side_role(ProvenanceRole::KSequencePayload),
                ordinal,
            )
        } else {
            quote!(::core::option::Option::None)
        };
        let dot_k_key = if sequence.notation() == KSequenceNotation::DotK {
            let ordinal = take_counter(&mut self.counters.k_tail)?;
            option_key(
                facade,
                self.side_role(ProvenanceRole::KSequenceTail),
                ordinal,
            )
        } else {
            quote!(::core::option::Option::None)
        };
        let notation = k_notation(facade, sequence.notation());
        let mut items = Vec::new();
        for item in sequence.items() {
            let ordinal = take_counter(&mut self.counters.k_item)?;
            let key = self.key(ProvenanceRole::KSequenceItem, ordinal);
            let value = self.expand_term(item.tree())?;
            items.push(quote!(#facade::ProtocolRuleKSequenceItem { key: #key, value: #value }));
        }
        let tail = if sequence.notation() == KSequenceNotation::DotK {
            quote!(#facade::ProtocolRuleFrame::Exact)
        } else {
            self.expand_frame(sequence.tail(), ProvenanceRole::KSequenceTail)?
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
            option_key(facade, self.side_role(ProvenanceRole::MapPayload), ordinal)
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
                    let key_key = self.key(ProvenanceRole::MapKey, ko);
                    let value_key = self.key(ProvenanceRole::MapValue, vo);
                    let key = self.expand_term(item.key().tree())?;
                    let value = self.expand_term(item.value().tree())?;
                    values.push(quote!(#facade::ProtocolRuleMapItem {
                        key_key: #key_key, key: #key, value_key: #value_key, value: #value,
                    }));
                }
                let remainder = self.expand_frame(remainder, ProvenanceRole::MapRemainder)?;
                quote!(#facade::ProtocolRuleMapBody::Items {
                    items: ::std::vec![#(#values),*], remainder: #remainder,
                })
            }
            MapBody::Update { base, key, value } => {
                let bo = take_counter(&mut self.counters.map_update_base)?;
                let ko = take_counter(&mut self.counters.map_key)?;
                let vo = take_counter(&mut self.counters.map_value)?;
                let base_key = self.key(ProvenanceRole::MapUpdateBase, bo);
                let key_key = self.key(ProvenanceRole::MapKey, ko);
                let value_key = self.key(ProvenanceRole::MapValue, vo);
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
        role: ProvenanceRole,
    ) -> syn::Result<TokenStream> {
        let facade = self.facade;
        let side_role = self.side_role(role);
        let counter = match role {
            ProvenanceRole::CellsRemainder => &mut self.counters.remainder,
            ProvenanceRole::KSequenceTail => &mut self.counters.k_tail,
            ProvenanceRole::MapRemainder => &mut self.counters.map_remainder,
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
                let value = bytes_token_value(literal);
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

pub(crate) fn term(input: TokenStream) -> syn::Result<TokenStream> {
    let term = parse_term_expression(input).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let expression = term.expression();
    Ok(quote! {{
        let _krs_typecheck_named_term = || {
            let _ = #expression;
        };
        ::core::panic!("`term!` has no runtime value in KRS")
    }})
}

pub(crate) fn k(env: &dyn MacroEnvironment, input: TokenStream) -> syn::Result<TokenStream> {
    let sequence =
        parse_k_sequence_expression(input).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let expressions = sequence.items().iter().map(TermExpression::expression);
    let facade = env.facade_path()?;
    Ok(quote! {{
        let _krs_typecheck_computation_items = || {
            #(let _ = #expressions;)*
        };
        #facade::builtin::KSequence::__new()
    }})
}

pub(crate) fn map(env: &dyn MacroEnvironment, input: TokenStream) -> syn::Result<TokenStream> {
    let map = parse_map_expression(input).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let mut expressions = Vec::new();
    match map.body() {
        MapBody::Empty { .. } => {}
        MapBody::Items { items, .. } => {
            for item in items {
                expressions.push(item.key().expression());
                expressions.push(item.value().expression());
            }
        }
        MapBody::Update { base, key, value } => {
            expressions.extend([base.expression(), key.expression(), value.expression()]);
        }
    }
    let facade = env.facade_path()?;
    Ok(quote! {{
        let _krs_typecheck_map_items = || {
            #(let _ = #expressions;)*
        };
        #facade::builtin::Map::__new()
    }})
}

pub(crate) fn cells(input: TokenStream) -> syn::Result<TokenStream> {
    let island_import_checks = nested_state_island_import_checks(&input);
    let cells = parse_cells_expression(input).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let mut expressions = Vec::new();
    let wrappers = cells.entries().iter().map(krs_syntax::CellsEntry::wrapper);
    for entry in cells.entries() {
        match entry.value() {
            StateTerm::Term(term) => expressions.push(term.expression()),
            StateTerm::KSequence(sequence) => {
                expressions.extend(sequence.items().iter().map(TermExpression::expression));
            }
            StateTerm::Map(map) => match map.body() {
                MapBody::Empty { .. } => {}
                MapBody::Items { items, .. } => {
                    for item in items {
                        expressions.push(item.key().expression());
                        expressions.push(item.value().expression());
                    }
                }
                MapBody::Update { base, key, value } => {
                    expressions.extend([base.expression(), key.expression(), value.expression()]);
                }
            },
        }
    }
    let wrapper_checks = wrappers.map(wrapper_type_check);
    Ok(quote! {{
        let _krs_typecheck_cells = || {
            #(#wrapper_checks)*
            #(#island_import_checks)*
            #(let _ = #expressions;)*
        };
        ::core::panic!("`cells!` has no runtime value in KRS")
    }})
}

pub(crate) fn fragment(
    env: &dyn MacroEnvironment,
    input: &TokenStream,
) -> syn::Result<TokenStream> {
    let facade = env.facade_path()?;
    let record: syn::ExprStruct = syn::parse2(input.clone())?;
    let parsed = parse_term_expression(quote!(#facade::fragment![#input]))
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let TermTree::Cell(cell) = parsed.tree() else {
        return Err(syn::Error::new(
            Span::call_site(),
            "fragment! requires `Parent { field: value, ... }`",
        ));
    };
    let owner = call_site_path(cell.owner())?;
    let expressions = record.fields.iter().map(|field| &field.expr);
    Ok(quote! {{
        let _krs_typecheck_fragment = || {
            let _ = ::core::any::TypeId::of::<#owner>();
            #(let _ = #expressions;)*
        };
        ::core::panic!("fragment! has no runtime value in KRS")
    }})
}

#[derive(Clone, Copy)]
enum TermSide {
    Left,
    Right,
    Requires,
    Ensures,
}

/// A term-node role that a [`TermSide`] maps to its provenance role.
#[derive(Clone, Copy)]
enum TermRole {
    Path,
    ApplicationHead,
    Reference,
    Literal,
    RecordFieldName,
    Wildcard,
}

impl TermSide {
    fn role(self, role: TermRole) -> ProvenanceRole {
        use ProvenanceRole as P;
        use TermRole as T;
        match (self, role) {
            (Self::Left, T::Path) => P::RuleLeftPath,
            (Self::Left, T::ApplicationHead) => P::RuleLeftApplicationHead,
            (Self::Left, T::Reference) => P::RuleLeftReference,
            (Self::Left, T::Literal) => P::RuleLeftLiteral,
            (Self::Left, T::RecordFieldName) => P::RuleLeftRecordFieldName,
            (Self::Left, T::Wildcard) => P::RuleLeftWildcard,
            (Self::Right, T::Path) => P::RuleRightPath,
            (Self::Right, T::ApplicationHead) => P::RuleRightApplicationHead,
            (Self::Right, T::Reference) => P::RuleRightReference,
            (Self::Right, T::Literal | T::Wildcard) => P::RuleRightLiteral,
            (Self::Right, T::RecordFieldName) => P::RuleRightRecordFieldName,
            (Self::Requires, T::Path) => P::RuleRequiresPath,
            (Self::Requires, T::ApplicationHead) => P::RuleRequiresApplicationHead,
            (Self::Requires, T::Reference) => P::RuleRequiresReference,
            (Self::Requires, T::Literal | T::Wildcard) => P::RuleRequiresLiteral,
            (Self::Requires, T::RecordFieldName) => P::RuleRequiresRecordFieldName,
            (Self::Ensures, T::Path) => P::ClaimEnsuresPath,
            (Self::Ensures, T::ApplicationHead) => P::ClaimEnsuresApplicationHead,
            (Self::Ensures, T::Reference) => P::ClaimEnsuresReference,
            (Self::Ensures, T::Literal | T::Wildcard) => P::ClaimEnsuresLiteral,
            (Self::Ensures, T::RecordFieldName) => P::ClaimEnsuresRecordFieldName,
        }
    }
}

#[derive(Default)]
struct TermCounters {
    path: u32,
    application: u32,
    reference: u32,
    literal: u32,
    field: u32,
    wildcard: u32,
}

struct TermBuilder<'a> {
    facade: &'a Path,
    nonce: u64,
    cfg: &'a [Attribute],
    bindings: &'a [Ident],
    counters: TermCounters,
    next_key: usize,
    key_functions: Vec<TokenStream>,
    associated_keys: bool,
    claim: bool,
    id_token_ordinal: u32,
    bytes_token_ordinal: u32,
    or_bool_ordinal: u32,
    enum_glob: Option<&'a Path>,
    enum_variant: Option<&'a Ident>,
    lexical_rule_head: bool,
    tooling_binding_references: Vec<Path>,
}

impl<'a> TermBuilder<'a> {
    fn new(facade: &'a Path, nonce: u64, cfg: &'a [Attribute], bindings: &'a [Ident]) -> Self {
        Self {
            facade,
            nonce,
            cfg,
            bindings,
            counters: TermCounters::default(),
            next_key: 0,
            key_functions: Vec::new(),
            associated_keys: false,
            claim: false,
            id_token_ordinal: 0,
            bytes_token_ordinal: 0,
            or_bool_ordinal: 0,
            enum_glob: None,
            enum_variant: None,
            lexical_rule_head: false,
            tooling_binding_references: Vec::new(),
        }
    }

    fn with_associated_keys(mut self) -> Self {
        self.associated_keys = true;
        self
    }

    fn for_claim(mut self) -> Self {
        self.claim = true;
        self
    }

    fn with_enum_glob(mut self, owner: Option<&'a Path>) -> Self {
        self.enum_glob = owner;
        self
    }

    fn with_enum_import(mut self, owner: Option<&'a Path>, variant: Option<&'a Ident>) -> Self {
        self.enum_glob = owner;
        self.enum_variant = variant;
        self
    }

    fn with_lexical_rule_head(mut self, enabled: bool) -> Self {
        self.lexical_rule_head = enabled;
        self
    }

    fn reset_side(&mut self) {
        self.counters = TermCounters::default();
    }

    #[allow(clippy::too_many_lines)]
    fn expand(&mut self, tree: &TermTree, side: TermSide) -> syn::Result<TokenStream> {
        let facade = self.facade;
        match tree {
            TermTree::Application(application) => {
                let path_ordinal = take_counter(&mut self.counters.path)?;
                let application_ordinal = take_counter(&mut self.counters.application)?;
                let path_key = provenance_key(facade, side.role(TermRole::Path), path_ordinal);
                let reference_key = provenance_key(
                    facade,
                    side.role(TermRole::ApplicationHead),
                    application_ordinal,
                );
                let target = if self.take_lexical_rule_head(application.head()) {
                    self.lexical_rule_application_target(
                        application.head(),
                        Some(application.arguments()),
                    )
                } else {
                    self.application_target(application.head())?
                };
                let mut arguments = Vec::new();
                match application.arguments() {
                    TermArguments::Positional(values) => {
                        for value in values {
                            let value = self.expand(value, side)?;
                            arguments.push(quote! {
                                #facade::HostTermArgument::Positional {
                                    value: ::std::boxed::Box::new(#value),
                                }
                            });
                        }
                    }
                    TermArguments::Named(values) => {
                        for argument in values {
                            let field_ordinal = take_counter(&mut self.counters.field)?;
                            let field_key = provenance_key(
                                facade,
                                side.role(TermRole::RecordFieldName),
                                field_ordinal,
                            );
                            let field = argument.name().to_string();
                            let value = self.expand(argument.value(), side)?;
                            arguments.push(quote! {
                                #facade::HostTermArgument::Named {
                                    key: #field_key,
                                    field: #facade::ProductionFieldId::new(#field)
                                        .expect("Rust field identifiers are valid production fields"),
                                    value: ::std::boxed::Box::new(#value),
                                }
                            });
                        }
                    }
                }
                Ok(quote! {
                    #facade::HostTerm::Application {
                        head_class: #facade::DescriptorApplicationHeadClass::Applied,
                        reference: #facade::HostApplicationReference {
                            key: #reference_key,
                            target: #target,
                        },
                        path_key: #path_key,
                        arguments: ::std::vec![#(#arguments),*],
                    }
                })
            }
            TermTree::Reference(path) => {
                let lexical_rule_head = self.take_lexical_rule_head(path);
                let path_ordinal = take_counter(&mut self.counters.path)?;
                let reference_ordinal = take_counter(&mut self.counters.reference)?;
                let path_key = provenance_key(facade, side.role(TermRole::Path), path_ordinal);
                let key = provenance_key(facade, side.role(TermRole::Reference), reference_ordinal);
                if is_bound_ident_path(path, self.bindings) {
                    self.tooling_binding_references.push(path.clone());
                    let name = spelling(path);
                    Ok(quote! {
                        #facade::HostTerm::Variable {
                            key: #key,
                            path_key: #path_key,
                            name: #name.to_owned(),
                        }
                    })
                } else {
                    let target = if lexical_rule_head {
                        self.lexical_rule_application_target(path, None)
                    } else {
                        self.application_target(path)?
                    };
                    Ok(quote! {
                        #facade::HostTerm::Application {
                            head_class: #facade::DescriptorApplicationHeadClass::BareReference,
                            reference: #facade::HostApplicationReference {
                                key: #key,
                                target: #target,
                            },
                            path_key: #path_key,
                            arguments: ::std::vec![],
                        }
                    })
                }
            }
            TermTree::Literal(literal) => {
                let ordinal = take_counter(&mut self.counters.literal)?;
                let key = provenance_key(facade, side.role(TermRole::Literal), ordinal);
                let literal = match literal {
                    TermLiteral::Integer(value) => {
                        let value = value.base10_digits().replace('_', "");
                        quote!(#facade::DescriptorLiteral::Int(#value.to_owned()))
                    }
                    TermLiteral::Boolean(value) => {
                        let value = value.value;
                        quote!(#facade::DescriptorLiteral::Bool(#value))
                    }
                };
                Ok(quote!(#facade::HostTerm::Literal { key: #key, literal: #literal }))
            }
            TermTree::Wildcard(_) => {
                if !matches!(side, TermSide::Left) {
                    return Err(syn::Error::new(
                        Span::call_site(),
                        "KRS rule results cannot contain wildcards",
                    ));
                }
                let ordinal = take_counter(&mut self.counters.wildcard)?;
                let key = provenance_key(facade, side.role(TermRole::Wildcard), ordinal);
                Ok(quote!(#facade::HostTerm::Wildcard { key: #key }))
            }
            TermTree::IdToken { literal } => {
                if !self.claim {
                    return Err(syn::Error::new(
                        literal.span(),
                        "id! is currently claim-only",
                    ));
                }
                let ordinal = self.id_token_ordinal;
                self.id_token_ordinal += 1;
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
                let ordinal = self.bytes_token_ordinal;
                self.bytes_token_ordinal += 1;
                let key = provenance_key(facade, ProvenanceRole::ClaimBytesToken, ordinal);
                let value = bytes_token_value(literal);
                Ok(
                    quote!(#facade::HostTerm::BuiltinToken { key: #key, sort: #facade::BuiltinSort::Bytes, value: #value.to_owned() }),
                )
            }
            TermTree::Anonymous { spelling, .. } => Err(syn::Error::new(
                spelling.span(),
                "anonymous! is valid only in a claim subject",
            )),
            TermTree::OrBool { arguments, .. } => {
                if !self.claim {
                    return Err(syn::Error::new(
                        Span::call_site(),
                        "or_bool! is currently claim-only",
                    ));
                }
                let ordinal = self.or_bool_ordinal;
                self.or_bool_ordinal += 1;
                let key = provenance_key(facade, ProvenanceRole::ClaimOrBool, ordinal);
                let values = arguments
                    .iter()
                    .map(|argument| self.expand(argument, side))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(quote!(#facade::HostTerm::OrBool { key: #key, arguments: vec![#(#values),*] }))
            }
            TermTree::Cell(cell) => {
                let path_ordinal = take_counter(&mut self.counters.path)?;
                let application_ordinal = take_counter(&mut self.counters.application)?;
                let _path_key = provenance_key(facade, side.role(TermRole::Path), path_ordinal);
                let key = provenance_key(
                    facade,
                    side.role(TermRole::ApplicationHead),
                    application_ordinal,
                );
                let declaration = self.cell_declaration_target(cell.owner())?;
                let mut fields = Vec::new();
                for field in cell.fields() {
                    let ordinal = take_counter(&mut self.counters.field)?;
                    let field_key =
                        provenance_key(facade, side.role(TermRole::RecordFieldName), ordinal);
                    let name = field.name().to_string();
                    let value = self.expand(field.value(), side)?;
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

    fn cell_declaration_target(&mut self, authored: &Path) -> syn::Result<TokenStream> {
        let generated = call_site_path(authored)?;
        let authored_spelling = spelling(authored);
        let key_fn = format_ident!("__krs_rule_cell_{:016x}_{}", self.nonce, self.next_key);
        self.next_key += 1;
        let cfg = self.cfg;
        self.key_functions.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #key_fn() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#generated>()
            }
        });
        let key_reference = if self.associated_keys {
            quote!(Self::#key_fn)
        } else {
            quote!(#key_fn)
        };
        let facade = self.facade;
        Ok(quote!(#facade::HostTypeReference {
            key: #facade::HostTypeKey(#key_reference),
            authored_path: #authored_spelling.to_owned(),
        }))
    }

    fn application_target(&mut self, authored: &Path) -> syn::Result<TokenStream> {
        if authored.leading_colon.is_none()
            && authored.segments.len() == 1
            && let Some(owner) = self.enum_glob
        {
            let variant = authored
                .segments
                .first()
                .expect("one-segment paths have one identifier")
                .ident
                .clone();
            if self
                .enum_variant
                .is_none_or(|imported| imported == &variant)
            {
                return self.enum_variant_target(owner, &variant);
            }
        }
        // Resolve the descriptor witness from the authored path itself so
        // qualified calls retain definition, hover, completion, and rename
        // mapping through the proc-macro expansion.
        let generated = authored;
        let authored_spelling = spelling(authored);
        let key_fn = format_ident!(
            "__krs_rule_application_{:016x}_{}",
            self.nonce,
            self.next_key
        );
        self.next_key += 1;
        let facade = self.facade;
        let cfg = self.cfg;
        let key_reference = if self.associated_keys {
            quote!(Self::#key_fn)
        } else {
            quote!(#key_fn)
        };
        if let Some((owner, variant)) = enum_variant_parts(generated) {
            let owner_spelling = spelling(&owner);
            let marker = variant_marker_function(&variant);
            self.key_functions.push(quote! {
                #(#cfg)*
                #[doc(hidden)]
                fn #key_fn() -> ::core::any::TypeId {
                    ::core::any::TypeId::of::<#owner>()
                }
            });
            Ok(quote! {
                #facade::HostApplicationTarget::EnumVariant(
                    #facade::HostEnumVariantReference::new(
                        #facade::HostTypeReference {
                            key: #facade::HostTypeKey(#key_reference),
                            authored_path: #owner_spelling.to_owned(),
                        },
                        #facade::HostTypeKey(#owner::#marker),
                        #authored_spelling,
                    )
                    .expect("qualified enum variants retain their owning enum path"),
                )
            })
        } else {
            self.key_functions.push(quote! {
                #(#cfg)*
                #[doc(hidden)]
                fn #key_fn() -> ::core::any::TypeId {
                    ::core::any::TypeId::of::<#generated>()
                }
            });
            Ok(quote! {
                #facade::HostApplicationTarget::Nominal(#facade::HostTypeReference {
                    key: #facade::HostTypeKey(#key_reference),
                    authored_path: #authored_spelling.to_owned(),
                })
            })
        }
    }

    fn take_lexical_rule_head(&mut self, path: &Path) -> bool {
        let enabled = ::core::mem::take(&mut self.lexical_rule_head);
        enabled && path.leading_colon.is_none() && path.segments.len() == 1
    }

    fn lexical_rule_application_target(
        &self,
        authored: &Path,
        arguments: Option<&TermArguments>,
    ) -> TokenStream {
        let path = authored.clone();
        let ident = authored
            .segments
            .first()
            .expect("one-segment lexical paths have one identifier");
        let selector = rule_application_selector(&ident.ident);
        let authored_spelling = spelling(authored);
        let pattern = match arguments {
            Some(TermArguments::Positional(values)) if values.is_empty() => quote!(#path(..)),
            Some(TermArguments::Positional(_) | TermArguments::Named(_)) => quote!(#path { .. }),
            None => quote!(#path),
        };
        let facade = self.facade;
        quote! {{
            let __krs_rule_application_witness: ::core::option::Option<_> =
                ::core::option::Option::None;
            if let ::core::option::Option::Some(#pattern) =
                &__krs_rule_application_witness
            {}
            #facade::__krs_resolve_rule_application::<_, #selector>(
                &__krs_rule_application_witness,
                #authored_spelling,
            )
        }}
    }

    fn enum_variant_target(
        &mut self,
        authored_owner: &Path,
        variant: &Ident,
    ) -> syn::Result<TokenStream> {
        let owner = call_site_path(authored_owner)?;
        let owner_spelling = spelling(authored_owner);
        let authored_spelling = format!("{owner_spelling}::{variant}");
        let marker = variant_marker_function(variant);
        let key_fn = format_ident!(
            "__krs_rule_application_{:016x}_{}",
            self.nonce,
            self.next_key
        );
        self.next_key += 1;
        let facade = self.facade;
        let cfg = self.cfg;
        let key_reference = if self.associated_keys {
            quote!(Self::#key_fn)
        } else {
            quote!(#key_fn)
        };
        self.key_functions.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #key_fn() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#owner>()
            }
        });
        Ok(quote! {
            #facade::HostApplicationTarget::EnumVariant(
                #facade::HostEnumVariantReference::new(
                    #facade::HostTypeReference {
                        key: #facade::HostTypeKey(#key_reference),
                        authored_path: #owner_spelling.to_owned(),
                    },
                    #facade::HostTypeKey(#owner::#marker),
                    #authored_spelling,
                )
                .expect("block-local enum imports retain their owning enum path"),
            )
        })
    }
}

fn take_counter(counter: &mut u32) -> syn::Result<u32> {
    let value = *counter;
    *counter = counter
        .checked_add(1)
        .ok_or_else(|| syn::Error::new(Span::call_site(), "too many term nodes"))?;
    Ok(value)
}

fn provenance_key(facade: &Path, role: ProvenanceRole, ordinal: u32) -> TokenStream {
    quote! {
        #facade::ProvenanceKey::new(#role, #ordinal)
            .expect("KRS parser roles are nonempty")
    }
}

fn host_sort_reference(
    facade: &Path,
    role: ProvenanceRole,
    ordinal: u32,
    key_function: &Ident,
    authored_path: &str,
) -> TokenStream {
    let key = provenance_key(facade, role, ordinal);
    quote! {
        #facade::HostSortReference {
            key: #key,
            target: #facade::HostTypeReference {
                key: #facade::HostTypeKey(#key_function),
                authored_path: #authored_path.to_owned(),
            },
        }
    }
}

fn sort_type_tokens(path: &Path, dynamic: bool) -> TokenStream {
    if dynamic {
        quote!(dyn #path)
    } else {
        quote!(#path)
    }
}

fn is_bound_ident_path(path: &Path, bindings: &[Ident]) -> bool {
    path.leading_colon.is_none()
        && path.segments.len() == 1
        && path.segments.first().is_some_and(|segment| {
            bindings
                .iter()
                .any(|binding| binding == &segment.ident.to_string())
        })
}

fn enum_variant_parts(path: &Path) -> Option<(Path, Ident)> {
    if path.segments.len() < 2 {
        return None;
    }
    let owner_segment = path.segments.iter().nth_back(1)?;
    if !owner_segment
        .ident
        .to_string()
        .chars()
        .next()
        .is_some_and(char::is_uppercase)
    {
        return None;
    }
    let variant = path.segments.last()?.ident.clone();
    let mut owner = path.clone();
    owner.segments.pop();
    if owner.segments.trailing_punct() {
        owner.segments.pop_punct();
    }
    Some((owner, variant))
}

fn variant_marker_function(variant: &Ident) -> Ident {
    format_ident!("__krs_variant_type_id_{}", variant)
}

fn reject_unexpanded_symbol(attributes: &[Attribute]) -> syn::Result<()> {
    if let Some(attribute) = attributes
        .iter()
        .find(|attribute| last_segment_entry(attribute.path()) == Some(AttributeMacro::Symbol))
    {
        return Err(syn::Error::new(
            attribute.span(),
            "#[k::symbol] must appear before the symbol-bearing KRS declaration attribute",
        ));
    }
    Ok(())
}

fn take_explicit_symbol_helper(
    attributes: &mut Vec<Attribute>,
) -> syn::Result<Option<krs_syntax::SymbolAttribute>> {
    let mut symbol = None;
    let mut retained = Vec::with_capacity(attributes.len());
    for attribute in std::mem::take(attributes) {
        if attribute.path().is_ident("__krs_explicit_symbol") {
            let parsed =
                parse_symbol_attribute(helper_tokens(&attribute, "__krs_explicit_symbol")?)
                    .map_err(krs_syntax::SyntaxError::into_syn_error)?;
            if symbol.replace(parsed).is_some() {
                return Err(syn::Error::new(
                    attribute.span(),
                    "duplicate explicit stable-symbol helper",
                ));
            }
        } else {
            retained.push(attribute);
        }
    }
    *attributes = retained;
    Ok(symbol)
}

fn helper_tokens(attribute: &Attribute, name: &str) -> syn::Result<TokenStream> {
    let Meta::List(list) = &attribute.meta else {
        return Err(syn::Error::new(
            attribute.span(),
            format!("`{name}` requires a parenthesized payload"),
        ));
    };
    Ok(list.tokens.clone())
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

fn take_strictness_helpers(
    attributes: &mut Vec<Attribute>,
) -> syn::Result<Option<StrictnessAttribute>> {
    let mut strictness = None;
    let mut retained = Vec::with_capacity(attributes.len());
    for attribute in std::mem::take(attributes) {
        let parsed = match helper_entry(attribute.path()) {
            Some(entry @ AttributeMacro::Strict) => Some(
                parse_strict_attribute(helper_tokens(&attribute, entry.name())?)
                    .map_err(krs_syntax::SyntaxError::into_syn_error)?,
            ),
            Some(entry @ AttributeMacro::Seqstrict) => Some(
                parse_seqstrict_attribute(helper_tokens(&attribute, entry.name())?)
                    .map_err(krs_syntax::SyntaxError::into_syn_error)?,
            ),
            _ => None,
        };
        if let Some(parsed) = parsed {
            if strictness.is_some() {
                return Err(syn::Error::new(
                    attribute.span(),
                    "a constructor may declare only one `strict` or `seqstrict` strategy",
                ));
            }
            strictness = Some(parsed);
        } else {
            retained.push(attribute);
        }
    }
    *attributes = retained;
    Ok(strictness)
}

fn take_alias_helper(attributes: &mut Vec<Attribute>) -> syn::Result<Option<ProvenanceAnchor>> {
    let mut alias = None;
    let mut retained = Vec::with_capacity(attributes.len());
    for attribute in std::mem::take(attributes) {
        if helper_entry(attribute.path()) == Some(AttributeMacro::Alias) {
            let tokens = match &attribute.meta {
                Meta::Path(_) => TokenStream::new(),
                Meta::List(list) => list.tokens.clone(),
                Meta::NameValue(_) => {
                    return Err(syn::Error::new(
                        attribute.span(),
                        "`alias` must use marker syntax",
                    ));
                }
            };
            parse_alias_attribute(tokens).map_err(krs_syntax::SyntaxError::into_syn_error)?;
            if alias.is_some() {
                return Err(syn::Error::new(
                    attribute.span(),
                    "a constructor may declare `alias` only once",
                ));
            }
            let marker = attribute
                .path()
                .segments
                .last()
                .expect("helper attributes have a final path segment");
            alias = Some(ProvenanceAnchor::new(
                ProvenanceRole::AliasProduction,
                0,
                TokenRange::for_tokens(&marker.ident)
                    .map_err(krs_syntax::SyntaxError::into_syn_error)?,
            ));
        } else {
            retained.push(attribute);
        }
    }
    *attributes = retained;
    Ok(alias)
}

pub(crate) fn orphan_strictness(
    entry: AttributeMacro,
    attributes: TokenStream,
    _item: TokenStream,
) -> syn::Result<TokenStream> {
    let name = entry.name();
    match entry {
        AttributeMacro::Strict => {
            parse_strict_attribute(attributes).map_err(krs_syntax::SyntaxError::into_syn_error)?;
        }
        AttributeMacro::Seqstrict => {
            parse_seqstrict_attribute(attributes)
                .map_err(krs_syntax::SyntaxError::into_syn_error)?;
        }
        _ => unreachable!(),
    }
    Err(syn::Error::new(
        Span::call_site(),
        format!("`#[k::{name}]` is a constructor helper; place `#[k::constructor(...)]` before it"),
    ))
}

#[allow(clippy::needless_pass_by_value)]
pub(crate) fn orphan_rule_helper(
    env: &dyn MacroEnvironment,
    entry: AttributeMacro,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let name = entry.name();
    if entry == AttributeMacro::Requires {
        let mut function: ItemFn = syn::parse2(item)?;
        if let Some((index, outer)) =
            function
                .attrs
                .iter()
                .enumerate()
                .find_map(|(index, attribute)| {
                    let helper = helper_entry(attribute.path())?;
                    matches!(
                        helper,
                        AttributeMacro::Equation | AttributeMacro::Simplification
                    )
                    .then_some((index, helper))
                })
        {
            function.attrs.remove(index);
            let helper: Attribute = syn::parse_quote!(#[k::requires(#attributes)]);
            function.attrs.insert(0, helper);
            return if outer == AttributeMacro::Equation {
                equation(env, TokenStream::new(), function.to_token_stream())
            } else {
                simplification(env, TokenStream::new(), function.to_token_stream())
            };
        }
    }
    Err(syn::Error::new(
        Span::call_site(),
        if matches!(entry, AttributeMacro::Exists | AttributeMacro::Ensures) {
            format!("`#[k::{name}]` is a claim helper; place `#[k::claim(...)]` before it")
        } else {
            format!("`#[k::{name}]` is a rule helper; place `#[k::rule]` before it")
        },
    ))
}

#[allow(clippy::too_many_lines)]
pub(crate) fn token(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let token_lexical_precedence_role = ProvenanceRole::TokenLexicalPrecedence;
    let token_declaration_role = ProvenanceRole::TokenDeclaration;
    let token_regex_role = ProvenanceRole::TokenRegex;
    let attribute =
        parse_token_attribute(attributes).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let declaration =
        parse_token_declaration(item).map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let facade = env.facade_path()?;
    let fallback = TokenRange::for_tokens(declaration.item())
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let nonce = expansion_nonce(env, "token", declaration.name(), fallback);
    let key_fn = format_ident!("__krs_token_type_{nonce:016x}");
    let sort_factory = format_ident!("__krs_token_sort_descriptor_{nonce:016x}");
    let grammar_factory = format_ident!("__krs_token_grammar_descriptor_{nonce:016x}");
    let cfg = call_site_cfg_attributes(&declaration.item().attrs)?;
    let item = declaration.item();
    let name = declaration.name().to_string();
    let declared = call_site_ident(declaration.name())?;

    let sort_anchor = ProvenanceAnchor::new(
        ProvenanceRole::SortDeclaration,
        0,
        TokenRange::for_tokens(declaration.name())
            .map_err(krs_syntax::SyntaxError::into_syn_error)?,
    );
    let sort_provenance = host_provenance(env, &facade, fallback, &[sort_anchor])?;
    let mut grammar_anchors = attribute
        .provenance()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    grammar_anchors.extend(
        declaration
            .provenance()
            .map_err(krs_syntax::SyntaxError::into_syn_error)?,
    );
    let grammar_provenance = host_provenance(env, &facade, fallback, &grammar_anchors)?;
    let regex = attribute.regex().value();
    let lexical_precedence = if let Some(value) = attribute.lexical_precedence() {
        quote!(::core::option::Option::Some(#facade::DescriptorLexicalPrecedence {
            key: #facade::ProvenanceKey::new(#token_lexical_precedence_role, 0)
                .expect("KRS parser roles are nonempty"),
            value: #value,
        }))
    } else {
        quote!(::core::option::Option::None)
    };
    let grammar_name = format!("__krs_grammar_token_{name}");
    let token_reference =
        host_sort_reference(&facade, ProvenanceRole::TokenDeclaration, 0, &key_fn, &name);

    Ok(quote! {
        #item

        #(#cfg)*
        #[doc(hidden)]
        fn #key_fn() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#declared>()
        }

        #(#cfg)*
        #[doc(hidden)]
        fn #sort_factory() -> #facade::HostDescriptor {
            #facade::HostDescriptor {
                protocol_version: #facade::ProtocolVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"),
                    env!("CARGO_MANIFEST_DIR"), module_path!(), #name,
                    #facade::ItemKind::Sort, "",
                ).expect("Cargo and Rust macro context form a valid token-sort identity"),
                declared_type: ::core::option::Option::Some(
                    #facade::HostDeclarationIdentity::Nominal(#facade::HostTypeKey(#key_fn)),
                ),
                payload: #facade::HostDescriptorPayload::Sort(
                    #facade::HostSortDescriptor { parents: ::std::vec![] },
                ),
                cfg: ::core::default::Default::default(),
                provenance: #sort_provenance,
            }
        }

        #(#cfg)*
        #facade::__register_host_descriptor!(#sort_factory);

        #(#cfg)*
        #[doc(hidden)]
        fn #grammar_factory() -> #facade::HostDescriptor {
            #facade::HostDescriptor {
                protocol_version: #facade::ProtocolVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"),
                    env!("CARGO_MANIFEST_DIR"), module_path!(), #grammar_name,
                    #facade::ItemKind::Grammar, "token",
                ).expect("Cargo and Rust macro context form a valid token-grammar identity"),
                declared_type: ::core::option::Option::None,
                payload: #facade::HostDescriptorPayload::Grammar(::std::boxed::Box::new(
                    #facade::HostGrammarDescriptor::Production(#facade::HostProduction {
                        key: #facade::ProvenanceKey::new(#token_declaration_role, 0)
                            .expect("KRS parser roles are nonempty"),
                        template_key: ::core::option::Option::None,
                        owner: #facade::HostProductionOwner::TokenSort {
                            sort: #token_reference,
                        },
                        result_sort: #facade::HostSortReference {
                            key: #facade::ProvenanceKey::new(#token_declaration_role, 0)
                                .expect("KRS parser roles are nonempty"),
                            target: #facade::HostTypeReference {
                                key: #facade::HostTypeKey(#key_fn),
                                authored_path: #name.to_owned(),
                            },
                        },
                        items: ::std::vec![#facade::HostProductionItem::RegexTerminal {
                            key: #facade::ProvenanceKey::new(#token_regex_role, 0)
                                .expect("KRS parser roles are nonempty"),
                            precede_regex: ::core::option::Option::None,
                            regex: #regex.to_owned(),
                            follow_regex: ::core::option::Option::None,
                        }],
                        attributes: ::std::vec![#facade::HostProductionAttribute::Token {
                            key: #facade::ProvenanceKey::new(#token_regex_role, 0)
                                .expect("KRS parser roles are nonempty"),
                            lexical_precedence: #lexical_precedence,
                        }],
                    }),
                )),
                cfg: ::core::default::Default::default(),
                provenance: #grammar_provenance,
            }
        }

        #(#cfg)*
        #facade::__register_host_descriptor!(#grammar_factory);
    })
}

#[allow(clippy::too_many_lines)]
pub(crate) fn constructors(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> syn::Result<TokenStream> {
    let subsort_declaration_role = ProvenanceRole::SubsortDeclaration;
    let attribute = parse_constructors_attribute(attributes)
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let item: ItemEnum = syn::parse2(item)?;
    let declaration = krs_syntax::EnumConstructorDeclaration::from_parts(&attribute, item)
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let facade = env.facade_path()?;
    let fallback = TokenRange::for_tokens(declaration.item())
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let nonce = expansion_nonce(env, "constructors", declaration.sort_name(), fallback);
    let cfg = call_site_cfg_attributes(&declaration.item().attrs)?;
    let enum_ident = call_site_ident(declaration.sort_name())?;
    let enum_name = declaration.sort_name().to_string();
    let enum_key = format_ident!("__krs_enum_type_{nonce:016x}");
    let sort_factory = format_ident!("__krs_enum_sort_descriptor_{nonce:016x}");
    let membership_factory = format_ident!("__krs_enum_membership_descriptor_{nonce:016x}");
    let membership_key = format_ident!("__krs_enum_membership_super_{nonce:016x}");
    // Keep the enum family's authored membership sort attached to the
    // `constructors(sort = ...)` token. This witness is the semantic bridge
    // rust-analyzer needs for definition and rename through the consumed
    // procedural-attribute argument.
    let outer_path = declaration.membership_sort();
    let outer_spelling = spelling(declaration.membership_sort());
    let family_sort_key = format_ident!("__krs_enum_family_sort_{nonce:016x}");
    let item = declaration.item();

    let mut marker_types = Vec::new();
    let mut associated_keys = Vec::new();
    let mut rule_applications = Vec::new();
    let mut variant_expansions = Vec::new();
    let mut rule_application_selectors = BTreeMap::new();
    for (index, variant) in declaration.variants().iter().enumerate() {
        let marker = format_ident!("__KrsEnumVariant_{nonce:016x}_{index}");
        let variant_key = format_ident!("__krs_enum_variant_{nonce:016x}_{index}");
        let associated = variant_marker_function(variant.name());
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
        let selector = rule_application_selector(variant.name());
        if let Some(previous) = rule_application_selectors.insert(selector, variant.name()) {
            return Err(syn::Error::new(
                variant.name().span(),
                format!(
                    "enum variants `{previous}` and `{}` collide in readable rule resolution",
                    variant.name()
                ),
            ));
        }
        let variant_name = variant.name().to_string();
        let application_path = format!("{enum_name}::{variant_name}");
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
                        .expect("generated enum variants retain their owning enum path"),
                    )
                }
            }
        });
        variant_expansions.push(expand_enum_variant(
            env,
            &facade,
            &declaration,
            variant,
            &enum_key,
            if declaration.is_open_family() {
                &family_sort_key
            } else {
                &enum_key
            },
            &variant_key,
            nonce,
            index,
            &cfg,
        )?);
    }

    let membership_name = format!("__krs_grammar_membership_{enum_name}");
    let membership_subsort = host_sort_reference(
        &facade,
        ProvenanceRole::SubsortSubSort,
        0,
        &enum_key,
        &enum_name,
    );
    let membership_supersort = host_sort_reference(
        &facade,
        ProvenanceRole::SubsortSuperSort,
        0,
        &membership_key,
        &outer_spelling,
    );

    let closed_sort = if declaration.is_open_family() {
        TokenStream::new()
    } else {
        let sort_anchors = declaration
            .sort_provenance()
            .map_err(krs_syntax::SyntaxError::into_syn_error)?;
        let sort_provenance = host_provenance(env, &facade, fallback, &sort_anchors)?;
        let membership_anchors = declaration
            .membership_provenance()
            .map_err(krs_syntax::SyntaxError::into_syn_error)?;
        let membership_provenance = host_provenance(env, &facade, fallback, &membership_anchors)?;
        quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #membership_key() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<dyn #outer_path>()
            }

            #(#cfg)*
            #[doc(hidden)]
            fn #sort_factory() -> #facade::HostDescriptor {
                #facade::HostDescriptor {
                    protocol_version: #facade::ProtocolVersion::CURRENT,
                    id: #facade::HostItemId::from_macro_context(
                        env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"),
                        env!("CARGO_MANIFEST_DIR"), module_path!(), #enum_name,
                        #facade::ItemKind::Sort, "",
                    ).expect("Cargo and Rust macro context form a valid enum-sort identity"),
                    declared_type: ::core::option::Option::Some(
                        #facade::HostDeclarationIdentity::Nominal(#facade::HostTypeKey(#enum_key)),
                    ),
                    payload: #facade::HostDescriptorPayload::Sort(
                        #facade::HostSortDescriptor { parents: ::std::vec![] },
                    ),
                    cfg: ::core::default::Default::default(),
                    provenance: #sort_provenance,
                }
            }

            #(#cfg)*
            #facade::__register_host_descriptor!(#sort_factory);

            #(#cfg)*
            #[doc(hidden)]
            fn #membership_factory() -> #facade::HostDescriptor {
                #facade::HostDescriptor {
                    protocol_version: #facade::ProtocolVersion::CURRENT,
                    id: #facade::HostItemId::from_macro_context(
                        env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"),
                        env!("CARGO_MANIFEST_DIR"), module_path!(), #membership_name,
                        #facade::ItemKind::Grammar, "enum-membership",
                    ).expect("Cargo and Rust macro context form a valid enum-membership identity"),
                    declared_type: ::core::option::Option::None,
                    payload: #facade::HostDescriptorPayload::Grammar(::std::boxed::Box::new(
                        #facade::HostGrammarDescriptor::Subsort {
                            key: #facade::ProvenanceKey::new(#subsort_declaration_role, 0)
                                .expect("KRS parser roles are nonempty"),
                            subsort: #membership_subsort,
                            supersort: #membership_supersort,
                        },
                    )),
                    cfg: ::core::default::Default::default(),
                    provenance: #membership_provenance,
                }
            }

            #(#cfg)*
            #facade::__register_host_descriptor!(#membership_factory);
        }
    };
    let open_sort_key = declaration.is_open_family().then(|| {
        quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #family_sort_key() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#outer_path>()
            }
        }
    });
    let family_grammar = expand_enum_family_grammar(
        env,
        &facade,
        &declaration,
        nonce,
        &enum_name,
        &cfg,
        fallback,
    )?;

    Ok(quote! {
        #item

        #(#cfg)*
        #[doc(hidden)]
        fn #enum_key() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#enum_ident>()
        }

        #open_sort_key

        #(#marker_types)*

        #(#cfg)*
        impl #enum_ident {
            #(#associated_keys)*
        }

        #(#rule_applications)*

        #closed_sort

        #(#variant_expansions)*
        #family_grammar
    })
}

fn enum_precedence_group_name(
    declaration: &krs_syntax::EnumConstructorDeclaration,
    ordinal: usize,
) -> String {
    declaration.precedence_groups()[ordinal].emitted_name(declaration.sort_name(), ordinal)
}

#[allow(clippy::too_many_lines)]
fn expand_enum_family_grammar(
    env: &dyn MacroEnvironment,
    facade: &Path,
    declaration: &krs_syntax::EnumConstructorDeclaration,
    nonce: u64,
    enum_name: &str,
    cfg: &[Attribute],
    fallback: TokenRange,
) -> syn::Result<TokenStream> {
    let precedence_group_reference_role = ProvenanceRole::PrecedenceGroupReference;
    let precedence_declaration_role = ProvenanceRole::PrecedenceDeclaration;
    let precedence_chain_role = ProvenanceRole::PrecedenceChain;
    let associativity_sentence_role = ProvenanceRole::AssociativitySentence;
    let associativity_group_reference_role = ProvenanceRole::AssociativityGroupReference;
    let associativity_declaration_role = ProvenanceRole::AssociativityDeclaration;
    if !declaration.is_open_family() {
        return Ok(TokenStream::new());
    }
    let mut output = Vec::new();
    if let Some(anchors) = declaration
        .precedence_provenance()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?
    {
        let provenance = host_provenance(env, facade, fallback, &anchors)?;
        let factory = format_ident!("__krs_enum_precedence_{nonce:016x}");
        let name = format!("__krs_grammar_{enum_name}_precedence");
        let mut groups = Vec::new();
        for (ordinal, _) in declaration.precedence_groups().iter().enumerate() {
            let group = enum_precedence_group_name(declaration, ordinal);
            let ordinal = u32::try_from(ordinal)
                .map_err(|_| syn::Error::new(declaration.sort_name().span(), "too many groups"))?;
            groups.push(quote! {
                #facade::DescriptorGroupReference {
                    key: #facade::ProvenanceKey::new(#precedence_group_reference_role, #ordinal)
                        .expect("KRS parser roles are nonempty"),
                    group: #facade::ProductionGroupId::new(#group)
                        .expect("generated enum groups are valid identities"),
                }
            });
        }
        let grammar = quote! {
            #facade::HostGrammarDescriptor::Precedence {
                key: #facade::ProvenanceKey::new(#precedence_declaration_role, 0)
                    .expect("KRS parser roles are nonempty"),
                chains: ::std::vec![#facade::DescriptorPrecedenceChain {
                    key: #facade::ProvenanceKey::new(#precedence_chain_role, 0)
                        .expect("KRS parser roles are nonempty"),
                    groups: ::std::vec![#(#groups),*],
                }],
            }
        };
        let descriptor = grammar_macro_descriptor(
            facade,
            &factory,
            &name,
            &format!("enum-precedence:{enum_name}"),
            &grammar,
            &provenance,
            None,
        );
        output.push(quote!(#(#cfg)* #descriptor));
    }
    if let Some(anchors) = declaration
        .associativity_provenance()
        .map_err(krs_syntax::SyntaxError::into_syn_error)?
    {
        let provenance = host_provenance(env, facade, fallback, &anchors)?;
        let factory = format_ident!("__krs_enum_associativity_{nonce:016x}");
        let name = format!("__krs_grammar_{enum_name}_associativity");
        let mut sentences = Vec::new();
        for (sentence_ordinal, (group_ordinal, group)) in declaration
            .precedence_groups()
            .iter()
            .enumerate()
            .filter(|(_, group)| group.associativity().is_some())
            .enumerate()
        {
            let group_name = enum_precedence_group_name(declaration, group_ordinal);
            let associativity = match group
                .associativity()
                .expect("filtered enum groups have explicit associativity")
            {
                SyntaxGroupAssociativity::Left => quote!(#facade::GroupAssociativity::Left),
                SyntaxGroupAssociativity::Right => quote!(#facade::GroupAssociativity::Right),
                SyntaxGroupAssociativity::NonAssociative => {
                    quote!(#facade::GroupAssociativity::NonAssociative)
                }
            };
            let ordinal = u32::try_from(sentence_ordinal)
                .map_err(|_| syn::Error::new(group.range().first(), "too many groups"))?;
            sentences.push(quote! {
                #facade::DescriptorAssociativitySentence {
                    key: #facade::ProvenanceKey::new(#associativity_sentence_role, #ordinal)
                        .expect("KRS parser roles are nonempty"),
                    associativity: #associativity,
                    groups: ::std::vec![#facade::DescriptorGroupReference {
                        key: #facade::ProvenanceKey::new(
                            #associativity_group_reference_role,
                            #ordinal,
                        ).expect("KRS parser roles are nonempty"),
                        group: #facade::ProductionGroupId::new(#group_name)
                            .expect("generated enum groups are valid identities"),
                    }],
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
        let descriptor = grammar_macro_descriptor(
            facade,
            &factory,
            &name,
            &format!("enum-associativity:{enum_name}"),
            &grammar,
            &provenance,
            None,
        );
        output.push(quote!(#(#cfg)* #descriptor));
    }
    Ok(quote!(#(#output)*))
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn expand_enum_variant(
    env: &dyn MacroEnvironment,
    facade: &Path,
    declaration: &krs_syntax::EnumConstructorDeclaration,
    variant: &krs_syntax::EnumConstructorVariant,
    enum_key: &Ident,
    result_key: &Ident,
    variant_key: &Ident,
    nonce: u64,
    index: usize,
    cfg: &[Attribute],
) -> syn::Result<TokenStream> {
    let alias_production_role = ProvenanceRole::AliasProduction;
    let constructor_syntax_role = ProvenanceRole::ConstructorSyntax;
    let constructor_declaration_role = ProvenanceRole::ConstructorDeclaration;
    let enum_name = declaration.sort_name().to_string();
    let variant_name = variant.name().to_string();
    let descriptor_factory = format_ident!("__krs_enum_constructor_{nonce:016x}_{index}");
    let grammar_factory = format_ident!("__krs_enum_grammar_{nonce:016x}_{index}");
    let disambiguator = format!("enum:{enum_name}");
    let grammar_name = format!("__krs_grammar_{enum_name}_{variant_name}");
    let anchors = declaration
        .variant_provenance(variant)
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    if variant.syntax().is_some_and(|syntax| !syntax.avoid())
        && anchors
            .iter()
            .any(|anchor| anchor.role() == ProvenanceRole::ConstructorAvoid)
    {
        return Err(syn::Error::new(
            variant.name().span(),
            "`avoid = false` is not metadata; omit the argument instead",
        ));
    }
    let fallback = TokenRange::for_tokens(variant.variant())
        .map_err(krs_syntax::SyntaxError::into_syn_error)?;
    let provenance = host_provenance(env, facade, fallback, &anchors)?;
    let grammar_provenance = host_provenance(env, facade, fallback, &anchors)?;
    let syntax = option_owned_string(variant.syntax().map(|syntax| syntax.syntax().value()));

    let mut field_key_functions = Vec::new();
    let mut fields = Vec::new();
    for (field_index, field) in variant.fields().iter().enumerate() {
        let key = format_ident!("__krs_enum_field_{nonce:016x}_{index}_{field_index}");
        let ty = if declaration.is_reference_family() && field.term_sort().is_dynamic() {
            field.term_sort().ty().to_token_stream()
        } else {
            let path = call_site_path(field.term_sort().sort())?;
            sort_type_tokens(&path, field.term_sort().is_dynamic())
        };
        let spelling = field.term_sort().sort_spelling();
        let field_name = field.name().to_string();
        field_key_functions.push(quote! {
            #(#cfg)*
            #[doc(hidden)]
            fn #key() -> ::core::any::TypeId {
                ::core::any::TypeId::of::<#ty>()
            }
        });
        let reference = type_reference(facade, &key, &spelling);
        fields.push(quote! {
            #facade::HostConstructorFieldDescriptor {
                name: #field_name.to_owned(),
                sort: #reference,
            }
        });
    }

    let items = enum_variant_production_items(facade, variant, nonce, index)?;
    let group = variant
        .precedence_group()
        .map(|ordinal| enum_precedence_group_name(declaration, ordinal));
    let mut attributes = if let Some(syntax) = variant.syntax() {
        constructor_metadata_tokens(
            facade,
            group.or_else(|| syntax.group().map(syn::LitStr::value)),
            syntax.avoid(),
            syntax.structured_format(),
        )?
    } else {
        Vec::new()
    };
    attributes.splice(
        0..0,
        production_documentation_tokens(facade, variant.documentation())?,
    );
    if variant.is_alias() {
        attributes.insert(
            0,
            quote! {
                #facade::HostProductionAttribute::Alias {
                    key: #facade::ProvenanceKey::new(#alias_production_role, 0)
                        .expect("KRS parser roles are nonempty"),
                }
            },
        );
    }
    let (strictness_key, strictness) = strictness_tokens(
        facade,
        variant.strictness(),
        variant
            .fields()
            .iter()
            .map(krs_syntax::ConstructorField::name),
        expansion_nonce(env, "enum_strictness", variant.name(), fallback),
        cfg,
    )?;
    if let Some(strictness) = strictness {
        attributes.push(strictness);
    }
    let template_key = if variant.syntax().is_some() {
        quote!(::core::option::Option::Some(
            #facade::ProvenanceKey::new(#constructor_syntax_role, 0)
                .expect("KRS parser roles are nonempty")
        ))
    } else {
        quote!(::core::option::Option::None)
    };
    let owner_path = enum_name.clone();
    let application_path = format!("{enum_name}::{variant_name}");
    let result_spelling = spelling(variant.constructor_sort());
    let result_sort = host_sort_reference(
        facade,
        ProvenanceRole::ConstructorSort,
        0,
        result_key,
        &result_spelling,
    );
    let primary = provenance_key(facade, ProvenanceRole::ConstructorDeclaration, 0);

    Ok(quote! {
        #(#field_key_functions)*
        #strictness_key

        #(#cfg)*
        #[doc(hidden)]
        fn #descriptor_factory() -> #facade::HostDescriptor {
            #facade::HostDescriptor {
                protocol_version: #facade::ProtocolVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"),
                    env!("CARGO_MANIFEST_DIR"), module_path!(), #variant_name,
                    #facade::ItemKind::Constructor, #disambiguator,
                ).expect("Cargo and Rust macro context form a valid enum-variant identity"),
                declared_type: ::core::option::Option::Some(
                    #facade::HostDeclarationIdentity::EnumVariant(
                        #facade::HostEnumVariantKey::new(
                            #facade::HostTypeKey(#enum_key),
                            #facade::HostTypeKey(#variant_key),
                        ),
                    ),
                ),
                payload: #facade::HostDescriptorPayload::Constructor(
                    #facade::HostConstructorDescriptor {
                        sort: #result_sort,
                        syntax: #syntax,
                        fields: ::std::vec![#(#fields),*],
                    },
                ),
                cfg: ::core::default::Default::default(),
                provenance: #provenance,
            }
        }

        #(#cfg)*
        #facade::__register_host_descriptor!(#descriptor_factory);

        #(#cfg)*
        #[doc(hidden)]
        fn #grammar_factory() -> #facade::HostDescriptor {
            #facade::HostDescriptor {
                protocol_version: #facade::ProtocolVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"),
                    env!("CARGO_MANIFEST_DIR"), module_path!(), #grammar_name,
                    #facade::ItemKind::Grammar, #disambiguator,
                ).expect("Cargo and Rust macro context form a valid variant-grammar identity"),
                declared_type: ::core::option::Option::None,
                payload: #facade::HostDescriptorPayload::Grammar(::std::boxed::Box::new(
                    #facade::HostGrammarDescriptor::Production(#facade::HostProduction {
                        key: #primary,
                        template_key: #template_key,
                        owner: #facade::HostProductionOwner::Constructor {
                            constructor: #facade::HostApplicationReference {
                                key: #facade::ProvenanceKey::new(#constructor_declaration_role, 0)
                                    .expect("KRS parser roles are nonempty"),
                                target: #facade::HostApplicationTarget::EnumVariant(
                                    #facade::HostEnumVariantReference::new(
                                        #facade::HostTypeReference {
                                            key: #facade::HostTypeKey(#enum_key),
                                            authored_path: #owner_path.to_owned(),
                                        },
                                        #facade::HostTypeKey(#variant_key),
                                        #application_path,
                                    ).expect("generated variant paths retain their enum owner"),
                                ),
                            },
                        },
                        result_sort: #result_sort,
                        items: ::std::vec![#(#items),*],
                        attributes: ::std::vec![#(#attributes),*],
                    }),
                )),
                cfg: ::core::default::Default::default(),
                provenance: #grammar_provenance,
            }
        }

        #(#cfg)*
        #facade::__register_host_descriptor!(#grammar_factory);
    })
}

fn enum_variant_production_items(
    facade: &Path,
    variant: &krs_syntax::EnumConstructorVariant,
    nonce: u64,
    variant_index: usize,
) -> syn::Result<Vec<TokenStream>> {
    let constructor_field_declaration_role = ProvenanceRole::ConstructorFieldDeclaration;
    let mut items = Vec::new();
    if let Some(syntax) = variant.syntax() {
        let mut field_ordinal = 0_u32;
        for (item_index, item) in syntax.syntax_template().items().iter().enumerate() {
            let item_ordinal = u32::try_from(item_index)
                .map_err(|_| syn::Error::new(variant.name().span(), "too many production items"))?;
            let item_key =
                provenance_key(facade, ProvenanceRole::ConstructorSyntaxItem, item_ordinal);
            match item {
                SyntaxTemplateItem::Terminal(text) => items.push(quote! {
                    #facade::HostProductionItem::Terminal { key: #item_key, text: #text.to_owned() }
                }),
                SyntaxTemplateItem::Field(name) => {
                    let declaration_index = variant
                        .fields()
                        .iter()
                        .position(|field| field.name() == name)
                        .ok_or_else(|| {
                            syn::Error::new(variant.name().span(), "checked field disappeared")
                        })?;
                    let declaration_ordinal = u32::try_from(declaration_index)
                        .map_err(|_| syn::Error::new(variant.name().span(), "too many fields"))?;
                    let sort_key = format_ident!(
                        "__krs_enum_field_{nonce:016x}_{variant_index}_{declaration_index}"
                    );
                    let field = &variant.fields()[declaration_index];
                    let sort = host_sort_reference(
                        facade,
                        ProvenanceRole::ConstructorFieldSort,
                        declaration_ordinal,
                        &sort_key,
                        &field.term_sort().sort_spelling(),
                    );
                    let field_key = provenance_key(
                        facade,
                        ProvenanceRole::ConstructorSyntaxFieldReference,
                        field_ordinal,
                    );
                    let declaration_key = provenance_key(
                        facade,
                        ProvenanceRole::ConstructorFieldDeclaration,
                        declaration_ordinal,
                    );
                    items.push(quote! {
                        #facade::HostProductionItem::NonTerminal {
                            key: #item_key,
                            field_key: #field_key,
                            declaration_key: ::core::option::Option::Some(#declaration_key),
                            field: #facade::ProductionFieldId::new(#name)
                                .expect("Rust fields are valid production fields"),
                            sort: ::std::boxed::Box::new(#sort),
                        }
                    });
                    field_ordinal = field_ordinal
                        .checked_add(1)
                        .ok_or_else(|| syn::Error::new(variant.name().span(), "too many fields"))?;
                }
            }
        }
    } else {
        let key = provenance_key(facade, ProvenanceRole::ConstructorDeclaration, 0);
        let terminal = variant.name().to_string();
        items.push(quote! {
            #facade::HostProductionItem::Terminal { key: #key, text: #terminal.to_owned() }
        });
        for (field_index, field) in variant.fields().iter().enumerate() {
            let ordinal = u32::try_from(field_index)
                .map_err(|_| syn::Error::new(variant.name().span(), "too many fields"))?;
            let field_key =
                provenance_key(facade, ProvenanceRole::ConstructorFieldDeclaration, ordinal);
            let sort_key =
                format_ident!("__krs_enum_field_{nonce:016x}_{variant_index}_{field_index}");
            let sort = host_sort_reference(
                facade,
                ProvenanceRole::ConstructorFieldSort,
                ordinal,
                &sort_key,
                &field.term_sort().sort_spelling(),
            );
            let name = field.name().to_string();
            items.push(quote! {
                #facade::HostProductionItem::NonTerminal {
                    key: #field_key,
                    field_key: #facade::ProvenanceKey::new(
                        #constructor_field_declaration_role, #ordinal,
                    ).expect("KRS parser roles are nonempty"),
                    declaration_key: ::core::option::Option::Some(
                        #facade::ProvenanceKey::new(#constructor_field_declaration_role, #ordinal)
                            .expect("KRS parser roles are nonempty"),
                    ),
                    field: #facade::ProductionFieldId::new(#name)
                        .expect("Rust fields are valid production fields"),
                    sort: ::std::boxed::Box::new(#sort),
                }
            });
        }
    }
    Ok(items)
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
    let provenance = host_provenance(env, &facade, fallback, &anchors)?;
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
    let supersort = host_sort_reference(
        &facade,
        ProvenanceRole::SubsortSuperSort,
        0,
        &super_key,
        &super_spelling,
    );
    let subsort = host_sort_reference(
        &facade,
        ProvenanceRole::SubsortSubSort,
        0,
        &sub_key,
        &sub_spelling,
    );

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
                protocol_version: #facade::ProtocolVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"),
                    env!("CARGO_MANIFEST_DIR"), module_path!(), #grammar_name,
                    #facade::ItemKind::Grammar, "subsort",
                ).expect("Cargo and Rust macro context form a valid subsort identity"),
                declared_type: ::core::option::Option::None,
                payload: #facade::HostDescriptorPayload::Grammar(::std::boxed::Box::new(
                    #facade::HostGrammarDescriptor::Subsort {
                        key: #facade::ProvenanceKey::new(#subsort_declaration_role, 0)
                            .expect("KRS parser roles are nonempty"),
                        subsort: #subsort,
                        supersort: #supersort,
                    },
                )),
                cfg: ::core::default::Default::default(),
                provenance: #provenance,
            }
        }

        #(#cfg)*
        #facade::__register_host_descriptor!(#factory);
    })
}

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

fn grammar_macro_descriptor(
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
    let provenance = host_provenance(env, facade, fallback, anchors)?;
    let factory = format_ident!("__krs_bracket_descriptor_{nonce:016x}_{index}");
    let grammar_name = format!("__krs_grammar_bracket_{sort_name}_{index}");
    let sort_reference =
        |role: ProvenanceRole| host_sort_reference(facade, role, 0, sort_key, sort_name);
    let mut items = Vec::new();
    let mut value_ordinal = 0_u32;
    for (item_index, item) in bracket.template().items().iter().enumerate() {
        let ordinal = u32::try_from(item_index).map_err(|_| {
            syn::Error::new(
                bracket.template().literal().span(),
                "too many bracket items",
            )
        })?;
        let key = provenance_key(facade, ProvenanceRole::BracketSyntaxItem, ordinal);
        match item {
            SyntaxTemplateItem::Terminal(text) => items.push(quote! {
                #facade::HostProductionItem::Terminal {
                    key: #key,
                    text: #text.to_owned(),
                }
            }),
            SyntaxTemplateItem::Field(_) => {
                let field_key =
                    provenance_key(facade, ProvenanceRole::BracketValueReference, value_ordinal);
                value_ordinal = value_ordinal.checked_add(1).ok_or_else(|| {
                    syn::Error::new(
                        bracket.template().literal().span(),
                        "too many bracket values",
                    )
                })?;
                let value_sort = sort_reference(ProvenanceRole::SortDeclaration);
                items.push(quote! {
                    #facade::HostProductionItem::NonTerminal {
                        key: #key,
                        field_key: #field_key,
                        declaration_key: ::core::option::Option::None,
                        field: #facade::ProductionFieldId::new("value")
                            .expect("the bracket value field is valid"),
                        sort: ::std::boxed::Box::new(#value_sort),
                    }
                });
            }
        }
    }
    let owner_sort = sort_reference(ProvenanceRole::SortDeclaration);
    let result_sort = sort_reference(ProvenanceRole::SortDeclaration);
    let disambiguator = format!("bracket:{index}");
    Ok(quote! {
        #(#cfg)*
        #[doc(hidden)]
        fn #factory() -> #facade::HostDescriptor {
            #facade::HostDescriptor {
                protocol_version: #facade::ProtocolVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"),
                    env!("CARGO_MANIFEST_DIR"), module_path!(), #grammar_name,
                    #facade::ItemKind::Grammar, #disambiguator,
                ).expect("Cargo and Rust macro context form a valid bracket identity"),
                declared_type: ::core::option::Option::None,
                payload: #facade::HostDescriptorPayload::Grammar(::std::boxed::Box::new(
                    #facade::HostGrammarDescriptor::Production(#facade::HostProduction {
                        key: #facade::ProvenanceKey::new(#bracket_declaration_role, 0)
                            .expect("KRS parser roles are nonempty"),
                        template_key: ::core::option::Option::None,
                        owner: #facade::HostProductionOwner::BracketSort { sort: #owner_sort },
                        result_sort: #result_sort,
                        items: ::std::vec![#(#items),*],
                        attributes: ::std::vec![#facade::HostProductionAttribute::Bracket {
                            key: #facade::ProvenanceKey::new(#bracket_declaration_role, 0)
                                .expect("KRS parser roles are nonempty"),
                        }],
                    }),
                )),
                cfg: ::core::default::Default::default(),
                provenance: #provenance,
            }
        }

        #(#cfg)*
        #facade::__register_host_descriptor!(#factory);
    })
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn constructor_grammar(
    facade: &Path,
    attribute: &krs_syntax::ConstructorAttribute,
    declaration: &krs_syntax::ConstructorDeclaration,
    strictness: Option<&StrictnessAttribute>,
    _declared_key: &Ident,
    sort_key: &Ident,
    nonce: u64,
    cfg: &[Attribute],
    provenance: &TokenStream,
    owner_target: &TokenStream,
    disambiguator: &str,
    functional: bool,
    total: bool,
    hook: Option<&TokenStream>,
    alias: bool,
) -> syn::Result<TokenStream> {
    let function_total_role = ProvenanceRole::FunctionTotal;
    let function_hook_role = ProvenanceRole::FunctionHook;
    let alias_production_role = ProvenanceRole::AliasProduction;
    let constructor_declaration_role = ProvenanceRole::ConstructorDeclaration;
    let name = declaration.name().to_string();
    let grammar_name = format!("__krs_grammar_{name}");
    let factory = format_ident!("__krs_constructor_grammar_{nonce:016x}");
    let result_sort_spelling = spelling(&attribute.sort);
    let result_sort = host_sort_reference(
        facade,
        ProvenanceRole::ConstructorSort,
        0,
        sort_key,
        &result_sort_spelling,
    );
    let template_key = attribute
        .syntax_template()
        .map(|_| provenance_key(facade, ProvenanceRole::ConstructorSyntax, 0));
    let template_key = if let Some(key) = template_key {
        quote!(::core::option::Option::Some(#key))
    } else {
        quote!(::core::option::Option::None)
    };
    let items = constructor_production_items(
        facade,
        attribute.syntax_template(),
        declaration.name(),
        declaration.fields(),
        nonce,
    )?;
    let (strict_key_function, strict_attribute) = strictness_tokens(
        facade,
        strictness,
        declaration
            .fields()
            .iter()
            .map(krs_syntax::ConstructorField::name),
        nonce,
        cfg,
    )?;
    let mut attributes = constructor_metadata_tokens(
        facade,
        attribute.group.as_ref().map(syn::LitStr::value),
        attribute.avoid,
        attribute.structured_format(),
    )?;
    attributes.splice(
        0..0,
        production_documentation_tokens(facade, declaration.documentation())?,
    );
    if functional {
        let function_key = if total {
            ProvenanceRole::FunctionDeclaration
        } else {
            ProvenanceRole::FunctionPartial
        };
        attributes.insert(
            0,
            quote! {
                #facade::HostProductionAttribute::Function {
                    key: #facade::ProvenanceKey::new(#function_key, 0)
                        .expect("KRS parser roles are nonempty"),
                }
            },
        );
        if total {
            attributes.insert(
                1,
                quote! {
                    #facade::HostProductionAttribute::Total {
                        key: #facade::ProvenanceKey::new(#function_total_role, 0)
                            .expect("KRS parser roles are nonempty"),
                    }
                },
            );
        }
    }
    if let Some(operation) = hook {
        let position = if total { 2 } else { 1 };
        attributes.insert(
            position,
            quote! {
                #facade::HostProductionAttribute::Hook {
                    key: #facade::ProvenanceKey::new(#function_hook_role, 0)
                        .expect("KRS parser roles are nonempty"),
                    operation: #operation,
                }
            },
        );
    }
    if alias {
        attributes.insert(
            0,
            quote! {
                #facade::HostProductionAttribute::Alias {
                    key: #facade::ProvenanceKey::new(#alias_production_role, 0)
                        .expect("KRS parser roles are nonempty"),
                }
            },
        );
    }
    if let Some(strict_attribute) = strict_attribute {
        attributes.push(strict_attribute);
    }
    let primary = provenance_key(facade, ProvenanceRole::ConstructorDeclaration, 0);

    Ok(quote! {
        #strict_key_function

        #(#cfg)*
        #[doc(hidden)]
        fn #factory() -> #facade::HostDescriptor {
            #facade::HostDescriptor {
                protocol_version: #facade::ProtocolVersion::CURRENT,
                id: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"),
                    env!("CARGO_PKG_VERSION"),
                    env!("CARGO_MANIFEST_DIR"),
                    module_path!(),
                    #grammar_name,
                    #facade::ItemKind::Grammar,
                    #disambiguator,
                )
                .expect("Cargo and Rust macro context form a valid grammar identity"),
                declared_type: ::core::option::Option::None,
                payload: #facade::HostDescriptorPayload::Grammar(::std::boxed::Box::new(
                    #facade::HostGrammarDescriptor::Production(#facade::HostProduction {
                        key: #primary,
                        template_key: #template_key,
                        owner: #facade::HostProductionOwner::Constructor {
                            constructor: #facade::HostApplicationReference {
                                key: #facade::ProvenanceKey::new(#constructor_declaration_role, 0)
                                    .expect("KRS parser roles are nonempty"),
                                target: #owner_target,
                            },
                        },
                        result_sort: #result_sort,
                        items: ::std::vec![#(#items),*],
                        attributes: ::std::vec![#(#attributes),*],
                    }),
                )),
                cfg: ::core::default::Default::default(),
                provenance: #provenance,
            }
        }

        #(#cfg)*
        #facade::__register_host_descriptor!(#factory);
    })
}

fn constructor_production_items(
    facade: &Path,
    template: Option<&krs_syntax::SyntaxTemplate>,
    name: &Ident,
    fields: &[krs_syntax::ConstructorField],
    nonce: u64,
) -> syn::Result<Vec<TokenStream>> {
    let mut items = Vec::new();
    if let Some(template) = template {
        let mut field_ordinal = 0_u32;
        for (item_index, item) in template.items().iter().enumerate() {
            let item_ordinal = u32::try_from(item_index)
                .map_err(|_| syn::Error::new(name.span(), "too many production items"))?;
            let item_key =
                provenance_key(facade, ProvenanceRole::ConstructorSyntaxItem, item_ordinal);
            match item {
                SyntaxTemplateItem::Terminal(text) => items.push(quote! {
                    #facade::HostProductionItem::Terminal {
                        key: #item_key,
                        text: #text.to_owned(),
                    }
                }),
                SyntaxTemplateItem::Field(field_name) => {
                    let declaration_index = fields
                        .iter()
                        .position(|field| field.name() == field_name)
                        .ok_or_else(|| {
                            syn::Error::new(name.span(), "checked template field disappeared")
                        })?;
                    let declaration_ordinal = u32::try_from(declaration_index)
                        .map_err(|_| syn::Error::new(name.span(), "too many constructor fields"))?;
                    let sort_key =
                        format_ident!("__krs_constructor_field_{nonce:016x}_{declaration_index}");
                    let field = &fields[declaration_index];
                    let sort_spelling = field.term_sort().sort_spelling();
                    let sort = host_sort_reference(
                        facade,
                        ProvenanceRole::ConstructorFieldSort,
                        declaration_ordinal,
                        &sort_key,
                        &sort_spelling,
                    );
                    let field_key = provenance_key(
                        facade,
                        ProvenanceRole::ConstructorSyntaxFieldReference,
                        field_ordinal,
                    );
                    let declaration_key = provenance_key(
                        facade,
                        ProvenanceRole::ConstructorFieldDeclaration,
                        declaration_ordinal,
                    );
                    items.push(quote! {
                        #facade::HostProductionItem::NonTerminal {
                            key: #item_key,
                            field_key: #field_key,
                            declaration_key: ::core::option::Option::Some(#declaration_key),
                            field: #facade::ProductionFieldId::new(#field_name)
                                .expect("Rust field identifiers are valid production fields"),
                            sort: ::std::boxed::Box::new(#sort),
                        }
                    });
                    field_ordinal = field_ordinal
                        .checked_add(1)
                        .ok_or_else(|| syn::Error::new(name.span(), "too many fields"))?;
                }
            }
        }
    } else {
        let declaration_key = provenance_key(facade, ProvenanceRole::ConstructorDeclaration, 0);
        let terminal = name.to_string();
        items.push(quote! {
            #facade::HostProductionItem::Terminal {
                key: #declaration_key,
                text: #terminal.to_owned(),
            }
        });
        for (index, field) in fields.iter().enumerate() {
            let ordinal = u32::try_from(index)
                .map_err(|_| syn::Error::new(name.span(), "too many constructor fields"))?;
            let key = provenance_key(facade, ProvenanceRole::ConstructorFieldDeclaration, ordinal);
            let sort_key = format_ident!("__krs_constructor_field_{nonce:016x}_{index}");
            let sort_spelling = field.term_sort().sort_spelling();
            let sort = host_sort_reference(
                facade,
                ProvenanceRole::ConstructorFieldSort,
                ordinal,
                &sort_key,
                &sort_spelling,
            );
            let field_name = field.name().to_string();
            items.push(quote! {
                #facade::HostProductionItem::NonTerminal {
                    key: #key,
                    field_key: #key,
                    declaration_key: ::core::option::Option::Some(#key),
                    field: #facade::ProductionFieldId::new(#field_name)
                        .expect("Rust field identifiers are valid production fields"),
                    sort: ::std::boxed::Box::new(#sort),
                }
            });
        }
    }
    Ok(items)
}

fn constructor_metadata_tokens(
    facade: &Path,
    group: Option<String>,
    avoid: bool,
    format: Option<&krs_syntax::StructuredFormat>,
) -> syn::Result<Vec<TokenStream>> {
    let constructor_group_role = ProvenanceRole::ConstructorGroup;
    let constructor_avoid_role = ProvenanceRole::ConstructorAvoid;
    let constructor_format_fragment_role = ProvenanceRole::ConstructorFormatFragment;
    let constructor_format_role = ProvenanceRole::ConstructorFormat;
    let mut attributes = Vec::new();
    if let Some(group) = group {
        attributes.push(quote! {
            #facade::HostProductionAttribute::Group {
                reference: #facade::DescriptorGroupReference {
                    key: #facade::ProvenanceKey::new(#constructor_group_role, 0)
                        .expect("KRS parser roles are nonempty"),
                    group: #facade::ProductionGroupId::new(#group)
                        .expect("checked production groups are valid identities"),
                },
            }
        });
    }
    if avoid {
        attributes.push(quote! {
            #facade::HostProductionAttribute::Avoid {
                key: #facade::ProvenanceKey::new(#constructor_avoid_role, 0)
                    .expect("KRS parser roles are nonempty"),
            }
        });
    }
    if let Some(format) = format {
        let mut fragments = Vec::new();
        for (index, fragment) in format.fragments().iter().enumerate() {
            let ordinal = u32::try_from(index).map_err(|_| {
                syn::Error::new(format.literal().span(), "too many format fragments")
            })?;
            let fragment = match fragment {
                StructuredFormatFragment::Literal(text) => {
                    quote!(#facade::FormatFragment::Literal(#text.to_owned()))
                }
                StructuredFormatFragment::Item(position) => {
                    quote!(#facade::FormatFragment::Item(#position))
                }
                StructuredFormatFragment::Newline => {
                    quote!(#facade::FormatFragment::Newline)
                }
                StructuredFormatFragment::Indent => {
                    quote!(#facade::FormatFragment::Indent)
                }
                StructuredFormatFragment::Dedent => {
                    quote!(#facade::FormatFragment::Dedent)
                }
            };
            fragments.push(quote! {
                #facade::DescriptorFormatFragment {
                    key: #facade::ProvenanceKey::new(
                        #constructor_format_fragment_role,
                        #ordinal,
                    )
                    .expect("KRS parser roles are nonempty"),
                    fragment: #fragment,
                }
            });
        }
        attributes.push(quote! {
            #facade::HostProductionAttribute::Format {
                key: #facade::ProvenanceKey::new(#constructor_format_role, 0)
                    .expect("KRS parser roles are nonempty"),
                fragments: ::std::vec![#(#fragments),*],
            }
        });
    }
    Ok(attributes)
}

fn production_documentation_tokens(
    facade: &Path,
    documentation: &[krs_syntax::ProductionDocumentation],
) -> syn::Result<Vec<TokenStream>> {
    let constructor_documentation_role = ProvenanceRole::ConstructorDocumentation;
    documentation
        .iter()
        .enumerate()
        .map(|(ordinal, documentation)| {
            let ordinal = u32::try_from(ordinal).map_err(|_| {
                syn::Error::new(documentation.literal().span(), "too many rustdoc lines")
            })?;
            let text = documentation.text();
            Ok(quote! {
                #facade::HostProductionAttribute::Documentation {
                    key: #facade::ProvenanceKey::new(#constructor_documentation_role, #ordinal)
                        .expect("KRS parser roles are nonempty"),
                    text: #text.to_owned(),
                }
            })
        })
        .collect()
}

fn strictness_tokens<'a>(
    facade: &Path,
    strictness: Option<&StrictnessAttribute>,
    fields: impl IntoIterator<Item = &'a Ident>,
    nonce: u64,
    cfg: &[Attribute],
) -> syn::Result<(TokenStream, Option<TokenStream>)> {
    let strictness_context_alias_reference_role = ProvenanceRole::StrictnessContextAliasReference;
    let strictness_field_reference_role = ProvenanceRole::StrictnessFieldReference;
    let strictness_declaration_role = ProvenanceRole::StrictnessDeclaration;
    let Some(strictness) = strictness else {
        return Ok((TokenStream::new(), None));
    };
    let available = fields
        .into_iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    let key_fn = format_ident!("__krs_strictness_result_{nonce:016x}");
    let path = call_site_path(strictness.result_sort())?;
    let spelling = spelling(strictness.result_sort());
    let result_sort = host_sort_reference(
        facade,
        ProvenanceRole::StrictnessResultSort,
        0,
        &key_fn,
        &spelling,
    );
    let result_type = if strictness.has_readable_result() {
        quote!(#path)
    } else {
        quote!(dyn #path)
    };
    let key_function = quote! {
        #(#cfg)*
        #[doc(hidden)]
        fn #key_fn() -> ::core::any::TypeId {
            ::core::any::TypeId::of::<#result_type>()
        }
    };
    let kind = match strictness.kind() {
        SyntaxStrictnessKind::Strict => quote!(#facade::StrictnessKind::Strict),
        SyntaxStrictnessKind::SeqStrict => quote!(#facade::StrictnessKind::SeqStrict),
    };
    let using = strictness.using().map_or_else(
        || Ok(quote!(::core::option::Option::None)),
        |alias| -> syn::Result<TokenStream> {
            if strictness.result_sort().segments.last().is_none_or(|segment| segment.ident != "KResult") {
                return Err(syn::Error::new(
                    strictness.result_sort().span(),
                    "a named context alias currently requires the unambiguous `KResult` result sort",
                ));
            }
            let name = alias.to_string();
            Ok(quote!(::core::option::Option::Some(#facade::HostContextAliasReference {
                key: #facade::ProvenanceKey::new(#strictness_context_alias_reference_role, 0)
                    .expect("KRS parser roles are nonempty"),
                alias: #facade::HostItemId::from_macro_context(
                    env!("CARGO_PKG_NAME"), env!("CARGO_PKG_VERSION"), env!("CARGO_MANIFEST_DIR"),
                    module_path!(), #name, #facade::ItemKind::ContextAlias, "",
                ).expect("a strictness context alias forms a valid host identity"),
            })))
        },
    )?;
    let mut selected = Vec::new();
    for (index, field) in strictness.fields().iter().enumerate() {
        let name = field.to_string();
        if !available.iter().any(|available| available == &name) {
            return Err(syn::Error::new(
                field.span(),
                "strictness field is not declared",
            ));
        }
        let ordinal = u32::try_from(index)
            .map_err(|_| syn::Error::new(field.span(), "too many strictness fields"))?;
        selected.push(quote! {
            #facade::DescriptorFieldReference {
                key: #facade::ProvenanceKey::new(#strictness_field_reference_role, #ordinal)
                    .expect("KRS parser roles are nonempty"),
                field: #facade::ProductionFieldId::new(#name)
                    .expect("Rust field identifiers are valid production fields"),
            }
        });
    }
    let attribute = quote! {
        #facade::HostProductionAttribute::Strictness {
            key: #facade::ProvenanceKey::new(#strictness_declaration_role, 0)
                .expect("KRS parser roles are nonempty"),
            kind: #kind,
            using: #using,
            fields: ::std::vec![#(#selected),*],
            result_sort: ::std::boxed::Box::new(#result_sort),
        }
    };
    Ok((key_function, Some(attribute)))
}

fn wrapper_type_check(path: &Path) -> TokenStream {
    // Type paths retain the author's lexical imports; a generated `use` path
    // instead re-roots bare `Cell`/`KCell` spellings during expansion.
    quote! {
        let _: ::core::marker::PhantomData<#path<()>> = ::core::marker::PhantomData;
    }
}

fn initializer_state_island_import_checks(cells: &[FixedCellInitializer]) -> Vec<TokenStream> {
    let mut paths = Vec::new();
    append_initializer_state_islands(cells, &mut paths);
    island_import_checks(paths)
}

fn append_initializer_state_islands(cells: &[FixedCellInitializer], output: &mut Vec<Path>) {
    for cell in cells {
        match cell.content() {
            InitializerCellContent::Leaf { .. } => {
                let expression = &cell.field().expr;
                let macro_expression = match expression {
                    syn::Expr::Macro(expression) => Some(expression),
                    syn::Expr::Call(call) => {
                        call.args.first().and_then(|argument| match argument {
                            syn::Expr::Macro(expression) => Some(expression),
                            _ => None,
                        })
                    }
                    _ => None,
                };
                if let Some(expression) = macro_expression
                    && expression.mac.path.leading_colon.is_none()
                    && expression.mac.path.segments.len() == 1
                    && matches!(
                        expression.mac.path.segments[0].ident.to_string().as_str(),
                        "k" | "map"
                    )
                {
                    output.push(expression.mac.path.clone());
                }
            }
            InitializerCellContent::Nested { children, .. } => {
                append_initializer_state_islands(children, output);
            }
        }
    }
}

fn consumed_state_island_import_checks(item: &ItemFn) -> Vec<TokenStream> {
    let mut paths = Vec::new();
    if let Some(FnArg::Typed(argument)) = item.sig.inputs.last()
        && let Pat::Macro(pattern) = &*argument.pat
    {
        append_consumed_state_island(&pattern.mac.path, &pattern.mac.tokens, &mut paths);
    }
    for statement in &item.block.stmts {
        match statement {
            syn::Stmt::Expr(syn::Expr::Macro(expression), _) => append_consumed_state_island(
                &expression.mac.path,
                &expression.mac.tokens,
                &mut paths,
            ),
            syn::Stmt::Macro(statement) => {
                append_consumed_state_island(
                    &statement.mac.path,
                    &statement.mac.tokens,
                    &mut paths,
                );
            }
            _ => {}
        }
    }
    island_import_checks(paths)
}

fn nested_state_island_import_checks(tokens: &TokenStream) -> Vec<TokenStream> {
    let mut paths = Vec::new();
    append_nested_state_islands(tokens, &mut paths);
    island_import_checks(paths)
}

fn island_import_checks(paths: Vec<Path>) -> Vec<TokenStream> {
    // Attribute/outer-macro parsing consumes these invocations before rustc
    // can credit their imports. Re-import only each consumed binding and keep
    // the necessary lint allowance on that generated item.
    let mut seen = std::collections::BTreeSet::new();
    paths
        .into_iter()
        .filter(|path| seen.insert(path.to_token_stream().to_string()))
        .map(|path| {
            quote! {
                #[allow(unused_imports)]
                use #path as _;
            }
        })
        .collect()
}

fn append_consumed_state_island(path: &Path, tokens: &TokenStream, output: &mut Vec<Path>) {
    if path
        .segments
        .last()
        .is_some_and(|segment| segment.ident == "cells")
    {
        output.push(path.clone());
        append_nested_state_islands(tokens, output);
    }
}

fn append_nested_state_islands(tokens: &TokenStream, output: &mut Vec<Path>) {
    let trees = tokens.clone().into_iter().collect::<Vec<_>>();
    for (index, tree) in trees.iter().enumerate() {
        if let TokenTree::Ident(ident) = tree
            && matches!(ident.to_string().as_str(), "k" | "map")
            && matches!(trees.get(index + 1), Some(TokenTree::Punct(bang)) if bang.as_char() == '!')
            && matches!(trees.get(index + 2), Some(TokenTree::Group(_)))
        {
            output.push(
                syn::parse2(quote!(#ident)).expect("an authored macro identifier is a Rust path"),
            );
        }
        if let TokenTree::Group(group) = tree {
            append_nested_state_islands(&group.stream(), output);
        }
    }
}

fn type_reference(facade: &Path, key_function: &Ident, authored_path: &str) -> TokenStream {
    quote! {
        #facade::HostTypeReference {
            key: #facade::HostTypeKey(#key_function),
            authored_path: #authored_path.to_owned(),
        }
    }
}

fn option_owned_string(value: Option<String>) -> TokenStream {
    if let Some(value) = value {
        quote!(::core::option::Option::Some(#value.to_owned()))
    } else {
        quote!(::core::option::Option::None)
    }
}

fn spelling(tokens: &impl ToTokens) -> String {
    tokens.to_token_stream().to_string()
}

fn call_site_path(path: &Path) -> syn::Result<Path> {
    syn::parse_str(&path.to_token_stream().to_string())
}

fn call_site_ident(ident: &Ident) -> syn::Result<Ident> {
    syn::parse_str(&ident.to_string())
}

fn call_site_cfg_attributes(attributes: &[Attribute]) -> syn::Result<Vec<Attribute>> {
    let mut parsed = Vec::new();
    for attribute in attributes
        .iter()
        .filter(|attribute| attribute.path().is_ident("cfg"))
    {
        let mut attributes =
            Attribute::parse_outer.parse_str(&attribute.to_token_stream().to_string())?;
        if attributes.len() != 1 {
            return Err(syn::Error::new(
                attribute.span(),
                "KRS could not reproduce this cfg attribute",
            ));
        }
        parsed.push(attributes.remove(0));
    }
    Ok(parsed)
}

fn expansion_nonce(
    env: &dyn MacroEnvironment,
    kind: &str,
    ident: &Ident,
    range: krs_syntax::TokenRange,
) -> u64 {
    let mut hasher = StableHasher::default();
    kind.hash(&mut hasher);
    ident.to_string().hash(&mut hasher);
    env.span_file(range.first()).hash(&mut hasher);
    let (start_line, start_column) = nonce_position(env.span_start(range.first()));
    let (end_line, end_column) = nonce_position(env.span_end(range.last()));
    start_line.hash(&mut hasher);
    start_column.hash(&mut hasher);
    end_line.hash(&mut hasher);
    end_column.hash(&mut hasher);
    hasher.finish()
}

/// The nonce's view of an environment position: the 1-based line and the
/// 0-based column that `proc_macro2::Span::start`/`end` report for a rustc
/// span, and `(0, 0)` where `proc_macro2` has no location.
///
/// The environment, not `proc_macro2`, resolves the span, so a host outside a
/// procedural macro can resolve synthesized spans (such as `Span::call_site()`
/// tokens re-quoted by `krs-syntax`) to the invocation, as rustc does. The
/// values are hashed as `u64`, which is what `usize` hashed on the 64-bit
/// hosts that run `krs-macros`, so the nonce does not depend on the pointer
/// width of the expanding host.
fn nonce_position(position: Option<SourcePosition>) -> (u64, u64) {
    position.map_or((0, 0), |position| {
        (
            u64::from(position.line),
            u64::from(position.column.saturating_sub(1)),
        )
    })
}

fn rule_application_selector(ident: &Ident) -> u64 {
    let mut selector = 0xcbf2_9ce4_8422_2325_u64;
    for byte in ident.unraw().to_string().bytes() {
        selector ^= u64::from(byte);
        selector = selector.wrapping_mul(0x0000_0100_0000_01b3);
    }
    selector
}

struct StableHasher(u64);

impl Default for StableHasher {
    fn default() -> Self {
        Self(0xcbf2_9ce4_8422_2325)
    }
}

impl Hasher for StableHasher {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, bytes: &[u8]) {
        for byte in bytes {
            self.0 ^= u64::from(*byte);
            self.0 = self.0.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{ReadableMembershipIdentity, bytes_token_value, expansion_nonce};
    use crate::environment::FixedEnvironment;

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

    #[test]
    fn expansion_nonce_depends_on_the_environment_display_file() {
        let ident: syn::Ident = syn::parse_str("Exp").unwrap();
        let tokens: proc_macro2::TokenStream = "Exp;".parse().unwrap();
        let range = krs_syntax::TokenRange::for_tokens(&tokens).unwrap();
        let first = FixedEnvironment::new("src/first.rs", "::k");
        let second = FixedEnvironment::new("src/second.rs", "::k");
        assert_eq!(
            expansion_nonce(&first, "sort", &ident, range),
            expansion_nonce(&first, "sort", &ident, range)
        );
        assert_ne!(
            expansion_nonce(&first, "sort", &ident, range),
            expansion_nonce(&second, "sort", &ident, range)
        );
    }

    #[test]
    fn byte_string_transport_is_canonical_lower_hex() {
        let literal = syn::parse_str::<syn::LitByteStr>(r#"b"\x00A\xff""#).unwrap();
        assert_eq!(bytes_token_value(&literal), r#"b"\x00\x41\xff""#);
    }
}
