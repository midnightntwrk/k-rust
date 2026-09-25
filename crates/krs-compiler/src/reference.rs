//! Deterministic readable-to-reference Rust projection.

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;
use std::path::Path;

use krs_ir::{
    BuiltinOperation, BuiltinSort, DescriptorApplicationRef, DescriptorHeadRule, DescriptorPayload,
    DescriptorTerm, DescriptorTermArgument, ListOperation, MapOperation, PackageId,
    ProtocolHeadRuleExtra, ProtocolHeadRuleResult, SemanticRule, SemanticSortRef, SemanticTheory,
    SetOperation, StableItemId,
};
use krs_syntax::surface::FunctionMacro;
use proc_macro2::{Ident, Span, TokenStream};
use quote::{ToTokens, format_ident, quote};
use syn::ext::IdentExt;
use syn::spanned::Spanned;

use crate::CollectionError;
use crate::facade::{AttributeResolver, FacadeAliases};

/// Expands the readable constructs in one Rust module to the deterministic
/// layer-2 reference surface.
///
/// Rules use whole-definition sort inference and fixed-configuration
/// completion. Readable sorts, direct memberships, constructor families,
/// syntax metadata, strictness, precedence, and explicit associativity are
/// projected through deterministic identity-preserving layer-2 carriers;
/// unrelated Rust items remain AST-equivalent.
///
/// # Errors
///
/// Returns a typed failure for invalid Rust/KRS syntax, absent or ambiguous
/// collected rules, missing inferred sorts, or an external declaration whose
/// Cargo dependency alias is not recoverable from the stable protocol.
#[allow(clippy::too_many_lines)] // The source-order traversal keeps projected items deterministic.
pub fn expand_reference_source(
    source: &str,
    facade_manifest: &Path,
    package: &PackageId,
    module_path: &[String],
    bundle: &krs_ir::DescriptorBundle,
    semantic: &SemanticTheory,
) -> Result<String, ReferenceExpansionError> {
    let mut file = syn::parse_file(source).map_err(ReferenceExpansionError::RustSyntax)?;
    let facade =
        FacadeAliases::from_manifest(facade_manifest).map_err(ReferenceExpansionError::Facade)?;
    let resolver = AttributeResolver::new(&facade, "reference source").scoped(&file.items);
    let semantic_rules = semantic
        .modules()
        .iter()
        .flat_map(krs_ir::SemanticModule::rules)
        .map(|rule| (rule.id(), rule))
        .collect::<BTreeMap<_, _>>();
    let mut rendered_names = BTreeSet::new();
    let mut needs_map_macro = false;
    let mut items = Vec::new();
    for mut item in std::mem::take(&mut file.items) {
        if let syn::Item::Use(item_use) = &mut item {
            item_use
                .attrs
                .push(syn::parse_quote!(#[allow(unused_imports)]));
        }
        if let syn::Item::Struct(item_struct) = &mut item {
            materialize_configuration_wrappers(item_struct)?;
        }
        let trailing_enum_grammar = if let syn::Item::Enum(item_enum) = &mut item {
            materialize_enum_productions(item_enum, package, module_path, bundle)?
        } else {
            Vec::new()
        };
        if let syn::Item::Impl(item_impl) = &mut item {
            materialize_initializers(item_impl)?;
        }
        let syn::Item::Macro(invocation) = &item else {
            items.push(item);
            items.extend(trailing_enum_grammar);
            continue;
        };
        if matches!(
            resolver.resolve_macro(&invocation.mac.path),
            Some(FunctionMacro::Sorts | FunctionMacro::FrameworkSorts)
        ) {
            items.extend(materialize_readable_sorts(invocation)?);
            continue;
        }
        if resolver.resolve_macro(&invocation.mac.path) != Some(FunctionMacro::Rules) {
            items.push(item);
            items.extend(trailing_enum_grammar);
            continue;
        }
        let block = krs_syntax::parse_rule_block(invocation.mac.tokens.clone())
            .map_err(ReferenceExpansionError::KrsSyntax)?;
        for clause in block.clauses() {
            let name = clause.rule().item().sig.ident.unraw().to_string();
            if !rendered_names.insert(name.clone()) {
                return Err(ReferenceExpansionError::DuplicateRule(name));
            }
            let descriptors = bundle
                .descriptors
                .iter()
                .filter(|descriptor| {
                    descriptor.id.package() == package
                        && descriptor.id.module_path() == module_path
                        && descriptor.id.item_name() == name
                        && matches!(descriptor.payload, DescriptorPayload::HeadRule(_))
                })
                .collect::<Vec<_>>();
            let [descriptor] = descriptors.as_slice() else {
                return Err(ReferenceExpansionError::RuleCoverage {
                    name,
                    found: descriptors.len(),
                });
            };
            let DescriptorPayload::HeadRule(rule) = &descriptor.payload else {
                unreachable!("the descriptor filter selected only head rules")
            };
            needs_map_macro |= !rule.extras.is_empty();
            let semantic_rule = semantic_rules.get(&descriptor.id).ok_or_else(|| {
                ReferenceExpansionError::MissingSemanticRule(Box::new(descriptor.id.clone()))
            })?;
            items.push(syn::Item::Fn(render_rule(
                clause,
                rule,
                semantic_rule,
                package,
                bundle,
            )?));
        }
    }
    if needs_map_macro {
        let map_use: syn::ItemUse = syn::parse_quote!(
            #[allow(unused_imports)]
            use k::map;
        );
        let map_key = map_use.tree.to_token_stream().to_string();
        let already_imported = contains_use_tree(&items, &map_key);
        if !already_imported {
            let insertion = items
                .iter()
                .position(|item| {
                    !matches!(item, syn::Item::Use(item_use) if item_use.tree.to_token_stream().to_string() < map_key)
                })
                .unwrap_or(items.len());
            items.insert(insertion, syn::Item::Use(map_use));
        }
    }
    file.items = items;
    let mut output =
        String::from("// @generated by `krs expand`; deterministic layer-2 reference surface.\n\n");
    output.push_str(&prettyplease::unparse(&file));
    Ok(output)
}

fn contains_use_tree(items: &[syn::Item], expected: &str) -> bool {
    items.iter().any(|item| {
        matches!(item, syn::Item::Use(item_use) if item_use.tree.to_token_stream().to_string() == expected)
    })
}

fn materialize_enum_productions(
    item: &mut syn::ItemEnum,
    package: &PackageId,
    module_path: &[String],
    bundle: &krs_ir::DescriptorBundle,
) -> Result<Vec<syn::Item>, ReferenceExpansionError> {
    if !has_attribute(&item.attrs, "constructors") {
        return Ok(Vec::new());
    }
    let declaration = krs_syntax::EnumConstructorDeclaration::from_attributed_item(item.clone())
        .map_err(ReferenceExpansionError::KrsSyntax)?;
    if !declaration.is_open_family() {
        return Ok(Vec::new());
    }
    materialize_reference_family_attribute(item, &declaration)?;
    for output_variant in &mut item.variants {
        let variant = declaration
            .variants()
            .iter()
            .find(|variant| variant.name() == &output_variant.ident)
            .ok_or_else(|| {
                ReferenceExpansionError::GeneratedRust(syn::Error::new(
                    output_variant.ident.span(),
                    "enum variant disappeared during reference projection",
                ))
            })?;
        let Some(syntax) = variant.syntax() else {
            continue;
        };
        let group_ordinal = variant.precedence_group().ok_or_else(|| {
            ReferenceExpansionError::GeneratedRust(syn::Error::new(
                output_variant.ident.span(),
                "readable enum variant has no checked precedence group",
            ))
        })?;
        let group = declaration.precedence_groups()[group_ordinal]
            .emitted_name(declaration.sort_name(), group_ordinal);
        let group = syn::LitStr::new(&group, Span::call_site());
        let template = syntax.syntax();
        let format = syntax.format().ok_or_else(|| {
            ReferenceExpansionError::GeneratedRust(syn::Error::new(
                template.span(),
                "readable enum syntax has no derived reference format",
            ))
        })?;
        let materialized: syn::Attribute = if syntax.avoid() {
            syn::parse_quote!(#[k::syntax(
                #template,
                group = #group,
                avoid = true,
                format = #format
            )])
        } else {
            syn::parse_quote!(#[k::syntax(
                #template,
                group = #group,
                format = #format
            )])
        };
        let syntax_index = output_variant
            .attrs
            .iter()
            .position(|attribute| attribute_is(attribute, "syntax"))
            .ok_or_else(|| {
                ReferenceExpansionError::GeneratedRust(syn::Error::new(
                    output_variant.ident.span(),
                    "checked enum syntax helper disappeared during reference projection",
                ))
            })?;
        output_variant
            .attrs
            .retain(|attribute| !attribute_is(attribute, "format"));
        output_variant.attrs[syntax_index] = materialized;
        materialize_reference_variant_fields(
            output_variant,
            declaration.sort_name(),
            package,
            module_path,
            bundle,
        )?;
        materialize_reference_strictness(output_variant, variant)?;
    }
    render_family_grammar(&declaration)
}

fn materialize_reference_family_attribute(
    item: &mut syn::ItemEnum,
    declaration: &krs_syntax::EnumConstructorDeclaration,
) -> Result<(), ReferenceExpansionError> {
    let sort = declaration.membership_sort();
    let constructors = item
        .attrs
        .iter()
        .position(|attribute| attribute_is(attribute, "constructors"))
        .ok_or_else(|| {
            ReferenceExpansionError::GeneratedRust(syn::Error::new(
                item.ident.span(),
                "checked constructor-family attribute disappeared during projection",
            ))
        })?;
    item.attrs[constructors] = syn::parse_quote!(#[k::constructors(sort = #sort, reference)]);
    item.attrs
        .retain(|attribute| !attribute_is(attribute, "precedence"));
    Ok(())
}

fn materialize_reference_variant_fields(
    output: &mut syn::Variant,
    family: &Ident,
    package: &PackageId,
    module_path: &[String],
    bundle: &krs_ir::DescriptorBundle,
) -> Result<(), ReferenceExpansionError> {
    let disambiguator = format!("enum:{family}");
    let descriptors = bundle
        .descriptors
        .iter()
        .filter(|descriptor| {
            descriptor.id.package() == package
                && descriptor.id.module_path() == module_path
                && output.ident == descriptor.id.item_name()
                && descriptor.id.disambiguator() == disambiguator
                && matches!(descriptor.payload, DescriptorPayload::Constructor(_))
        })
        .collect::<Vec<_>>();
    let [descriptor] = descriptors.as_slice() else {
        return Err(ReferenceExpansionError::ConstructorCoverage {
            family: family.to_string(),
            variant: output.ident.to_string(),
            found: descriptors.len(),
        });
    };
    let DescriptorPayload::Constructor(constructor) = &descriptor.payload else {
        unreachable!("the descriptor filter selected only constructors")
    };
    match &mut output.fields {
        syn::Fields::Named(fields) => {
            if fields.named.len() != constructor.fields.len() {
                return Err(ReferenceExpansionError::ConstructorFieldCoverage {
                    family: family.to_string(),
                    variant: output.ident.to_string(),
                    expected: constructor.fields.len(),
                    found: fields.named.len(),
                });
            }
            for field in &mut fields.named {
                let name = field.ident.as_ref().ok_or_else(|| {
                    ReferenceExpansionError::GeneratedRust(syn::Error::new(
                        field.span(),
                        "a checked enum record field lost its name",
                    ))
                })?;
                let descriptor_field = constructor
                    .fields
                    .iter()
                    .find(|candidate| *name == candidate.name)
                    .ok_or_else(|| ReferenceExpansionError::MissingConstructorField {
                        family: family.to_string(),
                        variant: output.ident.to_string(),
                        field: name.to_string(),
                    })?;
                let sort = descriptor_field.sort.as_ref().ok_or_else(|| {
                    ReferenceExpansionError::MissingConstructorFieldSort {
                        family: family.to_string(),
                        variant: output.ident.to_string(),
                        field: name.to_string(),
                    }
                })?;
                field.ty = syn::parse2(render_reference_term_type(
                    sort,
                    package,
                    module_path,
                    bundle,
                )?)
                .map_err(ReferenceExpansionError::GeneratedRust)?;
            }
        }
        syn::Fields::Unnamed(fields) if fields.unnamed.is_empty() => {
            if !constructor.fields.is_empty() {
                return Err(ReferenceExpansionError::ConstructorFieldCoverage {
                    family: family.to_string(),
                    variant: output.ident.to_string(),
                    expected: constructor.fields.len(),
                    found: 0,
                });
            }
        }
        syn::Fields::Unit => {
            if !constructor.fields.is_empty() {
                return Err(ReferenceExpansionError::ConstructorFieldCoverage {
                    family: family.to_string(),
                    variant: output.ident.to_string(),
                    expected: constructor.fields.len(),
                    found: 0,
                });
            }
        }
        syn::Fields::Unnamed(fields) => {
            return Err(ReferenceExpansionError::ConstructorFieldCoverage {
                family: family.to_string(),
                variant: output.ident.to_string(),
                expected: constructor.fields.len(),
                found: fields.unnamed.len(),
            });
        }
    }
    Ok(())
}

fn render_reference_term_type(
    sort: &krs_ir::DescriptorSortRef,
    package: &PackageId,
    module_path: &[String],
    bundle: &krs_ir::DescriptorBundle,
) -> Result<TokenStream, ReferenceExpansionError> {
    match sort {
        krs_ir::DescriptorSortRef::Builtin(sort) => {
            let sort = render_builtin_sort(*sort);
            Ok(quote!(k::Term<#sort>))
        }
        krs_ir::DescriptorSortRef::Declared(id)
            if id.package() == package && id.module_path() == module_path =>
        {
            if is_token_sort(id, bundle) {
                return render_reference_token_term_type(id, package);
            }
            let marker = format_ident!("{}Sort", id.item_name());
            Ok(quote!(k::Term<dyn #marker>))
        }
        krs_ir::DescriptorSortRef::Declared(id) => Err(
            ReferenceExpansionError::ExternalReferenceSort(Box::new(id.clone())),
        ),
    }
}

fn render_reference_token_term_type(
    id: &StableItemId,
    package: &PackageId,
) -> Result<TokenStream, ReferenceExpansionError> {
    let token = render_declared_path(id, package)?;
    Ok(quote!(k::Term<#token>))
}

fn is_token_sort(id: &StableItemId, bundle: &krs_ir::DescriptorBundle) -> bool {
    bundle.descriptors.iter().any(|descriptor| {
        let DescriptorPayload::Grammar(grammar) = &descriptor.payload else {
            return false;
        };
        let krs_ir::GrammarDescriptor::Production(production) = grammar.as_ref() else {
            return false;
        };
        matches!(
            &production.owner,
            krs_ir::DescriptorProductionOwner::TokenSort { sort }
                if sort.sort == krs_ir::DescriptorSortRef::Declared(id.clone())
        )
    })
}

fn materialize_reference_strictness(
    output: &mut syn::Variant,
    variant: &krs_syntax::EnumConstructorVariant,
) -> Result<(), ReferenceExpansionError> {
    let Some(strictness) = variant.strictness() else {
        return Ok(());
    };
    let indices = output
        .attrs
        .iter()
        .enumerate()
        .filter(|(_, attribute)| {
            attribute_is(attribute, "strict") || attribute_is(attribute, "seqstrict")
        })
        .map(|(index, _)| index)
        .collect::<Vec<_>>();
    let [index] = indices.as_slice() else {
        return Err(ReferenceExpansionError::GeneratedRust(syn::Error::new(
            output.ident.span(),
            "checked enum strictness helper disappeared or was duplicated during projection",
        )));
    };
    let fields = strictness.fields();
    let authored_result = strictness.result_sort();
    let result: syn::Path = if authored_result
        .segments
        .last()
        .is_some_and(|segment| segment.ident == "KResult")
    {
        syn::parse_quote!(k::KResult)
    } else {
        authored_result.clone()
    };
    output.attrs[*index] = match strictness.kind() {
        krs_syntax::StrictnessKind::Strict => {
            syn::parse_quote!(#[k::strict(sequence = [#(#fields),*], result = #result)])
        }
        krs_syntax::StrictnessKind::SeqStrict => {
            syn::parse_quote!(#[k::seqstrict(sequence = [#(#fields),*], result = #result)])
        }
    };
    Ok(())
}

fn render_family_grammar(
    declaration: &krs_syntax::EnumConstructorDeclaration,
) -> Result<Vec<syn::Item>, ReferenceExpansionError> {
    let owner = declaration.sort_name();
    let groups = declaration
        .precedence_groups()
        .iter()
        .enumerate()
        .map(|(ordinal, group)| {
            syn::parse_str::<Ident>(&group.emitted_name(owner, ordinal)).map_err(|error| {
                ReferenceExpansionError::GeneratedRust(syn::Error::new(
                    group.range().first(),
                    error,
                ))
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut items = Vec::new();
    if groups.len() >= 2 {
        let mut chain = TokenStream::new();
        for (ordinal, group) in groups.iter().enumerate() {
            if ordinal != 0 {
                chain.extend(quote!(>));
            }
            group.to_tokens(&mut chain);
        }
        let item: syn::ItemMacro = syn::parse2(quote! {
            k::precedence! { for #owner; #chain }
        })
        .map_err(ReferenceExpansionError::GeneratedRust)?;
        items.push(syn::Item::Macro(item));
    }

    let mut sentences = TokenStream::new();
    for (ordinal, group) in declaration.precedence_groups().iter().enumerate() {
        let Some(associativity) = group.associativity() else {
            continue;
        };
        let name = &groups[ordinal];
        match associativity {
            krs_syntax::GroupAssociativity::Left => {
                sentences.extend(quote!(left: #name;));
            }
            krs_syntax::GroupAssociativity::Right => {
                sentences.extend(quote!(right: #name;));
            }
            krs_syntax::GroupAssociativity::NonAssociative => {
                sentences.extend(quote!(non_associative: #name;));
            }
        }
    }
    if !sentences.is_empty() {
        let item: syn::ItemMacro = syn::parse2(quote! {
            k::associativity! { for #owner; #sentences }
        })
        .map_err(ReferenceExpansionError::GeneratedRust)?;
        items.push(syn::Item::Macro(item));
    }
    Ok(items)
}

#[allow(clippy::too_many_lines)] // Trait aliases and direct/ancestor impls are one graph projection.
fn materialize_readable_sorts(
    invocation: &syn::ItemMacro,
) -> Result<Vec<syn::Item>, ReferenceExpansionError> {
    let declaration = krs_syntax::parse_sorts_declaration(invocation.mac.tokens.clone())
        .map_err(ReferenceExpansionError::KrsSyntax)?;
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
    let mut items = Vec::new();
    for entry in declaration.entries() {
        let krs_syntax::SortsEntry::Sort(sort) = entry else {
            continue;
        };
        let name = sort.name();
        let marker = format_ident!("{name}Sort");
        let semantic_parents = sort
            .parents()
            .iter()
            .map(reference_semantic_sort_path)
            .collect::<Vec<_>>();
        let marker_parents = sort
            .parents()
            .iter()
            .map(reference_marker_path)
            .collect::<Result<Vec<_>, _>>()?;
        let brackets = sort
            .brackets()
            .iter()
            .map(|bracket| {
                let template = bracket.template().literal();
                syn::parse_quote!(#[k::bracket(#template)])
            })
            .collect::<Vec<syn::Attribute>>();
        let item_trait: syn::ItemTrait = if semantic_parents.is_empty() {
            syn::parse2(quote! {
                #[k::sort(alias = #name)]
                #(#brackets)*
                pub trait #marker {}
            })
        } else {
            syn::parse2(quote! {
                #[k::sort(alias = #name, parents = [#(#semantic_parents),*])]
                #(#brackets)*
                pub trait #marker: #(#marker_parents)+* {}
            })
        }
        .map_err(ReferenceExpansionError::GeneratedRust)?;
        let item_alias: syn::ItemType = syn::parse2(quote! {
            pub type #name = k::Term<dyn #marker>;
        })
        .map_err(ReferenceExpansionError::GeneratedRust)?;
        items.push(syn::Item::Trait(item_trait));
        items.push(syn::Item::Type(item_alias));
    }

    let mut emitted_impls = BTreeSet::new();
    for entry in declaration.entries() {
        let krs_syntax::SortsEntry::Membership(membership) = entry else {
            continue;
        };
        for member in membership.members() {
            let direct_sort = membership.supersort();
            let direct_marker = reference_marker_path(direct_sort)?;
            let direct_key = (
                direct_marker.to_token_stream().to_string(),
                member.to_token_stream().to_string(),
            );
            if emitted_impls.insert(direct_key) {
                let direct: syn::ItemImpl = syn::parse2(quote! {
                    #[k::subsort(sort = #direct_sort)]
                    impl #direct_marker for #member {}
                })
                .map_err(ReferenceExpansionError::GeneratedRust)?;
                items.push(syn::Item::Impl(direct));
            }

            let mut ancestors = Vec::new();
            push_reference_sort_ancestors(
                direct_sort,
                &local_parents,
                &mut BTreeSet::new(),
                &mut ancestors,
            );
            for ancestor in ancestors {
                let marker = reference_marker_path(&ancestor)?;
                let key = (
                    marker.to_token_stream().to_string(),
                    member.to_token_stream().to_string(),
                );
                if emitted_impls.insert(key) {
                    let implementation: syn::ItemImpl = syn::parse2(quote! {
                        impl #marker for #member {}
                    })
                    .map_err(ReferenceExpansionError::GeneratedRust)?;
                    items.push(syn::Item::Impl(implementation));
                }
            }
        }
    }
    Ok(items)
}

fn push_reference_sort_ancestors(
    sort: &syn::Path,
    local_parents: &BTreeMap<String, Vec<syn::Path>>,
    visited: &mut BTreeSet<String>,
    output: &mut Vec<syn::Path>,
) {
    let Some(name) = local_reference_sort_name(sort) else {
        return;
    };
    if !visited.insert(name.clone()) {
        return;
    }
    let Some(parents) = local_parents.get(&name) else {
        return;
    };
    for parent in parents {
        if local_reference_sort_name(parent).is_some_and(|name| local_parents.contains_key(&name)) {
            output.push(parent.clone());
            push_reference_sort_ancestors(parent, local_parents, visited, output);
        }
    }
}

fn local_reference_sort_name(path: &syn::Path) -> Option<String> {
    (path.leading_colon.is_none() && path.segments.len() == 1)
        .then(|| path.segments[0].ident.to_string())
}

fn reference_semantic_sort_path(path: &syn::Path) -> syn::Path {
    if is_framework_sort_path(path) {
        let name = &path
            .segments
            .last()
            .expect("a framework sort path has a final segment")
            .ident;
        syn::parse_quote!(k::#name)
    } else {
        path.clone()
    }
}

fn reference_marker_path(path: &syn::Path) -> Result<syn::Path, ReferenceExpansionError> {
    if is_framework_sort_path(path) {
        let name = &path
            .segments
            .last()
            .expect("a framework sort path has a final segment")
            .ident;
        let marker = format_ident!("{name}Sort");
        return Ok(syn::parse_quote!(k::#marker));
    }
    let mut marker = path.clone();
    let Some(last) = marker.segments.last_mut() else {
        return Err(ReferenceExpansionError::GeneratedRust(syn::Error::new(
            path.span(),
            "sort path has no final segment",
        )));
    };
    last.ident = format_ident!("{}Sort", last.ident);
    Ok(marker)
}

fn is_framework_sort_path(path: &syn::Path) -> bool {
    path.segments
        .last()
        .is_some_and(|segment| matches!(segment.ident.to_string().as_str(), "KItem" | "KResult"))
}

fn materialize_configuration_wrappers(
    item: &mut syn::ItemStruct,
) -> Result<(), ReferenceExpansionError> {
    if !has_attribute(&item.attrs, "configuration") && !has_attribute(&item.attrs, "cell") {
        return Ok(());
    }
    let declaration = krs_syntax::parse_configuration_declaration(item.to_token_stream())
        .map_err(ReferenceExpansionError::KrsSyntax)?;
    let syn::Fields::Named(fields) = &mut item.fields else {
        return Err(ReferenceExpansionError::GeneratedRust(syn::Error::new(
            item.fields.span(),
            "a fixed configuration must be a named-field struct",
        )));
    };
    for field in &mut fields.named {
        let Some(name) = &field.ident else {
            continue;
        };
        let cell = declaration
            .cells()
            .iter()
            .find(|cell| cell.name() == name)
            .ok_or_else(|| {
                ReferenceExpansionError::GeneratedRust(syn::Error::new(
                    name.span(),
                    "configuration field disappeared during reference projection",
                ))
            })?;
        if !cell.has_inferred_wrapper() {
            continue;
        }
        let content = field.ty.clone();
        field.ty = if cell.is_computation_cell() {
            syn::parse_quote!(k::configuration::KCell<#content>)
        } else {
            syn::parse_quote!(k::configuration::Cell<#content>)
        };
    }
    Ok(())
}

fn materialize_initializers(item: &mut syn::ItemImpl) -> Result<(), ReferenceExpansionError> {
    let mut contains_initializer = false;
    for impl_item in &mut item.items {
        let syn::ImplItem::Fn(method) = impl_item else {
            continue;
        };
        if !has_attribute(&method.attrs, "init") {
            continue;
        }
        contains_initializer = true;
        let mut parsed_method = method.clone();
        parsed_method
            .attrs
            .retain(|attribute| !attribute_is(attribute, "init"));
        let initializer = krs_syntax::parse_initializer_function(parsed_method.to_token_stream())
            .map_err(ReferenceExpansionError::KrsSyntax)?;
        for (input, variable) in method.sig.inputs.iter_mut().zip(initializer.variables()) {
            let syn::FnArg::Typed(parameter) = input else {
                continue;
            };
            if parameter
                .attrs
                .iter()
                .any(|attribute| attribute_is(attribute, "config_var"))
            {
                continue;
            }
            let name = variable.attribute().name();
            let attribute: syn::Attribute = if variable.attribute().is_main() {
                syn::parse_quote!(#[k::config_var(name = #name, main)])
            } else {
                syn::parse_quote!(#[k::config_var(name = #name)])
            };
            parameter.attrs.push(attribute);
        }
        let [syn::Stmt::Expr(syn::Expr::Struct(body), None)] = method.block.stmts.as_mut_slice()
        else {
            return Err(ReferenceExpansionError::GeneratedRust(syn::Error::new(
                method.block.span(),
                "a fixed initializer must contain exactly one struct expression",
            )));
        };
        materialize_initializer_cells(body, initializer.cells())?;
    }
    if contains_initializer && !item.attrs.iter().any(is_initializer_lint_allow) {
        item.attrs.push(syn::parse_quote!(
            #[allow(clippy::must_use_candidate, clippy::needless_pass_by_value)]
        ));
    }
    Ok(())
}

fn materialize_initializer_cells(
    body: &mut syn::ExprStruct,
    cells: &[krs_syntax::FixedCellInitializer],
) -> Result<(), ReferenceExpansionError> {
    for cell in cells {
        let field = body
            .fields
            .iter_mut()
            .find(|field| matches!(&field.member, syn::Member::Named(name) if name == cell.name()))
            .ok_or_else(|| {
                ReferenceExpansionError::GeneratedRust(syn::Error::new(
                    cell.name().span(),
                    "initializer field disappeared during reference projection",
                ))
            })?;
        qualify_reference_initializer_state_macro(&mut field.expr)?;
        match cell.content() {
            krs_syntax::InitializerCellContent::Leaf {
                computation,
                inferred_constructor: true,
                ..
            } => {
                let value = field.expr.clone();
                field.expr = if *computation {
                    syn::parse_quote!(k::configuration::KCell::new(#value))
                } else {
                    syn::parse_quote!(k::configuration::Cell::new(#value))
                };
                field.colon_token = Some(syn::token::Colon::default());
            }
            krs_syntax::InitializerCellContent::Leaf {
                inferred_constructor: false,
                ..
            } => {}
            krs_syntax::InitializerCellContent::Nested { children, .. } => {
                let syn::Expr::Struct(nested) = &mut field.expr else {
                    return Err(ReferenceExpansionError::GeneratedRust(syn::Error::new(
                        field.expr.span(),
                        "a nested fixed-cell initializer must be a struct expression",
                    )));
                };
                materialize_initializer_cells(nested, children)?;
            }
        }
    }
    Ok(())
}

fn qualify_reference_initializer_state_macro(
    expression: &mut syn::Expr,
) -> Result<(), ReferenceExpansionError> {
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
    expression.mac.path =
        syn::parse2(quote!(k::#name)).map_err(ReferenceExpansionError::GeneratedRust)?;
    Ok(())
}

fn has_attribute(attributes: &[syn::Attribute], name: &str) -> bool {
    attributes
        .iter()
        .any(|attribute| attribute_is(attribute, name))
}

fn attribute_is(attribute: &syn::Attribute, name: &str) -> bool {
    attribute
        .path()
        .segments
        .last()
        .is_some_and(|segment| segment.ident == name)
}

fn is_initializer_lint_allow(attribute: &syn::Attribute) -> bool {
    attribute_is(attribute, "allow")
        && attribute
            .meta
            .to_token_stream()
            .to_string()
            .contains("clippy :: must_use_candidate")
}

#[allow(clippy::too_many_lines)] // One rule projection keeps its two sides visibly paired.
fn render_rule(
    clause: &krs_syntax::RuleClause,
    rule: &DescriptorHeadRule,
    semantic: &SemanticRule,
    package: &PackageId,
    bundle: &krs_ir::DescriptorBundle,
) -> Result<syn::ItemFn, ReferenceExpansionError> {
    let variable_sorts = semantic
        .variables()
        .iter()
        .map(|variable| (variable.id().as_str(), variable.sort()))
        .collect::<BTreeMap<_, _>>();
    let mut reserved = rule
        .bindings
        .iter()
        .map(|binding| binding.name.clone())
        .collect::<BTreeSet<_>>();
    let tail = fresh_ident("tail", &mut reserved);
    let state = fresh_ident("state", &mut reserved);
    let mut parameters = Vec::new();
    for binding in &rule.bindings {
        let name = rust_ident(&binding.name);
        let sort = variable_sorts.get(binding.name.as_str()).ok_or_else(|| {
            ReferenceExpansionError::MissingBindingSort {
                rule: clause.rule().item().sig.ident.unraw().to_string(),
                binding: binding.name.clone(),
            }
        })?;
        let ty = render_sort_type(sort, package)?;
        parameters.push(quote!(#name: #ty));
    }

    let computation =
        render_rule_cell_field(&rule.computation_cell.cell, &rule.configuration, package)?;
    let subject = render_term(&rule.subject, true, package, bundle)?;
    let mut left_cells = vec![quote! {
        #computation: k::configuration::KCell(#subject, #tail @ ..)
    }];
    let mut right_cells = Vec::new();
    let result_items = match &rule.result {
        ProtocolHeadRuleResult::Replace(term) => {
            vec![render_term(term, false, package, bundle)?]
        }
        ProtocolHeadRuleResult::Splice(items) => items
            .iter()
            .map(|term| render_term(term, false, package, bundle))
            .collect::<Result<Vec<_>, _>>()?,
        ProtocolHeadRuleResult::Erase => Vec::new(),
    };
    right_cells.push(quote! {
        #computation: k::configuration::KCell(#(#result_items,)* ..#tail)
    });

    for (ordinal, extra) in rule.extras.iter().enumerate() {
        match extra {
            ProtocolHeadRuleExtra::HaveMap {
                cell,
                key,
                value_binding,
            } => {
                let cell = render_rule_cell_field(&cell.cell, &rule.configuration, package)?;
                let key = render_term(key, true, package, bundle)?;
                let value = rust_ident(value_binding);
                let rest = fresh_ident(&format!("rest{ordinal}"), &mut reserved);
                left_cells.push(quote! {
                    #cell: k::configuration::Cell(map![#key -> #value, #rest @ ..])
                });
            }
            ProtocolHeadRuleExtra::UpdateMap {
                cell,
                base_binding,
                update,
            } => {
                let cell = render_rule_cell_field(&cell.cell, &rule.configuration, package)?;
                let base = rust_ident(base_binding);
                let update = render_term(update, false, package, bundle)?;
                left_cells.push(quote!(#cell: k::configuration::Cell(#base)));
                right_cells.push(quote! {
                    #cell: k::configuration::Cell(#update)
                });
            }
            ProtocolHeadRuleExtra::RewriteCell {
                cell,
                before,
                after,
                ..
            } => {
                let cell = render_rule_cell_field(&cell.cell, &rule.configuration, package)?;
                let before = render_term(before, true, package, bundle)?;
                let after = render_term(after, false, package, bundle)?;
                left_cells.push(quote! {
                    #cell: k::configuration::Cell(#before)
                });
                right_cells.push(quote! {
                    #cell: k::configuration::Cell(#after)
                });
            }
        }
    }
    let configuration = render_declared_path(&rule.configuration, package)?;
    let name = &clause.rule().item().sig.ident;
    let label = syn::LitStr::new(
        rule.label
            .as_ref()
            .map_or_else(
                || name.unraw().to_string().replace('_', "-"),
                |label| label.name.clone(),
            )
            .as_str(),
        Span::call_site(),
    );
    let attrs = &clause.rule().item().attrs;
    let rule_attribute = if rule
        .priority
        .as_ref()
        .is_some_and(|priority| priority.key.role() == "rule_owise" && priority.value == 200)
    {
        quote!(#[k::rule(owise, label = #label)])
    } else {
        quote!(#[k::rule(label = #label)])
    };
    syn::parse2(quote! {
        #(#attrs)*
        #rule_attribute
        pub fn #name(
            #(#parameters,)*
            k::cells! {
                #(#left_cells,)*
                #state @ ..
            }: #configuration,
        ) -> #configuration {
            k::cells! {
                #(#right_cells,)*
                ..#state
            }
        }
    })
    .map_err(ReferenceExpansionError::GeneratedRust)
}

fn render_rule_cell_field(
    cell: &krs_ir::DescriptorCellIdentity,
    configuration: &StableItemId,
    package: &PackageId,
) -> Result<TokenStream, ReferenceExpansionError> {
    let field = rust_ident(&cell.field);
    if &cell.owner == configuration {
        return Ok(quote!(#field));
    }
    let owner = render_declared_path(&cell.owner, package)?;
    Ok(quote!(#owner::#field))
}

#[allow(clippy::too_many_lines)] // Exhaustive rendering mirrors the closed descriptor term sum.
fn render_term(
    term: &DescriptorTerm,
    pattern: bool,
    package: &PackageId,
    bundle: &krs_ir::DescriptorBundle,
) -> Result<TokenStream, ReferenceExpansionError> {
    match term {
        DescriptorTerm::Variable { name, .. } => {
            let name = rust_ident(name);
            Ok(quote!(#name))
        }
        DescriptorTerm::Application {
            reference,
            head_class,
            arguments,
            ..
        } => {
            let head = match &reference.application {
                DescriptorApplicationRef::Declared(id) => render_declared_application(id, package)?,
                DescriptorApplicationRef::Builtin(operation) => {
                    render_builtin_operation(*operation)
                }
                DescriptorApplicationRef::Map(operation) => render_map_operation(*operation)?,
                DescriptorApplicationRef::List(operation) => render_list_operation(*operation),
                DescriptorApplicationRef::Set(operation) => render_set_operation(*operation),
            };
            if arguments.is_empty()
                && matches!(
                    head_class,
                    krs_ir::DescriptorApplicationHeadClass::BareReference
                )
            {
                return Ok(head);
            }
            let positional = arguments
                .iter()
                .filter_map(|argument| match argument {
                    DescriptorTermArgument::Positional { value } => Some(value),
                    DescriptorTermArgument::Named { .. } => None,
                })
                .collect::<Vec<_>>();
            if positional.len() == arguments.len() {
                let values = positional
                    .into_iter()
                    .map(|value| render_term(value, pattern, package, bundle))
                    .collect::<Result<Vec<_>, _>>()?;
                return Ok(quote!(#head(#(#values),*)));
            }
            let DescriptorApplicationRef::Declared(id) = &reference.application else {
                return Err(ReferenceExpansionError::NamedBuiltinApplication);
            };
            let descriptor = bundle
                .descriptors
                .iter()
                .find(|descriptor| descriptor.id == *id)
                .ok_or_else(|| ReferenceExpansionError::MissingDeclaration(Box::new(id.clone())))?;
            let DescriptorPayload::Constructor(constructor) = &descriptor.payload else {
                return Err(ReferenceExpansionError::NamedNonConstructor(Box::new(
                    id.clone(),
                )));
            };
            let mut supplied = BTreeMap::new();
            for argument in arguments {
                let DescriptorTermArgument::Named { field, value, .. } = argument else {
                    return Err(ReferenceExpansionError::MixedApplicationArguments);
                };
                if supplied.insert(field.as_str(), value).is_some() {
                    return Err(ReferenceExpansionError::DuplicateApplicationField {
                        id: Box::new(id.clone()),
                        field: field.as_str().to_owned(),
                    });
                }
            }
            let mut values = Vec::with_capacity(constructor.fields.len());
            for field in &constructor.fields {
                if let Some(value) = supplied.remove(field.name.as_str()) {
                    values.push(render_term(value, pattern, package, bundle)?);
                } else if pattern {
                    values.push(quote!(_));
                } else {
                    return Err(ReferenceExpansionError::MissingApplicationField {
                        id: Box::new(id.clone()),
                        field: field.name.clone(),
                    });
                }
            }
            if let Some(field) = supplied.keys().next() {
                return Err(ReferenceExpansionError::UnknownApplicationField {
                    id: Box::new(id.clone()),
                    field: (*field).to_owned(),
                });
            }
            Ok(quote!(#head(#(#values),*)))
        }
        DescriptorTerm::Literal { literal, .. } => match literal {
            krs_ir::DescriptorLiteral::Int(value) => value
                .parse::<TokenStream>()
                .map_err(|_| ReferenceExpansionError::InvalidLiteral(value.clone())),
            krs_ir::DescriptorLiteral::Bool(value) => Ok(quote!(#value)),
        },
        DescriptorTerm::Wildcard { .. } => Ok(quote!(_)),
        DescriptorTerm::BuiltinToken { sort, value, .. } => match sort {
            BuiltinSort::Id => {
                let value = syn::LitStr::new(value, Span::call_site());
                Ok(quote!(k::id!(#value)))
            }
            BuiltinSort::Bytes => {
                let value = decode_bytes_token(value)
                    .ok_or_else(|| ReferenceExpansionError::InvalidLiteral(value.clone()))?;
                let value = syn::LitByteStr::new(&value, Span::call_site());
                Ok(quote!(k::bytes!(#value)))
            }
            _ => Err(ReferenceExpansionError::UnsupportedBuiltinToken(*sort)),
        },
        DescriptorTerm::Anonymous { sort, spelling, .. } => {
            let sort = render_descriptor_sort(&sort.sort, package)?;
            let spelling = syn::LitStr::new(spelling, Span::call_site());
            Ok(quote!(k::anonymous!(#sort, #spelling)))
        }
        DescriptorTerm::OrBool { arguments, .. } => {
            let arguments = arguments
                .iter()
                .map(|term| render_term(term, pattern, package, bundle))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(quote!(k::or_bool!(#(#arguments),*)))
        }
        DescriptorTerm::Cell {
            declaration,
            fields,
            ..
        } => {
            let owner = render_declared_path(declaration, package)?;
            let fields = fields
                .iter()
                .map(|field| {
                    let name = rust_ident(field.field.as_str());
                    let value = render_term(&field.value, pattern, package, bundle)?;
                    Ok(quote!(#name: #value))
                })
                .collect::<Result<Vec<_>, ReferenceExpansionError>>()?;
            Ok(quote!(k::fragment![#owner { #(#fields),* }]))
        }
    }
}

fn decode_bytes_token(value: &str) -> Option<Vec<u8>> {
    let body = value.strip_prefix("b\"")?.strip_suffix('"')?;
    if body.len() % 4 != 0 {
        return None;
    }
    body.as_bytes()
        .chunks(4)
        .map(|chunk| {
            (chunk[0] == b'\\' && chunk[1] == b'x')
                .then(|| u8::from_str_radix(std::str::from_utf8(&chunk[2..]).ok()?, 16).ok())
                .flatten()
        })
        .collect()
}

fn render_sort_type(
    sort: &SemanticSortRef,
    package: &PackageId,
) -> Result<TokenStream, ReferenceExpansionError> {
    match sort {
        SemanticSortRef::Declared(id) => render_declared_path(id, package),
        SemanticSortRef::Builtin(sort) => {
            let sort = render_builtin_sort(*sort);
            Ok(quote!(k::Term<#sort>))
        }
    }
}

fn render_descriptor_sort(
    sort: &krs_ir::DescriptorSortRef,
    package: &PackageId,
) -> Result<TokenStream, ReferenceExpansionError> {
    match sort {
        krs_ir::DescriptorSortRef::Declared(id) => render_declared_path(id, package),
        krs_ir::DescriptorSortRef::Builtin(sort) => Ok(render_builtin_sort(*sort)),
    }
}

fn render_declared_application(
    id: &StableItemId,
    package: &PackageId,
) -> Result<TokenStream, ReferenceExpansionError> {
    let base = render_declared_path(id, package)?;
    let Some(owner) = id.disambiguator().strip_prefix("enum:") else {
        return Ok(base);
    };
    let owner = rust_ident(owner);
    let variant = rust_ident(id.item_name());
    let path = render_local_path(id, package, &[owner, variant])?;
    Ok(quote!(#path))
}

fn render_declared_path(
    id: &StableItemId,
    package: &PackageId,
) -> Result<TokenStream, ReferenceExpansionError> {
    let item = rust_ident(id.item_name());
    let path = render_local_path(id, package, &[item])?;
    Ok(quote!(#path))
}

fn render_local_path(
    id: &StableItemId,
    package: &PackageId,
    suffix: &[Ident],
) -> Result<syn::Path, ReferenceExpansionError> {
    if id.package() != package {
        return Err(ReferenceExpansionError::ExternalDeclaration(Box::new(
            id.clone(),
        )));
    }
    let mut path: syn::Path = syn::parse_quote!(crate);
    path.segments.extend(
        id.module_path()
            .iter()
            .map(|segment| syn::PathSegment::from(rust_ident(segment))),
    );
    path.segments
        .extend(suffix.iter().cloned().map(syn::PathSegment::from));
    Ok(path)
}

fn render_builtin_sort(sort: BuiltinSort) -> TokenStream {
    let name = match sort {
        BuiltinSort::KSequence => format_ident!("KSequence"),
        BuiltinSort::Int => format_ident!("Int"),
        BuiltinSort::Bool => format_ident!("Bool"),
        BuiltinSort::Map => format_ident!("Map"),
        BuiltinSort::Id => format_ident!("Id"),
        BuiltinSort::Bytes => format_ident!("Bytes"),
        BuiltinSort::String => format_ident!("String"),
        BuiltinSort::List => format_ident!("List"),
        BuiltinSort::Set => format_ident!("Set"),
    };
    quote!(k::builtin::#name)
}

fn render_builtin_operation(operation: BuiltinOperation) -> TokenStream {
    let (module, name) = match operation {
        BuiltinOperation::IntAdd => (format_ident!("int"), format_ident!("add")),
        BuiltinOperation::IntSub => (format_ident!("int"), format_ident!("sub")),
        BuiltinOperation::IntMul => (format_ident!("int"), format_ident!("mul")),
        BuiltinOperation::IntTDiv => (format_ident!("int"), format_ident!("div")),
        BuiltinOperation::IntMod => (format_ident!("int"), format_ident!("modulo")),
        BuiltinOperation::IntPowMod => (format_ident!("int"), format_ident!("pow_mod")),
        BuiltinOperation::IntLog2 => (format_ident!("int"), format_ident!("log2")),
        BuiltinOperation::IntShiftRight => (format_ident!("int"), format_ident!("shift_right")),
        BuiltinOperation::IntShiftLeft => (format_ident!("int"), format_ident!("shift_left")),
        BuiltinOperation::IntBitAnd => (format_ident!("int"), format_ident!("bit_and")),
        BuiltinOperation::IntBitXor => (format_ident!("int"), format_ident!("bit_xor")),
        BuiltinOperation::IntBitOr => (format_ident!("int"), format_ident!("bit_or")),
        BuiltinOperation::IntGreaterEqual => (format_ident!("int"), format_ident!("ge")),
        BuiltinOperation::IntGreater => (format_ident!("int"), format_ident!("gt")),
        BuiltinOperation::IntLessEqual => (format_ident!("int"), format_ident!("le")),
        BuiltinOperation::IntLess => (format_ident!("int"), format_ident!("lt")),
        BuiltinOperation::IntEqual => (format_ident!("int"), format_ident!("eq")),
        BuiltinOperation::IntNotEqual => (format_ident!("int"), format_ident!("ne")),
        BuiltinOperation::BoolNot => (format_ident!("bool"), format_ident!("not")),
        BuiltinOperation::BoolEqual => (format_ident!("bool"), format_ident!("eq")),
        BuiltinOperation::BoolNotEqual => (format_ident!("bool"), format_ident!("ne")),
        BuiltinOperation::BoolAnd => (format_ident!("bool"), format_ident!("and")),
        BuiltinOperation::BoolOr => (format_ident!("bool"), format_ident!("or")),
        BuiltinOperation::BytesLength => (format_ident!("bytes"), format_ident!("length")),
        BuiltinOperation::BytesGet => (format_ident!("bytes"), format_ident!("get")),
        BuiltinOperation::BytesEmpty => (format_ident!("bytes"), format_ident!("empty")),
        BuiltinOperation::BytesUpdate => (format_ident!("bytes"), format_ident!("update")),
        BuiltinOperation::BytesPadRight => (format_ident!("bytes"), format_ident!("pad_right")),
        BuiltinOperation::BytesSubstring => (format_ident!("bytes"), format_ident!("substr")),
    };
    quote!(k::builtin::#module::#name)
}

fn render_map_operation(operation: MapOperation) -> Result<TokenStream, ReferenceExpansionError> {
    match operation {
        MapOperation::Update => Ok(quote!(k::builtin::map::update)),
        MapOperation::Get => Ok(quote!(k::builtin::map::get)),
        MapOperation::InKeys => Ok(quote!(k::builtin::map::in_keys)),
        MapOperation::Empty | MapOperation::Item => {
            Err(ReferenceExpansionError::NamedBuiltinApplication)
        }
    }
}

fn render_set_operation(operation: SetOperation) -> TokenStream {
    let name = match operation {
        SetOperation::Empty => format_ident!("empty"),
        SetOperation::Item => format_ident!("item"),
        SetOperation::Concat => format_ident!("concat"),
        SetOperation::Union => format_ident!("union"),
        SetOperation::Contains => format_ident!("contains"),
    };
    quote!(k::builtin::set::#name)
}

fn render_list_operation(operation: ListOperation) -> TokenStream {
    let name = match operation {
        ListOperation::Empty => format_ident!("empty"),
        ListOperation::Item => format_ident!("item"),
        ListOperation::Concat => format_ident!("concat"),
        ListOperation::Get => format_ident!("get"),
        ListOperation::Update => format_ident!("update"),
        ListOperation::Size => format_ident!("size"),
        ListOperation::Make => format_ident!("make"),
        ListOperation::Range => format_ident!("range"),
        ListOperation::UpdateAll => format_ident!("update_all"),
    };
    quote!(k::builtin::list::#name)
}

fn fresh_ident(base: &str, reserved: &mut BTreeSet<String>) -> Ident {
    if !reserved.contains(base) {
        reserved.insert(base.to_owned());
        return rust_ident(base);
    }
    let mut ordinal = 1_u32;
    loop {
        let candidate = format!("{base}{ordinal}");
        if !reserved.contains(candidate.as_str()) {
            reserved.insert(candidate.clone());
            return rust_ident(&candidate);
        }
        ordinal += 1;
    }
}

fn rust_ident(value: &str) -> Ident {
    syn::parse_str(value).unwrap_or_else(|_| Ident::new_raw(value, Span::call_site()))
}

/// Typed deterministic-reference projection failure.
#[derive(Debug)]
pub enum ReferenceExpansionError {
    /// The selected source is not a Rust module.
    RustSyntax(syn::Error),
    /// The selected package's facade aliases could not be read.
    Facade(CollectionError),
    /// One readable KRS island is malformed.
    KrsSyntax(krs_syntax::SyntaxError),
    /// Generated Rust unexpectedly failed to parse.
    GeneratedRust(syn::Error),
    /// One rule name occurred in more than one readable table.
    DuplicateRule(String),
    /// A readable rule did not map one-to-one to a collected head rule.
    RuleCoverage {
        /// Readable clause name.
        name: String,
        /// Number of matching collected head rules.
        found: usize,
    },
    /// An authored enum variant did not map one-to-one to a constructor.
    ConstructorCoverage {
        /// Rust enum family.
        family: String,
        /// Rust variant.
        variant: String,
        /// Number of matching constructor descriptors.
        found: usize,
    },
    /// The projected Rust fields did not cover the collected constructor.
    ConstructorFieldCoverage {
        /// Rust enum family.
        family: String,
        /// Rust variant.
        variant: String,
        /// Collected field count.
        expected: usize,
        /// Rust field count.
        found: usize,
    },
    /// A projected Rust field was absent from the collected constructor.
    MissingConstructorField {
        /// Rust enum family.
        family: String,
        /// Rust variant.
        variant: String,
        /// Rust field.
        field: String,
    },
    /// Collection did not resolve a constructor field sort.
    MissingConstructorFieldSort {
        /// Rust enum family.
        family: String,
        /// Rust variant.
        variant: String,
        /// Rust field.
        field: String,
    },
    /// Semantic lowering omitted a collected rule.
    MissingSemanticRule(Box<StableItemId>),
    /// Inference did not produce a type for a readable binder.
    MissingBindingSort {
        /// Readable clause name.
        rule: String,
        /// Binder whose inferred sort was absent.
        binding: String,
    },
    /// A stable dependency alias cannot be reconstructed from protocol data.
    ExternalDeclaration(Box<StableItemId>),
    /// A constructor field uses a declared sort whose marker path is external.
    ExternalReferenceSort(Box<StableItemId>),
    /// One application mixed positional and named arguments.
    MixedApplicationArguments,
    /// A builtin operation unexpectedly used named arguments.
    NamedBuiltinApplication,
    /// A referenced declaration was absent from the collected bundle.
    MissingDeclaration(Box<StableItemId>),
    /// A named application did not reference a constructor declaration.
    NamedNonConstructor(Box<StableItemId>),
    /// One named constructor field occurred more than once.
    DuplicateApplicationField {
        /// Constructor identity.
        id: Box<StableItemId>,
        /// Duplicate Rust field name.
        field: String,
    },
    /// A constructor result omitted a required named field.
    MissingApplicationField {
        /// Constructor identity.
        id: Box<StableItemId>,
        /// Missing Rust field name.
        field: String,
    },
    /// A named argument did not belong to its constructor declaration.
    UnknownApplicationField {
        /// Constructor identity.
        id: Box<StableItemId>,
        /// Unknown Rust field name.
        field: String,
    },
    /// A canonical integer payload was not valid Rust tokens.
    InvalidLiteral(String),
    /// No reference-surface spelling exists for this builtin token sort.
    UnsupportedBuiltinToken(BuiltinSort),
}

impl fmt::Display for ReferenceExpansionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RustSyntax(error) => write!(formatter, "invalid Rust source: {error}"),
            Self::Facade(error) => write!(formatter, "cannot resolve KRS facade: {error}"),
            Self::KrsSyntax(error) => write!(formatter, "invalid readable KRS source: {error}"),
            Self::GeneratedRust(error) => write!(formatter, "invalid generated Rust: {error}"),
            Self::DuplicateRule(name) => write!(formatter, "readable rule `{name}` occurs twice"),
            Self::RuleCoverage { name, found } => write!(
                formatter,
                "readable rule `{name}` maps to {found} collected head rules; expected one"
            ),
            Self::ConstructorCoverage {
                family,
                variant,
                found,
            } => write!(
                formatter,
                "readable enum variant `{family}::{variant}` maps to {found} constructors; expected one"
            ),
            Self::ConstructorFieldCoverage {
                family,
                variant,
                expected,
                found,
            } => write!(
                formatter,
                "readable enum variant `{family}::{variant}` has {found} Rust fields but {expected} collected fields"
            ),
            Self::MissingConstructorField {
                family,
                variant,
                field,
            } => write!(
                formatter,
                "readable enum field `{family}::{variant}.{field}` is absent from its collected constructor"
            ),
            Self::MissingConstructorFieldSort {
                family,
                variant,
                field,
            } => write!(
                formatter,
                "readable enum field `{family}::{variant}.{field}` has no collected sort"
            ),
            Self::MissingSemanticRule(id) => {
                write!(
                    formatter,
                    "collected rule {id:?} is absent from semantic IR"
                )
            }
            Self::MissingBindingSort { rule, binding } => {
                write!(
                    formatter,
                    "rule `{rule}` binding `{binding}` has no inferred sort"
                )
            }
            Self::ExternalDeclaration(id) => write!(
                formatter,
                "cannot render external declaration {id:?} without its authored Cargo alias"
            ),
            Self::ExternalReferenceSort(id) => write!(
                formatter,
                "cannot render external reference-sort marker {id:?} without its authored Cargo alias"
            ),
            Self::MixedApplicationArguments => {
                formatter.write_str("application mixes positional and named arguments")
            }
            Self::NamedBuiltinApplication => {
                formatter.write_str("builtin application unexpectedly uses named arguments")
            }
            Self::MissingDeclaration(id) => {
                write!(formatter, "application declaration {id:?} is absent")
            }
            Self::NamedNonConstructor(id) => {
                write!(formatter, "named application {id:?} is not a constructor")
            }
            Self::DuplicateApplicationField { id, field } => {
                write!(formatter, "constructor {id:?} repeats field `{field}`")
            }
            Self::MissingApplicationField { id, field } => {
                write!(formatter, "constructor result {id:?} omits field `{field}`")
            }
            Self::UnknownApplicationField { id, field } => {
                write!(formatter, "constructor {id:?} has no field `{field}`")
            }
            Self::InvalidLiteral(value) => write!(formatter, "invalid integer literal `{value}`"),
            Self::UnsupportedBuiltinToken(sort) => {
                write!(formatter, "unsupported builtin token sort {sort:?}")
            }
        }
    }
}

impl Error for ReferenceExpansionError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::RustSyntax(error) | Self::GeneratedRust(error) => Some(error),
            Self::Facade(error) => Some(error),
            Self::KrsSyntax(error) => Some(error),
            Self::DuplicateRule(_)
            | Self::RuleCoverage { .. }
            | Self::ConstructorCoverage { .. }
            | Self::ConstructorFieldCoverage { .. }
            | Self::MissingConstructorField { .. }
            | Self::MissingConstructorFieldSort { .. }
            | Self::MissingSemanticRule(_)
            | Self::MissingBindingSort { .. }
            | Self::ExternalDeclaration(_)
            | Self::ExternalReferenceSort(_)
            | Self::MixedApplicationArguments
            | Self::NamedBuiltinApplication
            | Self::MissingDeclaration(_)
            | Self::NamedNonConstructor(_)
            | Self::DuplicateApplicationField { .. }
            | Self::MissingApplicationField { .. }
            | Self::UnknownApplicationField { .. }
            | Self::InvalidLiteral(_)
            | Self::UnsupportedBuiltinToken(_) => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{contains_use_tree, render_reference_token_term_type, render_term};
    use krs_ir::{
        BuiltinSort, DescriptorApplicationHeadClass, DescriptorApplicationRef,
        DescriptorApplicationReference, DescriptorBundle, DescriptorTerm, DescriptorTermArgument,
        ItemKind, ListOperation, PackageId, ProvenanceKey, StableItemId,
    };
    use quote::ToTokens;

    #[test]
    fn map_macro_import_detection_ignores_attributes_and_rejects_other_uses() {
        let file = syn::parse_file("#[allow(unused_imports)] use k::map; use k::builtin::map;")
            .expect("valid imports");
        let expected = syn::parse_str::<syn::ItemUse>("use k::map;")
            .expect("valid map import")
            .tree
            .to_token_stream()
            .to_string();
        assert!(contains_use_tree(&file.items, &expected));

        let other = syn::parse_str::<syn::ItemUse>("use k::cells;")
            .expect("valid cells import")
            .tree
            .to_token_stream()
            .to_string();
        assert!(!contains_use_tree(&file.items, &other));
    }

    #[test]
    fn canonical_bytes_token_expands_back_to_a_byte_string_macro() {
        let package = PackageId::new("TEST", "test", "0.1.0", "workspace").unwrap();
        let token = DescriptorTerm::BuiltinToken {
            key: ProvenanceKey::new("claim_bytes_token", 0).unwrap(),
            sort: BuiltinSort::Bytes,
            value: r#"b"\x00\x41\xff""#.to_owned(),
        };
        let rendered = render_term(&token, false, &package, &DescriptorBundle::new(Vec::new()))
            .unwrap()
            .to_string();
        assert_eq!(rendered, r#"k :: bytes ! (b"\0A\xFF")"#);
    }

    #[test]
    fn declared_token_reference_field_remains_a_symbolic_term() {
        let package = PackageId::new("TEST", "test", "0.1.0", "workspace").unwrap();
        let token = StableItemId::new(
            package.clone(),
            std::iter::empty::<String>(),
            "String",
            ItemKind::Sort,
            "",
        )
        .unwrap();
        let rendered = render_reference_token_term_type(&token, &package)
            .unwrap()
            .to_string();

        assert_eq!(rendered, "k :: Term < crate :: String >");
    }

    #[test]
    fn list_lookup_expands_back_to_the_typed_builtin_marker() {
        let package = PackageId::new("TEST", "test", "0.1.0", "workspace").unwrap();
        let variable = |name: &str, ordinal| DescriptorTerm::Variable {
            key: ProvenanceKey::new("claim_reference", ordinal).unwrap(),
            path_key: ProvenanceKey::new("claim_path", ordinal).unwrap(),
            name: name.to_owned(),
        };
        let lookup = DescriptorTerm::Application {
            head_class: DescriptorApplicationHeadClass::Applied,
            reference: DescriptorApplicationReference {
                key: ProvenanceKey::new("claim_application_head", 0).unwrap(),
                application: DescriptorApplicationRef::List(ListOperation::Get),
            },
            path_key: ProvenanceKey::new("claim_path", 2).unwrap(),
            arguments: vec![
                DescriptorTermArgument::Positional {
                    value: Box::new(variable("program", 0)),
                },
                DescriptorTermArgument::Positional {
                    value: Box::new(variable("index", 1)),
                },
            ],
        };
        let rendered = render_term(&lookup, false, &package, &DescriptorBundle::new(Vec::new()))
            .unwrap()
            .to_string();
        assert_eq!(rendered, "k :: builtin :: list :: get (program , index)");
    }
}
