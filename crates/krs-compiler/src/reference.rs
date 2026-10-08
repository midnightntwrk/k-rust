//! Deterministic readable-to-reference Rust projection.

use krs_diagnostic::{Diagnostic, Location, ToDiagnostic, codes};
use krs_syntax::KrsSyntax;
use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use krs_ir::{
    BuiltinOperation, BuiltinSort, Descriptor, DescriptorApplicationRef, DescriptorBundle,
    DescriptorHeadRule, DescriptorIndex, DescriptorPayload, DescriptorTerm,
    ENUM_VARIANT_DISAMBIGUATOR_PREFIX, FacadeMarker, OriginFrame, PackageId, ProtocolHeadRuleExtra,
    ProtocolHeadRuleResult, ProvenanceRole, RangedOriginKind, Sha256Digest, SourceFileId,
    StableItemId,
};
use krs_ir_levels::{SemanticRule, SemanticSortRef, SemanticTheory};
use krs_syntax::surface::{self, FacadeScope, FunctionMacro, InvocationKind, Scope};
use proc_macro2::{Ident, Span, TokenStream, TokenTree};
use quote::{ToTokens, format_ident, quote};
use sha2::{Digest, Sha256};
use syn::ext::IdentExt;
use syn::spanned::Spanned;

/// Expands the one authored Rust module that defines a package's
/// descriptors.
///
/// The source is the authored file of the package's head rules,
/// or of all its descriptors when it has none.
/// Every selected descriptor must come from one file and one Rust module,
/// and the file under the manifest directory must still have its collected
/// content digest.
/// `facade` is the package's facade scope before file and inline-module bindings.
///
/// # Errors
///
/// Returns a typed failure when the selection is empty or ambiguous,
/// the source cannot be read, has changed since collection, or is not UTF-8,
/// or when [`expand_reference_source`] rejects it.
pub fn expand_package_reference_source(
    bundle: &DescriptorBundle,
    semantic: &SemanticTheory,
    package: &PackageId,
    manifest_path: &Path,
    facade: &FacadeScope,
) -> Result<String, ReferenceExpansionError> {
    let (source, module_path) = read_package_source(bundle, package, manifest_path)
        .map_err(ReferenceExpansionError::Source)?;
    expand_reference_source(&source, facade, package, module_path, bundle, semantic)
}

fn read_package_source<'bundle>(
    bundle: &'bundle DescriptorBundle,
    package: &PackageId,
    manifest_path: &Path,
) -> Result<(String, &'bundle [String]), ReferenceSourceError> {
    let in_package = || {
        bundle
            .descriptors()
            .iter()
            .filter(|descriptor| descriptor.id().package() == package)
    };
    let head_rules = in_package()
        .filter(|descriptor| matches!(descriptor.payload(), DescriptorPayload::HeadRule(_)))
        .collect::<Vec<_>>();
    let candidates = if head_rules.is_empty() {
        in_package().collect()
    } else {
        head_rules
    };
    let mut sources = BTreeMap::<&SourceFileId, BTreeSet<&[String]>>::new();
    for descriptor in candidates {
        if let Some(file) = authored_source_file(descriptor) {
            sources
                .entry(file)
                .or_default()
                .insert(descriptor.id().module_path());
        }
    }
    let [(file, module_paths)] = sources.iter().collect::<Vec<_>>()[..] else {
        return Err(ReferenceSourceError::Selection(
            sources.into_keys().cloned().collect(),
        ));
    };
    let [module_path] = module_paths.iter().copied().collect::<Vec<_>>()[..] else {
        return Err(ReferenceSourceError::Modules {
            file: Box::new((*file).clone()),
            module_paths: module_paths.iter().map(|path| path.to_vec()).collect(),
        });
    };
    let manifest_directory = manifest_path
        .parent()
        .ok_or_else(|| ReferenceSourceError::ManifestDirectory(manifest_path.to_path_buf()))?;
    let path = manifest_directory.join(file.package_relative_path());
    let source = match fs::read(&path) {
        Ok(source) => source,
        Err(error) => return Err(ReferenceSourceError::Read { path, error }),
    };
    if Sha256Digest::from_bytes(Sha256::digest(&source).into()) != *file.content_sha256() {
        return Err(ReferenceSourceError::Changed(path));
    }
    let source = match String::from_utf8(source) {
        Ok(source) => source,
        Err(error) => {
            return Err(ReferenceSourceError::Encoding {
                path,
                error: error.utf8_error(),
            });
        }
    };
    Ok((source, module_path))
}

fn authored_source_file(descriptor: &Descriptor) -> Option<&SourceFileId> {
    descriptor
        .origin()
        .frames()
        .iter()
        .find_map(|frame| match frame {
            OriginFrame::Ranged {
                kind: RangedOriginKind::Authored,
                range,
                ..
            } => Some(&range.file),
            OriginFrame::Ranged { .. } | OriginFrame::Transformation { .. } => None,
        })
}

/// Expands the readable constructs in one Rust module to the deterministic
/// layer-2 reference surface.
///
/// Rules use whole-definition sort inference and fixed-configuration
/// completion. Readable sorts, direct memberships, constructor families,
/// syntax metadata, strictness, precedence, and explicit associativity are
/// projected through deterministic identity-preserving layer-2 carriers;
/// unrelated Rust items remain AST-equivalent.
/// Readable macros are recognized under `facade`,
/// the package's facade scope before file and inline-module bindings.
///
/// # Errors
///
/// Returns a typed failure for invalid Rust/KRS syntax, absent or ambiguous
/// collected rules, missing inferred sorts, or an external declaration whose
/// Cargo dependency alias is not recoverable from the stable protocol.
#[expect(
    clippy::too_many_lines,
    reason = "The source-order traversal keeps projected items deterministic."
)]
pub fn expand_reference_source(
    source: &str,
    facade: &FacadeScope,
    package: &PackageId,
    module_path: &[String],
    bundle: &DescriptorBundle,
    semantic: &SemanticTheory,
) -> Result<String, ReferenceExpansionError> {
    let mut file = syn::parse_file(source).map_err(ReferenceExpansionError::RustSyntax)?;
    let descriptor_index = DescriptorIndex::new(bundle);
    let macro_entries = reference_macro_entries(&file, facade);
    let semantic_rules = semantic
        .modules()
        .iter()
        .flat_map(krs_ir_levels::SemanticModule::rules)
        .map(|rule| (rule.id(), rule))
        .collect::<BTreeMap<_, _>>();
    let mut rendered_names = BTreeSet::new();
    let mut needs_map_macro = false;
    let mut items = Vec::new();
    for (index, mut item) in std::mem::take(&mut file.items).into_iter().enumerate() {
        if let syn::Item::Use(item_use) = &mut item {
            item_use
                .attrs
                .push(syn::parse_quote!(#[allow(unused_imports)]));
        }
        if let syn::Item::Struct(item_struct) = &mut item {
            materialize_configuration_wrappers(item_struct)?;
            materialize_constructor_flags(item_struct);
        }
        let trailing_enum_grammar = if let syn::Item::Enum(item_enum) = &mut item {
            materialize_enum_productions(
                item_enum,
                package,
                module_path,
                bundle,
                &descriptor_index,
            )?
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
        let entry = macro_entries.get(&index);
        if matches!(
            entry,
            Some(FunctionMacro::Sorts | FunctionMacro::FrameworkSorts)
        ) {
            items.extend(materialize_readable_sorts(invocation)?);
            continue;
        }
        if entry != Some(&FunctionMacro::Rules) {
            items.push(item);
            items.extend(trailing_enum_grammar);
            continue;
        }
        let block = krs_syntax::RuleBlock::parse_tokens(invocation.mac.tokens.clone())
            .map_err(ReferenceExpansionError::KrsSyntax)?;
        for clause in block.clauses() {
            let name = clause.rule().item().sig.ident.unraw().to_string();
            if !rendered_names.insert(name.clone()) {
                return Err(ReferenceExpansionError::DuplicateRule(name));
            }
            let descriptors = descriptor_index
                .head_rules()
                .filter(|(descriptor, _)| {
                    descriptor.id().package() == package
                        && descriptor.id().module_path() == module_path
                        && descriptor.id().item_name() == name
                })
                .collect::<Vec<_>>();
            let [(descriptor, rule)] = descriptors.as_slice() else {
                return Err(ReferenceExpansionError::RuleCoverage {
                    name,
                    found: descriptors.len(),
                });
            };
            needs_map_macro |= !rule.extras.is_empty();
            let semantic_rule = semantic_rules.get(descriptor.id()).ok_or_else(|| {
                ReferenceExpansionError::MissingSemanticRule(Box::new(descriptor.id().clone()))
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

fn reference_macro_entries(
    file: &syn::File,
    facade: &FacadeScope,
) -> BTreeMap<usize, FunctionMacro> {
    let item_indices = file
        .items
        .iter()
        .enumerate()
        .map(|(index, item)| (std::ptr::from_ref(item), index))
        .collect::<BTreeMap<_, _>>();
    let discovered = surface::invocations(file, facade);
    surface::item_owners(&discovered)
        .into_iter()
        .filter_map(|(item, invocation)| {
            if !matches!(&invocation.scope, Scope::Module(modules) if modules.is_empty()) {
                return None;
            }
            let InvocationKind::Function { entry, .. } = &invocation.kind else {
                return None;
            };
            Some((item_indices[&item], *entry))
        })
        .collect()
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
    bundle: &DescriptorBundle,
    descriptor_index: &DescriptorIndex<'_>,
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
        let group = declaration
            .precedence_groups()
            .nth(group_ordinal)
            .expect("enum precedence ordinal identifies a parsed group")
            .emitted_name(declaration.sort_name(), group_ordinal);
        let group = syn::LitStr::new(&group, Span::call_site());
        let template = syntax.syntax();
        let format = syntax.format().ok_or_else(|| {
            ReferenceExpansionError::GeneratedRust(syn::Error::new(
                template.span(),
                "readable enum syntax has no derived reference format",
            ))
        })?;
        // Keys in the canonical order of decision X2.
        let avoid = syntax.avoid().then(|| quote!(avoid = true,));
        let prefer = syntax.prefer().then(|| quote!(prefer = true,));
        let placement = syntax.placement().map(|flag| {
            let key = format_ident!("{}", flag.as_str());
            quote!(#key = true,)
        });
        let overload = syntax.overload().map(|target| quote!(overload = #target,));
        let color = syntax.color().map(|color| quote!(color = #color,));
        let colors = syntax
            .colors()
            .map(|colors| quote!(colors = [#(#colors),*],));
        let materialized: syn::Attribute = syn::parse_quote!(#[k::syntax(
            #template,
            group = #group,
            #avoid
            #prefer
            #placement
            #overload
            #color
            #colors
            format = #format
        )]);
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
            descriptor_index,
        )?;
        materialize_reference_strictness(output_variant, variant)?;
    }
    render_family_grammar(&declaration)
}

/// Writes the reference spelling `internal = true` / `program = true` for a
/// bare placement flag in `#[k::constructor(..)]`; `#[k::function]` keeps its
/// bare flags in both layers (decision X2).
fn materialize_constructor_flags(item: &mut syn::ItemStruct) {
    for attribute in &mut item.attrs {
        if !attribute_is(attribute, "constructor") {
            continue;
        }
        let syn::Meta::List(list) = &mut attribute.meta else {
            continue;
        };
        let tokens = list.tokens.clone().into_iter().collect::<Vec<_>>();
        let mut rewritten = TokenStream::new();
        for (index, token) in tokens.iter().enumerate() {
            rewritten.extend(std::iter::once(token.clone()));
            let bare_flag = matches!(token, proc_macro2::TokenTree::Ident(ident) if ident == "internal" || ident == "program")
                && (index == 0
                    || matches!(&tokens[index - 1], proc_macro2::TokenTree::Punct(punct) if punct.as_char() == ','))
                && tokens.get(index + 1).is_none_or(|next| {
                    matches!(next, proc_macro2::TokenTree::Punct(punct) if punct.as_char() == ',')
                });
            if bare_flag {
                rewritten.extend(quote!(= true));
            }
        }
        list.tokens = rewritten;
    }
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
    bundle: &DescriptorBundle,
    descriptor_index: &DescriptorIndex<'_>,
) -> Result<(), ReferenceExpansionError> {
    let disambiguator = format!("{ENUM_VARIANT_DISAMBIGUATOR_PREFIX}{family}");
    let descriptors = descriptor_index
        .constructors()
        .filter(|(descriptor, _)| {
            descriptor.id().package() == package
                && descriptor.id().module_path() == module_path
                && output.ident == descriptor.id().item_name()
                && descriptor.id().disambiguator() == disambiguator
        })
        .collect::<Vec<_>>();
    let [(_, constructor)] = descriptors.as_slice() else {
        return Err(ReferenceExpansionError::ConstructorCoverage {
            family: family.to_string(),
            variant: output.ident.to_string(),
            found: descriptors.len(),
        });
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
        krs_ir::DescriptorSortRef::Cell(id) => render_declared_path(id, package),
    }
}

fn render_reference_token_term_type(
    id: &StableItemId,
    package: &PackageId,
) -> Result<TokenStream, ReferenceExpansionError> {
    let token = render_declared_path(id, package)?;
    Ok(quote!(k::Term<#token>))
}

/// Whether `cell` is a fixed nested (group) cell, whose `cells!` entry is
/// written without a wrapper because it mirrors the expanded struct (KF-016).
fn is_group_cell(cell: &krs_ir::DescriptorCellIdentity, bundle: &krs_ir::DescriptorBundle) -> bool {
    bundle.descriptors().iter().any(|descriptor| {
        if descriptor.id() != &cell.owner {
            return false;
        }
        let declaration = match descriptor.payload() {
            DescriptorPayload::Cell(declaration) => declaration.as_ref(),
            DescriptorPayload::FixedConfiguration(configuration) => &configuration.declaration,
            _ => return false,
        };
        declaration.fields.iter().any(|field| {
            field.rust_field == cell.field
                && matches!(field.content, krs_ir::ProtocolCellContent::Nested { .. })
        })
    })
}

fn is_token_sort(id: &StableItemId, bundle: &krs_ir::DescriptorBundle) -> bool {
    bundle.descriptors().iter().any(|descriptor| {
        let DescriptorPayload::Grammar(grammar) = descriptor.payload() else {
            return false;
        };
        let krs_ir::GrammarDescriptor::Tokens { productions } = grammar.as_ref() else {
            return false;
        };
        productions.iter().any(|production| {
            matches!(
                &production.owner,
                krs_ir::DescriptorProductionOwner::TokenSort { sort }
                    if sort.sort == krs_ir::DescriptorSortRef::Declared(id.clone())
            )
        })
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
    for (ordinal, group) in declaration.precedence_groups().enumerate() {
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

#[expect(
    clippy::too_many_lines,
    reason = "Trait aliases and direct/ancestor impls are one graph projection."
)]
fn materialize_readable_sorts(
    invocation: &syn::ItemMacro,
) -> Result<Vec<syn::Item>, ReferenceExpansionError> {
    let declaration = krs_syntax::SortsDeclaration::parse_tokens(invocation.mac.tokens.clone())
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
    let declaration = krs_syntax::ConfigurationDeclaration::parse_tokens(item.to_token_stream())
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
        let initializer =
            krs_syntax::InitializerFunction::parse_tokens(parsed_method.to_token_stream())
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

#[expect(
    clippy::too_many_lines,
    reason = "One rule projection keeps its two sides visibly paired."
)]
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
    let tail = rule
        .head
        .as_ref()
        .map(|_| fresh_ident("tail", &mut reserved));
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

    let mut left_cells = Vec::new();
    let mut right_cells = Vec::new();
    // A clause without the computation cell leaves it out of both sides (E7).
    if let (Some(head), Some(computation), Some(tail)) = (&rule.head, &rule.computation_cell, &tail)
    {
        let computation = render_rule_cell_field(&computation.cell, &rule.configuration, package)?;
        let subject = render_term(&head.subject, true, package, bundle)?;
        left_cells.push(quote! {
            #computation: k::configuration::KCell(#subject, #tail @ ..)
        });
        let result_items = match &head.result {
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
    }

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
                let group = is_group_cell(&cell.cell, bundle);
                let cell = render_rule_cell_field(&cell.cell, &rule.configuration, package)?;
                let before = render_term(before, true, package, bundle)?;
                let after = render_term(after, false, package, bundle)?;
                if group {
                    // A nested field's entry has no wrapper (KF-016).
                    left_cells.push(quote!(#cell: #before));
                    right_cells.push(quote!(#cell: #after));
                } else {
                    left_cells.push(quote! {
                        #cell: k::configuration::Cell(#before)
                    });
                    right_cells.push(quote! {
                        #cell: k::configuration::Cell(#after)
                    });
                }
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
    // The clause's `#[k::requires]` helper is consumed by the readable parser;
    // the reference form restates it from the descriptor, after `#[k::rule]`.
    let requires = rule
        .requires
        .as_ref()
        .map(|condition| {
            render_term(&condition.term, false, package, bundle)
                .map(|term| quote!(#[k::requires(#term)]))
        })
        .transpose()?;
    let rule_attribute =
        reference_rule_attribute(rule.priority.as_ref(), rule.nondet.as_ref(), &label);
    syn::parse2(quote! {
        #(#attrs)*
        #rule_attribute
        #requires
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

/// Renders `#[k::rule(..)]` with its keys in the canonical order
/// (`owise | priority = N`, then `nondet = g`, then `label`).
fn reference_rule_attribute(
    priority: Option<&krs_ir::DescriptorRulePriority>,
    nondet: Option<&krs_ir::DescriptorNondetGroup>,
    label: &syn::LitStr,
) -> TokenStream {
    let mut keys = Vec::new();
    if let Some(priority) = priority {
        if priority.key.role() == ProvenanceRole::RuleOwise {
            keys.push(quote!(owise));
        } else {
            let value = proc_macro2::Literal::u32_unsuffixed(priority.value);
            keys.push(quote!(priority = #value));
        }
    }
    if let Some(nondet) = nondet {
        let group = rust_ident(&nondet.name);
        keys.push(quote!(nondet = #group));
    }
    keys.push(quote!(label = #label));
    quote!(#[k::rule(#(#keys),*)])
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

#[expect(
    clippy::too_many_lines,
    reason = "Exhaustive rendering mirrors the closed descriptor term sum."
)]
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
                DescriptorApplicationRef::Map(operation) => {
                    render_facade_marker(operation.facade_marker())
                }
                DescriptorApplicationRef::List(operation) => {
                    render_facade_marker(operation.facade_marker())
                }
                DescriptorApplicationRef::Set(operation) => {
                    render_facade_marker(operation.facade_marker())
                }
            };
            if arguments.is_empty()
                && matches!(
                    head_class,
                    krs_ir::DescriptorApplicationHeadClass::BareReference
                )
            {
                return Ok(head);
            }
            if arguments.is_empty() {
                return Ok(quote!(#head()));
            }
            let arguments = match arguments {
                krs_ir::Arguments::Positional(values) => {
                    let values = values
                        .iter()
                        .map(|value| render_term(value, pattern, package, bundle))
                        .collect::<Result<Vec<_>, _>>()?;
                    return Ok(quote!(#head(#(#values),*)));
                }
                krs_ir::Arguments::Named(values) => values,
            };
            let DescriptorApplicationRef::Declared(id) = &reference.application else {
                return Err(ReferenceExpansionError::NamedBuiltinApplication);
            };
            let descriptor = bundle
                .descriptors()
                .iter()
                .find(|descriptor| descriptor.id() == id)
                .ok_or_else(|| ReferenceExpansionError::MissingDeclaration(Box::new(id.clone())))?;
            let DescriptorPayload::Constructor(constructor) = descriptor.payload() else {
                return Err(ReferenceExpansionError::NamedNonConstructor(Box::new(
                    id.clone(),
                )));
            };
            let mut supplied = BTreeMap::new();
            for argument in arguments {
                let field = &argument.field;
                let value = argument.value.as_ref();
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
            // One literal token, so a negative value prints as `-1`, not `- 1`.
            krs_ir::DescriptorLiteral::Int(value) => value
                .parse::<proc_macro2::Literal>()
                .map(|literal| TokenTree::Literal(literal).into())
                .map_err(|_| ReferenceExpansionError::InvalidLiteral(value.clone())),
            krs_ir::DescriptorLiteral::Bool(value) => Ok(quote!(#value)),
            krs_ir::DescriptorLiteral::String(value) => {
                let value = syn::LitStr::new(value, Span::call_site());
                Ok(quote!(#value))
            }
        },
        DescriptorTerm::Wildcard { .. } => Ok(quote!(_)),
        DescriptorTerm::BuiltinToken { sort, value, .. } => match sort {
            BuiltinSort::Id => {
                let value = syn::LitStr::new(value, Span::call_site());
                Ok(quote!(k::id!(#value)))
            }
            BuiltinSort::Bytes => {
                let value = krs_ir::bytes_token::decode(value)
                    .map_err(|_| ReferenceExpansionError::InvalidLiteral(value.clone()))?;
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
        DescriptorTerm::Lexeme { sort, text, .. } => {
            let sort = render_descriptor_sort(&sort.sort, package)?;
            let text = syn::LitStr::new(text, Span::call_site());
            Ok(quote!(k::lexeme!(#sort, #text)))
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

fn render_sort_type(
    sort: &SemanticSortRef,
    package: &PackageId,
) -> Result<TokenStream, ReferenceExpansionError> {
    match sort {
        // A whole-group binder is typed by its nested `#[k::cell]` struct (KF-016).
        SemanticSortRef::Declared(id) | SemanticSortRef::Cell(id) => {
            render_declared_path(id, package)
        }
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
        krs_ir::DescriptorSortRef::Declared(id) | krs_ir::DescriptorSortRef::Cell(id) => {
            render_declared_path(id, package)
        }
        krs_ir::DescriptorSortRef::Builtin(sort) => Ok(render_builtin_sort(*sort)),
    }
}

fn render_declared_application(
    id: &StableItemId,
    package: &PackageId,
) -> Result<TokenStream, ReferenceExpansionError> {
    let base = render_declared_path(id, package)?;
    let Some(owner) = id
        .disambiguator()
        .strip_prefix(ENUM_VARIANT_DISAMBIGUATOR_PREFIX)
    else {
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
    let name = format_ident!("{}", sort.marker_name());
    quote!(k::builtin::#name)
}

fn render_builtin_operation(operation: BuiltinOperation) -> TokenStream {
    let spec = operation.spec();
    let module = format_ident!("{}", spec.rust_module);
    let name = format_ident!("{}", spec.rust_name);
    quote!(k::builtin::#module::#name)
}

fn render_facade_marker(marker: FacadeMarker) -> TokenStream {
    let module = format_ident!("{}", marker.module);
    let name = format_ident!("{}", marker.name);
    quote!(k::builtin::#module::#name)
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

/// Failure to select or reread the one authored source of a package.
#[derive(Debug)]
pub enum ReferenceSourceError {
    /// The package's selected descriptors did not come from exactly one
    /// authored source file.
    Selection(Vec<SourceFileId>),
    /// The selected source file holds descriptors from more than one Rust
    /// module.
    Modules {
        /// Selected authored source file.
        file: Box<SourceFileId>,
        /// Module paths of its descriptors, in canonical order.
        module_paths: Vec<Vec<String>>,
    },
    /// The package manifest path has no parent directory.
    ManifestDirectory(PathBuf),
    /// The selected source file could not be read.
    Read {
        /// Source path under the manifest directory.
        path: PathBuf,
        /// Operating-system error.
        error: io::Error,
    },
    /// The selected source file no longer has its collected content digest.
    Changed(PathBuf),
    /// The selected source file is not UTF-8.
    Encoding {
        /// Source path under the manifest directory.
        path: PathBuf,
        /// Decoding error.
        error: std::str::Utf8Error,
    },
}

impl ToDiagnostic for ReferenceSourceError {
    fn to_diagnostic(&self) -> Diagnostic {
        let code = match self {
            Self::Selection(_) => codes::reference::SOURCE_SELECTION,
            Self::Modules { .. } => codes::reference::SOURCE_MODULES,
            Self::ManifestDirectory(_) => codes::reference::SOURCE_MANIFEST_DIRECTORY,
            Self::Read { .. } => codes::reference::SOURCE_READ,
            Self::Changed(_) => codes::reference::SOURCE_CHANGED,
            Self::Encoding { .. } => codes::reference::SOURCE_ENCODING,
        };
        Diagnostic::error(code, self.to_string(), Location::None)
    }
}

impl fmt::Display for ReferenceSourceError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Selection(files) => {
                write!(
                    formatter,
                    "expand requires one readable root source file; found {}",
                    files.len()
                )?;
                if !files.is_empty() {
                    let paths = files
                        .iter()
                        .map(SourceFileId::package_relative_path)
                        .collect::<Vec<_>>()
                        .join(", ");
                    write!(formatter, ": {paths}")?;
                }
                Ok(())
            }
            Self::Modules { file, module_paths } => {
                let paths = module_paths
                    .iter()
                    .map(|path| path.join("::"))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(
                    formatter,
                    "expand source `{}` contains descriptors from multiple Rust modules: {paths}",
                    file.package_relative_path()
                )
            }
            Self::ManifestDirectory(path) => write!(
                formatter,
                "manifest has no parent directory: `{}`",
                path.display()
            ),
            Self::Read { path, error } => {
                write!(formatter, "could not read `{}`: {error}", path.display())
            }
            Self::Changed(path) => write!(
                formatter,
                "expand source changed after collection: `{}`",
                path.display()
            ),
            Self::Encoding { path, error } => write!(
                formatter,
                "expand source is not UTF-8: `{}`: {error}",
                path.display()
            ),
        }
    }
}

impl Error for ReferenceSourceError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Read { error, .. } => Some(error),
            Self::Encoding { error, .. } => Some(error),
            Self::Selection(_)
            | Self::Modules { .. }
            | Self::ManifestDirectory(_)
            | Self::Changed(_) => None,
        }
    }
}

/// Typed deterministic-reference projection failure.
#[derive(Debug)]
pub enum ReferenceExpansionError {
    /// The package's authored source could not be selected or reread.
    Source(ReferenceSourceError),
    /// The selected source is not a Rust module.
    RustSyntax(syn::Error),
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

impl ToDiagnostic for ReferenceExpansionError {
    fn to_diagnostic(&self) -> Diagnostic {
        let code = match self {
            Self::Source(error) => return error.to_diagnostic(),
            Self::RustSyntax(_) => codes::reference::RUST_SYNTAX,
            Self::KrsSyntax(error) => {
                let mut diagnostic = error.to_diagnostic();
                diagnostic.message = self.to_string();
                return diagnostic;
            }
            Self::GeneratedRust(_) => codes::reference::GENERATED_RUST,
            Self::DuplicateRule(_) => codes::reference::DUPLICATE_RULE,
            Self::RuleCoverage { .. } => codes::reference::RULE_COVERAGE,
            Self::ConstructorCoverage { .. } => codes::reference::CONSTRUCTOR_COVERAGE,
            Self::ConstructorFieldCoverage { .. } => codes::reference::CONSTRUCTOR_FIELD_COVERAGE,
            Self::MissingConstructorField { .. } => codes::reference::MISSING_CONSTRUCTOR_FIELD,
            Self::MissingConstructorFieldSort { .. } => {
                codes::reference::MISSING_CONSTRUCTOR_FIELD_SORT
            }
            Self::MissingSemanticRule(_) => codes::reference::MISSING_SEMANTIC_RULE,
            Self::MissingBindingSort { .. } => codes::reference::MISSING_BINDING_SORT,
            Self::ExternalDeclaration(_) => codes::reference::EXTERNAL_DECLARATION,
            Self::ExternalReferenceSort(_) => codes::reference::EXTERNAL_REFERENCE_SORT,
            Self::MixedApplicationArguments => codes::reference::MIXED_APPLICATION_ARGUMENTS,
            Self::NamedBuiltinApplication => codes::reference::NAMED_BUILTIN_APPLICATION,
            Self::MissingDeclaration(_) => codes::reference::MISSING_DECLARATION,
            Self::NamedNonConstructor(_) => codes::reference::NAMED_NON_CONSTRUCTOR,
            Self::DuplicateApplicationField { .. } => codes::reference::DUPLICATE_APPLICATION_FIELD,
            Self::MissingApplicationField { .. } => codes::reference::MISSING_APPLICATION_FIELD,
            Self::UnknownApplicationField { .. } => codes::reference::UNKNOWN_APPLICATION_FIELD,
            Self::InvalidLiteral(_) => codes::reference::INVALID_LITERAL,
            Self::UnsupportedBuiltinToken(_) => codes::reference::UNSUPPORTED_BUILTIN_TOKEN,
        };
        Diagnostic::error(code, self.to_string(), Location::None)
    }
}

impl fmt::Display for ReferenceExpansionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Source(error) => error.fmt(formatter),
            Self::RustSyntax(error) => write!(formatter, "invalid Rust source: {error}"),
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
                write!(formatter, "collected rule {id} is absent from semantic IR")
            }
            Self::MissingBindingSort { rule, binding } => {
                write!(
                    formatter,
                    "rule `{rule}` binding `{binding}` has no inferred sort"
                )
            }
            Self::ExternalDeclaration(id) => write!(
                formatter,
                "cannot render external declaration {id} without its authored Cargo alias"
            ),
            Self::ExternalReferenceSort(id) => write!(
                formatter,
                "cannot render external reference-sort marker {id} without its authored Cargo alias"
            ),
            Self::MixedApplicationArguments => {
                formatter.write_str("application mixes positional and named arguments")
            }
            Self::NamedBuiltinApplication => {
                formatter.write_str("builtin application unexpectedly uses named arguments")
            }
            Self::MissingDeclaration(id) => {
                write!(formatter, "application declaration {id} is absent")
            }
            Self::NamedNonConstructor(id) => {
                write!(formatter, "named application {id} is not a constructor")
            }
            Self::DuplicateApplicationField { id, field } => {
                write!(formatter, "constructor {id} repeats field `{field}`")
            }
            Self::MissingApplicationField { id, field } => {
                write!(formatter, "constructor result {id} omits field `{field}`")
            }
            Self::UnknownApplicationField { id, field } => {
                write!(formatter, "constructor {id} has no field `{field}`")
            }
            Self::InvalidLiteral(value) => write!(formatter, "invalid integer literal `{value}`"),
            Self::UnsupportedBuiltinToken(sort) => {
                write!(formatter, "unsupported builtin token sort {sort}")
            }
        }
    }
}

impl Error for ReferenceExpansionError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Source(error) => error.source(),
            Self::RustSyntax(error) | Self::GeneratedRust(error) => Some(error),
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
    use super::{
        contains_use_tree, read_package_source, render_reference_token_term_type, render_term,
    };
    use krs_ir::{
        BuiltinSort, DescriptorApplicationHeadClass, DescriptorApplicationRef,
        DescriptorApplicationReference, DescriptorBundle, DescriptorTerm, ItemKind, ListOperation,
        PackageId, ProvenanceKey, ProvenanceRole, StableItemId,
    };
    use quote::ToTokens;

    #[test]
    fn facade_attributes_prevent_readable_item_macro_projection() {
        let facade = krs_syntax::surface::FacadeScope::new(["crate".to_owned()].into());
        let file = syn::parse_file(
            "use crate as k;\n#[k::sort] k::sorts! { A; }\n#[k::unknown] k::rules! { invalid }\n#[doc = \"x\"] k::sorts! { B; }\nk::rules! {}\n",
        )
        .unwrap();
        let entries = super::reference_macro_entries(&file, &facade);
        assert_eq!(
            entries,
            std::collections::BTreeMap::from([
                (3, krs_syntax::surface::FunctionMacro::Sorts),
                (4, krs_syntax::surface::FunctionMacro::Rules),
            ]),
        );
    }

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
    fn package_without_authored_descriptors_has_no_source_to_expand() {
        let package = PackageId::new("TEST", "test", "0.1.0", "workspace").unwrap();
        let error = read_package_source(
            &DescriptorBundle::new(Vec::new()).unwrap(),
            &package,
            std::path::Path::new("Cargo.toml"),
        )
        .unwrap_err();
        assert_eq!(
            error.to_string(),
            "expand requires one readable root source file; found 0"
        );
    }

    #[test]
    fn canonical_bytes_token_expands_back_to_a_byte_string_macro() {
        let package = PackageId::new("TEST", "test", "0.1.0", "workspace").unwrap();
        let token = DescriptorTerm::BuiltinToken {
            key: ProvenanceKey::new(ProvenanceRole::ClaimBytesToken, 0),
            sort: BuiltinSort::Bytes,
            value: r#"b"\x00\x41\xff""#.to_owned(),
        };
        let rendered = render_term(
            &token,
            false,
            &package,
            &DescriptorBundle::new(Vec::new()).unwrap(),
        )
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
            key: ProvenanceKey::new(ProvenanceRole::ClaimEnsuresReference, ordinal),
            path_key: ProvenanceKey::new(ProvenanceRole::ClaimEnsuresPath, ordinal),
            name: name.to_owned(),
        };
        let lookup = DescriptorTerm::Application {
            head_class: DescriptorApplicationHeadClass::Applied,
            reference: DescriptorApplicationReference {
                key: ProvenanceKey::new(ProvenanceRole::ClaimEnsuresApplicationHead, 0),
                application: DescriptorApplicationRef::List(ListOperation::Get),
            },
            path_key: ProvenanceKey::new(ProvenanceRole::ClaimEnsuresPath, 2),
            arguments: krs_ir::Arguments::Positional(vec![
                Box::new(variable("program", 0)),
                Box::new(variable("index", 1)),
            ]),
        };
        let rendered = render_term(
            &lookup,
            false,
            &package,
            &DescriptorBundle::new(Vec::new()).unwrap(),
        )
        .unwrap()
        .to_string();
        assert_eq!(rendered, "k :: builtin :: list :: get (program , index)");
    }
}
