//! `#[k::spec_module]`: author K proof modules (KF-041).
//!
//! The attribute consumes its inline `mod`: it expands every KRS invocation
//! of the module's items itself, so that it can register their descriptor
//! factories from the module's parent. A spec module is therefore one KRS
//! invocation at the crate root, which explicit registration (the crate-root
//! table) can name, exactly like a top-level invocation. The factories are
//! `pub(super)` inside the module, so `module_path!()` in each factory still
//! records the spec module's Rust path, which assigns its sentences to it.
//!
//! Each `imports = [..]` path becomes `use <path> as _;`, so rustc checks
//! that it names a module.

use krs_diagnostic::codes::expand;
use krs_ir::wire::{WireGrammarDescriptor, WirePayload};
use krs_ir::{DescriptorModuleImport, DescriptorSpecModuleName};
use krs_syntax::surface::{self, AttributeMacro, Entry};
use krs_syntax::{KrsSyntax, ProvenanceRole, SpecModuleAttribute, SpecModuleItem, TokenRange};
use proc_macro2::{Delimiter, Span, TokenStream, TokenTree};
use quote::{ToTokens, format_ident, quote};
use syn::ext::IdentExt;
use syn::{AttrStyle, Attribute, Ident, Item, Meta, Path};

use super::factory::{DescriptorFactory, FactoryPayload};
use super::nonce::expansion_nonce;
use super::terms::wire_key;
use crate::environment::{MacroEnvironment, SourcePosition};
use crate::provenance::host_provenance;
use crate::{ExpandError, expand_attribute, expand_function};

/// Expands one `#[k::spec_module(..)] mod name { .. }`.
pub(crate) fn spec_module(
    env: &dyn MacroEnvironment,
    attributes: TokenStream,
    item: TokenStream,
) -> crate::Result<TokenStream> {
    let attribute = SpecModuleAttribute::parse_tokens(attributes)?;
    let module = SpecModuleItem::parse_tokens(item)?;
    let facade = env.facade_path()?;
    let module_item = module.item();
    let ident = &module_item.ident;

    let mut body = TokenStream::new();
    let mut hoisted = Hoisted::default();
    for inner in module.items() {
        let expanded = expand_inner(env, inner)?;
        body.extend(hoisted.take(expanded));
    }

    let (factory, descriptor) = descriptor_factory(env, &facade, &attribute, &module)?;
    hoisted.factories.push((TokenStream::new(), factory));
    body.extend(descriptor);
    let body = publish_factories(body, &hoisted.factories);

    let outer = module_item
        .attrs
        .iter()
        .filter(|attribute| attribute.style == AttrStyle::Outer);
    let inner = module_item
        .attrs
        .iter()
        .filter(|attribute| matches!(attribute.style, AttrStyle::Inner(_)));
    let visibility = &module_item.vis;
    let unsafety = &module_item.unsafety;
    let registrations = hoisted.factories.iter().map(|(attributes, factory)| {
        quote! {
            #attributes
            #facade::__register_host_descriptor!(#ident::#factory);
        }
    });
    let framework = hoisted.framework;
    let imports = attribute.imports();
    let import_checks = (!imports.is_empty()).then(|| {
        quote! {
            #[allow(unused_imports)]
            const _: () = {
                #( use #imports as _; )*
            };
        }
    });
    Ok(quote! {
        #(#outer)*
        #visibility #unsafety mod #ident {
            #(#inner)*
            #body
        }
        #(#registrations)*
        #framework
        #import_checks
    })
}

/// Expands one item of the module body as rustc would after the outer
/// attribute returned it: the item's first expandable attribute, or its
/// function-like KRS macro.
fn expand_inner(env: &dyn MacroEnvironment, item: &Item) -> crate::Result<TokenStream> {
    if let Item::Macro(item_macro) = item
        && let Some(Entry::Function(entry)) = resolve(&item_macro.mac.path)
    {
        if let Some(attribute) = item_macro.attrs.first() {
            return Err(ExpandError::new(
                expand::SPEC_MODULE_ITEM,
                attribute.pound_token.span,
                "an attribute on a KRS macro inside a spec module is not supported; remove it",
            ));
        }
        let nested = NestedEnvironment::new(env, path_span(&item_macro.mac.path));
        return expand_function(entry, &nested, item_macro.mac.tokens.clone());
    }
    let Some(attributes) = item_attributes(item) else {
        return Ok(item.to_token_stream());
    };
    let Some(krs_index) = attributes
        .iter()
        .position(|attribute| matches!(resolve(attribute.path()), Some(Entry::Attribute(_))))
    else {
        return Ok(item.to_token_stream());
    };
    let attribute = &attributes[krs_index];
    let Some(Entry::Attribute(entry)) = resolve(attribute.path()) else {
        unreachable!("the position matched an attribute entry");
    };
    if entry == AttributeMacro::SpecModule {
        return Err(ExpandError::new(
            expand::SPEC_MODULE_ITEM,
            attribute.pound_token.span,
            "spec modules do not nest: declare this spec module beside its parent and list the parent in its `imports`",
        ));
    }
    let first_expandable = attributes
        .iter()
        .position(|candidate| !surface::is_inert(candidate.path()));
    if first_expandable != Some(krs_index) {
        return Err(ExpandError::new(
            expand::ATTRIBUTE_ORDER,
            attribute.pound_token.span,
            "a KRS attribute must come before every attribute that is not inert",
        ));
    }
    let arguments = match &attribute.meta {
        Meta::Path(_) => TokenStream::new(),
        Meta::List(list) => list.tokens.clone(),
        Meta::NameValue(_) => {
            return Err(ExpandError::new(
                expand::ATTRIBUTE_FORM,
                attribute.pound_token.span,
                "key-value macro attributes are not supported",
            ));
        }
    };
    let mut stripped = item.clone();
    if let Some(attributes) = item_attributes_mut(&mut stripped) {
        attributes.remove(krs_index);
    }
    let nested = NestedEnvironment::new(env, attribute.pound_token.span);
    expand_attribute(entry, &nested, arguments, stripped.to_token_stream())
}

/// The entry point an item inside the module invokes. Like a renderer's
/// helpers, the module does not know the authored facade alias, so it
/// recognises a path of two segments whose last segment is an entry point.
fn resolve(path: &Path) -> Option<Entry> {
    if path.leading_colon.is_some() || path.segments.len() != 2 {
        return None;
    }
    let segment = path.segments.last()?;
    if !segment.arguments.is_none() {
        return None;
    }
    Entry::from_name(&segment.ident.unraw().to_string())
}

fn path_span(path: &Path) -> Span {
    path.segments
        .first()
        .map_or_else(Span::call_site, |segment| segment.ident.span())
}

fn item_attributes(item: &Item) -> Option<&Vec<Attribute>> {
    Some(match item {
        Item::Const(item) => &item.attrs,
        Item::Enum(item) => &item.attrs,
        Item::Fn(item) => &item.attrs,
        Item::Impl(item) => &item.attrs,
        Item::Mod(item) => &item.attrs,
        Item::Static(item) => &item.attrs,
        Item::Struct(item) => &item.attrs,
        Item::Trait(item) => &item.attrs,
        Item::Type(item) => &item.attrs,
        Item::Union(item) => &item.attrs,
        Item::Macro(item) => &item.attrs,
        _ => return None,
    })
}

fn item_attributes_mut(item: &mut Item) -> Option<&mut Vec<Attribute>> {
    Some(match item {
        Item::Const(item) => &mut item.attrs,
        Item::Enum(item) => &mut item.attrs,
        Item::Fn(item) => &mut item.attrs,
        Item::Impl(item) => &mut item.attrs,
        Item::Mod(item) => &mut item.attrs,
        Item::Static(item) => &mut item.attrs,
        Item::Struct(item) => &mut item.attrs,
        Item::Trait(item) => &mut item.attrs,
        Item::Type(item) => &mut item.attrs,
        Item::Union(item) => &mut item.attrs,
        Item::Macro(item) => &mut item.attrs,
        _ => return None,
    })
}

/// Registrations taken out of the module body, to be emitted beside it.
#[derive(Default)]
struct Hoisted {
    /// Each factory's preceding attributes (its `#[cfg]`s) and its name.
    factories: Vec<(TokenStream, Ident)>,
    /// The framework-sort request, when an item asked for it.
    framework: Option<TokenStream>,
}

impl Hoisted {
    /// Returns `expanded` without its top-level `__register_host_descriptor!`
    /// and `__request_framework_sorts!` statements, which it records.
    fn take(&mut self, expanded: TokenStream) -> TokenStream {
        let trees = expanded.into_iter().collect::<Vec<_>>();
        let mut output = Vec::new();
        let mut pending = Vec::new();
        let mut index = 0;
        while index < trees.len() {
            if is_attribute_start(&trees, index) {
                pending.extend(trees[index..index + 2].iter().cloned());
                index += 2;
                continue;
            }
            if let Some(call) = surface::macro_call(&trees, index) {
                let name = call
                    .path
                    .segments
                    .last()
                    .map(|segment| segment.ident.to_string())
                    .unwrap_or_default();
                let end = index + call.len;
                let semicolon = usize::from(surface::is_punct(trees.get(end), ';'));
                if name == "__register_host_descriptor"
                    && let Ok(factory) = syn::parse2::<Ident>(call.group.stream())
                {
                    self.factories.push((pending.drain(..).collect(), factory));
                    index = end + semicolon;
                    continue;
                }
                if name == "__request_framework_sorts" {
                    let mut request = pending.drain(..).collect::<TokenStream>();
                    request.extend(trees[index..end + semicolon].iter().cloned());
                    self.framework = Some(request);
                    index = end + semicolon;
                    continue;
                }
            }
            output.append(&mut pending);
            output.push(trees[index].clone());
            index += 1;
        }
        output.append(&mut pending);
        output.into_iter().collect()
    }
}

fn is_attribute_start(trees: &[TokenTree], index: usize) -> bool {
    matches!(&trees[index], TokenTree::Punct(punct) if punct.as_char() == '#')
        && matches!(trees.get(index + 1), Some(TokenTree::Group(group)) if group.delimiter() == Delimiter::Bracket)
}

/// Makes each hoisted factory `pub(super)`, so the parent's registration can
/// name it.
fn publish_factories(body: TokenStream, factories: &[(TokenStream, Ident)]) -> TokenStream {
    let trees = body.into_iter().collect::<Vec<_>>();
    let mut output = TokenStream::new();
    for (index, tree) in trees.iter().enumerate() {
        if let TokenTree::Ident(keyword) = tree
            && keyword == "fn"
            && let Some(TokenTree::Ident(name)) = trees.get(index + 1)
            && factories.iter().any(|(_, factory)| factory == name)
        {
            output.extend(quote!(pub(super)));
        }
        output.extend([tree.clone()]);
    }
    output
}

/// The spec module's own descriptor factory, unregistered and placed inside
/// the module so that `module_path!()` names the module.
fn descriptor_factory(
    env: &dyn MacroEnvironment,
    facade: &Path,
    attribute: &SpecModuleAttribute,
    module: &SpecModuleItem,
) -> crate::Result<(Ident, TokenStream)> {
    let ident = module.ident();
    let mut anchors = module.provenance();
    anchors.extend(attribute.provenance()?);
    let fallback = TokenRange::new(ident.span(), ident.span());
    let provenance = host_provenance(env, facade, fallback, &anchors);
    let nonce = expansion_nonce(env, "spec_module", ident, fallback);
    let factory = format_ident!("__krs_spec_module_descriptor_{nonce:016x}");
    let imports = attribute
        .imports()
        .iter()
        .enumerate()
        .map(|(ordinal, path)| -> crate::Result<_> {
            let ordinal = u32::try_from(ordinal).map_err(|_| {
                ExpandError::new(
                    expand::DESCRIPTOR_CAPACITY,
                    ident.span(),
                    "too many spec-module imports",
                )
            })?;
            Ok(DescriptorModuleImport {
                key: wire_key(ProvenanceRole::SpecModuleImport, ordinal),
                path: surface::path_text(path),
            })
        })
        .collect::<crate::Result<Vec<_>>>()?;
    let grammar = WireGrammarDescriptor::SpecModule {
        key: wire_key(ProvenanceRole::SpecModuleDeclaration, 0),
        name: attribute.name().map(|name| DescriptorSpecModuleName {
            key: wire_key(ProvenanceRole::SpecModuleName, 0),
            value: name.value(),
        }),
        imports,
    };
    let wire = serde_json::to_string(&WirePayload::Grammar(Box::new(grammar)))
        .expect("KRS wire values serialize");
    let name = ident.unraw().to_string();
    let tokens = DescriptorFactory {
        facade,
        factory: &factory,
        name: quote!(#name),
        item_kind: quote!(#facade::ItemKind::Grammar),
        disambiguator: quote!("spec_module"),
        identity_label: "Cargo and Rust macro context form a valid spec-module identity",
        declared_type: quote!(::core::option::Option::None),
        payload: FactoryPayload::wire(wire, quote!(#facade::__KrsSlots::default())),
        cfg: quote!(::core::default::Default::default()),
        attributes: TokenStream::new(),
        provenance: quote!(#provenance),
        prelude: TokenStream::new(),
    }
    .render_unregistered();
    Ok((factory, tokens))
}

/// The environment of one invocation inside a spec module: rustc would
/// expand it with its own attribute as the call site.
struct NestedEnvironment<'a> {
    inner: &'a dyn MacroEnvironment,
    call_site: Span,
}

impl<'a> NestedEnvironment<'a> {
    fn new(inner: &'a dyn MacroEnvironment, call_site: Span) -> Self {
        Self { inner, call_site }
    }
}

impl MacroEnvironment for NestedEnvironment<'_> {
    fn span_file(&self, span: Span) -> String {
        self.inner.span_file(span)
    }

    fn span_package_file(&self, span: Span) -> String {
        self.inner.span_package_file(span)
    }

    fn span_start(&self, span: Span) -> Option<SourcePosition> {
        self.inner.span_start(span)
    }

    fn span_end(&self, span: Span) -> Option<SourcePosition> {
        self.inner.span_end(span)
    }

    fn call_site(&self) -> Option<Span> {
        self.inner.call_site().map(|_| self.call_site)
    }

    fn facade_path(&self) -> crate::Result<Path> {
        self.inner.facade_path()
    }
}
