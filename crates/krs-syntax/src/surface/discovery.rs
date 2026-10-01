//! Invocation discovery over Rust syntax and opaque macro inputs.

use proc_macro2::{Span, TokenStream};
use syn::spanned::Spanned;
use syn::visit::{self, Visit};
use syn::{Attribute, ImplItem, Item, Macro, MacroDelimiter, Meta, TraitItem};

use super::{Entry, FunctionMacro, Resolve, TokenCall, TokenCallKind, is_inert, token_calls};

/// Where an invocation's output lands.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Scope {
    /// Module level, in the inline modules listed (empty for the file root).
    Module(Vec<String>),
    /// Inside an impl, trait, function body, block, or macro input.
    Nested,
}

/// The syntax node on which an invocation was found.
#[derive(Clone, Debug)]
pub enum InvocationNode<'ast> {
    /// An attributed item or item-level macro.
    Item(&'ast Item),
    /// An attributed impl item or impl-level macro.
    ImplItem(&'ast ImplItem),
    /// An attributed trait item or trait-level macro.
    TraitItem(&'ast TraitItem),
    /// A macro in another syntax position.
    Macro(&'ast Macro),
    /// A call in opaque token trees.
    Tokens(TokenCall),
}

/// An attributed node, including invalid invocations that a consumer must diagnose.
#[derive(Clone, Debug)]
pub struct AttributeInvocation<'ast> {
    /// All attributes on the node.
    pub attributes: &'ast [Attribute],
    /// The first attribute whose path names a facade member.
    pub facade_index: usize,
    /// The first attribute rustc expands or evaluates.
    pub first_expandable_index: usize,
    /// The unraw facade member name of the facade attribute.
    pub member: String,
    /// The resolved entry, including a function entry used as an attribute.
    pub entry: Option<Entry>,
}

/// The invocation's input and entry-point facts.
#[derive(Clone, Debug)]
pub enum InvocationKind<'ast> {
    /// A function-like entry point, with its body and optional syntax delimiter.
    Function {
        /// The function-like entry point.
        entry: FunctionMacro,
        /// The macro body without delimiters.
        tokens: TokenStream,
        /// The delimiter for a call reached through Rust syntax.
        /// Raw calls retain their group in [`InvocationNode::Tokens`].
        delimiter: Option<&'ast MacroDelimiter>,
    },
    /// An attributed syntax node.
    Attribute(AttributeInvocation<'ast>),
    /// An attribute in opaque macro input.
    RawAttribute(TokenCall),
}

/// One invocation in deterministic traversal order, before its descendants.
#[derive(Clone, Debug)]
pub struct Invocation<'ast> {
    /// The entry point and input facts.
    pub kind: InvocationKind<'ast>,
    /// The span of the invoking macro or attribute.
    pub call_site: Span,
    /// The span replaced by expansion, including an enclosing item when applicable.
    pub replaced: Span,
    /// The syntax node or opaque-token call.
    pub node: InvocationNode<'ast>,
    /// The output scope at the call site.
    pub scope: Scope,
    /// The enclosing invocation's index in the returned vector.
    pub parent: Option<usize>,
    /// Whether a non-KRS macro's opaque input encloses this invocation.
    pub raw_tokens: bool,
}

impl<'ast> Invocation<'ast> {
    /// The item whose own invocation this is:
    /// the function-like call of an item macro, or the facade attribute of an item that is not a macro.
    /// An item macro under a facade attribute is therefore classified by its own entry, not by the attribute.
    #[must_use]
    pub fn owned_item(&self) -> Option<&'ast Item> {
        let InvocationNode::Item(item) = self.node else {
            return None;
        };
        let owned = match item {
            Item::Macro(_) => matches!(self.kind, InvocationKind::Function { .. }),
            _ => matches!(self.kind, InvocationKind::Attribute(_)),
        };
        owned.then_some(item)
    }
}

/// Finds every KRS invocation in `file`, resolving the file root and each inline module separately.
/// Rust attribute expressions and descendants of invalid attributed nodes must be visited under every resolver.
/// Descendants retain the attributed node's invocation index as their parent; consumers may select only outermost invocations.
/// The attribute expressions of a function-like KRS item macro are its descendants, since its replaced span contains them.
#[must_use]
pub fn invocations<'ast>(file: &'ast syn::File, resolve: &dyn Resolve) -> Vec<Invocation<'ast>> {
    let mut discovery = Discovery {
        resolve: resolve.scoped(&file.items),
        scope: Scope::Module(Vec::new()),
        parent: None,
        found: Vec::new(),
    };
    discovery.visit_file(file);
    discovery.found
}

struct Discovery<'ast> {
    resolve: Box<dyn Resolve>,
    scope: Scope,
    parent: Option<usize>,
    found: Vec<Invocation<'ast>>,
}

impl<'ast> Discovery<'ast> {
    fn record(&mut self, invocation: Invocation<'ast>) -> usize {
        let index = self.found.len();
        self.found.push(invocation);
        index
    }

    fn scan_tokens(&mut self, tokens: &TokenStream, raw_tokens: bool) {
        for call in token_calls(tokens, self.resolve.as_ref()) {
            let raw_tokens = raw_tokens || call.in_non_krs_macro;
            let call_site = match &call.kind {
                TokenCallKind::Function(group) => call.span.join(group.span()),
                TokenCallKind::Attribute(attribute) => call.span.join(attribute.group.span()),
            }
            .unwrap_or(call.span);
            let kind = match (&call.entry, &call.kind) {
                (Entry::Function(entry), TokenCallKind::Function(group)) => {
                    InvocationKind::Function {
                        entry: *entry,
                        tokens: group.stream(),
                        delimiter: None,
                    }
                }
                _ => InvocationKind::RawAttribute(call.clone()),
            };
            let index = self.record(Invocation {
                kind,
                call_site,
                replaced: call_site,
                node: InvocationNode::Tokens(call.clone()),
                scope: Scope::Nested,
                parent: self.parent,
                raw_tokens,
            });
            if let TokenCallKind::Function(group) = call.kind {
                let saved = self.parent.replace(index);
                self.scan_tokens(&group.stream(), raw_tokens);
                self.parent = saved;
            }
        }
    }

    /// Records a function-like KRS macro before its attribute expressions and body,
    /// which lie inside its replaced span and are therefore its descendants.
    fn visit_mac(
        &mut self,
        attrs: &'ast [Attribute],
        mac: &'ast Macro,
        node: InvocationNode<'ast>,
        replaced: Span,
    ) {
        let Some(Entry::Function(entry)) = self.resolve.resolve(&mac.path) else {
            self.visit_authored_attributes(attrs);
            self.scan_tokens(&mac.tokens, true);
            return;
        };
        let index = self.record(Invocation {
            kind: InvocationKind::Function {
                entry,
                tokens: mac.tokens.clone(),
                delimiter: Some(&mac.delimiter),
            },
            call_site: mac.span(),
            replaced,
            node,
            scope: self.scope.clone(),
            parent: self.parent,
            raw_tokens: false,
        });
        let saved = self.parent.replace(index);
        self.visit_authored_attributes(attrs);
        self.scan_tokens(&mac.tokens, false);
        self.parent = saved;
    }

    fn visit_attributes(
        &mut self,
        attrs: &'ast [Attribute],
        node: InvocationNode<'ast>,
        replaced: Span,
    ) -> Option<usize> {
        let facade_index = attrs.iter().position(|attribute| {
            !is_inert(attribute.path()) && self.resolve.facade_member(attribute.path()).is_some()
        })?;
        let first_expandable_index = attrs
            .iter()
            .position(|attribute| !is_inert(attribute.path()))
            .expect("a facade attribute is expandable");
        let attribute = &attrs[facade_index];
        let entry = self.resolve.resolve(attribute.path());
        let member = self
            .resolve
            .facade_member(attribute.path())
            .expect("a facade member");
        let index = self.record(Invocation {
            kind: InvocationKind::Attribute(AttributeInvocation {
                attributes: attrs,
                facade_index,
                first_expandable_index,
                member,
                entry,
            }),
            call_site: attribute.span(),
            replaced,
            node,
            scope: self.scope.clone(),
            parent: self.parent,
            raw_tokens: false,
        });
        Some(index)
    }

    fn nested(&mut self, visit: impl FnOnce(&mut Self)) {
        let saved = std::mem::replace(&mut self.scope, Scope::Nested);
        visit(self);
        self.scope = saved;
    }

    fn visit_authored_attributes(&mut self, attrs: &'ast [Attribute]) {
        for attribute in attrs {
            self.visit_attribute(attribute);
        }
    }

    fn attributed(
        &mut self,
        attrs: &'ast [Attribute],
        node: InvocationNode<'ast>,
        span: Span,
        visit: impl FnOnce(&mut Self),
    ) {
        let saved = self.parent;
        if let Some(index) = self.visit_attributes(attrs, node, span) {
            self.parent = Some(index);
            if let InvocationKind::Attribute(attribute) = &self.found[index].kind
                && let Meta::List(list) = &attrs[attribute.facade_index].meta
            {
                self.scan_tokens(&list.tokens, false);
            }
        }
        visit(self);
        self.parent = saved;
    }
}

impl<'ast> Visit<'ast> for Discovery<'ast> {
    fn visit_attribute(&mut self, attribute: &'ast Attribute) {
        self.nested(|this| visit::visit_attribute(this, attribute));
    }

    fn visit_item(&mut self, item: &'ast Item) {
        let attrs = item_attributes(item).unwrap_or_default();
        self.attributed(
            attrs,
            InvocationNode::Item(item),
            item.span(),
            |this| match item {
                Item::Mod(module) => {
                    let saved = this.scope.clone();
                    if let Scope::Module(modules) = &mut this.scope {
                        modules.push(module.ident.to_string());
                    }
                    if let Some((_, items)) = &module.content {
                        let scoped = this.resolve.scoped(items);
                        let saved_resolver = std::mem::replace(&mut this.resolve, scoped);
                        this.visit_authored_attributes(&module.attrs);
                        for item in items {
                            this.visit_item(item);
                        }
                        this.resolve = saved_resolver;
                    } else {
                        this.visit_authored_attributes(&module.attrs);
                    }
                    this.scope = saved;
                }
                Item::Macro(node) => {
                    this.visit_mac(
                        &node.attrs,
                        &node.mac,
                        InvocationNode::Item(item),
                        item.span(),
                    );
                }
                _ => this.nested(|this| visit::visit_item(this, item)),
            },
        );
    }

    fn visit_impl_item(&mut self, item: &'ast ImplItem) {
        let attrs = match item {
            ImplItem::Const(item) => &item.attrs,
            ImplItem::Fn(item) => &item.attrs,
            ImplItem::Type(item) => &item.attrs,
            ImplItem::Macro(node) => {
                self.attributed(
                    &node.attrs,
                    InvocationNode::ImplItem(item),
                    item.span(),
                    |this| {
                        this.visit_mac(
                            &node.attrs,
                            &node.mac,
                            InvocationNode::ImplItem(item),
                            item.span(),
                        );
                    },
                );
                return;
            }
            _ => return visit::visit_impl_item(self, item),
        };
        self.attributed(attrs, InvocationNode::ImplItem(item), item.span(), |this| {
            this.nested(|this| visit::visit_impl_item(this, item));
        });
    }

    fn visit_trait_item(&mut self, item: &'ast TraitItem) {
        let attrs = match item {
            TraitItem::Const(item) => &item.attrs,
            TraitItem::Fn(item) => &item.attrs,
            TraitItem::Type(item) => &item.attrs,
            TraitItem::Macro(node) => {
                self.attributed(
                    &node.attrs,
                    InvocationNode::TraitItem(item),
                    item.span(),
                    |this| {
                        this.visit_mac(
                            &node.attrs,
                            &node.mac,
                            InvocationNode::TraitItem(item),
                            item.span(),
                        );
                    },
                );
                return;
            }
            _ => return visit::visit_trait_item(self, item),
        };
        self.attributed(
            attrs,
            InvocationNode::TraitItem(item),
            item.span(),
            |this| {
                this.nested(|this| visit::visit_trait_item(this, item));
            },
        );
    }

    fn visit_macro(&mut self, mac: &'ast Macro) {
        self.visit_mac(&[], mac, InvocationNode::Macro(mac), mac.span());
    }

    fn visit_block(&mut self, block: &'ast syn::Block) {
        self.nested(|this| visit::visit_block(this, block));
    }
}

fn item_attributes(item: &Item) -> Option<&[Attribute]> {
    Some(match item {
        Item::Const(item) => &item.attrs,
        Item::Enum(item) => &item.attrs,
        Item::ExternCrate(item) => &item.attrs,
        Item::Fn(item) => &item.attrs,
        Item::ForeignMod(item) => &item.attrs,
        Item::Impl(item) => &item.attrs,
        Item::Macro(item) => &item.attrs,
        Item::Mod(item) => &item.attrs,
        Item::Static(item) => &item.attrs,
        Item::Struct(item) => &item.attrs,
        Item::Trait(item) => &item.attrs,
        Item::TraitAlias(item) => &item.attrs,
        Item::Type(item) => &item.attrs,
        Item::Union(item) => &item.attrs,
        Item::Use(item) => &item.attrs,
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::surface::{AttributeMacro, AuthoredResolver, FacadeScope};
    use std::collections::BTreeSet;

    #[test]
    fn parents_raw_inputs_and_output_scopes() {
        let file: syn::File = syn::parse_quote! {
            mod language {
                k::rules! { k::id!(nested) }
                other! { [k::rules! { k::id!(opaque) }] }
                #[k::function]
                fn f() { let _ = k::id!(body); }
            }
        };
        let calls = invocations(&file, &AuthoredResolver::new("k"));
        assert_eq!(calls.len(), 6);
        assert_eq!(
            calls.iter().map(|call| call.parent).collect::<Vec<_>>(),
            [None, Some(0), None, Some(2), None, Some(4)]
        );
        assert_eq!(
            calls.iter().map(|call| call.raw_tokens).collect::<Vec<_>>(),
            [false, false, true, true, false, false]
        );
        assert_eq!(calls[0].scope, Scope::Module(vec!["language".to_owned()]));
        assert_eq!(calls[4].scope, calls[0].scope);
        for index in [1, 2, 3, 5] {
            assert_eq!(calls[index].scope, Scope::Nested);
        }
        assert!(matches!(calls[4].node, InvocationNode::Item(Item::Fn(_))));
        assert!(matches!(calls[5].node, InvocationNode::Macro(_)));
        assert!(matches!(
            calls[0].kind,
            InvocationKind::Function {
                delimiter: Some(MacroDelimiter::Brace(_)),
                ..
            }
        ));
    }

    #[test]
    fn attribute_order_and_invalid_nodes_preserve_descendants() {
        let file: syn::File = syn::parse_quote! {
            #[doc = "inert"]
            #[derive(Clone)]
            #[k::sort]
            struct S(k::id!(hidden));
            #[k::rules]
            fn f() { k::id!(hidden); }
            #[k::unknown]
            fn g() { k::id!(hidden); }
            #[k::function = "wrong"]
            fn h() { k::id!(hidden); }
        };
        let authored = AuthoredResolver::new("k");
        let generated =
            crate::surface::GeneratedResolver::new("k", &syn::parse_quote!(::host::facade));
        let facade = FacadeScope::new(BTreeSet::from(["k".to_owned()]));
        for resolver in [&authored as &dyn Resolve, &generated, &facade] {
            let calls = invocations(&file, resolver);
            assert_eq!(calls.len(), 8);
            assert_eq!(
                calls.iter().map(|call| call.parent).collect::<Vec<_>>(),
                [None, Some(0), None, Some(2), None, Some(4), None, Some(6)],
            );
            for index in [1, 3, 5, 7] {
                assert!(matches!(
                    calls[index].kind,
                    InvocationKind::Function {
                        entry: FunctionMacro::Id,
                        delimiter: Some(_),
                        ..
                    }
                ));
                assert_eq!(calls[index].scope, Scope::Nested);
            }
        }
        let calls = invocations(&file, &authored)
            .into_iter()
            .filter(|call| call.parent.is_none())
            .collect::<Vec<_>>();
        assert_eq!(calls.len(), 4);
        let InvocationKind::Attribute(attribute) = &calls[0].kind else {
            panic!("attribute")
        };
        assert_eq!(attribute.facade_index, 2);
        assert_eq!(attribute.first_expandable_index, 1);
        assert_eq!(attribute.member, "sort");
        assert_eq!(
            attribute.entry,
            Some(Entry::Attribute(AttributeMacro::Sort))
        );
        let InvocationKind::Attribute(attribute) = &calls[2].kind else {
            panic!("attribute")
        };
        assert_eq!(attribute.entry, None);
        assert_eq!(attribute.member, "unknown");
    }

    #[test]
    fn rust_attribute_expressions_on_krs_macros_are_their_descendants() {
        let file: syn::File = syn::parse_quote! {
            #[name = k::id!(item_attribute)]
            k::id!(item_body);
            impl S {
                #[name = k::id!(impl_attribute)]
                k::id!(impl_body);
            }
            trait T {
                #[name = k::id!(trait_attribute)]
                k::id!(trait_body);
            }
            #[name = k::id!(opaque_attribute)]
            other!(k::id!(opaque_body));
        };
        let calls = invocations(&file, &AuthoredResolver::new("k"));
        assert_eq!(calls.len(), 8);
        assert_eq!(
            calls.iter().map(|call| call.parent).collect::<Vec<_>>(),
            [None, Some(0), None, Some(2), None, Some(4), None, None],
        );
        assert!(matches!(calls[0].node, InvocationNode::Item(_)));
        assert!(matches!(calls[2].node, InvocationNode::ImplItem(_)));
        assert!(matches!(calls[4].node, InvocationNode::TraitItem(_)));
        assert_eq!(calls[0].scope, Scope::Module(Vec::new()));
        for index in [1, 3, 5, 6] {
            assert!(matches!(calls[index].node, InvocationNode::Macro(_)));
            assert_eq!(calls[index].scope, Scope::Nested);
            assert!(!calls[index].raw_tokens);
        }
        assert!(matches!(calls[7].node, InvocationNode::Tokens(_)));
        assert!(calls[7].raw_tokens);
    }

    #[test]
    fn an_item_macro_owns_its_call_and_not_its_facade_attribute() {
        let file: syn::File = syn::parse_quote! {
            #[k::sort]
            k::rules! {}
            #[k::rules]
            other! {}
            #[k::sort]
            trait T {}
        };
        let calls = invocations(&file, &AuthoredResolver::new("k"));
        assert_eq!(calls.len(), 4);
        assert_eq!(
            calls
                .iter()
                .map(|call| call.owned_item().map(std::ptr::from_ref))
                .collect::<Vec<_>>(),
            [
                None,
                Some(std::ptr::from_ref(&file.items[0])),
                None,
                Some(std::ptr::from_ref(&file.items[2])),
            ],
        );
        assert_eq!(calls[1].parent, Some(0));
    }

    #[test]
    fn invalid_macro_attributes_parent_syntax_and_opaque_descendants() {
        let file: syn::File = syn::parse_quote! {
            #[k::rules]
            #[name = k::id!(attribute)]
            other! { k::id!(opaque) }
            #[k::function = k::id!(key_value)]
            fn f() { k::id!(body); }
        };
        let calls = invocations(&file, &AuthoredResolver::new("k"));
        assert_eq!(calls.len(), 6);
        assert_eq!(
            calls.iter().map(|call| call.parent).collect::<Vec<_>>(),
            [None, Some(0), Some(0), None, Some(3), Some(3)],
        );
        assert!(matches!(calls[1].node, InvocationNode::Macro(_)));
        assert!(matches!(calls[2].node, InvocationNode::Tokens(_)));
        assert!(calls[2].raw_tokens);
        assert!(matches!(calls[4].node, InvocationNode::Macro(_)));
    }

    #[test]
    fn scopes_resolve_file_root_and_every_inline_module() {
        let file: syn::File = syn::parse_quote! {
            use host as k;
            k::rules! {}
            mod nested {
                use super::k;
                use k as local;
                local::rules! {}
                mod shadowed {
                    use other as k;
                    k::rules! {}
                }
            }
        };
        let resolver = FacadeScope::new(BTreeSet::from(["host".to_owned()]));
        let calls = invocations(&file, &resolver);
        assert_eq!(calls.len(), 2);
        assert_eq!(calls[0].scope, Scope::Module(vec![]));
        assert_eq!(calls[1].scope, Scope::Module(vec!["nested".to_owned()]));
    }

    #[test]
    fn walks_impl_trait_patterns_types_and_statements() {
        let file: syn::File = syn::parse_quote! {
            impl S {
                k::rules! {}
                #[k::function]
                fn f() { let k::id!(p): k::id!(t) = k::id!(e); }
            }
            trait T {
                k::rules! {}
                #[k::function]
                fn f() { k::id!(statement); }
            }
        };
        let calls = invocations(&file, &AuthoredResolver::new("k"));
        assert_eq!(calls.len(), 8);
        assert!(calls.iter().all(|call| call.scope == Scope::Nested));
        assert!(matches!(calls[0].node, InvocationNode::ImplItem(_)));
        assert!(matches!(calls[1].node, InvocationNode::ImplItem(_)));
        assert!(matches!(calls[5].node, InvocationNode::TraitItem(_)));
        assert_eq!(calls[2].parent, Some(1));
        assert_eq!(calls[7].parent, Some(6));
    }

    #[test]
    fn rust_attribute_expressions_are_nested_invocations() {
        let file: syn::File = syn::parse_quote! {
            #[doc = k::id!(attribute)]
            struct S;
        };
        let calls = invocations(&file, &AuthoredResolver::new("k"));
        assert_eq!(calls.len(), 1);
        assert!(matches!(calls[0].node, InvocationNode::Macro(_)));
        assert_eq!(calls[0].scope, Scope::Nested);
        assert_eq!(calls[0].parent, None);
    }

    #[test]
    fn tool_attributes_are_never_facade_attributes() {
        let file: syn::File = syn::parse_quote! {
            use k as rustfmt;
            #[rustfmt::skip]
            fn f() {}
        };
        let resolver = FacadeScope::new(BTreeSet::from(["k".to_owned()]));
        assert!(invocations(&file, &resolver).is_empty());
    }

    #[test]
    fn nested_non_krs_macro_inputs_and_attribute_arguments() {
        let file: syn::File = syn::parse_quote! {
            k::rules! { other! { k::id!(nested) } }
            #[k::function(k::id!(argument))]
            fn f() {}
        };
        let calls = invocations(&file, &AuthoredResolver::new("k"));
        assert_eq!(calls.len(), 4);
        assert!(calls[1].raw_tokens);
        assert_eq!(calls[1].parent, Some(0));
        assert!(!calls[3].raw_tokens);
        assert_eq!(calls[3].parent, Some(2));
    }
}
