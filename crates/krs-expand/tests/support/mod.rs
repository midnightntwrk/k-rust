//! A non-proc-macro host for tour-minimal: a rustc-faithful test environment
//! and a driver that expands every invocation of the whole authored file.

#![allow(dead_code)] // each test binary uses part of the driver

use std::cell::Cell;

use krs_expand::sink::AuthoredFile;
use krs_expand::{MacroEnvironment, SourcePosition};
use krs_ir::Position;
use krs_syntax::surface::{AttributeMacro, FunctionMacro};
use proc_macro2::{LineColumn, Span, TokenStream, TokenTree};
use quote::ToTokens;
use syn::spanned::Spanned;

pub const TOUR_MINIMAL: &str = include_str!("../../../../tests/tour-minimal/src/lib.rs");

/// Facade `::k`, display file `src/lib.rs`, 1-based positions from fallback
/// spans of the whole parsed file, and the current invocation's call site.
///
/// Like rustc, it locates every span outside the authored file (call-site
/// tokens and tokens re-parsed from strings) at the invocation's call site.
pub struct TestEnvironment<'a> {
    authored: Option<&'a AuthoredFile>,
    call_site: Cell<Option<Span>>,
}

impl<'a> TestEnvironment<'a> {
    pub fn new(authored: Option<&'a AuthoredFile>) -> Self {
        Self {
            authored,
            call_site: Cell::new(None),
        }
    }

    /// Sets the call site of the next invocation.
    pub fn set_call_site(&self, span: Span) {
        self.call_site.set(Some(span));
    }

    fn resolve(&self, span: Span) -> Span {
        if self
            .authored
            .is_some_and(|authored| authored.contains(span))
        {
            span
        } else {
            self.call_site.get().unwrap_or(span)
        }
    }

    fn position(location: LineColumn) -> Option<SourcePosition> {
        Position::from_proc_macro2(location).ok().map(Into::into)
    }
}

impl MacroEnvironment for TestEnvironment<'_> {
    fn span_file(&self, _span: Span) -> String {
        "src/lib.rs".to_owned()
    }

    fn span_start(&self, span: Span) -> Option<SourcePosition> {
        Self::position(self.resolve(span).start())
    }

    fn span_end(&self, span: Span) -> Option<SourcePosition> {
        Self::position(self.resolve(span).end())
    }

    fn call_site(&self) -> Option<Span> {
        self.call_site.get()
    }

    fn facade_path(&self) -> krs_expand::Result<syn::Path> {
        syn::parse_str("::k").map_err(krs_expand::ExpandError::from)
    }
}

/// One expanded invocation.
pub struct Expansion {
    /// The `krs-macros` entry-point name.
    pub kind: &'static str,
    /// The call site rustc reports: the `#[...]` attribute, or the macro path
    /// through its closing delimiter.
    pub call_site: Span,
    /// The tokens the expansion replaces: the whole attributed item, the
    /// item-level macro, or the nested macro's tokens.
    pub replaced: Span,
    /// The expansion.
    pub output: TokenStream,
    /// Invocations found in `output`, as (position of the first replaced tree,
    /// number of replaced trees, expansion).
    pub nested: Vec<(Vec<usize>, usize, Expansion)>,
}

/// Every `k::k!` invocation in `tokens`, as (tree position, span).
fn nested_k_invocations(
    tokens: &TokenStream,
    path: &mut Vec<usize>,
    found: &mut Vec<(Vec<usize>, TokenStream, Span)>,
) {
    let trees = tokens.clone().into_iter().collect::<Vec<_>>();
    for (index, tree) in trees.iter().enumerate() {
        if let [
            TokenTree::Ident(facade),
            TokenTree::Punct(first),
            TokenTree::Punct(second),
            TokenTree::Ident(entry),
            TokenTree::Punct(bang),
            TokenTree::Group(group),
        ] = &trees[index..trees.len().min(index + 6)]
            && facade == "k"
            && first.as_char() == ':'
            && second.as_char() == ':'
            && entry == "k"
            && bang.as_char() == '!'
        {
            let span = facade.span().join(group.span()).expect("one fallback file");
            let mut at = path.clone();
            at.push(index);
            found.push((at, group.stream(), span));
        }
        if let TokenTree::Group(group) = tree {
            path.push(index);
            nested_k_invocations(&group.stream(), path, found);
            path.pop();
        }
    }
}

/// The `k::<entry>` name of a two-segment facade path.
fn facade_entry(path: &syn::Path) -> Option<String> {
    let [facade, entry] = [path.segments.first()?, path.segments.last()?];
    (path.segments.len() == 2 && facade.ident == "k").then(|| entry.ident.to_string())
}

/// Removes the first KRS entry-point attribute and returns its entry, its
/// arguments, and its span.
fn take_attribute(attrs: &mut Vec<syn::Attribute>) -> Option<(AttributeMacro, TokenStream, Span)> {
    let index = attrs.iter().position(|attribute| {
        facade_entry(attribute.path())
            .and_then(|name| AttributeMacro::from_name(&name))
            .is_some()
    })?;
    let attribute = attrs.remove(index);
    let entry = AttributeMacro::from_name(&facade_entry(attribute.path())?)?;
    let arguments = match &attribute.meta {
        syn::Meta::Path(_) => TokenStream::new(),
        syn::Meta::List(list) => list.tokens.clone(),
        syn::Meta::NameValue(_) => panic!("KRS attributes take no `=` value"),
    };
    Some((entry, arguments, attribute.span()))
}

/// Expands `k::k!` invocations of `output` in turn, as rustc does after the
/// enclosing attribute macro.
fn expand_nested(
    env: &TestEnvironment<'_>,
    output: &TokenStream,
) -> Vec<(Vec<usize>, usize, Expansion)> {
    let mut found = Vec::new();
    nested_k_invocations(output, &mut Vec::new(), &mut found);
    found
        .into_iter()
        .map(|(at, input, span)| {
            env.call_site.set(Some(span));
            let output = krs_expand::expand_function(FunctionMacro::K, env, input)
                .expect("the nested k::k! expands");
            let nested = expand_nested(env, &output);
            (
                at,
                6,
                Expansion {
                    kind: FunctionMacro::K.name(),
                    call_site: span,
                    replaced: span,
                    output,
                    nested,
                },
            )
        })
        .collect()
}

fn attribute_expansion(
    env: &TestEnvironment<'_>,
    attrs: &mut Vec<syn::Attribute>,
    replaced: Span,
    item: impl FnOnce(&[syn::Attribute]) -> TokenStream,
) -> Expansion {
    let (entry, arguments, call_site) = take_attribute(attrs).expect("a KRS attribute");
    let item = item(attrs);
    env.call_site.set(Some(call_site));
    let output = krs_expand::expand_attribute(entry, env, arguments, item)
        .unwrap_or_else(|error| panic!("#[k::{}] failed: {error}", entry.name()));
    let nested = expand_nested(env, &output);
    Expansion {
        kind: entry.name(),
        call_site,
        replaced,
        output,
        nested,
    }
}

/// Lexes tour-minimal as one authored file and expands its outermost KRS
/// invocations in source order, with nested invocations under their parent.
pub fn expand_tour_minimal() -> (AuthoredFile, Vec<Expansion>) {
    let (authored, tokens) =
        AuthoredFile::lex("src/lib.rs", TOUR_MINIMAL).expect("tour-minimal lexes");
    let file: syn::File = syn::parse2(tokens).expect("tour-minimal parses");
    let env = TestEnvironment::new(Some(&authored));
    let mut expansions = Vec::new();
    for item in file.items {
        match item {
            syn::Item::Macro(item) => {
                let name = facade_entry(&item.mac.path).expect("a facade-qualified macro");
                let entry = FunctionMacro::from_name(&name).expect("a krs-macros entry point");
                let call_site = item.mac.span();
                env.call_site.set(Some(call_site));
                let output = krs_expand::expand_function(entry, &env, item.mac.tokens.clone())
                    .unwrap_or_else(|error| panic!("k::{name}! failed: {error}"));
                let nested = expand_nested(&env, &output);
                expansions.push(Expansion {
                    kind: entry.name(),
                    call_site,
                    replaced: item.span(),
                    output,
                    nested,
                });
            }
            syn::Item::Enum(mut item) => {
                let replaced = item.span();
                let mut attrs = std::mem::take(&mut item.attrs);
                expansions.push(attribute_expansion(&env, &mut attrs, replaced, |attrs| {
                    item.attrs = attrs.to_vec();
                    item.to_token_stream()
                }));
            }
            syn::Item::Struct(mut item) => {
                let replaced = item.span();
                let mut attrs = std::mem::take(&mut item.attrs);
                expansions.push(attribute_expansion(&env, &mut attrs, replaced, |attrs| {
                    item.attrs = attrs.to_vec();
                    item.to_token_stream()
                }));
            }
            syn::Item::Impl(item) => {
                for impl_item in item.items {
                    let syn::ImplItem::Fn(mut function) = impl_item else {
                        continue;
                    };
                    let replaced = function.span();
                    let mut attrs = std::mem::take(&mut function.attrs);
                    expansions.push(attribute_expansion(&env, &mut attrs, replaced, |attrs| {
                        function.attrs = attrs.to_vec();
                        function.to_token_stream()
                    }));
                }
            }
            _ => {}
        }
    }
    (authored, expansions)
}
