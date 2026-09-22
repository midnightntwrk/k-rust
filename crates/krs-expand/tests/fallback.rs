//! Expands every tour-minimal invocation in an ordinary (non-proc-macro)
//! process, where `proc_macro2` uses its fallback implementation. A surviving
//! `proc_macro`-only call panics here.

use std::cell::Cell;

use krs_expand::{AttributeMacro, FunctionMacro, MacroEnvironment, SourcePosition};
use proc_macro2::{LineColumn, Span, TokenStream, TokenTree};
use quote::ToTokens;
use syn::spanned::Spanned;

const TOUR_MINIMAL: &str = include_str!("../../../tests/tour-minimal/src/lib.rs");

/// Facade `::k`, display file `src/lib.rs`, 1-based positions from fallback
/// spans of the whole parsed file, and the current invocation's call site.
struct TestEnvironment {
    call_site: Cell<Option<Span>>,
}

impl TestEnvironment {
    fn position(location: LineColumn) -> Option<SourcePosition> {
        Some(SourcePosition {
            line: u32::try_from(location.line).ok()?,
            column: u32::try_from(location.column).ok()?.checked_add(1)?,
        })
    }
}

impl MacroEnvironment for TestEnvironment {
    fn span_file(&self, _span: Span) -> String {
        "src/lib.rs".to_owned()
    }

    fn span_start(&self, span: Span) -> Option<SourcePosition> {
        Self::position(span.start())
    }

    fn span_end(&self, span: Span) -> Option<SourcePosition> {
        Self::position(span.end())
    }

    fn call_site(&self) -> Option<Span> {
        self.call_site.get()
    }

    fn facade_path(&self) -> syn::Result<syn::Path> {
        syn::parse_str("::k")
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

/// Every `k::k!` invocation nested in `tokens`, as (input, call site).
fn nested_k_invocations(tokens: TokenStream, found: &mut Vec<(TokenStream, Span)>) {
    let trees = tokens.into_iter().collect::<Vec<_>>();
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
            found.push((group.stream(), span));
        }
        if let TokenTree::Group(group) = tree {
            nested_k_invocations(group.stream(), found);
        }
    }
}

#[derive(Debug, Default)]
struct Expanded {
    attributes: Vec<AttributeMacro>,
    functions: Vec<FunctionMacro>,
}

fn expand_attribute(
    env: &TestEnvironment,
    expanded: &mut Expanded,
    entry: AttributeMacro,
    arguments: TokenStream,
    call_site: Span,
    item: TokenStream,
) -> TokenStream {
    env.call_site.set(Some(call_site));
    let output = krs_expand::expand_attribute(entry, env, arguments, item)
        .unwrap_or_else(|error| panic!("#[k::{}] failed: {error}", entry.name()));
    expanded.attributes.push(entry);
    output
}

fn expand_function(
    env: &TestEnvironment,
    expanded: &mut Expanded,
    mac: &syn::Macro,
) -> TokenStream {
    let name = facade_entry(&mac.path).expect("a facade-qualified macro");
    let entry = FunctionMacro::from_name(&name).expect("a krs-macros entry point");
    env.call_site.set(Some(mac.span()));
    let output = krs_expand::expand_function(entry, env, mac.tokens.clone())
        .unwrap_or_else(|error| panic!("k::{name}! failed: {error}"));
    expanded.functions.push(entry);
    output
}

#[test]
fn tour_minimal_expands_in_a_fallback_process() {
    let file = syn::parse_file(TOUR_MINIMAL).expect("tour-minimal parses");
    let env = TestEnvironment {
        call_site: Cell::new(None),
    };
    let mut expanded = Expanded::default();
    let mut outputs = Vec::new();
    for item in file.items {
        match item {
            syn::Item::Macro(item) => outputs.push(expand_function(&env, &mut expanded, &item.mac)),
            syn::Item::Enum(mut item) => {
                let (entry, arguments, span) = take_attribute(&mut item.attrs).unwrap();
                outputs.push(expand_attribute(
                    &env,
                    &mut expanded,
                    entry,
                    arguments,
                    span,
                    item.to_token_stream(),
                ));
            }
            syn::Item::Struct(mut item) => {
                let (entry, arguments, span) = take_attribute(&mut item.attrs).unwrap();
                outputs.push(expand_attribute(
                    &env,
                    &mut expanded,
                    entry,
                    arguments,
                    span,
                    item.to_token_stream(),
                ));
            }
            syn::Item::Impl(item) => {
                for impl_item in item.items {
                    let syn::ImplItem::Fn(mut function) = impl_item else {
                        continue;
                    };
                    let (entry, arguments, span) = take_attribute(&mut function.attrs).unwrap();
                    let mut nested = Vec::new();
                    nested_k_invocations(function.block.to_token_stream(), &mut nested);
                    outputs.push(expand_attribute(
                        &env,
                        &mut expanded,
                        entry,
                        arguments,
                        span,
                        function.to_token_stream(),
                    ));
                    for (input, span) in nested {
                        env.call_site.set(Some(span));
                        outputs.push(
                            krs_expand::expand_function(FunctionMacro::K, &env, input)
                                .expect("the nested k::k! expands"),
                        );
                        expanded.functions.push(FunctionMacro::K);
                    }
                }
            }
            _ => {}
        }
    }

    assert_eq!(
        expanded.attributes,
        [
            AttributeMacro::Constructors,
            AttributeMacro::Configuration,
            AttributeMacro::Init,
        ]
    );
    assert_eq!(
        expanded.functions,
        [FunctionMacro::Sorts, FunctionMacro::K, FunctionMacro::Rules]
    );
    let sorts = outputs[0].to_string();
    assert!(sorts.contains(":: k :: HostSourceAnchor :: new (\"src/lib.rs\" . to_owned ()"));
    // `k::sorts! { ... }` spans 10:1 through 12:2 of the authored file.
    assert!(sorts.contains(
        ":: k :: HostSourcePosition :: new (10u32 , 1u32) . expect (\"stable proc-macro positions are one-based\") , :: k :: HostSourcePosition :: new (12u32 , 2u32)"
    ));
    assert!(sorts.contains(":: k :: AnchorPrecision :: Exact"));
    assert!(outputs.iter().all(|output| !output.is_empty()));
}

#[test]
fn every_builtin_token_island_expands_in_a_fallback_process() {
    let env = TestEnvironment {
        call_site: Cell::new(None),
    };
    for (entry, input) in [
        (FunctionMacro::Id, "\"$x\""),
        (FunctionMacro::Bytes, "b\"\\x00\""),
        (FunctionMacro::Anonymous, ""),
        (FunctionMacro::OrBool, "a, b"),
    ] {
        let output = krs_expand::expand_function(entry, &env, input.parse().unwrap()).unwrap();
        assert!(output.to_string().contains("has no runtime value"));
    }
    let error =
        krs_expand::expand_function(FunctionMacro::Id, &env, "\"x\"".parse().unwrap()).unwrap_err();
    assert_eq!(error.to_string(), "invalid builtin `Id` token");
}

#[test]
fn entry_point_names_round_trip() {
    for &entry in AttributeMacro::ALL {
        assert_eq!(AttributeMacro::from_name(entry.name()), Some(entry));
    }
    for &entry in FunctionMacro::ALL {
        assert_eq!(FunctionMacro::from_name(entry.name()), Some(entry));
    }
    assert_eq!(AttributeMacro::from_name("sorts"), None);
    assert_eq!(FunctionMacro::from_name("sort"), None);
}
