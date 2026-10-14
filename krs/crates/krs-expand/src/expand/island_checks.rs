//! Import checks for state islands nested in expansion inputs.

use krs_syntax::{FixedCellInitializer, InitializerCellContent};
use proc_macro2::{TokenStream, TokenTree};
use quote::{ToTokens, quote};
use syn::{FnArg, ItemFn, Pat, Path};

pub(super) fn wrapper_type_check(path: &Path) -> TokenStream {
    // Type paths retain the author's lexical imports; a generated `use` path
    // instead re-roots bare `Cell`/`KCell` spellings during expansion.
    quote! {
        let _: ::core::marker::PhantomData<#path<()>> = ::core::marker::PhantomData;
    }
}

pub(super) fn initializer_state_island_import_checks(
    cells: &[FixedCellInitializer],
) -> Vec<TokenStream> {
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

pub(super) fn consumed_state_island_import_checks(item: &ItemFn) -> Vec<TokenStream> {
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

pub(super) fn nested_state_island_import_checks(tokens: &TokenStream) -> Vec<TokenStream> {
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
