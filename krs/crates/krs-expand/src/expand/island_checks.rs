//! Import checks for state islands nested in expansion inputs.

use krs_syntax::{FixedCellInitializer, InitializerCellContent};
use proc_macro2::{Delimiter, TokenStream, TokenTree};
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

/// Appends the paths of the `k!` and `map!` islands a `cells!` payload's cells hold: a wrapper's
/// content (`Cell(map![..])`, under `Some(..)` too) and an instance's child (`Owner { c: map![..] }`).
/// A term's arguments (`Cmd::Hold(map![..])`), a computation cell's items (`KCell(map![..], ..)`)
/// and an island's own payload hold terms, where a `map![..]` is a collection literal, the calls
/// it denotes, which rustc receives as calls and which no import names.
fn append_nested_state_islands(tokens: &TokenStream, output: &mut Vec<Path>) {
    append_state_islands(tokens, true, output);
}

/// [`append_nested_state_islands`] over `tokens`, which hold a cell's `map!` island where
/// `maps`: a computation cell's items (`KCell(..)`) are terms, and a `map![..]` there a literal.
fn append_state_islands(tokens: &TokenStream, maps: bool, output: &mut Vec<Path>) {
    let trees = tokens.clone().into_iter().collect::<Vec<_>>();
    let is_colon =
        |tree: &TokenTree| matches!(tree, TokenTree::Punct(colon) if colon.as_char() == ':');
    let mut payload = None;
    for (index, tree) in trees.iter().enumerate() {
        if let TokenTree::Ident(ident) = tree
            && (ident == "k" || (maps && ident == "map"))
            && matches!(trees.get(index + 1), Some(TokenTree::Punct(bang)) if bang.as_char() == '!')
            && matches!(trees.get(index + 2), Some(TokenTree::Group(_)))
        {
            payload = Some(index + 2);
            // A qualified island such as `k::map![..]` is checked through its
            // whole path; a bare one through the binding that imports it.
            let mut start = index;
            while start >= 3
                && is_colon(&trees[start - 1])
                && is_colon(&trees[start - 2])
                && matches!(trees[start - 3], TokenTree::Ident(_))
            {
                start -= 3;
            }
            let path = trees[start..=index]
                .iter()
                .cloned()
                .collect::<TokenStream>();
            output.push(syn::parse2(path).expect("an authored macro path is a Rust path"));
        }
        if let TokenTree::Group(group) = tree {
            let wrapper = index
                .checked_sub(1)
                .and_then(|previous| trees.get(previous))
                .and_then(|previous| match previous {
                    TokenTree::Ident(ident) => Some(ident.to_string()),
                    _ => None,
                });
            let holds = match (group.delimiter(), wrapper.as_deref()) {
                (Delimiter::Parenthesis, Some("Cell" | "Some")) => Some(maps),
                (Delimiter::Parenthesis, Some("KCell")) => Some(false),
                (Delimiter::Parenthesis, _) => None,
                _ => (payload != Some(index)).then_some(maps),
            };
            if let Some(maps) = holds {
                append_state_islands(&group.stream(), maps, output);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use quote::quote;

    use super::nested_state_island_import_checks;

    #[test]
    fn qualified_state_islands_are_checked_through_their_whole_path() {
        let checks = nested_state_island_import_checks(&quote! {
            k: k::configuration::KCell(x, ..),
            env: k::configuration::Cell(k::map![a -> v, ..]),
            regs: k::configuration::Cell(map![b -> w, ..]),
            ..state
        });
        let checks = checks.iter().map(ToString::to_string).collect::<Vec<_>>();
        assert_eq!(
            checks,
            [
                quote!(
                    #[allow(unused_imports)]
                    use k::map as _;
                )
                .to_string(),
                quote!(
                    #[allow(unused_imports)]
                    use map as _;
                )
                .to_string(),
            ]
        );
    }

    /// A `map![..]` in a term, a constructor's argument or an island's entry, is a collection
    /// literal, which no import names; a wrapper's and an instance child's are islands.
    #[test]
    fn a_collection_literal_in_a_term_is_no_state_island() {
        let checks = nested_state_island_import_checks(&quote! {
            k: k::configuration::KCell(Cmd::Hold(map![x -> 1]), map![], ..tail),
            env: Some(k::configuration::Cell(map![a -> map![b -> 1], ..])),
            pool: [Member { item: map![c -> 2] }, ..],
            ..state
        });
        let checks = checks.iter().map(ToString::to_string).collect::<Vec<_>>();
        assert_eq!(
            checks,
            [quote!(
                #[allow(unused_imports)]
                use map as _;
            )
            .to_string()]
        );
    }
}
