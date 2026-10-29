//! Import checks for state islands nested in expansion inputs.

use krs_syntax::{CellsExpression, FixedCellInitializer, InitializerCellContent, StateTerm};
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

/// Appends the bare `k!` and `map!` that write a cell's own content: the
/// cell's whole value, or the argument of its `Cell::new`/`KCell::new`, under
/// `Some(..)` too. A macro below a term's call (`list::item(map![..])`) is a
/// term, a collection literal, which rustc receives as calls.
fn append_initializer_state_islands(cells: &[FixedCellInitializer], output: &mut Vec<Path>) {
    for cell in cells {
        match cell.content() {
            InitializerCellContent::Leaf { value, .. } => {
                let island = match value.unwrap_present() {
                    StateTerm::KSequence(_) => cell_macro(&cell.field().expr),
                    StateTerm::Map(map) => map.island_path(),
                    _ => None,
                };
                if let Some(path) = island
                    && path.leading_colon.is_none()
                    && path.segments.len() == 1
                {
                    output.push(path.clone());
                }
            }
            InitializerCellContent::Nested { children, .. } => {
                append_initializer_state_islands(children, output);
            }
        }
    }
}

/// The path of the macro that is an initializer cell's own content: the whole
/// value or its constructor's one argument, inside `Some(..)`.
fn cell_macro(expression: &syn::Expr) -> Option<&Path> {
    match expression {
        syn::Expr::Macro(expression) => Some(&expression.mac.path),
        syn::Expr::Call(call) => cell_macro(call.args.first()?),
        _ => None,
    }
}

/// The checks of the islands of a `#[k::rule]`, claim or context fn whose
/// `cells!` parameter and body statements its expansion consumes; `cells` are
/// the parsed `cells!` terms, which tell a cell's own `map!` from a literal.
pub(super) fn consumed_state_island_import_checks(
    item: &ItemFn,
    cells: &[&CellsExpression],
) -> Vec<TokenStream> {
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
    paths.extend(cells.iter().flat_map(|cells| cells.map_islands()).cloned());
    island_import_checks(paths)
}

/// The checks of the islands of a `cells!` expression: its `k!` islands, found
/// in its tokens, and the `map!` islands that write its cells' maps, which the
/// parsed `cells` tell from a collection literal in a term.
pub(super) fn nested_state_island_import_checks(
    tokens: &TokenStream,
    cells: &CellsExpression,
) -> Vec<TokenStream> {
    let mut paths = Vec::new();
    append_nested_state_islands(tokens, &mut paths);
    paths.extend(cells.map_islands().into_iter().cloned());
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

/// Appends the paths of the `k!` islands in `tokens`. A `map![..]` is a cell's
/// own map or a collection literal, which only the parsed `cells!` tell apart
/// ([`krs_syntax::CellsExpression::map_islands`]).
fn append_nested_state_islands(tokens: &TokenStream, output: &mut Vec<Path>) {
    let trees = tokens.clone().into_iter().collect::<Vec<_>>();
    let is_colon =
        |tree: &TokenTree| matches!(tree, TokenTree::Punct(colon) if colon.as_char() == ':');
    for (index, tree) in trees.iter().enumerate() {
        if let TokenTree::Ident(ident) = tree
            && ident == "k"
            && matches!(trees.get(index + 1), Some(TokenTree::Punct(bang)) if bang.as_char() == '!')
            && matches!(trees.get(index + 2), Some(TokenTree::Group(_)))
        {
            // A qualified island such as `k::k![..]` is checked through its
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
            append_nested_state_islands(&group.stream(), output);
        }
    }
}

#[cfg(test)]
mod tests {
    use proc_macro2::TokenStream;
    use quote::quote;

    use super::nested_state_island_import_checks;

    fn checks(tokens: &TokenStream) -> Vec<String> {
        let cells = krs_syntax::parse_cells_expression(tokens.clone()).expect("the cells parse");
        nested_state_island_import_checks(tokens, &cells)
            .iter()
            .map(ToString::to_string)
            .collect()
    }

    #[test]
    fn qualified_state_islands_are_checked_through_their_whole_path() {
        assert_eq!(
            checks(&quote! {
                k: k::configuration::KCell(x, ..tail),
                env: k::configuration::Cell(k::map![a -> v]),
                regs: k::configuration::Cell(map![b -> w]),
                ..state
            }),
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

    /// A `map![..]` in a term (a computation item, a constructor's argument or
    /// field, an island's entry) is a collection literal, which no import
    /// names; only a cell's own map is an island.
    #[test]
    fn a_collection_literal_in_a_term_is_no_state_island() {
        assert_eq!(
            checks(&quote! {
                k: k::configuration::KCell(Cmd::Hold(map![x -> 1]), map![], ..tail),
                boxed: k::configuration::Cell(Cmd::Wrap { m: map![c -> 2] }),
                held: k::configuration::Cell(Cmd::Hold(map![d -> 3])),
                ..state
            }),
            Vec::<String>::new()
        );
        assert_eq!(
            checks(&quote! {
                env: Some(k::configuration::Cell(map![a -> map![b -> 1]])),
                ..state
            }),
            [quote!(
                #[allow(unused_imports)]
                use map as _;
            )
            .to_string()]
        );
    }
}
