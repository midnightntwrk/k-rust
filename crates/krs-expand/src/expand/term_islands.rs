//! Term islands: `term!`, `k!`, `map!`, `cells!`, and `fragment!`.

use crate::ExpandError;
use krs_diagnostic::codes::expand;
use krs_syntax::KrsSyntax;
use krs_syntax::{
    MapBody, StateTerm, TermExpression, TermTree, parse_cells_expression,
    parse_k_sequence_expression, parse_map_expression,
};
use proc_macro2::{Span, TokenStream};
use quote::quote;

use super::island_checks::{nested_state_island_import_checks, wrapper_type_check};
use super::tokens::call_site_path;
use crate::environment::MacroEnvironment;

pub(crate) fn term(input: TokenStream) -> crate::Result<TokenStream> {
    let term = krs_syntax::TermExpression::parse_tokens(input)?;
    let expression = term.expression();
    Ok(quote! {{
        let _krs_typecheck_named_term = || {
            let _ = #expression;
        };
        ::core::panic!("`term!` has no runtime value in KRS")
    }})
}

pub(crate) fn k(env: &dyn MacroEnvironment, input: TokenStream) -> crate::Result<TokenStream> {
    let sequence = parse_k_sequence_expression(input)?;
    let expressions = sequence.items().iter().map(TermExpression::expression);
    let facade = env.facade_path()?;
    Ok(quote! {{
        let _krs_typecheck_computation_items = || {
            #(let _ = #expressions;)*
        };
        #facade::builtin::KSequence::__new()
    }})
}

pub(crate) fn map(env: &dyn MacroEnvironment, input: TokenStream) -> crate::Result<TokenStream> {
    let map = parse_map_expression(input)?;
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

pub(crate) fn cells(input: TokenStream) -> crate::Result<TokenStream> {
    let island_import_checks = nested_state_island_import_checks(&input);
    let cells = parse_cells_expression(input)?;
    let mut expressions = Vec::new();
    let wrappers = cells
        .entries()
        .iter()
        .filter_map(krs_syntax::CellsEntry::wrapper);
    let mut owners = Vec::new();
    for entry in cells.entries() {
        collect_state_expressions(entry.value(), &mut expressions, &mut owners);
    }
    let wrapper_checks = wrappers.map(wrapper_type_check);
    let owners = owners
        .into_iter()
        .map(call_site_path)
        .collect::<Result<Vec<_>, _>>()?;
    let expressions = expressions
        .into_iter()
        .map(TermExpression::expression)
        .collect::<Vec<_>>();
    Ok(quote! {{
        let _krs_typecheck_cells = || {
            #(#wrapper_checks)*
            #(#island_import_checks)*
            #(let _ = ::core::any::TypeId::of::<#owners>();)*
            #(let _ = #expressions;)*
        };
        ::core::panic!("`cells!` has no runtime value in KRS")
    }})
}

/// The terms of one `cells!` result state and the cell structs its
/// collection instances name (KF-023).
fn collect_state_expressions<'a>(
    state: &'a StateTerm,
    expressions: &mut Vec<&'a TermExpression>,
    owners: &mut Vec<&'a syn::Path>,
) {
    if let StateTerm::Instances(list) = state {
        owners.extend(list.instances().map(krs_syntax::InstanceItem::owner));
    }
    match state {
        StateTerm::Present(_) | StateTerm::Instances(_) => {
            for nested in state.nested_states() {
                collect_state_expressions(nested, expressions, owners);
            }
        }
        _ => expressions.extend(state.terms()),
    }
}

pub(crate) fn fragment(
    env: &dyn MacroEnvironment,
    input: &TokenStream,
) -> crate::Result<TokenStream> {
    let facade = env.facade_path()?;
    let record: syn::ExprStruct = syn::parse2(input.clone())?;
    let parsed = krs_syntax::TermExpression::parse_tokens(quote!(#facade::fragment![#input]))?;
    let TermTree::Cell(cell) = parsed.tree() else {
        return Err(ExpandError::new(
            expand::FRAGMENT_SHAPE,
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
