use proc_macro2::{TokenStream, TokenTree};
use quote::quote;
use syn::ext::IdentExt;
use syn::parse::ParseStream;
use syn::parse::discouraged::Speculative;
use syn::spanned::Spanned;
use syn::{Attribute, Expr, Ident, ItemFn, Pat, PatIdent, Path, Token, Type, braced, bracketed};

use super::block::{
    RuleClause, RuleClauseLayout, RuleHeadResult, RuleNarrowing, take_rule_clause_attribute,
};
use super::condition::{MapUpdateExtra, RuleExtra, condition_token_range, parse_map_update};
use super::item::RuleItem;
use super::pattern::{
    NegativeLiteralSpans, RulePattern, parse_pattern_with_signs, parse_rule_pattern,
};
use crate::parse::{ParseError, validate_authored_binder};
use crate::path::is_plain_path;
use crate::{TermExpression, TermTree, TokenRange};

#[derive(Clone)]
enum MachinePatternCell {
    KHead(Pat, NegativeLiteralSpans),
    MapItem {
        key: Expr,
        value: Ident,
    },
    Term {
        pattern: Box<RulePattern>,
        tree: Box<TermTree>,
    },
}

#[derive(Clone)]
enum MachineResultCell {
    KItems(Vec<Expr>),
    Term(Box<Expr>),
}

fn parse_machine_pattern_record(
    input: ParseStream<'_>,
) -> Result<Vec<(Ident, MachinePatternCell)>, ParseError> {
    let content = input.call(|input| {
        let content;
        braced!(content in input);
        Ok(content)
    })?;
    let mut cells = Vec::new();
    while !content.is_empty() {
        let cell = content.call(Ident::parse_any)?;
        if cells
            .iter()
            .any(|(existing, _): &(Ident, MachinePatternCell)| existing.unraw() == cell.unraw())
        {
            return Err(syn::Error::new(
                cell.span(),
                format!("duplicate machine-rule cell `{}`", cell.unraw()),
            )
            .into());
        }
        content.parse::<Token![:]>()?;
        let value = if content.peek(syn::token::Bracket) {
            let sequence = content.call(|input| {
                let sequence;
                bracketed!(sequence in input);
                Ok(sequence)
            })?;
            if sequence.peek(Token![..]) {
                return Err(sequence
                    .error("a machine-rule pattern must match one k head before `..`")
                    .into());
            }
            let (head, signs) = parse_pattern_with_signs(&sequence)?;
            sequence.parse::<Token![,]>()?;
            sequence.parse::<Token![..]>()?;
            if sequence.peek(Token![,]) {
                sequence.parse::<Token![,]>()?;
            }
            if !sequence.is_empty() {
                return Err(sequence
                    .error("a machine-rule k pattern is `[head, ..]`")
                    .into());
            }
            MachinePatternCell::KHead(head, signs)
        } else if content.peek(syn::token::Brace) {
            let map = content.call(|input| {
                let map;
                braced!(map in input);
                Ok(map)
            })?;
            let key = parse_expression_before_arrow(&map)?;
            map.parse::<Token![->]>()?;
            let value = map.call(Ident::parse_any)?;
            validate_authored_binder(&value.to_string(), value.span())?;
            map.parse::<Token![,]>()?;
            map.parse::<Token![..]>()?;
            if map.peek(Token![,]) {
                map.parse::<Token![,]>()?;
            }
            if !map.is_empty() {
                return Err(map
                    .error("a machine-rule map pattern is `{ key -> value, .. }`")
                    .into());
            }
            MachinePatternCell::MapItem { key, value }
        } else {
            let (pattern, signs) = parse_pattern_with_signs(&content)?;
            let (pattern, tree) = parse_rule_pattern(pattern, true, true, signs)?;
            MachinePatternCell::Term {
                pattern: Box::new(pattern),
                tree: Box::new(tree),
            }
        };
        cells.push((cell, value));
        if content.peek(Token![,]) {
            content.parse::<Token![,]>()?;
        } else if !content.is_empty() {
            return Err(content
                .error("expected `,` between machine-rule cells")
                .into());
        }
    }
    Ok(cells)
}

pub(super) fn parse_expression_before_arrow(input: ParseStream<'_>) -> syn::Result<Expr> {
    let fork = input.fork();
    let mut tokens = TokenStream::new();
    while !fork.peek(Token![->]) {
        if fork.peek(Token![=>]) {
            return Err(fork.error("`=>` is reserved for rewrites; map entries use `->`"));
        }
        if fork.is_empty() {
            return Err(fork.error("a map item requires `key -> value`"));
        }
        tokens.extend([fork.parse::<TokenTree>()?]);
    }
    if tokens.is_empty() {
        return Err(fork.error("a map item requires a key before `->`"));
    }
    input.advance_to(&fork);
    syn::parse2(tokens)
}

fn parse_machine_result_record(
    input: ParseStream<'_>,
) -> syn::Result<Vec<(Ident, MachineResultCell)>> {
    let content;
    braced!(content in input);
    let mut cells = Vec::new();
    while !content.is_empty() {
        let cell = content.call(Ident::parse_any)?;
        if cells
            .iter()
            .any(|(existing, _): &(Ident, MachineResultCell)| existing.unraw() == cell.unraw())
        {
            return Err(syn::Error::new(
                cell.span(),
                format!("duplicate machine-rule result cell `{}`", cell.unraw()),
            ));
        }
        content.parse::<Token![:]>()?;
        let value = if content.peek(syn::token::Bracket) {
            let sequence;
            bracketed!(sequence in content);
            let mut items = Vec::new();
            while !sequence.peek(Token![..]) {
                items.push(sequence.parse::<Expr>()?);
                sequence.parse::<Token![,]>()?;
            }
            sequence.parse::<Token![..]>()?;
            if sequence.peek(Token![,]) {
                sequence.parse::<Token![,]>()?;
            }
            if !sequence.is_empty() {
                return Err(sequence.error("a machine-rule k result ends in `..`"));
            }
            MachineResultCell::KItems(items)
        } else {
            MachineResultCell::Term(Box::new(content.parse::<Expr>()?))
        };
        cells.push((cell, value));
        if content.peek(Token![,]) {
            content.parse::<Token![,]>()?;
        } else if !content.is_empty() {
            return Err(content.error("expected `,` between machine-rule result cells"));
        }
    }
    Ok(cells)
}

#[expect(
    clippy::too_many_lines,
    reason = "One linear parser retains clause layout and diagnostics at authored tokens."
)]
pub(super) fn parse_machine_clause(
    input: ParseStream<'_>,
    attributes: Vec<Attribute>,
    name: &Ident,
    configuration_type: &Type,
    clause_start: proc_macro2::Span,
) -> Result<RuleClause, ParseError> {
    let pattern_record: TokenTree = input.fork().parse()?;
    let subject_cells = parse_machine_pattern_record(input)?;
    input.parse::<Token![=>]>()?;
    let result_record: TokenTree = input.fork().parse()?;
    let result_cells = parse_machine_result_record(input)?;
    let mut layout = RuleClauseLayout {
        label: TokenRange::for_tokens(name)?,
        pattern: TokenRange::for_tokens(&pattern_record)?,
        result: TokenRange::for_tokens(&result_record)?,
        conditions: None,
    };

    let mut narrowings = Vec::new();
    if input.peek(Token![where]) {
        input.parse::<Token![where]>()?;
        layout.conditions = Some(condition_token_range(input)?);
        loop {
            let binding = input.call(Ident::parse_any)?;
            input.parse::<Token![:]>()?;
            let sort: Path = input.parse()?;
            if !is_plain_path(&sort) {
                return Err(syn::Error::new(
                    sort.span(),
                    "a rule narrowing requires a plain object-sort path",
                )
                .into());
            }
            if narrowings
                .iter()
                .any(|existing: &RuleNarrowing| existing.binding.unraw() == binding.unraw())
            {
                return Err(syn::Error::new(
                    binding.span(),
                    format!("duplicate narrowing for binding `{}`", binding.unraw()),
                )
                .into());
            }
            narrowings.push(RuleNarrowing { binding, sort });
            if !input.peek(Token![,]) {
                break;
            }
            input.parse::<Token![,]>()?;
        }
    }
    let semicolon = input.parse::<Token![;]>()?;

    let mut subject_k = None;
    let mut extras = Vec::new();
    let mut extra_bindings = Vec::new();
    for (cell, pattern) in &subject_cells {
        match pattern {
            MachinePatternCell::KHead(head, signs) => {
                if subject_k
                    .replace((cell.clone(), head.clone(), signs.clone()))
                    .is_some()
                {
                    return Err(syn::Error::new(
                        cell.span(),
                        "a machine rule has exactly one sequence-pattern cell",
                    )
                    .into());
                }
            }
            MachinePatternCell::MapItem { key, value } => {
                if result_cells
                    .iter()
                    .any(|(result_cell, _)| result_cell.unraw() == cell.unraw())
                {
                    return Err(syn::Error::new(
                        cell.span(),
                        "a preserved map-item cell is omitted from the machine-rule result",
                    )
                    .into());
                }
                extras.push(RuleExtra::HaveMap {
                    cell: cell.clone(),
                    key: Box::new(TermExpression::from_expression(key.clone())?),
                    value: value.clone(),
                });
                extra_bindings.push(value.clone());
            }
            MachinePatternCell::Term {
                pattern,
                tree: before_tree,
            } => {
                let Some((_, MachineResultCell::Term(result))) = result_cells
                    .iter()
                    .find(|(result_cell, _)| result_cell.unraw() == cell.unraw())
                else {
                    return Err(syn::Error::new(
                        cell.span(),
                        "an ordinary fixed-cell pattern requires a corresponding result",
                    )
                    .into());
                };
                let map_update = match pattern.native_pattern() {
                    Some(Pat::Ident(PatIdent { ident: base, .. })) => {
                        parse_machine_update(cell, base, result).ok()
                    }
                    _ => None,
                };
                if let Some(update) = map_update {
                    extra_bindings.push(update.base.clone());
                    extras.push(update.into());
                } else {
                    extra_bindings.extend(pattern.bindings().iter().cloned());
                    extras.push(RuleExtra::RewriteCell {
                        cell: cell.clone(),
                        before: pattern.clone(),
                        before_tree: before_tree.clone(),
                        after: Box::new(TermExpression::from_expression((**result).clone())?),
                    });
                }
            }
        }
    }
    for (cell, _) in &result_cells {
        if !subject_cells
            .iter()
            .any(|(subject_cell, _)| subject_cell.unraw() == cell.unraw())
        {
            return Err(syn::Error::new(
                cell.span(),
                "a machine-rule result cannot introduce an unmatched cell",
            )
            .into());
        }
    }
    let (computation_cell, subject_k, subject_signs) = subject_k.ok_or_else(|| {
        syn::Error::new(
            name.span(),
            "a machine rule must match one computation-cell sequence",
        )
    })?;
    let Some((_, MachineResultCell::KItems(result_k))) = result_cells
        .iter()
        .find(|(cell, _)| cell.unraw() == computation_cell.unraw())
    else {
        return Err(syn::Error::new(
            name.span(),
            "a machine rule must write its framed computation-cell sequence",
        )
        .into());
    };
    let head_result = match result_k.as_slice() {
        [] => RuleHeadResult::Erase(TokenRange::for_tokens(&name)?),
        [term] => RuleHeadResult::Replace(Box::new(TermExpression::from_expression(term.clone())?)),
        items => RuleHeadResult::Splice {
            range: TokenRange::for_tokens(&name)?,
            items: items
                .iter()
                .cloned()
                .map(TermExpression::from_expression)
                .collect::<Result<Vec<_>, _>>()?,
        },
    };

    let (attribute, retained) = take_rule_clause_attribute(attributes)?;
    let placeholder: Expr = match &head_result {
        RuleHeadResult::Replace(term) => term.expression().clone(),
        RuleHeadResult::Splice { .. } | RuleHeadResult::Erase(_) => syn::parse_quote!(true),
    };
    let item: ItemFn = syn::parse2(quote! {
        #(#retained)*
        pub fn #name(#subject_k: #configuration_type) -> #configuration_type { #placeholder }
    })?;
    let rule = RuleItem::from_readable_item(item, subject_signs)?;
    let mut bindings = rule.parameter.pattern.bindings().to_vec();
    for introduced in extra_bindings {
        if bindings
            .iter()
            .any(|binding| binding.unraw() == introduced.unraw())
        {
            return Err(syn::Error::new(
                introduced.span(),
                format!("duplicate readable rule binding `{}`", introduced.unraw()),
            )
            .into());
        }
        bindings.push(introduced);
    }
    for narrowing in &narrowings {
        if !bindings
            .iter()
            .any(|binding| binding.unraw() == narrowing.binding.unraw())
        {
            return Err(syn::Error::new(
                narrowing.binding.span(),
                format!(
                    "rule narrowing names unbound subject binding `{}`",
                    narrowing.binding.unraw()
                ),
            )
            .into());
        }
    }
    Ok(RuleClause {
        rule,
        attribute,
        narrowings,
        head_result,
        extras,
        bindings,
        computation_cell: Some(computation_cell),
        source_range: TokenRange::new(clause_start, semicolon.span),
        layout,
    })
}

fn parse_machine_update(
    cell: &Ident,
    base: &Ident,
    expression: &Expr,
) -> Result<MapUpdateExtra, ParseError> {
    parse_map_update(cell, base, expression, "the map update base must be")
}
