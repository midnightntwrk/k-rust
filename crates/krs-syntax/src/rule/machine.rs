use proc_macro2::{TokenStream, TokenTree};
use quote::{quote, quote_spanned};
use syn::ext::IdentExt;
use syn::parse::discouraged::Speculative;
use syn::parse::{ParseStream, Parser};
use syn::spanned::Spanned;
use syn::{Attribute, Expr, Ident, ItemFn, Pat, PatIdent, Path, Token, Type, braced, bracketed};

use super::block::{
    BracketAlternative, RuleClause, RuleClauseLayout, RuleHeadResult, RuleNarrowing,
    take_rule_clause_attribute,
};
use super::condition::{MapUpdateExtra, RuleExtra, condition_token_range, parse_map_update};
use super::item::RuleItem;
use super::pattern::{
    NegativeLiteralSpans, RulePattern, parse_pattern_with_signs, parse_rule_pattern,
};
use crate::parse::{ParseError, validate_authored_binder};
use crate::path::is_plain_path;
use crate::{
    InstanceField, InstanceItem, InstanceList, InstanceListDelimiter, InstanceRest,
    StateMacroContext, StateMacroRemainder, StateTerm, TermExpression, TermTree, TokenRange,
};

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
    /// `Some(p)`, `None`, or an instance list (KF-023).
    State(Box<StateTerm>),
    /// A bracketed value: the computation cell's `[head, ..]` or a List
    /// collection's instances (KF-023), read once the clause is assembled.
    Bracket(proc_macro2::Group),
}

#[derive(Clone)]
enum MachineResultCell {
    KItems(Vec<Expr>),
    Term(Box<Expr>),
    /// `Some(e)`, `None`, or an instance list (KF-023).
    State(Box<StateTerm>),
    /// A bracketed value, read like the subject's.
    Bracket(proc_macro2::Group),
}

/// What a subject record's optional or collection entry expects of the
/// same cell in the result record.
#[derive(Clone, Copy, Eq, PartialEq)]
enum StateFamily {
    Optional,
    Instances,
}

fn state_family(state: &StateTerm) -> StateFamily {
    if matches!(state, StateTerm::Instances(_)) {
        StateFamily::Instances
    } else {
        StateFamily::Optional
    }
}

fn readable_error(span: proc_macro2::Span, reason: &'static str) -> ParseError {
    crate::SyntaxError::new(
        crate::SyntaxErrorKind::InvalidStateMacro {
            macro_name: "rules",
            reason,
        },
        span,
    )
    .into()
}

/// Parses a subject-record value that is `None`, `Some(p)`, or an instance
/// list (KF-023), or returns `None` for every other value.
fn parse_readable_pattern_state(input: ParseStream<'_>) -> Result<Option<StateTerm>, ParseError> {
    let fork = input.fork();
    if let Ok(ident) = fork.parse::<Ident>() {
        if ident == "None" && (fork.is_empty() || fork.peek(Token![,])) {
            input.parse::<Ident>()?;
            return Ok(Some(StateTerm::Absent(TokenRange::for_tokens(&ident)?)));
        }
        if ident == "Some" && fork.peek(syn::token::Paren) {
            input.parse::<Ident>()?;
            let tokens = input.call(|input| {
                let inner;
                syn::parenthesized!(inner in input);
                inner.parse::<TokenStream>()
            })?;
            return Ok(Some(StateTerm::Present(Box::new(StateTerm::Term(
                TermExpression::parse_pattern_tokens(tokens)?,
            )))));
        }
    }
    if input.peek(syn::token::Brace) {
        let group: proc_macro2::Group = input.fork().parse()?;
        if !contains_top_level_arrow(&group) {
            let group: proc_macro2::Group = input.parse()?;
            return Ok(Some(StateTerm::Instances(parse_readable_instances(
                &group,
                StateMacroContext::Pattern,
            )?)));
        }
    }
    Ok(None)
}

/// Parses the result-record value of a cell whose subject value was an
/// optional or collection state.
fn parse_readable_result_state(
    input: ParseStream<'_>,
    family: StateFamily,
) -> Result<StateTerm, ParseError> {
    match family {
        StateFamily::Optional => {
            let fork = input.fork();
            let ident = fork.parse::<Ident>().ok();
            match ident {
                Some(ident) if ident == "None" && (fork.is_empty() || fork.peek(Token![,])) => {
                    input.parse::<Ident>()?;
                    Ok(StateTerm::Absent(TokenRange::for_tokens(&ident)?))
                }
                Some(ident) if ident == "Some" && fork.peek(syn::token::Paren) => {
                    input.parse::<Ident>()?;
                    let expression = input.call(|input| {
                        let inner;
                        syn::parenthesized!(inner in input);
                        let expression: Expr = inner.parse()?;
                        if !inner.is_empty() {
                            return Err(inner.error("`Some(..)` holds one term"));
                        }
                        Ok(expression)
                    })?;
                    Ok(StateTerm::Present(Box::new(StateTerm::Term(
                        TermExpression::from_expression(expression)?,
                    ))))
                }
                _ => Err(readable_error(
                    input.span(),
                    "an optional cell's result is `Some(..)` or `None`",
                )),
            }
        }
        StateFamily::Instances => {
            if !(input.peek(syn::token::Bracket) || input.peek(syn::token::Brace)) {
                return Err(readable_error(
                    input.span(),
                    "a collection cell's result is an instance list `{ .. }` or `[ .. ]`",
                ));
            }
            let group: proc_macro2::Group = input.parse()?;
            Ok(StateTerm::Instances(parse_readable_instances(
                &group,
                StateMacroContext::Expression,
            )?))
        }
    }
}

/// Splits a group's payload at its top-level commas.
fn top_level_items(tokens: TokenStream) -> Vec<TokenStream> {
    let mut items = Vec::new();
    let mut current = TokenStream::new();
    for token in tokens {
        if matches!(&token, TokenTree::Punct(punct) if punct.as_char() == ',') {
            items.push(std::mem::take(&mut current));
        } else {
            current.extend([token]);
        }
    }
    if !current.is_empty() {
        items.push(current);
    }
    items
}

fn is_dots(tokens: &TokenStream) -> bool {
    let trees = tokens.clone().into_iter().collect::<Vec<_>>();
    matches!(trees.as_slice(), [TokenTree::Punct(first), TokenTree::Punct(second)]
        if first.as_char() == '.' && second.as_char() == '.')
}

/// Whether one list item is an instance record whose body ends in a rest:
/// `[label @] Decl { .., .. }` or `Decl { .., ..label }`.
fn is_instance_record(tokens: &TokenStream) -> bool {
    let trees = tokens.clone().into_iter().collect::<Vec<_>>();
    let Some(TokenTree::Group(body)) = trees.last() else {
        return false;
    };
    if body.delimiter() != proc_macro2::Delimiter::Brace || trees.len() < 2 {
        return false;
    }
    let fields = top_level_items(body.stream());
    fields.last().is_some_and(|last| {
        let last = last.clone().into_iter().collect::<Vec<_>>();
        matches!(last.as_slice(),
            [TokenTree::Punct(first), TokenTree::Punct(second), ..]
                if first.as_char() == '.' && second.as_char() == '.')
    })
}

/// Whether a bracketed subject value that reads neither way looks like a
/// List collection: it has no item before its `..`, an item after it, or an
/// instance record that ends in a rest. It only picks which reading's error
/// to report; a value that reads one way is read by the cell's declared type
/// (see [`BracketReadings`]).
fn readable_bracket_is_list(group: &proc_macro2::Group) -> bool {
    let items = top_level_items(group.stream());
    let Some(first) = items.first() else {
        return false;
    };
    is_dots(first)
        || items
            .iter()
            .enumerate()
            .any(|(index, item)| is_dots(item) && index + 1 != items.len())
        || items.iter().any(is_instance_record)
}

/// Whether a braced value is a map pattern `{ key -> value, .. }` (or a
/// misspelled one with `=>`) rather than an instance list.
fn contains_top_level_arrow(group: &proc_macro2::Group) -> bool {
    let trees = group.stream().into_iter().collect::<Vec<_>>();
    trees.windows(2).any(|window| {
        matches!(&window[0], TokenTree::Punct(first) if matches!(first.as_char(), '-' | '='))
            && matches!(&window[1], TokenTree::Punct(second) if second.as_char() == '>')
    })
}

/// Parses a readable instance list `{ .. }` or `[ .. ]` (KF-023): records
/// `[label @] Decl { child: value, .., }` and one `..` rest.
fn parse_readable_instances(
    group: &proc_macro2::Group,
    context: StateMacroContext,
) -> Result<InstanceList, ParseError> {
    let delimiter = if group.delimiter() == proc_macro2::Delimiter::Bracket {
        InstanceListDelimiter::Bracket
    } else {
        InstanceListDelimiter::Brace
    };
    let mut front = Vec::new();
    let mut back = Vec::new();
    let mut rest = None;
    for item in top_level_items(group.stream()) {
        if is_dots(&item) {
            if rest.is_some() {
                return Err(readable_error(
                    item.span(),
                    "a collection entry has at most one `..`",
                ));
            }
            rest = Some(StateMacroRemainder::Anonymous(TokenRange::for_tokens(
                &item,
            )?));
            continue;
        }
        let parsed = parse_readable_instance(item, context)?;
        if rest.is_some() {
            if delimiter == InstanceListDelimiter::Brace {
                return Err(readable_error(
                    parsed.range().first(),
                    "the `..` of a Set or Map collection is last",
                ));
            }
            back.push(parsed);
        } else {
            front.push(parsed);
        }
    }
    Ok(InstanceList::new(
        delimiter,
        front,
        rest.unwrap_or(StateMacroRemainder::Exact),
        back,
    ))
}

fn parse_readable_instance(
    tokens: TokenStream,
    context: StateMacroContext,
) -> Result<InstanceItem, ParseError> {
    let range = TokenRange::for_tokens(&tokens)?;
    let mut trees = tokens.into_iter().collect::<Vec<_>>();
    let label = match trees.as_slice() {
        [TokenTree::Ident(label), TokenTree::Punct(at), ..] if at.as_char() == '@' => {
            if context == StateMacroContext::Expression {
                return Err(readable_error(
                    label.span(),
                    "a result instance has no label; write `..label` inside it to update the matched instance",
                ));
            }
            validate_authored_binder(&label.to_string(), label.span())?;
            let label = label.clone();
            trees.drain(..2);
            Some(label)
        }
        _ => None,
    };
    let Some(TokenTree::Group(body)) = trees.pop() else {
        return Err(readable_error(
            range.first(),
            "a collection instance is a cell record `Decl { .. }`",
        ));
    };
    if body.delimiter() != proc_macro2::Delimiter::Brace || trees.is_empty() {
        return Err(readable_error(
            body.span(),
            "a collection instance is a cell record `Decl { .. }`",
        ));
    }
    let owner: Path = syn::parse2(trees.into_iter().collect())?;
    if !is_plain_path(&owner) {
        return Err(readable_error(
            owner.span(),
            "an instance's cell struct is a plain Rust path",
        ));
    }
    let mut fields: Vec<InstanceField> = Vec::new();
    let mut rest = InstanceRest::Exact;
    let items = top_level_items(body.stream());
    let count = items.len();
    for (index, item) in items.into_iter().enumerate() {
        let trees = item.clone().into_iter().collect::<Vec<_>>();
        if let [TokenTree::Punct(first), TokenTree::Punct(second), tail @ ..] = trees.as_slice()
            && first.as_char() == '.'
            && second.as_char() == '.'
        {
            if index + 1 != count {
                return Err(readable_error(
                    first.span(),
                    "an instance record's `..` is last",
                ));
            }
            rest = match tail {
                [] => InstanceRest::Open(TokenRange::for_tokens(&item)?),
                [TokenTree::Ident(label)] if context == StateMacroContext::Expression => {
                    InstanceRest::Update {
                        label: label.clone(),
                        range: TokenRange::for_tokens(&item)?,
                    }
                }
                _ => {
                    return Err(readable_error(
                        first.span(),
                        "an instance record ends in `..`, or in a result `..label`",
                    ));
                }
            };
            continue;
        }
        let [TokenTree::Ident(name), TokenTree::Punct(colon), value @ ..] = trees.as_slice() else {
            return Err(readable_error(
                item.span(),
                "an instance child is `name: value`",
            ));
        };
        if colon.as_char() != ':' || value.is_empty() {
            return Err(readable_error(
                item.span(),
                "an instance child is `name: value`",
            ));
        }
        if fields.iter().any(|field| field.name() == name) {
            return Err(readable_error(
                name.span(),
                "an instance record names each child once",
            ));
        }
        let value = value.iter().cloned().collect::<TokenStream>();
        fields.push(InstanceField::new(
            name.clone(),
            parse_readable_child(value, context)?,
        ));
    }
    Ok(InstanceItem::new(range, label, owner, fields, rest))
}

/// One readable instance child: `[items.., ..]` for a computation cell, or
/// a term.
fn parse_readable_child(
    tokens: TokenStream,
    context: StateMacroContext,
) -> Result<StateTerm, ParseError> {
    let trees = tokens.clone().into_iter().collect::<Vec<_>>();
    if let [TokenTree::Group(group)] = trees.as_slice()
        && group.delimiter() == proc_macro2::Delimiter::Bracket
    {
        let mut items = Vec::new();
        let mut tail = StateMacroRemainder::Exact;
        let chunks = top_level_items(group.stream());
        let count = chunks.len();
        for (index, chunk) in chunks.into_iter().enumerate() {
            if is_dots(&chunk) {
                if index + 1 != count {
                    return Err(readable_error(
                        chunk.span(),
                        "a readable sequence ends in `..`",
                    ));
                }
                tail = StateMacroRemainder::Anonymous(TokenRange::for_tokens(&chunk)?);
                continue;
            }
            items.push(readable_term(chunk, context)?);
        }
        return Ok(StateTerm::KSequence(crate::KSequence::readable(
            group.stream(),
            items,
            tail,
        )));
    }
    Ok(StateTerm::Term(readable_term(tokens, context)?))
}

fn readable_term(
    tokens: TokenStream,
    context: StateMacroContext,
) -> Result<TermExpression, ParseError> {
    Ok(match context {
        StateMacroContext::Pattern => TermExpression::parse_pattern_tokens(tokens)?,
        StateMacroContext::Expression => {
            TermExpression::from_expression(syn::parse2::<Expr>(tokens)?)?
        }
    })
}

/// The bindings a readable subject state introduces, in first-occurrence
/// order: every unqualified identifier and `name @ ..` alias of its terms.
/// Instance labels are not bindings.
fn readable_state_bindings(state: &StateTerm) -> Vec<Ident> {
    let mut output: Vec<Ident> = Vec::new();
    for term in state.terms() {
        for node in crate::term::split_rewrite_images(term.nodes()).0 {
            let binding = match node {
                crate::TermNode::Reference(path) => crate::path::unqualified_path_ident(path),
                crate::TermNode::As { binding, .. } => Some(binding),
                _ => None,
            };
            if let Some(binding) = binding
                && !output
                    .iter()
                    .any(|existing| existing.unraw() == binding.unraw())
            {
                output.push(binding.clone());
            }
        }
    }
    output
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
        let value = if let Some(state) = parse_readable_pattern_state(&content)? {
            MachinePatternCell::State(Box::new(state))
        } else if content.peek(syn::token::Bracket) {
            MachinePatternCell::Bracket(content.parse()?)
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
            let (pattern, tree) = match pattern {
                // `frame: _` matches a whole cell whose content the rule
                // ignores, such as a nested cell it overwrites (KF-016).
                Pat::Wild(wildcard) if wildcard.attrs.is_empty() => {
                    let tree = TermTree::Wildcard(TokenRange::for_tokens(&wildcard)?);
                    (
                        RulePattern::Native {
                            pattern: Pat::Wild(wildcard),
                            paths: Vec::new(),
                            bindings: Vec::new(),
                            nodes: Vec::new(),
                        },
                        tree,
                    )
                }
                pattern => parse_rule_pattern(pattern, true, true, signs)?,
            };
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
    states: &[(Ident, StateFamily)],
) -> Result<Vec<(Ident, MachineResultCell)>, ParseError> {
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
            .any(|(existing, _): &(Ident, MachineResultCell)| existing.unraw() == cell.unraw())
        {
            return Err(syn::Error::new(
                cell.span(),
                format!("duplicate machine-rule result cell `{}`", cell.unraw()),
            )
            .into());
        }
        content.parse::<Token![:]>()?;
        let family = states
            .iter()
            .find(|(name, _)| name.unraw() == cell.unraw())
            .map(|(_, family)| *family);
        let value = if let Some(family) = family {
            MachineResultCell::State(Box::new(parse_readable_result_state(&content, family)?))
        } else if content.peek(syn::token::Bracket) {
            MachineResultCell::Bracket(content.parse()?)
        } else {
            MachineResultCell::Term(Box::new(content.parse::<Expr>()?))
        };
        cells.push((cell, value));
        if content.peek(Token![,]) {
            content.parse::<Token![,]>()?;
        } else if !content.is_empty() {
            return Err(content
                .error("expected `,` between machine-rule result cells")
                .into());
        }
    }
    Ok(cells)
}

pub(super) fn parse_machine_clause(
    input: ParseStream<'_>,
    attributes: &[Attribute],
    name: &Ident,
    configuration_type: &Type,
    clause_start: proc_macro2::Span,
) -> Result<RuleClause, ParseError> {
    let pattern_record: TokenTree = input.fork().parse()?;
    let subject_cells = parse_machine_pattern_record(input)?;
    if subject_cells.is_empty() {
        return Err(syn::Error::new(
            pattern_record.span(),
            "a machine rule selects at least one cell",
        )
        .into());
    }
    if input.peek(Token![|]) {
        // K's #Or combines terms; a machine record is a configuration
        // pattern, not a term (KF-030).
        return Err(crate::SyntaxError::new(
            crate::SyntaxErrorKind::InvalidPatternOr {
                reason: "`|` cannot join whole machine records; write one rule per record, or put `|` inside a cell value".to_owned(),
            },
            input.span(),
        )
        .into());
    }
    input.parse::<Token![=>]>()?;
    let result_record: TokenTree = input.fork().parse()?;
    let states = subject_cells
        .iter()
        .filter_map(|(cell, pattern)| match pattern {
            MachinePatternCell::State(state) => Some((cell.clone(), state_family(state))),
            _ => None,
        })
        .collect::<Vec<_>>();
    let result_cells = parse_machine_result_record(input, &states)?;
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
    let clause = MachineClause {
        attributes,
        name,
        configuration_type,
        pattern_record: &pattern_record,
        result_record: &result_record,
        layout,
        narrowings: &narrowings,
        source_range: TokenRange::new(clause_start, semicolon.span),
    };
    read_machine_clause(&clause, &subject_cells, &result_cells)
}

/// The parsed parts of one cell-record clause that every reading of its
/// bracketed values shares.
struct MachineClause<'a> {
    attributes: &'a [Attribute],
    name: &'a Ident,
    configuration_type: &'a Type,
    pattern_record: &'a TokenTree,
    result_record: &'a TokenTree,
    layout: RuleClauseLayout,
    narrowings: &'a [RuleNarrowing],
    source_range: TokenRange,
}

/// The readings a bracketed subject value admits with its result: the
/// computation cell's `[head, ..] => [items.., ..]`, and a List collection's
/// instances.
struct BracketReadings {
    computation: bool,
    list: bool,
}

impl BracketReadings {
    fn of(group: &proc_macro2::Group, result: Option<&MachineResultCell>) -> Self {
        let computation = bracket_head(group).is_ok()
            && matches!(result, Some(MachineResultCell::Bracket(result)) if bracket_items(result).is_ok());
        let list = parse_readable_instances(group, StateMacroContext::Pattern).is_ok()
            && match result {
                None => true,
                Some(MachineResultCell::Bracket(result)) => {
                    parse_readable_instances(result, StateMacroContext::Expression).is_ok()
                }
                Some(_) => false,
            };
        Self { computation, list }
    }
}

/// Reads a cell-record clause's bracketed values (KF-023). A bracketed value
/// that reads only one way is read that way. One that reads both ways, such
/// as `job: [Job { payload: p }, ..] => job: [..]`, depends on the cell's
/// declared type, which only the collector knows: when no other cell is the
/// computation cell, the clause is read with it as the computation cell and
/// carries its List reading beside it, and the collector keeps the reading
/// the configuration declares.
fn read_machine_clause(
    clause: &MachineClause<'_>,
    subject_cells: &[(Ident, MachinePatternCell)],
    result_cells: &[(Ident, MachineResultCell)],
) -> Result<RuleClause, ParseError> {
    let mut definite = Vec::new();
    let mut ambiguous = Vec::new();
    let mut unreadable = Vec::new();
    for (cell, pattern) in subject_cells {
        let MachinePatternCell::Bracket(group) = pattern else {
            continue;
        };
        let result = result_cells
            .iter()
            .find(|(result_cell, _)| result_cell.unraw() == cell.unraw())
            .map(|(_, result)| result);
        let readings = BracketReadings::of(group, result);
        match (readings.computation, readings.list) {
            (true, false) => definite.push(cell),
            (true, true) => ambiguous.push(cell),
            (false, true) => {}
            (false, false) => unreadable.push((cell, group)),
        }
    }
    if let [_, second, ..] = definite.as_slice() {
        return Err(syn::Error::new(
            second.span(),
            "a machine rule must match at most one computation-cell sequence",
        )
        .into());
    }
    let read = |computation: Option<&Ident>| {
        let (subject, result) = read_brackets(subject_cells, result_cells, computation)?;
        assemble_machine_clause(clause, &subject, &result)
    };
    if let Some(cell) = definite.first() {
        return read(Some(cell));
    }
    let Some(cell) = ambiguous.first() else {
        // A value that reads neither way reports the error of the reading
        // its shape suggests.
        let computation = unreadable
            .iter()
            .find(|(_, group)| !readable_bracket_is_list(group))
            .map(|(cell, _)| *cell);
        return read(computation);
    };
    match (read(Some(cell)), read(None)) {
        (Ok(mut computation), Ok(list)) => {
            computation.bracket_alternative = BracketAlternative::from_list_reading(list, cell);
            Ok(computation)
        }
        (Ok(computation), Err(_)) => Ok(computation),
        (Err(_), Ok(list)) => Ok(list),
        (Err(error), Err(_)) => Err(error),
    }
}

/// A clause's subject and result cells.
type MachineCells = (
    Vec<(Ident, MachinePatternCell)>,
    Vec<(Ident, MachineResultCell)>,
);

/// Reads every bracketed value: `computation`'s as the computation cell's
/// `[head, ..]`, every other one as a List collection's instances.
fn read_brackets(
    subject_cells: &[(Ident, MachinePatternCell)],
    result_cells: &[(Ident, MachineResultCell)],
    computation: Option<&Ident>,
) -> Result<MachineCells, ParseError> {
    let is_computation =
        |cell: &Ident| computation.is_some_and(|computation| computation.unraw() == cell.unraw());
    let is_list = |cell: &Ident| {
        !is_computation(cell)
            && subject_cells.iter().any(|(subject_cell, pattern)| {
                subject_cell.unraw() == cell.unraw()
                    && matches!(pattern, MachinePatternCell::Bracket(_))
            })
    };
    let mut subject = Vec::with_capacity(subject_cells.len());
    for (cell, pattern) in subject_cells {
        let pattern = match pattern {
            MachinePatternCell::Bracket(group) if is_computation(cell) => {
                let (head, signs) = bracket_head(group)?;
                MachinePatternCell::KHead(head, signs)
            }
            MachinePatternCell::Bracket(group) => MachinePatternCell::State(Box::new(
                StateTerm::Instances(parse_readable_instances(group, StateMacroContext::Pattern)?),
            )),
            pattern => pattern.clone(),
        };
        subject.push((cell.clone(), pattern));
    }
    let mut result = Vec::with_capacity(result_cells.len());
    for (cell, value) in result_cells {
        let value = match value {
            MachineResultCell::Bracket(group) if is_list(cell) => {
                MachineResultCell::State(Box::new(StateTerm::Instances(parse_readable_instances(
                    group,
                    StateMacroContext::Expression,
                )?)))
            }
            MachineResultCell::Bracket(group) => MachineResultCell::KItems(bracket_items(group)?),
            MachineResultCell::Term(expression) if is_list(cell) => {
                return Err(readable_error(
                    expression.span(),
                    "a collection cell's result is an instance list `{ .. }` or `[ .. ]`",
                ));
            }
            value => value.clone(),
        };
        result.push((cell.clone(), value));
    }
    Ok((subject, result))
}

/// Reads a bracketed subject value as the computation cell's `[head, ..]`.
fn bracket_head(group: &proc_macro2::Group) -> Result<(Pat, NegativeLiteralSpans), ParseError> {
    let parser = |input: ParseStream<'_>| {
        let sequence;
        bracketed!(sequence in input);
        if sequence.peek(Token![..]) {
            return Err(sequence.error("a machine-rule pattern must match one k head before `..`"));
        }
        let (head, signs) = parse_pattern_with_signs(&sequence)?;
        sequence.parse::<Token![,]>()?;
        sequence.parse::<Token![..]>()?;
        if sequence.peek(Token![,]) {
            sequence.parse::<Token![,]>()?;
        }
        if !sequence.is_empty() {
            return Err(sequence.error("a machine-rule k pattern is `[head, ..]`"));
        }
        Ok((head, signs))
    };
    Ok(parser.parse2(TokenStream::from(TokenTree::Group(group.clone())))?)
}

/// Reads a bracketed result value as the computation cell's `[items.., ..]`.
fn bracket_items(group: &proc_macro2::Group) -> Result<Vec<Expr>, ParseError> {
    let parser = |input: ParseStream<'_>| {
        let sequence;
        bracketed!(sequence in input);
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
        Ok(items)
    };
    Ok(parser.parse2(TokenStream::from(TokenTree::Group(group.clone())))?)
}

impl BracketAlternative {
    /// The List reading of `cell` from the clause read with every bracketed
    /// value as a List collection.
    fn from_list_reading(list: RuleClause, cell: &Ident) -> Option<Box<Self>> {
        let bindings = list.bindings;
        list.extras.into_iter().find_map(|extra| match extra {
            RuleExtra::RewriteState {
                cell: state_cell,
                before,
                result_cell,
                after,
            } if state_cell.unraw() == cell.unraw() => Some(Box::new(Self {
                cell: state_cell,
                before: *before,
                result_cell,
                after: after.map(|after| *after),
                bindings: bindings.clone(),
            })),
            _ => None,
        })
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "One linear pass retains clause layout and diagnostics at authored tokens."
)]
fn assemble_machine_clause(
    clause: &MachineClause<'_>,
    subject_cells: &[(Ident, MachinePatternCell)],
    result_cells: &[(Ident, MachineResultCell)],
) -> Result<RuleClause, ParseError> {
    let MachineClause {
        attributes,
        name,
        configuration_type,
        pattern_record,
        result_record,
        layout,
        narrowings,
        source_range,
    } = *clause;
    let mut subject_k = None;
    let mut extras = Vec::new();
    let mut extra_bindings = Vec::new();
    let mut state_bindings: Vec<Ident> = Vec::new();
    for (cell, pattern) in subject_cells {
        match pattern {
            MachinePatternCell::KHead(head, signs) => {
                if subject_k
                    .replace((cell.clone(), head.clone(), signs.clone()))
                    .is_some()
                {
                    return Err(syn::Error::new(
                        cell.span(),
                        "a machine rule must match at most one computation-cell sequence",
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
            MachinePatternCell::State(before) => {
                let result = result_cells
                    .iter()
                    .find(|(result_cell, _)| result_cell.unraw() == cell.unraw());
                let (result_cell, after) = match result {
                    Some((result_cell, MachineResultCell::State(after))) => {
                        (Some(result_cell.clone()), Some(after.clone()))
                    }
                    Some((result_cell, _)) => {
                        return Err(syn::Error::new(
                            result_cell.span(),
                            "an optional or collection cell's result restates its `Some`/`None` or instance list",
                        )
                        .into());
                    }
                    None => (None, None),
                };
                // A binder an optional or collection pattern repeats is
                // nonlinear matching, as in K: `{ me @ Thread { k: [Join(t), ..], .. },
                // Thread { id: t, .. }, .. }` joins the thread whose id is `t`.
                for binding in readable_state_bindings(before) {
                    if !state_bindings
                        .iter()
                        .any(|existing: &Ident| existing.unraw() == binding.unraw())
                    {
                        state_bindings.push(binding);
                    }
                }
                extras.push(RuleExtra::RewriteState {
                    cell: cell.clone(),
                    before: before.clone(),
                    result_cell,
                    after,
                });
            }
            MachinePatternCell::Bracket(group) => {
                return Err(readable_error(
                    group.span(),
                    "a bracketed cell value is read before the clause is assembled",
                ));
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
    for (cell, _) in result_cells {
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
    let (attribute, retained) = take_rule_clause_attribute(attributes.to_vec())?;
    let (rule, head_result, computation_cell) = if let Some((computation_cell, subject_k, signs)) =
        subject_k
    {
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
            [term] => {
                RuleHeadResult::Replace(Box::new(TermExpression::from_expression(term.clone())?))
            }
            items => RuleHeadResult::Splice {
                range: TokenRange::for_tokens(&name)?,
                items: items
                    .iter()
                    .cloned()
                    .map(TermExpression::from_expression)
                    .collect::<Result<Vec<_>, _>>()?,
            },
        };
        let placeholder: Expr = match &head_result {
            RuleHeadResult::Replace(term) => term
                .expression()
                .as_expression()
                .cloned()
                .expect("readable results are expressions"),
            RuleHeadResult::Splice { .. } | RuleHeadResult::Erase(_) => syn::parse_quote!(true),
        };
        let item: ItemFn = syn::parse2(quote! {
            #(#retained)*
            pub fn #name(#subject_k: #configuration_type) -> #configuration_type { #placeholder }
        })?;
        let rule = RuleItem::from_readable_item(item, signs)?;
        (rule, Some(head_result), Some(computation_cell))
    } else {
        // A record without the computation cell frames it like any omitted
        // cell (E7). The rule item carries only the label, attributes, and
        // configuration type; its subject binding is a placeholder whose
        // spans point at the authored records, and it binds nothing.
        let subject = quote_spanned!(pattern_record.span()=> framed);
        let placeholder = quote_spanned!(result_record.span()=> true);
        let item: ItemFn = syn::parse2(quote! {
            #(#retained)*
            pub fn #name(#subject: #configuration_type) -> #configuration_type { #placeholder }
        })?;
        let rule = RuleItem::from_readable_item(item, NegativeLiteralSpans::default())?;
        (rule, None, None)
    };
    let mut bindings = if head_result.is_some() {
        rule.parameter.pattern.bindings().to_vec()
    } else {
        Vec::new()
    };
    for introduced in state_bindings {
        if !bindings
            .iter()
            .chain(&extra_bindings)
            .any(|binding| binding.unraw() == introduced.unraw())
        {
            extra_bindings.push(introduced);
        }
    }
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
    for narrowing in narrowings {
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
    let clause = RuleClause {
        rule,
        attribute,
        narrowings: narrowings.to_vec(),
        head_result,
        extras,
        bindings,
        computation_cell,
        source_range,
        layout,
        bracket_alternative: None,
    };
    clause.check_existentials()?;
    Ok(clause)
}

fn parse_machine_update(
    cell: &Ident,
    base: &Ident,
    expression: &Expr,
) -> Result<MapUpdateExtra, ParseError> {
    parse_map_update(cell, base, expression, "the map update base must be")
}
