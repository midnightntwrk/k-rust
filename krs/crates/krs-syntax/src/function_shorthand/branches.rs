//! Branching bodies of the function shorthand: a body that is an `if` chain
//! or a `match` defines one equation per branch.
//!
//! ```ignore
//! #[k::function(total, internal)]
//! pub fn StorageValue(storage: k::Term<Map>, index: k::Term<Int>) -> k::Term<Int> {
//!     if map::in_keys(index, storage) { map::get(storage, index) } else { 0 }
//! }
//! ```
//!
//! is the equations `storage_value_1`, whose guard is the condition, and
//! `storage_value_2`, whose guard is its negation. A branch is a case of the
//! function's definition, so each branch is an equation whose guard is the
//! condition under which Rust reaches it:
//!
//! - branch `i` of an `if` chain is guarded by the negations of the earlier
//!   conditions and its own condition, conjoined with `&&` in source order,
//!   so the branches are disjoint by construction and each condition is
//!   evaluated only where the earlier ones are false;
//! - an arm of a `match` puts its pattern for a parameter into the equation's
//!   head, tests its pattern for any other term in the guard (an equality
//!   for a literal, `k::matches!` otherwise), and adds its own guard after
//!   those tests.
//!
//! Rust tries a `match`'s arms in order and K's equations are unordered; the
//! two readings agree exactly when the arms do not overlap, which the overlap
//! check of equations decides where it can, and when a catch-all arm is
//! last. The last catch-all arm of the body's own `match` is the `owise`
//! equation: "no other equation applies" is "every earlier arm failed",
//! because every other equation of the body lies under an earlier arm. A
//! catch-all arm of a nested `match` cannot be `owise`, because `owise` is one
//! band for the whole function: it is guarded by the negation of each earlier
//! arm's test instead, which needs every earlier arm's guard to read no name
//! its pattern binds.
//!
//! Branching happens only at the root of an equation, so an `if` or `match`
//! is either the whole body or the whole result of a branch. Each equation
//! is named after the function and the branch's position, `signed_less_2`,
//! `signed_less_2_1` for the first branch inside the second, so adding a
//! branch at the end keeps every name; `#[k::label(name)]` on an arm names it.

use proc_macro2::{Delimiter, Group, Literal, Punct, Spacing, Span, TokenStream, TokenTree};
use quote::{ToTokens, quote, quote_spanned};
use syn::ext::IdentExt;
use syn::parse::{ParseBuffer, ParseStream};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::visit::Visit;
use syn::visit_mut::VisitMut;
use syn::{Attribute, Block, Expr, Ident, ItemFn, Pat, Stmt, Token, braced, parenthesized};

use super::{ShorthandEquation, shorthand_error};
use crate::parse::{ParseError, structured};
use crate::rule::{NegativeLiteralSpans, parse_pattern_with_signs};
use crate::{SyntaxError, TokenRange};

/// What a function shorthand's equations are made of.
pub(super) struct Lowering<'a> {
    /// The function's name, the head of every equation.
    pub(super) function: &'a Ident,
    /// The parameters, in order.
    pub(super) parameters: &'a [Ident],
    /// The span of the parameter list's parentheses.
    pub(super) parentheses: Span,
    /// The return type, the equations' sort.
    pub(super) result_type: &'a syn::Type,
    /// `#[cfg]` attributes every equation keeps.
    pub(super) cfg: &'a [Attribute],
    /// The fn's `#[k::requires]` attributes, conjoined before every guard.
    pub(super) requires: &'a [Attribute],
}

/// Lowers a branching body to its equations, or returns `None` for a body
/// that is not an `if` or a `match`.
pub(super) fn lower(
    lowering: &Lowering<'_>,
    body: &Block,
    tokens: TokenStream,
) -> Result<Option<Vec<ShorthandEquation>>, SyntaxError> {
    let branching = matches!(
        body.stmts.as_slice(),
        [Stmt::Expr(Expr::If(_) | Expr::Match(_), None)]
    );
    if !branching {
        reject_nested_branching(&body.stmts)?;
        return Ok(None);
    }
    let tree = structured(
        tokens,
        |input: ParseStream<'_>| -> Result<Body, ParseError> {
            let body = parse_branching(input)?;
            if !input.is_empty() {
                return Err(not_tail(input.span()).into());
            }
            Ok(body)
        },
    )?;
    let mut leaves = Vec::new();
    let root = BranchPath {
        patterns: vec![None; lowering.parameters.len()],
        conjuncts: Vec::new(),
        name: Name {
            base: super::equation_name(&lowering.function.unraw().to_string()),
            span: lowering.function.span(),
            parts: Vec::new(),
        },
        owise: None,
        top_level: true,
        shadowed: Vec::new(),
    };
    walk(lowering, &tree, root, &mut leaves)?;
    let mut equations: Vec<ShorthandEquation> = Vec::with_capacity(leaves.len());
    for leaf in leaves {
        let equation = equation(lowering, leaf)?;
        if let Some(previous) = equations
            .iter()
            .find(|previous| previous.item.sig.ident.unraw() == equation.item.sig.ident.unraw())
        {
            return Err(shorthand_error(
                &format!(
                    "two branches are named `{}`; a label names its equation, so give each branch its own",
                    previous.item.sig.ident.unraw()
                ),
                equation.item.sig.ident.span(),
            ));
        }
        equations.push(equation);
    }
    Ok(Some(equations))
}

// ---------------------------------------------------------------------------
// The branching tree

/// A body or branch result, read as the branches it defines.
enum Body {
    If(IfChain),
    Match(MatchBody),
    Leaf(Block),
}

struct IfBranch {
    keyword: Span,
    condition: Expr,
    body: Body,
}

/// `if c1 { .. } else if c2 { .. } else { .. }`.
struct IfChain {
    branches: Vec<IfBranch>,
    /// The `else` after each branch.
    elses: Vec<Span>,
    otherwise: Box<Body>,
}

struct MatchBody {
    /// The scrutinee's components: its elements when it is a tuple.
    scrutinee: Vec<Expr>,
    arms: Vec<Arm>,
}

struct Arm {
    label: Option<Ident>,
    /// The first token of the arm's pattern, or its `=>` when the pattern
    /// starts with a negative literal.
    span: Span,
    /// One pattern per scrutinee component.
    components: Vec<Component>,
    guard: Option<(Span, Expr)>,
    body: Body,
}

/// One component's pattern, with the spans of its negative literals.
#[derive(Clone)]
struct Component {
    pattern: Pat,
    signs: NegativeLiteralSpans,
}

fn braces(input: ParseStream<'_>) -> syn::Result<(syn::token::Brace, ParseBuffer<'_>)> {
    let content;
    let brace = braced!(content in input);
    Ok((brace, content))
}

fn parentheses(input: ParseStream<'_>) -> syn::Result<(syn::token::Paren, ParseBuffer<'_>)> {
    let content;
    let parentheses = parenthesized!(content in input);
    Ok((parentheses, content))
}

fn parse_branching(input: ParseStream<'_>) -> Result<Body, ParseError> {
    if input.peek(Token![if]) {
        parse_if(input)
    } else {
        parse_match(input)
    }
}

fn parse_if(input: ParseStream<'_>) -> Result<Body, ParseError> {
    let mut branches = Vec::new();
    let mut elses = Vec::new();
    loop {
        let keyword: Token![if] = input.parse()?;
        let condition = Expr::parse_without_eager_brace(input)?;
        if let Expr::Let(binding) = &condition {
            return Err(shorthand_error(
                "`if let` does not define equations; match on the value instead, `match value { pattern => .., _ => .. }`",
                binding.let_token.span,
            )
            .into());
        }
        let (brace, content) = braces(input)?;
        let body = parse_block(&content, brace)?;
        branches.push(IfBranch {
            keyword: keyword.span,
            condition,
            body,
        });
        if !input.peek(Token![else]) {
            return Err(shorthand_error(
                "an `if` that defines a function needs an `else`, because each branch is an equation and the `if` is the function's value; to leave the other arguments without a value, guard the fn with `#[k::requires(..)]` and make it `partial`",
                keyword.span,
            )
            .into());
        }
        let otherwise: Token![else] = input.parse()?;
        elses.push(otherwise.span);
        if input.peek(Token![if]) {
            continue;
        }
        let (brace, content) = braces(input)?;
        let otherwise = parse_block(&content, brace)?;
        return Ok(Body::If(IfChain {
            branches,
            elses,
            otherwise: Box::new(otherwise),
        }));
    }
}

/// The contents of a branch's braces: another `if` or `match`, or a result.
fn parse_block(input: ParseStream<'_>, brace: syn::token::Brace) -> Result<Body, ParseError> {
    if input.peek(Token![if]) || input.peek(Token![match]) {
        let body = parse_branching(input)?;
        if !input.is_empty() {
            return Err(not_tail(input.span()).into());
        }
        return Ok(body);
    }
    Ok(Body::Leaf(Block {
        brace_token: brace,
        stmts: input.call(Block::parse_within)?,
    }))
}

fn parse_match(input: ParseStream<'_>) -> Result<Body, ParseError> {
    let keyword: Token![match] = input.parse()?;
    let scrutinee = Expr::parse_without_eager_brace(input)?;
    let (scrutinee, tuple) = match scrutinee {
        Expr::Tuple(tuple) if tuple.elems.len() >= 2 => (tuple.elems.into_iter().collect(), true),
        other => (vec![other], false),
    };
    let (_, content) = braces(input)?;
    let mut arms = Vec::new();
    while !content.is_empty() {
        arms.push(parse_arm(&content, scrutinee.len(), tuple)?);
    }
    if arms.is_empty() {
        return Err(shorthand_error(
            "a `match` that defines a function needs at least one arm",
            keyword.span,
        )
        .into());
    }
    Ok(Body::Match(MatchBody { scrutinee, arms }))
}

fn parse_arm(input: ParseStream<'_>, arity: usize, tuple: bool) -> Result<Arm, ParseError> {
    let attributes = input.call(Attribute::parse_outer)?;
    let label = arm_label(attributes)?;
    input.parse::<Option<Token![|]>>()?;
    // A leading negative literal reaches the collector as one token whose
    // span covers `-1`, and the macro as `-` and `1`: no single token of it
    // has one span in both, so such an arm is named at its `=>`.
    let negative = input.peek(Token![-])
        || input
            .cursor()
            .literal()
            .is_some_and(|(literal, _)| literal.to_string().starts_with('-'));
    let mut span = input.span();
    let components = if tuple {
        parse_tuple_pattern(input, arity)?
    } else {
        let (pattern, signs) = parse_pattern_with_signs(input)?;
        vec![Component { pattern, signs }]
    };
    let guard = if input.peek(Token![if]) {
        let keyword: Token![if] = input.parse()?;
        Some((keyword.span, input.parse::<Expr>()?))
    } else {
        None
    };
    let arrow = input.parse::<Token![=>]>()?;
    if negative {
        span = arrow.spans[0];
    }
    let (body, needs_comma) = if input.peek(Token![if]) || input.peek(Token![match]) {
        (parse_branching(input)?, false)
    } else if input.peek(syn::token::Brace) {
        let (brace, content) = braces(input)?;
        (parse_block(&content, brace)?, false)
    } else {
        let result: Expr = input.parse()?;
        let last = TokenRange::for_tokens(&result)?.last();
        let block = Block {
            brace_token: syn::token::Brace(last),
            stmts: vec![Stmt::Expr(result, None)],
        };
        (Body::Leaf(block), true)
    };
    if input.peek(Token![,]) {
        input.parse::<Token![,]>()?;
    } else if needs_comma && !input.is_empty() {
        return Err(input.error("expected `,` after the arm's result").into());
    }
    Ok(Arm {
        label,
        span,
        components,
        guard,
        body,
    })
}

/// The arm's `#[k::label(name)]`, its only attribute.
fn arm_label(attributes: Vec<Attribute>) -> Result<Option<Ident>, ParseError> {
    let mut label = None;
    for attribute in attributes {
        let path = attribute.path();
        let is_label = path.segments.len() >= 2
            && path
                .segments
                .last()
                .is_some_and(|segment| segment.ident == "label");
        if !is_label {
            return Err(shorthand_error(
                "a match arm of a function body takes only `#[k::label(name)]`, which names its equation",
                attribute.span(),
            )
            .into());
        }
        if label.is_some() {
            return Err(shorthand_error("a match arm takes one label", attribute.span()).into());
        }
        label = Some(attribute.parse_args::<Ident>()?);
    }
    Ok(label)
}

/// An arm of a tuple `match`: `(p1, .., pn)` with at most one `..`, or `_`.
fn parse_tuple_pattern(input: ParseStream<'_>, arity: usize) -> Result<Vec<Component>, ParseError> {
    if !input.peek(syn::token::Paren) {
        let (pattern, _) = parse_pattern_with_signs(input)?;
        let Pat::Wild(wild) = pattern else {
            return Err(shorthand_error(
                "an arm of a tuple `match` lists one pattern per component, `(p1, p2)`, or is `_`",
                pattern.span(),
            )
            .into());
        };
        return Ok(vec![wildcard(wild.underscore_token.span); arity]);
    }
    let (parentheses, content) = parentheses(input)?;
    let mut written = Vec::new();
    while !content.is_empty() {
        let (pattern, signs) = parse_pattern_with_signs(&content)?;
        written.push(Component { pattern, signs });
        if content.is_empty() {
            break;
        }
        content.parse::<Token![,]>()?;
    }
    if input.peek(Token![|]) {
        return Err(shorthand_error(
            "alternatives of a tuple arm are written per component, `(0 | 1, x)`, or as separate arms",
            input.span(),
        )
        .into());
    }
    let rests = written
        .iter()
        .filter(|component| matches!(component.pattern, Pat::Rest(_)))
        .count();
    let mut components = Vec::with_capacity(arity);
    for component in written.iter().cloned() {
        if let Pat::Rest(rest) = &component.pattern {
            let missing = (arity + 1).saturating_sub(written.len());
            components.extend(std::iter::repeat_n(
                wildcard(rest.dot2_token.spans[0]),
                missing,
            ));
        } else {
            components.push(component);
        }
    }
    if rests > 1 || components.len() != arity {
        return Err(shorthand_error(
            &format!(
                "this arm has {} patterns, but the scrutinee has {arity} components",
                written.len()
            ),
            parentheses.span.join(),
        )
        .into());
    }
    Ok(components)
}

fn wildcard(span: Span) -> Component {
    Component {
        pattern: Pat::Wild(syn::PatWild {
            attrs: Vec::new(),
            underscore_token: Token![_](span),
        }),
        signs: NegativeLiteralSpans::default(),
    }
}

// ---------------------------------------------------------------------------
// From branches to equations

/// An equation's name: the function's or a label's, and branch positions.
#[derive(Clone)]
struct Name {
    base: String,
    /// The innermost branch the name was given at.
    span: Span,
    parts: Vec<usize>,
}

impl Name {
    fn ident(&self) -> Ident {
        let mut text = self.base.clone();
        for part in &self.parts {
            text.push('_');
            text.push_str(&part.to_string());
        }
        syn::parse_str::<Ident>(&text).map_or_else(
            |_| Ident::new_raw(&text, self.span),
            |_| Ident::new(&text, self.span),
        )
    }

    fn child(&self, position: usize, span: Span) -> Self {
        let mut parts = self.parts.clone();
        parts.push(position);
        Self {
            base: self.base.clone(),
            span,
            parts,
        }
    }
}

/// The conditions under which Rust reaches a branch.
#[derive(Clone)]
struct BranchPath {
    /// Each parameter's pattern, `None` while no arm has refined it.
    patterns: Vec<Option<Component>>,
    /// The guard's conjuncts in order, each with the span its `&&` takes.
    conjuncts: Vec<(Span, TokenStream)>,
    name: Name,
    /// The catch-all arm whose equations are `owise`.
    owise: Option<Span>,
    /// Whether the branch is the body itself.
    top_level: bool,
    /// The names enclosing arms bind, which shadow parameters.
    shadowed: Vec<Ident>,
}

struct Leaf {
    path: BranchPath,
    block: Block,
}

/// How a `match` reads one scrutinee component.
#[derive(Clone, Copy)]
enum Scrutinee {
    /// An unrefined parameter: the arm's pattern goes into the head.
    Parameter(usize),
    /// Any other term: the arm's pattern is tested in the guard.
    Term,
}

fn walk(
    lowering: &Lowering<'_>,
    body: &Body,
    path: BranchPath,
    leaves: &mut Vec<Leaf>,
) -> Result<(), SyntaxError> {
    match body {
        Body::Leaf(block) => {
            reject_nested_branching(&block.stmts)?;
            leaves.push(Leaf {
                path,
                block: block.clone(),
            });
        }
        Body::If(chain) => {
            for (index, branch) in chain.branches.iter().enumerate() {
                reject_nested_branching_in(&branch.condition)?;
                let mut branch_path = path.clone();
                for (earlier, otherwise) in chain.branches[..index].iter().zip(&chain.elses) {
                    branch_path
                        .conjuncts
                        .push((*otherwise, negation(&earlier.condition, *otherwise)?));
                }
                branch_path
                    .conjuncts
                    .push((branch.keyword, conjunct(&branch.condition)?));
                branch_path.name = path.name.child(index + 1, branch.keyword);
                branch_path.top_level = false;
                walk(lowering, &branch.body, branch_path, leaves)?;
            }
            let last = *chain.elses.last().expect("an `if` chain ends with `else`");
            let mut otherwise_path = path.clone();
            for (branch, otherwise) in chain.branches.iter().zip(&chain.elses) {
                otherwise_path
                    .conjuncts
                    .push((*otherwise, negation(&branch.condition, *otherwise)?));
            }
            otherwise_path.name = path.name.child(chain.branches.len() + 1, last);
            otherwise_path.top_level = false;
            walk(lowering, &chain.otherwise, otherwise_path, leaves)?;
        }
        Body::Match(body) => walk_match(lowering, body, &path, leaves)?,
    }
    Ok(())
}

fn walk_match(
    lowering: &Lowering<'_>,
    body: &MatchBody,
    path: &BranchPath,
    leaves: &mut Vec<Leaf>,
) -> Result<(), SyntaxError> {
    let mut kinds = Vec::with_capacity(body.scrutinee.len());
    for expression in &body.scrutinee {
        let kind = parameter_index(lowering, path, expression)
            .filter(|index| {
                !kinds
                    .iter()
                    .any(|kind| matches!(kind, Scrutinee::Parameter(other) if other == index))
            })
            .map_or(Scrutinee::Term, Scrutinee::Parameter);
        if matches!(kind, Scrutinee::Term) {
            reject_nested_branching_in(expression)?;
        }
        kinds.push(kind);
    }
    let catch_alls = body
        .arms
        .iter()
        .map(|arm| is_catch_all(arm, &kinds))
        .collect::<Vec<_>>();
    if let Some(position) = catch_alls.iter().position(|catch_all| *catch_all)
        && position + 1 < body.arms.len()
    {
        return Err(shorthand_error(
            "this arm matches every value, so the arms after it could never apply; make it the last arm",
            body.arms[position].span,
        ));
    }
    for (index, arm) in body.arms.iter().enumerate() {
        let mut arm_path = path.clone();
        arm_path.top_level = false;
        arm_path.name = match &arm.label {
            Some(label) => Name {
                base: label.unraw().to_string(),
                span: label.span(),
                parts: Vec::new(),
            },
            None => path.name.child(index + 1, arm.span),
        };
        for ((component, kind), expression) in
            arm.components.iter().zip(&kinds).zip(&body.scrutinee)
        {
            match kind {
                Scrutinee::Parameter(parameter) => {
                    arm_path
                        .shadowed
                        .extend(binders(&component.pattern).into_iter().cloned());
                    if !matches!(component.pattern, Pat::Wild(_)) {
                        arm_path.patterns[*parameter] = Some(component.clone());
                    }
                }
                Scrutinee::Term => {
                    if let Some(binder) = binders(&component.pattern).first() {
                        return Err(shorthand_error(
                            &format!(
                                "`{}` binds a name, but this component of the scrutinee is not a parameter, so the arm only tests it (K's `:=K`), and a test's binders are local to it; match on a parameter to bind its parts, or move the computation into a helper function",
                                binder.unraw()
                            ),
                            binder.span(),
                        ));
                    }
                    if let Some(test) = component_test(expression, component)? {
                        arm_path.conjuncts.push((first_span_of(expression)?, test));
                    }
                }
            }
        }
        if let Some((keyword, guard)) = &arm.guard {
            reject_nested_branching_in(guard)?;
            arm_path.conjuncts.push((*keyword, conjunct(guard)?));
        }
        if catch_alls[index] && index > 0 {
            if path.top_level {
                arm_path.owise = Some(arm.span);
            } else {
                for earlier in &body.arms[..index] {
                    let test = arm_test(earlier, &kinds, &body.scrutinee)?;
                    arm_path
                        .conjuncts
                        .push((arm.span, negation_of_tokens(&test, arm.span)?));
                }
            }
        }
        walk(lowering, &arm.body, arm_path, leaves)?;
    }
    Ok(())
}

/// The parameter a scrutinee component names, while no arm has refined or
/// shadowed it.
fn parameter_index(lowering: &Lowering<'_>, path: &BranchPath, expression: &Expr) -> Option<usize> {
    let Expr::Path(reference) = unparenthesized(expression) else {
        return None;
    };
    let name = reference.path.get_ident()?;
    if reference.qself.is_some()
        || path
            .shadowed
            .iter()
            .any(|binder| binder.unraw() == name.unraw())
    {
        return None;
    }
    let index = lowering
        .parameters
        .iter()
        .position(|parameter| parameter.unraw() == name.unraw())?;
    path.patterns[index].is_none().then_some(index)
}

fn unparenthesized(expression: &Expr) -> &Expr {
    match expression {
        Expr::Paren(inner) => unparenthesized(&inner.expr),
        Expr::Group(inner) => unparenthesized(&inner.expr),
        other => other,
    }
}

/// Whether a bare name in a pattern refers to a `#[k::constant]`, which is
/// compared, not bound ([`crate::path::is_constant_name`]).
fn is_constant(binder: &syn::PatIdent) -> bool {
    binder.subpat.is_none() && crate::path::is_constant_name(&binder.ident)
}

/// Whether a bare name binds the whole value: a plain binder, not a constant.
fn is_binder(binder: &syn::PatIdent) -> bool {
    binder.subpat.is_none()
        && binder.by_ref.is_none()
        && binder.mutability.is_none()
        && !is_constant(binder)
}

/// Whether an arm matches every value: no guard, and `_` or a binder for
/// each parameter, `_` for each other term.
fn is_catch_all(arm: &Arm, kinds: &[Scrutinee]) -> bool {
    arm.guard.is_none()
        && arm.components.iter().zip(kinds).all(|(component, kind)| {
            match (&component.pattern, kind) {
                (Pat::Wild(_), _) => true,
                (Pat::Ident(binder), Scrutinee::Parameter(_)) => is_binder(binder),
                _ => false,
            }
        })
}

/// The test of an earlier arm, for the guard of a nested catch-all: each
/// component's pattern tested on its scrutinee, then the arm's guard.
fn arm_test(
    arm: &Arm,
    kinds: &[Scrutinee],
    scrutinee: &[Expr],
) -> Result<TokenStream, SyntaxError> {
    let mut bound = Vec::new();
    let mut tests = Vec::new();
    for ((component, kind), expression) in arm.components.iter().zip(kinds).zip(scrutinee) {
        if matches!(kind, Scrutinee::Parameter(_)) {
            bound.extend(binders(&component.pattern).into_iter().cloned());
        }
        let mut tested = component.clone();
        WildBinders.visit_pat_mut(&mut tested.pattern);
        if let Some(test) = component_test(expression, &tested)? {
            tests.push((first_span_of(expression)?, test));
        }
    }
    if let Some((keyword, guard)) = &arm.guard {
        let guard_tokens = guard.to_token_stream();
        if let Some(binder) = bound.iter().find(|binder| mentions(binder, &guard_tokens)) {
            return Err(shorthand_error(
                &format!(
                    "the catch-all arm of a nested `match` is guarded by the negation of every earlier arm, but this guard reads `{}`, which its pattern binds, so the negation cannot state it; move the nested `match` into a helper function, whose catch-all is `owise`",
                    binder.unraw()
                ),
                binder.span(),
            ));
        }
        tests.push((*keyword, conjunct(guard)?));
    }
    Ok(join_conjuncts(tests))
}

/// The guard test of one component's pattern, or `None` for `_`: an
/// equality for a literal (or a disjunction of them), the term itself or its
/// negation for a Bool literal, and `k::matches!` otherwise.
fn component_test(
    expression: &Expr,
    component: &Component,
) -> Result<Option<TokenStream>, SyntaxError> {
    let mut signs = component.signs.clone();
    let pattern = unparenthesized_pattern(&component.pattern);
    if matches!(pattern, Pat::Wild(_)) {
        return Ok(None);
    }
    if let Some(test) = literal_test(expression, pattern, &mut signs.clone())? {
        return Ok(Some(test));
    }
    let tokens = split_negative_literals(component.pattern.to_token_stream(), &mut signs);
    let range = TokenRange::for_tokens(&tokens)?;
    let subject = expression.to_token_stream();
    let mut arguments = Group::new(Delimiter::Parenthesis, quote!(#subject, #tokens));
    arguments.set_span(range.last());
    let head = quote_spanned!(range.first()=> k::matches!);
    Ok(Some(quote!(#head #arguments)))
}

fn unparenthesized_pattern(pattern: &Pat) -> &Pat {
    match pattern {
        Pat::Paren(inner) => unparenthesized_pattern(&inner.pat),
        other => other,
    }
}

/// The test of a literal pattern, or of alternatives that are all literals.
fn literal_test(
    expression: &Expr,
    pattern: &Pat,
    signs: &mut NegativeLiteralSpans,
) -> Result<Option<TokenStream>, SyntaxError> {
    match pattern {
        Pat::Lit(literal) if literal.attrs.is_empty() => {
            // A negative literal's own span differs between the hosts (see
            // `parse_arm`), so its test is anchored at the tested term.
            let span = if literal.lit.to_token_stream().to_string().starts_with('-') {
                first_span_of(expression)?
            } else {
                literal.lit.span()
            };
            let receiver = receiver(expression)?;
            let method = |domain: &str, argument: TokenStream, last: Span| {
                let receiver = &receiver;
                let domain = Ident::new(domain, span);
                let mut arguments = Group::new(Delimiter::Parenthesis, argument);
                arguments.set_span(last);
                let call = quote_spanned!(span=> .eq::<#domain>);
                quote!(#receiver #call #arguments)
            };
            Ok(match &literal.lit {
                syn::Lit::Int(integer) if integer.suffix().is_empty() => {
                    Some(match integer.base10_digits().strip_prefix('-') {
                        Some(digits) => {
                            let (minus, digit_span) = signs.next().unwrap_or((span, span));
                            let mut sign = Punct::new('-', Spacing::Alone);
                            sign.set_span(minus);
                            let mut magnitude: Literal =
                                digits.parse().expect("the digits of an Int literal");
                            magnitude.set_span(digit_span);
                            method("Int", quote!(#sign #magnitude), digit_span)
                        }
                        None => method("Int", literal.lit.to_token_stream(), span),
                    })
                }
                syn::Lit::Bool(boolean) if boolean.value => Some(receiver.clone()),
                syn::Lit::Bool(_) => {
                    let mut arguments = Group::new(Delimiter::Parenthesis, TokenStream::new());
                    arguments.set_span(span);
                    let call = quote_spanned!(span=> .not::<Bool>);
                    Some(quote!(#receiver #call #arguments))
                }
                syn::Lit::Str(_) => Some(method("String", literal.lit.to_token_stream(), span)),
                _ => None,
            })
        }
        Pat::Or(alternatives) => {
            let mut tests = Vec::new();
            for case in &alternatives.cases {
                let Some(test) = literal_test(expression, case, signs)? else {
                    return Ok(None);
                };
                tests.push(test);
            }
            let mut tests = tests.into_iter();
            let first = tests.next().expect("an or-pattern has alternatives");
            // Each later alternative's test is joined at the `|` before it.
            let bars = alternatives
                .cases
                .pairs()
                .filter_map(|pair| pair.punct().map(|bar| bar.span));
            Ok(Some(bars.zip(tests).fold(first, |left, (span, right)| {
                let last = TokenRange::for_tokens(&right).map_or(span, TokenRange::last);
                let mut arguments = Group::new(Delimiter::Parenthesis, right);
                arguments.set_span(last);
                let call = quote_spanned!(span=> .or_else::<Bool>);
                quote!(#left #call #arguments)
            })))
        }
        _ => Ok(None),
    }
}

/// `expression`, parenthesized unless a method call binds tighter.
fn receiver(expression: &Expr) -> Result<TokenStream, SyntaxError> {
    if matches!(
        expression,
        Expr::Call(_)
            | Expr::MethodCall(_)
            | Expr::Path(_)
            | Expr::Lit(_)
            | Expr::Paren(_)
            | Expr::Macro(_)
            | Expr::Field(_)
            | Expr::Index(_)
            | Expr::Group(_)
            | Expr::Tuple(_)
            | Expr::Struct(_)
    ) {
        return Ok(expression.to_token_stream());
    }
    parenthesized_tokens(expression.to_token_stream())
}

fn parenthesized_tokens(tokens: TokenStream) -> Result<TokenStream, SyntaxError> {
    let first = TokenRange::for_tokens(&tokens)?.first();
    let mut group = Group::new(Delimiter::Parenthesis, tokens);
    group.set_span(first);
    Ok(TokenTree::Group(group).into())
}

/// A condition as a conjunct of `&&`: `a || b` is written `a.or_else::<Bool>(b)`,
/// which binds tighter than `&&` and keeps the operands' spans.
fn conjunct(expression: &Expr) -> Result<TokenStream, SyntaxError> {
    match expression {
        Expr::Binary(binary) if matches!(binary.op, syn::BinOp::Or(_)) => {
            // The span of `||`'s first `|`: the joined span of both differs
            // between the macro host, which cannot join spans, and the
            // collector's reparse, which can.
            let syn::BinOp::Or(or) = binary.op else {
                unreachable!("the guard matched `||`");
            };
            let span = or.spans[0];
            let left = receiver(&binary.left)?;
            let right = binary.right.to_token_stream();
            let last = TokenRange::for_tokens(&right)?.last();
            let mut arguments = Group::new(Delimiter::Parenthesis, right);
            arguments.set_span(last);
            let call = quote_spanned!(span=> .or_else::<Bool>);
            Ok(quote!(#left #call #arguments))
        }
        Expr::Assign(_) | Expr::Range(_) | Expr::Closure(_) | Expr::Let(_) => {
            parenthesized_tokens(expression.to_token_stream())
        }
        other => Ok(other.to_token_stream()),
    }
}

/// `condition.not::<Bool>()`, the negation an `else` stands for.
fn negation(condition: &Expr, span: Span) -> Result<TokenStream, SyntaxError> {
    let receiver = receiver(condition)?;
    let mut arguments = Group::new(Delimiter::Parenthesis, TokenStream::new());
    arguments.set_span(span);
    let call = quote_spanned!(span=> .not::<Bool>);
    Ok(quote!(#receiver #call #arguments))
}

fn negation_of_tokens(test: &TokenStream, span: Span) -> Result<TokenStream, SyntaxError> {
    let receiver = parenthesized_tokens(test.clone())?;
    let mut arguments = Group::new(Delimiter::Parenthesis, TokenStream::new());
    arguments.set_span(span);
    let call = quote_spanned!(span=> .not::<Bool>);
    Ok(quote!(#receiver #call #arguments))
}

fn join_conjuncts(conjuncts: Vec<(Span, TokenStream)>) -> TokenStream {
    let mut tokens = TokenStream::new();
    for (index, (joint, conjunct)) in conjuncts.into_iter().enumerate() {
        if index > 0 {
            let and = Token![&&](joint);
            and.to_tokens(&mut tokens);
        }
        tokens.extend(conjunct);
    }
    tokens
}

/// The names a pattern binds: in a KRS pattern every bare name is a binder,
/// and every alternative of `A | B` binds the same names.
fn binders(pattern: &Pat) -> Vec<&Ident> {
    struct Binders<'a>(Vec<&'a Ident>);
    impl<'a> Visit<'a> for Binders<'a> {
        fn visit_pat_ident(&mut self, binder: &'a syn::PatIdent) {
            if !is_constant(binder) {
                self.0.push(&binder.ident);
            }
            syn::visit::visit_pat_ident(self, binder);
        }
        fn visit_pat_or(&mut self, alternatives: &'a syn::PatOr) {
            if let Some(first) = alternatives.cases.first() {
                self.visit_pat(first);
            }
        }
        fn visit_expr(&mut self, _: &'a Expr) {}
        fn visit_macro(&mut self, _: &'a syn::Macro) {}
    }
    let mut binders = Binders(Vec::new());
    binders.visit_pat(pattern);
    binders.0
}

/// Replaces every binder with `_`, for a test whose binders nothing reads.
struct WildBinders;

impl VisitMut for WildBinders {
    fn visit_field_pat_mut(&mut self, field: &mut syn::FieldPat) {
        if field.colon_token.is_none() {
            field.colon_token = Some(Token![:](field.pat.span()));
        }
        syn::visit_mut::visit_field_pat_mut(self, field);
    }

    fn visit_pat_mut(&mut self, pattern: &mut Pat) {
        if let Pat::Ident(binder) = pattern
            && !is_constant(binder)
        {
            *pattern = match binder.subpat.take() {
                Some((_, inner)) => *inner,
                None => Pat::Wild(syn::PatWild {
                    attrs: Vec::new(),
                    underscore_token: Token![_](binder.ident.span()),
                }),
            };
        }
        syn::visit_mut::visit_pat_mut(self, pattern);
    }

    fn visit_expr_mut(&mut self, _: &mut Expr) {}
    fn visit_macro_mut(&mut self, _: &mut syn::Macro) {}
}

/// Whether `tokens` spell `name` anywhere, macro arguments included.
fn mentions(name: &Ident, tokens: &TokenStream) -> bool {
    tokens.clone().into_iter().any(|token| match token {
        TokenTree::Ident(ident) => ident.unraw() == name.unraw(),
        TokenTree::Group(group) => mentions(name, &group.stream()),
        _ => false,
    })
}

/// Writes a pattern's negative literals as `-` and digits, with the spans
/// the scan recorded, so that every reparse reads them alike.
fn split_negative_literals(tokens: TokenStream, signs: &mut NegativeLiteralSpans) -> TokenStream {
    let tokens = tokens.into_iter().collect::<Vec<_>>();
    let mut output = TokenStream::new();
    let mut pending_digits = None;
    for (index, token) in tokens.iter().enumerate() {
        match token {
            TokenTree::Group(group) => {
                let mut inner = Group::new(
                    group.delimiter(),
                    split_negative_literals(group.stream(), signs),
                );
                inner.set_span(group.span());
                output.extend([TokenTree::Group(inner)]);
            }
            TokenTree::Literal(literal) if pending_digits.is_some() => {
                let mut digits = literal.clone();
                digits.set_span(pending_digits.take().expect("checked above"));
                output.extend([TokenTree::Literal(digits)]);
            }
            TokenTree::Literal(literal) => {
                let text = literal.to_string();
                match text.strip_prefix('-') {
                    Some(digits) if digits.starts_with(|first: char| first.is_ascii_digit()) => {
                        let (minus, digit_span) = signs
                            .next()
                            .unwrap_or_else(|| (literal.span(), literal.span()));
                        let mut sign = Punct::new('-', Spacing::Alone);
                        sign.set_span(minus);
                        let mut magnitude: Literal =
                            digits.parse().expect("the digits of a numeric literal");
                        magnitude.set_span(digit_span);
                        output.extend([TokenTree::Punct(sign), TokenTree::Literal(magnitude)]);
                    }
                    _ => output.extend([token.clone()]),
                }
            }
            TokenTree::Punct(punct)
                if punct.as_char() == '-'
                    && matches!(tokens.get(index + 1), Some(TokenTree::Literal(next))
                        if next.to_string().starts_with(|first: char| first.is_ascii_digit())) =>
            {
                // A compiler host prints syn's joined `-1` as `-` and `1`,
                // both at the `-`; the digits take the span the scan
                // recorded (as does an unjoined `-1` in a macro's arguments).
                let mut sign = punct.clone();
                if let Some((minus, digits)) = signs.next() {
                    sign.set_span(minus);
                    pending_digits = Some(digits);
                }
                output.extend([TokenTree::Punct(sign)]);
            }
            _ => output.extend([token.clone()]),
        }
    }
    output
}

/// The equation of one branch: its head, its guard, and its result.
fn equation(lowering: &Lowering<'_>, leaf: Leaf) -> Result<ShorthandEquation, SyntaxError> {
    let Leaf { path, block } = leaf;
    let mut conjuncts = Vec::new();
    for attribute in lowering.requires {
        let syn::Meta::List(list) = &attribute.meta else {
            return Err(shorthand_error(
                "`#[k::requires]` takes one parenthesized object-Bool term",
                attribute.span(),
            ));
        };
        let condition = syn::parse2::<Expr>(list.tokens.clone())?;
        conjuncts.push((first_span_of(&condition)?, conjunct(&condition)?));
    }
    conjuncts.extend(path.conjuncts.iter().cloned());
    let read = {
        let mut tokens = block.to_token_stream();
        for (_, conjunct) in &conjuncts {
            tokens.extend(conjunct.clone());
        }
        tokens
    };
    let components = head(lowering, &path, &read)?;
    let mut group = Group::new(
        Delimiter::Parenthesis,
        Punctuated::<TokenStream, Token![,]>::from_iter(components).into_token_stream(),
    );
    group.set_span(lowering.parentheses);
    let function = lowering.function;
    let subject = quote!(#function #group);
    let signs = NegativeLiteralSpans::scan(subject.clone());
    let requires = (!conjuncts.is_empty()).then(|| {
        let condition = join_conjuncts(conjuncts);
        lowering.requires.first().map_or_else(
            || quote!(#[k::requires(#condition)]),
            |authored| {
                let pound = authored.pound_token;
                let path = authored.path();
                let mut brackets = Group::new(Delimiter::Bracket, quote!(#path(#condition)));
                brackets.set_span(authored.bracket_token.span.join());
                quote!(#pound #brackets)
            },
        )
    });
    let cfg = lowering.cfg;
    let name = path.name.ident();
    let result_type = lowering.result_type;
    let item = syn::parse2::<ItemFn>(quote! {
        #(#cfg)*
        #requires
        fn #name(#subject: #result_type) -> #result_type #block
    })?;
    Ok(ShorthandEquation {
        item,
        owise: path.owise.map(|span| Ident::new("owise", span)),
        signs,
    })
}

/// The head's argument patterns: a parameter's pattern from the arms that
/// refined it (aliased by the parameter where the branch still reads the
/// parameter), the parameter itself where the branch reads it, and `_`
/// otherwise.
fn head(
    lowering: &Lowering<'_>,
    path: &BranchPath,
    read: &TokenStream,
) -> Result<Vec<TokenStream>, SyntaxError> {
    let mut components = Vec::with_capacity(lowering.parameters.len());
    let mut bound: Vec<Ident> = Vec::new();
    for (parameter, pattern) in lowering.parameters.iter().zip(&path.patterns) {
        let used = mentions(parameter, read)
            && !path
                .shadowed
                .iter()
                .any(|binder| binder.unraw() == parameter.unraw());
        let component = match pattern {
            None if used => {
                bound.push(parameter.clone());
                parameter.to_token_stream()
            }
            None => quote_spanned!(parameter.span()=> _),
            Some(component) => {
                let mut signs = component.signs.clone();
                let names = binders(&component.pattern);
                bound.extend(names.iter().map(|name| (*name).clone()));
                let tokens =
                    split_negative_literals(component.pattern.to_token_stream(), &mut signs);
                if used && !names.iter().any(|name| name.unraw() == parameter.unraw()) {
                    bound.push(parameter.clone());
                    let at = Token![@](parameter.span());
                    if matches!(component.pattern, Pat::Or(_)) {
                        let end = TokenRange::for_tokens(&tokens)?.last();
                        let mut group = Group::new(Delimiter::Parenthesis, tokens);
                        group.set_span(end);
                        quote!(#parameter #at #group)
                    } else {
                        quote!(#parameter #at #tokens)
                    }
                } else {
                    tokens
                }
            }
        };
        components.push(component);
    }
    for (index, name) in bound.iter().enumerate() {
        if bound[..index]
            .iter()
            .any(|earlier| earlier.unraw() == name.unraw())
        {
            return Err(shorthand_error(
                &format!(
                    "`{}` is bound twice in this branch's head: in Rust the later binding would shadow the earlier, but an equation's head has one variable per name, so both values would have to be equal; rename it",
                    name.unraw()
                ),
                name.span(),
            ));
        }
    }
    Ok(components)
}

fn first_span_of(expression: &Expr) -> Result<Span, SyntaxError> {
    Ok(TokenRange::for_tokens(expression)?.first())
}

// ---------------------------------------------------------------------------
// Branching below the root

fn not_tail(span: Span) -> SyntaxError {
    shorthand_error(
        "an `if` or `match` that defines equations is the whole body or the whole result of a branch, with nothing after it",
        span,
    )
}

/// Rejects an `if` or `match` inside a term: an equation branches only at
/// its root.
pub(super) fn reject_nested_branching(statements: &[Stmt]) -> Result<(), SyntaxError> {
    let mut finder = Nested(None);
    for statement in statements {
        finder.visit_stmt(statement);
    }
    finder.0.map_or(Ok(()), Err)
}

fn reject_nested_branching_in(expression: &Expr) -> Result<(), SyntaxError> {
    let mut finder = Nested(None);
    finder.visit_expr(expression);
    finder.0.map_or(Ok(()), Err)
}

struct Nested(Option<SyntaxError>);

impl Nested {
    fn report(&mut self, span: Span) {
        if self.0.is_none() {
            self.0 = Some(shorthand_error(
                "an `if` or `match` inside a term cannot define equations, because an equation branches only at its root; make it the whole body or the whole result of a branch, or move it into a helper function",
                span,
            ));
        }
    }
}

impl<'a> Visit<'a> for Nested {
    fn visit_expr_if(&mut self, expression: &'a syn::ExprIf) {
        self.report(expression.if_token.span);
    }

    fn visit_expr_match(&mut self, expression: &'a syn::ExprMatch) {
        self.report(expression.match_token.span);
    }
}

#[cfg(test)]
mod tests {
    use std::fmt::Write as _;

    use quote::ToTokens;

    use super::super::FunctionShorthand;
    use crate::SyntaxError;

    fn lower(attribute: &str, item: &str) -> Result<FunctionShorthand, SyntaxError> {
        FunctionShorthand::lower(
            attribute.parse().expect("attribute tokens"),
            syn::parse_str(item).expect("a shorthand item"),
        )
    }

    /// Each equation as `name [owise]: head requires guard => result`.
    fn equations(item: &str) -> Vec<String> {
        let shorthand = lower("total, internal", item).expect(item);
        shorthand
            .equations()
            .iter()
            .map(|equation| {
                let rule = equation.rule().expect("a valid equation");
                let item = equation.item();
                let syn::FnArg::Typed(subject) = &item.sig.inputs[0] else {
                    panic!("a typed subject");
                };
                let mut line = item.sig.ident.to_string();
                let keys = equation.equation_keys().to_string();
                if !keys.is_empty() {
                    write!(line, " [{keys}]").unwrap();
                }
                write!(line, ": {}", subject.pat.to_token_stream()).unwrap();
                if let Some(requires) = rule.requires() {
                    write!(
                        line,
                        " requires {}",
                        requires.term().expression().to_token_stream()
                    )
                    .unwrap();
                }
                let result = rule.result().expect("a result");
                write!(line, " => {}", result.expression().to_token_stream()).unwrap();
                line
            })
            .collect()
    }

    #[test]
    fn an_if_chain_negates_the_earlier_conditions() {
        expect_test::expect![[r#"
            [
                "storage_value_1: StorageValue (storage , index) requires map :: in_keys (index , storage) => map :: get (storage , index)",
                "storage_value_2: StorageValue (storage , index) requires map :: in_keys (index , storage) . not :: < Bool > () => 0",
            ]
        "#]]
        .assert_debug_eq(&equations(
            "pub fn StorageValue(storage: k::Term<Map>, index: k::Term<Int>) -> k::Term<Int> {
                if map::in_keys(index, storage) { map::get(storage, index) } else { 0 }
            }",
        ));
        expect_test::expect![[r#"
            [
                "clamp_1: Clamp (value) requires int :: lt (value , 0) => 0",
                "clamp_2: Clamp (value) requires int :: lt (value , 0) . not :: < Bool > () && int :: gt (value , 9) . or_else :: < Bool > (int :: eq (value , 7)) => 9",
                "clamp_3: Clamp (value) requires int :: lt (value , 0) . not :: < Bool > () && (int :: gt (value , 9) || int :: eq (value , 7)) . not :: < Bool > () => value",
            ]
        "#]]
        .assert_debug_eq(&equations(
            "pub fn Clamp(value: k::Term<Int>) -> k::Term<Int> {
                if int::lt(value, 0) { 0 } else if int::gt(value, 9) || int::eq(value, 7) { 9 } else { value }
            }",
        ));
    }

    #[test]
    fn a_constant_name_in_an_arm_is_compared_not_bound() {
        expect_test::expect![[r#"
            [
                "port_1: Port (IF , value) => value",
                "port_2_1 [owise]: Port (_ , MASK) => 1",
                "port_2_2 [owise]: Port (_ , value) requires (k :: matches ! (value , MASK)) . not :: < Bool > () => 0",
            ]
        "#]]
        .assert_debug_eq(&equations(
            "pub fn Port(address: k::Term<Int>, value: k::Term<Int>) -> k::Term<Int> {
                match address {
                    IF => value,
                    _ => match value {
                        MASK => 1,
                        _ => 0,
                    },
                }
            }",
        ));
    }

    #[test]
    fn match_arms_refine_parameters_and_test_terms() {
        expect_test::expect![[r#"
            [
                "signed_less_1: SignedLess (left , right) requires Sign (left) . eq :: < Int > (1) && Sign (right) . eq :: < Int > (1) => BoolToWord (int :: lt (left , right))",
                "signed_less_2: SignedLess (left , right) requires Sign (left) . eq :: < Int > (1) && Sign (right) . eq :: < Int > (- 1) => BoolToWord (false)",
                "signed_less_3: SignedLess (left , right) requires Sign (left) . eq :: < Int > (- 1) && Sign (right) . eq :: < Int > (1) => BoolToWord (true)",
                "signed_less_4: SignedLess (left , right) requires Sign (left) . eq :: < Int > (- 1) && Sign (right) . eq :: < Int > (- 1) => BoolToWord (int :: lt (Magnitude (right) , Magnitude (left)))",
            ]
        "#]]
        .assert_debug_eq(&equations(
            "pub fn SignedLess(left: k::Term<Int>, right: k::Term<Int>) -> k::Term<Int> {
                match (Sign(left), Sign(right)) {
                    (1, 1) => BoolToWord(int::lt(left, right)),
                    (1, -1) => BoolToWord(false),
                    (-1, 1) => BoolToWord(true),
                    (-1, -1) => BoolToWord(int::lt(Magnitude(right), Magnitude(left))),
                }
            }",
        ));
        expect_test::expect![[r#"
            [
                "describe_1: Describe (Value :: Integer { ty : 32 , value }) requires int :: lt (value , 0) => 0",
                "describe_2: Describe (Value :: Integer { value , .. }) requires int :: ge (value , 0) => value",
                "describe_3 [owise]: Describe (_) => - 1",
            ]
        "#]]
        .assert_debug_eq(&equations(
            "pub fn Describe(value: k::Term<Val>) -> k::Term<Int> {
                match value {
                    Value::Integer { ty: 32, value } if int::lt(value, 0) => 0,
                    Value::Integer { value, .. } if int::ge(value, 0) => value,
                    _ => -1,
                }
            }",
        ));
        expect_test::expect![[r#"
            [
                "pick_1: Pick (0 , - 1 , _) => 1",
                "pick_2: Pick (size , 2 | 3 , true) => size",
                "pick_3: Pick (size , _ , false) => size",
            ]
        "#]]
        .assert_debug_eq(&equations(
            "pub fn Pick(size: k::Term<Int>, code: k::Term<Int>, flag: k::Term<Bool>) -> k::Term<Int> {
                match (size, code, flag) {
                    (0, -1, _) => 1,
                    (_, 2 | 3, true) => size,
                    (.., false) => size,
                }
            }",
        ));
    }

    #[test]
    fn nested_branches_conjoin_their_paths_and_take_hierarchical_names() {
        expect_test::expect![[r#"
            [
                "nested_1_1: Nested (width @ 8 , flag) requires int :: ge (width , 0) && flag => 1",
                "nested_1_2: Nested (width @ 8 , flag) requires int :: ge (width , 0) && flag . not :: < Bool > () => 2",
                "wide_1 [owise]: Nested (width @ w , _) requires int :: ge (width , 0) && Sign (w) . eq :: < Int > (1) => w",
                "wide_2 [owise]: Nested (width @ w , _) requires int :: ge (width , 0) && (Sign (w) . eq :: < Int > (1)) . not :: < Bool > () => 0",
            ]
        "#]]
        .assert_debug_eq(&equations(
            "#[k::requires(int::ge(width, 0))]
            pub fn Nested(width: k::Term<Int>, flag: k::Term<Bool>) -> k::Term<Int> {
                match width {
                    8 => if flag { 1 } else { 2 },
                    #[k::label(wide)]
                    w => match Sign(w) {
                        1 => w,
                        _ => 0,
                    },
                }
            }",
        ));
    }

    #[test]
    fn a_nested_catch_all_negates_each_earlier_arm() {
        expect_test::expect![[r#"
            [
                "kind_1: Kind (_ , 0) => 0",
                "kind_2_1 [owise]: Kind (Op :: Add (a , _) , code) => a",
                "kind_2_2 [owise]: Kind (Op :: Mul (a , b) | Op :: Div (a , b) , code) requires int :: eq (code , 3) => 1",
                "kind_2_3 [owise]: Kind (Op :: Neg (- 1) , code) => 2",
                "kind_2_4 [owise]: Kind (op , code) requires (k :: matches ! (op , Op :: Add (_ , _))) . not :: < Bool > () && (k :: matches ! (op , Op :: Mul (_ , _) | Op :: Div (_ , _)) && int :: eq (code , 3)) . not :: < Bool > () && (k :: matches ! (op , Op :: Neg (- 1))) . not :: < Bool > () => 3",
            ]
        "#]]
        .assert_debug_eq(&equations(
            "pub fn Kind(op: k::Term<Exp>, code: k::Term<Int>) -> k::Term<Int> {
                match code {
                    0 => 0,
                    code => match op {
                        Op::Add(a, _) => a,
                        Op::Mul(a, b) | Op::Div(a, b) if int::eq(code, 3) => 1,
                        Op::Neg(-1) => 2,
                        _ => 3,
                    },
                }
            }",
        ));
    }

    #[test]
    fn branching_mistakes_are_rejected() {
        for (item, expected) in [
            (
                "fn F(x: k::Term<Int>) -> k::Term<Int> { if int::lt(x, 0) { 1 } }",
                "needs an `else`",
            ),
            (
                "fn F(x: k::Term<Int>) -> k::Term<Int> { match x { _ => 1, 0 => 2 } }",
                "make it the last arm",
            ),
            (
                "fn F(x: k::Term<Int>) -> k::Term<Int> { match Sign(x) { s => s } }",
                "`s` binds a name",
            ),
            (
                "fn F(x: k::Term<Int>) -> k::Term<Int> { int::add(1, if int::lt(x, 0) { 1 } else { 2 }) }",
                "branches only at its root",
            ),
            (
                "fn F(x: k::Term<Int>) -> k::Term<Int> { match x { 0 => int::add(1, match x { _ => 1 }), _ => 2 } }",
                "branches only at its root",
            ),
            (
                "fn F(x: k::Term<Int>) -> k::Term<Int> { if let 0 = x { 1 } else { 2 } }",
                "`if let`",
            ),
            (
                "fn F(x: k::Term<Int>, y: k::Term<Int>) -> k::Term<Int> { match (x, y) { (0, 0) => 0, (a, a) => a } }",
                "`a` is bound twice",
            ),
            (
                "fn F(x: k::Term<Int>, y: k::Term<Int>) -> k::Term<Int> { match (x, y) { (0, 1, 2) => 0, _ => 1 } }",
                "has 3 patterns",
            ),
            (
                "fn F(x: k::Term<Int>) -> k::Term<Int> { match x { #[k::label(a)] 0 => 1, #[k::label(a)] _ => 2 } }",
                "two branches are named `a`",
            ),
            (
                "fn F(x: k::Term<Int>) -> k::Term<Int> { match x { #[cfg(test)] 0 => 1, _ => 2 } }",
                "only `#[k::label(name)]`",
            ),
            (
                "fn F(x: k::Term<Int>, y: k::Term<Int>) -> k::Term<Int> { match x { 0 => match y { n if int::lt(n, x) => 1, a if int::lt(a, 0) => 2, _ => 3 }, _ => 4 } }",
                "reads `n`",
            ),
            (
                "fn F(x: k::Term<Int>) -> k::Term<Int> { match x { 0 => { if int::lt(x, 0) { 1 } else { 2 } 3 } _ => 0 } }",
                "is the whole body",
            ),
        ] {
            let error = lower("total, internal", item).expect_err(item);
            assert!(error.to_string().contains(expected), "{item}: {error}");
        }
    }

    #[test]
    fn a_body_that_is_one_term_keeps_its_one_equation() {
        assert_eq!(
            equations(
                "pub fn Byte(value: k::Term<Int>) -> k::Term<Int> { int::rem_euclid(value, 256) }"
            ),
            ["byte: Byte (value) => int :: rem_euclid (value , 256)"]
        );
    }
}
