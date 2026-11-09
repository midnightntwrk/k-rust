//! The other grammar's reading of a term below a position's root.
//!
//! A term is Rust tokens, and a position reads them with one of Rust's two grammars: a pattern
//! where terms are matched, an expression where they are built. Some constructs exist in only one
//! of them: `name @ pattern` and `A | B` alternatives are pattern syntax, while an operator, a
//! method call, an index, a record update `..base`, a `let` block and an `ml::exists` closure are
//! expression syntax. Either may stand anywhere a term does, and the position table, not the
//! grammar, says whether it may stand there ([`crate::positions`]).
//!
//! The readers take the position's grammar first, and a construct of the other grammar at the
//! root of the term as the term it is ([`crate::term::parse_term_pattern`],
//! [`crate::term::parse_term_expression`]). A construct of the other grammar below the root
//! makes both grammars fail on the whole term. This module reads such a term after that failure,
//! and only then, so a term either grammar reads keeps its reading:
//!
//! - **At a pattern position,** the term is read as a pattern down to each subterm the pattern
//!   grammar cannot read: alternatives first (a pattern's `|` joins alternatives wherever it
//!   stands below a constructor, never the bitwise operator), then an alias's pattern, a
//!   constructor's arguments and fields, and a list's items. A subterm that is an expression is
//!   that expression, a leaf of the pattern ([`Pat::Verbatim`]), which the pattern reader reads
//!   as the term it denotes.
//! - **At an expression position,** each `name @ pattern` is that pattern, a leaf of the
//!   expression ([`Expr::Verbatim`]), and a `let`'s pattern is read as a pattern is.
//!
//! The leaves are found on the tokens: each is wrapped in a marker macro invocation, which both
//! grammars read as one term, and the parsed term's markers are replaced by the leaves they hold.
//! A marker never leaves this module, and every marker it replaces is its own: tokens that already
//! name the marker get no reading here, so an author who writes it gets the parser's error.

use proc_macro2::{Delimiter, Group, Ident, Punct, Spacing, Span, TokenStream, TokenTree};
use syn::parse::{ParseStream, Parser as _};
use syn::visit_mut::VisitMut;
use syn::{Expr, Pat, Stmt};

/// The marker macro's name. It is only ever written by this module, and read back by it; tokens
/// that hold it already are not read here ([`holds_marker`]).
const MARKER: &str = "__krs_recovered_term";

/// Reads `tokens`, which neither grammar reads whole, at a pattern position: a pattern whose
/// subterms only the expression grammar reads are [`Pat::Verbatim`] leaves. `None` when no such
/// reading exists, or when it would be the whole term as one expression, which the caller reads
/// as such.
pub(crate) fn pattern(tokens: &TokenStream) -> Option<Pat> {
    if holds_marker(tokens) {
        return None;
    }
    let tokens = tokens.clone().into_iter().collect::<Vec<_>>();
    let marked = pattern_element(&tokens)?;
    if is_one_marker(&marked) || same(&marked, &tokens) {
        return None;
    }
    let mut pattern = Pat::parse_multi.parse2(marked.into_iter().collect()).ok()?;
    Unmark.visit_pat_mut(&mut pattern);
    Some(pattern)
}

/// Reads `tokens`, which no expression reads whole, at an expression position: an expression
/// whose aliases are [`Expr::Verbatim`] leaves, and whose `let` patterns are read as
/// [`pattern`] reads one. `None` when no such reading exists.
pub(crate) fn expression(tokens: &TokenStream) -> Option<Expr> {
    if holds_marker(tokens) {
        return None;
    }
    let tokens = tokens.clone().into_iter().collect::<Vec<_>>();
    let marked = expression_tokens(&tokens)?;
    let mut expression = syn::parse2::<Expr>(marked.into_iter().collect()).ok()?;
    Unmark.visit_expr_mut(&mut expression);
    Some(expression)
}

/// Whether `expression`, read where a pattern stands, holds `|` where a pattern's alternatives
/// stand: at its root as the pattern grammar reads it ([`bar_at_level`]), or below constructors,
/// parentheses and list items only. There `|` joins
/// alternatives, which the expression grammar would read as the bitwise operator.
pub(crate) fn holds_alternatives(expression: &Expr) -> bool {
    match expression {
        Expr::Binary(_) => bar_at_level(expression),
        Expr::Call(call) => {
            matches!(call.func.as_ref(), Expr::Path(_)) && call.args.iter().any(holds_alternatives)
        }
        Expr::Struct(record) => record
            .fields
            .iter()
            .any(|field| holds_alternatives(&field.expr)),
        Expr::Paren(paren) => holds_alternatives(&paren.expr),
        Expr::Group(group) => holds_alternatives(&group.expr),
        Expr::Array(array) => array.elems.iter().any(holds_alternatives),
        Expr::Tuple(tuple) => tuple.elems.iter().any(holds_alternatives),
        _ => false,
    }
}

/// Whether the binary `expression` has a `|` at its own level of the tokens: its operator, or an
/// operand's, unparenthesized, below an operator that binds looser than `|` (a comparison, `&&`,
/// `||`). The expression grammar reads `x < 1 | y` as `x < (1 | y)`; the pattern grammar's
/// alternatives bind loosest, so where a pattern stands its `|` joins `x < 1` and `y`.
fn bar_at_level(expression: &Expr) -> bool {
    use syn::BinOp;
    let Expr::Binary(binary) = expression else {
        return false;
    };
    match binary.op {
        BinOp::BitOr(_) => true,
        BinOp::Lt(_)
        | BinOp::Le(_)
        | BinOp::Gt(_)
        | BinOp::Ge(_)
        | BinOp::Eq(_)
        | BinOp::Ne(_)
        | BinOp::And(_)
        | BinOp::Or(_) => bar_at_level(&binary.left) || bar_at_level(&binary.right),
        _ => false,
    }
}

/// Whether `tokens` are alternatives at their own level.
pub(crate) fn rooted_in_alternatives(tokens: &TokenStream) -> bool {
    let trees = tokens.clone().into_iter().collect::<Vec<_>>();
    (0..trees.len()).any(|index| is_alternative_bar(&trees, index))
}

/// The tokens of the first `name @ pattern` that [`expression`] read as a leaf of `expression`,
/// in source order: an alias that stands where the expression is built, not one in a `let`
/// pattern or a macro's tokens.
pub(crate) fn first_alias(expression: &Expr) -> Option<TokenStream> {
    struct First(Option<TokenStream>);
    impl<'ast> syn::visit::Visit<'ast> for First {
        fn visit_expr(&mut self, expression: &'ast Expr) {
            if self.0.is_some() {
                return;
            }
            match expression {
                Expr::Verbatim(tokens) if is_alias(tokens) => self.0 = Some(tokens.clone()),
                _ => syn::visit::visit_expr(self, expression),
            }
        }
    }
    let mut first = First(None);
    syn::visit::Visit::visit_expr(&mut first, expression);
    first.0
}

/// Whether `tokens` are `name @ pattern`.
fn is_alias(tokens: &TokenStream) -> bool {
    let mut trees = tokens.clone().into_iter();
    matches!(
        (trees.next(), trees.next()),
        (Some(TokenTree::Ident(_)), Some(TokenTree::Punct(at))) if at.as_char() == '@'
    )
}

/// The tokens of the next term in `input`, up to the first token at its own level that ends a
/// term wherever one stands (`,`, `;`, `=>`, `->`, `~>`, an `=` that is no operator's, or the
/// `where` of a clause's narrowing, which no term holds), and the number of token trees they
/// are.
pub(crate) fn next_term(input: ParseStream<'_>) -> (TokenStream, usize) {
    let mut trees = Vec::new();
    let mut cursor = input.cursor();
    while let Some((tree, next)) = cursor.token_tree() {
        trees.push(tree);
        cursor = next;
    }
    let end = (0..trees.len())
        .find(|&index| ends_term(&trees, index))
        .unwrap_or(trees.len());
    (trees[..end].iter().cloned().collect(), end)
}

/// Advances `input` past `count` token trees.
pub(crate) fn skip(input: ParseStream<'_>, count: usize) -> syn::Result<()> {
    for _ in 0..count {
        input.parse::<TokenTree>()?;
    }
    Ok(())
}

fn punct(tree: Option<&TokenTree>, character: char) -> Option<&Punct> {
    match tree {
        Some(TokenTree::Punct(punct)) if punct.as_char() == character => Some(punct),
        _ => None,
    }
}

/// Whether the punctuation at `index` continues a multi-character operator begun before it.
fn continues_operator(trees: &[TokenTree], index: usize) -> bool {
    index > 0
        && matches!(&trees[index - 1], TokenTree::Punct(previous) if previous.spacing() == Spacing::Joint)
}

/// Whether the token at `index` ends the term before it (see [`next_term`]).
fn ends_term(trees: &[TokenTree], index: usize) -> bool {
    let token = match trees.get(index) {
        Some(TokenTree::Punct(token)) => token,
        Some(TokenTree::Ident(keyword)) => return keyword == "where",
        _ => return false,
    };
    if continues_operator(trees, index) {
        return false;
    }
    let arrow = token.spacing() == Spacing::Joint && punct(trees.get(index + 1), '>').is_some();
    match token.as_char() {
        ',' | ';' => true,
        '=' => token.spacing() == Spacing::Alone || arrow,
        '-' | '~' => arrow,
        _ => false,
    }
}

/// Whether the punctuation at `index` is a `|` that joins alternatives: a lone `|`, not one of
/// `||` or `|=`.
fn is_alternative_bar(trees: &[TokenTree], index: usize) -> bool {
    punct(trees.get(index), '|').is_some_and(|bar| bar.spacing() == Spacing::Alone)
        && !continues_operator(trees, index)
}

/// Splits `trees` at each of its own tokens `separates` picks.
fn split(
    trees: &[TokenTree],
    separates: impl Fn(&[TokenTree], usize) -> bool,
) -> (Vec<&[TokenTree]>, Vec<&TokenTree>) {
    let mut parts = Vec::new();
    let mut separators = Vec::new();
    let mut start = 0;
    for index in 0..trees.len() {
        if separates(trees, index) {
            parts.push(&trees[start..index]);
            separators.push(&trees[index]);
            start = index + 1;
        }
    }
    parts.push(&trees[start..]);
    (parts, separators)
}

fn stream(trees: &[TokenTree]) -> TokenStream {
    trees.iter().cloned().collect()
}

/// Whether two token sequences are the same tokens.
fn same(left: &[TokenTree], right: &[TokenTree]) -> bool {
    stream(left).to_string() == stream(right).to_string()
}

fn parses_as_pattern(trees: &[TokenTree]) -> bool {
    Pat::parse_multi.parse2(stream(trees)).is_ok()
}

fn as_expression(trees: &[TokenTree]) -> Option<Expr> {
    syn::parse2::<Expr>(stream(trees)).ok()
}

/// `trees` as one marker: `__krs_recovered_term!(trees)`, spanned at its first token.
fn marker(trees: &[TokenTree]) -> Vec<TokenTree> {
    let span = trees.first().map_or_else(Span::call_site, TokenTree::span);
    let mut bang = Punct::new('!', Spacing::Alone);
    bang.set_span(span);
    let mut group = Group::new(Delimiter::Parenthesis, stream(trees));
    group.set_span(span);
    vec![
        TokenTree::Ident(Ident::new(MARKER, span)),
        TokenTree::Punct(bang),
        TokenTree::Group(group),
    ]
}

/// Whether `tokens` name the marker anywhere, a group's tokens included: an author's tokens,
/// since this module reads only tokens it has not marked yet.
fn holds_marker(tokens: &TokenStream) -> bool {
    tokens.clone().into_iter().any(|tree| match tree {
        TokenTree::Ident(name) => name == MARKER,
        TokenTree::Group(group) => holds_marker(&group.stream()),
        TokenTree::Punct(_) | TokenTree::Literal(_) => false,
    })
}

fn is_marker(path: &syn::Path) -> bool {
    path.leading_colon.is_none() && path.segments.len() == 1 && path.segments[0].ident == MARKER
}

fn is_one_marker(trees: &[TokenTree]) -> bool {
    matches!(trees, [TokenTree::Ident(name), _, TokenTree::Group(_)] if name == MARKER)
}

/// A group with `trees` in place of its own tokens.
fn regroup(group: &Group, trees: Vec<TokenTree>) -> TokenTree {
    let mut regrouped = Group::new(group.delimiter(), trees.into_iter().collect());
    regrouped.set_span(group.span());
    TokenTree::Group(regrouped)
}

/// A term at a pattern position, alternatives included.
fn pattern_element(trees: &[TokenTree]) -> Option<Vec<TokenTree>> {
    if parses_as_pattern(trees) {
        return Some(trees.to_vec());
    }
    let (alternatives, bars) = split(trees, is_alternative_bar);
    if alternatives.len() > 1
        && alternatives
            .iter()
            .all(|alternative| !alternative.is_empty())
    {
        let mut marked = Vec::new();
        for (index, alternative) in alternatives.iter().enumerate() {
            if index > 0 {
                marked.push(bars[index - 1].clone());
            }
            marked.extend(alternative_element(alternative)?);
        }
        return Some(marked);
    }
    alternative_element(trees)
}

/// One alternative at a pattern position: a pattern, an expression that is a leaf, or a
/// pattern's structure around such leaves.
fn alternative_element(trees: &[TokenTree]) -> Option<Vec<TokenTree>> {
    if parses_as_pattern(trees) {
        return Some(trees.to_vec());
    }
    let expression = as_expression(trees);
    if expression
        .as_ref()
        .is_some_and(|expression| !holds_alternatives(expression))
    {
        return Some(marker(trees));
    }
    // An expression that holds an alias or a `let` pattern this module reads
    // is a leaf too.
    structure(trees).or_else(|| {
        (expression.is_some() || self::expression(&stream(trees)).is_some()).then(|| marker(trees))
    })
}

/// A pattern's structure whose subterms are read as [`pattern_element`] reads them: an alias's
/// pattern, a constructor's arguments or fields, a list's items, a parenthesized term.
fn structure(trees: &[TokenTree]) -> Option<Vec<TokenTree>> {
    // `name @ pattern`.
    if let [TokenTree::Ident(_), TokenTree::Punct(at), rest @ ..] = trees
        && at.as_char() == '@'
        && !rest.is_empty()
    {
        let mut marked = trees[..2].to_vec();
        marked.extend(alternative_element(rest)?);
        return Some(marked);
    }
    let (TokenTree::Group(group), head) = trees.split_last()? else {
        return None;
    };
    let path = || head.is_empty() || syn::parse2::<syn::ExprPath>(stream(head)).is_ok();
    let inner = group.stream().into_iter().collect::<Vec<_>>();
    let marked = match group.delimiter() {
        Delimiter::Parenthesis | Delimiter::Bracket if path() => elements(&inner, pattern_element)?,
        Delimiter::Brace if !head.is_empty() && path() => elements(&inner, field)?,
        _ => return None,
    };
    let mut rebuilt = head.to_vec();
    rebuilt.push(regroup(group, marked));
    Some(rebuilt)
}

/// The comma-separated elements of a group, each read by `read`; an empty element (a trailing
/// comma's) stays empty.
fn elements(
    trees: &[TokenTree],
    read: fn(&[TokenTree]) -> Option<Vec<TokenTree>>,
) -> Option<Vec<TokenTree>> {
    let (parts, commas) = split(trees, |trees, index| punct(trees.get(index), ',').is_some());
    let mut marked = Vec::new();
    for (index, part) in parts.iter().enumerate() {
        if index > 0 {
            marked.push(commas[index - 1].clone());
        }
        if !part.is_empty() {
            marked.extend(read(part)?);
        }
    }
    Some(marked)
}

/// A record pattern's field: `name: pattern`, read as [`pattern_element`] reads it; a shorthand
/// field and a `..` remainder stay as they are.
fn field(trees: &[TokenTree]) -> Option<Vec<TokenTree>> {
    match trees {
        [TokenTree::Ident(_), TokenTree::Punct(colon), value @ ..]
            if colon.as_char() == ':' && colon.spacing() == Spacing::Alone && !value.is_empty() =>
        {
            let mut marked = trees[..2].to_vec();
            marked.extend(pattern_element(value)?);
            Some(marked)
        }
        _ => Some(trees.to_vec()),
    }
}

/// A term at an expression position, each alias in it a marker and each `let` pattern read as
/// [`pattern_element`] reads one. `None` when nothing changed, so no other reading exists.
fn expression_tokens(trees: &[TokenTree]) -> Option<Vec<TokenTree>> {
    let mut changed = false;
    let marked = expression_trees(trees, &mut changed)?;
    changed.then_some(marked)
}

fn expression_trees(trees: &[TokenTree], changed: &mut bool) -> Option<Vec<TokenTree>> {
    let mut marked = Vec::with_capacity(trees.len());
    let mut index = 0;
    while index < trees.len() {
        match &trees[index] {
            // `let pattern = value`: the pattern runs to the `=` that is no operator's.
            TokenTree::Ident(keyword) if keyword == "let" => {
                let end = (index + 1..trees.len())
                    .find(|&end| {
                        punct(trees.get(end), '=').is_some_and(|equals| {
                            equals.spacing() == Spacing::Alone && !continues_operator(trees, end)
                        })
                    })
                    .unwrap_or(trees.len());
                let pattern = &trees[index + 1..end];
                let read = pattern_element(pattern)?;
                *changed |= !same(&read, pattern);
                marked.push(trees[index].clone());
                marked.extend(read);
                index = end;
            }
            // `name @ pattern`, but `name @ ..`, a remainder.
            TokenTree::Ident(_)
                if punct(trees.get(index + 1), '@').is_some()
                    && punct(trees.get(index + 2), '.').is_none() =>
            {
                let length = alias_pattern_length(&trees[index + 2..])?;
                marked.extend(marker(&trees[index..index + 2 + length]));
                *changed = true;
                index += 2 + length;
            }
            // A macro's tokens are its own reader's.
            TokenTree::Group(group) if index == 0 || punct(trees.get(index - 1), '!').is_none() => {
                let inner = group.stream().into_iter().collect::<Vec<_>>();
                marked.push(regroup(group, expression_trees(&inner, changed)?));
                index += 1;
            }
            tree => {
                marked.push(tree.clone());
                index += 1;
            }
        }
    }
    Some(marked)
}

/// The number of token trees of the pattern that starts `trees`, an alias's: one pattern without
/// top-level alternatives, as `name @ pattern` binds.
fn alias_pattern_length(trees: &[TokenTree]) -> Option<usize> {
    let count = |input: ParseStream<'_>| {
        let start = input.cursor();
        Pat::parse_single(input)?;
        let length = crate::term::tokens_between(start, input.cursor())
            .into_iter()
            .count();
        input.parse::<TokenStream>()?;
        Ok(length)
    };
    count
        .parse2(stream(trees))
        .ok()
        .filter(|&length| length > 0)
}

/// Replaces each marker by the leaf it holds.
struct Unmark;

impl VisitMut for Unmark {
    fn visit_pat_mut(&mut self, pattern: &mut Pat) {
        if let Pat::Macro(value) = pattern
            && is_marker(&value.mac.path)
        {
            *pattern = Pat::Verbatim(value.mac.tokens.clone());
            return;
        }
        syn::visit_mut::visit_pat_mut(self, pattern);
    }

    fn visit_expr_mut(&mut self, expression: &mut Expr) {
        if let Expr::Macro(value) = expression
            && is_marker(&value.mac.path)
        {
            *expression = Expr::Verbatim(value.mac.tokens.clone());
            return;
        }
        syn::visit_mut::visit_expr_mut(self, expression);
    }

    fn visit_stmt_mut(&mut self, statement: &mut Stmt) {
        if let Stmt::Macro(value) = statement
            && is_marker(&value.mac.path)
        {
            *statement = Stmt::Expr(Expr::Verbatim(value.mac.tokens.clone()), value.semi_token);
            return;
        }
        syn::visit_mut::visit_stmt_mut(self, statement);
    }
}

#[cfg(test)]
mod tests {
    use quote::{ToTokens as _, quote};

    use super::*;
    use crate::parse::KrsSyntax as _;

    #[test]
    fn a_pattern_reads_an_expression_below_its_root_as_a_leaf() {
        let read = pattern(&quote!(Cmd::C(x, y @ x + 1))).expect("a recovered pattern");
        let Pat::TupleStruct(tuple) = read else {
            panic!("a constructor pattern");
        };
        let Pat::Ident(alias) = &tuple.elems[1] else {
            panic!("an alias");
        };
        let (_, subpattern) = alias.subpat.as_ref().expect("an alias's pattern");
        assert!(
            matches!(subpattern.as_ref(), Pat::Verbatim(tokens) if tokens.to_string() == "x + 1")
        );
        assert!(pattern(&quote!(Cmd::C(x, 1))).is_none());
    }

    #[test]
    fn alternatives_are_read_before_any_expression() {
        let read = pattern(&quote!(Cmd::C(x, m.len() | Cmd::Go()))).expect("a recovered pattern");
        let Pat::TupleStruct(tuple) = read else {
            panic!("a constructor pattern");
        };
        let Pat::Or(or) = &tuple.elems[1] else {
            panic!("alternatives, not the bitwise operator");
        };
        assert!(
            matches!(&or.cases[0], Pat::Verbatim(tokens) if tokens.to_string() == "m . len ()")
        );
        assert!(matches!(&or.cases[1], Pat::TupleStruct(_)));
    }

    #[test]
    fn a_whole_expression_is_left_to_the_expression_reader() {
        assert!(pattern(&quote!(x + 1)).is_none());
        assert!(pattern(&quote!(Cmd::C(x @))).is_none());
    }

    #[test]
    fn an_expression_reads_an_alias_below_its_root_as_a_leaf() {
        let read = expression(&quote!({ let y = x; y @ Cmd::Hold(_) })).expect("a recovered block");
        let Expr::Block(block) = read else {
            panic!("a block");
        };
        assert!(matches!(
            block.block.stmts.last(),
            Some(Stmt::Expr(Expr::Verbatim(tokens), None)) if tokens.to_string().starts_with("y @")
        ));
        let read = expression(&quote!(k::ml::exists(|w: Int| y @ Cmd::Hold(_)))).expect("a call");
        assert!(
            read.to_token_stream()
                .to_string()
                .contains("y @ Cmd :: Hold")
        );
        assert!(expression(&quote!(Cmd::Pair(x, 1))).is_none());
    }

    #[test]
    fn a_let_pattern_is_read_as_a_pattern() {
        let read = expression(&quote!({ let x + 1 = x; true })).expect("a recovered block");
        let Expr::Block(block) = read else {
            panic!("a block");
        };
        let Some(Stmt::Local(local)) = block.block.stmts.first() else {
            panic!("a let statement");
        };
        assert!(matches!(&local.pat, Pat::Verbatim(tokens) if tokens.to_string() == "x + 1"));
    }

    #[test]
    fn a_pattern_followed_by_an_operator_is_its_operand() {
        let read = (|input: ParseStream<'_>| {
            let pattern = crate::term::parse_term_pattern(input)?;
            input.parse::<syn::Token![,]>()?;
            input.parse::<syn::Token![..]>()?;
            Ok(pattern)
        })
        .parse2(quote!(x + 1, ..))
        .expect("a term, then the list's rest");
        assert!(matches!(&read, Pat::Verbatim(tokens) if tokens.to_string() == "x + 1"));
    }

    #[test]
    fn a_let_binder_in_an_aliased_pattern_is_the_lets_own() {
        // The `let` is refused where it stands, by the term walker; its `y`
        // is no second binding of the alias's.
        crate::RuleBlock::parse_source(
            "for Stmt; a: Cmd::C(y @ Cmd::Hold({ let y = x; y }), _) => Cmd::Go();",
        )
        .expect("no E0416: the alias's subpattern binds no `y`");
    }

    #[test]
    fn a_for_sort_clause_whose_subject_is_a_let_block_is_a_term_clause() {
        crate::RuleBlock::parse_source("for Stmt; a: { let y = x; y } => Cmd::Go();")
            .expect("a term clause: no cell is named `let`");
    }

    #[test]
    fn tokens_a_group_leaves_unread_reach_the_recovery() {
        let read = crate::term::parse_term_expression
            .parse2(quote!({ let Cmd::Pair { a: x, ..x } = x; x }))
            .expect("the let pattern, read as the term it is");
        let Expr::Block(block) = read else {
            panic!("a block");
        };
        let Some(Stmt::Local(local)) = block.block.stmts.first() else {
            panic!("a let statement");
        };
        assert!(matches!(&local.pat, Pat::Verbatim(_)), "{:?}", local.pat);
    }

    #[test]
    fn a_term_ends_before_a_clauses_where() {
        let (tokens, length) = (|input: ParseStream<'_>| {
            let read = next_term(input);
            input.parse::<TokenStream>()?;
            Ok(read)
        })
        .parse2(quote!(Cmd::Hold({ let y = x; y @ Cmd::Hold(_) }) where x: Int))
        .expect("tokens");
        assert_eq!(length, 5, "{tokens}");
        assert!(!tokens.to_string().contains("where"), "{tokens}");
        crate::RuleBlock::parse_source(
            "for Stmt; a: Cmd::C(x, _) => Cmd::Hold({ let y = x; y @ Cmd::Hold(_) }) where x: Int;",
        )
        .expect("the result is read up to its `where`");
    }

    #[test]
    fn an_authored_marker_gets_no_recovered_reading() {
        assert!(pattern(&quote!(Cmd::C(x, y @ x + 1))).is_some());
        assert!(pattern(&quote!(Cmd::C(x, y @ x + 1, __krs_recovered_term!(z)))).is_none());
        assert!(expression(&quote!({ let y = x; y @ Cmd::Hold(_) })).is_some());
        assert!(
            expression(&quote!({ let y = x; y @ Cmd::Hold(__krs_recovered_term!(_)) })).is_none()
        );
    }

    #[test]
    fn a_readable_key_is_read_as_the_pattern_it_is() {
        // A subject's key is a pattern over the map's keys (every map read's key reader,
        // `TermExpression::parse_key_pattern_tokens`): an alias names the key it matches,
        // at the root or below it, and the position table judges it where it stands.
        for key in [
            "Wrap::<Stmt>(w @ Cmd::Hold(_))",
            "Cmd::Pair { a: w @ Cmd::Hold(_), b: z }",
            "{ let w = y; w @ Cmd::Hold(_) }",
            "w @ Cmd::Hold(_)",
            "y | 1",
            "y + 1 | 1",
        ] {
            let source = format!(
                "for Machine; a: {{ k: [Cmd::C(y, _), ..], env: {{ {key} -> v, .. }} }} => {{ k: [..] }};"
            );
            if let Err(error) = crate::RuleBlock::parse_source(&source) {
                panic!("{key}: a readable key reads as a pattern: {error}");
            }
        }
        // A `let` pattern in a key is the pattern it is, judged where it stands.
        crate::RuleBlock::parse_source(
            "for Machine; a: { k: [Cmd::C(y, _), ..], env: { { let k::builtin::list::item(x).len() = y; y } -> v, .. } } => { k: [..] };",
        )
        .expect("a key's let pattern reads");
    }

    #[test]
    fn a_bar_below_a_looser_operator_joins_alternatives() {
        // Where a pattern stands, alternatives bind loosest: `x < 1 | y` is `x < 1` or `y`, which
        // the expression grammar reads as `x < (1 | y)`. A parenthesized `|` is an operand's own.
        for (source, holds) in [
            ("x < 1 | y", true),
            ("x == 1 | y", true),
            ("x && true | y", true),
            ("x || true | y", true),
            ("x + 1 | y", true),
            ("x << 1 | y", true),
            ("x < 1", false),
            ("x == (1 | y)", false),
            ("Cmd::Hold(x < 1 | y)", true),
        ] {
            let expression = syn::parse_str::<Expr>(source).expect("an expression");
            assert_eq!(holds_alternatives(&expression), holds, "{source}");
        }
    }
}
