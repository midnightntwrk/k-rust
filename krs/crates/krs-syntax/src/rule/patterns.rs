//! Readable chain patterns, `k::patterns!` (FB-49).
//!
//! A clause `name: STEP (=> [unless(U[, requires(C)])] STEP)* ;` says that on some path of a run
//! there are states s1 ≤ … ≤ sn, each matching its step under one assignment of the binders the
//! steps share, and, where an arrow has an `unless`, that no state strictly between the two
//! steps' states matches it. A step, and an `unless`, is a cell record that denotes a set of
//! states: the subject of a readable claim, read by the same reader and judged by the same
//! entry table. So each part is parsed as the claim `{ record } => {}`, whose empty result reads
//! every named cell only, and carries the [`krs_ir::PatternDecl`] that says which part it is. A
//! cell a part does not name is unconstrained, and nothing is carried from one part to the next
//! but the values of the binders they share.
//!
//! The clause's `#[k::requires(..)]` conditions are pure functions of the binders, so each
//! conjunct is placed at the earliest step whose records bind every name it reads: later steps
//! only extend the assignment, so the placement cannot change what the pattern denotes. The
//! binders a placed conjunct reads from earlier steps are the part's imports: the part's
//! claim declares them, so they name the earlier step's values (kink substitutes them).

use proc_macro2::{Delimiter, Group, Span, TokenStream, TokenTree};
use quote::{ToTokens, format_ident, quote_spanned};
use syn::ext::IdentExt;
use syn::parse::ParseStream;
use syn::spanned::Spanned;
use syn::visit::Visit;
use syn::{Attribute, Expr, Ident, ItemUse, LitStr, Meta, Token, Type};

use super::block::{ReadableSentence, RuleBlock, RuleClause};
use super::condition::parenthesized;
use super::machine::parse_machine_clause;
use crate::parse::{KrsSyntax, ParseError, structured};
use crate::term_sort::{TermSort, parse_readable_sort};
use crate::{SyntaxError, SyntaxErrorKind};

/// The reason a helper is refused in a pattern (FB-49 item 7).
pub(crate) const PATTERN_HELPER: &str = "a pattern may call only the specification's functions: a `let` block and `k::matches!` each define a function of their own (K's `#let` and `:=K`), which nothing may add to the specification for a pattern; write the condition with the specification's functions, or define the function in the specification's package";

fn invalid(reason: impl Into<String>, span: Span) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::InvalidPattern {
            reason: reason.into(),
        },
        span,
    )
}

/// One part of a pattern clause: a step, or the `unless` of the arrow into a step.
#[derive(Clone, Debug)]
pub struct PatternPart {
    step: u32,
    unless: bool,
    /// The names the part's record binds, in introduction order.
    binders: Vec<String>,
    /// The names the part's conditions read that earlier steps bind.
    imports: Vec<String>,
}

impl PatternPart {
    /// The step the part belongs to, from 1.
    #[must_use]
    pub const fn step(&self) -> u32 {
        self.step
    }

    /// Whether the part is the `unless` of the arrow into [`Self::step`].
    #[must_use]
    pub const fn unless(&self) -> bool {
        self.unless
    }

    /// The names the part's record binds.
    #[must_use]
    pub fn binders(&self) -> &[String] {
        &self.binders
    }

    /// The names the part's conditions read that an earlier step binds.
    #[must_use]
    pub fn imports(&self) -> &[String] {
        &self.imports
    }
}

/// One `k::patterns!` clause.
#[derive(Clone, Debug)]
pub struct PatternClause {
    name: Ident,
    id: String,
    parts: Vec<PatternPart>,
}

impl PatternClause {
    /// The clause name as written.
    #[must_use]
    pub const fn name(&self) -> &Ident {
        &self.name
    }

    /// The pattern's id, the name with `_` written `-`.
    #[must_use]
    pub fn id(&self) -> &str {
        &self.id
    }

    /// The parts in order: step 1, then each arrow's `unless` (if any) and its step.
    #[must_use]
    pub fn parts(&self) -> &[PatternPart] {
        &self.parts
    }
}

/// A `k::patterns!` block: its clauses, and every part as the readable claim it is.
#[derive(Clone, Debug)]
pub struct PatternBlock {
    block: RuleBlock,
    patterns: Vec<PatternClause>,
}

impl PatternBlock {
    /// The configuration the parts' records are over.
    #[must_use]
    pub const fn sort(&self) -> &TermSort {
        self.block.sort()
    }

    /// The block's `use` items.
    #[must_use]
    pub fn imports(&self) -> &[ItemUse] {
        self.block.imports()
    }

    /// The patterns in authored order.
    #[must_use]
    pub fn patterns(&self) -> &[PatternClause] {
        &self.patterns
    }

    /// Every part of every pattern as a readable claim clause, in order; each carries its
    /// [`RuleClause::pattern`].
    #[must_use]
    pub fn clauses(&self) -> &[RuleClause] {
        self.block.clauses()
    }

    /// The parts as a block of readable claims, which they share the expansion of.
    #[must_use]
    pub const fn block(&self) -> &RuleBlock {
        &self.block
    }
}

impl KrsSyntax for PatternBlock {
    fn parse_tokens(tokens: TokenStream) -> Result<Self, SyntaxError> {
        crate::with_pattern_steps(|| structured(tokens, parse_block))
    }
}

/// Parses a pattern block together with lossless source trivia.
///
/// # Errors
///
/// Returns the same failures as [`PatternBlock::parse_tokens`] and rejects non-documentation
/// block comments with a byte-exact source range.
pub fn parse_pattern_block_source_with_trivia(
    source: &str,
) -> Result<(PatternBlock, crate::TriviaTable), SyntaxError> {
    let (tokens, trivia) = crate::trivia::tokenize_with_trivia(source)?;
    trivia.reject_non_doc_block_comments("k::patterns")?;
    Ok((PatternBlock::parse_tokens(tokens)?, trivia))
}

/// A part as written: its record, and an `unless`'s own condition.
struct WrittenPart {
    step: u32,
    unless: bool,
    record: Group,
    requires: Option<Conjunct>,
}

/// One conjunct of a part's conditions, and the authored token that joins it to the conjunct
/// before it on its part: the `&&` it was split at, or the `requires` of the attribute (or of
/// the `unless`) it is the first conjunct of.
///
/// A part's conditions are one conjunction, the claim's `requires`, so on a part that carries
/// several conjuncts each one after the first is joined to those before it by an `&&`. That
/// `&&` is a node of the part's sentence and is anchored, and an anchor must denote the same
/// authored tokens wherever the clause is parsed: so it is spanned at one authored token,
/// never at a span joined over the conjunct's tokens, whose extent depends on the parser's
/// host (a compiler's span does not join, a reparse's does).
struct Conjunct {
    condition: Expr,
    joiner: Token![&&],
}

impl Conjunct {
    /// A condition that a `requires` at `requires` writes, before it is split.
    fn written(condition: Expr, requires: Span) -> Self {
        Self {
            condition,
            joiner: Token![&&](requires),
        }
    }
}

/// The clause's attributes, read.
#[derive(Default)]
struct ClauseAttributes {
    note: Vec<String>,
    programs: Option<Vec<String>>,
    expect: Option<krs_ir::PatternExpect>,
    conjuncts: Vec<Conjunct>,
}

fn parse_block(input: ParseStream<'_>) -> Result<PatternBlock, ParseError> {
    input.parse::<Token![for]>()?;
    let sort_type: Type = input.parse()?;
    let sort = parse_readable_sort(sort_type.clone())?;
    input.parse::<Token![;]>()?;
    let mut imports = Vec::new();
    while input.peek(Token![use]) {
        imports.push(input.parse::<ItemUse>()?);
    }
    let mut clauses = Vec::new();
    let mut patterns: Vec<PatternClause> = Vec::new();
    while !input.is_empty() {
        let clause_start = input.cursor().span();
        let attributes = input.call(Attribute::parse_outer)?;
        let name = input.call(Ident::parse_any)?;
        if patterns
            .iter()
            .any(|pattern| pattern.name.unraw() == name.unraw())
        {
            return Err(syn::Error::new(
                name.span(),
                format!("duplicate readable rule clause `{}`", name.unraw()),
            )
            .into());
        }
        input.parse::<Token![:]>()?;
        let read = read_attributes(attributes)?;
        let written = parse_parts(input)?;
        let (pattern, parts) = clause_parts(&name, &sort_type, clause_start, &read, &written)?;
        clauses.extend(parts);
        patterns.push(pattern);
    }
    if patterns.is_empty() {
        return Err(input
            .error("a readable rule block requires at least one clause")
            .into());
    }
    for clause in &mut clauses {
        clause.keyed()?;
    }
    Ok(PatternBlock {
        block: RuleBlock::of_claims(sort, imports, clauses),
        patterns,
    })
}

/// Whether the input starts `unless(..)`.
fn peek_unless(input: ParseStream<'_>) -> bool {
    let ahead = input.fork();
    matches!(ahead.call(Ident::parse_any), Ok(ident) if ident == "unless")
        && ahead.peek(syn::token::Paren)
}

fn parse_record(input: ParseStream<'_>) -> Result<Group, ParseError> {
    match input.parse::<TokenTree>()? {
        TokenTree::Group(group) if group.delimiter() == Delimiter::Brace => Ok(group),
        other => Err(invalid(
            "a pattern's step is a cell record `{ cell: value, .. }` over the block's configuration",
            other.span(),
        )
        .into()),
    }
}

fn parse_parts(input: ParseStream<'_>) -> Result<Vec<WrittenPart>, ParseError> {
    let mut parts = Vec::new();
    let mut step = 1;
    loop {
        if peek_unless(input) {
            let keyword = input.call(Ident::parse_any)?;
            if step == 1 {
                return Err(invalid(
                    "step 1 has no arrow before it, so no state lies between it and an earlier step for `unless` to exclude: write `unless(..)` after a `=>`",
                    keyword.span(),
                )
                .into());
            }
            let content = input.call(|input| {
                let content;
                syn::parenthesized!(content in input);
                Ok(content)
            })?;
            let record = parse_record(&content)?;
            let mut requires: Option<Conjunct> = None;
            if content.peek(Token![,]) {
                content.parse::<Token![,]>()?;
                if !content.is_empty() {
                    let head = content.call(Ident::parse_any)?;
                    if head != "requires" || !content.peek(syn::token::Paren) {
                        return Err(invalid(
                            "an `unless` is `unless(record)` or `unless(record, requires(condition))`",
                            head.span(),
                        )
                        .into());
                    }
                    let condition = content.call(|input| {
                        let condition;
                        syn::parenthesized!(condition in input);
                        Ok(condition)
                    })?;
                    requires = Some(Conjunct::written(condition.parse::<Expr>()?, head.span()));
                    if !condition.is_empty() {
                        return Err(condition.error("expected one condition").into());
                    }
                    if content.peek(Token![,]) {
                        content.parse::<Token![,]>()?;
                    }
                }
            }
            if !content.is_empty() {
                return Err(invalid(
                    "an `unless` is `unless(record)` or `unless(record, requires(condition))`",
                    content.span(),
                )
                .into());
            }
            parts.push(WrittenPart {
                step,
                unless: true,
                record,
                requires,
            });
        }
        let record = parse_record(input)?;
        parts.push(WrittenPart {
            step,
            unless: false,
            record,
            requires: None,
        });
        if input.peek(Token![=>]) {
            input.parse::<Token![=>]>()?;
            step += 1;
            continue;
        }
        input.parse::<Token![;]>()?;
        return Ok(parts);
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "one arm per attribute a pattern clause reads, each refusal at its token"
)]
fn read_attributes(attributes: Vec<Attribute>) -> Result<ClauseAttributes, ParseError> {
    let mut read = ClauseAttributes::default();
    let mut cases_span = None;
    let mut expect_span = None;
    for attribute in attributes {
        if attribute.path().is_ident("doc") {
            if let Meta::NameValue(value) = &attribute.meta
                && let Expr::Lit(syn::ExprLit {
                    lit: syn::Lit::Str(text),
                    ..
                }) = &value.value
            {
                let text = text.value();
                read.note
                    .push(text.strip_prefix(' ').unwrap_or(&text).to_owned());
            }
            continue;
        }
        let helper = attribute
            .path()
            .segments
            .last()
            .map(|segment| segment.ident.to_string());
        match helper.as_deref() {
            Some("cases") => {
                if cases_span.is_some() {
                    return Err(invalid(
                        "a pattern carries one `#[k::cases(..)]`; list every program in it",
                        attribute.span(),
                    )
                    .into());
                }
                cases_span = Some(attribute.span());
                let programs = attribute
                    .parse_args_with(
                        syn::punctuated::Punctuated::<LitStr, Token![,]>::parse_terminated,
                    )
                    .map_err(|_| {
                        invalid(
                            "`#[k::cases(..)]` lists the corpus programs that hit the pattern, each a string: `#[k::cases(\"dir/program\")]`",
                            attribute.span(),
                        )
                    })?;
                if programs.is_empty() {
                    return Err(invalid(
                        "`#[k::cases()]` names no program, which claims nothing: leave it out to ask every program",
                        attribute.span(),
                    )
                    .into());
                }
                let mut seen = Vec::new();
                for program in &programs {
                    let value = program.value();
                    if value.is_empty() {
                        return Err(
                            invalid("a program id is a nonempty string", program.span()).into()
                        );
                    }
                    if seen.contains(&value) {
                        return Err(invalid(
                            format!("`#[k::cases(..)]` names the program `{value}` twice"),
                            program.span(),
                        )
                        .into());
                    }
                    seen.push(value);
                }
                read.programs = Some(seen);
            }
            Some("expect") => {
                if expect_span.is_some() {
                    return Err(invalid(
                        "a pattern carries one `#[k::expect(..)]`",
                        attribute.span(),
                    )
                    .into());
                }
                expect_span = Some(attribute.span());
                let value = attribute.parse_args::<Ident>().ok();
                if value.is_none_or(|value| value != "no") {
                    return Err(invalid(
                        "`#[k::expect(no)]` claims that no program's run holds the pattern; without it, the pattern claims a run that does, so `no` is its one value",
                        attribute.span(),
                    )
                    .into());
                }
                read.expect = Some(krs_ir::PatternExpect::No);
            }
            Some("requires") => {
                let condition = attribute.parse_args::<Expr>()?;
                let requires = attribute
                    .path()
                    .segments
                    .last()
                    .expect("a helper names a segment")
                    .ident
                    .span();
                split_conjuncts(Conjunct::written(condition, requires), &mut read.conjuncts);
            }
            Some(other) => {
                let reason = match other {
                    "claim" => {
                        "`#[k::claim(..)]` is a claim's modality; a pattern is no claim: it asks whether some run passes its steps, and has no modality"
                    }
                    "rule" => "`#[k::rule(..)]` is a rule's metadata; a pattern is no rule",
                    "exists" | "ensures" => {
                        "a pattern has no result, so nothing exists in it and nothing is ensured: its steps are sets of states"
                    }
                    "fresh" => "a pattern takes no step, so it draws no fresh value",
                    _ => {
                        "a pattern clause takes `#[k::cases(..)]`, `#[k::expect(no)]`, `#[k::requires(..)]` and its documentation"
                    }
                };
                return Err(invalid(
                    format!(
                        "`#[{}]` on a pattern: {reason}",
                        attribute.path().to_token_stream()
                    ),
                    attribute.span(),
                )
                .into());
            }
            None => {
                return Err(invalid("an attribute names a path", attribute.span()).into());
            }
        }
    }
    if let (Some(_), Some(span)) = (&read.programs, expect_span) {
        return Err(invalid(
            "`#[k::cases(..)]` claims those programs hit the pattern, which contradicts `#[k::expect(no)]`: keep one of the two",
            span,
        )
        .into());
    }
    Ok(read)
}

/// Splits a condition at its top-level `&&` into conjuncts, in source order: a right operand's
/// first conjunct is joined by that `&&`, a left operand's by what joined the whole.
fn split_conjuncts(conjunct: Conjunct, conjuncts: &mut Vec<Conjunct>) {
    let Conjunct { condition, joiner } = conjunct;
    match condition {
        Expr::Binary(syn::ExprBinary {
            left,
            op: syn::BinOp::And(and),
            right,
            attrs,
        }) if attrs.is_empty() => {
            split_conjuncts(
                Conjunct {
                    condition: *left,
                    joiner,
                },
                conjuncts,
            );
            split_conjuncts(
                Conjunct {
                    condition: *right,
                    joiner: and,
                },
                conjuncts,
            );
        }
        Expr::Paren(syn::ExprParen { expr, attrs, .. })
            if attrs.is_empty()
                && matches!(*expr, Expr::Binary(ref binary) if matches!(binary.op, syn::BinOp::And(_))) =>
        {
            split_conjuncts(
                Conjunct {
                    condition: *expr,
                    joiner,
                },
                conjuncts,
            );
        }
        condition => conjuncts.push(Conjunct { condition, joiner }),
    }
}

/// The bare names a condition reads: every one-segment path that is not a call's head.
fn condition_names(condition: &Expr) -> Vec<Ident> {
    struct Names(Vec<Ident>);
    impl<'ast> Visit<'ast> for Names {
        fn visit_expr_call(&mut self, call: &'ast syn::ExprCall) {
            for argument in &call.args {
                self.visit_expr(argument);
            }
        }
        fn visit_expr_path(&mut self, path: &'ast syn::ExprPath) {
            if path.qself.is_none()
                && path.path.leading_colon.is_none()
                && let Some(ident) = path.path.get_ident()
                && !self.0.iter().any(|known| known.unraw() == ident.unraw())
            {
                self.0.push(ident.clone());
            }
        }
        fn visit_expr_method_call(&mut self, call: &'ast syn::ExprMethodCall) {
            self.visit_expr(&call.receiver);
            for argument in &call.args {
                self.visit_expr(argument);
            }
        }
        fn visit_field_value(&mut self, field: &'ast syn::FieldValue) {
            self.visit_expr(&field.expr);
        }
    }
    let mut names = Names(Vec::new());
    names.visit_expr(condition);
    names.0
}

/// The first `let` block or `k::matches!` in `tokens`, which a pattern refuses.
fn helper_in(tokens: TokenStream) -> Option<Span> {
    let mut previous: Option<TokenTree> = None;
    for token in tokens {
        match &token {
            TokenTree::Group(group) => {
                if group.delimiter() == Delimiter::Brace
                    && matches!(group.stream().into_iter().next(), Some(TokenTree::Ident(ident)) if ident == "let")
                {
                    return Some(group.span());
                }
                if let Some(span) = helper_in(group.stream()) {
                    return Some(span);
                }
            }
            TokenTree::Punct(bang) if bang.as_char() == '!' => {
                if let Some(TokenTree::Ident(ident)) = &previous
                    && ident == "matches"
                {
                    return Some(ident.span());
                }
            }
            _ => {}
        }
        previous = Some(token);
    }
    None
}

/// A record-level rest `..` or `name @ ..` among a record's top-level entries: the anonymous
/// one is dropped (a cell the record does not name is unconstrained already), the named one is
/// refused.
fn without_record_rest(record: &Group) -> Result<Group, SyntaxError> {
    let tokens = record.stream().into_iter().collect::<Vec<_>>();
    let mut fields: Vec<Vec<TokenTree>> = vec![Vec::new()];
    for token in tokens {
        if matches!(&token, TokenTree::Punct(comma) if comma.as_char() == ',') {
            fields.push(Vec::new());
        } else {
            fields.last_mut().expect("one field at least").push(token);
        }
    }
    let is_dots = |field: &[TokenTree]| {
        matches!(field, [TokenTree::Punct(a), TokenTree::Punct(b)]
            if a.as_char() == '.' && b.as_char() == '.')
    };
    let mut kept = Vec::new();
    for field in fields {
        if field.is_empty() || is_dots(&field) {
            continue;
        }
        if let [TokenTree::Ident(name), TokenTree::Punct(at), rest @ ..] = field.as_slice()
            && at.as_char() == '@'
            && is_dots(rest)
        {
            return Err(invalid(
                format!(
                    "`{name} @ ..` names a record's rest, the cells the record does not name, which a step leaves unconstrained: it is several cells, and no value a step can share; write `..`"
                ),
                name.span(),
            ));
        }
        kept.push(field);
    }
    let mut stream = TokenStream::new();
    for (index, field) in kept.into_iter().enumerate() {
        if index > 0 {
            stream.extend(quote_spanned!(record.span()=> ,));
        }
        stream.extend(field);
    }
    let mut group = Group::new(Delimiter::Brace, stream);
    group.set_span(record.span());
    Ok(group)
}

/// Parses one part as the claim `{ record } => {}` named `name`, with `conditions`, in order,
/// as its one `#[k::requires]` and `imports` declared as its bindings.
fn part_clause(
    record: &Group,
    name: &Ident,
    sort_type: &Type,
    clause_start: Span,
    conditions: &[&Conjunct],
    imports: &[Ident],
    decl: Option<krs_ir::PatternDecl>,
) -> Result<RuleClause, ParseError> {
    let span = record.span();
    let mut attributes: Vec<Attribute> =
        vec![syn::parse_quote_spanned!(span=> #[k::claim(one_path)])];
    if let Some((first, rest)) = conditions.split_first() {
        attributes.push(requires_attribute(first, rest));
    }
    let mut result = Group::new(Delimiter::Brace, TokenStream::new());
    result.set_span(span);
    let record = without_record_rest(record)?;
    let mut tokens = record.to_token_stream();
    tokens.extend(quote_spanned!(span=> =>));
    tokens.extend([TokenTree::Group(result)]);
    tokens.extend(quote_spanned!(span=> ;));
    let parser = |input: ParseStream<'_>| -> Result<RuleClause, ParseError> {
        parse_machine_clause(
            input,
            &attributes,
            name,
            sort_type,
            clause_start,
            ReadableSentence::Claim,
        )
    };
    let mut clause = structured(tokens, parser)?;
    for import in imports {
        if !clause
            .bindings
            .iter()
            .any(|binding| binding.unraw() == import.unraw())
        {
            clause.bindings.push(import.clone());
        }
    }
    clause.pattern = decl;
    Ok(clause)
}

/// The one `#[k::requires]` of a part whose conjuncts are `first` then `rest`: their conjunction,
/// each conjunct after the first joined to those before it by its own joiner, in the form a
/// claim's several `#[k::requires]` take ([`parenthesized`]).
fn requires_attribute(first: &Conjunct, rest: &[&Conjunct]) -> Attribute {
    let mut condition = first.condition.clone();
    for next in rest {
        condition = Expr::Binary(syn::ExprBinary {
            attrs: Vec::new(),
            left: Box::new(parenthesized(condition)),
            op: syn::BinOp::And(next.joiner),
            right: Box::new(parenthesized(next.condition.clone())),
        });
    }
    let span = first.joiner.spans[0];
    syn::parse_quote_spanned!(span=> #[k::requires(#condition)])
}

/// The name of a part's claim: the clause name for step 1, which is the pattern's item, and the
/// name with the part appended for the others.
fn part_name(name: &Ident, part: &WrittenPart) -> Ident {
    match (part.step, part.unless) {
        (1, _) => name.clone(),
        (step, false) => format_ident!("{}__step{}", name.unraw(), step, span = name.span()),
        (step, true) => format_ident!("{}__unless{}", name.unraw(), step, span = name.span()),
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "one pass over a clause's parts: helpers, binders, placement, then the claims"
)]
fn clause_parts(
    name: &Ident,
    sort_type: &Type,
    clause_start: Span,
    attributes: &ClauseAttributes,
    written: &[WrittenPart],
) -> Result<(PatternClause, Vec<RuleClause>), ParseError> {
    for part in written {
        if let Some(span) = helper_in(part.record.stream()) {
            return Err(SyntaxError::new(
                SyntaxErrorKind::PatternHelper {
                    reason: PATTERN_HELPER.to_owned(),
                },
                span,
            )
            .into());
        }
        if let Some(condition) = &part.requires
            && let Some(span) = helper_in(condition.condition.to_token_stream())
        {
            return Err(SyntaxError::new(
                SyntaxErrorKind::PatternHelper {
                    reason: PATTERN_HELPER.to_owned(),
                },
                span,
            )
            .into());
        }
    }
    for conjunct in &attributes.conjuncts {
        if let Some(span) = helper_in(conjunct.condition.to_token_stream()) {
            return Err(SyntaxError::new(
                SyntaxErrorKind::PatternHelper {
                    reason: PATTERN_HELPER.to_owned(),
                },
                span,
            )
            .into());
        }
    }
    // The binders each part's record binds, read with no condition.
    let mut binders = Vec::with_capacity(written.len());
    for part in written {
        let clause = part_clause(
            &part.record,
            &part_name(name, part),
            sort_type,
            clause_start,
            &[],
            &[],
            None,
        )?;
        // A bare upper-case name is a unit constructor's or a constant's, never a binder.
        binders.push(
            clause
                .bindings
                .iter()
                .filter(|binding| is_binder_name(binding))
                .cloned()
                .collect::<Vec<_>>(),
        );
    }
    let bound_by = |index: usize, ident: &Ident| {
        binders[index]
            .iter()
            .any(|binder| binder.unraw() == ident.unraw())
    };
    // A binder is one variable of the clause: one that an `unless` names is shared only with a
    // step that binds it before the `unless` is asked (R2).
    for (index, part) in written.iter().enumerate() {
        if !part.unless {
            continue;
        }
        for binder in &binders[index] {
            let earlier =
                (0..index).any(|before| !written[before].unless && bound_by(before, binder));
            let elsewhere =
                (0..written.len()).any(|other| other != index && bound_by(other, binder));
            if !earlier && elsewhere {
                return Err(invalid(
                    format!(
                        "`{}` is named by this `unless` and by another part, and no earlier step binds it: an `unless` is asked before its own step's state, between the earlier steps' and that one, so its names are its own unless an earlier step bound them; bind `{}` in an earlier step, or give the `unless`'s binder another name",
                        binder.unraw(),
                        binder.unraw()
                    ),
                    binder.span(),
                )
                .into());
            }
        }
    }
    let steps = written
        .iter()
        .enumerate()
        .filter(|(_, part)| !part.unless)
        .map(|(index, _)| index)
        .collect::<Vec<_>>();
    // Each conjunct goes to the earliest step whose records, with the earlier steps', bind every
    // name it reads; one that reads a name no step binds goes to the last step, whose expansion
    // refuses the name as unbound.
    let mut placed: Vec<Vec<&Conjunct>> = vec![Vec::new(); written.len()];
    let mut imports: Vec<Vec<Ident>> = vec![Vec::new(); written.len()];
    for conjunct in &attributes.conjuncts {
        let names = condition_names(&conjunct.condition);
        let last = *steps.last().expect("a clause has a step");
        let at = steps
            .iter()
            .copied()
            .find(|&step| {
                names
                    .iter()
                    .filter(|name| is_binder_name(name))
                    .all(|name| {
                        steps
                            .iter()
                            .any(|&other| other <= step && bound_by(other, name))
                    })
            })
            .unwrap_or(last);
        placed[at].push(conjunct);
        for name in names {
            if !bound_by(at, &name)
                && steps
                    .iter()
                    .any(|&other| other < at && bound_by(other, &name))
                && !imports[at]
                    .iter()
                    .any(|known| known.unraw() == name.unraw())
            {
                imports[at].push(name);
            }
        }
    }
    for (index, part) in written.iter().enumerate() {
        let Some(condition) = &part.requires else {
            continue;
        };
        placed[index].push(condition);
        for name in condition_names(&condition.condition) {
            if !bound_by(index, &name)
                && steps
                    .iter()
                    .any(|&other| other < index && bound_by(other, &name))
                && !imports[index]
                    .iter()
                    .any(|known| known.unraw() == name.unraw())
            {
                imports[index].push(name);
            }
        }
    }
    let id = name.unraw().to_string().replace('_', "-");
    let note = (!attributes.note.is_empty()).then(|| attributes.note.join("\n").trim().to_owned());
    let mut clauses = Vec::with_capacity(written.len());
    let mut parts = Vec::with_capacity(written.len());
    for (index, part) in written.iter().enumerate() {
        let decl = krs_ir::PatternDecl {
            id: id.clone(),
            name: name.unraw().to_string(),
            step: part.step,
            unless: part.unless,
            binders: binders[index]
                .iter()
                .chain(&imports[index])
                .map(|binder| binder.unraw().to_string())
                .collect(),
            note: note.clone().filter(|note| !note.is_empty()),
            programs: attributes.programs.clone(),
            expect: attributes.expect,
        };
        clauses.push(part_clause(
            &part.record,
            &part_name(name, part),
            sort_type,
            clause_start,
            &placed[index],
            &imports[index],
            Some(decl),
        )?);
        parts.push(PatternPart {
            step: part.step,
            unless: part.unless,
            binders: binders[index]
                .iter()
                .map(|binder| binder.unraw().to_string())
                .collect(),
            imports: imports[index]
                .iter()
                .map(|import| import.unraw().to_string())
                .collect(),
        });
    }
    Ok((
        PatternClause {
            name: name.clone(),
            id,
            parts,
        },
        clauses,
    ))
}

/// Whether a bare name is a binder's (snake case), rather than a constant's or a unit
/// constructor's (upper case), which no step binds.
fn is_binder_name(name: &Ident) -> bool {
    name.unraw()
        .to_string()
        .chars()
        .next()
        .is_some_and(|first| first.is_lowercase() || first == '_')
}
