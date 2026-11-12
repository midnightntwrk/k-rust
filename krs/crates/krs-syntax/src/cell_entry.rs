//! A cell entry's spelling, read kind-neutrally (design S5, §2.2).
//!
//! An entry's value is read as the marks it carries (presence, sequence brackets, instance
//! braces, map notation, the `cells!` wrappers), the names it binds, and the values it holds.
//! What the marks mean depends on the cell's kind, which this module does not know:
//! [`crate::cell_entries`] judges a spelling against the cell's stack.
//!
//! The reading depends on the form only where the forms spell a mark differently: in a `cells!`
//! entry, brackets and braces at the entry's head are an instance list and an instance set,
//! while inside `Cell(..)` brackets are the leaf's own; a readable `{ k -> v, .. }` is a map
//! read; an initializer names its configuration variables, and a value inside one of its entries
//! that is no entry (an operator's application, `0 + 1`) is a term it builds, read as an
//! application whose arguments are not read.
//!
//! The shape rules hold here: a sequence or map has at most one rest, `Some(..)` holds one
//! entry, and a map read names each key once.

use proc_macro2::TokenStream;
use syn::ext::IdentExt;
use syn::parse::discouraged::Speculative;
use syn::parse::{ParseStream, Parser};
use syn::{Ident, Lit, Path, Token, braced, bracketed, parenthesized};

/// The form an entry is written in.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum EntryForm {
    /// A readable record (`k::rules!` with `for Machine`).
    Readable,
    /// A readable claim.
    Claim,
    /// A `k::patterns!` step or `unless` (FB-49): a claim's subject, whose lists may hold
    /// several rests.
    Pattern,
    /// A `cells!` entry.
    Cells,
    /// An initializer's field.
    Initializer,
}

impl EntryForm {
    /// Whether the form is a readable record or claim.
    #[must_use]
    pub const fn is_readable(self) -> bool {
        matches!(self, Self::Readable | Self::Claim | Self::Pattern)
    }

    /// Whether the form is a claim's, whose subject a pattern's step is too.
    #[must_use]
    pub const fn is_claim(self) -> bool {
        matches!(self, Self::Claim | Self::Pattern)
    }
}

/// A rest at a content root.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EntryRest {
    /// `..`.
    Anonymous,
    /// `name @ ..`.
    Named(String),
    /// `..name`.
    Splice(String),
}

/// Where a sequence's rest stands.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RestPlace {
    /// After every item, `[x, ..]`.
    Back,
    /// Before the item at this index: `[.., x]` is `Before(0)`, `[x, .., y]` is `Before(1)`.
    Before(usize),
}

/// Items with an optional rest.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EntrySeq {
    /// The items in order.
    pub items: Vec<EntrySpelling>,
    /// The rest and its place; `None` for an exact sequence.
    pub rest: Option<(EntryRest, RestPlace)>,
    /// The rests after the first, which only a pattern step's list holds (FB-49 R-2): its
    /// items then occur in order, with any list between and around them.
    pub more_rests: usize,
}

impl EntrySeq {
    /// The items before the rest: every item where the rest is last or there is none.
    #[must_use]
    pub fn front(&self) -> &[EntrySpelling] {
        &self.items[..self.split()]
    }

    /// The items after the rest: none where the rest is last or there is none.
    #[must_use]
    pub fn back(&self) -> &[EntrySpelling] {
        &self.items[self.split()..]
    }

    fn split(&self) -> usize {
        match self.rest {
            Some((_, RestPlace::Before(at))) => at,
            _ => self.items.len(),
        }
    }
}

/// `key -> value` entries with an optional rest.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EntryMap {
    /// The entries in order.
    pub entries: Vec<(EntrySpelling, EntrySpelling)>,
    /// The rest; `None` for an exact map.
    pub rest: Option<EntryRest>,
}

/// A record's tail.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RecordTail {
    /// Every field is named.
    Exact,
    /// `..`.
    Open,
    /// `..base`.
    Update(String),
}

/// A record `Head { field: value, .. }`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EntryRecord {
    /// The struct path's last segment.
    pub head: String,
    /// The fields in order; a shorthand field binds its own name.
    pub fields: Vec<(String, EntrySpelling)>,
    /// The tail.
    pub tail: RecordTail,
}

/// A cell entry's spelling: marks, names and values, read from source.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EntrySpelling {
    /// `_`.
    Wild,
    /// A name.
    Binder(String),
    /// A literal, as written.
    Literal(String),
    /// An application or a constructor term, with its arguments.
    Call(Vec<Self>),
    /// An initializer's configuration variable.
    ConfigVar(String),
    /// `Some(..)`.
    Present(Box<Self>),
    /// `None`.
    Missing,
    /// `k::absent!(..)`.
    Absent(Box<Self>),
    /// Brackets: a readable or initializer sequence, or a leaf's inside `Cell(..)`.
    Brackets(EntrySeq),
    /// Readable instance braces, `{ Obj { .. }, .. }`.
    Braces(EntrySeq),
    /// A readable map read, `{ k -> v, .. }`.
    MapRead(EntryMap),
    /// A record.
    Record(EntryRecord),
    /// `name @ pattern`; with no name, parentheses around a pattern, which group it and name
    /// nothing, so its rest is matched inside a term, not by the cell's own brackets.
    Alias(String, Box<Self>),
    /// Pattern alternatives, `p | q`, each an entry of the same cell, in order.
    Alternatives(Vec<Self>),
    /// `Cell(..)`.
    Cell(Box<Self>),
    /// `KCell(..)`.
    KCell(EntrySeq),
    /// `k::fragment![crate::G { .. }]`.
    Fragment(EntryRecord),
    /// A `cells!` instance list, `[k::fragment![..], rest @ ..]`.
    InstanceList(EntrySeq),
    /// A `cells!` instance set, `{ k::fragment![..], rest @ .. }`.
    InstanceSet(EntrySeq),
    /// A map literal, `k::map![..]` (`map![..]` in readable).
    MapLiteral(EntryMap),
    /// `k::k![..]`.
    KMacro(EntrySeq),
}

/// How an entry is read: its form, and an initializer's configuration variables.
#[derive(Clone, Copy, Debug)]
pub struct EntryReading<'a> {
    form: EntryForm,
    variables: &'a [String],
}

impl<'a> EntryReading<'a> {
    /// A reading of entries of `form`; `variables` are an initializer's configuration
    /// variables.
    #[must_use]
    pub const fn new(form: EntryForm, variables: &'a [String]) -> Self {
        Self { form, variables }
    }

    /// Reads an entry's value.
    ///
    /// # Errors
    ///
    /// Tokens that are no entry, or an entry that breaks a shape rule.
    pub fn value(self, tokens: TokenStream) -> syn::Result<EntrySpelling> {
        (|input: ParseStream<'_>| self.parse_value(input)).parse2(tokens)
    }

    /// Reads a `name: value` field: its key path (`crate::Queue::job` in `cells!`) and its
    /// value.
    ///
    /// # Errors
    ///
    /// Tokens that are no field, or a value that breaks a shape rule.
    pub fn field(self, tokens: TokenStream) -> syn::Result<(Path, EntrySpelling)> {
        (|input: ParseStream<'_>| self.parse_field(input)).parse2(tokens)
    }

    /// [`Self::value`] over a parse stream.
    ///
    /// # Errors
    ///
    /// As [`Self::value`].
    pub fn parse_value(self, input: ParseStream<'_>) -> syn::Result<EntrySpelling> {
        self.content(input, true)
    }

    /// [`Self::field`] over a parse stream.
    ///
    /// # Errors
    ///
    /// As [`Self::field`].
    pub fn parse_field(self, input: ParseStream<'_>) -> syn::Result<(Path, EntrySpelling)> {
        let key = input.call(Path::parse_mod_style)?;
        input.parse::<Token![:]>()?;
        Ok((key, self.content(input, true)?))
    }

    /// A whole entry's value, or the content of its presence: a value that is no entry (`a + b`,
    /// a `let` block) is the term it denotes, as inside an entry ([`Self::term`]), so that its
    /// marks, or their absence, are still judged against the cell.
    fn content(self, input: ParseStream<'_>, head: bool) -> syn::Result<EntrySpelling> {
        self.term(input, head)
    }

    /// One entry; `head` is whether it stands at the entry's head (below presence and
    /// aliases only), where `cells!` reads brackets and braces as instances.
    fn parse(self, input: ParseStream<'_>, head: bool) -> syn::Result<EntrySpelling> {
        if input.peek(Token![_]) {
            input.parse::<Token![_]>()?;
            return Ok(EntrySpelling::Wild);
        }
        if input.peek(Ident::peek_any) && input.peek2(Token![@]) && !input.peek3(Token![..]) {
            let name = input.call(Ident::parse_any)?.unraw().to_string();
            input.parse::<Token![@]>()?;
            return Ok(EntrySpelling::Alias(
                name,
                Box::new(self.parse(input, head)?),
            ));
        }
        // A pattern in parentheses is the pattern they group, `([x, ..])`, as Rust reads it: the
        // entry inside a term that names nothing ([`EntrySpelling::Alias`] with no name), so its
        // rest is matched inside a term, not by the cell's own brackets. A tuple is no entry.
        if input.peek(syn::token::Paren) && self.form != EntryForm::Initializer {
            let content;
            parenthesized!(content in input);
            let inner = self.marked(&content, head)?;
            if !content.is_empty() {
                return Err(content.error("a tuple is no entry"));
            }
            return Ok(EntrySpelling::Alias(String::new(), Box::new(inner)));
        }
        if input.peek(syn::token::Bracket) {
            let content;
            bracketed!(content in input);
            let seq = self.seq(&content)?;
            return Ok(if head && self.form == EntryForm::Cells {
                EntrySpelling::InstanceList(seq)
            } else {
                EntrySpelling::Brackets(seq)
            });
        }
        // A block, `{ let s = set::empty(); s }`, is the term it evaluates to, no list of items.
        if input.peek(syn::token::Brace) && is_block(input) {
            input.parse::<syn::Block>()?;
            return Ok(EntrySpelling::Call(Vec::new()));
        }
        if input.peek(syn::token::Brace) {
            let content;
            braced!(content in input);
            return self.braces(&content, head);
        }
        if input.peek(Lit) {
            let literal = input.parse::<Lit>()?;
            return Ok(EntrySpelling::Literal(
                quote::ToTokens::to_token_stream(&literal).to_string(),
            ));
        }
        if input.peek(Token![-]) && input.peek2(Lit) {
            input.parse::<Token![-]>()?;
            let literal = input.parse::<Lit>()?;
            return Ok(EntrySpelling::Literal(format!(
                "-{}",
                quote::ToTokens::to_token_stream(&literal)
            )));
        }
        // An expression's path: a turbofish names its generic arguments (`Wrap::<Val>(..)`),
        // and a `<` after a name is an operator, not arguments.
        let path = input.parse::<syn::ExprPath>()?.path;
        let last = path
            .segments
            .last()
            .map(|segment| segment.ident.unraw().to_string())
            .unwrap_or_default();
        if input.peek(Token![!]) && !input.peek(Token![!=]) {
            input.parse::<Token![!]>()?;
            return self.macro_call(&last, input);
        }
        if input.peek(syn::token::Paren) {
            let content;
            parenthesized!(content in input);
            return self.call(&last, &content, head);
        }
        if input.peek(syn::token::Brace) {
            let content;
            braced!(content in input);
            return Ok(EntrySpelling::Record(self.record(last, &content)?));
        }
        if path.segments.len() == 1 {
            return Ok(match last.as_str() {
                "None" => EntrySpelling::Missing,
                _ if self.form == EntryForm::Initializer && self.variables.contains(&last) => {
                    EntrySpelling::ConfigVar(last)
                }
                _ => EntrySpelling::Binder(last),
            });
        }
        // A qualified name without arguments is a constant.
        Ok(EntrySpelling::Call(Vec::new()))
    }

    /// `Some(..)`, `Cell(..)`, `KCell(..)`, or an application.
    fn call(self, name: &str, content: ParseStream<'_>, head: bool) -> syn::Result<EntrySpelling> {
        match name {
            "Some" => {
                let inner = self.marked(content, head)?;
                if !content.is_empty() {
                    return Err(content.error("`Some(..)` holds one entry"));
                }
                Ok(EntrySpelling::Present(Box::new(inner)))
            }
            // In an initializer, `Cell::new(v)` and `KCell::new(..)` read as these marks
            // (`crate::initializer`'s `unwrapped_value`).
            "Cell" if matches!(self.form, EntryForm::Cells | EntryForm::Initializer) => {
                let inner = self.marked(content, false)?;
                content.parse::<Option<Token![,]>>()?;
                if !content.is_empty() {
                    return Err(content.error("`Cell(..)` holds one value"));
                }
                Ok(EntrySpelling::Cell(Box::new(inner)))
            }
            "KCell" if matches!(self.form, EntryForm::Cells | EntryForm::Initializer) => {
                Ok(EntrySpelling::KCell(self.seq(content)?))
            }
            _ => {
                let mut arguments = Vec::new();
                while !content.is_empty() {
                    arguments.push(self.inner(content)?);
                    if content.is_empty() {
                        break;
                    }
                    content.parse::<Token![,]>()?;
                }
                Ok(EntrySpelling::Call(arguments))
            }
        }
    }

    /// `k::k![..]`, `k::map![..]`, `k::fragment![..]`, `k::absent!(..)`, or another macro,
    /// which is a value.
    fn macro_call(self, name: &str, input: ParseStream<'_>) -> syn::Result<EntrySpelling> {
        let content;
        if input.peek(syn::token::Bracket) {
            bracketed!(content in input);
        } else if input.peek(syn::token::Paren) {
            parenthesized!(content in input);
        } else {
            braced!(content in input);
        }
        match name {
            "k" => Ok(EntrySpelling::KMacro(self.seq(&content)?)),
            "map" => Ok(EntrySpelling::MapLiteral(self.map(&content)?)),
            "fragment" => {
                let path = content.call(Path::parse_mod_style)?;
                let head = path
                    .segments
                    .last()
                    .map(|segment| segment.ident.unraw().to_string())
                    .unwrap_or_default();
                let fields;
                braced!(fields in content);
                Ok(EntrySpelling::Fragment(self.record(head, &fields)?))
            }
            "absent" => Ok(EntrySpelling::Absent(Box::new(
                self.content(&content, false)?,
            ))),
            _ => {
                content.parse::<TokenStream>()?;
                Ok(EntrySpelling::Call(Vec::new()))
            }
        }
    }

    /// A rest, if the input starts with one: `..`, `name @ ..` or `..name`.
    fn rest(input: ParseStream<'_>) -> syn::Result<Option<EntryRest>> {
        if input.peek(Token![..]) {
            input.parse::<Token![..]>()?;
            if input.is_empty() || input.peek(Token![,]) {
                return Ok(Some(EntryRest::Anonymous));
            }
            // `..name` puts back the list `name`; `..term` the list a term denotes.
            let ahead = input.fork();
            if ahead.call(Ident::parse_any).is_ok() && (ahead.is_empty() || ahead.peek(Token![,])) {
                let name = input.call(Ident::parse_any)?.unraw().to_string();
                return Ok(Some(EntryRest::Splice(name)));
            }
            let term = input.parse::<syn::Expr>()?;
            return Ok(Some(EntryRest::Splice(
                quote::ToTokens::to_token_stream(&term).to_string(),
            )));
        }
        if input.peek(Ident::peek_any) && input.peek2(Token![@]) && input.peek3(Token![..]) {
            let name = input.call(Ident::parse_any)?.unraw().to_string();
            input.parse::<Token![@]>()?;
            input.parse::<Token![..]>()?;
            return Ok(Some(EntryRest::Named(name)));
        }
        Ok(None)
    }

    /// A value inside an entry, followed by a `,` or by nothing: an item, an argument or a
    /// record field's value ([`Self::term`]).
    fn inner(self, input: ParseStream<'_>) -> syn::Result<EntrySpelling> {
        self.term(input, false)
    }

    /// A value followed by a `,`, a `->` or by nothing, read as an entry where it is one, and
    /// otherwise as the term it is: operator notation (`x + 1`), a method call, a negation are
    /// spellings of a term, as `int::add(x, 1)` is, so one that is no entry is read as an
    /// application whose arguments are not read. The marks around it are still the entry's to
    /// judge, on every form alike, and what it holds is the term's.
    ///
    /// An initializer builds every value it holds, so whatever its reading cannot read there is
    /// a term. Where a pattern may stand (every other form), a value the reading starts as an
    /// entry and cannot finish breaks that entry's shape rule (`Some(x, y)`, a second rest), which
    /// is no term, and `|` at a pattern's level joins alternatives and `..` is a rest: a value
    /// holding one stays unread.
    fn term(self, input: ParseStream<'_>, head: bool) -> syn::Result<EntrySpelling> {
        self.term_in(input, head, false)
    }

    /// The value a mark holds, `Some(..)`'s or `Cell(..)`'s, read as [`Self::term`] reads one,
    /// except that pattern alternatives (`s | s`) there are the one term pattern they make,
    /// matching either, so the marks around them are judged as around any term.
    fn marked(self, input: ParseStream<'_>, head: bool) -> syn::Result<EntrySpelling> {
        self.term_in(input, head, true)
    }

    fn term_in(
        self,
        input: ParseStream<'_>,
        head: bool,
        marked: bool,
    ) -> syn::Result<EntrySpelling> {
        let ahead = input.fork();
        match self.parse(&ahead, head) {
            Ok(spelling) if ahead.is_empty() || ahead.peek(Token![,]) || ahead.peek(Token![->]) => {
                input.advance_to(&ahead);
                return Ok(spelling);
            }
            Err(error) if self.form != EntryForm::Initializer && starts_entry(input) => {
                return Err(error);
            }
            _ => {}
        }
        // Pattern alternatives, `[x, ..] | [x]`, `Go() | Last()`: each is an entry of the cell,
        // read in order, so every one is judged by the cell's kind and none by its place.
        if self.form != EntryForm::Initializer
            && let Some(alternatives) = pattern_alternatives(input)
        {
            let alternatives = alternatives
                .into_iter()
                .map(|alternative| self.value(alternative))
                .collect::<syn::Result<Vec<_>>>()?;
            return Ok(EntrySpelling::Alternatives(alternatives));
        }
        let expression = input.parse::<syn::Expr>()?;
        if self.form != EntryForm::Initializer
            && !denotes_term(&expression)
            && (!marked || holds_rest(&expression))
        {
            return Err(syn::Error::new_spanned(
                &expression,
                "alternatives or a rest are no term",
            ));
        }
        Ok(EntrySpelling::Call(Vec::new()))
    }

    /// Comma-separated items with at most one rest, or, in a pattern step, any number.
    fn seq(self, content: ParseStream<'_>) -> syn::Result<EntrySeq> {
        let mut items = Vec::new();
        let mut rest = None;
        let mut more_rests = 0;
        while !content.is_empty() {
            if let Some(found) = Self::rest(content)? {
                if rest.is_some() && self.form == EntryForm::Pattern {
                    more_rests += 1;
                    if content.is_empty() {
                        break;
                    }
                    content.parse::<Token![,]>()?;
                    continue;
                }
                if rest.is_some() {
                    return Err(content.error("a sequence has at most one rest"));
                }
                let place = if content.is_empty()
                    || content.peek(Token![,]) && {
                        let ahead = content.fork();
                        ahead.parse::<Token![,]>()?;
                        ahead.is_empty()
                    } {
                    RestPlace::Back
                } else {
                    RestPlace::Before(items.len())
                };
                rest = Some((found, place));
            } else {
                // An item's alternatives (`Go() | Last()`) are the one term pattern they make,
                // matching either, as a mark's content is: the item is a term either way.
                items.push(self.marked(content, false)?);
            }
            if content.is_empty() {
                break;
            }
            content.parse::<Token![,]>()?;
        }
        Ok(EntrySeq {
            items,
            rest,
            more_rests,
        })
    }

    /// `key -> value` entries with at most one rest, last.
    fn map(self, content: ParseStream<'_>) -> syn::Result<EntryMap> {
        let mut entries = Vec::new();
        let mut rest = None;
        while !content.is_empty() {
            if let Some(found) = Self::rest(content)? {
                if rest.is_some() {
                    return Err(content.error("a map has at most one rest"));
                }
                rest = Some(found);
            } else {
                // The key ends at the `->`, which the expression grammar would read as `-`.
                let mut key = TokenStream::new();
                while !content.is_empty() && !content.peek(Token![->]) {
                    key.extend([content.parse::<proc_macro2::TokenTree>()?]);
                }
                let key = (|input: ParseStream<'_>| self.term(input, false)).parse2(key)?;
                content.parse::<Token![->]>()?;
                entries.push((key, self.term(content, false)?));
            }
            if content.is_empty() {
                break;
            }
            content.parse::<Token![,]>()?;
        }
        Ok(EntryMap { entries, rest })
    }

    /// Braces: a readable map read (an item holds `->`), readable instance braces, or a
    /// `cells!` instance set.
    fn braces(self, content: ParseStream<'_>, head: bool) -> syn::Result<EntrySpelling> {
        let ahead = content.fork();
        let mut map_read = false;
        while !ahead.is_empty() {
            if ahead.peek(Token![->]) {
                map_read = true;
                break;
            }
            ahead.parse::<proc_macro2::TokenTree>()?;
        }
        if map_read && self.form != EntryForm::Cells {
            let map = self.map(content)?;
            let mut keys = Vec::new();
            for (key, _) in &map.entries {
                // `_` names no key: two of them are two entries, of any keys.
                if *key != EntrySpelling::Wild && keys.contains(&key) {
                    return Err(content.error("a map read names each key once"));
                }
                keys.push(key);
            }
            return Ok(EntrySpelling::MapRead(map));
        }
        let seq = self.seq(content)?;
        Ok(if self.form == EntryForm::Cells && head {
            EntrySpelling::InstanceSet(seq)
        } else {
            EntrySpelling::Braces(seq)
        })
    }

    /// A record's fields and tail.
    fn record(self, head: String, content: ParseStream<'_>) -> syn::Result<EntryRecord> {
        let mut fields = Vec::new();
        let mut tail = RecordTail::Exact;
        while !content.is_empty() {
            if content.peek(Token![..]) {
                content.parse::<Token![..]>()?;
                tail = if content.peek(Ident::peek_any) {
                    RecordTail::Update(content.call(Ident::parse_any)?.unraw().to_string())
                } else {
                    RecordTail::Open
                };
                content.parse::<Option<Token![,]>>()?;
                if !content.is_empty() {
                    return Err(content.error("a record's `..` is last"));
                }
                break;
            }
            let name = content.call(Ident::parse_any)?.unraw().to_string();
            let value = if content.peek(Token![:]) {
                content.parse::<Token![:]>()?;
                self.inner(content)?
            } else {
                EntrySpelling::Binder(name.clone())
            };
            fields.push((name, value));
            if content.is_empty() {
                break;
            }
            content.parse::<Token![,]>()?;
        }
        Ok(EntryRecord { head, fields, tail })
    }
}

/// Whether `input` starts with braces holding a block's statements: a `let`, or a `;` at their top
/// level, which no list of items, record or map holds.
fn is_block(input: ParseStream<'_>) -> bool {
    use proc_macro2::TokenTree;
    let Ok(group) = input.fork().parse::<proc_macro2::Group>() else {
        return false;
    };
    let trees = group.stream().into_iter().collect::<Vec<_>>();
    matches!(trees.first(), Some(TokenTree::Ident(first)) if first == "let")
        || trees
            .iter()
            .any(|tree| matches!(tree, TokenTree::Punct(punct) if punct.as_char() == ';'))
}

/// Whether `input` starts as an entry the reading knows: `_`, a name or a path, brackets,
/// braces, or a literal.
fn starts_entry(input: ParseStream<'_>) -> bool {
    input.peek(Token![_])
        || input.peek(Ident::peek_any)
        || input.peek(Token![::])
        || input.peek(syn::token::Bracket)
        || input.peek(syn::token::Brace)
        || input.peek(Lit)
        || (input.peek(Token![-]) && input.peek2(Lit))
}

/// Whether `expression`, read where a pattern may stand, is a term: no alternatives at a
/// pattern's level ([`crate::recover::holds_alternatives`]) and no rest (`..`) outside a macro.
fn denotes_term(expression: &syn::Expr) -> bool {
    !holds_rest(expression) && !crate::recover::holds_alternatives(expression)
}

/// The tokens of each alternative of a pattern `p | q | ..` that `input` starts with, read to
/// the next `,`, `->` or its end, which it then advances past; `None`, advancing nothing, where
/// it starts with no alternatives.
fn pattern_alternatives(input: ParseStream<'_>) -> Option<Vec<TokenStream>> {
    let cases = |pattern: syn::Pat| match pattern {
        syn::Pat::Or(alternatives) if alternatives.leading_vert.is_none() => Some(
            alternatives
                .cases
                .iter()
                .map(quote::ToTokens::to_token_stream)
                .collect::<Vec<_>>(),
        ),
        _ => None,
    };
    let ahead = input.fork();
    if let Ok(pattern) = syn::Pat::parse_multi(&ahead)
        && (ahead.is_empty() || ahead.peek(Token![,]) || ahead.peek(Token![->]))
    {
        let alternatives = cases(pattern)?;
        input.advance_to(&ahead);
        return Some(alternatives);
    }
    // Alternatives whose leaves only the expression grammar reads (`1 | n + 1`), as the readable
    // reader reads them: a pattern down to those leaves, each the term it denotes.
    let (tokens, count) = crate::recover::next_term(input);
    let alternatives = cases(crate::recover::pattern(&tokens)?)?;
    crate::recover::skip(input, count).ok()?;
    Some(alternatives)
}

/// Whether `expression` holds a rest (`..`) outside a macro.
fn holds_rest(expression: &syn::Expr) -> bool {
    struct Rest(bool);
    impl<'ast> syn::visit::Visit<'ast> for Rest {
        fn visit_expr_range(&mut self, _: &'ast syn::ExprRange) {
            self.0 = true;
        }
    }
    let mut rest = Rest(false);
    syn::visit::Visit::visit_expr(&mut rest, expression);
    rest.0
}

/// One field of a `cells!` payload as a `cells!` [`EntryReading`] reads it.
#[derive(Clone, Debug)]
pub struct CellsField {
    /// The key path, `pc` or `crate::Queue::job`.
    pub key: Path,
    /// The value's spelling; `None` where the value is no entry the reading knows (a term
    /// with an operator, a `k::rewrite!`), which no admission judges.
    pub spelling: Option<EntrySpelling>,
    /// The range of the value's tokens.
    pub value: Option<crate::TokenRange>,
    /// The range of each spelling inside the value, by its path ([`located_spellings`]); empty
    /// where the value is no entry the reading knows.
    pub located: Vec<(Vec<usize>, crate::TokenRange)>,
    /// Where the value is no entry the reading knows, whether it is a `cells!` `KCell(..)` whose
    /// rest is the anonymous `..` ([`anonymous_kcell_rest`]): whether a result's `..` has a rest
    /// to keep is a fact about the entry's frame, not its items (P6), so it is paired though
    /// its items are not read.
    pub anonymous_rest: bool,
}

/// Whether `value` is a `KCell(..)` whose last element is the anonymous rest `..`, read from
/// its frame alone: the elements before it are not read.
#[must_use]
pub fn anonymous_kcell_rest(value: &TokenStream) -> bool {
    use proc_macro2::{Delimiter, Spacing, TokenTree};
    let trees = value.clone().into_iter().collect::<Vec<_>>();
    let [.., TokenTree::Ident(wrapper), TokenTree::Group(content)] = trees.as_slice() else {
        return false;
    };
    if wrapper != "KCell" || content.delimiter() != Delimiter::Parenthesis {
        return false;
    }
    let elements = content.stream().into_iter().collect::<Vec<_>>();
    let last = elements
        .split(|tree| matches!(tree, TokenTree::Punct(punct) if punct.as_char() == ','))
        .rev()
        .find(|element| !element.is_empty());
    matches!(
        last,
        Some([TokenTree::Punct(first), TokenTree::Punct(second)])
            if first.as_char() == '.' && first.spacing() == Spacing::Joint && second.as_char() == '.'
    )
}

/// The fields of a `cells!` payload, each `key: value`, in authored order; the configuration's
/// frame (`..`, `..name`, `name @ ..`) names no cell and is left out. `None` when a part of the
/// payload is neither, so that no field's neighbours are guessed.
#[must_use]
pub fn cells_fields(tokens: &TokenStream) -> Option<Vec<CellsField>> {
    entry_fields(tokens, EntryForm::Cells)
}

/// The fields of a record of cell entries written in `form`, each `key: value`, in authored
/// order: a `cells!` payload, or a readable record's or claim's subject or result (the tokens
/// inside its braces), where a field written as its name alone binds that name (Rust's field
/// shorthand). The configuration's frame (`..`, `..name`, `name @ ..`) names no cell and is left
/// out. `None` when a part of the record is neither, so that no field's neighbours are guessed.
#[must_use]
pub fn entry_fields(tokens: &TokenStream, form: EntryForm) -> Option<Vec<CellsField>> {
    EntryReading::new(form, &[]).fields(tokens)
}

impl EntryReading<'_> {
    /// The fields of a record of cell entries read this way ([`entry_fields`]): an initializer's
    /// body reads its configuration variables as such.
    #[must_use]
    pub fn fields(self, tokens: &TokenStream) -> Option<Vec<CellsField>> {
        read_fields(tokens, self)
    }
}

fn read_fields(tokens: &TokenStream, reading: EntryReading<'_>) -> Option<Vec<CellsField>> {
    use proc_macro2::{Spacing, TokenTree};
    let form = reading.form;
    let trees = tokens.clone().into_iter().collect::<Vec<_>>();
    let mut fields = Vec::new();
    for part in
        trees.split(|tree| matches!(tree, TokenTree::Punct(punct) if punct.as_char() == ','))
    {
        if part.is_empty() {
            continue;
        }
        let is_dot = |tree: Option<&TokenTree>| matches!(tree, Some(TokenTree::Punct(punct)) if punct.as_char() == '.');
        let is_at = |tree: Option<&TokenTree>| matches!(tree, Some(TokenTree::Punct(punct)) if punct.as_char() == '@');
        if is_dot(part.first())
            || (matches!(part.first(), Some(TokenTree::Ident(_)))
                && is_at(part.get(1))
                && is_dot(part.get(2)))
        {
            continue;
        }
        // An initializer's shorthand field `name` is `name: name`, the variable it names.
        if form == EntryForm::Initializer
            && let [TokenTree::Ident(name)] = part
        {
            let value = TokenStream::from(TokenTree::Ident(name.clone()));
            let range = crate::TokenRange::for_tokens(&value).ok();
            let spelling = reading.value(value).ok();
            fields.push(CellsField {
                key: Path::from(name.clone()),
                located: range
                    .filter(|_| spelling.is_some())
                    .map(|range| (Vec::new(), range))
                    .into_iter()
                    .collect(),
                spelling,
                value: range,
                anonymous_rest: false,
            });
            continue;
        }
        if form.is_readable()
            && let [TokenTree::Ident(name)] = part
        {
            let value = TokenStream::from(TokenTree::Ident(name.clone()));
            let range = crate::TokenRange::for_tokens(&value).ok();
            fields.push(CellsField {
                key: Path::from(name.clone()),
                spelling: Some(EntrySpelling::Binder(name.unraw().to_string())),
                value: range,
                located: range.map(|range| (Vec::new(), range)).into_iter().collect(),
                anonymous_rest: false,
            });
            continue;
        }
        // The key ends at the first `:` that is no path separator.
        let mut colon = None;
        let mut index = 0;
        while index < part.len() {
            if let TokenTree::Punct(punct) = &part[index]
                && punct.as_char() == ':'
            {
                if punct.spacing() == Spacing::Joint
                    && matches!(part.get(index + 1), Some(TokenTree::Punct(next)) if next.as_char() == ':')
                {
                    index += 2;
                    continue;
                }
                colon = Some(index);
                break;
            }
            index += 1;
        }
        let colon = colon?;
        let key = (|input: ParseStream<'_>| input.call(Path::parse_mod_style))
            .parse2(part[..colon].iter().cloned().collect())
            .ok()?;
        let value = part[colon + 1..].iter().cloned().collect::<TokenStream>();
        let spelling = reading.value(value.clone()).ok();
        fields.push(CellsField {
            key,
            located: spelling
                .as_ref()
                .map_or_else(Vec::new, |spelling| located_spellings(&value, spelling)),
            anonymous_rest: spelling.is_none()
                && form == EntryForm::Cells
                && anonymous_kcell_rest(&value),
            spelling,
            value: crate::TokenRange::for_tokens(&value).ok(),
        });
    }
    Some(fields)
}

/// The tokens of the spelling at `at` inside `spelling`, an entry's value read from `tokens`
/// ([`crate::cell_entries::Located::at`]: a step is the index of a spelling among those directly
/// inside the one before, or [`crate::cell_entries::REST`] for a sequence's or a map's rest).
/// `None` where the path leads to no spelling the tokens hold. The tokens are walked as the
/// reader read them, so a refusal raised inside an entry is placed at what it refuses.
#[must_use]
pub fn locate(tokens: &TokenStream, spelling: &EntrySpelling, at: &[usize]) -> Option<TokenStream> {
    let Some((&step, below)) = at.split_first() else {
        return Some(tokens.clone());
    };
    let (tokens, child) = child_tokens(tokens, spelling, step)?;
    match child {
        Some(child) => locate(&tokens, child, below),
        None => below.is_empty().then_some(tokens),
    }
}

/// Every spelling inside `spelling`, read from `tokens`, with its path and its tokens' range
/// ([`locate`]), the value itself first with the empty path, and each rest with its
/// [`crate::cell_entries::REST`] step.
#[must_use]
pub fn located_spellings(
    tokens: &TokenStream,
    spelling: &EntrySpelling,
) -> Vec<(Vec<usize>, crate::TokenRange)> {
    fn walk(
        tokens: &TokenStream,
        spelling: &EntrySpelling,
        path: &mut Vec<usize>,
        out: &mut Vec<(Vec<usize>, crate::TokenRange)>,
    ) {
        if let Ok(range) = crate::TokenRange::for_tokens(tokens) {
            out.push((path.clone(), range));
        }
        let steps = (0..spelling_children(spelling))
            .chain(has_rest(spelling).then_some(crate::cell_entries::REST));
        for step in steps {
            let Some((child_tokens, child)) = child_tokens(tokens, spelling, step) else {
                continue;
            };
            path.push(step);
            match child {
                Some(child) => walk(&child_tokens, child, path, out),
                None => {
                    if let Ok(range) = crate::TokenRange::for_tokens(&child_tokens) {
                        out.push((path.clone(), range));
                    }
                }
            }
            path.pop();
        }
    }
    let mut out = Vec::new();
    walk(tokens, spelling, &mut Vec::new(), &mut out);
    out
}

/// How many spellings stand directly inside `spelling`.
fn spelling_children(spelling: &EntrySpelling) -> usize {
    match spelling {
        EntrySpelling::Present(_)
        | EntrySpelling::Absent(_)
        | EntrySpelling::Cell(_)
        | EntrySpelling::Alias(..) => 1,
        EntrySpelling::Record(record) | EntrySpelling::Fragment(record) => record.fields.len(),
        EntrySpelling::Call(arguments) | EntrySpelling::Alternatives(arguments) => arguments.len(),
        EntrySpelling::Brackets(seq)
        | EntrySpelling::Braces(seq)
        | EntrySpelling::KCell(seq)
        | EntrySpelling::InstanceList(seq)
        | EntrySpelling::InstanceSet(seq)
        | EntrySpelling::KMacro(seq) => seq.items.len(),
        EntrySpelling::MapRead(map) | EntrySpelling::MapLiteral(map) => 2 * map.entries.len(),
        _ => 0,
    }
}

fn has_rest(spelling: &EntrySpelling) -> bool {
    match spelling {
        EntrySpelling::Brackets(seq)
        | EntrySpelling::Braces(seq)
        | EntrySpelling::KCell(seq)
        | EntrySpelling::InstanceList(seq)
        | EntrySpelling::InstanceSet(seq)
        | EntrySpelling::KMacro(seq) => seq.rest.is_some(),
        EntrySpelling::MapRead(map) | EntrySpelling::MapLiteral(map) => map.rest.is_some(),
        _ => false,
    }
}

/// The tokens of the spelling at `step` directly inside `spelling` (read from `tokens`), with
/// that spelling; a rest's tokens, with none.
#[expect(
    clippy::too_many_lines,
    reason = "One match walks the tokens of every spelling as the reader reads them."
)]
fn child_tokens<'s>(
    tokens: &TokenStream,
    spelling: &'s EntrySpelling,
    step: usize,
) -> Option<(TokenStream, Option<&'s EntrySpelling>)> {
    use proc_macro2::{Delimiter, TokenTree};
    let trees = tokens.clone().into_iter().collect::<Vec<_>>();
    // The first group after the head's path (and a macro's `!`), delimited by `delimiter` where
    // one is given.
    let group = |delimiter: Option<Delimiter>| {
        trees.iter().find_map(|tree| match tree {
            TokenTree::Group(group)
                if delimiter.is_none_or(|wanted| group.delimiter() == wanted) =>
            {
                Some(group.stream())
            }
            _ => None,
        })
    };
    let parts = |stream: TokenStream| {
        let trees = stream.into_iter().collect::<Vec<_>>();
        trees
            .split(|tree| matches!(tree, TokenTree::Punct(punct) if punct.as_char() == ','))
            .filter(|part| !part.is_empty())
            .map(<[TokenTree]>::to_vec)
            .collect::<Vec<_>>()
    };
    let is_punct = |tree: Option<&TokenTree>, wanted: char| matches!(tree, Some(TokenTree::Punct(punct)) if punct.as_char() == wanted);
    let is_rest = |part: &[TokenTree]| {
        is_punct(part.first(), '.')
            || (matches!(part.first(), Some(TokenTree::Ident(_)))
                && is_punct(part.get(1), '@')
                && is_punct(part.get(2), '.'))
    };
    let stream = |part: &[TokenTree]| part.iter().cloned().collect::<TokenStream>();
    let in_order = |stream_of: TokenStream, items: &'s [EntrySpelling]| {
        let parts = parts(stream_of);
        if step == crate::cell_entries::REST {
            return parts
                .iter()
                .find(|part| is_rest(part))
                .map(|part| (stream(part), None));
        }
        let part = parts.iter().filter(|part| !is_rest(part)).nth(step)?;
        Some((stream(part), Some(items.get(step)?)))
    };
    match spelling {
        // Each alternative's tokens stand between the top-level `|`s.
        EntrySpelling::Alternatives(arguments) => {
            let part = trees
                .split(|tree| matches!(tree, TokenTree::Punct(punct) if punct.as_char() == '|'))
                .nth(step)?;
            Some((stream(part), Some(arguments.get(step)?)))
        }
        EntrySpelling::Alias(name, inner) if step == 0 && name.is_empty() => {
            let [TokenTree::Group(group)] = trees.as_slice() else {
                return None;
            };
            Some((group.stream(), Some(&**inner)))
        }
        EntrySpelling::Alias(_, inner) if step == 0 => {
            Some((stream(trees.get(2..)?), Some(&**inner)))
        }
        EntrySpelling::Present(inner) | EntrySpelling::Absent(inner) if step == 0 => {
            Some((group(None)?, Some(&**inner)))
        }
        EntrySpelling::Cell(inner) if step == 0 => {
            let content = parts(group(Some(Delimiter::Parenthesis))?);
            Some((stream(content.first()?), Some(&**inner)))
        }
        EntrySpelling::Call(arguments) => {
            let part = parts(group(Some(Delimiter::Parenthesis))?)
                .into_iter()
                .nth(step)?;
            Some((stream(&part), Some(arguments.get(step)?)))
        }
        EntrySpelling::Record(record) | EntrySpelling::Fragment(record) => {
            let fields = match spelling {
                EntrySpelling::Fragment(_) => {
                    let inside = group(None)?.into_iter().collect::<Vec<_>>();
                    inside.iter().find_map(|tree| match tree {
                        TokenTree::Group(group) if group.delimiter() == Delimiter::Brace => {
                            Some(group.stream())
                        }
                        _ => None,
                    })?
                }
                _ => group(Some(Delimiter::Brace))?,
            };
            let part = parts(fields)
                .into_iter()
                .filter(|part| !is_punct(part.first(), '.'))
                .nth(step)?;
            let (_, value) = record.fields.get(step)?;
            // The value follows the first `:` that is no path separator; a shorthand field is
            // its name alone.
            let mut index = 0;
            while index < part.len() {
                if let TokenTree::Punct(punct) = &part[index]
                    && punct.as_char() == ':'
                {
                    if punct.spacing() == proc_macro2::Spacing::Joint
                        && is_punct(part.get(index + 1), ':')
                    {
                        index += 2;
                        continue;
                    }
                    return Some((stream(&part[index + 1..]), Some(value)));
                }
                index += 1;
            }
            Some((stream(&part), Some(value)))
        }
        EntrySpelling::Brackets(seq)
        | EntrySpelling::Braces(seq)
        | EntrySpelling::InstanceList(seq)
        | EntrySpelling::InstanceSet(seq)
        | EntrySpelling::KMacro(seq) => in_order(group(None)?, &seq.items),
        EntrySpelling::KCell(seq) => in_order(group(Some(Delimiter::Parenthesis))?, &seq.items),
        EntrySpelling::MapRead(map) | EntrySpelling::MapLiteral(map) => {
            let parts = parts(group(None)?);
            if step == crate::cell_entries::REST {
                return parts
                    .iter()
                    .find(|part| is_rest(part))
                    .map(|part| (stream(part), None));
            }
            let part = parts.iter().filter(|part| !is_rest(part)).nth(step / 2)?;
            let arrow = (0..part.len()).find(|&index| {
                matches!(&part[index], TokenTree::Punct(punct) if punct.as_char() == '-' && punct.spacing() == proc_macro2::Spacing::Joint)
                    && is_punct(part.get(index + 1), '>')
            })?;
            let (key, value) = map.entries.get(step / 2)?;
            Some(if step.is_multiple_of(2) {
                (stream(&part[..arrow]), Some(key))
            } else {
                (stream(&part[arrow + 2..]), Some(value))
            })
        }
        _ => None,
    }
}

#[cfg(test)]
mod cells_fields_tests {
    use super::{EntrySpelling, cells_fields};

    #[test]
    fn a_payloads_fields_are_read_in_order_and_its_frame_names_no_cell() {
        let tokens = "pc: k::configuration::Cell(x), crate::Frame::env: k::configuration::Cell(k::map![y -> x, ..]), k: k::configuration::KCell(x + 1, ..), rest @ .."
            .parse()
            .expect("lexes");
        let fields = cells_fields(&tokens).expect("a list of fields");
        let names = fields
            .iter()
            .map(|field| field.key.segments.last().expect("a name").ident.to_string())
            .collect::<Vec<_>>();
        assert_eq!(names, ["pc", "env", "k"]);
        assert_eq!(
            fields[0].spelling,
            Some(EntrySpelling::Cell(Box::new(EntrySpelling::Binder(
                "x".to_owned()
            ))))
        );
        assert!(matches!(fields[1].spelling, Some(EntrySpelling::Cell(_))));
        // A term with an operator is a term, as its named function's application is: the
        // computation's items and its rest are read, and the rest is paired by the spelling.
        assert_eq!(
            fields[2].spelling,
            Some(EntrySpelling::KCell(super::EntrySeq {
                items: vec![EntrySpelling::Call(Vec::new())],
                rest: Some((super::EntryRest::Anonymous, super::RestPlace::Back)),
                more_rests: 0,
            }))
        );
        assert!(!fields[2].anonymous_rest);
        assert!(!fields[0].anonymous_rest);
        let rest = |value: &str| super::anonymous_kcell_rest(&value.parse().expect("lexes"));
        assert!(rest("k::configuration::KCell(x + 1, ..,)"));
        assert!(!rest("k::configuration::KCell(x + 1, tail @ ..)"));
        assert!(!rest("k::configuration::KCell(x + 1, ..tail)"));
        assert!(!rest("k::configuration::KCell(x + 1)"));
        assert!(!rest("k::configuration::Cell(..)"));
        assert!(fields.iter().all(|field| field.value.is_some()));
    }

    #[test]
    fn a_readable_records_fields_are_read_with_their_shorthand_and_its_frame_names_no_cell() {
        let tokens = "k: [Go(), ..], pc, env: { a -> x, .. }, .."
            .parse()
            .expect("lexes");
        let fields = super::entry_fields(&tokens, super::EntryForm::Readable).expect("fields");
        let names = fields
            .iter()
            .map(|field| field.key.segments.last().expect("a name").ident.to_string())
            .collect::<Vec<_>>();
        assert_eq!(names, ["k", "pc", "env"]);
        assert!(matches!(
            fields[0].spelling,
            Some(EntrySpelling::Brackets(_))
        ));
        assert_eq!(
            fields[1].spelling,
            Some(EntrySpelling::Binder("pc".to_owned()))
        );
        assert!(matches!(
            fields[2].spelling,
            Some(EntrySpelling::MapRead(_))
        ));
        assert!(fields.iter().all(|field| field.value.is_some()));
    }

    #[test]
    fn an_initializer_s_value_that_is_no_entry_is_a_term_and_its_shorthand_its_variable() {
        let tokens = "pc: [0 + 1, x], shelf: Shelf { n: 0 + 1, bag: [f(0 + 1)] }, pgm, k: 0 + 1, \
                      counter: Some(0 + 1), olist: k::absent!({ let y = pgm; y })"
            .parse()
            .expect("lexes");
        let variables = ["pgm".to_owned()];
        let fields = super::EntryReading::new(super::EntryForm::Initializer, &variables)
            .fields(&tokens)
            .expect("fields");
        let term = || EntrySpelling::Call(Vec::new());
        assert_eq!(
            fields[0].spelling,
            Some(EntrySpelling::Brackets(super::EntrySeq {
                items: vec![term(), EntrySpelling::Binder("x".to_owned())],
                rest: None,
                more_rests: 0,
            }))
        );
        assert_eq!(
            fields[1].spelling,
            Some(EntrySpelling::Record(super::EntryRecord {
                head: "Shelf".to_owned(),
                fields: vec![
                    ("n".to_owned(), term()),
                    (
                        "bag".to_owned(),
                        EntrySpelling::Brackets(super::EntrySeq {
                            items: vec![EntrySpelling::Call(vec![term()])],
                            rest: None,
                            more_rests: 0,
                        })
                    ),
                ],
                tail: super::RecordTail::Exact,
            }))
        );
        assert_eq!(
            fields[2].spelling,
            Some(EntrySpelling::ConfigVar("pgm".to_owned()))
        );
        // At the entry's head, and inside its presence, a value that is no entry is a term too:
        // its marks, or their absence, are judged against its cell's kind.
        assert_eq!(fields[3].spelling, Some(term()));
        assert_eq!(
            fields[4].spelling,
            Some(EntrySpelling::Present(Box::new(term())))
        );
        assert_eq!(
            fields[5].spelling,
            Some(EntrySpelling::Absent(Box::new(term())))
        );
        let located = super::located_spellings(
            &"[0 + 1, x]".parse().expect("lexes"),
            fields[0].spelling.as_ref().expect("read"),
        );
        assert_eq!(located.len(), 3);
    }

    /// Operator notation is a spelling of the term its function's application is, so on every
    /// form a value written with it is read where its named twin is, a term of some sort, and
    /// the entry around it is judged alike (RDRA item 2, AUDIT-R P7). Where a pattern may stand,
    /// alternatives and a rest are no term and stay unread.
    #[test]
    fn an_operator_value_is_a_term_on_every_form() {
        let term = || EntrySpelling::Call(Vec::new());
        for form in [
            super::EntryForm::Readable,
            super::EntryForm::Claim,
            super::EntryForm::Cells,
            super::EntryForm::Initializer,
        ] {
            let read = |text: &str| {
                super::EntryReading::new(form, &[])
                    .value(text.parse().expect("lexes"))
                    .ok()
            };
            assert_eq!(read("x + 1"), Some(term()), "{form:?}");
            assert_eq!(
                read("Some(x + 1)"),
                Some(EntrySpelling::Present(Box::new(term()))),
                "{form:?}"
            );
            assert_eq!(
                read("Rec { a: x.len(), b: y }"),
                Some(EntrySpelling::Record(super::EntryRecord {
                    head: "Rec".to_owned(),
                    fields: vec![
                        ("a".to_owned(), term()),
                        ("b".to_owned(), EntrySpelling::Binder("y".to_owned())),
                    ],
                    tail: super::RecordTail::Exact,
                })),
                "{form:?}"
            );
            let Some(EntrySpelling::MapLiteral(map)) = read("k::map![x + 1 -> y * 2, z -> w]")
            else {
                panic!("{form:?}: a map literal");
            };
            assert_eq!(
                map.entries,
                [
                    (term(), term()),
                    (
                        EntrySpelling::Binder("z".to_owned()),
                        EntrySpelling::Binder("w".to_owned())
                    )
                ],
                "{form:?}"
            );
            // Pattern alternatives are each an entry of the cell, in order, so every one is the
            // kind's to judge; an initializer builds, so they are its term.
            let literal = |text: &str| EntrySpelling::Literal(text.to_owned());
            let alternatives = EntrySpelling::Alternatives;
            if form == super::EntryForm::Initializer {
                assert_eq!(
                    read("Some(1 | 2)"),
                    Some(EntrySpelling::Present(Box::new(term()))),
                    "{form:?}"
                );
            } else {
                assert_eq!(
                    read("x | 1"),
                    Some(alternatives(vec![
                        EntrySpelling::Binder("x".to_owned()),
                        literal("1"),
                    ])),
                    "{form:?}"
                );
                assert_eq!(
                    read("Some(1 | 2)"),
                    Some(EntrySpelling::Present(Box::new(alternatives(vec![
                        literal("1"),
                        literal("2")
                    ])))),
                    "{form:?}"
                );
            }
        }
        let cells = |text: &str| {
            super::EntryReading::new(super::EntryForm::Cells, &[])
                .value(text.parse().expect("lexes"))
                .ok()
        };
        assert_eq!(
            cells("k::configuration::Cell(x + 1)"),
            Some(EntrySpelling::Cell(Box::new(term())))
        );
        assert_eq!(cells("k::configuration::Cell(..)"), None);
        assert_eq!(
            cells("Some(k::configuration::Cell(s | s))"),
            Some(EntrySpelling::Present(Box::new(EntrySpelling::Cell(
                Box::new(EntrySpelling::Alternatives(vec![
                    EntrySpelling::Binder("s".to_owned()),
                    EntrySpelling::Binder("s".to_owned()),
                ]))
            ))))
        );
        let Some(EntrySpelling::Brackets(seq)) =
            super::EntryReading::new(super::EntryForm::Readable, &[])
                .value("[x + 1, ..]".parse().expect("lexes"))
                .ok()
        else {
            panic!("brackets");
        };
        assert_eq!(seq.items, [term()]);
    }

    #[test]
    fn a_spelling_inside_a_value_is_located_at_its_own_tokens() {
        use crate::cell_entries::REST;
        let read = |text: &str| {
            let tokens: proc_macro2::TokenStream = text.parse().expect("lexes");
            let spelling = super::EntryReading::new(super::EntryForm::Readable, &[])
                .value(tokens.clone())
                .expect("reads");
            (tokens, spelling)
        };
        let at = |text: &str, path: &[usize]| {
            let (tokens, spelling) = read(text);
            super::locate(&tokens, &spelling, path).map(|found| found.to_string())
        };
        assert_eq!(
            at("Outer { frame: Frame { pc: p }, flag: f }", &[0]).as_deref(),
            Some("Frame { pc : p }")
        );
        assert_eq!(
            at("Outer { frame: Frame { pc: p }, flag }", &[1]).as_deref(),
            Some("flag")
        );
        assert_eq!(at("[x, r @ ..]", &[REST]).as_deref(), Some("r @ .."));
        assert_eq!(at("[x, r @ ..]", &[0]).as_deref(), Some("x"));
        assert_eq!(at("{ a -> x, .. }", &[1]).as_deref(), Some("x"));
        assert_eq!(at("Some(_)", &[0]).as_deref(), Some("_"));
        assert_eq!(at("y @ Cmd::Hold(_)", &[0, 0]).as_deref(), Some("_"));
        assert_eq!(
            at("{ Job { payload: map![y -> x, ..] }, .. }", &[0, 0]).as_deref(),
            Some("map ! [y -> x , ..]")
        );
        assert_eq!(at("[x, ..]", &[1]), None);
        let (tokens, spelling) = read("Some(G { a: [x, ..] })");
        let paths = super::located_spellings(&tokens, &spelling)
            .into_iter()
            .map(|(path, _)| path)
            .collect::<Vec<_>>();
        assert_eq!(
            paths,
            [vec![], vec![0], vec![0, 0], vec![0, 0, 0], vec![0, 0, REST]]
        );
    }

    #[test]
    fn a_part_that_is_no_field_reads_no_payload() {
        let tokens = "pc: k::configuration::Cell(x), Foo::<A, B>"
            .parse()
            .expect("lexes");
        assert!(cells_fields(&tokens).is_none());
    }
}
