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
//! read; an initializer names its configuration variables.
//!
//! The shape rules hold here: a sequence or map has at most one rest, `Some(..)` holds one
//! entry, and a map read names each key once.

use proc_macro2::TokenStream;
use syn::ext::IdentExt;
use syn::parse::{ParseStream, Parser};
use syn::{Ident, Lit, Path, Token, braced, bracketed, parenthesized};

/// The form an entry is written in.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum EntryForm {
    /// A readable record (`k::rules!` with `for Machine`).
    Readable,
    /// A readable claim.
    Claim,
    /// A `cells!` entry.
    Cells,
    /// An initializer's field.
    Initializer,
}

impl EntryForm {
    /// Whether the form is a readable record or claim.
    #[must_use]
    pub const fn is_readable(self) -> bool {
        matches!(self, Self::Readable | Self::Claim)
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
    /// `name @ pattern`.
    Alias(String, Box<Self>),
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
        self.parse(input, true)
    }

    /// [`Self::field`] over a parse stream.
    ///
    /// # Errors
    ///
    /// As [`Self::field`].
    pub fn parse_field(self, input: ParseStream<'_>) -> syn::Result<(Path, EntrySpelling)> {
        let key = input.call(Path::parse_mod_style)?;
        input.parse::<Token![:]>()?;
        Ok((key, self.parse(input, true)?))
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
        let path = input.call(Path::parse_mod_style)?;
        let last = path
            .segments
            .last()
            .map(|segment| segment.ident.unraw().to_string())
            .unwrap_or_default();
        if input.peek(Token![!]) {
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
                let inner = self.parse(content, head)?;
                if !content.is_empty() {
                    return Err(content.error("`Some(..)` holds one entry"));
                }
                Ok(EntrySpelling::Present(Box::new(inner)))
            }
            "Cell" if self.form == EntryForm::Cells => {
                let inner = self.parse(content, false)?;
                content.parse::<Option<Token![,]>>()?;
                if !content.is_empty() {
                    return Err(content.error("`Cell(..)` holds one value"));
                }
                Ok(EntrySpelling::Cell(Box::new(inner)))
            }
            "KCell" if self.form == EntryForm::Cells => {
                Ok(EntrySpelling::KCell(self.seq(content)?))
            }
            _ => {
                let mut arguments = Vec::new();
                while !content.is_empty() {
                    arguments.push(self.parse(content, false)?);
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
                self.parse(&content, false)?,
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
            if input.peek(Ident::peek_any) {
                let name = input.call(Ident::parse_any)?.unraw().to_string();
                return Ok(Some(EntryRest::Splice(name)));
            }
            return Ok(Some(EntryRest::Anonymous));
        }
        if input.peek(Ident::peek_any) && input.peek2(Token![@]) && input.peek3(Token![..]) {
            let name = input.call(Ident::parse_any)?.unraw().to_string();
            input.parse::<Token![@]>()?;
            input.parse::<Token![..]>()?;
            return Ok(Some(EntryRest::Named(name)));
        }
        Ok(None)
    }

    /// Comma-separated items with at most one rest.
    fn seq(self, content: ParseStream<'_>) -> syn::Result<EntrySeq> {
        let mut items = Vec::new();
        let mut rest = None;
        while !content.is_empty() {
            if let Some(found) = Self::rest(content)? {
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
                items.push(self.parse(content, false)?);
            }
            if content.is_empty() {
                break;
            }
            content.parse::<Token![,]>()?;
        }
        Ok(EntrySeq { items, rest })
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
                let key = self.parse(content, false)?;
                content.parse::<Token![->]>()?;
                entries.push((key, self.parse(content, false)?));
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
                if keys.contains(&key) {
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
                self.parse(content, false)?
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
}

/// The fields of a `cells!` payload, each `key: value`, in authored order; the configuration's
/// frame (`..`, `..name`, `name @ ..`) names no cell and is left out. `None` when a part of the
/// payload is neither, so that no field's neighbours are guessed.
#[must_use]
pub fn cells_fields(tokens: &TokenStream) -> Option<Vec<CellsField>> {
    use proc_macro2::{Spacing, TokenTree};
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
        fields.push(CellsField {
            key,
            spelling: EntryReading::new(EntryForm::Cells, &[])
                .value(value.clone())
                .ok(),
            value: crate::TokenRange::for_tokens(&value).ok(),
        });
    }
    Some(fields)
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
        // A term with an operator is no entry the reading knows: nothing judges it.
        assert_eq!(fields[2].spelling, None);
        assert!(fields.iter().all(|field| field.value.is_some()));
    }

    #[test]
    fn a_part_that_is_no_field_reads_no_payload() {
        let tokens = "pc: k::configuration::Cell(x), Foo::<A, B>"
            .parse()
            .expect("lexes");
        assert!(cells_fields(&tokens).is_none());
    }
}
