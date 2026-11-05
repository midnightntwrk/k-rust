//! The reading of one cell entry: what an author writes at one cell of a `k::cells!` subject or
//! result, printed from the entry's IR-level form.
//!
//! This is the entry point for every printer that writes cell entries: `krs expand` reaches it
//! from the transported head rule, and a printer of a K configuration reaches it from the cell
//! contents converted to [`Entry`]. Its input holds no readable-source tokens, only terms
//! already printed and the entry's structure, so the reading depends on what the entry denotes,
//! not on how its source spelled it.
//!
//! Its scope is a top-level fixed cell of the configuration: it writes the wrappers
//! `k::configuration::KCell(..)` and `k::configuration::Cell(..)`, and a map entry's `map![..]`
//! relies on the printed file's import of the `map!` macro. An entry of an instance record or
//! inside `Some(..)` writes `k::k![..]` and `k::map!` instead and is not printed here.
//!
//! An anonymous rest stays `..` on both sides: the subject's `..` matches the rest of the cell
//! and the result's `..` keeps that same rest, which is what a name bound in the subject and
//! written back in the result denotes, so no name is invented for it. A named rest is bound in
//! the subject (`r @ ..`) and written in the result (`..r`), where it may be any term of the
//! cell's sort.

use proc_macro2::TokenStream;
use quote::quote;

/// The side of a rule an entry stands on.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Side {
    Subject,
    Result,
}

/// What follows an entry's written contents.
#[derive(Clone, Debug)]
pub(crate) enum Rest {
    /// Nothing: the entry names the whole cell.
    Exact,
    /// The anonymous `..`: the rest of the cell in the subject, the same rest kept in the result.
    Anonymous,
    /// A named rest: in the subject the binder `r` of `r @ ..`, in the result the term `t` of
    /// `..t`.
    Named(TokenStream),
}

/// Which list a list cell holds.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ListKind {
    /// A `#[k::cons_list]` sort, built from its front by its constructors.
    Cons,
    /// K's builtin `List`.
    Builtin,
}

/// An entry's written contents, by the kind its cell declares.
#[derive(Clone, Debug)]
pub(crate) enum Contents {
    /// A K-sequence cell (`KCell`): its items, front first.
    KSequence(Vec<TokenStream>),
    /// A `Map` cell: its `key -> value` pairs, in written order.
    Map(Vec<(TokenStream, TokenStream)>),
    /// A list cell, a cons list or K's `List`: the items before the rest and the items after
    /// it, each front first. Only a `List` has items after the rest, and only when it has a rest.
    List {
        kind: ListKind,
        items: Vec<TokenStream>,
        back: Vec<TokenStream>,
    },
}

/// One cell entry in IR-level form: what it writes and what follows.
#[derive(Clone, Debug)]
pub(crate) struct Entry {
    pub(crate) contents: Contents,
    pub(crate) rest: Rest,
}

/// An entry `k::cells!` refuses, which has no reading to print.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct IllegalEntry(&'static str);

impl From<IllegalEntry> for super::ReferenceExpansionError {
    fn from(IllegalEntry(reason): IllegalEntry) -> Self {
        Self::IllegalEntry(reason)
    }
}

/// The entry `field: value` as an author reads it on `side`: `k: KCell(x, ..)`,
/// `env: Cell(map![k -> v, ..])`, `stack: Cell([a, rest @ ..])` and `stack: Cell([b, ..rest])`.
///
/// # Errors
///
/// [`IllegalEntry`] for an entry `k::cells!` refuses: an anonymous rest in a result map, whose
/// `..` names no map the entries are written over; brackets that hold an anonymous rest and no
/// item (`[..]`, which name no element); and items after a cons list's rest, since a cons list
/// is built from its front.
pub(crate) fn print_entry(
    field: &TokenStream,
    entry: &Entry,
    side: Side,
) -> Result<TokenStream, IllegalEntry> {
    match (&entry.contents, &entry.rest, side) {
        (Contents::Map(_), Rest::Anonymous, Side::Result) => {
            return Err(IllegalEntry(
                "an anonymous `..` in a result map literal: a result names the map's rest",
            ));
        }
        (Contents::List { items, back, .. }, Rest::Anonymous, _)
            if items.is_empty() && back.is_empty() =>
        {
            return Err(IllegalEntry(
                "brackets holding only an anonymous `..`: `[..]` names no element",
            ));
        }
        (
            Contents::List {
                kind: ListKind::Cons,
                back,
                ..
            },
            ..,
        ) if !back.is_empty() => {
            return Err(IllegalEntry(
                "an item after a cons list's rest: a cons list is built from its front",
            ));
        }
        _ => {}
    }
    let rest = match (&entry.rest, side) {
        (Rest::Exact, _) => None,
        (Rest::Anonymous, _) => Some(quote!(..)),
        (Rest::Named(rest), Side::Subject) => Some(quote!(#rest @ ..)),
        (Rest::Named(rest), Side::Result) => Some(quote!(..#rest)),
    };
    let value = match &entry.contents {
        Contents::KSequence(items) => {
            let parts = items.iter().cloned().chain(rest);
            quote!(k::configuration::KCell(#(#parts),*))
        }
        Contents::Map(pairs) => {
            let parts = pairs
                .iter()
                .map(|(key, value)| quote!(#key -> #value))
                .chain(rest);
            quote!(k::configuration::Cell(map![#(#parts),*]))
        }
        // Brackets that hold only a named rest are the list it names (`[..r]` is `r`), and
        // `r` alone, not `[r @ ..]`, is the pattern binding the whole list.
        Contents::List { items, back, .. } if items.is_empty() && back.is_empty() => {
            match &entry.rest {
                Rest::Named(rest) => quote!(k::configuration::Cell(#rest)),
                Rest::Exact => quote!(k::configuration::Cell([])),
                Rest::Anonymous => unreachable!("refused above"),
            }
        }
        Contents::List { items, back, .. } => {
            let parts = items
                .iter()
                .cloned()
                .chain(rest)
                .chain(back.iter().cloned());
            quote!(k::configuration::Cell([#(#parts),*]))
        }
    };
    Ok(quote!(#field: #value))
}

/// A group cell's record `Owner { field: value, .. }` as an author reads it: the children
/// `fields` written, then `..` when the record is `open`, which leaves every child it does not
/// name unconstrained.
pub(crate) fn print_record(
    owner: &TokenStream,
    fields: &[(TokenStream, TokenStream)],
    open: bool,
) -> TokenStream {
    let fields = fields.iter().map(|(name, value)| quote!(#name: #value));
    let open = open.then(|| quote!(..));
    let parts = fields.chain(open);
    quote!(k::fragment![#owner { #(#parts),* }])
}

#[cfg(test)]
mod tests {
    use super::{Contents, Entry, ListKind, Rest, Side, print_entry, print_record};
    use quote::quote;

    fn printed(contents: Contents, rest: Rest, side: Side) -> String {
        print_entry(&quote!(k), &Entry { contents, rest }, side)
            .expect("a legal entry")
            .to_string()
    }

    #[test]
    fn an_anonymous_rest_prints_as_written_on_both_sides() {
        let items = || Contents::KSequence(vec![quote!(x)]);
        assert_eq!(
            printed(items(), Rest::Anonymous, Side::Subject),
            "k : k :: configuration :: KCell (x , ..)"
        );
        assert_eq!(
            printed(items(), Rest::Anonymous, Side::Result),
            "k : k :: configuration :: KCell (x , ..)"
        );
        assert_eq!(
            printed(
                Contents::KSequence(Vec::new()),
                Rest::Anonymous,
                Side::Result
            ),
            "k : k :: configuration :: KCell (..)"
        );
        assert_eq!(
            printed(Contents::KSequence(Vec::new()), Rest::Exact, Side::Result),
            "k : k :: configuration :: KCell ()"
        );
    }

    #[test]
    fn a_map_entry_prints_its_pairs_and_its_rest() {
        let pairs = Contents::Map(vec![(quote!(name), quote!(value))]);
        assert_eq!(
            printed(pairs, Rest::Anonymous, Side::Subject),
            "k : k :: configuration :: Cell (map ! [name -> value , ..])"
        );
    }

    #[test]
    fn a_list_entry_prints_its_brackets_and_its_rest_as_written() {
        let list = |items: Vec<_>, back: Vec<_>| Contents::List {
            kind: ListKind::Builtin,
            items,
            back,
        };
        assert_eq!(
            printed(
                list(vec![quote!(a)], Vec::new()),
                Rest::Named(quote!(rest)),
                Side::Subject
            ),
            "k : k :: configuration :: Cell ([a , rest @ ..])"
        );
        assert_eq!(
            printed(
                list(vec![quote!(x)], Vec::new()),
                Rest::Named(quote!(s)),
                Side::Result
            ),
            "k : k :: configuration :: Cell ([x , .. s])"
        );
        assert_eq!(
            printed(list(Vec::new(), Vec::new()), Rest::Exact, Side::Result),
            "k : k :: configuration :: Cell ([])"
        );
        assert_eq!(
            printed(
                list(Vec::new(), vec![quote!(z)]),
                Rest::Named(quote!(init)),
                Side::Result
            ),
            "k : k :: configuration :: Cell ([.. init , z])"
        );
        assert_eq!(
            printed(
                list(vec![quote!(a)], vec![quote!(z)]),
                Rest::Named(quote!(mid)),
                Side::Subject
            ),
            "k : k :: configuration :: Cell ([a , mid @ .. , z])"
        );
        assert_eq!(
            printed(
                list(Vec::new(), Vec::new()),
                Rest::Named(quote!(r)),
                Side::Result
            ),
            "k : k :: configuration :: Cell (r)"
        );
    }

    #[test]
    fn an_open_record_prints_its_written_children_and_its_rest() {
        let fields = [(quote!(gas), quote!(g))];
        assert_eq!(
            print_record(&quote!(CallState), &fields, true).to_string(),
            "k :: fragment ! [CallState { gas : g , .. }]"
        );
        assert_eq!(
            print_record(&quote!(CallState), &fields, false).to_string(),
            "k :: fragment ! [CallState { gas : g }]"
        );
        assert_eq!(
            print_record(&quote!(CallState), &[], true).to_string(),
            "k :: fragment ! [CallState { .. }]"
        );
    }

    #[test]
    fn an_entry_cells_refuses_has_no_reading() {
        let refused = |contents, rest, side| {
            print_entry(&quote!(k), &Entry { contents, rest }, side).is_err()
        };
        let pairs = || Contents::Map(vec![(quote!(name), quote!(value))]);
        assert!(refused(pairs(), Rest::Anonymous, Side::Result));
        assert!(!refused(pairs(), Rest::Anonymous, Side::Subject));
        let list = |kind, back: Vec<_>| Contents::List {
            kind,
            items: vec![quote!(a)],
            back,
        };
        assert!(!refused(
            list(ListKind::Cons, Vec::new()),
            Rest::Anonymous,
            Side::Result
        ));
        let bare = |kind| Contents::List {
            kind,
            items: Vec::new(),
            back: Vec::new(),
        };
        assert!(refused(
            bare(ListKind::Cons),
            Rest::Anonymous,
            Side::Subject
        ));
        assert!(refused(
            bare(ListKind::Builtin),
            Rest::Anonymous,
            Side::Result
        ));
        assert!(refused(
            list(ListKind::Cons, vec![quote!(z)]),
            Rest::Named(quote!(r)),
            Side::Subject
        ));
        assert!(!refused(
            list(ListKind::Builtin, vec![quote!(z)]),
            Rest::Named(quote!(r)),
            Side::Subject
        ));
    }
}
