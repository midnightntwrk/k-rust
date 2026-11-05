//! The reading of one cell entry: what an author writes at one cell of a `k::cells!` subject or
//! result, printed from the entry's IR-level form.
//!
//! This is the entry point for every printer that writes cell entries: `krs expand` reaches it
//! from the transported head rule, and a printer of a K configuration reaches it from the cell
//! contents converted to [`Entry`]. Its input holds no readable-source tokens, only terms
//! already printed and the entry's structure, so the reading depends on what the entry denotes,
//! not on how its source spelled it.
//!
//! An anonymous rest stays `..` on both sides: the subject's `..` matches the rest of the cell
//! and the result's `..` keeps that same rest, which is what a name bound in the subject and
//! written back in the result denotes, so no name is invented for it.

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
}

/// An entry's written contents, by the kind its cell declares.
#[derive(Clone, Debug)]
pub(crate) enum Contents {
    /// A K-sequence cell (`KCell`): its items, front first.
    KSequence(Vec<TokenStream>),
    /// A `Map` cell: its `key -> value` pairs, in written order.
    Map(Vec<(TokenStream, TokenStream)>),
}

/// One cell entry in IR-level form: what it writes and what follows.
#[derive(Clone, Debug)]
pub(crate) struct Entry {
    pub(crate) contents: Contents,
    pub(crate) rest: Rest,
}

/// The entry `field: value` as an author reads it on `side`: `k: KCell(x, ..)`,
/// `env: Cell(map![k -> v, ..])`.
pub(crate) fn print_entry(field: &TokenStream, entry: &Entry, side: Side) -> TokenStream {
    // Both sides spell an anonymous rest alike; `side` is where a named rest will differ.
    let _ = side;
    let rest = match entry.rest {
        Rest::Exact => None,
        Rest::Anonymous => Some(quote!(..)),
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
    };
    quote!(#field: #value)
}

#[cfg(test)]
mod tests {
    use super::{Contents, Entry, Rest, Side, print_entry};
    use quote::quote;

    fn printed(contents: Contents, rest: Rest, side: Side) -> String {
        print_entry(&quote!(k), &Entry { contents, rest }, side).to_string()
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
}
