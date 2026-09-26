//! Sorts at mutation sites, as computed by k-rust's sentence typer.

use k_rust::kast::Sort;
use k_rust::kompile::SentenceTyping;

/// The placed sort in every branch where `path` occurs. A missing sort or
/// missing path cannot establish a sort selector's match.
pub(crate) fn site_sorts<'a>(typing: &'a SentenceTyping, path: &[u32]) -> Option<Vec<&'a Sort>> {
    if let Some(position) = typing.positions.get(path) {
        return Some(vec![position.sort.as_ref()?]);
    }
    let branches = typing.branches.get(path)?;
    Some(vec![
        branches.left.sort.as_ref()?,
        branches.right.sort.as_ref()?,
    ])
}
