//! The trace of one execution path, shared with the paths it forked from.
//!
//! A path's trace is the sequence of the rewrite, remainder and simplification entries it went
//! through. Paths fork at every state with several successors, and each successor's trace is
//! its parent's followed by its own entries, so the trace is stored as a persistent list whose
//! nodes point at their predecessor: a fork clones a handle to the newest node, which is
//! constant time whatever the path's depth, and appending one entry adds one node that only the
//! appending path sees. The latest rewrite entry, which the halts that name the rule producing a
//! state read, is cached beside the newest node. A leaf materialises its trace once, in time and
//! memory linear in the entries it returns, moving out the entries no pending fork shares.

use std::rc::Rc;

use super::{TraceEntry, TraceKind};

/// One path's trace: a shared-prefix list of [`TraceEntry`] with its latest rewrite entry.
#[derive(Clone, Default)]
pub(super) struct PathTrace {
    newest: Option<Rc<TraceNode>>,
    /// The newest node whose entry is a [`TraceKind::Rewrite`], when the path has one.
    last_rewrite: Option<Rc<TraceNode>>,
    len: usize,
}

struct TraceNode {
    entry: TraceEntry,
    parent: Option<Rc<TraceNode>>,
}

impl PathTrace {
    /// Append `entry` to this path only; paths sharing the earlier entries do not see it.
    pub(super) fn push(&mut self, entry: TraceEntry) {
        let node = Rc::new(TraceNode {
            entry,
            parent: self.newest.take(),
        });
        if node.entry.kind == TraceKind::Rewrite {
            self.last_rewrite = Some(Rc::clone(&node));
        }
        self.newest = Some(node);
        self.len += 1;
    }

    /// Forget every entry of this path; paths sharing them keep theirs.
    pub(super) fn clear(&mut self) {
        self.newest = None;
        self.last_rewrite = None;
        self.len = 0;
    }

    /// The latest rewrite entry of the path, if it took a rewrite step.
    pub(super) fn last_rewrite(&self) -> Option<&TraceEntry> {
        self.last_rewrite.as_deref().map(|node| &node.entry)
    }

    /// The path's entries, oldest first, leaving the path as it is.
    #[cfg(test)]
    pub(super) fn to_vec(&self) -> Vec<TraceEntry> {
        let mut entries = Vec::with_capacity(self.len);
        let mut node = self.newest.as_deref();
        while let Some(current) = node {
            entries.push(current.entry.clone());
            node = current.parent.as_deref();
        }
        entries.reverse();
        entries
    }

    /// The path's entries, oldest first, for the leaf that ends the path: an entry no other
    /// path shares is moved out, and only the entries shared with a pending fork are cloned, so
    /// a path that never forked returns its trace without holding a second copy of it.
    pub(super) fn into_vec(mut self) -> Vec<TraceEntry> {
        let mut entries = Vec::with_capacity(self.len);
        // The cache is a second handle on a node of the chain; without it, a node this path
        // holds alone has one owner and can be taken apart.
        self.last_rewrite = None;
        let mut node = self.newest.take();
        while let Some(current) = node {
            match Rc::try_unwrap(current) {
                Ok(mut owned) => {
                    entries.push(std::mem::replace(
                        &mut owned.entry,
                        TraceEntry {
                            depth: 0,
                            kind: TraceKind::Rewrite,
                            label: None,
                            unique_id: String::new(),
                        },
                    ));
                    node = owned.parent.take();
                }
                Err(shared) => {
                    let mut ancestor = Some(&*shared);
                    while let Some(current) = ancestor {
                        entries.push(current.entry.clone());
                        ancestor = current.parent.as_deref();
                    }
                    break;
                }
            }
        }
        entries.reverse();
        entries
    }

    /// The address of each entry's `unique_id` text, oldest first, read in place: a moved entry
    /// keeps its text's buffer and a cloned one does not.
    #[cfg(test)]
    pub(super) fn unique_id_buffers(&self) -> Vec<*const u8> {
        let mut buffers =
            std::iter::successors(self.newest.as_deref(), |node| node.parent.as_deref())
                .map(|node| node.entry.unique_id.as_ptr())
                .collect::<Vec<_>>();
        buffers.reverse();
        buffers
    }

    /// Whether `self` and `other` hold the same newest node, so that every entry of one is an
    /// entry of the other, stored once.
    #[cfg(test)]
    pub(super) fn shares_entries_with(&self, other: &Self) -> bool {
        match (&self.newest, &other.newest) {
            (Some(left), Some(right)) => Rc::ptr_eq(left, right),
            (None, None) => true,
            _ => false,
        }
    }
}

impl Extend<TraceEntry> for PathTrace {
    fn extend<I: IntoIterator<Item = TraceEntry>>(&mut self, entries: I) {
        for entry in entries {
            self.push(entry);
        }
    }
}

impl Drop for TraceNode {
    /// Unlink a long unshared chain iteratively rather than by recursive drops.
    fn drop(&mut self) {
        let mut parent = self.parent.take();
        while let Some(node) = parent {
            match Rc::try_unwrap(node) {
                Ok(mut node) => parent = node.parent.take(),
                Err(_) => break,
            }
        }
    }
}
