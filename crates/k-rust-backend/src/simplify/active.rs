//! The rule conditions being decided around a simplification, against re-entry
//! ([`ActiveConditions`]).

use std::{
    hash::{BuildHasher, Hash, Hasher},
    sync::Arc,
};

use rustc_hash::{FxBuildHasher, FxHashSet};

use super::ConditionKey;

/// The set of rule-condition keys whose conditions are being decided around a simplification
/// (`simplify_rule_predicates`), each the rule and the term it is evaluated for.
///
/// A recursion through an equation's `requires` decides one condition per level, under the
/// keys of every level around it, and each level's set is the one around it with its own key
/// added. The sets of all the levels are live at once, so a set that copied the one around it
/// would hold, over a recursion of depth `d`, `d(d + 1)/2` keys in all; the set is instead a
/// persistent list, whose added key shares the set around it: one node per level, `d` in all.
///
/// A set never holds a key twice: [`ActiveConditions::with`] is given only a key it does not
/// hold, since an active key's condition is not decided again. Equality is of sets, regardless of
/// the order the keys were added in, and the hash is the wrapping sum of the keys' hashes, which
/// does not depend on it either; both are kept in the node, so hashing a set reads no key.
#[derive(Clone, Default)]
pub(crate) struct ActiveConditions(Option<Arc<Node>>);

struct Node {
    key: ConditionKey,
    /// The hash of `key` ([`key_hash`]).
    key_hash: u64,
    /// The wrapping sum of the hashes of every key of the set this node heads.
    set_hash: u64,
    /// The number of keys of the set this node heads.
    len: usize,
    rest: ActiveConditions,
}

/// The hash of a rule-condition key; a term's hash is cached, so it reads no term node.
fn key_hash(key: &ConditionKey) -> u64 {
    FxBuildHasher.hash_one(key)
}

impl ActiveConditions {
    /// The empty set.
    pub(crate) fn new() -> Self {
        Self(None)
    }

    pub(crate) fn len(&self) -> usize {
        self.0.as_ref().map_or(0, |node| node.len)
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_none()
    }

    fn set_hash(&self) -> u64 {
        self.0.as_ref().map_or(0, |node| node.set_hash)
    }

    /// The set with `key` added, sharing this one. `key` is not in it.
    pub(crate) fn with(&self, key: ConditionKey) -> Self {
        debug_assert!(!self.contains(&key), "an active key is added again");
        let key_hash = key_hash(&key);
        #[cfg(test)]
        LIVE_NODES.with(|live| {
            live.set(live.get() + 1);
            PEAK_NODES.set(PEAK_NODES.get().max(live.get()));
        });
        Self(Some(Arc::new(Node {
            key,
            key_hash,
            set_hash: self.set_hash().wrapping_add(key_hash),
            len: self.len() + 1,
            rest: self.clone(),
        })))
    }

    pub(crate) fn contains(&self, key: &ConditionKey) -> bool {
        let hash = key_hash(key);
        self.nodes()
            .any(|node| node.key_hash == hash && node.key == *key)
    }

    /// The keys, the last added first.
    pub(crate) fn iter(&self) -> impl Iterator<Item = &ConditionKey> {
        self.nodes().map(|node| &node.key)
    }

    fn nodes(&self) -> impl Iterator<Item = &Node> {
        std::iter::successors(self.0.as_deref(), |node| node.rest.0.as_deref())
    }

    /// The address of the set's first node, 0 for the empty set: two sets with the same address
    /// are the same set.
    pub(crate) fn address(&self) -> usize {
        self.0
            .as_ref()
            .map_or(0, |node| Arc::as_ptr(node).cast::<()>().addr())
    }

    /// The bytes a table that holds a handle on this set (`InternTable`) counts for it: the
    /// handle twice, and every node of the set with its rule id. The nodes past the first are
    /// shared with the sets this one extends, which the table may hold as well, but a handle
    /// keeps all of them alive once the run around has dropped them, so the count bounds what the
    /// table holds.
    pub(crate) fn retained_bytes(&self) -> usize {
        2 * std::mem::size_of::<Arc<Self>>()
            + self
                .nodes()
                .map(|node| std::mem::size_of::<Node>() + node.key.0.capacity())
                .sum::<usize>()
    }

    /// Whether every key of this set is in `other`.
    ///
    /// Two sets share the nodes from the first one both reach on: the set that both extend, or
    /// the empty set. The sets' lengths fall by one per node, so stepping the longer one to the
    /// other's length and then both together finds it, O(a). Neither set repeats a key, so this
    /// set's keys in the shared part are none of those above it, which are in `other` only above
    /// the shared part too. Those few are compared pairwise by their hashes; where both parts
    /// are long, `other`'s are hashed once.
    pub(crate) fn is_subset(&self, other: &Self) -> bool {
        if self.len() > other.len() {
            return false;
        }
        let shared = self.shared_with(other);
        let own = || self.nodes().take_while(move |node| node.len > shared);
        let others = || other.nodes().take_while(move |node| node.len > shared);
        let (own_count, other_count) = (self.len() - shared, other.len() - shared);
        if own_count.saturating_mul(other_count) <= PAIRWISE {
            own().all(|node| {
                others().any(|held| held.key_hash == node.key_hash && held.key == node.key)
            })
        } else {
            let held = others().map(|node| &node.key).collect::<FxHashSet<_>>();
            own().all(|node| held.contains(&node.key))
        }
    }

    /// The length of the set this one and `other` both extend, or are.
    fn shared_with(&self, other: &Self) -> usize {
        let (mut longer, mut shorter) = if self.len() >= other.len() {
            (self.0.as_deref(), other.0.as_deref())
        } else {
            (other.0.as_deref(), self.0.as_deref())
        };
        let len = |node: Option<&Node>| node.map_or(0, |node| node.len);
        while len(longer) > len(shorter) {
            longer = longer.and_then(|node| node.rest.0.as_deref());
        }
        while let (Some(left), Some(right)) = (longer, shorter) {
            if std::ptr::eq(left, right) {
                break;
            }
            longer = left.rest.0.as_deref();
            shorter = right.rest.0.as_deref();
        }
        len(longer)
    }
}

/// The most pairs of keys [`ActiveConditions::is_subset`] compares one by one before it hashes.
const PAIRWISE: usize = 1024;

impl PartialEq for ActiveConditions {
    fn eq(&self, other: &Self) -> bool {
        // Neither set repeats a key, so a subset as large as the other set is that set.
        self.len() == other.len() && self.set_hash() == other.set_hash() && self.is_subset(other)
    }
}

impl Eq for ActiveConditions {}

impl Hash for ActiveConditions {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_usize(self.len());
        state.write_u64(self.set_hash());
    }
}

impl Drop for Node {
    /// The nodes of a set no other set shares are dropped one after another, not by a recursion
    /// as deep as the set.
    fn drop(&mut self) {
        #[cfg(test)]
        LIVE_NODES.with(|live| live.set(live.get() - 1));
        let mut rest = self.rest.0.take();
        while let Some(node) = rest {
            match Arc::try_unwrap(node) {
                Ok(mut node) => rest = node.rest.0.take(),
                Err(_) => break,
            }
        }
    }
}

impl std::fmt::Debug for ActiveConditions {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.debug_set().entries(self.iter()).finish()
    }
}

#[cfg(test)]
thread_local! {
    /// The nodes alive on this thread, and the most alive at once since [`peak_nodes`] began.
    static LIVE_NODES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static PEAK_NODES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// `action`'s result, and the most nodes of active-condition sets made on this thread that were
/// alive at once while it ran, beyond those alive when it began.
#[cfg(test)]
pub(crate) fn peak_nodes<T>(action: impl FnOnce() -> T) -> (T, usize) {
    let before = LIVE_NODES.get();
    PEAK_NODES.set(before);
    let result = action();
    (result, PEAK_NODES.get() - before)
}

#[cfg(test)]
mod tests {
    use super::{ActiveConditions, peak_nodes};
    use crate::term::{Sort, Term, Variable};

    fn key(rule: &str) -> (String, Term) {
        (
            rule.to_owned(),
            Term::variable(Variable::new("X", Sort::simple("SortInt"))),
        )
    }

    fn hash(set: &ActiveConditions) -> u64 {
        std::hash::BuildHasher::hash_one(&rustc_hash::FxBuildHasher, set)
    }

    #[test]
    fn a_set_is_its_keys_whatever_the_order_they_were_added_in() {
        let empty = ActiveConditions::new();
        let ab = empty.with(key("a")).with(key("b"));
        let ba = empty.with(key("b")).with(key("a"));
        assert!(ab.contains(&key("a")) && ab.contains(&key("b")));
        assert!(!ab.contains(&key("c")) && !empty.contains(&key("a")));
        assert_eq!(ab.len(), 2);
        assert_eq!(ab, ba);
        assert_eq!(hash(&ab), hash(&ba));
        assert_ne!(ab, empty.with(key("a")).with(key("c")));
        assert_ne!(ab, empty.with(key("a")));
        assert_eq!(ActiveConditions::new(), empty);
        assert_eq!(hash(&ActiveConditions::new()), hash(&empty));
    }

    #[test]
    fn a_set_is_a_subset_of_every_set_that_extends_it_and_of_no_set_missing_a_key() {
        let a = ActiveConditions::new().with(key("a"));
        let ab = a.with(key("b"));
        let abc = ab.with(key("c"));
        assert!(ActiveConditions::new().is_subset(&a));
        assert!(a.is_subset(&abc) && ab.is_subset(&abc) && abc.is_subset(&abc));
        assert!(!abc.is_subset(&ab));
        // Not by a shared node: the same keys, added in another order.
        let cba = ActiveConditions::new()
            .with(key("c"))
            .with(key("b"))
            .with(key("a"));
        assert!(ab.is_subset(&cba) && abc.is_subset(&cba) && cba.is_subset(&abc));
        assert!(!ab.is_subset(&ActiveConditions::new().with(key("b")).with(key("c"))));
    }

    /// Each set added to one shares it: a chain of `n` sets, every one alive, holds `n` nodes,
    /// not the `n(n + 1)/2` keys of `n` copies; dropping it takes no recursion as deep as it,
    /// which on a thread of 256 KiB would run out of stack.
    #[test]
    fn a_chain_of_sets_holds_one_node_per_set_and_drops_without_recursion() {
        let levels = 20_000;
        let peak = std::thread::Builder::new()
            .stack_size(256 << 10)
            .spawn(move || {
                let ((), peak) = peak_nodes(|| {
                    let mut sets = vec![ActiveConditions::new()];
                    for level in 0..levels {
                        let next = sets[level].with(key(&level.to_string()));
                        sets.push(next);
                    }
                    assert_eq!(sets[levels].len(), levels);
                });
                peak
            })
            .expect("the thread starts")
            .join()
            .expect("the chain drops");
        assert_eq!(peak, levels);
    }
}
