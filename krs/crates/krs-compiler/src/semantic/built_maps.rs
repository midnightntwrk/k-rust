//! A built whole cell map: an initializer cell's `map![..]`, a `cells!` result's, and a claim's
//! end state's.
//!
//! A built `map![k1 -> v1, .., kn -> vn]` is the collection literal's value: each entry written
//! over the map before it, `map::update(..map::update(base, k1, v1).., kn, vn)`, so the map is
//! total and of two keys that evaluate equal the later one wins. The base is the empty map, a
//! whole map the subject bound (`map![k -> v, ..m]`), or the remainder a framed subject leaves.
//!
//! K's join of the entries, `K1 |-> V1 .. Kn |-> Vn`, is defined exactly when the keys are
//! pairwise distinct, and it is then the same map as the update chain. So the map is emitted as
//! the join wherever that is provable, which keeps the K a reader and a prover expect:
//!
//! - one entry, `K |-> V`, which is `.Map [ K <- V ]` whatever `K` is;
//! - entries whose keys are pairwise provably distinct: ground tokens of one sort with different
//!   values, or keys the subject matched as distinct entries of this map (in a claim, the start
//!   state's map in the same cell).
//!
//! Otherwise two keys may evaluate equal at run time, and the map is emitted as the update chain
//! `.Map [ K1 <- V1 ] .. [ Kn <- Vn ]`, the only term that has the decided value there. Two
//! entries whose keys are provably equal (the same term, or one key the subject matched written
//! twice, as `a` and `(a)`) are one entry with the later value, which is the chain's value too.
//!
//! Over a remainder the subject leaves (`..`, `rest @ ..`), K's cell frame keeps the remainder by
//! joining it with the result's entries, `<env> K |-> V Rest => K |-> W Rest </env>`. That join
//! is the remainder with the entries written over it exactly when no written key is in the
//! remainder, which holds for the keys the subject matched, since the remainder is what its
//! distinct entries leave. A key the subject did not match may already be in the remainder;
//! writing it needs the remainder bound on the left alone (`K |-> V Rest => Rest [ K <- W ]`),
//! which the IR has no frame for (finding NT-9-1), so it is refused at the key.

use krs_ir::{
    Descriptor, ProtocolRuleFrame, ProtocolRuleMapBody, ProtocolRuleStateTerm, ProvenanceKey,
};
use krs_ir_levels::{IrSortRef, IrTermKind, MapEntry, MapOperands, SemanticSortRef, SemanticTerm};

use super::configuration_rules::semantic_terms_equivalent;
use super::error::DescriptorLoweringError;
use super::origin::{key_range, semantic_origin};

/// What a built whole map is written over, as the subject reads the cell.
#[derive(Clone, Debug)]
pub(super) enum MapBase<'a> {
    /// Nothing the subject matched: an initializer, a new instance, or a subject that binds the
    /// cell's whole content.
    Unmatched,
    /// The keys the subject's map matched as distinct entries of the map; `framed` when the
    /// subject leaves a remainder, which the result is written over. `cell` names the cell.
    Matched {
        keys: Vec<&'a SemanticTerm>,
        framed: bool,
        cell: &'a str,
    },
}

impl<'a> MapBase<'a> {
    /// The base of a result written over `subject`, the subject's state of the cell `cell`, which
    /// lowers to `before`.
    pub(super) fn of<T>(
        before: Option<&'a SemanticTerm>,
        subject: Option<&ProtocolRuleStateTerm<T>>,
        cell: &'a str,
    ) -> Self {
        let framed = subject.is_some_and(subject_map_framed);
        match before.map(SemanticTerm::kind) {
            Some(IrTermKind::Map(operands)) => match &**operands {
                MapOperands::Items(entries) => Self::Matched {
                    keys: entries.iter().map(|entry| &entry.key).collect(),
                    framed,
                    cell,
                },
                _ => Self::Unmatched,
            },
            _ => Self::Unmatched,
        }
    }

    /// Whether the subject leaves a remainder the result is written over.
    pub(super) const fn is_framed(&self) -> bool {
        matches!(self, Self::Matched { framed: true, .. })
    }
}

/// One written entry of a built map, with the key of its key's authored text.
pub(super) struct WrittenEntry {
    /// The provenance key of the entry's key, where an error about the key is told.
    pub(super) key_key: ProvenanceKey,
    /// The lowered key and value.
    pub(super) entry: MapEntry<SemanticTerm>,
}

/// A built whole map: its payload, the written entries in order, and a whole map they are
/// written over (`..m`), if any.
pub(super) struct BuiltMap {
    /// The provenance key of the map's payload, which the map's own nodes are anchored at.
    pub(super) payload_key: ProvenanceKey,
    /// The semantic role of the map's node (`rule-map`, `initializer-map`).
    pub(super) role: &'static str,
    /// The written entries, in order.
    pub(super) entries: Vec<WrittenEntry>,
    /// A whole map the entries are written over, `m` of `map![k -> v, ..m]`.
    pub(super) over: Option<SemanticTerm>,
}

/// What a written key is provably equal to: one of the keys the subject matched, a ground token
/// of a sort with its value, or nothing known beyond its term.
enum KeyIdentity<'a> {
    Matched(usize),
    Token(&'a SemanticSortRef, &'a str),
    Term,
}

fn identity<'a>(key: &'a SemanticTerm, base: &MapBase<'_>) -> KeyIdentity<'a> {
    if let MapBase::Matched { keys, .. } = base
        && let Some(index) = keys
            .iter()
            .position(|matched| semantic_terms_equivalent(matched, key))
    {
        return KeyIdentity::Matched(index);
    }
    match key.kind() {
        IrTermKind::Token { value } if has_value_identity(key.sort(), value) => {
            KeyIdentity::Token(key.sort(), value)
        }
        _ => KeyIdentity::Term,
    }
}

/// Whether a token's text is its value, so that two tokens of the sort with different texts are
/// different values: an `Int` (written in decimal by the parser, whatever the source radix), a
/// `Bool`, an `Id`, a `String` or `Bytes` without escapes, and a declared token sort, whose values
/// are its texts. A `Float` is not: `1.0` and `1.00` are one value.
fn has_value_identity(sort: &SemanticSortRef, value: &str) -> bool {
    use krs_ir::BuiltinSort;
    match sort {
        IrSortRef::Builtin(BuiltinSort::Int) => {
            value
                .strip_prefix('-')
                .unwrap_or(value)
                .bytes()
                .all(|digit| digit.is_ascii_digit())
                && value != "-0"
        }
        IrSortRef::Builtin(BuiltinSort::Bool | BuiltinSort::Id) => true,
        IrSortRef::Builtin(BuiltinSort::String | BuiltinSort::Bytes) => !value.contains('\\'),
        IrSortRef::Builtin(_) => false,
        _ => true,
    }
}

/// Whether two written keys are provably one key.
fn same_key(
    left: &KeyIdentity<'_>,
    left_key: &SemanticTerm,
    right: &KeyIdentity<'_>,
    right_key: &SemanticTerm,
) -> bool {
    match (left, right) {
        (KeyIdentity::Matched(left), KeyIdentity::Matched(right)) => left == right,
        (KeyIdentity::Token(left_sort, left), KeyIdentity::Token(right_sort, right)) => {
            left_sort == right_sort && left == right
        }
        _ => semantic_terms_equivalent(left_key, right_key),
    }
}

/// Whether two written keys, not provably one key, are provably different keys: two keys the
/// subject matched as different entries, or two tokens of one sort with different values.
fn distinct_keys(left: &KeyIdentity<'_>, right: &KeyIdentity<'_>) -> bool {
    match (left, right) {
        (KeyIdentity::Matched(left), KeyIdentity::Matched(right)) => left != right,
        (KeyIdentity::Token(left_sort, left), KeyIdentity::Token(right_sort, right)) => {
            left_sort == right_sort && left != right
        }
        _ => false,
    }
}

/// Builds the map `map` denotes over `base`: the join of its entries where the join provably has
/// the update chain's value, the chain otherwise.
///
/// # Errors
///
/// Refuses, at the key, an entry written over a remainder the subject leaves at a key the subject
/// did not match (finding NT-9-1).
pub(super) fn build(
    descriptor: &Descriptor,
    map: BuiltMap,
    base: &MapBase<'_>,
) -> Result<SemanticTerm, DescriptorLoweringError> {
    let identities = map
        .entries
        .iter()
        .map(|written| identity(&written.entry.key, base))
        .collect::<Vec<_>>();
    if base.is_framed()
        && let MapBase::Matched { cell, .. } = *base
        && let Some(index) = identities
            .iter()
            .position(|identity| !matches!(identity, KeyIdentity::Matched(_)))
    {
        return Err(DescriptorLoweringError::invalid_term(
            descriptor.id(),
            format!(
                "the result writes an entry over the map the subject leaves unread (`..` or `rest @ ..`) at a key the subject does not match, and that map may already hold the key: a result's whole `map![..]` writes each entry over the map before it, here that remainder, but K's cell frame only joins the remainder with the result's entries, which has no value where the two share a key, so KRS cannot write it yet; bind the whole map instead, `{cell}: Cell(m)` (inside `Some(..)` for an optional cell), and write `map![k -> v, ..m]`, which writes the entries over `m`"
            ),
        )
        .within(
            descriptor.id(),
            key_range(descriptor, &map.entries[index].key_key).as_ref(),
        ));
    }
    // Of two entries at one key, the later one's value is the map's.
    let kept = (0..map.entries.len())
        .filter(|&index| {
            !(index + 1..map.entries.len()).any(|later| {
                same_key(
                    &identities[index],
                    &map.entries[index].entry.key,
                    &identities[later],
                    &map.entries[later].entry.key,
                )
            })
        })
        .collect::<Vec<_>>();
    let joined = map.over.is_none()
        && kept.iter().enumerate().all(|(position, &left)| {
            kept[position + 1..]
                .iter()
                .all(|&right| distinct_keys(&identities[left], &identities[right]))
        });
    let mut entries = map
        .entries
        .into_iter()
        .enumerate()
        .filter(|(index, _)| kept.contains(index))
        .map(|(_, written)| written.entry)
        .collect::<Vec<_>>();
    if joined {
        let operands = MapOperands::items(entries).map_err(|error| {
            DescriptorLoweringError::invalid_term(descriptor.id(), error.to_string())
        })?;
        return Ok(SemanticTerm::map(
            semantic_origin(descriptor, map.payload_key, map.role)?,
            operands,
        ));
    }
    // Each level of the chain is a node of its own, anchored at the payload under a role of its
    // own, and the outermost is the map's node.
    let last = entries.pop();
    let mut built = match map.over {
        Some(over) => over,
        None => SemanticTerm::map(
            semantic_origin(
                descriptor,
                map.payload_key.clone(),
                &format!("{}-empty", map.role),
            )?,
            MapOperands::Empty,
        ),
    };
    for (level, entry) in entries.into_iter().enumerate() {
        built = SemanticTerm::map(
            semantic_origin(
                descriptor,
                map.payload_key.clone(),
                &format!("{}-update-{level}", map.role),
            )?,
            MapOperands::Update {
                map: built,
                key: entry.key,
                value: entry.value,
            },
        );
    }
    Ok(match last {
        Some(entry) => SemanticTerm::map(
            semantic_origin(descriptor, map.payload_key, map.role)?,
            MapOperands::Update {
                map: built,
                key: entry.key,
                value: entry.value,
            },
        ),
        None => built,
    })
}

/// Whether the subject's state of a cell is a map that leaves a remainder (`..`, `rest @ ..`).
pub(super) fn subject_map_framed<T>(subject: &ProtocolRuleStateTerm<T>) -> bool {
    matches!(
        subject,
        ProtocolRuleStateTerm::Map(map) if matches!(
            &map.body,
            ProtocolRuleMapBody::Items { remainder, .. } if !matches!(remainder, ProtocolRuleFrame::Exact)
        )
    )
}

/// Whether the result writes its whole map over a map the subject bound whole,
/// `map![k -> v, ..m]` over `Cell(m)`: no frame, the map's whole new content.
pub(super) fn writes_over_whole_map<T>(
    subject: &ProtocolRuleStateTerm<T>,
    result: &ProtocolRuleStateTerm<T>,
) -> bool {
    matches!(
        result,
        ProtocolRuleStateTerm::Map(map) if matches!(
            &map.body,
            ProtocolRuleMapBody::Items { remainder: ProtocolRuleFrame::Reuse { .. }, .. }
        )
    ) && !subject_map_framed(subject)
}
