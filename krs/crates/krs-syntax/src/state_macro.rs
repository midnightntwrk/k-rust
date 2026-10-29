use std::collections::BTreeSet;

use proc_macro2::{Delimiter, Span, TokenStream, TokenTree};
use quote::quote;
use syn::parse::ParseStream;
use syn::spanned::Spanned;
use syn::{Ident, Path, Token, parenthesized};

use crate::parse::{KeyAllocator, KrsSyntax, structured_with};
use crate::path::{path_text, plain_path_last};
use crate::{
    ProvenanceAnchor, ProvenanceRole, RuleRole, RuleSide, SyntaxError, SyntaxErrorKind,
    TermExpression, TermTree, TokenRange,
};
use krs_ir::ProvenanceKey;

/// Where a state macro stands in its sentence, which decides the roles of its
/// nodes: alone, under the standalone `cells_*`, `k_sequence_*` and `map_*`
/// roles, or on one side of a rule, under that side's roles.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum StatePosition {
    /// The state macro is its own sentence.
    Standalone,
    /// The state macro is one side's cells, or a state inside them.
    Rule(RuleSide),
}

impl StatePosition {
    /// The role of a node in `slot` at this position.
    pub(crate) const fn role(self, slot: RuleRole) -> ProvenanceRole {
        match self {
            Self::Standalone => match slot {
                RuleRole::CellsPayload => ProvenanceRole::CellsPayload,
                RuleRole::CellsField => ProvenanceRole::CellsField,
                RuleRole::CellsWrapper => ProvenanceRole::CellsWrapper,
                RuleRole::CellsRemainder => ProvenanceRole::CellsRemainder,
                RuleRole::KSequencePayload => ProvenanceRole::KSequencePayload,
                RuleRole::KSequenceItem => ProvenanceRole::KSequenceItem,
                RuleRole::KSequenceTail => ProvenanceRole::KSequenceTail,
                RuleRole::MapPayload => ProvenanceRole::MapPayload,
                RuleRole::MapKey => ProvenanceRole::MapKey,
                RuleRole::MapValue => ProvenanceRole::MapValue,
                RuleRole::MapRemainder => ProvenanceRole::MapRemainder,
                RuleRole::MapUpdateBase => ProvenanceRole::MapUpdateBase,
                RuleRole::CellsInstance => ProvenanceRole::CellsInstance,
                RuleRole::CellsInstanceField => ProvenanceRole::CellsInstanceField,
                RuleRole::CellsInstancesRest => ProvenanceRole::CellsInstancesRest,
            },
            Self::Rule(side) => slot.on_side(side),
        }
    }
}

/// Hands out the next key of `slot`'s role at `position` to the node at
/// `range`.
fn key_at(
    keys: &mut KeyAllocator,
    position: StatePosition,
    slot: RuleRole,
    range: TokenRange,
) -> Result<ProvenanceKey, SyntaxError> {
    keys.key(position.role(slot), range)
}

/// Where a shell's payload key is anchored: at the payload, or, when the
/// payload is empty, at the invocation that delimits it, since the empty
/// shell's text is its invocation. An empty payload read without its
/// invocation has nowhere to anchor.
fn payload_range(
    tokens: &TokenStream,
    invocation: Option<TokenRange>,
) -> Result<Option<TokenRange>, SyntaxError> {
    if tokens.is_empty() {
        Ok(invocation)
    } else {
        TokenRange::for_tokens(tokens).map(Some)
    }
}

/// Whether a compiler-owned state island occurs in pattern or expression position.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StateMacroContext {
    /// Bindings use `name @ ..` and expression-style spread is rejected.
    Pattern,
    /// Reuse uses `..name` and pattern-style binding is rejected.
    Expression,
}

/// Exact, anonymous, bound-pattern, or reused-expression associative tail.
#[derive(Clone, Debug)]
pub enum StateMacroRemainder {
    /// No content is omitted.
    Exact,
    /// Anonymous pattern remainder (`..`).
    Anonymous(TokenRange),
    /// Pattern remainder binding (`name @ ..`).
    Bind {
        /// Introduced pattern binding.
        binding: Ident,
        /// Complete `binding @ ..` range.
        range: TokenRange,
    },
    /// Expression remainder reuse (`..name`).
    Reuse {
        /// Previously introduced frame binding.
        binding: Ident,
        /// Complete `..binding` range.
        range: TokenRange,
    },
}

impl StateMacroRemainder {
    /// Returns the optional binding name.
    #[must_use]
    pub const fn binding(&self) -> Option<&Ident> {
        match self {
            Self::Bind { binding, .. } | Self::Reuse { binding, .. } => Some(binding),
            Self::Exact | Self::Anonymous(_) => None,
        }
    }

    /// Returns the authored range of a non-exact remainder.
    #[must_use]
    pub fn range(&self) -> Option<TokenRange> {
        match self {
            Self::Exact => None,
            Self::Anonymous(range) | Self::Bind { range, .. } | Self::Reuse { range, .. } => {
                Some(*range)
            }
        }
    }
}

/// Surface notation used for an exact K sequence.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum KSequenceNotation {
    /// Comma-delimited host notation.
    Comma,
    /// K's authored `~>` connective.
    Operator,
    /// Explicit empty `.K`.
    DotK,
}

/// Parsed `k!` payload with an ordered prefix and explicit associative tail.
#[derive(Clone, Debug)]
pub struct KSequence {
    tokens: TokenStream,
    items: Vec<TermExpression>,
    tail: StateMacroRemainder,
    notation: KSequenceNotation,
    /// The delimited text that holds the payload (the `k::k![..]`
    /// invocation, `KCell(..)`'s parentheses, a readable `[..]`), when the
    /// parser of an enclosing form read it.
    invocation: Option<TokenRange>,
    payload_key: Option<ProvenanceKey>,
    tail_key: Option<ProvenanceKey>,
    /// The anchors of the sequence's standalone keying.
    anchors: Vec<ProvenanceAnchor>,
}

impl KSequence {
    /// A readable `[items.., ..]` sequence (KF-023): `tokens` is the bracket
    /// payload and `tail` is exact or anonymous.
    ///
    /// # Errors
    ///
    /// Returns an endpoint or ordinal-overflow error of its standalone keying.
    pub(crate) fn readable(
        brackets: &proc_macro2::Group,
        items: Vec<TermExpression>,
        tail: StateMacroRemainder,
    ) -> Result<Self, SyntaxError> {
        Self::new(brackets.stream(), items, tail, KSequenceNotation::Comma)
            .invoked_at(Some(TokenRange::for_tokens(brackets)?))
            .keyed_standalone()
    }

    const fn new(
        tokens: TokenStream,
        items: Vec<TermExpression>,
        tail: StateMacroRemainder,
        notation: KSequenceNotation,
    ) -> Self {
        Self {
            tokens,
            items,
            tail,
            notation,
            invocation: None,
            payload_key: None,
            tail_key: None,
            anchors: Vec::new(),
        }
    }

    /// Records the delimited text that holds the payload, where the empty
    /// sequence is anchored.
    const fn invoked_at(mut self, invocation: Option<TokenRange>) -> Self {
        self.invocation = invocation;
        self
    }

    /// Ordered K items before the tail.
    #[must_use]
    pub fn items(&self) -> &[TermExpression] {
        &self.items
    }

    /// Ordered K items before the tail, for a pass that keys them.
    pub(crate) fn items_mut(&mut self) -> &mut [TermExpression] {
        &mut self.items
    }

    /// Exact or framed sequence tail.
    #[must_use]
    pub const fn tail(&self) -> &StateMacroRemainder {
        &self.tail
    }

    /// Authored comma/operator/`.K` notation.
    #[must_use]
    pub const fn notation(&self) -> KSequenceNotation {
        self.notation
    }

    /// Whether the sequence denotes exact `.K` (explicitly or as `k![]`).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.items.is_empty() && matches!(self.tail, StateMacroRemainder::Exact)
    }

    /// The key of the payload, anchored at the payload, or at the
    /// invocation when the payload is empty (`k::k![]`); absent only for an
    /// empty sequence parsed without its invocation. An item's key is the
    /// payload key of its term ([`crate::TermKeys::payload`]).
    #[must_use]
    pub const fn payload_key(&self) -> Option<&ProvenanceKey> {
        self.payload_key.as_ref()
    }

    /// The key of the tail: the remainder, or the authored `.K`.
    #[must_use]
    pub const fn tail_key(&self) -> Option<&ProvenanceKey> {
        self.tail_key.as_ref()
    }

    /// Returns payload, item, and tail anchors of the sequence's standalone
    /// keying.
    ///
    /// # Errors
    ///
    /// None: the sequence was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    fn keyed_standalone(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        self.clear_keys();
        self.allocate_keys(&mut keys, StatePosition::Standalone)?;
        self.anchors = keys.into_anchors();
        Ok(self)
    }

    /// Forgets the keys of the sequence and of its items, and the anchors
    /// of its standalone keying, before an enclosing sentence's pass keys
    /// them.
    pub(crate) fn clear_keys(&mut self) {
        self.payload_key = None;
        self.tail_key = None;
        self.anchors.clear();
        for item in &mut self.items {
            item.clear_keys();
        }
    }

    /// Keys the payload, each item (as its term's payload), then the tail,
    /// under the roles of `position`. The items' own nodes are the enclosing
    /// sentence's to key.
    pub(crate) fn allocate_keys(
        &mut self,
        keys: &mut KeyAllocator,
        position: StatePosition,
    ) -> Result<(), SyntaxError> {
        if let Some(range) = payload_range(&self.tokens, self.invocation)? {
            self.payload_key = Some(key_at(keys, position, RuleRole::KSequencePayload, range)?);
        }
        for item in &mut self.items {
            item.allocate_payload_key(keys, position.role(RuleRole::KSequenceItem))?;
        }
        let tail = match self.tail.range() {
            Some(range) => Some(range),
            None if self.notation == KSequenceNotation::DotK => {
                Some(TokenRange::for_tokens(&self.tokens)?)
            }
            None => None,
        };
        if let Some(range) = tail {
            self.tail_key = Some(key_at(keys, position, RuleRole::KSequenceTail, range)?);
        }
        Ok(())
    }
}

/// One associative map item.
#[derive(Clone, Debug)]
pub struct MapItem {
    key: TermExpression,
    value: TermExpression,
}

impl MapItem {
    /// Returns the authored key term.
    #[must_use]
    pub const fn key(&self) -> &TermExpression {
        &self.key
    }

    /// Returns the authored value term.
    #[must_use]
    pub const fn value(&self) -> &TermExpression {
        &self.value
    }
}

/// Empty, associative-item, or functional-update `map!` payload.
#[derive(Clone, Debug)]
#[expect(
    clippy::large_enum_variant,
    reason = "Span-preserving term nodes are the public parser contract."
)]
pub enum MapBody {
    /// Empty `.Map` unit (also represented by `map![]`).
    Empty {
        /// Whether `.Map` was authored instead of an empty payload.
        explicit_dot: bool,
    },
    /// Ordered authored items plus an exact or associative remainder.
    Items {
        /// Key/value items.
        items: Vec<MapItem>,
        /// Exact or framed map remainder.
        remainder: StateMacroRemainder,
    },
    /// Functional update of a base map at one key.
    Update {
        /// Existing map term.
        base: TermExpression,
        /// Updated key.
        key: TermExpression,
        /// Replacement value.
        value: TermExpression,
    },
}

#[derive(Clone, Debug, Default)]
pub(crate) struct MapPatternBindings {
    pub(crate) terms: Vec<Ident>,
    pub(crate) frame: Option<Ident>,
}

impl MapPatternBindings {
    fn from_items(items: &[MapItem], remainder: &StateMacroRemainder) -> Self {
        // Only the left image binds (KF-011).
        let terms = items
            .iter()
            .flat_map(|item| [item.key(), item.value()])
            .flat_map(|term| crate::term::pattern_tree_binders(term.tree(), false))
            .collect();
        let frame = match remainder {
            StateMacroRemainder::Bind { binding, .. } => Some(binding.clone()),
            _ => None,
        };
        Self { terms, frame }
    }
}

/// Parsed `map!` payload.
#[derive(Clone, Debug)]
pub struct MapExpression {
    tokens: TokenStream,
    body: MapBody,
    pattern_bindings: Option<MapPatternBindings>,
    /// The delimited text that holds the payload (`k::map![..]`), when the
    /// parser of an enclosing form read it.
    invocation: Option<TokenRange>,
    /// The macro's path as written (`map`, `k::map`), when the map is a
    /// cell's own content, an island the enclosing macro consumes.
    island: Option<Path>,
    payload_key: Option<ProvenanceKey>,
    remainder_key: Option<ProvenanceKey>,
    /// The anchors of the map's standalone keying.
    anchors: Vec<ProvenanceAnchor>,
}

impl MapExpression {
    /// Returns the tokens the expression was parsed from.
    #[must_use]
    pub const fn tokens(&self) -> &TokenStream {
        &self.tokens
    }

    fn empty(tokens: TokenStream, explicit_dot: bool, context: StateMacroContext) -> Self {
        Self::new(
            tokens,
            MapBody::Empty { explicit_dot },
            (context == StateMacroContext::Pattern).then(MapPatternBindings::default),
        )
    }

    const fn new(
        tokens: TokenStream,
        body: MapBody,
        pattern_bindings: Option<MapPatternBindings>,
    ) -> Self {
        Self {
            tokens,
            body,
            pattern_bindings,
            invocation: None,
            island: None,
            payload_key: None,
            remainder_key: None,
            anchors: Vec::new(),
        }
    }

    /// Records the delimited text that holds the payload, where the empty
    /// map is anchored.
    const fn invoked_at(mut self, invocation: Option<TokenRange>) -> Self {
        self.invocation = invocation;
        self
    }

    /// Records the path of the macro that writes a cell's own map.
    pub(crate) fn island_of(mut self, path: Option<Path>) -> Self {
        self.island = path;
        self
    }

    /// The path of the macro (`map`, `k::map`) that writes the map as a
    /// cell's own content, which the enclosing macro consumes before rustc
    /// sees it; `None` for a map no cell's macro wrote.
    #[must_use]
    pub const fn island_path(&self) -> Option<&Path> {
        self.island.as_ref()
    }

    fn items(
        tokens: TokenStream,
        items: Vec<MapItem>,
        remainder: StateMacroRemainder,
        context: StateMacroContext,
    ) -> Self {
        let pattern_bindings = (context == StateMacroContext::Pattern)
            .then(|| MapPatternBindings::from_items(&items, &remainder));
        Self::new(
            tokens,
            MapBody::Items { items, remainder },
            pattern_bindings,
        )
    }

    pub(crate) const fn pattern_bindings(&self) -> Option<&MapPatternBindings> {
        self.pattern_bindings.as_ref()
    }

    /// Returns the classified map operation.
    #[must_use]
    pub const fn body(&self) -> &MapBody {
        &self.body
    }

    /// The key of the payload, anchored at the payload, or at the
    /// invocation when the payload is empty (`k::map![]`); absent only for
    /// an empty map parsed without its invocation. An item's key and value,
    /// and an update's base, key and value, are keyed as their terms'
    /// payloads ([`crate::TermKeys::payload`]).
    #[must_use]
    pub const fn payload_key(&self) -> Option<&ProvenanceKey> {
        self.payload_key.as_ref()
    }

    /// The key of the items' remainder.
    #[must_use]
    pub const fn remainder_key(&self) -> Option<&ProvenanceKey> {
        self.remainder_key.as_ref()
    }

    /// Returns payload and structural map anchors of the map's standalone
    /// keying.
    ///
    /// # Errors
    ///
    /// None: the map was keyed when it was parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    fn keyed_standalone(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        self.clear_keys();
        self.allocate_keys(&mut keys, StatePosition::Standalone)?;
        self.anchors = keys.into_anchors();
        Ok(self)
    }

    /// The map's terms in key order: each item's key and value, or an
    /// update's base, key and value.
    pub(crate) fn terms_mut(&mut self) -> Vec<&mut TermExpression> {
        match &mut self.body {
            MapBody::Empty { .. } => Vec::new(),
            MapBody::Items { items, .. } => items
                .iter_mut()
                .flat_map(|item| [&mut item.key, &mut item.value])
                .collect(),
            MapBody::Update { base, key, value } => vec![base, key, value],
        }
    }

    /// Forgets the keys of the map and of its terms, and the anchors of its
    /// standalone keying, before an enclosing sentence's pass keys them.
    pub(crate) fn clear_keys(&mut self) {
        self.payload_key = None;
        self.remainder_key = None;
        self.anchors.clear();
        for term in self.terms_mut() {
            term.clear_keys();
        }
    }

    /// Keys the payload, then each item's key and value and the remainder, or
    /// an update's base, key and value, under the roles of `position`. The
    /// terms' own nodes are the enclosing sentence's to key.
    pub(crate) fn allocate_keys(
        &mut self,
        keys: &mut KeyAllocator,
        position: StatePosition,
    ) -> Result<(), SyntaxError> {
        if let Some(range) = payload_range(&self.tokens, self.invocation)? {
            self.payload_key = Some(key_at(keys, position, RuleRole::MapPayload, range)?);
        }
        let key_role = position.role(RuleRole::MapKey);
        let value_role = position.role(RuleRole::MapValue);
        match &mut self.body {
            MapBody::Empty { .. } => {}
            MapBody::Items { items, remainder } => {
                for item in items {
                    item.key.allocate_payload_key(keys, key_role)?;
                    item.value.allocate_payload_key(keys, value_role)?;
                }
                if let Some(range) = remainder.range() {
                    self.remainder_key =
                        Some(key_at(keys, position, RuleRole::MapRemainder, range)?);
                }
            }
            MapBody::Update { base, key, value } => {
                base.allocate_payload_key(keys, position.role(RuleRole::MapUpdateBase))?;
                key.allocate_payload_key(keys, key_role)?;
                value.allocate_payload_key(keys, value_role)?;
            }
        }
        Ok(())
    }
}

/// Term families admitted as fixed leaf-cell contents.
#[derive(Clone, Debug)]
#[expect(
    clippy::large_enum_variant,
    reason = "Avoid hiding parser AST ownership behind allocation."
)]
pub enum StateTerm {
    /// Ordinary named term.
    Term(TermExpression),
    /// Compiler-parsed K sequence.
    KSequence(KSequence),
    /// Compiler-parsed map operation.
    Map(MapExpression),
    /// A whole nested (group) cell written without a wrapper: a group
    /// binder, `_`, or a complete `k::fragment!` term (KF-016).
    Group(TermExpression),
    /// `Some(..)` of an optional (`?`) cell: the present cell's state; a
    /// leaf's `Cell(..)` wrapper is the entry's wrapper (KF-023, R7).
    Present(Box<StateTerm>),
    /// `None` of an optional (`?`) cell: the cell is absent (KF-023).
    Absent(TokenRange),
    /// The instances of a collection (`*`) cell (KF-023, R8).
    Instances(InstanceList),
}

impl StateTerm {
    /// The state inside any `Some(..)` wrappers.
    #[must_use]
    pub fn unwrap_present(&self) -> &Self {
        match self {
            Self::Present(inner) => inner.unwrap_present(),
            other => other,
        }
    }

    /// Every term of the state in traversal order: a term or group, the
    /// items of `k!`, the keys and values of `map!`, and the terms nested in
    /// `Some(..)` and collection instances.
    #[must_use]
    pub fn terms(&self) -> Vec<&TermExpression> {
        match self {
            Self::Term(term) | Self::Group(term) => vec![term],
            Self::KSequence(sequence) => sequence.items().iter().collect(),
            Self::Map(map) => match map.body() {
                MapBody::Empty { .. } => Vec::new(),
                MapBody::Items { items, .. } => items
                    .iter()
                    .flat_map(|item| [item.key(), item.value()])
                    .collect(),
                MapBody::Update { base, key, value } => vec![base, key, value],
            },
            Self::Present(_) | Self::Absent(_) | Self::Instances(_) => self
                .nested_states()
                .into_iter()
                .flat_map(Self::terms)
                .collect(),
        }
    }

    /// Every term of the state, mutably, in [`Self::terms`] order.
    pub(crate) fn terms_mut(&mut self) -> Vec<&mut TermExpression> {
        match self {
            Self::Term(term) | Self::Group(term) => vec![term],
            Self::KSequence(sequence) => sequence.items.iter_mut().collect(),
            Self::Map(map) => map.terms_mut(),
            Self::Present(inner) => inner.terms_mut(),
            Self::Absent(_) => Vec::new(),
            Self::Instances(list) => list
                .nested_states_mut()
                .into_iter()
                .flat_map(Self::terms_mut)
                .collect(),
        }
    }

    /// Forgets the keys of the state and of everything inside it, before an
    /// enclosing sentence's pass keys them.
    pub(crate) fn clear_keys(&mut self) {
        match self {
            Self::Term(term) | Self::Group(term) => term.clear_keys(),
            Self::KSequence(sequence) => sequence.clear_keys(),
            Self::Map(map) => map.clear_keys(),
            Self::Present(inner) => inner.clear_keys(),
            Self::Absent(_) => {}
            Self::Instances(list) => list.clear_keys(),
        }
    }

    /// The paths of the `map!` islands that write this state's maps, its
    /// nested states' included, in source order ([`MapExpression::island_path`]).
    #[must_use]
    pub fn map_islands(&self) -> Vec<&Path> {
        match self {
            Self::Map(map) => map.island_path().into_iter().collect(),
            Self::Present(_) | Self::Instances(_) => self
                .nested_states()
                .into_iter()
                .flat_map(Self::map_islands)
                .collect(),
            Self::Term(_) | Self::KSequence(_) | Self::Group(_) | Self::Absent(_) => Vec::new(),
        }
    }

    /// Every directly nested state: the inside of `Some(..)` and the
    /// children of collection instances, in source order.
    #[must_use]
    pub fn nested_states(&self) -> Vec<&Self> {
        match self {
            Self::Present(inner) => vec![inner],
            Self::Instances(list) => list
                .instances()
                .flat_map(|instance| instance.fields().iter().map(InstanceField::value))
                .collect(),
            Self::Term(_)
            | Self::KSequence(_)
            | Self::Map(_)
            | Self::Group(_)
            | Self::Absent(_) => Vec::new(),
        }
    }
}

/// The delimiter of a collection entry (KF-023, R8).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InstanceListDelimiter {
    /// `{ .. }`: some instances of a Set or Map collection.
    Brace,
    /// `[ .. ]`: the ends of a List collection.
    Bracket,
}

/// The rest of one collection instance record.
#[derive(Clone, Debug)]
pub enum InstanceRest {
    /// No rest: the record names every child.
    Exact,
    /// `..`: unconstrained children (pattern) or template defaults (result).
    Open(TokenRange),
    /// `..label` in a result: the matched instance `label`, updated.
    Update {
        /// The pattern instance label.
        label: Ident,
        /// Complete `..label` range.
        range: TokenRange,
    },
}

/// One named child of a collection instance record.
#[derive(Clone, Debug)]
pub struct InstanceField {
    name: Ident,
    value: StateTerm,
    name_key: Option<ProvenanceKey>,
}

impl InstanceField {
    pub(crate) const fn new(name: Ident, value: StateTerm) -> Self {
        Self {
            name,
            value,
            name_key: None,
        }
    }

    /// The key of the child's field name, given by the rule side that
    /// anchors the collection.
    #[must_use]
    pub const fn name_key(&self) -> Option<&ProvenanceKey> {
        self.name_key.as_ref()
    }

    /// The child's Rust field name.
    #[must_use]
    pub const fn name(&self) -> &Ident {
        &self.name
    }

    /// The child's state: a term, a whole group, `k!`, or `map!`.
    #[must_use]
    pub const fn value(&self) -> &StateTerm {
        &self.value
    }
}

/// One instance record of a collection entry: `label @ Decl { .. }` or
/// `k::fragment![Decl { .. }]` (KF-023).
#[derive(Clone, Debug)]
pub struct InstanceItem {
    range: TokenRange,
    label: Option<Ident>,
    owner: Path,
    fields: Vec<InstanceField>,
    rest: InstanceRest,
    fragment: bool,
    key: Option<ProvenanceKey>,
}

impl InstanceItem {
    /// Keys the instance record, then each child's name under the roles of
    /// `position`, each followed by what `child` keys in that child's state.
    pub(crate) fn allocate_keys(
        &mut self,
        keys: &mut KeyAllocator,
        position: StatePosition,
        child: &mut dyn FnMut(&mut KeyAllocator, &mut StateTerm) -> Result<(), SyntaxError>,
    ) -> Result<(), SyntaxError> {
        self.key = Some(key_at(keys, position, RuleRole::CellsInstance, self.range)?);
        for field in &mut self.fields {
            let range = TokenRange::for_tokens(&field.name)?;
            field.name_key = Some(key_at(keys, position, RuleRole::CellsInstanceField, range)?);
            child(keys, &mut field.value)?;
        }
        Ok(())
    }

    pub(crate) const fn new(
        range: TokenRange,
        label: Option<Ident>,
        owner: Path,
        fields: Vec<InstanceField>,
        rest: InstanceRest,
    ) -> Self {
        Self {
            range,
            label,
            owner,
            fields,
            rest,
            fragment: false,
            key: None,
        }
    }

    /// The key of the instance record, given by the rule side that anchors
    /// the collection.
    #[must_use]
    pub const fn key(&self) -> Option<&ProvenanceKey> {
        self.key.as_ref()
    }

    /// The complete instance-record range.
    #[must_use]
    pub const fn range(&self) -> TokenRange {
        self.range
    }

    /// The pattern label (`me @ ..`); a label is not a term binder.
    #[must_use]
    pub const fn label(&self) -> Option<&Ident> {
        self.label.as_ref()
    }

    /// The instance's `#[k::cell]` struct path.
    #[must_use]
    pub const fn owner(&self) -> &Path {
        &self.owner
    }

    /// The named children in source order.
    #[must_use]
    pub fn fields(&self) -> &[InstanceField] {
        &self.fields
    }

    /// The record's rest.
    #[must_use]
    pub const fn rest(&self) -> &InstanceRest {
        &self.rest
    }

    /// Whether the record was written inside `k::fragment![..]`.
    #[must_use]
    pub const fn is_fragment(&self) -> bool {
        self.fragment
    }
}

/// A collection entry: instance records and an optional rest (KF-023, R8).
#[derive(Clone, Debug)]
pub struct InstanceList {
    delimiter: InstanceListDelimiter,
    front: Vec<InstanceItem>,
    rest: StateMacroRemainder,
    back: Vec<InstanceItem>,
    rest_key: Option<ProvenanceKey>,
}

impl InstanceList {
    pub(crate) const fn new(
        delimiter: InstanceListDelimiter,
        front: Vec<InstanceItem>,
        rest: StateMacroRemainder,
        back: Vec<InstanceItem>,
    ) -> Self {
        Self {
            delimiter,
            front,
            rest,
            back,
            rest_key: None,
        }
    }

    /// The key of the collection rest, given by the rule side that anchors
    /// the collection.
    #[must_use]
    pub const fn rest_key(&self) -> Option<&ProvenanceKey> {
        self.rest_key.as_ref()
    }

    /// Braces (Set, Map) or brackets (List).
    #[must_use]
    pub const fn delimiter(&self) -> InstanceListDelimiter {
        self.delimiter
    }

    /// The instances before the rest.
    #[must_use]
    pub fn front(&self) -> &[InstanceItem] {
        &self.front
    }

    /// The collection rest; [`StateMacroRemainder::Exact`] when absent.
    #[must_use]
    pub const fn rest(&self) -> &StateMacroRemainder {
        &self.rest
    }

    /// The instances after the rest of a bracketed list.
    #[must_use]
    pub fn back(&self) -> &[InstanceItem] {
        &self.back
    }

    /// Every instance, front then back.
    pub fn instances(&self) -> impl Iterator<Item = &InstanceItem> {
        self.front.iter().chain(&self.back)
    }

    /// Forgets the keys of the list and of its instances' children, before
    /// an enclosing sentence's pass keys them.
    pub(crate) fn clear_keys(&mut self) {
        self.rest_key = None;
        for item in self.front.iter_mut().chain(&mut self.back) {
            item.key = None;
            for field in &mut item.fields {
                field.name_key = None;
                field.value.clear_keys();
            }
        }
    }

    /// Keys the front instances (each followed by its children's names), the
    /// rest, then the back instances, under the roles of `position`. The
    /// children's states are the enclosing sentence's to key.
    pub(crate) fn allocate_keys(
        &mut self,
        keys: &mut KeyAllocator,
        position: StatePosition,
    ) -> Result<(), SyntaxError> {
        for item in &mut self.front {
            item.allocate_keys(keys, position, &mut |_, _| Ok(()))?;
        }
        self.allocate_rest_key(keys, position)?;
        for item in &mut self.back {
            item.allocate_keys(keys, position, &mut |_, _| Ok(()))?;
        }
        Ok(())
    }

    /// Keys the collection rest, if any, under the role of `position`.
    pub(crate) fn allocate_rest_key(
        &mut self,
        keys: &mut KeyAllocator,
        position: StatePosition,
    ) -> Result<(), SyntaxError> {
        if let Some(range) = self.rest.range() {
            self.rest_key = Some(key_at(keys, position, RuleRole::CellsInstancesRest, range)?);
        }
        Ok(())
    }

    /// The instances before the rest, for a pass that keys them.
    pub(crate) fn front_mut(&mut self) -> &mut [InstanceItem] {
        &mut self.front
    }

    /// The instances after the rest, for a pass that keys them.
    pub(crate) fn back_mut(&mut self) -> &mut [InstanceItem] {
        &mut self.back
    }

    /// Every instance's children's states, mutably, in [`Self::instances`]
    /// order.
    pub(crate) fn nested_states_mut(&mut self) -> Vec<&mut StateTerm> {
        self.front
            .iter_mut()
            .chain(&mut self.back)
            .flat_map(|instance| instance.fields.iter_mut().map(|field| &mut field.value))
            .collect()
    }
}

/// One selected fixed cell in a `cells!` payload: a leaf with its
/// `Cell(..)`/`KCell(..)` wrapper, or a whole nested cell without one.
#[derive(Clone, Debug)]
pub struct CellsEntry {
    name: Ident,
    owner: Option<Path>,
    wrapper: Option<Path>,
    value: StateTerm,
    name_key: Option<ProvenanceKey>,
    wrapper_key: Option<ProvenanceKey>,
}

impl CellsEntry {
    /// Returns the declared Rust field name used for identity resolution.
    #[must_use]
    pub const fn name(&self) -> &Ident {
        &self.name
    }

    /// Returns an explicit nested declaration owner, when the field was
    /// written as an owner-qualified path such as `Account::storage`.
    ///
    /// Unqualified authored fields continue to resolve against the rule's
    /// top-level configuration.
    #[must_use]
    pub const fn owner(&self) -> Option<&Path> {
        self.owner.as_ref()
    }

    /// Returns the authored `Cell`/`KCell` wrapper path, absent exactly for a
    /// whole nested-cell entry ([`StateTerm::Group`]), `None`, and a
    /// collection entry; for `Some(Cell(..))` it is the inner wrapper.
    #[must_use]
    pub const fn wrapper(&self) -> Option<&Path> {
        self.wrapper.as_ref()
    }

    /// Returns the compiler-parsed leaf contents.
    #[must_use]
    pub const fn value(&self) -> &StateTerm {
        &self.value
    }

    /// Returns the compiler-parsed leaf contents, for a pass that keys them.
    pub(crate) const fn value_mut(&mut self) -> &mut StateTerm {
        &mut self.value
    }

    /// The key of the field name.
    #[must_use]
    pub const fn name_key(&self) -> Option<&ProvenanceKey> {
        self.name_key.as_ref()
    }

    /// The key of the `Cell`/`KCell` wrapper.
    #[must_use]
    pub const fn wrapper_key(&self) -> Option<&ProvenanceKey> {
        self.wrapper_key.as_ref()
    }
}

/// Parsed `cells!` pattern or expression payload.
#[derive(Clone, Debug)]
pub struct CellsExpression {
    tokens: TokenStream,
    context: StateMacroContext,
    entries: Vec<CellsEntry>,
    remainder: StateMacroRemainder,
    payload_key: Option<ProvenanceKey>,
    remainder_key: Option<ProvenanceKey>,
    /// The anchors of the cells' standalone keying.
    anchors: Vec<ProvenanceAnchor>,
}

impl CellsExpression {
    /// Pattern versus expression context used for frame validation.
    #[must_use]
    pub const fn context(&self) -> StateMacroContext {
        self.context
    }

    /// Selected cells in authored order.
    #[must_use]
    pub fn entries(&self) -> &[CellsEntry] {
        &self.entries
    }

    /// The paths of the `map!` islands that write the cells' maps, in source
    /// order ([`StateTerm::map_islands`]).
    #[must_use]
    pub fn map_islands(&self) -> Vec<&Path> {
        self.entries
            .iter()
            .flat_map(|entry| entry.value().map_islands())
            .collect()
    }

    /// Exact, anonymous, bound, or reused configuration frame.
    #[must_use]
    pub const fn remainder(&self) -> &StateMacroRemainder {
        &self.remainder
    }

    /// Selected cells in authored order, for a pass that keys them.
    pub(crate) fn entries_mut(&mut self) -> &mut [CellsEntry] {
        &mut self.entries
    }

    /// The key of the payload.
    #[must_use]
    pub const fn payload_key(&self) -> Option<&ProvenanceKey> {
        self.payload_key.as_ref()
    }

    /// The key of the configuration remainder.
    #[must_use]
    pub const fn remainder_key(&self) -> Option<&ProvenanceKey> {
        self.remainder_key.as_ref()
    }

    /// Returns payload, field, wrapper, and remainder anchors of the cells'
    /// standalone keying.
    ///
    /// Nested `k!`/`map!` provenance is returned by each entry's [`StateTerm`].
    ///
    /// # Errors
    ///
    /// None: the cells were keyed when they were parsed.
    pub fn provenance(&self) -> Result<Vec<ProvenanceAnchor>, SyntaxError> {
        Ok(self.anchors.clone())
    }

    /// Keys the cells as a sentence of their own. Their entries' states are
    /// not part of it: each `k!` or `map!` among them is keyed as its own.
    fn keyed_standalone(mut self) -> Result<Self, SyntaxError> {
        let mut keys = KeyAllocator::default();
        self.allocate_keys(&mut keys, StatePosition::Standalone)?;
        self.anchors = keys.into_anchors();
        Ok(self)
    }

    /// Forgets the keys of the cells and of every entry's state, and the
    /// anchors of its standalone keying, before an enclosing sentence's pass
    /// keys them.
    pub(crate) fn clear_keys(&mut self) {
        self.payload_key = None;
        self.remainder_key = None;
        self.anchors.clear();
        for entry in &mut self.entries {
            entry.name_key = None;
            entry.wrapper_key = None;
            entry.value.clear_keys();
        }
    }

    /// Keys the payload, each field with its wrapper, then the remainder,
    /// under the roles of `position`. A standalone wrapper is numbered as its
    /// field is; a rule side numbers its wrappers on their own. The entries'
    /// states are the enclosing sentence's to key.
    pub(crate) fn allocate_keys(
        &mut self,
        keys: &mut KeyAllocator,
        position: StatePosition,
    ) -> Result<(), SyntaxError> {
        let range = TokenRange::for_tokens(&self.tokens)?;
        self.payload_key = Some(key_at(keys, position, RuleRole::CellsPayload, range)?);
        for entry in &mut self.entries {
            let field = key_at(
                keys,
                position,
                RuleRole::CellsField,
                TokenRange::for_tokens(&entry.name)?,
            )?;
            if let Some(wrapper) = &entry.wrapper {
                let range = TokenRange::for_tokens(wrapper)?;
                let role = position.role(RuleRole::CellsWrapper);
                entry.wrapper_key = Some(match position {
                    StatePosition::Standalone => keys.paired(role, &field, range)?,
                    StatePosition::Rule(_) => keys.key(role, range)?,
                });
            }
            entry.name_key = Some(field);
        }
        if let Some(range) = self.remainder.range() {
            self.remainder_key = Some(key_at(keys, position, RuleRole::CellsRemainder, range)?);
        }
        Ok(())
    }
}

/// Parses a `k!` pattern payload.
///
/// # Errors
///
/// Rejects malformed separators, misplaced `.K`, duplicate tails, and
/// expression-style `..tail` at the responsible token.
pub fn parse_k_sequence_pattern(tokens: TokenStream) -> Result<KSequence, SyntaxError> {
    parse_k_sequence(tokens, StateMacroContext::Pattern, None)
}

/// Parses a `k!` expression payload.
///
/// # Errors
///
/// Rejects pattern-only tail bindings and malformed sequence syntax.
pub fn parse_k_sequence_expression(tokens: TokenStream) -> Result<KSequence, SyntaxError> {
    parse_k_sequence(tokens, StateMacroContext::Expression, None)
}

/// Parses a `map!` pattern payload.
///
/// # Errors
///
/// Rejects updates and expression-style remainders in pattern position.
pub fn parse_map_pattern(tokens: TokenStream) -> Result<MapExpression, SyntaxError> {
    parse_map(tokens, StateMacroContext::Pattern, None)
}

/// Parses a `map!` expression payload, including functional updates.
///
/// # Errors
///
/// Rejects pattern-only remainder bindings and malformed items/updates.
pub fn parse_map_expression(tokens: TokenStream) -> Result<MapExpression, SyntaxError> {
    parse_map(tokens, StateMacroContext::Expression, None)
}

/// Parses a `map!` pattern payload together with lossless source trivia.
///
/// # Errors
///
/// Returns the same semantic failures as [`parse_map_pattern`] and rejects
/// non-documentation block comments with a byte-exact source range.
pub fn parse_map_pattern_source_with_trivia(
    source: &str,
) -> Result<(MapExpression, crate::TriviaTable), SyntaxError> {
    let (tokens, trivia) = crate::trivia::tokenize_with_trivia(source)?;
    trivia.reject_non_doc_block_comments("map")?;
    Ok((parse_map_pattern(tokens)?, trivia))
}

/// Parses a `map!` expression payload together with lossless source trivia.
///
/// # Errors
///
/// Returns the same semantic failures as [`parse_map_expression`] and rejects
/// non-documentation block comments with a byte-exact source range.
pub fn parse_map_expression_source_with_trivia(
    source: &str,
) -> Result<(MapExpression, crate::TriviaTable), SyntaxError> {
    let (tokens, trivia) = crate::trivia::tokenize_with_trivia(source)?;
    trivia.reject_non_doc_block_comments("map")?;
    Ok((parse_map_expression(tokens)?, trivia))
}

/// Parses a `cells!` pattern payload.
///
/// # Errors
///
/// Rejects duplicate cells, malformed wrappers, and expression-only frames.
pub fn parse_cells_pattern(tokens: TokenStream) -> Result<CellsExpression, SyntaxError> {
    parse_cells(tokens, StateMacroContext::Pattern)
}

/// Parses a `cells!` expression payload.
///
/// # Errors
///
/// Rejects duplicate cells, malformed wrappers, and pattern-only frames.
pub fn parse_cells_expression(tokens: TokenStream) -> Result<CellsExpression, SyntaxError> {
    parse_cells(tokens, StateMacroContext::Expression)
}

/// Parses a `cells!` pattern payload together with lossless source trivia.
///
/// # Errors
///
/// Returns the same semantic failures as [`parse_cells_pattern`] and rejects
/// non-documentation block comments with a byte-exact source range.
pub fn parse_cells_pattern_source_with_trivia(
    source: &str,
) -> Result<(CellsExpression, crate::TriviaTable), SyntaxError> {
    let (tokens, trivia) = crate::trivia::tokenize_with_trivia(source)?;
    trivia.reject_non_doc_block_comments("cells")?;
    Ok((parse_cells_pattern(tokens)?, trivia))
}

/// Parses a `cells!` expression payload together with lossless source trivia.
///
/// # Errors
///
/// Returns the same semantic failures as [`parse_cells_expression`] and rejects
/// non-documentation block comments with a byte-exact source range.
pub fn parse_cells_expression_source_with_trivia(
    source: &str,
) -> Result<(CellsExpression, crate::TriviaTable), SyntaxError> {
    let (tokens, trivia) = crate::trivia::tokenize_with_trivia(source)?;
    trivia.reject_non_doc_block_comments("cells")?;
    Ok((parse_cells_expression(tokens)?, trivia))
}

/// Parses a `k!` payload held by `invocation`, if an enclosing form read
/// it, and keys it as a sentence of its own.
pub(crate) fn parse_k_sequence(
    tokens: TokenStream,
    context: StateMacroContext,
    invocation: Option<TokenRange>,
) -> Result<KSequence, SyntaxError> {
    parse_unkeyed_k_sequence(tokens, context)
        .map(|sequence| sequence.invoked_at(invocation))
        .and_then(KSequence::keyed_standalone)
}

#[expect(
    clippy::too_many_lines,
    reason = "One closed sequence grammar keeps tail diagnostics local."
)]
fn parse_unkeyed_k_sequence(
    tokens: TokenStream,
    context: StateMacroContext,
) -> Result<KSequence, SyntaxError> {
    // A trailing comma ends the list; it is no element.
    let tokens = crate::parse::strip_trailing_comma(tokens);
    let original = tokens.clone();
    structured_with(
        tokens,
        move |input| {
            if input.is_empty() {
                return Ok(KSequence::new(
                    original.clone(),
                    Vec::new(),
                    StateMacroRemainder::Exact,
                    KSequenceNotation::Comma,
                ));
            }
            if starts_remainder(input) {
                let tail = parse_remainder(input, context, "k")?;
                if !input.is_empty() {
                    return Err(state_error(
                        "k",
                        "the sequence tail must be last",
                        input.span(),
                    ));
                }
                return Ok(KSequence::new(
                    original.clone(),
                    Vec::new(),
                    tail,
                    KSequenceNotation::Comma,
                ));
            }
            if input.peek(Token![.]) {
                let range = parse_dot_unit(input, "K")?;
                if !input.is_empty() {
                    return Err(state_error(
                        "k",
                        "`.K` must be the complete empty sequence",
                        input.span(),
                    ));
                }
                let _ = range;
                return Ok(KSequence::new(
                    original.clone(),
                    Vec::new(),
                    StateMacroRemainder::Exact,
                    KSequenceNotation::DotK,
                ));
            }

            let mut items = Vec::new();
            let mut tail = StateMacroRemainder::Exact;
            let mut notation = None;
            loop {
                if starts_remainder(input) {
                    tail = parse_remainder(input, context, "k")?;
                    break;
                }
                items.push(parse_state_item(input, context)?);
                if input.is_empty() {
                    break;
                }
                let separator = if input.peek(Token![,]) {
                    input.parse::<Token![,]>().map_err(SyntaxError::from)?;
                    KSequenceNotation::Comma
                } else if input.peek(Token![~]) {
                    input.parse::<Token![~]>().map_err(SyntaxError::from)?;
                    input.parse::<Token![>]>().map_err(SyntaxError::from)?;
                    KSequenceNotation::Operator
                } else {
                    return Err(state_error(
                        "k",
                        "expected `,`, `~>`, or a sequence tail",
                        input.span(),
                    ));
                };
                if let Some(previous) = notation
                    && previous != separator
                {
                    return Err(state_error(
                        "k",
                        "cannot mix `,` and `~>` separators",
                        input.span(),
                    ));
                }
                notation = Some(separator);
                if input.is_empty() {
                    return Err(state_error(
                        "k",
                        "a sequence separator requires another item",
                        input.span(),
                    ));
                }
                if input.peek(Token![.]) && !input.peek(Token![..]) {
                    parse_dot_unit(input, "K")?;
                    if !input.is_empty() {
                        return Err(state_error(
                            "k",
                            "`.K` must terminate the sequence",
                            input.span(),
                        ));
                    }
                    break;
                }
            }
            if !input.is_empty() {
                return Err(state_error(
                    "k",
                    "the sequence tail must be last",
                    input.span(),
                ));
            }
            Ok(KSequence::new(
                original.clone(),
                items,
                tail,
                notation.unwrap_or(KSequenceNotation::Comma),
            ))
        },
        |error| state_error("k", "malformed compiler-owned state syntax", error.span()),
    )
}

/// Whether an initializer cell's own `map![..]` payload is read as a collection literal: one with
/// a rest (`map![k -> v, ..m]`, the update chain over `m`), or one the cell's own map does not
/// read at all, whose error the literal reports. The empty map, a functional update
/// (`map![m; k <- v]`) and the entries alone keep the cell's own reading, whose entries the
/// compiler builds as the literal's value (`krs_compiler`'s built maps).
pub(crate) fn built_map_is_literal(payload: TokenStream) -> bool {
    !matches!(
        parse_unkeyed_map(payload, StateMacroContext::Expression).map(|map| map.body),
        Ok(MapBody::Empty { .. }
            | MapBody::Update { .. }
            | MapBody::Items {
                remainder: StateMacroRemainder::Exact,
                ..
            })
    )
}

/// Parses a `map!` payload held by `invocation`, if an enclosing form read
/// it, and keys it as a sentence of its own.
pub(crate) fn parse_map(
    tokens: TokenStream,
    context: StateMacroContext,
    invocation: Option<TokenRange>,
) -> Result<MapExpression, SyntaxError> {
    parse_unkeyed_map(tokens, context)
        .map(|map| map.invoked_at(invocation))
        .and_then(MapExpression::keyed_standalone)
}

#[expect(
    clippy::too_many_lines,
    reason = "One closed grammar keeps update/item diagnostics local."
)]
fn parse_unkeyed_map(
    tokens: TokenStream,
    context: StateMacroContext,
) -> Result<MapExpression, SyntaxError> {
    // A trailing comma ends the list; it is no element.
    let tokens = crate::parse::strip_trailing_comma(tokens);
    if let Some((base, bracket)) = split_bracket_update(&tokens) {
        if context == StateMacroContext::Pattern {
            return Err(state_error(
                "map",
                "functional updates are expression-only",
                bracket.span(),
            ));
        }
        let base = TermExpression::parse_tokens(base)?;
        let (key, value) = parse_update_inner(bracket.stream())?;
        return Ok(MapExpression::new(
            tokens,
            MapBody::Update { base, key, value },
            None,
        ));
    }
    if let Some((base_tokens, update_tokens)) = split_once_punct(&tokens, ';') {
        if context == StateMacroContext::Pattern {
            return Err(state_error(
                "map",
                "functional updates are expression-only",
                tokens.span(),
            ));
        }
        let base = TermExpression::parse_tokens(base_tokens)?;
        let (key, value) = parse_update_inner(update_tokens)?;
        return Ok(MapExpression::new(
            tokens,
            MapBody::Update { base, key, value },
            None,
        ));
    }
    let original = tokens.clone();
    structured_with(
        tokens,
        move |input| {
            if input.is_empty() {
                return Ok(MapExpression::empty(original.clone(), false, context));
            }
            if input.peek(Token![.]) {
                parse_dot_unit(input, "Map")?;
                if !input.is_empty() {
                    return Err(state_error(
                        "map",
                        "`.Map` must be the complete empty map",
                        input.span(),
                    ));
                }
                return Ok(MapExpression::empty(original.clone(), true, context));
            }

            if starts_remainder(input) {
                let remainder = parse_remainder(input, context, "map")?;
                if !input.is_empty() {
                    return Err(state_error(
                        "map",
                        "the map remainder must be the complete payload",
                        input.span(),
                    ));
                }
                return Ok(MapExpression::items(
                    original.clone(),
                    Vec::new(),
                    remainder,
                    context,
                ));
            }

            let first = parse_map_item_key(input)?;
            let mut keys = vec![first.to_string()];
            parse_map_item_arrow(input)?;
            let value = parse_state_item(input, context)?;
            let mut items = vec![MapItem {
                key: state_key_tokens(first, context)?,
                value,
            }];
            let mut remainder = StateMacroRemainder::Exact;
            while !input.is_empty() {
                input.parse::<Token![,]>().map_err(SyntaxError::from)?;
                if input.is_empty() {
                    break;
                }
                if starts_remainder(input) {
                    remainder = parse_remainder(input, context, "map")?;
                    break;
                }
                let key = parse_map_item_key(input)?;
                // A pattern's items are distinct entries of the map, so two
                // keys that are the same term can never both match; two `_`
                // keys match two distinct entries. A built map writes each
                // entry over the map before it, so of two keys that are the
                // same term the earlier value could never be read.
                let text = key.to_string();
                if text != "_" && keys.contains(&text) {
                    return Err(if context == StateMacroContext::Pattern {
                        state_error(
                            "map",
                            "a map pattern names one key twice; \
                             its items are distinct entries of the map, so no map matches it",
                            key.span(),
                        )
                    } else {
                        crate::collection_literal::repeated_key(&text, key.span())
                    });
                }
                keys.push(text);
                parse_map_item_arrow(input)?;
                let value = parse_state_item(input, context)?;
                items.push(MapItem {
                    key: state_key_tokens(key, context)?,
                    value,
                });
            }
            if !input.is_empty() {
                return Err(state_error(
                    "map",
                    "the map remainder must be last",
                    input.span(),
                ));
            }
            Ok(MapExpression::items(
                original.clone(),
                items,
                remainder,
                context,
            ))
        },
        |error| state_error("map", "malformed compiler-owned state syntax", error.span()),
    )
}

fn parse_map_item_arrow(input: ParseStream<'_>) -> Result<(), SyntaxError> {
    if input.peek(Token![=>]) {
        return Err(state_error(
            "map",
            "`=>` is reserved for rewrites; map entries use `->`",
            input.span(),
        ));
    }
    input
        .parse::<Token![->]>()
        .map(|_| ())
        .map_err(|_| state_error("map", "expected `->` after a map-item key", input.span()))
}

fn parse_map_item_key(input: ParseStream<'_>) -> Result<TokenStream, SyntaxError> {
    let mut tokens = TokenStream::new();
    while !input.is_empty() && !input.peek(Token![->]) && !input.peek(Token![=>]) {
        tokens.extend([input.parse::<TokenTree>().map_err(SyntaxError::from)?]);
    }
    if tokens.is_empty() {
        return Err(state_error("map", "expected a map-item key", input.span()));
    }
    Ok(tokens)
}

/// Parses a `cells!` payload and keys it as a sentence of its own.
fn parse_cells(
    tokens: TokenStream,
    context: StateMacroContext,
) -> Result<CellsExpression, SyntaxError> {
    parse_unkeyed_cells(tokens, context).and_then(CellsExpression::keyed_standalone)
}

fn parse_unkeyed_cells(
    tokens: TokenStream,
    context: StateMacroContext,
) -> Result<CellsExpression, SyntaxError> {
    // A trailing comma ends the list; it is no element.
    let tokens = crate::parse::strip_trailing_comma(tokens);
    let original = tokens.clone();
    structured_with(
        tokens,
        move |input| {
            let mut entries = Vec::new();
            let mut names = BTreeSet::new();
            let mut remainder = StateMacroRemainder::Exact;
            while !input.is_empty() {
                if starts_remainder(input) {
                    remainder = parse_remainder(input, context, "cells")?;
                    if !input.is_empty() {
                        return Err(state_error(
                            "cells",
                            "the configuration remainder must be last",
                            input.span(),
                        ));
                    }
                    break;
                }
                let mut field: Path = input.parse().map_err(SyntaxError::from)?;
                let Some(last) = plain_path_last(&field) else {
                    return Err(state_error(
                        "cells",
                        "cell fields must be plain Rust paths",
                        field.span(),
                    ));
                };
                let name = last.ident.clone();
                field.segments.pop();
                field.segments.pop_punct();
                let owner = if field.segments.is_empty() {
                    None
                } else {
                    Some(field)
                };
                let identity = owner.as_ref().map_or_else(
                    || name.to_string(),
                    |owner| format!("{}::{name}", path_text(owner)),
                );
                if !names.insert(identity) {
                    return Err(state_error(
                        "cells",
                        "an owner-qualified cell field occurs more than once",
                        name.span(),
                    ));
                }
                input.parse::<Token![:]>().map_err(SyntaxError::from)?;
                let (wrapper, value) = parse_entry_value(input, context)?;
                entries.push(CellsEntry {
                    name,
                    owner,
                    wrapper,
                    value,
                    name_key: None,
                    wrapper_key: None,
                });
                if input.is_empty() {
                    break;
                }
                input.parse::<Token![,]>().map_err(SyntaxError::from)?;
            }
            if entries.is_empty() {
                return Err(state_error(
                    "cells",
                    "at least one cell clause is required",
                    input.span(),
                ));
            }
            Ok(CellsExpression {
                tokens: original.clone(),
                context,
                entries,
                remainder,
                payload_key: None,
                remainder_key: None,
                anchors: Vec::new(),
            })
        },
        |error| {
            state_error(
                "cells",
                "malformed compiler-owned state syntax",
                error.span(),
            )
        },
    )
}

/// Parses one `cells!` entry value: `None`, `Some(..)` around a leaf or
/// group entry, an instance list, a wrapped leaf, or a group entry.
fn parse_entry_value(
    input: ParseStream<'_>,
    context: StateMacroContext,
) -> Result<(Option<Path>, StateTerm), SyntaxError> {
    if let Some(range) = parse_option_none(input)? {
        return Ok((None, StateTerm::Absent(range)));
    }
    if starts_option_some(input) {
        input.parse::<Ident>().map_err(SyntaxError::from)?;
        let inner = parse_parenthesized_tokens(input).map_err(SyntaxError::from)?;
        let span = inner.span();
        let (wrapper, value) = structured_with(
            inner,
            move |inner| {
                let parsed = parse_entry_value(inner, context)?;
                if !inner.is_empty() {
                    return Err(state_error(
                        "cells",
                        "`Some(..)` holds one cell entry",
                        inner.span(),
                    ));
                }
                Ok(parsed)
            },
            |error| state_error("cells", "malformed `Some(..)` entry", error.span()),
        )?;
        if matches!(
            value,
            StateTerm::Present(_) | StateTerm::Absent(_) | StateTerm::Instances(_)
        ) {
            return Err(state_error(
                "cells",
                "`Some(..)` holds a `Cell(..)` leaf entry or a nested-cell entry",
                span,
            ));
        }
        return Ok((wrapper, StateTerm::Present(Box::new(value))));
    }
    if input.peek(syn::token::Brace) || input.peek(syn::token::Bracket) {
        let group: proc_macro2::Group = input.parse().map_err(SyntaxError::from)?;
        return Ok((
            None,
            StateTerm::Instances(parse_instance_list(&group, context)?),
        ));
    }
    if !starts_wrapped_entry(input) {
        return Ok((None, parse_group_entry(input, context)?));
    }
    let wrapper: Path = input.parse().map_err(SyntaxError::from)?;
    let Some(last) = plain_path_last(&wrapper) else {
        return Err(state_error(
            "cells",
            "cell wrappers must be plain Rust paths",
            wrapper.span(),
        ));
    };
    let (value_tokens, parentheses) =
        parse_parenthesized_group(input).map_err(SyntaxError::from)?;
    let wrapper_name = last.ident.to_string();
    let value = match wrapper_name.as_str() {
        // `KCell(..)`'s parentheses hold the K sequence, as `k::k![..]`'s
        // brackets do; the wrapper path is a node of its own.
        "KCell" => {
            StateTerm::KSequence(parse_k_sequence(value_tokens, context, Some(parentheses))?)
        }
        "Cell" => parse_state_term(crate::parse::strip_trailing_comma(value_tokens), context)?,
        _ => {
            return Err(state_error(
                "cells",
                "entries require `Cell(...)` or `KCell(...)`",
                wrapper.span(),
            ));
        }
    };
    Ok((Some(wrapper), value))
}

/// Parses `None` (optionally `Option::None`) when it is the whole entry value.
fn parse_option_none(input: ParseStream<'_>) -> Result<Option<TokenRange>, SyntaxError> {
    let fork = input.fork();
    let Ok(path) = fork.parse::<Path>() else {
        return Ok(None);
    };
    if !crate::initializer::is_option_variant(&path, "None")
        || !(fork.is_empty() || fork.peek(Token![,]))
    {
        return Ok(None);
    }
    let path: Path = input.parse().map_err(SyntaxError::from)?;
    Ok(Some(TokenRange::for_tokens(&path)?))
}

/// Whether the entry value is `Some(..)`.
fn starts_option_some(input: ParseStream<'_>) -> bool {
    let fork = input.fork();
    fork.parse::<Ident>()
        .is_ok_and(|ident| ident == "Some" && fork.peek(syn::token::Paren))
}

/// Parses the `{ .. }` or `[ .. ]` payload of a collection entry.
fn parse_instance_list(
    group: &proc_macro2::Group,
    context: StateMacroContext,
) -> Result<InstanceList, SyntaxError> {
    let delimiter = match group.delimiter() {
        Delimiter::Brace => InstanceListDelimiter::Brace,
        Delimiter::Bracket => InstanceListDelimiter::Bracket,
        _ => {
            return Err(state_error(
                "cells",
                "a collection entry is `{ .. }` (Set, Map) or `[ .. ]` (List)",
                group.span(),
            ));
        }
    };
    structured_with(
        group.stream(),
        move |input| {
            let mut front = Vec::new();
            let mut back = Vec::new();
            let mut rest = None;
            while !input.is_empty() {
                if starts_instance_rest(input) {
                    if rest.is_some() {
                        return Err(state_error(
                            "cells",
                            "a collection entry has at most one rest",
                            input.span(),
                        ));
                    }
                    rest = Some(parse_instance_list_rest(input, context)?);
                } else if rest.is_some() {
                    if delimiter == InstanceListDelimiter::Brace {
                        return Err(state_error(
                            "cells",
                            "the rest of a Set or Map collection is last",
                            input.span(),
                        ));
                    }
                    back.push(parse_instance_item(input, context)?);
                } else {
                    front.push(parse_instance_item(input, context)?);
                }
                if input.is_empty() {
                    break;
                }
                input.parse::<Token![,]>().map_err(SyntaxError::from)?;
            }
            Ok(InstanceList::new(
                delimiter,
                front,
                rest.unwrap_or(StateMacroRemainder::Exact),
                back,
            ))
        },
        |error| state_error("cells", "malformed collection entry", error.span()),
    )
}

/// Whether the next list item is a collection rest: `..`, `name @ ..`, or `..name`.
fn starts_instance_rest(input: ParseStream<'_>) -> bool {
    starts_remainder(input)
}

/// Parses a collection rest; a result may write a bare `..` as well as `..name`.
fn parse_instance_list_rest(
    input: ParseStream<'_>,
    context: StateMacroContext,
) -> Result<StateMacroRemainder, SyntaxError> {
    if context == StateMacroContext::Expression && input.peek(Token![..]) {
        let fork = input.fork();
        fork.parse::<Token![..]>().map_err(SyntaxError::from)?;
        if !fork.peek(Ident) {
            let dots: Token![..] = input.parse().map_err(SyntaxError::from)?;
            return Ok(StateMacroRemainder::Anonymous(TokenRange::for_tokens(
                &dots,
            )?));
        }
    }
    parse_remainder(input, context, "cells")
}

/// Parses one instance record: `[label @] Decl { .. }` or
/// `[label @] k::fragment![Decl { .. }]`.
fn parse_instance_item(
    input: ParseStream<'_>,
    context: StateMacroContext,
) -> Result<InstanceItem, SyntaxError> {
    let start = input.cursor();
    let label = if input.peek(Ident) && input.peek2(Token![@]) {
        let label: Ident = input.parse().map_err(SyntaxError::from)?;
        input.parse::<Token![@]>().map_err(SyntaxError::from)?;
        if context == StateMacroContext::Expression {
            return Err(state_error(
                "cells",
                "a result instance has no label; write `..label` inside it to update the matched instance",
                label.span(),
            ));
        }
        crate::parse::validate_authored_binder(&label.to_string(), label.span())?;
        Some(label)
    } else {
        None
    };
    let path: Path = input.parse().map_err(SyntaxError::from)?;
    let (owner, body, fragment) = if input.peek(Token![!]) {
        if plain_path_last(&path).is_none_or(|last| last.ident != "fragment") {
            return Err(state_error(
                "cells",
                "a collection instance is a cell record `Decl { .. }` or `k::fragment![Decl { .. }]`",
                path.span(),
            ));
        }
        input.parse::<Token![!]>().map_err(SyntaxError::from)?;
        let group: proc_macro2::Group = input.parse().map_err(SyntaxError::from)?;
        let (owner, body) = structured_with(
            crate::parse::strip_trailing_comma(group.stream()),
            |inner| {
                let owner: Path = inner.parse().map_err(SyntaxError::from)?;
                let body: proc_macro2::Group = inner.parse().map_err(SyntaxError::from)?;
                if !inner.is_empty() || body.delimiter() != Delimiter::Brace {
                    return Err(state_error(
                        "cells",
                        "`k::fragment![..]` holds one cell record `Decl { .. }`",
                        inner.span(),
                    ));
                }
                Ok((owner, body))
            },
            |error| state_error("cells", "malformed fragment! instance", error.span()),
        )?;
        (owner, body, true)
    } else {
        let body: proc_macro2::Group = input.parse().map_err(SyntaxError::from)?;
        if body.delimiter() != Delimiter::Brace {
            return Err(state_error(
                "cells",
                "a collection instance is a cell record `Decl { .. }`",
                body.span(),
            ));
        }
        (path, body, false)
    };
    if !crate::path::is_plain_path(&owner) {
        return Err(state_error(
            "cells",
            "an instance's cell struct is a plain Rust path",
            owner.span(),
        ));
    }
    let (fields, rest) = parse_instance_record(&body, context)?;
    let mut tokens = TokenStream::new();
    let mut cursor = start;
    while cursor != input.cursor() {
        let Some((token, next)) = cursor.token_tree() else {
            break;
        };
        tokens.extend([token]);
        cursor = next;
    }
    Ok(InstanceItem {
        range: TokenRange::for_tokens(&tokens)?,
        label,
        owner,
        fields,
        rest,
        fragment,
        key: None,
    })
}

/// Parses the braced body of an instance record: `child: value` entries and a
/// final rest.
fn parse_instance_record(
    body: &proc_macro2::Group,
    context: StateMacroContext,
) -> Result<(Vec<InstanceField>, InstanceRest), SyntaxError> {
    structured_with(
        body.stream(),
        move |input| {
            let mut fields: Vec<InstanceField> = Vec::new();
            let mut rest = InstanceRest::Exact;
            while !input.is_empty() {
                if input.peek(Token![..]) {
                    let dots: Token![..] = input.parse().map_err(SyntaxError::from)?;
                    rest = if input.peek(Ident) {
                        let label: Ident = input.parse().map_err(SyntaxError::from)?;
                        if context == StateMacroContext::Pattern {
                            return Err(state_error(
                                "cells",
                                "`..label` updates a matched instance in a result; a pattern instance writes `..`",
                                label.span(),
                            ));
                        }
                        InstanceRest::Update {
                            range: TokenRange::for_tokens(&quote!(#dots #label))?,
                            label,
                        }
                    } else {
                        InstanceRest::Open(TokenRange::for_tokens(&dots)?)
                    };
                    if !input.is_empty() {
                        return Err(state_error(
                            "cells",
                            "an instance record's rest is last",
                            input.span(),
                        ));
                    }
                    break;
                }
                let name: Ident = input.parse().map_err(SyntaxError::from)?;
                if fields.iter().any(|field| field.name == name) {
                    return Err(state_error(
                        "cells",
                        "an instance record names each child once",
                        name.span(),
                    ));
                }
                input.parse::<Token![:]>().map_err(SyntaxError::from)?;
                let mut tokens = TokenStream::new();
                while !input.is_empty() && !input.peek(Token![,]) {
                    tokens.extend([input.parse::<TokenTree>().map_err(SyntaxError::from)?]);
                }
                if tokens.is_empty() {
                    return Err(state_error(
                        "cells",
                        "an instance child needs a value",
                        name.span(),
                    ));
                }
                fields.push(InstanceField::new(
                    name,
                    parse_instance_child(tokens, context)?,
                ));
                if input.is_empty() {
                    break;
                }
                input.parse::<Token![,]>().map_err(SyntaxError::from)?;
            }
            Ok((fields, rest))
        },
        |error| state_error("cells", "malformed instance record", error.span()),
    )
}

/// Parses one instance child value: `k::k![..]`, `map![..]`, or a term (a
/// leaf's content or a whole nested cell, which semantic analysis tells
/// apart by the declaration).
fn parse_instance_child(
    tokens: TokenStream,
    context: StateMacroContext,
) -> Result<StateTerm, SyntaxError> {
    if let Some((name, payload)) = qualified_macro_payload(&tokens) {
        let invocation = || TokenRange::for_tokens(&tokens).map(Some);
        match name.as_str() {
            "k" => {
                return Ok(StateTerm::KSequence(parse_k_sequence(
                    payload,
                    context,
                    invocation()?,
                )?));
            }
            "map" => {
                return Ok(StateTerm::Map(
                    parse_map(payload, context, invocation()?)?.island_of(macro_path(&tokens)),
                ));
            }
            _ => {}
        }
    }
    Ok(StateTerm::Term(state_term_tokens(tokens, context)?))
}

/// The path of the macro invocation `path::name!(..)` that `tokens` hold.
fn macro_path(tokens: &TokenStream) -> Option<Path> {
    let trees = tokens.clone().into_iter().collect::<Vec<_>>();
    let path = trees.get(..trees.len().checked_sub(2)?)?;
    syn::parse2(path.iter().cloned().collect()).ok()
}

/// The last path segment and payload of `path::name!(..)`.
fn qualified_macro_payload(tokens: &TokenStream) -> Option<(String, TokenStream)> {
    let trees = tokens.clone().into_iter().collect::<Vec<_>>();
    let [
        prefix @ ..,
        TokenTree::Ident(name),
        TokenTree::Punct(bang),
        TokenTree::Group(group),
    ] = trees.as_slice()
    else {
        return None;
    };
    if bang.as_char() != '!' {
        return None;
    }
    let (chunks, remainder) = prefix.as_chunks::<3>();
    let qualified = remainder.is_empty()
        && chunks.iter().all(|chunk| {
            matches!(chunk, [TokenTree::Ident(_), TokenTree::Punct(first), TokenTree::Punct(second)]
                if first.as_char() == ':' && second.as_char() == ':')
        });
    qualified.then(|| (name.to_string(), group.stream()))
}

/// Whether the next entry value is a wrapper application `Path(..)`, as
/// every leaf entry is; a whole nested-cell entry is not (KF-016).
fn starts_wrapped_entry(input: ParseStream<'_>) -> bool {
    let fork = input.fork();
    fork.parse::<Path>().is_ok() && fork.peek(syn::token::Paren)
}

/// Parses a whole nested-cell entry value: a group binder, `_` (patterns
/// only), or a complete `k::fragment!` term (KF-016).
fn parse_group_entry(
    input: ParseStream<'_>,
    context: StateMacroContext,
) -> Result<StateTerm, SyntaxError> {
    let mut tokens = TokenStream::new();
    while !input.is_empty() && !input.peek(Token![,]) && !starts_remainder(input) {
        tokens.extend([input.parse::<TokenTree>().map_err(SyntaxError::from)?]);
    }
    let invalid = |span| {
        state_error(
            "cells",
            "nested cell entries are a binder, `_`, or fragment!",
            span,
        )
    };
    if tokens.is_empty() {
        return Err(invalid(input.span()));
    }
    let span = tokens.span();
    let term = state_term_tokens(tokens, context).map_err(|_| invalid(span))?;
    match term.tree() {
        TermTree::Reference(path) if path.get_ident().is_some() => Ok(StateTerm::Group(term)),
        TermTree::Wildcard(_) if context == StateMacroContext::Pattern => {
            Ok(StateTerm::Group(term))
        }
        TermTree::Cell(_) => Ok(StateTerm::Group(term)),
        _ => Err(invalid(span)),
    }
}

/// Parses a leaf cell's content. `k!` and `map!` are read by their last
/// path segment, so `k::map![..]` is the same map as `map![..]`, as in
/// instance children and initializers; another qualified macro, such as
/// `k::fragment![..]` or a set literal `set![..]`, is an ordinary term.
fn parse_state_term(
    tokens: TokenStream,
    context: StateMacroContext,
) -> Result<StateTerm, SyntaxError> {
    if let Some((name, payload)) = qualified_macro_payload(&tokens) {
        let invocation = || TokenRange::for_tokens(&tokens).map(Some);
        match name.as_str() {
            "k" => {
                return Ok(StateTerm::KSequence(parse_k_sequence(
                    payload,
                    context,
                    invocation()?,
                )?));
            }
            "map" => {
                return Ok(StateTerm::Map(
                    parse_map(payload, context, invocation()?)?.island_of(macro_path(&tokens)),
                ));
            }
            // A set literal has no reading of a cell's own: it is the term
            // its calls build, or a pattern holds them.
            "set" => {}
            _ if macro_payload(&tokens).is_some() => {
                return Err(state_error(
                    "cells",
                    "cell contents use only `k!` or `map!` state macros",
                    tokens.span(),
                ));
            }
            _ => {}
        }
    }
    Ok(StateTerm::Term(state_term_tokens(tokens, context)?))
}

fn parse_remainder(
    input: ParseStream<'_>,
    context: StateMacroContext,
    macro_name: &'static str,
) -> Result<StateMacroRemainder, SyntaxError> {
    let remainder = parse_remainder_tokens(input, context, macro_name)?;
    if input.peek(Token![|]) {
        // K's #Or combines terms; a remainder is a frame (KF-030).
        return Err(SyntaxError::new(
            crate::SyntaxErrorKind::InvalidPatternOr {
                reason: crate::term::PATTERN_OR_REMAINDER.to_owned(),
            },
            input.span(),
        ));
    }
    Ok(remainder)
}

fn parse_remainder_tokens(
    input: ParseStream<'_>,
    context: StateMacroContext,
    macro_name: &'static str,
) -> Result<StateMacroRemainder, SyntaxError> {
    if input.peek(Token![..]) {
        let dots: Token![..] = input.parse().map_err(SyntaxError::from)?;
        if input.peek(Ident) {
            let binding: Ident = input.parse().map_err(SyntaxError::from)?;
            if context == StateMacroContext::Pattern {
                return Err(state_error(
                    macro_name,
                    "patterns bind remainders as `name @ ..`",
                    binding.span(),
                ));
            }
            return Ok(StateMacroRemainder::Reuse {
                range: TokenRange::for_tokens(&quote!(#dots #binding))?,
                binding,
            });
        }
        if context == StateMacroContext::Expression {
            return Err(state_error(
                macro_name,
                "expression remainders must reuse a named binding as `..name`",
                dots.span(),
            ));
        }
        return Ok(StateMacroRemainder::Anonymous(TokenRange::for_tokens(
            &dots,
        )?));
    }
    let binding: Ident = input.parse().map_err(SyntaxError::from)?;
    input.parse::<Token![@]>().map_err(SyntaxError::from)?;
    let dots: Token![..] = input.parse().map_err(SyntaxError::from)?;
    if context == StateMacroContext::Expression {
        return Err(state_error(
            macro_name,
            "expressions reuse remainders as `..name`",
            binding.span(),
        ));
    }
    Ok(StateMacroRemainder::Bind {
        range: TokenRange::for_tokens(&quote!(#binding #dots))?,
        binding,
    })
}

/// Whether the next tokens are a remainder: `..`, `name @ ..`, or (in
/// expression position) `..name`. `name @ pattern` with any other pattern is
/// an alias item (KF-029).
fn starts_remainder(input: ParseStream<'_>) -> bool {
    if input.peek(Token![..]) {
        return true;
    }
    if !(input.peek(Ident) && input.peek2(Token![@])) {
        return false;
    }
    let fork = input.fork();
    fork.parse::<Ident>().is_ok() && fork.parse::<Token![@]>().is_ok() && fork.peek(Token![..])
}

/// Parses one state-island item: a pattern payload (PAT-1) in pattern
/// position, an expression otherwise.
fn parse_state_item(
    input: ParseStream<'_>,
    context: StateMacroContext,
) -> Result<TermExpression, SyntaxError> {
    match context {
        StateMacroContext::Pattern => {
            let start = input.cursor();
            let fork = input.fork();
            let pattern = input
                .call(crate::term::parse_term_pattern)
                .map_err(|error| crate::notation::pattern_parse_error(&fork, error))?;
            let tokens = crate::term::tokens_between(start, input.cursor());
            let signs = crate::rule::NegativeLiteralSpans::scan(tokens.clone());
            TermExpression::from_pattern(pattern, tokens, signs)
        }
        StateMacroContext::Expression => {
            // Full expression syntax, so an item may be a record constructor
            // (`Tag { b: x }`), as any term may.
            let expression = input
                .call(crate::term::parse_term_expression)
                .map_err(SyntaxError::from)?;
            TermExpression::from_expression(expression)
        }
    }
}

/// Parses one complete state-island payload as a term in `context`.
fn state_term_tokens(
    tokens: TokenStream,
    context: StateMacroContext,
) -> Result<TermExpression, SyntaxError> {
    match context {
        StateMacroContext::Pattern => TermExpression::parse_pattern_tokens(tokens),
        StateMacroContext::Expression => TermExpression::parse_tokens(tokens),
    }
}

/// A map item's key: in a pattern, the key a map is looked up by, which a
/// computed term may be ([`TermExpression::parse_key_pattern_tokens`]).
fn state_key_tokens(
    tokens: TokenStream,
    context: StateMacroContext,
) -> Result<TermExpression, SyntaxError> {
    match context {
        StateMacroContext::Pattern => TermExpression::parse_key_pattern_tokens(tokens),
        StateMacroContext::Expression => TermExpression::parse_tokens(tokens),
    }
}

fn parse_dot_unit(
    input: ParseStream<'_>,
    expected: &'static str,
) -> Result<TokenRange, SyntaxError> {
    let dot: Token![.] = input.parse().map_err(SyntaxError::from)?;
    let name: Ident = input.parse().map_err(SyntaxError::from)?;
    if name != expected {
        return Err(state_error(
            if expected == "K" { "k" } else { "map" },
            if expected == "K" {
                "expected `.K`"
            } else {
                "expected `.Map`"
            },
            name.span(),
        ));
    }
    TokenRange::for_tokens(&quote!(#dot #name))
}

fn parse_parenthesized_tokens(input: ParseStream<'_>) -> syn::Result<TokenStream> {
    parse_parenthesized_group(input).map(|(tokens, _)| tokens)
}

/// The contents of a parenthesized group and the range of its delimiters.
fn parse_parenthesized_group(input: ParseStream<'_>) -> syn::Result<(TokenStream, TokenRange)> {
    let content;
    let parentheses = parenthesized!(content in input);
    let range = TokenRange::new(parentheses.span.open(), parentheses.span.close());
    Ok((content.parse()?, range))
}

/// The base and the brackets of `base[key <- value]`. Brackets that end the
/// last entry's value of `k -> v` items (an index, `m[k]`) are no update.
fn split_bracket_update(tokens: &TokenStream) -> Option<(TokenStream, proc_macro2::Group)> {
    let mut trees = tokens.clone().into_iter().collect::<Vec<_>>();
    let TokenTree::Group(group) = trees.pop()? else {
        return None;
    };
    if group.delimiter() != Delimiter::Bracket || trees.is_empty() {
        return None;
    }
    let inner = group.stream().into_iter().collect::<Vec<_>>();
    if has_arrow(&trees, '-', '>') && !has_arrow(&inner, '<', '-') {
        return None;
    }
    Some((trees.into_iter().collect(), group))
}

/// Whether `trees` hold the punctuation `first` joined to `second` (`->`,
/// `<-`); `i < -1`, a comparison with a negative operand, holds no `<-`.
fn has_arrow(trees: &[TokenTree], first: char, second: char) -> bool {
    trees.windows(2).any(|window| {
        matches!(&window[0], TokenTree::Punct(value)
            if value.as_char() == first && value.spacing() == proc_macro2::Spacing::Joint)
            && matches!(&window[1], TokenTree::Punct(value) if value.as_char() == second)
    })
}

fn parse_update_inner(
    tokens: TokenStream,
) -> Result<(TermExpression, TermExpression), SyntaxError> {
    let trees = tokens.into_iter().collect::<Vec<_>>();
    if let Some(legacy_arrow) = trees.windows(2).position(|window| {
        matches!(&window[0], TokenTree::Punct(value) if value.as_char() == '=')
            && matches!(&window[1], TokenTree::Punct(value) if value.as_char() == '>')
    }) {
        return Err(state_error(
            "map",
            "`=>` is reserved for rewrites; map updates use `<-`",
            trees[legacy_arrow].span(),
        ));
    }
    let split = trees.windows(2).position(|window| {
        matches!(&window[0], TokenTree::Punct(value) if value.as_char() == '<')
            && matches!(&window[1], TokenTree::Punct(value) if value.as_char() == '-')
    });
    let Some(split) = split else {
        return Err(state_error(
            "map",
            "functional updates require `key <- value`",
            Span::call_site(),
        ));
    };
    if split == 0 || split + 2 == trees.len() {
        return Err(state_error(
            "map",
            "functional update key and value must be nonempty",
            Span::call_site(),
        ));
    }
    let key = trees[..split].iter().cloned().collect();
    let value = trees[split + 2..].iter().cloned().collect();
    Ok((
        TermExpression::parse_tokens(key)?,
        TermExpression::parse_tokens(value)?,
    ))
}

fn split_once_punct(tokens: &TokenStream, expected: char) -> Option<(TokenStream, TokenStream)> {
    let trees = tokens.clone().into_iter().collect::<Vec<_>>();
    let split = trees
        .iter()
        .position(|tree| matches!(tree, TokenTree::Punct(value) if value.as_char() == expected))?;
    if split == 0 || split + 1 == trees.len() {
        return None;
    }
    Some((
        trees[..split].iter().cloned().collect(),
        trees[split + 1..].iter().cloned().collect(),
    ))
}

fn macro_payload(tokens: &TokenStream) -> Option<(String, TokenStream)> {
    let trees = tokens.clone().into_iter().collect::<Vec<_>>();
    if trees.len() != 3 {
        return None;
    }
    let TokenTree::Ident(name) = &trees[0] else {
        return None;
    };
    let TokenTree::Punct(bang) = &trees[1] else {
        return None;
    };
    let TokenTree::Group(group) = &trees[2] else {
        return None;
    };
    (bang.as_char() == '!').then(|| (name.to_string(), group.stream()))
}

fn state_error(macro_name: &'static str, reason: &'static str, span: Span) -> SyntaxError {
    SyntaxError::new(
        SyntaxErrorKind::InvalidStateMacro { macro_name, reason },
        span,
    )
}

#[cfg(test)]
mod keyed {
    use super::{
        CellsExpression, InstanceItem, InstanceList, KSequence, KSequenceNotation, MapBody,
        MapExpression, StateTerm,
    };
    use crate::keyed_nodes::KeyedNodes;
    use crate::{SyntaxError, TokenRange};
    use krs_ir::ProvenanceKey;
    use proc_macro2::TokenStream;

    /// Records a shell's payload key with the range it is anchored at: the
    /// payload, or the invocation of an empty one.
    fn push_payload(
        nodes: &mut KeyedNodes,
        key: Option<&ProvenanceKey>,
        tokens: &TokenStream,
        invocation: Option<TokenRange>,
    ) -> Result<(), SyntaxError> {
        if let Some(range) = super::payload_range(tokens, invocation)? {
            nodes.push(key, range);
        } else {
            assert!(key.is_none(), "a payload key without an anchor");
        }
        Ok(())
    }

    impl KSequence {
        /// Records the sequence's keyed nodes: the payload (or the
        /// invocation of an empty one), each item and its nodes, then the
        /// tail (its remainder, or the authored `.K`).
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            push_payload(
                nodes,
                self.payload_key.as_ref(),
                &self.tokens,
                self.invocation,
            )?;
            for item in &self.items {
                item.keyed_nodes(nodes)?;
            }
            if let Some(range) = self.tail.range() {
                nodes.push(self.tail_key.as_ref(), range);
            } else if self.notation == KSequenceNotation::DotK {
                nodes.push_tokens(self.tail_key.as_ref(), &self.tokens)?;
            } else {
                assert!(self.tail_key.is_none(), "a tail key without a tail");
            }
            Ok(())
        }
    }

    impl MapExpression {
        /// Records the map's keyed nodes: the payload (or the invocation of
        /// an empty one), each key and value (or update base, key and value)
        /// and their nodes, then the remainder.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            push_payload(
                nodes,
                self.payload_key.as_ref(),
                &self.tokens,
                self.invocation,
            )?;
            match &self.body {
                MapBody::Empty { .. } => {}
                MapBody::Items { items, remainder } => {
                    for item in items {
                        item.key.keyed_nodes(nodes)?;
                        item.value.keyed_nodes(nodes)?;
                    }
                    if let Some(range) = remainder.range() {
                        nodes.push(self.remainder_key.as_ref(), range);
                    }
                }
                MapBody::Update { base, key, value } => {
                    for term in [base, key, value] {
                        term.keyed_nodes(nodes)?;
                    }
                }
            }
            Ok(())
        }
    }

    impl StateTerm {
        /// Records the keyed nodes of the state: its term, sequence or map,
        /// the state under `Some(..)`, or each instance of a collection.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            match self {
                Self::Term(term) | Self::Group(term) => term.keyed_nodes(nodes),
                Self::KSequence(sequence) => sequence.keyed_nodes(nodes),
                Self::Map(map) => map.keyed_nodes(nodes),
                Self::Present(inner) => inner.keyed_nodes(nodes),
                Self::Absent(_) => Ok(()),
                Self::Instances(list) => list.keyed_nodes(nodes),
            }
        }
    }

    impl InstanceItem {
        /// Records the instance's keyed nodes: the instance record, then
        /// each field's name and value.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            nodes.push(self.key.as_ref(), self.range);
            for field in &self.fields {
                nodes.push_tokens(field.name_key.as_ref(), &field.name)?;
                field.value.keyed_nodes(nodes)?;
            }
            Ok(())
        }
    }

    impl InstanceList {
        /// Records the collection's keyed nodes: its instances and its rest.
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            for item in self.instances() {
                item.keyed_nodes(nodes)?;
            }
            if let Some(range) = self.rest.range() {
                nodes.push(self.rest_key.as_ref(), range);
            }
            Ok(())
        }
    }

    impl CellsExpression {
        /// Records the configuration's keyed nodes: the payload, each
        /// entry's cell name and wrapper, then the remainder. The entries'
        /// values are keyed by the sentence that holds the configuration (a
        /// configuration standing alone does not key them: each value keeps
        /// the keys of its own parse).
        pub(crate) fn keyed_nodes(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            nodes.push_tokens(self.payload_key.as_ref(), &self.tokens)?;
            for entry in &self.entries {
                nodes.push_tokens(entry.name_key.as_ref(), &entry.name)?;
                if let Some(wrapper) = &entry.wrapper {
                    nodes.push_tokens(entry.wrapper_key.as_ref(), wrapper)?;
                }
            }
            if let Some(range) = self.remainder.range() {
                nodes.push(self.remainder_key.as_ref(), range);
            }
            Ok(())
        }

        /// Records the keyed nodes of the entries' values, which the sentence
        /// that holds the configuration keyed.
        pub(crate) fn keyed_values(&self, nodes: &mut KeyedNodes) -> Result<(), SyntaxError> {
            for entry in &self.entries {
                entry.value.keyed_nodes(nodes)?;
            }
            Ok(())
        }
    }
}
