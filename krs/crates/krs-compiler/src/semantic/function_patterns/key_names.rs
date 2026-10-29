//! The reading of a map key or a set element in a pattern, which the
//! collection is looked up by: computed and looked up, or a selection among
//! the collection's evaluated keys.
//!
//! A key is computable when its value follows from names the rest of the
//! pattern binds: nothing in it but what the pattern matches elsewhere,
//! values, and constructs that compute (a function application, an
//! operator, a sort test, a record update) from those. The rule computes it
//! and looks its entry up. A key that holds, outside every construct that
//! computes, a name nothing else binds, `_`, an alias, alternatives or an
//! open record is a selection instead: the rule chooses an entry whose key
//! matches it, and the key is matched against the map's keys, which are
//! evaluated values. The same holds for a set, which is looked up by its
//! elements as a map by its keys (`set::item(e)` in a set pattern).
//!
//! So, in one key:
//! - below a construct that computes, every position is built: `_`, an
//!   alias, alternatives and an open record mean nothing there
//!   ([`DescriptorLoweringError::PatternInComputedKey`]), and a name is read,
//!   which some other part of the pattern must bind: `{ int::add(x, 1) -> v,
//!   .. }` reads `x`, and with `x` bound nowhere else the lookup reads a value
//!   nothing gave ([`DescriptorLoweringError::UnboundKeyName`]);
//! - in a selection, a construct that computes describes a term that never
//!   occurs among the evaluated keys, so the key never matches it:
//!   `{ Pair { a: Size(n), b: y } -> v, .. }` with `y` bound nowhere else
//!   (`function-in-pattern`, and a sort test's own class).
//!
//! Whether an application computes is a fact of the declaration its head
//! resolves to, and whether a name is bound elsewhere a fact of the whole
//! pattern, so this is decided here, after resolution.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    Descriptor, DescriptorApplicationRef, DescriptorApplicationReference, DescriptorHeadRuleExtra,
    DescriptorPayload, DescriptorTerm, ProtocolHeadRuleExtra, ProtocolHeadRuleListRest,
    ProtocolRuleCells, ProtocolRuleFrame, ProtocolRuleMapBody, ProtocolRuleStateTerm,
    ProvenanceKey, SetOperation, StableItemId, TermArgumentRef,
};

use super::{
    Applied, DescriptorLoweringError, ProductionSignature, applied_function, key_range,
    matches_evaluated_sentence,
};
use crate::semantic::error::KeyPattern;

/// Refuses, in the descriptor's pattern, the first pattern-only construct
/// below a construct a computed key computes, then the first name a computed
/// key reads that the pattern binds nowhere, then the first construct that
/// computes in a key that is a selection, then the first computed keys whose
/// names no order of lookups gives.
///
/// # Errors
///
/// Returns [`DescriptorLoweringError::PatternInComputedKey`],
/// [`DescriptorLoweringError::UnboundKeyName`],
/// [`DescriptorLoweringError::FunctionInPattern`] or
/// [`DescriptorLoweringError::InvalidSortTest`].
pub(super) fn check(
    descriptor: &Descriptor,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<(), DescriptorLoweringError> {
    let payload = descriptor.payload();
    if !matches_evaluated_sentence(payload) {
        return Ok(());
    }
    let mut pattern = Pattern {
        outside: BTreeSet::new(),
        entries: Vec::new(),
        remainders: Vec::new(),
    };
    pattern.sentence(payload);
    let keys = pattern
        .entries
        .iter()
        .map(|entry| {
            let mut key = Key {
                catalog,
                lookup: entry.lookup,
                matched: Vec::new(),
                selection: None,
                computes: None,
                built: None,
                read: Vec::new(),
            };
            key.term(entry.key, None);
            key
        })
        .collect::<Vec<_>>();
    let order = Order::of(&pattern, &keys);
    let item = || Box::new(descriptor.id().clone());
    // A computed key's built positions: below a construct it computes.
    let built = order
        .computed
        .iter()
        .find_map(|&index| Some((&keys[index], keys[index].built.as_ref()?)));
    if let Some((key, (construct, at, function))) = built {
        return Err(DescriptorLoweringError::PatternInComputedKey {
            item: item(),
            construct: *construct,
            reason: format!(
                "{what} stands below {function} in {place}, which computes the value looked up, so the position is built: {why}",
                what = construct.spelling(),
                place = key.lookup.place(),
                why = construct.why(),
            ),
            range: key_range(descriptor, at).map(Box::new),
        });
    }
    if let Some((key, read)) = order.unbound(&keys) {
        let why = match key.lookup {
            Lookup::MapKey => "a key is evaluated to look its entry up, so the key",
            Lookup::SetElement => {
                "an element is evaluated to look it up in the set, so the element"
            }
        };
        return Err(DescriptorLoweringError::UnboundKeyName {
            item: item(),
            reason: format!(
                "`{name}` is not bound in this sentence: it stands only below {function} in {place}, and {why} reads `{name}` and binds nothing; bind `{name}` elsewhere in the pattern",
                name = read.name,
                function = read.function,
                place = key.lookup.place(),
            ),
            range: key_range(descriptor, read.key).map(Box::new),
        });
    }
    if let Some((key, selector, computes)) =
        order.selections.iter().find_map(|(index, selector)| {
            Some((&keys[*index], selector, keys[*index].computes.as_ref()?))
        })
    {
        let reason = format!(
            "{what} stands in {place} that also holds {selector}, so the key selects an entry by matching {held} rather than computing the {looked} looked up; {what} denotes the value evaluation produces, which no evaluated {one} is, so the key never matches: bind the selected part elsewhere in the pattern to look the entry up, or match a variable here and relate it to the application in a guard (`requires`)",
            what = computes.what,
            place = key.lookup.place(),
            held = key.lookup.held(),
            looked = key.lookup.looked_up(),
            one = key.lookup.looked_up(),
        );
        return Err(computes_refusal(descriptor, computes, reason));
    }
    if let Some(&index) = order.cycle.first() {
        let key = &keys[index];
        let computes = key.computes.as_ref().expect("a computed key computes");
        let names = order.cycle_names(&keys);
        let reason = format!(
            "{what} stands in {place} that reads {names}, which only the values of the collection's entries this key or another computed key looks up bind: no order of lookups gives a computed key the names it reads, so matching would choose an entry and evaluate {what} on each, a selection holding a function, which never matches an evaluated {one}; bind those names elsewhere in the pattern, or match a variable here and relate it to the application in a guard (`requires`)",
            what = computes.what,
            place = key.lookup.place(),
            one = key.lookup.looked_up(),
        );
        return Err(computes_refusal(descriptor, computes, reason));
    }
    Ok(())
}

/// The refusal of the construct that computes, `computes`: its class's.
fn computes_refusal(
    descriptor: &Descriptor,
    computes: &Computes<'_>,
    reason: String,
) -> DescriptorLoweringError {
    let item = Box::new(descriptor.id().clone());
    let range = key_range(descriptor, computes.at).map(Box::new);
    if computes.sort_test {
        DescriptorLoweringError::InvalidSortTest {
            item,
            reason,
            range,
        }
    } else {
        DescriptorLoweringError::FunctionInPattern {
            item,
            reason,
            range,
        }
    }
}

/// The reading of a pattern's keys and set elements, by the order matching
/// can bind their names in.
///
/// A key with no construct that computes binds its names as it matches. A
/// key with one is computed and looked up when every name in it is bound
/// first: by a position outside every key, by a key that matches, by the
/// value of an entry already found, or by a collection's remainder once
/// every computed key of the collection is found. Under rewriting the rule
/// applies when some substitution makes its left side equal the term with
/// its functions evaluated; when the keys' names follow such an order,
/// matching is the selections, then the lookups in that order, each of a
/// value already determined. A computed key whose own pattern part holds a
/// name nothing else binds, or `_`, an alias, alternatives or an open
/// record, is a selection instead.
struct Order {
    /// The keys read as selections that compute, with what selects.
    selections: Vec<(usize, String)>,
    /// The keys read as computed and looked up.
    computed: Vec<usize>,
    /// The computed keys no order of lookups resolves.
    cycle: Vec<usize>,
    /// The names bound by the order.
    bound: BTreeSet<String>,
    /// The names some part of the pattern binds, in any order.
    anywhere: BTreeSet<String>,
}

impl Order {
    fn of(pattern: &Pattern<'_>, keys: &[Key<'_, '_>]) -> Self {
        let mut bound: BTreeSet<String> = pattern
            .outside
            .iter()
            .map(|name| (*name).to_owned())
            .collect();
        // The names some part of the pattern other than key `except` binds,
        // in any order.
        let elsewhere = |except: usize| {
            let mut names: BTreeSet<&str> = pattern.outside.iter().copied().collect();
            for (index, (entry, key)) in pattern.entries.iter().zip(keys).enumerate() {
                names.extend(entry.values.iter().copied());
                if index != except {
                    names.extend(key.matched.iter().map(|(name, _)| *name));
                }
            }
            names.extend(pattern.remainders.iter().flatten().copied());
            names
        };
        let mut selections = Vec::new();
        let mut computed = Vec::new();
        for (index, (entry, key)) in pattern.entries.iter().zip(keys).enumerate() {
            let fresh = key
                .matched
                .iter()
                .find(|(name, _)| !elsewhere(index).contains(name));
            let selector = key.selection.clone().or_else(|| {
                fresh.map(|(name, _)| format!("the name `{name}`, which nothing else binds"))
            });
            if key.computes.is_some() && selector.is_none() {
                computed.push(index);
            } else {
                // A key that matches binds its names, and its entry's value.
                if let (Some(_), Some(selector)) = (&key.computes, selector) {
                    selections.push((index, selector));
                }
                bound.extend(key.matched.iter().map(|(name, _)| (*name).to_owned()));
                bound.extend(entry.values.iter().map(|name| (*name).to_owned()));
            }
        }
        // A remainder binds once every computed key of its collection is
        // found.
        let remainder_ready = |found: &BTreeSet<usize>, collection: usize| {
            computed.iter().all(|index| {
                pattern.entries[*index].collection != collection || found.contains(index)
            })
        };
        let mut found = BTreeSet::new();
        loop {
            for (collection, remainder) in pattern.remainders.iter().enumerate() {
                if let Some(remainder) = remainder
                    && remainder_ready(&found, collection)
                {
                    bound.insert((*remainder).to_owned());
                }
            }
            let next = computed.iter().copied().find(|index| {
                !found.contains(index) && keys[*index].names().all(|name| bound.contains(name))
            });
            let Some(index) = next else { break };
            found.insert(index);
            bound.extend(
                pattern.entries[index]
                    .values
                    .iter()
                    .map(|name| (*name).to_owned()),
            );
        }
        let cycle = computed
            .iter()
            .copied()
            .filter(|index| !found.contains(index))
            .collect();
        let anywhere = elsewhere(usize::MAX)
            .into_iter()
            .map(str::to_owned)
            .collect();
        Self {
            selections,
            computed,
            cycle,
            bound,
            anywhere,
        }
    }

    /// The first name an unresolved computed key reads that the pattern
    /// binds nowhere at all: the key reads a value nothing gave.
    fn unbound<'k, 't>(&self, keys: &'k [Key<'_, 't>]) -> Option<(&'k Key<'k, 't>, &'k Read<'t>)> {
        self.cycle.iter().find_map(|index| {
            let key = &keys[*index];
            key.read
                .iter()
                .find(|read| !self.anywhere.contains(read.name))
                .map(|read| (key, read))
        })
    }

    /// The names the unresolved computed keys read, described.
    fn cycle_names(&self, keys: &[Key<'_, '_>]) -> String {
        let names = self
            .cycle
            .iter()
            .flat_map(|index| keys[*index].names())
            .filter(|name| !self.bound.contains(*name))
            .collect::<BTreeSet<_>>();
        names
            .iter()
            .map(|name| format!("`{name}`"))
            .collect::<Vec<_>>()
            .join(", ")
    }
}

/// What a collection is looked up by.
#[derive(Clone, Copy)]
enum Lookup {
    /// A map's key.
    MapKey,
    /// A set's element.
    SetElement,
}

impl Lookup {
    /// The lookup's place, for a diagnostic.
    const fn place(self) -> &'static str {
        match self {
            Self::MapKey => "a map key",
            Self::SetElement => "a set element",
        }
    }

    /// What the collection holds that a selection matches, for a diagnostic.
    const fn held(self) -> &'static str {
        match self {
            Self::MapKey => "the evaluated keys the map holds",
            Self::SetElement => "the evaluated elements the set holds",
        }
    }

    /// What the collection is looked up by, for a diagnostic.
    const fn looked_up(self) -> &'static str {
        match self {
            Self::MapKey => "key",
            Self::SetElement => "element",
        }
    }
}

/// The pattern of one sentence: the names it binds outside its keys and set
/// elements, and those keys and elements with what their entries bind.
struct Pattern<'t> {
    /// The names the pattern binds outside every key, entry value and
    /// remainder.
    outside: BTreeSet<&'t str>,
    /// The keys and set elements, in pattern order.
    entries: Vec<Entry<'t>>,
    /// Each collection's remainder binding, by collection.
    remainders: Vec<Option<&'t str>>,
}

/// One key or set element and its entry.
struct Entry<'t> {
    key: &'t DescriptorTerm,
    lookup: Lookup,
    /// The names its entry's value binds once the entry is found.
    values: Vec<&'t str>,
    /// Its collection.
    collection: usize,
}

impl<'t> Pattern<'t> {
    fn sentence(&mut self, payload: &'t DescriptorPayload) {
        match payload {
            DescriptorPayload::StructuredRule(rule) => {
                self.term(&rule.subject);
                if let Some(context) = &rule.function_context {
                    self.cells(&context.cells);
                }
            }
            DescriptorPayload::HeadRule(rule) => {
                for item in rule.head.iter().flat_map(|head| &head.items) {
                    self.term(item);
                }
                for extra in &rule.extras {
                    self.extra(extra);
                }
            }
            DescriptorPayload::ConfigurationRule(rule) => self.cells(&rule.subject),
            DescriptorPayload::ContextAlias(alias) => self.cells(&alias.pattern),
            _ => {}
        }
    }

    fn cells<I>(&mut self, cells: &'t ProtocolRuleCells<I, DescriptorTerm>) {
        for cell in &cells.cells {
            self.state(&cell.value);
        }
        self.frame(&cells.remainder);
    }

    fn frame(&mut self, frame: &'t ProtocolRuleFrame) {
        if let Some(binding) = binding(frame) {
            self.outside.insert(binding);
        }
    }

    /// A new collection, whose remainder is `remainder`.
    fn collection(&mut self, remainder: Option<&'t str>) -> usize {
        self.remainders.push(remainder);
        self.remainders.len() - 1
    }

    /// The names `term` binds, apart from the pattern's other names.
    fn names_of(&mut self, term: &'t DescriptorTerm) -> Vec<&'t str> {
        let outside = std::mem::take(&mut self.outside);
        self.term(term);
        let names = std::mem::replace(&mut self.outside, outside);
        names.into_iter().collect()
    }

    fn state(&mut self, state: &'t ProtocolRuleStateTerm<DescriptorTerm>) {
        match state {
            ProtocolRuleStateTerm::Map(map) => match &map.body {
                ProtocolRuleMapBody::Items { items, remainder } => {
                    let collection = self.collection(binding(remainder));
                    for item in items {
                        let values = self.names_of(&item.value);
                        self.entries.push(Entry {
                            key: &item.key,
                            lookup: Lookup::MapKey,
                            values,
                            collection,
                        });
                    }
                }
                ProtocolRuleMapBody::Update { base, .. } => self.term(base),
                ProtocolRuleMapBody::Empty { .. } => {}
            },
            ProtocolRuleStateTerm::Present { value } => self.state(value),
            ProtocolRuleStateTerm::KSequence(sequence) => {
                for item in &sequence.items {
                    self.term(&item.value);
                }
                self.frame(&sequence.tail);
            }
            ProtocolRuleStateTerm::Instances(instances) => {
                for term in state.terms() {
                    self.term(term);
                }
                self.frame(&instances.rest);
            }
            ProtocolRuleStateTerm::Term(term) | ProtocolRuleStateTerm::Group(term) => {
                self.term(term);
            }
            ProtocolRuleStateTerm::Absent => {}
        }
    }

    /// The matched side of a readable rule's cell; a map update is what the
    /// result writes, and its base binding names the whole map.
    fn extra(&mut self, extra: &'t DescriptorHeadRuleExtra) {
        match extra {
            ProtocolHeadRuleExtra::HaveMap { entries, .. } => {
                let collection = self.collection(None);
                for entry in entries {
                    self.entries.push(Entry {
                        key: &entry.key,
                        lookup: Lookup::MapKey,
                        values: vec![&entry.value_binding],
                        collection,
                    });
                }
            }
            ProtocolHeadRuleExtra::UpdateMap { base_binding, .. } => {
                self.outside.insert(base_binding);
            }
            ProtocolHeadRuleExtra::RewriteCell { before, .. } => self.term(before),
            ProtocolHeadRuleExtra::RewriteState { before, .. } => self.state(before),
            ProtocolHeadRuleExtra::RewriteList { before, .. } => {
                for term in &before.items {
                    self.term(term);
                }
                if let ProtocolHeadRuleListRest::Term(rest) = &before.rest {
                    self.term(rest);
                }
                for term in &before.back {
                    self.term(term);
                }
            }
        }
    }

    /// A set pattern `term`, one collection: its elements are keys, and a
    /// name beside them is its remainder.
    fn set(&mut self, term: &'t DescriptorTerm) {
        let mut elements = Vec::new();
        let mut remainder = None;
        let mut others = Vec::new();
        set_parts(term, &mut elements, &mut remainder, &mut others);
        let collection = self.collection(remainder);
        for element in elements {
            self.entries.push(Entry {
                key: element,
                lookup: Lookup::SetElement,
                values: Vec::new(),
                collection,
            });
        }
        for other in others {
            self.term(other);
        }
    }

    /// `term`, outside every key: its names are bound, and a set's elements
    /// are keys of their own.
    fn term(&mut self, term: &'t DescriptorTerm) {
        match term {
            DescriptorTerm::Variable { name, .. } => {
                self.outside.insert(name);
            }
            DescriptorTerm::As { name, pattern, .. } => {
                self.outside.insert(name);
                self.term(pattern);
            }
            DescriptorTerm::Application {
                reference,
                arguments,
                ..
            } => {
                if matches!(
                    reference.application,
                    DescriptorApplicationRef::Set(SetOperation::Item | SetOperation::Concat)
                ) {
                    self.set(term);
                    return;
                }
                for value in argument_values(arguments) {
                    self.term(value);
                }
            }
            DescriptorTerm::Or { alternatives, .. } => {
                for alternative in alternatives {
                    self.term(alternative);
                }
            }
            DescriptorTerm::Rewrite { from, .. } => self.term(from),
            DescriptorTerm::Cell { fields, .. } => {
                for field in fields {
                    self.term(&field.value);
                }
            }
            DescriptorTerm::Literal { .. }
            | DescriptorTerm::Wildcard { .. }
            | DescriptorTerm::BuiltinToken { .. }
            | DescriptorTerm::Anonymous { .. }
            | DescriptorTerm::OrBool { .. }
            | DescriptorTerm::Lexeme { .. }
            | DescriptorTerm::SortTest { .. }
            | DescriptorTerm::Matches { .. }
            | DescriptorTerm::Let { .. }
            | DescriptorTerm::Closure { .. } => {}
        }
    }
}

/// A frame's binding, when it names one.
fn binding(frame: &ProtocolRuleFrame) -> Option<&str> {
    match frame {
        ProtocolRuleFrame::Bind { binding, .. } => Some(binding),
        _ => None,
    }
}

/// The parts of a set pattern: its elements, the name beside them (its
/// remainder), and its other operands.
fn set_parts<'t>(
    term: &'t DescriptorTerm,
    elements: &mut Vec<&'t DescriptorTerm>,
    remainder: &mut Option<&'t str>,
    others: &mut Vec<&'t DescriptorTerm>,
) {
    match term {
        DescriptorTerm::Application {
            reference,
            arguments,
            ..
        } if reference.application == DescriptorApplicationRef::Set(SetOperation::Item) => {
            elements.extend(argument_values(arguments));
        }
        DescriptorTerm::Application {
            reference,
            arguments,
            ..
        } if reference.application == DescriptorApplicationRef::Set(SetOperation::Concat) => {
            for operand in argument_values(arguments) {
                set_parts(operand, elements, remainder, others);
            }
        }
        DescriptorTerm::Variable { name, .. } if remainder.is_none() => *remainder = Some(name),
        other => others.push(other),
    }
}

/// The values of an application's arguments.
fn argument_values(
    arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
) -> impl Iterator<Item = &DescriptorTerm> {
    arguments.into_iter().map(|argument| {
        let (TermArgumentRef::Positional { value } | TermArgumentRef::Named { value, .. }) =
            argument;
        value
    })
}

/// One key or set element, as its walk finds it.
struct Key<'a, 't> {
    catalog: &'a BTreeMap<StableItemId, ProductionSignature>,
    lookup: Lookup,
    /// The names its matched part holds, outside every construct that
    /// computes, with their keys.
    matched: Vec<(&'t str, &'t ProvenanceKey)>,
    /// What makes it a selection by its own shape: the first `_`, alias,
    /// alternatives or open record outside every construct that computes,
    /// described. A name nothing else binds does too ([`Order`]).
    selection: Option<String>,
    /// The first construct that computes in it.
    computes: Option<Computes<'t>>,
    /// The first pattern-only construct below a construct that computes, its
    /// key, and the construct above it, described.
    built: Option<(KeyPattern, &'t ProvenanceKey, String)>,
    /// The names it reads below a construct that computes.
    read: Vec<Read<'t>>,
}

/// A construct that computes, where it stands, described.
struct Computes<'t> {
    at: &'t ProvenanceKey,
    what: String,
    sort_test: bool,
}

/// A name a key reads below a construct that computes.
struct Read<'t> {
    name: &'t str,
    key: &'t ProvenanceKey,
    /// The innermost construct above the name that computes, described.
    function: String,
}

impl<'t> Key<'_, 't> {
    /// Every name the key holds: its matched part's and those it reads.
    fn names(&self) -> impl Iterator<Item = &'t str> + '_ {
        self.matched
            .iter()
            .map(|(name, _)| *name)
            .chain(self.read.iter().map(|read| read.name))
    }

    /// A pattern-only `construct` at `at`: built below `computing`, a
    /// selection otherwise.
    fn pattern_only(
        &mut self,
        construct: KeyPattern,
        at: &'t ProvenanceKey,
        computing: Option<&str>,
        selector: impl FnOnce() -> String,
    ) {
        match computing {
            Some(function) => {
                if self.built.is_none() {
                    self.built = Some((construct, at, function.to_owned()));
                }
            }
            None => {
                if self.selection.is_none() {
                    self.selection = Some(selector());
                }
            }
        }
    }

    /// The first construct that computes.
    fn computes(&mut self, at: &'t ProvenanceKey, what: &str, sort_test: bool) {
        if self.computes.is_none() {
            self.computes = Some(Computes {
                at,
                what: what.to_owned(),
                sort_test,
            });
        }
    }

    /// `term`, below the innermost construct that computes, `computing`, or
    /// in the key's matched part when `None`.
    fn term(&mut self, term: &'t DescriptorTerm, computing: Option<&str>) {
        match term {
            DescriptorTerm::Variable { key, name, .. } => {
                if let Some(function) = computing {
                    self.read.push(Read {
                        name,
                        key,
                        function: function.to_owned(),
                    });
                } else {
                    self.matched.push((name, key));
                }
            }
            DescriptorTerm::Wildcard { key } => {
                self.pattern_only(KeyPattern::Wildcard, key, computing, || "`_`".to_owned());
            }
            DescriptorTerm::As {
                binding_key,
                name,
                pattern,
                ..
            } => {
                self.pattern_only(KeyPattern::Alias, binding_key, computing, || {
                    format!("the alias `{name} @ ..`")
                });
                if computing.is_none() {
                    self.matched.push((name, binding_key));
                }
                self.term(pattern, computing);
            }
            DescriptorTerm::Or { key, alternatives } => {
                self.pattern_only(KeyPattern::Alternatives, key, computing, || {
                    "alternatives `A | B`".to_owned()
                });
                for alternative in alternatives {
                    self.term(alternative, computing);
                }
            }
            DescriptorTerm::Application {
                reference,
                arguments,
                open,
                update,
                ..
            } => self.application(reference, arguments, *open, update.is_some(), computing),
            DescriptorTerm::SortTest { key, operand, .. } => {
                self.computes(key, "a sort test", true);
                self.term(operand, Some("a sort test"));
            }
            DescriptorTerm::Rewrite { from, .. } => self.term(from, computing),
            DescriptorTerm::Cell { fields, .. } => {
                for field in fields {
                    self.term(&field.value, computing);
                }
            }
            DescriptorTerm::Literal { .. }
            | DescriptorTerm::BuiltinToken { .. }
            | DescriptorTerm::Anonymous { .. }
            | DescriptorTerm::OrBool { .. }
            | DescriptorTerm::Lexeme { .. }
            | DescriptorTerm::Matches { .. }
            | DescriptorTerm::Let { .. }
            | DescriptorTerm::Closure { .. } => {}
        }
    }

    fn application(
        &mut self,
        reference: &'t DescriptorApplicationReference,
        arguments: &'t krs_ir::Arguments<krs_ir::DescriptorStage>,
        open: bool,
        update: bool,
        computing: Option<&str>,
    ) {
        if open {
            self.pattern_only(KeyPattern::OpenRecord, &reference.key, computing, || {
                "an open record `Ctor { .. }`".to_owned()
            });
        }
        let applied = applied_function(&reference.application, self.catalog);
        let below = match &applied {
            Applied::Function(function) => {
                self.computes(&reference.key, function, false);
                Some(function.clone())
            }
            // A record update builds its record from a matched one.
            _ if update => Some("a record update".to_owned()),
            _ => computing.map(str::to_owned),
        };
        for value in argument_values(arguments) {
            self.term(value, below.as_deref());
        }
    }
}
