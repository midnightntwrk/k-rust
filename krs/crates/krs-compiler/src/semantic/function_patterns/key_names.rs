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
//! elements as a map by its keys (`set::item(e)` in a set pattern), and for
//! a Set cell collection, a set of its instances, which is looked up by an
//! instance as by an element: the instance's cells, all of them written
//! (no `..` in the instance), are the element's value, and a `..` that
//! leaves its other cells open selects as a name nothing else binds does.
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
    CellCollectionType, Descriptor, DescriptorApplicationRef, DescriptorApplicationReference,
    DescriptorCellIdentity, DescriptorHeadRule, DescriptorHeadRuleExtra, DescriptorIndex,
    DescriptorPayload, DescriptorTerm, ProtocolHeadRuleExtra, ProtocolHeadRuleListRest,
    ProtocolInstanceRest, ProtocolRecordRest, ProtocolRuleCells, ProtocolRuleFrame,
    ProtocolRuleInstance, ProtocolRuleMapBody, ProtocolRuleStateTerm, ProvenanceKey, SetOperation,
    StableItemId, TermArgumentRef,
};

use super::{
    Applied, DescriptorLoweringError, ProductionSignature, applied_function, collection_type,
    key_range, matches_evaluated_sentence,
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
    declarations: &DescriptorIndex<'_>,
) -> Result<(), DescriptorLoweringError> {
    let payload = descriptor.payload();
    if !matches_evaluated_sentence(payload) {
        return Ok(());
    }
    let mut pattern = Pattern {
        declarations,
        outside: BTreeSet::new(),
        entries: Vec::new(),
        remainders: Vec::new(),
        alternatives: Vec::new(),
    };
    pattern.sentence(payload);
    judge(descriptor, &pattern, catalog)
}

/// Refuses what [`check`] refuses, in the readable rule `rule` before it is elaborated, when one
/// of its keys, set elements or Set collection instances holds a construct the elaboration
/// rewrites there: an open constructor record `Ctor { f: e, .. }`, a record update
/// `Ctor { f: e, ..base }`, or an alias `name @ pattern` or its name.
///
/// This check reads each of them where it stands in a key: a pattern-only construct below what
/// the key computes is built, one outside it makes the key a selection, and an update computes.
/// The elaborated rule says none of them as written. It names every field of a constructor's
/// record, `_` for one a pattern leaves out, takes an update's fields from its base, drops an
/// alias used only as a base, names every child of a labelled group record, and rebuilds a whole
/// use of a group alias from its children. `cells!` notation writes no open constructor record
/// and no update, and those rewrites of an alias follow from the updates. So such a key is
/// judged as written here. A rule whose keys hold none of them keeps its keys as written, and is
/// the elaborated rule's to judge ([`check`]).
///
/// # Errors
///
/// As [`check`].
pub(in crate::semantic) fn check_readable(
    descriptor: &Descriptor,
    rule: &DescriptorHeadRule,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
    declarations: &DescriptorIndex<'_>,
) -> Result<(), DescriptorLoweringError> {
    if !matches_evaluated_sentence(descriptor.payload()) {
        return Ok(());
    }
    let mut pattern = Pattern {
        declarations,
        outside: BTreeSet::new(),
        entries: Vec::new(),
        remainders: Vec::new(),
        alternatives: Vec::new(),
    };
    pattern.readable_rule(rule);
    let mut aliases = BTreeSet::new();
    for term in crate::semantic::rules::head_rule_terms(rule) {
        alias_names(term, &mut aliases);
    }
    let rewritten = pattern.entries.iter().any(|entry| match &entry.key {
        EntryKey::Term(term) => readable_only(term, &aliases),
        EntryKey::Instance(instance) => instance
            .fields
            .iter()
            .flat_map(|field| field.value.terms())
            .any(|term| readable_only(term, &aliases)),
    });
    if !rewritten {
        return Ok(());
    }
    judge(descriptor, &pattern, catalog)
}

/// Every name an alias `name @ pattern` in `term` binds.
fn alias_names<'t>(term: &'t DescriptorTerm, names: &mut BTreeSet<&'t str>) {
    if let DescriptorTerm::As { name, .. } = term {
        names.insert(name);
    }
    for child in children(term) {
        alias_names(child, names);
    }
}

/// Whether `term` holds an open constructor record, a record update, an alias, or a name one of
/// `aliases` binds ([`check_readable`]).
fn readable_only(term: &DescriptorTerm, aliases: &BTreeSet<&str>) -> bool {
    let here = match term {
        DescriptorTerm::Application { open, update, .. }
        | DescriptorTerm::Cell { open, update, .. } => *open || update.is_some(),
        DescriptorTerm::As { .. } => true,
        DescriptorTerm::Variable { name, .. } => aliases.contains(name.as_str()),
        _ => false,
    };
    here || children(term)
        .into_iter()
        .any(|child| readable_only(child, aliases))
}

/// The direct subterms of `term`.
fn children(term: &DescriptorTerm) -> Vec<&DescriptorTerm> {
    match term {
        DescriptorTerm::Application {
            arguments, update, ..
        } => argument_values(arguments)
            .chain(update.as_deref())
            .collect(),
        DescriptorTerm::Cell { fields, update, .. } => fields
            .iter()
            .map(|field| &*field.value)
            .chain(update.as_deref())
            .collect(),
        DescriptorTerm::As { pattern, .. } => vec![pattern],
        DescriptorTerm::OrBool { arguments, .. } => arguments.iter().collect(),
        DescriptorTerm::Or { alternatives, .. } => alternatives.iter().collect(),
        DescriptorTerm::MapEntries { entries, rest, .. } => entries
            .iter()
            .flat_map(|entry| [&*entry.key, &*entry.value])
            .chain(rest.as_deref())
            .collect(),
        DescriptorTerm::SortTest { operand, .. } => vec![operand],
        DescriptorTerm::Matches {
            subject, pattern, ..
        } => vec![subject, pattern],
        DescriptorTerm::Let {
            pattern,
            value,
            body,
            ..
        } => vec![pattern, value, body],
        DescriptorTerm::Closure { body, .. } => vec![body],
        DescriptorTerm::Rewrite { from, to, .. } => {
            std::iter::once(&**from).chain(to.as_deref()).collect()
        }
        DescriptorTerm::Variable { .. }
        | DescriptorTerm::Literal { .. }
        | DescriptorTerm::Wildcard { .. }
        | DescriptorTerm::KeptRest { .. }
        | DescriptorTerm::BuiltinToken { .. }
        | DescriptorTerm::Anonymous { .. }
        | DescriptorTerm::Lexeme { .. } => Vec::new(),
    }
}

/// The refusals of [`check`] over `pattern`, the pattern of `descriptor`'s sentence.
fn judge(
    descriptor: &Descriptor,
    pattern: &Pattern<'_, '_>,
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<(), DescriptorLoweringError> {
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
                alternatives: Vec::new(),
            };
            key.entry(&entry.key);
            key
        })
        .collect::<Vec<_>>();
    let order = Order::of(pattern, &keys);
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
    // Alternatives that bind a name another alternative does not, which no other position of
    // the pattern binds: a name a computed key reads is bound by nothing there.
    if let Some((alternatives, name)) = pattern
        .alternatives
        .iter()
        .chain(keys.iter().flat_map(|key| &key.alternatives))
        .find_map(|alternatives| Some((alternatives, alternatives.unbound(&order.anywhere)?)))
    {
        return Err(DescriptorLoweringError::AlternativesBindUnequally {
            item: item(),
            reason: format!("variable `{name}` is not bound in all alternatives"),
            range: key_range(descriptor, alternatives.at).map(Box::new),
        });
    }
    if let Some((key, read)) = order.unbound(&keys) {
        let why = match key.lookup {
            Lookup::MapKey => "a key is evaluated to look its entry up, so the key",
            Lookup::SetElement => {
                "an element is evaluated to look it up in the set, so the element"
            }
            Lookup::Instance => {
                "an instance is evaluated to look it up in the collection, so the instance"
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
        let reason = match computes.construct {
            Computing::Let | Computing::Matches => local_selection_reason(key, selector, computes),
            Computing::Function | Computing::SortTest => selection_reason(key, selector, computes),
        };
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

/// Why a construct that computes, `computes`, never matches in `key`, which
/// `selector` makes a selection.
fn selection_reason(key: &Key<'_, '_>, selector: &str, computes: &Computes<'_>) -> String {
    match key.lookup {
        // A selection instance is matched cells, as a Map or a List
        // collection's instance is.
        Lookup::Instance => format!(
            "{what} stands in {place} that also holds {selector}, so the instance selects one by matching {held} as they stand, rather than computing the instance looked up; {what} denotes the value evaluation produces, which no cell of an instance holds, so this pattern describes an instance that never occurs and the sentence never applies: bind the selected part elsewhere in the pattern and write every cell to look the instance up, or match a variable here and relate it to the application in a guard (`requires`)",
            what = computes.what,
            place = key.lookup.place(),
            held = key.lookup.held(),
        ),
        Lookup::MapKey | Lookup::SetElement => format!(
            "{what} stands in {place} that also holds {selector}, so the key selects an entry by matching {held} rather than computing the {looked} looked up; {what} denotes the value evaluation produces, which no evaluated {one} is, so the key never matches: bind the selected part elsewhere in the pattern to look the entry up, or match a variable here and relate it to the application in a guard (`requires`)",
            what = computes.what,
            place = key.lookup.place(),
            held = key.lookup.held(),
            looked = key.lookup.looked_up(),
            one = key.lookup.looked_up(),
        ),
    }
}

/// Why a `let` block or `k::matches!`, `computes`, is refused in `key`, which `selector` makes a
/// selection: a selection binds its names by matching the entries the collection holds, and KRS
/// computes a construct only in a key or an instance whose names the pattern binds elsewhere.
fn local_selection_reason(key: &Key<'_, '_>, selector: &str, computes: &Computes<'_>) -> String {
    let what = &computes.what;
    let place = key.lookup.place();
    let held = key.lookup.held();
    match key.lookup {
        Lookup::Instance => format!(
            "{what} stands in {place} that also holds {selector}, so the instance selects one by matching {held} as they stand, rather than computing the instance looked up; KRS computes {what} only in an instance whose every cell is written and computed from names the pattern binds elsewhere, and does not solve a selection for the names {what} reads: bind the selected part elsewhere in the pattern and write every cell to look the instance up, or match a variable here and relate it to that value in the sentence's condition"
        ),
        Lookup::MapKey | Lookup::SetElement => format!(
            "{what} stands in {place} that also holds {selector}, so the key selects an entry by matching {held} rather than computing the {looked} looked up; KRS computes {what} only in a key whose every other name the pattern binds elsewhere, and does not solve a selection for the names {what} reads: bind the selected part elsewhere in the pattern so the key is computed and looked up, or match a variable here and relate it to that value in the sentence's condition",
            looked = key.lookup.looked_up(),
        ),
    }
}

/// The refusal of the construct that computes, `computes`: its class's.
fn computes_refusal(
    descriptor: &Descriptor,
    computes: &Computes<'_>,
    reason: String,
) -> DescriptorLoweringError {
    let item = Box::new(descriptor.id().clone());
    let range = key_range(descriptor, computes.at).map(Box::new);
    match computes.construct {
        Computing::SortTest => DescriptorLoweringError::InvalidSortTest {
            item,
            reason,
            range,
        },
        Computing::Function => DescriptorLoweringError::FunctionInPattern {
            item,
            reason,
            range,
        },
        Computing::Let | Computing::Matches => DescriptorLoweringError::LocalFunctionInPattern {
            item,
            reason,
            matches: computes.construct == Computing::Matches,
            range,
        },
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
    fn of(pattern: &Pattern<'_, '_>, keys: &[Key<'_, '_>]) -> Self {
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
    /// A Set cell collection's instance, the collection's element.
    Instance,
}

impl Lookup {
    /// The lookup's place, for a diagnostic.
    const fn place(self) -> &'static str {
        match self {
            Self::MapKey => "a map key",
            Self::SetElement => "a set element",
            Self::Instance => "a Set collection's instance",
        }
    }

    /// What the collection holds that a selection matches, for a diagnostic.
    const fn held(self) -> &'static str {
        match self {
            Self::MapKey => "the evaluated keys the map holds",
            Self::SetElement => "the evaluated elements the set holds",
            Self::Instance => "the instances the collection holds",
        }
    }

    /// What the collection is looked up by, for a diagnostic.
    const fn looked_up(self) -> &'static str {
        match self {
            Self::MapKey => "key",
            Self::SetElement => "element",
            Self::Instance => "instance",
        }
    }
}

/// The pattern of one sentence: the names it binds outside its keys and set
/// elements, and those keys and elements with what their entries bind.
struct Pattern<'t, 'd> {
    /// The cells' declarations, which tell a Set collection.
    declarations: &'d DescriptorIndex<'d>,
    /// The names the pattern binds outside every key, entry value and
    /// remainder.
    outside: BTreeSet<&'t str>,
    /// The keys and set elements, in pattern order.
    entries: Vec<Entry<'t>>,
    /// Each collection's remainder binding, by collection.
    remainders: Vec<Option<&'t str>>,
    /// The or-patterns outside every key, with what each alternative binds.
    alternatives: Vec<Alternatives<'t>>,
}

/// An `A | B` of the pattern and the names each alternative binds where it stands. Every match
/// binds only the names all the alternatives bind; a name some alternative binds and another
/// does not is bound by the match only where another position binds it, a use in each
/// alternative then (nonlinear matching).
struct Alternatives<'t> {
    at: &'t ProvenanceKey,
    held: Vec<BTreeSet<&'t str>>,
}

impl<'t> Alternatives<'t> {
    /// The names every alternative binds.
    fn every(&self) -> BTreeSet<&'t str> {
        let mut held = self.held.iter();
        let first = held.next().cloned().unwrap_or_default();
        held.fold(first, |every, names| {
            every.intersection(names).copied().collect()
        })
    }

    /// The first name, in alternative order, that some alternative binds, another does not,
    /// and no position of the pattern outside the alternatives binds (`bound`).
    fn unbound(&self, bound: &BTreeSet<String>) -> Option<&'t str> {
        let every = self.every();
        self.held
            .iter()
            .flatten()
            .copied()
            .find(|name| !every.contains(name) && !bound.contains(*name))
    }
}

/// One key or set element and its entry.
struct Entry<'t> {
    key: EntryKey<'t>,
    lookup: Lookup,
    /// The names its entry's value binds once the entry is found.
    values: Vec<&'t str>,
    /// Its collection.
    collection: usize,
}

/// What a collection is looked up by: a term, or a Set collection's
/// instance, whose cells together are the element.
enum EntryKey<'t> {
    Term(&'t DescriptorTerm),
    Instance(&'t ProtocolRuleInstance<DescriptorTerm>),
}

impl<'t> Pattern<'t, '_> {
    fn sentence(&mut self, payload: &'t DescriptorPayload) {
        match payload {
            DescriptorPayload::StructuredRule(rule) => {
                self.term(&rule.subject);
                if let Some(context) = &rule.function_context {
                    self.cells(&context.cells);
                }
            }
            DescriptorPayload::ConfigurationRule(rule) => self.cells(&rule.subject),
            DescriptorPayload::ContextAlias(alias) => self.cells(&alias.pattern),
            _ => {}
        }
    }

    /// A readable rule's pattern, as the author wrote it ([`check_readable`]): the computation's
    /// items, then each extra's matched side.
    fn readable_rule(&mut self, rule: &'t DescriptorHeadRule) {
        for item in rule.head.iter().flat_map(|head| &head.items) {
            self.term(item);
        }
        for extra in &rule.extras {
            self.extra(extra);
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
                        key: EntryKey::Term(&entry.key),
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
            ProtocolHeadRuleExtra::RewriteState { cell, before, .. } => {
                self.state(Some(&cell.cell), before);
            }
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

    fn cells(
        &mut self,
        cells: &'t ProtocolRuleCells<krs_ir::DescriptorCellReference, DescriptorTerm>,
    ) {
        for cell in &cells.cells {
            self.state(Some(&cell.field.cell), &cell.value);
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

    /// The state of the cell `cell` names, when it names one.
    fn state(
        &mut self,
        cell: Option<&DescriptorCellIdentity>,
        state: &'t ProtocolRuleStateTerm<DescriptorTerm>,
    ) {
        match state {
            ProtocolRuleStateTerm::Map(map) => match &map.body {
                ProtocolRuleMapBody::Items { items, remainder } => {
                    let collection = self.collection(binding(remainder));
                    for item in items {
                        let values = self.names_of(&item.value);
                        self.entries.push(Entry {
                            key: EntryKey::Term(&item.key),
                            lookup: Lookup::MapKey,
                            values,
                            collection,
                        });
                    }
                }
                ProtocolRuleMapBody::Update { base, .. } => self.term(base),
                ProtocolRuleMapBody::Empty { .. } => {}
            },
            ProtocolRuleStateTerm::Present { value } => self.state(cell, value),
            ProtocolRuleStateTerm::KSequence(sequence) => {
                for item in &sequence.items {
                    self.term(&item.value);
                }
                self.frame(&sequence.tail);
            }
            // A Set collection is a set of its instances, each the element it is looked up by;
            // a Map and a List collection's instances are matched.
            ProtocolRuleStateTerm::Instances(instances)
                if cell.is_some_and(|cell| {
                    collection_type(self.declarations, cell) == Some(CellCollectionType::Set)
                }) =>
            {
                let collection = self.collection(binding(&instances.rest));
                for instance in instances.front.iter().chain(&instances.back) {
                    self.entries.push(Entry {
                        key: EntryKey::Instance(instance),
                        lookup: Lookup::Instance,
                        values: Vec::new(),
                        collection,
                    });
                }
            }
            ProtocolRuleStateTerm::Instances(instances) => {
                for term in state.terms() {
                    self.term(term);
                }
                self.frame(&instances.rest);
            }
            // A group record's children, as an instance's; its head is no term of the state.
            ProtocolRuleStateTerm::Record(_) => {
                for term in state.terms() {
                    self.term(term);
                }
            }
            ProtocolRuleStateTerm::Term(term) | ProtocolRuleStateTerm::Group(term) => {
                self.term(term);
            }
            ProtocolRuleStateTerm::Absent => {}
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
                key: EntryKey::Term(element),
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
            // Every match binds only what all the alternatives bind.
            DescriptorTerm::Or { key, alternatives } => {
                let held = alternatives
                    .iter()
                    .map(|alternative| self.names_of(alternative).into_iter().collect())
                    .collect();
                let alternatives = Alternatives { at: key, held };
                self.outside.extend(alternatives.every());
                self.alternatives.push(alternatives);
            }
            DescriptorTerm::Rewrite { from, .. } => self.term(from),
            DescriptorTerm::Cell { fields, .. } => {
                for field in fields {
                    self.term(&field.value);
                }
            }
            // A map pattern is one collection, as a cell's map is: its keys are what the map
            // is looked up by, its values bind once their entries are found, and a named rest
            // is its remainder.
            DescriptorTerm::MapEntries { entries, rest, .. } => {
                let remainder = match rest.as_deref() {
                    Some(DescriptorTerm::Variable { name, .. }) => Some(name.as_str()),
                    _ => None,
                };
                let collection = self.collection(remainder);
                for entry in entries {
                    let values = self.names_of(&entry.value);
                    self.entries.push(Entry {
                        key: EntryKey::Term(&entry.key),
                        lookup: Lookup::MapKey,
                        values,
                        collection,
                    });
                }
            }
            DescriptorTerm::Literal { .. }
            | DescriptorTerm::Wildcard { .. }
            | DescriptorTerm::KeptRest { .. }
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
    /// The or-patterns of its matched part, with what each alternative binds.
    alternatives: Vec<Alternatives<'t>>,
}

/// A construct that computes, where it stands, described.
struct Computes<'t> {
    at: &'t ProvenanceKey,
    what: String,
    construct: Computing,
}

/// What kind of construct computes, which names its class where the key never matches it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Computing {
    /// A function's application, an operator or a method.
    Function,
    /// `k::is!` or `k::project!`.
    SortTest,
    /// A `let` block, the application of a function generated for it.
    Let,
    /// `k::matches!`, the application of a function generated for it.
    Matches,
}

/// A name a key reads below a construct that computes.
struct Read<'t> {
    name: &'t str,
    key: &'t ProvenanceKey,
    /// The innermost construct above the name that computes, described.
    function: String,
}

impl<'t> Key<'_, 't> {
    /// The key `entry`: a term, or each cell of an instance, all of which a
    /// Set collection's element holds, so an instance that leaves cells open
    /// selects.
    fn entry(&mut self, entry: &EntryKey<'t>) {
        let instance = match entry {
            EntryKey::Term(term) => return self.term(term, None),
            EntryKey::Instance(instance) => instance,
        };
        if matches!(instance.rest, ProtocolInstanceRest::Open) {
            self.select("`..`, which leaves the instance's other cells open");
        }
        for field in &instance.fields {
            self.cell_state(&field.value);
        }
    }

    /// One cell's state in an instance: its terms, and a sequence's items, of
    /// which a `..` leaves the others open.
    fn cell_state(&mut self, state: &'t ProtocolRuleStateTerm<DescriptorTerm>) {
        match state {
            ProtocolRuleStateTerm::Term(term) | ProtocolRuleStateTerm::Group(term) => {
                self.term(term, None);
            }
            ProtocolRuleStateTerm::KSequence(sequence) => {
                if !matches!(sequence.tail, ProtocolRuleFrame::Exact) {
                    self.select("`..` in a cell's sequence, which leaves its other items open");
                }
                for item in &sequence.items {
                    self.term(&item.value, None);
                }
            }
            ProtocolRuleStateTerm::Present { value } => self.cell_state(value),
            // A group record's children, each one cell's state; its head is no term of the state.
            ProtocolRuleStateTerm::Record(record) => {
                if matches!(record.rest, ProtocolRecordRest::Open) {
                    self.select("`..`, which leaves the group's other cells open");
                }
                for field in &record.fields {
                    self.cell_state(&field.value);
                }
            }
            // An exact map is the value its entries write; `..` leaves its
            // other entries open.
            ProtocolRuleStateTerm::Map(map) => match &map.body {
                ProtocolRuleMapBody::Empty { .. } => {}
                ProtocolRuleMapBody::Items { items, remainder } => {
                    if !matches!(remainder, ProtocolRuleFrame::Exact) {
                        self.select("`..` in a cell's map, which leaves its other entries open");
                    }
                    for item in items {
                        self.term(&item.key, None);
                        self.term(&item.value, None);
                    }
                }
                ProtocolRuleMapBody::Update { .. } => {
                    self.select("a map update, which a result writes and no pattern matches");
                    for term in state.terms() {
                        self.term(term, None);
                    }
                }
            },
            // An instance record names no optional or collection child, which
            // lowering refuses; such a cell matches among what it holds.
            ProtocolRuleStateTerm::Absent | ProtocolRuleStateTerm::Instances(_) => {
                self.select("an optional or collection cell, which an instance record cannot name");
                for term in state.terms() {
                    self.term(term, None);
                }
            }
        }
    }

    /// Makes the key a selection by `selector`, unless something else did first.
    fn select(&mut self, selector: &str) {
        if self.selection.is_none() {
            self.selection = Some(selector.to_owned());
        }
    }

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
    fn computes(&mut self, at: &'t ProvenanceKey, what: &str, construct: Computing) {
        if self.computes.is_none() {
            self.computes = Some(Computes {
                at,
                what: what.to_owned(),
                construct,
            });
        }
    }

    /// `body`, below the `let` block or `k::matches!` described `what`, whose pattern binds
    /// `pattern`'s names: the names it reads other than those are the key's.
    fn local_body(&mut self, body: &'t DescriptorTerm, pattern: &'t DescriptorTerm, what: &str) {
        let mut local = BTreeSet::new();
        local_names(pattern, &mut local);
        let before = self.read.len();
        self.term(body, Some(what));
        let read = self
            .read
            .drain(before..)
            .filter(|read| !local.contains(read.name))
            .collect::<Vec<_>>();
        self.read.extend(read);
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
            DescriptorTerm::KeptRest { key } => {
                self.pattern_only(KeyPattern::Wildcard, key, computing, || "`..`".to_owned());
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
                self.alternatives(key, alternatives, computing);
            }
            DescriptorTerm::Application {
                reference,
                arguments,
                open,
                update,
                ..
            } => self.application(reference, arguments, *open, update.is_some(), computing),
            DescriptorTerm::SortTest { key, operand, .. } => {
                self.computes(key, "a sort test", Computing::SortTest);
                self.term(operand, Some("a sort test"));
            }
            DescriptorTerm::Rewrite { from, .. } => self.term(from, computing),
            // A map pattern matches a map's entries and leaves the others to its rest: a
            // pattern's construct, which makes the key a selection, and means nothing in a
            // position the key computes.
            DescriptorTerm::MapEntries { key, entries, rest } => {
                self.pattern_only(KeyPattern::MapPattern, key, computing, || {
                    "a map pattern `map![k -> v, ..]`".to_owned()
                });
                for entry in entries {
                    self.term(&entry.key, computing);
                    self.term(&entry.value, computing);
                }
                if let Some(rest) = rest {
                    self.term(rest, computing);
                }
            }
            // A group's cells are part of the value; `..` leaves some open.
            DescriptorTerm::Cell {
                key, fields, open, ..
            } => {
                if *open {
                    self.pattern_only(KeyPattern::OpenRecord, key, computing, || {
                        "an open record `Ctor { .. }`".to_owned()
                    });
                }
                for field in fields {
                    self.term(&field.value, computing);
                }
            }
            // A `let` block and `k::matches!` compute their value from the names they read,
            // outside their patterns, whose names are their own.
            DescriptorTerm::Let {
                key,
                pattern,
                value,
                body,
                ..
            } => {
                let what = "a `let` block";
                self.computes(key, what, Computing::Let);
                self.term(value, Some(what));
                self.local_body(body, pattern, what);
            }
            DescriptorTerm::Matches { key, subject, .. } => {
                let what = "`k::matches!`";
                self.computes(key, what, Computing::Matches);
                self.term(subject, Some(what));
            }
            DescriptorTerm::Literal { .. }
            | DescriptorTerm::BuiltinToken { .. }
            | DescriptorTerm::Anonymous { .. }
            | DescriptorTerm::OrBool { .. }
            | DescriptorTerm::Lexeme { .. }
            | DescriptorTerm::Closure { .. } => {}
        }
    }

    /// `A | B` at `key`, below `computing`: a selection where the key matches, which binds
    /// only what all the alternatives bind.
    fn alternatives(
        &mut self,
        key: &'t ProvenanceKey,
        alternatives: &'t krs_ir::AtLeastTwo<DescriptorTerm>,
        computing: Option<&str>,
    ) {
        self.pattern_only(KeyPattern::Alternatives, key, computing, || {
            "alternatives `A | B`".to_owned()
        });
        let start = self.matched.len();
        let mut held = Vec::new();
        for alternative in alternatives {
            let before = self.matched.len();
            self.term(alternative, computing);
            held.push(
                self.matched[before..]
                    .iter()
                    .map(|(name, _)| *name)
                    .collect(),
            );
        }
        if computing.is_none() {
            let alternatives = Alternatives { at: key, held };
            let every = alternatives.every();
            let mut position = 0;
            self.matched.retain(|(name, _)| {
                let kept = position < start || every.contains(name);
                position += 1;
                kept
            });
            self.alternatives.push(alternatives);
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
                self.computes(&reference.key, function, Computing::Function);
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

/// Every name `pattern`, a `let` pattern, binds.
fn local_names<'t>(pattern: &'t DescriptorTerm, names: &mut BTreeSet<&'t str>) {
    match pattern {
        DescriptorTerm::Variable { name, .. } => {
            names.insert(name);
        }
        DescriptorTerm::As { name, pattern, .. } => {
            names.insert(name);
            local_names(pattern, names);
        }
        DescriptorTerm::Or { alternatives, .. } => {
            for alternative in alternatives {
                local_names(alternative, names);
            }
        }
        DescriptorTerm::Application { arguments, .. } => {
            for value in argument_values(arguments) {
                local_names(value, names);
            }
        }
        DescriptorTerm::Cell { fields, .. } => {
            for field in fields {
                local_names(&field.value, names);
            }
        }
        _ => {}
    }
}
