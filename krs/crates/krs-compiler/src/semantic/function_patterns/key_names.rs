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
/// below a construct a key computes, then the first name a key reads that the
/// pattern binds nowhere else, then the first construct that computes in a
/// key that is a selection.
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
        keys: Vec::new(),
    };
    pattern.sentence(payload);
    let keys = pattern
        .keys
        .iter()
        .map(|(term, lookup)| {
            let mut key = Key {
                catalog,
                outside: &pattern.outside,
                lookup: *lookup,
                matched: BTreeSet::new(),
                selection: None,
                computes: None,
                built: None,
                read: Vec::new(),
            };
            key.term(term, None);
            key
        })
        .collect::<Vec<_>>();
    let item = || Box::new(descriptor.id().clone());
    if let Some(key) = keys.iter().find(|key| key.built.is_some()) {
        let (construct, at, function) = key.built.as_ref().expect("found");
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
    let unbound = keys.iter().find_map(|key| {
        key.read
            .iter()
            .find(|read| !key.outside.contains(read.name) && !key.matched.contains(read.name))
            .map(|read| (key, read))
    });
    if let Some((key, read)) = unbound {
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
    let selection = keys
        .iter()
        .find_map(|key| Some((key, key.selection.as_ref()?, key.computes.as_ref()?)));
    let Some((key, selector, computes)) = selection else {
        return Ok(());
    };
    let reason = format!(
        "{what} stands in {place} that also holds {selector}, so the key selects an entry by matching the evaluated keys the collection holds rather than computing the key looked up; {what} denotes the value evaluation produces, which no evaluated key is, so the key never matches: bind the selected part elsewhere in the pattern to look the entry up, or match a variable here and relate it to the application in a guard (`requires`)",
        what = computes.what,
        place = key.lookup.place(),
    );
    let range = key_range(descriptor, computes.at).map(Box::new);
    Err(if computes.sort_test {
        DescriptorLoweringError::InvalidSortTest {
            item: item(),
            reason,
            range,
        }
    } else {
        DescriptorLoweringError::FunctionInPattern {
            item: item(),
            reason,
            range,
        }
    })
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
}

/// The pattern of one sentence: the names it binds outside its keys and set
/// elements, and those keys and elements.
struct Pattern<'t> {
    /// The names the pattern binds outside every key and set element.
    outside: BTreeSet<&'t str>,
    /// The keys and set elements, in pattern order.
    keys: Vec<(&'t DescriptorTerm, Lookup)>,
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
        if let ProtocolRuleFrame::Bind { binding, .. } = frame {
            self.outside.insert(binding);
        }
    }

    fn state(&mut self, state: &'t ProtocolRuleStateTerm<DescriptorTerm>) {
        match state {
            ProtocolRuleStateTerm::Map(map) => match &map.body {
                ProtocolRuleMapBody::Items { items, remainder } => {
                    for item in items {
                        self.keys.push((&item.key, Lookup::MapKey));
                        self.term(&item.value);
                    }
                    self.frame(remainder);
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
                for entry in entries {
                    self.keys.push((&entry.key, Lookup::MapKey));
                    self.outside.insert(&entry.value_binding);
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

    /// `term`, outside every key: its names are bound, and a set's element is
    /// a key of its own.
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
                let element =
                    reference.application == DescriptorApplicationRef::Set(SetOperation::Item);
                for value in argument_values(arguments) {
                    if element {
                        self.keys.push((value, Lookup::SetElement));
                    } else {
                        self.term(value);
                    }
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
    outside: &'a BTreeSet<&'t str>,
    lookup: Lookup,
    /// The names its matched part binds.
    matched: BTreeSet<&'t str>,
    /// What makes it a selection: the first name nothing else binds, `_`,
    /// alias, alternatives or open record outside every construct that
    /// computes, described.
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
                    self.matched.insert(name);
                    if !self.outside.contains(name.as_str()) && self.selection.is_none() {
                        self.selection =
                            Some(format!("the name `{name}`, which nothing else binds"));
                    }
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
                    self.matched.insert(name);
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
