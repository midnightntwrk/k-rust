//! ```toml algorithm
//! id = "backend.alias.unfold"
//! name = "capture-avoiding alias unfolding"
//! sites = ["expand", "expand_within", "collect", "measure_aliases", "unfolded_size", "measure_node", "visit_associative", "lay_out", "Expander::expand", "Expander::enter", "Expander::expand_binder"]
//! variable = "p = pattern size; o = what the unfolding builds and checks: the unfolded pattern, for each alias application it unfolds the application and one unit per argument, and for each binder of a body it enters one capture check per parameter substituted under a binder of that body, at most p + max(UNFOLDING_LIMIT, UNFOLDING_FACTOR * p) for a request since it is measured before it is built; v = variables of the alias bodies an unfolding enters whose names have the form {base}Alias{digits}, at most B; B = total size of the alias bodies; A = total parameters and sort parameters of the aliases"
//! counters = []
//! no_counter = "alias unfolding has no dedicated counter; each alias body is measured and laid out once at load, and patterns are unfolded once per axiom at load and once per internalize_term or internalize_pattern request"
//! span = "per call"
//!
//! [[cost]]
//! mode = "one expand call"
//! bound = "O(p + o log^2 o + v log o): every node it visits is built once, as output or as an alias application it enters, and every capture check is counted, with map and set operations of logarithmic cost; free-variable sets are merged smaller into larger, O(o log o) insertions, and copied only with a copy of their argument; a renamed binder resumes the fresh-name search of its base name where the last one stopped, so each candidate is tried at most once, and a rejected one is the name of a variable built or one of the v; O(p) for a pattern that applies no alias, which is returned as it is"
//!
//! [[cost]]
//! mode = "definition load (measure_aliases)"
//! bound = "O(B log B + A) to measure and lay out each body once, O(D) to size the modules, then one expand call per axiom, whose builds together exceed the axioms by at most max(UNFOLDING_LIMIT, UNFOLDING_FACTOR * D) for the modules given with the definition, D the written size of their axioms, claims and alias bodies, plus max(UNFOLDING_LIMIT, UNFOLDING_FACTOR * M) for each module added later (BackendSession::add_module), M that size for the added module alone"
//! ```
//!
//! Capture-avoiding alias unfolding, measured before it is built; no counter; the loops are the
//! work lists of the measurement and of the layout of the alias bodies, the recursion over the
//! pattern and the bodies it enters, and the fresh-name retry.
//!
//! An alias body may apply further aliases and use a parameter several times, so the unfolding of
//! a pattern can be exponentially larger than the pattern and the definition: a chain of `n`
//! aliases, each applying the next twice, unfolds to `2^n` nodes. Loading therefore does not
//! unfold the aliases to check them. It measures, once per alias, the size of what unfolding an
//! application of it builds, as an affine function of the sizes of its arguments ([`Size`]), in
//! one top down pass over the body that counts the copies the unfolding holds of each node, so
//! the measures compose along the chain in time linear in the definition. Every pattern is
//! measured the same way before it is unfolded, and the unfolding is built only when what it
//! adds fits in the budget of its operation ([`UnfoldingBudget`]).
//!
//! Unfolding builds what is measured ([`Expander`]): an argument is unfolded once, only when the
//! alias keeps a copy of it, and moved into its last copy, so every node it builds is a node of
//! the result, except the alias applications it enters, which the measure counts too, with the
//! capture checks of the binders of the bodies it enters. The measure counts each name as
//! written; a binder renamed to avoid capture has a longer name, which the budget counts at its
//! longest ([`Size::bound`]), so what is built never exceeds what is spent.

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;
use std::sync::Arc;

use k_rust_kore::kore::ast as kore;
use k_rust_kore::measure::{self, Algorithm};

use crate::definition::DefinitionError;

/// The least that unfolding aliases may add to the size ([`Size`]) of the patterns one operation
/// supplies, however small they are: one request pattern, the axioms of the modules a definition
/// is given with, or those of one module added to it later. An operation's budget
/// ([`UnfoldingBudget`]) is the larger of this floor and [`UNFOLDING_FACTOR`] times the size of
/// what it supplied.
///
/// The size counts what unfolding builds: each pattern and sort node and each byte of the names
/// they own, of the unfolded pattern and of each alias application it enters, plus one unit for
/// each argument of such an application. A cloned node allocates its own names, so memory grows
/// with it: about 10 bytes per unit for nodes with short names, and at most about 60 for nodes
/// with one-byte names, on a 64-bit target, so the floor, 2^22 (4,194,304), lets the unfolded
/// pattern of a small operation reach a few hundred MiB at worst, which the internal terms built
/// from it and every later pass over them multiply. A binder renamed to avoid capture gets
/// `Alias` and an index added to its name, so the size spent counts each name that renaming can
/// lengthen at the longest index the operation can reach ([`Size::bound`]): what is built never
/// exceeds what is spent. On renaming shapes the bound is within 10% of what is built; where a
/// body's one-byte binders could be renamed but are not, it can count up to about 4 times what is
/// built. Time grows with the size too: unfolding builds nothing it does not count, and the size
/// also counts the capture checks at the binders of the alias bodies it enters, the one part of
/// its work that is not proportional to what it builds. Each unit is visited or checked once,
/// with map and set operations of logarithmic cost, whatever the number of free variables of the
/// arguments. The fresh names a renamed binder tries are not counted, but each candidate is tried
/// at most once per operation, so the tries are one per renamed binder and one per name of the
/// form of a fresh name among the variables built and those of the alias bodies entered
/// ([`Expander`]). With the stack provided up front, as operations provide it, a release build
/// took 18 to 150 ns per measured unit on alias chains that duplicate their argument, nest
/// binders around it, pass it through 256,000 nested bodies, or rename every binder they nest
/// around it, on a body of 64,000 nested binders that are all renamed, and on a chain of 64,000
/// renamed binders around an argument whose free variables spell the first 64,000 candidates;
/// unfolding 98% of the floor took 0.55 s.
pub(crate) const UNFOLDING_LIMIT: u64 = 1 << 22;

/// How many times its own size, as written ([`Size`]), unfolding may add to the patterns of an
/// operation above [`UNFOLDING_LIMIT`].
///
/// The budget exists because an unfolding can be exponentially larger than its input: a chain
/// of `n` aliases, each applying the next twice, unfolds to `2^n` nodes from a module of a few
/// kilobytes, and that must be refused before it is built. What makes such an input harmful is
/// the ratio of what it makes the backend build to what was sent, not the absolute size: a
/// definition without aliases is loaded at a cost proportional to its own size, however large.
/// A budget linear in the input bounds that ratio, so the memory and time an operation spends on
/// unfolding stay within a constant factor of what loading or reading its input costs anyway,
/// whatever the aliases, while a small input still gets only the floor.
///
/// Unfoldings polynomial in the definition are real: a closed alias applied by many axioms
/// unfolds to a copy of its body at each application, as the alias that collects the left-hand
/// sides of a priority group's rules does in every rule of a later group. A 15 MB EVM definition
/// of 6.4 million units built that way spends about 51.5 million units on unfolding (8.1 times
/// its own size): a release build loaded it in 2.4 s more, and with 1.4 GB more peak memory, than
/// the same definition with those bodies emptied (about 47 ns and 28 bytes of peak memory per
/// unit, the internal terms built from the unfolded axioms included). The factor leaves about
/// four times that ratio for definitions of the same shape with more rules.
///
/// What a unit costs once the unfolded axioms are internalized depends on its shape, since a
/// unit is a node or a byte of a name: those closed bodies have long names, while a chain of
/// aliases over one-byte variables, applied by an axiom under `\not`, costs about 235 bytes of
/// peak memory and 290 ns per unit (7.9 million units took 1.8 GB and 2.3 s more than the same
/// module without the chain), the most measured. So 1 MB of KORE text, about 0.4 to 0.65 million
/// units, may make one operation build from about 0.4 GB up to about 5 GB. Patterns written out
/// cost at least as much per unit as their unfolding: the same variable shape written out, as a
/// 3.9 MB module of 2.4 million units, took about 460 bytes and 600 ns per unit to add, parsing
/// included. So what the factor bounds is the ratio: unfolding costs at most about 32 times what
/// loading the patterns the operation supplied costs.
pub(crate) const UNFOLDING_FACTOR: u64 = 32;

#[derive(Clone, Debug)]
pub(crate) struct AliasDefinition {
    pub(crate) sort_parameters: Vec<String>,
    pub(crate) argument_sorts: Vec<kore::Sort>,
    pub(crate) result_sort: kore::Sort,
    pub(crate) parameters: Vec<kore::Variable>,
    pub(crate) right: kore::Pattern,
    /// The height of `right` itself (`nesting::height`, aliases in it not unfolded): the levels
    /// that unfolding descends through within this body before it enters another.
    pub(crate) depth: usize,
    /// The height of `right` with every alias in it unfolded (`nesting::alias_heights`).
    pub(crate) height: usize,
    /// The size of what unfolding an application of the alias builds, as a function of the sizes
    /// of its arguments: `Some` once [`collect`] has measured it.
    pub(crate) size: Option<Size>,
    /// Where in `right` unfolding substitutes each parameter, laid out by [`collect`].
    layout: Layout,
}

/// The size of a pattern is one for each pattern node and each sort node, plus the length of each
/// symbol, sort, and variable name, as the pattern is written: names are owned strings that every
/// copy of a node copies, while string and domain values are shared and count as one node.
///
/// A `Size` is the size of what unfolding an application of an alias builds, as an affine
/// function of the arguments and sort arguments of the application, in two parts.
///
/// The unfolded body, of which each copy of the application's unfolding holds one copy: `constant`,
/// plus each argument's size times its coefficient in `terms`, plus each sort argument's size
/// times its coefficient in `sorts`, with one coefficient for each parameter and each sort
/// parameter. A term coefficient is the number of copies of that argument the unfolding builds;
/// it is zero exactly when the body keeps no copy of the argument, which is then not unfolded at
/// all.
///
/// The alias applications that unfolding the body enters, each counted as the application node
/// with its sorts substituted plus one unit for each of its arguments, and the capture checks of
/// the binders of every body entered, one unit for each binder unfolding visits in the body times
/// the parameters of that body with an occurrence it substitutes under a binder
/// ([`Layout::captured`]): `entered`, plus each sort argument's size times its coefficient in
/// `entered_sorts`. Unfolding enters each application of a body once each time it enters the
/// body, since an argument is unfolded once and then copied, so this part is built, and checked,
/// once per entry, however many copies of the result are made.
///
/// Both parts count each name as written. A binder of an alias body is renamed when it would
/// capture a free variable of an argument, and the fresh name is longer than the written one;
/// `renamed` counts the copies of the names that renaming can lengthen (each binder of a body and
/// each variable such a binder binds), so that [`Size::bound`] can add the most they can grow.
///
/// The arithmetic saturates: a saturated size exceeds every budget.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct Size {
    constant: u64,
    terms: Vec<u64>,
    sorts: Vec<u64>,
    entered: u64,
    entered_sorts: Vec<u64>,
    renamed: u64,
}

impl Size {
    /// The size of the alias body's own unfolding, as a constant and sort coefficients.
    fn body(&mut self) -> Part<'_> {
        Part {
            constant: &mut self.constant,
            sorts: &mut self.sorts,
        }
    }

    /// The size of the applications its unfolding enters, as a constant and sort coefficients.
    fn entries(&mut self) -> Part<'_> {
        Part {
            constant: &mut self.entered,
            sorts: &mut self.entered_sorts,
        }
    }

    /// The whole size of a pattern, which has no parameters, with every name as written: what
    /// its unfolding builds when it renames no binder.
    fn total(&self) -> u64 {
        self.constant.saturating_add(self.entered)
    }

    /// An upper bound of what the unfolding of a pattern of this size builds, renamed binders
    /// included, given `body_names`, the number of variable names of all the alias bodies.
    ///
    /// A renamed binder is named `{name}Alias{index}` ([`Expander::rename_to_avoid_capture`]),
    /// so each of the `renamed` names grows by at most `Alias` and the digits of the largest index
    /// the unfolding can reach. A base name's index only grows through one unfolding, and each
    /// value below it was either taken by a renamed binder, of which there are at most
    /// `renamed`, or rejected as the name of a variable already built, of which there are at most
    /// `total` (each counts at least one unit), or of a variable of the body entered, of which
    /// there are at most `body_names`. So every index is below the sum of the three.
    fn bound(&self, body_names: impl FnOnce() -> u64) -> u64 {
        let total = self.total();
        if self.renamed == 0 {
            return total;
        }
        let largest_index = self
            .renamed
            .saturating_add(total)
            .saturating_add(body_names());
        let growth = length("Alias").saturating_add(decimal_digits(largest_index));
        total.saturating_add(self.renamed.saturating_mul(growth))
    }
}

/// The number of decimal digits of `value`.
fn decimal_digits(value: u64) -> u64 {
    value
        .checked_ilog10()
        .map_or(1, |digits| u64::from(digits) + 1)
}

/// One part of a [`Size`]: a constant and a coefficient for each sort parameter.
struct Part<'s> {
    constant: &'s mut u64,
    sorts: &'s mut [u64],
}

impl Part<'_> {
    /// Add `copies` copies of something of size `value`.
    fn add_constant(&mut self, copies: u64, value: u64) {
        *self.constant = self.constant.saturating_add(copies.saturating_mul(value));
    }
}

fn add_copies(coefficient: &mut u64, copies: u64) {
    *coefficient = coefficient.saturating_add(copies);
}

fn length(name: &str) -> u64 {
    u64::try_from(name.len()).unwrap_or(u64::MAX)
}

/// The size of `pattern` as written ([`Size`]), with a work list.
pub(crate) fn size(pattern: &kore::Pattern) -> u64 {
    let mut total = 0_u64;
    let mut pending = vec![pattern];
    // Each pop pushes only proper subpatterns of the popped one, so the loop terminates.
    while let Some(pattern) = pending.pop() {
        total = total.saturating_add(written_size(pattern));
        let (first, second) = crate::nesting::children(pattern);
        pending.extend(first.iter().chain(second));
    }
    total
}

/// Add `copies` copies of `sort` to `size`, with each sort variable that is a sort parameter (its
/// position in `sort_parameters`) standing for the sort argument of that position, and return the
/// size of `sort` as written.
fn add_sort(
    size: &mut Part<'_>,
    copies: u64,
    sort: &kore::Sort,
    sort_parameters: &BTreeMap<&str, usize>,
) -> u64 {
    let mut written = 0_u64;
    let mut add = |sort: &kore::Sort| {
        let (name, parameter) = match sort {
            kore::Sort::Variable(name) => (name, sort_parameters.get(name.as_str())),
            kore::Sort::Application { name, .. } => (name, None),
        };
        let own = 1 + length(name);
        written = written.saturating_add(own);
        match parameter {
            Some(&index) => add_copies(&mut size.sorts[index], copies),
            None => size.add_constant(copies, own),
        }
    };
    match sort {
        kore::Sort::Application { arguments, .. } if !arguments.is_empty() => {
            let mut pending = vec![sort];
            // Each pop pushes only proper subsorts of the popped one, so the loop terminates.
            while let Some(sort) = pending.pop() {
                add(sort);
                if let kore::Sort::Application { arguments, .. } = sort {
                    pending.extend(arguments);
                }
            }
        }
        _ => add(sort),
    }
    written
}

/// The size of `sort` as written.
#[cfg(test)]
fn sort_size(sort: &kore::Sort) -> u64 {
    add_sort(&mut Size::default().body(), 0, sort, &BTreeMap::new())
}

/// Add `copies` copies of `pattern`'s own node, without its subpatterns, to `size`: the node, its
/// name, the variable of a binder, and the sorts it carries, substituted as [`add_sort`] does.
/// Return the size of that node as written.
fn add_own(
    size: &mut Part<'_>,
    copies: u64,
    pattern: &kore::Pattern,
    sort_parameters: &BTreeMap<&str, usize>,
) -> u64 {
    use kore::Pattern;

    let names = match pattern {
        Pattern::Application { symbol, .. } | Pattern::AssociativeApplication { symbol, .. } => {
            length(&symbol.name)
        }
        Pattern::Variable(variable) => length(&variable.name),
        Pattern::Exists { variable, .. }
        | Pattern::Forall { variable, .. }
        | Pattern::Mu { variable, .. }
        | Pattern::Nu { variable, .. } => 1 + length(&variable.name),
        Pattern::String(_)
        | Pattern::Top { .. }
        | Pattern::Bottom { .. }
        | Pattern::And { .. }
        | Pattern::Or { .. }
        | Pattern::Not { .. }
        | Pattern::Next { .. }
        | Pattern::Implies { .. }
        | Pattern::Iff { .. }
        | Pattern::Rewrites { .. }
        | Pattern::Ceil { .. }
        | Pattern::Floor { .. }
        | Pattern::Equals { .. }
        | Pattern::In { .. }
        | Pattern::DomainValue { .. } => 0,
    };
    let own = 1 + names;
    size.add_constant(copies, own);
    crate::nesting::sorts(pattern).fold(own, |written, sort| {
        written.saturating_add(add_sort(size, copies, sort, sort_parameters))
    })
}

/// The size of `pattern`'s own node as written, without its subpatterns.
fn written_size(pattern: &kore::Pattern) -> u64 {
    add_own(&mut Size::default().body(), 0, pattern, &BTreeMap::new())
}

/// What unfolding may still add to the patterns of one operation: at first the larger of
/// [`UNFOLDING_LIMIT`] and [`UNFOLDING_FACTOR`] times the size of the patterns the operation was
/// given, as written.
pub(crate) struct UnfoldingBudget {
    available: u64,
}

impl UnfoldingBudget {
    /// The budget of an operation given patterns of size `input` as written.
    pub(crate) fn for_input(input: u64) -> Self {
        Self {
            available: UNFOLDING_LIMIT.max(input.saturating_mul(UNFOLDING_FACTOR)),
        }
    }

    /// The budget of loading `modules`, supplied by one operation, whose axioms are unfolded
    /// together: their input is every axiom, claim, and alias body they declare, each counted
    /// once as written.
    pub(crate) fn for_modules(modules: &[&kore::Module]) -> Self {
        let input = modules
            .iter()
            .flat_map(|module| &module.sentences)
            .map(|sentence| match sentence {
                kore::Sentence::Axiom { pattern, .. } | kore::Sentence::Claim { pattern, .. } => {
                    size(pattern)
                }
                kore::Sentence::AliasDeclaration { right, .. } => size(right),
                kore::Sentence::Import { .. }
                | kore::Sentence::SortDeclaration { .. }
                | kore::Sentence::SymbolDeclaration { .. } => 0,
            })
            .fold(0, u64::saturating_add);
        Self::for_input(input)
    }

    fn spend(&mut self, added: u64) -> Result<(), DefinitionError> {
        if added > self.available {
            return Err(DefinitionError::AliasUnfoldingTooLarge {
                added,
                available: self.available,
            });
        }
        self.available -= added;
        Ok(())
    }
}

/// The aliases declared in `modules`, with the unfolded heights of their bodies from `heights`
/// (`nesting::alias_heights`), the sizes measured by [`measure_aliases`], and the layouts that
/// unfolding reads.
pub(crate) fn collect(
    modules: &[&kore::Module],
    heights: &BTreeMap<String, usize>,
) -> Result<BTreeMap<String, AliasDefinition>, DefinitionError> {
    let mut aliases = BTreeMap::new();
    for module in modules {
        for sentence in &module.sentences {
            let kore::Sentence::AliasDeclaration {
                alias,
                argument_sorts,
                result_sort,
                left,
                right,
                ..
            } = sentence
            else {
                continue;
            };
            let sort_parameters = alias
                .sort_parameters
                .iter()
                .map(|sort| match sort {
                    kore::Sort::Variable(name) => Ok(name.clone()),
                    kore::Sort::Application { .. } => Err(DefinitionError::InvalidSortParameter),
                })
                .collect::<Result<Vec<_>, _>>()?;
            if let Some(duplicate) = first_duplicate(sort_parameters.iter()) {
                return Err(DefinitionError::DuplicateParameter(duplicate.clone()));
            }
            let kore::Pattern::Application { symbol, arguments } = left.as_ref() else {
                return Err(DefinitionError::MalformedAlias(format!(
                    "alias {} must have an application on the left",
                    alias.name
                )));
            };
            if symbol.name != alias.name || symbol.sort_parameters != alias.sort_parameters {
                return Err(DefinitionError::MalformedAlias(format!(
                    "alias {} has a mismatched left-hand symbol",
                    alias.name
                )));
            }
            if arguments.len() != argument_sorts.len() {
                return Err(DefinitionError::WrongAliasArity {
                    alias: alias.name.clone(),
                    expected: argument_sorts.len(),
                    actual: arguments.len(),
                });
            }
            let parameters = arguments
                .iter()
                .zip(argument_sorts)
                .map(|(argument, expected_sort)| {
                    let kore::Pattern::Variable(variable) = argument else {
                        return Err(DefinitionError::MalformedAlias(format!(
                            "alias {} left-hand arguments must be variables",
                            alias.name
                        )));
                    };
                    if &variable.sort != expected_sort {
                        return Err(DefinitionError::MalformedAlias(format!(
                            "alias {} left-hand variable {} has the wrong sort",
                            alias.name, variable.name
                        )));
                    }
                    Ok(variable.clone())
                })
                .collect::<Result<Vec<_>, _>>()?;
            if let Some(duplicate) =
                first_duplicate(parameters.iter().map(|variable| &variable.name))
            {
                return Err(DefinitionError::DuplicateParameter(duplicate.clone()));
            }
            let definition = AliasDefinition {
                sort_parameters,
                argument_sorts: argument_sorts.clone(),
                result_sort: result_sort.clone(),
                parameters,
                right: (**right).clone(),
                depth: crate::nesting::height(right, &crate::nesting::Syntactic),
                height: heights.get(&alias.name).copied().unwrap_or(1),
                size: None,
                layout: Layout::default(),
            };
            if aliases.insert(alias.name.clone(), definition).is_some() {
                return Err(DefinitionError::DuplicateAlias(alias.name.clone()));
            }
        }
    }
    measure_aliases(&mut aliases)?;
    Ok(aliases)
}

fn first_duplicate<'a>(values: impl IntoIterator<Item = &'a String>) -> Option<&'a String> {
    let mut seen = BTreeSet::new();
    values.into_iter().find(|value| !seen.insert(*value))
}

/// Measure the unfolded size of every alias body into its `size`, refusing a definition whose
/// unfolding cannot terminate, then lay out every body for unfolding ([`lay_out`]).
///
/// Every alias body is measured once, entering the body of an alias it applies before that
/// application's arguments, so an application anywhere in a body that is malformed for its alias
/// (`WrongAliasSortArgumentCount`, `WrongAliasArity`) or that applies an alias whose body is being
/// measured (`AliasCycle`, which unfolding would repeat forever) is refused without building the
/// unfolding. Unfolding relies on this: it applies only aliases measured here, to patterns
/// measured before they are unfolded, and checks neither again. The size of an alias is not
/// checked against [`UNFOLDING_LIMIT`] here: it depends on the arguments it is applied to, so
/// only the patterns that apply it are checked, before they are unfolded.
fn measure_aliases(aliases: &mut BTreeMap<String, AliasDefinition>) -> Result<(), DefinitionError> {
    let mut measured = Measured::default();
    for (name, alias) in aliases.iter() {
        if !measured.sizes.contains_key(name.as_str()) {
            unfolded_size(Frame::alias(name, alias), aliases, &mut measured)?;
        }
    }
    let Measured { mut sizes, order } = measured;
    let measured = order
        .into_iter()
        .map(|name| (name.to_owned(), sizes.remove(name)))
        .collect::<Vec<_>>();
    let order = measured
        .iter()
        .map(|(name, _)| name.clone())
        .collect::<Vec<_>>();
    for (name, size) in measured {
        if let Some(alias) = aliases.get_mut(&name) {
            alias.size = size;
        }
    }
    // A body is laid out after every alias it applies, which finished its measurement first.
    for name in &order {
        let layout = lay_out(&aliases[name], aliases);
        if let Some(alias) = aliases.get_mut(name) {
            alias.layout = layout;
        }
    }
    Ok(())
}

/// One step of the size measurement of a pattern.
enum Visit<'a> {
    /// Measure this pattern, of which the unfolding builds this many copies: zero for an argument
    /// that an alias drops, which is checked although unfolding never unfolds it.
    Enter(&'a kore::Pattern, u64),
    /// Leave a binder of the parameter at this position.
    Unbind(usize),
    /// Leave a binder.
    Leave,
}

/// The measurement of one pattern: a request's, or the body of the alias `alias`.
struct Frame<'a> {
    alias: Option<&'a str>,
    /// The position of each parameter of `alias`.
    parameters: BTreeMap<&'a kore::Variable, usize>,
    /// The position of each sort parameter of `alias`.
    sort_parameters: BTreeMap<&'a str, usize>,
    /// How many binders around the current visit bind each parameter, which then stands for
    /// itself rather than for its argument.
    shadowed: Vec<usize>,
    pending: Vec<Visit<'a>>,
    /// The size of what unfolding what has been visited builds, as a function of the arguments.
    unfolded: Size,
    /// The size of what has been visited, as written.
    written: u64,
    /// Whether what has been visited applies an alias, so that unfolding changes it.
    applies_alias: bool,
    /// The binders around the current visit.
    binders: usize,
    /// The binders visited with copies, which unfolding enters.
    entered_binders: u64,
    /// Whether each parameter has an occurrence with copies under a binder, and how many do.
    captured: Vec<bool>,
    captured_count: u64,
}

impl<'a> Frame<'a> {
    fn pattern(pattern: &'a kore::Pattern) -> Self {
        Self {
            alias: None,
            parameters: BTreeMap::new(),
            sort_parameters: BTreeMap::new(),
            shadowed: Vec::new(),
            pending: vec![Visit::Enter(pattern, 1)],
            unfolded: Size::default(),
            written: 0,
            applies_alias: false,
            binders: 0,
            entered_binders: 0,
            captured: Vec::new(),
            captured_count: 0,
        }
    }

    fn alias(name: &'a str, alias: &'a AliasDefinition) -> Self {
        Self {
            alias: Some(name),
            parameters: parameter_positions(alias),
            sort_parameters: alias
                .sort_parameters
                .iter()
                .enumerate()
                .map(|(index, parameter)| (parameter.as_str(), index))
                .collect(),
            shadowed: vec![0; alias.parameters.len()],
            pending: vec![Visit::Enter(&alias.right, 1)],
            unfolded: Size {
                constant: 0,
                terms: vec![0; alias.parameters.len()],
                sorts: vec![0; alias.sort_parameters.len()],
                entered: 0,
                entered_sorts: vec![0; alias.sort_parameters.len()],
                renamed: 0,
            },
            written: 0,
            applies_alias: false,
            binders: 0,
            entered_binders: 0,
            captured: vec![false; alias.parameters.len()],
            captured_count: 0,
        }
    }

    /// The measurement of what has been visited. Each entry of an alias body also checks, at
    /// each binder it unfolds, every parameter substituted under some binder of the body
    /// ([`Layout::captured`]), so that work is counted with the applications the body enters.
    fn finish(mut self) -> Measurement {
        if self.alias.is_some() {
            self.unfolded
                .entries()
                .add_constant(self.entered_binders, self.captured_count);
        }
        Measurement {
            unfolded: self.unfolded,
            written: self.written,
            applies_alias: self.applies_alias,
        }
    }

    /// Push `arguments` paired with their copies, in order, so that the first is visited first.
    fn enter_in_order(&mut self, arguments: impl IntoIterator<Item = (&'a kore::Pattern, u64)>) {
        let start = self.pending.len();
        self.pending.extend(
            arguments
                .into_iter()
                .map(|(argument, copies)| Visit::Enter(argument, copies)),
        );
        self.pending[start..].reverse();
    }
}

/// The position of each parameter of `alias`.
fn parameter_positions(alias: &AliasDefinition) -> BTreeMap<&kore::Variable, usize> {
    alias
        .parameters
        .iter()
        .enumerate()
        .map(|(index, parameter)| (parameter, index))
        .collect()
}

/// The aliases whose bodies are being measured, outermost first.
#[derive(Default)]
struct Entered<'a> {
    order: Vec<&'a str>,
    names: BTreeSet<&'a str>,
}

impl<'a> Entered<'a> {
    fn extend(&mut self, name: Option<&'a str>) {
        if let Some(name) = name {
            self.order.push(name);
            self.names.insert(name);
        }
    }

    fn pop(&mut self) -> Option<&'a str> {
        let name = self.order.pop()?;
        self.names.remove(name);
        Some(name)
    }

    /// The cycle that an application of `name` closes, from where `name` was entered, when its
    /// body is being measured.
    fn cycle(&self, name: &str) -> Option<Vec<String>> {
        if !self.names.contains(name) {
            return None;
        }
        let start = self.order.iter().position(|entered| *entered == name)?;
        let mut cycle = self.order[start..]
            .iter()
            .map(|entered| (*entered).to_owned())
            .collect::<Vec<_>>();
        cycle.push(name.to_owned());
        Some(cycle)
    }
}

/// The alias bodies measured by one measurement, in the order their measurements finished: the
/// body of an alias after the bodies of the aliases it applies.
#[derive(Default)]
struct Measured<'a> {
    sizes: BTreeMap<&'a str, Size>,
    order: Vec<&'a str>,
}

impl<'a> Measured<'a> {
    fn insert(&mut self, name: &'a str, size: Size) {
        self.sizes.insert(name, size);
        self.order.push(name);
    }
}

/// The result of measuring a pattern or an alias body.
struct Measurement {
    /// The size of what its unfolding builds, as a function of the arguments of the alias.
    unfolded: Size,
    /// Its size as written.
    written: u64,
    /// Whether it applies an alias, so that unfolding changes it.
    applies_alias: bool,
}

/// Measure the unfolding of the pattern or alias body of `root`, with the sizes of alias bodies
/// measured earlier in `measured` or in their `size`. A body it needs that neither has is
/// measured first and added to `measured`.
///
/// Every node is visited once, top down, with the number of copies of it that the unfolding
/// builds: a node of an argument of an alias application has as many copies as the application
/// times the alias's coefficient for that argument. So the measurement takes time linear in what
/// it visits, plus the parameters of the bodies it measures, whatever the number of parameters
/// and their occurrences. It refuses a malformed alias application and an alias cycle anywhere
/// in what it visits, dropped arguments included, entering the body of an alias before the
/// arguments of its application; unfolding checks neither again.
///
/// Every frame, pattern, and sort is measured with explicit work lists, so the stack it takes is
/// bounded whatever the depth of the patterns and of the chains of aliases.
fn unfolded_size<'a>(
    root: Frame<'a>,
    aliases: &'a BTreeMap<String, AliasDefinition>,
    measured: &mut Measured<'a>,
) -> Result<Measurement, DefinitionError> {
    // Invariant: `stack` names the aliases of `frames`, whose bodies are being measured, in
    // order; an application of one of them is a cycle.
    let mut stack = Entered::default();
    stack.extend(root.alias);
    let mut frames = vec![root];
    // Each iteration pops a visit, which pushes visits only for proper subpatterns and binder
    // exits, pushes a frame for a body not yet measured (at most once per alias: the body is
    // measured before the visit that needed it is retried, and an alias already on the stack is
    // a cycle), or finishes a frame.
    while let Some(frame) = frames.last_mut() {
        let Some(visit) = frame.pending.pop() else {
            let Some(frame) = frames.pop() else {
                unreachable!("the loop runs while a frame is open")
            };
            let measurement = frame.finish();
            let Some(name) = stack.pop() else {
                return Ok(measurement);
            };
            if frames.is_empty() {
                measured.insert(name, measurement.unfolded.clone());
                return Ok(measurement);
            }
            measured.insert(name, measurement.unfolded);
            continue;
        };
        let callee = match visit {
            Visit::Enter(pattern, copies) => {
                measure_node(frame, pattern, copies, aliases, &measured.sizes, &stack)?
            }
            Visit::Unbind(index) => {
                frame.shadowed[index] -= 1;
                None
            }
            Visit::Leave => {
                frame.binders -= 1;
                None
            }
        };
        if let Some(name) = callee {
            stack.extend(Some(name));
            frames.push(Frame::alias(name, &aliases[name]));
        }
    }
    unreachable!("the measurement returns when it finishes its root frame")
}

/// Add `copies` copies of what unfolding `pattern`'s own node builds to the measurement of
/// `frame`, and push its subpatterns with the copies the unfolding builds of each, or name the
/// alias whose body must be measured first.
fn measure_node<'a>(
    frame: &mut Frame<'a>,
    pattern: &'a kore::Pattern,
    copies: u64,
    aliases: &'a BTreeMap<String, AliasDefinition>,
    measured: &BTreeMap<&'a str, Size>,
    stack: &Entered<'a>,
) -> Result<Option<&'a str>, DefinitionError> {
    use kore::Pattern;

    match pattern {
        Pattern::Application { symbol, arguments } if aliases.contains_key(&symbol.name) => {
            let body = match callee(symbol, arguments.len(), aliases, measured, stack)? {
                Callee::Measured(body) => body,
                Callee::Unmeasured(name) => {
                    frame.pending.push(Visit::Enter(pattern, copies));
                    return Ok(Some(name));
                }
            };
            frame.applies_alias = true;
            // Unfolding enters the body once per entry of this frame, if it reaches the
            // application at all: the application with its sorts substituted, the substitution
            // of its arguments, and what the body enters.
            let entries = u64::from(copies > 0);
            let written = add_own(
                &mut frame.unfolded.entries(),
                entries,
                pattern,
                &frame.sort_parameters,
            );
            frame.written = frame.written.saturating_add(written);
            enter_body(frame, copies, entries, length_of(arguments), symbol, body);
            frame.enter_in_order(
                arguments
                    .iter()
                    .zip(&body.terms)
                    .map(|(argument, coefficient)| (argument, copies.saturating_mul(*coefficient))),
            );
            return Ok(None);
        }
        Pattern::AssociativeApplication {
            associativity,
            symbol,
            arguments,
        } if aliases.contains_key(&symbol.name) => {
            return visit_associative(
                frame,
                pattern,
                copies,
                *associativity,
                symbol,
                arguments,
                aliases,
                measured,
                stack,
            );
        }
        Pattern::Variable(variable) => {
            if let Some(&index) = frame.parameters.get(variable)
                && frame.shadowed[index] == 0
            {
                frame.written = frame.written.saturating_add(written_size(pattern));
                add_copies(&mut frame.unfolded.terms[index], copies);
                if copies > 0 && frame.binders > 0 && !frame.captured[index] {
                    frame.captured[index] = true;
                    frame.captured_count += 1;
                }
                return Ok(None);
            }
            // Any other variable of an alias body is bound by a binder of the body (verification
            // refuses a free one), which renaming can lengthen.
            if frame.alias.is_some() {
                add_copies(&mut frame.unfolded.renamed, copies);
            }
        }
        Pattern::Exists { variable, .. }
        | Pattern::Forall { variable, .. }
        | Pattern::Mu { variable, .. }
        | Pattern::Nu { variable, .. } => {
            if frame.alias.is_some() {
                add_copies(&mut frame.unfolded.renamed, copies);
            }
            frame.binders += 1;
            frame.entered_binders += u64::from(copies > 0);
            frame.pending.push(Visit::Leave);
            if let Some(&index) = frame.parameters.get(variable.as_ref()) {
                frame.shadowed[index] += 1;
                frame.pending.push(Visit::Unbind(index));
            }
        }
        _ => {}
    }
    let written = add_own(
        &mut frame.unfolded.body(),
        copies,
        pattern,
        &frame.sort_parameters,
    );
    frame.written = frame.written.saturating_add(written);
    let (first, second) = crate::nesting::children(pattern);
    frame.enter_in_order(first.iter().chain(second).map(|child| (child, copies)));
    Ok(None)
}

fn length_of<T>(items: &[T]) -> u64 {
    u64::try_from(items.len()).unwrap_or(u64::MAX)
}

/// Measure an associative application of an alias as the chain of binary applications it folds
/// into: for `n` arguments, `n - 1` applications of the alias, each nested in the first argument
/// (left associative) or the second (right associative) of the one around it. A link that the
/// alias drops (its coefficient is zero) is measured with no copies, as are the links and
/// arguments inside it.
#[allow(clippy::too_many_arguments)]
fn visit_associative<'a>(
    frame: &mut Frame<'a>,
    pattern: &'a kore::Pattern,
    copies: u64,
    associativity: kore::Associativity,
    symbol: &'a kore::Symbol,
    arguments: &'a [kore::Pattern],
    aliases: &'a BTreeMap<String, AliasDefinition>,
    measured: &BTreeMap<&'a str, Size>,
    stack: &Entered<'a>,
) -> Result<Option<&'a str>, DefinitionError> {
    frame.applies_alias = true;
    let written = written_size(pattern);
    let (first, last) = match arguments {
        // Unfolding leaves it as written.
        [] => {
            frame.written = frame.written.saturating_add(written);
            frame.unfolded.body().add_constant(copies, written);
            return Ok(None);
        }
        // Unfolding replaces it by its argument.
        [argument] => {
            frame.written = frame.written.saturating_add(written);
            frame.pending.push(Visit::Enter(argument, copies));
            return Ok(None);
        }
        [first, .., last] => (first, last),
    };
    let body = match callee(symbol, 2, aliases, measured, stack)? {
        Callee::Measured(body) => body,
        Callee::Unmeasured(name) => {
            frame.pending.push(Visit::Enter(pattern, copies));
            return Ok(Some(name));
        }
    };
    frame.written = frame.written.saturating_add(written);
    let (left, right) = (body.terms[0], body.terms[1]);
    // `chain` counts the copies of the application at the current link, outermost first; `links`
    // their total, and `entered` the links that unfolding enters, those with any copy.
    let mut chain = copies;
    let mut links = 0_u64;
    let mut entered = 0_u64;
    let mut steps = Vec::with_capacity(arguments.len());
    let mut link = |chain: u64| {
        links = links.saturating_add(chain);
        entered += u64::from(chain > 0);
    };
    match associativity {
        kore::Associativity::Left => {
            // f(f(f(a0, a1), a2), a3): the outermost link takes the last argument second.
            for argument in arguments[1..].iter().rev() {
                link(chain);
                steps.push((argument, chain.saturating_mul(right)));
                chain = chain.saturating_mul(left);
            }
            steps.push((first, chain));
            steps.reverse();
        }
        kore::Associativity::Right => {
            // f(a0, f(a1, f(a2, a3))): the outermost link takes the first argument first.
            for argument in &arguments[..arguments.len() - 1] {
                link(chain);
                steps.push((argument, chain.saturating_mul(left)));
                chain = chain.saturating_mul(right);
            }
            steps.push((last, chain));
        }
    }
    // Each link that unfolding enters builds the associative node's symbol with its sorts
    // substituted, and the substitution of its two arguments.
    add_own(
        &mut frame.unfolded.entries(),
        entered,
        pattern,
        &frame.sort_parameters,
    );
    enter_body(frame, links, entered, 2, symbol, body);
    frame.enter_in_order(steps);
    Ok(None)
}

/// Add to `frame` what `copies` copies of the unfolding of an application of the alias `symbol`,
/// whose body measures `body`, hold, and what entering its body `entries` times builds: the
/// substitution of its `arity` arguments and the applications the body enters.
fn enter_body(
    frame: &mut Frame<'_>,
    copies: u64,
    entries: u64,
    arity: u64,
    symbol: &kore::Symbol,
    body: &Size,
) {
    frame.unfolded.body().add_constant(copies, body.constant);
    add_copies(
        &mut frame.unfolded.renamed,
        copies.saturating_mul(body.renamed),
    );
    let mut part = frame.unfolded.entries();
    part.add_constant(entries, arity);
    part.add_constant(entries, body.entered);
    for (sort, (coefficient, entered)) in symbol
        .sort_parameters
        .iter()
        .zip(body.sorts.iter().zip(&body.entered_sorts))
    {
        add_sort(
            &mut frame.unfolded.body(),
            copies.saturating_mul(*coefficient),
            sort,
            &frame.sort_parameters,
        );
        add_sort(
            &mut frame.unfolded.entries(),
            entries.saturating_mul(*entered),
            sort,
            &frame.sort_parameters,
        );
    }
}

/// The measured unfolding of an alias body, or an alias whose body is not measured yet.
enum Callee<'a, 'm> {
    Measured(&'m Size),
    Unmeasured(&'a str),
}

/// Check an application of the alias `symbol` to `arity` arguments as unfolding does, and return
/// the measured size of its body, or the alias if its body must be measured first.
fn callee<'a: 'm, 'm>(
    symbol: &kore::Symbol,
    arity: usize,
    aliases: &'a BTreeMap<String, AliasDefinition>,
    measured: &'m BTreeMap<&'a str, Size>,
    stack: &Entered<'a>,
) -> Result<Callee<'a, 'm>, DefinitionError> {
    let Some((name, alias)) = aliases.get_key_value(&symbol.name) else {
        unreachable!("only applications of aliases are measured as such")
    };
    if symbol.sort_parameters.len() != alias.sort_parameters.len() {
        return Err(DefinitionError::WrongAliasSortArgumentCount {
            alias: name.clone(),
            expected: alias.sort_parameters.len(),
            actual: symbol.sort_parameters.len(),
        });
    }
    if arity != alias.parameters.len() {
        return Err(DefinitionError::WrongAliasArity {
            alias: name.clone(),
            expected: alias.parameters.len(),
            actual: arity,
        });
    }
    if let Some(cycle) = stack.cycle(name) {
        return Err(DefinitionError::AliasCycle(cycle));
    }
    Ok(match measured.get(name.as_str()).or(alias.size.as_ref()) {
        Some(body) => Callee::Measured(body),
        None => Callee::Unmeasured(name),
    })
}

/// Where in an alias body unfolding substitutes each parameter, and what it needs to know there.
///
/// The nodes of the body are numbered in pre-order, the order in which unfolding walks them, as
/// [`crate::nesting::children`] lists the subpatterns of a node; a node's subpatterns are the
/// positions after it, up to the end of its subtree.
#[derive(Clone, Debug, Default)]
struct Layout {
    /// The number of nodes in the subtree of each position.
    subtree: Vec<usize>,
    /// For each parameter, in increasing order, the positions of the occurrences that unfolding
    /// substitutes: those that no binder in the body shadows and no alias in it drops. Unfolding
    /// copies the argument once for each.
    occurrences: Vec<Vec<usize>>,
    /// For each parameter, whether unfolding asks for the free variables of its argument's
    /// unfolding: an occurrence is under a binder of the body, which must not capture them, or in
    /// an argument whose own free variables are asked for.
    needs_free: Vec<bool>,
    /// The parameters, in increasing order, with a substituted occurrence under a binder of the
    /// body: each binder of the body checks whether it would capture a free variable of their
    /// arguments ([`Size`] counts these checks).
    captured: Vec<usize>,
    /// The name of every variable of the body, its parameters included, which a binder renamed
    /// to avoid capture never takes.
    names: BTreeSet<String>,
}

/// One step of laying out an alias body.
enum Place<'a> {
    /// Number this pattern and its subpatterns: whether unfolding substitutes its parameter
    /// occurrences (no alias around it drops it), and whether it asks for their free variables.
    Enter(&'a kore::Pattern, bool, bool),
    /// The subtree of the node at this position ends here.
    Exit(usize),
    /// Leave a binder of the parameter at this position.
    Unbind(usize),
    /// Leave a binder.
    Leave,
}

/// Lay out the body of `alias` ([`Layout`]), whose size and the sizes and layouts of the aliases
/// it applies are known, with a work list over the body.
fn lay_out(alias: &AliasDefinition, aliases: &BTreeMap<String, AliasDefinition>) -> Layout {
    use kore::Pattern;

    let parameters = parameter_positions(alias);
    let mut layout = Layout {
        subtree: Vec::new(),
        occurrences: vec![Vec::new(); alias.parameters.len()],
        needs_free: vec![false; alias.parameters.len()],
        captured: Vec::new(),
        names: alias
            .parameters
            .iter()
            .map(|parameter| parameter.name.clone())
            .collect(),
    };
    let mut shadowed = vec![0_usize; alias.parameters.len()];
    let mut captured = vec![false; alias.parameters.len()];
    // The binders around the current position.
    let mut binders = 0_usize;
    let mut pending = vec![Place::Enter(&alias.right, true, false)];
    // Each `Enter` pushes `Enter`s only for proper subpatterns, so the loop terminates.
    while let Some(place) = pending.pop() {
        let (pattern, substituted, asked) = match place {
            Place::Enter(pattern, substituted, asked) => (pattern, substituted, asked),
            Place::Exit(position) => {
                layout.subtree[position] = layout.subtree.len() - position;
                continue;
            }
            Place::Unbind(index) => {
                shadowed[index] -= 1;
                continue;
            }
            Place::Leave => {
                binders -= 1;
                continue;
            }
        };
        let position = layout.subtree.len();
        layout.subtree.push(1);
        pending.push(Place::Exit(position));
        let start = pending.len();
        match pattern {
            Pattern::Variable(variable) => {
                layout.names.insert(variable.name.clone());
                if let Some(&index) = parameters.get(variable)
                    && shadowed[index] == 0
                    && substituted
                {
                    layout.occurrences[index].push(position);
                    layout.needs_free[index] |= asked;
                    captured[index] |= binders > 0;
                }
            }
            Pattern::Application { symbol, arguments } if aliases.contains_key(&symbol.name) => {
                let callee = &aliases[&symbol.name];
                let terms = &callee
                    .size
                    .as_ref()
                    .expect("callees are measured first")
                    .terms;
                pending.extend(arguments.iter().enumerate().map(|(index, argument)| {
                    Place::Enter(
                        argument,
                        substituted && terms[index] > 0,
                        asked || callee.layout.needs_free[index],
                    )
                }));
            }
            Pattern::AssociativeApplication {
                associativity,
                symbol,
                arguments,
            } if aliases.contains_key(&symbol.name) && arguments.len() >= 2 => {
                let callee = &aliases[&symbol.name];
                let links = Links::of(callee, *associativity, arguments.len());
                pending.extend(arguments.iter().enumerate().map(|(index, argument)| {
                    let (kept, argument_asked) = links.argument(index, asked);
                    Place::Enter(argument, substituted && kept, argument_asked)
                }));
            }
            Pattern::Exists { variable, body, .. }
            | Pattern::Forall { variable, body, .. }
            | Pattern::Mu { variable, body }
            | Pattern::Nu { variable, body } => {
                layout.names.insert(variable.name.clone());
                binders += 1;
                pending.push(Place::Leave);
                if let Some(&index) = parameters.get(variable.as_ref()) {
                    shadowed[index] += 1;
                    pending.push(Place::Unbind(index));
                }
                // The binder asks for the free variables of every argument substituted under it.
                pending.push(Place::Enter(body, substituted, true));
                continue;
            }
            _ => {
                let (first, second) = crate::nesting::children(pattern);
                pending.extend(
                    first
                        .iter()
                        .chain(second)
                        .map(|child| Place::Enter(child, substituted, asked)),
                );
            }
        }
        pending[start..].reverse();
    }
    layout.captured = (0..captured.len())
        .filter(|&index| captured[index])
        .collect();
    layout
}

/// Which links of the chain that an associative application of an alias folds into
/// ([`visit_associative`]) unfolding enters, and what it asks of their arguments.
#[derive(Clone, Copy)]
struct Links {
    associativity: kore::Associativity,
    /// The number of arguments, at least two.
    arguments: usize,
    /// Whether the alias keeps a copy of its first and of its second argument.
    keeps: (bool, bool),
    /// Whether it asks for the free variables of its first and of its second argument.
    asks: (bool, bool),
}

impl Links {
    fn of(alias: &AliasDefinition, associativity: kore::Associativity, arguments: usize) -> Self {
        let terms = &alias.size.as_ref().expect("aliases are measured").terms;
        Self {
            associativity,
            arguments,
            keeps: (terms[0] > 0, terms[1] > 0),
            asks: (alias.layout.needs_free[0], alias.layout.needs_free[1]),
        }
    }

    /// Whether unfolding enters link `link` (numbered as its last argument for a left
    /// associative chain, `f(link_{k-1}, a_k)`, and as its first for a right associative one,
    /// `f(a_k, link_{k+1})`), and whether it asks for the free variables of that link's unfolding,
    /// given whether the free variables of the whole chain are asked for.
    fn link(self, link: usize, asked: bool) -> (bool, bool) {
        let outermost = match self.associativity {
            kore::Associativity::Left => link + 1 == self.arguments,
            kore::Associativity::Right => link == 0,
        };
        // An inner link is the first argument (left associative) or the second (right
        // associative) of the link around it.
        let (keeps, asks) = match self.associativity {
            kore::Associativity::Left => (self.keeps.0, self.asks.0),
            kore::Associativity::Right => (self.keeps.1, self.asks.1),
        };
        if outermost {
            (true, asked)
        } else {
            (keeps, asked || asks)
        }
    }

    /// Whether unfolding unfolds argument `index` of the chain, and whether it asks for the free
    /// variables of its unfolding.
    fn argument(self, index: usize, asked: bool) -> (bool, bool) {
        let last = self.arguments - 1;
        // The link the argument is an argument of, and whether it is that link's first argument.
        let (link, first) = match self.associativity {
            kore::Associativity::Left if index == 0 => (1, true),
            kore::Associativity::Left => (index, false),
            kore::Associativity::Right if index == last => (last - 1, false),
            kore::Associativity::Right => (index, true),
        };
        let (entered, link_asked) = self.link(link, asked);
        let (keeps, asks) = if first {
            (self.keeps.0, self.asks.0)
        } else {
            (self.keeps.1, self.asks.1)
        };
        (entered && keeps, link_asked || asks)
    }
}

/// Unfold the aliases of `pattern` with a budget of its own.
pub(crate) fn expand<'p>(
    pattern: &'p kore::Pattern,
    aliases: &BTreeMap<String, AliasDefinition>,
) -> Result<Cow<'p, kore::Pattern>, DefinitionError> {
    expand_measured(pattern, aliases, None)
}

/// Unfold the aliases of `pattern`, after measuring what that builds and spending what it adds to
/// the pattern from `budget`, so an unfolding too large to use is refused before it is built. A
/// pattern that applies no alias is its own unfolding, and is returned as it is.
pub(crate) fn expand_within<'p>(
    pattern: &'p kore::Pattern,
    aliases: &BTreeMap<String, AliasDefinition>,
    budget: &mut UnfoldingBudget,
) -> Result<Cow<'p, kore::Pattern>, DefinitionError> {
    expand_measured(pattern, aliases, Some(budget))
}

/// [`expand_within`] with `budget`, or, when it is `None`, with the budget of an operation given
/// `pattern` alone ([`UnfoldingBudget::for_input`]), which the measurement sizes.
fn expand_measured<'p>(
    pattern: &'p kore::Pattern,
    aliases: &BTreeMap<String, AliasDefinition>,
    budget: Option<&mut UnfoldingBudget>,
) -> Result<Cow<'p, kore::Pattern>, DefinitionError> {
    let _span = measure::algorithm_span(Algorithm::BackendAliasUnfold);
    if aliases.is_empty() {
        return Ok(Cow::Borrowed(pattern));
    }
    let measurement = unfolded_size(Frame::pattern(pattern), aliases, &mut Measured::default())?;
    if !measurement.applies_alias {
        return Ok(Cow::Borrowed(pattern));
    }
    let added = measurement
        .unfolded
        .bound(|| body_names(aliases))
        .saturating_sub(measurement.written);
    match budget {
        Some(budget) => budget.spend(added)?,
        None => UnfoldingBudget::for_input(measurement.written).spend(added)?,
    }
    let mut expander = Expander::new(aliases);
    expander
        .expand(&mut Scope::pattern(), pattern, 0, false)
        .map(|(unfolded, _)| Cow::Owned(unfolded))
}

/// The number of variable names of the alias bodies ([`Layout::names`]), which [`Size::bound`]
/// takes as the most names of alias bodies a fresh-name search can reject.
fn body_names(aliases: &BTreeMap<String, AliasDefinition>) -> u64 {
    aliases
        .values()
        .map(|alias| u64::try_from(alias.layout.names.len()).unwrap_or(u64::MAX))
        .fold(0, u64::saturating_add)
}

/// The free variables of a pattern unfolding built, where unfolding asks for them: `None` when
/// it has none. The free variables of an argument are shared by its copies.
type Free = Option<Arc<BTreeSet<kore::Variable>>>;

/// What a variable of the pattern being unfolded stands for in a [`Scope`].
enum Binding {
    /// A parameter of the alias, and the unfolding of its argument: built once, copied for each
    /// occurrence that unfolding substitutes, and moved into the last (`remaining` counts the
    /// occurrences left). `free` holds its free variables when the layout asks for them.
    Argument {
        value: Option<kore::Pattern>,
        remaining: usize,
        free: Free,
    },
    /// A binder of the body renamed to avoid capturing a free variable of an argument.
    Renamed(kore::Variable),
}

/// Whether `name` has the form of a fresh name, `{base}Alias{digits}`
/// ([`Expander::rename_to_avoid_capture`]).
fn spells_fresh(name: &str) -> bool {
    let base = name.trim_end_matches(|character: char| character.is_ascii_digit());
    base.len() < name.len() && base.ends_with("Alias")
}

/// Whether some position of `positions`, in increasing order, is in `range`.
fn any_within(positions: &[usize], range: &Range<usize>) -> bool {
    positions
        .get(positions.partition_point(|&position| position < range.start))
        .is_some_and(|&position| position < range.end)
}

/// The pattern being unfolded, or the body of one application of an alias.
struct Scope<'a> {
    /// The alias whose body this is, `None` for the pattern being unfolded.
    alias: Option<&'a AliasDefinition>,
    /// The sort argument of each sort parameter.
    sorts: BTreeMap<&'a str, kore::Sort>,
    /// What each parameter, and each renamed binder around the current position, stands for.
    terms: BTreeMap<&'a kore::Variable, Binding>,
}

impl<'a> Scope<'a> {
    fn pattern() -> Self {
        Self {
            alias: None,
            sorts: BTreeMap::new(),
            terms: BTreeMap::new(),
        }
    }

    /// The positions of the subpatterns of the node at `position`, which follow it: each is the
    /// previous one plus the size of its subtree. Positions are not tracked outside alias bodies.
    fn children(&self, position: usize) -> Positions<'a> {
        Positions {
            subtree: self.alias.map(|alias| alias.layout.subtree.as_slice()),
            next: position + 1,
        }
    }
}

/// The positions of the subpatterns of one node, in order ([`Scope::children`]).
struct Positions<'s> {
    subtree: Option<&'s [usize]>,
    next: usize,
}

impl Positions<'_> {
    fn next(&mut self) -> usize {
        let position = self.next;
        if let Some(subtree) = self.subtree {
            self.next += subtree[position];
        }
        position
    }
}

/// Builds the unfolding of a pattern measured by [`unfolded_size`].
///
/// It builds what the measure counts, a renamed binder's longer name within [`Size::bound`].
/// Arguments are unfolded once, before the body of
/// their alias is entered, and only when the alias keeps a copy ([`Size`]): an argument the body
/// drops, or only uses under a binder that shadows its parameter, is never unfolded, so nothing
/// it would have unfolded to is built, and the measurement has already checked it. The unfolded
/// argument is copied for each occurrence the body substitutes but its last, into which it is
/// moved, so every node built for it is a node of the result. The links of an associative
/// application that the alias drops are not entered either.
///
/// A binder of a body is renamed when an argument substituted under it has its variable free.
/// The free variables of an argument are computed while it is unfolded, and only for the
/// parameters whose layout asks for them, so each node's are computed once, from its
/// subpatterns', by inserting the smaller set into the larger, which is extended in place
/// ([`Expander::union`]). A binder checks each parameter substituted under some binder of the
/// body ([`Layout::captured`]): whether it has an occurrence in the binder's range, and whether
/// its argument's set has the binder variable, so the check takes one lookup per parameter
/// whatever the number of free variables, and no pattern or set is rescanned.
///
/// A renamed binder takes the next fresh name of its base name that no variable of its body and
/// no variable built so far spells ([`Expander::rename_to_avoid_capture`]). Each base name's
/// index only grows through one unfolding, so a candidate is tried at most once: the fresh-name
/// search costs one try per renamed binder plus one per distinct name of the form
/// `{base}Alias{digits}` among the variables built and the bodies entered. The measure counts the
/// variables built; a name in a body entered is counted by it unless it lies in an argument that a
/// nested alias drops, so the tries the measure does not count are bounded by the size of the
/// definition's alias bodies, not by the request.
struct Expander<'a> {
    aliases: &'a BTreeMap<String, AliasDefinition>,
    /// For each base name, the index of its next fresh-name candidate, `{base}Alias{index}`.
    fresh: BTreeMap<String, u64>,
    /// The names of the variables built so far that have the form of a fresh name
    /// ([`spells_fresh`]).
    built: BTreeSet<String>,
    /// What the unfolding built besides its result, one unit per argument and the application
    /// node of each alias application it entered, and the capture checks of the binders of the
    /// bodies it entered ([`Size`]).
    #[cfg(test)]
    entered: u64,
    /// The other operations it performed: the elements it inserted into or copied between sets
    /// of free variables, the variables it removed from them, the fresh-name candidates it tried,
    /// and the names it recorded in [`Expander::built`].
    #[cfg(test)]
    steps: u64,
}

impl<'a> Expander<'a> {
    fn new(aliases: &'a BTreeMap<String, AliasDefinition>) -> Self {
        Self {
            aliases,
            fresh: BTreeMap::new(),
            built: BTreeSet::new(),
            #[cfg(test)]
            entered: 0,
            #[cfg(test)]
            steps: 0,
        }
    }

    fn step(&mut self, _count: usize) {
        #[cfg(test)]
        {
            self.steps += _count as u64;
        }
    }

    /// Unfold `pattern`, at `position` of the body of `scope`, and when `asked` its free
    /// variables.
    ///
    /// The recursion descends once per level of the pattern, so the stack held by one level bounds
    /// how deep a term can be internalized. Applications, the constructor that nests with term
    /// depth, are unfolded in [`Expander::expand_application`], whose frame holds only that case;
    /// every other constructor goes through [`Expander::expand_connective`]. Both return straight
    /// into this frame's result, so one level of an application spine costs this dispatch plus one
    /// application frame rather than the temporaries of every constructor case.
    fn expand(
        &mut self,
        scope: &mut Scope<'a>,
        pattern: &'a kore::Pattern,
        position: usize,
        asked: bool,
    ) -> Result<(kore::Pattern, Free), DefinitionError> {
        match pattern {
            kore::Pattern::Application { symbol, arguments } => {
                self.expand_application(scope, symbol, arguments, position, asked)
            }
            _ => self.expand_connective(scope, pattern, position, asked),
        }
    }

    fn expand_application(
        &mut self,
        scope: &mut Scope<'a>,
        symbol: &'a kore::Symbol,
        arguments: &'a [kore::Pattern],
        position: usize,
        asked: bool,
    ) -> Result<(kore::Pattern, Free), DefinitionError> {
        let Some(alias) = self.aliases.get(&symbol.name) else {
            let (arguments, free) = self.expand_many(scope, arguments, position, asked)?;
            return Ok((
                kore::Pattern::Application {
                    symbol: substitute_symbol(symbol, &scope.sorts),
                    arguments,
                },
                free,
            ));
        };
        let terms = &alias
            .size
            .as_ref()
            .expect("collect measures every alias")
            .terms;
        let mut positions = scope.children(position);
        let mut values = Vec::with_capacity(arguments.len());
        for (index, argument) in arguments.iter().enumerate() {
            let position = positions.next();
            values.push(if terms[index] == 0 {
                None
            } else {
                let asked = asked || alias.layout.needs_free[index];
                Some(self.expand(scope, argument, position, asked)?)
            });
        }
        let sorts = substitute_sorts(&symbol.sort_parameters, &scope.sorts);
        self.enter(alias, &symbol.name, sorts, values, asked)
    }

    /// Unfold the body of `alias` applied to the sort arguments `sorts` and to the unfolded
    /// arguments `values`, `None` for each argument the body keeps no copy of.
    fn enter(
        &mut self,
        alias: &'a AliasDefinition,
        _name: &str,
        sorts: Vec<kore::Sort>,
        values: Vec<Option<(kore::Pattern, Free)>>,
        asked: bool,
    ) -> Result<(kore::Pattern, Free), DefinitionError> {
        #[cfg(test)]
        {
            self.entered +=
                1 + length(_name) + sorts.iter().map(sort_size).sum::<u64>() + length_of(&values);
        }
        let terms = alias
            .parameters
            .iter()
            .zip(values)
            .enumerate()
            .filter_map(|(parameter, (variable, value))| {
                let (value, free) = value?;
                Some((
                    variable,
                    Binding::Argument {
                        value: Some(value),
                        remaining: alias.layout.occurrences[parameter].len(),
                        free,
                    },
                ))
            })
            .collect();
        let mut scope = Scope {
            alias: Some(alias),
            sorts: alias
                .sort_parameters
                .iter()
                .map(String::as_str)
                .zip(sorts)
                .collect(),
            terms,
        };
        // The body is unfolded below the frames of every alias body and pattern level enclosing
        // this application, and an alias body can apply further aliases. An operation provides
        // the stack for the whole unfolding up front (`nesting::height` counts each alias at its
        // unfolded height), and each body is also given the stack for its own levels where it is
        // entered, so an unfolding run without that provision cannot overflow either: the
        // recursion over the body's levels fits in it, and every deeper descent enters another
        // body. The measurement found no alias cycle, so the recursion through bodies ends.
        crate::nesting::with_stack(alias.depth, || {
            self.expand(&mut scope, &alias.right, 0, asked)
        })?
    }

    fn expand_many(
        &mut self,
        scope: &mut Scope<'a>,
        patterns: &'a [kore::Pattern],
        position: usize,
        asked: bool,
    ) -> Result<(Vec<kore::Pattern>, Free), DefinitionError> {
        let mut positions = scope.children(position);
        let mut free = None;
        let mut unfolded = Vec::with_capacity(patterns.len());
        for pattern in patterns {
            let position = positions.next();
            let (pattern, pattern_free) = self.expand(scope, pattern, position, asked)?;
            unfolded.push(pattern);
            if asked {
                free = self.union(free, pattern_free);
            }
        }
        Ok((unfolded, free))
    }

    /// Unfold the two subpatterns of a node at `position`.
    fn expand_pair(
        &mut self,
        scope: &mut Scope<'a>,
        left: &'a kore::Pattern,
        right: &'a kore::Pattern,
        position: usize,
        asked: bool,
    ) -> Result<(Box<kore::Pattern>, Box<kore::Pattern>, Free), DefinitionError> {
        let mut positions = scope.children(position);
        let left_position = positions.next();
        let right_position = positions.next();
        let (left, left_free) = self.expand(scope, left, left_position, asked)?;
        let (right, right_free) = self.expand(scope, right, right_position, asked)?;
        let free = if asked {
            self.union(left_free, right_free)
        } else {
            None
        };
        Ok((Box::new(left), Box::new(right), free))
    }

    fn expand_connective(
        &mut self,
        scope: &mut Scope<'a>,
        pattern: &'a kore::Pattern,
        position: usize,
        asked: bool,
    ) -> Result<(kore::Pattern, Free), DefinitionError> {
        use kore::Pattern;

        self.step(1);
        let sort = |sort: &kore::Sort, scope: &Scope<'a>| substitute_sort(sort, &scope.sorts);
        Ok(match pattern {
            Pattern::String(value) => (Pattern::String(value.clone()), None),
            Pattern::Variable(variable) => return Ok(self.expand_variable(scope, variable, asked)),
            Pattern::Application { symbol, arguments } => {
                return self.expand_application(scope, symbol, arguments, position, asked);
            }
            Pattern::Top { sort: top } => (
                Pattern::Top {
                    sort: sort(top, scope),
                },
                None,
            ),
            Pattern::Bottom { sort: bottom } => (
                Pattern::Bottom {
                    sort: sort(bottom, scope),
                },
                None,
            ),
            Pattern::And {
                sort: and,
                arguments,
            } => {
                let (arguments, free) = self.expand_many(scope, arguments, position, asked)?;
                (
                    Pattern::And {
                        sort: sort(and, scope),
                        arguments,
                    },
                    free,
                )
            }
            Pattern::Or {
                sort: or,
                arguments,
            } => {
                let (arguments, free) = self.expand_many(scope, arguments, position, asked)?;
                (
                    Pattern::Or {
                        sort: sort(or, scope),
                        arguments,
                    },
                    free,
                )
            }
            Pattern::Not {
                sort: not,
                argument,
            } => {
                let (argument, free) = self.expand(scope, argument, position + 1, asked)?;
                (
                    Pattern::Not {
                        sort: sort(not, scope),
                        argument: Box::new(argument),
                    },
                    free,
                )
            }
            Pattern::Next {
                sort: next,
                argument,
            } => {
                let (argument, free) = self.expand(scope, argument, position + 1, asked)?;
                (
                    Pattern::Next {
                        sort: sort(next, scope),
                        argument: Box::new(argument),
                    },
                    free,
                )
            }
            Pattern::Implies {
                sort: implies,
                left,
                right,
            } => {
                let (left, right, free) = self.expand_pair(scope, left, right, position, asked)?;
                (
                    Pattern::Implies {
                        sort: sort(implies, scope),
                        left,
                        right,
                    },
                    free,
                )
            }
            Pattern::Iff {
                sort: iff,
                left,
                right,
            } => {
                let (left, right, free) = self.expand_pair(scope, left, right, position, asked)?;
                (
                    Pattern::Iff {
                        sort: sort(iff, scope),
                        left,
                        right,
                    },
                    free,
                )
            }
            Pattern::Rewrites {
                sort: rewrites,
                left,
                right,
            } => {
                let (left, right, free) = self.expand_pair(scope, left, right, position, asked)?;
                (
                    Pattern::Rewrites {
                        sort: sort(rewrites, scope),
                        left,
                        right,
                    },
                    free,
                )
            }
            Pattern::Exists {
                sort,
                variable,
                body,
            } => {
                return self.expand_binder(
                    scope,
                    BinderKind::Exists,
                    Some(sort),
                    variable,
                    body,
                    position,
                    asked,
                );
            }
            Pattern::Forall {
                sort,
                variable,
                body,
            } => {
                return self.expand_binder(
                    scope,
                    BinderKind::Forall,
                    Some(sort),
                    variable,
                    body,
                    position,
                    asked,
                );
            }
            Pattern::Mu { variable, body } => {
                return self.expand_binder(
                    scope,
                    BinderKind::Mu,
                    None,
                    variable,
                    body,
                    position,
                    asked,
                );
            }
            Pattern::Nu { variable, body } => {
                return self.expand_binder(
                    scope,
                    BinderKind::Nu,
                    None,
                    variable,
                    body,
                    position,
                    asked,
                );
            }
            Pattern::Ceil {
                operand_sort,
                result_sort,
                argument,
            } => {
                let (argument, free) = self.expand(scope, argument, position + 1, asked)?;
                (
                    Pattern::Ceil {
                        operand_sort: Box::new(sort(operand_sort, scope)),
                        result_sort: sort(result_sort, scope),
                        argument: Box::new(argument),
                    },
                    free,
                )
            }
            Pattern::Floor {
                operand_sort,
                result_sort,
                argument,
            } => {
                let (argument, free) = self.expand(scope, argument, position + 1, asked)?;
                (
                    Pattern::Floor {
                        operand_sort: Box::new(sort(operand_sort, scope)),
                        result_sort: sort(result_sort, scope),
                        argument: Box::new(argument),
                    },
                    free,
                )
            }
            Pattern::Equals {
                operand_sort,
                result_sort,
                left,
                right,
            } => {
                let (left, right, free) = self.expand_pair(scope, left, right, position, asked)?;
                (
                    Pattern::Equals {
                        operand_sort: Box::new(sort(operand_sort, scope)),
                        result_sort: sort(result_sort, scope),
                        left,
                        right,
                    },
                    free,
                )
            }
            Pattern::In {
                operand_sort,
                result_sort,
                left,
                right,
            } => {
                let (left, right, free) = self.expand_pair(scope, left, right, position, asked)?;
                (
                    Pattern::In {
                        operand_sort: Box::new(sort(operand_sort, scope)),
                        result_sort: sort(result_sort, scope),
                        left,
                        right,
                    },
                    free,
                )
            }
            Pattern::DomainValue {
                sort: domain,
                value,
            } => (
                Pattern::DomainValue {
                    sort: sort(domain, scope),
                    value: value.clone(),
                },
                None,
            ),
            Pattern::AssociativeApplication {
                associativity,
                symbol,
                arguments,
            } => {
                if let Some(alias) = self.aliases.get(&symbol.name) {
                    return self.expand_associative(
                        scope,
                        pattern,
                        alias,
                        *associativity,
                        symbol,
                        arguments,
                        position,
                        asked,
                    );
                }
                let (arguments, free) = self.expand_many(scope, arguments, position, asked)?;
                (
                    Pattern::AssociativeApplication {
                        associativity: *associativity,
                        symbol: substitute_symbol(symbol, &scope.sorts),
                        arguments,
                    },
                    free,
                )
            }
        })
    }

    fn expand_variable(
        &mut self,
        scope: &mut Scope<'a>,
        variable: &'a kore::Variable,
        asked: bool,
    ) -> (kore::Pattern, Free) {
        match scope.terms.get_mut(variable) {
            Some(Binding::Argument {
                value,
                remaining,
                free,
                ..
            }) => {
                *remaining -= 1;
                // The last occurrence takes the unfolding and its free variables, so neither is
                // shared afterwards. A binder that needs the free variables precedes every
                // occurrence under it, so none needs them after the last.
                let (unfolded, free) = if *remaining == 0 {
                    (value.take(), free.take())
                } else {
                    (value.clone(), free.clone())
                };
                let unfolded =
                    unfolded.expect("an argument is substituted once for each counted occurrence");
                (unfolded, if asked { free } else { None })
            }
            Some(Binding::Renamed(renamed)) => {
                let free = asked.then(|| self.single(renamed.clone())).flatten();
                (kore::Pattern::Variable(renamed.clone()), free)
            }
            None => {
                let variable = substitute_variable(variable, &scope.sorts);
                self.record(&variable.name);
                let free = asked.then(|| self.single(variable.clone())).flatten();
                (kore::Pattern::Variable(variable), free)
            }
        }
    }

    /// Unfold an associative application of an alias as the chain of binary applications it
    /// folds into ([`visit_associative`]), entering only the links unfolding keeps and unfolding
    /// only the arguments they keep ([`Links`]).
    #[allow(clippy::too_many_arguments)]
    fn expand_associative(
        &mut self,
        scope: &mut Scope<'a>,
        pattern: &'a kore::Pattern,
        alias: &'a AliasDefinition,
        associativity: kore::Associativity,
        symbol: &'a kore::Symbol,
        arguments: &'a [kore::Pattern],
        position: usize,
        asked: bool,
    ) -> Result<(kore::Pattern, Free), DefinitionError> {
        match arguments {
            // Unfolding leaves it as written; it has no variables.
            [] => return Ok((pattern.clone(), None)),
            [argument] => return self.expand(scope, argument, position + 1, asked),
            _ => {}
        }
        let links = Links::of(alias, associativity, arguments.len());
        let mut positions = scope.children(position);
        let mut values = Vec::with_capacity(arguments.len());
        for (index, argument) in arguments.iter().enumerate() {
            let position = positions.next();
            let (kept, argument_asked) = links.argument(index, asked);
            values.push(if kept {
                Some(self.expand(scope, argument, position, argument_asked)?)
            } else {
                None
            });
        }
        let sorts = substitute_sorts(&symbol.sort_parameters, &scope.sorts);
        let last = arguments.len() - 1;
        let mut chain;
        match associativity {
            kore::Associativity::Left => {
                chain = values[0].take();
                for (link, value) in values.iter_mut().enumerate().skip(1) {
                    let (entered, link_asked) = links.link(link, asked);
                    if entered {
                        let applied = vec![chain.take(), value.take()];
                        chain = Some(self.enter(
                            alias,
                            &symbol.name,
                            sorts.clone(),
                            applied,
                            link_asked,
                        )?);
                    }
                }
            }
            kore::Associativity::Right => {
                chain = values[last].take();
                for link in (0..last).rev() {
                    let (entered, link_asked) = links.link(link, asked);
                    if entered {
                        let applied = vec![values[link].take(), chain.take()];
                        chain = Some(self.enter(
                            alias,
                            &symbol.name,
                            sorts.clone(),
                            applied,
                            link_asked,
                        )?);
                    }
                }
            }
        }
        Ok(chain.expect("the outermost link is always entered"))
    }

    #[allow(clippy::too_many_arguments)]
    fn expand_binder(
        &mut self,
        scope: &mut Scope<'a>,
        kind: BinderKind,
        sort: Option<&kore::Sort>,
        variable: &'a kore::Variable,
        body: &'a kore::Pattern,
        position: usize,
        asked: bool,
    ) -> Result<(kore::Pattern, Free), DefinitionError> {
        let substituted = substitute_variable(variable, &scope.sorts);
        let renamed = self.rename_to_avoid_capture(scope, variable, &substituted, position);
        // The binder shadows what its variable stood for around it.
        let shadowed = scope.terms.remove(variable);
        let bound = match renamed {
            Some(renamed) => {
                scope
                    .terms
                    .insert(variable, Binding::Renamed(renamed.clone()));
                renamed
            }
            None => substituted,
        };
        let unfolded = self.expand(scope, body, position + 1, asked);
        scope.terms.remove(variable);
        if let Some(shadowed) = shadowed {
            scope.terms.insert(variable, shadowed);
        }
        let (body, free) = unfolded?;
        let free = if asked {
            self.without(free, &bound)
        } else {
            None
        };
        let variable = Box::new(bound);
        let body = Box::new(body);
        let result_sort = || {
            substitute_sort(
                sort.expect("exists and forall have a result sort"),
                &scope.sorts,
            )
        };
        Ok((
            match kind {
                BinderKind::Exists => kore::Pattern::Exists {
                    sort: result_sort(),
                    variable,
                    body,
                },
                BinderKind::Forall => kore::Pattern::Forall {
                    sort: result_sort(),
                    variable,
                    body,
                },
                BinderKind::Mu => kore::Pattern::Mu { variable, body },
                BinderKind::Nu => kore::Pattern::Nu { variable, body },
            },
            free,
        ))
    }

    /// The fresh variable that the binder of `variable` at `position` of the body of `scope` is
    /// renamed to, when an argument substituted under it has `substituted` (the binder variable
    /// with its sort substituted) free, which the binder would otherwise capture.
    ///
    /// ```toml algorithm-site
    /// id = "backend.fresh.variables"
    /// role = "variant"
    /// sites = ["Expander::rename_to_avoid_capture"]
    /// ```
    fn rename_to_avoid_capture(
        &mut self,
        scope: &Scope<'a>,
        variable: &kore::Variable,
        substituted: &kore::Variable,
        position: usize,
    ) -> Option<kore::Variable> {
        let alias = scope.alias?;
        let captured = &alias.layout.captured;
        // One check for each parameter substituted under some binder of the body, which the
        // measure counts for each binder that unfolding enters ([`Size`]).
        #[cfg(test)]
        {
            self.entered += length_of(captured);
        }
        let range = position + 1..position + alias.layout.subtree[position];
        let free = captured
            .iter()
            .filter(|&&parameter| any_within(&alias.layout.occurrences[parameter], &range))
            .filter_map(
                |&parameter| match scope.terms.get(&alias.parameters[parameter]) {
                    Some(Binding::Argument {
                        free: Some(free), ..
                    }) => Some(free.as_ref()),
                    _ => None,
                },
            )
            .collect::<Vec<_>>();
        if !free.iter().any(|free| free.contains(substituted)) {
            return None;
        }
        // The fresh name is not the name of a variable of the body, so no binder of the body
        // captures its occurrences and it captures none of the body's. It is not the name of a
        // variable free in an argument substituted under the binder: those arguments were
        // unfolded before the body was entered, and the free variables of their unfoldings are
        // variables built since the unfolding began, whose names `built` records when they could
        // be fresh names, or renamed binders. Fresh names never repeat within one unfolding: the
        // digits after the last `Alias` give the index, what precedes it the base name, and each
        // base name's index only grows.
        // Nothing else can be free under the binder: an alias body has no free variable but its
        // parameters (verification refuses others), so the aliases it applies bring in only the
        // free variables of their arguments, which come from these. A rejected candidate is
        // never tried again in this unfolding, because the next search for the same base name
        // starts after it.
        let mut index = self.fresh.get(&variable.name).copied().unwrap_or(0);
        let name = loop {
            self.step(1);
            let name = format!("{}Alias{index}", variable.name);
            index += 1;
            if !alias.layout.names.contains(&name) && !self.built.contains(&name) {
                break name;
            }
        };
        self.fresh.insert(variable.name.clone(), index);
        Some(kore::Variable {
            kind: variable.kind,
            name,
            sort: substitute_sort(&variable.sort, &scope.sorts),
        })
    }

    /// Record `name`, of a variable unfolding built, when it has the form of a fresh name, which
    /// a binder renamed later must then not take.
    fn record(&mut self, name: &str) {
        if spells_fresh(name) && !self.built.contains(name) {
            self.step(1);
            self.built.insert(name.to_owned());
        }
    }

    fn single(&mut self, variable: kore::Variable) -> Free {
        self.step(1);
        Some(Arc::new(BTreeSet::from([variable])))
    }

    /// The union of two sets of free variables, inserting the smaller into the larger.
    ///
    /// The sets are taken by value, so the larger is extended in place unless another copy of
    /// the unfolding shares it ([`Expander::unique`]).
    fn union(&mut self, left: Free, right: Free) -> Free {
        let (mut larger, smaller) = match (left, right) {
            (Some(left), Some(right)) if left.len() >= right.len() => (left, right),
            (Some(left), Some(right)) => (right, left),
            (left, right) => return left.or(right),
        };
        if Arc::ptr_eq(&larger, &smaller) {
            return Some(larger);
        }
        self.step(smaller.len());
        let set = self.unique(&mut larger);
        match Arc::try_unwrap(smaller) {
            Ok(smaller) => set.extend(smaller),
            Err(smaller) => set.extend(smaller.iter().cloned()),
        }
        Some(larger)
    }

    /// `free` without `variable`.
    fn without(&mut self, free: Free, variable: &kore::Variable) -> Free {
        let mut free = free?;
        self.step(1);
        if free.contains(variable) {
            self.unique(&mut free).remove(variable);
        }
        (!free.is_empty()).then_some(free)
    }

    /// `free` itself, copied first when another copy of the unfolding shares it.
    ///
    /// Sets are shared only between the copies of one argument's unfolding: its binding hands a
    /// handle on its set to each copy but the last, which takes the set itself, as it takes the
    /// unfolding. Copying a shared set gives one handle a set of its own, so a set is copied at
    /// most once for each copy of the argument, and a copy of the argument is at least as large
    /// as its set of free variables, each of which occurs in it: copying sets costs no more than
    /// copying the arguments, which the measure counts.
    fn unique<'s>(
        &mut self,
        free: &'s mut Arc<BTreeSet<kore::Variable>>,
    ) -> &'s mut BTreeSet<kore::Variable> {
        if Arc::get_mut(free).is_none() {
            self.step(free.len());
        }
        Arc::make_mut(free)
    }
}

#[derive(Clone, Copy)]
enum BinderKind {
    Exists,
    Forall,
    Mu,
    Nu,
}

fn substitute_symbol(symbol: &kore::Symbol, sorts: &BTreeMap<&str, kore::Sort>) -> kore::Symbol {
    kore::Symbol {
        name: symbol.name.clone(),
        sort_parameters: substitute_sorts(&symbol.sort_parameters, sorts),
    }
}

fn substitute_sorts(
    sorts: &[kore::Sort],
    parameters: &BTreeMap<&str, kore::Sort>,
) -> Vec<kore::Sort> {
    sorts
        .iter()
        .map(|sort| substitute_sort(sort, parameters))
        .collect()
}

fn substitute_variable(
    variable: &kore::Variable,
    sorts: &BTreeMap<&str, kore::Sort>,
) -> kore::Variable {
    kore::Variable {
        kind: variable.kind,
        name: variable.name.clone(),
        sort: substitute_sort(&variable.sort, sorts),
    }
}

fn substitute_sort(sort: &kore::Sort, sorts: &BTreeMap<&str, kore::Sort>) -> kore::Sort {
    match sort {
        kore::Sort::Variable(name) => sorts
            .get(name.as_str())
            .cloned()
            .unwrap_or_else(|| sort.clone()),
        kore::Sort::Application { name, arguments } => kore::Sort::Application {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_sort(argument, sorts))
                .collect(),
        },
    }
}

#[cfg(test)]
mod tests {
    use indoc::indoc;
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;

    #[test]
    fn alpha_renames_alias_binders_to_avoid_capture() {
        let definition = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortValue{} []
                alias bind{}(SortValue{}) : SortValue{}
                    where bind{}(X:SortValue{}) := \exists{SortValue{}}(
                        Y:SortValue{},
                        \and{SortValue{}}(X:SortValue{}, Y:SortValue{})
                    ) []
            endmodule []
        "#})
        .expect("alias definition should parse");
        let modules = definition.modules.iter().collect::<Vec<_>>();
        let aliases =
            collect(&modules, &BTreeMap::new()).expect("alias definition should validate");
        let application = parse_pattern(indoc! {r#"
            bind{}(
                \and{SortValue{}}(Y:SortValue{}, YAlias0:SortValue{})
            )
        "#})
        .expect("alias application should parse");
        let expected = parse_pattern(indoc! {r#"
            \exists{SortValue{}}(
                YAlias1:SortValue{},
                \and{SortValue{}}(
                    \and{SortValue{}}(Y:SortValue{}, YAlias0:SortValue{}),
                    YAlias1:SortValue{}
                )
            )
        "#})
        .expect("expected expansion should parse");

        assert_eq!(
            expand(&application, &aliases).unwrap().into_owned(),
            expected
        );
    }

    #[test]
    fn alpha_renaming_respects_nested_shadowing() {
        let definition = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortValue{} []
                alias bind{}(SortValue{}) : SortValue{}
                    where bind{}(X:SortValue{}) := \exists{SortValue{}}(
                        Y:SortValue{},
                        \and{SortValue{}}(
                            X:SortValue{},
                            \exists{SortValue{}}(Y:SortValue{}, Y:SortValue{})
                        )
                    ) []
            endmodule []
        "#})
        .expect("alias definition should parse");
        let modules = definition.modules.iter().collect::<Vec<_>>();
        let aliases =
            collect(&modules, &BTreeMap::new()).expect("alias definition should validate");
        let application =
            parse_pattern("bind{}(Y:SortValue{})").expect("alias application should parse");
        let expected = parse_pattern(indoc! {r#"
            \exists{SortValue{}}(
                YAlias0:SortValue{},
                \and{SortValue{}}(
                    Y:SortValue{},
                    \exists{SortValue{}}(Y:SortValue{}, Y:SortValue{})
                )
            )
        "#})
        .expect("expected expansion should parse");

        assert_eq!(
            expand(&application, &aliases).unwrap().into_owned(),
            expected
        );
    }

    /// Every connective of an alias body is rebuilt with its sorts substituted, and every binder
    /// under one is renamed exactly when the parameter occurs in its scope. Under each
    /// connective, and on both sides of a binary one, `beside` holds a binder next to the
    /// parameter, which keeps its name, and a binder over it, which is renamed because the
    /// argument has its variable free. Both decisions read the layout at the positions the
    /// connectives pass down, so a connective that passes a wrong position renames the first
    /// binder or captures under the second.
    #[test]
    fn binders_under_every_connective_of_a_body_avoid_capture() {
        let beside = r"\and{T}(\exists{T}(Y:T, Y:T), \exists{T}(Y:T, \and{T}(X:T, Y:T)))";
        let body = [
            r"\not{T}(B)",
            r"\next{T}(B)",
            r"\implies{T}(B, B)",
            r"\iff{T}(B, B)",
            r"\ceil{T, T}(B)",
            r"\floor{T, T}(B)",
            r"\in{T, T}(B, B)",
            r"\mu{}(@Z:T, B)",
            r"\forall{T}(Z:T, B)",
            r"\equals{T, T}(B, B)",
            r"\rewrites{T}(B, B)",
            r"\iff{T}(\mu{}(@Y:T, @Y:T), \nu{}(@Y:T, \and{T}(X:T, @Y:T)))",
            r"\iff{T}(\nu{}(@Y:T, \and{T}(X:T, @Y:T)), \mu{}(@Y:T, @Y:T))",
            r"\bottom{T}()",
            r"\top{T}()",
            r#"\dv{T}("text")"#,
            r#"str{}("text")"#,
        ]
        .join(", ")
        .replace('B', beside);
        let aliases = aliases_of(&format!(
            "[] module MAIN sort S{{}} [] symbol str{{}}(S{{}}) : S{{}} []
                alias every{{T}}(T) : T where every{{T}}(X:T) := \\or{{T}}({body}) []
            endmodule []"
        ));
        let argument = r"\and{S{}}(Y:S{}, @Y:S{})";
        let mut renamed = 0..;
        let mut kept_and_renamed = || {
            let name = format!("YAlias{}", renamed.next().unwrap());
            format!(
                r"\and{{S{{}}}}(\exists{{S{{}}}}(Y:S{{}}, Y:S{{}}), \exists{{S{{}}}}({name}:S{{}}, \and{{S{{}}}}({argument}, {name}:S{{}})))"
            )
        };
        let expected = [
            format!(r"\not{{S{{}}}}({})", kept_and_renamed()),
            format!(r"\next{{S{{}}}}({})", kept_and_renamed()),
            format!(
                r"\implies{{S{{}}}}({}, {})",
                kept_and_renamed(),
                kept_and_renamed()
            ),
            format!(r"\iff{{S{{}}}}({}, {})", kept_and_renamed(), kept_and_renamed()),
            format!(r"\ceil{{S{{}}, S{{}}}}({})", kept_and_renamed()),
            format!(r"\floor{{S{{}}, S{{}}}}({})", kept_and_renamed()),
            format!(
                r"\in{{S{{}}, S{{}}}}({}, {})",
                kept_and_renamed(),
                kept_and_renamed()
            ),
            format!(r"\mu{{}}(@Z:S{{}}, {})", kept_and_renamed()),
            format!(r"\forall{{S{{}}}}(Z:S{{}}, {})", kept_and_renamed()),
            format!(
                r"\equals{{S{{}}, S{{}}}}({}, {})",
                kept_and_renamed(),
                kept_and_renamed()
            ),
            format!(
                r"\rewrites{{S{{}}}}({}, {})",
                kept_and_renamed(),
                kept_and_renamed()
            ),
            format!(
                r"\iff{{S{{}}}}(\mu{{}}(@Y:S{{}}, @Y:S{{}}), \nu{{}}(@YAlias0:S{{}}, \and{{S{{}}}}({argument}, @YAlias0:S{{}})))"
            ),
            format!(
                r"\iff{{S{{}}}}(\nu{{}}(@YAlias1:S{{}}, \and{{S{{}}}}({argument}, @YAlias1:S{{}})), \mu{{}}(@Y:S{{}}, @Y:S{{}}))"
            ),
            r"\bottom{S{}}()".to_owned(),
            r"\top{S{}}()".to_owned(),
            r#"\dv{S{}}("text")"#.to_owned(),
            r#"str{}("text")"#.to_owned(),
        ]
        .join(", ");
        let application = parse_pattern(&format!("every{{S{{}}}}({argument})")).unwrap();
        let expected = parse_pattern(&format!(r"\or{{S{{}}}}({expected})")).unwrap();
        assert_eq!(
            expand(&application, &aliases).map(Cow::into_owned),
            Ok(expected)
        );
    }

    /// Each unary connective and binder gives its child the child's own position in the body's
    /// layout, also when the child's first part has subpatterns of its own. The child here is
    /// `\and(\and(\top, \top), \exists(Y, \and(X, Y)))`: the binder over the parameter must be
    /// renamed, since the argument has `Y` free. Given any other position, the child's parts are
    /// laid over the wrong nodes, and the binder's range falls on a leaf of the first part, where
    /// no occurrence of `X` lies, so the binder is kept and captures the argument's `Y`. (With a
    /// first part of one child, as in the body test above, a child one position off lands the
    /// binder on its own body, whose occurrences are the same.)
    #[test]
    fn binders_after_a_nested_sibling_under_every_unary_connective_avoid_capture() {
        let child = r"\and{T}(\and{T}(\top{T}(), \top{T}()), \exists{T}(Y:T, \and{T}(X:T, Y:T)))";
        let body = [
            r"\not{T}(C)",
            r"\next{T}(C)",
            r"\ceil{T, T}(C)",
            r"\floor{T, T}(C)",
            r"\exists{T}(Z:T, C)",
            r"\forall{T}(Z:T, C)",
            r"\mu{}(@Z:T, C)",
            r"\nu{}(@Z:T, C)",
        ]
        .join(", ")
        .replace('C', child);
        let aliases = aliases_of(&format!(
            "[] module MAIN sort S{{}} []
                alias every{{T}}(T) : T where every{{T}}(X:T) := \\or{{T}}({body}) []
            endmodule []"
        ));
        let mut renamed = 0..;
        let mut child = || {
            let name = format!("YAlias{}", renamed.next().unwrap());
            format!(
                r"\and{{S{{}}}}(\and{{S{{}}}}(\top{{S{{}}}}(), \top{{S{{}}}}()), \exists{{S{{}}}}({name}:S{{}}, \and{{S{{}}}}(Y:S{{}}, {name}:S{{}})))"
            )
        };
        let expected = [
            format!(r"\not{{S{{}}}}({})", child()),
            format!(r"\next{{S{{}}}}({})", child()),
            format!(r"\ceil{{S{{}}, S{{}}}}({})", child()),
            format!(r"\floor{{S{{}}, S{{}}}}({})", child()),
            format!(r"\exists{{S{{}}}}(Z:S{{}}, {})", child()),
            format!(r"\forall{{S{{}}}}(Z:S{{}}, {})", child()),
            format!(r"\mu{{}}(@Z:S{{}}, {})", child()),
            format!(r"\nu{{}}(@Z:S{{}}, {})", child()),
        ]
        .join(", ");
        let application = parse_pattern("every{S{}}(Y:S{})").unwrap();
        let expected = parse_pattern(&format!(r"\or{{S{{}}}}({expected})")).unwrap();
        assert_eq!(
            expand(&application, &aliases).map(Cow::into_owned),
            Ok(expected)
        );
    }

    /// The free variables of an argument substituted under a binder are collected through every
    /// connective, from both sides of a binary one, and without the variables its own binders
    /// bind: the body's binder `Y` is renamed exactly when `Y` is free in the argument.
    #[test]
    fn free_variables_of_an_argument_are_collected_through_every_connective() {
        let aliases = aliases_of(indoc! {r#"
            []
            module MAIN
                sort S{} []
                symbol a{}() : S{} []
                alias bind{}(S{}) : S{}
                    where bind{}(X:S{}) := \exists{S{}}(
                        Y:S{},
                        \and{S{}}(X:S{}, Y:S{})
                    ) []
            endmodule []
        "#});
        let free = [
            r"\not{S{}}(Y:S{})",
            r"\next{S{}}(Y:S{})",
            r"\or{S{}}(a{}(), Y:S{})",
            r"\or{S{}}(Y:S{}, a{}())",
            r"\implies{S{}}(\top{S{}}(), Y:S{})",
            r"\implies{S{}}(Y:S{}, \bottom{S{}}())",
            r"\iff{S{}}(\top{S{}}(), Y:S{})",
            r"\iff{S{}}(Y:S{}, \top{S{}}())",
            r"\rewrites{S{}}(a{}(), Y:S{})",
            r"\rewrites{S{}}(Y:S{}, a{}())",
            r"\ceil{S{}, S{}}(Y:S{})",
            r"\floor{S{}, S{}}(Y:S{})",
            r"\equals{S{}, S{}}(a{}(), Y:S{})",
            r"\equals{S{}, S{}}(Y:S{}, a{}())",
            r"\in{S{}, S{}}(a{}(), Y:S{})",
            r"\in{S{}, S{}}(Y:S{}, a{}())",
            r"\mu{}(@Z:S{}, Y:S{})",
            r"\nu{}(@Z:S{}, Y:S{})",
            r"\forall{S{}}(Z:S{}, Y:S{})",
        ];
        let bound = [
            r"\or{S{}}(\exists{S{}}(Y:S{}, Y:S{}), \forall{S{}}(Y:S{}, Y:S{}))",
            r"\in{S{}, S{}}(\top{S{}}(), \exists{S{}}(Y:S{}, Y:S{}))",
            r#"\or{S{}}(@Y:S{}, \mu{}(@Y:S{}, @Y:S{}), \nu{}(@Z:S{}, @Z:S{}), \dv{S{}}("Y"))"#,
        ];
        for (arguments, binder) in [(&free[..], "YAlias0"), (&bound[..], "Y")] {
            for argument in arguments {
                let application = parse_pattern(&format!("bind{{}}({argument})")).unwrap();
                let expected = parse_pattern(&format!(
                    r"\exists{{S{{}}}}({binder}:S{{}}, \and{{S{{}}}}({argument}, {binder}:S{{}}))"
                ))
                .unwrap();
                assert_eq!(
                    expand(&application, &aliases).map(Cow::into_owned),
                    Ok(expected),
                    "{argument}"
                );
            }
        }
    }

    #[test]
    fn expands_aliases_through_associative_wrappers() {
        let definition = parse_definition(indoc! {r#"
            []
            module MAIN
                sort S{} []
                symbol f{}(S{}, S{}) : S{} []
                symbol a{}() : S{} []
                symbol b{}() : S{} []
                symbol c{}() : S{} []
                alias pair{}(S{}, S{}) : S{}
                    where pair{}(X:S{}, Y:S{}) := f{}(X:S{}, Y:S{}) []
            endmodule []
        "#})
        .expect("alias definition should parse");
        let modules = definition.modules.iter().collect::<Vec<_>>();
        let aliases =
            collect(&modules, &BTreeMap::new()).expect("alias definition should validate");
        let left = parse_pattern(r"\left-assoc{}(pair{}(a{}(), b{}(), c{}()))")
            .expect("left-associative alias application should parse");
        let right = parse_pattern(r"\right-assoc{}(pair{}(a{}(), b{}(), c{}()))")
            .expect("right-associative alias application should parse");

        assert_eq!(
            expand(&left, &aliases).unwrap().into_owned(),
            parse_pattern("f{}(f{}(a{}(), b{}()), c{}())").unwrap()
        );
        assert_eq!(
            expand(&right, &aliases).unwrap().into_owned(),
            parse_pattern("f{}(a{}(), f{}(b{}(), c{}()))").unwrap()
        );
    }

    fn aliases_of(source: &str) -> BTreeMap<String, AliasDefinition> {
        let definition = parse_definition(source).expect("alias definition should parse");
        let modules = definition.modules.iter().collect::<Vec<_>>();
        collect(&modules, &BTreeMap::new()).expect("alias definition should validate")
    }

    fn measured(
        pattern: &kore::Pattern,
        aliases: &BTreeMap<String, AliasDefinition>,
    ) -> Result<u64, DefinitionError> {
        unfolded_size(Frame::pattern(pattern), aliases, &mut Measured::default())
            .map(|measurement| measurement.unfolded.total())
    }

    /// The bound of what unfolding `pattern` builds, renamed binders included ([`Size::bound`]).
    fn bounded(pattern: &kore::Pattern, aliases: &BTreeMap<String, AliasDefinition>) -> u64 {
        unfolded_size(Frame::pattern(pattern), aliases, &mut Measured::default())
            .expect("the pattern should measure")
            .unfolded
            .bound(|| body_names(aliases))
    }

    /// What unfolding `pattern`, which must measure without error, builds: the unfolded pattern,
    /// what it built besides (the alias applications it entered, and its capture checks), and the
    /// operations it counted on sets of free variables and fresh names.
    fn unfold(
        pattern: &kore::Pattern,
        aliases: &BTreeMap<String, AliasDefinition>,
    ) -> (kore::Pattern, u64, u64) {
        let mut expander = Expander::new(aliases);
        let (unfolded, _) = expander
            .expand(&mut Scope::pattern(), pattern, 0, false)
            .expect("the pattern should unfold");
        (unfolded, expander.entered, expander.steps)
    }

    /// A chain of `length` aliases over `S{}`, each applying the next to its parameter twice, so
    /// that `al0` unfolds to `2^length` occurrences of its argument.
    fn doubling_chain(length: usize) -> String {
        let mut source = String::from(indoc! {r#"
            []
            module MAIN
                sort S{} []
                symbol pair{}(S{}, S{}) : S{} [constructor{}()]
        "#});
        for index in 0..length {
            let body = if index + 1 == length {
                "pair{}(X:S{}, X:S{})".to_owned()
            } else {
                let next = index + 1;
                format!("pair{{}}(al{next}{{}}(X:S{{}}), al{next}{{}}(X:S{{}}))")
            };
            source.push_str(&format!(
                "    alias al{index}{{}}(S{{}}) : S{{}} where al{index}{{}}(X:S{{}}) := {body} []\n"
            ));
        }
        source.push_str("endmodule []\n");
        source
    }

    /// The measured size of every unfolding is the size of what unfolding builds, the pattern
    /// `expand` returns and the alias applications it enters: through parameters used several
    /// times or not at all, sort parameters, nested and associative applications, associative
    /// links that the alias drops, and binders that shadow a parameter. (Binders that need
    /// renaming are left out: the fresh name is longer than the one written, which
    /// `an_unfolding_spends_at_least_what_its_renamed_binders_add` checks against the bound.)
    #[test]
    fn measures_the_size_of_the_unfolding_without_building_it() {
        let aliases = aliases_of(indoc! {r#"
            []
            module MAIN
                sort S{} []
                sort List{T} []
                symbol f{}(S{}, S{}) : S{} []
                symbol a{}() : S{} []
                symbol b{}() : S{} []
                symbol c{}() : S{} []
                symbol nil{T}() : List{T} []
                alias twice{}(S{}) : S{} where twice{}(X:S{}) := f{}(X:S{}, X:S{}) []
                alias drop{}(S{}) : S{} where drop{}(X:S{}) := a{}() []
                alias pair{}(S{}, S{}) : S{}
                    where pair{}(X:S{}, Y:S{}) := f{}(twice{}(Y:S{}), X:S{}) []
                alias nils{T}(S{}) : List{T}
                    where nils{T}(X:S{}) := \and{List{T}}(nil{T}(), nil{T}()) []
                alias nested{T}(S{}) : List{T}
                    where nested{T}(X:S{}) := nils{List{T}}(twice{}(X:S{})) []
                alias shadow{}(S{}) : S{}
                    where shadow{}(X:S{}) := f{}(
                        X:S{},
                        \exists{S{}}(X:S{}, f{}(X:S{}, X:S{}))
                    ) []
                alias first{}(S{}, S{}) : S{} where first{}(X:S{}, Y:S{}) := X:S{} []
                alias second{}(S{}, S{}) : S{} where second{}(X:S{}, Y:S{}) := Y:S{} []
                alias bind{}(S{}) : S{}
                    where bind{}(X:S{}) := \exists{S{}}(Y:S{}, f{}(X:S{}, twice{}(X:S{}))) []
                alias binds{}(S{}, S{}, S{}) : S{}
                    where binds{}(X:S{}, W:S{}, V:S{}) := f{}(
                        \exists{S{}}(Y:S{}, \forall{S{}}(Z:S{}, f{}(X:S{}, drop{}(V:S{})))),
                        f{}(\exists{S{}}(Y:S{}, W:S{}), \exists{S{}}(V:S{}, V:S{}))
                    ) []
            endmodule []
        "#});
        for source in [
            "twice{}(a{}())",
            "twice{}(twice{}(twice{}(f{}(a{}(), b{}()))))",
            "drop{}(twice{}(twice{}(Long:S{})))",
            "pair{}(a{}(), twice{}(b{}()))",
            "nils{List{List{S{}}}}(a{}())",
            "nested{List{S{}}}(twice{}(a{}()))",
            "shadow{}(twice{}(a{}()))",
            r"\left-assoc{}(pair{}(a{}(), b{}(), c{}(), twice{}(a{}())))",
            r"\right-assoc{}(pair{}(a{}(), b{}(), c{}(), twice{}(a{}())))",
            r"\left-assoc{}(pair{}(twice{}(a{}())))",
            r"\left-assoc{}(f{}(twice{}(a{}()), b{}()))",
            r"\exists{S{}}(X:S{}, \and{S{}}(twice{}(X:S{}), drop{}(X:S{})))",
            r"\left-assoc{}(first{}(twice{}(a{}()), b{}(), twice{}(c{}())))",
            r"\left-assoc{}(second{}(twice{}(a{}()), b{}(), twice{}(c{}())))",
            r"\right-assoc{}(first{}(twice{}(a{}()), b{}(), twice{}(c{}())))",
            r"\right-assoc{}(second{}(twice{}(a{}()), b{}(), twice{}(c{}())))",
            "bind{}(twice{}(f{}(Z:S{}, a{}())))",
            "binds{}(twice{}(a{}()), W:S{}, b{}())",
        ] {
            let pattern = parse_pattern(source).expect("pattern should parse");
            let expanded = expand(&pattern, &aliases).expect("pattern should unfold");
            let (unfolded, entered, _) = unfold(&pattern, &aliases);
            assert_eq!(unfolded, *expanded, "{source}");
            assert_eq!(
                measured(&pattern, &aliases),
                Ok(size(&expanded) + entered),
                "{source}"
            );
        }
        // An associative link that the alias drops is not entered, and the arguments inside it
        // are not unfolded.
        let dropped = |source: &str| unfold(&parse_pattern(source).unwrap(), &aliases);
        let (unfolded, entered, _) =
            dropped(r"\left-assoc{}(second{}(twice{}(a{}()), b{}(), twice{}(c{}())))");
        assert_eq!(unfolded, parse_pattern("f{}(c{}(), c{}())").unwrap());
        // One link of `second` (7 for the node, 2 for its arguments) and one of `twice` (6, 1).
        assert_eq!(entered, 9 + 7);
        let (unfolded, _, _) =
            dropped(r"\right-assoc{}(first{}(twice{}(a{}()), b{}(), twice{}(c{}())))");
        assert_eq!(unfolded, parse_pattern("f{}(a{}(), a{}())").unwrap());
    }

    /// Loading measures each body once, as a function of its arguments, and never unfolds one:
    /// a 64-alias chain whose first alias would unfold to 2^64 copies of its argument loads at
    /// once, and an application of it is refused before it is unfolded. The size of an
    /// 18-alias chain's unfolding is exact.
    #[test]
    fn measures_an_exponential_alias_chain_without_unfolding_it() {
        let aliases = aliases_of(&doubling_chain(64));
        let al0 = aliases["al0"]
            .size
            .as_ref()
            .expect("al0 should be measured");
        assert_eq!(al0.terms, vec![u64::MAX]);
        assert!(matches!(
            expand(&parse_pattern("al0{}(X:S{})").unwrap(), &aliases),
            Err(DefinitionError::AliasUnfoldingTooLarge { available, .. })
                if available == UNFOLDING_LIMIT
        ));

        let aliases = aliases_of(&doubling_chain(18));
        let application = parse_pattern("al0{}(X:S{})").unwrap();
        // 2^18 occurrences of `X:S{}` (4 each) and 2^18 - 1 `pair` nodes (5 each), and 2^k
        // entries into `al{k}`: the node and its name, and its one argument.
        let unfolded = (1_u64 << 18) * 4 + ((1 << 18) - 1) * 5;
        let entered = (0..18_u64)
            .map(|k| (1 << k) * (2 + length(&format!("al{k}"))))
            .sum::<u64>();
        assert_eq!(measured(&application, &aliases), Ok(unfolded + entered));
    }

    /// Whether an alias loads, or a pattern unfolds, does not depend on the names of the alias's
    /// parameters, which unfolding replaces: a 16-alias doubling chain whose first parameter has
    /// a 70-byte name loads, and its application to `a{}()` adds as much as with a one-byte name.
    #[test]
    fn the_names_of_alias_parameters_do_not_count() {
        let long = "X".repeat(70);
        let source = doubling_chain(16).replacen(
            "al0{}(X:S{}) := pair{}(al1{}(X:S{}), al1{}(X:S{}))",
            &format!(
                "al0{{}}({long}:S{{}}) := pair{{}}(al1{{}}({long}:S{{}}), al1{{}}({long}:S{{}}))"
            ),
            1,
        );
        assert!(source.contains(&long));
        let renamed = aliases_of(&source);
        let aliases = aliases_of(&doubling_chain(16));
        assert_eq!(renamed["al0"].size, aliases["al0"].size);
        let application = parse_pattern("al0{}(a{}())").unwrap();
        assert!(expand(&application, &renamed).is_ok());
        assert_eq!(
            measured(&application, &renamed),
            measured(&application, &aliases)
        );
    }

    /// Measuring a body takes time and memory linear in the body and the alias's parameters,
    /// however many parameters each subpattern mentions: a body that mentions every one of
    /// 20,000 parameters, and one that mentions the last of them 20,000 times, are measured in
    /// one pass each.
    #[test]
    fn measures_bodies_over_many_parameters_in_linear_time() {
        const PARAMETERS: usize = 20_000;
        let alias = |name: &str, body: &str| {
            let sorts = vec!["S{}"; PARAMETERS].join(", ");
            let parameters = (0..PARAMETERS)
                .map(|index| format!("X{index}:S{{}}"))
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "    alias {name}{{}}({sorts}) : S{{}} where {name}{{}}({parameters}) := {body} []\n"
            )
        };
        let every = (0..PARAMETERS)
            .map(|index| format!("X{index}:S{{}}"))
            .collect::<Vec<_>>()
            .join(", ");
        let last = format!("X{}:S{{}}", PARAMETERS - 1);
        let repeated = vec![format!("f{{}}({last}, {last})"); PARAMETERS / 2].join(", ");
        let source = format!(
            "[]\nmodule MAIN\n    sort S{{}} []\n    symbol f{{}}(S{{}}, S{{}}) : S{{}} []\n{}{}endmodule []\n",
            alias("every", &format!("\\and{{S{{}}}}({every})")),
            alias("last", &format!("\\and{{S{{}}}}({repeated})")),
        );
        let aliases = aliases_of(&source);
        let every = aliases["every"].size.as_ref().unwrap();
        assert_eq!(every.terms, vec![1; PARAMETERS]);
        // The `\and` and its sort `S{}`.
        assert_eq!(every.constant, 1 + 2);
        let last = aliases["last"].size.as_ref().unwrap();
        assert_eq!(last.terms[PARAMETERS - 1], PARAMETERS as u64);
        assert!(
            last.terms[..PARAMETERS - 1]
                .iter()
                .all(|&copies| copies == 0)
        );
        // The `\and`, its sort, and `PARAMETERS / 2` nodes `f{}` of 2.
        assert_eq!(last.constant, 3 + (PARAMETERS as u64 / 2) * 2);
    }

    /// A pattern that applies no alias is its own unfolding and is not copied.
    #[test]
    fn a_pattern_without_aliases_is_not_copied() {
        let aliases = aliases_of(&doubling_chain(2));
        let plain = parse_pattern(r"\exists{S{}}(X:S{}, pair{}(X:S{}, Y:S{}))").unwrap();
        assert!(matches!(expand(&plain, &aliases), Ok(Cow::Borrowed(_))));
        let applied = parse_pattern("pair{}(al1{}(X:S{}), Y:S{})").unwrap();
        assert_eq!(
            expand(&applied, &aliases).unwrap(),
            Cow::<kore::Pattern>::Owned(
                parse_pattern("pair{}(pair{}(X:S{}, X:S{}), Y:S{})").unwrap()
            )
        );
    }

    /// A pattern whose unfolding would add more than its operation's budget is refused before
    /// any of it is built, and the axioms of a definition share one budget.
    #[test]
    fn refuses_an_unfolding_beyond_the_budget_before_building_it() {
        let aliases = aliases_of(&doubling_chain(18));
        let twice = parse_pattern("pair{}(al0{}(X:S{}), al0{}(X:S{}))").unwrap();
        assert!(matches!(
            expand(&twice, &aliases),
            Err(DefinitionError::AliasUnfoldingTooLarge { added, available })
                if added > UNFOLDING_LIMIT && available == UNFOLDING_LIMIT
        ));

        let aliases = aliases_of(&doubling_chain(3));
        let once = parse_pattern("al0{}(X:S{})").unwrap();
        let added = measured(&once, &aliases).unwrap() - size(&once);
        let mut budget = UnfoldingBudget {
            available: 2 * added,
        };
        assert!(expand_within(&once, &aliases, &mut budget).is_ok());
        assert!(expand_within(&once, &aliases, &mut budget).is_ok());
        assert_eq!(
            expand_within(&once, &aliases, &mut budget),
            Err(DefinitionError::AliasUnfoldingTooLarge {
                added,
                available: 0,
            })
        );
    }

    /// A balanced tree of `pair` with `2^height` leaves `X:S{}`: a pattern without aliases whose
    /// written size grows with `height`.
    fn wide_pair_tree(height: u32) -> String {
        if height == 0 {
            "X:S{}".to_owned()
        } else {
            let half = wide_pair_tree(height - 1);
            format!("pair{{}}({half},{half})")
        }
    }

    /// A request may add up to `UNFOLDING_FACTOR` times its own written size, however far that is
    /// above the floor `UNFOLDING_LIMIT`, and is refused, before anything is built, beyond that:
    /// what an operation may build is bounded relative to what it was sent.
    #[test]
    fn a_request_may_add_a_multiple_of_its_own_size_and_no_more() {
        let aliases = aliases_of(&doubling_chain(18));
        let wide = wide_pair_tree(15);
        let application = "al0{}(X:S{})";

        let twice = parse_pattern(&format!(
            "pair{{}}(pair{{}}({application}, {application}), {wide})"
        ))
        .unwrap();
        let unfolded_size = measured(&twice, &aliases).unwrap();
        let added = unfolded_size - size(&twice);
        assert!(added > UNFOLDING_LIMIT);
        assert!(added <= UNFOLDING_FACTOR * size(&twice));
        let unfolded = expand(&twice, &aliases).expect("the request should unfold");
        assert_eq!(size(&unfolded) + unfold(&twice, &aliases).1, unfolded_size);

        let four = parse_pattern(&format!(
            "pair{{}}(pair{{}}(pair{{}}({application}, {application}), pair{{}}({application}, {application})), {wide})"
        ))
        .unwrap();
        let added = measured(&four, &aliases).unwrap() - size(&four);
        let available = UNFOLDING_FACTOR * size(&four);
        assert!(available > UNFOLDING_LIMIT && added > available);
        assert_eq!(
            expand(&four, &aliases),
            Err(DefinitionError::AliasUnfoldingTooLarge { added, available })
        );
    }

    /// Loading still finds every malformed alias application and cycle in the bodies, which it
    /// no longer unfolds.
    #[test]
    fn refuses_malformed_applications_and_cycles_in_alias_bodies() {
        let refused = |aliases: &str| {
            let source = format!(
                "[]\nmodule MAIN\n    sort S{{}} []\n    symbol a{{}}() : S{{}} []\n{aliases}\nendmodule []\n"
            );
            let definition = parse_definition(&source).expect("aliases should parse");
            let modules = definition.modules.iter().collect::<Vec<_>>();
            collect(&modules, &BTreeMap::new()).unwrap_err()
        };
        assert_eq!(
            refused(indoc! {r#"
                alias one{}(S{}) : S{} where one{}(X:S{}) := X:S{} []
                alias bad{}(S{}) : S{} where bad{}(X:S{}) := one{}(X:S{}, X:S{}) []
            "#}),
            DefinitionError::WrongAliasArity {
                alias: "one".into(),
                expected: 1,
                actual: 2,
            }
        );
        assert_eq!(
            refused(indoc! {r#"
                alias one{}(S{}) : S{} where one{}(X:S{}) := X:S{} []
                alias bad{}(S{}) : S{} where bad{}(X:S{}) := one{S{}}(X:S{}) []
            "#}),
            DefinitionError::WrongAliasSortArgumentCount {
                alias: "one".into(),
                expected: 0,
                actual: 1,
            }
        );
        assert_eq!(
            refused(indoc! {r#"
                alias one{}(S{}) : S{} where one{}(X:S{}) := X:S{} []
                alias bad{}(S{}) : S{} where bad{}(X:S{}) := \left-assoc{}(one{}(X:S{}, a{}())) []
            "#}),
            DefinitionError::WrongAliasArity {
                alias: "one".into(),
                expected: 1,
                actual: 2,
            }
        );
        assert_eq!(
            refused(indoc! {r#"
                alias a1{}(S{}) : S{} where a1{}(X:S{}) := a2{}(a{}()) []
                alias a2{}(S{}) : S{} where a2{}(X:S{}) := a3{}(X:S{}) []
                alias a3{}(S{}) : S{} where a3{}(X:S{}) := a2{}(X:S{}) []
            "#}),
            DefinitionError::AliasCycle(vec!["a2".into(), "a3".into(), "a2".into()])
        );
    }

    /// An argument that an alias keeps no copy of is not unfolded, so it adds nothing and costs
    /// nothing, however large its unfolding: on the 64-alias doubling chain, whose `al0{}(a{}())`
    /// would unfold to 2^64 nodes, `drop` (which ignores its parameter), `shadow` (which only uses
    /// it under a binder that shadows it), an alias whose body drops an application of `al0`, and
    /// associative links that drop it unfold at once, entering only the aliases they keep.
    #[test]
    fn arguments_an_alias_drops_are_not_unfolded() {
        let mut source = doubling_chain(64);
        source.truncate(source.rfind("endmodule").unwrap());
        source.push_str(indoc! {r#"
                symbol a{}() : S{} []
                alias drop{}(S{}) : S{} where drop{}(X:S{}) := a{}() []
                alias shadow{}(S{}) : S{} where shadow{}(X:S{}) := \exists{S{}}(X:S{}, X:S{}) []
                alias hide{}(S{}) : S{} where hide{}(X:S{}) := drop{}(al0{}(X:S{})) []
                alias second{}(S{}, S{}) : S{} where second{}(X:S{}, Y:S{}) := Y:S{} []
            endmodule []
        "#});
        let aliases = aliases_of(&source);
        for (applied, unfolded, entered) in [
            ("drop{}(al0{}(a{}()))", "a{}()", 1 + 4 + 1),
            (
                "shadow{}(al0{}(a{}()))",
                r"\exists{S{}}(X:S{}, X:S{})",
                1 + 6 + 1,
            ),
            ("hide{}(a{}())", "a{}()", (1 + 4 + 1) + (1 + 4 + 1)),
            (
                r"\left-assoc{}(second{}(al0{}(a{}()), al0{}(a{}()), a{}()))",
                "a{}()",
                1 + 6 + 2,
            ),
        ] {
            let pattern = parse_pattern(applied).unwrap();
            let expected = parse_pattern(unfolded).unwrap();
            assert_eq!(
                measured(&pattern, &aliases),
                Ok(size(&expected) + entered),
                "{applied}"
            );
            assert_eq!(
                expand(&pattern, &aliases).map(Cow::into_owned),
                Ok(expected.clone()),
                "{applied}"
            );
            let (unfolded, built, _) = unfold(&pattern, &aliases);
            assert_eq!((unfolded, built), (expected, entered), "{applied}");
        }
    }

    /// Entering an alias body is counted as building the application, so a chain that applies
    /// the next alias twice to its parameter and ends in the identity, whose unfolding is no
    /// larger than its argument but which unfolding would enter 2^64 times, is refused before
    /// any body is entered; so is a chain that doubles a sort argument that the last alias drops.
    #[test]
    fn entering_alias_bodies_counts_against_the_budget() {
        let chain = |length: usize, body: &dyn Fn(usize) -> String| {
            let mut source = String::from(indoc! {r#"
                []
                module MAIN
                    sort S{} []
                    sort P{A, B} []
                    symbol a{}() : S{} []
            "#});
            for index in 0..length {
                source.push_str(&body(index));
            }
            source.push_str("endmodule []\n");
            aliases_of(&source)
        };
        let identity = |length: usize| {
            chain(length, &move |index| {
                let body = if index + 1 == length {
                    "X:S{}".to_owned()
                } else {
                    let next = index + 1;
                    format!("c{next}{{}}(c{next}{{}}(X:S{{}}))")
                };
                format!(
                    "    alias c{index}{{}}(S{{}}) : S{{}} where c{index}{{}}(X:S{{}}) := {body} []\n"
                )
            })
        };
        let refused = |aliases: &BTreeMap<String, AliasDefinition>, source: &str| {
            matches!(
                expand(&parse_pattern(source).unwrap(), aliases),
                Err(DefinitionError::AliasUnfoldingTooLarge { .. })
            )
        };
        assert!(refused(&identity(64), "c0{}(a{}())"));
        let aliases = identity(10);
        let pattern = parse_pattern("c0{}(a{}())").unwrap();
        let (unfolded, entered, _) = unfold(&pattern, &aliases);
        assert_eq!(unfolded, parse_pattern("a{}()").unwrap());
        assert_eq!(measured(&pattern, &aliases), Ok(size(&unfolded) + entered));
        // 2^10 - 1 entries of 4 (the node, its name, its argument).
        assert_eq!(entered, ((1 << 10) - 1) * 4);

        let sorts = |length: usize| {
            chain(length, &move |index| {
                let body = if index + 1 == length {
                    "a{}()".to_owned()
                } else {
                    format!("s{}{{P{{T, T}}}}()", index + 1)
                };
                format!("    alias s{index}{{T}}() : S{{}} where s{index}{{T}}() := {body} []\n")
            })
        };
        assert!(refused(&sorts(64), "s0{S{}}()"));
        let aliases = sorts(8);
        let pattern = parse_pattern("s0{S{}}()").unwrap();
        let (unfolded, entered, _) = unfold(&pattern, &aliases);
        assert_eq!(unfolded, parse_pattern("a{}()").unwrap());
        assert_eq!(measured(&pattern, &aliases), Ok(size(&unfolded) + entered));
    }

    /// The work of unfolding, on free variables, capture checks, and fresh names, is bounded by
    /// what the measure counts, however many free variables the arguments have: a binder over an
    /// argument with many free variables; chains that pass such an argument through many binder
    /// bodies, nested in each other or entered side by side; and a chain that rebuilds an
    /// argument around it at each level. So are the fresh-name tries, however many renamed
    /// binders take a name of one base, or free variables of the argument spell candidates: a
    /// body whose nested binders are all renamed, entered several times; and a chain of binder
    /// bodies, each renamed, around an argument whose free variables spell the first candidates.
    #[test]
    fn unfolding_work_is_bounded_by_the_measure() {
        let definition = |aliases: &str| {
            aliases_of(&format!(
                "[]\nmodule MAIN\n    sort S{{}} []\n    symbol a{{}}() : S{{}} []\n    \
                 symbol f{{}}(S{{}}, S{{}}) : S{{}} []\n{aliases}endmodule []\n"
            ))
        };
        let alias = |name: &str, parameters: &[&str], body: &str| {
            let sorts = vec!["S{}"; parameters.len()].join(", ");
            let parameters = parameters
                .iter()
                .map(|parameter| format!("{parameter}:S{{}}"))
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "    alias {name}{{}}({sorts}) : S{{}} where {name}{{}}({parameters}) := {body} []\n"
            )
        };
        let chain =
            |length: usize, parameters: &[&str], step: &dyn Fn(&str) -> String, last: &str| {
                (0..length)
                    .map(|index| {
                        let body = if index + 1 == length {
                            last.to_owned()
                        } else {
                            step(&format!("c{}", index + 1))
                        };
                        alias(&format!("c{index}"), parameters, &body)
                    })
                    .collect::<String>()
            };
        let variables = |count: usize| {
            let variables = (0..count)
                .map(|index| format!("V{index}:S{{}}"))
                .collect::<Vec<_>>()
                .join(", ");
            format!("\\and{{S{{}}}}({variables})")
        };
        let many = variables(1000);
        let nested = format!(
            "{}X:S{{}}{}",
            r"\exists{S{}}(Y:S{}, ".repeat(300),
            ")".repeat(300)
        );
        let candidates = format!(
            "\\and{{S{{}}}}(Y:S{{}}, {})",
            (0..300)
                .map(|index| format!("YAlias{index}:S{{}}"))
                .collect::<Vec<_>>()
                .join(", ")
        );
        let cases = [
            (
                "a binder over many free variables",
                false,
                definition(&alias("c0", &["X"], r"\exists{S{}}(Y:S{}, X:S{})")),
                format!("c0{{}}({many})"),
            ),
            (
                "binders entered side by side",
                false,
                definition(&chain(
                    10,
                    &["X"],
                    &|next| format!("{next}{{}}({next}{{}}(X:S{{}}))"),
                    r"\exists{S{}}(Y:S{}, X:S{})",
                )),
                format!("c0{{}}({many})"),
            ),
            (
                "nested binders",
                false,
                definition(&chain(
                    200,
                    &["X"],
                    &|next| format!("\\exists{{S{{}}}}(Z:S{{}}, {next}{{}}(X:S{{}}))"),
                    "X:S{}",
                )),
                format!("c0{{}}({many})"),
            ),
            (
                "an argument rebuilt at each level",
                false,
                definition(&chain(
                    200,
                    &["X", "W"],
                    &|next| format!("{next}{{}}(f{{}}(X:S{{}}, W:S{{}}), W:S{{}})"),
                    r"\exists{S{}}(Y:S{}, f{}(X:S{}, W:S{}))",
                )),
                format!("c0{{}}({many}, Z:S{{}})"),
            ),
            (
                "nested binders all renamed, entered 8 times",
                true,
                definition(&alias("c0", &["X"], &nested)),
                format!("\\and{{S{{}}}}({})", ["c0{}(Y:S{})"; 8].join(", ")),
            ),
            (
                "renamed binders around candidates the argument spells",
                true,
                definition(&chain(
                    300,
                    &["X"],
                    &|next| format!("\\exists{{S{{}}}}(Y:S{{}}, {next}{{}}(X:S{{}}))"),
                    r"\exists{S{}}(Y:S{}, X:S{})",
                )),
                format!("c0{{}}({candidates})"),
            ),
        ];
        let mut exceeded = Vec::new();
        for (shape, renames, aliases, source) in cases {
            let pattern = parse_pattern(&source).unwrap();
            let measured = measured(&pattern, &aliases).unwrap();
            let (unfolded, entered, steps) = unfold(&pattern, &aliases);
            let built = size(&unfolded) + entered;
            // A renamed binder is longer than written; the bound counts that too.
            if renames {
                assert!(measured < built, "{shape}");
            } else {
                assert_eq!(measured, built, "{shape}");
            }
            let bound = bounded(&pattern, &aliases);
            assert!(built <= bound, "{shape}: built {built}, bound {bound}");
            if steps > measured {
                exceeded.push(format!("{shape}: {steps} steps for {measured}"));
            }
        }
        assert!(exceeded.is_empty(), "{exceeded:#?}");
    }

    /// What an unfolding spends from its budget bounds what it adds, renamed binders included.
    /// A renamed binder's name is its base name with `Alias` and an index appended, so the
    /// binder and every variable it binds are built longer than they are written. An unfolding
    /// is refused by a budget one unit smaller than what it adds, and spends no less than that
    /// from a larger one. Shapes: one-byte binders, all renamed, nested in a body entered 8
    /// times; a chain of renamed binders around an argument whose free variables spell the
    /// first candidates, which pushes the indices furthest; and 2,000 bodies of 16 binders each.
    #[test]
    fn an_unfolding_spends_at_least_what_its_renamed_binders_add() {
        let module = |aliases: String| {
            aliases_of(&format!(
                "[]\nmodule MAIN\n    sort S{{}} []\n{aliases}endmodule []\n"
            ))
        };
        let alias = |name: &str, body: &str| {
            format!("    alias {name}{{}}(S{{}}) : S{{}} where {name}{{}}(X:S{{}}) := {body} []\n")
        };
        let nested = |binders: usize| {
            format!(
                "{}X:S{{}}{}",
                r"\exists{S{}}(Y:S{}, ".repeat(binders),
                ")".repeat(binders)
            )
        };
        let chain = (0..300)
            .map(|index| {
                let body = if index == 299 {
                    r"\exists{S{}}(Y:S{}, X:S{})".to_owned()
                } else {
                    format!("\\exists{{S{{}}}}(Y:S{{}}, c{}{{}}(X:S{{}}))", index + 1)
                };
                alias(&format!("c{index}"), &body)
            })
            .collect::<String>();
        let candidates = format!(
            "\\and{{S{{}}}}(Y:S{{}}, {})",
            (0..300)
                .map(|index| format!("YAlias{index}:S{{}}"))
                .collect::<Vec<_>>()
                .join(", ")
        );
        let cases = [
            (
                "nested binders all renamed, entered 8 times",
                module(alias("c0", &nested(300))),
                format!("\\and{{S{{}}}}({})", ["c0{}(Y:S{})"; 8].join(", ")),
            ),
            (
                "renamed binders around candidates the argument spells",
                module(chain),
                format!("c0{{}}({candidates})"),
            ),
            (
                "2,000 bodies of 16 renamed binders",
                module(alias("c0", &nested(16))),
                format!("\\and{{S{{}}}}({})", vec!["c0{}(Y:S{})"; 2_000].join(", ")),
            ),
        ];
        for (shape, aliases, source) in cases {
            let pattern = parse_pattern(&source).unwrap();
            let (unfolded, entered, _) = unfold(&pattern, &aliases);
            let added = size(&unfolded) + entered - size(&pattern);
            let mut short = UnfoldingBudget {
                available: added - 1,
            };
            assert!(
                matches!(
                    expand_within(&pattern, &aliases, &mut short),
                    Err(DefinitionError::AliasUnfoldingTooLarge { .. })
                ),
                "{shape}: a budget of {} admitted an unfolding that adds {added}",
                added - 1
            );
            let mut budget = UnfoldingBudget::for_input(0);
            expand_within(&pattern, &aliases, &mut budget).expect("the unfolding fits the limit");
            let spent = UNFOLDING_LIMIT - budget.available;
            assert!(spent >= added, "{shape}: spent {spent} for {added}");
        }
    }

    /// A renamed binder takes the next fresh name of its base name that no variable of its body
    /// or built so far spells: candidates the argument spells are skipped once, and every later
    /// binder renamed from the same base name continues after the last fresh name.
    #[test]
    fn fresh_names_continue_after_the_last_one_taken() {
        let aliases = aliases_of(indoc! {r#"
            []
            module MAIN
                sort S{} []
                alias c0{}(S{}) : S{} where c0{}(X:S{}) := \exists{S{}}(Y:S{}, c1{}(X:S{})) []
                alias c1{}(S{}) : S{} where c1{}(X:S{}) := \exists{S{}}(Y:S{}, X:S{}) []
            endmodule []
        "#});
        let pattern = parse_pattern(r"c0{}(\and{S{}}(Y:S{}, YAlias0:S{}))").unwrap();
        let (unfolded, _, _) = unfold(&pattern, &aliases);
        assert_eq!(
            unfolded,
            parse_pattern(
                r"\exists{S{}}(YAlias1:S{}, \exists{S{}}(YAlias2:S{}, \and{S{}}(Y:S{}, YAlias0:S{})))"
            )
            .unwrap()
        );
    }

    /// The binder chain `c_i(X) := c_{i+1}(c_{i+1}(X))`, `c_{n-1}(X) := \exists(Y, X)` unfolds
    /// `c0` into 2^(n-1) nested binders around its argument. The free variables of each argument
    /// are computed once, from those of its parts, so unfolding takes work proportional to what
    /// it builds: adding one alias doubles the unfolding and at most doubles the operations on
    /// free variables and fresh names, whether the argument is closed, has a
    /// free variable, or has one that every binder would capture and is renamed to avoid.
    #[test]
    fn nested_binders_unfold_in_linear_time() {
        let chain = |length: usize| {
            let mut source = String::from(indoc! {r#"
                []
                module MAIN
                    sort S{} []
                    symbol a{}() : S{} []
                    symbol f{}(S{}, S{}) : S{} []
            "#});
            for index in 0..length {
                let body = if index + 1 == length {
                    r"\exists{S{}}(Y:S{}, X:S{})".to_owned()
                } else {
                    let next = index + 1;
                    format!("c{next}{{}}(c{next}{{}}(X:S{{}}))")
                };
                source.push_str(&format!(
                    "    alias c{index}{{}}(S{{}}) : S{{}} where c{index}{{}}(X:S{{}}) := {body} []\n"
                ));
            }
            source.push_str("endmodule []\n");
            aliases_of(&source)
        };
        let small = chain(2);
        let (unfolded, _, _) = unfold(&parse_pattern("c0{}(Y:S{})").unwrap(), &small);
        assert_eq!(
            unfolded,
            parse_pattern(r"\exists{S{}}(YAlias1:S{}, \exists{S{}}(YAlias0:S{}, Y:S{}))").unwrap()
        );
        let (shorter, longer) = (chain(11), chain(12));
        for argument in ["a{}()", "f{}(Z:S{}, a{}())", "f{}(Y:S{}, a{}())"] {
            let pattern = parse_pattern(&format!("c0{{}}({argument})")).unwrap();
            let (shorter_unfolded, _, shorter_steps) = unfold(&pattern, &shorter);
            let (longer_unfolded, _, longer_steps) = unfold(&pattern, &longer);
            assert!(size(&longer_unfolded) > 2 * size(&shorter_unfolded) - 20);
            assert!(
                longer_steps <= 2 * shorter_steps + 16,
                "{argument}: {shorter_steps} then {longer_steps}"
            );
        }
    }
}
