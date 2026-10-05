//! ```toml algorithm
//! id = "backend.alias.unfold"
//! name = "capture-avoiding alias unfolding"
//! sites = ["expand", "expand_within", "expand_with", "collect", "measure_aliases", "unfolded_size", "measure_node", "visit_associative"]
//! variable = "p = pattern size; o = expanded output size, at most p + UNFOLDING_LIMIT, since the unfolding is measured before it is built; b = binders visited; r = total size of the parameter map at a binder; B = total size of the alias bodies; A = total parameters and sort parameters of the aliases"
//! counters = []
//! no_counter = "alias unfolding has no dedicated counter; each alias body is measured once at load, and patterns are unfolded once per axiom at load and once per internalize_term or internalize_pattern request"
//! span = "per call"
//!
//! [[cost]]
//! mode = "one expand call"
//! bound = "O(p + o + b x (p + r)); O(p) for a pattern that applies no alias, which is returned as it is"
//!
//! [[cost]]
//! mode = "definition load (measure_aliases)"
//! bound = "O(B + A) to measure each body once, top down, as a function of its parameters, then one expand call per axiom, whose outputs together exceed the axioms by at most UNFOLDING_LIMIT"
//! ```
//!
//! Capture-avoiding alias unfolding with a cycle stack, linear in the expanded output plus a clone
//! of the parameter map and a free-variable scan of the body and of the captured replacements at
//! each binder, at load time and per internalized request; no counter; the loops are the
//! cycle-stack recursion, the per-binder free-variable scans, the work lists of the size
//! measurement, and the fresh-name retry.
//!
//! An alias body may apply further aliases and use a parameter several times, so the unfolding of
//! a pattern can be exponentially larger than the pattern and the definition: a chain of `n`
//! aliases, each applying the next twice, unfolds to `2^n` nodes. Loading therefore does not
//! unfold the aliases to check them. It measures, once per alias, the size of the body's
//! unfolding as an affine function of the sizes of the alias's arguments ([`Size`]), in one top
//! down pass over the body that counts the copies the unfolding holds of each node, so the
//! measures compose along the chain in time linear in the definition. Every pattern is measured
//! the same way before it is unfolded, and the unfolding is built only when what it adds fits in
//! the budget of its operation ([`UnfoldingBudget`]).

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};

use k_rust_kore::kore::ast as kore;
use k_rust_kore::measure::{self, Algorithm};

use crate::definition::DefinitionError;

/// The most that unfolding aliases may add to the size ([`Size`]) of the patterns of one
/// operation: one request pattern, or every axiom of a definition being loaded together.
///
/// The size counts each pattern and sort node and each byte of the names they own, and a cloned
/// node allocates its own names, so memory grows with it: about 10 bytes per unit for nodes with
/// short names, and at most about 60 for nodes with one-byte names, on a 64-bit target. The limit,
/// 2^22 (4,194,304), therefore bounds the unfolded pattern of one operation to a few hundred MiB
/// at worst, which the internal terms built from it and every later pass over them multiply. A
/// pattern that large is too large to execute or prove anything about, while the aliases of
/// generated definitions (the modalities of claims, which unfold to their argument) add nothing,
/// and the patterns a client sends are not counted, only what unfolding adds to them.
pub(crate) const UNFOLDING_LIMIT: u64 = 1 << 22;

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
    /// The size of `right` with every alias in it unfolded, as a function of the sizes of the
    /// arguments of an application: `Some` once [`collect`] has measured it.
    pub(crate) size: Option<Size>,
}

/// The size of a pattern is one for each pattern node and each sort node, plus the length of each
/// symbol, sort, and variable name, as the pattern is written: names are owned strings that every
/// copy of a node copies, while string and domain values are shared and count as one node.
///
/// A `Size` is the size of the unfolding of an alias body, as an affine function of the sizes of
/// the arguments and sort arguments of an application of the alias: `constant`, plus each
/// argument's size times its coefficient in `terms`, plus each sort argument's size times its
/// coefficient in `sorts`, with one coefficient for each parameter and each sort parameter. A
/// coefficient is the number of copies of that argument the unfolding holds. The arithmetic
/// saturates: a saturated size exceeds every budget.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct Size {
    constant: u64,
    terms: Vec<u64>,
    sorts: Vec<u64>,
}

impl Size {
    /// Add `copies` copies of something of size `value`.
    fn add_constant(&mut self, copies: u64, value: u64) {
        self.constant = self.constant.saturating_add(copies.saturating_mul(value));
    }
}

fn add_copies(coefficient: &mut u64, copies: u64) {
    *coefficient = coefficient.saturating_add(copies);
}

fn length(name: &str) -> u64 {
    u64::try_from(name.len()).unwrap_or(u64::MAX)
}

/// The size of `pattern` as written ([`Size`]), with a work list.
#[cfg(test)]
fn size(pattern: &kore::Pattern) -> u64 {
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
    size: &mut Size,
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

/// Add `copies` copies of `pattern`'s own node, without its subpatterns, to `size`: the node, its
/// name, the variable of a binder, and the sorts it carries, substituted as [`add_sort`] does.
/// Return the size of that node as written.
fn add_own(
    size: &mut Size,
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
    add_own(&mut Size::default(), 0, pattern, &BTreeMap::new())
}

/// What unfolding may still add to the patterns of one operation ([`UNFOLDING_LIMIT`]).
pub(crate) struct UnfoldingBudget {
    available: u64,
}

impl UnfoldingBudget {
    pub(crate) fn new() -> Self {
        Self {
            available: UNFOLDING_LIMIT,
        }
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
/// (`nesting::alias_heights`) and the unfolded sizes measured by [`measure_aliases`].
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
/// unfolding cannot terminate.
///
/// Every alias body is measured once, entering the body of an alias it applies before that
/// application's arguments, so an application anywhere in a body that is malformed for its alias
/// (`WrongAliasSortArgumentCount`, `WrongAliasArity`) or that applies an alias whose body is being
/// measured (`AliasCycle`, which unfolding would repeat forever) is refused without building the
/// unfolding. The size of an alias is not checked against [`UNFOLDING_LIMIT`] here: it depends on
/// the arguments it is applied to, so only the patterns that apply it are checked, before they
/// are unfolded.
fn measure_aliases(aliases: &mut BTreeMap<String, AliasDefinition>) -> Result<(), DefinitionError> {
    let mut measured = BTreeMap::new();
    for (name, alias) in aliases.iter() {
        if !measured.contains_key(name.as_str()) {
            unfolded_size(Frame::alias(name, alias), aliases, &mut measured)?;
        }
    }
    let measured = measured
        .into_iter()
        .map(|(name, size)| (name.to_owned(), size))
        .collect::<Vec<_>>();
    for (name, size) in measured {
        if let Some(alias) = aliases.get_mut(&name) {
            alias.size = Some(size);
        }
    }
    Ok(())
}

/// One step of the size measurement of a pattern.
enum Visit<'a> {
    /// Measure this pattern, of which the unfolding holds this many copies: zero for an argument
    /// that an alias drops, which is still checked as unfolding checks it.
    Enter(&'a kore::Pattern, u64),
    /// Leave a binder of the parameter at this position.
    Unbind(usize),
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
    /// The size of the unfolding of what has been visited, as a function of the arguments.
    unfolded: Size,
    /// The size of what has been visited, as written.
    written: u64,
    /// Whether what has been visited applies an alias, so that unfolding changes it.
    applies_alias: bool,
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
        }
    }

    fn alias(name: &'a str, alias: &'a AliasDefinition) -> Self {
        Self {
            alias: Some(name),
            parameters: alias
                .parameters
                .iter()
                .enumerate()
                .map(|(index, parameter)| (parameter, index))
                .collect(),
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
            },
            written: 0,
            applies_alias: false,
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

/// The result of measuring a pattern or an alias body.
struct Measurement {
    /// The size of its unfolding, as a function of the arguments of the alias.
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
/// holds: a node of an argument of an alias application has as many copies as the application
/// times the alias's coefficient for that argument. So the measurement takes time linear in what
/// it visits, plus the parameters of the bodies it measures, whatever the number of parameters
/// and their occurrences. It reports a malformed alias application and an alias cycle as
/// unfolding would, entering the body of an alias before the arguments of its application.
///
/// Every frame, pattern, and sort is measured with explicit work lists, so the stack it takes is
/// bounded whatever the depth of the patterns and of the chains of aliases.
fn unfolded_size<'a>(
    root: Frame<'a>,
    aliases: &'a BTreeMap<String, AliasDefinition>,
    measured: &mut BTreeMap<&'a str, Size>,
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
            let measurement = Measurement {
                unfolded: frame.unfolded,
                written: frame.written,
                applies_alias: frame.applies_alias,
            };
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
                measure_node(frame, pattern, copies, aliases, measured, &stack)?
            }
            Visit::Unbind(index) => {
                frame.shadowed[index] -= 1;
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

/// Add `copies` copies of the unfolding of `pattern`'s own node to the measurement of `frame`, and
/// push its subpatterns with the copies the unfolding holds of each, or name the alias whose body
/// must be measured first.
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
            frame.written = frame.written.saturating_add(written_size(pattern));
            frame.unfolded.add_constant(copies, body.constant);
            add_sort_arguments(frame, copies, symbol, body);
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
                return Ok(None);
            }
        }
        Pattern::Exists { variable, .. }
        | Pattern::Forall { variable, .. }
        | Pattern::Mu { variable, .. }
        | Pattern::Nu { variable, .. } => {
            if let Some(&index) = frame.parameters.get(variable.as_ref()) {
                frame.shadowed[index] += 1;
                frame.pending.push(Visit::Unbind(index));
            }
        }
        _ => {}
    }
    let written = add_own(&mut frame.unfolded, copies, pattern, &frame.sort_parameters);
    frame.written = frame.written.saturating_add(written);
    let (first, second) = crate::nesting::children(pattern);
    frame.enter_in_order(first.iter().chain(second).map(|child| (child, copies)));
    Ok(None)
}

/// Measure an associative application of an alias as the chain of binary applications it folds
/// into: for `n` arguments, `n - 1` applications of the alias, each nested in the first argument
/// (left associative) or the second (right associative) of the one around it.
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
            frame.unfolded.add_constant(copies, written);
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
    // their total.
    let mut chain = copies;
    let mut links = 0_u64;
    let mut steps = Vec::with_capacity(arguments.len());
    match associativity {
        kore::Associativity::Left => {
            // f(f(f(a0, a1), a2), a3): the outermost link takes the last argument second.
            for argument in arguments[1..].iter().rev() {
                links = links.saturating_add(chain);
                steps.push((argument, chain.saturating_mul(right)));
                chain = chain.saturating_mul(left);
            }
            steps.push((first, chain));
            steps.reverse();
        }
        kore::Associativity::Right => {
            // f(a0, f(a1, f(a2, a3))): the outermost link takes the first argument first.
            for argument in &arguments[..arguments.len() - 1] {
                links = links.saturating_add(chain);
                steps.push((argument, chain.saturating_mul(left)));
                chain = chain.saturating_mul(right);
            }
            steps.push((last, chain));
        }
    }
    frame.unfolded.add_constant(links, body.constant);
    add_sort_arguments(frame, links, symbol, body);
    frame.enter_in_order(steps);
    Ok(None)
}

/// Add `copies` copies of what the sort arguments of `symbol` contribute to an unfolding of its
/// alias, whose body unfolds to `body`.
fn add_sort_arguments(frame: &mut Frame<'_>, copies: u64, symbol: &kore::Symbol, body: &Size) {
    for (sort, coefficient) in symbol.sort_parameters.iter().zip(&body.sorts) {
        add_sort(
            &mut frame.unfolded,
            copies.saturating_mul(*coefficient),
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

/// Unfold the aliases of `pattern` with a budget of its own.
pub(crate) fn expand<'p>(
    pattern: &'p kore::Pattern,
    aliases: &BTreeMap<String, AliasDefinition>,
) -> Result<Cow<'p, kore::Pattern>, DefinitionError> {
    expand_within(pattern, aliases, &mut UnfoldingBudget::new())
}

/// Unfold the aliases of `pattern`, after measuring what that adds to its size and spending it
/// from `budget`, so an unfolding too large to use is refused before it is built. A pattern that
/// applies no alias is its own unfolding, and is returned as it is.
pub(crate) fn expand_within<'p>(
    pattern: &'p kore::Pattern,
    aliases: &BTreeMap<String, AliasDefinition>,
    budget: &mut UnfoldingBudget,
) -> Result<Cow<'p, kore::Pattern>, DefinitionError> {
    let _span = measure::algorithm_span(Algorithm::BackendAliasUnfold);
    if aliases.is_empty() {
        return Ok(Cow::Borrowed(pattern));
    }
    let measurement = unfolded_size(Frame::pattern(pattern), aliases, &mut BTreeMap::new())?;
    if !measurement.applies_alias {
        return Ok(Cow::Borrowed(pattern));
    }
    budget.spend(
        measurement
            .unfolded
            .constant
            .saturating_sub(measurement.written),
    )?;
    expand_with(
        pattern,
        aliases,
        &BTreeMap::new(),
        &BTreeMap::new(),
        &mut Vec::new(),
    )
    .map(Cow::Owned)
}

/// Expands `pattern` under the sort and term substitutions of the enclosing alias bodies.
///
/// The recursion descends once per level of the pattern, so the stack held by one level bounds
/// how deep a term can be internalized. Applications, the constructor that nests with term
/// depth, are expanded in `expand_application`, whose frame holds only that case; every other
/// constructor goes through `expand_connective`. Both return straight into this frame's result,
/// so one level of an application spine costs this dispatch plus one application frame rather
/// than the temporaries of every constructor case.
fn expand_with(
    pattern: &kore::Pattern,
    aliases: &BTreeMap<String, AliasDefinition>,
    sorts: &BTreeMap<String, kore::Sort>,
    terms: &BTreeMap<kore::Variable, kore::Pattern>,
    stack: &mut Vec<String>,
) -> Result<kore::Pattern, DefinitionError> {
    match pattern {
        kore::Pattern::Application { symbol, arguments } => {
            expand_application(symbol, arguments, aliases, sorts, terms, stack)
        }
        _ => expand_connective(pattern, aliases, sorts, terms, stack),
    }
}

fn expand_application(
    symbol: &kore::Symbol,
    arguments: &[kore::Pattern],
    aliases: &BTreeMap<String, AliasDefinition>,
    sorts: &BTreeMap<String, kore::Sort>,
    terms: &BTreeMap<kore::Variable, kore::Pattern>,
    stack: &mut Vec<String>,
) -> Result<kore::Pattern, DefinitionError> {
    let symbol = substitute_symbol(symbol, sorts);
    let mut expanded = Vec::with_capacity(arguments.len());
    for argument in arguments {
        expanded.push(expand_with(argument, aliases, sorts, terms, stack)?);
    }
    let arguments = expanded;
    let Some(alias) = aliases.get(&symbol.name) else {
        return Ok(kore::Pattern::Application { symbol, arguments });
    };
    if symbol.sort_parameters.len() != alias.sort_parameters.len() {
        return Err(DefinitionError::WrongAliasSortArgumentCount {
            alias: symbol.name,
            expected: alias.sort_parameters.len(),
            actual: symbol.sort_parameters.len(),
        });
    }
    if arguments.len() != alias.parameters.len() {
        return Err(DefinitionError::WrongAliasArity {
            alias: symbol.name,
            expected: alias.parameters.len(),
            actual: arguments.len(),
        });
    }
    if let Some(start) = stack.iter().position(|name| name == &symbol.name) {
        let mut cycle = stack[start..].to_vec();
        cycle.push(symbol.name);
        return Err(DefinitionError::AliasCycle(cycle));
    }
    let alias_sorts = alias
        .sort_parameters
        .iter()
        .cloned()
        .zip(symbol.sort_parameters)
        .collect::<BTreeMap<_, _>>();
    let alias_terms = alias
        .parameters
        .iter()
        .cloned()
        .zip(arguments)
        .collect::<BTreeMap<_, _>>();
    // The body is unfolded below the frames of every alias body and pattern level enclosing this
    // application, and an alias body can apply further aliases. An operation provides the stack
    // for the whole unfolding up front (`nesting::height` counts each alias at its unfolded
    // height), and each body is also given the stack for its own levels where it is entered,
    // so an unfolding run without that provision cannot overflow either: the recursion over the
    // body's levels, and the helpers that rescan them, fit in it, and every deeper descent
    // enters another body.
    // Invariant: `stack` lists the aliases under expansion; a repeat on it is a cycle.
    stack.push(symbol.name);
    let result = crate::nesting::with_stack(alias.depth, || {
        expand_with(&alias.right, aliases, &alias_sorts, &alias_terms, stack)
    });
    stack.pop();
    result?
}

fn expand_connective(
    pattern: &kore::Pattern,
    aliases: &BTreeMap<String, AliasDefinition>,
    sorts: &BTreeMap<String, kore::Sort>,
    terms: &BTreeMap<kore::Variable, kore::Pattern>,
    stack: &mut Vec<String>,
) -> Result<kore::Pattern, DefinitionError> {
    use kore::Pattern;

    let recurse = |pattern: &Pattern, stack: &mut Vec<String>| {
        expand_with(pattern, aliases, sorts, terms, stack)
    };
    match pattern {
        Pattern::String(value) => Ok(Pattern::String(value.clone())),
        Pattern::Variable(variable) => Ok(terms
            .get(variable)
            .cloned()
            .unwrap_or_else(|| Pattern::Variable(substitute_variable(variable, sorts)))),
        Pattern::Application { symbol, arguments } => {
            expand_application(symbol, arguments, aliases, sorts, terms, stack)
        }
        Pattern::Top { sort } => Ok(Pattern::Top {
            sort: substitute_sort(sort, sorts),
        }),
        Pattern::Bottom { sort } => Ok(Pattern::Bottom {
            sort: substitute_sort(sort, sorts),
        }),
        Pattern::And { sort, arguments } => Ok(Pattern::And {
            sort: substitute_sort(sort, sorts),
            arguments: expand_many(arguments, aliases, sorts, terms, stack)?,
        }),
        Pattern::Or { sort, arguments } => Ok(Pattern::Or {
            sort: substitute_sort(sort, sorts),
            arguments: expand_many(arguments, aliases, sorts, terms, stack)?,
        }),
        Pattern::Not { sort, argument } => Ok(Pattern::Not {
            sort: substitute_sort(sort, sorts),
            argument: Box::new(recurse(argument, stack)?),
        }),
        Pattern::Next { sort, argument } => Ok(Pattern::Next {
            sort: substitute_sort(sort, sorts),
            argument: Box::new(recurse(argument, stack)?),
        }),
        Pattern::Implies { sort, left, right } => Ok(Pattern::Implies {
            sort: substitute_sort(sort, sorts),
            left: Box::new(recurse(left, stack)?),
            right: Box::new(recurse(right, stack)?),
        }),
        Pattern::Iff { sort, left, right } => Ok(Pattern::Iff {
            sort: substitute_sort(sort, sorts),
            left: Box::new(recurse(left, stack)?),
            right: Box::new(recurse(right, stack)?),
        }),
        Pattern::Rewrites { sort, left, right } => Ok(Pattern::Rewrites {
            sort: substitute_sort(sort, sorts),
            left: Box::new(recurse(left, stack)?),
            right: Box::new(recurse(right, stack)?),
        }),
        Pattern::Exists {
            sort,
            variable,
            body,
        } => expand_binder(
            BinderKind::Exists,
            Some(sort),
            variable,
            body,
            aliases,
            sorts,
            terms,
            stack,
        ),
        Pattern::Forall {
            sort,
            variable,
            body,
        } => expand_binder(
            BinderKind::Forall,
            Some(sort),
            variable,
            body,
            aliases,
            sorts,
            terms,
            stack,
        ),
        Pattern::Mu { variable, body } => expand_binder(
            BinderKind::Mu,
            None,
            variable,
            body,
            aliases,
            sorts,
            terms,
            stack,
        ),
        Pattern::Nu { variable, body } => expand_binder(
            BinderKind::Nu,
            None,
            variable,
            body,
            aliases,
            sorts,
            terms,
            stack,
        ),
        Pattern::Ceil {
            operand_sort,
            result_sort,
            argument,
        } => Ok(Pattern::Ceil {
            operand_sort: Box::new(substitute_sort(operand_sort, sorts)),
            result_sort: substitute_sort(result_sort, sorts),
            argument: Box::new(recurse(argument, stack)?),
        }),
        Pattern::Floor {
            operand_sort,
            result_sort,
            argument,
        } => Ok(Pattern::Floor {
            operand_sort: Box::new(substitute_sort(operand_sort, sorts)),
            result_sort: substitute_sort(result_sort, sorts),
            argument: Box::new(recurse(argument, stack)?),
        }),
        Pattern::Equals {
            operand_sort,
            result_sort,
            left,
            right,
        } => Ok(Pattern::Equals {
            operand_sort: Box::new(substitute_sort(operand_sort, sorts)),
            result_sort: substitute_sort(result_sort, sorts),
            left: Box::new(recurse(left, stack)?),
            right: Box::new(recurse(right, stack)?),
        }),
        Pattern::In {
            operand_sort,
            result_sort,
            left,
            right,
        } => Ok(Pattern::In {
            operand_sort: Box::new(substitute_sort(operand_sort, sorts)),
            result_sort: substitute_sort(result_sort, sorts),
            left: Box::new(recurse(left, stack)?),
            right: Box::new(recurse(right, stack)?),
        }),
        Pattern::DomainValue { sort, value } => Ok(Pattern::DomainValue {
            sort: substitute_sort(sort, sorts),
            value: value.clone(),
        }),
        Pattern::AssociativeApplication {
            associativity,
            symbol,
            arguments,
        } => {
            if aliases.contains_key(&symbol.name) {
                let Some(application) = associative_application(*associativity, symbol, arguments)
                else {
                    return Ok(pattern.clone());
                };
                return recurse(&application, stack);
            }
            Ok(Pattern::AssociativeApplication {
                associativity: *associativity,
                symbol: substitute_symbol(symbol, sorts),
                arguments: expand_many(arguments, aliases, sorts, terms, stack)?,
            })
        }
    }
}

fn associative_application(
    associativity: kore::Associativity,
    symbol: &kore::Symbol,
    arguments: &[kore::Pattern],
) -> Option<kore::Pattern> {
    let application = |arguments| kore::Pattern::Application {
        symbol: symbol.clone(),
        arguments,
    };
    match associativity {
        kore::Associativity::Left => {
            let mut arguments = arguments.iter().cloned();
            let first = arguments.next()?;
            Some(arguments.fold(first, |left, right| application(vec![left, right])))
        }
        kore::Associativity::Right => {
            let (last, rest) = arguments.split_last()?;
            Some(
                rest.iter()
                    .rev()
                    .cloned()
                    .fold(last.clone(), |right, left| application(vec![left, right])),
            )
        }
    }
}

fn expand_many(
    patterns: &[kore::Pattern],
    aliases: &BTreeMap<String, AliasDefinition>,
    sorts: &BTreeMap<String, kore::Sort>,
    terms: &BTreeMap<kore::Variable, kore::Pattern>,
    stack: &mut Vec<String>,
) -> Result<Vec<kore::Pattern>, DefinitionError> {
    patterns
        .iter()
        .map(|pattern| expand_with(pattern, aliases, sorts, terms, stack))
        .collect()
}

#[derive(Clone, Copy)]
enum BinderKind {
    Exists,
    Forall,
    Mu,
    Nu,
}

#[allow(clippy::too_many_arguments)]
fn expand_binder(
    kind: BinderKind,
    sort: Option<&kore::Sort>,
    variable: &kore::Variable,
    body: &kore::Pattern,
    aliases: &BTreeMap<String, AliasDefinition>,
    sorts: &BTreeMap<String, kore::Sort>,
    terms: &BTreeMap<kore::Variable, kore::Pattern>,
    stack: &mut Vec<String>,
) -> Result<kore::Pattern, DefinitionError> {
    let mut body_terms = terms.clone();
    body_terms.remove(variable);
    let substituted_variable = substitute_variable(variable, sorts);
    // The replacements are unfolded arguments, of any depth, so they and the body are scanned by
    // `Pattern::free_variables`, which reads them with an explicit work list.
    let body_free = body.free_variables();
    let (variable, body) = if body_terms.iter().any(|(parameter, replacement)| {
        body_free.contains(parameter)
            && replacement.free_variables().contains(&substituted_variable)
    }) {
        let fresh = fresh_variable(variable, body, &body_terms);
        let body = rename_bound_occurrences(body, variable, &fresh);
        (substitute_variable(&fresh, sorts), body)
    } else {
        (substituted_variable, body.clone())
    };
    let body = Box::new(expand_with(&body, aliases, sorts, &body_terms, stack)?);
    Ok(match kind {
        BinderKind::Exists => kore::Pattern::Exists {
            sort: substitute_sort(sort.expect("exists has a result sort"), sorts),
            variable: Box::new(variable),
            body,
        },
        BinderKind::Forall => kore::Pattern::Forall {
            sort: substitute_sort(sort.expect("forall has a result sort"), sorts),
            variable: Box::new(variable),
            body,
        },
        BinderKind::Mu => kore::Pattern::Mu {
            variable: Box::new(variable),
            body,
        },
        BinderKind::Nu => kore::Pattern::Nu {
            variable: Box::new(variable),
            body,
        },
    })
}

/// ```toml algorithm-site
/// id = "backend.fresh.variables"
/// role = "variant"
/// sites = ["fresh_variable"]
/// ```
fn fresh_variable(
    variable: &kore::Variable,
    body: &kore::Pattern,
    terms: &BTreeMap<kore::Variable, kore::Pattern>,
) -> kore::Variable {
    // The replacements are unfolded arguments, of any depth; `Pattern::variables` reads them
    // with an explicit work list.
    let mut names = BTreeSet::new();
    names.extend(body.variables().into_iter().map(|variable| variable.name));
    for (parameter, replacement) in terms {
        names.insert(parameter.name.clone());
        names.extend(
            replacement
                .variables()
                .into_iter()
                .map(|variable| variable.name),
        );
    }
    // Invariant: `index` only grows, so at most |names| + 1 candidates are tried.
    for index in 0usize.. {
        let name = format!("{}Alias{index}", variable.name);
        if names.insert(name.clone()) {
            return kore::Variable {
                kind: variable.kind,
                name,
                sort: variable.sort.clone(),
            };
        }
    }
    unreachable!("the set of finite variable names cannot exhaust every suffix")
}

fn rename_bound_occurrences(
    pattern: &kore::Pattern,
    old: &kore::Variable,
    new: &kore::Variable,
) -> kore::Pattern {
    use kore::Pattern;

    let recurse = |pattern: &Pattern| rename_bound_occurrences(pattern, old, new);
    match pattern {
        Pattern::String(value) => Pattern::String(value.clone()),
        Pattern::Variable(variable) => Pattern::Variable(if variable == old {
            new.clone()
        } else {
            variable.clone()
        }),
        Pattern::Application { symbol, arguments } => Pattern::Application {
            symbol: symbol.clone(),
            arguments: arguments.iter().map(recurse).collect(),
        },
        Pattern::Top { sort } => Pattern::Top { sort: sort.clone() },
        Pattern::Bottom { sort } => Pattern::Bottom { sort: sort.clone() },
        Pattern::And { sort, arguments } => Pattern::And {
            sort: sort.clone(),
            arguments: arguments.iter().map(recurse).collect(),
        },
        Pattern::Or { sort, arguments } => Pattern::Or {
            sort: sort.clone(),
            arguments: arguments.iter().map(recurse).collect(),
        },
        Pattern::Not { sort, argument } => Pattern::Not {
            sort: sort.clone(),
            argument: Box::new(recurse(argument)),
        },
        Pattern::Next { sort, argument } => Pattern::Next {
            sort: sort.clone(),
            argument: Box::new(recurse(argument)),
        },
        Pattern::Implies { sort, left, right } => Pattern::Implies {
            sort: sort.clone(),
            left: Box::new(recurse(left)),
            right: Box::new(recurse(right)),
        },
        Pattern::Iff { sort, left, right } => Pattern::Iff {
            sort: sort.clone(),
            left: Box::new(recurse(left)),
            right: Box::new(recurse(right)),
        },
        Pattern::Rewrites { sort, left, right } => Pattern::Rewrites {
            sort: sort.clone(),
            left: Box::new(recurse(left)),
            right: Box::new(recurse(right)),
        },
        Pattern::Exists {
            sort,
            variable,
            body,
        } => Pattern::Exists {
            sort: sort.clone(),
            variable: variable.clone(),
            body: if variable.as_ref() == old {
                body.clone()
            } else {
                Box::new(recurse(body))
            },
        },
        Pattern::Forall {
            sort,
            variable,
            body,
        } => Pattern::Forall {
            sort: sort.clone(),
            variable: variable.clone(),
            body: if variable.as_ref() == old {
                body.clone()
            } else {
                Box::new(recurse(body))
            },
        },
        Pattern::Mu { variable, body } => Pattern::Mu {
            variable: variable.clone(),
            body: if variable.as_ref() == old {
                body.clone()
            } else {
                Box::new(recurse(body))
            },
        },
        Pattern::Nu { variable, body } => Pattern::Nu {
            variable: variable.clone(),
            body: if variable.as_ref() == old {
                body.clone()
            } else {
                Box::new(recurse(body))
            },
        },
        Pattern::Ceil {
            operand_sort,
            result_sort,
            argument,
        } => Pattern::Ceil {
            operand_sort: operand_sort.clone(),
            result_sort: result_sort.clone(),
            argument: Box::new(recurse(argument)),
        },
        Pattern::Floor {
            operand_sort,
            result_sort,
            argument,
        } => Pattern::Floor {
            operand_sort: operand_sort.clone(),
            result_sort: result_sort.clone(),
            argument: Box::new(recurse(argument)),
        },
        Pattern::Equals {
            operand_sort,
            result_sort,
            left,
            right,
        } => Pattern::Equals {
            operand_sort: operand_sort.clone(),
            result_sort: result_sort.clone(),
            left: Box::new(recurse(left)),
            right: Box::new(recurse(right)),
        },
        Pattern::In {
            operand_sort,
            result_sort,
            left,
            right,
        } => Pattern::In {
            operand_sort: operand_sort.clone(),
            result_sort: result_sort.clone(),
            left: Box::new(recurse(left)),
            right: Box::new(recurse(right)),
        },
        Pattern::DomainValue { sort, value } => Pattern::DomainValue {
            sort: sort.clone(),
            value: value.clone(),
        },
        Pattern::AssociativeApplication {
            associativity,
            symbol,
            arguments,
        } => Pattern::AssociativeApplication {
            associativity: *associativity,
            symbol: symbol.clone(),
            arguments: arguments.iter().map(recurse).collect(),
        },
    }
}

fn substitute_symbol(symbol: &kore::Symbol, sorts: &BTreeMap<String, kore::Sort>) -> kore::Symbol {
    kore::Symbol {
        name: symbol.name.clone(),
        sort_parameters: symbol
            .sort_parameters
            .iter()
            .map(|sort| substitute_sort(sort, sorts))
            .collect(),
    }
}

fn substitute_variable(
    variable: &kore::Variable,
    sorts: &BTreeMap<String, kore::Sort>,
) -> kore::Variable {
    kore::Variable {
        kind: variable.kind,
        name: variable.name.clone(),
        sort: substitute_sort(&variable.sort, sorts),
    }
}

fn substitute_sort(sort: &kore::Sort, sorts: &BTreeMap<String, kore::Sort>) -> kore::Sort {
    match sort {
        kore::Sort::Variable(name) => sorts.get(name).cloned().unwrap_or_else(|| sort.clone()),
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
        unfolded_size(Frame::pattern(pattern), aliases, &mut BTreeMap::new())
            .map(|measurement| measurement.unfolded.constant)
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

    /// The measured size of every unfolding is the size of the pattern `expand` builds: through
    /// parameters used several times or not at all, sort parameters, nested and associative
    /// applications, and binders that shadow a parameter. (Binders that need renaming are left
    /// out: the fresh name is longer than the one measured.)
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
        ] {
            let pattern = parse_pattern(source).expect("pattern should parse");
            let expanded = expand(&pattern, &aliases).expect("pattern should unfold");
            assert_eq!(
                measured(&pattern, &aliases),
                Ok(size(&expanded)),
                "{source}"
            );
        }
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
        // 2^18 occurrences of `X:S{}` (4 each) and 2^18 - 1 `pair` nodes (5 each).
        let unfolded = (1_u64 << 18) * 4 + ((1 << 18) - 1) * 5;
        assert_eq!(measured(&application, &aliases), Ok(unfolded));
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
}
