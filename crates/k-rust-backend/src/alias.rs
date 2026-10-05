//! ```toml algorithm
//! id = "backend.alias.unfold"
//! name = "capture-avoiding alias unfolding"
//! sites = ["expand", "expand_within", "expand_with", "collect", "measure_aliases", "unfolded_size"]
//! variable = "p = pattern size; o = expanded output size, at most p + UNFOLDING_LIMIT, since the unfolding is measured before it is built; b = binders visited; r = total size of the parameter map at a binder; B = total size of the alias bodies; a = the most parameters and sort parameters of one alias"
//! counters = []
//! no_counter = "alias unfolding has no dedicated counter; each alias body is measured once at load, and patterns are unfolded once per axiom at load and once per internalize_term or internalize_pattern request"
//! span = "per call"
//!
//! [[cost]]
//! mode = "one expand call"
//! bound = "O(p + o + b x (p + r))"
//!
//! [[cost]]
//! mode = "definition load (measure_aliases)"
//! bound = "O(B x (a + 1)) to measure each body once as a function of a coefficients, then one expand call per axiom, whose outputs together exceed the axioms by at most UNFOLDING_LIMIT"
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
//! unfold the aliases to check them. It measures, once per alias, the size of the body's unfolding as an affine
//! function of the sizes of the alias's arguments ([`Size`]), which composes along the chain in
//! time polynomial in the definition, and refuses an alias whose unfolding at its own parameters
//! would add more than [`UNFOLDING_LIMIT`]. Every pattern is measured the same way before it is
//! unfolded, and the unfolding is built only when it fits in the budget of its operation
//! ([`UnfoldingBudget`]).

use std::collections::{BTreeMap, BTreeSet};

use k_rust_kore::kore::ast as kore;
use k_rust_kore::measure::{self, Algorithm};

use crate::definition::DefinitionError;

/// The most that unfolding aliases may add to the [`size`] of the patterns of one operation: one
/// request pattern, or every axiom of a definition being loaded together. It also bounds what the
/// unfolding of one alias at its own parameters may add.
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

/// The size ([`size`]) of an unfolding as an affine function of the sizes of the arguments and
/// sort arguments of the alias whose body holds it: `constant`, plus each argument's size times
/// its coefficient in `terms`, plus each sort argument's size times its coefficient in `sorts`.
/// A missing coefficient is zero. The arithmetic saturates: a saturated size exceeds every
/// budget, and a saturated coefficient multiplies a size of at least one.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct Size {
    constant: u64,
    terms: Vec<u64>,
    sorts: Vec<u64>,
}

impl Size {
    fn constant(constant: u64) -> Self {
        Self {
            constant,
            ..Self::default()
        }
    }

    fn add_constant(&mut self, value: u64) {
        self.constant = self.constant.saturating_add(value);
    }

    /// Add `factor` times `other`.
    fn add_scaled(&mut self, factor: u64, other: &Self) {
        if factor == 0 {
            return;
        }
        self.add_constant(factor.saturating_mul(other.constant));
        add_scaled(&mut self.terms, factor, &other.terms);
        add_scaled(&mut self.sorts, factor, &other.sorts);
    }

    /// The size of an application of an alias whose body unfolds to `self`, to arguments and sort
    /// arguments of the given sizes.
    fn apply(&self, arguments: &[Self], sort_arguments: &[Self]) -> Self {
        let mut size = Self::constant(self.constant);
        for (factor, argument) in self.terms.iter().zip(arguments) {
            size.add_scaled(*factor, argument);
        }
        for (factor, argument) in self.sorts.iter().zip(sort_arguments) {
            size.add_scaled(*factor, argument);
        }
        size
    }
}

fn add_scaled(coefficients: &mut Vec<u64>, factor: u64, other: &[u64]) {
    if coefficients.len() < other.len() {
        coefficients.resize(other.len(), 0);
    }
    for (coefficient, value) in coefficients.iter_mut().zip(other) {
        *coefficient = coefficient.saturating_add(factor.saturating_mul(*value));
    }
}

fn unit(index: usize) -> Vec<u64> {
    let mut coefficients = vec![0; index + 1];
    coefficients[index] = 1;
    coefficients
}

fn length(name: &str) -> u64 {
    u64::try_from(name.len()).unwrap_or(u64::MAX)
}

/// The size of `pattern`: one for each pattern node and each sort node, plus the length of each
/// symbol, sort, and variable name, as `pattern` is written. Measured with a work list, so a
/// pattern of any depth is measured on a bounded stack.
pub(crate) fn size(pattern: &kore::Pattern) -> u64 {
    let mut total = 0_u64;
    let mut pending = vec![pattern];
    // Each pop pushes only proper subpatterns of the popped one, so the loop terminates.
    while let Some(pattern) = pending.pop() {
        total = total.saturating_add(own_size(pattern, &[]).constant);
        let (first, second) = crate::nesting::children(pattern);
        pending.extend(first.iter().chain(second));
    }
    total
}

/// The size of `sort` with each sort variable among `sort_parameters` standing for the sort
/// argument of that position.
fn sort_size(sort: &kore::Sort, sort_parameters: &[String]) -> Size {
    let mut size = Size::default();
    let add = |sort: &kore::Sort, size: &mut Size| match sort {
        kore::Sort::Variable(name) => {
            match sort_parameters
                .iter()
                .position(|parameter| parameter == name)
            {
                Some(index) => add_scaled(&mut size.sorts, 1, &unit(index)),
                None => size.add_constant(1 + length(name)),
            }
        }
        kore::Sort::Application { name, .. } => size.add_constant(1 + length(name)),
    };
    match sort {
        kore::Sort::Application { arguments, .. } if !arguments.is_empty() => {
            let mut pending = vec![sort];
            // Each pop pushes only proper subsorts of the popped one, so the loop terminates.
            while let Some(sort) = pending.pop() {
                add(sort, &mut size);
                if let kore::Sort::Application { arguments, .. } = sort {
                    pending.extend(arguments);
                }
            }
        }
        _ => add(sort, &mut size),
    }
    size
}

/// The size of `pattern`'s own node, without its subpatterns, its sorts substituted for
/// `sort_parameters` as [`sort_size`] does: the node, its name, the variable of a binder, and the
/// sorts it carries.
fn own_size(pattern: &kore::Pattern, sort_parameters: &[String]) -> Size {
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
    let mut size = Size::constant(1 + names);
    for sort in crate::nesting::sorts(pattern) {
        size.add_scaled(1, &sort_size(sort, sort_parameters));
    }
    size
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
                alias: None,
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
/// unfolding cannot terminate or is too large to use.
///
/// Every alias body is measured once, in the order its unfolding enters the bodies of the
/// aliases it applies, so an application anywhere in a body that is malformed for its alias
/// (`WrongAliasSortArgumentCount`, `WrongAliasArity`) or that applies an alias whose body is being
/// measured (`AliasCycle`, which unfolding would repeat forever) is found as unfolding would find
/// it, without building the unfolding. An alias whose unfolding at its own parameters would add
/// more than [`UNFOLDING_LIMIT`] is refused, since no operation could unfold it.
fn measure_aliases(aliases: &mut BTreeMap<String, AliasDefinition>) -> Result<(), DefinitionError> {
    let mut measured = BTreeMap::new();
    for name in aliases.keys() {
        if !measured.contains_key(name.as_str()) {
            unfolded_size(Frame::alias(name, &aliases[name]), &*aliases, &mut measured)?;
        }
    }
    for (name, alias) in aliases.iter() {
        let arguments = alias
            .parameters
            .iter()
            .map(|parameter| Size::constant(size(&kore::Pattern::Variable(parameter.clone()))))
            .collect::<Vec<_>>();
        let sort_arguments = alias
            .sort_parameters
            .iter()
            .map(|parameter| Size::constant(1 + length(parameter)))
            .collect::<Vec<_>>();
        let unfolded = measured[name.as_str()]
            .apply(&arguments, &sort_arguments)
            .constant;
        let written = arguments
            .iter()
            .chain(&sort_arguments)
            .fold(1 + length(name), |total, argument| {
                total.saturating_add(argument.constant)
            });
        let added = unfolded.saturating_sub(written);
        if added > UNFOLDING_LIMIT {
            return Err(DefinitionError::AliasUnfoldingTooLarge {
                alias: Some(name.clone()),
                added,
                available: UNFOLDING_LIMIT,
            });
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
    /// Measure this pattern: push its subpatterns, then its `Exit`.
    Enter(&'a kore::Pattern),
    /// Combine the sizes of this pattern's subpatterns, on top of `done`, into its own.
    Exit(&'a kore::Pattern),
    /// Combine the two sizes on top of `done` into that of one binary application of the alias
    /// `symbol`, a link of the chain an associative application of it folds into.
    Fold(&'a kore::Symbol),
}

/// The measurement of one pattern: a request's, or the body of the alias `alias`.
struct Frame<'a> {
    alias: Option<&'a str>,
    parameters: &'a [kore::Variable],
    sort_parameters: &'a [String],
    /// How many binders around the current visit bind each parameter, which then stands for
    /// itself rather than for its argument.
    shadowed: Vec<usize>,
    pending: Vec<Visit<'a>>,
    /// The sizes of the subpatterns measured so far whose parent is not.
    done: Vec<Size>,
}

impl<'a> Frame<'a> {
    fn pattern(pattern: &'a kore::Pattern) -> Self {
        Self {
            alias: None,
            parameters: &[],
            sort_parameters: &[],
            shadowed: Vec::new(),
            pending: vec![Visit::Enter(pattern)],
            done: Vec::new(),
        }
    }

    fn alias(name: &'a str, alias: &'a AliasDefinition) -> Self {
        Self {
            alias: Some(name),
            parameters: &alias.parameters,
            sort_parameters: &alias.sort_parameters,
            shadowed: vec![0; alias.parameters.len()],
            pending: vec![Visit::Enter(&alias.right)],
            done: Vec::new(),
        }
    }

    fn parameter(&self, variable: &kore::Variable) -> Option<usize> {
        self.parameters
            .iter()
            .position(|parameter| parameter == variable)
    }

    /// Pop the sizes of the last `count` subpatterns measured.
    fn take(&mut self, count: usize) -> Vec<Size> {
        self.done.split_off(self.done.len() - count)
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

/// The size of the unfolding of the pattern or alias body of `root`, as a function of the sizes
/// of the alias's arguments, with the sizes of alias bodies measured earlier in `measured` or in
/// their `size`. A body it needs that neither has is measured first and added to `measured`.
///
/// It reports the first malformed alias application, or alias cycle, that [`expand`] would meet
/// unfolding `root`: it visits the subpatterns and the links of the chains that associative
/// applications of aliases fold into in the order unfolding does, and enters a body where
/// unfolding would first enter it.
///
/// Every frame, pattern, and sort is measured with explicit work lists, so the stack it takes is
/// bounded whatever the depth of the patterns and of the chains of aliases.
fn unfolded_size<'a>(
    root: Frame<'a>,
    aliases: &'a BTreeMap<String, AliasDefinition>,
    measured: &mut BTreeMap<&'a str, Size>,
) -> Result<Size, DefinitionError> {
    // Invariant: `stack` names the aliases of `frames`, whose bodies are being measured, in
    // order; an application of one of them is a cycle.
    let mut stack = Entered::default();
    stack.extend(root.alias);
    let mut frames = vec![root];
    // Each iteration pops a visit, which pushes visits only for proper subpatterns, pushes a
    // frame for a body not yet measured (at most once per alias: the body is measured before the
    // visit that needed it is retried, and an alias already on the stack is a cycle), or
    // finishes a frame.
    while let Some(frame) = frames.last_mut() {
        let Some(visit) = frame.pending.pop() else {
            let size = frame.done.pop().unwrap_or_default();
            frames.pop();
            let Some(name) = stack.pop() else {
                return Ok(size);
            };
            if frames.is_empty() {
                measured.insert(name, size.clone());
                return Ok(size);
            }
            measured.insert(name, size);
            continue;
        };
        let callee = match visit {
            Visit::Enter(pattern) => {
                enter(frame, pattern, aliases);
                None
            }
            Visit::Exit(pattern) => exit(frame, pattern, aliases, measured, &stack)?,
            Visit::Fold(symbol) => {
                let callee = apply_alias(frame, symbol, 2, aliases, measured, &stack)?;
                if callee.is_some() {
                    frame.pending.push(Visit::Fold(symbol));
                }
                callee
            }
        };
        if let Some(name) = callee {
            stack.extend(Some(name));
            frames.push(Frame::alias(name, &aliases[name]));
        }
    }
    unreachable!("the measurement returns when it finishes its root frame")
}

fn enter<'a>(
    frame: &mut Frame<'a>,
    pattern: &'a kore::Pattern,
    aliases: &BTreeMap<String, AliasDefinition>,
) {
    use kore::Pattern;

    match pattern {
        Pattern::AssociativeApplication {
            associativity,
            symbol,
            arguments,
        } if aliases.contains_key(&symbol.name) => {
            // As `associative_application` folds it: an application of the alias for each
            // argument after the first, in the order unfolding enters them.
            let Some((first, rest)) = arguments.split_first() else {
                // Unfolding leaves it as written.
                frame.done.push(Size::constant(size(pattern)));
                return;
            };
            let mut steps = vec![Visit::Enter(first)];
            match associativity {
                kore::Associativity::Left => {
                    for argument in rest {
                        steps.push(Visit::Enter(argument));
                        steps.push(Visit::Fold(symbol));
                    }
                }
                kore::Associativity::Right => {
                    steps.extend(rest.iter().map(Visit::Enter));
                    steps.extend(rest.iter().map(|_| Visit::Fold(symbol)));
                }
            }
            frame.pending.extend(steps.into_iter().rev());
        }
        _ => {
            if let Pattern::Exists { variable, .. }
            | Pattern::Forall { variable, .. }
            | Pattern::Mu { variable, .. }
            | Pattern::Nu { variable, .. } = pattern
                && let Some(index) = frame.parameter(variable)
            {
                frame.shadowed[index] += 1;
            }
            frame.pending.push(Visit::Exit(pattern));
            let (first, second) = crate::nesting::children(pattern);
            frame
                .pending
                .extend(first.iter().chain(second).rev().map(Visit::Enter));
        }
    }
}

/// Combine the sizes of `pattern`'s subpatterns into its own, or name the alias whose body must
/// be measured first.
fn exit<'a>(
    frame: &mut Frame<'a>,
    pattern: &'a kore::Pattern,
    aliases: &'a BTreeMap<String, AliasDefinition>,
    measured: &BTreeMap<&'a str, Size>,
    stack: &Entered<'a>,
) -> Result<Option<&'a str>, DefinitionError> {
    use kore::Pattern;

    match pattern {
        Pattern::Variable(variable) => {
            if let Some(index) = frame.parameter(variable)
                && frame.shadowed[index] == 0
            {
                frame.done.push(Size {
                    constant: 0,
                    terms: unit(index),
                    sorts: Vec::new(),
                });
                return Ok(None);
            }
        }
        Pattern::Application { symbol, arguments } if aliases.contains_key(&symbol.name) => {
            let callee = apply_alias(frame, symbol, arguments.len(), aliases, measured, stack)?;
            if callee.is_some() {
                frame.pending.push(Visit::Exit(pattern));
            }
            return Ok(callee);
        }
        Pattern::Exists { variable, .. }
        | Pattern::Forall { variable, .. }
        | Pattern::Mu { variable, .. }
        | Pattern::Nu { variable, .. } => {
            if let Some(index) = frame.parameter(variable) {
                frame.shadowed[index] -= 1;
            }
        }
        _ => {}
    }
    let (first, second) = crate::nesting::children(pattern);
    let mut size = own_size(pattern, frame.sort_parameters);
    for child in frame.take(first.len() + second.len()) {
        size.add_scaled(1, &child);
    }
    frame.done.push(size);
    Ok(None)
}

/// Combine the sizes of the last `arity` subpatterns measured into the size of an application
/// of the alias `symbol` to them, checking the application as unfolding does, or name the alias
/// whose body must be measured first.
fn apply_alias<'a>(
    frame: &mut Frame<'a>,
    symbol: &kore::Symbol,
    arity: usize,
    aliases: &'a BTreeMap<String, AliasDefinition>,
    measured: &BTreeMap<&'a str, Size>,
    stack: &Entered<'a>,
) -> Result<Option<&'a str>, DefinitionError> {
    let Some((name, alias)) = aliases.get_key_value(&symbol.name) else {
        unreachable!("only applications of aliases are folded or applied")
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
    let Some(body) = measured.get(name.as_str()).or(alias.size.as_ref()) else {
        return Ok(Some(name));
    };
    let sort_arguments = symbol
        .sort_parameters
        .iter()
        .map(|sort| sort_size(sort, frame.sort_parameters))
        .collect::<Vec<_>>();
    let arguments = frame.take(arity);
    frame.done.push(body.apply(&arguments, &sort_arguments));
    Ok(None)
}

/// Unfold the aliases of `pattern` with a budget of its own.
pub(crate) fn expand(
    pattern: &kore::Pattern,
    aliases: &BTreeMap<String, AliasDefinition>,
) -> Result<kore::Pattern, DefinitionError> {
    expand_within(pattern, aliases, &mut UnfoldingBudget::new())
}

/// Unfold the aliases of `pattern`, after measuring what that adds to its size and spending it
/// from `budget`, so an unfolding too large to use is refused before it is built.
pub(crate) fn expand_within(
    pattern: &kore::Pattern,
    aliases: &BTreeMap<String, AliasDefinition>,
    budget: &mut UnfoldingBudget,
) -> Result<kore::Pattern, DefinitionError> {
    let _span = measure::algorithm_span(Algorithm::BackendAliasUnfold);
    if !aliases.is_empty() {
        let unfolded = unfolded_size(Frame::pattern(pattern), aliases, &mut BTreeMap::new())?;
        budget.spend(unfolded.constant.saturating_sub(size(pattern)))?;
    }
    expand_with(
        pattern,
        aliases,
        &BTreeMap::new(),
        &BTreeMap::new(),
        &mut Vec::new(),
    )
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

        assert_eq!(expand(&application, &aliases).unwrap(), expected);
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

        assert_eq!(expand(&application, &aliases).unwrap(), expected);
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
            expand(&left, &aliases).unwrap(),
            parse_pattern("f{}(f{}(a{}(), b{}()), c{}())").unwrap()
        );
        assert_eq!(
            expand(&right, &aliases).unwrap(),
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
            .map(|size| size.constant)
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
    /// a 64-alias chain whose first alias would unfold to 2^64 nodes is refused at once, naming
    /// it, while the 18-alias prefix of such a chain, which adds about 2.4 million, loads.
    #[test]
    fn refuses_an_exponential_alias_chain_at_load_without_unfolding_it() {
        let definition = parse_definition(&doubling_chain(64)).expect("the chain should parse");
        let modules = definition.modules.iter().collect::<Vec<_>>();
        let Err(DefinitionError::AliasUnfoldingTooLarge {
            alias: Some(alias),
            added,
            available,
        }) = collect(&modules, &BTreeMap::new())
        else {
            panic!("the chain should be refused as too large");
        };
        assert_eq!(alias, "al0");
        assert!(added > UNFOLDING_LIMIT);
        assert_eq!(available, UNFOLDING_LIMIT);

        let aliases = aliases_of(&doubling_chain(18));
        let application = parse_pattern("al0{}(X:S{})").unwrap();
        // 2^18 occurrences of `X:S{}` (4 each) and 2^18 - 1 `pair` nodes (5 each).
        let unfolded = (1_u64 << 18) * 4 + ((1 << 18) - 1) * 5;
        assert_eq!(measured(&application, &aliases), Ok(unfolded));
    }

    /// A pattern whose unfolding would add more than its operation's budget is refused before
    /// any of it is built, and the axioms of a definition share one budget.
    #[test]
    fn refuses_an_unfolding_beyond_the_budget_before_building_it() {
        let aliases = aliases_of(&doubling_chain(18));
        let twice = parse_pattern("pair{}(al0{}(X:S{}), al0{}(X:S{}))").unwrap();
        assert!(matches!(
            expand(&twice, &aliases),
            Err(DefinitionError::AliasUnfoldingTooLarge { alias: None, added, available })
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
                alias: None,
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
