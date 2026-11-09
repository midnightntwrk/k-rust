//! One equation that applies to one argument in two ways and gives it two
//! results.
//!
//! An equation `f(p̄) => r` holds for every way `p̄` matches the argument.
//! A map entry whose key and value are names or `_` bound nowhere else in
//! the pattern, beside a rest, `map![k -> v, rest @ ..]`, selects an entry:
//! on a map of two entries it matches in two ways, one per entry, and the
//! equation states its result for each. Where those results differ, it
//! states that they are equal, which is what two overlapping equations with
//! different results state ([`super::first_equation_overlap`]). A set's
//! element selects the same way (`set::concat(set::item(x), rest)`), since a
//! set is looked up by its elements as a map by its keys, and so does a
//! function context's map cell of one such entry beside its remainder
//! (`mem: Cell(map![k -> v, ..])`). A key or element
//! the rest of the pattern binds is looked up instead, and matches one way.
//!
//! As for a pair of equations, the check reports only what it can exhibit:
//! an argument at which both ways apply and give results that differ. It
//! reads an equation with no `requires` (a guard may let only one way
//! apply), one selection in its subject or its function context and every
//! other part of the pattern a name, `_`, a literal or a constructor, and a
//! result built by constructors and literals from the selection's key,
//! value or rest and the other names. The argument is a map of two entries
//! (a set of two elements) at two values of the key's sort, Int or Bool, and
//! a name of the pattern anywhere else; the selection's key differs between
//! the two ways, and its rest too (each holds the entry the other chose), so
//! a result whose constructors hold either differs, constructors being free.
//! An equation after a lower priority, or `owise`, applies only where no
//! earlier one does: it is read only when each earlier equation's pattern
//! excludes the argument (an empty map, another constructor, a literal).
//! Everything else, a fold such as `1 + Count(rest)` among it, is not
//! reported: whether its results agree is not decided here.

use std::collections::BTreeMap;

use krs_ir::{ApplicationRef, SemanticId, SemanticIdKind, SourceRange, StableItemId};
use krs_ir_levels::{
    MapOperands, SemanticModule, SemanticProduction, SemanticRule, SemanticTerm, SemanticTermKind,
    SetOperands,
};

use super::{Ground, equation_rank, function_equations};
use crate::coverage::{EquationSignature, Signature, binder_text, display_name};

/// An equation of one function that applies to one argument in two ways and
/// gives it different results.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct EquationChoice {
    /// The function, rendered.
    pub(crate) function: String,
    /// The equation.
    pub(crate) equation: StableItemId,
    /// The argument it applies to, rendered as an application, with the cell
    /// that holds the selected collection when its function context selects.
    pub(crate) application: String,
    /// The two ways it applies: the entry or element each selects.
    pub(crate) choices: (String, String),
    /// The result each way gives, rendered.
    pub(crate) results: (String, String),
    /// The exact authored range of the selecting pattern, when it has one.
    pub(crate) range: Option<SourceRange>,
}

/// The first equation, by function in declaration order and then by stable
/// identity, that applies to one argument in two ways with two results.
pub(crate) fn first_equation_choice(modules: &[SemanticModule]) -> Option<EquationChoice> {
    let signature = EquationSignature::new(modules);
    let signature = signature.signature();
    for (production, _, mut rules) in function_equations(modules) {
        rules.sort_by(|left, right| left.id().cmp(right.id()));
        for rule in &rules {
            let rank = equation_rank(rule);
            let earlier = rules
                .iter()
                .filter(|other| equation_rank(other) < rank)
                .copied()
                .collect::<Vec<_>>();
            if let Some(choice) = shown(signature, modules, production, rule, &earlier) {
                return Some(choice);
            }
        }
    }
    None
}

/// The selection a pattern holds.
enum Selection<'t> {
    /// `map![key -> value, rest @ ..]`, or a map cell's one entry beside its remainder.
    Map {
        key: &'t SemanticTerm,
        value: &'t SemanticTerm,
        rest: Rest<'t>,
    },
    /// `set::concat(set::item(element), rest)`.
    Set {
        element: &'t SemanticTerm,
        rest: Rest<'t>,
    },
}

/// A selection's rest.
#[derive(Clone, Copy)]
enum Rest<'t> {
    /// `..`, which names nothing.
    Anonymous,
    /// `rest @ ..`.
    Named(&'t SemanticId),
}

/// One selection and the term that holds it.
struct Site<'t> {
    term: &'t SemanticTerm,
    selection: Selection<'t>,
}

/// The argument a witness stands for, where an earlier equation's pattern is
/// compared with it ([`excludes`]).
enum Witness {
    /// Any term: a name or `_` of the pattern.
    Any,
    /// A literal, by its value where it is an Int or a Bool.
    Literal(Option<Ground>),
    /// A constructor applied to witnesses.
    Constructor(StableItemId, Vec<Witness>),
    /// The selected collection: a map of these keys, or a set of these
    /// elements.
    Collection { map: bool, parts: Vec<Ground> },
}

/// The collection a witness writes for a selection: two keys (or elements) and, for a map, the
/// two values where the value's sort has two the check writes.
struct Parts {
    map: bool,
    selected: [Ground; 2],
    values: Option<[Ground; 2]>,
}

impl Parts {
    fn of(signature: &Signature, selection: &Selection<'_>) -> Option<Self> {
        Some(match selection {
            Selection::Map { key, value, .. } => Self {
                map: true,
                selected: two_values(signature, key)?,
                values: two_values(signature, value),
            },
            Selection::Set { element, .. } => Self {
                map: false,
                selected: two_values(signature, element)?,
                values: None,
            },
        })
    }

    fn part(&self, index: usize) -> String {
        let selected = ground(&self.selected[index]);
        match &self.values {
            Some(values) => format!("{selected} -> {}", ground(&values[index])),
            None if self.map => format!("{selected} -> _"),
            None => selected,
        }
    }

    /// The collection of the parts at `indices`.
    fn collection(&self, indices: &[usize]) -> String {
        let parts = indices
            .iter()
            .map(|&index| self.part(index))
            .collect::<Vec<_>>();
        if self.map {
            format!("map![{}]", parts.join(", "))
        } else {
            format!("set![{}]", parts.join(", "))
        }
    }

    /// The entry or element the way `index` selects.
    fn choice(&self, index: usize) -> String {
        let selected = ground(&self.selected[index]);
        if self.map {
            format!("the entry at `{selected}`")
        } else {
            format!("the element `{selected}`")
        }
    }

    fn witness(&self) -> Witness {
        Witness::Collection {
            map: self.map,
            parts: self.selected.to_vec(),
        }
    }

    /// The result the way `chosen` gives: its names replaced by the chosen part and the rest
    /// that holds the other.
    fn result(
        &self,
        signature: &Signature,
        selection: &Selection<'_>,
        term: &SemanticTerm,
        chosen: usize,
    ) -> Option<String> {
        let mut substitution = BTreeMap::new();
        let rest = match selection {
            Selection::Map { key, value, rest } => {
                bind(&mut substitution, key, ground(&self.selected[chosen]));
                if let Some(values) = &self.values {
                    bind(&mut substitution, value, ground(&values[chosen]));
                }
                rest
            }
            Selection::Set { element, rest } => {
                bind(&mut substitution, element, ground(&self.selected[chosen]));
                rest
            }
        };
        if let Rest::Named(rest) = rest {
            substitution.insert(*rest, self.collection(&[1 - chosen]));
        }
        result(signature, term, &substitution)
    }
}

/// Whether one equation applies to one argument in two ways with two results
/// ([module docs](self)), and where.
fn shown(
    signature: &Signature,
    modules: &[SemanticModule],
    production: &SemanticProduction,
    rule: &SemanticRule,
    earlier: &[&SemanticRule],
) -> Option<EquationChoice> {
    if rule.requires().is_some() {
        return None;
    }
    let body = rule.body()?;
    let SemanticTermKind::Application { arguments, .. } = body.from().kind() else {
        return None;
    };
    let cells = rule
        .function_context()
        .map(|context| context.cells().cells().iter().collect::<Vec<_>>())
        .unwrap_or_default();
    let site = only_site(arguments, &cells)?;
    let holder = cells.iter().find(|cell| holds(cell.pattern(), site.term));
    if holder.is_some() && !earlier.is_empty() {
        return None;
    }
    let parts = Parts::of(signature, &site.selection)?;
    let first = parts.result(signature, &site.selection, body.to(), 0)?;
    let second = parts.result(signature, &site.selection, body.to(), 1)?;
    if first == second {
        return None;
    }
    let witness = parts.witness();
    let written = parts.collection(&[0, 1]);
    let mut rendered = Vec::new();
    let mut shapes = Vec::new();
    for argument in arguments {
        let (text, shape) = pattern(signature, argument, site.term, &written, &witness)?;
        rendered.push(text);
        shapes.push(shape);
    }
    if earlier
        .iter()
        .any(|other| !excluded(signature, other, &shapes))
    {
        return None;
    }
    let head = display_name(production.id());
    let mut application = format!("`{head}({})`", rendered.join(", "));
    if let Some(cell) = holder {
        let (text, _) = pattern(signature, cell.pattern(), site.term, &written, &witness)?;
        application = format!(
            "{application} where the cell `{}` holds `{text}`",
            cell_name(modules, cell.cell())
        );
    }
    Some(EquationChoice {
        function: head,
        equation: rule.id().clone(),
        application,
        choices: (parts.choice(0), parts.choice(1)),
        results: (first, second),
        range: site.term.origin().origin().exact_authored_range(),
    })
}

/// The one selection of a subject and its function context's cells, with every name counted
/// where both bind it; `None` for none or several.
fn only_site<'t>(
    arguments: &'t [SemanticTerm],
    cells: &[&'t krs_ir::FixedCellPattern<SemanticId, SemanticTerm>],
) -> Option<Site<'t>> {
    let patterns = || {
        arguments
            .iter()
            .chain(cells.iter().map(|cell| cell.pattern()))
    };
    let mut occurrences = BTreeMap::new();
    for term in patterns() {
        count(term, &mut occurrences);
    }
    let once = |term: &SemanticTerm| match term.kind() {
        SemanticTermKind::Variable { variable } => {
            matches!(variable.kind(), SemanticIdKind::Wildcard)
                || occurrences.get(variable) == Some(&1)
        }
        _ => false,
    };
    let mut sites = Vec::new();
    for term in patterns() {
        selections(term, &once, &mut sites);
    }
    sites.extend(cells.iter().filter_map(|cell| cell_selection(cell, &once)));
    let site = sites.pop()?;
    sites.is_empty().then_some(site)
}

/// The name the configuration declares a cell by, its Rust field where it has one, as a
/// `cells!` pattern writes it.
fn cell_name(modules: &[SemanticModule], id: &SemanticId) -> String {
    fn find<'c>(
        cells: &'c [krs_ir::FixedCell<krs_ir_levels::SemanticSortRef, SemanticId>],
        id: &SemanticId,
    ) -> Option<&'c krs_ir::FixedCell<krs_ir_levels::SemanticSortRef, SemanticId>> {
        cells.iter().find_map(|cell| {
            if cell.id() == id {
                return Some(cell);
            }
            match cell.content() {
                krs_ir::FixedCellContent::Children { children } => find(children, id),
                krs_ir::FixedCellContent::Term { .. } => None,
            }
        })
    }
    modules
        .iter()
        .filter_map(SemanticModule::configuration)
        .find_map(|configuration| find(configuration.cells(), id))
        .map_or_else(
            || id.as_str().to_owned(),
            |cell| cell.field().unwrap_or(cell.name()).to_owned(),
        )
}

/// Counts each named binder's occurrences in a pattern.
fn count<'t>(term: &'t SemanticTerm, occurrences: &mut BTreeMap<&'t SemanticId, usize>) {
    match term.kind() {
        SemanticTermKind::Variable { variable } => {
            if !matches!(variable.kind(), SemanticIdKind::Wildcard) {
                *occurrences.entry(variable).or_default() += 1;
            }
        }
        SemanticTermKind::As { alias, pattern } => {
            *occurrences.entry(alias).or_default() += 1;
            count(pattern, occurrences);
        }
        _ => {
            for child in term.children() {
                count(child, occurrences);
            }
        }
    }
}

/// Every selection in a pattern: a map of one entry and a rest whose key and value are names
/// or `_` bound nowhere else, or a set of one such element and a rest.
fn selections<'t>(
    term: &'t SemanticTerm,
    once: &dyn Fn(&SemanticTerm) -> bool,
    sites: &mut Vec<Site<'t>>,
) {
    let selection = match term.kind() {
        SemanticTermKind::Map(operands) => match &**operands {
            MapOperands::ItemsWithRest { items, rest } if items.len() == 1 => {
                let entry = items.first();
                rest_of(rest)
                    .filter(|_| once(&entry.key) && once(&entry.value))
                    .map(|rest| Selection::Map {
                        key: &entry.key,
                        value: &entry.value,
                        rest,
                    })
            }
            _ => None,
        },
        SemanticTermKind::Set(operands) => match &**operands {
            SetOperands::Concat { left, right } => {
                let item = |term: &'t SemanticTerm| match term.kind() {
                    SemanticTermKind::Set(operands) => match &**operands {
                        SetOperands::Item { element } => Some(element),
                        _ => None,
                    },
                    _ => None,
                };
                let parts = match (item(left), item(right)) {
                    (Some(element), None) => rest_of(right).map(|rest| (element, rest)),
                    (None, Some(element)) => rest_of(left).map(|rest| (element, rest)),
                    _ => None,
                };
                parts
                    .filter(|(element, _)| once(element))
                    .map(|(element, rest)| Selection::Set { element, rest })
            }
            _ => None,
        },
        _ => None,
    };
    if let Some(selection) = selection {
        sites.push(Site { term, selection });
        return;
    }
    for child in term.children() {
        selections(child, once, sites);
    }
}

/// A rest written as a name or `..`; `None` for a term that is neither.
fn rest_of(term: &SemanticTerm) -> Option<Rest<'_>> {
    match term.kind() {
        SemanticTermKind::Variable { variable } => {
            Some(if matches!(variable.kind(), SemanticIdKind::Wildcard) {
                Rest::Anonymous
            } else {
                Rest::Named(variable)
            })
        }
        _ => None,
    }
}

/// The selection of a function context's map cell whose pattern is one entry beside the cell's
/// remainder, `mem: Cell(map![k -> v, ..])`.
fn cell_selection<'t>(
    cell: &'t krs_ir::FixedCellPattern<SemanticId, SemanticTerm>,
    once: &dyn Fn(&SemanticTerm) -> bool,
) -> Option<Site<'t>> {
    let rest = match cell.frame() {
        krs_ir::CellContentFrame::MapRemainder { binding, .. } => {
            binding.as_ref().map_or(Rest::Anonymous, Rest::Named)
        }
        krs_ir::CellContentFrame::MovedMapRemainder { binding, .. } => Rest::Named(binding),
        _ => return None,
    };
    let term = cell.pattern();
    let SemanticTermKind::Map(operands) = term.kind() else {
        return None;
    };
    let MapOperands::Items(items) = &**operands else {
        return None;
    };
    let entry = items.first();
    (items.len() == 1 && once(&entry.key) && once(&entry.value)).then_some(Site {
        term,
        selection: Selection::Map {
            key: &entry.key,
            value: &entry.value,
            rest,
        },
    })
}

/// Whether `term` is `site` or holds it.
fn holds(term: &SemanticTerm, site: &SemanticTerm) -> bool {
    std::ptr::eq(term, site) || term.children().into_iter().any(|child| holds(child, site))
}

/// Two different values of a part's sort, for a name or `_` of a sort that holds two Ints
/// (an Int, a `KItem`, a sort above Int) or the two Bools; `None` for any other sort, whose
/// values the check does not write.
fn two_values(signature: &Signature, part: &SemanticTerm) -> Option<[Ground; 2]> {
    let sort = part.sort();
    if signature.value_in_sort(&Ground::Int(0), sort) == Some(true) {
        Some([Ground::Int(0), Ground::Int(1)])
    } else if signature.value_in_sort(&Ground::Bool(false), sort) == Some(true) {
        Some([Ground::Bool(false), Ground::Bool(true)])
    } else {
        None
    }
}

fn ground(value: &Ground) -> String {
    match value {
        Ground::Int(value) => value.to_string(),
        Ground::Bool(value) => value.to_string(),
        Ground::Term { .. } | Ground::Undefined => "_".to_owned(),
    }
}

/// Binds a part's name, if it has one, to its text in one way the equation applies.
fn bind<'t>(
    substitution: &mut BTreeMap<&'t SemanticId, String>,
    part: &'t SemanticTerm,
    text: String,
) {
    if let SemanticTermKind::Variable { variable } = part.kind()
        && !matches!(variable.kind(), SemanticIdKind::Wildcard)
    {
        substitution.insert(variable, text);
    }
}

/// A result built of constructors, literals and names, rendered with the selection's names
/// replaced; `None` for any other result, whose value the check does not compare.
fn result(
    signature: &Signature,
    term: &SemanticTerm,
    substitution: &BTreeMap<&SemanticId, String>,
) -> Option<String> {
    match term.kind() {
        SemanticTermKind::Variable { variable } => {
            substitution.get(variable).cloned().or_else(|| {
                (!matches!(variable.kind(), SemanticIdKind::Wildcard))
                    .then(|| binder_text(variable))
            })
        }
        SemanticTermKind::Token { value } => Some(value.clone()),
        SemanticTermKind::Application {
            application: ApplicationRef::Declared(id),
            arguments,
            ..
        } if signature.is_constructor(id) => {
            let arguments = arguments
                .iter()
                .map(|argument| result(signature, argument, substitution))
                .collect::<Option<Vec<_>>>()?;
            Some(format!("{}({})", display_name(id), arguments.join(", ")))
        }
        _ => None,
    }
}

/// A pattern rendered with `site` replaced by the witness collection, and the witness it
/// stands for; `None` for a pattern with any part but names, `_`, literals, constructors,
/// aliases and the site.
fn pattern(
    signature: &Signature,
    term: &SemanticTerm,
    site: &SemanticTerm,
    witness_text: &str,
    witness: &Witness,
) -> Option<(String, Witness)> {
    if std::ptr::eq(term, site) {
        let Witness::Collection { map, parts } = witness else {
            return None;
        };
        return Some((
            witness_text.to_owned(),
            Witness::Collection {
                map: *map,
                parts: parts.clone(),
            },
        ));
    }
    match term.kind() {
        SemanticTermKind::Variable { .. } => Some(("_".to_owned(), Witness::Any)),
        SemanticTermKind::As { pattern: inner, .. } => {
            pattern(signature, inner, site, witness_text, witness)
        }
        SemanticTermKind::Token { value } => Some((value.clone(), Witness::Literal(literal(term)))),
        SemanticTermKind::Application {
            application: ApplicationRef::Declared(id),
            arguments,
            ..
        } if signature.is_constructor(id) => {
            let mut texts = Vec::new();
            let mut shapes = Vec::new();
            for argument in arguments {
                let (text, shape) = pattern(signature, argument, site, witness_text, witness)?;
                texts.push(text);
                shapes.push(shape);
            }
            Some((
                format!("{}({})", display_name(id), texts.join(", ")),
                Witness::Constructor(id.clone(), shapes),
            ))
        }
        _ => None,
    }
}

/// A literal's value where it is an Int or a Bool.
fn literal(term: &SemanticTerm) -> Option<Ground> {
    let SemanticTermKind::Token { value } = term.kind() else {
        return None;
    };
    match term.sort() {
        krs_ir_levels::SemanticSortRef::Builtin(krs_ir::BuiltinSort::Int) => {
            value.parse().ok().map(Ground::Int)
        }
        krs_ir_levels::SemanticSortRef::Builtin(krs_ir::BuiltinSort::Bool) => {
            match value.as_str() {
                "true" => Some(Ground::Bool(true)),
                "false" => Some(Ground::Bool(false)),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Whether an earlier equation's subject excludes the witness: one of its arguments can match
/// no term the witness stands for. One with a function context, or a subject the check does
/// not read, excludes nothing.
fn excluded(signature: &Signature, rule: &SemanticRule, witness: &[Witness]) -> bool {
    let Some(body) = rule.body() else {
        return false;
    };
    let SemanticTermKind::Application { arguments, .. } = body.from().kind() else {
        return false;
    };
    arguments.len() == witness.len()
        && arguments
            .iter()
            .zip(witness)
            .any(|(argument, witness)| excludes(signature, argument, witness))
}

/// Whether a pattern matches no term the witness stands for.
fn excludes(signature: &Signature, term: &SemanticTerm, witness: &Witness) -> bool {
    match (term.kind(), witness) {
        (_, Witness::Any) | (SemanticTermKind::Variable { .. }, _) => false,
        (SemanticTermKind::As { pattern, .. }, _) => excludes(signature, pattern, witness),
        // Two literals differ where both are Ints or Bools of different values; a literal is
        // never a constructor's term or a collection, nor is a constructor's term a literal.
        (SemanticTermKind::Token { .. }, Witness::Literal(ground)) => {
            matches!((literal(term), ground), (Some(left), Some(right)) if left != *right)
        }
        (SemanticTermKind::Token { .. }, Witness::Constructor(..) | Witness::Collection { .. }) => {
            true
        }
        (
            SemanticTermKind::Application {
                application: ApplicationRef::Declared(id),
                arguments,
                ..
            },
            Witness::Constructor(other, witnesses),
        ) if signature.is_constructor(id) => {
            id != other
                || arguments
                    .iter()
                    .zip(witnesses)
                    .any(|(argument, witness)| excludes(signature, argument, witness))
        }
        (SemanticTermKind::Map(operands), Witness::Collection { map: true, parts }) => {
            match &**operands {
                MapOperands::Empty => true,
                MapOperands::Items(items) => {
                    items.len() != parts.len() || absent_literal_key(items.iter(), parts)
                }
                MapOperands::ItemsWithRest { items, .. } => {
                    items.len() > parts.len() || absent_literal_key(items.iter(), parts)
                }
                _ => false,
            }
        }
        (SemanticTermKind::Set(operands), Witness::Collection { map: false, .. }) => {
            matches!(&**operands, SetOperands::Empty)
        }
        (
            SemanticTermKind::Application {
                application: ApplicationRef::Declared(id),
                ..
            },
            Witness::Literal(_) | Witness::Collection { .. },
        ) => signature.is_constructor(id),
        _ => false,
    }
}

/// Whether one of a map pattern's keys is a literal no part of the witness has.
fn absent_literal_key<'t>(
    mut items: impl Iterator<Item = &'t krs_ir_levels::MapEntry<SemanticTerm>>,
    parts: &[Ground],
) -> bool {
    items.any(|entry| literal(&entry.key).is_some_and(|key| !parts.contains(&key)))
}

#[cfg(test)]
mod tests {
    use krs_ir::{BuiltinSort, NodeOrigin, SemanticId, SourceMapKey};
    use krs_ir_levels::{
        MapEntry, MapOperands, SemanticSortRef as Sort, SemanticTerm, SetOperands,
    };

    use super::{Ground, Selection, Witness, excludes, result, selections};
    use crate::coverage::Signature;

    const INT: Sort = Sort::Builtin(BuiltinSort::Int);

    fn origin() -> NodeOrigin {
        NodeOrigin::new(
            SourceMapKey::new("sem.equation-choices").unwrap(),
            krs_ir::testing::authored(0, 1),
        )
    }

    fn name(text: &str) -> SemanticTerm {
        SemanticTerm::variable(origin(), INT, SemanticId::new(text.to_owned()).unwrap())
    }

    fn wildcard(ordinal: usize) -> SemanticTerm {
        SemanticTerm::variable(origin(), INT, SemanticId::wildcard(ordinal))
    }

    fn int(value: i128) -> SemanticTerm {
        SemanticTerm::token(origin(), INT, value.to_string()).unwrap()
    }

    fn map_with_rest(
        entries: Vec<(SemanticTerm, SemanticTerm)>,
        rest: SemanticTerm,
    ) -> SemanticTerm {
        let mut entries = entries
            .into_iter()
            .map(|(key, value)| MapEntry { key, value });
        let first = entries.next().unwrap();
        SemanticTerm::map(
            origin(),
            MapOperands::ItemsWithRest {
                items: krs_ir::NonEmpty::new(first, entries.collect()),
                rest,
            },
        )
    }

    fn set(operands: SetOperands<SemanticTerm>) -> SemanticTerm {
        SemanticTerm::set(origin(), Sort::Builtin(BuiltinSort::Set), operands)
    }

    /// The selections of `term`, by kind, with the names bound once.
    fn kinds(term: &SemanticTerm, once: &[&str]) -> Vec<&'static str> {
        let once = |part: &SemanticTerm| match part.kind() {
            krs_ir_levels::SemanticTermKind::Variable { variable } => {
                matches!(variable.kind(), krs_ir::SemanticIdKind::Wildcard)
                    || once.contains(&variable.as_str())
            }
            _ => false,
        };
        let mut sites = Vec::new();
        selections(term, &once, &mut sites);
        sites
            .iter()
            .map(|site| match site.selection {
                Selection::Map { .. } => "map",
                Selection::Set { .. } => "set",
            })
            .collect()
    }

    #[test]
    fn a_key_bound_once_selects_and_a_key_bound_elsewhere_is_looked_up() {
        let open = map_with_rest(vec![(name("k"), wildcard(0))], name("rest"));
        assert_eq!(kinds(&open, &["k", "rest"]), ["map"]);
        // `k` bound elsewhere in the subject: a lookup, one way.
        assert!(kinds(&open, &["rest"]).is_empty());
        // A literal key and a value with structure select nothing the check reads.
        let literal = map_with_rest(vec![(int(1), name("v"))], name("rest"));
        assert!(kinds(&literal, &["v", "rest"]).is_empty());
        let element = set(SetOperands::Concat {
            left: set(SetOperands::Item { element: name("x") }),
            right: name("rest"),
        });
        assert_eq!(kinds(&element, &["x", "rest"]), ["set"]);
    }

    #[test]
    fn an_earlier_pattern_excludes_the_witness_only_where_no_term_matches_both() {
        let signature = Signature::default();
        let witness = Witness::Collection {
            map: true,
            parts: vec![Ground::Int(0), Ground::Int(1)],
        };
        let empty = SemanticTerm::map(origin(), MapOperands::Empty);
        assert!(excludes(&signature, &empty, &witness));
        let other_key = map_with_rest(vec![(int(2), name("v"))], wildcard(0));
        assert!(excludes(&signature, &other_key, &witness));
        let held_key = map_with_rest(vec![(int(1), name("v"))], wildcard(0));
        assert!(!excludes(&signature, &held_key, &witness));
        assert!(!excludes(&signature, &name("m"), &witness));
        assert!(!excludes(&signature, &int(3), &Witness::Any));
        assert!(excludes(
            &signature,
            &int(3),
            &Witness::Literal(Some(Ground::Int(4)))
        ));
    }

    #[test]
    fn a_result_is_read_through_names_and_literals_only() {
        let signature = Signature::default();
        let substitution = [(SemanticId::new("k".to_owned()).unwrap(), "0".to_owned())];
        let substitution = substitution
            .iter()
            .map(|(name, text)| (name, text.clone()))
            .collect();
        assert_eq!(
            result(&signature, &name("k"), &substitution).as_deref(),
            Some("0")
        );
        assert_eq!(
            result(&signature, &name("e"), &substitution).as_deref(),
            Some("e")
        );
        assert_eq!(
            result(&signature, &int(7), &substitution).as_deref(),
            Some("7")
        );
        let call = SemanticTerm::application(
            origin(),
            INT,
            krs_ir::ApplicationRef::Builtin(krs_ir::BuiltinOperation::IntAdd),
            vec![name("k"), int(1)],
        );
        assert_eq!(result(&signature, &call, &substitution), None);
    }
}
