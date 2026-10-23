//! The element types of collection-typed configuration variables, checked on the values a
//! configuration is given.
//!
//! A cell declared `env: Map<Id, Value>` states an invariant of every reachable configuration:
//! each key of the cell is an `Id` and each value a `Value`. K erases element types, so K neither
//! states nor checks it. The compiler proves the induction step, that every rule keeps the
//! invariant (`krs::analysis::collection-element-sort`), and checks the initializer's terms
//! assuming each configuration variable holds a value of its declared type: its `#[k::init]`
//! parameter's type, element types included (`xs: List<Value>`). The base case also needs each
//! value to have that type, and only execution sees the value: [`CellTypes::check`] is that
//! check, which [`crate::Semantics::configure`] and [`crate::Semantics::configure_surface`] apply
//! to every configuration they assemble, whether a variable was given as text (`krs run -c
//! NAME=TEXT`) or as a [`crate::Value`]. It needs no knowledge of where the initializer places
//! the variable: the whole content of a cell, an operand of `list::concat`, an argument, or an
//! untyped position alike.
//!
//! An element fits when its sort is at most the declared element sort in the definition's sort
//! lattice, and a nested collection is checked against its own element types. A part is
//! checked at the sort its symbol declares, which bounds every value it can take: a function
//! application the configuration leaves unevaluated is checked at its result sort, but the
//! elements of a collection it would compute are not seen. The boundary is therefore: those
//! elements, and any part without a sort to check (a variable, a result sort with sort
//! variables); configurations the Java route (`krun`) assembles, which never reach this check;
//! and `k::raw_k!` sentences, which the compiler does not check, so a raw rule can break the
//! invariant after the initial configuration.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use k_rust::{
    k_rust_backend::{definition::BackendDefinition, matching::SortGraph, term::Sort},
    kore::ast::Pattern,
};
use krs_ir::{BuiltinSort, CellSortArgument};
use krs_ir_levels::{DefinitionIr, DefinitionSentence, DefinitionSortRef, SymbolId};

use crate::values::{ValueIndex, kore_sort_name};

/// The declared type of a typed cell or of one of its element positions.
#[derive(Debug)]
struct CellType {
    /// The KORE sort name.
    sort: String,
    /// The collection the sort is, when it is one of K's collections with element types.
    collection: Option<BuiltinSort>,
    arguments: Vec<CellType>,
    /// The type as its declaration spells it (`Map<Id, Value>`).
    display: String,
}

/// The declared type of one collection-typed configuration variable.
#[derive(Debug)]
struct TypedVariable {
    /// The `#[k::init]` parameter that declares the variable.
    parameter: String,
    ty: CellType,
}

/// One position inside a configuration value, from the value's root.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Step<'p> {
    /// A key of a map.
    Key,
    /// The value of a map entry, at this key.
    Value(&'p Pattern),
    /// The element of a list at this index.
    Index(usize),
    /// An element of a set.
    Element,
}

/// A configuration value part that does not fit its declared element type.
#[derive(Debug)]
pub(crate) struct Mismatch<'p> {
    /// The `#[k::init]` parameter that declares the variable.
    pub(crate) parameter: String,
    /// The variable's declared type.
    pub(crate) declared: String,
    /// Where the part is, from the value's root.
    pub(crate) path: Vec<Step<'p>>,
    /// The part.
    pub(crate) element: &'p Pattern,
    /// The part's sort, as an author writes it.
    pub(crate) sort: String,
    /// The declared sort it is not at most.
    pub(crate) expected: String,
}

/// The declared types of a definition's collection-typed configuration variables, and the sort
/// lattice their elements are checked in.
#[derive(Debug, Default)]
pub(crate) struct CellTypes {
    /// By K name of the variable, without `$`.
    variables: BTreeMap<String, TypedVariable>,
    sorts: SortGraph,
}

impl CellTypes {
    /// Index the configuration variables declared with a typed collection type.
    pub(crate) fn new(
        definition: &DefinitionIr,
        backend: &BackendDefinition,
        values: &ValueIndex,
    ) -> Self {
        let sort_names = definition
            .modules()
            .iter()
            .flat_map(krs_ir_levels::DefinitionModule::sentences)
            .filter_map(|sentence| match sentence {
                DefinitionSentence::SyntaxSort(sort) => Some((
                    sort.symbol().id().clone(),
                    kore_sort_name(sort.symbol().emitted_name()),
                )),
                _ => None,
            })
            .collect::<BTreeMap<_, _>>();
        let mut variables = BTreeMap::new();
        for module in definition.modules() {
            for sentence in module.sentences() {
                let DefinitionSentence::Configuration(configuration) = sentence else {
                    continue;
                };
                for variable in configuration.variables() {
                    if variable.arguments().is_empty() {
                        continue;
                    }
                    if let Some(ty) =
                        cell_type(variable.sort(), variable.arguments(), &sort_names, values)
                    {
                        variables.insert(
                            variable.external_name().to_owned(),
                            TypedVariable {
                                parameter: variable.id().as_str().to_owned(),
                                ty,
                            },
                        );
                    }
                }
            }
        }
        Self {
            variables,
            sorts: backend.sort_graph().clone(),
        }
    }

    /// The first part of the value bound to `variable` (its K name without `$`) that does not
    /// fit the variable's declared type, if any.
    pub(crate) fn check<'p>(
        &self,
        values: &ValueIndex,
        variable: &str,
        value: &'p Pattern,
    ) -> Option<Mismatch<'p>> {
        let typed = self.variables.get(variable)?;
        let mut path = Vec::new();
        self.part(values, value, &typed.ty, &mut path)
            .map(|(element, sort, expected)| Mismatch {
                parameter: typed.parameter.clone(),
                declared: typed.ty.display.clone(),
                path,
                element,
                sort: values.sort_display(&sort),
                expected: values.sort_display(expected),
            })
    }

    /// The first part of `pattern` that does not fit `ty`, with its sort and the sort it is not
    /// at most; `path` ends at that part.
    fn part<'p, 't>(
        &self,
        values: &ValueIndex,
        pattern: &'p Pattern,
        ty: &'t CellType,
        path: &mut Vec<Step<'p>>,
    ) -> Option<(&'p Pattern, String, &'t str)> {
        if let Some(collection) = ty.collection
            && let Some(items) = values.collection_items(pattern, collection)
        {
            for (index, item) in items.into_iter().enumerate() {
                let parts = match (collection, item.as_slice()) {
                    (BuiltinSort::Map, [key, value]) => vec![
                        (Step::Key, *key, &ty.arguments[0]),
                        (Step::Value(key), *value, &ty.arguments[1]),
                    ],
                    (BuiltinSort::List, [element]) => {
                        vec![(Step::Index(index), *element, &ty.arguments[0])]
                    }
                    (_, [element]) => vec![(Step::Element, *element, &ty.arguments[0])],
                    _ => continue,
                };
                for (step, part, part_type) in parts {
                    path.push(step);
                    if let Some(mismatch) = self.part(values, part, part_type, path) {
                        return Some(mismatch);
                    }
                    path.pop();
                }
            }
            return None;
        }
        let sort = values.sort_of(pattern)?;
        let fits = self.sorts.check_subsort(
            &Sort::simple(sort.as_str()),
            &Sort::simple(ty.sort.as_str()),
        );
        // An answer the lattice cannot give (an undeclared sort) is no evidence of a mismatch.
        (fits == Ok(false)).then_some((pattern, sort, ty.sort.as_str()))
    }
}

/// The type of a sort with its element types; `None` when a sort has no KORE name to check.
fn cell_type(
    sort: &DefinitionSortRef,
    arguments: &[CellSortArgument<DefinitionSortRef>],
    sort_names: &BTreeMap<SymbolId, String>,
    values: &ValueIndex,
) -> Option<CellType> {
    let (kore, builtin) = match sort {
        DefinitionSortRef::Builtin(builtin) => (kore_sort_name(builtin.k_name()), Some(*builtin)),
        DefinitionSortRef::Declared(symbol) => (sort_names.get(symbol)?.clone(), None),
        DefinitionSortRef::Cell(_) | DefinitionSortRef::Parameter(_) => return None,
    };
    let arguments = arguments
        .iter()
        .map(|argument| cell_type(&argument.sort, &argument.arguments, sort_names, values))
        .collect::<Option<Vec<_>>>()?;
    let collection = builtin
        .filter(|sort| {
            matches!(
                sort,
                BuiltinSort::Map | BuiltinSort::List | BuiltinSort::Set
            )
        })
        .filter(|sort| arguments.len() == if *sort == BuiltinSort::Map { 2 } else { 1 });
    let mut display = values.sort_display(&kore);
    if !arguments.is_empty() {
        display.push('<');
        for (index, argument) in arguments.iter().enumerate() {
            if index > 0 {
                display.push_str(", ");
            }
            let _ = write!(display, "{}", argument.display);
        }
        display.push('>');
    }
    Some(CellType {
        sort: kore,
        collection,
        arguments,
        display,
    })
}

/// Where `path` leads inside a value, from its innermost step (``the value at key `x` ``,
/// ``an element of the value at key `x` ``); `key` prints a map key.
pub(crate) fn describe(path: &[Step<'_>], key: impl Fn(&Pattern) -> String) -> String {
    let mut text = String::new();
    for (index, step) in path.iter().rev().enumerate() {
        if index > 0 {
            text.push_str(" of ");
        }
        match step {
            Step::Key => text.push_str("a key"),
            Step::Value(at) => {
                let _ = write!(text, "the value at key `{}`", key(at));
            }
            Step::Index(position) => {
                let _ = write!(text, "the element at index {position}");
            }
            Step::Element => text.push_str("an element"),
        }
    }
    if text.is_empty() {
        text.push_str("the value");
    }
    text
}
