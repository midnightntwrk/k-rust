//! Typed collections: the element types of `Map<K, V>`, `List<T>`, and
//! `Set<T>` cells, constructor fields, and function parameters and results,
//! and the check that every term written into one fits them.
//!
//! A cell declared `env: Map<Id, Value>` states an invariant of every
//! reachable configuration: each key of the cell is an `Id` and each value a
//! `Value`. K's collections hold `KItem`s, so K neither states nor checks it,
//! and the element types are erased from the emitted K. The invariant holds
//! by induction over transitions when the initializer satisfies it and every
//! rule places at each typed position only terms that fit its type, assuming
//! every binder matched at a typed position already has that position's
//! type. This module is that induction step:
//!
//! - a binder matched at a typed position (`env: e`, the rest of a typed
//!   map pattern, a typed child of a group record, a typed field of a
//!   constructor pattern, a typed parameter in an equation's subject) takes
//!   the position's type;
//! - every other term at a typed position is checked: a binder's type must
//!   fit, a collection operation's operands are checked at the types the
//!   operation's catalog row gives them, and an element operand (the `v` of
//!   `map::update(m, k, v)`) is inferred at the element sort, where it
//!   narrows a binder as any other occurrence does;
//! - a read (`map::get(e, k)`) has the element sort, and a read that asks
//!   for a sort the collection never holds is an error.
//!
//! A typed function moves the obligation to its equations: an argument is
//! checked at its parameter's type, an application has its result's type,
//! and each equation's result is checked at that type, with its subject's
//! binders at the parameters' types.
//!
//! A collection whose elements nothing declares (a function result or a
//! constructor field declared as a bare `Map`, a bare `Map` cell) is
//! untyped. Writing one into a typed position is the error
//! `krs::analysis::untyped-collection`: nothing checks its elements, so the
//! induction step would not hold.
//!
//! [`CollectionTyping`] walks a sentence's typed positions before inference.
//! Binder types come from the patterns alone, so they are known before any
//! term is inferred; element sorts and read sorts are recorded by the
//! provenance key of the term they apply to, which inference and lowering
//! consult.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{self, Write as _};

use krs_ir::{
    BuiltinSort, CellSortArgument, CollectionApplication, Descriptor, DescriptorApplicationRef,
    DescriptorCellField, DescriptorClaimBinder, DescriptorConfigurationVariable, DescriptorIndex,
    DescriptorSortArgument, DescriptorSortRef, DescriptorTerm, ListNotation, ListOperation,
    OperationSort, ProtocolCellContent, ProtocolRuleFrame, ProtocolRuleMapBody,
    ProtocolRuleStateTerm, ProvenanceKey, SetOperation, StableItemId, TermMapOperation,
};
use krs_ir_levels::SemanticSortRef;

use super::catalog::{ProductionSignature, semantic_is_subsort, semantic_sort_ref};
use super::error::DescriptorLoweringError;
use super::infer::most_specific_common_descendants;
use super::references::require_cell_field;

type SortParents = BTreeMap<SemanticSortRef, BTreeSet<SemanticSortRef>>;

/// A sort with the arguments of its collection type: `Map<Id, Value>`,
/// `List<StackFrame>`, `Map<Int, Set<Int>>`. A bare `Map`, `List`, or `Set`
/// has no arguments and is untyped; every other sort has none.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct SortType {
    sort: SemanticSortRef,
    arguments: Vec<SortType>,
}

impl SortType {
    fn collection(sort: BuiltinSort, arguments: Vec<Self>) -> Self {
        Self {
            sort: SemanticSortRef::Builtin(sort),
            arguments,
        }
    }

    /// The content type of a leaf cell, or `None` for a nested cell. A
    /// collection type with the wrong number of arguments is an error.
    pub(super) fn of_cell(
        field: &DescriptorCellField,
        descriptor: &Descriptor,
    ) -> Result<Option<Self>, DescriptorLoweringError> {
        let ProtocolCellContent::Leaf {
            sort, arguments, ..
        } = &field.content
        else {
            return Ok(None);
        };
        let ty = Self {
            sort: semantic_sort_ref(&sort.sort),
            arguments: arguments.iter().map(Self::of_argument).collect(),
        };
        ty.check_arity(
            &format!("the cell `{}`", field.rust_field),
            descriptor,
            &sort.key,
        )?;
        Ok(Some(ty))
    }

    /// The declared type of a configuration variable: its parameter's sort
    /// and, for a collection, the element types it states. A collection type
    /// with the wrong number of arguments is an error.
    pub(super) fn of_variable(
        variable: &DescriptorConfigurationVariable,
        descriptor: &Descriptor,
    ) -> Result<Self, DescriptorLoweringError> {
        let ty = Self {
            sort: semantic_sort_ref(&variable.sort.sort),
            arguments: variable.arguments.iter().map(Self::of_argument).collect(),
        };
        ty.check_arity(
            &format!("{},", Owner::variable(variable).describe()),
            descriptor,
            &variable.sort.key,
        )?;
        Ok(ty)
    }

    /// The type of a production's field or result: its sort and the element
    /// types its declaration states.
    fn of_production(
        sort: &DescriptorSortRef,
        arguments: &[krs_ir::ConstructorSortArgumentDescriptor],
    ) -> Self {
        Self {
            sort: semantic_sort_ref(sort),
            arguments: arguments
                .iter()
                .map(|argument| Self::of_production(&argument.sort.sort, &argument.arguments))
                .collect(),
        }
    }

    fn of_argument(argument: &DescriptorSortArgument) -> Self {
        Self {
            sort: semantic_sort_ref(&argument.sort.sort),
            arguments: argument.arguments.iter().map(Self::of_argument).collect(),
        }
    }

    /// Rejects `Map<Id>`, `List<A, B>`, and arguments of a sort that is not
    /// a collection, here and in every argument; `owner` names the position,
    /// as in "the cell `raw`".
    fn check_arity(
        &self,
        owner: &str,
        descriptor: &Descriptor,
        key: &ProvenanceKey,
    ) -> Result<(), DescriptorLoweringError> {
        let expected = match self.kind() {
            Some(BuiltinSort::Map) => 2,
            Some(_) => 1,
            None => 0,
        };
        if !self.arguments.is_empty() && self.arguments.len() != expected {
            let reason = match self.kind() {
                Some(BuiltinSort::Map) => format!(
                    "{owner} is declared `{self}`: a `Map` takes a key and a value type, `Map<K, V>`, or none, `Map`"
                ),
                Some(kind) => format!(
                    "{owner} is declared `{self}`: a `{name}` takes one element type, `{name}<T>`, or none, `{name}`",
                    name = kind.k_name()
                ),
                None => format!(
                    "{owner} is declared `{self}`, but only `Map`, `List`, and `Set` take element types"
                ),
            };
            return Err(DescriptorLoweringError::CollectionElementSort {
                item: Box::new(descriptor.id().clone()),
                reason,
                range: authored_range(descriptor, key),
            });
        }
        for argument in &self.arguments {
            argument.check_arity(owner, descriptor, key)?;
        }
        Ok(())
    }

    /// `Map`, `List`, or `Set` when the sort is one of K's collections.
    fn kind(&self) -> Option<BuiltinSort> {
        match self.sort {
            SemanticSortRef::Builtin(
                sort @ (BuiltinSort::Map | BuiltinSort::List | BuiltinSort::Set),
            ) => Some(sort),
            _ => None,
        }
    }

    /// Whether this is a collection whose element types are declared.
    fn is_typed(&self) -> bool {
        self.kind().is_some() && !self.arguments.is_empty()
    }

    /// The element types, as the Semantic IR records them on a leaf cell.
    pub(super) fn ir_arguments(&self) -> Vec<CellSortArgument<SemanticSortRef>> {
        self.arguments
            .iter()
            .map(|argument| CellSortArgument {
                sort: argument.sort.clone(),
                arguments: argument.ir_arguments(),
            })
            .collect()
    }

    /// The sort, without arguments.
    pub(super) const fn sort(&self) -> &SemanticSortRef {
        &self.sort
    }

    /// The value type of a typed map.
    pub(super) fn map_value(&self) -> Option<&Self> {
        self.part(Step::Value)
    }

    /// The type at `step` of a typed collection: a map's key or value type,
    /// a list's or set's element type.
    fn part(&self, step: Step) -> Option<&Self> {
        if !self.is_typed() {
            return None;
        }
        let index = match (self.kind()?, step) {
            (BuiltinSort::Map, Step::Key)
            | (BuiltinSort::List | BuiltinSort::Set, Step::Element) => 0,
            (BuiltinSort::Map, Step::Value) => 1,
            _ => return None,
        };
        self.arguments.get(index)
    }

    /// Whether a term of type `self` fits a position of type `expected`.
    /// Collections are values, so every argument is covariant.
    fn fits(&self, expected: &Self, parents: &SortParents) -> Fit {
        if !expected.is_typed() {
            return Fit::Yes;
        }
        if self.kind() != expected.kind() {
            // Sort inference decides whether the sorts fit.
            return Fit::Yes;
        }
        if !self.is_typed() {
            return Fit::Untyped;
        }
        let mut fit = Fit::Yes;
        for (actual, expected) in self.arguments.iter().zip(&expected.arguments) {
            let argument = if expected.is_typed() {
                actual.fits(expected, parents)
            } else if semantic_is_subsort(&actual.sort, &expected.sort, parents) {
                Fit::Yes
            } else {
                Fit::No
            };
            fit = fit.and(argument);
        }
        fit
    }

    /// The first argument sorts, depth first, at which `self` does not fit
    /// `expected`.
    fn first_mismatch<'t>(
        &'t self,
        expected: &'t Self,
        parents: &SortParents,
    ) -> Option<(&'t SemanticSortRef, &'t SemanticSortRef)> {
        self.arguments
            .iter()
            .zip(&expected.arguments)
            .find_map(|(actual, expected)| {
                if expected.is_typed() && actual.is_typed() {
                    actual.first_mismatch(expected, parents)
                } else if !expected.is_typed()
                    && !semantic_is_subsort(&actual.sort, &expected.sort, parents)
                {
                    Some((&actual.sort, &expected.sort))
                } else {
                    None
                }
            })
    }

    /// The more precise of two types a binder is matched at. Both hold of
    /// the binder's value, so either is sound; the typed one says more.
    fn meet(self, other: Self, parents: &SortParents) -> Self {
        match (self.is_typed(), other.is_typed()) {
            (false, true) => other,
            (true, true) if other.fits(&self, parents) == Fit::Yes => other,
            _ => self,
        }
    }
}

impl fmt::Display for SortType {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&super::overload::sort_name(&self.sort))?;
        if let Some((first, rest)) = self.arguments.split_first() {
            write!(formatter, "<{first}")?;
            for argument in rest {
                write!(formatter, ", {argument}")?;
            }
            formatter.write_str(">")?;
        }
        Ok(())
    }
}

/// Whether a type fits a position.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Fit {
    Yes,
    /// Some element type of the term is not declared.
    Untyped,
    No,
}

impl Fit {
    const fn and(self, other: Self) -> Self {
        match (self, other) {
            (Self::No, _) | (_, Self::No) => Self::No,
            (Self::Untyped, _) | (_, Self::Untyped) => Self::Untyped,
            (Self::Yes, Self::Yes) => Self::Yes,
        }
    }
}

/// One step from a collection to a part of it.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Step {
    Key,
    Value,
    Element,
}

impl Step {
    const fn noun(self) -> &'static str {
        match self {
            Self::Key => "a key",
            Self::Value => "a value",
            Self::Element => "an element",
        }
    }
}

/// One step from a position to a part of it: a key, value, or element of
/// the collection there, or the collection a reading operation written
/// there reads its result from.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum PathStep {
    Part(Step),
    /// The operand of a reading operation (`map::keys(m)`'s `m`), whose
    /// `part` (`keys`) the operation writes to the position.
    Read {
        operation: String,
        collection: &'static str,
        part: &'static str,
    },
}

/// What declares a typed position's type.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Owner {
    /// A cell, by its Rust field name.
    Cell(String),
    /// A constructor's field or a function's parameter.
    Field {
        production: String,
        field: String,
        parameter: bool,
    },
    /// A function's result.
    Result(String),
    /// A configuration variable of an initializer, by its Rust binding and
    /// its external name without `$`.
    Variable { binding: String, external: String },
}

impl Owner {
    fn variable(variable: &DescriptorConfigurationVariable) -> Self {
        Self::Variable {
            binding: variable.binding.clone(),
            external: variable.external_name.clone(),
        }
    }

    /// The owner alone, as in "`xs`, the configuration variable `$XS`".
    fn describe(&self) -> String {
        match self {
            Self::Cell(cell) => format!("the cell `{cell}`"),
            Self::Field {
                production,
                field,
                parameter,
            } => format!(
                "the {} `{field}` of `{production}`",
                if *parameter { "parameter" } else { "field" }
            ),
            Self::Result(function) => format!("the result of `{function}`"),
            Self::Variable { binding, external } => {
                format!("`{binding}`, the configuration variable `${external}`")
            }
        }
    }
}

/// A typed position: a cell, a constructor field, a function parameter or
/// result (or one of its parts), and its declared type, for diagnostics.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct Position {
    owner: Owner,
    /// The owner's declared type.
    declared: SortType,
    /// The steps from the owner's type to this position, outermost first.
    path: Vec<PathStep>,
}

impl Position {
    fn cell(cell: &str, declared: SortType) -> Self {
        Self::of(Owner::Cell(cell.to_owned()), declared)
    }

    const fn of(owner: Owner, declared: SortType) -> Self {
        Self {
            owner,
            declared,
            path: Vec::new(),
        }
    }

    fn child(&self, step: Step) -> Self {
        let mut child = self.clone();
        child.path.push(PathStep::Part(step));
        child
    }

    /// The operand of a reading operation written at this position.
    fn read_through(
        &self,
        operation: String,
        collection: &'static str,
        part: &'static str,
    ) -> Self {
        let mut operand = self.clone();
        operand.path.push(PathStep::Read {
            operation,
            collection,
            part,
        });
        operand
    }

    /// The position, as in "a value of the cell `env`", "an element of a
    /// value of the cell `raw`", or "the parameter `accessed` of `Mark`".
    fn describe(&self) -> String {
        let mut text = String::new();
        for step in self.path.iter().rev() {
            match step {
                PathStep::Part(step) => {
                    text.push_str(step.noun());
                    text.push_str(" of ");
                }
                PathStep::Read {
                    operation,
                    collection,
                    part,
                } => {
                    let _ = write!(
                        text,
                        "the {collection} whose {part} `{operation}` writes to "
                    );
                }
            }
        }
        text.push_str(&self.owner.describe());
        text
    }

    /// The position and its owner's declared type, as in "the cell `env`,
    /// declared `Map<Id, Value>`".
    fn describe_declared(&self) -> String {
        format!("{}, declared `{}`", self.describe(), self.declared)
    }
}

/// An element position: the sort a key, value, or element operand is
/// inferred at, and where it is.
#[derive(Clone, Debug)]
pub(super) struct ElementSite {
    pub(super) sort: SemanticSortRef,
    position: Position,
    /// Whether the term is read from the position (a map read's value
    /// binder) rather than stored at it.
    read: bool,
}

/// What a binder matched at a collection position is known to hold.
#[derive(Clone, Debug)]
enum Matched {
    /// Matched at a position of this type.
    Typed(Box<(SortType, Position)>),
    /// Matched in a bare collection cell.
    Untyped(String),
    /// Fits every type that sort inference lets it stand at: a configuration
    /// variable or a transition existential of a sort that is not a
    /// collection, whose occurrences sort inference checks against its
    /// declared sort; a claim's existential, which stands for whatever the
    /// state holds; or a fresh binder, which is never a collection.
    Checked,
}

/// What a term at a typed position is known to be.
enum Source {
    /// `.Map`, `.List`, `.Set`, or a configuration variable: fits every type.
    Fits,
    /// A typed collection, and what it is.
    Typed(Box<SortType>, String),
    /// A collection whose elements nothing declares, and why.
    Untyped(String),
    /// Not known to be a collection; sort inference decides.
    Unknown,
}

/// The element types of one sentence: binder types from its patterns, the
/// element and read sorts of its collection operands.
#[derive(Default)]
pub(super) struct CollectionTyping {
    binders: BTreeMap<String, Matched>,
    /// Element operands of typed collections, by term key.
    elements: BTreeMap<ProvenanceKey, ElementSite>,
    /// The element binders, with the key of each element position.
    element_binders: BTreeMap<String, Vec<(ProvenanceKey, ElementSite)>>,
    /// Probes into typed collections (`map::remove(m, k)`'s `k`), by term key.
    reads: BTreeMap<ProvenanceKey, ElementSite>,
    /// The sort `map::get`, `map::get_or_default`, and `list::get` read, by
    /// application key.
    projections: BTreeMap<ProvenanceKey, ElementSite>,
    /// The sort of an element of a collection whose element types nothing
    /// declares (a bare `Map`, `List`, or `Set`): `KItem`, which K's
    /// `ListItem`, `|->`, and `SetItem` hold and its lookups return, when
    /// the definition selects it.
    untyped_element: Option<SemanticSortRef>,
}

impl CollectionTyping {
    /// The sort an element operand is inferred at, if it has one.
    pub(super) fn element(&self, term: &DescriptorTerm) -> Option<&ElementSite> {
        self.elements.get(term_key(term))
    }

    /// The typed element position of the term at `key`, if it stands at one.
    pub(super) fn element_at(&self, key: &ProvenanceKey) -> Option<&ElementSite> {
        self.elements.get(key)
    }

    /// The sort an element operand is inferred and lowered at: the element
    /// sort of its typed collection, or [`Self::untyped_element`] for an
    /// element of a collection whose element types nothing declares. Only
    /// called for a term that stands at an element position.
    pub(super) fn element_sort(&self, term: &DescriptorTerm) -> Option<SemanticSortRef> {
        self.element(term)
            .map(|site| site.sort.clone())
            .or_else(|| self.untyped_element.clone())
    }

    /// The sort of an element of a collection whose element types nothing
    /// declares: `KItem`, when the definition selects it. A binder that
    /// occurs only at such positions is a `KItem`, a wildcard there matches
    /// any element, and a read of such a collection that no position sorts
    /// is a `KItem`.
    pub(super) fn untyped_element(&self) -> Option<&SemanticSortRef> {
        self.untyped_element.as_ref()
    }

    /// The sort a probe operand must share a sort with, if it has one.
    pub(super) fn read(&self, term: &DescriptorTerm) -> Option<&ElementSite> {
        self.reads.get(term_key(term))
    }

    /// The probe at a term key.
    pub(super) fn reads_at(&self, key: &ProvenanceKey) -> Option<&ElementSite> {
        self.reads.get(key)
    }

    /// The sort a projecting read returns, by its application key.
    pub(super) fn projection(&self, key: &ProvenanceKey) -> Option<&ElementSite> {
        self.projections.get(key)
    }

    /// The element positions a binder occurs at, by occurrence key.
    pub(super) fn element_sites_of(&self, name: &str) -> Vec<(&ProvenanceKey, &ElementSite)> {
        self.element_binders
            .get(name)
            .into_iter()
            .flatten()
            .map(|(key, site)| (key, site))
            .collect()
    }

    /// The empty typing of a sentence without typed positions.
    pub(super) fn empty() -> &'static Self {
        static EMPTY: CollectionTyping = CollectionTyping {
            binders: BTreeMap::new(),
            elements: BTreeMap::new(),
            element_binders: BTreeMap::new(),
            reads: BTreeMap::new(),
            projections: BTreeMap::new(),
            untyped_element: None,
        };
        &EMPTY
    }
}

/// Walks one sentence's terms: first its patterns, for binder types, then
/// every term, for element sorts, reads, and flows into typed positions.
pub(super) struct Walker<'a> {
    descriptor: &'a Descriptor,
    declarations: Option<&'a DescriptorIndex<'a>>,
    /// The productions, for the field order of positional arguments and
    /// whether a production is a function.
    catalog: &'a BTreeMap<StableItemId, ProductionSignature>,
    parents: &'a SortParents,
    typing: CollectionTyping,
    /// Whether this pass records binder types (the first) or checks (the
    /// second).
    binding: bool,
    /// Names a `let`, `k::matches!`, or `ml::exists` binds in scope.
    locals: Vec<BTreeSet<String>>,
}

/// A term of a sentence and the position it stands at.
pub(super) enum Root<'t> {
    /// A term at a position of `ty` (a cell's content), or at an untyped
    /// position when `ty` is `None`.
    Term {
        term: &'t DescriptorTerm,
        ty: Option<(SortType, Position)>,
        subject: bool,
    },
    /// A cell's `map![..]` state.
    Map {
        map: &'t krs_ir::ProtocolRuleMap<DescriptorTerm>,
        ty: Option<(SortType, Position)>,
        subject: bool,
    },
    /// An initializer's `k::map![..]` state.
    InitializerMap {
        map: &'t krs_ir::ProtocolMap<DescriptorTerm>,
        ty: Option<(SortType, Position)>,
    },
    /// An element of a list cell of `ty`, written in brackets.
    Element {
        term: &'t DescriptorTerm,
        ty: Option<(SortType, Position)>,
        subject: bool,
    },
    /// A binder matched as the whole content of a cell of `ty`.
    Binder {
        name: &'t str,
        ty: Option<(SortType, Position)>,
    },
    /// One entry `key -> value` of a readable map read of a cell of `ty`:
    /// the key a key of the map, the value binder one of its values.
    MapEntry {
        key: &'t DescriptorTerm,
        value: &'t str,
        /// The read's cell-field key, where a diagnostic about the value
        /// binder points.
        cell_key: &'t ProvenanceKey,
        ty: Option<(SortType, Position)>,
    },
}

impl<'a> Walker<'a> {
    pub(super) fn new(
        descriptor: &'a Descriptor,
        declarations: Option<&'a DescriptorIndex<'a>>,
        catalog: &'a BTreeMap<StableItemId, ProductionSignature>,
        parents: &'a SortParents,
    ) -> Self {
        Self {
            descriptor,
            declarations,
            catalog,
            parents,
            typing: CollectionTyping {
                untyped_element: declarations.and_then(|declarations| {
                    super::rules::framework_k_item_sort(declarations).ok()
                }),
                ..CollectionTyping::default()
            },
            binding: true,
            locals: Vec::new(),
        }
    }

    /// Classifies a sentence's `#[k::exists]` binders by what they range
    /// over. A transition's existential is a value the step introduces, any
    /// value of its sort: one of sort `Map`, `List`, or `Set` is an unknown
    /// collection whose elements nothing constrains, an untyped source. A
    /// claim's existential stands for whatever the target state holds where
    /// it occurs, so it fits every type. An existential of any other sort is
    /// checked by sort inference.
    pub(super) fn existentials(&mut self, binders: &[DescriptorClaimBinder], claim: bool) {
        for binder in binders {
            let kind = SortType {
                sort: semantic_sort_ref(&binder.sort.sort),
                arguments: Vec::new(),
            }
            .kind();
            let matched = match kind {
                Some(kind) if !claim => Matched::Untyped(format!(
                    "`{}` is an existential `{}`, an unknown {} whose elements nothing constrains",
                    binder.name,
                    kind.k_name(),
                    kind.k_name().to_lowercase(),
                )),
                _ => Matched::Checked,
            };
            self.typing.binders.insert(binder.name.clone(), matched);
        }
    }

    /// Marks `names` as binders that fit every type that sort inference lets
    /// them stand at: claim existentials, and fresh binders, whose sort is a
    /// fresh generator's result and so never a collection.
    pub(super) fn checked_binders<'n>(&mut self, names: impl IntoIterator<Item = &'n str>) {
        for name in names {
            self.typing
                .binders
                .insert(name.to_owned(), Matched::Checked);
        }
    }

    /// Binds each configuration variable of an initializer at its declared
    /// type, as a typed function's equation binds its parameters: a variable
    /// of a typed collection type is a binder of that type, whose every
    /// placement is a checked flow; one of a bare collection type is an
    /// untyped source; any other is checked by sort inference. Execution
    /// checks each value against the same type, so the two meet at the
    /// variable boundary wherever the initializer places it.
    pub(super) fn variables(
        &mut self,
        variables: &[DescriptorConfigurationVariable],
    ) -> Result<(), DescriptorLoweringError> {
        for variable in variables {
            let ty = SortType::of_variable(variable, self.descriptor)?;
            let owner = Owner::variable(variable);
            let matched = if ty.is_typed() {
                Matched::Typed(Box::new((ty.clone(), Position::of(owner, ty))))
            } else if ty.kind().is_some() {
                Matched::Untyped(format!("{}, is declared `{ty}`", owner.describe()))
            } else {
                Matched::Checked
            };
            self.typing
                .binders
                .insert(variable.binding.clone(), matched);
        }
        Ok(())
    }

    /// The content type and position of a leaf cell.
    pub(super) fn cell_type(
        &self,
        field: &DescriptorCellField,
    ) -> Result<Option<(SortType, Position)>, DescriptorLoweringError> {
        Ok(SortType::of_cell(field, self.descriptor)?
            .filter(|ty| ty.kind().is_some())
            .map(|ty| {
                let position = Position::cell(&field.rust_field, ty.clone());
                (ty, position)
            }))
    }

    /// The type and position of a term's result when its head is a
    /// production whose result is a collection: an equation's result
    /// stands there.
    pub(super) fn result_type(&self, term: &DescriptorTerm) -> Option<(SortType, Position)> {
        let DescriptorTerm::Application { reference, .. } = term else {
            return None;
        };
        let DescriptorApplicationRef::Declared(id) = &reference.application else {
            return None;
        };
        self.production_types(id)?.result
    }

    /// Walks every root twice and returns the sentence's typing.
    pub(super) fn run(
        mut self,
        roots: &[Root<'_>],
    ) -> Result<CollectionTyping, DescriptorLoweringError> {
        for binding in [true, false] {
            self.binding = binding;
            for root in roots {
                self.root(root)?;
            }
        }
        Ok(self.typing)
    }

    fn root(&mut self, root: &Root<'_>) -> Result<(), DescriptorLoweringError> {
        match root {
            Root::Term { term, ty, subject } => self.walk(term, ty.as_ref(), *subject),
            Root::Element { term, ty, subject } => {
                let operated = ty.as_ref().filter(|(ty, _)| ty.is_typed());
                self.element(term, operated, Step::Element, *subject)
            }
            Root::Map { map, ty, subject } => self.rule_map(map, ty.as_ref(), *subject),
            Root::InitializerMap { map, ty } => {
                let at = ty.as_ref();
                match &map.body {
                    krs_ir::ProtocolMapBody::Empty { .. } => Ok(()),
                    krs_ir::ProtocolMapBody::Items { items } => {
                        for item in items {
                            self.element(&item.key.term, at, Step::Key, false)?;
                            self.element(&item.value.term, at, Step::Value, false)?;
                        }
                        Ok(())
                    }
                    krs_ir::ProtocolMapBody::Update {
                        base, key, value, ..
                    } => {
                        self.walk(&base.term, at, false)?;
                        self.element(&key.term, at, Step::Key, false)?;
                        self.element(&value.term, at, Step::Value, false)
                    }
                }
            }
            Root::Binder { name, ty } => {
                if self.binding
                    && let Some((ty, position)) = ty
                {
                    self.bind(name, ty, position);
                }
                Ok(())
            }
            Root::MapEntry {
                key,
                value,
                cell_key,
                ty,
            } => {
                if let Some((ty, position)) = ty
                    && let Some(part) = ty.part(Step::Value)
                {
                    let position = position.child(Step::Value);
                    if self.binding && part.kind().is_some() {
                        self.bind(value, &part.clone(), &position);
                    } else if !self.binding && !self.is_local(value) {
                        self.typing
                            .element_binders
                            .entry((*value).to_owned())
                            .or_default()
                            .push((
                                (*cell_key).clone(),
                                ElementSite {
                                    sort: part.sort.clone(),
                                    position,
                                    read: true,
                                },
                            ));
                    }
                }
                self.element(key, ty.as_ref(), Step::Key, true)
            }
        }
    }

    /// A `cells!` rule's `map![..]` state.
    fn rule_map(
        &mut self,
        map: &krs_ir::ProtocolRuleMap<DescriptorTerm>,
        at: Option<&(SortType, Position)>,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        match &map.body {
            ProtocolRuleMapBody::Empty { .. } => Ok(()),
            ProtocolRuleMapBody::Items { items, remainder } => {
                for item in items {
                    self.element(&item.key, at, Step::Key, subject)?;
                    self.element(&item.value, at, Step::Value, subject)?;
                }
                match (remainder, at) {
                    (ProtocolRuleFrame::Bind { binding, .. }, Some((ty, position)))
                        if self.binding =>
                    {
                        self.bind(binding, ty, position);
                    }
                    (ProtocolRuleFrame::Reuse { key, binding }, Some(at)) if !self.binding => {
                        let source = self.binder_source(binding);
                        self.flow(source, at, key)?;
                    }
                    _ => {}
                }
                Ok(())
            }
            ProtocolRuleMapBody::Update {
                base, key, value, ..
            } => {
                self.walk(base, at, subject)?;
                self.element(key, at, Step::Key, subject)?;
                self.element(value, at, Step::Value, subject)
            }
        }
    }

    /// Walks the state of a cell entry: a term or `map![..]` at the cell's
    /// type, the inside of `Some(..)`, or the children of instances.
    pub(super) fn state_roots<'t>(
        &self,
        state: &'t ProtocolRuleStateTerm<DescriptorTerm>,
        field: &DescriptorCellField,
        subject: bool,
        roots: &mut Vec<Root<'t>>,
    ) -> Result<(), DescriptorLoweringError> {
        match state {
            ProtocolRuleStateTerm::Term(term) | ProtocolRuleStateTerm::Group(term) => {
                roots.push(Root::Term {
                    term,
                    ty: self.cell_type(field)?,
                    subject,
                });
            }
            ProtocolRuleStateTerm::Map(map) => roots.push(Root::Map {
                map,
                ty: self.cell_type(field)?,
                subject,
            }),
            ProtocolRuleStateTerm::KSequence(sequence) => {
                for item in &sequence.items {
                    roots.push(Root::Term {
                        term: &item.value,
                        ty: None,
                        subject,
                    });
                }
            }
            ProtocolRuleStateTerm::Present { value } => {
                self.state_roots(value, field, subject, roots)?;
            }
            ProtocolRuleStateTerm::Absent => {}
            ProtocolRuleStateTerm::Instances(instances) => {
                let (Some(declarations), ProtocolCellContent::Nested { declaration }) =
                    (self.declarations, &field.content)
                else {
                    return Ok(());
                };
                let children = &declarations.cell(&declaration.declaration)?.fields;
                for instance in instances.front.iter().chain(&instances.back) {
                    for child in &instance.fields {
                        if let Some(declared) = children
                            .iter()
                            .find(|candidate| candidate.rust_field == child.field)
                        {
                            self.state_roots(&child.value, declared, subject, roots)?;
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn bind(&mut self, name: &str, ty: &SortType, position: &Position) {
        if self.is_local(name) {
            return;
        }
        let matched = if ty.is_typed() {
            Matched::Typed(Box::new((ty.clone(), position.clone())))
        } else {
            Matched::Untyped(format!(
                "`{name}` is matched in {}",
                position.describe_declared()
            ))
        };
        let merged = match (self.typing.binders.remove(name), matched) {
            (None | Some(Matched::Untyped(_) | Matched::Checked), matched) => matched,
            (Some(Matched::Typed(left)), Matched::Untyped(_) | Matched::Checked) => {
                Matched::Typed(left)
            }
            (Some(Matched::Typed(left)), Matched::Typed(right)) => {
                let (left, left_position) = *left;
                let (right, right_position) = *right;
                let meet = left.clone().meet(right, self.parents);
                if meet == left {
                    Matched::Typed(Box::new((left, left_position)))
                } else {
                    Matched::Typed(Box::new((meet, right_position)))
                }
            }
        };
        self.typing.binders.insert(name.to_owned(), merged);
    }

    fn is_local(&self, name: &str) -> bool {
        self.locals.iter().any(|scope| scope.contains(name))
    }

    /// Walks `term` standing at `at` (a collection position, typed or not)
    /// or at an untyped position.
    #[expect(
        clippy::too_many_lines,
        reason = "Exhaustive walk over the closed descriptor term sum."
    )]
    fn walk(
        &mut self,
        term: &DescriptorTerm,
        at: Option<&(SortType, Position)>,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        match term {
            DescriptorTerm::Variable { name, key, .. } => match at {
                Some((ty, position)) if subject && self.binding => self.bind(name, ty, position),
                Some(at) if !subject && !self.binding && !self.is_local(name) => {
                    let source = self.binder_source(name);
                    self.flow(source, at, key)?;
                }
                _ => {}
            },
            DescriptorTerm::As { name, pattern, .. } => {
                if let Some((ty, position)) = at
                    && self.binding
                {
                    self.bind(name, ty, position);
                }
                self.walk(pattern, at, subject)?;
            }
            DescriptorTerm::Or { alternatives, .. } => {
                for alternative in alternatives.iter() {
                    self.walk(alternative, at, subject)?;
                }
            }
            DescriptorTerm::Rewrite { from, to, .. } => {
                self.walk(from, at, true)?;
                if let Some(to) = to {
                    self.walk(to, at, false)?;
                }
            }
            DescriptorTerm::Let {
                pattern,
                value,
                body,
                ..
            } => {
                self.walk(value, None, subject)?;
                self.locals.push(pattern_names(pattern));
                self.walk(body, at, subject)?;
                self.locals.pop();
            }
            DescriptorTerm::Matches {
                subject: tested,
                pattern,
                ..
            } => {
                self.walk(tested, None, subject)?;
                self.locals.push(pattern_names(pattern));
                self.walk(pattern, None, true)?;
                self.locals.pop();
            }
            DescriptorTerm::Closure { name, body, .. } => {
                self.locals.push(BTreeSet::from([name.clone()]));
                self.walk(body, None, subject)?;
                self.locals.pop();
            }
            DescriptorTerm::Application {
                reference,
                arguments,
                update,
                ..
            } => {
                self.application(term, &reference.application, arguments, at, subject)?;
                if let Some(update) = update {
                    self.walk(update, None, subject)?;
                }
            }
            DescriptorTerm::SortTest { kind, operand, .. } => {
                if let Some(at) = at
                    && !subject
                    && *kind == krs_ir::SortTestKind::Projection
                {
                    let source = Source::Untyped(format!(
                        "`{}` is a projection, which tests only the sort",
                        spelling(term)
                    ));
                    self.flow(source, at, term_key(term))?;
                }
                self.walk(operand, None, subject)?;
            }
            DescriptorTerm::Cell {
                declaration,
                fields,
                update,
                ..
            } => {
                let children = match self.declarations {
                    Some(declarations) => Some(declarations.cell(declaration)?.fields.clone()),
                    None => None,
                };
                for field in fields {
                    let declared = children.as_ref().and_then(|children| {
                        children
                            .iter()
                            .find(|child| child.rust_field == field.field.as_str())
                    });
                    let ty = match declared {
                        Some(declared) => self.cell_type(declared)?,
                        None => None,
                    };
                    self.walk(&field.value, ty.as_ref(), subject)?;
                }
                if let Some(update) = update {
                    self.walk(update, None, subject)?;
                }
            }
            DescriptorTerm::OrBool { arguments, .. } => {
                for argument in arguments.iter() {
                    self.walk(argument, None, subject)?;
                }
            }
            DescriptorTerm::Wildcard { .. }
            | DescriptorTerm::Literal { .. }
            | DescriptorTerm::BuiltinToken { .. }
            | DescriptorTerm::Anonymous { .. }
            | DescriptorTerm::Lexeme { .. } => {}
        }
        Ok(())
    }

    fn application(
        &mut self,
        term: &DescriptorTerm,
        application: &DescriptorApplicationRef,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
        at: Option<&(SortType, Position)>,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        let values = arguments
            .iter()
            .map(|argument| match argument {
                krs_ir::TermArgumentRef::Positional { value }
                | krs_ir::TermArgumentRef::Named { value, .. } => value,
            })
            .collect::<Vec<_>>();
        match application {
            DescriptorApplicationRef::Map(operation) => {
                self.collection(term, *operation, &values, at, subject)
            }
            DescriptorApplicationRef::List(operation) => {
                self.collection(term, *operation, &values, at, subject)
            }
            DescriptorApplicationRef::Set(operation) => {
                self.collection(term, *operation, &values, at, subject)
            }
            DescriptorApplicationRef::Builtin(operation)
                if operation.result_sort() == OperationSort::Parameter =>
            {
                // The branches of `kequal::ite` stand at the position.
                for (value, sort) in values.iter().zip(operation.argument_sorts()) {
                    let branch = (*sort == OperationSort::Parameter).then_some(at).flatten();
                    self.walk(value, branch, subject)?;
                }
                Ok(())
            }
            DescriptorApplicationRef::Declared(id) => {
                self.declared_application(term, id, arguments, at, subject)
            }
            DescriptorApplicationRef::Builtin(_) => {
                if let Some(at) = at
                    && !subject
                {
                    let source = Source::Untyped(format!(
                        "`{}` returns an untyped `{}`",
                        spelling(term),
                        super::overload::sort_name(&at.0.sort)
                    ));
                    self.flow(source, at, term_key(term))?;
                }
                for value in values {
                    self.walk(value, None, subject)?;
                }
                Ok(())
            }
            // Brackets at a `List` position are its elements and its rest,
            // as `list::item(head)` and the list it is concatenated with.
            DescriptorApplicationRef::ListNotation(notation) => {
                let carried =
                    at.filter(|(ty, _)| ty.sort == SemanticSortRef::Builtin(BuiltinSort::List));
                let operated = carried.filter(|(ty, _)| ty.is_typed());
                match (notation, values.as_slice()) {
                    (ListNotation::Cons, [head, tail]) => {
                        self.element(head, operated, Step::Element, subject)?;
                        self.walk(tail, carried, subject)
                    }
                    (ListNotation::Snoc, [init, last]) => {
                        self.walk(init, carried, subject)?;
                        self.element(last, operated, Step::Element, subject)
                    }
                    _ => {
                        for value in values {
                            self.walk(value, None, subject)?;
                        }
                        Ok(())
                    }
                }
            }
            DescriptorApplicationRef::Ml(_) | DescriptorApplicationRef::Operator(_) => {
                for value in values {
                    self.walk(value, None, subject)?;
                }
                Ok(())
            }
        }
    }

    /// A production's application: its result checked at the position when
    /// it is written there, and each argument at its field's or parameter's
    /// type.
    fn declared_application(
        &mut self,
        term: &DescriptorTerm,
        id: &StableItemId,
        arguments: &krs_ir::Arguments<krs_ir::DescriptorStage>,
        at: Option<&(SortType, Position)>,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        let types = self.production_types(id);
        if let Some(at) = at
            && !subject
        {
            let source = match types.as_ref().and_then(|types| types.result.as_ref()) {
                Some((ty, _)) if ty.is_typed() => {
                    Source::Typed(Box::new(ty.clone()), format!("`{}`", spelling(term)))
                }
                _ => Source::Untyped(format!(
                    "`{}` returns an untyped `{}`",
                    spelling(term),
                    super::overload::sort_name(&at.0.sort)
                )),
            };
            self.flow(source, at, term_key(term))?;
        }
        // Each argument stands at its field's or parameter's type: a
        // pattern's binder takes it, a written term is checked.
        for (index, argument) in arguments.iter().enumerate() {
            let (field, value) = match argument {
                krs_ir::TermArgumentRef::Positional { value } => (
                    self.catalog
                        .get(id)
                        .and_then(|signature| signature.fields.get(index))
                        .map(|(field, _)| field.as_str()),
                    value,
                ),
                krs_ir::TermArgumentRef::Named { field, value, .. } => {
                    (Some(field.as_str()), value)
                }
            };
            let ty = types
                .as_ref()
                .zip(field)
                .and_then(|(types, field)| types.field(field));
            self.walk(value, ty.as_ref(), subject)?;
        }
        Ok(())
    }

    /// A collection operation: its operands at the types its catalog row
    /// gives them, and its result, when it is not the operated collection,
    /// checked at the position.
    fn collection<O: Typed>(
        &mut self,
        term: &DescriptorTerm,
        operation: O,
        operands: &[&DescriptorTerm],
        at: Option<&(SortType, Position)>,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        let roles = operation.roles();
        if roles.len() != operands.len() {
            // Inference reports the arity.
            return Ok(());
        }
        // The collection the operation reads or builds: the position's for
        // an operation whose result is that collection, else its operand's.
        let carried = at
            .filter(|(ty, _)| ty.sort == SemanticSortRef::Builtin(O::SORT))
            .filter(|_| operation.carries());
        let operated = match carried {
            Some(at) => Some(at.clone()),
            None => self.operand_type(&roles, operands),
        };
        let operated = operated.filter(|(ty, _)| ty.is_typed());
        // A reading operation whose operand the sentence builds, so that no
        // declaration types it, checks that operand against the inverse of
        // the position's type instead (`map::keys(m)` at `Set<K>`: `m` at
        // `Map<K, KItem>`, its discarded values unconstrained).
        let inverse = if operated.is_none() && !subject {
            at.and_then(|at| self.inverse(term, operation, &roles, operands, at))
        } else {
            None
        };
        let operated = operated.or_else(|| inverse.clone());
        for (operand, role) in operands.iter().zip(&roles) {
            match role {
                Role::Collection => self.walk(operand, carried.or(inverse.as_ref()), subject)?,
                Role::Element(step) => {
                    self.element(operand, operated.as_ref(), *step, subject)?;
                }
                Role::Read(step) => {
                    if !self.binding
                        && let Some((ty, position)) = &operated
                        && let Some(part) = ty.part(*step)
                    {
                        self.typing.reads.insert(
                            term_key(operand).clone(),
                            ElementSite {
                                sort: part.sort.clone(),
                                position: position.child(*step),
                                read: false,
                            },
                        );
                    }
                    self.walk(operand, None, subject)?;
                }
                Role::Other => self.walk(operand, None, subject)?,
            }
        }
        if self.binding {
            return Ok(());
        }
        if let Some(step) = operation.projects()
            && let Some((ty, position)) = &operated
            && let Some(part) = ty.part(step)
        {
            self.typing.projections.insert(
                term_key(term).clone(),
                ElementSite {
                    sort: part.sort.clone(),
                    position: position.child(step),
                    read: false,
                },
            );
        }
        if !operation.carries()
            && !subject
            && inverse.is_none()
            && let Some(at) = at
        {
            let source = self.source(term);
            self.flow(source, at, term_key(term))?;
        }
        Ok(())
    }

    /// The type and position a reading operation's collection operand is
    /// checked at, when the operation stands at the typed position `at` and
    /// its one collection operand is a collection the sentence builds (a
    /// collection operation or brackets), which no declaration types. The
    /// parts the operation discards are `KItem`: unconstrained.
    fn inverse<O: Typed>(
        &self,
        term: &DescriptorTerm,
        operation: O,
        roles: &[Role],
        operands: &[&DescriptorTerm],
        at: &(SortType, Position),
    ) -> Option<(SortType, Position)> {
        let (ty, position) = at;
        if operation.carries() || !ty.is_typed() {
            return None;
        }
        let k_item = self.typing.untyped_element.as_ref()?;
        let [operand] = operands
            .iter()
            .zip(roles)
            .filter(|(_, role)| matches!(role, Role::Collection))
            .map(|(operand, _)| *operand)
            .collect::<Vec<_>>()[..]
        else {
            return None;
        };
        let built = matches!(
            operand,
            DescriptorTerm::Application { reference, .. } if matches!(
                reference.application,
                DescriptorApplicationRef::Map(_)
                    | DescriptorApplicationRef::List(_)
                    | DescriptorApplicationRef::Set(_)
                    | DescriptorApplicationRef::ListNotation(_)
            )
        );
        if !built {
            return None;
        }
        let (inverse, collection, part) = operation.operand(ty, k_item)?;
        Some((
            inverse,
            position.read_through(spelling(term), collection, part),
        ))
    }

    /// The type of the first collection operand whose type is known.
    fn operand_type(
        &self,
        roles: &[Role],
        operands: &[&DescriptorTerm],
    ) -> Option<(SortType, Position)> {
        operands
            .iter()
            .zip(roles)
            .filter(|(_, role)| matches!(role, Role::Collection))
            .find_map(|(operand, _)| self.typed_source(operand))
    }

    /// The type and position of a term that is known to be a typed
    /// collection: a binder matched at a typed position, or an operation on
    /// one.
    fn typed_source(&self, term: &DescriptorTerm) -> Option<(SortType, Position)> {
        match term {
            DescriptorTerm::Variable { name, .. } if !self.is_local(name) => {
                match self.typing.binders.get(name) {
                    Some(Matched::Typed(typed)) => Some((**typed).clone()),
                    _ => None,
                }
            }
            DescriptorTerm::Application {
                reference,
                arguments,
                ..
            } => {
                let operands = arguments
                    .iter()
                    .filter_map(|argument| match argument {
                        krs_ir::TermArgumentRef::Positional { value } => Some(value),
                        krs_ir::TermArgumentRef::Named { .. } => None,
                    })
                    .collect::<Vec<_>>();
                match &reference.application {
                    DescriptorApplicationRef::Map(operation) => {
                        self.operation_type(*operation, &operands)
                    }
                    DescriptorApplicationRef::List(operation) => {
                        self.operation_type(*operation, &operands)
                    }
                    DescriptorApplicationRef::Set(operation) => {
                        self.operation_type(*operation, &operands)
                    }
                    DescriptorApplicationRef::Declared(id) => self
                        .production_types(id)?
                        .result
                        .filter(|(ty, _)| ty.is_typed()),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// The type of a collection operation's result, from its operands.
    fn operation_type<O: Typed>(
        &self,
        operation: O,
        operands: &[&DescriptorTerm],
    ) -> Option<(SortType, Position)> {
        let roles = operation.roles();
        if roles.len() != operands.len() {
            return None;
        }
        let (ty, position) = self.operand_type(&roles, operands)?;
        if operation.carries() {
            return Some((ty, position));
        }
        let result = operation.result(&ty)?;
        Some((result, position))
    }

    /// What a term at a typed position is.
    fn source(&self, term: &DescriptorTerm) -> Source {
        match term {
            DescriptorTerm::Variable { name, .. } => {
                if self.is_local(name) {
                    Source::Unknown
                } else {
                    self.binder_source(name)
                }
            }
            DescriptorTerm::Application { reference, .. } => match &reference.application {
                DescriptorApplicationRef::Map(TermMapOperation::Empty)
                | DescriptorApplicationRef::List(ListOperation::Empty)
                | DescriptorApplicationRef::Set(SetOperation::Empty) => Source::Fits,
                DescriptorApplicationRef::Map(_)
                | DescriptorApplicationRef::List(_)
                | DescriptorApplicationRef::Set(_) => match self.typed_source(term) {
                    Some((ty, position)) => Source::Typed(
                        Box::new(ty),
                        format!("`{}`, read from {},", spelling(term), position.describe()),
                    ),
                    None => Source::Untyped(format!(
                        "`{}` reads a collection whose element types are not declared",
                        spelling(term)
                    )),
                },
                _ => Source::Unknown,
            },
            _ => Source::Unknown,
        }
    }

    /// The collection types of a production's fields and result, as its
    /// constructor descriptor declares them.
    fn production_types(&self, id: &StableItemId) -> Option<ProductionTypes> {
        let constructor = self.declarations?.constructor(id).ok()?;
        let production = id.item_name().to_owned();
        let parameter = self
            .catalog
            .get(id)
            .is_some_and(|signature| signature.function);
        let result = Some(SortType::of_production(
            &constructor.sort,
            &constructor.arguments,
        ))
        .filter(|ty| ty.kind().is_some())
        .map(|ty| {
            let position = Position::of(Owner::Result(production.clone()), ty.clone());
            (ty, position)
        });
        let fields = constructor
            .fields
            .iter()
            .filter_map(|field| {
                let ty = SortType::of_production(field.sort.as_ref()?, &field.arguments);
                ty.kind()?;
                let position = Position::of(
                    Owner::Field {
                        production: production.clone(),
                        field: field.name.clone(),
                        parameter,
                    },
                    ty.clone(),
                );
                Some((field.name.clone(), (ty, position)))
            })
            .collect();
        Some(ProductionTypes { result, fields })
    }

    fn binder_source(&self, name: &str) -> Source {
        match self.typing.binders.get(name) {
            Some(Matched::Typed(typed)) => Source::Typed(
                Box::new(typed.0.clone()),
                if matches!(typed.1.owner, Owner::Variable { .. }) {
                    format!("{},", typed.1.describe())
                } else {
                    format!("`{name}`, matched as {},", typed.1.describe())
                },
            ),
            Some(Matched::Untyped(reason)) => Source::Untyped(reason.clone()),
            Some(Matched::Checked) => Source::Fits,
            None => Source::Untyped(format!(
                "`{name}` is matched where no element types are declared"
            )),
        }
    }

    /// Checks a term of `source` written at `at`: a typed term must fit,
    /// and an untyped one is an error, since nothing checks its elements.
    fn flow(
        &mut self,
        source: Source,
        at: &(SortType, Position),
        key: &ProvenanceKey,
    ) -> Result<(), DescriptorLoweringError> {
        let (ty, position) = at;
        if self.binding || !ty.is_typed() {
            return Ok(());
        }
        match source {
            Source::Fits | Source::Unknown => Ok(()),
            Source::Untyped(reason) => Err(self.untyped(position, &reason, key)),
            Source::Typed(actual, what) => match actual.fits(ty, self.parents) {
                Fit::Yes => Ok(()),
                Fit::Untyped => Err(self.untyped(
                    position,
                    &format!("{what} has type `{actual}`, which declares not every element type"),
                    key,
                )),
                Fit::No => {
                    let (left, right) = actual
                        .first_mismatch(ty, self.parents)
                        .expect("a type that does not fit has a mismatched argument");
                    Err(DescriptorLoweringError::CollectionElementSort {
                        item: Box::new(self.descriptor.id().clone()),
                        reason: format!(
                            "{what} has type `{actual}`, which does not fit {}: {} is not {}",
                            position.describe_declared(),
                            super::overload::sort_name(left),
                            a(right),
                        ),
                        range: authored_range(self.descriptor, key),
                    })
                }
            },
        }
    }

    /// The error for a term whose elements nothing declares, written at a
    /// typed position: it would break the position's invariant unchecked.
    fn untyped(
        &self,
        position: &Position,
        reason: &str,
        key: &ProvenanceKey,
    ) -> DescriptorLoweringError {
        DescriptorLoweringError::UntypedCollection {
            item: Box::new(self.descriptor.id().clone()),
            reason: format!(
                "{reason}, so nothing checks the elements it writes to {}",
                position.describe_declared()
            ),
            range: authored_range(self.descriptor, key),
        }
    }

    /// An element operand: inferred at the part's sort, and checked at the
    /// part's type when the part is itself a typed collection.
    fn element(
        &mut self,
        operand: &DescriptorTerm,
        operated: Option<&(SortType, Position)>,
        step: Step,
        subject: bool,
    ) -> Result<(), DescriptorLoweringError> {
        let part = operated.and_then(|(ty, position)| {
            ty.part(step)
                .map(|part| (part.clone(), position.child(step)))
        });
        if let Some((part, position)) = &part
            && !self.binding
        {
            let key = term_key(operand).clone();
            let site = ElementSite {
                sort: part.sort.clone(),
                position: position.clone(),
                read: false,
            };
            // A `k::rewrite!` stores both of its sides at the position.
            let sides = match operand {
                DescriptorTerm::Rewrite { from, to, .. } => std::iter::once(from.as_ref())
                    .chain(to.as_deref())
                    .collect(),
                operand => vec![operand],
            };
            for side in sides {
                match side {
                    DescriptorTerm::Variable { name, .. } if !self.is_local(name) => {
                        self.typing
                            .element_binders
                            .entry(name.clone())
                            .or_default()
                            .push((key.clone(), site.clone()));
                    }
                    stored if !std::ptr::eq(stored, operand) => {
                        self.typing
                            .elements
                            .insert(term_key(stored).clone(), site.clone());
                    }
                    _ => {}
                }
            }
            self.typing.elements.insert(key, site);
        }
        let nested = part.filter(|(part, _)| part.kind().is_some());
        self.walk(operand, nested.as_ref(), subject)
    }
}

/// The collection-typed fields (or parameters) and result of a production.
struct ProductionTypes {
    result: Option<(SortType, Position)>,
    fields: BTreeMap<String, (SortType, Position)>,
}

impl ProductionTypes {
    fn field(&self, name: &str) -> Option<(SortType, Position)> {
        self.fields.get(name).cloned()
    }
}

/// Checks the collection types every constructor and function declares for
/// its fields, parameters, and result: `Map<Id>` and `Foo<Int>` are errors
/// wherever the production is used, or if it never is.
pub(super) fn check_production_types(
    descriptors: &[&Descriptor],
    catalog: &BTreeMap<StableItemId, ProductionSignature>,
) -> Result<(), DescriptorLoweringError> {
    for descriptor in descriptors {
        let krs_ir::DescriptorPayload::Constructor(constructor) = descriptor.payload() else {
            continue;
        };
        let production = descriptor.id().item_name();
        let noun = if catalog
            .get(descriptor.id())
            .is_some_and(|signature| signature.function)
        {
            "parameter"
        } else {
            "field"
        };
        if let Some(first) = constructor.arguments.first() {
            SortType::of_production(&constructor.sort, &constructor.arguments).check_arity(
                &format!("the result of `{production}`"),
                descriptor,
                &first.sort.key,
            )?;
        }
        for field in &constructor.fields {
            if let (Some(sort), Some(first)) = (&field.sort, field.arguments.first()) {
                SortType::of_production(sort, &field.arguments).check_arity(
                    &format!("the {noun} `{}` of `{production}`", field.name),
                    descriptor,
                    &first.sort.key,
                )?;
            }
        }
    }
    Ok(())
}

/// The part of a collection an operand stands for.
#[derive(Clone, Copy, Debug)]
enum Role {
    /// A collection of the operated type.
    Collection,
    /// A key, value, or element stored in the collection: inferred at its
    /// sort.
    Element(Step),
    /// A key or element looked up: it must share a sort with the part.
    Read(Step),
    /// An index, a count, or a collection of any type.
    Other,
}

/// The typing rows of the collection catalog.
trait Typed: CollectionApplication {
    /// The role of each operand, in wire order.
    fn roles(self) -> Vec<Role>;
    /// Whether the result is the operated collection (`map::update`), as
    /// opposed to something read from it (`map::keys`).
    fn carries(self) -> bool;
    /// The part a projecting read (`map::get`) returns.
    fn projects(self) -> Option<Step> {
        None
    }
    /// The type of a non-carrying result read from a collection of `ty`.
    fn result(self, ty: &SortType) -> Option<SortType>;
    /// The type a non-carrying operation's collection operand must have for
    /// its result to fit `result`, its discarded parts `k_item`, with the
    /// nouns of the operand's collection and of the part the result holds.
    /// The result fits exactly when the operand fits this type.
    fn operand(
        self,
        result: &SortType,
        k_item: &SemanticSortRef,
    ) -> Option<(SortType, &'static str, &'static str)>;
}

/// The unconstrained part of an inverse type: any `KItem`.
fn any(k_item: &SemanticSortRef) -> SortType {
    SortType {
        sort: k_item.clone(),
        arguments: Vec::new(),
    }
}

impl Typed for TermMapOperation {
    fn roles(self) -> Vec<Role> {
        use Role::{Collection, Element, Other, Read};
        match self {
            Self::Empty => vec![],
            Self::Update => vec![Collection, Element(Step::Key), Element(Step::Value)],
            Self::Get | Self::Remove => vec![Collection, Read(Step::Key)],
            Self::InKeys => vec![Read(Step::Key), Collection],
            Self::RemoveAll => vec![Collection, Other],
            Self::Keys | Self::KeysList | Self::Values | Self::Size => vec![Collection],
            Self::UpdateAll => vec![Collection, Collection],
            Self::GetOrDefault => vec![Collection, Read(Step::Key), Element(Step::Value)],
        }
    }

    fn carries(self) -> bool {
        matches!(
            self,
            Self::Empty | Self::Update | Self::Remove | Self::RemoveAll | Self::UpdateAll
        )
    }

    fn projects(self) -> Option<Step> {
        matches!(self, Self::Get | Self::GetOrDefault).then_some(Step::Value)
    }

    fn result(self, ty: &SortType) -> Option<SortType> {
        let key = ty.part(Step::Key)?;
        let value = ty.part(Step::Value)?;
        match self {
            Self::Get | Self::GetOrDefault => Some(value.clone()),
            Self::Keys => Some(SortType::collection(BuiltinSort::Set, vec![key.clone()])),
            Self::KeysList => Some(SortType::collection(BuiltinSort::List, vec![key.clone()])),
            Self::Values => Some(SortType::collection(BuiltinSort::List, vec![value.clone()])),
            _ => None,
        }
    }

    fn operand(
        self,
        result: &SortType,
        k_item: &SemanticSortRef,
    ) -> Option<(SortType, &'static str, &'static str)> {
        let map = |key: SortType, value: SortType| {
            SortType::collection(BuiltinSort::Map, vec![key, value])
        };
        match (self, result.kind()) {
            (Self::Keys, Some(BuiltinSort::Set)) | (Self::KeysList, Some(BuiltinSort::List)) => {
                Some((
                    map(result.part(Step::Element)?.clone(), any(k_item)),
                    "map",
                    "keys",
                ))
            }
            (Self::Values, Some(BuiltinSort::List)) => Some((
                map(any(k_item), result.part(Step::Element)?.clone()),
                "map",
                "values",
            )),
            (Self::Get | Self::GetOrDefault, _) => {
                Some((map(any(k_item), result.clone()), "map", "values"))
            }
            _ => None,
        }
    }
}

impl Typed for ListOperation {
    fn roles(self) -> Vec<Role> {
        use Role::{Collection, Element, Other, Read};
        match self {
            Self::Empty => vec![],
            Self::Item => vec![Element(Step::Element)],
            Self::Concat => vec![Collection, Collection],
            Self::Get => vec![Collection, Other],
            Self::Update => vec![Collection, Other, Element(Step::Element)],
            Self::Size => vec![Collection],
            Self::Make => vec![Other, Element(Step::Element)],
            Self::Range => vec![Collection, Other, Other],
            Self::UpdateAll => vec![Collection, Other, Collection],
            Self::Contains => vec![Read(Step::Element), Collection],
        }
    }

    fn carries(self) -> bool {
        !matches!(self, Self::Get | Self::Size | Self::Contains)
    }

    fn projects(self) -> Option<Step> {
        matches!(self, Self::Get).then_some(Step::Element)
    }

    fn result(self, ty: &SortType) -> Option<SortType> {
        match self {
            Self::Get => ty.part(Step::Element).cloned(),
            _ => None,
        }
    }

    fn operand(
        self,
        result: &SortType,
        _k_item: &SemanticSortRef,
    ) -> Option<(SortType, &'static str, &'static str)> {
        match self {
            Self::Get => Some((
                SortType::collection(BuiltinSort::List, vec![result.clone()]),
                "list",
                "elements",
            )),
            _ => None,
        }
    }
}

impl Typed for SetOperation {
    fn roles(self) -> Vec<Role> {
        use Role::{Collection, Element, Other, Read};
        match self {
            Self::Empty => vec![],
            Self::Item => vec![Element(Step::Element)],
            Self::Concat | Self::Union => vec![Collection, Collection],
            Self::Contains => vec![Read(Step::Element), Collection],
            Self::Difference | Self::Intersect => vec![Collection, Other],
            Self::Size | Self::ToList | Self::FromList => vec![Collection],
            Self::IsSubset => vec![Other, Other],
        }
    }

    fn carries(self) -> bool {
        matches!(
            self,
            Self::Empty
                | Self::Item
                | Self::Concat
                | Self::Union
                | Self::Difference
                | Self::Intersect
        )
    }

    /// `set::to_list(s)` and `set::from_list(l)` keep the element type; the
    /// operand of `from_list` is a list.
    fn result(self, ty: &SortType) -> Option<SortType> {
        let element = ty.part(Step::Element)?;
        match self {
            Self::ToList => Some(SortType::collection(
                BuiltinSort::List,
                vec![element.clone()],
            )),
            Self::FromList => Some(SortType::collection(
                BuiltinSort::Set,
                vec![element.clone()],
            )),
            _ => None,
        }
    }

    fn operand(
        self,
        result: &SortType,
        _k_item: &SemanticSortRef,
    ) -> Option<(SortType, &'static str, &'static str)> {
        let element = result.part(Step::Element)?.clone();
        match (self, result.kind()?) {
            (Self::ToList, BuiltinSort::List) => Some((
                SortType::collection(BuiltinSort::Set, vec![element]),
                "set",
                "elements",
            )),
            (Self::FromList, BuiltinSort::Set) => Some((
                SortType::collection(BuiltinSort::List, vec![element]),
                "list",
                "elements",
            )),
            _ => None,
        }
    }
}

/// A sort's name with its indefinite article: `a Value`, `an Id`.
fn a(sort: &SemanticSortRef) -> String {
    let name = super::overload::sort_name(sort);
    let article = if name.starts_with(['A', 'E', 'I', 'O', 'U']) {
        "an"
    } else {
        "a"
    };
    format!("{article} {name}")
}

/// The provenance key of a term.
pub(super) fn term_key(term: &DescriptorTerm) -> &ProvenanceKey {
    super::infer::StructuredTermBuilder::term_key(term)
}

/// A short spelling of a term for messages.
pub(super) fn spelling(term: &DescriptorTerm) -> String {
    match term {
        DescriptorTerm::Variable { name, .. } => name.clone(),
        DescriptorTerm::Literal { literal, .. } => match literal {
            krs_ir::DescriptorLiteral::Int(value) | krs_ir::DescriptorLiteral::Float(value) => {
                value.clone()
            }
            krs_ir::DescriptorLiteral::Bool(value) => value.to_string(),
            krs_ir::DescriptorLiteral::String(value) => format!("{value:?}"),
        },
        DescriptorTerm::Application { reference, .. } => {
            application_spelling(&reference.application)
        }
        DescriptorTerm::BuiltinToken { sort, .. } => match sort {
            BuiltinSort::Id => "k::id!(..)".to_owned(),
            BuiltinSort::Bytes => "k::bytes!(..)".to_owned(),
            _ => "this token".to_owned(),
        },
        DescriptorTerm::Anonymous { .. } => "k::anonymous!(..)".to_owned(),
        DescriptorTerm::Lexeme { text, .. } => format!("k::lexeme!(.., {text:?})"),
        DescriptorTerm::OrBool { .. } => "k::or_bool!(..)".to_owned(),
        DescriptorTerm::SortTest { kind, sort, .. } => format!(
            "{}({}, ..)",
            match kind {
                krs_ir::SortTestKind::Predicate => "k::is!",
                krs_ir::SortTestKind::Projection => "k::project!",
            },
            super::overload::sort_name(&semantic_sort_ref(&sort.sort))
        ),
        _ => "this term".to_owned(),
    }
}

/// A short spelling of an application for messages: `Skip(..)`,
/// `map::update(..)`, an operator as written.
pub(super) fn application_spelling(application: &DescriptorApplicationRef) -> String {
    let head = match application {
        DescriptorApplicationRef::Declared(id) => id.item_name().to_owned(),
        DescriptorApplicationRef::Map(operation) => marker(operation.facade_marker()),
        DescriptorApplicationRef::List(operation) => marker(operation.facade_marker()),
        DescriptorApplicationRef::Set(operation) => marker(operation.facade_marker()),
        DescriptorApplicationRef::Builtin(operation) => operation.to_string(),
        DescriptorApplicationRef::Operator(operator) => return operator_spelling(*operator),
        DescriptorApplicationRef::Ml(_) | DescriptorApplicationRef::ListNotation(_) => {
            return "this term".to_owned();
        }
    };
    format!("{head}(..)")
}

/// An operator as written, its operands elided: `.. + ..`, `!..`.
pub(super) fn operator_spelling(operator: krs_ir::BuiltinOperator) -> String {
    if operator.arity() == 1 {
        format!("{}..", operator.symbol())
    } else {
        format!(".. {} ..", operator.symbol())
    }
}

fn marker(marker: krs_ir::FacadeMarker) -> String {
    format!("{}::{}", marker.module, marker.name)
}

/// Every name a pattern binds.
fn pattern_names(pattern: &DescriptorTerm) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    collect_pattern_names(pattern, &mut names);
    names
}

fn collect_pattern_names(term: &DescriptorTerm, names: &mut BTreeSet<String>) {
    match term {
        DescriptorTerm::Variable { name, .. } => {
            names.insert(name.clone());
        }
        DescriptorTerm::As { name, pattern, .. } => {
            names.insert(name.clone());
            collect_pattern_names(pattern, names);
        }
        DescriptorTerm::Or { alternatives, .. } => {
            for alternative in alternatives.iter() {
                collect_pattern_names(alternative, names);
            }
        }
        DescriptorTerm::Application { arguments, .. } => {
            for argument in arguments {
                let (krs_ir::TermArgumentRef::Positional { value }
                | krs_ir::TermArgumentRef::Named { value, .. }) = argument;
                collect_pattern_names(value, names);
            }
        }
        DescriptorTerm::Cell { fields, .. } => {
            for field in fields {
                collect_pattern_names(&field.value, names);
            }
        }
        _ => {}
    }
}

fn authored_range(
    descriptor: &Descriptor,
    key: &ProvenanceKey,
) -> Option<Box<krs_ir::SourceRange>> {
    descriptor
        .provenance()
        .origin_for(key)
        .and_then(krs_ir::OriginStack::exact_authored_range)
        .map(Box::new)
}

/// Whether two sorts have a common subsort, so that some term has both.
pub(super) fn share_a_sort(
    left: &SemanticSortRef,
    right: &SemanticSortRef,
    parents: &SortParents,
) -> bool {
    semantic_is_subsort(left, right, parents)
        || semantic_is_subsort(right, left, parents)
        || !most_specific_common_descendants(
            &BTreeSet::from([left.clone(), right.clone()]),
            parents,
        )
        .is_empty()
}

/// The error for a map read `{ k -> v, .. }` whose value binder is narrowed
/// to a sort no value of the map has.
pub(super) fn disjoint_refinement(
    descriptor: &Descriptor,
    cell: &str,
    declared: &SortType,
    name: &str,
    refinement: &SemanticSortRef,
    key: &ProvenanceKey,
) -> DescriptorLoweringError {
    let value = declared
        .map_value()
        .map_or_else(String::new, |value| super::overload::sort_name(&value.sort));
    let refinement_sort = refinement;
    let refinement = super::overload::sort_name(refinement);
    DescriptorLoweringError::CollectionElementSort {
        item: Box::new(descriptor.id().clone()),
        reason: format!(
            "`{name}` is read as a value of the cell `{cell}`, declared `{declared}`, but `where {name}: {refinement}` asks for {}, which no {value} is",
            a(refinement_sort)
        ),
        range: authored_range(descriptor, key),
    }
}

/// The error for a read that asks for a sort the collection never holds.
pub(super) fn disjoint_read(
    descriptor: &Descriptor,
    site: &ElementSite,
    what: &str,
    asked: &SemanticSortRef,
    key: &ProvenanceKey,
) -> DescriptorLoweringError {
    DescriptorLoweringError::CollectionElementSort {
        item: Box::new(descriptor.id().clone()),
        reason: format!(
            "{what} reads {}, which is always {} and never {}",
            site.position.describe_declared(),
            a(&site.sort),
            a(asked),
        ),
        range: authored_range(descriptor, key),
    }
}

/// The error for an element operand whose sort is not the element sort.
pub(super) fn element_mismatch(
    descriptor: &Descriptor,
    site: &ElementSite,
    what: &str,
    actual: &str,
    key: &ProvenanceKey,
) -> DescriptorLoweringError {
    DescriptorLoweringError::CollectionElementSort {
        item: Box::new(descriptor.id().clone()),
        reason: format!(
            "`{what}` of sort {actual} is stored as {}, and {actual} is not {}",
            site.position.describe_declared(),
            a(&site.sort),
        ),
        range: authored_range(descriptor, key),
    }
}

/// The error for a binder stored at an element position whose other
/// occurrences need sorts no element has. `others` is the one sort they
/// meet at, when there is one.
pub(super) fn binder_conflict(
    descriptor: &Descriptor,
    name: &str,
    key: &ProvenanceKey,
    site: &ElementSite,
    others: Option<&SemanticSortRef>,
    occurrence_sorts: &str,
) -> DescriptorLoweringError {
    let verb = if site.read { "read" } else { "stored" };
    let reason = match others {
        Some(sort) => {
            let name_of_sort = super::overload::sort_name(sort);
            format!(
                "`{name}` of sort {name_of_sort} is {verb} as {}, and {name_of_sort} is not {}",
                site.position.describe_declared(),
                a(&site.sort),
            )
        }
        None => format!(
            "`{name}` is {verb} as {}, but its occurrences need the sorts [{occurrence_sorts}], which no {} has together",
            site.position.describe_declared(),
            super::overload::sort_name(&site.sort),
        ),
    };
    DescriptorLoweringError::CollectionElementSort {
        item: Box::new(descriptor.id().clone()),
        reason,
        range: authored_range(descriptor, key),
    }
}

/// The content type of a selected cell, through the declaration index.
pub(super) fn selected_cell_type(
    walker: &Walker<'_>,
    cell: &krs_ir::DescriptorCellReference,
    declarations: &DescriptorIndex<'_>,
) -> Result<Option<(SortType, Position)>, DescriptorLoweringError> {
    walker.cell_type(require_cell_field(&cell.cell, declarations)?)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn declared(name: &str) -> SemanticSortRef {
        SemanticSortRef::Declared(krs_ir::testing::item("sorts", name, krs_ir::ItemKind::Sort))
    }

    impl SortType {
        fn plain(sort: SemanticSortRef) -> Self {
            Self {
                sort,
                arguments: Vec::new(),
            }
        }
    }

    fn builtin(sort: BuiltinSort) -> SortType {
        SortType::plain(SemanticSortRef::Builtin(sort))
    }

    /// `Int` and `Value` below `KItem`; `Int` below `Value`; `Stmt` below
    /// `KItem` only.
    fn graph() -> SortParents {
        let k_item = declared("KItem");
        BTreeMap::from([
            (
                SemanticSortRef::Builtin(BuiltinSort::Int),
                BTreeSet::from([declared("Value")]),
            ),
            (declared("Value"), BTreeSet::from([k_item.clone()])),
            (declared("Stmt"), BTreeSet::from([k_item.clone()])),
            (
                SemanticSortRef::Builtin(BuiltinSort::Id),
                BTreeSet::from([k_item]),
            ),
        ])
    }

    fn map(key: SortType, value: SortType) -> SortType {
        SortType::collection(BuiltinSort::Map, vec![key, value])
    }

    fn set(element: SortType) -> SortType {
        SortType::collection(BuiltinSort::Set, vec![element])
    }

    fn list(element: SortType) -> SortType {
        SortType::collection(BuiltinSort::List, vec![element])
    }

    /// A reading operation's operand type is the inverse of its result's:
    /// the result fits exactly when the operand fits it, the discarded parts
    /// `KItem`, so a map of any values fits under `map::keys`.
    #[test]
    fn reading_operations_invert_their_result_type() {
        let parents = graph();
        let k_item = declared("KItem");
        let any = SortType::plain(k_item.clone());
        let id = builtin(BuiltinSort::Id);
        let int = builtin(BuiltinSort::Int);
        let stmt = SortType::plain(declared("Stmt"));
        let inverse = TermMapOperation::Keys
            .operand(&set(id.clone()), &k_item)
            .unwrap();
        assert_eq!(inverse, (map(id.clone(), any.clone()), "map", "keys"));
        assert_eq!(
            map(id.clone(), stmt.clone()).fits(&inverse.0, &parents),
            Fit::Yes
        );
        assert_eq!(
            map(int.clone(), stmt.clone()).fits(&inverse.0, &parents),
            Fit::No
        );
        assert_eq!(
            TermMapOperation::KeysList
                .operand(&list(id.clone()), &k_item)
                .unwrap()
                .0,
            map(id.clone(), any.clone())
        );
        assert_eq!(
            TermMapOperation::Values
                .operand(&list(int.clone()), &k_item)
                .unwrap()
                .0,
            map(any.clone(), int.clone())
        );
        assert_eq!(
            TermMapOperation::Get
                .operand(&set(int.clone()), &k_item)
                .unwrap()
                .0,
            map(any.clone(), set(int.clone()))
        );
        assert_eq!(
            ListOperation::Get
                .operand(&set(int.clone()), &k_item)
                .unwrap()
                .0,
            list(set(int.clone()))
        );
        assert_eq!(
            SetOperation::ToList
                .operand(&list(id.clone()), &k_item)
                .unwrap()
                .0,
            set(id.clone())
        );
        assert_eq!(
            SetOperation::FromList
                .operand(&set(id.clone()), &k_item)
                .unwrap()
                .0,
            list(id.clone())
        );
        // A result of the wrong collection has no inverse; sort inference
        // rejects it, and a carrying operation has none to take.
        assert!(
            TermMapOperation::Keys
                .operand(&list(id.clone()), &k_item)
                .is_none()
        );
        assert!(
            TermMapOperation::Update
                .operand(&map(id.clone(), int), &k_item)
                .is_none()
        );
        assert!(SetOperation::FromList.operand(&list(id), &k_item).is_none());
    }

    #[test]
    fn arguments_are_covariant() {
        let parents = graph();
        let id = builtin(BuiltinSort::Id);
        let int = builtin(BuiltinSort::Int);
        let value = SortType::plain(declared("Value"));
        let stmt = SortType::plain(declared("Stmt"));
        let env = map(id.clone(), value.clone());
        assert_eq!(map(id.clone(), int).fits(&env, &parents), Fit::Yes);
        assert_eq!(
            map(id.clone(), value.clone()).fits(&env, &parents),
            Fit::Yes
        );
        assert_eq!(map(id.clone(), stmt).fits(&env, &parents), Fit::No);
        assert_eq!(
            env.fits(&map(id, SortType::plain(declared("KItem"))), &parents),
            Fit::Yes
        );
        // A wider value type does not fit a narrower one.
        assert_eq!(
            map(builtin(BuiltinSort::Id), value.clone()).fits(
                &map(builtin(BuiltinSort::Id), builtin(BuiltinSort::Int)),
                &parents
            ),
            Fit::No
        );
    }

    #[test]
    fn nested_arguments_are_checked() {
        let parents = graph();
        let int = builtin(BuiltinSort::Int);
        let accessed = map(int.clone(), set(int.clone()));
        assert_eq!(accessed.fits(&accessed, &parents), Fit::Yes);
        assert_eq!(
            map(int.clone(), set(SortType::plain(declared("Stmt")))).fits(&accessed, &parents),
            Fit::No
        );
        // A bare inner `Set` has no declared element type.
        assert_eq!(
            map(int.clone(), builtin(BuiltinSort::Set)).fits(&accessed, &parents),
            Fit::Untyped
        );
        // A typed term fits a bare inner position.
        assert_eq!(
            accessed.fits(&map(int, builtin(BuiltinSort::Set)), &parents),
            Fit::Yes
        );
    }

    #[test]
    fn untyped_collections_accept_and_are_untyped() {
        let parents = graph();
        let env = map(builtin(BuiltinSort::Id), SortType::plain(declared("Value")));
        let raw = builtin(BuiltinSort::Map);
        assert_eq!(env.fits(&raw, &parents), Fit::Yes);
        assert_eq!(raw.fits(&env, &parents), Fit::Untyped);
        assert_eq!(raw.fits(&raw, &parents), Fit::Yes);
    }

    #[test]
    fn the_meet_keeps_the_typed_and_the_narrower_type() {
        let parents = graph();
        let id = builtin(BuiltinSort::Id);
        let env = map(id.clone(), SortType::plain(declared("Value")));
        let ints = map(id, builtin(BuiltinSort::Int));
        let raw = builtin(BuiltinSort::Map);
        assert_eq!(raw.clone().meet(env.clone(), &parents), env);
        assert_eq!(env.clone().meet(raw, &parents), env);
        assert_eq!(env.clone().meet(ints.clone(), &parents), ints);
        assert_eq!(ints.clone().meet(env, &parents), ints);
    }

    #[test]
    fn types_and_positions_print_as_written() {
        let int = builtin(BuiltinSort::Int);
        let accessed = map(int.clone(), set(int));
        assert_eq!(accessed.to_string(), "Map<Int, Set<Int>>");
        let position = Position::cell("accessed_storage", accessed)
            .child(Step::Value)
            .child(Step::Element);
        assert_eq!(
            position.describe_declared(),
            "an element of a value of the cell `accessed_storage`, declared `Map<Int, Set<Int>>`"
        );
    }

    #[test]
    fn fields_parameters_and_results_are_named_as_declared() {
        let int = builtin(BuiltinSort::Int);
        let accessed = map(int.clone(), set(int));
        let parameter = Position::of(
            Owner::Field {
                production: "MarkStorageAccess".to_owned(),
                field: "accessed".to_owned(),
                parameter: true,
            },
            accessed.clone(),
        )
        .child(Step::Value);
        assert_eq!(
            parameter.describe_declared(),
            "a value of the parameter `accessed` of `MarkStorageAccess`, declared `Map<Int, Set<Int>>`"
        );
        let field = Position::of(
            Owner::Field {
                production: "Snapshot".to_owned(),
                field: "storage".to_owned(),
                parameter: false,
            },
            accessed.clone(),
        );
        assert_eq!(field.describe(), "the field `storage` of `Snapshot`");
        let result = Position::of(Owner::Result("MarkStorageAccess".to_owned()), accessed)
            .child(Step::Value)
            .child(Step::Element);
        assert_eq!(
            result.describe(),
            "an element of a value of the result of `MarkStorageAccess`"
        );
    }

    #[test]
    fn the_catalog_rows_cover_every_operation() {
        for operation in TermMapOperation::ALL {
            assert_eq!(
                operation.roles().len(),
                operation.spec().arity(),
                "{operation}"
            );
        }
        for operation in ListOperation::ALL {
            assert_eq!(
                operation.roles().len(),
                operation.spec().arity(),
                "{operation}"
            );
        }
        for operation in SetOperation::ALL {
            assert_eq!(
                operation.roles().len(),
                operation.spec().arity(),
                "{operation}"
            );
        }
    }

    #[test]
    fn reads_derive_their_types() {
        let int = builtin(BuiltinSort::Int);
        let id = builtin(BuiltinSort::Id);
        let value = SortType::plain(declared("Value"));
        let env = map(id.clone(), value.clone());
        assert_eq!(TermMapOperation::Get.result(&env), Some(value.clone()));
        assert_eq!(TermMapOperation::Keys.result(&env), Some(set(id.clone())));
        assert_eq!(
            TermMapOperation::Values.result(&env),
            Some(SortType::collection(BuiltinSort::List, vec![value]))
        );
        assert_eq!(
            SetOperation::ToList.result(&set(int.clone())),
            Some(SortType::collection(BuiltinSort::List, vec![int.clone()]))
        );
        assert_eq!(
            SetOperation::FromList
                .result(&SortType::collection(BuiltinSort::List, vec![id.clone()])),
            Some(set(id))
        );
        assert_eq!(
            TermMapOperation::Get.result(&builtin(BuiltinSort::Map)),
            None
        );
        let _ = int;
    }
}
