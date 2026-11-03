//! Step-event declarations and a baseline-owned observation decider.

use std::collections::BTreeMap;

use k_rust::backend::{Backend, BackendError};
use k_rust::kore::ast::{Pattern, Sort, VariableKind};
use k_rust_backend::definition::BackendDefinition;
use k_rust_backend::nesting::SegmentRefused;
use k_rust_backend::smt::SmtSolver;
use k_rust_backend::term::Sort as InternalSort;
use kink_pattern::{
    Constructor, EventVocabulary, Feasibility, PathInput, RelationDecider, RelationDecision,
    TermRelation,
};

use crate::data::DataEnds;
use crate::feasibility::{
    BackendRelations, Inhabitation, TestInitialState, contains_non_strict_injection,
    contains_untrusted_domain_value, domain_value_identity_safe, free_constructor,
    non_strict_injection_node, strict_injection_sorts,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StepEventSpec {
    pub constructor: String,
    pub pre: Pattern,
    pub post: Option<Pattern>,
    pub payload: Vec<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StepObservationError {
    Internalization(String),
    VariableSort(String),
    NonFreeSymbol(String),
    NonCanonicalValue(String),
    UnsupportedPattern(String),
    ReservedVariable(String),
    MissingPayload(String),
    ConstructorSorts(String),
}

impl std::fmt::Display for StepObservationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for StepObservationError {}
impl From<BackendError> for StepObservationError {
    fn from(error: BackendError) -> Self {
        Self::Internalization(error.to_string())
    }
}
impl From<k_rust_backend::stop::StopCause> for StepObservationError {
    fn from(cause: k_rust_backend::stop::StopCause) -> Self {
        Self::Internalization(cause.to_string())
    }
}

#[derive(Clone, Debug)]
pub struct StepObservation {
    specs: Vec<StepEventSpec>,
    vocabulary: EventVocabulary,
}

impl StepObservation {
    pub fn new(
        backend: &mut Backend,
        specs: Vec<StepEventSpec>,
    ) -> Result<Self, StepObservationError> {
        let vocabulary = Self::vocabulary_of(&specs)?;
        backend.with_solver(None, |definition, _| -> Result<(), StepObservationError> {
            for spec in &specs {
                validate_pattern(definition, &spec.pre)?;
                if let Some(post) = &spec.post {
                    validate_pattern(definition, post)?;
                }
            }
            Ok(())
        })?;
        Ok(Self { specs, vocabulary })
    }

    pub fn vocabulary(&self) -> &EventVocabulary {
        &self.vocabulary
    }
    pub fn specs(&self) -> &[StepEventSpec] {
        &self.specs
    }

    pub fn vocabulary_of(specs: &[StepEventSpec]) -> Result<EventVocabulary, StepObservationError> {
        let mut constructors = BTreeMap::<String, Vec<Sort>>::new();
        for spec in specs {
            let mut vars = BTreeMap::new();
            collect_variables(&spec.pre, &mut vars)?;
            if let Some(post) = &spec.post {
                collect_variables(post, &mut vars)?;
            }
            let sorts = spec
                .payload
                .iter()
                .map(|name| {
                    vars.get(name)
                        .cloned()
                        .ok_or_else(|| StepObservationError::MissingPayload(name.clone()))
                })
                .collect::<Result<Vec<_>, _>>()?;
            match constructors.get(&spec.constructor) {
                Some(old) if old != &sorts => {
                    return Err(StepObservationError::ConstructorSorts(
                        spec.constructor.clone(),
                    ));
                }
                None => {
                    constructors.insert(spec.constructor.clone(), sorts);
                }
                _ => {}
            }
        }
        EventVocabulary::new(
            constructors
                .into_iter()
                .map(|(name, payload_sorts)| Constructor {
                    name,
                    payload_sorts,
                })
                .collect(),
        )
        .map_err(|error| StepObservationError::ConstructorSorts(error.to_string()))
    }
}

fn collect_variables(
    pattern: &Pattern,
    vars: &mut BTreeMap<String, Sort>,
) -> Result<(), StepObservationError> {
    match pattern {
        Pattern::Variable(var) => {
            if var.kind != VariableKind::Element {
                return Err(StepObservationError::UnsupportedPattern(var.name.clone()));
            }
            if var.name.contains('!') {
                return Err(StepObservationError::ReservedVariable(var.name.clone()));
            }
            if let Some(old) = vars.insert(var.name.clone(), var.sort.clone())
                && old != var.sort
            {
                return Err(StepObservationError::VariableSort(var.name.clone()));
            }
        }
        Pattern::Application { arguments, .. } => {
            for child in arguments {
                collect_variables(child, vars)?;
            }
        }
        _ => {}
    }
    Ok(())
}

fn internal_sort(sort: &Sort) -> Option<InternalSort> {
    match sort {
        Sort::Application { name, arguments } if arguments.is_empty() => {
            Some(InternalSort::simple(name.as_str()))
        }
        _ => None,
    }
}

fn validate_pattern(
    definition: &BackendDefinition,
    pattern: &Pattern,
) -> Result<(), StepObservationError> {
    validate_node(definition, pattern, None)?;
    let term = definition
        .admit_unverified(pattern, &[])
        .internalize_term()
        .map_err(|error| StepObservationError::Internalization(error.to_string()))?;
    if term.sort() != InternalSort::simple("SortGeneratedTopCell") {
        return Err(StepObservationError::Internalization(
            "configuration sort".into(),
        ));
    }
    Ok(())
}

fn validate_node(
    definition: &BackendDefinition,
    pattern: &Pattern,
    expected: Option<&InternalSort>,
) -> Result<(), StepObservationError> {
    match pattern {
        Pattern::Variable(var) => {
            if var.kind != VariableKind::Element {
                return Err(StepObservationError::UnsupportedPattern(var.name.clone()));
            }
            if var.name.contains('!') {
                return Err(StepObservationError::ReservedVariable(var.name.clone()));
            }
            if expected.is_some_and(|sort| internal_sort(&var.sort).as_ref() != Some(sort)) {
                return Err(StepObservationError::VariableSort(var.name.clone()));
            }
        }
        Pattern::DomainValue { sort, value } => {
            if !domain_value_identity_safe(definition, sort, value.as_bytes()) {
                return Err(StepObservationError::NonCanonicalValue(format!(
                    "{value:?}"
                )));
            }
            if expected.is_some_and(|expected| internal_sort(sort).as_ref() != Some(expected)) {
                return Err(StepObservationError::VariableSort("domain value".into()));
            }
        }
        Pattern::Application { symbol, arguments } if symbol.name == "inj" => {
            let [source, target] = symbol.sort_parameters.as_slice() else {
                return Err(StepObservationError::Internalization(
                    "injection sorts".into(),
                ));
            };
            if arguments.len() != 1 {
                return Err(StepObservationError::Internalization(
                    "injection arity".into(),
                ));
            }
            if !strict_injection_sorts(definition, source, target) {
                return Err(StepObservationError::VariableSort(
                    "injection must have a strict subsort source".into(),
                ));
            }
            if expected.is_some_and(|sort| internal_sort(target).as_ref() != Some(sort)) {
                return Err(StepObservationError::VariableSort(
                    "injection target".into(),
                ));
            }
            let source = internal_sort(source)
                .ok_or_else(|| StepObservationError::Internalization("injection source".into()))?;
            validate_node(definition, &arguments[0], Some(&source))?;
        }
        Pattern::Application { symbol, arguments } => {
            let backend_symbol = definition
                .symbols()
                .get(symbol.name.as_str())
                .ok_or_else(|| StepObservationError::Internalization(symbol.name.clone()))?;
            if !free_constructor(backend_symbol) {
                return Err(StepObservationError::NonFreeSymbol(symbol.name.clone()));
            }
            if expected.is_some_and(|sort| backend_symbol.result_sort != *sort) {
                return Err(StepObservationError::VariableSort(symbol.name.clone()));
            }
            if arguments.len() != backend_symbol.argument_sorts.len() {
                return Err(StepObservationError::Internalization(symbol.name.clone()));
            }
            for (arg, sort) in arguments.iter().zip(&backend_symbol.argument_sorts) {
                validate_node(definition, arg, Some(sort))?;
            }
        }
        _ => {
            return Err(StepObservationError::UnsupportedPattern(format!(
                "{pattern:?}"
            )));
        }
    }
    Ok(())
}

fn is_injection(pattern: &Pattern) -> bool {
    matches!(pattern, Pattern::Application { symbol, .. } if symbol.name == "inj")
}

/// Whether `term` holds an application of a symbol that `definition` declares a collection
/// symbol (one with collection metadata).
fn holds_collection_symbol(definition: &BackendDefinition, term: &Pattern) -> bool {
    let mut found = false;
    k_rust::kore::walk::for_each_post_order(term, |node| {
        if let Pattern::Application { symbol, .. } = node {
            found |= definition
                .symbols()
                .get(symbol.name.as_str())
                .is_some_and(|s| s.attributes.collection.is_some());
        }
    });
    found
}

/// The sort of `pattern` when its syntax fixes it: a variable, a domain value, an injection's
/// target, or an application of a symbol without sort variables. `None` otherwise.
fn determined_sort(definition: &BackendDefinition, pattern: &Pattern) -> Option<InternalSort> {
    match pattern {
        Pattern::Variable(var) => internal_sort(&var.sort),
        Pattern::DomainValue { sort, .. } => internal_sort(sort),
        Pattern::Application { symbol, .. } if symbol.name == "inj" => {
            match symbol.sort_parameters.as_slice() {
                [_, target] => internal_sort(target),
                _ => None,
            }
        }
        Pattern::Application { symbol, .. } => definition
            .symbols()
            .get(symbol.name.as_str())
            .filter(|backend| {
                backend.sort_variables.is_empty() && symbol.sort_parameters.is_empty()
            })
            .map(|backend| backend.result_sort),
        _ => None,
    }
}

/// Whether `pattern` is a sort injection in k-rust's normal form (TV-01 fix 1, review R1-F1):
/// one argument, a proper subsort source (`strict_injection_sorts`), an argument whose sort is
/// determined and equal to the source, and an argument that is not itself an injection. k-rust
/// builds only such injections: `Term::injection` collapses a nested pair
/// (`term.rs:893-907`), `inject_to_sort` returns the bare term when the sorts are equal
/// (`matching/mod.rs:2342`, `builtin/substitution.rs:1172`). Internalization admits an identity
/// injection (`check_subsort` is reflexive) and does not sort-check an injection's argument
/// (`definition.rs:2474-2490`), so a test may write `inj{S,S}(t)`, which the matcher keeps
/// apart from `t` although `inj{S,S}(t) = t` in K's semantics. Such a term is neither a value
/// nor admissible test input.
pub(crate) fn canonical_injection(definition: &BackendDefinition, pattern: &Pattern) -> bool {
    let Pattern::Application { symbol, arguments } = pattern else {
        return false;
    };
    let ([source, target], [argument]) = (symbol.sort_parameters.as_slice(), arguments.as_slice())
    else {
        return false;
    };
    symbol.name == "inj"
        && strict_injection_sorts(definition, source, target)
        && !is_injection(argument)
        && internal_sort(source).is_some_and(|source| {
            determined_sort(definition, argument).is_some_and(|sort| sort == source)
        })
}

/// Which own test of [`ObservationDecider::terminal_value`] a node fails ([`NonValue`]): each is
/// a test of the node alone, its children ignored.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LocalTest {
    /// A node that is not a variable, a domain value or an application.
    TermKind,
    /// A domain value whose sort has no trusted injective codec for it.
    IdentitySafeDomainValue,
    /// A sort injection not in k-rust's normal form ([`canonical_injection`]).
    CanonicalInjection,
    /// An application of a symbol the definition does not declare.
    DeclaredSymbol,
    /// An application whose head is not a free constructor (nor, with the definition's data
    /// facts, a data head: an overload head or another `anywhere` head k-rust's `data_term`
    /// selects).
    FreeConstructor,
    /// The outermost application of a data head, which k-rust does not judge data.
    OverloadData,
    /// An application, or a collection's element application, with another number of
    /// arguments than its symbol declares.
    Arity,
    /// A collection term, while collection terms are not trusted
    /// ([`ObservationDecider::trusting_collections`]).
    TrustedCollections,
    /// A collection term that is not at its collection sort.
    CollectionSort,
    /// A collection term with a variable in it.
    Ground,
    /// A collection term with a component that is not a natural unit, element or concat
    /// application of its collection.
    NaturalCollection,
    /// A Map with two equal keys, or a Set with two equal elements (among the entries that
    /// have values).
    DistinctEntries,
}

impl LocalTest {
    /// The test the node fails, in the reader's words.
    #[must_use]
    pub const fn description(self) -> &'static str {
        match self {
            Self::TermKind => "it is not a variable, a domain value or an application",
            Self::IdentitySafeDomainValue => {
                "it is a domain value without a trusted injective codec (only canonical Int and \
                 Bool values, ASCII values of String and of sorts without a hook, and Bytes \
                 values have one)"
            }
            Self::CanonicalInjection => "it is a sort injection not in k-rust's normal form",
            Self::DeclaredSymbol => "its symbol is not declared by the definition",
            Self::FreeConstructor => {
                "its head is neither a free constructor (it is for example a function, a hooked \
                 or anywhere symbol, or a symbol with axioms) nor a data head"
            }
            Self::OverloadData => {
                "it is an application of a data head that k-rust does not judge data (an \
                 equation of its head may apply to it, or an argument is not data)"
            }
            Self::Arity => "it has another number of arguments than its symbol declares",
            Self::TrustedCollections => {
                "it is a collection term, and the definition has an axiom rooted at a collection \
                 symbol, so collection terms are not trusted"
            }
            Self::CollectionSort => "it is a collection term outside its collection sort",
            Self::Ground => "it is a collection term with a variable in it",
            Self::NaturalCollection => {
                "it is a collection term with a component that is not a natural unit, element or \
                 concatenation of its collection"
            }
            Self::DistinctEntries => {
                "it is a Map with two equal keys or a Set with two equal elements"
            }
        }
    }
}

/// The role of an entry's argument in a collection ([`NonValueStep::Entry`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EntryRole {
    Key,
    Value,
    Element,
}

/// One step from a node to one of its children ([`NonValue::path`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum NonValueStep {
    /// Argument `index` (from 0) of an application of `symbol`.
    Argument { symbol: String, index: usize },
    /// Argument `argument` (from 0, the key of a Map entry being 0) of entry `entry` (from 0, in
    /// the term's order) of a collection term of sort `collection`, read as a sequence of
    /// element applications.
    Entry {
        collection: String,
        entry: usize,
        role: EntryRole,
        argument: usize,
    },
}

/// Why a term has no terminal value ([`ObservationDecider::first_non_value`]): the first node,
/// in pre-order, whose own test fails with its children ignored, where it is, and which test.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NonValue {
    /// The steps from the term's root to the node, outermost first.
    pub path: Vec<NonValueStep>,
    /// The node.
    pub node: Pattern,
    /// The test the node fails.
    pub test: LocalTest,
    /// When the node is an overload application k-rust does not judge data
    /// ([`LocalTest::OverloadData`]): the first node inside it, in pre-order, that fails its own
    /// test when its arguments are walked as terms of their own, without the application's
    /// judgement, its path from the application. A hint at what keeps the application from being
    /// data, not k-rust's reason.
    pub inside: Option<Box<NonValue>>,
}

impl NonValue {
    fn at(node: &Pattern, test: LocalTest) -> Box<Self> {
        Box::new(Self {
            path: Vec::new(),
            node: node.clone(),
            test,
            inside: None,
        })
    }

    /// This failure seen from the parent, `step` above it (the walk builds the path innermost
    /// first, and only on a failure).
    fn below(mut self: Box<Self>, step: NonValueStep) -> Box<Self> {
        self.path.push(step);
        self
    }

    fn below_argument(self: Box<Self>, symbol: &str, index: usize) -> Box<Self> {
        self.below(NonValueStep::Argument {
            symbol: symbol.to_owned(),
            index,
        })
    }
}

/// What [`ObservationDecider::value_at`] does next.
enum ValueVisit<'t> {
    /// Compute the value of a node at a sort, with the `judged` flag of
    /// [`ObservationDecider::independent`].
    Enter(&'t Pattern, Option<InternalSort>, bool),
    /// The value of the node visited last, or its failure.
    Done(Result<Pattern, Box<NonValue>>),
    /// Visit the next child of the innermost frame, or finish it.
    Continue,
}

/// A node holding a collection symbol whose value [`ObservationDecider::value_at`] computes from
/// the values of its children, visited in order.
enum ValueFrame<'t> {
    /// A canonical injection or an application of a declared symbol: its arguments' values at
    /// `sorts`, the first failure ending it.
    Arguments {
        symbol: &'t k_rust::kore::ast::Symbol,
        arguments: &'t [Pattern],
        sorts: Vec<InternalSort>,
        judged: bool,
        /// Whether the node lies inside a collection term whose own tests passed, and so is
        /// ground ([`ValueFrame::ground`]).
        ground: bool,
        values: Vec<Pattern>,
        failure: Option<Box<NonValue>>,
    },
    /// A collection term whose own tests passed.
    Entries(Box<EntriesFrame<'t>>),
}

/// The collection kind of an [`EntriesFrame`].
#[derive(Clone, Copy)]
enum CollectionRole {
    Map,
    Set,
    List,
}

/// A collection term whose own tests passed: the arguments of its element applications, in the
/// term's order, and the value or failure of each argument visited so far. Every argument is
/// visited, a failing one included, since distinct Map keys and Set elements are checked among
/// the entries that have values before the first failing entry is reported.
struct EntriesFrame<'t> {
    term: &'t Pattern,
    role: CollectionRole,
    collection: String,
    unit: String,
    element: String,
    concat: String,
    items: Vec<&'t [Pattern]>,
    sorts: Vec<InternalSort>,
    judged: bool,
    results: Vec<Vec<Result<Pattern, Box<NonValue>>>>,
}

impl<'t> ValueFrame<'t> {
    /// Whether the frame's children are known to be ground: they lie inside a collection term
    /// whose own tests passed, and one of those tests is that the collection is ground, so every
    /// subterm of it is.
    const fn ground(&self) -> bool {
        match self {
            Self::Arguments { ground, .. } => *ground,
            Self::Entries(_) => true,
        }
    }

    /// Record the value or failure of the child visited last.
    fn accept(&mut self, result: Result<Pattern, Box<NonValue>>) {
        match self {
            Self::Arguments {
                symbol,
                values,
                failure,
                ..
            } => match result {
                Ok(value) => values.push(value),
                Err(below) => *failure = Some(below.below_argument(&symbol.name, values.len())),
            },
            Self::Entries(frame) => frame
                .results
                .last_mut()
                .expect("an entry argument was visited")
                .push(result),
        }
    }

    /// The next child to visit, with its sort and `judged` flag, or `None` when the frame is
    /// complete.
    fn next_child(&mut self) -> Option<(&'t Pattern, InternalSort, bool)> {
        match self {
            Self::Arguments {
                arguments,
                sorts,
                judged,
                values,
                failure,
                ..
            } => {
                if failure.is_some() {
                    return None;
                }
                let index = values.len();
                arguments
                    .get(index)
                    .map(|argument| (argument, sorts[index], *judged))
            }
            Self::Entries(frame) => loop {
                if let Some(row) = frame.results.last() {
                    let entry = frame.results.len() - 1;
                    let argument = row.len();
                    if let Some(child) = frame.items[entry].get(argument) {
                        return Some((child, frame.sorts[argument], frame.judged));
                    }
                }
                if frame.results.len() == frame.items.len() {
                    return None;
                }
                let arity = frame.items[frame.results.len()].len();
                frame.results.push(Vec::with_capacity(arity));
            },
        }
    }

    /// The value of the frame's node, from its children's.
    fn finish(self) -> Result<Pattern, Box<NonValue>> {
        match self {
            Self::Arguments {
                symbol,
                values,
                failure,
                ..
            } => match failure {
                Some(failure) => Err(failure),
                None => Ok(Pattern::Application {
                    symbol: symbol.clone(),
                    arguments: values,
                }),
            },
            Self::Entries(frame) => frame.finish(),
        }
    }
}

impl EntriesFrame<'_> {
    /// The collection's value once every entry argument has its value or failure: distinct
    /// Map keys or Set elements among the entries that have values, then the first entry
    /// argument without a value, in the term's order, then the collection rebuilt as k-rust
    /// externalizes collections, a right-nested concat of element applications (unit when
    /// empty), Map entries sorted by key and Set elements sorted.
    fn finish(self) -> Result<Pattern, Box<NonValue>> {
        let mut compared = match self.role {
            CollectionRole::Map => self
                .results
                .iter()
                .filter_map(|entry| Some(vec![entry.first()?.as_ref().ok()?]))
                .collect::<Vec<_>>(),
            CollectionRole::Set => self
                .results
                .iter()
                .filter_map(|entry| entry.iter().map(|value| value.as_ref().ok()).collect())
                .collect::<Vec<_>>(),
            CollectionRole::List => Vec::new(),
        };
        compared.sort();
        if compared.windows(2).any(|pair| pair[0] == pair[1]) {
            return Err(NonValue::at(self.term, LocalTest::DistinctEntries));
        }
        drop(compared);
        let mut values = Vec::with_capacity(self.results.len());
        for (entry, arguments) in self.results.into_iter().enumerate() {
            let mut row = Vec::with_capacity(arguments.len());
            for (argument, value) in arguments.into_iter().enumerate() {
                row.push(value.map_err(|failure| {
                    failure.below(NonValueStep::Entry {
                        collection: self.collection.clone(),
                        entry,
                        role: match (self.role, argument) {
                            (CollectionRole::Map, 0) => EntryRole::Key,
                            (CollectionRole::Map, _) => EntryRole::Value,
                            _ => EntryRole::Element,
                        },
                        argument,
                    })
                })?);
            }
            values.push(row);
        }
        match self.role {
            // Keys (Set elements) are distinct, checked above.
            CollectionRole::Map => values.sort_by(|left, right| left[0].cmp(&right[0])),
            CollectionRole::Set => values.sort(),
            CollectionRole::List => {}
        }
        let application = |name: &str, arguments| Pattern::Application {
            symbol: k_rust::kore::ast::Symbol {
                name: name.to_owned(),
                sort_parameters: Vec::new(),
            },
            arguments,
        };
        let mut elements = values
            .into_iter()
            .map(|arguments| application(&self.element, arguments))
            .collect::<Vec<_>>();
        let Some(mut result) = elements.pop() else {
            return Ok(application(&self.unit, Vec::new()));
        };
        // Invariant: `result` is the right-nested concat of the elements popped so far.
        while let Some(element) = elements.pop() {
            result = application(&self.concat, vec![element, result]);
        }
        Ok(result)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StepPresence {
    Certain(Vec<Pattern>),
    Conditional(Vec<Pattern>, Vec<TermRelation>),
    Absent,
    Undecided,
}

/// Decides what one side's leaves and steps show, with two definitions in two roles.
///
/// The shared definition (the baseline's, for both sides of a mutant pair) decides everything
/// that must mean the same on both sides: definition independence and terminal values
/// ([`Self::definition_independent`], [`Self::terminal_value`]) and the structural walk of event
/// classification. The leaf definition, the one whose run produced the leaves, decides every
/// feasibility and relation query about them: leaf feasibility and the relation and feasibility
/// queries of event classification (re-pin finding A-12). Since 501f18b9, k-rust's admission
/// restates the definedness of the admitted pattern from the admitting definition, so a mutant
/// leaf admitted under the baseline would carry the baseline's definedness conditions: a mutant
/// that makes a partial symbol defined could have a leaf refuted or a relation decided by the
/// baseline's definedness. Deciding them on the leaf's own definition adds no premise.
pub struct ObservationDecider<'a> {
    definition: &'a BackendDefinition,
    leaf_definition: &'a BackendDefinition,
    leaf_solver: &'a dyn SmtSolver,
    leaf_inhabitation: Inhabitation,
    relations: BackendRelations<'a>,
    /// Whether a collection term can be a terminal value (re-pin finding C-10).
    collections_trusted: bool,
    /// Which ends are data under the shared definition, from its own facts
    /// ([`crate::data::data_ends`]): the data heads whose applications the walk admits
    /// where k-rust's data judgement holds (KINK-OVERLOAD-VALUE). [`DataEnds::None`] (the default)
    /// admits no data-head application; it does not refuse the rest of TV-01, since refusing every
    /// kill on a definition with a finding is the runner's gate (KINK-BASELINE-FINDINGS).
    data: DataEnds<'a>,
    /// The same for the leaf definition when it is another definition than the shared one: an
    /// overload application in a leaf is admitted only where it is data under both.
    leaf_data: DataEnds<'a>,
}

impl<'a> ObservationDecider<'a> {
    /// A decider for the leaves of a run on `definition` itself (a baseline run, or any side
    /// judged on its own definition).
    pub fn new(
        definition: &'a BackendDefinition,
        solver: &'a dyn SmtSolver,
        initial_state: TestInitialState<'_>,
    ) -> Self {
        Self::for_leaves_of(definition, definition, solver, initial_state)
    }

    /// A decider whose shared definition is `definition` (the baseline's) for the leaves of a run
    /// on `leaf_definition` (the mutant's), whose `leaf_solver` decides their queries.
    pub fn for_leaves_of(
        definition: &'a BackendDefinition,
        leaf_definition: &'a BackendDefinition,
        leaf_solver: &'a dyn SmtSolver,
        initial_state: TestInitialState<'_>,
    ) -> Self {
        Self {
            definition,
            leaf_definition,
            leaf_solver,
            leaf_inhabitation: Inhabitation::of(leaf_definition),
            relations: BackendRelations::shared(leaf_definition, leaf_solver, initial_state),
            collections_trusted: true,
            data: DataEnds::None,
            leaf_data: DataEnds::None,
        }
    }

    /// `work`'s result, or the first refusal by the host to map a stack that one of this
    /// decider's judgements needed while `work` ran.
    ///
    /// A judgement over a leaf, or over a subterm of it, runs on the stack k-rust sizes for an
    /// operation over that term ([`crate::feasibility::on_stack_for`]). When the term is too deep
    /// for the largest stack k-rust provides, the judgement is its one-sided answer (unknown
    /// feasibility, not shown to exist, not data), a function of the term. When the host refuses
    /// to map the stack (an address-space limit such as `ulimit -v`), the judgement answers the
    /// same way, so that its caller goes on as before, and the refusal is recorded here instead,
    /// since it is a fact about the host and must not become an answer about the term: a caller
    /// that turns the judgements into a run's evidence runs them in `work` and reports a refusal
    /// as a failure of the run that names the host. The decisions of [`Self::relations`] are
    /// among these judgements.
    pub fn host_refusal_during<R>(&self, work: impl FnOnce() -> R) -> Result<R, SegmentRefused> {
        self.relations.host_refusal_during(work)
    }

    /// `work` on the stack k-rust gives an operation over `patterns` on `definition`, or
    /// `refused` when that stack is not provided, the host's refusal recorded
    /// ([`Self::host_refusal_during`]).
    fn on_stack_for<R>(
        &self,
        definition: &BackendDefinition,
        patterns: &[&Pattern],
        work: impl FnOnce() -> R,
        refused: R,
    ) -> R {
        self.relations
            .on_stack_for(definition, patterns, work, refused)
    }

    /// Records `host` unless a refusal is already recorded ([`Self::host_refusal_during`]).
    fn record_host_refusal(&self, host: SegmentRefused) {
        self.relations.record_host_refusal(host);
    }

    /// This decider, admitting in terms the instance-normal applications of the overload data
    /// heads that `shared` (the shared definition's [`crate::data::data_ends`]) gives, where
    /// k-rust's data judgement holds on the outermost one ([`DataEnds::overload_application_is_data`]),
    /// and, for leaves of another definition, under `leaf` (the leaf definition's) as well
    /// (KINK-OVERLOAD-VALUE). Every other head must still be a free constructor of the shared
    /// definition.
    #[must_use]
    pub const fn judging_data(mut self, shared: DataEnds<'a>, leaf: DataEnds<'a>) -> Self {
        self.data = shared;
        self.leaf_data = leaf;
        self
    }

    /// This decider, with no collection term a terminal value unless `trusted`: false when the
    /// definition that produced the leaves (or the shared one) has an axiom rooted at a
    /// collection role symbol ([`crate::exclusion::DefinitionExclusions::collections_trusted`]),
    /// whose collection terms then need not denote what their structure shows (KINK-05).
    #[must_use]
    pub const fn trusting_collections(mut self, trusted: bool) -> Self {
        self.collections_trusted = self.collections_trusted && trusted;
        self
    }

    /// The relation decider of this decider's leaves (the leaf definition's), for pattern slots.
    #[must_use]
    pub const fn relations(&self) -> &BackendRelations<'a> {
        &self.relations
    }
    /// Whether `term` is a value that no definition can change: variables, domain values with a
    /// trusted injective codec, free constructors, and sort injections in k-rust's normal form
    /// ([`canonical_injection`]). Anything else, including an identity or nested injection, is
    /// not (TV-01 and its fix 1, review R1-F1). With [`Self::judging_data`], also a ground
    /// application of a data head that is data ([`Self::overload_data`]).
    pub fn definition_independent(&self, term: &Pattern) -> bool {
        self.independent(term, false).is_ok()
    }

    /// [`Self::definition_independent`] of `term`, or the first node, in pre-order, that fails
    /// its own test ([`Self::node_test`]); `judged` when an enclosing data-head application was
    /// already judged data as a whole, so a nested one needs no judgement of its own.
    ///
    /// A leaf is as deep as the run made it, so the walk keeps the applications it is inside on a
    /// work list instead of the native stack.
    fn independent(&self, term: &Pattern, judged: bool) -> Result<(), Box<NonValue>> {
        // The applications whose own test passed and whose arguments are being walked: each with
        // the `judged` flag of its arguments and the index of the argument walked next.
        let mut open: Vec<(&k_rust::kore::ast::Symbol, &[Pattern], bool, usize)> = Vec::new();
        let mut next = Some((term, judged));
        // Invariant: every node before `next` in pre-order passed its own test, and `open` holds
        // the applications on the path from `term` to `next`, outermost first; each node is
        // tested once, so the loop ends after visiting every node or at the first failure.
        loop {
            if let Some((node, judged)) = next.take() {
                match self.node_test(node, judged) {
                    Err(failure) => {
                        return Err(open.iter().rev().fold(
                            failure,
                            |failure, (symbol, _, _, following)| {
                                failure.below_argument(&symbol.name, following - 1)
                            },
                        ));
                    }
                    Ok(judged) => {
                        if let Pattern::Application { symbol, arguments } = node {
                            open.push((symbol, arguments, judged, 0));
                        }
                    }
                }
            }
            let Some((_, arguments, judged, following)) = open.last_mut() else {
                return Ok(());
            };
            if let Some(argument) = arguments.get(*following) {
                *following += 1;
                next = Some((argument, *judged));
            } else {
                open.pop();
            }
        }
    }

    /// The own test of one node that is not a collection term, its children ignored, shared by
    /// [`Self::definition_independent`] and [`Self::terminal_value`]: a variable passes; a domain
    /// value passes when its codec is trusted and injective (`domain_value_identity_safe`); an
    /// injection when it is in k-rust's normal form ([`canonical_injection`]); an application when
    /// its head is a free constructor of the shared definition, or, with [`Self::judging_data`],
    /// a data head whose outermost application is data ([`Self::overload_data`]);
    /// nothing else passes. On a pass, the `judged` flag of its arguments.
    fn node_test(&self, term: &Pattern, judged: bool) -> Result<bool, Box<NonValue>> {
        let fails = |test| Err(NonValue::at(term, test));
        match term {
            Pattern::Variable(_) => Ok(judged),
            Pattern::DomainValue { sort, value } => {
                if domain_value_identity_safe(self.definition, sort, value.as_bytes()) {
                    Ok(judged)
                } else {
                    fails(LocalTest::IdentitySafeDomainValue)
                }
            }
            Pattern::Application { .. } if is_injection(term) => {
                if canonical_injection(self.definition, term) {
                    Ok(judged)
                } else {
                    fails(LocalTest::CanonicalInjection)
                }
            }
            Pattern::Application { symbol, .. } => {
                let Some(head) = self.definition.symbols().get(symbol.name.as_str()) else {
                    return fails(LocalTest::DeclaredSymbol);
                };
                if free_constructor(head) {
                    Ok(judged)
                } else if self.data.overload_head(&symbol.name) {
                    if judged || self.overload_data(term) {
                        Ok(true)
                    } else {
                        fails(LocalTest::OverloadData)
                    }
                } else {
                    fails(LocalTest::FreeConstructor)
                }
            }
            _ => fails(LocalTest::TermKind),
        }
    }

    /// Whether `application`, an application of a data head of the shared definition
    /// that no enclosing one covers, is data: under the shared definition with its facts, and,
    /// for leaves of another definition, under the leaf definition with its facts too
    /// ([`DataEnds::overload_application_is_data`], k-rust's `is_data`, once for the whole
    /// subterm; review N4). Its arguments are walked for the rest of TV-01 by the caller.
    ///
    /// The application may be as deep as the leaf it is in, so each judgement, which internalizes
    /// it and walks the internal term, runs on the stack k-rust gives an operation over it
    /// ([`Self::on_stack_for`]); without that stack the application is not data, which refuses
    /// closed.
    fn overload_data(&self, application: &Pattern) -> bool {
        let data = |definition: &BackendDefinition, ends: &DataEnds<'_>| {
            self.on_stack_for(
                definition,
                &[application],
                || ends.overload_application_is_data(definition, application),
                false,
            )
        };
        data(self.definition, &self.data)
            && (std::ptr::eq(self.definition, self.leaf_definition)
                || data(self.leaf_definition, &self.leaf_data))
    }
    /// The canonical value of a terminal term, or `None` when it is not
    /// definition-independent. A term without collection symbols is itself exactly when
    /// [`Self::definition_independent`] holds. A collection is admitted when every collection
    /// symbol in it is a natural role of one metadata (census rules C and C-H), it occurs at its
    /// metadata's collection sort, it is ground, every key, value and element is a value at the
    /// element symbol's argument sort, and its Map keys or Set elements are distinct; it is
    /// rebuilt as k-rust externalizes collections, a right-nested concat of element
    /// applications (unit when empty), Map entries sorted by key and Set elements sorted.
    /// With [`Self::trusting_collections`] off, no term with a collection symbol has a value.
    pub fn terminal_value(&self, term: &Pattern) -> Option<Pattern> {
        self.value_at(term, None, false).ok()
    }

    /// Whether k-rust shows that the configuration `term` exists (has an instance) on the leaf
    /// definition: `term` is ground, holds no conjunction, kink reads it back as k-rust's term,
    /// and k-rust's `ground_defined` holds of its internalization. One-sided: `true` says the
    /// configuration exists, `false` says nothing. This is the existence an undefined step's
    /// pre-step configuration needs for its path to be real (kink27 R3-UNDEF-BRIDGE); it is a
    /// fact of the theory whose step is undefined, so it is asked of the leaf's own definition.
    ///
    /// The guards:
    /// - a free variable: the existence of every instance is not one ground fact;
    /// - a conjunction `\and(a, b)` anywhere exists only where its sides are equal, which
    ///   `ground_defined` does not decide;
    /// - a domain value without an injective codec, or an injection that is not strict: the
    ///   read-back term may not be the term k-rust built, so k-rust's answer may be about
    ///   another term;
    /// - a collection symbol (of the leaf or the shared definition) while collections are not
    ///   trusted ([`Self::trusting_collections`], finding C-10): `ground_defined`'s collection
    ///   obligations (distinct Map keys and Set elements) read k-rust's builtin collection model,
    ///   and a definition with an axiom rooted at a collection role symbol states facts of its
    ///   collection terms that this model does not read, so a collection term there need not
    ///   denote what its structure shows, and k-rust's answer may not be about the term's
    ///   meaning in the theory. Whether such an axiom can make a keys-apart map undefined is not
    ///   decided here; the guard fails closed, as [`Self::terminal_value`] does.
    ///
    /// `ground_defined` counts an irreducible hooked `value-production` application as existing
    /// whether or not its hook ran; every run whose k-rust lists hold an unsupported hook or an
    /// allowance refusal is excluded before a side is formed (`run_exclusion`), so no verdict
    /// rests on that answer. It runs in proof mode, so it never reads an implementation-chosen
    /// value.
    ///
    /// The term is internalized, and `ground_defined` walks it, on the stack k-rust gives an
    /// operation over the term ([`Self::on_stack_for`]), since a leaf is as deep as the run made
    /// it; a term without that stack is not shown to exist (a host's refusal of it recorded,
    /// [`Self::host_refusal_during`]). No panic is caught, unlike kink-flow's `defined_state`: the adapter's feasibility
    /// (`leaf_feasibility`) already admitted the same leaf state on the same definition, so this
    /// adds no verification hazard of its own.
    pub fn configuration_exists(&self, term: &Pattern) -> bool {
        let definition = self.leaf_definition;
        if !term.free_variables().is_empty() {
            return false;
        }
        if !self.collections_trusted
            && (holds_collection_symbol(definition, term)
                || holds_collection_symbol(self.definition, term))
        {
            return false;
        }
        let mut conjunction = false;
        k_rust::kore::walk::for_each_post_order(term, |node| {
            conjunction |= matches!(node, Pattern::And { .. });
        });
        !conjunction
            && !contains_untrusted_domain_value(definition, term)
            && !contains_non_strict_injection(definition, term)
            && self.on_stack_for(
                definition,
                &[term],
                || {
                    definition
                        .admit_unverified(term, &[])
                        .internalize_term()
                        .is_ok_and(|internal| definition.ground_defined(&internal))
                },
                false,
            )
    }

    /// Why `term` has no [`Self::terminal_value`]: the first node, in pre-order, that fails its
    /// own test with its children ignored ([`NonValue`]), or `None` when `term` has a terminal
    /// value. Naming the first subterm without a terminal value would always name the root,
    /// since a term has none whenever a subterm has none. The tests are exactly those
    /// [`Self::terminal_value`] applies, from the same walk: a node not a collection term passes
    /// [`Self::node_test`] and, below a collection, has its symbol's arity; a collection node is
    /// trusted ([`Self::trusting_collections`]), at its collection sort, ground, built of natural
    /// unit, element and concat applications of its metadata with the element symbol's arity,
    /// and has distinct Map keys or Set elements among the entries that have values.
    ///
    /// This is the shared definition's judgement of one term (P7-SIMPLE-IN, KINK-CAUSE-SUBTERM):
    /// it cannot name why an end of one side of a pair is not data under the other side's
    /// definition, which the campaign runner judges for each pair (`judge_across`).
    pub fn first_non_value(&self, term: &Pattern) -> Option<NonValue> {
        self.value_at(term, None, false).err().map(|failure| {
            let mut failure = *failure;
            failure.path.reverse();
            if failure.test == LocalTest::OverloadData {
                failure.inside = self.inside_overload(&failure.node);
            }
            failure
        })
    }

    /// Why `term` is not [`Self::definition_independent`]: the first node, in pre-order, that
    /// fails [`Self::node_test`] with its children ignored (a collection symbol fails it, as a
    /// head that is not a free constructor), or `None` when `term` is definition-independent.
    /// The walk is the one [`Self::definition_independent`] takes.
    pub fn first_dependent(&self, term: &Pattern) -> Option<NonValue> {
        self.independent(term, false).err().map(|failure| {
            let mut failure = *failure;
            failure.path.reverse();
            if failure.test == LocalTest::OverloadData {
                failure.inside = self.inside_overload(&failure.node);
            }
            failure
        })
    }

    /// [`NonValue::inside`] of an overload application: the first of its arguments, at its
    /// symbol's argument sorts, without a value of its own, and the first node of that argument
    /// that fails its own test.
    fn inside_overload(&self, application: &Pattern) -> Option<Box<NonValue>> {
        let Pattern::Application { symbol, arguments } = application else {
            return None;
        };
        let head = self.definition.symbols().get(symbol.name.as_str())?;
        let mut failure = arguments
            .iter()
            .zip(&head.argument_sorts)
            .enumerate()
            .find_map(|(index, (argument, sort))| {
                self.value_at(argument, Some(sort), false)
                    .err()
                    .map(|failure| failure.below_argument(&symbol.name, index))
            })?;
        failure.path.reverse();
        Some(failure)
    }

    /// Whether `term` holds an application of a collection symbol of the shared definition,
    /// remembered in `holders` for every subterm found to hold one.
    ///
    /// The walk does not enter a collection application, which holds one, and records only the
    /// subterms that hold one, so a subterm that holds none may be walked again: [`Self::value_at`]
    /// asks once for each subterm it reaches and descends only into a subterm that holds one, so
    /// a subterm holding none is walked here at most twice, and every subterm holding one is
    /// walked once, whatever the depth of the term.
    fn holds_collection(
        &self,
        term: &Pattern,
        holders: &mut std::collections::HashSet<*const Pattern>,
    ) -> bool {
        enum Visit<'t> {
            Enter(&'t Pattern),
            Exit(&'t Pattern, usize),
        }
        if holders.contains(&std::ptr::from_ref(term)) {
            return true;
        }
        let collection = |node: &Pattern| {
            matches!(node, Pattern::Application { symbol, .. }
                if self
                    .definition
                    .symbols()
                    .get(symbol.name.as_str())
                    .is_some_and(|head| head.attributes.collection.is_some()))
        };
        // Invariant: after the `Exit` of a node, `found` ends with whether it holds a collection
        // symbol, in place of its children's entries; each node is entered and left once.
        let mut found: Vec<bool> = Vec::new();
        let mut pending = vec![Visit::Enter(term)];
        while let Some(visit) = pending.pop() {
            match visit {
                Visit::Enter(node) => {
                    if holders.contains(&std::ptr::from_ref(node)) || collection(node) {
                        holders.insert(std::ptr::from_ref(node));
                        found.push(true);
                        continue;
                    }
                    let children = k_rust::kore::walk::children(node);
                    pending.push(Visit::Exit(node, children.len()));
                    pending.extend(children.into_iter().rev().map(Visit::Enter));
                }
                Visit::Exit(node, count) => {
                    let start = found.len() - count;
                    let holds = found[start..].iter().any(|holds| *holds);
                    found.truncate(start);
                    if holds {
                        holders.insert(std::ptr::from_ref(node));
                    }
                    found.push(holds);
                }
            }
        }
        found.pop().unwrap_or(false)
    }

    /// The value of `term` at the sort `expected`, or the first node, in pre-order, that fails
    /// its own test (its path innermost first); `judged` as in [`Self::independent`].
    ///
    /// A subterm without a collection symbol is its own value when it is
    /// [`Self::definition_independent`]. A collection term's value is computed by
    /// [`Self::enter_collection`] and [`ValueFrame::finish`]; any other node holding a collection
    /// symbol passes [`Self::node_test`], is a canonical injection or an application of a declared
    /// symbol with its arity, and its value is the node over its arguments' values at its
    /// argument sorts, the first failing argument failing it.
    ///
    /// A leaf is as deep as the run made it (a list one level deeper per step that appends to
    /// it), so the walk keeps the nodes whose children it is computing on a work list
    /// ([`ValueFrame`]) instead of the native stack.
    fn value_at(
        &self,
        term: &Pattern,
        expected: Option<&InternalSort>,
        judged: bool,
    ) -> Result<Pattern, Box<NonValue>> {
        let mut holders = std::collections::HashSet::new();
        let mut frames: Vec<ValueFrame<'_>> = Vec::new();
        let mut visit = ValueVisit::Enter(term, expected.copied(), judged);
        // Invariant: `frames` holds the nodes on the path from `term` to the node being visited,
        // outermost first, each with the values (or failures) of its children visited so far; a
        // `Done` result is that of the child its innermost frame visited last. Each node is
        // entered once and each frame is finished once, so the loop ends.
        loop {
            visit = match visit {
                ValueVisit::Enter(node, expected, judged) => {
                    self.enter_value(node, expected, judged, &mut frames, &mut holders)
                }
                ValueVisit::Done(result) => match frames.last_mut() {
                    None => return result,
                    Some(frame) => {
                        frame.accept(result);
                        ValueVisit::Continue
                    }
                },
                ValueVisit::Continue => {
                    let frame = frames.last_mut().expect("a frame continues");
                    match frame.next_child() {
                        Some((child, expected, judged)) => {
                            ValueVisit::Enter(child, Some(expected), judged)
                        }
                        None => {
                            let frame = frames.pop().expect("the frame is on the work list");
                            ValueVisit::Done(frame.finish())
                        }
                    }
                }
            };
        }
    }

    /// The first step of [`Self::value_at`] at `term`: its value or failure when it needs no
    /// value of a child, or a frame for its children pushed onto `frames`.
    fn enter_value<'t>(
        &self,
        term: &'t Pattern,
        expected: Option<InternalSort>,
        judged: bool,
        frames: &mut Vec<ValueFrame<'t>>,
        holders: &mut std::collections::HashSet<*const Pattern>,
    ) -> ValueVisit<'t> {
        if !self.holds_collection(term, holders) {
            return ValueVisit::Done(self.independent(term, judged).map(|()| term.clone()));
        }
        let ground = frames.last().is_some_and(ValueFrame::ground);
        if let Pattern::Application { symbol, .. } = term
            && !is_injection(term)
            && self
                .definition
                .symbols()
                .get(symbol.name.as_str())
                .is_some_and(|head| head.attributes.collection.is_some())
        {
            return match self.enter_collection(term, expected.as_ref(), judged, ground) {
                Ok(frame) => {
                    frames.push(ValueFrame::Entries(Box::new(frame)));
                    ValueVisit::Continue
                }
                Err(failure) => ValueVisit::Done(Err(failure)),
            };
        }
        let fails = |test| ValueVisit::Done(Err(NonValue::at(term, test)));
        let judged = match self.node_test(term, judged) {
            Ok(judged) => judged,
            Err(failure) => return ValueVisit::Done(Err(failure)),
        };
        let Pattern::Application { symbol, arguments } = term else {
            // A variable or a domain value holds no collection symbol.
            return fails(LocalTest::TermKind);
        };
        let sorts = if is_injection(term) {
            // A canonical injection has one argument and a source sort.
            let (Some(source), [_]) = (
                symbol.sort_parameters.first().and_then(internal_sort),
                arguments.as_slice(),
            ) else {
                return fails(LocalTest::CanonicalInjection);
            };
            vec![source]
        } else {
            let Some(backend) = self.definition.symbols().get(symbol.name.as_str()) else {
                return fails(LocalTest::DeclaredSymbol);
            };
            if arguments.len() != backend.argument_sorts.len() {
                return fails(LocalTest::Arity);
            }
            backend.argument_sorts.clone()
        };
        frames.push(ValueFrame::Arguments {
            symbol,
            arguments,
            sorts,
            judged,
            ground,
            values: Vec::with_capacity(arguments.len()),
            failure: None,
        });
        ValueVisit::Continue
    }

    /// The own tests of a collection term at `expected`, in order: trusted, at its collection
    /// sort, ground, built of natural unit, element and concat applications of its metadata, and
    /// of elements with the element symbol's arity; on a pass, the frame that computes the values
    /// of its entries, in the term's order, each key before its value, and then
    /// ([`ValueFrame::finish`]) checks that its Map keys or Set elements are distinct among the
    /// entries whose keys or elements have values, fails at its first entry argument without a
    /// value, and rebuilds it as k-rust externalizes collections.
    ///
    /// `ground` when the term lies inside a collection whose own tests passed, so that it is known
    /// to be ground: its variables are not looked for again, which would take time quadratic in
    /// the depth of collections nested in each other.
    fn enter_collection<'t>(
        &self,
        term: &'t Pattern,
        expected: Option<&InternalSort>,
        judged: bool,
        ground: bool,
    ) -> Result<EntriesFrame<'t>, Box<NonValue>> {
        use k_rust_backend::term::CollectionMetadata;
        let fails = |test| Err(NonValue::at(term, test));
        if !self.collections_trusted {
            return fails(LocalTest::TrustedCollections);
        }
        let Pattern::Application { symbol, .. } = term else {
            return fails(LocalTest::TermKind);
        };
        let Some(metadata) = self
            .definition
            .symbols()
            .get(symbol.name.as_str())
            .and_then(|head| head.attributes.collection.clone())
        else {
            return fails(LocalTest::DeclaredSymbol);
        };
        let (collection_sort, symbols) = match &metadata {
            CollectionMetadata::Map(d) => (d.map_sort.clone(), d.symbols.clone()),
            CollectionMetadata::List(d) | CollectionMetadata::Set(d) => {
                (d.list_sort.clone(), d.symbols.clone())
            }
        };
        if expected != Some(&InternalSort::simple(collection_sort.clone())) {
            return fails(LocalTest::CollectionSort);
        }
        if !ground && !term.free_variables().is_empty() {
            return fails(LocalTest::Ground);
        }
        let Some(items) = self.collection_entries(term, &metadata) else {
            return fails(LocalTest::NaturalCollection);
        };
        let Some(element) = self.definition.symbols().get(&*symbols.element) else {
            return fails(LocalTest::NaturalCollection);
        };
        if items
            .iter()
            .any(|arguments| arguments.len() != element.argument_sorts.len())
        {
            return fails(LocalTest::Arity);
        }
        Ok(EntriesFrame {
            term,
            role: match &metadata {
                CollectionMetadata::Map(_) => CollectionRole::Map,
                CollectionMetadata::Set(_) => CollectionRole::Set,
                CollectionMetadata::List(_) => CollectionRole::List,
            },
            collection: collection_sort.to_string(),
            unit: symbols.unit.to_string(),
            element: symbols.element.to_string(),
            concat: symbols.concat.to_string(),
            sorts: element.argument_sorts.clone(),
            judged,
            results: Vec::with_capacity(items.len()),
            items,
        })
    }

    /// The argument lists of the element applications of a collection term, in the term's
    /// order, or `None` when a component is not a natural unit, element or concat of `metadata`.
    ///
    /// A collection is a chain of concatenations as long as it has elements, so the walk keeps
    /// the components still to read on a work list instead of the native stack.
    fn collection_entries<'t>(
        &self,
        term: &'t Pattern,
        metadata: &k_rust_backend::term::CollectionMetadata,
    ) -> Option<Vec<&'t [Pattern]>> {
        use k_rust_backend::term::CollectionMetadata;
        let symbols = match metadata {
            CollectionMetadata::Map(d) => &d.symbols,
            CollectionMetadata::List(d) | CollectionMetadata::Set(d) => &d.symbols,
        };
        let mut out = Vec::new();
        let mut pending = vec![term];
        // Invariant: `out` holds the element arguments of the components before the ones on
        // `pending`, which holds the components still to read, the next one last; each component
        // is read once.
        while let Some(component) = pending.pop() {
            let Pattern::Application { symbol, arguments } = component else {
                return None;
            };
            if !symbol.sort_parameters.is_empty() {
                return None;
            }
            let backend = self.definition.symbols().get(symbol.name.as_str())?;
            if backend.attributes.collection.as_ref() != Some(metadata)
                || !crate::census::natural_collection_symbol(backend, self.definition)
            {
                return None;
            }
            let name = symbol.name.as_str();
            if name == &*symbols.concat && arguments.len() == 2 {
                pending.push(&arguments[1]);
                pending.push(&arguments[0]);
            } else if name == &*symbols.element {
                out.push(arguments.as_slice());
            } else if name != &*symbols.unit || !arguments.is_empty() {
                return None;
            }
        }
        Some(out)
    }

    /// The feasibility of a leaf state (KORE JSON) of the leaf definition's run, decided on the
    /// leaf definition and its solver (re-pin finding A-12); `Unknown` when the host refuses the
    /// stack the leaf needs, the refusal recorded ([`Self::host_refusal_during`]).
    pub fn shared_leaf_feasibility(
        &self,
        state: &serde_json::Value,
    ) -> crate::feasibility::LeafFeasibility {
        crate::feasibility::shared_leaf_feasibility(
            self.leaf_definition,
            self.leaf_solver,
            &self.leaf_inhabitation,
            state,
        )
        .unwrap_or_else(|host| {
            self.record_host_refusal(host);
            crate::feasibility::LeafFeasibility::Unknown
        })
    }
    /// Classifies one declaration; the reference bridge deliberately runs both phases per leaf.
    pub fn classify_step(
        &self,
        spec: &StepEventSpec,
        pre: &Pattern,
        post: Option<&Pattern>,
        path: &PathInput,
    ) -> StepPresence {
        let phase1 = self.classify_step_phase1(spec, pre, post);
        self.classify_step_phase2(spec, &phase1, path)
    }

    /// The definition-dependent structural walk, independent of the leaf predicate.
    pub(crate) fn classify_step_phase1(
        &self,
        spec: &StepEventSpec,
        pre: &Pattern,
        post: Option<&Pattern>,
    ) -> StepPhase1 {
        if contains_non_strict_injection(self.definition, &spec.pre)
            || spec
                .post
                .as_ref()
                .is_some_and(|post| contains_non_strict_injection(self.definition, post))
            || contains_non_strict_injection(self.definition, pre)
            || post.is_some_and(|post| contains_non_strict_injection(self.definition, post))
        {
            return StepPhase1::Undecided;
        }
        let mut walk = Walk::default();
        walk.pair(self.definition, &spec.pre, pre);
        if let Some(pattern) = &spec.post {
            if let Some(post) = post {
                walk.pair(self.definition, pattern, post);
            } else {
                walk.undecided = true;
            }
        }
        if walk.absent {
            return StepPhase1::Absent;
        }
        if walk.undecided {
            return StepPhase1::Undecided;
        }
        StepPhase1::Matched(walk)
    }

    /// Decides the walk's deferred relations and feasibility under this leaf's predicate.
    pub(crate) fn classify_step_phase2(
        &self,
        spec: &StepEventSpec,
        phase1: &StepPhase1,
        path: &PathInput,
    ) -> StepPresence {
        let walk = match phase1 {
            StepPhase1::Absent => return StepPresence::Absent,
            StepPhase1::Undecided => return StepPresence::Undecided,
            StepPhase1::Matched(walk) => walk,
        };
        let mut relations = Vec::new();
        for (left, right, deferred) in &walk.pairs {
            let left = if *deferred {
                let Some(left) = substitute_pattern(left, &walk.bindings) else {
                    return StepPresence::Undecided;
                };
                left
            } else {
                left.clone()
            };
            // Both terms are subterms of states of one request, where one printed name is one
            // variable (variable identity: names are read verbatim and printed injectively), so
            // identical terms are equal on every instance.
            let decision = if left == *right
                && !crate::feasibility::contains_untrusted_domain_value(self.definition, &left)
            {
                RelationDecision::Equal
            } else {
                self.relations.relate(path, &[], &left, right)
            };
            match decision {
                RelationDecision::Equal => {}
                RelationDecision::EqualIf(more) => relations.extend(more),
                RelationDecision::Unequal => return StepPresence::Absent,
                RelationDecision::Indeterminate => return StepPresence::Undecided,
            }
        }
        relations.sort();
        relations.dedup();
        let Some(payload) = spec
            .payload
            .iter()
            .map(|name| walk.bindings.get(name).cloned())
            .collect::<Option<Vec<_>>>()
        else {
            return StepPresence::Undecided;
        };
        if relations.is_empty() {
            StepPresence::Certain(payload)
        } else if self.relations.feasible(path, &relations) == Feasibility::Unsat {
            StepPresence::Absent
        } else {
            StepPresence::Conditional(payload, relations)
        }
    }
}

fn substitute_pattern(pattern: &Pattern, bindings: &BTreeMap<String, Pattern>) -> Option<Pattern> {
    match pattern {
        Pattern::Variable(var) => bindings.get(&var.name).cloned(),
        Pattern::Application { symbol, arguments } => Some(Pattern::Application {
            symbol: symbol.clone(),
            arguments: arguments
                .iter()
                .map(|arg| substitute_pattern(arg, bindings))
                .collect::<Option<Vec<_>>>()?,
        }),
        Pattern::DomainValue { .. } => Some(pattern.clone()),
        _ => None,
    }
}

#[derive(Clone)]
pub(crate) enum StepPhase1 {
    Absent,
    Undecided,
    Matched(Walk),
}

#[derive(Clone, Default)]
pub(crate) struct Walk {
    bindings: BTreeMap<String, Pattern>,
    pairs: Vec<(Pattern, Pattern, bool)>,
    absent: bool,
    undecided: bool,
}

impl Walk {
    fn pair(&mut self, definition: &BackendDefinition, pattern: &Pattern, state: &Pattern) {
        if self.absent {
            return;
        }
        if non_strict_injection_node(definition, pattern)
            || non_strict_injection_node(definition, state)
        {
            self.undecided = true;
            return;
        }
        if let Pattern::Variable(var) = pattern {
            if let Some(first) = self.bindings.get(&var.name) {
                self.pairs.push((first.clone(), state.clone(), false));
            } else {
                self.bindings.insert(var.name.clone(), state.clone());
            }
            return;
        }
        if matches!(state, Pattern::Variable(_)) {
            self.pairs.push((pattern.clone(), state.clone(), true));
            return;
        }
        match (pattern, state) {
            (
                Pattern::DomainValue {
                    sort: ps,
                    value: pv,
                },
                Pattern::DomainValue {
                    sort: ss,
                    value: sv,
                },
            ) => {
                if ps != ss
                    || !domain_value_identity_safe(definition, ps, pv.as_bytes())
                    || !domain_value_identity_safe(definition, ss, sv.as_bytes())
                {
                    self.undecided = true;
                } else if pv != sv {
                    self.absent = true;
                }
            }
            (
                Pattern::Application {
                    symbol: ps,
                    arguments: pa,
                },
                Pattern::Application {
                    symbol: ss,
                    arguments: sa,
                },
            ) if ps == ss && pa.len() == sa.len() => {
                if ps.name == "inj" || free_symbol(definition, &ps.name) {
                    for (p, s) in pa.iter().zip(sa) {
                        self.pair(definition, p, s);
                    }
                } else {
                    self.undecided = true;
                }
            }
            (
                Pattern::Application {
                    symbol: ps,
                    arguments: pa,
                },
                Pattern::Application {
                    symbol: ss,
                    arguments: sa,
                },
            ) if ps.name == "inj" && ss.name == "inj" && pa.len() == 1 && sa.len() == 1 => {
                let ([p_source, p_target], [s_source, s_target]) =
                    (ps.sort_parameters.as_slice(), ss.sort_parameters.as_slice())
                else {
                    self.undecided = true;
                    return;
                };
                if p_target != s_target {
                    self.undecided = true;
                    return;
                }
                let (Some(p_sort), Some(s_sort)) =
                    (internal_sort(p_source), internal_sort(s_source))
                else {
                    self.undecided = true;
                    return;
                };
                if definition
                    .sort_graph()
                    .check_subsort(&s_sort, &p_sort)
                    .unwrap_or(false)
                {
                    if p_sort == s_sort {
                        self.pair(definition, &pa[0], &sa[0]);
                    } else {
                        self.pair(
                            definition,
                            &pa[0],
                            &Pattern::Application {
                                symbol: k_rust::kore::ast::Symbol {
                                    name: "inj".into(),
                                    sort_parameters: vec![s_source.clone(), p_source.clone()],
                                },
                                arguments: vec![sa[0].clone()],
                            },
                        );
                    }
                } else if definition
                    .sort_graph()
                    .check_subsort(&p_sort, &s_sort)
                    .unwrap_or(false)
                {
                    if matches!(sa[0], Pattern::Variable(_)) {
                        self.pairs.push((pattern.clone(), state.clone(), true));
                    } else if free_top(definition, &sa[0], &s_sort) {
                        self.absent = true;
                    } else {
                        self.undecided = true;
                    }
                } else if free_top(definition, &sa[0], &s_sort)
                    || free_top(definition, &pa[0], &p_sort)
                    || closures_disjoint(definition, &p_sort, &s_sort)
                {
                    self.absent = true;
                } else {
                    self.undecided = true;
                }
            }
            (Pattern::Application { symbol: ps, .. }, Pattern::Application { symbol: ss, .. })
                if (free_symbol(definition, &ps.name)
                    && (free_symbol(definition, &ss.name) || ss.name == "inj"))
                    || (ps.name == "inj" && free_symbol(definition, &ss.name)) =>
            {
                self.absent = true;
            }
            _ => self.undecided = true,
        }
    }
}

fn free_symbol(definition: &BackendDefinition, name: &str) -> bool {
    definition
        .symbols()
        .get(name)
        .is_some_and(|symbol| free_constructor(symbol))
}
fn free_top(definition: &BackendDefinition, pattern: &Pattern, sort: &InternalSort) -> bool {
    matches!(pattern, Pattern::Application { symbol, .. }
        if definition.symbols().get(symbol.name.as_str()).is_some_and(|head|
            free_constructor(head) && head.result_sort == *sort))
}

fn closures_disjoint(
    definition: &BackendDefinition,
    left: &InternalSort,
    right: &InternalSort,
) -> bool {
    !definition.sorts().keys().any(|sort| {
        let sort = InternalSort::simple(sort.as_ref());
        definition
            .sort_graph()
            .check_subsort(&sort, left)
            .unwrap_or(false)
            && definition
                .sort_graph()
                .check_subsort(&sort, right)
                .unwrap_or(false)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{NativeValidator, support};
    use k_rust::backend::BackendOptions;
    use k_rust::kompile::CompileOptions;

    #[test]
    fn generated_cells_and_k_sequence_are_free_constructors() {
        let validator = NativeValidator::bind(support::load("symmem.k"), CompileOptions::default());
        let side = validator.compile_baseline().expect("symmem compiles");
        let mut backend = Backend::new(
            &side.artifacts().definition_kore,
            "SYMMEM",
            BackendOptions::default(),
        )
        .expect("backend");
        backend
            .with_solver(None, |definition, _| -> Result<(), BackendError> {
                for name in [
                    "Lbl'-LT-'generatedTop'-GT-'",
                    "Lbl'-LT-'k'-GT-'",
                    "Lbl'-LT-'generatedCounter'-GT-'",
                    "kseq",
                    "dotk",
                ] {
                    let symbol = definition
                        .symbols()
                        .get(name)
                        .expect("declared constructor");
                    assert!(
                        free_constructor(symbol),
                        "{name} must be a free constructor"
                    );
                }
                Ok(())
            })
            .expect("definition");
    }

    mod kink_tier {
        use super::*;

        #[test]
        #[ignore = "kink"]
        fn same_non_free_head_does_not_decompose_to_an_absence() {
            let validator =
                NativeValidator::bind(support::load("residue.k"), CompileOptions::default());
            let side = validator.compile_baseline().expect("residue compiles");
            let mut backend = Backend::new(
                &side.artifacts().definition_kore,
                "RESIDUE",
                BackendOptions::default(),
            )
            .expect("backend");
            backend
                .with_solver(None, |definition, _| -> Result<(), BackendError> {
                    let mut walk = Walk::default();
                    walk.pair(
                        definition,
                        &support::app("Lblf", vec![support::int(1)]),
                        &support::app("Lblf", vec![support::int(2)]),
                    );
                    assert!(walk.undecided);
                    assert!(!walk.absent);
                    Ok(())
                })
                .expect("definition");
        }
    }

    /// kink27 R3-UNDEF-BRIDGE: `configuration_exists` is k-rust's `ground_defined` on the leaf
    /// definition, behind kink's guards. An irreducible application of a total function exists
    /// though it has no terminal value; one of a partial function that no equation reduces is not
    /// shown to exist; a conjunction and a free variable are refused before k-rust is asked.
    #[test]
    fn configuration_exists_is_k_rusts_existence_on_the_leaf_definition() {
        let definition = BackendDefinition::internalize(
            &k_rust::kore::parser::parse_definition(
                r"[]
                module MAIN
                    sort SortS{} []
                    symbol Lbla{}() : SortS{} [constructor{}()]
                    symbol Lblg{}(SortS{}) : SortS{} [function{}(), total{}()]
                    symbol Lblh{}(SortS{}) : SortS{} [function{}()]
                endmodule []",
            )
            .expect("KORE"),
            "MAIN",
        )
        .expect("definition");
        let pattern = |text: &str| k_rust::kore::parser::parse_pattern(text).expect("pattern");
        let total = pattern(r"Lblg{}(Lbla{}())");
        let decider = ObservationDecider::new(
            &definition,
            &k_rust_backend::smt::NoSolver,
            TestInitialState::of_test(&total),
        );
        assert!(decider.configuration_exists(&total));
        assert_eq!(decider.terminal_value(&total), None);
        assert!(!decider.configuration_exists(&pattern(r"Lblh{}(Lbla{}())")));
        assert!(!decider.configuration_exists(&pattern(r"\and{SortS{}}(Lbla{}(), Lbla{}())")));
        assert!(!decider.configuration_exists(&pattern(r"Lblg{}(X:SortS{})")));
    }

    /// kink27 R3-UNDEF-BRIDGE fix round 1 (review should-fix 2): existence is asked of the leaf
    /// definition, not the shared one (A-12: a mutant's leaf is judged by the mutant's theory).
    /// `g(a)` exists where `g` is total, so the answer follows the leaf definition's declaration
    /// whichever way the shared one declares `g`. Each read-back guard is load-bearing: k-rust's
    /// own `ground_defined` holds of the refused terms, and kink refuses them because the
    /// read-back term may not be the term k-rust built (a non-ASCII String domain value has no
    /// injective codec; an identity injection is not strict).
    #[test]
    fn configuration_exists_reads_the_leaf_definition_behind_the_read_back_guards() {
        let declarations = |g: &str| {
            format!(
                r#"[]
                module MAIN
                    sort SortS{{}} []
                    hooked-sort SortString{{}} [hook{{}}("STRING.String"), hasDomainValues{{}}()]
                    symbol Lbla{{}}() : SortS{{}} [constructor{{}}()]
                    symbol Lblg{{}}(SortS{{}}) : SortS{{}} [function{{}}(){g}]
                    symbol Lbls{{}}(SortString{{}}) : SortS{{}} [function{{}}(), total{{}}()]
                    symbol inj{{From, To}}(From) : To [sortInjection{{}}()]
                endmodule []"#
            )
        };
        let internalize = |g: &str| {
            BackendDefinition::internalize(
                &k_rust::kore::parser::parse_definition(&declarations(g)).expect("KORE"),
                "MAIN",
            )
            .expect("definition")
        };
        let total = internalize(", total{}()");
        let partial = internalize("");
        let pattern = |text: &str| k_rust::kore::parser::parse_pattern(text).expect("pattern");
        let applied = pattern(r"Lblg{}(Lbla{}())");
        let initial = TestInitialState::of_test(&applied);
        let solver = &k_rust_backend::smt::NoSolver;
        assert!(
            ObservationDecider::for_leaves_of(&partial, &total, solver, initial)
                .configuration_exists(&applied),
            "the leaf definition declares g total"
        );
        assert!(
            !ObservationDecider::for_leaves_of(&total, &partial, solver, initial)
                .configuration_exists(&applied),
            "only the shared definition declares g total"
        );

        let decider = ObservationDecider::new(&total, solver, initial);
        let k_rust_defined = |term: &Pattern| {
            total
                .admit_unverified(term, &[])
                .internalize_term()
                .is_ok_and(|internal| total.ground_defined(&internal))
        };
        let ascii = pattern(r#"Lbls{}(\dv{SortString{}}("A"))"#);
        assert!(decider.configuration_exists(&ascii));
        let accented = pattern(r#"Lbls{}(\dv{SortString{}}("\u00e9"))"#);
        assert!(k_rust_defined(&accented));
        assert!(!decider.configuration_exists(&accented));
        let identity = pattern(r"Lblg{}(inj{SortS{}, SortS{}}(Lbla{}()))");
        assert!(k_rust_defined(&identity));
        assert!(!decider.configuration_exists(&identity));
    }

    /// kink27 R5-BYTES-ENDS: a domain value of a sort hooked `BYTES.Bytes` has a trusted
    /// injective codec. Its payload is its sort's one stored form (the byte sequence itself at
    /// `SortBytes`, the UTF-8 of one code point per byte at a renamed sort), so every spelling of
    /// one value reads to one payload and distinct payloads are distinct values. A payload at a
    /// renamed sort outside that form has no decode and stays refused.
    #[test]
    fn bytes_domain_values_have_a_trusted_injective_codec() {
        let definition = BackendDefinition::internalize(
            &k_rust::kore::parser::parse_definition(
                r#"[]
                module MAIN
                    sort SortS{} []
                    hooked-sort SortBytes{} [hook{}("BYTES.Bytes"), hasDomainValues{}()]
                    hooked-sort SortMyBytes{} [hook{}("BYTES.Bytes"), hasDomainValues{}()]
                    symbol Lblb{}(SortBytes{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
                    symbol Lblm{}(SortMyBytes{}) : SortS{} [constructor{}(), functional{}(), injective{}()]
                endmodule []"#,
            )
            .expect("KORE"),
            "MAIN",
        )
        .expect("definition");
        let pattern = |text: &str| k_rust::kore::parser::parse_pattern(text).expect("pattern");
        let empty = pattern(r#"Lblb{}(\dv{SortBytes{}}(""))"#);
        let decider = ObservationDecider::new(
            &definition,
            &k_rust_backend::smt::NoSolver,
            TestInitialState::of_test(&empty),
        );
        for text in [
            r#"Lblb{}(\dv{SortBytes{}}(""))"#,
            r#"Lblb{}(\dv{SortBytes{}}("\x03\x00\x00\x00\x00\x00\x00\x00"))"#,
            r#"Lblb{}(\dv{SortBytes{}}("\xff\x80A"))"#,
            r#"Lblm{}(\dv{SortMyBytes{}}("\xe9"))"#,
        ] {
            let term = pattern(text);
            assert_eq!(decider.terminal_value(&term), Some(term.clone()), "{text}");
        }

        // One value, one payload: every spelling of the byte 0x41 (raw, `\x`, `\u`, `\U`) reads to
        // one pattern, so does every spelling of the byte 0xe9, and the byte 0xe9 and the two bytes
        // of the UTF-8 of `é` are distinct values.
        let spelled = pattern(r#"\dv{SortBytes{}}("A")"#);
        assert_eq!(spelled, pattern(r#"\dv{SortBytes{}}("\x41")"#));
        assert_eq!(spelled, pattern(r#"\dv{SortBytes{}}("\u0041")"#));
        assert_eq!(spelled, pattern(r#"\dv{SortBytes{}}("\U00000041")"#));
        assert_eq!(
            pattern(r#"\dv{SortBytes{}}("\u00e9")"#),
            pattern(r#"\dv{SortBytes{}}("\xe9")"#)
        );
        assert_ne!(
            pattern(r#"\dv{SortBytes{}}("\xe9")"#),
            pattern(r#"\dv{SortBytes{}}("\xc3\xa9")"#)
        );

        // A payload outside a renamed sort's form (not UTF-8, or a code point above U+00FF) is
        // stored by no k-rust route and has no decode.
        let template = pattern(r#"Lblm{}(\dv{SortMyBytes{}}(""))"#);
        let Pattern::Application { symbol, arguments } = &template else {
            unreachable!("an application")
        };
        let Some(Pattern::DomainValue { sort: renamed, .. }) = arguments.first() else {
            unreachable!("a domain value argument")
        };
        for payload in [vec![0xe9], "\u{101}".as_bytes().to_vec()] {
            let term = Pattern::Application {
                symbol: symbol.clone(),
                arguments: std::iter::once(Pattern::DomainValue {
                    sort: renamed.clone(),
                    value: k_rust::kore::ast::KoreString::from_bytes(payload.clone()),
                })
                .collect(),
            };
            assert_eq!(decider.terminal_value(&term), None, "{payload:?}");
        }

        assert!(decider.configuration_exists(&pattern(r#"Lblb{}(\dv{SortBytes{}}("\xff"))"#)));
    }
}
