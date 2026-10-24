//! Step-event declarations and a baseline-owned observation decider.

use std::collections::BTreeMap;

use k_rust::backend::{Backend, BackendError};
use k_rust::kore::ast::{Pattern, Sort, VariableKind};
use k_rust_backend::definition::BackendDefinition;
use k_rust_backend::smt::SmtSolver;
use k_rust_backend::term::Sort as InternalSort;
use kink_pattern::{
    Constructor, EventVocabulary, Feasibility, PathInput, RelationDecider, RelationDecision,
    TermRelation,
};

use crate::data::DataEnds;
use crate::feasibility::{
    BackendRelations, Inhabitation, TestInitialState, contains_non_strict_injection,
    domain_value_identity_safe, free_constructor, non_strict_injection_node,
    strict_injection_sorts,
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
    /// facts, an overload data head).
    FreeConstructor,
    /// The outermost application of an overload data head, which k-rust does not judge data.
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
                 Bool values, and ASCII values of String and of sorts without a hook, have one)"
            }
            Self::CanonicalInjection => "it is a sort injection not in k-rust's normal form",
            Self::DeclaredSymbol => "its symbol is not declared by the definition",
            Self::FreeConstructor => {
                "its head is neither a free constructor (it is for example a function, a hooked \
                 or anywhere symbol, or a symbol with axioms) nor an overload data head"
            }
            Self::OverloadData => {
                "it is an application of an overload head that k-rust does not judge data"
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
    /// ([`crate::data::data_ends`]): the overload data heads whose applications the walk admits
    /// where k-rust's data judgement holds (KINK-OVERLOAD-VALUE). [`DataEnds::None`] (the default)
    /// admits no overload application; it does not refuse the rest of TV-01, since refusing every
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
    /// application of an overload data head that is data ([`Self::overload_data`]).
    pub fn definition_independent(&self, term: &Pattern) -> bool {
        self.independent(term, false).is_ok()
    }

    /// [`Self::definition_independent`] of `term`, or the first node, in pre-order, that fails
    /// its own test ([`Self::node_test`]); `judged` when an enclosing overload application was
    /// already judged data as a whole, so a nested one needs no judgement of its own.
    fn independent(&self, term: &Pattern, judged: bool) -> Result<(), Box<NonValue>> {
        let judged = self.node_test(term, judged)?;
        if let Pattern::Application { symbol, arguments } = term {
            for (index, argument) in arguments.iter().enumerate() {
                self.independent(argument, judged)
                    .map_err(|failure| failure.below_argument(&symbol.name, index))?;
            }
        }
        Ok(())
    }

    /// The own test of one node that is not a collection term, its children ignored, shared by
    /// [`Self::definition_independent`] and [`Self::terminal_value`]: a variable passes; a domain
    /// value passes when its codec is trusted and injective (`domain_value_identity_safe`); an
    /// injection when it is in k-rust's normal form ([`canonical_injection`]); an application when
    /// its head is a free constructor of the shared definition, or, with [`Self::judging_data`],
    /// an overload data head whose outermost application is data ([`Self::overload_data`]);
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

    /// Whether `application`, an application of an overload data head of the shared definition
    /// that no enclosing one covers, is data: under the shared definition with its facts, and,
    /// for leaves of another definition, under the leaf definition with its facts too
    /// ([`DataEnds::overload_application_is_data`], k-rust's `is_data`, once for the whole
    /// subterm; review N4). Its arguments are walked for the rest of TV-01 by the caller.
    fn overload_data(&self, application: &Pattern) -> bool {
        self.data
            .overload_application_is_data(self.definition, application)
            && (std::ptr::eq(self.definition, self.leaf_definition)
                || self
                    .leaf_data
                    .overload_application_is_data(self.leaf_definition, application))
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

    fn has_collection_symbol(&self, term: &Pattern) -> bool {
        let mut found = false;
        k_rust::kore::walk::for_each_post_order(term, |node| {
            if let Pattern::Application { symbol, .. } = node {
                found |= self
                    .definition
                    .symbols()
                    .get(symbol.name.as_str())
                    .is_some_and(|s| s.attributes.collection.is_some());
            }
        });
        found
    }

    /// The value of `term` at the sort `expected`, or the first node, in pre-order, that fails
    /// its own test (its path innermost first); `judged` as in [`Self::independent`].
    fn value_at(
        &self,
        term: &Pattern,
        expected: Option<&InternalSort>,
        judged: bool,
    ) -> Result<Pattern, Box<NonValue>> {
        if !self.has_collection_symbol(term) {
            return self.independent(term, judged).map(|()| term.clone());
        }
        if let Pattern::Application { symbol, .. } = term
            && !is_injection(term)
            && self
                .definition
                .symbols()
                .get(symbol.name.as_str())
                .is_some_and(|head| head.attributes.collection.is_some())
        {
            return self.collection_value(term, expected, judged);
        }
        let judged = self.node_test(term, judged)?;
        let fails = |test| Err(NonValue::at(term, test));
        let Pattern::Application { symbol, arguments } = term else {
            // A variable or a domain value holds no collection symbol.
            return fails(LocalTest::TermKind);
        };
        if is_injection(term) {
            // A canonical injection has one argument and a source sort.
            let (Some(source), [argument]) = (
                symbol.sort_parameters.first().and_then(internal_sort),
                arguments.as_slice(),
            ) else {
                return fails(LocalTest::CanonicalInjection);
            };
            return Ok(Pattern::Application {
                symbol: symbol.clone(),
                arguments: vec![
                    self.value_at(argument, Some(&source), judged)
                        .map_err(|failure| failure.below_argument(&symbol.name, 0))?,
                ],
            });
        }
        let Some(backend) = self.definition.symbols().get(symbol.name.as_str()) else {
            return fails(LocalTest::DeclaredSymbol);
        };
        if arguments.len() != backend.argument_sorts.len() {
            return fails(LocalTest::Arity);
        }
        let mut values = Vec::with_capacity(arguments.len());
        for (index, (argument, sort)) in arguments.iter().zip(&backend.argument_sorts).enumerate() {
            values.push(
                self.value_at(argument, Some(sort), judged)
                    .map_err(|failure| failure.below_argument(&symbol.name, index))?,
            );
        }
        Ok(Pattern::Application {
            symbol: symbol.clone(),
            arguments: values,
        })
    }

    /// The value of a collection term at `expected`, or the first node, in pre-order, that fails
    /// its own test: the collection node's own tests come first (trusted, at its collection sort,
    /// ground, natural components with the element's arity, distinct Map keys or Set elements
    /// among the entries whose keys or elements have values), then its entries in the term's
    /// order, each key before its value.
    fn collection_value(
        &self,
        term: &Pattern,
        expected: Option<&InternalSort>,
        judged: bool,
    ) -> Result<Pattern, Box<NonValue>> {
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
        if !term.free_variables().is_empty() {
            return fails(LocalTest::Ground);
        }
        let mut items = Vec::new();
        if self
            .collection_entries(term, &metadata, &mut items)
            .is_none()
        {
            return fails(LocalTest::NaturalCollection);
        }
        let Some(element) = self.definition.symbols().get(&*symbols.element) else {
            return fails(LocalTest::NaturalCollection);
        };
        if items
            .iter()
            .any(|arguments| arguments.len() != element.argument_sorts.len())
        {
            return fails(LocalTest::Arity);
        }
        let results = items
            .iter()
            .map(|arguments| {
                arguments
                    .iter()
                    .zip(&element.argument_sorts)
                    .map(|(argument, sort)| self.value_at(argument, Some(sort), judged))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let mut compared = match &metadata {
            CollectionMetadata::Map(_) => results
                .iter()
                .filter_map(|entry| Some(vec![entry.first()?.as_ref().ok()?]))
                .collect::<Vec<_>>(),
            CollectionMetadata::Set(_) => results
                .iter()
                .filter_map(|entry| entry.iter().map(|value| value.as_ref().ok()).collect())
                .collect::<Vec<_>>(),
            CollectionMetadata::List(_) => Vec::new(),
        };
        compared.sort();
        if compared.windows(2).any(|pair| pair[0] == pair[1]) {
            return fails(LocalTest::DistinctEntries);
        }
        let collection = collection_sort.to_string();
        let mut values = Vec::with_capacity(results.len());
        for (entry, arguments) in results.into_iter().enumerate() {
            let arity = arguments.len();
            let mut row = Vec::with_capacity(arity);
            for (argument, value) in arguments.into_iter().enumerate() {
                row.push(value.map_err(|failure| {
                    failure.below(NonValueStep::Entry {
                        collection: collection.clone(),
                        entry,
                        role: match (&metadata, argument) {
                            (CollectionMetadata::Map(_), 0) => EntryRole::Key,
                            (CollectionMetadata::Map(_), _) => EntryRole::Value,
                            _ => EntryRole::Element,
                        },
                        argument,
                    })
                })?);
            }
            values.push(row);
        }
        match &metadata {
            // Keys (Set elements) are distinct, checked above.
            CollectionMetadata::Map(_) => values.sort_by(|left, right| left[0].cmp(&right[0])),
            CollectionMetadata::Set(_) => values.sort(),
            CollectionMetadata::List(_) => {}
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
            .map(|arguments| application(&symbols.element, arguments))
            .collect::<Vec<_>>();
        let Some(mut result) = elements.pop() else {
            return Ok(application(&symbols.unit, Vec::new()));
        };
        while let Some(element) = elements.pop() {
            result = application(&symbols.concat, vec![element, result]);
        }
        Ok(result)
    }

    /// The argument lists of the element applications of a collection term, or `None` when a
    /// component is not a natural unit, element or concat of `metadata`.
    fn collection_entries(
        &self,
        term: &Pattern,
        metadata: &k_rust_backend::term::CollectionMetadata,
        out: &mut Vec<Vec<Pattern>>,
    ) -> Option<()> {
        use k_rust_backend::term::CollectionMetadata;
        let Pattern::Application { symbol, arguments } = term else {
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
        let symbols = match metadata {
            CollectionMetadata::Map(d) => &d.symbols,
            CollectionMetadata::List(d) | CollectionMetadata::Set(d) => &d.symbols,
        };
        let name = symbol.name.as_str();
        if name == &*symbols.unit && arguments.is_empty() {
            Some(())
        } else if name == &*symbols.concat && arguments.len() == 2 {
            self.collection_entries(&arguments[0], metadata, out)?;
            self.collection_entries(&arguments[1], metadata, out)
        } else if name == &*symbols.element {
            out.push(arguments.clone());
            Some(())
        } else {
            None
        }
    }

    /// The feasibility of a leaf state (KORE JSON) of the leaf definition's run, decided on the
    /// leaf definition and its solver (re-pin finding A-12).
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
}
