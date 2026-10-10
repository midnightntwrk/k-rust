//! ```toml algorithm
//! id = "backend.definition.internalize"
//! name = "KORE definition validation and internalization"
//! sites = ["BackendDefinition::internalize", "BackendDefinition::internalize_with_added", "BackendDefinition::internalize_for_source_execution", "BackendDefinition::internalize_canonical", "BackendDefinition::internalize_term", "BackendDefinition::internalize_pattern", "visit_module"]
//! variable = "d = definition sentences and pattern nodes; a = axioms and claims of the modules the main module reaches, each module counted once"
//! counters = []
//! no_counter = "the internalize phase of kprove timings measures the whole boundary; TermConstructed, and through definedness discharge MatchingProblems, MatchingPairs and SimplifyInvocations, are bumped by callees"
//! span = "per problem"
//! consumes = [
//!   { type = "k_rust_kore::kore::ast::Definition", role = "compiled definition" },
//!   { type = "k_rust_kore::kore::ast::Pattern", role = "converted term" },
//! ]
//! produces = [
//!   { type = "k_rust_backend::definition::BackendDefinition", role = "internalized theory" },
//!   { type = "k_rust_backend::term::Term", role = "internalized term" },
//!   { type = "k_rust_backend::rewrite::Pattern", role = "internalized pattern" },
//! ]
//! constrains = [{ id = "kompile.sentences.number", site = "BackendDefinition::internalize_for_source_execution", via = "the UNIQUE_ID attribute survives KORE emission and determines source rewrite order" }]
//!
//! [[cost]]
//! mode = "one definition load"
//! bound = "O(d) for the module, sort and symbol passes, plus O(a) axiom pushes each with one alias expansion and one classification, plus collapse_equal_axioms (one traversal per comparison, comparing only axioms with one UNIQUE_ID), plus a fixed-root symbol index pass and one result-head bucket and schema scan per finite-domain candidate with recursive sort matching, plus verify_definition, backend.definition.closure and backend.definedness.discharge, plus, after the critical-pair check, one walk of the executable left-hand sides and at most r + 1 rounds of one instance-normality scan per ground term an equation-head application of them denotes, not yet recorded, for r recorded terms (record_pattern_tokens)"
//!
//! [[cost]]
//! mode = "one term or pattern request (internalize_term, internalize_pattern)"
//! bound = "one alias expansion plus O(pattern nodes)"
//! ```
//!
//! ```toml algorithm
//! id = "backend.definition.closure"
//! name = "subsort and overload transitive-closure construction"
//! sites = ["build_sort_graph", "OverloadGraph::from_relations", "OverloadGraph"]
//! variable = "S = nodes of the subsort order (declared sorts without parameters and the sorts the subsort axioms name) or overload symbols; C = closure pairs; h = longest relation chain"
//! counters = []
//! no_counter = "closure construction runs once per definition load and has no dedicated counter"
//! span = "per call"
//! invariant = "each closure grows monotonically and is bounded by |S| squared pairs"
//!
//! [[cost]]
//! mode = "subsort closure (build_sort_graph)"
//! bound = "at most h rounds, each O(|S| x |C|)"
//!
//! [[cost]]
//! mode = "overload closure (OverloadGraph::from_relations)"
//! bound = "at most h rounds, each O(|C|^2)"
//! ```
//!
//! Validation and internalization of textual KORE definitions, O(|definition|) for the module, sort
//! and symbol passes plus one axiom push, alias expansion and classification per axiom or claim of
//! each module the main module reaches, once per load: one import DFS with a path stack for cycle
//! detection, which visits each module once and gives the declaration order (postorder) and the
//! axiom order (first-visit preorder), axiom-shape classification, term internalization; subsort
//! and overload transitive closures by naive iteration, rounds <= longest chain, each
//! O(|S| x |closure|) for subsorts and O(|closure|^2) for overloads.
//! No counter; the `internalize` phase of `kprove --timings` measures it,
//! `Counter::TermConstructed` indirectly.

use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fmt,
    mem::Discriminant,
    sync::{Arc, OnceLock},
};

use k_rust_kore::kore::ast as kore;
use k_rust_kore::kore::string as kore_string;
use k_rust_kore::measure::{self, Algorithm};
use k_rust_kore::names::{BuiltinSort, KoreAttribute, MalformedAttribute, WellKnownSymbol};
use rustc_hash::FxHashMap;

use crate::{
    alias::{
        AliasDefinition, UnfoldingBudget, collect as collect_aliases, expand as expand_aliases,
        expand_within as expand_aliases_within,
    },
    builtin::KVarSorts,
    claim::{ClaimError, ReachabilityClaim, internalize_reachability_claim},
    externalize,
    matching::{ClosedSort, SortError, SortGraph},
    rewrite::Pattern,
    rule::{
        AxiomError, ClassifiedAxiom, InternalizedRule, Predicate, PredicateTheory, RewriteTheory,
        RuleKind, RulePatternError, SentenceKey, TermIndex, Theory, algebraic_axiom_roots,
        classify_axiom, collapse_equal_axioms, insert_rewrite_theory, insert_theory,
        internalize_axiom, internalize_model_predicate as internalize_rule_model_predicate,
        internalize_predicate as internalize_rule_predicate, internalize_rule_pattern, rule_index,
    },
    smt::{SExpr, SmtType},
    term::{
        AlgebraicAxioms, CollectionMetadata, CollectionSymbols, FunctionType, HeadRole,
        ListDefinition, MapDefinition, Name, Sort, Symbol, SymbolAttributes, SymbolDeclaration,
        SymbolType, Term, TermKind, Variable,
        names::{HookName, variable_name_problems},
    },
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SortInfo {
    pub parameters: Vec<Name>,
    pub hook: Option<Name>,
    pub has_domain_values: bool,
    collection: Option<CollectionSort>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum CollectionSort {
    Map(CollectionSymbols),
    List(CollectionSymbols),
    Set(CollectionSymbols),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum UnlicensedInjectionSite {
    /// Requests, claims, no-junk alternatives and initial configurations require a subsort path.
    Refuse,
    /// Definition axioms also admit sort-variable schemas; closed pairs still require a path.
    /// The axiom loader drops dead matched alternatives and refuses unlicensed written terms.
    InAxiom,
    /// A matched predicate of a definition axiom (a predicate simplification's left-hand side):
    /// sort-variable pairs are licensed as in InAxiom, but a membership whose pattern operand
    /// holds an unlicensed injection is refused, so the axiom is dead rather than matching
    /// \bottom.
    InAxiomMatched,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PatternOrPredicate {
    Term(Pattern),
    Predicate(crate::rule::Predicate, Sort),
}

/// How a KORE pattern from outside the definition was admitted to internalization.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Admission {
    /// Every check of the standalone verifier passed under the witness's sort variables.
    Verified,
    /// No standalone verification. Internalization still rejects undeclared heads and sorts,
    /// arity and sort mismatches, and domain values at sorts without domain values.
    Unverified,
}

/// A KORE pattern admitted to internalization against one definition, with the sort variables
/// it is read under.
///
/// A pattern from outside the definition denotes something only once it is checked against the
/// definition's signature, and how far it was checked is a decision of the boundary that read it.
/// [`BackendDefinition::verify_standalone_pattern`] and [`BackendDefinition::admit_unverified`]
/// make that decision explicit and are the only constructors. Internalization is a method of the
/// witness, so the definition that admitted a pattern is the one that internalizes it, and the
/// sort-variable context the verifier checked is the one the internalizer uses.
///
/// Outside this crate a definition does not internalize a bare pattern:
///
/// ```compile_fail,E0624
/// # use k_rust_backend::definition::BackendDefinition;
/// # fn f(definition: &BackendDefinition, pattern: &k_rust_kore::kore::ast::Pattern) {
/// let _ = definition.internalize_pattern(pattern, &[]);
/// # }
/// ```
///
/// It internalizes an admitted one:
///
/// ```
/// # use k_rust_backend::definition::BackendDefinition;
/// # fn f(definition: &BackendDefinition, pattern: &k_rust_kore::kore::ast::Pattern) {
/// let _ = definition.admit_unverified(pattern, &[]).internalize_pattern();
/// # }
/// ```
///
/// A verification whose witness is dropped is rejected, since its result decides nothing:
///
/// ```compile_fail
/// # #![deny(unused_must_use)]
/// # use k_rust_backend::definition::{BackendDefinition, DefinitionError};
/// # fn f(d: &BackendDefinition, p: &k_rust_kore::kore::ast::Pattern) -> Result<(),
/// # DefinitionError> {
/// d.verify_standalone_pattern(p, &[])?;
/// # Ok(()) }
/// ```
///
/// ```
/// # #![deny(unused_must_use)]
/// # use k_rust_backend::definition::{BackendDefinition, DefinitionError};
/// # fn f(d: &BackendDefinition, p: &k_rust_kore::kore::ast::Pattern) -> Result<(),
/// # DefinitionError> {
/// let _admitted = d.verify_standalone_pattern(p, &[])?;
/// # Ok(()) }
/// ```
///
/// Binary KORE is decoded to syntax by `k_rust_kore` and admitted like text; this crate has no
/// decoder that internalizes on its own:
///
/// ```compile_fail
/// use k_rust_backend::binary;
/// # fn main() { let _ = binary::decode_term; }
/// ```
///
/// ```
/// use k_rust_kore::kore::binary;
/// # fn main() { let _ = binary::decode_term; }
/// ```
#[derive(Clone, Copy)]
#[must_use = "internalize an admitted pattern through its methods"]
pub struct Admitted<'a> {
    definition: &'a BackendDefinition,
    pattern: &'a kore::Pattern,
    sort_variables: &'a [Name],
    admission: Admission,
}

impl<'a> Admitted<'a> {
    /// The admission decision this witness records.
    pub fn admission(self) -> Admission {
        self.admission
    }

    /// The admitted pattern.
    pub fn pattern(self) -> &'a kore::Pattern {
        self.pattern
    }

    /// The sort variables the pattern is read under.
    pub fn sort_variables(self) -> &'a [Name] {
        self.sort_variables
    }

    /// The definition that admitted the pattern.
    pub(crate) fn definition(self) -> &'a BackendDefinition {
        self.definition
    }

    /// Internalize the pattern as a term, checking its sort injections.
    pub fn internalize_term(self) -> Result<Term, DefinitionError> {
        self.definition
            .internalize_term(self.pattern, self.sort_variables)
    }

    /// Internalize a constrained KORE pattern into its term and predicate components.
    pub fn internalize_pattern(self) -> Result<Pattern, DefinitionError> {
        self.definition
            .internalize_pattern(self.pattern, self.sort_variables)
    }

    /// Internalize KORE as a constrained term, or as a predicate when it has no term leaf.
    pub fn internalize_pattern_or_predicate(self) -> Result<PatternOrPredicate, DefinitionError> {
        self.definition
            .internalize_pattern_or_predicate(self.pattern, self.sort_variables)
    }

    /// Internalize the pattern as an ML predicate and retain its result sort.
    pub fn internalize_predicate(self) -> Result<(crate::rule::Predicate, Sort), DefinitionError> {
        self.definition
            .internalize_predicate(self.pattern, self.sort_variables)
    }

    /// Extract the predicate portion used by the backend get-model operation.
    pub fn internalize_model_predicate(
        self,
    ) -> Result<Option<(crate::rule::Predicate, Sort)>, DefinitionError> {
        self.definition
            .internalize_model_predicate(self.pattern, self.sort_variables)
    }

    /// Internalize one side of an implication, peeling its leading existential binders.
    pub fn internalize_implication_pattern(
        self,
    ) -> Result<(Pattern, BTreeSet<Variable>), DefinitionError> {
        self.definition
            .internalize_implication_pattern(self.pattern, self.sort_variables)
    }

    /// Internalize the alternatives of a top-level KORE disjunction.
    pub fn internalize_disjunction(self) -> Result<Vec<Pattern>, DefinitionError> {
        self.definition
            .internalize_disjunction(self.pattern, self.sort_variables)
    }
}

/// Transitive strict ordering between overloaded KORE symbols.
///
/// A relation `(greater, lesser)` records that `greater` overloads `lesser`. Symbols which share
/// a strict upper bound may be unified by lifting both applications to a common overload.
/// ```toml algorithm-site
/// id = "backend.matching.relation_query"
/// role = "part"
/// sites = ["OverloadGraph::is_overloading", "OverloadGraph::common_overloads", "OverloadGraph::overloaded_by"]
/// ```
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct OverloadGraph {
    greater_than: BTreeMap<Name, BTreeSet<Name>>,
    members: BTreeSet<Name>,
}

impl OverloadGraph {
    fn from_relations(
        relations: impl IntoIterator<Item = (Name, Name)>,
    ) -> Result<Self, DefinitionError> {
        let _span = measure::algorithm_span(Algorithm::BackendDefinitionClosure);
        let mut pairs = relations.into_iter().collect::<BTreeSet<_>>();
        // Invariant: `pairs` only grows, bounded by |S|^2; exit when a round adds no pair.
        loop {
            let inferred = pairs
                .iter()
                .flat_map(|(greater, middle)| {
                    pairs
                        .iter()
                        .filter(move |(candidate, _)| candidate == middle)
                        .map(move |(_, lesser)| (greater.clone(), lesser.clone()))
                })
                .collect::<Vec<_>>();
            let previous = pairs.len();
            pairs.extend(inferred);
            if pairs.len() == previous {
                break;
            }
        }
        if let Some((symbol, _)) = pairs.iter().find(|(greater, lesser)| greater == lesser) {
            return Err(DefinitionError::MalformedAttribute(format!(
                "symbol-overload relation contains a cycle through {symbol}"
            )));
        }
        let mut graph = Self::default();
        for (greater, lesser) in pairs {
            graph.members.insert(greater.clone());
            graph.members.insert(lesser.clone());
            graph
                .greater_than
                .entry(greater)
                .or_default()
                .insert(lesser);
        }
        Ok(graph)
    }

    pub fn is_overloaded(&self, symbol: &Name) -> bool {
        self.members.contains(symbol)
    }

    pub fn is_overloading(&self, greater: &Name, lesser: &Name) -> bool {
        self.greater_than
            .get(greater)
            .is_some_and(|lessers| lessers.contains(lesser))
    }

    pub fn common_overloads(&self, left: &Name, right: &Name) -> BTreeSet<Name> {
        self.greater_than
            .iter()
            .filter(|(_, lessers)| lessers.contains(left) && lessers.contains(right))
            .map(|(greater, _)| greater.clone())
            .collect()
    }

    pub fn overloaded_by(&self, greater: &Name) -> BTreeSet<Name> {
        self.greater_than.get(greater).cloned().unwrap_or_default()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PendingAxiom {
    pub module: Name,
    pub parameters: Vec<Name>,
    pub pattern: kore::Pattern,
    pub attributes: kore::Attributes,
}

/// A validated immutable semantic snapshot of a selected KORE module closure.
///
/// Its signature, source sentences, executable theories, constructor-domain facts and lazy
/// caches describe the same input for the lifetime of the value.
/// Shared getters expose the stored data without granting authority to edit it.
/// To change semantics, edit the KORE syntax and construct a separate validated value with
/// [`Self::internalize`] or [`Self::internalize_for_source_execution`].
/// Rule-only module additions use [`crate::session::BackendSession::add_module`].
/// Cloning preserves the snapshot and its derived facts.
///
/// Each stored component is private, including to other backend modules:
///
/// ```compile_fail
/// use k_rust_backend::definition::BackendDefinition;
///
/// fn edit(definition: &mut BackendDefinition) {
///     definition.main_module = "OTHER".into();
/// }
/// ```
///
/// ```compile_fail
/// use k_rust_backend::definition::BackendDefinition;
///
/// fn edit(definition: &mut BackendDefinition) {
///     definition.modules.clear();
/// }
/// ```
///
/// ```compile_fail
/// use k_rust_backend::definition::BackendDefinition;
///
/// fn edit(definition: &mut BackendDefinition) {
///     definition.sorts.clear();
/// }
/// ```
///
/// ```compile_fail
/// use k_rust_backend::definition::BackendDefinition;
///
/// fn edit(definition: &mut BackendDefinition) {
///     definition.symbols.clear();
/// }
/// ```
///
/// ```compile_fail
/// use k_rust_backend::definition::BackendDefinition;
///
/// fn edit(definition: &mut BackendDefinition) {
///     definition.sort_graph = Default::default();
/// }
/// ```
///
/// ```compile_fail
/// use k_rust_backend::definition::BackendDefinition;
///
/// fn edit(definition: &mut BackendDefinition) {
///     definition.overloads = Default::default();
/// }
/// ```
///
/// ```compile_fail
/// use k_rust_backend::definition::BackendDefinition;
///
/// fn edit(definition: &mut BackendDefinition) {
///     definition.axioms.clear();
/// }
/// ```
///
/// ```compile_fail
/// use k_rust_backend::definition::BackendDefinition;
///
/// fn edit(definition: &mut BackendDefinition) {
///     definition.classified_axioms.clear();
/// }
/// ```
///
/// ```compile_fail
/// use k_rust_backend::definition::BackendDefinition;
///
/// fn edit(definition: &mut BackendDefinition) {
///     definition.claims.clear();
/// }
/// ```
///
/// ```compile_fail
/// use k_rust_backend::definition::BackendDefinition;
///
/// fn edit(definition: &mut BackendDefinition) {
///     definition.reachability_claims.clear();
/// }
/// ```
///
/// ```compile_fail
/// use k_rust_backend::definition::BackendDefinition;
///
/// fn edit(definition: &mut BackendDefinition) {
///     definition.rewrite_theory.clear();
/// }
/// ```
///
/// ```compile_fail
/// use k_rust_backend::definition::BackendDefinition;
///
/// fn edit(definition: &mut BackendDefinition) {
///     definition.ceil_theory.clear();
/// }
/// ```
///
/// Shared views also prevent editing the signature, relations, nested symbol or rule handles,
/// and stored claim consequents:
///
/// ```compile_fail
/// use k_rust_backend::{definition::BackendDefinition, term::Name};
///
/// fn edit(definition: &BackendDefinition) {
///     definition.sorts().get_mut(&Name::from("SortS")).unwrap().has_domain_values = true;
/// }
/// ```
///
/// ```compile_fail
/// use k_rust_backend::definition::BackendDefinition;
///
/// fn edit(definition: &BackendDefinition) {
///     definition.sort_graph().insert("SortS", []);
/// }
/// ```
///
/// ```compile_fail
/// use std::sync::Arc;
/// use k_rust_backend::{definition::BackendDefinition, term::Name};
///
/// fn edit(definition: &BackendDefinition) {
///     Arc::make_mut(definition.symbols().get(&Name::from("a")).unwrap()).name = "other".into();
/// }
/// ```
///
/// ```compile_fail
/// use std::sync::Arc;
/// use k_rust_backend::definition::BackendDefinition;
///
/// fn edit(definition: &BackendDefinition) {
///     let stored = definition.rewrite_theory().values().next().unwrap()
///         .values().next().unwrap().first().unwrap();
///     Arc::make_mut(&mut stored.rule).attributes.preserves_definedness = false;
/// }
/// ```
///
/// ```compile_fail
/// use k_rust_backend::definition::BackendDefinition;
///
/// fn edit(definition: &BackendDefinition) {
///     definition.reachability_claims()[0].rhs.clear();
/// }
/// ```
///
/// Construction, every shared view, cloning and session installation remain available:
///
/// ```
/// use k_rust_backend::{definition::BackendDefinition, session::BackendSession};
/// use k_rust_kore::kore::parser::parse_definition;
///
/// let syntax = parse_definition(r#"[] module MAIN
///     sort SortS{} []
///     symbol a{}() : SortS{} [constructor{}()]
/// endmodule []"#).unwrap();
/// let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
/// assert_eq!(definition.main_module().to_string(), "MAIN");
/// assert_eq!(definition.modules().len(), 1);
/// assert_eq!(definition.sorts().len(), 1);
/// assert_eq!(definition.symbols().len(), 1);
/// let _sort_graph = definition.sort_graph();
/// let _overloads = definition.overloads();
/// assert!(definition.axioms().is_empty());
/// assert!(definition.classified_axioms().is_empty());
/// assert!(definition.claims().is_empty());
/// assert!(definition.reachability_claims().is_empty());
/// assert!(definition.rewrite_theory().is_empty());
/// assert!(definition.ceil_theory().is_empty());
/// assert!(definition.function_theory().is_empty());
/// assert!(definition.simplification_theory().is_empty());
/// assert!(definition.predicate_simplification_theory().is_empty());
/// let session = BackendSession::with_definition(definition.clone());
/// assert_eq!(session.default_module(), "MAIN");
/// assert_eq!(session.definition(None).unwrap().main_module(), definition.main_module());
/// ```
///
/// A cloned symbol handle may be edited as a detached copy.
/// Its edit leaves the stored signature unchanged, and no API installs the copy into this snapshot:
///
/// ```
/// use std::sync::Arc;
/// use k_rust_backend::{definition::BackendDefinition, term::{Name, Sort}};
/// use k_rust_kore::kore::parser::parse_definition;
///
/// let syntax = parse_definition(r#"[] module MAIN
///     sort SortS{} []
///     symbol a{}() : SortS{} [constructor{}()]
/// endmodule []"#).unwrap();
/// let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
/// let stored = definition.symbols().get(&Name::from("a")).unwrap();
/// let mut detached = Arc::clone(stored);
/// Arc::make_mut(&mut detached).argument_sorts.push(Sort::simple("SortS"));
/// assert_eq!(detached.argument_sorts.len(), 1);
/// assert!(stored.argument_sorts.is_empty());
/// assert!(definition.symbols()["a"].argument_sorts.is_empty());
/// ```
#[derive(Clone, Debug)]
pub struct BackendDefinition {
    main_module: Name,
    modules: BTreeSet<Name>,
    sorts: BTreeMap<Name, SortInfo>,
    symbols: BTreeMap<Name, Arc<Symbol>>,
    aliases: BTreeMap<String, AliasDefinition>,
    sort_graph: SortGraph,
    overloads: OverloadGraph,
    axioms: Vec<PendingAxiom>,
    classified_axioms: Vec<ClassifiedAxiom>,
    claims: Vec<PendingAxiom>,
    reachability_claims: Vec<ReachabilityClaim>,
    rewrite_theory: RewriteTheory,
    function_theory: Theory,
    simplification_theory: Theory,
    predicate_simplification_theory: PredicateTheory,
    /// `predicate_simplification_theory` by the top connective of each equation's left-hand
    /// side, each group in the same order: an equation matches only a predicate of its own top
    /// connective, so the simplifier tries a predicate's equations here. Built by `internalize`
    /// from the theory, which is fixed from then on.
    predicate_theory_by_connective: FxHashMap<Discriminant<Predicate>, PredicateTheory>,
    ceil_theory: Theory,
    /// The symbols declared with the KORE `value-production` attribute, which states that an
    /// application no equation reduces is a value of its sort; read by
    /// [`Self::irreducible_application_is_defined`].
    value_productions: BTreeSet<Name>,
    /// The symbols declared with the KORE `impure` attribute, K's mark of an operation with an
    /// effect; read by [`Self::is_impure`].
    impure_symbols: BTreeSet<Name>,
    finite_sort_constructors: BTreeMap<Sort, FiniteConstructorDomain>,
    /// Which sorts may contain a `KVar` token; computed on first use by `SUBSTITUTION.substOne`.
    kvar_sorts: OnceLock<KVarSorts>,
    /// The sorts known to have a value; computed on first use by `sort_is_inhabited`.
    inhabited_sorts: OnceLock<BTreeSet<ClosedSort>>,
    /// The verdict of the load-time critical-pair check (`confluence::check`): which indexes may
    /// carry value claims. [`crate::confluence::ValueClaims::withheld`] until `internalize`
    /// computes it, so that the check itself runs with every claim withheld.
    value_claims: crate::confluence::ValueClaims,
    /// Whether some simplification axiom states an equation between terms but was filed in
    /// `predicate_simplification_theory`, because its left-hand side is not a term pattern (an
    /// `\and` of term patterns). The term simplifier never tries it. Set by `internalize`; see
    /// [`Self::equation_selection_complete`].
    term_equation_in_predicate_theory: bool,
    /// Every term equation's left-hand side by root symbol, for the normal-form checker; built
    /// on first use by `normal_form_catalog`.
    #[cfg(feature = "check-normal-forms")]
    normal_form_catalog: OnceLock<crate::term::head::check::Catalog>,
    /// The height (`nesting::height`) of the deepest pattern or sort of the loaded modules, with
    /// their aliases unfolded: the depth below which the internal rules, claims, and sorts of
    /// the definition lie, and above which an operation's own patterns can be substituted.
    deepest: usize,
}

/// Minted only by `BackendDefinition::equation_selection_complete`: equation selection reaches
/// every term equation that could match an application (CBC-02 I3 (i)).
pub(crate) struct SelectionComplete(());

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum ConstructorHead {
    Symbol {
        name: Name,
        sort_arguments: Vec<Sort>,
    },
    Injection {
        source: Sort,
        target: Sort,
    },
}

/// I5: every value of the sort is an alternative of its no-junk axiom.
/// Minted only by `complete`, which checks that every fixed-root symbol instance is listed.
/// An `EquationHead` can have a normal form with its own root, so constructor heads alone
/// cannot cover a sort that such a symbol can build.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct FiniteConstructorDomain {
    heads: BTreeSet<ConstructorHead>,
}

impl FiniteConstructorDomain {
    fn complete(
        index: &FixedRootSymbols<'_>,
        sort: &Sort,
        listed: BTreeSet<ConstructorHead>,
    ) -> Option<Self> {
        let bucket = match sort {
            Sort::Application { name, .. } => index.by_result_head.get(name),
            Sort::Variable(_) => None,
        };
        for symbol in bucket.into_iter().flatten().chain(&index.schemas) {
            let mut bindings = BTreeMap::new();
            if !match_declaration_sort(
                &symbol.result_sort,
                sort,
                &symbol.sort_variables,
                &mut bindings,
            ) {
                continue;
            }
            if symbol.attributes.head_role() == HeadRole::EquationHead {
                return None;
            }
            let sort_arguments = symbol
                .sort_variables
                .iter()
                .map(|variable| bindings.get(variable).cloned())
                .collect::<Option<Vec<_>>>()?;
            if !listed.contains(&ConstructorHead::Symbol {
                name: symbol.name.clone(),
                sort_arguments,
            }) {
                return None;
            }
        }
        Some(Self { heads: listed })
    }

    pub(crate) fn contains(&self, head: &ConstructorHead) -> bool {
        self.heads.contains(head)
    }

    pub(crate) fn is_covered_by(&self, excluded: &BTreeSet<ConstructorHead>) -> bool {
        self.heads.is_subset(excluded)
    }
}

struct FixedRootSymbols<'a> {
    by_result_head: BTreeMap<Name, Vec<&'a Symbol>>,
    schemas: Vec<&'a Symbol>,
}

impl<'a> FixedRootSymbols<'a> {
    fn of(definition: &'a BackendDefinition) -> Self {
        let mut index = Self {
            by_result_head: BTreeMap::new(),
            schemas: Vec::new(),
        };
        for symbol in definition.symbols.values() {
            if symbol.is(WellKnownSymbol::Inj)
                || !matches!(
                    symbol.attributes.head_role(),
                    HeadRole::FreeConstructor | HeadRole::EquationHead
                )
            {
                continue;
            }
            match &symbol.result_sort {
                Sort::Application { name, .. } => index
                    .by_result_head
                    .entry(name.clone())
                    .or_default()
                    .push(symbol),
                Sort::Variable(name) if symbol.sort_variables.contains(name) => {
                    index.schemas.push(symbol);
                }
                Sort::Variable(_) => {}
            }
        }
        index
    }
}

/// Match a symbol's result sort, binding only variables declared by that symbol.
fn match_declaration_sort(
    declaration: &Sort,
    instance: &Sort,
    variables: &[Name],
    bindings: &mut BTreeMap<Name, Sort>,
) -> bool {
    match (declaration, instance) {
        (Sort::Variable(name), _) if variables.contains(name) => {
            if let Some(bound) = bindings.get(name) {
                bound == instance
            } else {
                bindings.insert(name.clone(), instance.clone());
                true
            }
        }
        (
            Sort::Application { name, arguments },
            Sort::Application {
                name: instance_name,
                arguments: instance_arguments,
            },
        ) => {
            name == instance_name
                && arguments.len() == instance_arguments.len()
                && arguments
                    .iter()
                    .zip(instance_arguments)
                    .all(|(left, right)| match_declaration_sort(left, right, variables, bindings))
        }
        (Sort::Variable(_), Sort::Variable(_)) => declaration == instance,
        (Sort::Variable(_), Sort::Application { .. })
        | (Sort::Application { .. }, Sort::Variable(_)) => false,
    }
}

/// Why a definition, module, or pattern was refused.
///
/// An error outlives the operation that found it, and so the stack that operation was given
/// (`nesting::with_stack`): the caller drops, formats, and compares it on its own stack. Its
/// sorts are therefore held in their KORE form, which is cloned, compared, formatted, and
/// dropped with explicit work lists, so an error naming a sort of any depth is safe to handle on
/// any thread.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DefinitionError {
    NoSuchModule(String),
    ImportCycle(Vec<String>),
    DuplicateModule(String),
    DuplicateSort(String),
    DuplicateSymbol(String),
    DuplicateAlias(String),
    DuplicateRewriteOrderId(String),
    MissingRewriteOrderIds(Vec<String>),
    DuplicateName {
        name: String,
        first_module: String,
        second_module: String,
    },
    DuplicateParameter(String),
    UnknownSort(String),
    UnknownSymbol(String),
    WrongSortArity {
        sort: String,
        expected: usize,
        actual: usize,
    },
    WrongSortArgumentCount {
        symbol: String,
        expected: usize,
        actual: usize,
    },
    WrongSymbolArity {
        symbol: String,
        expected: usize,
        actual: usize,
    },
    WrongAliasSortArgumentCount {
        alias: String,
        expected: usize,
        actual: usize,
    },
    WrongAliasArity {
        alias: String,
        expected: usize,
        actual: usize,
    },
    IncorrectArgumentSort {
        symbol: String,
        index: usize,
        expected: Box<kore::Sort>,
        actual: Box<kore::Sort>,
    },
    NotSubsort {
        source: Box<kore::Sort>,
        target: Box<kore::Sort>,
    },
    /// An executable axiom would write an injection with no subsort path.
    UnlicensedInjection {
        source: Box<kore::Sort>,
        target: Box<kore::Sort>,
        axiom: String,
        /// Declaring module and zero-based position of the representative axiom that failed
        /// in that module's sentence list, counting all sentences, including sorts, symbols
        /// and imports.
        sentence: Box<SentenceKey>,
    },
    InvalidSymbolType(String),
    ConstructorAtFixedSort {
        symbol: String,
        sort: Box<kore::Sort>,
    },
    InvalidSortParameter,
    MalformedAttribute(String),
    MalformedCollection(String),
    MalformedAlias(String),
    AliasCycle(Vec<String>),
    /// Unfolding the aliases of a request pattern, or of the axioms of a definition or of a
    /// module added to it, would add `added` to the size of what is unfolded (`alias::Size`: its
    /// pattern and sort nodes and the bytes of their names), more than the `available` part of
    /// the budget of the operation that supplied them that is left: the larger of
    /// `alias::UNFOLDING_LIMIT` and `alias::UNFOLDING_FACTOR` times the size of the patterns that
    /// operation supplied.
    AliasUnfoldingTooLarge {
        added: u64,
        available: u64,
    },
    MacroOrAliasInImplication(String),
    MacroOrAliasInExecutablePattern(String),
    PredicateInTermPosition {
        count: usize,
    },
    SortWithoutDomainValues {
        sort: Box<kore::Sort>,
    },
    InvalidDomainValue {
        sort: Box<kore::Sort>,
        value: String,
    },
    ExpectedTerm(&'static str),
    EmptyAssociativeApplication(String),
    /// A variable whose name is not a KORE identifier (`@` and an identifier for a set
    /// variable). Textual and JSON KORE cannot spell one; binary KORE and patterns built in
    /// process can.
    VariableName {
        name: String,
        set: bool,
    },
    /// The recursive passes over patterns and sorts nested `depth` levels deep need about
    /// `required` bytes of stack, more than the `limit` that the backend provides for one
    /// operation (`nesting::with_stack`).
    InsufficientStack {
        depth: usize,
        required: usize,
        limit: usize,
    },
    /// The recursive passes over patterns and sorts nested `depth` levels deep need a stack
    /// segment within the limit of [`InsufficientStack`](Self::InsufficientStack), and the system
    /// refused to map it (`nesting::map_segment`).
    StackSegmentRefused {
        depth: usize,
        refused: crate::nesting::SegmentRefused,
    },
    Axiom(AxiomError),
    RulePattern(RulePatternError),
    Claim(ClaimError),
    Verification(crate::verify::VerificationError),
}

impl fmt::Display for DefinitionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoSuchModule(module) => write!(formatter, "Module {module} not found."),
            Self::ImportCycle(modules) => {
                write!(formatter, "Import cycle: {}", modules.join(" -> "))
            }
            Self::DuplicateModule(module) => write!(formatter, "Duplicate module '{module}'"),
            Self::DuplicateSort(sort) => write!(formatter, "Duplicate sort '{sort}'"),
            Self::DuplicateSymbol(symbol) => write!(formatter, "Duplicate symbol '{symbol}'"),
            Self::DuplicateAlias(alias) => write!(formatter, "Duplicate alias '{alias}'"),
            Self::DuplicateRewriteOrderId(unique_id) => {
                write!(formatter, "Duplicate rewrite-order UNIQUE_ID '{unique_id}'")
            }
            Self::MissingRewriteOrderIds(unique_ids) => write!(
                formatter,
                "Rewrite order is missing executable UNIQUE_ID{}: {}",
                if unique_ids.len() == 1 { "" } else { "s" },
                unique_ids.join(", ")
            ),
            Self::DuplicateName { name, .. } => write!(formatter, "Duplicated name: {name}."),
            Self::DuplicateParameter(parameter) => {
                write!(formatter, "Duplicate sort parameter '{parameter}'")
            }
            Self::UnknownSort(sort) => write!(formatter, "Unknown sort '{sort}'"),
            Self::UnknownSymbol(symbol) => write!(formatter, "Unknown symbol '{symbol}'"),
            Self::WrongSortArity {
                sort,
                expected,
                actual,
            } => write!(
                formatter,
                "Sort '{sort}' expected {expected} parameters but got {actual}"
            ),
            Self::WrongSortArgumentCount {
                symbol,
                expected,
                actual,
            } => write!(
                formatter,
                "Symbol '{symbol}' expected {expected} sort arguments but got {actual}"
            ),
            Self::WrongSymbolArity {
                symbol,
                expected,
                actual,
            } => write!(
                formatter,
                "Symbol '{symbol}' expected {expected} arguments but got {actual}"
            ),
            Self::WrongAliasSortArgumentCount {
                alias,
                expected,
                actual,
            } => write!(
                formatter,
                "Alias '{alias}' expected {expected} sort arguments but got {actual}"
            ),
            Self::WrongAliasArity {
                alias,
                expected,
                actual,
            } => write!(
                formatter,
                "Alias '{alias}' expected {expected} arguments but got {actual}"
            ),
            Self::IncorrectArgumentSort {
                symbol,
                index,
                expected,
                actual,
            } => write!(
                formatter,
                "Argument {index} of symbol '{symbol}' expected sort {expected} but got {actual}"
            ),
            Self::NotSubsort { source, target } => {
                write!(formatter, "{source} is not a subsort of {target}")
            }
            Self::UnlicensedInjection {
                source,
                target,
                axiom,
                ..
            } => write!(
                formatter,
                "Unlicensed injection from {source} to {target} in axiom {axiom}"
            ),
            Self::InvalidSymbolType(symbol) => {
                write!(formatter, "Invalid type for symbol '{symbol}'")
            }
            Self::ConstructorAtFixedSort { symbol, sort } => write!(
                formatter,
                "Constructor {symbol} is applied at sort {sort}, which is hooked or has domain values."
            ),
            Self::InvalidSortParameter => write!(formatter, "Invalid sort parameter"),
            Self::MalformedAttribute(attribute) => {
                write!(formatter, "Malformed attribute: {attribute}")
            }
            Self::MalformedCollection(error) => {
                write!(formatter, "Malformed collection: {error}")
            }
            Self::MalformedAlias(error) => write!(formatter, "Malformed alias: {error}"),
            Self::AliasCycle(aliases) => {
                write!(formatter, "Alias cycle: {}", aliases.join(" -> "))
            }
            Self::AliasUnfoldingTooLarge { added, available } => {
                write!(
                    formatter,
                    "Unfolding the aliases would add {added} nodes and name bytes, more than the {available} left of what alias unfolding may add: the larger of {} and {} times the size of the patterns supplied by the operation that unfolds them",
                    crate::alias::UNFOLDING_LIMIT,
                    crate::alias::UNFOLDING_FACTOR
                )
            }
            Self::MacroOrAliasInImplication(symbol) => {
                write!(
                    formatter,
                    "A symbol cannot be an alias or a macro: '{symbol}'"
                )
            }
            Self::MacroOrAliasInExecutablePattern(symbol) => write!(
                formatter,
                "invalid executable input: macro or alias symbol '{symbol}' survived expansion"
            ),
            Self::PredicateInTermPosition { count } => write!(
                formatter,
                "predicate in term position ({count} floated conjuncts) where a term is required"
            ),
            Self::SortWithoutDomainValues { sort } => write!(
                formatter,
                "Sort {sort} used with a domain value must have the hasDomainValues attribute."
            ),
            Self::InvalidDomainValue { sort, value } => {
                write!(formatter, "Invalid domain value {value:?} for sort {sort}")
            }
            Self::ExpectedTerm(pattern) => {
                write!(
                    formatter,
                    "Pattern not supported where a term is required: {pattern}"
                )
            }
            Self::EmptyAssociativeApplication(symbol) => {
                write!(formatter, "Associative symbol '{symbol}' has no arguments")
            }
            Self::VariableName { name, set } => {
                let problems = variable_name_problems(name, *set)
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join("; ");
                let kind = if *set { "set" } else { "element" };
                write!(
                    formatter,
                    "Invalid {kind} variable name '{name}': {problems}"
                )
            }
            Self::InsufficientStack {
                depth,
                required,
                limit,
            } => write!(
                formatter,
                "Patterns and sorts nested {depth} levels deep need about {required} bytes of stack, more than the {limit} bytes the backend provides for one operation"
            ),
            Self::StackSegmentRefused { depth, refused } => write!(
                formatter,
                "Patterns and sorts nested {depth} levels deep need about {} bytes of stack, and {refused}",
                refused.size
            ),
            Self::Axiom(error) => write!(formatter, "Invalid axiom: {error:?}"),
            Self::RulePattern(error) => write!(formatter, "Invalid rule pattern: {error:?}"),
            Self::Claim(error) => write!(formatter, "Invalid claim: {error:?}"),
            Self::Verification(error) => write!(formatter, "{error}"),
        }
    }
}

impl Error for DefinitionError {}

/// The backend variable a KORE variable denotes: its name verbatim, at `sort`.
///
/// Only a KORE identifier is accepted as a name (`@` and an identifier for a set variable). No
/// identifier contains `#` or `!`, the characters every name the backend makes from another
/// one adds (`term::names`), so no variable read from KORE is ever a rule variable or a mint
/// of the backend, whatever it is spelled.
fn read_variable(variable: &kore::Variable, sort: Sort) -> Result<Variable, DefinitionError> {
    let set = variable.kind == kore::VariableKind::Set;
    if !variable_name_problems(&variable.name, set).is_empty() {
        return Err(DefinitionError::VariableName {
            name: variable.name.clone(),
            set,
        });
    }
    Ok(if set {
        Variable::set(variable.name.as_str(), sort)
    } else {
        Variable::new(variable.name.as_str(), sort)
    })
}

impl From<MalformedAttribute> for DefinitionError {
    /// `"{name} must contain one string"` and `"{name} must contain one nullary symbol"`, the
    /// two texts this crate has always rendered.
    fn from(malformed: MalformedAttribute) -> Self {
        Self::MalformedAttribute(format!(
            "{} must contain {}",
            malformed.attribute.as_str(),
            malformed.expected
        ))
    }
}

impl crate::nesting::Unfolding for BackendDefinition {
    fn alias_height(&self, name: &str) -> Option<usize> {
        self.aliases.get(name).map(|alias| alias.height)
    }

    /// An associative application of a collection symbol folds its entries into one flat
    /// collection; only the arguments that are not an element or unit of the collection can
    /// stay as the collection's opaque rest, a chain of binary concatenations. Any other
    /// symbol folds into a chain of binary applications, one per argument.
    fn associative_levels(&self, symbol: &kore::Symbol, arguments: &[kore::Pattern]) -> usize {
        let Some(collection) = self
            .symbols
            .get(symbol.name.as_str())
            .and_then(|symbol| symbol.attributes.collection.as_ref())
        else {
            return arguments.len();
        };
        let symbols = match collection {
            CollectionMetadata::Map(definition) => &definition.symbols,
            CollectionMetadata::List(definition) | CollectionMetadata::Set(definition) => {
                &definition.symbols
            }
        };
        let opaque = arguments
            .iter()
            .filter(|argument| {
                !matches!(
                    argument,
                    kore::Pattern::Application { symbol, .. }
                        if *symbols.element == *symbol.name || *symbols.unit == *symbol.name
                )
            })
            .count();
        1 + opaque
    }
}

/// Drops the parts of a definition that hold its internal terms and sorts on a stack measured
/// for them, as loading built them on (`nesting`): their destruction recurses once per level.
impl Drop for BackendDefinition {
    fn drop(&mut self) {
        let parts = (
            std::mem::take(&mut self.symbols),
            std::mem::take(&mut self.sort_graph),
            std::mem::take(&mut self.overloads),
            std::mem::take(&mut self.axioms),
            std::mem::take(&mut self.classified_axioms),
            std::mem::take(&mut self.claims),
            std::mem::take(&mut self.reachability_claims),
            std::mem::take(&mut self.rewrite_theory),
            std::mem::take(&mut self.function_theory),
            std::mem::take(&mut self.simplification_theory),
            std::mem::take(&mut self.predicate_simplification_theory),
            std::mem::take(&mut self.predicate_theory_by_connective),
            std::mem::take(&mut self.ceil_theory),
            std::mem::take(&mut self.finite_sort_constructors),
            std::mem::take(&mut self.inhabited_sorts),
        );
        // A refusal drops the parts here, on the current stack. Only a definition deeper than
        // any segment holds is refused, and only a thread with more stack than that loads one.
        let _ = crate::nesting::with_stack(self.deepest, move || drop(parts));
    }
}

impl BackendDefinition {
    /// The aliases of the definition, by name.
    #[cfg(test)]
    pub(crate) fn aliases(&self) -> &BTreeMap<String, AliasDefinition> {
        &self.aliases
    }

    /// The depth that the recursive passes of an operation over `patterns` in this definition
    /// descend to, as counted by `nesting::height`: the deepest of the patterns with its aliases
    /// unfolded, above the deepest pattern of the definition, since a rule of the definition
    /// can place the operation's terms below its own.
    pub fn operation_depth(&self, patterns: &[&kore::Pattern]) -> usize {
        patterns
            .iter()
            .map(|pattern| crate::nesting::height(pattern, self))
            .max()
            .unwrap_or(0)
            .saturating_add(self.deepest)
    }

    /// Run `work`, an operation of this definition over `patterns`, with everything it does to
    /// them and to the internal terms built from them, on a stack that holds the recursion
    /// over [`Self::operation_depth`] levels (`nesting::with_stack`). The work's result must
    /// hold no internal term built from `patterns`, since it is dropped outside that stack.
    pub fn with_stack_for<R>(
        &self,
        patterns: &[&kore::Pattern],
        work: impl FnOnce() -> R,
    ) -> Result<R, DefinitionError> {
        crate::nesting::with_stack(self.operation_depth(patterns), work)
    }
}

/// The equation-head applications written strictly below the root of the left-hand side of an
/// executable function, simplification or ceil equation that denote one ground term, grouped by
/// that term, each written application once, in the order a depth-first walk of the theories
/// meets them: the subterms equation matching may read as values
/// (`BackendDefinition::record_pattern_tokens`).
///
/// An application denotes one ground term when it is ground once each `\and` in it is replaced
/// by its structured conjunct (`confluence::collapse_conjunctions`): a left-hand side may name a
/// subterm with a variable, `\and(1, X)`, to reuse it on its right-hand side, and an instance of
/// the conjunction is an instance of each conjunct, so the application has at most the one value
/// of the collapsed term. The walk keeps its pending subterms on a work list.
fn ground_equation_head_patterns(definition: &BackendDefinition) -> Vec<(Term, Vec<Term>)> {
    let mut seen = rustc_hash::FxHashSet::default();
    let mut groups: Vec<(Term, Vec<Term>)> = Vec::new();
    let mut group_of = rustc_hash::FxHashMap::default();
    let mut work: Vec<&Term> = Vec::new();
    let theories = [
        &definition.function_theory,
        &definition.simplification_theory,
        &definition.ceil_theory,
    ];
    for rule in theories
        .into_iter()
        .flat_map(BTreeMap::values)
        .flat_map(BTreeMap::values)
        .flatten()
    {
        work.extend(crate::term::immediate_children(rule.lhs.kind()));
        while let Some(term) = work.pop() {
            if term.shape() == crate::term::head::Shape::Application(HeadRole::EquationHead) {
                if !seen.insert(term) {
                    continue;
                }
                let value = if term.attributes().variables.is_empty() {
                    term.clone()
                } else {
                    crate::confluence::collapse_conjunctions(term)
                };
                if value.attributes().variables.is_empty() {
                    let group = *group_of.entry(value.clone()).or_insert_with(|| {
                        groups.push((value, Vec::new()));
                        groups.len() - 1
                    });
                    groups[group].1.push(term.clone());
                }
            }
            work.extend(crate::term::immediate_children(term.kind()));
        }
    }
    groups
}

impl BackendDefinition {
    /// After the check, record in the verdict an instance-normal token for each equation-head
    /// application written below the root of an executable equation's left-hand side that
    /// denotes one ground term, when that term has one (`confluence::ValueClaims::pattern_token`).
    /// Equation matching reads a recorded application as the value it denotes
    /// (`term::head::RecordedPatterns`), so that a ground normal form is compared by the same
    /// evidence whether the equation writes it or the subject holds it.
    ///
    /// A ground term is its own only instance, so its token is a fact about the one value it
    /// denotes, the fact the scan establishes for an equal subject. The root of a left-hand side
    /// is not recorded: it is compared with the application the equation is tried on, which has
    /// its symbol, by its arguments.
    ///
    /// The scan of a term matches the left-hand sides of the equations that could reach it, and
    /// those may hold applications of this record, so a token recorded here can let the scan of
    /// another term find it normal. A recorded token only adds refutations to equation
    /// matching, never removes one, so a term the scan found normal stays normal as the record
    /// grows. The record is therefore built in rounds, each scanning the terms not yet recorded
    /// against the record so far, until a round records nothing. Then the scan, run against the
    /// final record, finds every recorded term normal and no other one: what the pattern side
    /// reads of a ground term is what the subject side reads of it. With `g` such terms, there
    /// are at most `r + 1` rounds for `r` recorded ones, and at most `g` scans per round.
    fn record_pattern_tokens(&mut self) {
        let mut pending = ground_equation_head_patterns(self);
        while !pending.is_empty() {
            let mut recorded = Vec::new();
            let mut rest = Vec::new();
            for (value, written) in pending {
                match self.instance_normal(&value) {
                    Some(token) => recorded.push((written, token)),
                    None => rest.push((value, written)),
                }
            }
            if recorded.is_empty() {
                break;
            }
            for (written, token) in recorded {
                for pattern in written {
                    self.value_claims.record_pattern_token(pattern, token);
                }
            }
            pending = rest;
        }
    }

    /// Discharge rewrite annotations only after the semantic input has been assembled.
    ///
    /// ```toml algorithm-site
    /// id = "backend.definedness.discharge"
    /// role = "part"
    /// sites = ["BackendDefinition::discharge_rewrite_definedness"]
    /// ```
    fn discharge_rewrite_definedness(&mut self) {
        let _span = measure::algorithm_span(Algorithm::BackendDefinedness);
        let mut discharged = Vec::new();
        {
            let definition: &BackendDefinition = self;
            for (index, groups) in &definition.rewrite_theory {
                for (priority, rules) in groups {
                    for (position, rule) in rules.iter().enumerate() {
                        discharged.push((
                            index.clone(),
                            *priority,
                            position,
                            crate::definedness::rule_is_defined(definition, &rule.rule),
                        ));
                    }
                }
            }
        }

        for (index, priority, position, is_defined) in discharged {
            if !is_defined {
                continue;
            }
            let rule = Arc::make_mut(
                &mut self
                    .rewrite_theory
                    .get_mut(&index)
                    .expect("indexed rewrite group should remain present")
                    .get_mut(&priority)
                    .expect("indexed rewrite priority should remain present")[position]
                    .rule,
            );
            rule.attributes.preserves_definedness = true;
            rule.computed_attributes.undefined_symbols.clear();
        }
    }

    /// The stored main module of this semantic snapshot.
    #[inline]
    pub fn main_module(&self) -> &Name {
        &self.main_module
    }

    /// The stored modules of this semantic snapshot.
    #[inline]
    pub fn modules(&self) -> &BTreeSet<Name> {
        &self.modules
    }

    /// The stored sorts of this semantic snapshot.
    #[inline]
    pub fn sorts(&self) -> &BTreeMap<Name, SortInfo> {
        &self.sorts
    }

    /// The stored symbols of this semantic snapshot.
    #[inline]
    pub fn symbols(&self) -> &BTreeMap<Name, Arc<Symbol>> {
        &self.symbols
    }

    /// The stored sort graph of this semantic snapshot.
    #[inline]
    pub fn sort_graph(&self) -> &SortGraph {
        &self.sort_graph
    }

    /// The stored overloads of this semantic snapshot.
    #[inline]
    pub fn overloads(&self) -> &OverloadGraph {
        &self.overloads
    }

    /// The stored axioms of this semantic snapshot.
    #[inline]
    pub fn axioms(&self) -> &[PendingAxiom] {
        &self.axioms
    }

    /// The stored classified axioms of this semantic snapshot.
    #[inline]
    pub fn classified_axioms(&self) -> &[ClassifiedAxiom] {
        &self.classified_axioms
    }

    /// The stored claims of this semantic snapshot.
    #[inline]
    pub fn claims(&self) -> &[PendingAxiom] {
        &self.claims
    }

    /// The stored reachability claims of this semantic snapshot.
    #[inline]
    pub fn reachability_claims(&self) -> &[ReachabilityClaim] {
        &self.reachability_claims
    }

    /// The stored rewrite theory of this semantic snapshot.
    #[inline]
    pub fn rewrite_theory(&self) -> &RewriteTheory {
        &self.rewrite_theory
    }

    /// The stored ceil theory of this semantic snapshot.
    #[inline]
    pub fn ceil_theory(&self) -> &Theory {
        &self.ceil_theory
    }

    /// Whether the definition declares `symbol` `impure`: its applications are effects, which
    /// must be performed in order, not values that may be computed whenever they are needed.
    pub(crate) fn is_impure(&self, symbol: &Name) -> bool {
        self.impure_symbols.contains(symbol)
    }

    /// Whether `term` is an application of a `value-production` symbol that no equation of the
    /// definition reduces, on any instance, so that the application is defined wherever its
    /// arguments are.
    ///
    /// `value-production` states that an application no equation reduces is a value of its
    /// sort. Evidence that no equation reduces the application is either the simplifier's
    /// certificate on a ground normal form (`term::head::certified_ground_normal_form`) or
    /// instance normality (`instance_normal`): every equation equation selection could offer the
    /// application or one of its instances fails to unify with it or to match it. Both are
    /// minted only at an index the load-time critical-pair check leaves untainted
    /// (`confluence::ValueClaims::admit`), where the definition's normal-form model is a model of
    /// it, so the application is an element there. Either holds for every valuation, so the
    /// answer does not depend on a path condition. Without the marker an equation head claims
    /// nothing about its irreducible applications, and a conditional equation whose left-hand
    /// side reaches the application withholds both kinds of evidence, so the answer is `false`
    /// there (`docs/compatibility.md`, "Anywhere rules").
    pub(crate) fn irreducible_application_is_defined(&self, term: &Term) -> bool {
        let TermKind::Application { symbol, .. } = term.kind() else {
            return false;
        };
        self.value_productions.contains(&symbol.name)
            && (crate::term::head::certified_ground_normal_form(term)
                || self.instance_normal(term).is_some())
    }

    /// Names of the symbols declared with the KORE `function` attribute whose role is a function
    /// ([`HeadRole::Function`]); a declared function that is also a macro or alias, or also a
    /// constructor or sort injection, has another role.
    pub fn function_symbol_names(&self) -> BTreeSet<String> {
        self.symbols
            .iter()
            .filter(|(_, symbol)| {
                matches!(
                    symbol.attributes.head_role(),
                    HeadRole::Function { declared: true, .. }
                )
            })
            .map(|(name, _)| name.to_string())
            .collect()
    }

    pub fn internalize(
        definition: &kore::Definition,
        main_module: &str,
    ) -> Result<Self, DefinitionError> {
        Self::internalize_with_added(definition, main_module, &BTreeSet::new())
    }

    /// Internalizes `definition` at `main_module`, where each module named in `added` was added
    /// to the definition by an operation of its own after the rest of it was given
    /// ([`crate::session::BackendSession::add_module`]).
    ///
    /// Unfolding the aliases of an axiom is charged to the operation that supplied the axiom:
    /// the axioms of the modules given with the definition share one budget relative to their
    /// size, and those of each added module one relative to that module's own size
    /// (`alias::UnfoldingBudget`), so what an addition may make the backend build is bounded by
    /// what it sent, however large the definition it extends.
    pub(crate) fn internalize_with_added(
        definition: &kore::Definition,
        main_module: &str,
        added: &BTreeSet<&str>,
    ) -> Result<Self, DefinitionError> {
        let _span = measure::algorithm_span(Algorithm::BackendDefinitionInternalize);
        Self::internalize_canonical(definition, main_module, added)
    }

    /// Internalizes a definition and orders semantic rewrites by their stable identifiers.
    ///
    /// This is the source-compiled execution boundary: the frontend supplies the order from its
    /// transformed definition before KORE emission structurally sorts the rules. Function,
    /// simplification, predicate, and definedness theories keep declaration order. Every
    /// executable rewrite must have exactly one entry; extra frontend entries are accepted.
    pub fn internalize_for_source_execution<T: AsRef<str>>(
        definition: &kore::Definition,
        main_module: &str,
        rewrite_order: &[T],
    ) -> Result<Self, DefinitionError> {
        let mut result = Self::internalize(definition, main_module)?;
        let mut ranks = BTreeMap::new();
        for (rank, unique_id) in rewrite_order.iter().enumerate() {
            let unique_id = unique_id.as_ref();
            if ranks.insert(unique_id, rank).is_some() {
                return Err(DefinitionError::DuplicateRewriteOrderId(
                    unique_id.to_owned(),
                ));
            }
        }
        let missing = result
            .rewrite_theory
            .values()
            .flat_map(BTreeMap::values)
            .flatten()
            .filter(|stored| !ranks.contains_key(stored.rule.attributes.unique_id.as_str()))
            .map(|stored| stored.rule.attributes.unique_id.clone())
            .collect::<BTreeSet<_>>();
        if !missing.is_empty() {
            return Err(DefinitionError::MissingRewriteOrderIds(
                missing.into_iter().collect(),
            ));
        }
        for priority_groups in result.rewrite_theory.values_mut() {
            for rules in priority_groups.values_mut() {
                rules.sort_by_key(|stored| {
                    ranks
                        .get(stored.rule.attributes.unique_id.as_str())
                        .copied()
                        .expect("all executable rewrites were checked above")
                });
            }
        }
        Ok(result)
    }

    #[deny(clippy::wildcard_enum_match_arm)]
    fn internalize_canonical(
        definition: &kore::Definition,
        main_module: &str,
        added: &BTreeSet<&str>,
    ) -> Result<Self, DefinitionError> {
        let mut module_map = BTreeMap::new();
        for module in &definition.modules {
            if module_map.insert(module.name.as_str(), module).is_some() {
                return Err(DefinitionError::DuplicateModule(module.name.clone()));
            }
        }

        let mut visiting = Vec::new();
        let mut visited = BTreeSet::new();
        let mut ordered = Vec::new();
        let mut preorder = Vec::new();
        visit_module(
            main_module,
            &module_map,
            &mut visiting,
            &mut visited,
            &mut ordered,
            &mut preorder,
        )?;
        // Every later pass recurses over the sentences, with their aliases unfolded, and over
        // the internal terms built from them, so each runs on a stack measured for what it
        // descends through before it starts (`nesting`): the declarations here, each axiom and
        // claim where it is verified, and the passes after verification all of them.
        let alias_heights = crate::nesting::alias_heights(ordered.iter().flat_map(|module| {
            module
                .sentences
                .iter()
                .filter_map(|sentence| match sentence {
                    kore::Sentence::AliasDeclaration { alias, right, .. } => {
                        Some((alias.name.as_str(), right.as_ref()))
                    }
                    kore::Sentence::Import { .. }
                    | kore::Sentence::SortDeclaration { .. }
                    | kore::Sentence::SymbolDeclaration { .. }
                    | kore::Sentence::Axiom { .. }
                    | kore::Sentence::Claim { .. } => None,
                })
        }));
        let unfolding = crate::nesting::Aliases(&alias_heights);
        let declared = crate::nesting::declarations_height(&ordered, &unfolding);
        crate::nesting::with_stack(declared, || {
            Self::internalize_modules(
                definition,
                &preorder,
                main_module,
                added,
                &ordered,
                &alias_heights,
                declared,
            )
        })
        .and_then(|loaded| loaded)
        .map_err(|error| {
            // A definition deeper than any stack the backend provides cannot be loaded, whatever
            // else is wrong with it, so that is the error it is refused with, as a request is
            // (`with_stack_for`). The passes before verification measure only what they
            // descend through, and they or the verification of an earlier sentence can fail
            // before the deepest sentence is measured, so the whole definition is measured here,
            // only on that failure path.
            crate::nesting::refusal(crate::nesting::definition_height(&ordered, &unfolding))
                .unwrap_or(error)
        })
    }

    #[deny(clippy::wildcard_enum_match_arm)]
    fn internalize_modules(
        definition: &kore::Definition,
        preorder: &[&kore::Module],
        main_module: &str,
        added: &BTreeSet<&str>,
        ordered: &[&kore::Module],
        alias_heights: &BTreeMap<String, usize>,
        declared: usize,
    ) -> Result<Self, DefinitionError> {
        let aliases = collect_aliases(ordered, alias_heights)?;

        let mut sorts = BTreeMap::new();
        for module in ordered {
            for sentence in &module.sentences {
                let kore::Sentence::SortDeclaration {
                    name,
                    parameters,
                    attributes,
                    ..
                } = sentence
                else {
                    continue;
                };
                reject_duplicates(parameters)?;
                let collection = collection_sort(attributes)?;
                let info = SortInfo {
                    parameters: parameters.iter().cloned().map(Into::into).collect(),
                    hook: attributes.string(KoreAttribute::Hook)?.map(Into::into),
                    has_domain_values: attributes.has(KoreAttribute::HasDomainValues),
                    collection,
                };
                if sorts.insert(Name::from(name.as_str()), info).is_some() {
                    return Err(DefinitionError::DuplicateSort(name.clone()));
                }
            }
        }
        validate_alias_declarations(ordered, &sorts)?;

        let mut algebraic_facts = BTreeMap::<Name, AlgebraicAxioms>::new();
        for module in ordered {
            for sentence in &module.sentences {
                let kore::Sentence::Axiom {
                    pattern,
                    attributes,
                    ..
                } = sentence
                else {
                    continue;
                };
                if let Some(facts) = algebraic_axiom_roots(pattern, attributes) {
                    let (facts, roots) = facts.map_err(DefinitionError::Axiom)?;
                    for root in roots {
                        let entry = algebraic_facts.entry(root).or_default();
                        *entry = entry.union(facts);
                    }
                }
            }
        }

        let mut symbols = BTreeMap::new();
        for module in ordered {
            for sentence in &module.sentences {
                let kore::Sentence::SymbolDeclaration {
                    symbol,
                    argument_sorts,
                    result_sort,
                    attributes,
                    ..
                } = sentence
                else {
                    continue;
                };
                let sort_variables = symbol
                    .sort_parameters
                    .iter()
                    .map(|sort| match sort {
                        kore::Sort::Variable(name) => Ok(Name::from(name.as_str())),
                        kore::Sort::Application { .. } => {
                            Err(DefinitionError::InvalidSortParameter)
                        }
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                reject_name_duplicates(&sort_variables)?;
                let known = sort_variables.iter().cloned().collect();
                let argument_sorts = argument_sorts
                    .iter()
                    .map(|sort| internalize_sort(sort, &sorts, &known))
                    .collect::<Result<Vec<_>, _>>()?;
                let result_sort = internalize_sort(result_sort, &sorts, &known)?;
                let facts = algebraic_facts
                    .get(symbol.name.as_str())
                    .copied()
                    .unwrap_or_default();
                let attributes = symbol_attributes(symbol.name.as_str(), attributes, facts)?;
                validate_binder_attribute(&attributes, &argument_sorts, &sorts)?;
                let internal = Arc::new(Symbol {
                    name: symbol.name.as_str().into(),
                    sort_variables,
                    argument_sorts,
                    result_sort,
                    attributes,
                });
                if symbols
                    .insert(Name::from(symbol.name.as_str()), internal)
                    .is_some()
                {
                    return Err(DefinitionError::DuplicateSymbol(symbol.name.clone()));
                }
            }
        }

        attach_collection_metadata(&sorts, &mut symbols)?;
        let verified = crate::verify::verify_definition(
            ordered,
            &definition.modules,
            &sorts,
            &symbols,
            &aliases,
            &crate::nesting::Aliases(alias_heights),
        )?;
        let deepest = declared.max(verified);
        crate::nesting::with_stack(deepest, || {
            Self::internalize_axioms(
                preorder,
                main_module,
                added,
                ordered,
                sorts,
                symbols,
                aliases,
                deepest,
            )
        })?
    }

    /// The definition of the modules `ordered`, whose declarations have been read into `sorts`,
    /// `symbols`, and `aliases` and verified with its axioms and claims, built from those axioms
    /// and claims. Its patterns and sorts are at most `deepest` levels deep. The modules named in
    /// `added` were each added by an operation of their own ([`Self::internalize_with_added`]).
    #[deny(clippy::wildcard_enum_match_arm)]
    #[allow(clippy::too_many_arguments)]
    fn internalize_axioms(
        preorder: &[&kore::Module],
        main_module: &str,
        added: &BTreeSet<&str>,
        ordered: &[&kore::Module],
        sorts: BTreeMap<Name, SortInfo>,
        symbols: BTreeMap<Name, Arc<Symbol>>,
        aliases: BTreeMap<String, AliasDefinition>,
        deepest: usize,
    ) -> Result<Self, DefinitionError> {
        let mut axioms = Vec::new();
        let mut claims = Vec::new();
        let mut subsorts = Vec::new();
        let mut overloads = Vec::new();
        let rule_orders = ordered
            .iter()
            .map(|module| (module.name.as_str(), rule_sentence_indices(module)))
            .collect::<BTreeMap<_, _>>();
        let mut axiom_sentences = Vec::new();
        // Unfolding is charged to the operation that supplied each axiom: the axioms of the
        // modules given with the definition are unfolded together, within one budget relative to
        // their size, and those of each added module within one relative to its own size.
        let (added_modules, given_modules): (Vec<&kore::Module>, Vec<&kore::Module>) = ordered
            .iter()
            .copied()
            .partition(|module| added.contains(module.name.as_str()));
        let mut given_unfolding = UnfoldingBudget::for_modules(&given_modules);
        let mut added_unfolding = added_modules
            .into_iter()
            .map(|module| {
                (
                    module.name.as_str(),
                    UnfoldingBudget::for_modules(&[module]),
                )
            })
            .collect::<BTreeMap<_, _>>();
        // A module's axioms and claims are its sentences however many import paths reach it, so
        // each module is read once, in the order the main module's imports first reach it.
        for &module in preorder {
            let unfolding = match added_unfolding.get_mut(module.name.as_str()) {
                Some(budget) => budget,
                None => &mut given_unfolding,
            };
            for &index in &rule_orders[module.name.as_str()] {
                let sentence = &module.sentences[index];
                let (target, parameters, pattern, attributes, expand) = match sentence {
                    kore::Sentence::Axiom {
                        parameters,
                        pattern,
                        attributes,
                    } => (&mut axioms, parameters, pattern, attributes, true),
                    kore::Sentence::Claim {
                        parameters,
                        pattern,
                        attributes,
                    } => (&mut claims, parameters, pattern, attributes, false),
                    kore::Sentence::Import { .. }
                    | kore::Sentence::SortDeclaration { .. }
                    | kore::Sentence::SymbolDeclaration { .. }
                    | kore::Sentence::AliasDeclaration { .. } => continue,
                };
                reject_duplicates(parameters)?;
                if let Some((sub, sup)) = subsort_attribute(pattern, attributes, &sorts)? {
                    subsorts.push((sub, sup));
                }
                if let Some(overload) = overload_attribute(attributes)? {
                    overloads.push(overload);
                }
                if expand {
                    axiom_sentences.push((Name::from(module.name.as_str()), index));
                }
                target.push(PendingAxiom {
                    module: module.name.as_str().into(),
                    parameters: parameters.iter().cloned().map(Into::into).collect(),
                    pattern: if expand {
                        expand_aliases_within(pattern, &aliases, unfolding)?.into_owned()
                    } else {
                        (**pattern).clone()
                    },
                    attributes: attributes.clone(),
                });
            }
        }

        let (classified_axioms, axiom_sentences): (Vec<_>, Vec<_>) = collapse_equal_axioms(
            axioms
                .iter()
                .zip(axiom_sentences)
                .filter_map(|(axiom, sentence)| {
                    classify_axiom(
                        axiom.module.clone(),
                        axiom.parameters.clone(),
                        &axiom.pattern,
                        &axiom.attributes,
                    )
                    .map(|classified| classified.map(|classified| (classified, sentence)))
                    .transpose()
                })
                .collect::<Result<Vec<_>, _>>()
                .map_err(DefinitionError::Axiom)?,
        )
        .into_iter()
        .unzip();
        let sort_graph = build_sort_graph(&sorts, subsorts);
        for (greater, lesser) in &overloads {
            if !symbols.contains_key(greater) {
                return Err(DefinitionError::UnknownSymbol(greater.to_string()));
            }
            if !symbols.contains_key(lesser) {
                return Err(DefinitionError::UnknownSymbol(lesser.to_string()));
            }
        }
        let overloads = OverloadGraph::from_relations(overloads)?;
        let declared_with = |attribute: KoreAttribute| -> BTreeSet<Name> {
            ordered
                .iter()
                .flat_map(|module| &module.sentences)
                .filter_map(|sentence| match sentence {
                    kore::Sentence::SymbolDeclaration {
                        symbol, attributes, ..
                    } => attributes
                        .has(attribute)
                        .then(|| Name::from(symbol.name.as_str())),
                    kore::Sentence::Import { .. }
                    | kore::Sentence::SortDeclaration { .. }
                    | kore::Sentence::AliasDeclaration { .. }
                    | kore::Sentence::Axiom { .. }
                    | kore::Sentence::Claim { .. } => None,
                })
                .collect()
        };
        let value_productions = declared_with(KoreAttribute::ValueProduction);
        let impure_symbols = declared_with(KoreAttribute::Impure);
        let mut result = Self {
            main_module: main_module.into(),
            modules: ordered
                .iter()
                .map(|module| Name::from(module.name.as_str()))
                .collect(),
            sorts,
            symbols,
            aliases,
            sort_graph,
            overloads,
            axioms,
            classified_axioms,
            claims,
            reachability_claims: Vec::new(),
            rewrite_theory: RewriteTheory::new(),
            function_theory: Theory::new(),
            simplification_theory: Theory::new(),
            predicate_simplification_theory: PredicateTheory::new(),
            predicate_theory_by_connective: FxHashMap::default(),
            ceil_theory: Theory::new(),
            value_productions,
            impure_symbols,
            finite_sort_constructors: BTreeMap::new(),
            kvar_sorts: OnceLock::new(),
            inhabited_sorts: OnceLock::new(),
            value_claims: crate::confluence::ValueClaims::withheld(),
            term_equation_in_predicate_theory: false,
            deepest,
            #[cfg(feature = "check-normal-forms")]
            normal_form_catalog: OnceLock::new(),
        };
        let rules = result
            .classified_axioms
            .iter()
            .zip(axiom_sentences)
            .filter(|(axiom, _)| match axiom {
                ClassifiedAxiom::Rewrite { attributes, .. }
                | ClassifiedAxiom::Function { attributes, .. }
                | ClassifiedAxiom::Simplification { attributes, .. }
                | ClassifiedAxiom::Ceil { attributes, .. } => attributes.executable,
            })
            .map(|(axiom, sentence)| internalize_axiom(&result, axiom, &sentence))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten();
        for rule in rules {
            match rule {
                InternalizedRule::Term(RuleKind::Rewrite, rule) => {
                    let index = rule_index(&result, &rule.lhs);
                    insert_rewrite_theory(&mut result.rewrite_theory, rule, index);
                }
                InternalizedRule::Term(kind, rule) => {
                    let theory = match kind {
                        RuleKind::Function => &mut result.function_theory,
                        RuleKind::Simplification => &mut result.simplification_theory,
                        RuleKind::Ceil => &mut result.ceil_theory,
                        RuleKind::Rewrite => unreachable!("rewrite handled above"),
                    };
                    insert_theory(theory, rule);
                }
                InternalizedRule::Predicate(rule) => {
                    result
                        .predicate_simplification_theory
                        .entry(rule.attributes.priority)
                        .or_default()
                        .push(Arc::new(rule));
                }
            }
        }
        result.reachability_claims = result
            .claims
            .iter()
            .map(|claim| internalize_reachability_claim(&result, claim))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect();
        result.term_equation_in_predicate_theory = result
            .predicate_simplification_theory
            .values()
            .flatten()
            .any(|rule| has_term_component(&rule.lhs));
        for (priority, rules) in &result.predicate_simplification_theory {
            for rule in rules {
                result
                    .predicate_theory_by_connective
                    .entry(std::mem::discriminant(&rule.lhs))
                    .or_default()
                    .entry(*priority)
                    .or_default()
                    .push(Arc::clone(rule));
            }
        }
        result.finite_sort_constructors = collect_finite_sort_constructors(&result)?;
        // The check runs while the definition still withholds every claim, and before the
        // rewrite rules' definedness is discharged, which reads the claims.
        #[cfg(test)]
        {
            let switches = crate::confluence::switches::active();
            if switches.claims_during_check || switches.discharge_before_check {
                result.value_claims = crate::confluence::ValueClaims::admitting_everything();
            }
            if switches.discharge_before_check {
                result.discharge_rewrite_definedness();
            }
        }
        result.value_claims = crate::confluence::check(
            &result,
            crate::confluence::CheckScope::Gate,
            crate::confluence::ConditionMemo::On,
        );
        result.record_pattern_tokens();
        result.discharge_rewrite_definedness();
        Ok(result)
    }

    /// The verdict of the load-time critical-pair check: which term indexes may carry value
    /// claims, and the pairs that withdrew the others (`confluence`).
    pub fn value_claims(&self) -> &crate::confluence::ValueClaims {
        &self.value_claims
    }

    /// The verdict of the critical-pair check run again in `scope`, on a copy of this definition
    /// that withholds every claim while it runs, as the load does. The load runs
    /// [`crate::confluence::CheckScope::Gate`]; [`crate::confluence::CheckScope::All`] also
    /// classifies the pairs that can change no claim, for a report of every pair that does not
    /// join and for the test that both scopes admit the same claims
    /// ([`crate::confluence::ValueClaims::claim_differences`]).
    #[must_use]
    pub fn value_claims_in_scope(
        &self,
        scope: crate::confluence::CheckScope,
    ) -> crate::confluence::ValueClaims {
        self.value_claims_checked(scope, crate::confluence::ConditionMemo::On)
    }

    /// [`Self::value_claims_in_scope`], with the check's memo of condition simplifications on or
    /// off ([`crate::confluence::ConditionMemo`]; every load runs it on), for the tests that show
    /// the memo changes no verdict and no count but the simplifier's calls.
    #[must_use]
    pub fn value_claims_checked(
        &self,
        scope: crate::confluence::CheckScope,
        memo: crate::confluence::ConditionMemo,
    ) -> crate::confluence::ValueClaims {
        let mut copy = self.clone();
        copy.value_claims = crate::confluence::ValueClaims::withheld();
        crate::confluence::check(&copy, scope, memo)
    }

    /// Test builds: this definition with every value claim withheld, as while its check runs, so
    /// that a test can compare what the evaluator decides without claims with what it decides
    /// with them.
    #[cfg(test)]
    pub(crate) fn with_claims_withheld(&self) -> Self {
        let mut copy = self.clone();
        copy.value_claims = crate::confluence::ValueClaims::withheld();
        copy
    }

    /// Returns the equations for function applications.
    pub fn function_theory(&self) -> &Theory {
        &self.function_theory
    }

    /// Returns the simplification equations indexed by term head.
    pub fn simplification_theory(&self) -> &Theory {
        &self.simplification_theory
    }

    /// Returns simplification rules whose left-hand sides are predicates.
    ///
    /// The three theories are fixed by `internalize`, and `equation_selection_complete` is
    /// computed from them, so even a caller holding `&mut BackendDefinition` only reads them:
    ///
    /// ```
    /// use k_rust_backend::definition::BackendDefinition;
    /// fn inspect(definition: &mut BackendDefinition) {
    ///     let _ = definition.predicate_simplification_theory().len();
    /// }
    /// ```
    ///
    /// ```compile_fail
    /// use k_rust_backend::definition::BackendDefinition;
    /// fn inspect(definition: &mut BackendDefinition) {
    ///     definition.predicate_simplification_theory.clear();
    /// }
    /// ```
    pub fn predicate_simplification_theory(&self) -> &PredicateTheory {
        &self.predicate_simplification_theory
    }

    /// The predicate equations whose left-hand side has the top connective of `predicate`, by
    /// priority: the only ones that can match it.
    pub(crate) fn predicate_equations_for(
        &self,
        predicate: &Predicate,
    ) -> Option<&PredicateTheory> {
        self.predicate_theory_by_connective
            .get(&std::mem::discriminant(predicate))
    }

    /// Whether the term simplifier's equation selection (`rule::applicable_groups` on
    /// `rule::term_index`) offers an application every equation of the definition whose
    /// left-hand side could match it. Selection offers the function and simplification equations
    /// indexed by the application's symbol, plus those indexed by a bare variable.
    ///
    /// Two shapes of term equation escape it; a definition holding either gives no evaluated
    /// mark (`Term::with_evaluated_cache`):
    ///
    /// - A simplification axiom whose left-hand side is not a term pattern (an `\and` of term
    ///   patterns) is filed in `predicate_simplification_theory` as a predicate over those terms.
    ///   The term simplifier never tries it, yet it states an equation between terms.
    ///   Internalization records this. kompile does not emit it for anywhere or overload
    ///   equations, but hand-written KORE (RPC, library callers) can.
    /// - A term-theory entry indexed `TermIndex::And`. Internalization never produces one:
    ///   function equations need an application left-hand side, and a conjunction goes to the
    ///   predicate theory.
    ///
    /// Every other left-hand side fails to match an application it is not offered to. A head of
    /// another symbol is refuted by equation matching. So is a domain value, an injection, or a
    /// collection against a concrete subject.
    #[must_use]
    pub(crate) fn equation_selection_complete(&self) -> Option<SelectionComplete> {
        (!self.term_equation_in_predicate_theory
            && !self.function_theory.contains_key(&TermIndex::And)
            && !self.simplification_theory.contains_key(&TermIndex::And))
        .then_some(SelectionComplete(()))
    }

    /// The term equations the normal-form checker tries (`term::head::check`), catalogued at most
    /// once per definition. The theories it reads are fixed by `internalize`, so the catalog
    /// cannot go stale.
    #[cfg(feature = "check-normal-forms")]
    pub(crate) fn normal_form_catalog(&self) -> &crate::term::head::check::Catalog {
        self.normal_form_catalog
            .get_or_init(|| crate::term::head::check::Catalog::of(self))
    }

    /// The may-contain-`KVar` sort fact, a least fixpoint computed at most once per definition.
    pub(crate) fn kvar_sorts(&self) -> &KVarSorts {
        self.kvar_sorts.get_or_init(|| KVarSorts::of(self))
    }

    /// Whether `sort` is known to have at least one value.
    ///
    /// The known-inhabited sorts are the least fixed point of: a hooked sort, a sort with domain
    /// values, and a collection sort (it has its empty collection) are inhabited; the result sort
    /// of a constructor or total function without sort parameters is inhabited when every
    /// argument sort is, since applying it to values of those sorts denotes a value; and a
    /// supersort of an inhabited sort is inhabited through the injection. A sort outside the
    /// fixed point and a sort with a sort variable answer false; a closed instance is analysed
    /// like any sort. Instances of a hooked or domain-value parametric constructor are not
    /// inhabited by declaration alone: which instances have values is the hook's to say.
    pub(crate) fn sort_is_inhabited(&self, sort: &Sort) -> bool {
        self.inhabited_sorts
            .get_or_init(|| inhabited_sorts(self))
            .contains(sort)
    }

    /// I5: every value of `sort` is covered by an alternative of a complete no-junk axiom.
    /// Returns no domain if an `EquationHead` can build the sort: its normal form may keep
    /// that root, which no listed constructor head covers.
    pub(crate) fn finite_constructor_heads(&self, sort: &Sort) -> Option<&FiniteConstructorDomain> {
        self.finite_sort_constructors.get(sort)
    }

    pub(crate) fn internalize_term(
        &self,
        pattern: &kore::Pattern,
        sort_variables: &[Name],
    ) -> Result<Term, DefinitionError> {
        let _span = measure::algorithm_span(Algorithm::BackendDefinitionInternalize);
        self.internalize_term_with_validation(
            pattern,
            sort_variables,
            UnlicensedInjectionSite::Refuse,
        )
    }

    fn injection_licensed(
        &self,
        source: &Sort,
        target: &Sort,
        role: UnlicensedInjectionSite,
    ) -> bool {
        match role {
            UnlicensedInjectionSite::Refuse => self
                .sort_graph
                .check_subsort(source, target)
                .unwrap_or(false),
            UnlicensedInjectionSite::InAxiom | UnlicensedInjectionSite::InAxiomMatched => {
                match self.sort_graph.check_subsort(source, target) {
                    Ok(licensed) => licensed,
                    Err(SortError::FoundSortVariable(_)) => true,
                    Err(_) => false,
                }
            }
        }
    }

    pub(crate) fn internalize_term_with_validation(
        &self,
        pattern: &kore::Pattern,
        sort_variables: &[Name],
        injection_role: UnlicensedInjectionSite,
    ) -> Result<Term, DefinitionError> {
        let mut floated = Vec::new();
        let term = self.internalize_term_collecting(
            pattern,
            sort_variables,
            injection_role,
            &mut floated,
            None,
        )?;
        if !floated.is_empty() {
            return Err(DefinitionError::PredicateInTermPosition {
                count: floated.len(),
            });
        }
        Ok(term)
    }

    pub(crate) fn internalize_term_collecting(
        &self,
        pattern: &kore::Pattern,
        sort_variables: &[Name],
        injection_role: UnlicensedInjectionSite,
        floated: &mut Vec<crate::rule::Predicate>,
        deferred_predicates: Option<&mut Vec<kore::Pattern>>,
    ) -> Result<Term, DefinitionError> {
        let known = sort_variables.iter().cloned().collect::<BTreeSet<_>>();
        let pattern = expand_aliases(pattern, &self.aliases)?;
        self.internalize_term_with(
            &pattern,
            &known,
            injection_role,
            floated,
            deferred_predicates,
        )
    }

    /// Internalize a constrained KORE pattern into its term and predicate components.
    pub(crate) fn internalize_pattern(
        &self,
        pattern: &kore::Pattern,
        sort_variables: &[Name],
    ) -> Result<Pattern, DefinitionError> {
        let _span = measure::algorithm_span(Algorithm::BackendDefinitionInternalize);
        let pattern = expand_aliases(pattern, &self.aliases)?;
        let (term, constraints) = internalize_rule_pattern(
            self,
            &pattern,
            sort_variables,
            UnlicensedInjectionSite::Refuse,
        )?;
        Ok(Pattern { term, constraints })
    }

    /// Internalize KORE as a constrained term, or as a predicate when it has no term leaf.
    pub(crate) fn internalize_pattern_or_predicate(
        &self,
        pattern: &kore::Pattern,
        sort_variables: &[Name],
    ) -> Result<PatternOrPredicate, DefinitionError> {
        match self.internalize_pattern(pattern, sort_variables) {
            Ok(pattern) => Ok(PatternOrPredicate::Term(pattern)),
            Err(DefinitionError::RulePattern(RulePatternError::MissingTerm)) => {
                let (predicate, sort) = self.internalize_predicate(pattern, sort_variables)?;
                Ok(PatternOrPredicate::Predicate(predicate, sort))
            }
            Err(error) => Err(error),
        }
    }

    /// Verify a standalone KORE pattern under `sort_variables` and admit it to internalization.
    ///
    /// Well-formedness is relative to the declared sort variables: the pattern's sort variables
    /// are parameters of the query, and one outside `sort_variables` is an error. The witness
    /// carries the same `sort_variables`, so the pattern is internalized under the context it was
    /// verified under.
    pub fn verify_standalone_pattern<'a>(
        &'a self,
        pattern: &'a kore::Pattern,
        sort_variables: &'a [Name],
    ) -> Result<Admitted<'a>, DefinitionError> {
        crate::verify::verify_standalone(
            &self.main_module,
            pattern,
            &self.sorts,
            &self.symbols,
            &self.aliases,
            sort_variables,
        )
        .map_err(DefinitionError::Verification)?;
        Ok(Admitted {
            definition: self,
            pattern,
            sort_variables,
            admission: Admission::Verified,
        })
    }

    /// Admit a KORE pattern to internalization under `sort_variables` without standalone
    /// verification.
    ///
    /// Internalization still rejects undeclared heads and sorts, arity and sort mismatches, and
    /// domain values at sorts without domain values; the standalone verifier's further checks,
    /// such as one sort per variable name, are not made.
    pub fn admit_unverified<'a>(
        &'a self,
        pattern: &'a kore::Pattern,
        sort_variables: &'a [Name],
    ) -> Admitted<'a> {
        Admitted {
            definition: self,
            pattern,
            sort_variables,
            admission: Admission::Unverified,
        }
    }

    /// Internalize an arbitrary KORE pattern as an ML predicate and retain its result sort.
    pub(crate) fn internalize_predicate(
        &self,
        pattern: &kore::Pattern,
        sort_variables: &[Name],
    ) -> Result<(crate::rule::Predicate, Sort), DefinitionError> {
        let pattern = expand_aliases(pattern, &self.aliases)?;
        let known = sort_variables.iter().cloned().collect::<BTreeSet<_>>();
        let result_sort = self.internalize_pattern_result_sort(
            &pattern,
            &known,
            UnlicensedInjectionSite::Refuse,
        )?;
        let predicate = internalize_rule_predicate(
            self,
            &pattern,
            sort_variables,
            UnlicensedInjectionSite::Refuse,
        )?;
        Ok((predicate, result_sort))
    }

    /// Extract the predicate portion used by the backend get-model operation.
    pub(crate) fn internalize_model_predicate(
        &self,
        pattern: &kore::Pattern,
        sort_variables: &[Name],
    ) -> Result<Option<(crate::rule::Predicate, Sort)>, DefinitionError> {
        let pattern = expand_aliases(pattern, &self.aliases)?;
        let known = sort_variables.iter().cloned().collect::<BTreeSet<_>>();
        let result_sort = self.internalize_pattern_result_sort(
            &pattern,
            &known,
            UnlicensedInjectionSite::Refuse,
        )?;
        Ok(internalize_rule_model_predicate(
            self,
            &pattern,
            sort_variables,
            UnlicensedInjectionSite::Refuse,
        )?
        .map(|predicate| (predicate, result_sort)))
    }

    /// Internalize one side of an implication, peeling its leading existential binders.
    pub(crate) fn internalize_implication_pattern(
        &self,
        pattern: &kore::Pattern,
        sort_variables: &[Name],
    ) -> Result<(Pattern, BTreeSet<Variable>), DefinitionError> {
        self.validate_implication_pattern(pattern)?;
        let pattern = expand_aliases(pattern, &self.aliases)?;
        let mut body = &*pattern;
        let mut existentials = BTreeSet::new();
        while let kore::Pattern::Exists {
            variable,
            body: next,
            ..
        } = body
        {
            existentials.insert(self.internalize_variable(variable, sort_variables)?);
            body = next;
        }
        let (term, constraints) =
            internalize_rule_pattern(self, body, sort_variables, UnlicensedInjectionSite::Refuse)?;
        Ok((Pattern { term, constraints }, existentials))
    }

    /// Reject syntax that the implication RPC boundary does not permit.
    pub fn validate_implication_pattern(
        &self,
        pattern: &kore::Pattern,
    ) -> Result<(), DefinitionError> {
        if let Some(name) = self.macro_or_alias_in_pattern(pattern) {
            Err(DefinitionError::MacroOrAliasInImplication(name))
        } else {
            Ok(())
        }
    }

    /// Reject preprocessing symbols before executable KORE is internalized.
    ///
    /// Alias internalization expands alias applications, so callers that execute a raw pattern
    /// must validate it first to preserve the invalid-input boundary.
    pub fn validate_executable_pattern(
        &self,
        pattern: &kore::Pattern,
    ) -> Result<(), DefinitionError> {
        if let Some(name) = self.macro_or_alias_in_pattern(pattern) {
            Err(DefinitionError::MacroOrAliasInExecutablePattern(name))
        } else {
            Ok(())
        }
    }

    fn macro_or_alias_in_pattern(&self, pattern: &kore::Pattern) -> Option<String> {
        let mut pending = vec![pattern];
        // Each pop pushes only proper subpatterns of the popped one, so the loop terminates.
        // Invariant: `pending` holds exactly the subpatterns not yet inspected.
        while let Some(pattern) = pending.pop() {
            match pattern {
                kore::Pattern::Application { symbol, arguments }
                | kore::Pattern::AssociativeApplication {
                    symbol, arguments, ..
                } => {
                    if self.aliases.contains_key(&symbol.name)
                        || self
                            .symbols
                            .get(symbol.name.as_str())
                            .is_some_and(|symbol| symbol.attributes.macro_or_alias)
                    {
                        return Some(symbol.name.clone());
                    }
                    pending.extend(arguments.iter().rev());
                }
                kore::Pattern::And { arguments, .. } | kore::Pattern::Or { arguments, .. } => {
                    pending.extend(arguments.iter().rev());
                }
                kore::Pattern::Not { argument, .. }
                | kore::Pattern::Next { argument, .. }
                | kore::Pattern::Ceil { argument, .. }
                | kore::Pattern::Floor { argument, .. } => pending.push(argument),
                kore::Pattern::Implies { left, right, .. }
                | kore::Pattern::Iff { left, right, .. }
                | kore::Pattern::Rewrites { left, right, .. }
                | kore::Pattern::Equals { left, right, .. }
                | kore::Pattern::In { left, right, .. } => {
                    pending.push(right);
                    pending.push(left);
                }
                kore::Pattern::Exists { body, .. }
                | kore::Pattern::Forall { body, .. }
                | kore::Pattern::Mu { body, .. }
                | kore::Pattern::Nu { body, .. } => pending.push(body),
                kore::Pattern::String(_)
                | kore::Pattern::Variable(_)
                | kore::Pattern::Top { .. }
                | kore::Pattern::Bottom { .. }
                | kore::Pattern::DomainValue { .. } => {}
            }
        }
        None
    }

    /// Internalize the alternatives of a top-level KORE disjunction.
    pub(crate) fn internalize_disjunction(
        &self,
        pattern: &kore::Pattern,
        sort_variables: &[Name],
    ) -> Result<Vec<Pattern>, DefinitionError> {
        let pattern = expand_aliases(pattern, &self.aliases)?;
        crate::rule::term_disjuncts(&pattern)
            .into_iter()
            .map(|alternative| {
                let (term, constraints) = internalize_rule_pattern(
                    self,
                    &alternative,
                    sort_variables,
                    UnlicensedInjectionSite::Refuse,
                )?;
                Ok(Pattern { term, constraints })
            })
            .collect()
    }

    pub(crate) fn internalize_syntax_sort(
        &self,
        sort: &kore::Sort,
        sort_variables: &[Name],
    ) -> Result<Sort, DefinitionError> {
        let known = sort_variables.iter().cloned().collect::<BTreeSet<_>>();
        internalize_sort(sort, &self.sorts, &known)
    }

    pub(crate) fn internalize_variable(
        &self,
        variable: &kore::Variable,
        sort_variables: &[Name],
    ) -> Result<Variable, DefinitionError> {
        let sort = self.internalize_syntax_sort(&variable.sort, sort_variables)?;
        read_variable(variable, sort)
    }

    fn internalize_term_with(
        &self,
        pattern: &kore::Pattern,
        sort_variables: &BTreeSet<Name>,
        injection_role: UnlicensedInjectionSite,
        floated: &mut Vec<crate::rule::Predicate>,
        mut deferred_predicates: Option<&mut Vec<kore::Pattern>>,
    ) -> Result<Term, DefinitionError> {
        match pattern {
            kore::Pattern::String(value) => Ok(Term::domain_value(
                Sort::builtin(BuiltinSort::String),
                value.clone(),
            )),
            kore::Pattern::Variable(variable) => {
                let sort = internalize_sort(&variable.sort, &self.sorts, sort_variables)?;
                Ok(Term::variable(read_variable(variable, sort)?))
            }
            kore::Pattern::Application { symbol, arguments } => {
                self.validate_application_shape(symbol, arguments.len())?;
                let arguments = arguments
                    .iter()
                    .map(|argument| {
                        self.internalize_term_with(
                            argument,
                            sort_variables,
                            injection_role,
                            floated,
                            deferred_predicates.as_deref_mut(),
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                self.internalize_application(symbol, arguments, sort_variables, injection_role)
            }
            kore::Pattern::DomainValue { sort, value } => {
                let sort = internalize_sort(sort, &self.sorts, sort_variables)?;
                self.validate_domain_value(&sort, value)?;
                Ok(Term::domain_value(sort, value.clone()))
            }
            kore::Pattern::And { arguments, .. } => {
                let (terms, predicates): (Vec<_>, Vec<_>) = arguments
                    .iter()
                    .partition(|argument| crate::rule::contains_term_component(argument));
                let sort_variables = sort_variables.iter().cloned().collect::<Vec<_>>();
                for predicate in predicates {
                    if let Some(deferred) = deferred_predicates.as_deref_mut() {
                        deferred.push(predicate.clone());
                    } else {
                        floated.push(internalize_rule_predicate(
                            self,
                            predicate,
                            &sort_variables,
                            injection_role,
                        )?);
                    }
                }
                let known = sort_variables.iter().cloned().collect::<BTreeSet<_>>();
                let mut arguments = terms
                    .into_iter()
                    .map(|argument| {
                        self.internalize_term_with(
                            argument,
                            &known,
                            injection_role,
                            floated,
                            deferred_predicates.as_deref_mut(),
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let Some(mut result) = arguments.pop() else {
                    return Err(DefinitionError::ExpectedTerm("top"));
                };
                // Invariant: `result` is the conjunction of the arguments popped so far.
                while let Some(left) = arguments.pop() {
                    result = Term::and(left, result);
                }
                Ok(result)
            }
            kore::Pattern::AssociativeApplication {
                associativity,
                symbol,
                arguments,
            } => {
                let arguments = arguments
                    .iter()
                    .map(|argument| {
                        self.internalize_term_with(
                            argument,
                            sort_variables,
                            injection_role,
                            floated,
                            deferred_predicates.as_deref_mut(),
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let mut iter: Box<dyn Iterator<Item = Term>> = match associativity {
                    kore::Associativity::Left => Box::new(arguments.into_iter()),
                    kore::Associativity::Right => Box::new(arguments.into_iter().rev()),
                };
                let Some(mut result) = iter.next() else {
                    return Err(DefinitionError::EmptyAssociativeApplication(
                        symbol.name.clone(),
                    ));
                };
                for argument in iter {
                    let pair = match associativity {
                        kore::Associativity::Left => vec![result, argument],
                        kore::Associativity::Right => vec![argument, result],
                    };
                    result =
                        self.internalize_application(symbol, pair, sort_variables, injection_role)?;
                }
                Ok(result)
            }
            kore::Pattern::Top { .. } => Err(DefinitionError::ExpectedTerm("top")),
            kore::Pattern::Bottom { .. } => Err(DefinitionError::ExpectedTerm("bottom")),
            kore::Pattern::Or { .. } => Err(DefinitionError::ExpectedTerm("or")),
            kore::Pattern::Not { .. } => Err(DefinitionError::ExpectedTerm("not")),
            kore::Pattern::Next { .. } => Err(DefinitionError::ExpectedTerm("next")),
            kore::Pattern::Implies { .. } => Err(DefinitionError::ExpectedTerm("implies")),
            kore::Pattern::Iff { .. } => Err(DefinitionError::ExpectedTerm("iff")),
            kore::Pattern::Rewrites { .. } => Err(DefinitionError::ExpectedTerm("rewrites")),
            kore::Pattern::Exists { .. } => Err(DefinitionError::ExpectedTerm("exists")),
            kore::Pattern::Forall { .. } => Err(DefinitionError::ExpectedTerm("forall")),
            kore::Pattern::Mu { .. } => Err(DefinitionError::ExpectedTerm("mu")),
            kore::Pattern::Nu { .. } => Err(DefinitionError::ExpectedTerm("nu")),
            kore::Pattern::Ceil { .. } => Err(DefinitionError::ExpectedTerm("ceil")),
            kore::Pattern::Floor { .. } => Err(DefinitionError::ExpectedTerm("floor")),
            kore::Pattern::Equals { .. } => Err(DefinitionError::ExpectedTerm("equals")),
            kore::Pattern::In { .. } => Err(DefinitionError::ExpectedTerm("in")),
        }
    }

    fn validate_domain_value(
        &self,
        sort: &Sort,
        value: &kore::KoreString,
    ) -> Result<(), DefinitionError> {
        let Sort::Application { name, .. } = sort else {
            return Err(DefinitionError::SortWithoutDomainValues {
                sort: Box::new(externalize::sort(sort)),
            });
        };
        let Some(info) = self.sorts.get(name) else {
            return Err(DefinitionError::UnknownSort(name.to_string()));
        };
        if !info.has_domain_values {
            return Err(DefinitionError::SortWithoutDomainValues {
                sort: Box::new(externalize::sort(sort)),
            });
        }
        let text = value.as_utf8().ok();
        if info.hook.as_deref() == Some("BOOL.Bool") && !matches!(text, Some("true" | "false")) {
            return Err(DefinitionError::InvalidDomainValue {
                sort: Box::new(externalize::sort(sort)),
                value: text.map_or_else(|| kore_string::quote(value), str::to_owned),
            });
        }
        if info.hook.as_deref() == Some("INT.Int") && !text.is_some_and(is_decimal_integer) {
            return Err(DefinitionError::InvalidDomainValue {
                sort: Box::new(externalize::sort(sort)),
                value: text.map_or_else(|| kore_string::quote(value), str::to_owned),
            });
        }
        Ok(())
    }

    fn validate_application_shape(
        &self,
        syntax: &kore::Symbol,
        argument_count: usize,
    ) -> Result<(), DefinitionError> {
        let symbol = self
            .symbols
            .get(syntax.name.as_str())
            .ok_or_else(|| DefinitionError::UnknownSymbol(syntax.name.clone()))?;
        if syntax.sort_parameters.len() != symbol.sort_variables.len() {
            return Err(DefinitionError::WrongSortArgumentCount {
                symbol: syntax.name.clone(),
                expected: symbol.sort_variables.len(),
                actual: syntax.sort_parameters.len(),
            });
        }
        if argument_count != symbol.argument_sorts.len() {
            return Err(DefinitionError::WrongSymbolArity {
                symbol: syntax.name.clone(),
                expected: symbol.argument_sorts.len(),
                actual: argument_count,
            });
        }
        Ok(())
    }

    fn internalize_pattern_result_sort(
        &self,
        pattern: &kore::Pattern,
        sort_variables: &BTreeSet<Name>,
        injection_role: UnlicensedInjectionSite,
    ) -> Result<Sort, DefinitionError> {
        let syntax_sort = match pattern {
            kore::Pattern::Variable(variable) => Some(&variable.sort),
            kore::Pattern::Top { sort }
            | kore::Pattern::Bottom { sort }
            | kore::Pattern::Not { sort, .. }
            | kore::Pattern::Next { sort, .. }
            | kore::Pattern::And { sort, .. }
            | kore::Pattern::Or { sort, .. }
            | kore::Pattern::Rewrites { sort, .. }
            | kore::Pattern::Implies { sort, .. }
            | kore::Pattern::Iff { sort, .. }
            | kore::Pattern::Exists { sort, .. }
            | kore::Pattern::Forall { sort, .. } => Some(sort),
            kore::Pattern::Ceil { result_sort, .. }
            | kore::Pattern::Floor { result_sort, .. }
            | kore::Pattern::Equals { result_sort, .. }
            | kore::Pattern::In { result_sort, .. } => Some(result_sort),
            kore::Pattern::Mu { variable, .. } | kore::Pattern::Nu { variable, .. } => {
                Some(&variable.sort)
            }
            kore::Pattern::DomainValue { sort, .. } => Some(sort),
            kore::Pattern::String(_) => return Ok(Sort::builtin(BuiltinSort::String)),
            kore::Pattern::Application { .. } | kore::Pattern::AssociativeApplication { .. } => {
                None
            }
        };
        match syntax_sort {
            Some(sort) => internalize_sort(sort, &self.sorts, sort_variables),
            None => Ok(self
                .internalize_term_with_validation(
                    pattern,
                    &sort_variables.iter().cloned().collect::<Vec<_>>(),
                    injection_role,
                )?
                .sort()),
        }
    }

    /// Build a symbol application after alias expansion, rejecting constructor-schema
    /// instances at sorts whose values are fixed by a hook or domain values.
    fn internalize_application(
        &self,
        syntax: &kore::Symbol,
        arguments: Vec<Term>,
        sort_variables: &BTreeSet<Name>,
        injection_role: UnlicensedInjectionSite,
    ) -> Result<Term, DefinitionError> {
        let symbol = self
            .symbols
            .get(syntax.name.as_str())
            .ok_or_else(|| DefinitionError::UnknownSymbol(syntax.name.clone()))?
            .clone();
        if syntax.sort_parameters.len() != symbol.sort_variables.len() {
            return Err(DefinitionError::WrongSortArgumentCount {
                symbol: syntax.name.clone(),
                expected: symbol.sort_variables.len(),
                actual: syntax.sort_parameters.len(),
            });
        }
        if arguments.len() != symbol.argument_sorts.len() {
            return Err(DefinitionError::WrongSymbolArity {
                symbol: syntax.name.clone(),
                expected: symbol.argument_sorts.len(),
                actual: arguments.len(),
            });
        }
        let sort_arguments = syntax
            .sort_parameters
            .iter()
            .map(|sort| internalize_sort(sort, &self.sorts, sort_variables))
            .collect::<Result<Vec<_>, _>>()?;
        let substitution = symbol
            .sort_variables
            .iter()
            .cloned()
            .zip(sort_arguments.iter().cloned())
            .collect::<BTreeMap<_, _>>();
        if symbol.attributes.declares_constructor()
            && matches!(symbol.result_sort, Sort::Variable(_))
        {
            let result = substitute_sort(&symbol.result_sort, &substitution);
            if let Sort::Application { name, .. } = &result
                && self
                    .sorts
                    .get(name)
                    .is_some_and(|info| info.hook.is_some() || info.has_domain_values)
            {
                return Err(DefinitionError::ConstructorAtFixedSort {
                    symbol: syntax.name.clone(),
                    sort: Box::new(externalize::sort(&result)),
                });
            }
        }
        if syntax.is(WellKnownSymbol::Inj)
            && let [source, target] = sort_arguments.as_slice()
            && !self.injection_licensed(source, target, injection_role)
        {
            return Err(DefinitionError::NotSubsort {
                source: Box::new(externalize::sort(source)),
                target: Box::new(externalize::sort(target)),
            });
        }
        // An injection `inj{S, T}(t)` is an application whose argument sort is `S`, so its
        // operand is checked like every other argument: an operand of any other sort, a strict
        // subsort of `S` included, is refused on every route, as the verifier refuses it.
        for (index, (expected, argument)) in symbol
            .argument_sorts
            .iter()
            .map(|sort| substitute_sort(sort, &substitution))
            .zip(&arguments)
            .enumerate()
        {
            let actual = argument.sort();
            if expected != actual {
                return Err(DefinitionError::IncorrectArgumentSort {
                    symbol: syntax.name.clone(),
                    index,
                    expected: Box::new(externalize::sort(&expected)),
                    actual: Box::new(externalize::sort(&actual)),
                });
            }
        }
        Ok(Term::application(symbol, sort_arguments, arguments))
    }
}

fn is_decimal_integer(value: &str) -> bool {
    let digits = value.strip_prefix(['+', '-']).unwrap_or(value).as_bytes();
    !digits.is_empty() && digits.iter().all(u8::is_ascii_digit)
}

/// The least fixed point described at [`BackendDefinition::sort_is_inhabited`]; each round
/// scans the symbols and subsort sets once, and a round that adds no sort ends the iteration.
fn inhabited_sorts(definition: &BackendDefinition) -> BTreeSet<ClosedSort> {
    let mut inhabited = definition
        .sorts
        .iter()
        .filter(|(_, info)| {
            info.parameters.is_empty()
                && (info.hook.is_some() || info.has_domain_values || info.collection.is_some())
        })
        .map(|(name, _)| ClosedSort::simple(name.clone()))
        .collect::<BTreeSet<_>>();
    let builders = definition
        .symbols
        .values()
        .filter(|symbol| {
            symbol.sort_variables.is_empty()
                && matches!(
                    symbol.attributes.symbol_type,
                    SymbolType::Constructor | SymbolType::Function(FunctionType::Total)
                )
        })
        .filter_map(|symbol| {
            let result = ClosedSort::new(symbol.result_sort.clone()).ok()?;
            let arguments = symbol
                .argument_sorts
                .iter()
                .map(|sort| ClosedSort::new(sort.clone()).ok())
                .collect::<Option<Vec<_>>>()?;
            Some((result, arguments))
        })
        .collect::<Vec<_>>();
    // Invariant: `inhabited` holds only sorts shown to have a value; a round that adds none ends.
    loop {
        let before = inhabited.len();
        for (result, arguments) in &builders {
            if !inhabited.contains(result)
                && arguments
                    .iter()
                    .all(|argument| inhabited.contains(argument))
            {
                inhabited.insert(result.clone());
            }
        }
        for (supersort, below) in definition.sort_graph.closures() {
            if !inhabited.contains(supersort) && below.iter().any(|sort| inhabited.contains(sort)) {
                inhabited.insert(supersort.clone());
            }
        }
        if inhabited.len() == before {
            return inhabited;
        }
    }
}

fn collect_finite_sort_constructors(
    definition: &BackendDefinition,
) -> Result<BTreeMap<Sort, FiniteConstructorDomain>, DefinitionError> {
    let index = FixedRootSymbols::of(definition);
    let mut domains = BTreeMap::new();
    for axiom in &definition.axioms {
        if !axiom.attributes.has(KoreAttribute::Constructor) {
            continue;
        }
        let mut alternatives = Vec::new();
        flatten_or(&axiom.pattern, &mut alternatives);
        if alternatives.len() < 2 {
            continue;
        }
        let mut domain_sort = None;
        let mut constructors = BTreeSet::new();
        let mut has_bottom = false;
        let mut valid = true;
        for alternative in alternatives {
            match alternative {
                kore::Pattern::Bottom { sort } => {
                    let Ok(sort) = definition.internalize_syntax_sort(sort, &axiom.parameters)
                    else {
                        valid = false;
                        break;
                    };
                    has_bottom = true;
                    if domain_sort.get_or_insert_with(|| sort.clone()) != &sort {
                        valid = false;
                        break;
                    }
                }
                alternative => {
                    let mut constructor = alternative;
                    let mut binders = BTreeSet::new();
                    while let kore::Pattern::Exists { variable, body, .. } = constructor {
                        let Ok(sort) =
                            definition.internalize_syntax_sort(&variable.sort, &axiom.parameters)
                        else {
                            valid = false;
                            break;
                        };
                        binders.insert(read_variable(variable, sort)?);
                        constructor = body;
                    }
                    if !valid {
                        break;
                    }
                    let Ok(term) = definition.internalize_term_with_validation(
                        constructor,
                        &axiom.parameters,
                        UnlicensedInjectionSite::Refuse,
                    ) else {
                        valid = false;
                        break;
                    };
                    let Some(head) = constructor_head(&term) else {
                        valid = false;
                        break;
                    };
                    if !term.attributes().variables.is_subset(&binders) {
                        valid = false;
                        break;
                    }
                    let sort = term.sort();
                    if domain_sort.get_or_insert_with(|| sort.clone()) != &sort {
                        valid = false;
                        break;
                    }
                    constructors.insert(head);
                }
            }
        }
        if valid && has_bottom && !constructors.is_empty() {
            let sort = domain_sort.expect("a nonempty domain has a sort");
            if let Some(domain) = FiniteConstructorDomain::complete(&index, &sort, constructors) {
                domains.insert(sort, domain);
            }
        }
    }
    Ok(domains)
}

pub(crate) fn constructor_head(term: &Term) -> Option<ConstructorHead> {
    match term.kind() {
        TermKind::Application {
            symbol,
            sort_arguments,
            ..
        } if symbol.attributes.head_role() == HeadRole::FreeConstructor => {
            Some(ConstructorHead::Symbol {
                name: symbol.name.clone(),
                sort_arguments: sort_arguments.clone(),
            })
        }
        TermKind::Injection { source, target, .. } => Some(ConstructorHead::Injection {
            source: source.clone(),
            target: target.clone(),
        }),
        _ => None,
    }
}

fn flatten_or<'a>(pattern: &'a kore::Pattern, output: &mut Vec<&'a kore::Pattern>) {
    if let kore::Pattern::Or { arguments, .. } = pattern {
        for argument in arguments {
            flatten_or(argument, output);
        }
    } else {
        output.push(pattern);
    }
}

fn validate_alias_declarations(
    modules: &[&kore::Module],
    sorts: &BTreeMap<Name, SortInfo>,
) -> Result<(), DefinitionError> {
    for module in modules {
        for sentence in &module.sentences {
            let kore::Sentence::AliasDeclaration {
                alias,
                argument_sorts,
                result_sort,
                ..
            } = sentence
            else {
                continue;
            };
            let known = alias
                .sort_parameters
                .iter()
                .map(|sort| match sort {
                    kore::Sort::Variable(name) => Ok(Name::from(name.as_str())),
                    kore::Sort::Application { .. } => Err(DefinitionError::InvalidSortParameter),
                })
                .collect::<Result<BTreeSet<_>, _>>()?;
            for sort in argument_sorts.iter().chain([result_sort]) {
                internalize_sort(sort, sorts, &known)?;
            }
        }
    }
    Ok(())
}

/// Visits the modules `name` reaches, each once: `ordered` lists them in postorder (a module
/// after the modules it imports), `preorder` in the order the imports, read in declaration
/// order, first reach them.
fn visit_module<'a>(
    name: &str,
    modules: &BTreeMap<&str, &'a kore::Module>,
    visiting: &mut Vec<String>,
    visited: &mut BTreeSet<String>,
    ordered: &mut Vec<&'a kore::Module>,
    preorder: &mut Vec<&'a kore::Module>,
) -> Result<(), DefinitionError> {
    if visited.contains(name) {
        return Ok(());
    }
    if let Some(start) = visiting.iter().position(|module| module == name) {
        let mut cycle = visiting[start..].to_vec();
        cycle.push(name.to_owned());
        return Err(DefinitionError::ImportCycle(cycle));
    }
    let module = modules
        .get(name)
        .copied()
        .ok_or_else(|| DefinitionError::NoSuchModule(name.to_owned()))?;
    visiting.push(name.to_owned());
    preorder.push(module);
    // A module found in `visiting` closes an import cycle; `visited` skips finished modules.
    // Invariant: `visiting` is the import path down to `name`; `visited` holds finished modules;
    // a module is in `preorder` exactly when it is in `visiting` or `visited`.
    for sentence in &module.sentences {
        if let kore::Sentence::Import { module, .. } = sentence {
            visit_module(module, modules, visiting, visited, ordered, preorder)?;
        }
    }
    visiting.pop();
    visited.insert(name.to_owned());
    ordered.push(module);
    Ok(())
}

/// Axiom and claim sentences of `module` in declaration order. Within one priority group the
/// backend tries rules in this order, main module first and imports depth-first in their written
/// order; which rule an engine follows among equal-priority rules is not a K contract
/// (docs/compatibility.md#search-results).
fn rule_sentence_indices(module: &kore::Module) -> Vec<usize> {
    module
        .sentences
        .iter()
        .enumerate()
        .filter(|(_, sentence)| {
            matches!(
                sentence,
                kore::Sentence::Axiom { .. } | kore::Sentence::Claim { .. }
            )
        })
        .map(|(index, _)| index)
        .collect()
}

pub(crate) fn internalize_sort(
    sort: &kore::Sort,
    sorts: &BTreeMap<Name, SortInfo>,
    variables: &BTreeSet<Name>,
) -> Result<Sort, DefinitionError> {
    match sort {
        kore::Sort::Variable(name) if variables.contains(name.as_str()) => {
            Ok(Sort::Variable(name.as_str().into()))
        }
        kore::Sort::Variable(name) => Err(DefinitionError::UnknownSort(name.clone())),
        kore::Sort::Application { name, arguments } => {
            let info = sorts
                .get(name.as_str())
                .ok_or_else(|| DefinitionError::UnknownSort(name.clone()))?;
            if arguments.len() != info.parameters.len() {
                return Err(DefinitionError::WrongSortArity {
                    sort: name.clone(),
                    expected: info.parameters.len(),
                    actual: arguments.len(),
                });
            }
            Ok(Sort::application(
                name.as_str(),
                arguments
                    .iter()
                    .map(|sort| internalize_sort(sort, sorts, variables))
                    .collect::<Result<Vec<_>, _>>()?,
            ))
        }
    }
}

pub(crate) fn substitute_sort(sort: &Sort, substitution: &BTreeMap<Name, Sort>) -> Sort {
    match sort {
        Sort::Variable(name) => substitution
            .get(name)
            .cloned()
            .unwrap_or_else(|| sort.clone()),
        Sort::Application { name, arguments } => Sort::application(
            name.clone(),
            arguments
                .iter()
                .map(|argument| substitute_sort(argument, substitution))
                .collect(),
        ),
    }
}

fn symbol_attributes(
    symbol_name: &str,
    attributes: &kore::Attributes,
    axiom_facts: AlgebraicAxioms,
) -> Result<SymbolAttributes, DefinitionError> {
    let constructor =
        attributes.has(KoreAttribute::Constructor) || attributes.has(KoreAttribute::SortInjection);
    let total = attributes.has(KoreAttribute::Total) || attributes.has(KoreAttribute::Functional);
    let function = attributes.has(KoreAttribute::Function);
    let evaluated_by_equations = [
        KoreAttribute::Anywhere,
        KoreAttribute::Macro,
        KoreAttribute::MacroRec,
        KoreAttribute::Alias,
        KoreAttribute::AliasRec,
    ]
    .into_iter()
    .any(|key| attributes.has(key));
    let symbol_type = if constructor {
        SymbolType::Constructor
    } else if total {
        SymbolType::Function(FunctionType::Total)
    } else if function || evaluated_by_equations {
        // A symbol evaluated by its equations without a totality claim is partial:
        // its applications carry definedness obligations.
        SymbolType::Function(FunctionType::Partial)
    } else {
        return Err(DefinitionError::InvalidSymbolType(format!(
            "attributes {attributes:?}"
        )));
    };
    let mut algebraic = axiom_facts;
    for (attribute, fact) in [
        (KoreAttribute::Assoc, AlgebraicAxioms::assoc()),
        (KoreAttribute::Comm, AlgebraicAxioms::comm()),
        (KoreAttribute::Idem, AlgebraicAxioms::idem()),
    ] {
        if attributes.has(attribute) {
            algebraic = algebraic.union(fact);
        }
    }
    if constructor && !algebraic.is_empty() {
        let claim = if attributes.has(KoreAttribute::SortInjection) {
            "sortInjection"
        } else {
            "constructor"
        };
        let facts = [
            ("assoc", AlgebraicAxioms::assoc()),
            ("comm", AlgebraicAxioms::comm()),
            ("idem", AlgebraicAxioms::idem()),
            ("unit", AlgebraicAxioms::unit()),
        ]
        .into_iter()
        .filter_map(|(name, fact)| (algebraic.union(fact) == algebraic).then_some(name))
        .collect::<Vec<_>>()
        .join(", ");
        return Err(DefinitionError::MalformedAttribute(format!(
            "symbol {symbol_name} is declared {claim} but algebraic axioms identify its applications: {facts}"
        )));
    }
    let smt_hook = attributes
        .string(KoreAttribute::SmtHook)?
        .map(str::to_owned);
    let smtlib = attributes.string(KoreAttribute::Smtlib)?.map(str::to_owned);
    let smt = if let Some(hook) = smt_hook {
        Some(SmtType::Hook(SExpr::parse(&hook).map_err(|error| {
            DefinitionError::MalformedAttribute(format!("invalid smt-hook {hook:?}: {error}"))
        })?))
    } else {
        smtlib.map(SmtType::Lib)
    };
    // Every field is named, so a new field of `SymbolAttributes` does not compile here until
    // the internalizer decides it from the declaration.
    Ok(SymbolDeclaration {
        symbol_type,
        declared_constructor: attributes.has(KoreAttribute::Constructor),
        anywhere: attributes.has(KoreAttribute::Anywhere),
        // A value production is single-valued, but its irreducible applications are values,
        // rather than stuck computations. `function` alone declares the computed role.
        declared_function: function && !attributes.has(KoreAttribute::ValueProduction),
        binder: attributes.has(KoreAttribute::Binder),
        injective: attributes.has(KoreAttribute::Injective),
        algebraic,
        macro_or_alias: attributes.has(KoreAttribute::Macro)
            || attributes.has(KoreAttribute::Alias),
        has_evaluators: !attributes.has(KoreAttribute::NoEvaluators),
        smt,
        hook: attributes.string(KoreAttribute::Hook)?.map(Into::into),
        // Both are decided once every sort is known (`attach_collection_metadata`).
        collection: None,
        result_collection: None,
    }
    .into())
}

fn validate_binder_attribute(
    attributes: &SymbolAttributes,
    argument_sorts: &[Sort],
    sorts: &BTreeMap<Name, SortInfo>,
) -> Result<(), DefinitionError> {
    if !attributes.binder {
        return Ok(());
    }
    if argument_sorts.len() < 2 {
        return Err(DefinitionError::MalformedAttribute(
            "Binder productions must have at least two nonterminals.".into(),
        ));
    }
    let Sort::Application { name, .. } = &argument_sorts[0] else {
        return Err(DefinitionError::MalformedAttribute(
            "First child of binder must have a sort with the 'KVAR.KVar' hook attribute.".into(),
        ));
    };
    if sorts
        .get(name)
        .and_then(|info| info.hook.as_deref())
        .and_then(HookName::parse)
        != Some(HookName {
            namespace: "KVAR",
            operation: "KVar",
        })
    {
        return Err(DefinitionError::MalformedAttribute(
            "First child of binder must have a sort with the 'KVAR.KVar' hook attribute.".into(),
        ));
    }
    Ok(())
}

fn collection_sort(
    attributes: &kore::Attributes,
) -> Result<Option<CollectionSort>, DefinitionError> {
    let element = attributes
        .nullary_symbol(KoreAttribute::Element)?
        .map(str::to_owned);
    let concat = attributes
        .nullary_symbol(KoreAttribute::Concat)?
        .map(str::to_owned);
    let unit = attributes
        .nullary_symbol(KoreAttribute::Unit)?
        .map(str::to_owned);
    let hook = attributes.string(KoreAttribute::Hook)?.map(str::to_owned);
    match (element, concat, unit, hook.as_deref()) {
        (None, None, None, _) => Ok(None),
        (Some(element), Some(concat), Some(unit), Some(hook)) => {
            let symbols = CollectionSymbols {
                unit: unit.into(),
                element: element.into(),
                concat: concat.into(),
            };
            match hook {
                "MAP.Map" => Ok(Some(CollectionSort::Map(symbols))),
                "LIST.List" => Ok(Some(CollectionSort::List(symbols))),
                "SET.Set" => Ok(Some(CollectionSort::Set(symbols))),
                _ => Ok(None),
            }
        }
        _ => Err(DefinitionError::MalformedCollection(
            "collection sorts require unit, element, concat, and a collection hook".into(),
        )),
    }
}

/// Builds each collection sort's description from its declaration, the one place a collection's
/// shape is constructed, and gives it to the sort's unit, element and concatenation symbols
/// (`collection`) and to every hooked symbol whose result sort is that sort
/// (`result_collection`): a value of the sort is built from its own symbols, whatever computes it.
fn attach_collection_metadata(
    sorts: &BTreeMap<Name, SortInfo>,
    symbols: &mut BTreeMap<Name, Arc<Symbol>>,
) -> Result<(), DefinitionError> {
    let mut metadata = BTreeMap::new();
    let mut by_sort = BTreeMap::new();
    for (sort_name, info) in sorts {
        let Some(collection) = &info.collection else {
            continue;
        };
        // The three attributes name one symbol each, fixing one collection sort; collection
        // terms carry that sort without arguments.
        if !info.parameters.is_empty() {
            return Err(DefinitionError::MalformedCollection(format!(
                "collection sort {sort_name} must have no sort parameters"
            )));
        }
        let (names, collection) = match collection {
            CollectionSort::Map(names) => {
                let element = symbols.get(&names.element).ok_or_else(|| {
                    DefinitionError::MalformedCollection(format!(
                        "missing map element symbol {}",
                        names.element
                    ))
                })?;
                let [
                    Sort::Application {
                        name: key_sort,
                        arguments: key_arguments,
                    },
                    Sort::Application {
                        name: value_sort,
                        arguments: value_arguments,
                    },
                ] = element.argument_sorts.as_slice()
                else {
                    return Err(DefinitionError::MalformedCollection(format!(
                        "map element symbol {} must take key and value sorts",
                        names.element
                    )));
                };
                if !key_arguments.is_empty() || !value_arguments.is_empty() {
                    return Err(DefinitionError::MalformedCollection(
                        "parametric map element sorts are not supported".into(),
                    ));
                }
                let definition = Arc::new(MapDefinition {
                    symbols: names.clone(),
                    key_sort: key_sort.clone(),
                    value_sort: value_sort.clone(),
                    map_sort: sort_name.clone(),
                });
                (names, CollectionMetadata::Map(definition))
            }
            CollectionSort::List(names) | CollectionSort::Set(names) => {
                let element = symbols.get(&names.element).ok_or_else(|| {
                    DefinitionError::MalformedCollection(format!(
                        "missing collection element symbol {}",
                        names.element
                    ))
                })?;
                let [
                    Sort::Application {
                        name: element_sort,
                        arguments,
                    },
                ] = element.argument_sorts.as_slice()
                else {
                    return Err(DefinitionError::MalformedCollection(format!(
                        "collection element symbol {} must take one sort",
                        names.element
                    )));
                };
                if !arguments.is_empty() {
                    return Err(DefinitionError::MalformedCollection(
                        "parametric collection element sorts are not supported".into(),
                    ));
                }
                let definition = Arc::new(ListDefinition {
                    symbols: names.clone(),
                    element_sort: element_sort.clone(),
                    list_sort: sort_name.clone(),
                });
                let collection = match collection {
                    CollectionSort::List(_) => CollectionMetadata::List(definition),
                    CollectionSort::Set(_) => CollectionMetadata::Set(definition),
                    CollectionSort::Map(_) => unreachable!(),
                };
                (names, collection)
            }
        };
        by_sort.insert(sort_name.clone(), collection.clone());
        for name in [&names.unit, &names.element, &names.concat] {
            if metadata.insert(name.clone(), collection.clone()).is_some() {
                return Err(DefinitionError::MalformedCollection(format!(
                    "symbol {name} belongs to multiple collections"
                )));
            }
        }
    }
    for (name, collection) in metadata {
        let symbol = symbols.get_mut(&name).ok_or_else(|| {
            DefinitionError::MalformedCollection(format!("missing collection symbol {name}"))
        })?;
        Arc::make_mut(symbol).attributes.collection = Some(collection);
    }
    for symbol in symbols.values_mut() {
        let Sort::Application { name, .. } = &symbol.result_sort else {
            continue;
        };
        if symbol.attributes.hook.is_some()
            && let Some(collection) = by_sort.get(name)
        {
            Arc::make_mut(symbol).attributes.result_collection = Some(collection.clone());
        }
    }
    Ok(())
}

fn build_sort_graph(
    sorts: &BTreeMap<Name, SortInfo>,
    pairs: Vec<(ClosedSort, ClosedSort)>,
) -> SortGraph {
    let _span = measure::algorithm_span(Algorithm::BackendDefinitionClosure);
    let names = sorts
        .iter()
        .filter(|(_, info)| info.parameters.is_empty())
        .map(|(name, _)| ClosedSort::simple(name.clone()))
        .chain(
            pairs
                .iter()
                .flat_map(|(sub, sup)| [sub.clone(), sup.clone()]),
        )
        .collect::<BTreeSet<_>>();
    let mut closure = names
        .iter()
        .cloned()
        .map(|name| (name.clone(), BTreeSet::from([name])))
        .collect::<BTreeMap<_, _>>();
    for (sub, sup) in &pairs {
        closure.entry(sup.clone()).or_default().insert(sub.clone());
    }
    // Invariant: `closure` only grows, bounded by |S|^2 pairs; exit when a round adds nothing.
    loop {
        let previous = closure.clone();
        for subsorts in closure.values_mut() {
            let descendants = subsorts
                .iter()
                .filter_map(|sort| previous.get(sort))
                .flatten()
                .cloned()
                .collect::<Vec<_>>();
            subsorts.extend(descendants);
        }
        if closure == previous {
            break;
        }
    }
    let graph = SortGraph::from_closure(sorts.keys().cloned(), closure);
    #[cfg(debug_assertions)]
    for (sub, sup) in &pairs {
        debug_assert_eq!(
            graph.check_subsort(sub.sort(), sup.sort()),
            Ok(true),
            "the subsort order misses a declared subsort axiom: {:?} <= {:?}",
            sub.sort(),
            sup.sort()
        );
    }
    graph
}

fn subsort_attribute(
    pattern: &kore::Pattern,
    attributes: &kore::Attributes,
    sorts: &BTreeMap<Name, SortInfo>,
) -> Result<Option<(ClosedSort, ClosedSort)>, DefinitionError> {
    let Some((symbol, arguments)) = attributes.application(KoreAttribute::Subsort) else {
        return Ok(None);
    };
    if !arguments.is_empty() || symbol.sort_parameters.len() != 2 {
        return Err(DefinitionError::MalformedAttribute(
            "subsort must have two sort parameters and no arguments".into(),
        ));
    }
    let known = BTreeSet::new();
    let sub = internalize_sort(&symbol.sort_parameters[0], sorts, &known)?;
    let sup = internalize_sort(&symbol.sort_parameters[1], sorts, &known)?;
    let kore::Pattern::Exists { variable, body, .. } = pattern else {
        return Err(DefinitionError::MalformedAttribute(
            "subsort attribute must annotate the generated existential axiom".into(),
        ));
    };
    let kore::Pattern::Equals { left, right, .. } = body.as_ref() else {
        return Err(DefinitionError::MalformedAttribute(
            "subsort existential must contain an equality".into(),
        ));
    };
    let kore::Pattern::Variable(left_variable) = left.as_ref() else {
        return Err(DefinitionError::MalformedAttribute(
            "subsort equality must bind its existential variable".into(),
        ));
    };
    let kore::Pattern::Application {
        symbol: injection,
        arguments,
    } = right.as_ref()
    else {
        return Err(DefinitionError::MalformedAttribute(
            "subsort equality must contain an injection".into(),
        ));
    };
    if left_variable != variable.as_ref()
        || !injection.is(WellKnownSymbol::Inj)
        || injection.sort_parameters.as_slice()
            != [
                symbol.sort_parameters[0].clone(),
                symbol.sort_parameters[1].clone(),
            ]
        || !matches!(arguments.as_slice(), [kore::Pattern::Variable(inner)] if inner.sort == symbol.sort_parameters[0])
        || variable.sort != symbol.sort_parameters[1]
    {
        return Err(DefinitionError::MalformedAttribute(
            "subsort axiom does not agree with its sub- and supersort parameters".into(),
        ));
    }
    let closed = |sort| {
        ClosedSort::new(sort).map_err(|_| {
            DefinitionError::MalformedAttribute("subsort arguments must be concrete sorts".into())
        })
    };
    Ok(Some((closed(sub)?, closed(sup)?)))
}

fn overload_attribute(
    attributes: &kore::Attributes,
) -> Result<Option<(Name, Name)>, DefinitionError> {
    let Some(arguments) = attributes
        .arguments(KoreAttribute::SymbolOverload)
        .or_else(|| attributes.arguments(KoreAttribute::Overload))
    else {
        return Ok(None);
    };
    let [
        kore::Pattern::Application {
            symbol: greater,
            arguments: greater_arguments,
        },
        kore::Pattern::Application {
            symbol: lesser,
            arguments: lesser_arguments,
        },
    ] = arguments
    else {
        return Err(DefinitionError::MalformedAttribute(
            "symbol-overload must contain two nullary symbols".into(),
        ));
    };
    if !greater_arguments.is_empty() || !lesser_arguments.is_empty() {
        return Err(DefinitionError::MalformedAttribute(
            "symbol-overload must contain two nullary symbols".into(),
        ));
    }
    Ok(Some((
        greater.name.as_str().into(),
        lesser.name.as_str().into(),
    )))
}

fn reject_duplicates(parameters: &[String]) -> Result<(), DefinitionError> {
    let mut seen = BTreeSet::new();
    for parameter in parameters {
        if !seen.insert(parameter) {
            return Err(DefinitionError::DuplicateParameter(parameter.clone()));
        }
    }
    Ok(())
}

fn reject_name_duplicates(parameters: &[Name]) -> Result<(), DefinitionError> {
    let mut seen = BTreeSet::new();
    for parameter in parameters {
        if !seen.insert(parameter) {
            return Err(DefinitionError::DuplicateParameter(parameter.to_string()));
        }
    }
    Ok(())
}

/// Whether `predicate` has a term in predicate position (`Predicate::Term`), at any depth of its
/// connectives: the internalized form of a term pattern inside a non-term left-hand side.
fn has_term_component(predicate: &Predicate) -> bool {
    match predicate {
        Predicate::Term(_) => true,
        Predicate::True
        | Predicate::False
        | Predicate::Equals(..)
        | Predicate::Ceil(_)
        | Predicate::Floor(_)
        | Predicate::In(..)
        | Predicate::Absent(_) => false,
        Predicate::Not(inner) | Predicate::Exists(_, inner) | Predicate::Forall(_, inner) => {
            has_term_component(inner)
        }
        Predicate::And(inner) | Predicate::Or(inner) => inner.iter().any(has_term_component),
        Predicate::Implies(left, right) | Predicate::Iff(left, right) => {
            has_term_component(left) || has_term_component(right)
        }
    }
}

#[cfg(test)]
mod tests {
    use indoc::indoc;
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use crate::term::TermKind;

    use super::*;

    fn algebraic_symbol_definition(
        attributes: &str,
        axiom: &str,
    ) -> Result<BackendDefinition, DefinitionError> {
        let symbol_keyword = if attributes.contains("hook{}(") {
            "hooked-symbol"
        } else {
            "symbol"
        };
        let source = format!(
            r#"[]
            module MAIN
                sort SortS{{}} []
                symbol c{{}}() : SortS{{}} [constructor{{}}(), functional{{}}()]
                {symbol_keyword} g{{}}(SortS{{}}, SortS{{}}) : SortS{{}} [{attributes}]
                {axiom}
            endmodule []"#
        );
        let syntax = parse_definition(&source).expect("algebraic definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN")
    }

    const COMM_AXIOM: &str = r"axiom{R} \equals{SortS{}, R}(
        g{}(X:SortS{}, Y:SortS{}), g{}(Y:SortS{}, X:SortS{})
    ) [comm{}()]";

    #[test]
    fn algebraic_facts_refuse_constructor_and_sort_injection_claims() {
        for (attributes, axiom, claim, tag) in [
            (
                "constructor{}(), functional{}(), assoc{}()",
                "",
                "constructor",
                "assoc",
            ),
            (
                "constructor{}(), functional{}()",
                COMM_AXIOM,
                "constructor",
                "comm",
            ),
            ("sortInjection{}(), comm{}()", "", "sortInjection", "comm"),
            (
                "constructor{}(), functional{}(), assoc{}(), comm{}(), idem{}()",
                r"axiom{R} \equals{SortS{}, R}(g{}(X:SortS{}, c{}()), X:SortS{}) [unit{}()]",
                "constructor",
                "assoc, comm, idem, unit",
            ),
        ] {
            let error = algebraic_symbol_definition(attributes, axiom)
                .expect_err("no-confusion claims contradict algebraic application identities");
            let DefinitionError::MalformedAttribute(message) = error else {
                panic!("expected a constructor/algebraic contradiction, got {error}");
            };
            assert_eq!(
                message,
                format!(
                    "symbol g is declared {claim} but algebraic axioms identify its applications: {tag}"
                )
            );
        }
    }

    #[test]
    fn other_malformed_symbol_attributes_keep_their_diagnostics() {
        let error = algebraic_symbol_definition(r#"function{}(), smt-hook{}("(")"#, "")
            .expect_err("an unclosed smt expression is malformed");
        let DefinitionError::MalformedAttribute(message) = error else {
            panic!("expected an invalid smt-hook, got {error}");
        };
        assert!(message.starts_with("invalid smt-hook"), "{message}");
    }

    #[test]
    fn a_cell_constructor_unit_attribute_states_no_algebraic_axiom() {
        let definition =
            algebraic_symbol_definition("constructor{}(), functional{}(), unit{}(c{}())", "")
                .expect("a unit declaration names the empty cell without identifying applications");
        let attributes = &definition.symbols[&Name::from("g")].attributes;
        assert_eq!(attributes.head_role(), HeadRole::FreeConstructor);
        assert!(attributes.algebraic_axioms().is_empty());
    }

    #[test]
    fn loaded_symbol_roles_read_declarations_and_algebraic_axioms_together() {
        for (attributes, axiom, expected) in [
            ("functional{}()", COMM_AXIOM, HeadRole::Uninterpreted),
            (
                "functional{}(), anywhere{}()",
                COMM_AXIOM,
                HeadRole::Uninterpreted,
            ),
            ("functional{}(), anywhere{}()", "", HeadRole::EquationHead),
            (
                r#"function{}(), total{}(), hook{}("LIST.concat"), assoc{}()"#,
                "",
                HeadRole::Function {
                    declared: true,
                    injective: false,
                    refutable_arguments: false,
                },
            ),
            (
                "functional{}(), injective{}()",
                "",
                HeadRole::Function {
                    declared: false,
                    injective: true,
                    refutable_arguments: true,
                },
            ),
            ("functional{}()", "", HeadRole::Uninterpreted),
        ] {
            let definition = algebraic_symbol_definition(attributes, axiom)
                .expect("consistent declaration should internalize");
            assert_eq!(
                definition.symbols[&Name::from("g")].attributes.head_role(),
                expected,
                "attributes {attributes}, axiom {axiom}"
            );
        }
    }

    #[test]
    fn algebraic_axiom_facts_union_tags_and_both_application_roots() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortS{} []
                symbol g{}(SortS{}) : SortS{} [functional{}(), anywhere{}(), idem{}()]
                symbol h{}(SortS{}) : SortS{} [functional{}(), anywhere{}()]
                axiom{R} \equals{SortS{}, R}(g{}(X:SortS{}), h{}(X:SortS{}))
                    [assoc{}(), comm{}(), unit{}()]
            endmodule []
        "#})
        .expect("tagged root equation should parse");
        let definition = BackendDefinition::internalize(&syntax, "MAIN")
            .expect("algebraic tags conservatively remove freeness from both roots");
        let axiom_facts = AlgebraicAxioms::assoc()
            .union(AlgebraicAxioms::comm())
            .union(AlgebraicAxioms::unit());
        for (name, expected) in [
            ("g", axiom_facts.union(AlgebraicAxioms::idem())),
            ("h", axiom_facts),
        ] {
            let attributes = &definition.symbols[&Name::from(name)].attributes;
            assert_eq!(attributes.algebraic_axioms(), expected);
            assert_eq!(attributes.head_role(), HeadRole::Uninterpreted);
        }
    }

    #[test]
    fn an_algebraic_axiom_without_application_roots_is_malformed() {
        let error = algebraic_symbol_definition(
            "functional{}()",
            r"axiom{R} \equals{SortS{}, R}(X:SortS{}, Y:SortS{}) [comm{}()]",
        )
        .expect_err("an algebraic fact must identify the applications it constrains");
        assert!(matches!(
            error,
            DefinitionError::Axiom(AxiomError::MalformedEquation)
        ));
    }

    fn selection_complete_source(guarded: bool, attribute: &str) -> String {
        let attribute = if attribute.is_empty() {
            String::new()
        } else {
            format!(", {attribute}")
        };
        let requires = if guarded {
            r#"\equals{SortBool{}, R}(condition{}(), \dv{SortBool{}}("true"))"#
        } else {
            r#"\top{R}()"#
        };
        format!(
            r#"[]
                module MAIN
                    sort SortNat{{}} []
                    sort SortAddress{{}} []
                    sort SortCell{{}} []
                    sort SortSub{{}} []
                    sort SortKItem{{}} []
                    symbol inj{{From, To}}(From) : To [sortInjection{{}}()]
                    axiom{{R}} \exists{{R}}(
                        Value:SortAddress{{}},
                        \equals{{SortAddress{{}}, R}}(
                            Value:SortAddress{{}},
                            inj{{SortSub{{}}, SortAddress{{}}}}(From:SortSub{{}})
                        )
                    ) [subsort{{SortSub{{}}, SortAddress{{}}}}()]
                    axiom{{R}} \exists{{R}}(
                        Value:SortKItem{{}},
                        \equals{{SortKItem{{}}, R}}(Value:SortKItem{{}}, inj{{SortSub{{}}, SortKItem{{}}}}(From:SortSub{{}}))
                    ) [subsort{{SortSub{{}}, SortKItem{{}}}}()]
                    axiom{{R}} \exists{{R}}(
                        Value:SortKItem{{}},
                        \equals{{SortKItem{{}}, R}}(Value:SortKItem{{}}, inj{{SortNat{{}}, SortKItem{{}}}}(From:SortNat{{}}))
                    ) [subsort{{SortNat{{}}, SortKItem{{}}}}()]
                    axiom{{R}} \exists{{R}}(
                        Value:SortKItem{{}},
                        \equals{{SortKItem{{}}, R}}(Value:SortKItem{{}}, inj{{SortAddress{{}}, SortKItem{{}}}}(From:SortAddress{{}}))
                    ) [subsort{{SortAddress{{}}, SortKItem{{}}}}()]
                    symbol sub{{}}() : SortSub{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                    symbol item{{}}(SortKItem{{}}) : SortCell{{}}
                        [constructor{{}}(), functional{{}}(), injective{{}}()]
                    hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
                    hooked-sort SortCellSet{{}}
                        [hook{{}}("SET.Set"), unit{{}}(setUnit{{}}()), element{{}}(setItem{{}}()),
                         concat{{}}(setConcat{{}}())]
                    symbol z{{}}() : SortNat{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                    symbol s{{}}(SortNat{{}}) : SortNat{{}}
                        [constructor{{}}(), functional{{}}(), injective{{}}()]
                    symbol wrap{{}}(SortNat{{}}) : SortAddress{{}}
                        [anywhere{{}}(), functional{{}}(), injective{{}}()]
                    symbol tag{{}}(SortNat{{}}) : SortAddress{{}} [anywhere{{}}(), functional{{}}()]
                    symbol pick{{}}(SortNat{{}}) : SortNat{{}} [anywhere{{}}(), functional{{}}()]
                    symbol addr{{}}(SortNat{{}}) : SortAddress{{}}
                        [constructor{{}}(), functional{{}}(), injective{{}}()]
                    symbol cell{{}}(SortAddress{{}}) : SortCell{{}}
                        [constructor{{}}(), functional{{}}(), injective{{}}()]
                    symbol spare{{}}(SortAddress{{}}) : SortCell{{}}
                        [constructor{{}}(), functional{{}}(), injective{{}}()]
                    symbol condition{{}}() : SortBool{{}} [function{{}}(), total{{}}(), no-evaluators{{}}()]
                    hooked-symbol setUnit{{}}() : SortCellSet{{}}
                        [function{{}}(), total{{}}(), hook{{}}("SET.unit")]
                    hooked-symbol setItem{{}}(SortCell{{}}) : SortCellSet{{}}
                        [function{{}}(), total{{}}(), hook{{}}("SET.element")]
                    hooked-symbol setConcat{{}}(SortCellSet{{}}, SortCellSet{{}}) : SortCellSet{{}}
                        [function{{}}(), hook{{}}("SET.concat"), assoc{{}}(), comm{{}}(), idem{{}}()]
                    axiom{{R}} \implies{{R}}(
                        \and{{R}}(
                            {requires},
                            \and{{R}}(\in{{SortNat{{}}, R}}(X0:SortNat{{}}, s{{}}(X:SortNat{{}})), \top{{R}}())
                        ),
                        \equals{{SortAddress{{}}, R}}(
                            wrap{{}}(X0:SortNat{{}}),
                            \and{{SortAddress{{}}}}(wrap{{}}(X:SortNat{{}}), \top{{SortAddress{{}}}}())
                        )
                    ) [label{{}}("unwrap"), anywhere{{}}(){attribute}]
                endmodule []"#
        )
    }

    #[test]
    fn equation_selection_complete_requires_every_term_equation_to_be_offered() {
        let lemma = r#"
                    axiom{R} \implies{R}(
                        \top{R}(),
                        \equals{SortAddress{}, R}(
                            \and{SortAddress{}}(tag{}(s{}(X:SortNat{})), tag{}(s{}(X:SortNat{}))),
                            \and{SortAddress{}}(tag{}(X:SortNat{}), \top{SortAddress{}}())
                        )
                    ) [simplification{}()]
                endmodule []"#;
        let with_axiom =
            selection_complete_source(false, "").replace("\n                endmodule []", lemma);
        let without_axiom = selection_complete_source(false, "");
        let syntax = parse_definition(&with_axiom).expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        assert!(definition.equation_selection_complete().is_none());

        let syntax = parse_definition(&without_axiom).expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        assert!(definition.equation_selection_complete().is_some());
    }

    #[test]
    fn retains_valid_binder_attribute() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                hooked-sort SortKVar{} [hook{}("KVAR.KVar"), hasDomainValues{}()]
                sort SortExp{} []
                symbol lambda{}(SortKVar{}, SortExp{}) : SortExp{}
                    [constructor{}(), binder{}()]
                symbol apply{}(SortExp{}, SortExp{}) : SortExp{} [constructor{}()]
            endmodule []
        "#})
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");

        assert!(definition.symbols["lambda"].attributes.binder);
        assert!(!definition.symbols["apply"].attributes.binder);
    }

    #[test]
    fn retains_three_argument_binder_attribute() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                hooked-sort SortKVar{} [hook{}("KVAR.KVar"), hasDomainValues{}()]
                sort SortExp{} []
                symbol letWithAnnotation{}(SortKVar{}, SortExp{}, SortExp{}) : SortExp{}
                    [constructor{}(), binder{}()]
            endmodule []
        "#})
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");

        assert!(definition.symbols["letWithAnnotation"].attributes.binder);
    }

    #[test]
    fn rejects_unary_binder_attribute() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                hooked-sort SortKVar{} [hook{}("KVAR.KVar"), hasDomainValues{}()]
                sort SortExp{} []
                symbol malformed{}(SortKVar{}) : SortExp{} [constructor{}(), binder{}()]
            endmodule []
        "#})
        .expect("definition should parse");

        assert!(matches!(
            BackendDefinition::internalize(&syntax, "MAIN"),
            Err(DefinitionError::MalformedAttribute(message))
                if message == "Binder productions must have at least two nonterminals."
        ));
    }

    #[test]
    fn rejects_binder_attribute_without_kvar_hook() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortExp{} []
                symbol malformed{}(SortExp{}, SortExp{}) : SortExp{}
                    [constructor{}(), binder{}()]
            endmodule []
        "#})
        .expect("definition should parse");

        assert!(matches!(
            BackendDefinition::internalize(&syntax, "MAIN"),
            Err(DefinitionError::MalformedAttribute(message))
                if message == "First child of binder must have a sort with the 'KVAR.KVar' hook attribute."
        ));
    }

    #[test]
    fn rejects_binder_attribute_with_first_sort_variable() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortExp{} []
                symbol malformed{S}(S, SortExp{}) : SortExp{} [constructor{}(), binder{}()]
            endmodule []
        "#})
        .expect("definition should parse");

        assert!(matches!(
            BackendDefinition::internalize(&syntax, "MAIN"),
            Err(DefinitionError::MalformedAttribute(message))
                if message == "First child of binder must have a sort with the 'KVAR.KVar' hook attribute."
        ));
    }

    fn classified_rule_labels(definition: &BackendDefinition) -> Vec<&str> {
        definition
            .classified_axioms
            .iter()
            .filter_map(|axiom| match axiom {
                ClassifiedAxiom::Rewrite { attributes, .. }
                | ClassifiedAxiom::Function { attributes, .. }
                | ClassifiedAxiom::Simplification { attributes, .. }
                | ClassifiedAxiom::Ceil { attributes, .. } => attributes.label.as_deref(),
            })
            .collect()
    }

    #[test]
    fn indexes_main_module_before_imports_in_declaration_order() {
        let syntax = parse_definition(indoc! {r#"
            []
            module BASE
                sort SortS{} []
                symbol base{}() : SortS{} [constructor{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(base{}(), \top{SortS{}}()),
                    base{}()
                ) [label{}("base")]
            endmodule []
            module A
                import BASE []
                symbol a{}() : SortS{} [constructor{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(a{}(), \top{SortS{}}()),
                    a{}()
                ) [label{}("a")]
            endmodule []
            module B
                import BASE []
                symbol b{}() : SortS{} [constructor{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(b{}(), \top{SortS{}}()),
                    b{}()
                ) [label{}("b")]
            endmodule []
            module MAIN
                import A []
                import B []
                symbol main{}() : SortS{} [constructor{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(main{}(), \top{SortS{}}()),
                    main{}()
                ) [label{}("main")]
            endmodule []
        "#})
        .expect("definition should parse");

        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");

        // `BASE` is reached through `A` and through `B`; its one sentence is one rule, kept at
        // its first position, with one origin.
        assert_eq!(
            classified_rule_labels(&definition),
            ["main", "a", "base", "b"]
        );
        assert_eq!(
            definition.classified_axioms[2].attributes().origins.len(),
            1
        );
    }

    #[test]
    fn indexes_axioms_in_declaration_order() {
        let heat = r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(injectiveFunction{}(X:SortV{})),
                    \top{SortS{}}()
                ),
                heatResult{}()
            ) [label{}("heat")]
        "#;
        let lookup = r#"
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(\dv{SortV{}}("value")),
                    \top{SortS{}}()
                ),
                lookupResult{}()
            ) [label{}("lookup")]
        "#;

        for (rules, expected) in [
            (format!("{heat}{lookup}"), ["heat", "lookup"]),
            (format!("{lookup}{heat}"), ["lookup", "heat"]),
        ] {
            let source = format!(
                r#"[]
                module MAIN
                    sort SortV{{}} [hasDomainValues{{}}()]
                    sort SortS{{}} []
                    symbol wrap{{}}(SortV{{}}) : SortS{{}} [constructor{{}}()]
                    symbol injectiveFunction{{}}(SortV{{}}) : SortV{{}}
                        [function{{}}(), total{{}}(), injective{{}}()]
                    symbol heatResult{{}}() : SortS{{}} [constructor{{}}()]
                    symbol lookupResult{{}}() : SortS{{}} [constructor{{}}()]
                    {rules}
                endmodule []"#
            );
            let syntax = parse_definition(&source).expect("definition should parse");
            let definition = BackendDefinition::internalize(&syntax, "MAIN")
                .expect("definition should internalize");

            assert_eq!(classified_rule_labels(&definition), expected);
        }
    }

    fn source_execution_order_definition() -> kore::Definition {
        parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortS{} []
                symbol a{}() : SortS{} [constructor{}()]
                symbol b{}() : SortS{} [constructor{}()]
                symbol c{}() : SortS{} [constructor{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(a{}(), \top{SortS{}}()),
                    b{}()
                ) [UNIQUE'Unds'ID{}("first")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(a{}(), \top{SortS{}}()),
                    c{}()
                ) [UNIQUE'Unds'ID{}("second")]
            endmodule []
        "#})
        .expect("source-execution definition should parse")
    }

    #[test]
    fn source_execution_rejects_missing_and_duplicate_rewrite_order_ids() {
        let syntax = source_execution_order_definition();
        assert_eq!(
            BackendDefinition::internalize_for_source_execution(&syntax, "MAIN", &["first"])
                .unwrap_err(),
            DefinitionError::MissingRewriteOrderIds(vec!["second".into()])
        );
        assert_eq!(
            BackendDefinition::internalize_for_source_execution(
                &syntax,
                "MAIN",
                &["first", "first", "second"],
            )
            .unwrap_err(),
            DefinitionError::DuplicateRewriteOrderId("first".into())
        );
    }

    #[test]
    fn source_execution_accepts_frontend_order_entries_not_emitted_as_rewrites() {
        BackendDefinition::internalize_for_source_execution(
            &source_execution_order_definition(),
            "MAIN",
            &["first", "equation-or-macro", "second"],
        )
        .expect("extra frontend ranks do not make rewrite precedence ambiguous");
    }

    fn reference_definition_fixture(name: &str) -> kore::Definition {
        let source = match name {
            "undef" => include_str!("../../k-rust/tests/fixtures/reference/definition/undef.kore"),
            "arity" => include_str!("../../k-rust/tests/fixtures/reference/definition/arity.kore"),
            "boolbad" => {
                include_str!("../../k-rust/tests/fixtures/reference/definition/boolbad.kore")
            }
            "varsort" => {
                include_str!("../../k-rust/tests/fixtures/reference/definition/varsort.kore")
            }
            "claimrhs" => {
                include_str!("../../k-rust/tests/fixtures/reference/definition/claimrhs.kore")
            }
            "unbound" => {
                include_str!("../../k-rust/tests/fixtures/reference/definition/unbound.kore")
            }
            "selfsub" => {
                include_str!("../../k-rust/tests/fixtures/reference/definition/selfsub.kore")
            }
            "dupsym" => {
                include_str!("../../k-rust/tests/fixtures/reference/definition/dupsym.kore")
            }
            "ok" => include_str!("../../k-rust/tests/fixtures/reference/definition/ok.kore"),
            _ => panic!("unknown definition fixture {name}"),
        };
        parse_definition(source).expect("reference definition fixture should parse")
    }

    fn reference_pattern_fixture(name: &str) -> kore::Pattern {
        let source = match name {
            "dv" => include_str!("../../k-rust/tests/fixtures/reference/definition/dv.kore"),
            "pat" => include_str!("../../k-rust/tests/fixtures/reference/definition/pat.kore"),
            "var" => include_str!("../../k-rust/tests/fixtures/reference/definition/var.kore"),
            _ => panic!("unknown pattern fixture {name}"),
        };
        parse_pattern(source).expect("reference pattern fixture should parse")
    }

    /// These verification fixtures constrain application roots by algebraic axioms.
    /// Their roots must not claim constructor freeness, so verification reaches the
    /// original undeclared-symbol and arity defects rather than a declaration contradiction.
    fn algebraic_verification_fixture(name: &str, roots: &[&str]) -> kore::Definition {
        let mut definition = reference_definition_fixture(name);
        for module in &mut definition.modules {
            for sentence in &mut module.sentences {
                if let kore::Sentence::SymbolDeclaration {
                    symbol, attributes, ..
                } = sentence
                    && roots.contains(&symbol.name.as_str())
                {
                    for attribute in &mut attributes.0 {
                        if let kore::Pattern::Application { symbol, .. } = attribute
                            && symbol.name == "constructor"
                        {
                            symbol.name = "functional".into();
                        }
                    }
                }
            }
        }
        definition
    }

    #[test]
    fn reference_rejects_undeclared_symbols_in_ignored_axioms() {
        let error =
            BackendDefinition::internalize(&algebraic_verification_fixture("undef", &["c"]), "M")
                .expect_err("ignored axioms must be verified");
        assert!(
            format!("{error}").contains("Head 'g' not defined."),
            "{error}"
        );
    }

    #[test]
    fn reference_rejects_arity_errors_in_ignored_axioms() {
        let error = BackendDefinition::internalize(
            &algebraic_verification_fixture("arity", &["c", "d"]),
            "M",
        )
        .expect_err("ignored axioms must have their application arity verified");
        assert!(
            format!("{error}").contains("Expected 1 operands, but got 0."),
            "{error}"
        );
    }

    #[test]
    fn reference_rejects_domain_values_on_unmarked_sorts() {
        let definition = BackendDefinition::internalize(&reference_definition_fixture("ok"), "M")
            .expect("control definition should internalize");
        let error = definition
            .internalize_term(&reference_pattern_fixture("dv"), &[])
            .expect_err("domain values require hasDomainValues");
        assert!(format!("{error}").contains("hasDomainValues"), "{error}");
    }

    #[test]
    fn reference_rejects_non_boolean_bool_literals() {
        let error = BackendDefinition::internalize(&reference_definition_fixture("boolbad"), "M")
            .expect_err("Bool literals must be true or false");
        assert!(format!("{error}").contains("BOOL.Bool"), "{error}");
    }

    #[test]
    fn rejects_non_decimal_int_literals() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortToken{} [hasDomainValues{}()]
            endmodule []
        "#})
        .expect("domain-value definition should parse");
        let definition = BackendDefinition::internalize(&syntax, "MAIN")
            .expect("domain-value definition should internalize");

        for value in ["3.0", "three"] {
            let pattern = parse_pattern(&format!(r#"\dv{{SortInt{{}}}}("{value}")"#))
                .expect("malformed Int domain value should parse as KORE");
            assert!(matches!(
                definition.internalize_term(&pattern, &[]),
                Err(DefinitionError::InvalidDomainValue { sort, value: actual })
                    if *sort == crate::externalize::sort(&Sort::simple("SortInt")) && actual == value
            ));
        }

        let token = parse_pattern(r#"\dv{SortToken{}}("value")"#)
            .expect("unhooked domain value should parse");
        definition
            .internalize_term(&token, &[])
            .expect("an unhooked hasDomainValues sort stays accepted");
    }

    #[test]
    fn reference_rejects_inconsistent_free_variable_sorts() {
        let error = BackendDefinition::internalize(&reference_definition_fixture("varsort"), "M")
            .expect_err("one free variable name must have one sort");
        assert!(
            format!("{error}").contains("Inconsistent free variable usage"),
            "{error}"
        );
    }

    #[test]
    fn reference_rejects_claims_with_free_rhs_variables() {
        let error = BackendDefinition::internalize(&reference_definition_fixture("claimrhs"), "M")
            .expect_err("claim RHS variables must be bound on the LHS or existential");
        assert!(
            format!("{error}").contains("universally-quantified variables"),
            "{error}"
        );
    }

    #[test]
    fn reference_accepts_free_rhs_variables_in_axioms() {
        BackendDefinition::internalize(&reference_definition_fixture("unbound"), "M")
            .expect("Kore permits free variables appearing only on an axiom RHS");
    }

    #[test]
    fn reference_accepts_reflexive_subsort_axioms() {
        BackendDefinition::internalize(&reference_definition_fixture("selfsub"), "M")
            .expect("subsort order is reflexive; S <= S adds nothing");
    }

    #[test]
    fn reference_reports_duplicate_names_across_modules() {
        let error = BackendDefinition::internalize(&reference_definition_fixture("dupsym"), "N")
            .expect_err("duplicate names in an import closure must be rejected");
        assert!(format!("{error}").contains("c"), "{error}");
    }

    #[test]
    fn reference_accepts_free_standalone_variables() {
        let definition = BackendDefinition::internalize(&reference_definition_fixture("ok"), "M")
            .expect("control definition should internalize");
        definition
            .internalize_pattern(&reference_pattern_fixture("var"), &[])
            .expect("Kore permits free variables in standalone patterns");
    }

    /// A schematic pattern's sort variables are parameters of the query: the standalone verifier
    /// accepts one the witness declares and rejects an undeclared one, and the witness
    /// internalizes under the context it was verified under.
    #[test]
    fn standalone_verification_reads_the_witness_sort_variables() {
        let definition = BackendDefinition::internalize(&reference_definition_fixture("ok"), "M")
            .expect("control definition should internalize");
        let pattern = parse_pattern(r"\top{S}()").expect("pattern should parse");

        let Err(error) = definition.verify_standalone_pattern(&pattern, &[]) else {
            panic!("an undeclared sort variable must be rejected");
        };
        assert!(
            format!("{error}").contains("Sort variable S not declared."),
            "{error}"
        );

        let sort_variables = [Name::from("S")];
        let admitted = definition
            .verify_standalone_pattern(&pattern, &sort_variables)
            .expect("a declared sort variable verifies");
        assert_eq!(admitted.admission(), Admission::Verified);
        assert_eq!(admitted.sort_variables(), &sort_variables);
        let (_, sort) = admitted
            .internalize_predicate()
            .expect("the verified context internalizes");
        assert_eq!(sort, Sort::Variable(Name::from("S")));
    }

    /// An associative application denotes the fold of its binary head over its operands, so the
    /// standalone verifier accepts every fold that internalizes, of one or more operands, and
    /// checks the sorts of each fold step.
    #[test]
    fn standalone_verification_reads_an_associative_application_as_a_fold() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortA{} []
                sort SortB{} []
                symbol a{}() : SortA{} [constructor{}(), functional{}()]
                symbol b{}() : SortB{} [constructor{}(), functional{}()]
                symbol pair{}(SortA{}, SortA{}) : SortA{} [constructor{}(), functional{}()]
                symbol push{}(SortA{}, SortB{}) : SortA{} [constructor{}(), functional{}()]
                symbol one{}(SortA{}) : SortA{} [constructor{}(), functional{}()]
            endmodule []
        "#})
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let verify = |source: &str| {
            let pattern = parse_pattern(source).expect("pattern should parse");
            definition
                .verify_standalone_pattern(&pattern, &[])
                .and_then(|admitted| admitted.internalize_term())
                .map_err(|error| error.to_string())
        };

        for source in [
            r"\left-assoc{}(pair{}(a{}()))",
            r"\left-assoc{}(pair{}(a{}(), a{}()))",
            r"\left-assoc{}(pair{}(a{}(), a{}(), a{}()))",
            r"\right-assoc{}(pair{}(a{}(), a{}(), a{}()))",
            r"\left-assoc{}(push{}(a{}(), b{}(), b{}()))",
        ] {
            verify(source).unwrap_or_else(|error| panic!("{source}: {error}"));
        }
        for (source, message) in [
            (
                r"\right-assoc{}(push{}(a{}(), b{}(), b{}()))",
                "Expecting sort SortA{} but got SortB{}.",
            ),
            (
                r"\left-assoc{}(one{}(a{}()))",
                "Associative application needs a binary head, but 'one' takes 1 operands.",
            ),
        ] {
            let error = verify(source).expect_err(source);
            assert!(error.contains(message), "{source}: {error}");
        }
    }

    fn predicate_floating_definition() -> BackendDefinition {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortToken{} [hasDomainValues{}()]
                sort SortK{} []
                symbol item{}(SortToken{}) : SortK{} [constructor{}()]
                symbol cell{}(SortK{}) : SortK{} [constructor{}()]
            endmodule []
        "#})
        .expect("predicate-floating definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN")
            .expect("predicate-floating definition should internalize")
    }

    fn nested_predicate_pattern() -> kore::Pattern {
        parse_pattern(indoc! {r#"
            cell{}(
                \and{SortK{}}(
                    item{}(\dv{SortToken{}}("2")),
                    \equals{SortToken{}, SortK{}}(
                        \dv{SortToken{}}("3"),
                        X:SortToken{}
                    )
                )
            )
        "#})
        .expect("nested predicate pattern should parse")
    }

    #[test]
    fn floats_predicates_under_constructors_into_rule_constraints() {
        let definition = predicate_floating_definition();
        let pattern = definition
            .internalize_pattern(&nested_predicate_pattern(), &[])
            .expect("nested predicates should float to the pattern condition");

        assert_eq!(pattern.constraints.len(), 1);
        let TermKind::Application {
            symbol, arguments, ..
        } = pattern.term.kind()
        else {
            panic!("expected outer cell application: {:?}", pattern.term);
        };
        assert_eq!(symbol.name.as_ref(), "cell");
        assert_eq!(arguments.len(), 1);
        assert!(matches!(
            arguments[0].kind(),
            TermKind::Application { symbol, .. } if symbol.name.as_ref() == "item"
        ));
    }

    #[test]
    fn rejects_floated_predicates_at_pure_term_entry_points() {
        let error = predicate_floating_definition()
            .internalize_term(&nested_predicate_pattern(), &[])
            .expect_err("a pure term boundary must not discard floated predicates");

        assert_eq!(
            format!("{error}"),
            "predicate in term position (1 floated conjuncts) where a term is required"
        );
    }

    #[test]
    fn keeps_term_conjunctions_as_and_terms() {
        let definition = predicate_floating_definition();
        let syntax = parse_pattern(indoc! {r#"
            \and{SortToken{}}(
                \dv{SortToken{}}("2"),
                \dv{SortToken{}}("3")
            )
        "#})
        .expect("term conjunction should parse");

        let term = definition
            .internalize_term(&syntax, &[])
            .expect("two term components stay a term conjunction");
        assert!(matches!(term.kind(), TermKind::And(..)));
    }

    fn disjunction_definition(sentences: &str) -> Result<BackendDefinition, DefinitionError> {
        let source = format!(
            r#"[]
            module MAIN
                sort SortS{{}} []
                symbol a{{}}() : SortS{{}} [constructor{{}}()]
                symbol b{{}}() : SortS{{}} [constructor{{}}()]
                symbol c{{}}() : SortS{{}} [constructor{{}}()]
                symbol box{{}}(SortS{{}}) : SortS{{}} [constructor{{}}()]
                alias weakAlwaysFinally{{S}}(S) : S
                    where weakAlwaysFinally{{S}}(@X:S) := @X:S []
                {sentences}
            endmodule []"#
        );
        BackendDefinition::internalize(
            &parse_definition(&source).expect("disjunction definition should parse"),
            "MAIN",
        )
    }

    #[test]
    fn splits_lhs_disjunctions_into_one_rule_per_disjunct() {
        let definition = disjunction_definition(
            r#"axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    box{}(\or{SortS{}}(a{}(), b{}())),
                    \top{SortS{}}()
                ),
                c{}()
            ) [label{}("split-lhs")]"#,
        )
        .expect("term disjunctions on rewrite LHSs should split");

        let rules = definition
            .rewrite_theory
            .values()
            .flat_map(BTreeMap::values)
            .flatten()
            .collect::<Vec<_>>();
        assert_eq!(rules.len(), 2);
        assert!(
            rules
                .iter()
                .all(|rule| rule.attributes.unique_id == "split-lhs")
        );
    }

    #[test]
    fn internalizes_rhs_disjunctions_without_splitting_the_source_rule() {
        let definition = disjunction_definition(
            r#"axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(c{}(), \top{SortS{}}()),
                \or{SortS{}}(a{}(), b{}())
            ) [label{}("split-rhs")]"#,
        )
        .expect("term disjunctions on rewrite RHSs should internalize");

        let rule_count = definition
            .rewrite_theory
            .values()
            .flat_map(BTreeMap::values)
            .map(Vec::len)
            .sum::<usize>();
        assert_eq!(rule_count, 1);
    }

    #[test]
    fn splits_claim_lhs_disjunctions_into_several_claims() {
        let definition = disjunction_definition(
            r#"claim{} \implies{SortS{}}(
                \or{SortS{}}(a{}(), b{}()),
                weakAlwaysFinally{SortS{}}(c{}())
            ) [label{}("split-claim"), all-path{}()]"#,
        )
        .expect("term disjunctions on claim LHSs should split");

        assert_eq!(definition.reachability_claims.len(), 2);
        assert!(
            definition
                .reachability_claims
                .iter()
                .all(|claim| claim.attributes.unique_id == "split-claim")
        );
    }

    #[test]
    fn nested_initial_disjunctions_expand_but_single_pattern_entry_rejects_them() {
        let definition = disjunction_definition("").expect("control definition should load");
        let syntax = parse_pattern(r#"box{}(\or{SortS{}}(a{}(), b{}()))"#)
            .expect("nested initial disjunction should parse");

        let alternatives = definition
            .internalize_disjunction(&syntax, &[])
            .expect("nested initial disjunction should distribute");
        assert_eq!(alternatives.len(), 2);

        let error = definition
            .internalize_pattern(&syntax, &[])
            .expect_err("a single-pattern boundary must reject a term disjunction");
        assert!(
            format!("{error:?}").contains("TermDisjunction"),
            "{error:?}"
        );
    }

    fn definition() -> BackendDefinition {
        let syntax = parse_definition(indoc! {r#"
            []
            module BASE
                sort SortKey{} []
                sort SortValue{} []
                sort SortBox{S} []
                hooked-sort SortMap{}
                    [hook{}("MAP.Map"), unit{}(dot{}()), element{}(item{}()), concat{}(concat{}())]
                hooked-symbol dot{}() : SortMap{} [function{}(), functional{}(), hook{}("MAP.unit")]
                hooked-symbol item{}(SortKey{}, SortValue{}) : SortMap{}
                    [function{}(), functional{}(), hook{}("MAP.element")]
                hooked-symbol concat{}(SortMap{}, SortMap{}) : SortMap{}
                    [function{}(), assoc{}(), hook{}("MAP.concat")]
                symbol value{}() : SortValue{} [constructor{}()]
                symbol wrap{}(SortValue{}) : SortValue{} [constructor{}()]
                symbol injectiveFunction{}(SortValue{}) : SortValue{}
                    [function{}(), total{}(), injective{}()]
                symbol box{S}(S) : SortBox{S} [constructor{}()]
                symbol inj{From, To}(From) : To [sortInjection{}()]
                axiom{R}
                    \exists{R}(
                        Val:SortValue{},
                        \equals{SortValue{}, R}(
                            Val:SortValue{},
                            inj{SortKey{}, SortValue{}}(From:SortKey{})
                        )
                    )
                    [subsort{SortKey{}, SortValue{}}()]
            endmodule []
            module MAIN
                import BASE []
                symbol key{}() : SortKey{} [constructor{}()]
                axiom{}
                    \rewrites{SortValue{}}(
                        \and{SortValue{}}(
                            wrap{}(X:SortValue{}),
                            \equals{SortValue{}, SortValue{}}(X:SortValue{}, value{}())
                        ),
                        \exists{SortValue{}}(
                            Y:SortValue{},
                            \and{SortValue{}}(
                                wrap{}(Y:SortValue{}),
                                \equals{SortValue{}, SortValue{}}(Y:SortValue{}, X:SortValue{})
                            )
                        )
                    )
                    [label{}("kept-for-rule-internalization")]
            endmodule []
        "#})
        .expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    fn overload_definition() -> BackendDefinition {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortS{} []
                symbol A{}() : SortS{} [constructor{}()]
                symbol B{}() : SortS{} [constructor{}()]
                symbol C{}() : SortS{} [constructor{}()]
                symbol D{}() : SortS{} [constructor{}()]
                symbol E{}() : SortS{} [constructor{}()]
                axiom{} \equals{SortS{}, SortS{}}(D{}(), B{}())
                    [symbol-overload{}(D{}(), B{}())]
                axiom{} \equals{SortS{}, SortS{}}(D{}(), C{}())
                    [symbol-overload{}(D{}(), C{}())]
                axiom{} \equals{SortS{}, SortS{}}(B{}(), A{}())
                    [symbol-overload{}(B{}(), A{}())]
                axiom{} \equals{SortS{}, SortS{}}(C{}(), A{}())
                    [symbol-overload{}(C{}(), A{}())]
            endmodule []
        "#})
        .expect("overload definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN")
            .expect("overload definition should internalize")
    }

    #[test]
    fn model_predicates_require_an_atomic_ml_condition() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
            endmodule []"#,
        )
        .unwrap();
        let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
        let term_only =
            parse_pattern(r"\and{SortBool{}}(\not{SortBool{}}(X:SortBool{}), X:SortBool{})")
                .unwrap();
        let predicate = parse_pattern(
            r"\equals{SortBool{}, SortBool{}}(\not{SortBool{}}(X:SortBool{}), X:SortBool{})",
        )
        .unwrap();

        assert_eq!(
            definition.internalize_model_predicate(&term_only, &[]),
            Ok(None)
        );
        assert!(matches!(
            definition.internalize_model_predicate(&predicate, &[]),
            Ok(Some((crate::rule::Predicate::Iff(..), _)))
        ));
    }

    #[test]
    fn resolves_transitive_module_scope_and_subsorts() {
        let definition = definition();
        assert_eq!(
            definition.modules,
            BTreeSet::from([Name::from("BASE"), Name::from("MAIN")])
        );
        assert!(definition.sorts.contains_key("SortBox"));
        assert!(definition.symbols.contains_key("key"));
        assert_eq!(definition.axioms.len(), 2);
        assert_eq!(definition.classified_axioms.len(), 1);
        let priorities = definition
            .rewrite_theory
            .get(&crate::rule::TermIndex::Symbol("wrap".into()))
            .expect("rewrite should be indexed by its head symbol");
        let rule = &priorities[&50][0];
        assert_eq!(rule.requires.len(), 1);
        assert_eq!(rule.ensures.len(), 1);
        assert!(
            rule.lhs
                .attributes()
                .variables
                .iter()
                .any(|variable| variable.name.as_ref() == "Rule#X")
        );
        assert_eq!(
            rule.existentials
                .iter()
                .map(|variable| variable.name.as_ref())
                .collect::<Vec<_>>(),
            vec!["Ex#Y"]
        );
        assert_eq!(
            definition
                .sort_graph
                .check_subsort(&Sort::simple("SortKey"), &Sort::simple("SortValue")),
            Ok(true)
        );
    }

    #[test]
    fn validates_and_instantiates_parametric_symbol_sorts() {
        let definition = definition();
        let pattern = parse_pattern("box{SortValue{}}(value{}())").expect("pattern should parse");
        let term = definition
            .internalize_term(&pattern, &[])
            .expect("term should internalize");
        assert_eq!(
            term.sort(),
            Sort::application("SortBox", vec![Sort::simple("SortValue")])
        );
    }

    #[test]
    fn preserves_injective_symbol_metadata() {
        let definition = definition();

        assert_eq!(
            definition.symbols["injectiveFunction"]
                .attributes
                .head_role(),
            HeadRole::Function {
                declared: true,
                injective: true,
                refutable_arguments: true
            }
        );
        // Negative control: a declared function without `injective` stays non-injective.
        assert_eq!(
            definition.symbols["item"].attributes.head_role(),
            HeadRole::Function {
                declared: true,
                injective: false,
                refutable_arguments: true
            }
        );
        assert_eq!(
            definition.symbols["wrap"].attributes.head_role(),
            HeadRole::FreeConstructor
        );
    }

    #[test]
    fn internalizes_the_transitive_symbol_overload_graph() {
        let definition = overload_definition();
        let a = Name::from("A");
        let b = Name::from("B");
        let c = Name::from("C");
        let d = Name::from("D");
        let e = Name::from("E");

        assert!(definition.overloads.is_overloaded(&a));
        assert!(definition.overloads.is_overloaded(&d));
        assert!(!definition.overloads.is_overloaded(&e));
        assert!(definition.overloads.is_overloading(&d, &a));
        assert!(!definition.overloads.is_overloading(&a, &d));
        assert_eq!(
            definition.overloads.common_overloads(&a, &a),
            BTreeSet::from([b, c, d.clone()])
        );
        assert_eq!(
            definition
                .overloads
                .common_overloads(&Name::from("B"), &Name::from("C")),
            BTreeSet::from([d])
        );
    }

    #[test]
    fn rejects_cyclic_symbol_overloads() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortS{} []
                symbol A{}() : SortS{} [constructor{}()]
                symbol B{}() : SortS{} [constructor{}()]
                axiom{} \equals{SortS{}, SortS{}}(A{}(), B{}())
                    [symbol-overload{}(A{}(), B{}())]
                axiom{} \equals{SortS{}, SortS{}}(B{}(), A{}())
                    [symbol-overload{}(B{}(), A{}())]
            endmodule []
        "#})
        .expect("cyclic overload definition should parse");

        assert!(matches!(
            BackendDefinition::internalize(&syntax, "MAIN"),
            Err(DefinitionError::MalformedAttribute(message))
                if message.contains("cycle")
        ));
    }

    #[test]
    fn canonicalizes_collection_symbol_applications() {
        let definition = definition();
        let pattern = parse_pattern("concat{}(item{}(key{}(), value{}()), REST:SortMap{})")
            .expect("pattern should parse");
        let term = definition
            .internalize_term(&pattern, &[])
            .expect("term should internalize");

        let TermKind::Map {
            definition,
            entries,
            rest,
        } = term.kind()
        else {
            panic!("expected internal map, found {term:?}");
        };
        assert_eq!(definition.map_sort.as_ref(), "SortMap");
        assert_eq!(entries.len(), 1);
        assert!(matches!(
            rest.as_ref().map(Term::kind),
            Some(TermKind::Variable(Variable { name, .. })) if name.as_ref() == "REST"
        ));
    }

    #[test]
    fn rejects_import_cycles_with_the_cycle_path() {
        let syntax = parse_definition(indoc! {"
            []
            module A
                import B []
            endmodule []
            module B
                import A []
            endmodule []
        "})
        .expect("definition should parse");

        assert_eq!(
            BackendDefinition::internalize(&syntax, "A").unwrap_err(),
            DefinitionError::ImportCycle(vec!["A".into(), "B".into(), "A".into()])
        );
    }

    #[test]
    fn rejects_term_sort_mismatches() {
        let definition = definition();
        let pattern = parse_pattern("box{SortKey{}}(value{}())").expect("pattern should parse");

        assert!(matches!(
            definition.internalize_term(&pattern, &[]),
            Err(DefinitionError::IncorrectArgumentSort {
                symbol,
                index: 0,
                expected,
                actual,
            }) if symbol == "box"
                && *expected == crate::externalize::sort(&Sort::simple("SortKey"))
                && *actual == crate::externalize::sort(&Sort::simple("SortValue"))
        ));
    }

    #[test]
    fn validates_application_shape_before_internalizing_children() {
        let definition = definition();
        let pattern = parse_pattern("box{SortKey{}}(box{SortKey{}}(value{}()), value{}())")
            .expect("pattern should parse");

        assert_eq!(
            definition.internalize_term(&pattern, &[]).unwrap_err(),
            DefinitionError::WrongSymbolArity {
                symbol: "box".into(),
                expected: 1,
                actual: 2,
            }
        );
    }

    #[test]
    fn rejects_injections_between_unrelated_sorts() {
        let definition = definition();
        let pattern =
            parse_pattern("inj{SortValue{}, SortKey{}}(key{}())").expect("pattern should parse");

        assert_eq!(
            definition.internalize_term(&pattern, &[]).unwrap_err(),
            DefinitionError::NotSubsort {
                source: Box::new(crate::externalize::sort(&Sort::simple("SortValue"))),
                target: Box::new(crate::externalize::sort(&Sort::simple("SortKey"))),
            }
        );
    }

    #[test]
    fn dead_rewrite_injection_is_not_loaded() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortA{} []
                sort SortB{} []
                symbol inj{From, To}(From) : To [sortInjection{}()]
                axiom{}
                    \rewrites{SortB{}}(
                        \and{SortB{}}(
                            inj{SortA{}, SortB{}}(X:SortA{}),
                            \top{SortB{}}()
                        ),
                        inj{SortA{}, SortB{}}(X:SortA{})
                    ) []
            endmodule []
        "#})
        .expect("definition should parse");

        let definition = BackendDefinition::internalize(&syntax, "MAIN")
            .expect("dead matched injection should not load a rewrite rule");
        assert!(definition.rewrite_theory.is_empty());
    }

    #[test]
    fn expands_parametric_aliases_without_treating_them_as_symbols() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortValue{} []
                symbol value{}() : SortValue{} [constructor{}()]
                alias identity{S}(S) : S
                    where identity{S}(X:S) := X:S []
            endmodule []
        "#})
        .expect("definition should parse");

        let definition = BackendDefinition::internalize(&syntax, "MAIN")
            .expect("alias definition should internalize");
        assert!(!definition.symbols.contains_key("identity"));
        let application = parse_pattern("identity{SortValue{}}(value{}())")
            .expect("alias application should parse");
        assert_eq!(
            definition.internalize_term(&application, &[]).unwrap(),
            definition
                .internalize_term(&parse_pattern("value{}()").unwrap(), &[])
                .unwrap()
        );
    }

    #[test]
    fn expands_aliases_before_classifying_rewrite_axioms() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortValue{} []
                sort SortState{} []
                symbol value{}() : SortValue{} [constructor{}()]
                symbol state{}(SortValue{}) : SortState{} [constructor{}()]
                symbol done{}() : SortState{} [constructor{}()]
                alias stateAlias{}(SortValue{}) : SortState{}
                    where stateAlias{}(X:SortValue{}) := state{}(X:SortValue{}) []
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                        stateAlias{}(value{}()),
                        \top{SortState{}}()
                    ),
                    done{}()
                ) [label{}("aliased-rewrite")]
            endmodule []
        "#})
        .expect("aliased rewrite definition should parse");

        let definition = BackendDefinition::internalize(&syntax, "MAIN")
            .expect("aliased rewrite should internalize");
        let rules = definition
            .rewrite_theory
            .values()
            .flat_map(|groups| groups.values())
            .flatten()
            .collect::<Vec<_>>();
        let [rule] = rules.as_slice() else {
            panic!("expected one expanded rewrite rule, found {rules:?}");
        };
        assert_eq!(
            rule.lhs,
            definition
                .internalize_term(&parse_pattern("state{}(value{}())").unwrap(), &[])
                .unwrap()
        );
    }

    /// A module of `aliases` chained as `al{i}(X) := pair(al{i+1}(X), al{i+1}(X))`, so that
    /// `al0` unfolds to `2^aliases` occurrences of its argument, and of `axioms`.
    fn doubling_alias_chain(aliases: usize, axioms: &str) -> kore::Definition {
        let mut source = String::from(indoc! {r#"
            []
            module MAIN
                sort S{} []
                symbol pair{}(S{}, S{}) : S{} [constructor{}()]
                symbol a{}() : S{} [constructor{}()]
        "#});
        for index in 0..aliases {
            let body = if index + 1 == aliases {
                "pair{}(X:S{}, X:S{})".to_owned()
            } else {
                let next = index + 1;
                format!("pair{{}}(al{next}{{}}(X:S{{}}), al{next}{{}}(X:S{{}}))")
            };
            source.push_str(&format!(
                "    alias al{index}{{}}(S{{}}) : S{{}} where al{index}{{}}(X:S{{}}) := {body} []\n"
            ));
        }
        source.push_str(axioms);
        source.push_str("endmodule []\n");
        parse_definition(&source).expect("the chain should parse")
    }

    /// Alias unfolding can be exponential in the definition: a module of a few kilobytes can
    /// imply an unfolding of 2^64 nodes. Loading measures the aliases without unfolding them, and
    /// refuses the axioms or request patterns whose unfolding would be too large to build.
    #[test]
    fn refuses_alias_unfoldings_too_large_to_use_before_building_them() {
        // The aliases alone load: what an alias unfolds to depends on what it is applied to.
        let definition = BackendDefinition::internalize(&doubling_alias_chain(64, ""), "MAIN")
            .expect("the chain should load");
        let pattern = parse_pattern("al0{}(a{}())").unwrap();
        assert!(matches!(
            definition.internalize_pattern(&pattern, &[]),
            Err(DefinitionError::AliasUnfoldingTooLarge { .. })
        ));
        assert!(matches!(
            BackendDefinition::internalize(
                &doubling_alias_chain(64, "axiom{} \\equals{S{}, S{}}(a{}(), al0{}(a{}())) []\n"),
                "MAIN"
            ),
            Err(DefinitionError::AliasUnfoldingTooLarge { .. })
        ));

        // `al0` of an 18-alias chain adds about 2.4 million to an application, within the limit,
        // and twice that is beyond it.
        let axiom = indoc! {r#"
            axiom{} \rewrites{S{}}(
                \and{S{}}(pair{}(al0{}(X:S{}), al0{}(X:S{})), \top{S{}}()),
                a{}()
            ) []
        "#};
        assert!(matches!(
            BackendDefinition::internalize(&doubling_alias_chain(18, axiom), "MAIN"),
            Err(DefinitionError::AliasUnfoldingTooLarge { .. })
        ));
        let definition = BackendDefinition::internalize(&doubling_alias_chain(18, ""), "MAIN")
            .expect("the chain should load");
        let pattern = parse_pattern("pair{}(al0{}(X:S{}), al0{}(X:S{}))").unwrap();
        assert!(matches!(
            definition.internalize_pattern(&pattern, &[]),
            Err(DefinitionError::AliasUnfoldingTooLarge { .. })
        ));
    }

    /// A closed alias applied by many axioms unfolds to a copy of its body at each application,
    /// as the alias of a priority group's rules does in every rule of a later group: an unfolding
    /// that grows with the product of the axioms and the body, not exponentially. A definition
    /// whose axioms add more than the floor `UNFOLDING_LIMIT` (12 copies of a body of about
    /// 360,000 units), but less than `UNFOLDING_FACTOR` times the definition's own size, loads.
    #[test]
    fn loads_a_closed_alias_applied_by_many_axioms_beyond_the_floor() {
        const DISJUNCTS: usize = 40_000;
        const RULES: usize = 12;
        let mut source = String::from(indoc! {r#"
            []
            module MAIN
                sort S{} []
                symbol pair{}(S{}, S{}) : S{} [constructor{}()]
                symbol a{}() : S{} [constructor{}()]
        "#});
        let body = vec!["pair{}(a{}(), a{}())"; DISJUNCTS].join(", ");
        source.push_str(&format!(
            "    alias earlier{{}}() : S{{}} where earlier{{}}() := \\or{{S{{}}}}({body}) []\n"
        ));
        for rule in 0..RULES {
            source.push_str(&format!(
                "    axiom{{}} \\rewrites{{S{{}}}}(\\and{{S{{}}}}(\\not{{S{{}}}}(earlier{{}}()), pair{{}}(X:S{{}}, a{{}}())), a{{}}()) [label{{}}(\"later{rule}\")]\n"
            ));
        }
        source.push_str("endmodule []\n");
        let definition = parse_definition(&source).expect("the definition should parse");

        let loaded = BackendDefinition::internalize(&definition, "MAIN")
            .expect("an unfolding within a multiple of the definition's size should load");
        assert_eq!(loaded.classified_axioms().len(), RULES);
    }

    /// A definition's budget is `UNFOLDING_FACTOR` times its own size as written, each axiom,
    /// claim, and alias body counted once, and no more: one axiom that applies a closed alias of
    /// about 360,000 units 40 times, more than 32 times the definition's size, is refused before
    /// anything is built, with exactly that budget available.
    #[test]
    fn refuses_a_definition_whose_unfolding_exceeds_a_multiple_of_its_size() {
        const DISJUNCTS: usize = 40_000;
        const APPLICATIONS: usize = 40;
        let mut source = String::from(indoc! {r#"
            []
            module MAIN
                sort S{} []
                symbol pair{}(S{}, S{}) : S{} [constructor{}()]
                symbol a{}() : S{} [constructor{}()]
        "#});
        let body = vec!["pair{}(a{}(), a{}())"; DISJUNCTS].join(", ");
        source.push_str(&format!(
            "    alias earlier{{}}() : S{{}} where earlier{{}}() := \\or{{S{{}}}}({body}) []\n"
        ));
        let applications = vec!["earlier{}()"; APPLICATIONS].join(", ");
        source.push_str(&format!(
            "    axiom{{}} \\rewrites{{S{{}}}}(\\and{{S{{}}}}(\\not{{S{{}}}}(\\or{{S{{}}}}({applications})), pair{{}}(X:S{{}}, a{{}}())), a{{}}()) [label{{}}(\"later\")]\n"
        ));
        source.push_str("endmodule []\n");
        let definition = parse_definition(&source).expect("the definition should parse");
        let written = definition.modules[0]
            .sentences
            .iter()
            .map(|sentence| match sentence {
                kore::Sentence::AliasDeclaration { right, .. } => crate::alias::size(right),
                kore::Sentence::Axiom { pattern, .. } => crate::alias::size(pattern),
                kore::Sentence::Import { .. }
                | kore::Sentence::SortDeclaration { .. }
                | kore::Sentence::SymbolDeclaration { .. }
                | kore::Sentence::Claim { .. } => 0,
            })
            .sum::<u64>();
        let budget = crate::alias::UNFOLDING_FACTOR * written;
        assert!(budget > crate::alias::UNFOLDING_LIMIT);

        match BackendDefinition::internalize(&definition, "MAIN") {
            Err(DefinitionError::AliasUnfoldingTooLarge { added, available }) => {
                assert_eq!(available, budget);
                assert!(added > available);
            }
            Ok(_) => panic!("an unfolding beyond a multiple of the definition's size loaded"),
            Err(error) => panic!("unexpected error: {error:?}"),
        }
    }

    /// An alias argument that the alias keeps no copy of is not unfolded at all: an axiom and a
    /// request that wrap the 64-alias chain in `drop`, which ignores its parameter, or in
    /// `shadow`, which only uses it under a binder that shadows it, load and internalize at
    /// once, and so does an alias whose body drops an application of the chain.
    #[test]
    fn alias_arguments_that_are_dropped_are_never_unfolded() {
        let aliases = indoc! {r#"
            alias drop{}(S{}) : S{} where drop{}(X:S{}) := a{}() []
            alias shadow{}(S{}) : S{} where shadow{}(X:S{}) := \exists{S{}}(X:S{}, X:S{}) []
            alias hide{}(S{}) : S{} where hide{}(X:S{}) := drop{}(al0{}(X:S{})) []
        "#};
        for applied in ["drop{}(al0{}(X:S{}))", "hide{}(X:S{})"] {
            let axiom = format!(
                "axiom{{}} \\rewrites{{S{{}}}}(\\and{{S{{}}}}({applied}, \\top{{S{{}}}}()), a{{}}()) []\n"
            );
            BackendDefinition::internalize(
                &doubling_alias_chain(64, &format!("{aliases}{axiom}")),
                "MAIN",
            )
            .unwrap_or_else(|error| panic!("{applied}: {error}"));
        }
        let definition = BackendDefinition::internalize(&doubling_alias_chain(64, aliases), "MAIN")
            .expect("the chain should load");
        let pattern = parse_pattern("drop{}(al0{}(a{}()))").unwrap();
        assert!(definition.internalize_pattern(&pattern, &[]).is_ok());
        // `\exists{S{}}(X:S{}, X:S{})` is no term, which internalization refuses once unfolded.
        let pattern = parse_pattern("shadow{}(al0{}(a{}()))").unwrap();
        assert!(matches!(
            definition.internalize_pattern(&pattern, &[]),
            Err(DefinitionError::RulePattern(RulePatternError::MissingTerm))
        ));
    }

    #[test]
    fn rejects_recursive_alias_expansion_with_the_cycle() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortValue{} []
                symbol value{}() : SortValue{} [constructor{}()]
                alias loop{}(SortValue{}) : SortValue{}
                    where loop{}(X:SortValue{}) := loop{}(X:SortValue{}) []
            endmodule []
        "#})
        .expect("recursive alias definition should parse");
        assert_eq!(
            BackendDefinition::internalize(&syntax, "MAIN").unwrap_err(),
            DefinitionError::AliasCycle(vec!["loop".into(), "loop".into()])
        );
    }

    #[test]
    fn implication_patterns_reject_aliases_and_macros() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortValue{} []
                symbol value{}() : SortValue{} [constructor{}()]
                symbol macroValue{}() : SortValue{} [constructor{}(), macro{}()]
                alias identity{}(SortValue{}) : SortValue{}
                    where identity{}(X:SortValue{}) := X:SortValue{} []
            endmodule []
        "#})
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");

        for (source, expected) in [
            (
                "identity{}(value{}())",
                DefinitionError::MacroOrAliasInImplication("identity".into()),
            ),
            (
                "macroValue{}()",
                DefinitionError::MacroOrAliasInImplication("macroValue".into()),
            ),
        ] {
            let pattern = parse_pattern(source).expect("pattern should parse");
            let symbol = match &expected {
                DefinitionError::MacroOrAliasInImplication(symbol) => symbol.clone(),
                _ => unreachable!("the table contains only macro-or-alias failures"),
            };
            assert_eq!(
                definition.validate_executable_pattern(&pattern),
                Err(DefinitionError::MacroOrAliasInExecutablePattern(symbol))
            );
            assert_eq!(
                definition
                    .internalize_implication_pattern(&pattern, &[])
                    .unwrap_err(),
                expected
            );
        }

        let pattern = parse_pattern(r#"\and{SortValue{}}(macroValue{}(), identity{}(value{}()))"#)
            .expect("pattern should parse");
        assert_eq!(
            definition.validate_implication_pattern(&pattern),
            Err(DefinitionError::MacroOrAliasInImplication(
                "macroValue".into()
            ))
        );
    }

    #[test]
    fn builds_function_simplification_and_ceil_theories() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortValue{} []
                symbol value{}() : SortValue{} [constructor{}()]
                symbol wrap{}(SortValue{}) : SortValue{} [constructor{}()]
                symbol f{}(SortValue{}) : SortValue{} [function{}()]
                axiom{R}
                    \implies{R}(
                        \and{R}(
                            \top{R}(),
                            \and{R}(
                                \in{SortValue{}, R}(X0:SortValue{}, wrap{}(X:SortValue{})),
                                \top{R}()
                            )
                        ),
                        \equals{SortValue{}, R}(
                            f{}(X0:SortValue{}),
                            \and{SortValue{}}(value{}(), \top{SortValue{}}())
                        )
                    )
                    [label{}("evaluate-f")]
                axiom{R}
                    \implies{R}(
                        \top{R}(),
                        \equals{SortValue{}, R}(
                            f{}(X:SortValue{}),
                            \and{SortValue{}}(X:SortValue{}, \top{SortValue{}}())
                        )
                    )
                    [label{}("simplify-f"), simplification{}()]
                axiom{R}
                    \implies{R}(
                        \top{R}(),
                        \equals{R, R}(
                            \ceil{SortValue{}, R}(f{}(X:SortValue{})),
                            \top{R}()
                        )
                    )
                    [label{}("ceil-f")]
            endmodule []
        "#})
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let index = crate::rule::TermIndex::Symbol("f".into());

        let function = &definition.function_theory[&index][&50][0];
        assert!(
            function
                .lhs
                .attributes()
                .variables
                .iter()
                .any(|variable| variable.name.as_ref() == "Eq#X")
        );
        assert!(definition.simplification_theory.contains_key(&index));
        let ceil = &definition.ceil_theory[&index][&50][0];
        assert!(matches!(
            ceil.rhs,
            crate::rule::RuleRhs::Predicates(ref predicates) if predicates.is_empty()
        ));
    }

    #[test]
    fn source_execution_order_changes_only_the_rewrite_theory() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortValue{} []
                symbol value{}() : SortValue{} [constructor{}()]
                symbol other{}() : SortValue{} [constructor{}()]
                symbol wrap{}(SortValue{}) : SortValue{} [constructor{}()]
                symbol f{}(SortValue{}) : SortValue{} [function{}()]
                axiom{} \rewrites{SortValue{}}(
                    \and{SortValue{}}(value{}(), \top{SortValue{}}()),
                    other{}()
                ) [UNIQUE'Unds'ID{}("rewrite-value")]
                axiom{} \rewrites{SortValue{}}(
                    \and{SortValue{}}(value{}(), \top{SortValue{}}()),
                    wrap{}(other{}())
                ) [UNIQUE'Unds'ID{}("rewrite-wrap")]
                axiom{R}
                    \implies{R}(
                        \and{R}(
                            \top{R}(),
                            \and{R}(
                                \in{SortValue{}, R}(X0:SortValue{}, wrap{}(X:SortValue{})),
                                \top{R}()
                            )
                        ),
                        \equals{SortValue{}, R}(
                            f{}(X0:SortValue{}),
                            \and{SortValue{}}(value{}(), \top{SortValue{}}())
                        )
                    )
                    [label{}("evaluate-f"), UNIQUE'Unds'ID{}("function")]
                axiom{R}
                    \implies{R}(
                        \top{R}(),
                        \equals{SortValue{}, R}(
                            f{}(X:SortValue{}),
                            \and{SortValue{}}(X:SortValue{}, \top{SortValue{}}())
                        )
                    )
                    [label{}("simplify-f"), UNIQUE'Unds'ID{}("simplification"), simplification{}()]
                axiom{R}
                    \implies{R}(
                        \top{R}(),
                        \equals{R, R}(
                            \ceil{SortValue{}, R}(f{}(X:SortValue{})),
                            \top{R}()
                        )
                    )
                    [label{}("ceil-f"), UNIQUE'Unds'ID{}("ceil")]
            endmodule []
        "#})
        .expect("mixed-theory definition should parse");
        let canonical = BackendDefinition::internalize(&syntax, "MAIN")
            .expect("mixed-theory definition should internalize");
        let canonical_order = canonical
            .rewrite_theory
            .values()
            .flat_map(BTreeMap::values)
            .flatten()
            .map(|rule| rule.attributes.unique_id.clone())
            .collect::<Vec<_>>();
        assert_eq!(canonical_order.len(), 2);
        let requested = canonical_order.iter().rev().cloned().collect::<Vec<_>>();

        let ordered =
            BackendDefinition::internalize_for_source_execution(&syntax, "MAIN", &requested)
                .expect("explicit rewrite order should internalize");
        let ordered_rewrites = ordered
            .rewrite_theory
            .values()
            .flat_map(BTreeMap::values)
            .flatten()
            .map(|rule| rule.attributes.unique_id.clone())
            .collect::<Vec<_>>();

        assert_eq!(ordered_rewrites, requested);
        assert_eq!(ordered.function_theory, canonical.function_theory);
        assert_eq!(
            ordered.simplification_theory,
            canonical.simplification_theory
        );
        assert_eq!(
            ordered.predicate_simplification_theory,
            canonical.predicate_simplification_theory
        );
        assert_eq!(ordered.ceil_theory, canonical.ceil_theory);
        assert_eq!(ordered.claims, canonical.claims);
        assert_eq!(ordered.classified_axioms, canonical.classified_axioms);
    }

    #[test]
    fn internalizes_smt_hooks_and_smtlib_symbol_names() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                symbol absolute{}(SortInt{}) : SortInt{}
                    [function{}(), total{}(), smt-hook{}("(ite (< #1 0) (- 0 #1) #1)")]
                symbol opaque{}(SortInt{}) : SortInt{}
                    [function{}(), total{}(), smtlib{}("opaque_int")]
                symbol hookWins{}(SortInt{}) : SortInt{}
                    [function{}(), total{}(), smt-hook{}("+"), smtlib{}("ignored")]
            endmodule []
        "#})
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");

        assert_eq!(
            definition.symbols["absolute"].attributes.smt,
            Some(SmtType::Hook(
                SExpr::parse("(ite (< #1 0) (- 0 #1) #1)").unwrap()
            ))
        );
        assert_eq!(
            definition.symbols["opaque"].attributes.smt,
            Some(SmtType::Lib("opaque_int".into()))
        );
        assert_eq!(
            definition.symbols["hookWins"].attributes.smt,
            Some(SmtType::Hook(SExpr::atom("+")))
        );
    }

    /// A variable name read from KORE is kept verbatim and must be a KORE identifier: patterns
    /// handed over in process (or as binary KORE) cannot spell a marked name of the backend.
    #[test]
    fn variable_names_are_read_verbatim_and_must_be_identifiers() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                sort SortS{} []
                symbol a{}() : SortS{} [constructor{}(), functional{}()]
            endmodule []
        "#})
        .unwrap();
        let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
        let sort_s = || kore::Sort::Application {
            name: "SortS".into(),
            arguments: Vec::new(),
        };
        let variable = |name: &str, kind| {
            kore::Pattern::Variable(kore::Variable {
                kind,
                name: name.into(),
                sort: sort_s(),
            })
        };
        for (name, kind) in [
            ("Ex-hX-b0", kore::VariableKind::Element),
            ("a-x", kore::VariableKind::Element),
            ("@Rule-hM", kore::VariableKind::Set),
        ] {
            let term = definition
                .internalize_term(&variable(name, kind), &[])
                .unwrap_or_else(|error| panic!("{name}: {error}"));
            let TermKind::Variable(read) = term.kind() else {
                panic!("{name} should read as a variable");
            };
            assert_eq!(read.name.as_ref(), name);
            assert_eq!(read.provenance(), None);
        }
        for (name, kind) in [
            ("Ex#X!0", kore::VariableKind::Element),
            ("Rule#X", kore::VariableKind::Element),
            ("X!apart0", kore::VariableKind::Element),
            ("@M", kore::VariableKind::Element),
            ("M", kore::VariableKind::Set),
            ("@Rule#M", kore::VariableKind::Set),
        ] {
            let error = definition
                .internalize_term(&variable(name, kind), &[])
                .expect_err(name);
            assert!(
                matches!(&error, DefinitionError::VariableName { name: read, .. } if read == name),
                "{name}: {error:?}"
            );
        }
        // A definition carries the same check: its rule variables are marked by the backend.
        let constrained = |term| kore::Pattern::And {
            sort: sort_s(),
            arguments: vec![term, kore::Pattern::Top { sort: sort_s() }],
        };
        let mut syntax = syntax;
        syntax.modules[0].sentences.push(kore::Sentence::Axiom {
            parameters: Vec::new(),
            pattern: Box::new(kore::Pattern::Rewrites {
                sort: sort_s(),
                left: Box::new(constrained(variable("X!0", kore::VariableKind::Element))),
                right: Box::new(constrained(variable("X!0", kore::VariableKind::Element))),
            }),
            attributes: Default::default(),
        });
        let result = BackendDefinition::internalize(&syntax, "MAIN");
        assert!(
            matches!(result, Err(DefinitionError::VariableName { .. })),
            "{:?}",
            result.err()
        );
    }
}
