//! Import-DAG resolution uses petgraph topological order and a colouring DFS for cycle reports.
//! A resolve costs O(M log M + E + sum n_m^2 * eq); visible sentences use bucketed equivalence dedup and signatures use O(S^2 * eq) dedup.
//! `Counter::KompileResolveCalls` counts invocations.
//!
//! Resolution of flat, name-based modules into an import graph.

use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet},
    fmt,
    sync::{Arc, OnceLock},
};

use k_rust_kore::measure::{self, Counter};
use petgraph::Direction::{Incoming, Outgoing};
use petgraph::algo::toposort;
use petgraph::graph::{DiGraph, NodeIndex};
use petgraph::visit::EdgeRef;

use super::ast::{Associativity, Attributes, Definition, FlatModule, ProductionItem, Sentence};
use super::catalog::ProductionCatalog;
use super::equivalence::{EquivalenceAccumulator, dedup_by_equivalence, push_if_inequivalent};
use crate::definition::AttributeKey;
use crate::kast::{Label, Sort, Term};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Error {
    DuplicateModule(String),
    MissingMainModule(String),
    MissingImport { module: String, import: String },
    SelfImport(String),
    CircularImports(Vec<String>),
}

impl std::fmt::Display for Error {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DuplicateModule(name) => write!(formatter, "module {name:?} is not unique"),
            Self::MissingMainModule(name) => {
                write!(formatter, "main module {name:?} was not found")
            }
            Self::MissingImport { module, import } => {
                write!(
                    formatter,
                    "module {module:?} imports missing module {import:?}"
                )
            }
            Self::SelfImport(name) => write!(formatter, "module {name:?} imports itself"),
            Self::CircularImports(path) => {
                write!(formatter, "circular module imports: {}", path.join(" -> "))
            }
        }
    }
}

impl std::error::Error for Error {}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ModuleId(pub(crate) NodeIndex);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ImportRef {
    pub module: ModuleId,
    pub public: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedModule {
    pub name: String,
    pub local_sentences: Vec<Arc<Sentence>>,
    pub attributes: Attributes,
}

#[derive(Clone, Copy, Debug)]
struct Import {
    public: bool,
}

type SentenceLocation = (ModuleId, usize);

// These keys may collide, but equivalent sentences must always have equal keys.
// Attributes and other omitted fields are checked by sentence_equivalent inside each bucket.
#[derive(Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct SentenceKey<'a>(SentenceKeyKind<'a>);

#[derive(Eq, Ord, PartialEq, PartialOrd)]
enum SentenceKeyKind<'a> {
    SyntaxSort(&'a [Sort], &'a Sort),
    SortSynonym(&'a Sort, &'a Sort),
    SyntaxLexical(&'a str, &'a str),
    Production(
        Option<&'a Label>,
        &'a [Sort],
        &'a Sort,
        usize,
        Option<FirstItem<'a>>,
    ),
    SyntaxAssociativity(u8),
    SyntaxPriority(usize),
    ContextAlias(SentenceBody<'a>),
    Context(SentenceBody<'a>),
    Rule(SentenceBody<'a>),
    Claim(SentenceBody<'a>),
    Configuration(SentenceBody<'a>),
    Bubble(&'a str, &'a str),
}

impl<'a> SentenceKey<'a> {
    pub(crate) fn of(sentence: &'a Sentence) -> Self {
        Self(match sentence {
            Sentence::SyntaxSort {
                parameters, sort, ..
            } => SentenceKeyKind::SyntaxSort(parameters, sort),
            Sentence::SortSynonym {
                new_sort, old_sort, ..
            } => SentenceKeyKind::SortSynonym(new_sort, old_sort),
            Sentence::SyntaxLexical { name, regex, .. } => {
                SentenceKeyKind::SyntaxLexical(name, regex)
            }
            Sentence::Production {
                label,
                parameters,
                sort,
                items,
                ..
            } => SentenceKeyKind::Production(
                label.as_ref(),
                parameters,
                sort,
                items.len(),
                items.first().map(|item| match item {
                    ProductionItem::NonTerminal { sort, name } => {
                        FirstItem::NonTerminal(sort, name.as_deref())
                    }
                    ProductionItem::RegexTerminal { regex, .. } => FirstItem::Regex(regex),
                    ProductionItem::Terminal(text) => FirstItem::Terminal(text),
                }),
            ),
            Sentence::SyntaxAssociativity { associativity, .. } => {
                SentenceKeyKind::SyntaxAssociativity(match associativity {
                    Associativity::Left => 0,
                    Associativity::Right => 1,
                    Associativity::NonAssoc => 2,
                    Associativity::Unspecified => 3,
                })
            }
            Sentence::SyntaxPriority { priorities, .. } => {
                SentenceKeyKind::SyntaxPriority(priorities.len())
            }
            Sentence::ContextAlias { body, .. } => {
                SentenceKeyKind::ContextAlias(SentenceBody(body))
            }
            Sentence::Context { body, .. } => SentenceKeyKind::Context(SentenceBody(body)),
            Sentence::Rule { body, .. } => SentenceKeyKind::Rule(SentenceBody(body)),
            Sentence::Claim { body, .. } => SentenceKeyKind::Claim(SentenceBody(body)),
            Sentence::Configuration { body, .. } => {
                SentenceKeyKind::Configuration(SentenceBody(body))
            }
            Sentence::Bubble {
                sentence_type,
                contents,
                ..
            } => SentenceKeyKind::Bubble(sentence_type, contents),
        })
    }
}

#[derive(Eq, Ord, PartialEq, PartialOrd)]
enum FirstItem<'a> {
    NonTerminal(&'a Sort, Option<&'a str>),
    Regex(&'a str),
    Terminal(&'a str),
}

// Ordinary Term equality also compares variable sorts; sentence equality does not.
// The key only has to agree with `term_equivalent`: equivalent bodies compare equal, and
// the order among the rest is a deterministic preorder walk with no fidelity claim.
struct SentenceBody<'a>(&'a Term);

impl PartialEq for SentenceBody<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}

impl Eq for SentenceBody<'_> {}

impl PartialOrd for SentenceBody<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SentenceBody<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        compare_erased_terms(self.0, other.0)
    }
}

/// Preorder comparison of the unannotated term with variable sorts erased.
// Invariant: each recursive visit consumes one input node or follows an unvisited graph edge, so the finite input bounds the remaining visits.
fn compare_erased_terms(left: &Term, right: &Term) -> Ordering {
    fn variant(term: &Term) -> u8 {
        match term {
            Term::InjectedLabel(_) => 0,
            Term::Rewrite { .. } => 1,
            Term::As { .. } => 2,
            Term::Variable { .. } => 3,
            Term::Sequence(_) => 4,
            Term::Apply { .. } => 5,
            Term::Token { .. } => 6,
            Term::Annotated { .. } => unreachable!("annotations are stripped before comparison"),
        }
    }
    fn slices(left: &[Term], right: &[Term]) -> Ordering {
        left.len().cmp(&right.len()).then_with(|| {
            left.iter()
                .zip(right)
                .map(|(left, right)| compare_erased_terms(left, right))
                .find(|ordering| ordering.is_ne())
                .unwrap_or(Ordering::Equal)
        })
    }

    let left = left.unannotated();
    let right = right.unannotated();
    variant(left)
        .cmp(&variant(right))
        .then_with(|| match (left, right) {
            (Term::InjectedLabel(left), Term::InjectedLabel(right)) => left.cmp(right),
            (
                Term::Rewrite {
                    left: left_lhs,
                    right: left_rhs,
                },
                Term::Rewrite {
                    left: right_lhs,
                    right: right_rhs,
                },
            ) => compare_erased_terms(left_lhs, right_lhs)
                .then_with(|| compare_erased_terms(left_rhs, right_rhs)),
            (
                Term::As {
                    pattern: left_pattern,
                    alias: left_alias,
                },
                Term::As {
                    pattern: right_pattern,
                    alias: right_alias,
                },
            ) => compare_erased_terms(left_pattern, right_pattern)
                .then_with(|| compare_erased_terms(left_alias, right_alias)),
            (Term::Variable { name: left, .. }, Term::Variable { name: right, .. }) => {
                left.cmp(right)
            }
            (Term::Sequence(left), Term::Sequence(right)) => slices(left, right),
            (
                Term::Apply {
                    label: left_label,
                    arguments: left_arguments,
                },
                Term::Apply {
                    label: right_label,
                    arguments: right_arguments,
                },
            ) => left_label
                .cmp(right_label)
                .then_with(|| slices(left_arguments, right_arguments)),
            (
                Term::Token {
                    token: left_token,
                    sort: left_sort,
                },
                Term::Token {
                    token: right_token,
                    sort: right_sort,
                },
            ) => left_token
                .cmp(right_token)
                .then_with(|| left_sort.cmp(right_sort)),
            _ => unreachable!("equal variants have matching shapes"),
        })
}

#[derive(Clone)]
pub struct ResolvedDefinition {
    graph: DiGraph<ResolvedModule, Import>,
    modules_by_name: BTreeMap<String, ModuleId>,
    main_module: ModuleId,
    dependency_order: Vec<ModuleId>,
    // The graph is immutable, with dense node indices and stable local sentence indices.
    // Clones share only coordinates; each read borrows sentences from its receiving graph.
    visible_sentences: Vec<OnceLock<Arc<[SentenceLocation]>>>,
    pub(crate) production_catalogs: Arc<Vec<OnceLock<Arc<ProductionCatalog<'static>>>>>,
}

impl fmt::Debug for ResolvedDefinition {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ResolvedDefinition")
            .field("graph", &self.graph)
            .field("modules_by_name", &self.modules_by_name)
            .field("main_module", &self.main_module)
            .field("dependency_order", &self.dependency_order)
            .finish()
    }
}

impl ResolvedDefinition {
    pub fn resolve(definition: &Definition) -> Result<Self, Error> {
        measure::bump(Counter::KompileResolveCalls);
        let mut modules = definition.modules.iter().collect::<Vec<_>>();
        modules.sort_by(|left, right| left.name.cmp(&right.name));

        for pair in modules.windows(2) {
            if pair[0].name == pair[1].name {
                return Err(Error::DuplicateModule(pair[0].name.clone()));
            }
        }

        // Invariant: processed entries have reached their recorded state, the pending collection is the discovered frontier, and each pop consumes one entry before unseen successors are added.
        let mut graph = DiGraph::new();
        let mut modules_by_name = BTreeMap::new();
        for module in &modules {
            let id = ModuleId(graph.add_node(ResolvedModule::from(*module)));
            modules_by_name.insert(module.name.clone(), id);
        }

        let Some(&main_module) = modules_by_name.get(&definition.main_module) else {
            return Err(Error::MissingMainModule(definition.main_module.clone()));
        };

        for module in modules {
            let module_id = modules_by_name[&module.name];
            let mut imports = module.imports.iter().collect::<Vec<_>>();
            imports.sort_by(|left, right| {
                left.name
                    .cmp(&right.name)
                    .then(left.public.cmp(&right.public))
            });
            imports.dedup_by(|left, right| left.name == right.name && left.public == right.public);
            for import in imports {
                let Some(&import_id) = modules_by_name.get(&import.name) else {
                    return Err(Error::MissingImport {
                        module: module.name.clone(),
                        import: import.name.clone(),
                    });
                };
                if module_id == import_id {
                    return Err(Error::SelfImport(module.name.clone()));
                }
                // Invariant: processed entries have reached their recorded state, the pending collection is the discovered frontier, and each pop consumes one entry before unseen successors are added.
                graph.add_edge(
                    module_id.0,
                    import_id.0,
                    Import {
                        public: import.public,
                    },
                );
            }
        }

        // Invariant: processed entries have reached their recorded state, the pending collection is the discovered frontier, and each pop consumes one entry before unseen successors are added.
        let mut dependency_order = match toposort(&graph, None) {
            Ok(order) => order.into_iter().map(ModuleId).collect::<Vec<_>>(),
            Err(_) => {
                return Err(Error::CircularImports(
                    find_cycle(&graph).expect("toposort reported a cycle"),
                ));
            }
        };
        dependency_order.reverse();
        // Invariant: processed entries have reached their recorded state, the pending collection is the discovered frontier, and each pop consumes one entry before unseen successors are added.
        let visible_sentences = (0..graph.node_count()).map(|_| OnceLock::new()).collect();
        let production_catalogs = (0..graph.node_count()).map(|_| OnceLock::new()).collect();

        Ok(Self {
            graph,
            modules_by_name,
            main_module,
            dependency_order,
            visible_sentences,
            production_catalogs: Arc::new(production_catalogs),
        })
    }

    pub fn main_module_id(&self) -> ModuleId {
        self.main_module
    }

    pub fn main_module(&self) -> &ResolvedModule {
        self.module(self.main_module)
    }

    /// Reuse resolved nodes and visible sentence selections for an updated flat definition.
    /// The module set and import graph are structural inputs; when either changes, rebuilding
    /// the graph is both simpler and required to preserve deterministic node coordinates.
    pub fn update(&self, previous: &Definition, definition: &Definition) -> Result<Self, Error> {
        if definition.main_module != self.main_module().name
            || definition.modules.len() != self.graph.node_count()
            || previous.modules.len() != self.graph.node_count()
        {
            return Self::resolve(definition);
        }

        let mut previous_by_name = BTreeMap::new();
        let mut next_by_name = BTreeMap::new();
        for module in &previous.modules {
            if previous_by_name
                .insert(module.name.as_str(), module)
                .is_some()
            {
                return Self::resolve(definition);
            }
        }
        for module in &definition.modules {
            if next_by_name.insert(module.name.as_str(), module).is_some() {
                return Self::resolve(definition);
            }
        }
        if previous.main_module != definition.main_module
            || previous_by_name.len() != self.modules_by_name.len()
            || next_by_name.len() != self.modules_by_name.len()
            || self.modules_by_name.keys().any(|name| {
                !previous_by_name.contains_key(name.as_str())
                    || !next_by_name.contains_key(name.as_str())
            })
            || self.modules_by_name.iter().any(|(name, &id)| {
                normalized_imports(previous_by_name[name.as_str()])
                    != normalized_imports(next_by_name[name.as_str()])
                    || normalized_imports(previous_by_name[name.as_str()])
                        != normalized_imports_from_resolved(self, id)
            })
        {
            return Self::resolve(definition);
        }

        let mut graph = self.graph.clone();
        let mut changed = vec![false; graph.node_count()];
        let mut syntax_changed = vec![false; graph.node_count()];
        for (name, &id) in &self.modules_by_name {
            let (same, same_syntax) =
                modules_identical(previous_by_name[name.as_str()], next_by_name[name.as_str()]);
            if !same {
                graph[id.0] = ResolvedModule::from(next_by_name[name.as_str()]);
                changed[id.0.index()] = true;
                syntax_changed[id.0.index()] = !same_syntax;
            }
        }

        let visible_invalid = reverse_reachable(&graph, &changed);
        let catalog_invalid = reverse_reachable(&graph, &syntax_changed);
        let visible_sentences = self
            .visible_sentences
            .iter()
            .enumerate()
            .map(|(index, previous)| {
                let lock = OnceLock::new();
                if !visible_invalid[index]
                    && let Some(locations) = previous.get()
                {
                    let _ = lock.set(Arc::clone(locations));
                }
                lock
            })
            .collect();
        let production_catalogs = self
            .production_catalogs
            .iter()
            .enumerate()
            .map(|(index, previous)| {
                let lock = OnceLock::new();
                if !catalog_invalid[index]
                    && let Some(catalog) = previous.get()
                {
                    let _ = lock.set(Arc::clone(catalog));
                }
                lock
            })
            .collect();
        measure::bump(Counter::KompileResolveUpdates);
        Ok(Self {
            graph,
            modules_by_name: self.modules_by_name.clone(),
            main_module: self.main_module,
            dependency_order: self.dependency_order.clone(),
            visible_sentences,
            production_catalogs: Arc::new(production_catalogs),
        })
    }

    pub fn module_id(&self, name: &str) -> Option<ModuleId> {
        self.modules_by_name.get(name).copied()
    }

    pub fn module(&self, id: ModuleId) -> &ResolvedModule {
        &self.graph[id.0]
    }

    pub fn modules(&self) -> impl Iterator<Item = (ModuleId, &ResolvedModule)> {
        self.dependency_order
            .iter()
            .copied()
            .map(|id| (id, self.module(id)))
    }

    /// Modules in deterministic dependency-first topological order.
    pub fn dependency_order(&self) -> &[ModuleId] {
        &self.dependency_order
    }

    pub fn direct_imports(&self, module: ModuleId) -> Vec<ImportRef> {
        let mut imports = self
            .graph
            // Invariant: processed entries have reached their recorded state, the pending collection is the discovered frontier, and each pop consumes one entry before unseen successors are added.
            .edges_directed(module.0, Outgoing)
            .map(|edge| ImportRef {
                module: ModuleId(edge.target()),
                public: edge.weight().public,
            })
            .collect::<Vec<_>>();
        imports.sort_by(|left, right| {
            self.module(left.module)
                .name
                .cmp(&self.module(right.module).name)
                .then(left.public.cmp(&right.public))
        });
        imports
    }

    /// All transitively imported modules, sorted by module name.
    pub fn transitive_imports(&self, module: ModuleId) -> Vec<ModuleId> {
        let mut found = BTreeSet::new();
        let mut pending = self
            .direct_imports(module)
            .into_iter()
            .map(|import| import.module)
            .collect::<Vec<_>>();
        // Invariant: `found` contains expanded imports and `pending` contains discovered imports
        // not yet expanded; a module is expanded only after its first insertion into `found`.
        while let Some(import) = pending.pop() {
            if found.insert(import) {
                pending.extend(
                    self.direct_imports(import)
                        .into_iter()
                        .map(|next| next.module),
                );
            }
        }
        found.into_iter().collect()
    }

    /// Local and transitively imported sentences, with dependencies first.
    pub fn sentences(&self, module: ModuleId) -> Vec<&Sentence> {
        let locations = self.visible_sentences[module.0.index()]
            .get_or_init(|| self.select_sentence_locations(module));
        locations
            .iter()
            .map(|&(owner, index)| self.module(owner).local_sentences[index].as_ref())
            .collect()
    }

    /// Local and visible sentences as shared nodes for derived owned views.
    pub(crate) fn sentence_arcs(&self, module: ModuleId) -> Vec<Arc<Sentence>> {
        let locations = self.visible_sentences[module.0.index()]
            .get_or_init(|| self.select_sentence_locations(module));
        locations
            .iter()
            .map(|&(owner, index)| Arc::clone(&self.module(owner).local_sentences[index]))
            .collect()
    }

    pub(crate) fn local_sentence_arcs(
        &self,
        module: ModuleId,
    ) -> impl Iterator<Item = Arc<Sentence>> + '_ {
        self.module(module).local_sentences.iter().cloned()
    }

    fn select_sentence_locations(&self, module: ModuleId) -> Arc<[SentenceLocation]> {
        let mut visible = self.transitive_imports(module);
        visible.push(module);
        let visible = visible.into_iter().collect::<BTreeSet<_>>();
        let mut unique = EquivalenceAccumulator::new();
        let mut locations = Vec::new();
        for (owner, index, sentence) in self
            .dependency_order
            .iter()
            .filter(|id| visible.contains(id))
            .flat_map(|&id| {
                self.module(id)
                    .local_sentences
                    .iter()
                    .enumerate()
                    .map(move |(index, sentence)| (id, index, sentence.as_ref()))
            })
        {
            if push_if_inequivalent(&mut unique, sentence) {
                locations.push((owner, index));
            }
        }
        locations.into()
    }

    /// Scala's `Module.signature`: local sentences plus the exported sentences
    /// of every direct import, following only public imports after that first edge.
    pub fn signature_sentences(&self, module: ModuleId) -> Vec<&Sentence> {
        let mut exported_modules = BTreeSet::new();
        let mut pending = self
            .direct_imports(module)
            .into_iter()
            .map(|import| import.module)
            .collect::<Vec<_>>();
        // Invariant: `exported_modules` contains expanded imports and `pending` contains the
        // public-import frontier; each module is expanded at most once.
        while let Some(import) = pending.pop() {
            if exported_modules.insert(import) {
                pending.extend(
                    self.direct_imports(import)
                        .into_iter()
                        .filter(|next| next.public)
                        .map(|next| next.module),
                );
            }
        }

        let sentences = self
            .dependency_order
            .iter()
            .filter(|module| exported_modules.contains(module))
            .flat_map(|module| self.public_sentences(*module))
            .chain(self.module(module).local_sentences.iter().map(Arc::as_ref));
        dedup_by_equivalence(sentences)
    }

    /// Scala's `publicSentences`: the local sentences exported by a module signature.
    pub fn public_sentences(&self, module: ModuleId) -> Vec<&Sentence> {
        let module = self.module(module);
        let module_is_private = module.attributes.has(AttributeKey::Private);
        module
            .local_sentences
            .iter()
            .filter(|sentence| {
                if module_is_private {
                    sentence.attributes().has(AttributeKey::Public)
                } else {
                    !sentence.attributes().has(AttributeKey::Private)
                }
            })
            .map(Arc::as_ref)
            .collect()
    }
}

fn normalized_imports(module: &FlatModule) -> Vec<(&str, bool)> {
    let mut imports = module
        .imports
        .iter()
        .map(|import| (import.name.as_str(), import.public))
        .collect::<Vec<_>>();
    imports.sort_unstable();
    imports.dedup();
    imports
}

fn normalized_imports_from_resolved(
    resolved: &ResolvedDefinition,
    module: ModuleId,
) -> Vec<(&str, bool)> {
    let mut imports = resolved
        .direct_imports(module)
        .into_iter()
        .map(|import| (resolved.module(import.module).name.as_str(), import.public))
        .collect::<Vec<_>>();
    imports.sort_unstable();
    imports.dedup();
    imports
}

fn modules_identical(previous: &FlatModule, next: &FlatModule) -> (bool, bool) {
    let same_header = previous.name == next.name
        && previous.imports == next.imports
        && previous.attributes.identical(&next.attributes);
    let same_sentences = previous.local_sentences.len() == next.local_sentences.len()
        && previous
            .local_sentences
            .iter()
            .zip(&next.local_sentences)
            .all(|(left, right)| {
                measure::bump(Counter::KompileResolveUpdateSentenceVisits);
                sentences_identical(left, right)
            });
    let identical = same_header && same_sentences;
    let syntax_identical = identical
        || iter_identical(
            previous
                .local_sentences
                .iter()
                .filter(|sentence| is_syntax_sentence(sentence)),
            next.local_sentences
                .iter()
                .filter(|sentence| is_syntax_sentence(sentence)),
        );
    (identical, syntax_identical)
}

fn iter_identical<'a>(
    mut left: impl Iterator<Item = &'a Sentence>,
    mut right: impl Iterator<Item = &'a Sentence>,
) -> bool {
    loop {
        match (left.next(), right.next()) {
            (Some(left), Some(right)) if sentences_identical(left, right) => {}
            (None, None) => return true,
            _ => return false,
        }
    }
}

fn sentences_identical(left: &Sentence, right: &Sentence) -> bool {
    match (left, right) {
        (
            Sentence::SyntaxSort {
                parameters: left_parameters,
                sort: left_sort,
                attributes: left_attributes,
            },
            Sentence::SyntaxSort {
                parameters: right_parameters,
                sort: right_sort,
                attributes: right_attributes,
            },
        ) => {
            left_parameters == right_parameters
                && left_sort == right_sort
                && left_attributes.identical(right_attributes)
        }
        (
            Sentence::SortSynonym {
                new_sort: left_new,
                old_sort: left_old,
                attributes: left_attributes,
            },
            Sentence::SortSynonym {
                new_sort: right_new,
                old_sort: right_old,
                attributes: right_attributes,
            },
        ) => {
            left_new == right_new
                && left_old == right_old
                && left_attributes.identical(right_attributes)
        }
        (
            Sentence::SyntaxLexical {
                name: left_name,
                regex: left_regex,
                attributes: left_attributes,
            },
            Sentence::SyntaxLexical {
                name: right_name,
                regex: right_regex,
                attributes: right_attributes,
            },
        ) => {
            left_name == right_name
                && left_regex == right_regex
                && left_attributes.identical(right_attributes)
        }
        (
            Sentence::Production {
                label: left_label,
                parameters: left_parameters,
                sort: left_sort,
                items: left_items,
                attributes: left_attributes,
            },
            Sentence::Production {
                label: right_label,
                parameters: right_parameters,
                sort: right_sort,
                items: right_items,
                attributes: right_attributes,
            },
        ) => {
            left_label == right_label
                && left_parameters == right_parameters
                && left_sort == right_sort
                && left_items == right_items
                && left_attributes.identical(right_attributes)
        }
        (
            Sentence::SyntaxAssociativity {
                associativity: left_associativity,
                tags: left_tags,
                attributes: left_attributes,
            },
            Sentence::SyntaxAssociativity {
                associativity: right_associativity,
                tags: right_tags,
                attributes: right_attributes,
            },
        ) => {
            left_associativity == right_associativity
                && left_tags == right_tags
                && left_attributes.identical(right_attributes)
        }
        (
            Sentence::SyntaxPriority {
                priorities: left_priorities,
                attributes: left_attributes,
            },
            Sentence::SyntaxPriority {
                priorities: right_priorities,
                attributes: right_attributes,
            },
        ) => left_priorities == right_priorities && left_attributes.identical(right_attributes),
        (
            Sentence::ContextAlias {
                body: left_body,
                requires: left_requires,
                attributes: left_attributes,
            },
            Sentence::ContextAlias {
                body: right_body,
                requires: right_requires,
                attributes: right_attributes,
            },
        ) => {
            left_body.identical(right_body)
                && left_requires.identical(right_requires)
                && left_attributes.identical(right_attributes)
        }
        (
            Sentence::Context {
                body: left_body,
                requires: left_requires,
                attributes: left_attributes,
            },
            Sentence::Context {
                body: right_body,
                requires: right_requires,
                attributes: right_attributes,
            },
        ) => {
            left_body.identical(right_body)
                && left_requires.identical(right_requires)
                && left_attributes.identical(right_attributes)
        }
        (
            Sentence::Rule {
                body: left_body,
                requires: left_requires,
                ensures: left_ensures,
                attributes: left_attributes,
            },
            Sentence::Rule {
                body: right_body,
                requires: right_requires,
                ensures: right_ensures,
                attributes: right_attributes,
            },
        ) => {
            left_body.identical(right_body)
                && left_requires.identical(right_requires)
                && left_ensures.identical(right_ensures)
                && left_attributes.identical(right_attributes)
        }
        (
            Sentence::Claim {
                body: left_body,
                requires: left_requires,
                ensures: left_ensures,
                attributes: left_attributes,
            },
            Sentence::Claim {
                body: right_body,
                requires: right_requires,
                ensures: right_ensures,
                attributes: right_attributes,
            },
        ) => {
            left_body.identical(right_body)
                && left_requires.identical(right_requires)
                && left_ensures.identical(right_ensures)
                && left_attributes.identical(right_attributes)
        }
        (
            Sentence::Configuration {
                body: left_body,
                ensures: left_ensures,
                attributes: left_attributes,
            },
            Sentence::Configuration {
                body: right_body,
                ensures: right_ensures,
                attributes: right_attributes,
            },
        ) => {
            left_body.identical(right_body)
                && left_ensures.identical(right_ensures)
                && left_attributes.identical(right_attributes)
        }
        (
            Sentence::Bubble {
                sentence_type: left_type,
                contents: left_contents,
                attributes: left_attributes,
            },
            Sentence::Bubble {
                sentence_type: right_type,
                contents: right_contents,
                attributes: right_attributes,
            },
        ) => {
            left_type == right_type
                && left_contents == right_contents
                && left_attributes.identical(right_attributes)
        }
        _ => false,
    }
}

fn reverse_reachable(graph: &DiGraph<ResolvedModule, Import>, roots: &[bool]) -> Vec<bool> {
    let mut reached = roots.to_vec();
    let mut pending = roots
        .iter()
        .enumerate()
        .filter_map(|(index, root)| root.then_some(NodeIndex::new(index)))
        .collect::<Vec<_>>();
    while let Some(node) = pending.pop() {
        for importer in graph.neighbors_directed(node, Incoming) {
            if !reached[importer.index()] {
                reached[importer.index()] = true;
                pending.push(importer);
            }
        }
    }
    reached
}

fn find_cycle(graph: &DiGraph<ResolvedModule, Import>) -> Option<Vec<String>> {
    // Invariant: each recursive visit consumes one input node or follows an unvisited graph edge, so the finite input bounds the remaining visits.
    fn visit(
        graph: &DiGraph<ResolvedModule, Import>,
        node: NodeIndex,
        state: &mut [u8],
        stack: &mut Vec<NodeIndex>,
    ) -> Option<Vec<String>> {
        state[node.index()] = 1;
        stack.push(node);

        // Invariant: each recursive visit consumes one input node or follows an unvisited graph edge, so the finite input bounds the remaining visits.
        let mut imports = graph.neighbors_directed(node, Outgoing).collect::<Vec<_>>();
        imports.sort_by(|left, right| graph[*left].name.cmp(&graph[*right].name));
        for import in imports {
            match state[import.index()] {
                0 => {
                    if let Some(cycle) = visit(graph, import, state, stack) {
                        return Some(cycle);
                    }
                }
                1 => {
                    // Invariant: each recursive visit consumes one input node or follows an unvisited graph edge, so the finite input bounds the remaining visits.
                    let start = stack
                        .iter()
                        .position(|candidate| *candidate == import)
                        .expect("visiting node must be on the DFS stack");
                    let mut cycle = stack[start..]
                        .iter()
                        .map(|node| graph[*node].name.clone())
                        .collect::<Vec<_>>();
                    cycle.push(graph[import].name.clone());
                    return Some(cycle);
                }
                _ => {}
            }
        }

        stack.pop();
        state[node.index()] = 2;
        None
    }

    // Invariant: each recursive visit consumes one input node or follows an unvisited graph edge, so the finite input bounds the remaining visits.
    let mut nodes = graph.node_indices().collect::<Vec<_>>();
    nodes.sort_by(|left, right| graph[*left].name.cmp(&graph[*right].name));
    let mut state = vec![0; graph.node_count()];
    let mut stack = Vec::new();
    for node in nodes {
        if state[node.index()] == 0
            && let Some(cycle) = visit(graph, node, &mut state, &mut stack)
        {
            return Some(cycle);
        }
    }
    None
}

impl TryFrom<&Definition> for ResolvedDefinition {
    type Error = Error;

    fn try_from(definition: &Definition) -> Result<Self, Self::Error> {
        Self::resolve(definition)
    }
}

impl From<&FlatModule> for ResolvedModule {
    fn from(module: &FlatModule) -> Self {
        Self {
            name: module.name.clone(),
            local_sentences: deduplicate_sentences(&module.local_sentences),
            attributes: module.attributes.clone(),
        }
    }
}

fn is_syntax_sentence(sentence: &Sentence) -> bool {
    matches!(
        sentence,
        Sentence::SyntaxSort { .. }
            | Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::Production { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
    )
}

fn deduplicate_sentences(sentences: &[Sentence]) -> Vec<Arc<Sentence>> {
    dedup_by_equivalence(sentences)
        .into_iter()
        .map(|sentence| Arc::new(sentence.clone()))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::super::ast::FlatImport;
    use super::*;

    fn module(name: &str, sentence: Sentence) -> FlatModule {
        FlatModule {
            name: name.into(),
            imports: Vec::new(),
            local_sentences: vec![sentence],
            attributes: Attributes::default(),
        }
    }

    fn sort_sentence(name: &str) -> Sentence {
        Sentence::SyntaxSort {
            parameters: Vec::new(),
            sort: Sort::new(name),
            attributes: Attributes::default(),
        }
    }

    #[test]
    fn update_matches_full_resolve_and_reuses_unchanged_nodes() {
        let initial = Definition {
            main_module: "MAIN".into(),
            modules: vec![
                module("MAIN", sort_sentence("K")),
                module("OTHER", sort_sentence("A")),
            ],
            attributes: Attributes::default(),
        };
        let base = ResolvedDefinition::resolve(&initial).unwrap();
        let mut next = initial.clone();
        next.modules[1].local_sentences[0] = sort_sentence("B");
        let updated = base.update(&initial, &next).unwrap();
        let resolved = ResolvedDefinition::resolve(&next).unwrap();
        assert_eq!(updated.dependency_order, resolved.dependency_order);
        for id in updated.dependency_order().iter().copied() {
            assert_eq!(updated.sentences(id), resolved.sentences(id));
        }
        let main = updated.module_id("MAIN").unwrap();
        assert!(Arc::ptr_eq(
            &base.module(main).local_sentences[0],
            &updated.module(main).local_sentences[0]
        ));
    }

    #[test]
    fn update_falls_back_when_imports_change() {
        let initial = Definition {
            main_module: "MAIN".into(),
            modules: vec![
                module("MAIN", sort_sentence("K")),
                module("OTHER", sort_sentence("A")),
            ],
            attributes: Attributes::default(),
        };
        let base = ResolvedDefinition::resolve(&initial).unwrap();
        let mut next = initial.clone();
        next.modules[0].imports.push(FlatImport {
            name: "OTHER".into(),
            public: true,
        });
        let updated = base.update(&initial, &next).unwrap();
        let resolved = ResolvedDefinition::resolve(&next).unwrap();
        assert_eq!(updated.dependency_order, resolved.dependency_order);
        for id in updated.dependency_order().iter().copied() {
            assert_eq!(updated.sentences(id), resolved.sentences(id));
        }
        assert_eq!(updated.sentences(updated.main_module_id()).len(), 2);
    }
}
