//! Resolution of flat, name-based modules into an import graph.

use std::collections::{BTreeMap, BTreeSet};

use petgraph::Direction::Outgoing;
use petgraph::algo::toposort;
use petgraph::graph::{DiGraph, NodeIndex};
use petgraph::visit::EdgeRef;

use super::ast::{Attributes, Definition, FlatModule, Sentence};

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
pub struct ModuleId(NodeIndex);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ImportRef {
    pub module: ModuleId,
    pub public: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedModule {
    pub name: String,
    pub local_sentences: Vec<Sentence>,
    pub attributes: Attributes,
}

#[derive(Clone, Copy, Debug)]
struct Import {
    public: bool,
}

#[derive(Clone, Debug)]
pub struct ResolvedDefinition {
    graph: DiGraph<ResolvedModule, Import>,
    modules_by_name: BTreeMap<String, ModuleId>,
    main_module: ModuleId,
    dependency_order: Vec<ModuleId>,
}

impl ResolvedDefinition {
    pub fn resolve(definition: &Definition) -> Result<Self, Error> {
        let mut modules = definition.modules.iter().collect::<Vec<_>>();
        modules.sort_by(|left, right| left.name.cmp(&right.name));

        for pair in modules.windows(2) {
            if pair[0].name == pair[1].name {
                return Err(Error::DuplicateModule(pair[0].name.clone()));
            }
        }

        let mut graph = DiGraph::new();
        let mut modules_by_name = BTreeMap::new();
        for module in &modules {
            let id = ModuleId(graph.add_node(ResolvedModule {
                name: module.name.clone(),
                local_sentences: deduplicate_sentences(&module.local_sentences),
                attributes: module.attributes.clone(),
            }));
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
                graph.add_edge(
                    module_id.0,
                    import_id.0,
                    Import {
                        public: import.public,
                    },
                );
            }
        }

        let mut dependency_order = match toposort(&graph, None) {
            Ok(order) => order.into_iter().map(ModuleId).collect::<Vec<_>>(),
            Err(_) => {
                return Err(Error::CircularImports(
                    find_cycle(&graph).expect("toposort reported a cycle"),
                ));
            }
        };
        dependency_order.reverse();

        Ok(Self {
            graph,
            modules_by_name,
            main_module,
            dependency_order,
        })
    }

    pub fn main_module_id(&self) -> ModuleId {
        self.main_module
    }

    pub fn main_module(&self) -> &ResolvedModule {
        self.module(self.main_module)
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
        let mut visible = self.transitive_imports(module);
        visible.push(module);
        let visible = visible.into_iter().collect::<BTreeSet<_>>();
        let mut sentences = Vec::new();
        for sentence in self
            .dependency_order
            .iter()
            .filter(|id| visible.contains(id))
            .flat_map(|id| self.module(*id).local_sentences.iter())
        {
            if !sentences.contains(&sentence) {
                sentences.push(sentence);
            }
        }
        sentences
    }

    /// Scala's `publicSentences`: the local sentences exported by a module signature.
    pub fn public_sentences(&self, module: ModuleId) -> Vec<&Sentence> {
        let module = self.module(module);
        let module_is_private = module.attributes.get("private").is_some();
        module
            .local_sentences
            .iter()
            .filter(|sentence| {
                if module_is_private {
                    sentence.attributes().get("public").is_some()
                } else {
                    sentence.attributes().get("private").is_none()
                }
            })
            .collect()
    }
}

fn find_cycle(graph: &DiGraph<ResolvedModule, Import>) -> Option<Vec<String>> {
    fn visit(
        graph: &DiGraph<ResolvedModule, Import>,
        node: NodeIndex,
        state: &mut [u8],
        stack: &mut Vec<NodeIndex>,
    ) -> Option<Vec<String>> {
        state[node.index()] = 1;
        stack.push(node);

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

fn deduplicate_sentences(sentences: &[Sentence]) -> Vec<Sentence> {
    let mut unique = Vec::new();
    for sentence in sentences {
        if !unique.contains(sentence) {
            unique.push(sentence.clone());
        }
    }
    unique
}
