//! Memoised derived definition views scoped to one immutable resolution.
//!
//! ```toml algorithm-contract
//! id = "contract.definition.production_catalog_cache"
//! name = "lazy production-catalog view shared by its consumers"
//! sites = ["DefinitionViews::production_catalog"]
//! constrains = [{ id = "definition.catalog.production", site = "DefinitionViews::production_catalog", via = "ResolvedDefinition keeps one ProductionCatalog per module in a OnceLock that ResolvedDefinition::update carries forward while the module's visible syntax is unchanged; DefinitionViews caches an Arc to it" }]
//! ```

use std::sync::{Arc, OnceLock};

use super::partial_order::{Cycle, PartialOrder};
use super::relations::{self, AssociativityRelations, OverloadOrder};
use super::{ModuleId, ProductionCatalog, ResolvedDefinition, SortCatalog};
use crate::kast::Sort;

/// Lazily computed catalogs and relations for one [`ResolvedDefinition`].
pub struct DefinitionViews<'a> {
    definition: &'a ResolvedDefinition,
    production_catalogs: Vec<OnceLock<Arc<ProductionCatalog<'static>>>>,
    sort_catalogs: Vec<OnceLock<SortCatalog<'a>>>,
    subsorts: Vec<OnceLock<Result<PartialOrder<Sort>, Cycle<Sort>>>>,
    syntactic_subsorts: Vec<OnceLock<Result<PartialOrder<Sort>, Cycle<Sort>>>>,
    overloads: Vec<OnceLock<Result<OverloadOrder<'a>, relations::Error>>>,
    priorities: Vec<OnceLock<Result<PartialOrder<String>, Cycle<String>>>>,
    associativities: Vec<OnceLock<AssociativityRelations>>,
    rule_grammar_subsorts: Vec<OnceLock<Result<PartialOrder<Sort>, Cycle<Sort>>>>,
    importers: OnceLock<Vec<Vec<ModuleId>>>,
}

impl ResolvedDefinition {
    /// Create an empty memo for views derived from this resolution.
    pub fn views(&self) -> DefinitionViews<'_> {
        DefinitionViews::new(self)
    }
}

impl<'a> DefinitionViews<'a> {
    fn new(definition: &'a ResolvedDefinition) -> Self {
        fn locks<T>(modules: usize) -> Vec<OnceLock<T>> {
            (0..modules).map(|_| OnceLock::new()).collect()
        }
        let modules = definition.modules().count();
        Self {
            definition,
            production_catalogs: locks(modules),
            sort_catalogs: locks(modules),
            subsorts: locks(modules),
            syntactic_subsorts: locks(modules),
            overloads: locks(modules),
            priorities: locks(modules),
            associativities: locks(modules),
            rule_grammar_subsorts: locks(modules),
            importers: OnceLock::new(),
        }
    }

    pub fn definition(&self) -> &'a ResolvedDefinition {
        self.definition
    }

    pub fn production_catalog(&self, module: ModuleId) -> &ProductionCatalog<'a> {
        self.production_catalogs[module.0.index()]
            .get_or_init(|| self.definition.production_catalog(module))
    }

    // stack-accepted(import-chain): one level per module of an import chain; real chains are tens deep, 4,000 modules pass on 8 MiB, and compile time is already about n^1.6. See docs/backend-port.md#stack-bounds.
    pub fn sort_catalog(&self, module: ModuleId) -> &SortCatalog<'a> {
        self.sort_catalogs[module.0.index()].get_or_init(|| {
            let imported_sorts = self
                .definition
                .direct_imports(module)
                .into_iter()
                .flat_map(|import| self.sort_catalog(import.module).all_sorts().iter().cloned())
                .collect::<std::collections::BTreeSet<_>>();
            SortCatalog::new(self.definition.sentences(module), imported_sorts)
        })
    }

    pub fn subsorts(&self, module: ModuleId) -> Result<&PartialOrder<Sort>, &Cycle<Sort>> {
        self.subsorts[module.0.index()]
            .get_or_init(|| relations::compute_subsorts(self.definition.sentences(module), false))
            .as_ref()
    }

    pub fn syntactic_subsorts(
        &self,
        module: ModuleId,
    ) -> Result<&PartialOrder<Sort>, &Cycle<Sort>> {
        self.syntactic_subsorts[module.0.index()]
            .get_or_init(|| relations::compute_subsorts(self.definition.sentences(module), true))
            .as_ref()
    }

    pub fn overloads(&self, module: ModuleId) -> Result<&OverloadOrder<'a>, &relations::Error> {
        self.overloads[module.0.index()]
            .get_or_init(|| {
                let subsorts = self
                    .subsorts(module)
                    .map_err(|cycle| relations::Error::CircularSubsort(cycle.clone()))?;
                relations::compute_overloads_with_catalog(self.production_catalog(module), subsorts)
                    .map_err(relations::Error::CircularOverload)
            })
            .as_ref()
    }

    pub fn priorities(&self, module: ModuleId) -> Result<&PartialOrder<String>, &Cycle<String>> {
        self.priorities[module.0.index()]
            .get_or_init(|| relations::compute_priorities(self.definition.sentences(module)))
            .as_ref()
    }

    pub fn associativities(&self, module: ModuleId) -> &AssociativityRelations {
        self.associativities[module.0.index()]
            .get_or_init(|| relations::compute_associativities(self.definition.sentences(module)))
    }

    /// The order in which the rule grammar of `module` admits terms
    /// ([`super::checks::rule_grammar_subsorts`]).
    pub(crate) fn rule_grammar_subsorts(
        &self,
        module: ModuleId,
    ) -> Result<&PartialOrder<Sort>, &Cycle<Sort>> {
        self.rule_grammar_subsorts[module.0.index()]
            .get_or_init(|| {
                super::checks::rule_grammar_subsorts(&self.definition.sentences(module))
            })
            .as_ref()
    }

    /// The modules other than `module` whose view contains `module`'s sentences: those that import
    /// it, directly or not, in dependency order.
    pub(crate) fn importers(&self, module: ModuleId) -> &[ModuleId] {
        &self.importers.get_or_init(|| {
            let mut importers = vec![Vec::new(); self.production_catalogs.len()];
            // Invariant: `importers[i]` lists, in dependency order, every module before `importer`
            // whose transitive imports contain module `i`.
            for &importer in self.definition.dependency_order() {
                for imported in self.definition.transitive_imports(importer) {
                    importers[imported.0.index()].push(importer);
                }
            }
            importers
        })[module.0.index()]
    }
}
