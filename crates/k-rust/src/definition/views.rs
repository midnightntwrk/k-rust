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
///
/// The per-module views are memoised in the resolution itself ([`ModuleViews`]), so every
/// `DefinitionViews` of one resolution shares them, and [`ResolvedDefinition::update`] carries
/// them into the next resolution while their inputs are unchanged.
pub struct DefinitionViews<'a> {
    definition: &'a ResolvedDefinition,
    production_catalogs: Vec<OnceLock<Arc<ProductionCatalog<'static>>>>,
    importers: OnceLock<Vec<Vec<ModuleId>>>,
}

type SubsortView = Result<PartialOrder<Sort>, Cycle<Sort>>;

/// The views of one module that are functions of the syntax sentences of its import closure.
///
/// Each constructor reads only the module's visible sentences ([`ResolvedDefinition::sentences`])
/// and, for the sort catalog, the sort catalogs of its direct imports, whose views are subsets of
/// the closure; and of those sentences only syntax kinds ([`super::Sentence::is_syntax`]):
///
/// | view | sentence kinds read |
/// | --- | --- |
/// | `sort_catalog` | `SyntaxSort` (sort, parameters, attributes), `SortSynonym`, `Production` (sort, parameters, `token`, `userList`) |
/// | `subsorts`, `syntactic_subsorts` | `Production` (label, parameters, sort, items, `token`) |
/// | `overloads` | `Production`, through the module's production catalog and `subsorts` |
/// | `priorities` | `SyntaxPriority` |
/// | `associativities` | `SyntaxAssociativity` |
/// | `rule_grammar_subsorts` | `Production` (as `subsorts`, plus `userList`), `SyntaxSort` (sort) |
///
/// Every view is an owned value of what it read: none holds a sentence of the resolution, and
/// the overload order holds only the module's production catalog, which is memoised beside it
/// under the same condition. Errors are cycles of sorts or of catalog ids, values of the same
/// inputs. Each view is held behind an `Arc` so that a resolution updated from this one can
/// share the values already built.
#[derive(Default)]
pub(crate) struct ModuleViews {
    sort_catalog: OnceLock<Arc<SortCatalog<'static>>>,
    subsorts: OnceLock<Arc<SubsortView>>,
    syntactic_subsorts: OnceLock<Arc<SubsortView>>,
    overloads: OnceLock<Arc<Result<OverloadOrder<'static>, relations::Error>>>,
    priorities: OnceLock<Arc<Result<PartialOrder<String>, Cycle<String>>>>,
    associativities: OnceLock<Arc<AssociativityRelations>>,
    rule_grammar_subsorts: OnceLock<Arc<SubsortView>>,
}

impl ModuleViews {
    /// The views already built here, for a resolution in which the syntax sentences of the
    /// module's import closure are identical to this one's ([`ResolvedDefinition::update`]).
    ///
    /// Those sentences are the views' only inputs, so each built value is the value its
    /// constructor returns on that resolution. The overload order is carried only together with
    /// the production catalog it holds: it is built from this resolution's catalog, which is
    /// therefore built, and `update` carries the catalog under the same condition.
    pub(crate) fn carried(&self) -> Self {
        fn carry<T>(previous: &OnceLock<Arc<T>>) -> OnceLock<Arc<T>> {
            let lock = OnceLock::new();
            if let Some(value) = previous.get() {
                let _ = lock.set(Arc::clone(value));
            }
            lock
        }
        Self {
            sort_catalog: carry(&self.sort_catalog),
            subsorts: carry(&self.subsorts),
            syntactic_subsorts: carry(&self.syntactic_subsorts),
            overloads: carry(&self.overloads),
            priorities: carry(&self.priorities),
            associativities: carry(&self.associativities),
            rule_grammar_subsorts: carry(&self.rule_grammar_subsorts),
        }
    }

    /// The allocation of every view built so far, in field order.
    #[cfg(test)]
    pub(crate) fn built_allocations(&self) -> [Option<*const ()>; 7] {
        fn allocation<T>(lock: &OnceLock<Arc<T>>) -> Option<*const ()> {
            lock.get().map(|value| Arc::as_ptr(value).cast())
        }
        [
            allocation(&self.sort_catalog),
            allocation(&self.subsorts),
            allocation(&self.syntactic_subsorts),
            allocation(&self.overloads),
            allocation(&self.priorities),
            allocation(&self.associativities),
            allocation(&self.rule_grammar_subsorts),
        ]
    }
}

impl ResolvedDefinition {
    /// Create an empty memo for views derived from this resolution.
    pub fn views(&self) -> DefinitionViews<'_> {
        DefinitionViews::new(self)
    }

    /// Assert that every module view built in this resolution equals the one its constructor
    /// builds now: after an update, the built views are those carried.
    #[cfg(debug_assertions)]
    pub(crate) fn assert_module_views_fresh(&self) {
        k_rust_kore::measure::without_counting(|| {
            for (module, resolved) in self.modules() {
                let views = &self.module_views[module.0.index()];
                let name = &resolved.name;
                if let Some(carried) = views.sort_catalog.get() {
                    assert!(
                        carried.identical(&self.sort_catalog(module)),
                        "the carried sort catalog of {name} differs from a rebuilt one"
                    );
                }
                let subsorts = || relations::compute_subsorts(self.sentences(module), false);
                if let Some(carried) = views.subsorts.get() {
                    assert!(
                        **carried == subsorts(),
                        "the carried subsorts of {name} differ"
                    );
                }
                if let Some(carried) = views.syntactic_subsorts.get() {
                    assert!(
                        **carried == relations::compute_subsorts(self.sentences(module), true),
                        "the carried syntactic subsorts of {name} differ"
                    );
                }
                if let Some(carried) = views.overloads.get() {
                    let rebuilt = subsorts()
                        .map_err(relations::Error::CircularSubsort)
                        .and_then(|subsorts| {
                            relations::compute_overloads_with_shared_catalog(
                                self.production_catalog(module),
                                &subsorts,
                            )
                            .map_err(relations::Error::CircularOverload)
                        });
                    let same = match (carried.as_ref(), &rebuilt) {
                        (Ok(carried), Ok(rebuilt)) => carried.identical(rebuilt),
                        (Err(carried), Err(rebuilt)) => carried == rebuilt,
                        _ => false,
                    };
                    assert!(same, "the carried overloads of {name} differ");
                }
                if let Some(carried) = views.priorities.get() {
                    assert!(
                        **carried == relations::compute_priorities(self.sentences(module)),
                        "the carried priorities of {name} differ"
                    );
                }
                if let Some(carried) = views.associativities.get() {
                    assert!(
                        **carried == relations::compute_associativities(self.sentences(module)),
                        "the carried associativities of {name} differ"
                    );
                }
                if let Some(carried) = views.rule_grammar_subsorts.get() {
                    assert!(
                        **carried == super::checks::rule_grammar_subsorts(&self.sentences(module)),
                        "the carried rule grammar subsorts of {name} differ"
                    );
                }
            }
        });
    }
}

impl<'a> DefinitionViews<'a> {
    fn new(definition: &'a ResolvedDefinition) -> Self {
        let modules = definition.modules().count();
        Self {
            definition,
            production_catalogs: (0..modules).map(|_| OnceLock::new()).collect(),
            importers: OnceLock::new(),
        }
    }

    pub fn definition(&self) -> &'a ResolvedDefinition {
        self.definition
    }

    fn module_views(&self, module: ModuleId) -> &'a ModuleViews {
        &self.definition.module_views[module.0.index()]
    }

    pub fn production_catalog(&self, module: ModuleId) -> &ProductionCatalog<'a> {
        self.production_catalogs[module.0.index()]
            .get_or_init(|| self.definition.production_catalog(module))
    }

    // stack-accepted(import-chain): one level per module of an import chain; real chains are tens deep, 4,000 modules pass on 8 MiB, and compile time is already about n^1.6. See docs/backend-port.md#stack-bounds.
    pub fn sort_catalog(&self, module: ModuleId) -> &SortCatalog<'a> {
        self.module_views(module).sort_catalog.get_or_init(|| {
            let imported_sorts = self
                .definition
                .direct_imports(module)
                .into_iter()
                .flat_map(|import| self.sort_catalog(import.module).all_sorts().iter().cloned())
                .collect::<std::collections::BTreeSet<_>>();
            Arc::new(SortCatalog::new(
                self.definition.sentences(module),
                imported_sorts,
            ))
        })
    }

    pub fn subsorts(&self, module: ModuleId) -> Result<&PartialOrder<Sort>, &Cycle<Sort>> {
        self.module_views(module)
            .subsorts
            .get_or_init(|| {
                Arc::new(relations::compute_subsorts(
                    self.definition.sentences(module),
                    false,
                ))
            })
            .as_ref()
            .as_ref()
    }

    pub fn syntactic_subsorts(
        &self,
        module: ModuleId,
    ) -> Result<&PartialOrder<Sort>, &Cycle<Sort>> {
        self.module_views(module)
            .syntactic_subsorts
            .get_or_init(|| {
                Arc::new(relations::compute_subsorts(
                    self.definition.sentences(module),
                    true,
                ))
            })
            .as_ref()
            .as_ref()
    }

    pub fn overloads(&self, module: ModuleId) -> Result<&OverloadOrder<'a>, &relations::Error> {
        self.module_views(module)
            .overloads
            .get_or_init(|| {
                Arc::new(
                    self.subsorts(module)
                        .map_err(|cycle| relations::Error::CircularSubsort(cycle.clone()))
                        .and_then(|subsorts| {
                            // The resolution's own catalog, so that the order holds the
                            // catalog `update` carries with it.
                            relations::compute_overloads_with_shared_catalog(
                                self.definition.production_catalog(module),
                                subsorts,
                            )
                            .map_err(relations::Error::CircularOverload)
                        }),
                )
            })
            .as_ref()
            .as_ref()
    }

    pub fn priorities(&self, module: ModuleId) -> Result<&PartialOrder<String>, &Cycle<String>> {
        self.module_views(module)
            .priorities
            .get_or_init(|| {
                Arc::new(relations::compute_priorities(
                    self.definition.sentences(module),
                ))
            })
            .as_ref()
            .as_ref()
    }

    pub fn associativities(&self, module: ModuleId) -> &AssociativityRelations {
        self.module_views(module).associativities.get_or_init(|| {
            Arc::new(relations::compute_associativities(
                self.definition.sentences(module),
            ))
        })
    }

    /// The order in which the rule grammar of `module` admits terms
    /// ([`super::checks::rule_grammar_subsorts`]).
    pub(crate) fn rule_grammar_subsorts(
        &self,
        module: ModuleId,
    ) -> Result<&PartialOrder<Sort>, &Cycle<Sort>> {
        self.module_views(module)
            .rule_grammar_subsorts
            .get_or_init(|| {
                Arc::new(super::checks::rule_grammar_subsorts(
                    &self.definition.sentences(module),
                ))
            })
            .as_ref()
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
