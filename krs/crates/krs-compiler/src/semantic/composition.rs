//! What a composed definition holds: every package module of its root's dependency closure.
//!
//! A package's module imports the packages its descriptors refer to, which is what its own
//! sentences need. What the definition holds is another question: a composed definition is its
//! root package and the selected packages of the root's dependency closure (planning refuses a
//! facet outside it), so the root's module, which is the definition's main module, must reach
//! every one of them in the emitted K, whether or not some source happens to name one. Without
//! that, a selected package that no module reaches is a second top module: it is left out of the
//! definition, or, when it holds the configuration, it becomes the main module and the root's own
//! module is left out ([`crate::lowering::main_semantic_module`]).
//!
//! Reach is judged on the imports the K has. One semantic import is not one there: when a
//! module that the configured module reaches imports the configured module back (a dependency
//! whose rules name the definition's cells, FU-18), the K replaces that import by one of the
//! configuration's own module (`<NS>-CONFIGURATION`, [`crate::lowering`]), which holds neither the
//! configured module's rules nor its other sentences. That import reaches nothing of the
//! configured module, so it is left out here; whether an import is cut depends on what the
//! configured module reaches, the root's added imports included, so it is judged again after
//! each addition.
//!
//! The root's module imports the modules it does not reach that no other such module imports
//! (the tops of what is left), so a composition whose references already reach every package is
//! unchanged. A module of what is left that imports the root's is no exception: the root's module
//! is the main module, so the definition holds only what the root reaches. Only the configured
//! module can be imported against Cargo's dependency order, so such a module's import of the root
//! arises only when the root is the configured module, and it is then the cycle FU-18 cuts. What
//! is left has a top unless its imports
//! form a cycle no cut breaks; then the configured module, which every such cycle of a
//! composition passes through, is imported, or failing it the first module.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::ModuleId;
use krs_ir_levels::SemanticModule;

/// Makes the root package's module `root` reach every package module of `modules` (the
/// framework's module aside), adding to its imports the modules [`composition_imports`] gives.
pub(super) fn import_composition(modules: &mut [SemanticModule], root: &ModuleId) {
    // The framework's module is krs's own, no selected package: the definition holds it only
    // where a module uses it (`uses_framework`).
    let package_modules = modules
        .iter()
        .filter(|module| !crate::partition::is_framework_module(module.id()))
        .collect::<Vec<_>>();
    let imports = package_modules
        .iter()
        .map(|module| (module.id().clone(), module.imports().clone()))
        .collect::<BTreeMap<_, _>>();
    let configured = package_modules
        .iter()
        .find(|module| !module.is_spec() && module.configuration().is_some())
        .map(|module| module.id().clone());
    let added = composition_imports(&imports, configured.as_ref(), root);
    if let Some(module) = modules.iter_mut().find(|module| module.id() == root) {
        module.add_imports(added);
    }
}

/// The modules the root's module `root` must import so that, in the K, it reaches every module
/// of `imports` (each package module and the modules it imports), `configured` being the module
/// that holds the configuration.
pub(super) fn composition_imports(
    imports: &BTreeMap<ModuleId, BTreeSet<ModuleId>>,
    configured: Option<&ModuleId>,
    root: &ModuleId,
) -> BTreeSet<ModuleId> {
    let mut added = BTreeSet::<ModuleId>::new();
    loop {
        let mut graph = imports.clone();
        if let Some(own) = graph.get_mut(root) {
            own.extend(added.iter().cloned());
        }
        let edges = k_imports(&graph, configured);
        let reached = reach(&edges, [root.clone()]);
        let left = edges
            .keys()
            .filter(|id| !reached.contains(*id))
            .collect::<BTreeSet<_>>();
        if left.is_empty() {
            break;
        }
        let imported = left
            .iter()
            .flat_map(|id| &edges[*id])
            .collect::<BTreeSet<_>>();
        let mut tops = left
            .iter()
            .filter(|id| !imported.contains(**id))
            .map(|id| (*id).clone())
            .collect::<Vec<_>>();
        if tops.is_empty() {
            let cycle = configured
                .filter(|configured| left.contains(configured))
                .or_else(|| left.first().copied());
            tops.extend(cycle.cloned());
        }
        let before = added.len();
        added.extend(tops);
        // An import the K cuts reaches nothing more; another addition would not either.
        if added.len() == before {
            break;
        }
    }
    added
}

/// `graph` less each import FU-18 cuts: a module's import of `configured` where `configured`
/// reaches that module.
fn k_imports(
    graph: &BTreeMap<ModuleId, BTreeSet<ModuleId>>,
    configured: Option<&ModuleId>,
) -> BTreeMap<ModuleId, BTreeSet<ModuleId>> {
    let Some(configured) = configured else {
        return graph.clone();
    };
    let from_configured = reach(graph, graph.get(configured).into_iter().flatten().cloned());
    graph
        .iter()
        .map(|(id, imports)| {
            let mut imports = imports.clone();
            if from_configured.contains(id) {
                imports.remove(configured);
            }
            (id.clone(), imports)
        })
        .collect()
}

/// The modules `start` reaches by `graph`'s imports, `start` included.
fn reach(
    graph: &BTreeMap<ModuleId, BTreeSet<ModuleId>>,
    start: impl IntoIterator<Item = ModuleId>,
) -> BTreeSet<ModuleId> {
    let mut reached = BTreeSet::new();
    let mut pending = start.into_iter().collect::<Vec<_>>();
    while let Some(id) = pending.pop() {
        if reached.insert(id.clone())
            && let Some(next) = graph.get(&id)
        {
            pending.extend(next.iter().cloned());
        }
    }
    reached
}

#[cfg(test)]
mod tests {
    use super::*;

    fn id(name: &str) -> ModuleId {
        ModuleId::new(name).unwrap()
    }

    /// A module graph from `(module, [imports])` pairs.
    fn graph(edges: &[(&str, &[&str])]) -> BTreeMap<ModuleId, BTreeSet<ModuleId>> {
        edges
            .iter()
            .map(|(module, imports)| (id(module), imports.iter().map(|name| id(name)).collect()))
            .collect()
    }

    fn added(edges: &[(&str, &[&str])], configured: Option<&str>, root: &str) -> Vec<String> {
        composition_imports(&graph(edges), configured.map(id).as_ref(), &id(root))
            .iter()
            .map(|module| module.as_str().to_owned())
            .collect()
    }

    /// A composition whose references reach every package, the root alone (the framework's module
    /// is never given), and a root that is the configured module of an FU-18 cycle are unchanged.
    #[test]
    fn a_composition_its_references_reach_is_unchanged() {
        assert!(added(&[("ROOT", &[])], None, "ROOT").is_empty());
        assert!(
            added(
                &[("ROOT", &["LANG"]), ("LANG", &["CORE"]), ("CORE", &[])],
                Some("LANG"),
                "ROOT"
            )
            .is_empty()
        );
        // The dependency-rules shape: the configured root imports BASE, whose rules name its
        // cells, so BASE imports it back (cut in the K).
        assert!(
            added(
                &[("ZZZ-LANG", &["AAA-BASE"]), ("AAA-BASE", &["ZZZ-LANG"])],
                Some("ZZZ-LANG"),
                "ZZZ-LANG"
            )
            .is_empty()
        );
    }

    /// An observer that names only the FU-18 dependency reaches the configured module through no
    /// import the K has, so it imports the configured module, whatever the names' order.
    #[test]
    fn an_fu18_import_does_not_reach_the_configured_module() {
        for (base, lang) in [("AAA-BASE", "ZZZ-LANG"), ("ZZZ-BASE", "AAA-LANG")] {
            let shape: [(&str, &[&str]); 3] = [("OBS", &[base]), (base, &[lang]), (lang, &[base])];
            assert_eq!(added(&shape, Some(lang), "OBS"), [lang]);
            // An observer that names nothing: the cycle's top in the K is the configured module.
            let shape: [(&str, &[&str]); 3] = [("OBS", &[]), (base, &[lang]), (lang, &[base])];
            assert_eq!(added(&shape, Some(lang), "OBS"), [lang]);
        }
    }

    /// A helper that depends on the FU-18 dependency, which an observer names: the configured
    /// module is still unreached, and is the one import added.
    #[test]
    fn a_helper_of_the_fu18_dependency_adds_the_configured_module() {
        assert_eq!(
            added(
                &[
                    ("OBS", &["HELPER"]),
                    ("HELPER", &["AAA-BASE"]),
                    ("AAA-BASE", &["ZZZ-LANG"]),
                    ("ZZZ-LANG", &["AAA-BASE"]),
                ],
                Some("ZZZ-LANG"),
                "OBS"
            ),
            ["ZZZ-LANG"]
        );
    }

    /// A diamond: the root reaches one side; the other side, which only the configured module
    /// below both reaches nothing of, is imported, and so are both sides of a root that names
    /// neither, but not the configured module they share.
    #[test]
    fn a_diamond_imports_the_tops_left() {
        let diamond: [(&str, &[&str]); 4] = [
            ("ROOT", &["LEFT"]),
            ("LEFT", &["LANG"]),
            ("RIGHT", &["LANG"]),
            ("LANG", &[]),
        ];
        assert_eq!(added(&diamond, Some("LANG"), "ROOT"), ["RIGHT"]);
        let named_nothing: [(&str, &[&str]); 4] = [
            ("ROOT", &[]),
            ("LEFT", &["LANG"]),
            ("RIGHT", &["LANG"]),
            ("LANG", &[]),
        ];
        assert_eq!(
            added(&named_nothing, Some("LANG"), "ROOT"),
            ["LEFT", "RIGHT"]
        );
    }

    /// Two packages whose rules name the configured root's cells, which the root names nothing
    /// of: the definition holds both, each import of the root then being the cut FU-18 makes.
    #[test]
    fn packages_that_import_the_root_are_held() {
        assert_eq!(
            added(
                &[
                    ("LANG", &[]),
                    ("RULES-A", &["LANG"]),
                    ("RULES-B", &["LANG"]),
                ],
                Some("LANG"),
                "LANG"
            ),
            ["RULES-A", "RULES-B"]
        );
    }
}
