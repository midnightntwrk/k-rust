use std::collections::{BTreeMap, BTreeSet};

use k_rust::{
    builtin::embedded,
    outer::{Attribute, ProductionItem, Sentence, SyntaxBody, extract_fenced_k_code, parse},
};
use k_rust_backend::{
    builtin::{BuiltinError, BuiltinResult, EVALUATOR_HOOKS, evaluate_hook},
    term::{Sort, Term},
};
use serde::Deserialize;

#[derive(Debug, Deserialize)]
struct CapabilityManifest {
    version: u32,
    implemented: Vec<String>,
    structural: Vec<String>,
    unsupported: Vec<UnsupportedHooks>,
}

#[derive(Debug, Deserialize)]
struct UnsupportedHooks {
    reason: String,
    hooks: Vec<String>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DeclaredHookKind {
    Production,
    Sort,
}

#[derive(Debug)]
struct DeclaredHook {
    kind: DeclaredHookKind,
    arities: BTreeSet<usize>,
}

#[test]
fn pinned_prelude_hooks_have_an_enforced_capability_classification() {
    let manifest: CapabilityManifest =
        toml::from_str(include_str!("fixtures/hook-capabilities.toml"))
            .expect("hook capability manifest must be valid TOML");
    assert_eq!(manifest.version, 1, "unsupported manifest version");

    let declared = declared_prelude_hooks();
    let implemented = manifest.implemented.into_iter().collect::<BTreeSet<_>>();
    let structural = manifest.structural.into_iter().collect::<BTreeSet<_>>();
    let mut unsupported = BTreeSet::new();
    for group in manifest.unsupported {
        assert!(
            !group.reason.trim().is_empty(),
            "unsupported hooks need a reason"
        );
        for hook in group.hooks {
            assert!(
                unsupported.insert(hook.clone()),
                "duplicate unsupported hook {hook}"
            );
        }
    }

    assert_disjoint(&implemented, &structural, "implemented", "structural");
    assert_disjoint(&implemented, &unsupported, "implemented", "unsupported");
    assert_disjoint(&structural, &unsupported, "structural", "unsupported");

    let classified = implemented
        .union(&structural)
        .cloned()
        .collect::<BTreeSet<_>>()
        .union(&unsupported)
        .cloned()
        .collect::<BTreeSet<_>>();
    let declared_names = declared.keys().cloned().collect::<BTreeSet<_>>();
    assert_eq!(
        classified, declared_names,
        "manifest must classify every and only pinned-prelude runtime hook"
    );

    let registered_prelude_hooks = EVALUATOR_HOOKS
        .iter()
        .filter(|hook| declared.contains_key(**hook))
        .map(|hook| (*hook).to_owned())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        implemented, registered_prelude_hooks,
        "implemented classifications and the evaluator gate must agree"
    );

    for hook in &structural {
        assert_eq!(
            declared[hook].kind,
            DeclaredHookKind::Sort,
            "structural classification is reserved for hooked sorts: {hook}"
        );
    }
    for hook in &implemented {
        let declaration = &declared[hook];
        assert_eq!(
            declaration.kind,
            DeclaredHookKind::Production,
            "hooked sorts are structural, not evaluator hooks: {hook}"
        );
        for arity in &declaration.arities {
            let arguments = vec![dummy_term(); arity + 1];
            assert!(
                matches!(
                    evaluate_hook(hook, &arguments),
                    Err(BuiltinError::WrongArity { expected, actual, .. })
                        if expected == *arity && actual == arity + 1
                ),
                "implemented hook registry does not reach a concrete evaluator for {hook}"
            );
        }
    }

    for hook in &unsupported {
        let arity = declared[hook].arities.iter().next().copied().unwrap_or(0);
        let arguments = vec![dummy_term(); arity];
        assert_eq!(
            evaluate_hook(hook, &arguments),
            Ok(BuiltinResult::NotApplicable),
            "unsupported hook unexpectedly became evaluable; reclassify it: {hook}"
        );
    }
}

fn dummy_term() -> Term {
    Term::domain_value(Sort::simple("SortCapabilityAuditDummy"), "dummy")
}

fn assert_disjoint(
    left: &BTreeSet<String>,
    right: &BTreeSet<String>,
    left_name: &str,
    right_name: &str,
) {
    let duplicates = left.intersection(right).collect::<Vec<_>>();
    assert!(
        duplicates.is_empty(),
        "hooks classified as both {left_name} and {right_name}: {duplicates:?}"
    );
}

fn declared_prelude_hooks() -> BTreeMap<String, DeclaredHook> {
    let mut pending = vec!["prelude.md".to_owned()];
    let mut visited = BTreeSet::new();
    let mut hooks = BTreeMap::<String, DeclaredHook>::new();
    while let Some(name) = pending.pop() {
        if !visited.insert(name.clone()) {
            continue;
        }
        let source =
            embedded(&name).unwrap_or_else(|| panic!("missing embedded prelude source {name}"));
        let code = extract_fenced_k_code(&source.text, "k").unwrap();
        let file = parse(source.source, &code).unwrap();
        pending.extend(file.requires.into_iter().map(|required| required.path));
        for sentence in file.modules.into_iter().flat_map(|module| module.sentences) {
            let Sentence::Syntax(syntax) = sentence else {
                continue;
            };
            match syntax.body {
                SyntaxBody::Sort(attributes) => {
                    if let Some(hook) = hook_attribute(&attributes) {
                        insert_hook(&mut hooks, hook, DeclaredHookKind::Sort, None);
                    }
                }
                SyntaxBody::Productions(blocks) => {
                    for production in blocks.into_iter().flat_map(|block| block.productions) {
                        if let Some(hook) = hook_attribute(&production.attributes) {
                            let arity = production
                                .items
                                .iter()
                                .filter(|item| {
                                    matches!(
                                        item,
                                        ProductionItem::NonTerminal { .. }
                                            | ProductionItem::UserList { .. }
                                    )
                                })
                                .count();
                            insert_hook(
                                &mut hooks,
                                hook,
                                DeclaredHookKind::Production,
                                Some(arity),
                            );
                        }
                    }
                }
                SyntaxBody::Synonym { .. } => {}
            }
        }
    }
    hooks
}

fn hook_attribute(attributes: &[Attribute]) -> Option<String> {
    attributes
        .iter()
        .find(|attribute| attribute.key == "hook")
        .and_then(|attribute| attribute.value.clone())
}

fn insert_hook(
    hooks: &mut BTreeMap<String, DeclaredHook>,
    name: String,
    kind: DeclaredHookKind,
    arity: Option<usize>,
) {
    let hook = hooks.entry(name.clone()).or_insert_with(|| DeclaredHook {
        kind,
        arities: BTreeSet::new(),
    });
    assert_eq!(
        hook.kind, kind,
        "hook used as both a sort and production: {name}"
    );
    if let Some(arity) = arity {
        hook.arities.insert(arity);
    }
}
