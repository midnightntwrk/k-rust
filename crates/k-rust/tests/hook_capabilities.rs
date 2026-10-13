use std::collections::{BTreeMap, BTreeSet};

use k_rust::{
    builtin::embedded,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    kore::parser::parse_definition,
    outer::{
        Attribute, LoadOptions, ProductionItem, ResolvedSource, Sentence, SyntaxBody,
        extract_fenced_k_code, load_with_options, parse,
    },
};
use k_rust_backend::{
    builtin::{BuiltinError, BuiltinResult, evaluate_hook},
    definition::BackendDefinition,
    term::{Sort, Term, TermKind},
};
use serde::Deserialize;

#[derive(Debug, Deserialize)]
struct CapabilityManifest {
    version: u32,
    backend_namespaces: Vec<String>,
    implemented: Vec<String>,
    execution_only: Vec<String>,
    structural: Vec<String>,
    unsupported: Vec<UnsupportedHooks>,
    equation_defined: Vec<EquationDefinedHooks>,
    crypto: CryptoCapabilities,
}

/// Hooks without a backend evaluator that the equations of `module`, a module of the prelude,
/// define where they apply.
#[derive(Debug, Deserialize)]
struct EquationDefinedHooks {
    module: String,
    reason: String,
    hooks: Vec<String>,
}

#[derive(Debug, Deserialize)]
struct CryptoCapabilities {
    sources: Vec<String>,
    implemented: Vec<String>,
    arities: BTreeMap<String, usize>,
    unsupported: Vec<UnsupportedHooks>,
}

#[test]
fn crypto_namespace_hooks_have_an_enforced_classification() {
    let manifest: CapabilityManifest =
        toml::from_str(include_str!("fixtures/hook-capabilities.toml"))
            .expect("hook capability manifest must be valid TOML");
    assert_eq!(manifest.version, 2, "unsupported manifest version");
    assert!(
        manifest
            .crypto
            .sources
            .iter()
            .all(|source| !source.trim().is_empty()),
        "crypto classifications need immutable source references"
    );

    let implemented = manifest
        .crypto
        .implemented
        .into_iter()
        .collect::<BTreeSet<_>>();
    let mut unsupported = BTreeSet::new();
    for group in manifest.crypto.unsupported {
        assert!(
            !group.reason.trim().is_empty(),
            "unsupported crypto hooks need a reason"
        );
        for hook in group.hooks {
            assert!(
                unsupported.insert(hook.clone()),
                "duplicate unsupported crypto hook {hook}"
            );
        }
    }
    assert_disjoint(&implemented, &unsupported, "implemented", "unsupported");

    let classified = implemented
        .union(&unsupported)
        .cloned()
        .collect::<BTreeSet<_>>();
    let catalogued = manifest
        .crypto
        .arities
        .keys()
        .cloned()
        .collect::<BTreeSet<_>>();
    assert_eq!(
        classified, catalogued,
        "crypto arities and capability classifications must cover the same pinned hooks"
    );

    let namespaces = manifest
        .backend_namespaces
        .into_iter()
        .collect::<BTreeSet<_>>();
    for hook in &classified {
        let namespace = hook
            .split_once('.')
            .map(|(namespace, _)| namespace)
            .expect("catalogued hook must have a namespace");
        assert!(
            namespaces.contains(namespace),
            "crypto hook namespace is not dispatched by the backend: {hook}"
        );
    }

    for hook in &implemented {
        let arity = manifest.crypto.arities[hook];
        let arguments = vec![dummy_term(); arity + 1];
        assert!(
            matches!(
                evaluate_hook(hook, &arguments),
                Ok(Err(BuiltinError::WrongArity { expected, actual, .. }))
                    if expected == arity && actual == arity + 1
            ),
            "implemented crypto hook does not reach a concrete evaluator: {hook}"
        );
    }
    for hook in &unsupported {
        let arity = manifest.crypto.arities[hook];
        let arguments = vec![dummy_term(); arity + 1];
        let result = evaluate_hook(hook, &arguments)
            .unwrap_or_else(|stop| panic!("unsupported crypto hook {hook} stopped: {stop:?}"))
            .unwrap_or_else(|error| panic!("unsupported crypto hook {hook} failed: {error:?}"));
        assert_ne!(
            result,
            BuiltinResult::NotApplicable,
            "unsupported crypto hook was silently treated as symbolic: {hook}"
        );
    }
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
    assert_eq!(manifest.version, 2, "unsupported manifest version");

    let declared = declared_prelude_hooks();
    let implemented = manifest.implemented.into_iter().collect::<BTreeSet<_>>();
    let execution_only = manifest.execution_only.into_iter().collect::<BTreeSet<_>>();
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

    let mut equation_defined = BTreeSet::new();
    for group in &manifest.equation_defined {
        assert!(
            !group.reason.trim().is_empty() && !group.module.trim().is_empty(),
            "equation-defined hooks need a reason and the module whose equations define them"
        );
        for hook in &group.hooks {
            assert!(
                equation_defined.insert(hook.clone()),
                "duplicate equation-defined hook {hook}"
            );
        }
    }

    assert_disjoint(&implemented, &structural, "implemented", "structural");
    assert_disjoint(
        &implemented,
        &execution_only,
        "implemented",
        "execution-only",
    );
    assert_disjoint(&implemented, &unsupported, "implemented", "unsupported");
    assert_disjoint(&execution_only, &structural, "execution-only", "structural");
    assert_disjoint(
        &execution_only,
        &unsupported,
        "execution-only",
        "unsupported",
    );
    assert_disjoint(&structural, &unsupported, "structural", "unsupported");
    for (name, class) in [
        ("implemented", &implemented),
        ("execution-only", &execution_only),
        ("structural", &structural),
        ("unsupported", &unsupported),
    ] {
        assert_disjoint(&equation_defined, class, "equation-defined", name);
    }

    let classified = implemented
        .union(&execution_only)
        .cloned()
        .collect::<BTreeSet<_>>()
        .union(&structural)
        .cloned()
        .collect::<BTreeSet<_>>()
        .union(&unsupported)
        .cloned()
        .collect::<BTreeSet<_>>()
        .union(&equation_defined)
        .cloned()
        .collect::<BTreeSet<_>>();
    let declared_names = declared.keys().cloned().collect::<BTreeSet<_>>();
    assert_eq!(
        classified, declared_names,
        "manifest must classify every and only pinned-prelude runtime hook"
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
                    Ok(Err(BuiltinError::WrongArity { expected, actual, .. }))
                        if expected == *arity && actual == arity + 1
                ),
                "implemented hook registry does not reach a concrete evaluator for {hook}"
            );
        }
    }

    for hook in &execution_only {
        let declaration = &declared[hook];
        assert_eq!(
            declaration.kind,
            DeclaredHookKind::Production,
            "execution-only hooks must be productions: {hook}"
        );
        for arity in &declaration.arities {
            let arguments = vec![dummy_term(); *arity];
            assert_eq!(
                evaluate_hook(hook, &arguments),
                Ok(Ok(BuiltinResult::Unsupported(
                    k_rust_backend::builtin::UnsupportedHookReason::NotImplemented
                ))),
                "context-free evaluation must not expose execution-only hook {hook}"
            );
        }
    }

    for hook in &unsupported {
        let declaration = &declared[hook];
        assert_eq!(
            declaration.kind,
            DeclaredHookKind::Production,
            "hooked sorts are structural, not unsupported evaluator hooks: {hook}"
        );
        assert!(
            !declaration.arities.is_empty(),
            "production hook has no arity: {hook}"
        );
        for arity in &declaration.arities {
            let arguments = vec![dummy_term(); arity + 1];
            let result = evaluate_hook(hook, &arguments)
                .unwrap_or_else(|stop| panic!("unsupported hook {hook} stopped: {stop:?}"))
                .unwrap_or_else(|error| panic!("unsupported hook {hook} failed: {error:?}"));
            assert_ne!(
                result,
                BuiltinResult::NotApplicable,
                "unsupported hook was silently treated as symbolic: {hook}"
            );
        }
    }

    // An equation-defined hook has no evaluator: an evaluator would make it `implemented`.
    for hook in &equation_defined {
        let declaration = &declared[hook];
        assert_eq!(
            declaration.kind,
            DeclaredHookKind::Production,
            "hooked sorts are structural, not equation-defined hooks: {hook}"
        );
        for arity in &declaration.arities {
            let arguments = vec![dummy_term(); *arity];
            assert_eq!(
                evaluate_hook(hook, &arguments),
                Ok(Ok(BuiltinResult::Unsupported(
                    k_rust_backend::builtin::UnsupportedHookReason::NotImplemented
                ))),
                "equation-defined hook {hook} has an evaluator; classify it as implemented"
            );
        }
    }
}

/// Every `equation_defined` hook has function equations where its named module is imported: a
/// definition that imports only that module, compiled for the Rust backend and loaded by it, has
/// an equation whose left-hand side is rooted at the hooked symbol. A ground application of each
/// evaluating through them is `krun_evaluates_equation_defined_hooks_through_their_equations` in
/// `cli.rs`.
#[test]
fn equation_defined_hooks_have_equations_in_their_named_module() {
    let manifest: CapabilityManifest =
        toml::from_str(include_str!("fixtures/hook-capabilities.toml"))
            .expect("hook capability manifest must be valid TOML");
    assert!(!manifest.equation_defined.is_empty());
    for group in &manifest.equation_defined {
        let source = format!("module MAIN\n  imports {}\nendmodule\n", group.module);
        let definition = compiled_backend_definition(&source);
        let mut equations = BTreeMap::<&str, usize>::new();
        for rule in definition
            .function_theory()
            .values()
            .flatten()
            .flat_map(|(_, rules)| rules)
        {
            let TermKind::Application { symbol, .. } = rule.lhs.kind() else {
                continue;
            };
            if rule.attributes.simplification {
                continue;
            }
            if let Some(hook) = symbol.attributes.hook.as_deref() {
                *equations.entry(hook).or_default() += 1;
            }
        }
        for hook in &group.hooks {
            assert!(
                equations.get(hook.as_str()).is_some_and(|count| *count > 0),
                "{hook} has no function equation in a definition that imports {}",
                group.module
            );
        }
    }
}

fn compiled_backend_definition(source: &str) -> BackendDefinition {
    let prelude = embedded("prelude.md").expect("embedded prelude should exist");
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("main.k", source.to_owned()),
        "MAIN",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![prelude],
            ..CompilationBackend::Rust.load_options()
        },
    )
    .unwrap_or_else(|error| panic!("{source}: load: {error}"));
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default())
        .unwrap_or_else(|error| panic!("{source}: compile: {error}"));
    let kore = parse_definition(&artifacts.definition_kore).unwrap();
    BackendDefinition::internalize(&kore, "MAIN")
        .unwrap_or_else(|error| panic!("{source}: backend load: {error}"))
}

#[test]
fn substitution_hooks_have_an_enforced_external_capability_classification() {
    let declared = declared_hooks(["substitution.md"]);
    let subst_one = &declared["SUBSTITUTION.substOne"];
    assert_eq!(subst_one.kind, DeclaredHookKind::Production);
    assert_eq!(subst_one.arities, BTreeSet::from([3]));
    assert!(matches!(
        evaluate_hook("SUBSTITUTION.substOne", &vec![dummy_term(); 4]),
        Ok(Err(BuiltinError::WrongArity {
            expected: 3,
            actual: 4,
            ..
        }))
    ));

    let subst_many = &declared["SUBSTITUTION.substMany"];
    assert_eq!(subst_many.kind, DeclaredHookKind::Production);
    assert_eq!(subst_many.arities, BTreeSet::from([2]));
    assert_eq!(
        evaluate_hook("SUBSTITUTION.substMany", &vec![dummy_term(); 2]),
        Ok(Ok(BuiltinResult::Unsupported(
            k_rust_backend::builtin::UnsupportedHookReason::NotImplemented
        )))
    );
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
    declared_hooks(["prelude.md"])
}

fn declared_hooks<'a>(roots: impl IntoIterator<Item = &'a str>) -> BTreeMap<String, DeclaredHook> {
    let mut pending = roots.into_iter().map(str::to_owned).collect::<Vec<_>>();
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
