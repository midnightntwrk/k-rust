//! Author spec modules (KF-041).
//!
//! A `#[k::spec_module]` inline `mod` is a K proof module: `kprove --spec-module`
//! reads it beside the kompiled definition. Its sentences are the descriptors
//! whose Rust module path lies inside the `mod` (the innermost spec module
//! wins); K allows a proof module only claims, simplification lemmas, and
//! token productions for sorts the definition declares. KRS also keeps regex
//! tokens and `smt_lemma` lemmas out of spec modules: kore-exec did not
//! terminate with a regex token in a proof-side module in the design probe,
//! and it ignores `smt-lemma` outside the definition. The module imports the
//! definition explicitly through `imports = [..]`; the import graph is
//! acyclic and must reach the definition's main module.
//!
//! Only the main package's spec modules are part of a build: a dependency's
//! spec modules are that package's proof inputs, as a dependency's tests are
//! not part of a dependent's build.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    BuiltinSort, Descriptor, DescriptorModuleImport, DescriptorPayload,
    DescriptorProductionAttribute, DescriptorProductionItem, DescriptorProductionOwner,
    GrammarDescriptor, ItemKind, ModuleId, PackageId, ProductionAttribute, SourceRange,
    StableItemId,
};
use krs_ir_levels::{SemanticModule, SemanticSortRef};

use super::error::DescriptorLoweringError;

/// One `#[k::spec_module]` declaration of a package.
pub(super) struct SpecDeclaration<'a> {
    /// The spec module's own descriptor.
    pub(super) descriptor: &'a Descriptor,
    /// Its Rust module path below the crate root.
    pub(super) path: Vec<String>,
    /// Its K module name.
    pub(super) name: ModuleId,
    /// Its authored imports.
    pub(super) imports: &'a [DescriptorModuleImport],
}

/// A package's descriptors, split between its definition module and its spec modules.
pub(super) struct PackageSplit<'a> {
    /// Descriptors of the package's definition module.
    pub(super) definition: Vec<&'a Descriptor>,
    /// Each spec module with its descriptors, in Rust module path order.
    pub(super) specs: Vec<(SpecDeclaration<'a>, Vec<&'a Descriptor>)>,
}

/// Splits one package's descriptors and checks each spec module's content.
pub(super) fn split_package<'a>(
    package: &PackageId,
    descriptors: &[&'a Descriptor],
) -> Result<PackageSplit<'a>, DescriptorLoweringError> {
    let mut declarations = Vec::new();
    for descriptor in descriptors {
        let DescriptorPayload::Grammar(grammar) = descriptor.payload() else {
            continue;
        };
        let GrammarDescriptor::SpecModule { name, imports, .. } = grammar.as_ref() else {
            continue;
        };
        let name = if let Some(name) = name {
            name.value.clone()
        } else {
            let name = default_name(package, descriptor.id());
            // An authored name is checked by the attribute parser; the
            // derived one is checked here, including the `-SYNTAX` suffix.
            if let Err(error) =
                krs_syntax::validate_spec_module_name(&name, proc_macro2::Span::call_site())
            {
                return Err(fail(
                    descriptor,
                    format!("{error}; give the spec module `name = \"..\"`"),
                ));
            }
            name
        };
        let name = ModuleId::new(name.clone()).map_err(|_| {
            fail(
                descriptor,
                format!("`{name}` is not a K module name; give the spec module `name = \"..\"`"),
            )
        })?;
        declarations.push(SpecDeclaration {
            descriptor,
            path: descriptor.id().module_path().to_vec(),
            name,
            imports,
        });
    }
    declarations.sort_by(|left, right| left.path.cmp(&right.path));
    for (index, declaration) in declarations.iter().enumerate() {
        if let Some(outer) = declarations[..index]
            .iter()
            .find(|outer| declaration.path.starts_with(&outer.path))
        {
            return Err(fail(
                declaration.descriptor,
                format!(
                    "spec module `{}` is nested inside spec module `{}`; spec modules do not nest: declare it beside `{}` and list that module in its `imports`",
                    declaration.name.as_str(),
                    outer.name.as_str(),
                    outer.name.as_str()
                ),
            ));
        }
    }
    let mut definition = Vec::new();
    let mut specs = declarations
        .into_iter()
        .map(|declaration| (declaration, Vec::new()))
        .collect::<Vec<_>>();
    for descriptor in descriptors {
        if is_spec_declaration(descriptor) {
            continue;
        }
        let module_path = descriptor.id().module_path();
        let Some((spec, members)) = specs
            .iter_mut()
            .filter(|(spec, _)| module_path.starts_with(&spec.path))
            .max_by_key(|(spec, _)| spec.path.len())
        else {
            definition.push(*descriptor);
            continue;
        };
        check_member(spec, descriptor)?;
        members.push(*descriptor);
    }
    Ok(PackageSplit { definition, specs })
}

fn is_spec_declaration(descriptor: &Descriptor) -> bool {
    matches!(
        descriptor.payload(),
        DescriptorPayload::Grammar(grammar)
            if matches!(grammar.as_ref(), GrammarDescriptor::SpecModule { .. })
    )
}

/// `<k-namespace>-<UPPER-KEBAB(mod name)>`.
fn default_name(package: &PackageId, id: &StableItemId) -> String {
    let module = id.item_name().trim_start_matches("r#");
    format!(
        "{}-{}",
        package.k_namespace(),
        module.to_ascii_uppercase().replace('_', "-")
    )
}

/// The authored name of a declaration, without a generated grammar prefix.
fn display_name(id: &StableItemId) -> &str {
    let name = id.item_name();
    name.strip_prefix("__krs_grammar_token_").unwrap_or(name)
}

/// Checks that a descriptor may live in a K proof module.
fn check_member(
    spec: &SpecDeclaration<'_>,
    descriptor: &Descriptor,
) -> Result<(), DescriptorLoweringError> {
    let kind = match descriptor.id().item_kind() {
        ItemKind::Claim | ItemKind::Simplification => return Ok(()),
        ItemKind::Sort => "a sort",
        ItemKind::Constructor => "a constructor",
        ItemKind::Configuration => "a configuration",
        ItemKind::Cell => "a cell declaration",
        ItemKind::Rule => "a transition rule",
        ItemKind::Equation => "an equation",
        ItemKind::Alias => "an alias clause",
        ItemKind::Desugar => "a desugar clause",
        ItemKind::ContextAlias => "a context alias",
        ItemKind::Context => "a context",
        ItemKind::Grammar => match descriptor.payload() {
            DescriptorPayload::Grammar(grammar) => match grammar.as_ref() {
                GrammarDescriptor::Tokens { productions } => {
                    if productions.iter().any(|production| {
                        production.items.iter().any(|item| {
                            matches!(item, DescriptorProductionItem::RegexTerminal { .. })
                        })
                    }) {
                        return Err(fail(
                            descriptor,
                            format!(
                                "the regex token `{}` is in spec module `{}`; a spec module adds only terminal tokens (`#[k::token(terminal = \"..\")]`), because kore-exec did not terminate with a regex token in a proof module. Declare the regex token in the definition, as upstream IMP-VERIFICATION does",
                                display_name(descriptor.id()),
                                spec.name.as_str()
                            ),
                        ));
                    }
                    return Ok(());
                }
                GrammarDescriptor::Production(production) => match &production.owner {
                    DescriptorProductionOwner::Constructor { .. }
                        if production.attributes.iter().any(|attribute| {
                            matches!(attribute, DescriptorProductionAttribute::Function { .. })
                        }) =>
                    {
                        "a function"
                    }
                    DescriptorProductionOwner::Constructor { .. } => "a constructor",
                    DescriptorProductionOwner::TokenSort { .. } => "a token sort",
                    DescriptorProductionOwner::BracketSort { .. } => "a bracket",
                },
                GrammarDescriptor::Subsort { .. } => "a subsort",
                GrammarDescriptor::Precedence { .. } => "a precedence declaration",
                GrammarDescriptor::Associativity { .. } => "an associativity declaration",
                GrammarDescriptor::Lexical { .. } => "a `k::lexical!` block",
                GrammarDescriptor::Layout { .. } => "a `k::layout!` block",
                GrammarDescriptor::RawSentence { .. } => "a `k::raw_k!` sentence",
                GrammarDescriptor::SpecModule { .. } => "a spec module",
            },
            _ => "a grammar declaration",
        },
    };
    Err(fail(
        descriptor,
        format!(
            "`{}` is {kind} in spec module `{}`; K proof modules may contain only claims, simplification lemmas, and tokens for existing sorts. Move it into the definition",
            display_name(descriptor.id()),
            spec.name.as_str()
        ),
    ))
}

/// Resolves every spec module's imports and checks the import graph: no
/// cycle, every closure reaches `main`, and no name collides with another
/// module.
pub(super) fn resolve_imports(
    package: &PackageId,
    specs: &[SpecDeclaration<'_>],
    definition_modules: &BTreeMap<PackageId, ModuleId>,
    main: &ModuleId,
    reserved: &BTreeSet<String>,
) -> Result<Vec<Vec<ModuleId>>, DescriptorLoweringError> {
    definition_modules
        .get(package)
        .ok_or_else(|| DescriptorLoweringError::UnsupportedShape {
            node: "spec module",
            detail: format!("package {package} has no definition module for its spec modules"),
        })?;
    let mut names = BTreeSet::new();
    for spec in specs {
        if reserved.contains(spec.name.as_str()) || !names.insert(spec.name.as_str()) {
            return Err(fail(
                spec.descriptor,
                format!(
                    "spec module name `{}` is already a module of this definition; give the spec module another `name = \"..\"`",
                    spec.name.as_str()
                ),
            ));
        }
    }
    let spec_paths = specs
        .iter()
        .map(|spec| (spec.path.as_slice(), &spec.name))
        .collect::<Vec<_>>();
    let mut resolved = Vec::with_capacity(specs.len());
    for spec in specs {
        let parent = &spec.path[..spec.path.len().saturating_sub(1)];
        let mut imports = Vec::new();
        for import in spec.imports {
            let target = resolve_import(package, &import.path, parent, &spec_paths, definition_modules)
                .map_or_else(
                    || {
                        Err(fail_at(
                            spec.descriptor,
                            range_of(spec.descriptor, &import.key),
                            format!(
                                "spec-module import `{}` names neither `crate`, a dependency crate root, nor a spec module of this package",
                                import.path
                            ),
                        ))
                    },
                    Ok,
                )?;
            if !imports.contains(&target) {
                imports.push(target);
            }
        }
        resolved.push(imports);
    }
    let index = specs
        .iter()
        .enumerate()
        .map(|(position, spec)| (spec.name.clone(), position))
        .collect::<BTreeMap<_, _>>();
    // Cycles, by depth-first search over spec-module imports.
    let mut state = vec![0_u8; specs.len()];
    for start in 0..specs.len() {
        visit(start, specs, &resolved, &index, &mut state, &mut Vec::new())?;
    }
    for (position, spec) in specs.iter().enumerate() {
        let mut reached = BTreeSet::new();
        let mut stack = vec![position];
        let mut definition_imports = BTreeSet::new();
        while let Some(at) = stack.pop() {
            if !reached.insert(at) {
                continue;
            }
            for import in &resolved[at] {
                match index.get(import) {
                    Some(next) => stack.push(*next),
                    None => {
                        definition_imports.insert(import.clone());
                    }
                }
            }
        }
        // The main module tops the definition's import graph, so only a
        // direct import (of the spec module or one it imports) reaches it.
        if !definition_imports.contains(main) {
            return Err(fail(
                spec.descriptor,
                format!(
                    "spec module `{}` does not import the definition: its imports never reach `{}`. Add `imports = [crate]` (or a spec module that imports it)",
                    spec.name.as_str(),
                    main.as_str()
                ),
            ));
        }
    }
    Ok(resolved)
}

fn visit(
    at: usize,
    specs: &[SpecDeclaration<'_>],
    resolved: &[Vec<ModuleId>],
    index: &BTreeMap<ModuleId, usize>,
    state: &mut [u8],
    path: &mut Vec<usize>,
) -> Result<(), DescriptorLoweringError> {
    match state[at] {
        2 => return Ok(()),
        1 => {
            let start = path
                .iter()
                .position(|position| *position == at)
                .unwrap_or(0);
            let cycle = path[start..]
                .iter()
                .chain(std::iter::once(&at))
                .map(|position| specs[*position].name.as_str())
                .collect::<Vec<_>>()
                .join(" -> ");
            return Err(fail(
                specs[at].descriptor,
                format!(
                    "spec-module imports form a cycle: {cycle}; K module imports must be acyclic"
                ),
            ));
        }
        _ => {}
    }
    state[at] = 1;
    path.push(at);
    for import in &resolved[at] {
        if let Some(next) = index.get(import) {
            visit(*next, specs, resolved, index, state, path)?;
        }
    }
    path.pop();
    state[at] = 2;
    Ok(())
}

/// Resolves one authored import path relative to the spec module's parent.
fn resolve_import(
    package: &PackageId,
    path: &str,
    parent: &[String],
    specs: &[(&[String], &ModuleId)],
    definition_modules: &BTreeMap<PackageId, ModuleId>,
) -> Option<ModuleId> {
    if let Some(dependency) = path.strip_prefix("::") {
        return dependency_module(package, dependency, definition_modules);
    }
    let segments = path.split("::").collect::<Vec<_>>();
    let (base, rest) = match segments.first().copied()? {
        "crate" => (Vec::new(), &segments[1..]),
        "self" => (parent.to_vec(), &segments[1..]),
        "super" => {
            let mut base = parent.to_vec();
            let mut rest = &segments[..];
            while rest.first() == Some(&"super") {
                base.pop()?;
                rest = &rest[1..];
            }
            (base, rest)
        }
        _ => (parent.to_vec(), &segments[..]),
    };
    let mut target = base;
    target.extend(rest.iter().map(|segment| (*segment).to_owned()));
    if target.is_empty() {
        return definition_modules.get(package).cloned();
    }
    if let Some((_, name)) = specs.iter().find(|(path, _)| *path == target.as_slice()) {
        return Some((*name).clone());
    }
    if segments.len() == 1 && !matches!(segments[0], "crate" | "self" | "super") {
        return dependency_module(package, segments[0], definition_modules);
    }
    None
}

/// A dependency crate root: the package whose default library crate name is `name`.
fn dependency_module(
    package: &PackageId,
    name: &str,
    definition_modules: &BTreeMap<PackageId, ModuleId>,
) -> Option<ModuleId> {
    definition_modules
        .iter()
        .find(|(candidate, _)| {
            *candidate != package && candidate.cargo_name().replace('-', "_") == name
        })
        .map(|(_, module)| module.clone())
}

/// Rejects an `smt_lemma` simplification in a spec module: kore-exec ignores it there.
pub(super) fn check_spec_lemmas(modules: &[SemanticModule]) -> Result<(), DescriptorLoweringError> {
    for module in modules.iter().filter(|module| module.is_spec()) {
        for rule in module.rules() {
            if let Some(origin) = rule
                .restriction()
                .and_then(krs_ir_levels::IrMatchRestriction::smt_lemma)
            {
                return Err(DescriptorLoweringError::InvalidSpecModule {
                    item: Box::new(rule.id().clone()),
                    reason: format!(
                        "`smt_lemma` on `{}` in spec module `{}` would have no effect: kore-exec hands only the definition's lemmas to Z3. Move the lemma into the definition",
                        rule.id().item_name(),
                        module.id().as_str()
                    ),
                    range: origin.origin().exact_authored_range().map(Box::new),
                });
            }
        }
    }
    Ok(())
}

/// Requires every `Id` token of a spec-module sentence to be lexed by a token
/// production the spec module sees: K parses the module's claims with its
/// own grammar, which has no identifier regex outside program parsing.
pub(super) fn check_spec_identifiers(
    modules: &[SemanticModule],
) -> Result<(), DescriptorLoweringError> {
    let by_id = modules
        .iter()
        .map(|module| (module.id(), module))
        .collect::<BTreeMap<_, _>>();
    for module in modules.iter().filter(|module| module.is_spec()) {
        let visible = visible_modules(module, &by_id);
        // K's private syntax is visible only in its own module, so an
        // imported private token production lexes nothing here.
        let lexicon = crate::spec_tokens::IdLexicon::new(visible.iter().flat_map(|seen| {
            let own = seen.id() == module.id();
            seen.productions()
                .iter()
                .filter(move |production| {
                    (own || !crate::partition::is_private(production))
                        && production.result_sort() == &SemanticSortRef::Builtin(BuiltinSort::Id)
                        && production
                            .attributes()
                            .iter()
                            .any(|attribute| matches!(attribute, ProductionAttribute::Token { .. }))
                })
                .map(|production| {
                    production
                        .items()
                        .iter()
                        .map(krs_ir::GrammarProductionItem::kind)
                })
        }));
        for rule in module.rules() {
            let value = serde_json::to_value(rule).map_err(|error| {
                DescriptorLoweringError::UnsupportedShape {
                    node: "spec module",
                    detail: format!("cannot inspect a spec-module sentence: {error}"),
                }
            })?;
            let mut identifiers = BTreeSet::new();
            collect_identifiers(&value, &mut identifiers);
            if let Some(identifier) = identifiers
                .into_iter()
                .find(|identifier| !lexicon.may_lex(identifier))
            {
                return Err(DescriptorLoweringError::InvalidSpecModule {
                    item: Box::new(rule.id().clone()),
                    reason: format!(
                        "the identifier `{identifier}` in `{}` is lexed by no token production that spec module `{}` sees, and K parses its sentences with that grammar. Add a regex token for `Id` to the definition, as upstream IMP-VERIFICATION does: `#[k::token(regex = r\"\\$[a-zA-Z0-9_]+\")] pub type DollarId = k::builtin::Id;`",
                        rule.id().item_name(),
                        module.id().as_str()
                    ),
                    range: rule.origin().origin().exact_authored_range().map(Box::new),
                });
            }
        }
    }
    Ok(())
}

/// The spec module and every module it imports, transitively.
fn visible_modules<'a>(
    module: &'a SemanticModule,
    by_id: &BTreeMap<&ModuleId, &'a SemanticModule>,
) -> Vec<&'a SemanticModule> {
    let mut seen = BTreeSet::new();
    let mut stack = vec![module];
    let mut visible = Vec::new();
    while let Some(module) = stack.pop() {
        if !seen.insert(module.id()) {
            continue;
        }
        visible.push(module);
        stack.extend(
            module
                .imports()
                .iter()
                .filter_map(|import| by_id.get(import).copied()),
        );
    }
    visible
}

fn collect_identifiers(value: &serde_json::Value, identifiers: &mut BTreeSet<String>) {
    match value {
        serde_json::Value::Object(members) => {
            if members.get("term_kind").and_then(serde_json::Value::as_str) == Some("token")
                && members.get("sort").is_some_and(|sort| {
                    sort.get("sort").and_then(serde_json::Value::as_str) == Some("id")
                        && sort.get("sort_source").and_then(serde_json::Value::as_str)
                            == Some("builtin")
                })
                && let Some(text) = members.get("value").and_then(serde_json::Value::as_str)
            {
                identifiers.insert(text.to_owned());
            }
            for member in members.values() {
                collect_identifiers(member, identifiers);
            }
        }
        serde_json::Value::Array(items) => {
            for item in items {
                collect_identifiers(item, identifiers);
            }
        }
        _ => {}
    }
}

fn range_of(descriptor: &Descriptor, key: &krs_ir::ProvenanceKey) -> Option<SourceRange> {
    descriptor
        .provenance()
        .origin_for(key)
        .and_then(krs_ir::OriginStack::exact_authored_range)
}

fn fail(descriptor: &Descriptor, reason: String) -> DescriptorLoweringError {
    fail_at(
        descriptor,
        descriptor
            .provenance()
            .primary_origin()
            .exact_authored_range(),
        reason,
    )
}

fn fail_at(
    descriptor: &Descriptor,
    range: Option<SourceRange>,
    reason: String,
) -> DescriptorLoweringError {
    DescriptorLoweringError::InvalidSpecModule {
        item: Box::new(descriptor.id().clone()),
        reason,
        range: range.map(Box::new),
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use krs_ir::{ModuleId, PackageId};

    use super::resolve_import;

    fn package(namespace: &str, cargo: &str) -> PackageId {
        PackageId::new(namespace, cargo, "0.1.0", "workspace").unwrap()
    }

    #[test]
    fn imports_resolve_against_the_parent_module_the_crate_and_dependencies() {
        let own = package("IMP-VERIFICATION", "imp-verification");
        let dependency = package("KRS-IMP", "krs-imp-definition");
        let modules = BTreeMap::from([
            (own.clone(), ModuleId::new("IMP-VERIFICATION").unwrap()),
            (dependency, ModuleId::new("KRS-IMP").unwrap()),
        ]);
        let lemmas = ModuleId::new("LEMMAS").unwrap();
        let nested = ModuleId::new("NESTED").unwrap();
        let lemmas_path = ["lemmas".to_owned()];
        let nested_path = ["proofs".to_owned(), "nested".to_owned()];
        let specs = [
            (lemmas_path.as_slice(), &lemmas),
            (nested_path.as_slice(), &nested),
        ];
        let resolve = |path: &str, parent: &[&str]| {
            let parent = parent
                .iter()
                .map(|segment| (*segment).to_owned())
                .collect::<Vec<_>>();
            resolve_import(&own, path, &parent, &specs, &modules).map(|id| id.as_str().to_owned())
        };
        assert_eq!(resolve("crate", &[]).as_deref(), Some("IMP-VERIFICATION"));
        assert_eq!(resolve("lemmas", &[]).as_deref(), Some("LEMMAS"));
        assert_eq!(resolve("self::lemmas", &[]).as_deref(), Some("LEMMAS"));
        assert_eq!(
            resolve("crate::lemmas", &["proofs"]).as_deref(),
            Some("LEMMAS")
        );
        assert_eq!(
            resolve("super::lemmas", &["proofs"]).as_deref(),
            Some("LEMMAS")
        );
        assert_eq!(resolve("nested", &["proofs"]).as_deref(), Some("NESTED"));
        assert_eq!(
            resolve("krs_imp_definition", &[]).as_deref(),
            Some("KRS-IMP")
        );
        assert_eq!(
            resolve("::krs_imp_definition", &[]).as_deref(),
            Some("KRS-IMP")
        );
        assert_eq!(resolve("missing", &[]), None);
        assert_eq!(resolve("crate::missing", &[]), None);
        assert_eq!(resolve("super::lemmas", &[]), None);
    }
}
