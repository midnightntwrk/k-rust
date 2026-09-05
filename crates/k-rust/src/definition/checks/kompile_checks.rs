//! Definition-wide checks performed by Kompile and ProofDefinitionBuilder.

use std::collections::BTreeSet;

use super::rhs_variables::{CheckMode, StructuralCheckOptions};
use super::{ProductionItem, Sentence};
use crate::definition::{ModuleId, ResolvedDefinition};
use crate::diagnostic::{Diagnostic, DiagnosticCode};

pub fn check_claims_in_definition(
    definition: &ResolvedDefinition,
    options: &StructuralCheckOptions,
) -> Vec<Diagnostic> {
    let checked_modules = match &options.mode {
        CheckMode::Definition => definition
            .modules()
            .map(|(module, _)| module)
            .collect::<BTreeSet<_>>(),
        CheckMode::Proof { definition_module } => definition
            .module_id(definition_module)
            .map(|module| {
                if module == definition.main_module_id() {
                    BTreeSet::new()
                } else {
                    module_closure(definition, module)
                }
            })
            .unwrap_or_default(),
    };
    definition
        .modules()
        .filter(|(module, _)| checked_modules.contains(module))
        .flat_map(|(_, module)| &module.local_sentences)
        .filter(|sentence| matches!(sentence, Sentence::Claim { .. }))
        .map(|sentence| {
            Diagnostic::error(
                DiagnosticCode::ClaimInDefinition,
                "Claims are not allowed in the definition.",
                sentence,
            )
        })
        .collect()
}

pub fn check_proof_module(
    definition: &ResolvedDefinition,
    options: &StructuralCheckOptions,
) -> Vec<Diagnostic> {
    let CheckMode::Proof { definition_module } = &options.mode else {
        return Vec::new();
    };
    let Some(definition_module) = definition.module_id(definition_module) else {
        return Vec::new();
    };
    if definition_module == definition.main_module_id() {
        return Vec::new();
    }
    let definition_closure = module_closure(definition, definition_module);
    let specification_closure = module_closure(definition, definition.main_module_id());
    let definition_sort_catalog = definition.sort_catalog(definition_module);
    let definition_sorts = definition_sort_catalog.all_sorts();
    let mut diagnostics = Vec::new();
    for (module_id, module) in definition.modules() {
        if definition_closure.contains(&module_id) || !specification_closure.contains(&module_id) {
            continue;
        }
        for sentence in &module.local_sentences {
            if is_proof_syntax(sentence) && !is_existing_sort_token(sentence, definition_sorts) {
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::ProofModuleSyntax,
                    "Found syntax declaration in proof module. Only tokens for existing sorts are allowed.",
                    sentence,
                ));
            }
            if matches!(sentence, Sentence::Rule { .. })
                && sentence.attributes().get("simplification").is_none()
            {
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::ProofModuleRule,
                    "Only claims and simplification rules are allowed in proof modules.",
                    sentence,
                ));
            }
        }
    }
    diagnostics
}

/// `Kompile.checkIsSortPredicates` over the module set of the parsed definition.
///
/// The reference runs the check on the definition that
/// `DefinitionParsing.parseDefinitionAndResolveBubbles` trims (and, for `kprove`, on the module
/// set `Kompile.parseModules` hands to `ProofDefinitionBuilder.build`), not on every loaded
/// module: a prelude module such as `RANGEMAP` that nothing in the main closure imports, and
/// whose own import closure carries rules, never contributes a generated `is<Sort>` name.
pub fn check_is_sort_predicates(
    definition: &ResolvedDefinition,
    options: &StructuralCheckOptions,
) -> Vec<Diagnostic> {
    let checked_modules = parsed_definition_modules(definition, options);
    let generated = checked_modules
        .iter()
        .flat_map(|module| {
            definition
                .sort_catalog(*module)
                .defined_heads()
                .iter()
                .map(|sort| format!("is{}", sort.as_str()))
                .collect::<Vec<_>>()
        })
        .collect::<BTreeSet<_>>();
    let mut diagnostics = Vec::new();
    for module in checked_modules {
        for sentence in &definition.module(module).local_sentences {
            let Sentence::Production { sort, items, .. } = sentence else {
                continue;
            };
            let Some(ProductionItem::Terminal(predicate)) = items.first() else {
                continue;
            };
            if sort.name == "Bool"
                && items.len() >= 3
                && matches!(items.get(1), Some(ProductionItem::Terminal(open)) if open == "(")
                && matches!(items.last(), Some(ProductionItem::Terminal(close)) if close == ")")
                && generated.contains(predicate)
            {
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::IsSortPredicateConflict,
                    format!(
                        "Syntax declaration conflicts with automatically generated {predicate} predicate."
                    ),
                    sentence,
                ));
            }
        }
    }
    diagnostics
}

/// Modules `DefinitionParsing.parseDefinitionAndResolveBubbles` always retains, bubbles or not.
const FRONTEND_UTILITY_MODULES: [&str; 4] =
    ["K-REFLECTION", "STDIN-STREAM", "STDOUT-STREAM", "MAP"];

/// The module set of the parsed definition the reference checks: the import closures of the
/// main module (and of the definition module in proof mode, as `ProofDefinitionBuilder.build`
/// passes it), of the frontend utility modules, and of every loaded module whose visible
/// sentences held no bubble before inner parsing. Backend-tag exclusion has already removed
/// modules at load time.
///
/// The syntax module closure the reference also retains is not known to the checker; the CLI's
/// `parsed_definition_for_json` reproduces the same set with it for `parsed.json`.
fn parsed_definition_modules(
    definition: &ResolvedDefinition,
    options: &StructuralCheckOptions,
) -> BTreeSet<ModuleId> {
    let mut seeds = vec![definition.main_module_id()];
    if let CheckMode::Proof { definition_module } = &options.mode {
        seeds.extend(definition.module_id(definition_module));
    }
    seeds.extend(
        FRONTEND_UTILITY_MODULES
            .iter()
            .filter_map(|name| definition.module_id(name)),
    );
    // `Module.sentences` is local plus transitively imported sentences; dependency order lists
    // every import before its importer, so one pass propagates visible bubbles.
    let mut with_visible_bubbles = BTreeSet::new();
    for module in definition.dependency_order().iter().copied() {
        let local_bubble = definition
            .module(module)
            .local_sentences
            .iter()
            .any(is_bubble_sentence);
        let imported_bubble = definition
            .direct_imports(module)
            .iter()
            .any(|import| with_visible_bubbles.contains(&import.module));
        if local_bubble || imported_bubble {
            with_visible_bubbles.insert(module);
        } else {
            seeds.push(module);
        }
    }
    seeds
        .into_iter()
        .flat_map(|seed| module_closure(definition, seed))
        .collect()
}

/// Sentences the outer parser produces as bubbles, before or after inner parsing.
fn is_bubble_sentence(sentence: &Sentence) -> bool {
    matches!(
        sentence,
        Sentence::Rule { .. }
            | Sentence::Claim { .. }
            | Sentence::Context { .. }
            | Sentence::ContextAlias { .. }
            | Sentence::Configuration { .. }
            | Sentence::Bubble { .. }
    )
}

fn module_closure(definition: &ResolvedDefinition, module: ModuleId) -> BTreeSet<ModuleId> {
    let mut closure = definition
        .transitive_imports(module)
        .into_iter()
        .collect::<BTreeSet<_>>();
    closure.insert(module);
    closure
}

fn is_proof_syntax(sentence: &Sentence) -> bool {
    matches!(
        sentence,
        Sentence::SyntaxSort { .. }
            | Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::Production { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::SyntaxAssociativity { .. }
    )
}

fn is_existing_sort_token(
    sentence: &Sentence,
    definition_sorts: &BTreeSet<crate::kast::Sort>,
) -> bool {
    matches!(
        sentence,
        Sentence::Production { sort, attributes, .. }
            if attributes.get("token").is_some() && definition_sorts.contains(sort)
    )
}
