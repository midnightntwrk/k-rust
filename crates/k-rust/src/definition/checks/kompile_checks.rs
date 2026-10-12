//! This definition check traverses module sentences and terms linearly; callers supply derived catalogs and no dedicated counter is recorded.
//!
//! Definition-wide checks performed by Kompile and ProofDefinitionBuilder.

use std::collections::BTreeSet;

use super::rhs_variables::{CheckMode, StructuralCheckOptions};
use super::{ProductionItem, Sentence};
use crate::definition::AttributeKey;
use crate::definition::{DefinitionViews, ModuleId, ResolvedDefinition};
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::kast::{Label, WellKnownModule};
use crate::names::BuiltinSort;

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
        .flat_map(|(_, module)| module.local_sentences.iter().map(std::sync::Arc::as_ref))
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

/// Reject a `[locations]` sort of the main module's view when that view does not contain module
/// `K-LOCATIONS`, at each declaration of the attribute.
///
/// A sort `S` that declares `[locations]` asks that each term of `S` a program's text denotes be
/// `#location{S}(t, file, line, column, line, column)`, on every route that reads a program:
/// krust's in-process parser and the parsers it generates. `#location` is the symbol module
/// `K-LOCATIONS` declares, and the compiled definition is the main module's view, so without that
/// module no program holding a term of `S` denotes a term of the definition: `krun` could not
/// build its initial configuration, and a generated parser would print a pattern over a symbol
/// the definition lacks. The declaration can only be honoured with the import, so the definition
/// is refused where the declaration is written, instead of when the first program is read.
///
/// Compilation runs this check: its main module is the compiled definition, whereas the module
/// `kast --module` parses in is only where a program is read, not the definition it is read for.
pub fn check_locations_import(definition: &ResolvedDefinition) -> Vec<Diagnostic> {
    let main = definition.main_module_id();
    let locations = WellKnownModule::Locations.as_str();
    if definition
        .module_id(locations)
        .is_some_and(|module| module_closure(definition, main).contains(&module))
    {
        return Vec::new();
    }
    let main_name = &definition.main_module().name;
    definition
        .sentences(main)
        .into_iter()
        .filter_map(|sentence| {
            // The attribute is admitted on sort declarations only.
            let Sentence::SyntaxSort {
                sort, attributes, ..
            } = sentence
            else {
                return None;
            };
            attributes.value(AttributeKey::Locations)?;
            Some(Diagnostic::error(
                DiagnosticCode::MissingLocationsImport,
                format!(
                    "Sort {sort} declares 'locations', so each term of {sort} that a program denotes is wrapped in #location, which module {locations} declares, but the main module {main_name} does not import {locations}: no such program would denote a term of this definition. Add `imports {locations}` to {main_name}."
                ),
                sentence,
            ))
        })
        .collect()
}

pub fn check_proof_module(
    definition: &ResolvedDefinition,
    options: &StructuralCheckOptions,
) -> Vec<Diagnostic> {
    let views = definition.views();
    check_proof_module_with_views(&views, options)
}

pub(super) fn check_proof_module_with_views(
    views: &DefinitionViews<'_>,
    options: &StructuralCheckOptions,
) -> Vec<Diagnostic> {
    let definition = views.definition();
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
    let definition_sort_catalog = views.sort_catalog(definition_module);
    let definition_sorts = definition_sort_catalog.all_sorts();
    let mut diagnostics = Vec::new();
    for (module_id, module) in definition.modules() {
        if definition_closure.contains(&module_id) || !specification_closure.contains(&module_id) {
            continue;
        }
        for sentence in module.local_sentences.iter().map(std::sync::Arc::as_ref) {
            if is_proof_syntax(sentence) && !is_existing_sort_token(sentence, definition_sorts) {
                diagnostics.push(Diagnostic::error(
                    DiagnosticCode::ProofModuleSyntax,
                    "Found syntax declaration in proof module. Only tokens for existing sorts are allowed.",
                    sentence,
                ));
            }
            if matches!(sentence, Sentence::Rule { .. })
                && !sentence.attributes().has(AttributeKey::Simplification)
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

/// Reports every declared `syntax Bool ::= "isS" "(" ... ")"` production whose label is a sort
/// predicate compilation generates, which would give `isS` two definitions.
///
/// Compilation generates `isS` for every sort `S` whose role has a sort predicate
/// (`SortRole::has_sort_predicate`): `K`, `KItem`, `KConfigVar`, `Bool` and every defined sort,
/// a parametric one per instance (`isMInt{8}`, never `isMInt`). A declared `isS` for any other
/// sort (a numeral, a `#` sort, `KList`) is the definition's own function and conflicts with
/// nothing. The modules checked, and whose sorts contribute generated names, are those of the
/// parsed definition (`parsed_definition_modules`), not every loaded module: a prelude module
/// such as `RANGEMAP` that nothing in the main closure imports, and whose own import closure
/// carries rules, is outside that set and contributes no generated `isS`.
pub fn check_is_sort_predicates(
    definition: &ResolvedDefinition,
    options: &StructuralCheckOptions,
) -> Vec<Diagnostic> {
    let views = definition.views();
    check_is_sort_predicates_with_views(&views, options)
}

pub(super) fn check_is_sort_predicates_with_views(
    views: &DefinitionViews<'_>,
    options: &StructuralCheckOptions,
) -> Vec<Diagnostic> {
    let definition = views.definition();
    let checked_modules = parsed_definition_modules(definition, options);
    // The predicates compilation generates: `isS` for every sort `S` whose role has a sort
    // predicate. A declared `isS` for any other sort (a numeral, a `#` sort, `KList`) or for a
    // parametric head (compilation generates `isS` per instance) conflicts with nothing.
    let generated = checked_modules
        .iter()
        .flat_map(|module| {
            views
                .sort_catalog(*module)
                .all_sorts()
                .iter()
                .filter(|sort| sort.role().has_sort_predicate())
                .map(|sort| Label::sort_predicate(sort).name)
                .collect::<Vec<_>>()
        })
        .collect::<BTreeSet<_>>();
    let mut diagnostics = Vec::new();
    for module in checked_modules {
        for sentence in definition
            .module(module)
            .local_sentences
            .iter()
            .map(std::sync::Arc::as_ref)
        {
            let Sentence::Production { sort, items, .. } = sentence else {
                continue;
            };
            let Some(ProductionItem::Terminal(predicate)) = items.first() else {
                continue;
            };
            if sort.name == BuiltinSort::Bool.k_name()
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

/// Modules the parsed definition always retains, bubbles or not, because compilation reads them
/// whether or not the main module imports them: the stream pass (`kompile::passes::resolve_io`)
/// copies the `stream` rules of `STDIN-STREAM` and `STDOUT-STREAM` into a module that declares a
/// stream cell and adds imports of `K-IO` and `K-REFLECTION` to it (the stream modules import
/// both), and the loader, after selecting the modules, imports `MAP`, which declares the sort and
/// hooks of `type="Map"` cell collections, into every module with a configuration. Each import
/// must find its module, and a retained module's bubbles are parsed like the main module's, so
/// the rules a pass copies exist parsed.
const FRONTEND_UTILITY_MODULES: [&str; 4] = [
    WellKnownModule::KReflection.as_str(),
    WellKnownModule::StdinStream.as_str(),
    WellKnownModule::StdoutStream.as_str(),
    WellKnownModule::Map.as_str(),
];

/// The module set of the parsed definition, which compilation works on: the import closures of the
/// main module (and of the definition module in proof mode), of the frontend utility modules, and
/// of every loaded module whose visible sentences held no bubble before inner parsing. Bubbles are
/// parsed with the grammar of a module these closures reach; a module outside them that sees a
/// bubble would keep it unparsed, so it is left out; one that sees none needs no parse and is kept,
/// so the set holds every module that is complete without one. Backend-tag exclusion has already
/// removed modules at load time.
///
/// The parsed definition also retains the syntax module's closure, which the checker does not
/// know; the CLI's `parsed_definition_for_json` builds the same set with it for `parsed.json`.
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
    // A module's visible sentences are its local and transitively imported ones; dependency
    // order lists every import before its importer, so one pass propagates visible bubbles.
    let mut with_visible_bubbles = BTreeSet::new();
    // Invariant: `with_visible_bubbles` contains every module before `module` in `definition.dependency_order()` whose local or transitively imported sentences include a bubble, and `seeds` has gained every earlier module without one; each iteration consumes one module, and imports precede their importers in that order.
    for module in definition.dependency_order().iter().copied() {
        let local_bubble = definition
            .module(module)
            .local_sentences
            .iter()
            .any(|sentence| is_bubble_sentence(sentence.as_ref()));
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
            if attributes.has(AttributeKey::Token) && definition_sorts.contains(sort)
    )
}
