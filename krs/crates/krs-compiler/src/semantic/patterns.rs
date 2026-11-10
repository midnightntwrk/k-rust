//! The package of a `k::patterns!` block (FB-49 items 7 and 8).
//!
//! A pattern is a question kink asks of the runs of a definition; it is never a sentence of the
//! definition. So the block lives in a package of its own that depends on the specification's
//! package and declares nothing else: `use` items and the block. Then no edit to a pattern can
//! change the definition, its Definition IR or anything kink keys by them, and a pattern can
//! call only the specification's functions. For the same reason the package stands outside the
//! definition's closure: a package the semantics imports feeds the root Definition IR.

use std::collections::BTreeMap;

use krs_ir::{Descriptor, DescriptorPayload, PackageId};
use krs_ir_levels::SemanticModule;

use super::error::DescriptorLoweringError;
use super::origin::item_range;

/// Whether `descriptor` is a part of a `k::patterns!` chain: a readable claim, elaborated or
/// not, that carries the part it is.
pub(super) fn is_pattern_part(descriptor: &Descriptor) -> bool {
    part_of(descriptor).is_some()
}

/// The part of a chain `descriptor` is, if any.
fn part_of(descriptor: &Descriptor) -> Option<&krs_ir::PatternDecl> {
    match descriptor.payload() {
        DescriptorPayload::HeadRule(rule) => rule.claim.as_ref()?.pattern.as_ref(),
        DescriptorPayload::ConfigurationRule(rule) => rule.claim.as_ref()?.pattern.as_ref(),
        _ => None,
    }
}

/// The packages that hold a pattern, each with its first part, after checking that each
/// declares nothing else: a function there is a helper no pattern may call (item 7), and any
/// other declaration is one a patterns package does not hold (item 8).
pub(super) fn pattern_packages<'d>(
    packages: &BTreeMap<PackageId, Vec<&'d Descriptor>>,
    constants: &[Descriptor],
) -> Result<BTreeMap<PackageId, &'d Descriptor>, DescriptorLoweringError> {
    let mut found = BTreeMap::new();
    for (package, descriptors) in packages {
        let Some(first) = descriptors
            .iter()
            .copied()
            .find(|descriptor| is_pattern_part(descriptor))
        else {
            continue;
        };
        // A function is a helper no pattern may call (item 7), told at its declaration before
        // the equations its body defines; any other declaration is one a patterns package does
        // not hold (item 8).
        if let Some(function) = descriptors
            .iter()
            .copied()
            .find(|descriptor| is_function(descriptor))
        {
            // A function's production is the grammar item the expansion names after it.
            let name = function.id().item_name();
            let name = name.strip_prefix("__krs_grammar_").unwrap_or(name);
            return Err(DescriptorLoweringError::PatternHelper {
                item: Box::new(function.id().clone()),
                reason: format!(
                    "`{name}` is a function of the package that holds `k::patterns!`: a pattern may call only the specification's functions, since a function a pattern needs would have to be added to the specification for it; patterns go in a package of their own, which depends on the specification's: move the block there, or `{name}` to the specification's package"
                ),
                range: item_range(function).map(Box::new),
            });
        }
        // A constant is substituted at its uses before anything is lowered, so it is not among
        // the package's sentences, but it is declared there.
        if let Some(other) = descriptors
            .iter()
            .copied()
            .find(|descriptor| !is_pattern_part(descriptor))
            .or_else(|| {
                constants
                    .iter()
                    .find(|constant| constant.id().package() == package)
            })
        {
            let name = other.id().item_name();
            return Err(DescriptorLoweringError::PatternsPackage {
                item: Box::new(other.id().clone()),
                reason: format!(
                    "`{name}` is declared in the package that holds `k::patterns!`, which declares nothing but `use` items and the block: a pattern asks about the specification's runs and is no part of it, so patterns go in a package of their own, which depends on the specification's: move the block there, or `{name}` to the specification's package"
                ),
                range: item_range(other).map(Box::new),
            });
        }
        // A pattern's id names it to kink, so two clauses of the package have two ids: two
        // modules may each hold a clause of one name, which rustc does not compare.
        let mut ids: BTreeMap<&str, &[String]> = BTreeMap::new();
        for descriptor in descriptors {
            let Some(part) = part_of(descriptor) else {
                continue;
            };
            let module = descriptor.id().module_path();
            match ids.get(part.id.as_str()) {
                Some(seen) if *seen != module => {
                    return Err(DescriptorLoweringError::DuplicatePatternId {
                        item: Box::new(descriptor.id().clone()),
                        reason: format!(
                            "the pattern `{}` is declared in `{}` and in `{}` of one package: kink names a pattern by its id, the clause name with `_` written `-`, so the ids of one package are unique; rename one",
                            part.id,
                            seen.join("::"),
                            module.join("::"),
                        ),
                        range: item_range(descriptor).map(Box::new),
                    });
                }
                Some(_) => {}
                None => {
                    ids.insert(part.id.as_str(), module);
                }
            }
        }
        found.insert(package.clone(), first);
    }
    Ok(found)
}

/// Whether `descriptor` declares a function production.
fn is_function(descriptor: &Descriptor) -> bool {
    let DescriptorPayload::Grammar(grammar) = descriptor.payload() else {
        return false;
    };
    let krs_ir::GrammarDescriptor::Production(production) = grammar.as_ref() else {
        return false;
    };
    production.attributes.iter().any(|attribute| {
        matches!(
            attribute,
            krs_ir::DescriptorProductionAttribute::Function { .. }
        )
    })
}

/// Refuses a patterns package inside the definition's closure: one that is not the definition's
/// root (`root`, or else the top of the modules) or that another module imports.
pub(super) fn check_outside_closure(
    patterns: &BTreeMap<PackageId, &Descriptor>,
    root: Option<&PackageId>,
    module_ids: &BTreeMap<PackageId, krs_ir::ModuleId>,
    modules: &[SemanticModule],
) -> Result<(), DescriptorLoweringError> {
    for (package, part) in patterns {
        let imported = module_ids.get(package).is_some_and(|id| {
            modules
                .iter()
                .any(|module| module.id() != id && module.imports().contains(id))
        });
        let below_root = root.is_some_and(|root| root != package);
        if imported || below_root {
            return Err(DescriptorLoweringError::PatternsPackage {
                item: Box::new(part.id().clone()),
                reason: "this `k::patterns!` block is in a package the definition's semantics depends on, whose declarations make up the definition, so an edit to a pattern would change it: a patterns block goes in its own package, which depends on the semantics and which no package of the semantics depends on; declare it in FLOW.toml `[[patterns]] krs = \"..\"`".to_owned(),
                range: item_range(part).map(Box::new),
            });
        }
    }
    Ok(())
}
