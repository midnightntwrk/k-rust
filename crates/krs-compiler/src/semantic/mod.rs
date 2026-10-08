//! Descriptor-bundle lowering into target-neutral semantic IR.

mod catalog;
mod configuration;
mod configuration_rules;
mod error;
mod grammar;
mod infer;
mod open_sorts;
mod origin;
mod package;
mod references;
mod rules;

pub use error::{DescriptorLoweringError, NondetGroupProblem};

use crate::overlap::OverlapViolation;
pub use open_sorts::{OpenSortAnalysis, analyze_open_sorts};

use std::collections::BTreeMap;

use krs_ir::{
    BuiltinSort, Descriptor, DescriptorBundle, DescriptorDeclaration, DescriptorIndex,
    DescriptorPayload, ModuleId, PackageId, ProvenanceRole, StableItemId,
};
use krs_ir_levels::SemanticTheory;

use catalog::{DeclarationCatalog, build_production_catalog, build_semantic_sort_parents};
use package::lower_package_module;
use references::validate_all_stable_references;

/// Resolves one descriptor bundle into checked target-neutral IR.
///
/// This boundary performs no Cargo work and has no adapter knowledge. Named
/// paths are joined exclusively through their parser-owned
/// [`ProvenanceKey`](krs_ir::ProvenanceKey);
/// there is no short-name lookup or guessed constructor resolution.
///
/// # Errors
///
/// Returns [`DescriptorLoweringError`] for duplicate or dangling identities,
/// wrong descriptor shapes, parser/reference disagreement, malformed terms,
/// invalid generated identities, or a failed whole-theory invariant.
#[expect(
    clippy::too_many_lines,
    reason = "Lowering keeps the whole-bundle checks in their fixed order."
)]
pub fn lower_descriptor_bundle(
    bundle: &DescriptorBundle,
) -> Result<SemanticTheory, DescriptorLoweringError> {
    let mut descriptors = bundle.descriptors().iter().collect::<Vec<_>>();
    descriptors.sort_by(|left, right| left.id().cmp(right.id()));
    let configurations = descriptors
        .iter()
        .filter(|descriptor| {
            matches!(
                descriptor.payload(),
                DescriptorPayload::FixedConfiguration(_)
            )
        })
        .count();
    if configurations != 1 {
        return Err(DescriptorLoweringError::ConfigurationCount(configurations));
    }

    let declarations = DescriptorIndex::from_descriptors(descriptors.iter().copied());
    validate_all_stable_references(&descriptors, &declarations)?;
    let semantic_sort_parents = build_semantic_sort_parents(&descriptors);
    let production_catalog = build_production_catalog(&descriptors)?;
    let mut declaration_metadata = bundle
        .declarations()
        .iter()
        .cloned()
        .map(|declaration| (declaration.id().clone(), declaration))
        .collect::<BTreeMap<_, _>>();
    for descriptor in &descriptors {
        declaration_metadata
            .entry(descriptor.id().clone())
            .or_insert_with(|| {
                DescriptorDeclaration::new(
                    descriptor.id().clone(),
                    krs_ir::RustVisibility::Inherited,
                    None,
                )
            });
    }

    validate_builtin_sort_names(&descriptors, &declaration_metadata)?;

    let mut packages = BTreeMap::<PackageId, Vec<&Descriptor>>::new();
    for descriptor in descriptors {
        packages
            .entry(descriptor.id().package().clone())
            .or_default()
            .push(descriptor);
    }
    let module_ids = packages
        .keys()
        .map(|package| Ok((package.clone(), ModuleId::new(package.k_namespace())?)))
        .collect::<Result<BTreeMap<_, _>, DescriptorLoweringError>>()?;
    let declaration_catalog = DeclarationCatalog {
        descriptors: &declarations,
        metadata: &declaration_metadata,
    };
    let mut modules = Vec::with_capacity(packages.len());
    for (package, package_descriptors) in packages {
        modules.push(
            lower_package_module(
                &package,
                &package_descriptors,
                &module_ids,
                &declaration_catalog,
                &semantic_sort_parents,
                &production_catalog,
            )?
            .with_int_literals(bundle.int_literals(&package)),
        );
    }
    modules.sort_by(|left, right| left.id().cmp(right.id()));
    if let Some(violation) = crate::overlap::first_overlap_violation(&modules) {
        let range = |rule: &StableItemId| {
            declarations
                .get(rule)
                .and_then(exact_rule_head_range)
                .map(Box::new)
        };
        return Err(match violation {
            OverlapViolation::Overlap { first, second } => {
                DescriptorLoweringError::OverlappingRules {
                    second_head_range: range(&second),
                    first: Box::new(first),
                    second: Box::new(second),
                }
            }
            OverlapViolation::SingleMemberGroup { group, rule } => {
                DescriptorLoweringError::NondetGroup {
                    range: range(&rule),
                    rule: Box::new(rule),
                    problem: NondetGroupProblem::SingleMember { group },
                }
            }
            OverlapViolation::MixedPriorityGroup {
                group,
                rule,
                priorities,
            } => DescriptorLoweringError::NondetGroup {
                range: range(&rule),
                rule: Box::new(rule),
                problem: NondetGroupProblem::MixedPriorities { group, priorities },
            },
            OverlapViolation::StaleGroupMember { group, rule } => {
                DescriptorLoweringError::NondetGroup {
                    range: range(&rule),
                    rule: Box::new(rule),
                    problem: NondetGroupProblem::StaleMember { group },
                }
            }
        });
    }
    Ok(SemanticTheory::new(modules)?)
}

/// The authored range of a rule's subject head, or of its name when the
/// subject has no application head (a `cells!` rule).
fn exact_rule_head_range(descriptor: &Descriptor) -> Option<krs_ir::SourceRange> {
    let origins = descriptor.provenance().origins();
    [
        ProvenanceRole::RuleLeftApplicationHead,
        ProvenanceRole::RuleDeclaration,
    ]
    .into_iter()
    .find_map(|role| {
        origins
            .iter()
            .find(|node| node.key.role() == role && node.key.ordinal() == 0)?
            .origin
            .exact_authored_range()
    })
}

fn validate_builtin_sort_names(
    descriptors: &[&Descriptor],
    metadata: &BTreeMap<StableItemId, DescriptorDeclaration>,
) -> Result<(), DescriptorLoweringError> {
    for descriptor in descriptors {
        if !matches!(descriptor.payload(), DescriptorPayload::Sort(_)) {
            continue;
        }
        let declaration = &metadata[descriptor.id()];
        let name = declaration.explicit_symbol.as_ref().map_or_else(
            || descriptor.id().item_name(),
            krs_ir::ExplicitSymbol::final_component,
        );
        if let Some(builtin) = BuiltinSort::ALL
            .into_iter()
            .find(|builtin| builtin.k_name() == name)
        {
            return Err(DescriptorLoweringError::BuiltinSortNameCollision {
                id: Box::new(descriptor.id().clone()),
                builtin,
            });
        }
    }
    Ok(())
}
