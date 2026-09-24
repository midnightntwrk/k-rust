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

pub use error::DescriptorLoweringError;
pub use open_sorts::{OpenSortAnalysis, analyze_open_sorts};

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    Descriptor, DescriptorBundle, DescriptorDeclaration, DescriptorPayload, ItemKind, ModuleId,
    PackageId, SemanticTheory,
};

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
pub fn lower_descriptor_bundle(
    bundle: &DescriptorBundle,
) -> Result<SemanticTheory, DescriptorLoweringError> {
    let mut descriptors = bundle.descriptors.iter().collect::<Vec<_>>();
    descriptors.sort_by(|left, right| left.id.cmp(&right.id));
    let head_rule_ids = descriptors
        .iter()
        .filter(|descriptor| matches!(descriptor.payload, DescriptorPayload::HeadRule(_)))
        .map(|descriptor| descriptor.id.clone())
        .collect::<BTreeSet<_>>();
    let mut declarations = BTreeMap::new();
    for descriptor in &descriptors {
        descriptor.validate_grammar_contract().map_err(|error| {
            DescriptorLoweringError::ParserReferenceDisagreement {
                id: Box::new(descriptor.id.clone()),
                detail: error.to_string(),
            }
        })?;
        descriptor.validate_state_contract().map_err(|error| {
            DescriptorLoweringError::ParserReferenceDisagreement {
                id: Box::new(descriptor.id.clone()),
                detail: error.to_string(),
            }
        })?;
        if declarations
            .insert(descriptor.id.clone(), *descriptor)
            .is_some()
        {
            return Err(DescriptorLoweringError::DuplicateItemId(Box::new(
                descriptor.id.clone(),
            )));
        }
        require_payload_kind(descriptor)?;
    }
    let configurations = descriptors
        .iter()
        .filter(|descriptor| matches!(descriptor.payload, DescriptorPayload::FixedConfiguration(_)))
        .count();
    if configurations != 1 {
        return Err(DescriptorLoweringError::ConfigurationCount(configurations));
    }

    validate_all_stable_references(&descriptors, &declarations)?;
    let semantic_sort_parents = build_semantic_sort_parents(&descriptors);
    let production_catalog = build_production_catalog(&descriptors)?;
    let mut declaration_metadata = bundle
        .declarations
        .iter()
        .cloned()
        .map(|declaration| (declaration.id().clone(), declaration))
        .collect::<BTreeMap<_, _>>();
    for descriptor in &descriptors {
        declaration_metadata
            .entry(descriptor.id.clone())
            .or_insert_with(|| {
                DescriptorDeclaration::new(
                    descriptor.id.clone(),
                    krs_ir::RustVisibility::Inherited,
                    None,
                )
            });
    }

    let mut packages = BTreeMap::<PackageId, Vec<&Descriptor>>::new();
    for descriptor in descriptors {
        packages
            .entry(descriptor.id.package().clone())
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
        modules.push(lower_package_module(
            &package,
            &package_descriptors,
            &module_ids,
            &declaration_catalog,
            &semantic_sort_parents,
            &production_catalog,
        )?);
    }
    modules.sort_by(|left, right| left.id().cmp(right.id()));
    if let Some((first, second)) = crate::overlap::first_head_rule_overlap(&modules, &head_rule_ids)
    {
        return Err(DescriptorLoweringError::OverlappingRules {
            first: Box::new(first),
            second: Box::new(second),
        });
    }
    Ok(SemanticTheory::new(modules)?)
}

fn require_payload_kind(descriptor: &Descriptor) -> Result<(), DescriptorLoweringError> {
    let expected = match &descriptor.payload {
        DescriptorPayload::Sort(_) => ItemKind::Sort,
        DescriptorPayload::Constructor(_) => ItemKind::Constructor,
        DescriptorPayload::FixedConfiguration(_) => ItemKind::Configuration,
        DescriptorPayload::Grammar(_) => ItemKind::Grammar,
        DescriptorPayload::StructuredRule(rule) => match rule.sentence_kind {
            krs_ir::SentenceKind::Transition => ItemKind::Rule,
            krs_ir::SentenceKind::Equation => ItemKind::Equation,
            krs_ir::SentenceKind::Simplification => ItemKind::Simplification,
            krs_ir::SentenceKind::Alias => ItemKind::Alias,
            krs_ir::SentenceKind::Claim => ItemKind::Claim,
        },
        DescriptorPayload::Cell(_) => ItemKind::Cell,
        DescriptorPayload::ConfigurationRule(rule) => match rule.sentence_kind {
            krs_ir::SentenceKind::Transition => ItemKind::Rule,
            krs_ir::SentenceKind::Equation => ItemKind::Equation,
            krs_ir::SentenceKind::Simplification => ItemKind::Simplification,
            krs_ir::SentenceKind::Alias => ItemKind::Alias,
            krs_ir::SentenceKind::Claim => ItemKind::Claim,
        },
        DescriptorPayload::HeadRule(rule) => match rule.sentence_kind {
            krs_ir::SentenceKind::Transition => ItemKind::Rule,
            krs_ir::SentenceKind::Equation => ItemKind::Equation,
            krs_ir::SentenceKind::Simplification => ItemKind::Simplification,
            krs_ir::SentenceKind::Alias => ItemKind::Alias,
            krs_ir::SentenceKind::Claim => ItemKind::Claim,
        },
        DescriptorPayload::ContextAlias(_) => ItemKind::ContextAlias,
    };
    let actual = descriptor.id.item_kind();
    if actual == expected {
        Ok(())
    } else {
        Err(DescriptorLoweringError::WrongItemKind {
            id: Box::new(descriptor.id.clone()),
            expected,
            actual,
        })
    }
}
