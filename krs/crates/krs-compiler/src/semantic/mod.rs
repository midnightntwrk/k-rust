//! Descriptor-bundle lowering into target-neutral semantic IR.

mod catalog;
mod cell_alternatives;
mod cell_states;
mod collection_types;
mod configuration;
mod configuration_rules;
mod cons_lists;
mod constants;
mod equation_alternatives;
mod error;
mod evaluation;
mod family_precedence;
mod fresh;
mod function_patterns;
mod grammar;
mod infer;
mod lexicals;
mod list_patterns;
mod lists;
pub(crate) use lists::value_list_overloads;
mod ml;
mod open_sorts;
mod operators;
mod or_positions;
mod origin;
mod overload;
mod package;
mod raw_k;
mod record_updates;
pub(crate) use record_updates::{head_rule_long_form, structured_rule_long_form};
mod references;
mod restriction;
mod rules;
mod smt;
mod spec_modules;
mod statics;
mod token_collisions;
mod tokens;
mod visibility;

pub use error::{
    DescriptorLoweringError, FreshProblem, ImplicitPresentCell, LexicalProblem, NondetGroupProblem,
    OperatorProblem,
};

use crate::overlap::OverlapViolation;
pub use open_sorts::{OpenSortAnalysis, analyze_open_sorts};
pub use raw_k::{RawKPolicy, raw_k_policy};

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    BuiltinSort, Descriptor, DescriptorBundle, DescriptorDeclaration, DescriptorIndex,
    DescriptorPayload, ModuleId, PackageId, ProvenanceRole, StableItemId,
};
use krs_ir_levels::{SemanticModule, SemanticTheory};

use catalog::{DeclarationCatalog, build_production_catalog, build_semantic_sort_parents};
use package::{lower_package_module, lower_spec_module};
use references::validate_all_stable_references;

/// The bundle's descriptors in identity order, each constant inlined at its uses: a constant is
/// a name for a term, so every use becomes the term before anything else reads the bundle, and
/// no later check sees a constant. The alternatives at an equation's subject root are moved
/// below the function it defines, which they apply alike, so no later check sees them there.
fn ordered_descriptors(
    bundle: &DescriptorBundle,
) -> Result<constants::Inlined<'_>, DescriptorLoweringError> {
    let mut descriptors = bundle.descriptors().iter().collect::<Vec<_>>();
    descriptors.sort_by(|left, right| left.id().cmp(right.id()));
    let mut inlined = constants::inline_constants(&descriptors)?;
    inlined.descriptors = equation_alternatives::distribute_root_alternatives(inlined.descriptors)?;
    Ok(inlined)
}

/// The inference catalog's subsort judge over the bundle's descriptors, as lowering builds it.
///
/// # Errors
///
/// Returns the lowering error of a constant that does not inline.
#[cfg(feature = "test-support")]
pub(crate) fn catalog_subsort_judge(
    bundle: &DescriptorBundle,
) -> Result<
    impl Fn(&krs_ir_levels::SemanticSortRef, &krs_ir_levels::SemanticSortRef) -> bool + use<>,
    DescriptorLoweringError,
> {
    let inlined = ordered_descriptors(bundle)?;
    let descriptors = inlined
        .descriptors
        .iter()
        .map(AsRef::as_ref)
        .collect::<Vec<&Descriptor>>();
    let parents = build_semantic_sort_parents(&descriptors);
    Ok(
        move |candidate: &krs_ir_levels::SemanticSortRef,
              expected: &krs_ir_levels::SemanticSortRef| {
            catalog::semantic_is_subsort(candidate, expected, &parents)
        },
    )
}

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
    let inlined = ordered_descriptors(bundle)?;
    let descriptors = inlined
        .descriptors
        .iter()
        .map(AsRef::as_ref)
        .collect::<Vec<&Descriptor>>();
    let configurations = descriptors
        .iter()
        .filter(|descriptor| {
            matches!(
                descriptor.payload(),
                DescriptorPayload::FixedConfiguration(_)
            )
        })
        .collect::<Vec<_>>();
    if configurations.len() != 1 {
        // A second configuration is the one to remove or merge; none has nothing to point at.
        let range = |index: usize| {
            configurations
                .get(index)
                .and_then(|descriptor| self::origin::item_range(descriptor))
                .map(Box::new)
        };
        return Err(DescriptorLoweringError::ConfigurationCount {
            names: configurations
                .iter()
                .map(|descriptor| descriptor.id().item_name().to_owned())
                .collect(),
            range: range(1),
            first: range(0),
            item: configurations
                .get(1)
                .map(|descriptor| Box::new(descriptor.id().clone())),
        });
    }

    let declarations = DescriptorIndex::from_descriptors(descriptors.iter().copied());
    validate_all_stable_references(&descriptors, &declarations)?;
    let semantic_sort_parents = build_semantic_sort_parents(&descriptors);
    let production_catalog = build_production_catalog(&descriptors)?;
    cons_lists::check_cons_lists(&descriptors, &production_catalog)?;
    collection_types::check_production_types(&descriptors, &production_catalog)?;
    constants::check_constants(
        &inlined.constants,
        &declarations,
        &production_catalog,
        &semantic_sort_parents,
    )?;
    function_patterns::check_function_patterns(&descriptors, &production_catalog)?;
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
    let mut package_specs = Vec::new();
    for (package, package_descriptors) in packages {
        let split = spec_modules::split_package(&package, &package_descriptors)?;
        modules.push(
            lower_package_module(
                &package,
                &split.definition,
                &package_descriptors,
                &module_ids,
                &declaration_catalog,
                &semantic_sort_parents,
                &production_catalog,
            )?
            .with_int_literals(bundle.int_literals(&package)),
        );
        if !split.specs.is_empty() {
            package_specs.push((package, split.specs));
        }
    }
    // Only the main package's spec modules belong to this build (KF-041).
    if let Some(main) =
        crate::lowering::main_semantic_module(&modules).map(|module| module.id().clone())
        && let Some((package, specs)) = package_specs
            .into_iter()
            .find(|(package, _)| module_ids.get(package) == Some(&main))
    {
        let mut reserved = BTreeSet::new();
        for module in &modules {
            reserved.insert(module.id().as_str().to_owned());
            reserved.insert(format!("{}-SYNTAX", module.id().as_str()));
        }
        reserved.insert(format!("{}-SPEC", main.as_str()));
        let (declarations, members): (Vec<_>, Vec<_>) = specs.into_iter().unzip();
        let imports =
            spec_modules::resolve_imports(&package, &declarations, &module_ids, &main, &reserved)?;
        for ((spec, descriptors), imports) in declarations.iter().zip(&members).zip(imports) {
            modules.push(lower_spec_module(
                spec,
                imports,
                descriptors,
                &declaration_catalog,
                &semantic_sort_parents,
                &production_catalog,
            )?);
        }
    }
    if !uses_framework(&modules) {
        modules.retain(|module| !crate::partition::is_framework_module(module.id()));
    }
    modules.sort_by(|left, right| left.id().cmp(right.id()));
    overload::check_overloads(&modules, &semantic_sort_parents)?;
    family_precedence::check_chainless_families(&modules, &semantic_sort_parents)?;
    tokens::check_token_sorts(&modules)?;
    tokens::check_program_token_fields(&modules)?;
    token_collisions::check_token_collisions(&modules)?;
    lexicals::check_lexicals(&modules)?;
    lists::check_syntax_lists(&modules, &semantic_sort_parents)?;
    fresh::check_fresh_generators(&modules)?;
    evaluation::check_evaluation_steps(&modules)?;
    smt::check_smtlib_symbols(&modules)?;
    restriction::check_equation_restrictions(&modules)?;
    or_positions::check_or_pattern_positions(&modules)?;
    list_patterns::check_list_patterns(&modules)?;
    restriction::check_smt_lemmas(&modules)?;
    statics::check_static_clauses(&modules)?;
    visibility::check_proof_visibility(&modules)?;
    spec_modules::check_spec_lemmas(&modules)?;
    spec_modules::check_spec_identifiers(&modules)?;
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
            OverlapViolation::AmbiguousAlternatives {
                rule,
                first,
                second,
                range,
            } => DescriptorLoweringError::AmbiguousOrPattern {
                rule: Box::new(rule),
                first,
                second,
                range: range.map(Box::new),
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
    if let Some(overlap) = crate::equation_domain::first_equation_overlap(&modules) {
        if let Some(arms) = declarations
            .get(&overlap.first)
            .zip(declarations.get(&overlap.second))
            .and_then(|(first, second)| branch_ranges(first, second))
        {
            return Err(DescriptorLoweringError::OverlappingMatchArms {
                function: overlap.function,
                first: Box::new(overlap.first),
                second: Box::new(overlap.second),
                application: overlap.application,
                results: Box::new(overlap.results),
                arms: Box::new(arms),
            });
        }
        let range = declarations
            .get(&overlap.second)
            .and_then(exact_rule_head_range)
            .map(Box::new);
        return Err(DescriptorLoweringError::OverlappingEquations {
            function: overlap.function,
            first: Box::new(overlap.first),
            second: Box::new(overlap.second),
            application: overlap.application,
            results: Box::new(overlap.results),
            second_head_range: range,
        });
    }
    // A validator failure is located at the innermost term the validator was checking, and
    // names the item whose sentence it was checking.
    SemanticTheory::new_located(modules).map_err(|failure| {
        let krs_ir_levels::SemanticFailure { error, item, at } = *failure;
        DescriptorLoweringError::InvalidSemanticTheory {
            error,
            range: at
                .and_then(|origin| origin.origin().exact_authored_range())
                .map(Box::new),
            item: item.map(Box::new),
        }
    })
}

/// The exact authored range of a descriptor's first anchor of `role`.
/// Whether the definition uses the framework sorts, so that its K keeps the
/// framework module: some module imports it, which a module does exactly when
/// one of its declarations names `KItem` or `KResult` (as with any package),
/// or some sentence still refers to one of them, such as a rule variable
/// inferred at `KItem`. Every definition has the framework sorts; only what
/// it uses is emitted.
fn uses_framework(modules: &[SemanticModule]) -> bool {
    modules
        .iter()
        .filter(|module| !crate::partition::is_framework_module(module.id()))
        .any(|module| {
            module
                .imports()
                .iter()
                .any(crate::partition::is_framework_module)
                || serde_json::to_value(module).is_ok_and(|module| names_framework_item(&module))
        })
}

/// Whether a serialized IR value names an item of the framework package
/// outside provenance: an item identity serializes with its `package`, whose
/// `k_namespace` is the framework's.
fn names_framework_item(value: &serde_json::Value) -> bool {
    match value {
        serde_json::Value::Object(fields) => fields.iter().any(|(key, field)| {
            key != "origin"
                && ((key == "package"
                    && field.get("k_namespace").and_then(serde_json::Value::as_str)
                        == Some(crate::partition::FRAMEWORK_NAMESPACE))
                    || names_framework_item(field))
        }),
        serde_json::Value::Array(items) => items.iter().any(names_framework_item),
        serde_json::Value::Null
        | serde_json::Value::Bool(_)
        | serde_json::Value::Number(_)
        | serde_json::Value::String(_) => false,
    }
}

fn exact_role_range(descriptor: &Descriptor, role: ProvenanceRole) -> Option<krs_ir::SourceRange> {
    descriptor
        .provenance()
        .origins()
        .iter()
        .find(|node| node.key.role() == role && node.key.ordinal() == 0)?
        .origin
        .exact_authored_range()
}

/// The authored branches of two equations that one function shorthand's
/// branching body defines: both name the function at one authored head, the
/// fn's name, which is not where their sort is written (an equation table's
/// rows name their function at the header, which is also their sort), and
/// each is named at its own branch rather than at the head.
fn branch_ranges(
    first: &Descriptor,
    second: &Descriptor,
) -> Option<(krs_ir::SourceRange, krs_ir::SourceRange)> {
    let head = exact_role_range(first, ProvenanceRole::RuleLeftApplicationHead)?;
    if exact_role_range(second, ProvenanceRole::RuleLeftApplicationHead)? != head
        || exact_role_range(first, ProvenanceRole::RuleType)? == head
    {
        return None;
    }
    let first_branch = exact_role_range(first, ProvenanceRole::RuleDeclaration)?;
    let second_branch = exact_role_range(second, ProvenanceRole::RuleDeclaration)?;
    (first_branch != head && second_branch != head).then_some((first_branch, second_branch))
}

/// The source-map key semantic lowering gives the application whose head has
/// provenance `key` in `descriptor`, whatever operation it applies.
pub(crate) fn application_source_key(
    descriptor: &Descriptor,
    key: &krs_ir::ProvenanceKey,
) -> Option<krs_ir::SourceMapKey> {
    origin::semantic_origin(descriptor, key.clone(), "term-application")
        .ok()
        .map(|origin| origin.key().clone())
}

/// The source-map key of the builtin List operation lowered at the
/// application with provenance `key`, as [`application_source_key`] gives a
/// constructor's: `[]` at a builtin `List` position lowers to `.List`.
pub(crate) fn list_operation_source_key(
    descriptor: &Descriptor,
    key: &krs_ir::ProvenanceKey,
) -> Option<krs_ir::SourceMapKey> {
    origin::semantic_origin(descriptor, key.clone(), "term-list-operation")
        .ok()
        .map(|origin| origin.key().clone())
}

/// The source-map key of the `list::item` that the bracket level with
/// provenance `key` lowered to at a builtin `List` position, as
/// [`application_source_key`] gives a constructor's.
pub(crate) fn list_notation_source_key(
    descriptor: &Descriptor,
    key: &krs_ir::ProvenanceKey,
) -> Option<krs_ir::SourceMapKey> {
    origin::semantic_origin(descriptor, key.clone(), "list-notation-item")
        .ok()
        .map(|origin| origin.key().clone())
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
                range: self::origin::item_range(descriptor).map(Box::new),
            });
        }
    }
    Ok(())
}
