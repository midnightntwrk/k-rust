//! Program-syntax partition of each package (decisions X12 and R1).
//!
//! Every package emits two K modules: `<NS>-SYNTAX`, the grammar programs may
//! use, and `<NS>`, which imports it and adds everything else rules may use.
//! A `pub` production that is not `internal` is program syntax, unless its
//! result or argument sorts include a builtin sort that K supplies only with a
//! full module (Map, List and Set have no `-SYNTAX` module in K 7.1.337). Such a
//! production is placed in `<NS>` automatically: silently, unless the author
//! asserted `program`, which turns the placement into a warning.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{self, Write as _};

use krs_diagnostic::{Diagnostic, Location, Severity, codes};
use krs_ir::{
    BuiltinSort, GrammarProductionItemKind, ModuleId, NodeOrigin, ProductionAttribute,
    ProductionGroupId, RustVisibility, StableItemId,
};
use krs_ir_levels::{
    SemanticModule, SemanticProduction, SemanticSortRef, SemanticSubsort, SemanticTheory,
};

/// K namespace of the facade's framework package, which is not partitioned.
pub(crate) const FRAMEWORK_NAMESPACE: &str = "KRS-FRAMEWORK";

/// Suffix of a package's program-syntax module.
pub const PROGRAM_SYNTAX_SUFFIX: &str = "-SYNTAX";

/// Returns the program-syntax module name of a package module.
#[must_use]
pub fn program_syntax_module_name(module: &str) -> String {
    format!("{module}{PROGRAM_SYNTAX_SUFFIX}")
}

pub(crate) fn is_framework_module(module: &ModuleId) -> bool {
    module.as_str() == FRAMEWORK_NAMESPACE
}

fn is_framework_sort(sort: &SemanticSortRef) -> bool {
    matches!(sort, SemanticSortRef::Declared(id) if id.package().k_namespace() == FRAMEWORK_NAMESPACE)
}

/// Why a production or subsort is not in the program-syntax module.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PlacementReason {
    /// The author marked the production `internal`.
    Internal,
    /// The production is not `pub`, so it is private to the package's rules.
    NotPublic,
    /// A subsort into a framework sort (`KResult ::= Value`).
    FrameworkSubsort,
    /// The production's result or an argument has a builtin sort without a
    /// `-SYNTAX` module (R1).
    NeedsFullModule {
        /// The argument field, or `None` for the result sort.
        field: Option<String>,
        /// The builtin sort.
        sort: BuiltinSort,
    },
}

impl PlacementReason {
    /// Whether this placement is the automatic R1 placement of a `pub` production.
    #[must_use]
    pub const fn is_automatic(&self) -> bool {
        matches!(self, Self::NeedsFullModule { .. })
    }
}

impl fmt::Display for PlacementReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Internal => formatter.write_str("marked `internal`"),
            Self::NotPublic => formatter.write_str("not `pub`"),
            Self::FrameworkSubsort => formatter.write_str("framework subsort"),
            Self::NeedsFullModule { field, sort } => {
                let module = sort.spec().k_module.unwrap_or_else(|| sort.k_name());
                match field {
                    Some(field) => write!(formatter, "argument `{field}: {}`", sort.k_name())?,
                    None => write!(formatter, "result `{}`", sort.k_name())?,
                }
                write!(
                    formatter,
                    ": K has no {module}{PROGRAM_SYNTAX_SUFFIX} module"
                )
            }
        }
    }
}

/// Where one package's sentences go: each set lists what is placed in the
/// semantics module `<NS>`; everything else is in `<NS>-SYNTAX`.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ModulePlacement {
    /// Productions placed in `<NS>`, with the reason.
    productions: BTreeMap<StableItemId, PlacementReason>,
    /// Indices of subsorts (in module order) placed in `<NS>`, with the reason.
    subsorts: BTreeMap<usize, PlacementReason>,
    /// Indices of precedence sentences placed in `<NS>`.
    precedences: BTreeSet<usize>,
    /// Indices of associativity sentences placed in `<NS>`.
    associativities: BTreeSet<usize>,
}

impl ModulePlacement {
    /// Whether a production is program syntax.
    #[must_use]
    pub fn production_is_syntax(&self, id: &StableItemId) -> bool {
        !self.productions.contains_key(id)
    }

    /// Returns why a production is not program syntax.
    #[must_use]
    pub fn production_reason(&self, id: &StableItemId) -> Option<&PlacementReason> {
        self.productions.get(id)
    }

    /// Whether the subsort at `index` (module order) is program syntax.
    #[must_use]
    pub fn subsort_is_syntax(&self, index: usize) -> bool {
        !self.subsorts.contains_key(&index)
    }

    /// Whether the precedence sentence at `index` (module order) is program syntax.
    #[must_use]
    pub fn precedence_is_syntax(&self, index: usize) -> bool {
        !self.precedences.contains(&index)
    }

    /// Whether the associativity sentence at `index` (module order) is program syntax.
    #[must_use]
    pub fn associativity_is_syntax(&self, index: usize) -> bool {
        !self.associativities.contains(&index)
    }
}

/// The program-syntax partition of every package of a theory.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Partition {
    modules: BTreeMap<ModuleId, ModulePlacement>,
    report: Vec<PackageReport>,
    warnings: Vec<PartitionWarning>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct PackageReport {
    module: ModuleId,
    syntax: Vec<String>,
    placed: Vec<(String, String)>,
}

/// A `program` production that cannot be program syntax.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PartitionWarning {
    origin: NodeOrigin,
    message: String,
}

impl PartitionWarning {
    /// Returns the `warning[krs::partition::not-program-syntax]` diagnostic.
    #[must_use]
    pub fn to_diagnostic(&self) -> Diagnostic {
        let mut diagnostic = Diagnostic::error(
            codes::partition::NOT_PROGRAM_SYNTAX,
            self.message.clone(),
            self.origin
                .origin()
                .exact_authored_range()
                .map_or(Location::None, Location::Source),
        );
        diagnostic.severity = Severity::Warning;
        diagnostic
    }

    /// Returns the warning text.
    #[must_use]
    pub fn message(&self) -> &str {
        &self.message
    }
}

/// A partition that K would reject or that would silently change programs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PartitionError {
    /// A precedence or associativity group mixes `internal` productions with
    /// program-syntax productions.
    MixedGroup {
        /// The group.
        group: ProductionGroupId,
        /// An `internal` member.
        internal: String,
        /// A program-syntax member.
        program: String,
        /// The `internal` member's attribute origin.
        origin: NodeOrigin,
    },
    /// An `int-literals = "unsigned"` package's program syntax imports a signed
    /// package's program syntax, so signed literals would leak into programs.
    SignedIntegerLeak {
        /// The unsigned package's program-syntax module.
        module: String,
        /// The signed program-syntax module it imports.
        signed: String,
    },
}

impl fmt::Display for PartitionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MixedGroup {
                group,
                internal,
                program,
                ..
            } => write!(
                formatter,
                "group `{group}` mixes `internal` production `{internal}` with program-syntax production `{program}`; K priorities and associativity apply per module, so mark both `internal` or neither"
            ),
            Self::SignedIntegerLeak { module, signed } => write!(
                formatter,
                "`{module}` uses `int-literals = \"unsigned\"` but imports `{signed}`, whose signed INT-SYNTAX literals would leak into programs (K imports are unions)"
            ),
        }
    }
}

impl std::error::Error for PartitionError {}

impl Partition {
    /// Computes the partition of every non-framework package.
    ///
    /// # Errors
    ///
    /// Returns [`PartitionError::MixedGroup`] for a group that mixes `internal`
    /// and program-syntax productions.
    pub fn of(theory: &SemanticTheory) -> Result<Self, PartitionError> {
        let mut partition = Self::default();
        for module in theory.modules() {
            if is_framework_module(module.id()) {
                continue;
            }
            let placement = place_module(module, &mut partition.warnings)?;
            partition.report.push(report(module, &placement));
            partition.modules.insert(module.id().clone(), placement);
        }
        Ok(partition)
    }

    /// Returns the placement of one package module, or `None` for the framework.
    #[must_use]
    pub fn module(&self, module: &ModuleId) -> Option<&ModulePlacement> {
        self.modules.get(module)
    }

    /// Returns the `program` productions that cannot be program syntax.
    #[must_use]
    pub fn warnings(&self) -> &[PartitionWarning] {
        &self.warnings
    }

    /// Renders the partition printed by `krs check --partition`: for each
    /// package, the program-syntax module's productions and subsorts, then the
    /// `pub` productions placed in the semantics module with the reason.
    #[must_use]
    pub fn render(&self) -> String {
        let mut output = String::new();
        for package in &self.report {
            let module = package.module.as_str();
            let _ = writeln!(
                output,
                "{} (program syntax)",
                program_syntax_module_name(module)
            );
            if package.syntax.is_empty() {
                output.push_str("  (empty)\n");
            }
            for line in &package.syntax {
                let _ = writeln!(output, "  {line}");
            }
            let _ = writeln!(
                output,
                "{module} (pub productions that are not program syntax)"
            );
            if package.placed.is_empty() {
                output.push_str("  (none)\n");
            }
            for (name, reason) in &package.placed {
                let _ = writeln!(output, "  {name}: {reason}");
            }
        }
        output
    }
}

/// Returns the Rust spelling of a production: `Enum::Variant` or `Struct`.
#[must_use]
pub fn production_display_name(id: &StableItemId) -> String {
    id.disambiguator().strip_prefix("enum:").map_or_else(
        || id.item_name().to_owned(),
        |family| format!("{family}::{}", id.item_name()),
    )
}

fn sort_display(sort: &SemanticSortRef) -> String {
    match sort {
        SemanticSortRef::Declared(id) => id.item_name().to_owned(),
        SemanticSortRef::Builtin(sort) => sort.k_name().to_owned(),
    }
}

fn blocking_builtin(sort: &SemanticSortRef) -> Option<BuiltinSort> {
    match sort {
        SemanticSortRef::Builtin(sort) if !sort.spec().has_program_syntax() => Some(*sort),
        _ => None,
    }
}

fn needs_full_module(production: &SemanticProduction) -> Option<PlacementReason> {
    if let Some(sort) = blocking_builtin(production.result_sort()) {
        return Some(PlacementReason::NeedsFullModule { field: None, sort });
    }
    production
        .items()
        .iter()
        .find_map(|item| match item.kind() {
            GrammarProductionItemKind::NonTerminal { field, sort } => {
                blocking_builtin(sort).map(|sort| PlacementReason::NeedsFullModule {
                    field: Some(field.as_str().to_owned()),
                    sort,
                })
            }
            GrammarProductionItemKind::Terminal { .. }
            | GrammarProductionItemKind::RegexTerminal { .. } => None,
        })
}

fn is_generated_syntax(production: &SemanticProduction) -> bool {
    production.attributes().iter().any(|attribute| {
        matches!(
            attribute,
            ProductionAttribute::Bracket { .. } | ProductionAttribute::Token { .. }
        )
    })
}

fn attribute_origin(
    production: &SemanticProduction,
    matches: fn(&krs_ir_levels::SemanticProductionAttribute) -> bool,
) -> Option<&NodeOrigin> {
    production
        .attributes()
        .iter()
        .find(|attribute| matches(attribute))
        .map(ProductionAttribute::origin)
}

fn is_internal(attribute: &krs_ir_levels::SemanticProductionAttribute) -> bool {
    matches!(attribute, ProductionAttribute::Internal { .. })
}

fn is_program(attribute: &krs_ir_levels::SemanticProductionAttribute) -> bool {
    matches!(attribute, ProductionAttribute::Program { .. })
}

/// Whether a production is K `private`: its Rust item is not `pub`
/// (`pub(crate)` and `pub(in ..)` included). Generated token and bracket
/// productions follow their sort and are never private.
pub(crate) fn is_private(production: &SemanticProduction) -> bool {
    production.visibility() != &RustVisibility::Public && !is_generated_syntax(production)
}

fn production_placement(production: &SemanticProduction) -> Option<PlacementReason> {
    if attribute_origin(production, is_internal).is_some() {
        return Some(PlacementReason::Internal);
    }
    if is_private(production) {
        return Some(PlacementReason::NotPublic);
    }
    needs_full_module(production)
}

fn subsort_placement(subsort: &SemanticSubsort) -> Option<PlacementReason> {
    if is_framework_sort(subsort.subsort()) || is_framework_sort(subsort.supersort()) {
        return Some(PlacementReason::FrameworkSubsort);
    }
    [subsort.subsort(), subsort.supersort()]
        .into_iter()
        .find_map(blocking_builtin)
        .map(|sort| PlacementReason::NeedsFullModule { field: None, sort })
}

fn place_module(
    module: &SemanticModule,
    warnings: &mut Vec<PartitionWarning>,
) -> Result<ModulePlacement, PartitionError> {
    let mut placement = ModulePlacement::default();
    let mut syntax_groups = BTreeSet::new();
    let mut group_members = BTreeMap::<&ProductionGroupId, Vec<&SemanticProduction>>::new();
    for production in module.productions() {
        let reason = production_placement(production);
        for attribute in production.attributes() {
            if let ProductionAttribute::Group { group, .. } = attribute {
                group_members.entry(group).or_default().push(production);
                if reason.is_none() {
                    syntax_groups.insert(group.clone());
                }
            }
        }
        if let Some(reason) = reason {
            if let Some(origin) = attribute_origin(production, is_program) {
                warnings.push(PartitionWarning {
                    origin: origin.clone(),
                    message: program_warning(production, &reason, module.id()),
                });
            }
            placement
                .productions
                .insert(production.id().clone(), reason);
        }
    }
    for (group, members) in &group_members {
        let internal = members
            .iter()
            .find(|member| attribute_origin(member, is_internal).is_some());
        let program = members
            .iter()
            .find(|member| placement.production_is_syntax(member.id()));
        if let (Some(internal), Some(program)) = (internal, program) {
            return Err(PartitionError::MixedGroup {
                group: (*group).clone(),
                internal: production_display_name(internal.id()),
                program: production_display_name(program.id()),
                origin: attribute_origin(internal, is_internal)
                    .expect("found above")
                    .clone(),
            });
        }
    }
    for (index, subsort) in module.subsorts().iter().enumerate() {
        if let Some(reason) = subsort_placement(subsort) {
            placement.subsorts.insert(index, reason);
        }
    }
    for (index, precedence) in module.precedences().iter().enumerate() {
        if !precedence
            .higher()
            .iter()
            .chain(precedence.lower())
            .all(|group| syntax_groups.contains(group))
        {
            placement.precedences.insert(index);
        }
    }
    for (index, associativity) in module.associativities().iter().enumerate() {
        if !associativity
            .groups()
            .iter()
            .all(|group| syntax_groups.contains(group))
        {
            placement.associativities.insert(index);
        }
    }
    Ok(placement)
}

fn program_warning(
    production: &SemanticProduction,
    reason: &PlacementReason,
    module: &ModuleId,
) -> String {
    let name = production_display_name(production.id());
    match reason {
        PlacementReason::NeedsFullModule { field, sort } => {
            let full = sort.spec().k_module.unwrap_or_else(|| sort.k_name());
            let subject = field.as_ref().map_or_else(
                || format!("its result `{}`", sort.k_name()),
                |field| format!("its field `{field}: {}`", sort.k_name()),
            );
            format!(
                "`{name}` is marked `program` but {subject} needs K's {full} module, which has no -SYNTAX variant; it is placed in {} and programs cannot contain it",
                module.as_str()
            )
        }
        other => format!(
            "`{name}` is marked `program` but is {other}; it is placed in {} and programs cannot contain it",
            module.as_str()
        ),
    }
}

fn report(module: &SemanticModule, placement: &ModulePlacement) -> PackageReport {
    let mut syntax = module
        .sorts()
        .iter()
        .map(|sort| format!("sort {}", sort.id().item_name()))
        .collect::<Vec<_>>();
    for (index, subsort) in module.subsorts().iter().enumerate() {
        if placement.subsort_is_syntax(index) {
            syntax.push(format!(
                "subsort {} ::= {}",
                sort_display(subsort.supersort()),
                sort_display(subsort.subsort())
            ));
        }
    }
    let mut placed = Vec::new();
    for production in module.productions() {
        let name = production_display_name(production.id());
        match placement.production_reason(production.id()) {
            None => syntax.push(format!("production {name}")),
            Some(reason) if reason.is_automatic() => {
                placed.push((format!("production {name}"), reason.to_string()));
            }
            Some(_) => {}
        }
    }
    for (index, subsort) in module.subsorts().iter().enumerate() {
        if let Some(reason) = placement.subsorts.get(&index)
            && reason.is_automatic()
        {
            placed.push((
                format!(
                    "subsort {} ::= {}",
                    sort_display(subsort.supersort()),
                    sort_display(subsort.subsort())
                ),
                reason.to_string(),
            ));
        }
    }
    PackageReport {
        module: module.id().clone(),
        syntax,
        placed,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn placement_reasons_name_the_missing_syntax_module() {
        let field = PlacementReason::NeedsFullModule {
            field: Some("topics".to_owned()),
            sort: BuiltinSort::List,
        };
        assert_eq!(
            field.to_string(),
            "argument `topics: List`: K has no LIST-SYNTAX module"
        );
        assert!(field.is_automatic());
        let result = PlacementReason::NeedsFullModule {
            field: None,
            sort: BuiltinSort::Map,
        };
        assert_eq!(
            result.to_string(),
            "result `Map`: K has no MAP-SYNTAX module"
        );
        assert!(!PlacementReason::Internal.is_automatic());
    }

    #[test]
    fn only_sorts_without_syntax_modules_block_program_syntax() {
        for sort in [BuiltinSort::Map, BuiltinSort::List, BuiltinSort::Set] {
            assert_eq!(
                blocking_builtin(&SemanticSortRef::Builtin(sort)),
                Some(sort)
            );
        }
        for sort in [
            BuiltinSort::KSequence,
            BuiltinSort::Int,
            BuiltinSort::Bool,
            BuiltinSort::Id,
            BuiltinSort::Bytes,
            BuiltinSort::String,
        ] {
            assert_eq!(blocking_builtin(&SemanticSortRef::Builtin(sort)), None);
        }
        assert_eq!(program_syntax_module_name("KRS-EVM"), "KRS-EVM-SYNTAX");
    }
}
