//! Program-syntax partition of each package (decisions X12 and R1).
//!
//! Every package emits two K modules: `<NS>-SYNTAX`, the grammar programs may
//! use, and `<NS>`, which imports it and adds everything else rules may use.
//! A `pub` production that is not `internal` is program syntax, unless its
//! result or argument sorts include a builtin sort that K supplies only with a
//! full module (Map, List and Set have no `-SYNTAX` module in K 7.1.337). Such a
//! production is placed in `<NS>` automatically: silently, unless the author
//! asserted `program`, which turns the placement into a warning.
//!
//! A function evaluated in one instance of a Map collection is placed in `<NS>`
//! automatically too ([`PlacementReason::InstanceFunction`]): it receives the
//! instance's key as a hidden argument, and a program is evaluated in no
//! instance, so no program can apply it.
//!
//! When a dependency package's rules need the configuration, a third module,
//! `<NS>-CONFIGURATION`, holds it below that package's module, and declares
//! the productions the configuration names that its imports do not supply,
//! with the subsort sentences its typing reads
//! (`lowering::ConfigurationSplit`). Such a production is not `private`.

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

use crate::instance_keys::InstanceKeys;

/// K namespace of the facade's framework package, which is not partitioned.
pub(crate) const FRAMEWORK_NAMESPACE: &str = "KRS-FRAMEWORK";

/// Suffix of a package's program-syntax module.
pub const PROGRAM_SYNTAX_SUFFIX: &str = "-SYNTAX";

/// Suffix of the configured package's configuration module, emitted only
/// when a dependency package's rules need the configuration (FU-18).
pub const CONFIGURATION_SUFFIX: &str = "-CONFIGURATION";

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
    /// The production is a function evaluated in one instance of each of these
    /// Map collections, outermost first ([`crate::instance_keys`]): its function
    /// context reads such an instance, or the context of a function it applies
    /// does. It receives each instance's key as a hidden argument, and a
    /// program is a term evaluated in no instance, so no program can apply it.
    /// Whether a function is one depends on where the definition's
    /// configuration holds the cells it reads, not on its declaration.
    InstanceFunction {
        /// The K names of the Map collection cells that enclose `innermost`, outermost first.
        outer: Vec<String>,
        /// The K name of the innermost Map collection cell.
        innermost: String,
    },
}

impl PlacementReason {
    /// Whether this placement is the automatic R1 placement of a `pub` production.
    #[must_use]
    pub const fn is_automatic(&self) -> bool {
        matches!(
            self,
            Self::NeedsFullModule { .. } | Self::InstanceFunction { .. }
        )
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
            Self::InstanceFunction { outer, innermost } => {
                let (cells, holders, key) = if outer.is_empty() {
                    ("cell", format!("`{innermost}`"), "the instance's key")
                } else {
                    let outer = outer
                        .iter()
                        .map(|holder| format!("`{holder}`"))
                        .collect::<Vec<_>>();
                    (
                        "cells",
                        format!("{} and `{innermost}`", outer.join(", ")),
                        "each instance's key",
                    )
                };
                write!(
                    formatter,
                    "evaluated in one instance of the Map collection {cells} {holders}, so it receives {key}, and a program is evaluated in no instance"
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
    configuration: Option<ConfigurationReport>,
    warnings: Vec<PartitionWarning>,
}

/// The sentences the configuration module holds in place of packages'
/// semantics modules (`lowering::ConfigurationSplit`).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConfigurationReport {
    module: ModuleId,
    /// Each sentence with the module of its package.
    held: Vec<(String, ModuleId)>,
}

impl ConfigurationReport {
    pub(crate) const fn new(module: ModuleId, held: Vec<(String, ModuleId)>) -> Self {
        Self { module, held }
    }
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
    /// A dependency package's rules need the configuration, so it is emitted
    /// in a module of its own, but the configuration names a symbol that
    /// module can neither import nor declare.
    ConfigurationVisibility(Box<ConfigurationVisibility>),
}

/// The subject of [`PartitionError::ConfigurationVisibility`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConfigurationVisibility {
    /// The configuration module.
    pub module: String,
    /// The configured package's semantics module.
    pub configured: String,
    /// The dependency modules whose rules need the configuration.
    pub dependents: Vec<String>,
    /// The emitted name of the symbol the configuration names.
    pub symbol: String,
    /// The module of the package that declares the symbol, when it is known.
    pub owner: Option<String>,
    /// Why the configuration module cannot declare the symbol.
    pub obstacle: ConfigurationObstacle,
    /// Whether the symbol could be program syntax: no sort of it, and of
    /// no production a sentence orders with it, lacks a `-SYNTAX` module.
    pub program: bool,
    /// The production, when the symbol is one.
    pub item: Option<StableItemId>,
}

/// Why the configuration module cannot declare a production the
/// configuration names ([`ConfigurationVisibility`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ConfigurationObstacle {
    /// An argument or the result has a cell sort. The configuration sentence
    /// declares its cell sorts, so the production's declaration needs the
    /// configuration that names the production. KRS does not declare the
    /// two in one module.
    CellSort {
        /// The cell sort.
        sort: String,
    },
    /// The production is in a group that a precedence or associativity
    /// sentence of its package orders. K applies priorities and
    /// associativity per module, and the sentence stays with the group's
    /// other productions, above the configuration.
    OrderedGroup,
    /// No production of the theory declares the symbol below the
    /// configuration, and the configuration module cannot declare it.
    Undeclared,
    /// The symbol is a sort whose term the configuration places where
    /// another sort is expected, and the subsort sentences the configuration
    /// module holds or imports do not relate the two.
    Subsort {
        /// The expected sort.
        supersort: String,
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
            Self::ConfigurationVisibility(hidden) => {
                let ConfigurationVisibility {
                    module,
                    configured,
                    dependents,
                    symbol,
                    owner,
                    obstacle,
                    program,
                    ..
                } = &**hidden;
                let dependents = dependents
                    .iter()
                    .map(|dependent| format!("`{dependent}`"))
                    .collect::<Vec<_>>()
                    .join(", ");
                let owner = owner.as_deref().unwrap_or(configured);
                write!(
                    formatter,
                    "the rules of {dependents} need the configuration, so it is emitted in `{module}`, a module below theirs; the configuration names `{symbol}`, "
                )?;
                match obstacle {
                    ConfigurationObstacle::CellSort { sort } => write!(
                        formatter,
                        "which `{owner}` declares over the cell sort `{sort}`; the configuration sentence declares its cell sorts, so the production and the configuration would each need the other declared first, and `{module}` does not declare `{symbol}`. An initializer may call a production of `{configured}` or of a package it depends on whose argument and result sorts are not cell sorts"
                    ),
                    ConfigurationObstacle::OrderedGroup => {
                        write!(
                            formatter,
                            "which `{owner}` declares in a group that one of its precedence or associativity sentences orders; K applies priorities and associativity per module and the sentence stays in `{owner}` with the group's other productions, so `{module}` cannot declare `{symbol}`. Declare the production the initializer calls outside every ordered group, in `{configured}` or in a package it depends on"
                        )?;
                        if *program {
                            write!(
                                formatter,
                                ", or make every production those sentences order program syntax (`pub`, not `internal`), which lets programs contain them"
                            )?;
                        }
                        Ok(())
                    }
                    ConfigurationObstacle::Undeclared => write!(
                        formatter,
                        "which no module that `{module}` imports declares. Declare it in `{configured}`, or in a package `{configured}` depends on"
                    ),
                    ConfigurationObstacle::Subsort { supersort } => write!(
                        formatter,
                        "a sort whose term it places where `{supersort}` is expected; a K module reads only its own subsort sentences and those of the modules it imports, and none of them makes `{symbol}` a subsort of `{supersort}`. Declare the subsort in `{configured}`, or in a package `{configured}` depends on"
                    ),
                }
            }
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
        let keys = InstanceKeys::of(theory.modules());
        for module in theory.modules() {
            // A spec module (KF-041) is a proof module: it has no program syntax.
            if is_framework_module(module.id()) || module.is_spec() {
                continue;
            }
            let placement = place_module(module, &keys, &mut partition.warnings)?;
            partition.report.push(report(module, &placement));
            partition.modules.insert(module.id().clone(), placement);
        }
        Ok(partition)
    }

    /// Records the sentences the configuration module holds.
    #[must_use]
    pub(crate) fn with_configuration(mut self, configuration: Option<ConfigurationReport>) -> Self {
        self.configuration = configuration;
        self
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
    /// `pub` productions placed in the semantics module with the reason; then
    /// the sentences the configuration module holds, when it holds any.
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
        if let Some(configuration) = &self.configuration {
            let _ = writeln!(
                output,
                "{} (sentences the configuration depends on, held in place of their packages' modules)",
                configuration.module.as_str()
            );
            for (sentence, owner) in &configuration.held {
                let _ = writeln!(output, "  {sentence}: of {}", owner.as_str());
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

pub(crate) fn sort_display(sort: &SemanticSortRef) -> String {
    match sort {
        SemanticSortRef::Declared(id) => id.item_name().to_owned(),
        SemanticSortRef::Builtin(sort) => sort.k_name().to_owned(),
        SemanticSortRef::Cell(id) => format!("{}Cell", id.item_name()),
        SemanticSortRef::LeafCell(_) => crate::LEAF_CELL_SORT.to_owned(),
        SemanticSortRef::CellCollection(_) => crate::CELL_COLLECTION_SORT.to_owned(),
        SemanticSortRef::Parameter(name) => name.to_string(),
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

/// Whether an author could make `production` program syntax: none of its
/// sorts is a builtin that K supplies only with a full module.
pub(crate) fn could_be_program_syntax(production: &SemanticProduction) -> bool {
    needs_full_module(production).is_none()
}

fn is_bracket(production: &SemanticProduction) -> bool {
    production
        .attributes()
        .iter()
        .any(|attribute| matches!(attribute, ProductionAttribute::Bracket { .. }))
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
/// (`pub(crate)` and `pub(in ..)` included). A token production follows its
/// `#[k::token]` carrier, the struct or the type alias. A generated bracket
/// production follows its sort and is never private.
pub(crate) fn is_private(production: &SemanticProduction) -> bool {
    production.visibility() != &RustVisibility::Public && !is_bracket(production)
}

/// Whether a production is program syntax, placed in `<NS>-SYNTAX`, given the
/// instance keys of the definition's functions (`keys`).
pub(crate) fn is_program_syntax(production: &SemanticProduction, keys: &InstanceKeys) -> bool {
    production_placement(production, keys).is_none()
}

fn production_placement(
    production: &SemanticProduction,
    keys: &InstanceKeys,
) -> Option<PlacementReason> {
    if attribute_origin(production, is_internal).is_some() {
        return Some(PlacementReason::Internal);
    }
    if is_private(production) {
        return Some(PlacementReason::NotPublic);
    }
    let mut holders = keys
        .function(production.id())
        .iter()
        .map(|holder| {
            keys.holder(holder)
                .map_or_else(|| holder.to_string(), |holder| holder.name.clone())
        })
        .collect::<Vec<_>>();
    if let Some(innermost) = holders.pop() {
        return Some(PlacementReason::InstanceFunction {
            outer: holders,
            innermost,
        });
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
    keys: &InstanceKeys,
    warnings: &mut Vec<PartitionWarning>,
) -> Result<ModulePlacement, PartitionError> {
    let mut placement = ModulePlacement::default();
    let mut syntax_groups = BTreeSet::new();
    let mut group_members = BTreeMap::<&ProductionGroupId, Vec<&SemanticProduction>>::new();
    for production in module.productions() {
        let reason = production_placement(production, keys);
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
    // A syntactic list's terminator is generated from its cons sentence, so
    // it is placed with the cons production (KF-020).
    for production in module.productions() {
        let Some(cons) = production
            .attributes()
            .iter()
            .find_map(|attribute| match attribute {
                ProductionAttribute::ListTerminator { cons, .. } => Some(cons),
                _ => None,
            })
        else {
            continue;
        };
        match placement.productions.get(cons).cloned() {
            Some(reason) => {
                placement
                    .productions
                    .insert(production.id().clone(), reason);
            }
            None => {
                placement.productions.remove(production.id());
            }
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
    fn an_instance_function_is_placed_because_a_program_is_in_no_instance() {
        let one = PlacementReason::InstanceFunction {
            outer: Vec::new(),
            innermost: "hart".to_owned(),
        };
        assert_eq!(
            one.to_string(),
            "evaluated in one instance of the Map collection cell `hart`, so it receives the instance's key, and a program is evaluated in no instance"
        );
        assert!(one.is_automatic());
        let two = PlacementReason::InstanceFunction {
            outer: vec!["cluster".to_owned()],
            innermost: "hart".to_owned(),
        };
        assert_eq!(
            two.to_string(),
            "evaluated in one instance of the Map collection cells `cluster` and `hart`, so it receives each instance's key, and a program is evaluated in no instance"
        );
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
