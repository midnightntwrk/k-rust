//! The lint on a holder's rule that pre-empts a cell group's rule
//! (`krs::analysis::holder-preempts-group`).
//!
//! A library's rules for the cell group it declares are rules of every definition whose
//! configuration holds the group, and they are what the group's cells mean.
//! K tries a rule only where no rule of a more urgent priority (a lower number) applies, across
//! every module of the definition.
//! So a holder's rule at a priority more urgent than a group rule's, which can apply where the
//! group rule does, takes those states from the group rule: in that definition the group rule
//! does not apply there, and the group means something other than its author wrote, though the
//! author's package is unchanged and checks as before.
//! The lint makes that visible: it is a warning, and it changes nothing emitted.
//!
//! # Which pairs count
//!
//! - The *group rule* is a transition of the package that declares the group, every cell of
//!   whose footprint lies inside the group: a rule for the group, or a rule of that package whose
//!   cells happen to be the group's.
//!   The group is the innermost one around the footprint that its package declares.
//!   An `owise` group rule is not one: `owise` states that the rule applies where no other rule
//!   does, so a holder's rule before it is what the rule says.
//! - The *holder rule* is a transition of a package whose declarations hold the group: the
//!   package of the configuration, or of a group around the group, other than the group's own
//!   package.
//!   Two rules of one package are ordered by their one author, who sees both.
//!   An `owise` holder rule is after every rule it meets, so it pre-empts none.
//! - The holder rule's priority is more urgent than the group rule's.
//!   A holder rule at a later priority is tried only where the group rule failed, which is the
//!   order a group's rules have in any definition, so it changes nothing the group states.
//!   A group rule at a more urgent priority than a holder rule acts before the holder, which the
//!   holder's author sees in the library that the definition chose to hold.
//! - The two are shown to overlap as the overlap check shows two rules at one priority to:
//!   some unification of their patterns is not separated by their guards
//!   ([`super::transitions_overlap`]).
//!   Two rules with disjoint footprints commute: the group rule still applies after the holder
//!   rule has, so that pair is not reported (where the holder rule applies forever, the group
//!   rule is delayed forever, which the lint does not judge).
//!
//! The rules read are the transitions the overlap check reads: a heating or cooling step, an
//! `anywhere` rule, an equation and a `raw_k!` sentence are not.

use std::collections::{BTreeMap, BTreeSet};

use krs_diagnostic::{Diagnostic, Label, Location, Severity, codes};
use krs_ir::{FixedCell, FixedCellContent, OriginFrame, PackageId, SemanticId, StableItemId};
use krs_ir_levels::{SemanticConfiguration, SemanticModule, SemanticSortRef};

use super::{DEFAULT_PRIORITY, SortGraph, TransitionView, transitions, transitions_overlap};

/// One group cell of the configuration.
struct Group<'m> {
    /// The `#[k::cell]` struct that declares it.
    declaration: &'m StableItemId,
    /// Every cell below it.
    cells: BTreeSet<&'m SemanticId>,
    /// The packages whose declarations hold it: the configuration's and those of the groups
    /// around it.
    holders: BTreeSet<&'m PackageId>,
}

/// The `warning[krs::analysis::holder-preempts-group]` diagnostics of a lowered theory's
/// modules (the module documentation): none for a definition whose configuration holds no group
/// that another package declares.
#[must_use]
pub fn holder_preempts_warnings(modules: &[SemanticModule]) -> Vec<Diagnostic> {
    let mut configurations = modules.iter().filter_map(SemanticModule::configuration);
    let (Some(configuration), None) = (configurations.next(), configurations.next()) else {
        return Vec::new();
    };
    let Some(root) = configuration_package(configuration) else {
        return Vec::new();
    };
    let mut groups = Vec::new();
    collect_groups(configuration.cells(), &BTreeSet::from([root]), &mut groups);
    if groups
        .iter()
        .all(|group| group.declaration.package() == root)
    {
        return Vec::new();
    }
    let views = transitions(modules);
    let mut footprints = BTreeMap::<&StableItemId, BTreeSet<&SemanticId>>::new();
    for view in &views {
        footprints
            .entry(view.id())
            .or_default()
            .extend(view.clauses.iter().map(|clause| clause.cell));
    }
    let group_of = footprints
        .into_iter()
        .filter_map(|(rule, cells)| {
            // Groups are listed outer first, so the last one around the footprint is innermost.
            let group = groups.iter().rev().find(|group| {
                group.declaration.package() == rule.package()
                    && !cells.is_empty()
                    && cells.iter().all(|cell| group.cells.contains(cell))
            })?;
            Some((rule, group))
        })
        .collect::<BTreeMap<_, _>>();
    if group_of.is_empty() {
        return Vec::new();
    }
    let graph = SortGraph::from_modules(modules);
    // Each pair once, in the order of the holder rule, then the group rule.
    let mut pairs = BTreeMap::<(&StableItemId, &StableItemId), (usize, usize)>::new();
    for (by, holder) in views.iter().enumerate() {
        if holder.owise {
            continue;
        }
        for (of, member) in views.iter().enumerate() {
            let Some(group) = group_of.get(member.id()) else {
                continue;
            };
            if member.owise
                || holder.priority >= member.priority
                || holder.id().package() == member.id().package()
                || !group.holders.contains(holder.id().package())
                || pairs.contains_key(&(holder.id(), member.id()))
            {
                continue;
            }
            if transitions_overlap(holder, member, &graph) {
                pairs.insert((holder.id(), member.id()), (by, of));
            }
        }
    }
    pairs
        .into_values()
        .map(|(by, of)| {
            let member = &views[of];
            warning(&views[by], member, group_of[member.id()])
        })
        .collect()
}

/// The package that declares `configuration`: the package of its authored origin.
fn configuration_package(configuration: &SemanticConfiguration) -> Option<&PackageId> {
    match configuration.origin().origin().frames().first()? {
        OriginFrame::Ranged {
            item: Some(item), ..
        } => Some(item.package()),
        OriginFrame::Ranged { range, .. } => Some(range.file.package()),
        _ => None,
    }
}

/// Every group cell below `cells`, outer before inner, each with the packages that hold it.
fn collect_groups<'m>(
    cells: &'m [FixedCell<SemanticSortRef, SemanticId>],
    holders: &BTreeSet<&'m PackageId>,
    output: &mut Vec<Group<'m>>,
) {
    fn below<'m>(
        cells: &'m [FixedCell<SemanticSortRef, SemanticId>],
        output: &mut BTreeSet<&'m SemanticId>,
    ) {
        for cell in cells {
            output.insert(cell.id());
            if let FixedCellContent::Children { children } = cell.content() {
                below(children, output);
            }
        }
    }
    for cell in cells {
        let FixedCellContent::Children { children } = cell.content() else {
            continue;
        };
        match cell.declaration() {
            Some(declaration) => {
                let mut inside = BTreeSet::new();
                below(children, &mut inside);
                output.push(Group {
                    declaration,
                    cells: inside,
                    holders: holders.clone(),
                });
                let mut inner = holders.clone();
                inner.insert(declaration.package());
                collect_groups(children, &inner, output);
            }
            None => collect_groups(children, holders, output),
        }
    }
}

/// The priority a view is tried at, as a reader states it.
fn priority_text(view: &TransitionView<'_>) -> String {
    if view.rule.priority().is_some() {
        format!("priority {}", view.priority)
    } else {
        format!("the default priority {DEFAULT_PRIORITY}")
    }
}

/// The warning that `holder` pre-empts `member`, a rule of `group`.
fn warning(
    holder: &TransitionView<'_>,
    member: &TransitionView<'_>,
    group: &Group<'_>,
) -> Diagnostic {
    let by = holder.id().item_name();
    let of = member.id().item_name();
    let holder_package = holder.id().package().cargo_name();
    let library = member.id().package().cargo_name();
    let group_name = group.declaration.item_name();
    let message = format!(
        "the rule `{by}` of package `{holder_package}`, at {}, pre-empts the rule `{of}` of the cell group `{group_name}` of package `{library}`, at {}: the two can apply to one configuration, and a rule is tried only where no rule of a more urgent priority applies, so in this definition `{of}` does not apply where `{by}` does",
        priority_text(holder),
        priority_text(member),
    );
    let mut warning = match holder.rule.origin().origin().exact_authored_range() {
        Some(range) => Diagnostic::error(
            codes::analysis::HOLDER_PREEMPTS_GROUP,
            message,
            Location::Source(range),
        ),
        None => Diagnostic::error(
            codes::analysis::HOLDER_PREEMPTS_GROUP,
            message,
            Location::None,
        )
        .with_item(holder.id().to_string()),
    };
    warning.severity = Severity::Warning;
    if let Some(range) = member.rule.origin().origin().exact_authored_range() {
        warning = warning.with_secondary(
            Label::new(Location::Source(range))
                .with_message(format!("the rule `{of}` of `{group_name}`")),
        );
    }
    warning
        .with_note(format!(
            "`{library}`'s rules for `{group_name}` are what its cells mean in every definition that holds it, so this definition holds `{group_name}` with another meaning where `{by}` applies"
        ))
        .with_help(format!(
            "to act beside the group without changing what it means, drop the priority and guard `{by}` so that it cannot apply where `{of}` does; where this definition must decide such a state itself, ask the author of `{library}` to leave the state to the holder, as an open item that `{group_name}`'s rules produce and never consume"
        ))
}
