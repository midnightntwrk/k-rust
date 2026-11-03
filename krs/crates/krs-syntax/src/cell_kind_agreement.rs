//! The two views of a cell's declaration, compared (S5.1).
//!
//! Every reader of a cell's kind asks [`CellKind`] over one of two views of the same
//! declaration: the parsed source ([`ConfigurationCell`], which the macros and the class oracle
//! read without rustc) and the collected declaration
//! ([`krs_ir::cell_kind::DescriptorCell`], which the collector resolves and every
//! compile-path reader after it reads). [`agreement`] checks that both give every declared cell
//! the same kind, so the views cannot drift apart unseen.

use krs_ir::cell_kind::{CellKind, DescriptorCell};
use krs_ir::{DescriptorIndex, DescriptorPayload, DescriptorSortRef};
use syn::ext::IdentExt;

use crate::{ConfigurationCell, ConfigurationDeclaration};

/// Compares, for every configuration and nested cell declaration `index` holds, each field's
/// collected kind with the kind of the same field parsed from `files`. Returns the number of
/// cells compared, or one line per cell or declaration the views disagree on.
///
/// The parsed declarations are the structs of `files` (at any module depth) marked
/// `#[k::configuration]` or `#[k::cell]`, matched to a collected declaration by name and field
/// names. A leaf is a cons list in the parsed view when its sort's name is the name of a sort the
/// collected grammar makes a cons list: the source alone does not say which sort is one.
///
/// # Errors
///
/// Returns the disagreements, each naming the declaration and the field.
pub fn agreement(index: &DescriptorIndex<'_>, files: &[syn::File]) -> Result<usize, Vec<String>> {
    let mut failures = Vec::new();
    let mut parsed = Vec::new();
    for file in files {
        declarations(&file.items, &mut parsed, &mut failures);
    }
    let cons_lists = index
        .values()
        .filter_map(|descriptor| match descriptor.payload() {
            DescriptorPayload::Grammar(grammar) => krs_ir::cell_kind::cons_list_sort(grammar),
            _ => None,
        })
        .filter_map(|sort| match &sort.sort {
            DescriptorSortRef::Declared(id) => Some(id.item_name().to_owned()),
            _ => None,
        })
        .collect::<Vec<_>>();
    let mut compared = 0;
    for descriptor in index.values() {
        let declaration = match descriptor.payload() {
            DescriptorPayload::FixedConfiguration(configuration) => &configuration.declaration,
            DescriptorPayload::Cell(declaration) => declaration.as_ref(),
            _ => continue,
        };
        let name = descriptor.id().item_name();
        let collected = declaration
            .fields
            .iter()
            .map(|field| DescriptorCell::new(field, index))
            .collect::<Vec<_>>();
        let names = collected
            .iter()
            .map(krs_ir::cell_kind::CellView::name)
            .collect::<Vec<_>>();
        let Some(source) = parsed.iter().find(|candidate| {
            *candidate.name() == name
                && candidate
                    .cells()
                    .iter()
                    .map(|field| field.name().unraw().to_string())
                    .eq(names.iter().cloned())
        }) else {
            failures.push(format!(
                "`{name}`: no `#[k::configuration]` or `#[k::cell]` struct of that name declares the fields {names:?}"
            ));
            continue;
        };
        for (collected, field) in collected.iter().zip(source.cells()) {
            let parsed_kind = CellKind::of(&ConfigurationCell::new(field, &parsed, &cons_lists));
            let collected_kind = collected.kind();
            if parsed_kind != collected_kind {
                failures.push(format!(
                    "`{name}.{}`: collected {collected_kind:?}, parsed {parsed_kind:?}",
                    field.name()
                ));
            }
            compared += 1;
        }
    }
    if failures.is_empty() {
        Ok(compared)
    } else {
        Err(failures)
    }
}

/// Every `#[k::configuration]` and `#[k::cell]` struct of `items`, inline modules included.
fn declarations(
    items: &[syn::Item],
    parsed: &mut Vec<ConfigurationDeclaration>,
    failures: &mut Vec<String>,
) {
    for item in items {
        match item {
            syn::Item::Struct(item) => {
                let marked = item.attrs.iter().any(|attribute| {
                    attribute.path().segments.last().is_some_and(|segment| {
                        segment.ident == "configuration" || segment.ident == "cell"
                    })
                });
                if !marked {
                    continue;
                }
                match ConfigurationDeclaration::from_item(item.clone()) {
                    Ok(declaration) => parsed.push(declaration),
                    Err(error) => failures.push(format!(
                        "`{}` does not parse as a cell declaration: {error:?}",
                        item.ident
                    )),
                }
            }
            syn::Item::Mod(module) => {
                if let Some((_, items)) = &module.content {
                    declarations(items, parsed, failures);
                }
            }
            _ => {}
        }
    }
}
