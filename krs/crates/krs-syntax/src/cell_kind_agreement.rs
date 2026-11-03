//! The two views of a cell's declaration, compared (S5.1).
//!
//! Every reader of a cell's kind asks [`CellKind`] over one of two views of the same
//! declaration: the parsed source ([`ConfigurationCell`], which the macros and the class oracle
//! read without rustc) and the collected declaration
//! ([`krs_ir::cell_kind::DescriptorCell`], which the collector resolves and every
//! compile-path reader after it reads). [`agreement`] checks that both give every declared cell
//! the same kind, so the views cannot drift apart unseen.
//!
//! What each side reads is its own: the parsed side reads the attribute strings, the `KCell`
//! identifier, the builtin sorts and the cons lists by the names the source writes, and the
//! nested groups by the last segment of their declaration path; the collected side reads the
//! resolved declaration, its stable identities, and the collected grammar's cons productions.
//! Both share [`CellKind::of`], the fold of a view into layers, and the attribute parser that
//! both views' inputs come from.
//!
//! **Limits of a source-only view.** The parsed side does not resolve Rust names. A builtin
//! imported under another name (`use k::builtin::List as Stack;` and `Cell<Stack>`) is a plain
//! leaf there and a `List` leaf in the collected view; a user sort named `List`, `Map` or `Set`
//! is the reverse; and a cons-list sort declared in a package whose source is not among `files`
//! is a plain leaf there. Each is reported as a disagreement, though it is a limit of this check
//! and not a drift between the views. No fixture or port writes one.

use krs_ir::cell_kind::{CellKind, DescriptorCell};
use krs_ir::{DescriptorIndex, DescriptorPayload};
use syn::ext::IdentExt;

use crate::{
    ConfigurationCell, ConfigurationDeclaration, EnumConstructorDeclaration, SyntaxListDeclaration,
};

/// Compares, for every configuration and nested cell declaration `index` holds, each field's
/// collected kind with the kind of the same field parsed from `files`. Returns the number of
/// cells compared, or one line per cell or declaration the views disagree on.
///
/// The parsed declarations are the structs of `files` (at any module depth) marked
/// `#[k::configuration]` or `#[k::cell]`, matched to a collected declaration by name and field
/// names; parsed declarations no collected one matches are not compared. A leaf is a cons list
/// in the parsed view when its sort's name is one `files` declares a cons list: a
/// `#[k::syntax_list]` enum's own name, or a `#[k::cons_list]` constructors enum's `sort`.
///
/// # Errors
///
/// Returns the disagreements, each naming the declaration and the field.
pub fn agreement(index: &DescriptorIndex<'_>, files: &[syn::File]) -> Result<usize, Vec<String>> {
    let mut failures = Vec::new();
    let mut parsed = Vec::new();
    let mut cons_lists = Vec::new();
    for file in files {
        declarations(&file.items, &mut parsed, &mut cons_lists, &mut failures);
    }
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

/// Every `#[k::configuration]` and `#[k::cell]` struct of `items`, and the name of every sort
/// they declare a cons list, inline modules included.
fn declarations(
    items: &[syn::Item],
    parsed: &mut Vec<ConfigurationDeclaration>,
    cons_lists: &mut Vec<String>,
    failures: &mut Vec<String>,
) {
    for item in items {
        match item {
            syn::Item::Enum(item) => {
                if let Some(sort) = cons_list_sort_name(item, failures) {
                    cons_lists.push(sort);
                }
            }
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
                    declarations(items, parsed, cons_lists, failures);
                }
            }
            _ => {}
        }
    }
}

/// The name of the sort the enum `item` declares a cons list, read from the source: a
/// `#[k::syntax_list]` enum is the list sort itself, and a `#[k::constructors(sort = S)]` enum
/// marked `#[k::cons_list]` builds the list sort `S`.
fn cons_list_sort_name(item: &syn::ItemEnum, failures: &mut Vec<String>) -> Option<String> {
    let marked = |name: &str| {
        item.attrs.iter().any(|attribute| {
            attribute
                .path()
                .segments
                .last()
                .is_some_and(|segment| segment.ident == name)
        })
    };
    if marked("syntax_list") {
        return match SyntaxListDeclaration::from_attributed_item(item.clone()) {
            Ok(_) => Some(item.ident.unraw().to_string()),
            Err(error) => {
                failures.push(format!(
                    "`{}` does not parse as a syntax list: {error:?}",
                    item.ident
                ));
                None
            }
        };
    }
    if !(marked("constructors") && marked("cons_list")) {
        return None;
    }
    match EnumConstructorDeclaration::from_attributed_item(item.clone()) {
        Ok(declaration) => declaration.cons_list().and_then(|_| {
            declaration
                .sort()
                .segments
                .last()
                .map(|segment| segment.ident.unraw().to_string())
        }),
        Err(error) => {
            failures.push(format!(
                "`{}` does not parse as a constructors enum: {error:?}",
                item.ident
            ));
            None
        }
    }
}
