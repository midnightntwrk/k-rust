//! `krs-gate cell-kinds`: a descriptor bundle's cell kinds against the source of the packages
//! that declare its cells.
//!
//! The collector's declaration of each cell, as every compile-path reader sees it, and the
//! source's declaration, as the macros and the class oracle parse it, must give each cell the
//! same `CellKind` ([`krs_syntax::cell_kind_agreement::agreement`]).

use std::collections::BTreeSet;
use std::error::Error;
use std::fs;
use std::path::{Path, PathBuf};

use krs_ir::{DescriptorBundle, DescriptorIndex, DescriptorPayload};

/// Compares the kinds of the cells `bundle` declares with those the Rust sources of the
/// packages that declare them declare, and returns how many cells agree. `packages` gives each
/// package that may have written the bundle as its Cargo name and its source directory; the
/// sources compared are those of the packages the bundle's cell declarations belong to.
///
/// # Errors
///
/// Returns an error when a file cannot be read or parsed, when the bundle declares no cell or
/// declares one in a package `packages` does not name, or when the views disagree on a cell.
pub fn run(bundle: &Path, packages: &[(String, PathBuf)]) -> Result<usize, Box<dyn Error>> {
    let bundle: DescriptorBundle = serde_json::from_slice(&fs::read(bundle)?)?;
    let index = DescriptorIndex::new(&bundle);
    let declaring = index
        .values()
        .filter(|descriptor| {
            matches!(
                descriptor.payload(),
                DescriptorPayload::FixedConfiguration(_) | DescriptorPayload::Cell(_)
            )
        })
        .map(|descriptor| descriptor.id().package().cargo_name())
        .collect::<BTreeSet<_>>();
    if declaring.is_empty() {
        return Err("the bundle declares no cell".into());
    }
    let mut paths = Vec::new();
    for package in declaring {
        let (_, source) = packages
            .iter()
            .find(|(name, _)| name == package)
            .ok_or_else(|| {
                format!("the bundle declares cells of `{package}`, whose source is not given")
            })?;
        rust_files(source, &mut paths)?;
    }
    paths.sort();
    let files = paths
        .iter()
        .map(|path| {
            let text = fs::read_to_string(path)?;
            syn::parse_file(&text).map_err(|error| format!("{}: {error}", path.display()).into())
        })
        .collect::<Result<Vec<_>, Box<dyn Error>>>()?;
    let compared =
        krs_syntax::cell_kind_agreement::agreement(&index, &files).map_err(|failures| {
            format!(
                "the collected and parsed cell kinds disagree:\n{}",
                failures.join("\n")
            )
        })?;
    if compared == 0 {
        return Err("no cell was compared".into());
    }
    Ok(compared)
}

fn rust_files(directory: &Path, out: &mut Vec<PathBuf>) -> Result<(), Box<dyn Error>> {
    for entry in fs::read_dir(directory)? {
        let path = entry?.path();
        if path.is_dir() {
            rust_files(&path, out)?;
        } else if path.extension().is_some_and(|extension| extension == "rs") {
            out.push(path);
        }
    }
    Ok(())
}
