//! `krs-gate cell-kinds`: a descriptor bundle's cell kinds against its package's source.
//!
//! The collector's declaration of each cell, as every compile-path reader sees it, and the
//! source's declaration, as the macros and the class oracle parse it, must give each cell the
//! same `CellKind` ([`krs_syntax::cell_kind_agreement::agreement`]).

use std::error::Error;
use std::fs;
use std::path::{Path, PathBuf};

use krs_ir::{DescriptorBundle, DescriptorIndex};

/// Compares the kinds of the cells `bundle` declares with those the Rust sources under `sources`
/// declare, and returns how many cells agree.
///
/// # Errors
///
/// Returns an error when a file cannot be read or parsed, or when the views disagree on a cell.
pub fn run(bundle: &Path, sources: &[PathBuf]) -> Result<usize, Box<dyn Error>> {
    let bundle: DescriptorBundle = serde_json::from_slice(&fs::read(bundle)?)?;
    let index = DescriptorIndex::new(&bundle);
    let mut paths = Vec::new();
    for source in sources {
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
    krs_syntax::cell_kind_agreement::agreement(&index, &files).map_err(|failures| {
        format!(
            "the collected and parsed cell kinds disagree:\n{}",
            failures.join("\n")
        )
        .into()
    })
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
