//! `[result] cells` in a KRS corpus: each cell named by its declared Rust path, as every krs
//! surface names it (a case's `expect.compare`, `krs compare --compare`, a kill's
//! `krs-difference/3`), or by its K name, mapped to the K cell names kink-flow reads.
//!
//! A cell's declared path is the Rust fields from the configuration to it, joined by `.`, through
//! repeated cells without an index (`cpu.regs`, `harts.hart.pc`), as
//! [`krs_exec::Semantics::cells`] names it; its K name is the name of the cell `definition.k`
//! declares (`<regs>`), the field's name unless `#[k::cell(name = "..")]` renames it. Paths are
//! unique, since each is a distinct sequence of fields, and K names are unique, since a
//! configuration names each of its cells once, so every path names one cell and every K name
//! names one cell.
//!
//! An entry is read as a path first: the path is the KRS spelling of every cell, and it always
//! names exactly one, so a corpus written by paths means what it says whatever the K names are.
//! A K name is read only where no cell has it as its path. There it names one cell and competes
//! with no path, so a corpus written against `definition.k` keeps its meaning; where a K name is
//! also another cell's path, the entry is that cell's, the reading every krs surface gives it.
//! The documents state the reading of every entry (`result.krs.cells`), so a reading is never
//! silent. An entry that is neither refuses the corpus at stage `result`, reason
//! `result-cell-unknown`, naming each cell's path with its K cell; two entries that name one
//! cell (its path and its K name, which kink-flow's decode cannot see as one) refuse it there,
//! reason `result-cell-repeated`, naming both.
//!
//! kink-flow then judges the K names as for a K corpus (an unobservable cell, a cell inside one),
//! and the front end adds to its refusal, and to every document's `result`, the cells by path:
//! `result.krs = {compared, not_compared, unobservable}`, each the K-named list beside it by path,
//! and `cells`, each entry as written with the K cell it reads as.

use std::collections::BTreeMap;

use kink_flow::FlowManifest;
use krs_ir_levels::{DefinitionIr, DefinitionSentence};
use serde_json::{Map, Value, json};

use super::stop::Unbound;

/// The configuration's cells: each declared path with its K name, in configuration preorder.
#[derive(Clone, Debug, Default)]
pub(crate) struct CellNames {
    cells: Vec<(String, String)>,
}

impl CellNames {
    /// The cells of the configuration `ir` declares (none without a configuration).
    pub(crate) fn of(ir: &DefinitionIr) -> Self {
        fn walk(
            cells: &[krs_ir::FixedCell<
                krs_ir_levels::DefinitionSortRef,
                krs_ir_levels::SymbolId,
            >],
            prefix: &str,
            output: &mut Vec<(String, String)>,
        ) {
            for cell in cells {
                let path = format!("{prefix}{}", cell.field().unwrap_or(cell.name()));
                output.push((path.clone(), cell.name().to_owned()));
                if let krs_ir::FixedCellContent::Children { children } = cell.content() {
                    walk(children, &format!("{path}."), output);
                }
            }
        }
        let mut cells = Vec::new();
        for sentence in ir
            .modules()
            .iter()
            .flat_map(krs_ir_levels::DefinitionModule::sentences)
        {
            if let DefinitionSentence::Configuration(configuration) = sentence {
                walk(configuration.cells(), "", &mut cells);
            }
        }
        Self { cells }
    }

    /// The K name an entry of `[result] cells` reads as (module documentation).
    fn read(&self, written: &str) -> Option<&str> {
        self.cells
            .iter()
            .find(|(path, _)| path == written)
            .or_else(|| self.cells.iter().find(|(_, name)| name == written))
            .map(|(_, name)| name.as_str())
    }

    /// The K name of the cell whose declared path is `path`.
    pub(crate) fn name_of(&self, path: &str) -> Option<&str> {
        self.cells
            .iter()
            .find(|(declared, _)| declared == path)
            .map(|(_, name)| name.as_str())
    }

    /// The declared path of the cell whose K name is `name`.
    pub(crate) fn path_of(&self, name: &str) -> Option<&str> {
        self.cells
            .iter()
            .find(|(_, k)| k == name)
            .map(|(path, _)| path.as_str())
    }

    /// Every cell as `path (<name>)`, for a refusal.
    fn listed(&self) -> String {
        self.cells
            .iter()
            .map(|(path, name)| format!("{path} (<{name}>)"))
            .collect::<Vec<_>>()
            .join(", ")
    }
}

/// `manifest` with its `[result] cells` mapped to K cell names, and the reading of each entry
/// (`result.krs.cells`: each entry as written to its K name); `manifest` unchanged and no reading
/// without `[result]`.
///
/// # Errors
///
/// `result-cell-unknown` for an entry that is neither a cell's path nor its K name, and
/// `result-cell-repeated` for two entries that name one cell (by its path and by its K name).
pub(crate) fn bind(
    mut manifest: FlowManifest,
    names: &CellNames,
) -> Result<(FlowManifest, Option<BTreeMap<String, String>>), Unbound> {
    let Some(result) = manifest.result.as_mut() else {
        return Ok((manifest, None));
    };
    let mut readings = BTreeMap::new();
    let mut cells = Vec::with_capacity(result.cells.len());
    for written in &result.cells {
        let Some(name) = names.read(written) else {
            return Err(Unbound {
                reason: "result-cell-unknown",
                detail: format!(
                    "[result] cells names `{written}`, which is neither the Rust path nor the K \
                     name of a cell of the configuration; name a cell by its Rust path (its K \
                     cell in brackets): {}",
                    names.listed()
                ),
            });
        };
        if let Some((first, _)) = readings.iter().find(|(_, read)| *read == name) {
            return Err(Unbound {
                reason: "result-cell-repeated",
                detail: format!(
                    "[result] cells names the cell `{}` (<{name}>) twice, as `{first}` and as \
                     `{written}`; name it once",
                    names.path_of(name).unwrap_or(name)
                ),
            });
        }
        readings.insert(written.clone(), name.to_owned());
        cells.push(name.to_owned());
    }
    result.cells = cells;
    Ok((manifest, Some(readings)))
}

/// What the front end adds to a document's `result` and to a refusal of its cells (module
/// documentation).
pub(crate) struct ResultNames {
    names: CellNames,
    readings: Option<BTreeMap<String, String>>,
}

impl ResultNames {
    pub(crate) const fn new(names: CellNames, readings: Option<BTreeMap<String, String>>) -> Self {
        Self { names, readings }
    }

    /// The declared path of the cell whose K name is `name`.
    pub(crate) fn path_of(&self, name: &str) -> Option<&str> {
        self.names.path_of(name)
    }

    /// `document` with `result.krs` added, and a refusal at stage `result` of a cell the corpus
    /// named by another spelling than its K name told that spelling. Applying it twice gives what
    /// applying it once does.
    pub(crate) fn annotate(&self, document: &mut Value) {
        if let Some(result) = document.get_mut("result").and_then(Value::as_object_mut)
            && result.contains_key("slots")
        {
            let by_path = |key: &str| match result.get(key) {
                Some(Value::Array(names)) => Value::Array(
                    names
                        .iter()
                        .map(|name| {
                            name.as_str()
                                .and_then(|name| self.names.path_of(name))
                                .map_or(Value::Null, |path| json!(path))
                        })
                        .collect(),
                ),
                _ => Value::Null,
            };
            let mut krs = Map::new();
            for key in ["compared", "not_compared", "unobservable"] {
                krs.insert(key.into(), by_path(key));
            }
            if let Some(readings) = &self.readings {
                krs.insert("cells".into(), json!(readings));
            }
            result.insert("krs".into(), Value::Object(krs));
        }
        self.tell_refusal(document);
    }

    /// A refusal of a cell of `[result] cells` (stage `result`, a reason `result-cell-..`), which
    /// kink-flow states by K name, with each entry written otherwise and its K cell.
    fn tell_refusal(&self, document: &mut Value) {
        let Some(readings) = &self.readings else {
            return;
        };
        let renamed = readings
            .iter()
            .filter(|(written, name)| written != name)
            .map(|(written, name)| format!("`{written}` is <{name}>"))
            .collect::<Vec<_>>();
        if renamed.is_empty() {
            return;
        }
        let note = format!(" (as [result] cells writes them: {})", renamed.join(", "));
        let Some(spec) = document.get_mut("spec").and_then(Value::as_object_mut) else {
            return;
        };
        let refuses_cells = spec.get("stage").and_then(Value::as_str) == Some("result")
            && spec
                .get("reason")
                .and_then(Value::as_str)
                .is_some_and(|reason| reason.starts_with("result-cell-"));
        let Some(Value::String(detail)) = spec.get_mut("detail") else {
            return;
        };
        if !refuses_cells || detail.ends_with(&note) {
            return;
        }
        let old = detail.clone();
        detail.push_str(&note);
        let told = detail.clone();
        if document.get("action").and_then(Value::as_str) == Some(old.as_str()) {
            document["action"] = json!(told);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn names(cells: &[(&str, &str)]) -> CellNames {
        CellNames {
            cells: cells
                .iter()
                .map(|(path, name)| ((*path).to_owned(), (*name).to_owned()))
                .collect(),
        }
    }

    /// A path is read first, and a K name only where it is no cell's path.
    #[test]
    fn an_entry_is_read_as_a_path_then_as_a_k_name() {
        let names = names(&[
            ("k", "k"),
            ("ei_pending", "eiPending"),
            ("cpu", "cpu"),
            ("cpu.regs", "regs"),
            ("halted", "stopped"),
            ("stop", "halted"),
        ]);
        assert_eq!(names.read("ei_pending"), Some("eiPending"));
        assert_eq!(names.read("eiPending"), Some("eiPending"));
        assert_eq!(names.read("cpu.regs"), Some("regs"));
        assert_eq!(names.read("regs"), Some("regs"));
        // `halted` is one cell's path and another's K name: the path is read.
        assert_eq!(names.read("halted"), Some("stopped"));
        assert_eq!(names.read("stop"), Some("halted"));
        assert_eq!(names.read("pc"), None);
        assert_eq!(names.path_of("regs"), Some("cpu.regs"));
    }
}
