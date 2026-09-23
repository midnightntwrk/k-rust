//! Coverage evidence: which workspace functions one run executed.
//!
//! A run of `krust` built with `-C instrument-coverage` records the execution count of every
//! instrumented function, whatever entry reached it. `llvm-cov export` writes those counts as
//! JSON; [`normalize_export`] reduces the export to the workspace functions, and
//! [`map_algorithm_sites`] maps each algorithm's sites onto them for the join.
//!
//! An algorithm ran when one of its site items executed. A site item is the function, method,
//! or `impl` block that a `sites` entry names, together with every closure and nested function
//! inside its lines.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{
    Error, Graph,
    cards::{ItemSpan, item_spans},
};

/// Schema of the canonical `coverage.toml`.
pub const COVERAGE_SCHEMA_VERSION: u32 = 1;

/// The workspace functions of one coverage-instrumented run.
#[derive(Clone, Debug, Default, PartialEq, Serialize, Deserialize)]
pub struct Coverage {
    pub schema_version: u32,
    /// SHA-256 of the instrumented binary that produced the counts.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub binary_sha256: Option<String>,
    #[serde(rename = "file", default)]
    pub files: Vec<CoveredFile>,
}

/// One workspace source file with an instrumented function.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct CoveredFile {
    /// Workspace-relative path, as `crates/k-rust/src/lib.rs`.
    pub path: String,
    /// SHA-256 of the source as compiled; the join checks the checkout against it.
    pub sha256: String,
    #[serde(rename = "function", default)]
    pub functions: Vec<CoveredFunction>,
}

/// One instrumented function; the instantiations of a generic function are summed.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Serialize, Deserialize)]
pub struct CoveredFunction {
    /// First line of the function's code regions, 1-based.
    pub start: usize,
    /// Last line of the function's code regions, inclusive.
    pub end: usize,
    /// Demangled path without crate hashes and generic arguments.
    pub name: String,
    /// Times the function was entered.
    pub count: u64,
}

#[derive(Deserialize)]
struct Export {
    #[serde(rename = "type")]
    kind: String,
    data: Vec<ExportData>,
}

#[derive(Deserialize)]
struct ExportData {
    #[serde(default)]
    functions: Vec<ExportFunction>,
}

#[derive(Deserialize)]
struct ExportFunction {
    name: String,
    count: u64,
    /// `[line start, column start, line end, column end, count, file id, expanded file id, kind]`.
    regions: Vec<Vec<u64>>,
    filenames: Vec<String>,
}

/// Region kind of an ordinary code region in an `llvm-cov export` region array.
const CODE_REGION: u64 = 0;

/// Reduce an `llvm-cov export` JSON document to the functions of workspace sources.
///
/// A function belongs to the file of its code regions in file 0 and spans their first to last
/// line. Only files below `source_root` whose relative path is `crates/<crate>/src/**.rs` are
/// kept. Each file's digest is read from the file the export names, which is the source that was
/// compiled. `binary`, when given, is the instrumented executable, whose digest is recorded.
pub fn normalize_export(
    export: &str,
    source_root: &Path,
    binary: Option<&Path>,
) -> Result<Coverage, Error> {
    let export: Export = serde_json::from_str(export)?;
    if export.kind != "llvm.coverage.json.export" {
        return Err(Error::Invalid(format!(
            "coverage export type is {:?}, not llvm.coverage.json.export",
            export.kind
        )));
    }
    let roots = [
        source_root.to_owned(),
        fs::canonicalize(source_root).unwrap_or_else(|_| source_root.to_owned()),
    ];
    let mut functions = BTreeMap::<(String, usize, usize, String), u64>::new();
    let mut sources = BTreeMap::<String, PathBuf>::new();
    for function in export.data.iter().flat_map(|data| &data.functions) {
        let Some(filename) = function.filenames.first() else {
            continue;
        };
        let absolute = Path::new(filename);
        let Some(relative) = roots
            .iter()
            .find_map(|root| absolute.strip_prefix(root).ok())
            .map(slash_path)
            .filter(|relative| is_workspace_source(relative))
        else {
            continue;
        };
        let lines = function
            .regions
            .iter()
            .filter(|region| region.len() >= 8 && region[5] == 0 && region[7] == CODE_REGION)
            .map(|region| (region[0], region[2]))
            .collect::<Vec<_>>();
        let (Some(start), Some(end)) = (
            lines.iter().map(|(start, _)| *start).min(),
            lines.iter().map(|(_, end)| *end).max(),
        ) else {
            continue;
        };
        let key = (
            relative.clone(),
            usize::try_from(start).map_err(|_| Error::Invalid("line overflow".to_owned()))?,
            usize::try_from(end).map_err(|_| Error::Invalid("line overflow".to_owned()))?,
            demangle(&function.name),
        );
        let total = functions.entry(key).or_default();
        *total = total
            .checked_add(function.count)
            .ok_or_else(|| Error::Invalid(format!("execution count overflow in {relative}")))?;
        sources
            .entry(relative)
            .or_insert_with(|| absolute.to_owned());
    }
    let mut files = BTreeMap::<String, CoveredFile>::new();
    for ((path, start, end, name), count) in functions {
        let file = match files.get_mut(&path) {
            Some(file) => file,
            None => {
                let sha256 = sha256_file(&sources[&path])?;
                files.entry(path.clone()).or_insert(CoveredFile {
                    path: path.clone(),
                    sha256,
                    functions: Vec::new(),
                })
            }
        };
        file.functions.push(CoveredFunction {
            start,
            end,
            name,
            count,
        });
    }
    Ok(Coverage {
        schema_version: COVERAGE_SCHEMA_VERSION,
        binary_sha256: binary.map(sha256_file).transpose()?,
        files: files.into_values().collect(),
    })
}

/// Serialize coverage in its canonical TOML form: one `[[file]]` table per source file, and one
/// inline table per function, ordered by path, lines, and name.
pub fn canonical_coverage_toml(coverage: &Coverage) -> String {
    let quote = |text: &str| toml::Value::String(text.to_owned()).to_string();
    let mut output = format!("schema_version = {}\n", coverage.schema_version);
    if let Some(digest) = &coverage.binary_sha256 {
        output.push_str(&format!("binary_sha256 = {}\n", quote(digest)));
    }
    for file in &coverage.files {
        output.push_str(&format!(
            "\n[[file]]\npath = {}\nsha256 = {}\nfunction = [\n",
            quote(&file.path),
            quote(&file.sha256)
        ));
        for function in &file.functions {
            output.push_str(&format!(
                "  {{ start = {}, end = {}, count = {}, name = {} }},\n",
                function.start,
                function.end,
                function.count,
                quote(&function.name)
            ));
        }
        output.push_str("]\n");
    }
    output
}

/// Read a `coverage.toml` at the current schema.
pub fn read_coverage(path: &Path) -> Result<Coverage, Error> {
    let coverage: Coverage = toml::from_str(&fs::read_to_string(path)?)?;
    if coverage.schema_version != COVERAGE_SCHEMA_VERSION {
        return Err(Error::Invalid(format!(
            "{}: coverage schema {}, but this tool reads schema {COVERAGE_SCHEMA_VERSION}; rerun `algo-graph coverage`",
            path.display(),
            coverage.schema_version
        )));
    }
    Ok(coverage)
}

/// What the coverage records for one site of an algorithm.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum SiteState {
    /// Some instrumented function inside the item was entered: `executed` of `functions`, and
    /// the largest entry count among them.
    Executed {
        executed: usize,
        functions: usize,
        count: u64,
    },
    /// Every instrumented function inside the item, at least one, was entered zero times.
    Zero { functions: usize },
    /// The site names a struct, enum, union, or type alias, and no instrumented function lies in
    /// the type's item (derived-trait expansions) or in an `impl` block for the type in the
    /// site's file: the type holds no code that executes.
    TypeSite,
    /// No instrumented function lies inside the item; the reason says why.
    Unmapped(&'static str),
}

/// One site with its coverage state.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SiteCoverage {
    pub file: String,
    pub symbol: String,
    pub state: SiteState,
}

impl SiteCoverage {
    /// The site as `file::symbol`, with its state.
    pub(crate) fn describe(&self) -> String {
        let state = match &self.state {
            SiteState::Executed {
                executed,
                functions,
                count,
            } => format!(
                "executed: {executed} of {functions} instrumented functions entered, at most {count} times"
            ),
            SiteState::Zero { functions } => {
                format!("{functions} instrumented functions, none entered")
            }
            SiteState::TypeSite => {
                "a type site with no instrumented function in its item or impl blocks, which holds no code"
                    .to_owned()
            }
            SiteState::Unmapped(reason) => (*reason).to_owned(),
        };
        format!("{}::{} ({state})", self.file, self.symbol)
    }
}

/// Map every algorithm's sites to the functions of `coverage`, by file and line span.
///
/// Item spans are read from the sources below `root`, which must be the sources that were
/// compiled: a file whose digest differs from the digest `coverage` recorded is an error. A
/// function belongs to a site when its lines lie inside the lines of the item the site names,
/// so closures and nested functions belong to the enclosing site. A type site names the type's
/// code: its item, whose lines hold derived-trait expansions, and every inherent or trait
/// `impl` block for the type in the site's file.
pub(crate) fn map_algorithm_sites(
    root: &Path,
    graph: &Graph,
    coverage: &Coverage,
) -> Result<BTreeMap<String, Vec<SiteCoverage>>, Error> {
    let covered = coverage
        .files
        .iter()
        .map(|file| (file.path.as_str(), file))
        .collect::<BTreeMap<_, _>>();
    let mut spans = BTreeMap::<String, BTreeMap<String, Vec<ItemSpan>>>::new();
    let mut result = BTreeMap::new();
    for node in graph.nodes.iter().filter(|node| node.kind == "algorithm") {
        let mut sites = Vec::new();
        let mut seen = BTreeSet::new();
        for site in &node.sites {
            if !seen.insert((&site.file, &site.symbol)) {
                continue;
            }
            if !spans.contains_key(&site.file) {
                let source = fs::read(root.join(&site.file))
                    .map_err(|error| Error::Invalid(format!("{}: {error}", site.file)))?;
                if let Some(file) = covered.get(site.file.as_str()) {
                    let digest = sha256_hex(&source);
                    if digest != file.sha256 {
                        return Err(Error::Invalid(format!(
                            "{}: the source below {} (sha256 {digest}) differs from the covered build (sha256 {}); join from a checkout at the receipt's commit",
                            site.file,
                            root.display(),
                            file.sha256
                        )));
                    }
                }
                let text = String::from_utf8_lossy(&source);
                let items = item_spans(&text)
                    .map_err(|error| Error::Invalid(format!("{}: {error}", site.file)))?;
                spans.insert(site.file.clone(), items);
            }
            let file_items = &spans[&site.file];
            let items = file_items.get(&site.symbol);
            let impls = file_items.get(&format!("impl {}", site.symbol));
            let functions = covered
                .get(site.file.as_str())
                .map(|file| file.functions.as_slice())
                .unwrap_or_default();
            sites.push(SiteCoverage {
                file: site.file.clone(),
                symbol: site.symbol.clone(),
                state: site_state(
                    items.map(Vec::as_slice),
                    impls.map(Vec::as_slice).unwrap_or_default(),
                    functions,
                ),
            });
        }
        result.insert(node.id.clone(), sites);
    }
    Ok(result)
}

/// The coverage state of one site from the spans of the items it names, the `impl` blocks for
/// it when it names a type, and the instrumented functions of its file.
pub(crate) fn site_state(
    items: Option<&[ItemSpan]>,
    impls: &[ItemSpan],
    functions: &[CoveredFunction],
) -> SiteState {
    let Some(items) = items.filter(|items| !items.is_empty()) else {
        return SiteState::Unmapped("the site names no item in the source");
    };
    let code = items.iter().filter(|item| item.code).collect::<Vec<_>>();
    let is_type = code.is_empty();
    let ranges = if is_type {
        items.iter().chain(impls).collect::<Vec<_>>()
    } else {
        code
    };
    let inside = functions
        .iter()
        .filter(|function| {
            ranges
                .iter()
                .any(|item| item.start <= function.start && function.end <= item.end)
        })
        .collect::<Vec<_>>();
    if inside.is_empty() {
        return if is_type {
            SiteState::TypeSite
        } else {
            SiteState::Unmapped(
                "no instrumented function lies in the item: its code is removed by cfg or not compiled into the binary",
            )
        };
    }
    let executed = inside.iter().filter(|function| function.count > 0).count();
    if executed == 0 {
        SiteState::Zero {
            functions: inside.len(),
        }
    } else {
        SiteState::Executed {
            executed,
            functions: inside.len(),
            count: inside
                .iter()
                .map(|function| function.count)
                .max()
                .unwrap_or(0),
        }
    }
}

/// `crates/<crate>/src/**.rs`.
pub(crate) fn is_workspace_source(relative: &str) -> bool {
    let parts = relative.split('/').collect::<Vec<_>>();
    parts.len() >= 4
        && parts[0] == "crates"
        && parts[2] == "src"
        && relative.ends_with(".rs")
        && parts.iter().all(|part| !part.is_empty() && *part != "..")
}

fn slash_path(path: &Path) -> String {
    path.components()
        .map(|component| component.as_os_str().to_string_lossy())
        .collect::<Vec<_>>()
        .join("/")
}

fn sha256_file(path: &Path) -> Result<String, Error> {
    Ok(sha256_hex(&fs::read(path).map_err(|error| {
        Error::Invalid(format!("{}: {error}", path.display()))
    })?))
}

fn sha256_hex(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

/// The demangled symbol without crate hashes and without generic argument lists, so the
/// instantiations of one generic function share a name. `<impl ..>` segments are kept.
fn demangle(symbol: &str) -> String {
    strip_generic_arguments(&format!("{:#}", rustc_demangle::demangle(symbol)))
}

/// Remove every `::<..>` group whose contents do not begin with `impl `.
fn strip_generic_arguments(name: &str) -> String {
    let bytes = name.as_bytes();
    let mut output = String::with_capacity(name.len());
    let mut index = 0;
    while index < bytes.len() {
        if name[index..].starts_with("::<") && !name[index + 3..].starts_with("impl ") {
            let mut depth = 0usize;
            let mut end = index + 2;
            while end < bytes.len() {
                match bytes[end] {
                    b'<' => depth += 1,
                    b'>' if end > 0 && bytes[end - 1] == b'-' => {}
                    b'>' => {
                        depth -= 1;
                        if depth == 0 {
                            break;
                        }
                    }
                    _ => {}
                }
                end += 1;
            }
            index = end + 1;
            continue;
        }
        let character = name[index..].chars().next().unwrap_or_default();
        output.push(character);
        index += character.len_utf8();
    }
    output
}

#[cfg(test)]
mod tests {
    use super::*;

    fn function(start: usize, end: usize, count: u64) -> CoveredFunction {
        CoveredFunction {
            start,
            end,
            name: format!("f{start}"),
            count,
        }
    }

    fn code(start: usize, end: usize) -> ItemSpan {
        ItemSpan {
            start,
            end,
            code: true,
        }
    }

    #[test]
    fn strips_generic_arguments_but_keeps_impl_segments() {
        assert_eq!(
            strip_generic_arguments(
                "k_rust_kore::kore::walk::<impl k_rust_kore::kore::ast::Pattern>::find_application::<krust::rpc::locate_application::{closure#0}>"
            ),
            "k_rust_kore::kore::walk::<impl k_rust_kore::kore::ast::Pattern>::find_application"
        );
        assert_eq!(
            strip_generic_arguments("a::b::<fn() -> u8, c::D<e::F>>::g::{closure#1}"),
            "a::b::g::{closure#1}"
        );
        assert_eq!(
            strip_generic_arguments("<a::X<u8> as core::fmt::Display>::fmt"),
            "<a::X<u8> as core::fmt::Display>::fmt"
        );
    }

    #[test]
    fn a_closure_inside_a_site_belongs_to_it() {
        let source = "\
fn site() {
    let add = |x: u8| x + 1;
    add(1);
}

fn other() {}
";
        let spans = item_spans(source).unwrap();
        assert_eq!(spans["site"], [code(1, 4)]);
        // Only the closure ran: the site still executed, because its closure is part of it.
        let functions = [function(1, 4, 0), function(2, 2, 3), function(6, 6, 9)];
        assert_eq!(
            site_state(Some(&spans["site"]), &[], &functions),
            SiteState::Executed {
                executed: 1,
                functions: 2,
                count: 3
            }
        );
        assert_eq!(
            site_state(
                Some(&spans["site"]),
                &[],
                &[function(1, 4, 0), function(2, 2, 0)]
            ),
            SiteState::Zero { functions: 2 }
        );
    }

    #[test]
    fn a_type_site_holds_the_code_of_its_impl_blocks_and_derives() {
        let source = "\
#[derive(Clone)]
struct Matcher {
    pending: Vec<u8>,
}

impl Matcher {
    fn run(&self) {}
}

impl Default for Matcher {
    fn default() -> Self {
        Self { pending: Vec::new() }
    }
}

struct Marker;
";
        let spans = item_spans(source).unwrap();
        assert_eq!(
            spans["Matcher"],
            [ItemSpan {
                start: 1,
                end: 4,
                code: false
            }]
        );
        assert_eq!(spans["impl Matcher"], [code(6, 8), code(10, 14)]);
        assert_eq!(spans["Matcher::run"], [code(7, 7)]);
        let site = |functions: &[CoveredFunction]| {
            site_state(Some(&spans["Matcher"]), &spans["impl Matcher"], functions)
        };
        // A trait impl method executed.
        assert_eq!(
            site(&[function(7, 7, 0), function(11, 13, 2)]),
            SiteState::Executed {
                executed: 1,
                functions: 2,
                count: 2
            }
        );
        // A derived-trait expansion lies in the type's own item.
        assert_eq!(
            site(&[function(1, 1, 4)]),
            SiteState::Executed {
                executed: 1,
                functions: 1,
                count: 4
            }
        );
        assert_eq!(
            site(&[function(7, 7, 0), function(11, 13, 0)]),
            SiteState::Zero { functions: 2 }
        );
        // A type without instrumented code holds no code.
        assert_eq!(site(&[function(20, 20, 1)]), SiteState::TypeSite);
        assert_eq!(
            site_state(Some(&spans["Marker"]), &[], &[function(7, 7, 1)]),
            SiteState::TypeSite
        );
    }

    #[test]
    fn a_function_absent_from_coverage_is_unmapped() {
        let source = "\
#[cfg(feature = \"absent\")]
fn gated() {}

fn present() {}
";
        let spans = item_spans(source).unwrap();
        assert!(matches!(
            site_state(Some(&spans["gated"]), &[], &[function(4, 4, 1)]),
            SiteState::Unmapped(_)
        ));
        assert!(matches!(
            site_state(None, &[], &[function(4, 4, 1)]),
            SiteState::Unmapped(_)
        ));
    }

    #[test]
    fn normalizes_a_synthetic_export() {
        let directory = std::env::temp_dir().join(format!(
            "algo-graph-coverage-{}-{}",
            std::process::id(),
            line!()
        ));
        let source = directory.join("crates/demo/src/lib.rs");
        fs::create_dir_all(source.parent().unwrap()).unwrap();
        fs::write(&source, "fn a() {}\nfn b() {}\n").unwrap();
        let file = source.to_string_lossy().into_owned();
        let export = serde_json::json!({
            "type": "llvm.coverage.json.export",
            "version": "3.1.0",
            "data": [{
                "files": [],
                "functions": [
                    { "name": "_RNvCs1234_4demo1a", "count": 2, "filenames": [file],
                      "regions": [[1, 1, 1, 10, 2, 0, 0, 0]] },
                    { "name": "_RINvCs1234_4demo1bhE", "count": 0, "filenames": [file],
                      "regions": [[2, 1, 2, 10, 0, 0, 0, 0]] },
                    { "name": "_RINvCs1234_4demo1bmE", "count": 5, "filenames": [file],
                      "regions": [[2, 1, 2, 10, 5, 0, 0, 0]] },
                    { "name": "_RNvCs1234_3dep1c", "count": 1,
                      "filenames": ["/elsewhere/.cargo/registry/dep/src/lib.rs"],
                      "regions": [[1, 1, 1, 2, 1, 0, 0, 0]] }
                ]
            }]
        });
        let coverage = normalize_export(&export.to_string(), &directory, None).unwrap();
        fs::remove_dir_all(&directory).unwrap();
        assert_eq!(coverage.files.len(), 1);
        let file = &coverage.files[0];
        assert_eq!(file.path, "crates/demo/src/lib.rs");
        assert_eq!(file.sha256, sha256_hex(b"fn a() {}\nfn b() {}\n"));
        assert_eq!(
            file.functions,
            [
                CoveredFunction {
                    start: 1,
                    end: 1,
                    name: "demo::a".to_owned(),
                    count: 2
                },
                CoveredFunction {
                    start: 2,
                    end: 2,
                    name: "demo::b".to_owned(),
                    count: 5
                },
            ]
        );
        let text = canonical_coverage_toml(&coverage);
        let parsed: Coverage = toml::from_str(&text).unwrap();
        assert_eq!(parsed, coverage);
    }
}
