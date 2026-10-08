//! Filesystem lookup at the pinned k-rust resolver order, with relative identities.

use std::{
    collections::BTreeMap,
    fmt, fs, io,
    path::{Component, Path, PathBuf},
};

use k_rust::{
    builtin,
    kompile::CompilationBackend,
    outer::{LoadOptions, ResolvedSource, SourceResolver, load_for_compilation},
};
use kink_patch::{Baseline, Sha256Digest, sha256};

#[derive(Clone, Debug)]
pub struct CorpusSource {
    pub root: PathBuf,
    pub entry: String,
    pub include_dirs: Vec<String>,
    pub main_module: String,
    pub syntax_module: Option<String>,
    pub md_selector: Option<String>,
}

#[derive(Clone, Debug)]
pub struct LoadedSource {
    pub baseline: Baseline,
    pub files: Vec<SourceFile>,
    // Retain only host-side context here; neither field enters the baseline's identity.
    pub(crate) root: PathBuf,
    pub(crate) syntax_module: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceFile {
    pub name: String,
    pub sha256: Sha256Digest,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LoadError {
    OutsideRoot,
    Io { name: String, detail: String },
    Definition(Box<k_rust::outer::LoadError>),
}

impl fmt::Display for LoadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::OutsideRoot => f.write_str("source path is outside the definition root"),
            Self::Io { name, detail } => write!(f, "{name}: {detail}"),
            Self::Definition(error) => error.fmt(f),
        }
    }
}
impl std::error::Error for LoadError {}

/// Load every source under `root`, recording exactly the non-builtin bytes read.
pub fn load_source(source: &CorpusSource) -> Result<LoadedSource, LoadError> {
    let root = fs::canonicalize(&source.root).map_err(|e| io_error("root", e))?;
    let include_dirs = source
        .include_dirs
        .iter()
        .map(|name| {
            relative_path(name)?;
            if let Ok(path) = fs::canonicalize(root.join(name)) {
                path.strip_prefix(&root)
                    .map_err(|_| LoadError::OutsideRoot)?;
            }
            Ok(PathBuf::from(name))
        })
        .collect::<Result<Vec<_>, LoadError>>()?;
    let mut resolver = Resolver {
        root,
        include_dirs,
        files: BTreeMap::new(),
        failure: None,
    };
    relative_path(&source.entry)?;
    let entry = resolver.read(Path::new(&source.entry))?;
    let options = LoadOptions {
        markdown_selector: source.md_selector.clone().unwrap_or_else(|| "k".to_owned()),
        implicit_sources: vec![
            builtin::embedded("kast.md").expect("embedded kast"),
            builtin::embedded("prelude.md").expect("embedded prelude"),
        ],
        excluded_module_attributes: vec![
            CompilationBackend::Rust
                .excluded_module_attribute()
                .to_owned(),
        ],
        // Sources already have relative identities; a concrete project_root is unnecessary.
        ..LoadOptions::default()
    };
    let result = load_for_compilation(
        entry,
        &source.main_module,
        source.syntax_module.as_deref(),
        &mut resolver,
        &options,
    );
    if let Some(error) = resolver.failure {
        return Err(error);
    }
    let (definition, syntax_module) = result.map_err(|e| LoadError::Definition(Box::new(e)))?;
    Ok(LoadedSource {
        baseline: Baseline::new(definition),
        files: resolver
            .files
            .into_iter()
            .map(|(name, sha256)| SourceFile { name, sha256 })
            .collect(),
        root: resolver.root,
        syntax_module,
    })
}

fn io_error(name: &str, error: io::Error) -> LoadError {
    LoadError::Io {
        name: name.to_owned(),
        detail: error.to_string(),
    }
}

/// Normalize relative paths lexically, refusing any traversal above root.
fn relative_path(name: &str) -> Result<PathBuf, LoadError> {
    let mut relative = PathBuf::new();
    for component in Path::new(name).components() {
        match component {
            Component::Normal(part) => relative.push(part),
            Component::CurDir => {}
            Component::ParentDir if relative.pop() => {}
            _ => return Err(LoadError::OutsideRoot),
        }
    }
    Ok(relative)
}

pub(crate) fn read_under_root(root: &Path, name: &str) -> Result<(String, Vec<u8>), LoadError> {
    relative_path(name)?;
    let path = fs::canonicalize(root.join(name)).map_err(|e| io_error(name, e))?;
    let relative = path
        .strip_prefix(root)
        .map_err(|_| LoadError::OutsideRoot)?;
    let logical = relative
        .to_str()
        .ok_or_else(|| LoadError::Io {
            name: name.to_owned(),
            detail: "non-UTF-8 source name".to_owned(),
        })?
        .replace('\\', "/");
    let bytes = fs::read(path).map_err(|e| io_error(&logical, e))?;
    Ok((logical, bytes))
}

struct Resolver {
    root: PathBuf,
    include_dirs: Vec<PathBuf>,
    files: BTreeMap<String, Sha256Digest>,
    failure: Option<LoadError>,
}

impl Resolver {
    fn read(&mut self, relative: &Path) -> Result<ResolvedSource, LoadError> {
        let name = relative.to_str().ok_or_else(|| LoadError::Io {
            name: "source".to_owned(),
            detail: "non-UTF-8 source name".to_owned(),
        })?;
        let (name, bytes) = read_under_root(&self.root, name)?;
        let digest = sha256(&bytes);
        let text = String::from_utf8(bytes).map_err(|e| LoadError::Io {
            name: name.clone(),
            detail: e.to_string(),
        })?;
        self.files.insert(name.clone(), digest);
        Ok(ResolvedSource::new(name, text))
    }

    fn lookup(&mut self, requiring: &str, required: &str) -> Result<ResolvedSource, LoadError> {
        // native.rs:420-445: include candidates, builtin, then insert the requiring
        // directory at index min(1, len). With no includes, builtin is first.
        if Path::new(required).is_absolute() {
            return Err(LoadError::OutsideRoot);
        }
        let mut candidates = self
            .include_dirs
            .iter()
            .map(|dir| Some(dir.join(required)))
            .collect::<Vec<_>>();
        candidates.push(None);
        if !requiring.starts_with("krust-builtin://")
            && let Some(parent) = Path::new(requiring).parent()
        {
            candidates.insert(1.min(candidates.len()), Some(parent.join(required)));
        }
        let mut missing_outside = false;
        for candidate in candidates {
            match candidate {
                Some(path) => {
                    // native skips missing lookup probes before considering later
                    // candidates. A nested ../require may miss in an include
                    // directory yet resolve within root beside its requiring file.
                    match fs::canonicalize(self.root.join(&path)) {
                        Err(error) if error.kind() == io::ErrorKind::NotFound => {
                            missing_outside |=
                                relative_path(path.to_str().ok_or(LoadError::OutsideRoot)?)
                                    .is_err();
                            continue;
                        }
                        Err(error) => return Err(io_error(required, error)),
                        Ok(canonical) if !canonical.starts_with(&self.root) => {
                            return Err(LoadError::OutsideRoot);
                        }
                        Ok(_) => return self.read(&path),
                    }
                }
                None => {
                    if let Some(source) = builtin::embedded(required) {
                        return Ok(source);
                    }
                }
            }
        }
        if missing_outside {
            return Err(LoadError::OutsideRoot);
        }
        Err(LoadError::Io {
            name: required.to_owned(),
            detail: format!("not found from {requiring}"),
        })
    }
}

impl SourceResolver for Resolver {
    fn resolve(&mut self, requiring: &str, required: &str) -> Result<ResolvedSource, String> {
        self.lookup(requiring, required).map_err(|error| {
            let text = error.to_string();
            self.failure = Some(error);
            text
        })
    }
}
