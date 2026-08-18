//! Native host adapters kept out of the portable frontend build.

use std::{
    fs, io,
    path::{Path, PathBuf},
};

use crate::{
    builtin::{embedded, source_name},
    outer::{ResolvedSource, SourceResolver},
};

/// Filesystem-backed resolution for entry files and recursive `requires`.
#[derive(Clone, Debug)]
pub struct FileResolver {
    builtin_directory: Option<PathBuf>,
    working_directory: PathBuf,
    lookup_directories: Vec<PathBuf>,
}

impl FileResolver {
    pub fn new(
        working_directory: impl Into<PathBuf>,
        lookup_directories: impl IntoIterator<Item = PathBuf>,
    ) -> Self {
        Self {
            builtin_directory: None,
            working_directory: working_directory.into(),
            lookup_directories: lookup_directories.into_iter().collect(),
        }
    }

    pub fn from_current_directory(
        lookup_directories: impl IntoIterator<Item = PathBuf>,
    ) -> io::Result<Self> {
        Ok(Self::new(std::env::current_dir()?, lookup_directories))
    }

    pub fn load_entry(&self, path: impl AsRef<Path>) -> io::Result<ResolvedSource> {
        self.read(path.as_ref())
    }

    pub fn with_builtin_directory(mut self, directory: impl Into<PathBuf>) -> Self {
        self.builtin_directory = Some(directory.into());
        self
    }

    fn read(&self, path: &Path) -> io::Result<ResolvedSource> {
        let canonical = fs::canonicalize(path)?;
        let text = fs::read_to_string(&canonical)?;
        Ok(ResolvedSource::new(canonical.to_string_lossy(), text))
    }

    fn candidates(&self, requiring_source: &str, required: &str) -> Vec<PathBuf> {
        let required = PathBuf::from(source_name(required));
        let required = required.as_path();
        if required.is_absolute() {
            return vec![required.to_owned()];
        }

        let mut candidates = Vec::new();
        if let Some(directory) = &self.builtin_directory {
            candidates.push(directory.join(required));
        }
        if let Some(parent) = Path::new(requiring_source).parent() {
            candidates.push(parent.join(required));
        }
        candidates.push(self.working_directory.join(required));
        candidates.extend(
            self.lookup_directories
                .iter()
                .map(|directory| directory.join(required)),
        );
        candidates.dedup();
        candidates
    }
}

impl SourceResolver for FileResolver {
    fn resolve(
        &mut self,
        requiring_source: &str,
        required: &str,
    ) -> Result<ResolvedSource, String> {
        let candidates = self.candidates(requiring_source, required);
        for candidate in &candidates {
            match self.read(candidate) {
                Ok(source) => return Ok(source),
                Err(error) if error.kind() == io::ErrorKind::NotFound => {}
                Err(error) => {
                    return Err(format!("could not read {}: {error}", candidate.display()));
                }
            }
        }
        if let Some(source) = embedded(required) {
            return Ok(source);
        }
        Err(format!(
            "not found; searched {}",
            candidates
                .iter()
                .map(|path| path.display().to_string())
                .collect::<Vec<_>>()
                .join(", ")
        ))
    }
}

#[cfg(test)]
mod tests {
    use std::time::{SystemTime, UNIX_EPOCH};

    use super::*;

    #[test]
    fn resolves_relative_requires_before_lookup_directories() {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root = std::env::temp_dir().join(format!("k-rust-resolver-{nonce}"));
        let local = root.join("local");
        let lookup = root.join("lookup");
        fs::create_dir_all(&local).unwrap();
        fs::create_dir_all(&lookup).unwrap();
        fs::write(local.join("shared.k"), "local").unwrap();
        fs::write(lookup.join("shared.k"), "lookup").unwrap();

        let mut resolver = FileResolver::new(&root, [lookup]);
        let source = resolver
            .resolve(&local.join("main.k").to_string_lossy(), "shared.k")
            .unwrap();

        assert_eq!(source.text, "local");
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn falls_back_to_the_embedded_pinned_builtins() {
        let mut resolver = FileResolver::new(std::env::temp_dir(), []);
        let prelude = resolver
            .resolve("missing-definition.k", "prelude.md")
            .unwrap();
        let legacy_domains = resolver.resolve(&prelude.source, "domains.k").unwrap();

        assert_eq!(prelude.source, "krust-builtin://prelude.md");
        assert!(prelude.text.contains("requires \"kast.md\""));
        assert_eq!(legacy_domains.source, "krust-builtin://domains.md");
        assert!(legacy_domains.text.contains("module DOMAINS"));
    }
}
