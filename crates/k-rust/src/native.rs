//! Native host adapters kept out of the portable frontend build.

use std::{
    collections::BTreeSet,
    fs, io,
    path::{Path, PathBuf},
};

use crate::{
    builtin::embedded,
    outer::{ResolvedSource, SourceResolver, normalize_virtual_path},
};

/// Filesystem-backed resolution for entry files and recursive `requires`.
///
/// Relative requirements follow K's `ParserUtils.slurp` order: the first lookup directory, the requiring file's directory, the remaining lookup directories, and finally the configured or embedded builtin source.
/// With no lookup directory, the builtin source therefore precedes the requiring file's directory.
#[derive(Clone, Debug)]
pub struct FileResolver {
    builtin_directory: Option<PathBuf>,
    project_root: Option<PathBuf>,
    working_directory: PathBuf,
    lookup_directories: Vec<PathBuf>,
    prepared_sources: BTreeSet<String>,
}

impl FileResolver {
    pub fn new(
        working_directory: impl Into<PathBuf>,
        lookup_directories: impl IntoIterator<Item = PathBuf>,
    ) -> Self {
        let working_directory = working_directory.into();
        let lookup_directories = lookup_directories
            .into_iter()
            .map(|directory| {
                if directory.is_absolute() {
                    directory
                } else {
                    working_directory.join(directory)
                }
            })
            .collect();
        Self {
            builtin_directory: None,
            project_root: None,
            working_directory,
            lookup_directories,
            prepared_sources: BTreeSet::new(),
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
        let directory = directory.into();
        self.builtin_directory = Some(if directory.is_absolute() {
            directory
        } else {
            self.working_directory.join(directory)
        });
        self
    }

    pub fn with_project_root(mut self, directory: impl Into<PathBuf>) -> Self {
        self.project_root = Some(directory.into());
        self
    }

    /// Satisfy these canonical source identities without reopening their source text.
    pub fn with_prepared_sources(mut self, sources: impl IntoIterator<Item = String>) -> Self {
        self.prepared_sources = sources.into_iter().collect();
        self
    }

    fn read(&self, path: &Path) -> io::Result<ResolvedSource> {
        let canonical = fs::canonicalize(path)?;
        let text = fs::read_to_string(&canonical)?;
        let source = ResolvedSource::new(canonical.to_string_lossy(), text);
        Ok(if let Some(root) = &self.project_root {
            canonical
                .strip_prefix(root)
                .ok()
                .map(|relative| {
                    source
                        .clone()
                        .with_logical(relative.to_string_lossy().replace('\\', "/"))
                })
                .unwrap_or(source)
        } else {
            source
        })
    }

    fn candidates(&self, requiring_source: &str, required: &str) -> Vec<Candidate> {
        let required = Path::new(required);
        if required.is_absolute() {
            return vec![Candidate::Path(required.to_owned())];
        }

        let mut candidates = self
            .lookup_directories
            .iter()
            .map(|directory| Candidate::Path(directory.join(required)))
            .collect::<Vec<_>>();
        candidates.push(match &self.builtin_directory {
            Some(directory) => Candidate::Path(directory.join(required)),
            None => Candidate::Embedded,
        });
        let requiring_directory = (!requiring_source.starts_with("krust-builtin://"))
            .then(|| Path::new(requiring_source).parent())
            .flatten()
            .filter(|parent| !parent.as_os_str().is_empty());
        if let Some(directory) = requiring_directory {
            candidates.insert(
                1.min(candidates.len()),
                Candidate::Path(directory.join(required)),
            );
        }
        candidates
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Candidate {
    Path(PathBuf),
    Embedded,
}

impl SourceResolver for FileResolver {
    fn resolve(
        &mut self,
        requiring_source: &str,
        required: &str,
    ) -> Result<ResolvedSource, String> {
        let candidates = self.candidates(requiring_source, required);
        for candidate in &candidates {
            match candidate {
                Candidate::Path(path) => {
                    let identity = fs::canonicalize(path)
                        .map(|path| path.to_string_lossy().into_owned())
                        .unwrap_or_else(|_| normalize_virtual_path(&self.working_directory.join(path)));
                    if self.prepared_sources.contains(&identity) {
                        return Ok(ResolvedSource::new(identity, ""));
                    }
                    match self.read(path) {
                    Ok(source) => return Ok(source),
                    Err(error) if error.kind() == io::ErrorKind::NotFound => {}
                    Err(error) => {
                        return Err(format!("could not read {}: {error}", path.display()));
                    }
                    }
                }
                Candidate::Embedded => {
                    if let Some(source) = embedded(required) {
                        if self.prepared_sources.contains(&source.source) {
                            return Ok(ResolvedSource::new(source.source, ""));
                        }
                        return Ok(source);
                    }
                }
            }
        }
        Err(format!(
            "not found; searched {}",
            candidates
                .iter()
                .map(|candidate| match candidate {
                    Candidate::Path(path) => path.display().to_string(),
                    Candidate::Embedded => format!("krust-builtin://{required}"),
                })
                .collect::<Vec<_>>()
                .join(", ")
        ))
    }
}

#[cfg(test)]
mod tests {
    use std::{
        sync::atomic::{AtomicU64, Ordering},
        time::{SystemTime, UNIX_EPOCH},
    };

    use super::*;

    struct ResolverFixture(PathBuf);

    impl ResolverFixture {
        fn new() -> Self {
            static NEXT: AtomicU64 = AtomicU64::new(0);
            let nonce = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos();
            let sequence = NEXT.fetch_add(1, Ordering::Relaxed);
            let root = std::env::temp_dir().join(format!(
                "k-rust-resolver-{}-{nonce}-{sequence}",
                std::process::id()
            ));
            fs::create_dir_all(&root).unwrap();
            Self(root)
        }

        fn directory(&self, relative: &str) -> PathBuf {
            let directory = self.0.join(relative);
            fs::create_dir_all(&directory).unwrap();
            directory
        }

        fn write(&self, relative: &str, text: &str) -> PathBuf {
            let path = self.0.join(relative);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(&path, text).unwrap();
            path
        }
    }

    impl Drop for ResolverFixture {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }

    #[test]
    fn requires_order_matches_parser_utils_slurp() {
        let fixture = ResolverFixture::new();
        let local = fixture.directory("definition");
        let first = fixture.directory("include-first");
        let second = fixture.directory("include-second");
        let builtin = fixture.directory("builtin");
        let requiring = fixture.write("definition/main.k", "module MAIN endmodule");

        fixture.write("include-first/first.k", "first include");
        fixture.write("definition/first.k", "local");
        fixture.write("include-second/first.k", "second include");
        fixture.write("definition/local.k", "local");
        fixture.write("include-second/local.k", "second include");
        fixture.write("include-second/second.k", "second include");
        fixture.write("definition/json.md", "local json");

        let mut resolver = FileResolver::new(&fixture.0, [first, second]);
        assert_eq!(
            resolver
                .resolve(&requiring.to_string_lossy(), "first.k")
                .unwrap()
                .text,
            "first include"
        );
        assert_eq!(
            resolver
                .resolve(&requiring.to_string_lossy(), "local.k")
                .unwrap()
                .text,
            "local"
        );
        assert_eq!(
            resolver
                .resolve(&requiring.to_string_lossy(), "second.k")
                .unwrap()
                .text,
            "second include"
        );
        assert_eq!(
            resolver
                .resolve(&requiring.to_string_lossy(), "json.md")
                .unwrap()
                .text,
            "local json",
            "the requiring directory follows the first -I directory and precedes the builtin"
        );

        let mut no_includes = FileResolver::new(&fixture.0, []);
        assert_eq!(
            no_includes
                .resolve(&requiring.to_string_lossy(), "json.md")
                .unwrap()
                .source,
            "krust-builtin://json.md",
            "the builtin precedes the requiring directory when there is no -I directory"
        );
        assert_eq!(
            no_includes
                .resolve(
                    &fixture.0.join("arbitrary/main.k").to_string_lossy(),
                    "domains.md",
                )
                .unwrap()
                .source,
            "krust-builtin://domains.md"
        );

        fixture.write("builtin/json.md", "configured builtin");
        let mut configured = FileResolver::new(&fixture.0, []).with_builtin_directory(&builtin);
        assert_eq!(
            configured
                .resolve(&requiring.to_string_lossy(), "json.md")
                .unwrap()
                .text,
            "configured builtin"
        );
        assert!(
            configured
                .resolve(&requiring.to_string_lossy(), "domains.md")
                .is_err(),
            "a configured builtin directory disables the embedded fallback"
        );

        let absolute = fixture.write("absolute.k", "absolute");
        assert_eq!(
            resolver
                .resolve(&requiring.to_string_lossy(), &absolute.to_string_lossy(),)
                .unwrap()
                .text,
            "absolute"
        );

        fixture.write("cwd-only.k", "working directory");
        assert!(
            no_includes
                .resolve(&local.join("main.k").to_string_lossy(), "cwd-only.k")
                .is_err(),
            "the working directory is not an implicit requires candidate"
        );
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

    #[test]
    fn resolves_deleted_prepared_sources_by_identity() {
        let root = fs::canonicalize(std::env::temp_dir()).unwrap();
        let path = root.join("deleted-prepared-semantics.k");
        let identity = path.to_string_lossy().into_owned();
        let mut resolver = FileResolver::new(&root, []).with_prepared_sources([identity.clone()]);
        let source = resolver
            .resolve(
                &root.join("spec.k").to_string_lossy(),
                "deleted-prepared-semantics.k",
            )
            .unwrap();
        assert_eq!(source.source, identity);
        assert!(source.text.is_empty());
    }

    #[test]
    fn prepared_sources_do_not_shadow_an_unrelated_same_named_file() {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root = std::env::temp_dir().join(format!("k-rust-prepared-resolver-{nonce}"));
        fs::create_dir_all(&root).unwrap();
        let root = fs::canonicalize(root).unwrap();
        let local = root.join("shared.k");
        fs::write(&local, "new local source").unwrap();
        let mut resolver =
            FileResolver::new(&root, [root.join("first"), root.join("prepared")]).with_prepared_sources([root
                .join("prepared/shared.k")
                .to_string_lossy()
                .into_owned()]);
        let source = resolver
            .resolve(&root.join("spec.k").to_string_lossy(), "shared.k")
            .unwrap();
        assert_eq!(source.source, local.to_string_lossy());
        assert_eq!(source.text, "new local source");
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn resolves_deleted_prepared_sources_through_relative_include_directories() {
        let root = fs::canonicalize(std::env::temp_dir()).unwrap();
        let identity = root
            .join("prepared-semantics/semantics.k")
            .to_string_lossy()
            .into_owned();
        let mut resolver = FileResolver::new(&root, [PathBuf::from("prepared-semantics")])
            .with_prepared_sources([identity.clone()]);
        let source = resolver
            .resolve(&root.join("spec.k").to_string_lossy(), "semantics.k")
            .unwrap();
        assert_eq!(source.source, identity);
        assert!(source.text.is_empty());
    }

    #[test]
    fn reference_local_builtin_name_is_reserved() {
        // reference: kompile test.k --backend haskell --main-module LOCAL-SHADOWS-BUILTIN
        let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/reference/outer/local-shadows-builtin");
        let reference =
            include_str!("../tests/fixtures/reference/outer/local-shadows-builtin/diagnostic.txt");
        assert!(reference.contains("Could not find module: JSON-LOCAL"));

        let mut resolver = FileResolver::new(&fixture, []);
        let entry = resolver.load_entry(fixture.join("test.k")).unwrap();
        let prelude = resolver.resolve(&entry.source, "prelude.md").unwrap();
        let error = crate::outer::load_with_options(
            entry,
            "LOCAL-SHADOWS-BUILTIN",
            &mut resolver,
            &crate::outer::LoadOptions {
                implicit_sources: vec![prelude],
                ..crate::outer::LoadOptions::default()
            },
        )
        .unwrap_err();

        assert_eq!(
            error,
            crate::outer::LoadError::DefinitionResolution(
                crate::definition::ResolveError::MissingImport {
                    module: "LOCAL-SHADOWS-BUILTIN".into(),
                    import: "JSON-LOCAL".into(),
                }
            )
        );
    }
}
