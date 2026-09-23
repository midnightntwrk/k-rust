//! ```toml algorithm-site
//! id = "definition.json.encode"
//! role = "part"
//! sites = ["write_runnable_artifact"]
//! ```
//!
//! Native host adapters kept out of the portable frontend build.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs, io,
    path::{Path, PathBuf},
};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{
    builtin::embedded,
    definition::{AttributeKey, Definition, Sentence, json as definition_json},
    kast::Sort,
    outer::{ResolvedSource, SourceResolver, normalize_virtual_path},
    provenance::SourceTable,
};

/// File published last to make a compiled directory runnable.
pub const RUNTIME_MANIFEST: &str = "runtime.json";
const RUNTIME_FORMAT: &str = "krust-runnable-definition";
const RUNTIME_VERSION: u32 = 1;
const FRONTEND_PAYLOAD: &str = "frontend.json";
const EXECUTION_PAYLOAD: &str = "execution.json";
const KORE_PAYLOAD: &str = "definition.kore";
const RECOMPILE_REMEDY: &str = "run `krust kcompile` again to create a fresh runnable artifact";

#[derive(Clone, Debug)]
pub struct RunnableArtifact {
    pub main_module: String,
    pub syntax_module: String,
    pub frontend_definition: Definition,
    pub source_table: SourceTable,
    pub execution: ExecutionPayload,
    pub configuration_variables: BTreeMap<String, Sort>,
    pub execution_rewrite_order: Vec<String>,
    pub definition_kore: String,
}

/// The execution definition of a runnable artifact, as its digest-checked payload.
///
/// Execution runs from `definition.kore`; the execution definition is read only to compile a
/// search pattern, so it is decoded by the command that needs it rather than on every load.
/// Skipping the decode loses no load-time check of the artifact's compatibility: the payload's
/// digest is still verified at load, and `frontend.json`, which is always decoded, is written in
/// the same provenance format and version by the same `kcompile`, so an artifact from an
/// incompatible writer is still rejected at load.
#[derive(Clone, Debug)]
pub struct ExecutionPayload {
    file: String,
    bytes: Vec<u8>,
}

impl ExecutionPayload {
    /// Decode the execution definition.
    pub fn decode(&self) -> Result<Definition, Box<dyn std::error::Error>> {
        let text = std::str::from_utf8(&self.bytes)
            .map_err(|error| corrupt_payload_error(&self.file, error, RECOMPILE_REMEDY))?;
        Ok(definition_json::from_provenance_str(text)
            .map_err(|error| corrupt_payload_error(&self.file, error, RECOMPILE_REMEDY))?
            .definition)
    }
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct RuntimeManifest {
    format: String,
    version: u32,
    backend: String,
    main_module: String,
    syntax_module: String,
    frontend: PayloadIdentity,
    execution: PayloadIdentity,
    definition_kore: PayloadIdentity,
    configuration_variables: BTreeMap<String, String>,
    execution_rewrite_order: Vec<String>,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct PayloadIdentity {
    file: String,
    sha256: String,
}

/// Remove the publication marker before changing any file in a compiled directory.
pub fn unpublish_runnable_artifact(directory: &Path) -> io::Result<()> {
    match fs::remove_file(directory.join(RUNTIME_MANIFEST)) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(error),
    }
}

/// Write the runtime payloads atomically and publish their manifest last.
#[allow(clippy::too_many_arguments)]
pub fn write_runnable_artifact(
    directory: &Path,
    main_module: &str,
    syntax_module: &str,
    frontend_definition: &Definition,
    source_table: &SourceTable,
    execution_definition: &Definition,
    configuration_variables: &BTreeMap<String, Sort>,
    execution_rewrite_order: &[String],
    definition_kore: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    unpublish_runnable_artifact(directory)?;
    // Execution consumes semantic rules from definition.kore. The transformed definition serves
    // only command-line pattern compilation, whose catalogs need syntax sentences and macro-like
    // rules. Removing the other generated sentences avoids serializing the large compiled rule set
    // a second time. The source frontend keeps ordinary rules because macro attributes can be
    // propagated from their head productions when a concrete program is expanded.
    let mut runtime_frontend = frontend_definition.clone();
    for module in &mut runtime_frontend.modules {
        // Context aliases have already affected the transformed execution definition and KORE.
        // External KAST v4 represents them as an undecodable KBadsentence, and the runtime parser
        // does not consume them.
        module
            .local_sentences
            .retain(|sentence| !matches!(&**sentence, Sentence::ContextAlias { .. }));
    }
    let mut runtime_execution = execution_definition.clone();
    retain_pattern_sentences(&mut runtime_execution);
    let frontend = definition_json::to_provenance_string(&runtime_frontend, source_table)?;
    let execution = definition_json::to_provenance_string(&runtime_execution, source_table)?;
    let payloads = [
        (FRONTEND_PAYLOAD, frontend.as_bytes()),
        (EXECUTION_PAYLOAD, execution.as_bytes()),
        (KORE_PAYLOAD, definition_kore.as_bytes()),
    ];
    for (name, bytes) in payloads {
        write_atomic(&directory.join(name), bytes)?;
    }
    let manifest = RuntimeManifest {
        format: RUNTIME_FORMAT.into(),
        version: RUNTIME_VERSION,
        backend: "rust".into(),
        main_module: main_module.into(),
        syntax_module: syntax_module.into(),
        frontend: payload_identity(FRONTEND_PAYLOAD, frontend.as_bytes()),
        execution: payload_identity(EXECUTION_PAYLOAD, execution.as_bytes()),
        definition_kore: payload_identity(KORE_PAYLOAD, definition_kore.as_bytes()),
        configuration_variables: configuration_variables
            .iter()
            .map(|(name, sort)| (name.clone(), sort.to_string()))
            .collect(),
        execution_rewrite_order: execution_rewrite_order.to_vec(),
    };
    let manifest = serde_json::to_vec_pretty(&manifest)?;
    write_atomic(&directory.join(RUNTIME_MANIFEST), &manifest)?;
    Ok(())
}

fn retain_pattern_sentences(definition: &mut Definition) {
    for module in &mut definition.modules {
        module.local_sentences.retain(|sentence| {
            matches!(
                &**sentence,
                Sentence::SyntaxSort { .. }
                    | Sentence::SortSynonym { .. }
                    | Sentence::SyntaxLexical { .. }
                    | Sentence::Production { .. }
                    | Sentence::SyntaxAssociativity { .. }
                    | Sentence::SyntaxPriority { .. }
            ) || matches!(
                &**sentence,
                Sentence::Rule { attributes, .. }
                    if attributes.has_any(&AttributeKey::MACRO_LIKE)
            )
        });
    }
}

/// Load and validate a runnable compiled directory without consulting source files.
pub fn load_runnable_artifact(
    directory: &Path,
) -> Result<RunnableArtifact, Box<dyn std::error::Error>> {
    let remedy = RECOMPILE_REMEDY;
    let manifest_path = directory.join(RUNTIME_MANIFEST);
    let bytes = fs::read(&manifest_path).map_err(|error| {
        io::Error::new(
            error.kind(),
            format!(
                "runnable artifact manifest `{}` is missing or unreadable: {error}; {remedy}",
                manifest_path.display()
            ),
        )
    })?;
    let manifest: RuntimeManifest = serde_json::from_slice(&bytes).map_err(|error| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "runnable artifact manifest `{}` is corrupt: {error}; {remedy}",
                manifest_path.display()
            ),
        )
    })?;
    if manifest.format != RUNTIME_FORMAT {
        return Err(format!(
            "unsupported runnable artifact format {:?}; {remedy}",
            manifest.format
        )
        .into());
    }
    if manifest.version != RUNTIME_VERSION {
        return Err(format!(
            "unsupported runnable artifact version {}; this krust accepts version {RUNTIME_VERSION}; {remedy}",
            manifest.version
        )
        .into());
    }
    if manifest.backend != "rust" {
        return Err(format!(
            "runnable artifact backend {:?} is not executable by the Rust backend; {remedy}",
            manifest.backend
        )
        .into());
    }
    let frontend = read_validated_payload(directory, &manifest.frontend, remedy)?;
    let execution = read_validated_payload(directory, &manifest.execution, remedy)?;
    let definition_kore = read_validated_payload(directory, &manifest.definition_kore, remedy)?;
    let frontend = std::str::from_utf8(&frontend)
        .map_err(|error| corrupt_payload_error(&manifest.frontend.file, error, remedy))?;
    let frontend = definition_json::from_provenance_str(frontend)
        .map_err(|error| corrupt_payload_error(&manifest.frontend.file, error, remedy))?;
    let configuration_variables = manifest
        .configuration_variables
        .into_iter()
        .map(|(name, sort)| {
            crate::kast::parser::parse_sort(&sort)
                .map(|sort| (name.clone(), sort))
                .map_err(|error| {
                    corrupt_payload_error(
                        RUNTIME_MANIFEST,
                        format!("invalid sort for configuration variable `{name}`: {error}"),
                        remedy,
                    )
                })
        })
        .collect::<Result<_, _>>()?;
    Ok(RunnableArtifact {
        main_module: manifest.main_module,
        syntax_module: manifest.syntax_module,
        frontend_definition: frontend.definition,
        source_table: frontend.source_table,
        execution: ExecutionPayload {
            file: manifest.execution.file,
            bytes: execution,
        },
        configuration_variables,
        execution_rewrite_order: manifest.execution_rewrite_order,
        definition_kore: String::from_utf8(definition_kore).map_err(|error| {
            corrupt_payload_error(&manifest.definition_kore.file, error, remedy)
        })?,
    })
}

fn payload_identity(file: &str, bytes: &[u8]) -> PayloadIdentity {
    PayloadIdentity {
        file: file.into(),
        sha256: sha256(bytes),
    }
}

fn read_validated_payload(
    directory: &Path,
    identity: &PayloadIdentity,
    remedy: &str,
) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    if identity.file.contains('/')
        || identity.file.contains('\\')
        || matches!(identity.file.as_str(), "." | "..")
    {
        return Err(format!(
            "invalid runnable artifact payload name {:?}; {remedy}",
            identity.file
        )
        .into());
    }
    let path = directory.join(&identity.file);
    let bytes = fs::read(&path).map_err(|error| {
        io::Error::new(
            error.kind(),
            format!(
                "runnable artifact payload `{}` is missing or unreadable: {error}; {remedy}",
                path.display()
            ),
        )
    })?;
    let actual = sha256(&bytes);
    if actual != identity.sha256 {
        return Err(format!(
            "runnable artifact payload `{}` failed SHA-256 validation; {remedy}",
            path.display()
        )
        .into());
    }
    Ok(bytes)
}

fn corrupt_payload_error(file: &str, error: impl std::fmt::Display, remedy: &str) -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        format!("runnable artifact payload `{file}` is corrupt: {error}; {remedy}"),
    )
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn write_atomic(path: &Path, bytes: &[u8]) -> io::Result<()> {
    let temporary = path.with_extension(format!("tmp-{}", std::process::id()));
    fs::write(&temporary, bytes)?;
    fs::rename(temporary, path)
}

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

    /// Recognize these canonical source identities as members of a prepared definition.
    /// Existing files are still read so the loader can validate declarations under its current
    /// Markdown selector; a missing prepared source is represented by empty text and remains
    /// satisfiable from the prepared definition.
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
                    if !self.prepared_sources.is_empty() {
                        let identity = fs::canonicalize(path)
                            .map(|path| path.to_string_lossy().into_owned())
                            .unwrap_or_else(|_| {
                                normalize_virtual_path(&self.working_directory.join(path))
                            });
                        if self.prepared_sources.contains(&identity) {
                            return match self.read(path) {
                                Ok(source) => Ok(source),
                                Err(error) if error.kind() == io::ErrorKind::NotFound => {
                                    Ok(ResolvedSource::new(identity, ""))
                                }
                                Err(error) => {
                                    Err(format!("could not read {}: {error}", path.display()))
                                }
                            };
                        }
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
        let mut resolver = FileResolver::new(&root, [root.join("first"), root.join("prepared")])
            .with_prepared_sources([root
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
    fn prepared_first_include_keeps_priority_over_a_local_file() {
        let fixture = ResolverFixture::new();
        let local = fixture.write("shared.k", "local source");
        let prepared = fixture
            .0
            .join("prepared/shared.k")
            .to_string_lossy()
            .into_owned();
        let mut resolver = FileResolver::new(&fixture.0, [fixture.0.join("prepared")])
            .with_prepared_sources([prepared.clone()]);
        let source = resolver
            .resolve(&local.to_string_lossy(), "shared.k")
            .unwrap();
        assert_eq!(source.source, prepared);
        assert!(source.text.is_empty());
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
