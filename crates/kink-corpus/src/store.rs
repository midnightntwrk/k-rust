//! Atomic store writes and content-addressed corpus locations.

use crate::{
    LoadedSource, ProgramSource, assemble_input,
    manifest::{CorpusInput, CorpusManifest, DefinitionSpec},
    resolver::read_under_root,
};
use kink_campaign::TestCase;
use kink_patch::{Baseline, Sha256Digest, canonical_json, sha256};
use serde_json::{Value, json};
use std::{
    fmt, fs,
    io::Write,
    path::{Component, Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

#[derive(Debug)]
pub enum StoreError {
    Io(std::io::Error),
    Invalid(String),
}
impl fmt::Display for StoreError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(e) => e.fmt(f),
            Self::Invalid(e) => f.write_str(e),
        }
    }
}
impl std::error::Error for StoreError {}
impl From<std::io::Error> for StoreError {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}

#[derive(Clone, Debug)]
pub struct Store {
    root: PathBuf,
}
impl Store {
    pub fn new(root: impl Into<PathBuf>) -> Self {
        Self { root: root.into() }
    }
    pub fn root(&self) -> &Path {
        &self.root
    }
    pub fn corpus_path(&self, digest: Sha256Digest) -> PathBuf {
        self.root.join(digest.to_string())
    }
    pub fn profile_path(&self, digest: Sha256Digest, profile: &str) -> PathBuf {
        self.corpus_path(digest).join(profile)
    }
    pub fn admission_path(
        &self,
        digest: Sha256Digest,
        profile: &str,
        id: &str,
    ) -> Result<PathBuf, StoreError> {
        let relative = Path::new(id);
        if relative.as_os_str().is_empty()
            || relative
                .components()
                .any(|c| !matches!(c, Component::Normal(_)))
        {
            return Err(StoreError::Invalid("unsafe definition id".into()));
        }
        let mut path = self
            .profile_path(digest, profile)
            .join("admission")
            .join(relative);
        // Append rather than replace an extension: definition ids are arbitrary names.
        path.as_mut_os_string().push(".json");
        Ok(path)
    }
    pub fn read_json(&self, path: &Path) -> Result<Value, StoreError> {
        let text = fs::read_to_string(path)?;
        let value: Value =
            serde_json::from_str(&text).map_err(|e| StoreError::Invalid(e.to_string()))?;
        if canonical_json(&value) != text {
            return Err(StoreError::Invalid("non-canonical stored JSON".into()));
        }
        Ok(value)
    }
    pub fn read_index(&self, digest: Sha256Digest, profile: &str) -> Result<Value, StoreError> {
        let path = self.profile_path(digest, profile).join("index.json");
        if !path.exists() {
            return Ok(json!({}));
        }
        let value = self.read_json(&path)?;
        if !value.is_object() {
            return Err(StoreError::Invalid("index must be an object".into()));
        }
        Ok(value)
    }
    pub fn write_json(&self, path: &Path, value: &Value) -> Result<(), StoreError> {
        self.write_text(path, &canonical_json(value))
    }
    /// Publish complete bytes by rename; temporary names never enter stored JSON.
    pub fn write_text(&self, path: &Path, text: &str) -> Result<(), StoreError> {
        self.write_bytes(path, text.as_bytes())
    }
    pub fn write_bytes(&self, path: &Path, bytes: &[u8]) -> Result<(), StoreError> {
        static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);
        let parent = path
            .parent()
            .ok_or_else(|| StoreError::Invalid("missing parent".into()))?;
        fs::create_dir_all(parent)?;
        let temp = parent.join(format!(
            ".tmp-{}-{}",
            std::process::id(),
            NEXT_TEMP.fetch_add(1, Ordering::Relaxed)
        ));
        let result = (|| {
            let mut file = fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&temp)?;
            file.write_all(bytes)?;
            file.sync_all()?;
            fs::rename(&temp, path)?;
            Ok(())
        })();
        if result.is_err() {
            let _ = fs::remove_file(temp);
        }
        result
    }
    /// Read the sole authoritative corpus declaration and verify its directory digest.
    pub fn read_manifest(&self, digest: Sha256Digest) -> Result<CorpusManifest, StoreError> {
        let text = fs::read_to_string(self.corpus_path(digest).join("corpus-manifest.json"))?;
        let manifest = CorpusManifest::from_canonical_json(&text)
            .map_err(|e| StoreError::Invalid(format!("stored corpus manifest: {e}")))?;
        if manifest.digest() != digest {
            return Err(StoreError::Invalid("stored corpus manifest digest".into()));
        }
        Ok(manifest)
    }
    pub fn input_path(&self, corpus: Sha256Digest, input: Sha256Digest) -> PathBuf {
        self.corpus_path(corpus)
            .join("inputs")
            .join(input.to_string())
    }
    pub(crate) fn ensure_inputs(
        &self,
        corpus: Sha256Digest,
        definition: &DefinitionSpec,
        root: &Path,
    ) -> Result<(), StoreError> {
        // Verify all pins before publishing any input. Admission already used these
        // pins, so a changed workspace input cannot replace its admitted bytes.
        let mut inputs = Vec::new();
        for test in &definition.tests {
            if let Some((file, pin)) = input_pin(definition, &test.input)? {
                let (_, bytes) =
                    read_under_root(root, file).map_err(|e| StoreError::Invalid(e.to_string()))?;
                if sha256(&bytes) != pin {
                    return Err(StoreError::Invalid("workspace input digest differs".into()));
                }
                let path = self.input_path(corpus, pin);
                match fs::read(&path) {
                    Ok(existing) if existing != bytes => {
                        return Err(StoreError::Invalid("stored input differs".into()));
                    }
                    Ok(_) => {}
                    Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
                        inputs.push((path, bytes))
                    }
                    Err(e) => return Err(e.into()),
                }
            }
        }
        for (path, bytes) in inputs {
            self.write_bytes(&path, &bytes)?;
        }
        Ok(())
    }
    /// Rebuild tests using only the digest-checked stored declaration, inputs and artifact.
    pub fn rebuild_tests(
        &self,
        corpus: Sha256Digest,
        id: &str,
        baseline: &Baseline,
    ) -> Result<Vec<TestCase>, StoreError> {
        let manifest = self.read_manifest(corpus)?;
        let definition = manifest
            .definitions()
            .iter()
            .find(|d| d.id == id)
            .ok_or_else(|| StoreError::Invalid("definition is not listed".into()))?;
        let syntax_module = k_rust::outer::resolve_syntax_module(
            baseline.loaded().resolved(),
            definition.syntax_module.as_deref(),
        )
        .map_err(|e| StoreError::Invalid(e.to_string()))?
        .name;
        let loaded = LoadedSource {
            baseline: baseline.clone(),
            files: Vec::new(),
            root: PathBuf::new(),
            syntax_module,
        };
        definition
            .tests
            .iter()
            .map(|test| {
                let text = input_pin(definition, &test.input)?
                    .map(|(_, pin)| {
                        let bytes = fs::read(self.input_path(corpus, pin))?;
                        if sha256(&bytes) != pin {
                            return Err(StoreError::Invalid("stored input digest differs".into()));
                        }
                        String::from_utf8(bytes).map_err(|e| StoreError::Invalid(e.to_string()))
                    })
                    .transpose()?;
                let initial_state = match &test.input {
                    CorpusInput::Program(spec) => {
                        let mut spec = spec.clone();
                        if let Some(text) = text {
                            spec.program = ProgramSource::Text(text);
                        }
                        assemble_input(&loaded, &spec)
                            .map_err(|e| StoreError::Invalid(e.to_string()))?
                    }
                    CorpusInput::KoreState { .. } => {
                        let value = serde_json::from_str(&text.expect("file-backed input"))
                            .map_err(|e| StoreError::Invalid(e.to_string()))?;
                        k_rust::kore::codec::from_value(&value)
                            .map_err(|e| StoreError::Invalid(e.to_string()))?
                    }
                };
                if !initial_state.free_variables().is_empty() {
                    return Err(StoreError::Invalid("stored input is not concrete".into()));
                }
                Ok(TestCase {
                    id: test.id.clone(),
                    initial_state,
                    oracles: test.oracles.clone(),
                })
            })
            .collect()
    }
    pub(crate) fn ensure_manifest(
        &self,
        manifest: &crate::manifest::CorpusManifest,
    ) -> Result<(), StoreError> {
        let path = self
            .corpus_path(manifest.digest())
            .join("corpus-manifest.json");
        let text = manifest.text();
        match fs::read(&path) {
            Ok(bytes) if bytes == text.as_bytes() => Ok(()),
            Ok(_) => Err(StoreError::Invalid("stored corpus manifest differs".into())),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => self.write_text(&path, &text),
            Err(e) => Err(e.into()),
        }
    }
}

fn input_name(name: &str) -> Result<PathBuf, StoreError> {
    let relative = PathBuf::from(k_rust::outer::normalize_virtual_path(Path::new(name)));
    if relative.as_os_str().is_empty()
        || relative
            .components()
            .any(|c| !matches!(c, Component::Normal(_)))
    {
        return Err(StoreError::Invalid("input escapes definition root".into()));
    }
    Ok(relative)
}

fn input_pin<'a>(
    definition: &DefinitionSpec,
    input: &'a CorpusInput,
) -> Result<Option<(&'a str, Sha256Digest)>, StoreError> {
    match input {
        CorpusInput::Program(spec) => match &spec.program {
            ProgramSource::Text(_) => Ok(None),
            ProgramSource::File(file) => {
                let normalized = input_name(file)?;
                let pin = definition
                    .files
                    .iter()
                    .find(|f| Path::new(&f.name) == normalized)
                    .ok_or_else(|| StoreError::Invalid("missing program input pin".into()))?;
                Ok(Some((file, pin.sha256)))
            }
        },
        CorpusInput::KoreState { file, sha256 } => {
            if definition
                .files
                .iter()
                .any(|f| f.name == *file && f.sha256 != *sha256)
            {
                return Err(StoreError::Invalid("inconsistent input pins".into()));
            }
            Ok(Some((file, *sha256)))
        }
    }
}

/// A time bound is observed only through timeout statuses/sides or time-limit runs.
/// Declared time_ms bounds and undetectable SMT indeterminacy are not observations.
pub fn time_bound_fired(report: &Value) -> bool {
    fn run_fired(run: &Value) -> bool {
        run["failed"] == "time-limit"
            || run["sides"]
                .as_array()
                .is_some_and(|sides| sides.iter().any(|s| s == "timeout"))
    }
    report["baseline"]
        .as_array()
        .is_some_and(|rows| rows.iter().any(|row| run_fired(&row["run"])))
        || report["mutants"].as_array().is_some_and(|mutants| {
            mutants.iter().any(|mutant| {
                mutant["status"] == "timeout"
                    || mutant["tests"].as_array().is_some_and(|tests| {
                        tests
                            .iter()
                            .any(|test| run_fired(&test["run"]) || run_fired(&test["mutant"]))
                    })
            })
        })
}
