//! `kink/definition.k`: the K kink judges, kept equal to the package's emission.
//!
//! The file is compared with the fresh in-process emission byte for byte. Every command but
//! `emit --check` and a `--locked` one writes it when it differs; those two write nothing and
//! report it `stale`. The comparison is the whole freshness rule: the emission is a function of
//! the package's sources and this krs, and kink-flow's admission, digests and caches are then
//! exactly those of a K corpus over that file.

use std::fs;
use std::io;
use std::path::Path;

use serde_json::{Value, json};

/// What a command found `kink/definition.k` to be, or made it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DefinitionStatus {
    /// It held the emission.
    Unchanged,
    /// It was missing or differed, and the command wrote the emission.
    Written,
    /// It was missing or differed, and the command wrote nothing (`--locked`, `emit --check`).
    Stale,
}

impl DefinitionStatus {
    /// The name documents give the status.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Unchanged => "unchanged",
            Self::Written => "written",
            Self::Stale => "stale",
        }
    }
}

/// Why a command could not compare or write `kink/definition.k`.
#[derive(Debug)]
pub(super) enum FreshenError {
    /// The file exists and could not be read, so it was not compared.
    Read(io::Error),
    /// The emission could not be written there.
    Write(io::Error),
}

impl FreshenError {
    /// The reason a refused document gives.
    pub(super) const fn reason(&self) -> &'static str {
        match self {
            Self::Read(_) => "definition-unreadable",
            Self::Write(_) => "definition-unwritable",
        }
    }

    /// The detail a document gives, naming the file as `shown`.
    pub(super) fn detail(&self, shown: &str) -> String {
        match self {
            Self::Read(error) => format!("cannot read {shown}: {error}"),
            Self::Write(error) => format!("cannot write {shown}: {error}"),
        }
    }
}

/// Compare the file at `path` with `emitted`, and, when it is missing or differs and `write`
/// holds, write `emitted` there (creating its directory).
///
/// # Errors
///
/// Returns the error of reading an existing file, or of writing the new one.
pub(super) fn freshen(
    path: &Path,
    emitted: &str,
    write: bool,
) -> Result<DefinitionStatus, FreshenError> {
    match fs::read(path) {
        Ok(bytes) if bytes == emitted.as_bytes() => return Ok(DefinitionStatus::Unchanged),
        Ok(_) => {}
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(error) => return Err(FreshenError::Read(error)),
    }
    if !write {
        return Ok(DefinitionStatus::Stale);
    }
    let written = (|| {
        if let Some(directory) = path.parent() {
            fs::create_dir_all(directory)?;
        }
        // Written beside the file and renamed over it, so that a reader never sees half of it.
        let partial = path.with_extension("k.partial");
        fs::write(&partial, emitted)?;
        fs::rename(&partial, path)
    })();
    written.map_err(FreshenError::Write)?;
    Ok(DefinitionStatus::Written)
}

/// `path` as documents show it: relative to the root package's directory `root` when it lies
/// inside it (`kink/definition.k`), as given otherwise.
pub(super) fn shown_path(path: &Path, root: Option<&Path>) -> String {
    root.and_then(|root| path.strip_prefix(root).ok())
        .unwrap_or(path)
        .to_string_lossy()
        .replace('\\', "/")
}

/// The `definition` value of a document: the file's shown path and its status.
pub(super) fn definition_value(shown: &str, status: DefinitionStatus) -> Value {
    json!({"path": shown, "status": status.as_str()})
}

/// The `krs-kink-emit` document version.
pub const EMIT_VERSION: u64 = 1;

/// The document of `krs kink emit`: the definition's path and status (`null` when krs refused
/// the package or the file could not be written, with the reason as `refusal`), and whether it
/// was `--check`.
pub(super) fn emit_document(
    shown: &str,
    status: Option<DefinitionStatus>,
    check: bool,
    refusal: Option<&str>,
) -> Value {
    json!({
        "schema": "krs-kink-emit",
        "version": EMIT_VERSION,
        "check": check,
        "definition": {
            "path": shown,
            "status": status.map(DefinitionStatus::as_str),
        },
        "refusal": refusal,
    })
}

#[cfg(test)]
mod tests {
    use super::{DefinitionStatus, FreshenError, freshen, shown_path};
    use std::path::Path;

    #[test]
    fn a_file_that_cannot_be_read_is_not_reported_unwritable() {
        let directory = tempfile::tempdir().unwrap();
        // A directory where the file should be: reading it fails, and not as a missing file.
        let path = directory.path().join("definition.k");
        std::fs::create_dir(&path).unwrap();
        let error = freshen(&path, "a\n", true).unwrap_err();
        assert!(matches!(error, FreshenError::Read(_)), "{error:?}");
        assert_eq!(error.reason(), "definition-unreadable");
        assert!(
            error
                .detail("kink/definition.k")
                .starts_with("cannot read kink/definition.k: "),
            "{}",
            error.detail("kink/definition.k")
        );
    }

    #[test]
    fn a_stale_file_is_written_unless_locked() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("kink/definition.k");
        assert_eq!(
            freshen(&path, "a\n", false).unwrap(),
            DefinitionStatus::Stale
        );
        assert!(!path.exists());
        assert_eq!(
            freshen(&path, "a\n", true).unwrap(),
            DefinitionStatus::Written
        );
        assert_eq!(std::fs::read_to_string(&path).unwrap(), "a\n");
        assert_eq!(
            freshen(&path, "a\n", false).unwrap(),
            DefinitionStatus::Unchanged
        );
        assert_eq!(
            freshen(&path, "b\n", false).unwrap(),
            DefinitionStatus::Stale
        );
        assert_eq!(std::fs::read_to_string(&path).unwrap(), "a\n");
        assert_eq!(
            freshen(&path, "b\n", true).unwrap(),
            DefinitionStatus::Written
        );
        assert_eq!(std::fs::read_to_string(&path).unwrap(), "b\n");
        assert!(!path.with_extension("k.partial").exists());
    }

    #[test]
    fn a_path_inside_the_package_is_shown_relative_to_it() {
        let root = Path::new("/work/plus");
        assert_eq!(
            shown_path(Path::new("/work/plus/kink/definition.k"), Some(root)),
            "kink/definition.k"
        );
        assert_eq!(
            shown_path(Path::new("/elsewhere/definition.k"), Some(root)),
            "/elsewhere/definition.k"
        );
    }
}
