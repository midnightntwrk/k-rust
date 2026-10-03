use super::CommandError;
use krs_compiler::{ARTIFACT_MARKER, ARTIFACT_MARKER_FILE};
use std::fs;
use std::path::Path;

pub(super) fn prepare_output(path: &Path) -> Result<(), CommandError> {
    if path.exists() {
        let empty = fs::read_dir(path)
            .map_err(|source| CommandError::Io {
                path: path.to_path_buf(),
                source,
            })?
            .next()
            .is_none();
        if !empty {
            let marker = path.join(ARTIFACT_MARKER_FILE);
            let owned =
                fs::read_to_string(&marker).is_ok_and(|contents| contents == ARTIFACT_MARKER);
            if !owned {
                return Err(CommandError::UnsafeOutput(path.to_path_buf()));
            }
        }
    }
    fs::create_dir_all(path).map_err(|source| CommandError::Io {
        path: path.to_path_buf(),
        source,
    })?;
    write_output_if_different(path, ARTIFACT_MARKER_FILE, ARTIFACT_MARKER.as_bytes())
}

pub(super) fn write_output_if_different(
    directory: &Path,
    name: &str,
    bytes: &[u8],
) -> Result<(), CommandError> {
    let path = directory.join(name);
    if fs::read(&path).is_ok_and(|existing| existing == bytes) {
        return Ok(());
    }
    write_output(directory, name, bytes)
}

pub(super) fn write_output(directory: &Path, name: &str, bytes: &[u8]) -> Result<(), CommandError> {
    let path = directory.join(name);
    fs::write(&path, bytes).map_err(|source| CommandError::Io { path, source })
}
