//! Lexical path handling for host-provided virtual source graphs.

use std::path::{Component, Path};

/// Normalize `.` and `..` components without touching a filesystem.
///
/// This keeps virtual `requires` resolution deterministic in native and WebAssembly hosts.
pub fn normalize_virtual_path(path: &Path) -> String {
    let mut parts = Vec::new();
    let mut absolute = false;
    for component in path.components() {
        match component {
            Component::Normal(value) => parts.push(value.to_string_lossy().into_owned()),
            Component::ParentDir => {
                if parts.last().is_some_and(|part| part != "..") {
                    parts.pop();
                } else if !absolute {
                    parts.push("..".to_owned());
                }
            }
            Component::CurDir => {}
            Component::RootDir => {
                absolute = true;
                parts.clear();
            }
            Component::Prefix(prefix) => {
                parts.push(prefix.as_os_str().to_string_lossy().into_owned());
            }
        }
    }
    let normalized = parts.join("/");
    if absolute {
        format!("/{normalized}")
    } else {
        normalized
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn collapses_relative_components_without_escaping_relative_roots() {
        assert_eq!(
            normalize_virtual_path(Path::new("definitions/nested/../base.k")),
            "definitions/base.k"
        );
        assert_eq!(
            normalize_virtual_path(Path::new("../../base.k")),
            "../../base.k"
        );
        assert_eq!(normalize_virtual_path(Path::new("/../base.k")), "/base.k");
    }
}
