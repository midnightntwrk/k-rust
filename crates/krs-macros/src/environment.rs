//! The rustc host of [`MacroEnvironment`].
//!
//! [`ProcMacroEnvironment`] is the only code in the KRS workspace that calls
//! `Span::unwrap()` or `proc_macro_crate`; `krs-expand` reaches invocation
//! source locations and `krs` facade discovery only through it.

use std::fs;
use std::path::{Path as FsPath, PathBuf};

use krs_expand::{MacroEnvironment, SourcePosition, package_relative_file};
use krs_ir::Position;
use proc_macro_crate::{FoundCrate, crate_name};
use proc_macro2::Span;
use syn::{Ident, Path, parse_quote};

/// The environment of a macro invocation expanded by rustc.
pub(crate) struct ProcMacroEnvironment;

impl ProcMacroEnvironment {
    fn position(location: proc_macro::Span) -> Option<SourcePosition> {
        Position::from_proc_macro_values(location.line(), location.column())
            .ok()
            .map(Into::into)
    }
}

impl MacroEnvironment for ProcMacroEnvironment {
    fn span_file(&self, span: Span) -> String {
        span.unwrap().file()
    }

    /// Resolves rustc's display file against the working directory rustc
    /// runs in (the workspace root, for a workspace member's relative
    /// spelling) and makes it relative to `CARGO_MANIFEST_DIR`. Without a
    /// manifest directory, as outside Cargo, the display file is used as is.
    fn span_package_file(&self, span: Span) -> String {
        let display = self.span_file(span);
        package_file(
            &display,
            std::env::current_dir().ok().as_deref(),
            std::env::var_os("CARGO_MANIFEST_DIR")
                .map(PathBuf::from)
                .as_deref(),
        )
        .unwrap_or(display)
    }

    fn span_start(&self, span: Span) -> Option<SourcePosition> {
        Self::position(span.unwrap().start())
    }

    fn span_end(&self, span: Span) -> Option<SourcePosition> {
        Self::position(span.unwrap().end())
    }

    fn call_site(&self) -> Option<Span> {
        Some(Span::call_site())
    }

    fn facade_path(&self) -> krs_expand::Result<Path> {
        match crate_name("krs") {
            Ok(FoundCrate::Itself) => Ok(parse_quote!(crate)),
            Ok(FoundCrate::Name(name)) => {
                let ident = Ident::new(&name, Span::call_site());
                Ok(parse_quote!(::#ident))
            }
            Err(error) => Err(krs_expand::ExpandError::new(
                krs_diagnostic::codes::expand::FACADE_DEPENDENCY,
                Span::call_site(),
                format!(
                    "KRS macros require a direct dependency on the `krs` facade (dependency renames are supported): {error}"
                ),
            )),
        }
    }
}

/// `display` relative to `manifest_dir`, resolving a relative `display`
/// against `working_directory`. Both paths are canonicalized when they exist,
/// so a checkout reached through a symbolic link has the same identity as its
/// target.
fn package_file(
    display: &str,
    working_directory: Option<&FsPath>,
    manifest_dir: Option<&FsPath>,
) -> Option<String> {
    if display.trim().is_empty() {
        return None;
    }
    let manifest_dir = manifest_dir?;
    let display = FsPath::new(display);
    let file = if display.is_absolute() {
        display.to_path_buf()
    } else {
        working_directory?.join(display)
    };
    match (fs::canonicalize(&file), fs::canonicalize(manifest_dir)) {
        (Ok(file), Ok(manifest_dir)) => package_relative_file(&file, &manifest_dir),
        _ => package_relative_file(&file, manifest_dir),
    }
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::path::Path;

    use super::package_file;

    #[test]
    fn package_file_is_relative_to_the_manifest_wherever_the_checkout_is() {
        let identity = |root: &Path| {
            package_file(
                &root.join("tests/pkg/src/lib.rs").display().to_string(),
                None,
                Some(&root.join("tests/pkg")),
            )
        };
        assert_eq!(
            identity(Path::new("/home/a/krs")).as_deref(),
            Some("src/lib.rs")
        );
        assert_eq!(
            identity(Path::new("/var/tmp/b/k-rust/krs")).as_deref(),
            Some("src/lib.rs")
        );
    }

    #[test]
    fn workspace_member_and_path_dependency_spellings_agree() {
        let manifest = Path::new("/checkout/tests/fixtures/pkg");
        let member = package_file(
            "pkg/src/grammar.rs",
            Some(Path::new("/checkout/tests/fixtures")),
            Some(manifest),
        );
        let dependency = package_file(
            "/checkout/tests/fixtures/pkg/src/grammar.rs",
            Some(Path::new("/elsewhere/collector")),
            Some(manifest),
        );
        assert_eq!(member.as_deref(), Some("src/grammar.rs"));
        assert_eq!(member, dependency);
    }

    #[test]
    fn files_outside_the_manifest_dir_keep_their_relative_place() {
        assert_eq!(
            package_file(
                "/checkout/shared/./common/../layout.rs",
                None,
                Some(Path::new("/checkout/pkg")),
            )
            .as_deref(),
            Some("../shared/layout.rs")
        );
    }

    #[test]
    fn missing_cargo_context_keeps_the_display_file() {
        assert_eq!(
            package_file("src/lib.rs", None, Some(Path::new("/pkg"))),
            None
        );
        assert_eq!(package_file("/pkg/src/lib.rs", None, None), None);
        assert_eq!(
            package_file("", Some(Path::new("/w")), Some(Path::new("/pkg"))),
            None
        );
    }

    #[cfg(unix)]
    #[test]
    fn a_checkout_reached_through_a_symbolic_link_has_its_target_identity() {
        let temp = krs_test_support::temp_dir();
        let real = temp.path().join("real");
        fs::create_dir_all(real.join("pkg/src")).unwrap();
        fs::write(real.join("pkg/src/lib.rs"), "").unwrap();
        let link = temp.path().join("link");
        std::os::unix::fs::symlink(&real, &link).unwrap();
        let file = real.join("pkg/src/lib.rs").display().to_string();
        assert_eq!(
            package_file(&file, None, Some(&link.join("pkg"))).as_deref(),
            Some("src/lib.rs")
        );
    }
}
