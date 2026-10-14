//! Host facilities that exist only inside a running procedural macro.
//!
//! Expansion code reaches invocation source locations and `krs` facade
//! discovery only through [`MacroEnvironment`]. `krs-macros` implements it
//! for rustc (`ProcMacroEnvironment`); this crate never calls `Span::unwrap()`
//! or queries Cargo manifests for the facade.

use std::path::{Component, Path as FsPath};

use krs_ir::Position;
use proc_macro2::Span;
use syn::Path;

/// One source position as a proc macro observes it: 1-based line and column.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SourcePosition {
    /// 1-based line.
    pub line: u32,
    /// 1-based column, in the unit rustc span columns use.
    pub column: u32,
}

impl From<Position> for SourcePosition {
    fn from(position: Position) -> Self {
        Self {
            line: position.line(),
            column: position.scalar_column(),
        }
    }
}

/// The host of one macro invocation: source locations of its spans, its call
/// site, and the path of the `krs` facade.
///
/// Location queries resolve a span as rustc does. A span the expansion
/// synthesized rather than copied from the macro input (`Span::call_site()`,
/// `Span::mixed_site()`, or tokens re-parsed from a string) is located at the
/// invocation's call site. Expansion code reads span locations only through
/// this trait, never through `proc_macro2::Span::start`/`end`, because outside
/// a procedural macro a synthesized span is not located at the invocation.
pub trait MacroEnvironment {
    /// The display file of `span` (rustc `Span::file`).
    fn span_file(&self, span: Span) -> String;
    /// The file of `span` as expansion nonces hash it: its path relative to
    /// the invoking package's manifest directory, `/`-separated, for example
    /// `src/lib.rs`.
    ///
    /// Nonces name generated items whose names reach the emitted artifacts
    /// and the order of K sentences, so this identity must not depend on
    /// where the package lives on disk. rustc's display file does: Cargo
    /// passes a workspace member's file relative to the workspace root and a
    /// path dependency's file (every package the KRS collector builds) as an
    /// absolute path. A host that sees such spellings resolves them with
    /// [`package_relative_file`].
    fn span_package_file(&self, span: Span) -> String;
    /// Start of `span`, or `None` when the host has no representable location.
    fn span_start(&self, span: Span) -> Option<SourcePosition>;
    /// End of `span`, or `None` when the host has no representable location.
    fn span_end(&self, span: Span) -> Option<SourcePosition>;
    /// The invocation's call-site span, if the host exposes one.
    fn call_site(&self) -> Option<Span>;
    /// The path through which generated code names the `krs` facade.
    ///
    /// # Errors
    ///
    /// Returns the invocation's diagnostic when the host cannot name the
    /// facade, such as a crate without a direct `krs` dependency.
    fn facade_path(&self) -> crate::Result<Path>;
}

/// The path of the absolute `file` relative to the absolute `manifest_dir`,
/// `/`-separated, with a `..` for each level `file` lies outside the
/// directory; `None` when either path is relative or the two share no root.
///
/// The comparison is lexical: `.` components are dropped and `..` removes the
/// preceding component, so a host that wants symbolic links resolved
/// canonicalizes both paths first.
#[must_use]
pub fn package_relative_file(file: &FsPath, manifest_dir: &FsPath) -> Option<String> {
    if !file.is_absolute() || !manifest_dir.is_absolute() {
        return None;
    }
    let file = lexical_components(file);
    let base = lexical_components(manifest_dir);
    let common = file
        .iter()
        .zip(&base)
        .take_while(|(left, right)| left == right)
        .count();
    if common == 0 {
        return None;
    }
    let mut parts = std::iter::repeat_n("..".to_owned(), base.len() - common).collect::<Vec<_>>();
    parts.extend(
        file[common..]
            .iter()
            .map(|component| component.as_os_str().to_string_lossy().into_owned()),
    );
    Some(parts.join("/"))
}

fn lexical_components(path: &FsPath) -> Vec<Component<'_>> {
    let mut components = Vec::new();
    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                if matches!(components.last(), Some(Component::Normal(_))) {
                    components.pop();
                }
            }
            Component::Prefix(_) | Component::RootDir | Component::Normal(_) => {
                components.push(component);
            }
        }
    }
    components
}

/// A host-independent environment for unit tests: a configured display file
/// and facade path, positions from `proc_macro2` span locations, and no call
/// site.
#[cfg(test)]
pub(crate) struct FixedEnvironment {
    pub(crate) file: String,
    pub(crate) facade: Path,
}

#[cfg(test)]
impl FixedEnvironment {
    pub(crate) fn new(file: &str, facade: &str) -> Self {
        Self {
            file: file.to_owned(),
            facade: syn::parse_str(facade).expect("a test facade is a Rust path"),
        }
    }

    fn position(location: proc_macro2::LineColumn) -> Option<SourcePosition> {
        Position::from_proc_macro2(location).ok().map(Into::into)
    }
}

#[cfg(test)]
impl MacroEnvironment for FixedEnvironment {
    fn span_file(&self, _span: Span) -> String {
        self.file.clone()
    }

    fn span_package_file(&self, _span: Span) -> String {
        self.file.clone()
    }

    fn span_start(&self, span: Span) -> Option<SourcePosition> {
        Self::position(span.start())
    }

    fn span_end(&self, span: Span) -> Option<SourcePosition> {
        Self::position(span.end())
    }

    fn call_site(&self) -> Option<Span> {
        None
    }

    fn facade_path(&self) -> crate::Result<Path> {
        Ok(self.facade.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::FixedEnvironment;
    use super::package_relative_file;
    use std::path::Path;

    #[test]
    fn package_relative_file_is_lexical_and_checkout_independent() {
        let relative = |file: &str, manifest: &str| {
            package_relative_file(Path::new(file), Path::new(manifest))
        };
        assert_eq!(
            relative("/a/krs/tests/pkg/src/lib.rs", "/a/krs/tests/pkg").as_deref(),
            Some("src/lib.rs")
        );
        assert_eq!(
            relative(
                "/b/k-rust/krs/tests/pkg/src/lib.rs",
                "/b/k-rust/krs/tests/pkg/"
            )
            .as_deref(),
            Some("src/lib.rs")
        );
        assert_eq!(
            relative("/w/./pkg/src/../src/lib.rs", "/w/pkg").as_deref(),
            Some("src/lib.rs")
        );
        assert_eq!(
            relative("/w/shared/grammar.rs", "/w/pkg").as_deref(),
            Some("../shared/grammar.rs")
        );
        assert_eq!(relative("src/lib.rs", "/w/pkg"), None);
        assert_eq!(relative("/w/pkg/src/lib.rs", "pkg"), None);
    }
    use proc_macro2::TokenStream;

    #[test]
    fn sorts_expand_outside_a_proc_macro() {
        let environment = FixedEnvironment::new("src/lib.rs", "::k");
        let input: TokenStream = "Exp;\nVal;".parse().unwrap();
        let output = crate::expand::sorts(&environment, input)
            .unwrap()
            .to_string();
        assert!(output.contains(":: k :: __krs_host_provenance"));
        assert!(output.contains("\"src/lib.rs\""));
    }

    #[test]
    fn host_provenance_without_call_site_uses_first_token_range() {
        let environment = FixedEnvironment::new("src/lib.rs", "::k");
        let facade = syn::parse_str("::k").unwrap();
        let tokens: TokenStream = "alpha beta".parse().unwrap();
        let fallback = krs_syntax::TokenRange::for_tokens(&tokens).unwrap();
        let output =
            crate::provenance::host_provenance(&environment, &facade, fallback, &[]).to_string();
        assert!(output.contains("& [\"src/lib.rs\"]"));
        assert!(output.contains(
            ":: k :: __KrsRawAnchor :: new (0usize , false , (1u32 , 1u32) , (1u32 , 11u32) , false)"
        ));
        assert!(!output.contains("CARGO_MANIFEST_DIR"));
    }

    #[test]
    fn blank_display_file_takes_the_unavailable_path() {
        let facade = syn::parse_str("::k").unwrap();
        let tokens: TokenStream = "alpha beta".parse().unwrap();
        let fallback = krs_syntax::TokenRange::for_tokens(&tokens).unwrap();
        for file in ["", " \t"] {
            let environment = FixedEnvironment::new(file, "::k");
            let output = crate::provenance::host_provenance(&environment, &facade, fallback, &[])
                .to_string();
            assert!(output.contains("& [\"<proc-macro-input>\"]"), "{file:?}");
            assert!(output.contains(
                ":: k :: __KrsRawAnchor :: new (0usize , false , (1u32 , 1u32) , (1u32 , 2u32) , false)"
            ));
        }
    }

    #[test]
    fn absolute_anchor_includes_cargo_manifest_dir() {
        let facade = syn::parse_str("::k").unwrap();
        let tokens: TokenStream = "alpha beta".parse().unwrap();
        let fallback = krs_syntax::TokenRange::for_tokens(&tokens).unwrap();
        for file in [
            "/package/src/lib.rs",
            "file:relative.rs",
            "file:/lib.rs",
            "file:",
            r"\lib.rs",
        ] {
            let environment = FixedEnvironment::new(file, "::k");
            let output = crate::provenance::host_provenance(&environment, &facade, fallback, &[])
                .to_string();
            assert!(output.contains("env ! (\"CARGO_MANIFEST_DIR\")"), "{file}");
        }
    }
}
