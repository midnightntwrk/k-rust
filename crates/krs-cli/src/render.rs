//! Human diagnostic rendering with verified authored source revisions.

use std::collections::BTreeMap;
use std::path::PathBuf;

use annotate_snippets::{AnnotationKind, Group, Level, Origin, Renderer, Snippet};
use krs_diagnostic::{Diagnostic, Location, Severity};
use krs_ir::{LineIndex, PackageId, Sha256Digest, SourceRange};
use sha2::{Digest, Sha256};

use crate::{CollectorPlan, DiagnosticEnvelope, DiagnosticGeneratedRange};

/// Selected package roots available for rendering authored source.
/// Source text must match the diagnostic's digest before it is displayed.
#[derive(Clone, Debug, Default)]
pub struct DiagnosticSources {
    packages: BTreeMap<PackageId, PathBuf>,
}

impl DiagnosticSources {
    /// Selects source roots from a validated collector plan's definition facets.
    #[must_use]
    pub fn from_plan(plan: &CollectorPlan) -> Self {
        let packages = plan
            .facets()
            .iter()
            .filter_map(|facet| {
                let package = PackageId::new(
                    &facet.k_namespace,
                    &facet.package_name,
                    &facet.package_version,
                    &facet.cargo_source,
                )
                .ok()?;
                Some((package, facet.manifest_path.parent()?.to_path_buf()))
            })
            .collect();
        Self { packages }
    }

    /// Renders a located envelope using its exact authored revision when available.
    /// `color` must be true only when the output terminal permits ANSI styles.
    #[must_use]
    pub fn render_envelope(&self, envelope: &DiagnosticEnvelope, color: bool) -> String {
        let level = diagnostic_level(envelope.severity.into());
        self.render(
            level,
            &envelope.code,
            &envelope.message,
            Some(&envelope.authored_range),
            &envelope.notes,
            envelope.generated_range.as_ref(),
            color,
        )
    }

    /// Renders the shared producer model without consulting command error variants.
    /// Only exact authored locations may display source text.
    #[must_use]
    pub fn render_diagnostic(&self, diagnostic: &Diagnostic, color: bool) -> String {
        let level = diagnostic_level(diagnostic.severity);
        let range = match &diagnostic.primary.location {
            Location::Source(range) => Some(range),
            _ => None,
        };
        let generated = std::iter::once(&diagnostic.primary)
            .chain(&diagnostic.secondary)
            .find_map(|label| match &label.location {
                Location::Generated(range) => Some(range),
                _ => None,
            });
        self.render(
            level,
            diagnostic.code.as_str(),
            &diagnostic.message,
            range,
            &diagnostic.notes,
            generated,
            color,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn render<'a>(
        &self,
        level: Level<'a>,
        code: &'a str,
        message: &'a str,
        range: Option<&'a SourceRange>,
        notes: &'a [String],
        generated: Option<&DiagnosticGeneratedRange>,
        color: bool,
    ) -> String {
        let mut group = Group::with_title(level.primary_title(message).id(code));
        if let Some(range) = range {
            group = match self.source(range) {
                Ok(source) => {
                    let index = LineIndex::new(&source);
                    let start = range.start_byte as usize;
                    let end = range.end_byte as usize;
                    match (index.byte_to_position(start), index.byte_to_position(end)) {
                        (Ok(_), Ok(_)) if start <= end => group.element(
                            Snippet::source(source)
                                .path(range.file.package_relative_path())
                                .annotation(AnnotationKind::Primary.span(start..end)),
                        ),
                        _ => {
                            unavailable_source(group, range, "authored range is outside the source")
                        }
                    }
                }
                Err(reason) => unavailable_source(group, range, reason),
            };
        }
        for note in notes {
            group = group
                .element(Level::NOTE.message(annotate_snippets::normalize_untrusted_str(note)));
        }
        if let Some(generated) = generated {
            let note = format!(
                "generated {}:{}:{}..{}:{}",
                generated.artifact,
                generated.start_line,
                generated.start_column,
                generated.end_line,
                generated.end_column,
            );
            group = group
                .element(Level::NOTE.message(annotate_snippets::normalize_untrusted_str(&note)));
        }
        let renderer = if color {
            Renderer::styled()
        } else {
            Renderer::plain()
        };
        renderer.render(&[group])
    }

    fn source(&self, range: &SourceRange) -> Result<String, &'static str> {
        let root = self
            .packages
            .get(range.file.package())
            .ok_or("source package is unavailable")?;
        let bytes = std::fs::read(root.join(range.file.package_relative_path()))
            .map_err(|_| "source file is unavailable")?;
        let digest = Sha256Digest::from_bytes(Sha256::digest(&bytes).into());
        if &digest != range.file.content_sha256() {
            return Err("source changed since the diagnostic was produced");
        }
        String::from_utf8(bytes).map_err(|_| "source file is not UTF-8")
    }
}

fn diagnostic_level(severity: Severity) -> Level<'static> {
    match severity {
        Severity::Error => Level::ERROR,
        Severity::Warning => Level::WARNING,
    }
}

fn unavailable_source<'a>(group: Group<'a>, range: &SourceRange, reason: &'a str) -> Group<'a> {
    group
        .element(Origin::path(format!(
            "{} bytes {}..{}",
            range.file.package_relative_path(),
            range.start_byte,
            range.end_byte,
        )))
        .element(Level::NOTE.message(reason))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{DiagnosticSeverity, DiagnosticStage};
    use expect_test::expect;
    use krs_diagnostic::codes::analysis::OVERLAPPING_RULE_HEADS;
    use krs_ir::SourceFileId;

    const SOURCE: &str = "enum Term {\n    Foo,\n}\n";

    fn fixture() -> (tempfile::TempDir, DiagnosticSources, DiagnosticEnvelope) {
        let root = tempfile::tempdir().unwrap();
        std::fs::create_dir(root.path().join("src")).unwrap();
        std::fs::write(root.path().join("src/lib.rs"), SOURCE).unwrap();
        let package = PackageId::new("fixture", "fixture", "0.1.0", "workspace").unwrap();
        let file = SourceFileId::new(
            package.clone(),
            "src/lib.rs",
            Sha256Digest::from_bytes(Sha256::digest(SOURCE.as_bytes()).into()),
        )
        .unwrap();
        let range = SourceRange::new(file, 16, 19).unwrap();
        let sources = DiagnosticSources {
            packages: BTreeMap::from([(package, root.path().to_path_buf())]),
        };
        let envelope = DiagnosticEnvelope::error(
            DiagnosticStage::Analysis,
            OVERLAPPING_RULE_HEADS.as_str(),
            "rule heads overlap",
            range,
        );
        (root, sources, envelope)
    }

    #[test]
    fn located_error_with_notes() {
        let (_root, sources, mut envelope) = fixture();
        envelope.notes = vec!["first rule: first".into(), "second rule: second".into()];
        expect![[r"
            error[krs::analysis::overlapping-rule-heads]: rule heads overlap
             --> src/lib.rs:2:5
              |
            2 |     Foo,
              |     ^^^
              |
              = note: first rule: first
              = note: second rule: second"]]
        .assert_eq(&sources.render_envelope(&envelope, false));
    }

    #[test]
    fn located_warning() {
        let (_root, sources, mut envelope) = fixture();
        envelope.severity = DiagnosticSeverity::Warning;
        expect![[r"
            warning[krs::analysis::overlapping-rule-heads]: rule heads overlap
             --> src/lib.rs:2:5
              |
            2 |     Foo,
              |     ^^^"]]
        .assert_eq(&sources.render_envelope(&envelope, false));
    }

    #[test]
    fn unlocated_diagnostic() {
        let diagnostic =
            Diagnostic::error(OVERLAPPING_RULE_HEADS, "rule heads overlap", Location::None);
        expect!["error[krs::analysis::overlapping-rule-heads]: rule heads overlap"]
            .assert_eq(&DiagnosticSources::default().render_diagnostic(&diagnostic, false));
    }

    #[test]
    fn stale_source() {
        let (root, sources, envelope) = fixture();
        std::fs::write(root.path().join("src/lib.rs"), "enum Term { Bar }\n").unwrap();
        expect![[r"
            error[krs::analysis::overlapping-rule-heads]: rule heads overlap
             --> src/lib.rs bytes 16..19
              = note: source changed since the diagnostic was produced"]]
        .assert_eq(&sources.render_envelope(&envelope, false));
    }

    #[test]
    fn generated_range_note() {
        let (_root, sources, mut envelope) = fixture();
        envelope.generated_range = Some(DiagnosticGeneratedRange {
            artifact: "definition.k".into(),
            start_line: 7,
            start_column: 2,
            end_line: 8,
            end_column: 12,
        });
        expect![[r"
            error[krs::analysis::overlapping-rule-heads]: rule heads overlap
             --> src/lib.rs:2:5
              |
            2 |     Foo,
              |     ^^^
              |
              = note: generated definition.k:7:2..8:12"]]
        .assert_eq(&sources.render_envelope(&envelope, false));
    }

    #[test]
    fn missing_source_keeps_original_range() {
        let (_root, _sources, envelope) = fixture();
        let rendered = DiagnosticSources::default().render_envelope(&envelope, false);
        assert!(rendered.contains("src/lib.rs bytes 16..19"));
        assert!(rendered.contains("source package is unavailable"));
        assert!(!rendered.contains("Foo"));
    }

    #[test]
    fn invalid_source_range_does_not_panic() {
        let (_root, sources, mut envelope) = fixture();
        envelope.authored_range.end_byte = 100;
        let rendered = sources.render_envelope(&envelope, false);
        assert!(rendered.contains("src/lib.rs bytes 16..100"));
        assert!(rendered.contains("authored range is outside the source"));
    }

    #[test]
    fn origin_columns_count_unicode_scalars() {
        let (root, sources, mut envelope) = fixture();
        let source = "// λ Foo\n";
        std::fs::write(root.path().join("src/lib.rs"), source).unwrap();
        let file = SourceFileId::new(
            envelope.authored_range.file.package().clone(),
            "src/lib.rs",
            Sha256Digest::from_bytes(Sha256::digest(source.as_bytes()).into()),
        )
        .unwrap();
        envelope.authored_range = SourceRange::new(file, 6, 9).unwrap();
        let rendered = sources.render_envelope(&envelope, false);
        assert!(rendered.contains("src/lib.rs:1:6"));
        assert!(rendered.contains("// λ Foo"));
    }
}
