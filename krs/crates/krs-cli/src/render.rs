//! Human diagnostic rendering with verified authored source revisions.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use annotate_snippets::{AnnotationKind, Group, Level, Origin, Renderer, Snippet};
use krs_diagnostic::Severity;
use krs_diagnostic::codes::CodeKind;
use krs_ir::{LineIndex, PackageId, Sha256Digest, SourceFileId, SourceRange};
use sha2::{Digest, Sha256};

use crate::{CollectorPlan, DiagnosticEnvelope, DiagnosticLabel};

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

    /// Renders an envelope, showing each exact authored range in its source revision when that
    /// revision is available: the primary's file first, then each label's file in producer
    /// order, each file once. An envelope without an authored range names its item, if any.
    /// `color` must be true only when the output terminal permits ANSI styles.
    #[must_use]
    pub fn render_envelope(&self, envelope: &DiagnosticEnvelope, color: bool) -> String {
        let level = diagnostic_level(envelope.severity.into());
        let internal = envelope.kind == CodeKind::Internal;
        let title = if internal {
            format!("internal error (a KRS bug): {}", envelope.message)
        } else {
            envelope.message.clone()
        };
        let mut group = Group::with_title(level.primary_title(title).id(envelope.code.as_str()));
        let mut files = Vec::<&SourceFileId>::new();
        for file in envelope
            .authored_range
            .iter()
            .map(|range| &range.file)
            .chain(envelope.labels.iter().map(|label| &label.range.file))
        {
            if !files.contains(&file) {
                files.push(file);
            }
        }
        for file in files {
            let primary = envelope
                .authored_range
                .as_ref()
                .filter(|range| &range.file == file);
            let labels = envelope
                .labels
                .iter()
                .filter(|label| &label.range.file == file)
                .collect::<Vec<_>>();
            group = self.file_snippet(group, file, primary, &labels);
        }
        if envelope.authored_range.is_none()
            && let Some(item) = &envelope.item
        {
            group = group.element(Level::NOTE.message(format!("in {item}")));
        }
        for note in &envelope.notes {
            group = group
                .element(Level::NOTE.message(annotate_snippets::normalize_untrusted_str(note)));
        }
        for help in &envelope.help {
            group = group
                .element(Level::HELP.message(annotate_snippets::normalize_untrusted_str(help)));
        }
        if internal {
            group = group.element(Level::HELP.message(
                "this is a bug in KRS, not in the program: please report it with the source that reached it",
            ));
        }
        if let Some(generated) = &envelope.generated_range {
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

    /// One file's snippet: the primary range if it lies in `file`, and the labels that do. A
    /// revision that is unavailable, changed, or does not hold every range is reported by path
    /// and byte range with the reason, for each range.
    fn file_snippet<'a>(
        &self,
        group: Group<'a>,
        file: &SourceFileId,
        primary: Option<&SourceRange>,
        labels: &[&'a DiagnosticLabel],
    ) -> Group<'a> {
        let ranges = primary
            .into_iter()
            .chain(labels.iter().map(|label| &label.range))
            .collect::<Vec<_>>();
        let path = self.display_path(ranges[0]);
        let source = self.file_text(file).and_then(|source| {
            let index = LineIndex::new(&source);
            let holds = |range: &&SourceRange| {
                let (start, end) = (range.start_byte as usize, range.end_byte as usize);
                start <= end
                    && index.byte_to_position(start).is_ok()
                    && index.byte_to_position(end).is_ok()
            };
            if ranges.iter().all(holds) {
                Ok(source)
            } else {
                Err("authored range is outside the source")
            }
        });
        match source {
            Ok(source) => {
                let span = |range: &SourceRange| range.start_byte as usize..range.end_byte as usize;
                let mut snippet = Snippet::source(source).path(path);
                if let Some(range) = primary {
                    snippet = snippet.annotation(AnnotationKind::Primary.span(span(range)));
                }
                for label in labels {
                    let annotation = AnnotationKind::Context.span(span(&label.range));
                    snippet = snippet.annotation(match &label.message {
                        Some(message) => annotation.label(message.as_str()),
                        None => annotation,
                    });
                }
                group.element(snippet)
            }
            Err(reason) => ranges.iter().fold(group, |group, range| {
                unavailable_source(group, range, &path, reason)
            }),
        }
    }

    fn display_path(&self, range: &SourceRange) -> String {
        let relative = Path::new(range.file.package_relative_path());
        let Some(root) = self.packages.get(range.file.package()) else {
            return relative.to_string_lossy().into_owned();
        };
        let path = root.join(relative);
        let cwd = std::env::current_dir().ok();
        path_from_cwd(&path, cwd.as_deref())
            .to_string_lossy()
            .into_owned()
    }

    /// The exact authored revision of `file`, when its package is selected and its digest still matches.
    #[must_use]
    pub fn source_text(&self, file: &SourceFileId) -> Option<String> {
        self.file_text(file).ok()
    }

    fn file_text(&self, file: &SourceFileId) -> Result<String, &'static str> {
        let root = self
            .packages
            .get(file.package())
            .ok_or("source package is unavailable")?;
        let bytes = std::fs::read(root.join(file.package_relative_path()))
            .map_err(|_| "source file is unavailable")?;
        let digest = Sha256Digest::from_bytes(Sha256::digest(&bytes).into());
        if &digest != file.content_sha256() {
            return Err("source changed since the diagnostic was produced");
        }
        String::from_utf8(bytes).map_err(|_| "source file is not UTF-8")
    }
}

fn path_from_cwd<'a>(path: &'a Path, cwd: Option<&Path>) -> &'a Path {
    cwd.and_then(|cwd| path.strip_prefix(cwd).ok())
        .unwrap_or(path)
}

fn diagnostic_level(severity: Severity) -> Level<'static> {
    match severity {
        Severity::Error => Level::ERROR,
        Severity::Warning => Level::WARNING,
    }
}

fn unavailable_source<'a>(
    group: Group<'a>,
    range: &SourceRange,
    path: &str,
    reason: &'a str,
) -> Group<'a> {
    group
        .element(Origin::path(format!(
            "{} bytes {}..{}",
            path, range.start_byte, range.end_byte,
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
        fixture_at(tempfile::tempdir().unwrap())
    }

    fn fixture_at(
        root: tempfile::TempDir,
    ) -> (tempfile::TempDir, DiagnosticSources, DiagnosticEnvelope) {
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
            OVERLAPPING_RULE_HEADS,
            "rule heads overlap",
            range,
        );
        (root, sources, envelope)
    }

    fn render_fixture(
        root: &tempfile::TempDir,
        sources: &DiagnosticSources,
        envelope: &DiagnosticEnvelope,
    ) -> String {
        let rendered = sources.render_envelope(envelope, false);
        let path = root.path().join("src/lib.rs");
        let cwd = std::env::current_dir().unwrap();
        let displayed = path.strip_prefix(&cwd).unwrap_or(&path);
        assert!(rendered.contains(&format!("--> {}", displayed.display())));
        rendered.replace(&*displayed.to_string_lossy(), "<package>/src/lib.rs")
    }

    #[test]
    fn source_under_cwd_uses_cwd_relative_path() {
        let cwd = std::env::current_dir().unwrap();
        let (root, sources, envelope) = fixture_at(tempfile::tempdir_in(&cwd).unwrap());
        let path = root.path().join("src/lib.rs");
        let relative = path.strip_prefix(&cwd).unwrap();
        let rendered = sources.render_envelope(&envelope, false);
        assert!(rendered.contains(&format!("--> {}:2:5", relative.display())));
        assert!(!rendered.contains(&path.to_string_lossy().into_owned()));
    }

    #[test]
    fn unavailable_source_under_cwd_uses_cwd_relative_path() {
        let cwd = std::env::current_dir().unwrap();
        let (root, sources, envelope) = fixture_at(tempfile::tempdir_in(&cwd).unwrap());
        let path = root.path().join("src/lib.rs");
        std::fs::remove_file(&path).unwrap();
        let relative = path.strip_prefix(&cwd).unwrap();
        let rendered = sources.render_envelope(&envelope, false);
        assert!(rendered.contains(&format!("--> {} bytes 16..19", relative.display())));
        assert!(rendered.contains("source file is unavailable"));
    }

    #[test]
    fn unavailable_cwd_keeps_absolute_path() {
        let root = tempfile::tempdir().unwrap();
        let path = root.path().join("src/lib.rs");
        assert_eq!(path_from_cwd(&path, None), path);
    }

    #[test]
    fn source_outside_cwd_keeps_absolute_path() {
        let root = tempfile::tempdir().unwrap();
        let path = root.path().join("src/lib.rs");
        let cwd = root.path().join("another-package");
        assert_eq!(path_from_cwd(&path, Some(&cwd)), path);
    }

    #[test]
    fn located_error_with_notes() {
        let (root, sources, mut envelope) = fixture();
        envelope.notes = vec!["first rule: first".into(), "second rule: second".into()];
        expect![[r"
            error[krs::analysis::overlapping-rule-heads]: rule heads overlap
             --> <package>/src/lib.rs:2:5
              |
            2 |     Foo,
              |     ^^^
              |
              = note: first rule: first
              = note: second rule: second"]]
        .assert_eq(&render_fixture(&root, &sources, &envelope));
    }

    #[test]
    fn located_error_with_help_after_notes() {
        let (root, sources, mut envelope) = fixture();
        envelope.notes = vec!["a note".into()];
        envelope.help = vec!["remove `()` at src/lib.rs:2:8".into()];
        expect![[r"
            error[krs::analysis::overlapping-rule-heads]: rule heads overlap
             --> <package>/src/lib.rs:2:5
              |
            2 |     Foo,
              |     ^^^
              |
              = note: a note
              = help: remove `()` at src/lib.rs:2:8"]]
        .assert_eq(&render_fixture(&root, &sources, &envelope));
    }

    #[test]
    fn located_warning() {
        let (root, sources, mut envelope) = fixture();
        envelope.severity = DiagnosticSeverity::Warning;
        expect![[r"
            warning[krs::analysis::overlapping-rule-heads]: rule heads overlap
             --> <package>/src/lib.rs:2:5
              |
            2 |     Foo,
              |     ^^^"]]
        .assert_eq(&render_fixture(&root, &sources, &envelope));
    }

    #[test]
    fn unlocated_diagnostic() {
        let mut envelope = DiagnosticEnvelope::unlocated(
            DiagnosticStage::Analysis,
            OVERLAPPING_RULE_HEADS,
            "rule heads overlap",
        );
        expect!["error[krs::analysis::overlapping-rule-heads]: rule heads overlap"]
            .assert_eq(&DiagnosticSources::default().render_envelope(&envelope, false));
        envelope.item = Some("FIXTURE::step (rule)".to_owned());
        expect![[r"
            error[krs::analysis::overlapping-rule-heads]: rule heads overlap
              |
              = note: in FIXTURE::step (rule)"]]
        .assert_eq(&DiagnosticSources::default().render_envelope(&envelope, false));
    }

    #[test]
    fn internal_code_is_rendered_as_a_krs_bug() {
        let envelope = DiagnosticEnvelope::unlocated(
            DiagnosticStage::Analysis,
            krs_diagnostic::codes::analysis::INVALID_SEMANTIC_THEORY,
            "declared variables must exactly match sentence uses",
        );
        assert_eq!(envelope.kind, CodeKind::Internal);
        expect![[r"
            error[krs::analysis::invalid-semantic-theory]: internal error (a KRS bug): declared variables must exactly match sentence uses
              |
              = help: this is a bug in KRS, not in the program: please report it with the source that reached it"]]
        .assert_eq(&DiagnosticSources::default().render_envelope(&envelope, false));
    }

    #[test]
    fn labels_are_annotated_in_the_primary_snippet() {
        let (root, sources, mut envelope) = fixture();
        let file = envelope.authored_range.as_ref().unwrap().file.clone();
        envelope.labels = vec![
            DiagnosticLabel {
                range: SourceRange::new(file.clone(), 5, 9).unwrap(),
                message: Some("the earlier arm also applies".to_owned()),
            },
            DiagnosticLabel {
                range: SourceRange::new(file, 0, 4).unwrap(),
                message: None,
            },
        ];
        expect![[r"
            error[krs::analysis::overlapping-rule-heads]: rule heads overlap
             --> <package>/src/lib.rs:2:5
              |
            1 | enum Term {
              | ---- ---- the earlier arm also applies
            2 |     Foo,
              |     ^^^"]]
        .assert_eq(&render_fixture(&root, &sources, &envelope));
        std::fs::write(root.path().join("src/lib.rs"), "enum Term { Bar }\n").unwrap();
        let rendered = render_fixture(&root, &sources, &envelope);
        assert!(rendered.contains("src/lib.rs bytes 16..19"));
        assert!(rendered.contains("src/lib.rs bytes 5..9"));
        assert!(rendered.contains("src/lib.rs bytes 0..4"));
    }

    #[test]
    fn stale_source() {
        let (root, sources, envelope) = fixture();
        std::fs::write(root.path().join("src/lib.rs"), "enum Term { Bar }\n").unwrap();
        expect![[r"
            error[krs::analysis::overlapping-rule-heads]: rule heads overlap
             --> <package>/src/lib.rs bytes 16..19
              = note: source changed since the diagnostic was produced"]]
        .assert_eq(&render_fixture(&root, &sources, &envelope));
    }

    #[test]
    fn generated_range_note() {
        let (root, sources, mut envelope) = fixture();
        envelope.generated_range = Some(crate::DiagnosticGeneratedRange {
            artifact: "definition.k".into(),
            start_line: 7,
            start_column: 2,
            end_line: 8,
            end_column: 12,
        });
        expect![[r"
            error[krs::analysis::overlapping-rule-heads]: rule heads overlap
             --> <package>/src/lib.rs:2:5
              |
            2 |     Foo,
              |     ^^^
              |
              = note: generated definition.k:7:2..8:12"]]
        .assert_eq(&render_fixture(&root, &sources, &envelope));
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
        envelope.authored_range.as_mut().unwrap().end_byte = 100;
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
            envelope
                .authored_range
                .as_ref()
                .unwrap()
                .file
                .package()
                .clone(),
            "src/lib.rs",
            Sha256Digest::from_bytes(Sha256::digest(source.as_bytes()).into()),
        )
        .unwrap();
        envelope.authored_range = Some(SourceRange::new(file, 6, 9).unwrap());
        let rendered = sources.render_envelope(&envelope, false);
        assert!(rendered.contains("src/lib.rs:1:6"));
        assert!(rendered.contains("// λ Foo"));
    }
}
