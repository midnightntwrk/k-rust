//! Joining backend rule identities to authored KRS sources.

use std::collections::BTreeMap;

use krs_ir::{LineIndex, NodeOrigin, OriginFrame, SourceFileId, SourceRange};
use krs_k_rust::{Author, EmittedProvenance, InputSentenceKind};

use crate::{SourceText, report::SourceSpan, report::StepOrigin};

/// Positions authored ranges in source text supplied by the caller, caching one line index per file.
pub(crate) struct Origins {
    sources: Option<SourceText>,
    lines: BTreeMap<SourceFileId, Option<LineIndex>>,
}

impl Origins {
    pub(crate) fn new(sources: Option<SourceText>) -> Self {
        Self {
            sources,
            lines: BTreeMap::new(),
        }
    }

    /// The authored span of a KRS origin, positioned when its source text is available.
    pub(crate) fn span(&mut self, origin: &NodeOrigin) -> Option<SourceSpan> {
        let range = authored_range(origin)?;
        let (line, column) = self.position(range).unzip();
        Some(SourceSpan {
            file: range.file.package_relative_path().to_owned(),
            line,
            column,
        })
    }

    fn position(&mut self, range: &SourceRange) -> Option<(u32, u32)> {
        let sources = self.sources.as_ref()?;
        let index = self
            .lines
            .entry(range.file.clone())
            .or_insert_with(|| sources(&range.file).map(|text| LineIndex::new(&text)))
            .as_ref()?;
        let position = index
            .byte_to_position(usize::try_from(range.start_byte).ok()?)
            .ok()?;
        Some((position.line(), position.scalar_column()))
    }

    /// Classify the provenance of one emitted rule identity.
    ///
    /// A rule authored as a KRS rule is `Authored`. A rule the native frontend derived from another
    /// KRS sentence (a strict production's heating and cooling rules, a context) is `Generated` from
    /// that sentence. A rule of K's builtin closure is `Builtin`.
    pub(crate) fn step_origin(&mut self, provenance: Option<&EmittedProvenance>) -> StepOrigin {
        let Some(provenance) = provenance else {
            return StepOrigin::Generated {
                pass: "unknown".to_owned(),
                from: None,
            };
        };
        if let Some(pass) = provenance.generated_by() {
            return StepOrigin::Generated {
                pass: pass.as_str().to_owned(),
                from: None,
            };
        }
        match provenance.authors().first() {
            Some(Author::Krs { kind, origin, .. }) => {
                let span = self.span(origin);
                match kind {
                    InputSentenceKind::Rule | InputSentenceKind::Claim => match span {
                        Some(span) => StepOrigin::Authored {
                            file: span.file,
                            line: span.line,
                            column: span.column,
                        },
                        None => StepOrigin::Generated {
                            pass: "unknown".to_owned(),
                            from: None,
                        },
                    },
                    other => StepOrigin::Generated {
                        pass: generating_kind(*other).to_owned(),
                        from: span,
                    },
                }
            }
            Some(Author::Builtin { module, .. }) => StepOrigin::Builtin {
                module: module.clone(),
            },
            None => StepOrigin::Generated {
                pass: "unknown".to_owned(),
                from: None,
            },
        }
    }
}

/// The pass that turns a non-rule input sentence into rules.
const fn generating_kind(kind: InputSentenceKind) -> &'static str {
    match kind {
        InputSentenceKind::Production => "strict",
        InputSentenceKind::Context => "context",
        InputSentenceKind::ContextAlias => "context-alias",
        InputSentenceKind::Configuration => "configuration",
        InputSentenceKind::SyntaxSort
        | InputSentenceKind::SortSynonym
        | InputSentenceKind::SyntaxLexical
        | InputSentenceKind::SyntaxAssociativity
        | InputSentenceKind::SyntaxPriority
        | InputSentenceKind::Rule
        | InputSentenceKind::Claim
        | InputSentenceKind::Bubble => "frontend",
    }
}

/// The first authored frame of an origin stack.
pub(crate) fn authored_range(origin: &NodeOrigin) -> Option<&SourceRange> {
    origin
        .origin()
        .frames()
        .iter()
        .find_map(|frame| match frame {
            OriginFrame::Ranged { range, .. } if frame.is_authored() => Some(range),
            _ => None,
        })
}
