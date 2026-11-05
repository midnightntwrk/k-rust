//! Joining backend rule identities to authored KRS sources.

use std::collections::BTreeMap;

use krs_ir::{LineIndex, NodeOrigin, OriginFrame, SourceFileId, SourceRange};
use krs_k_rust::{Author, EmittedProvenance, InputSentenceKind};

use crate::{SourceText, report::SourceSpan, report::StepOrigin};

/// Positions authored ranges in source text supplied by the caller, caching one line index per file.
///
/// It is the one positioning of an authored origin: `krs run --trace` and the claims of a report
/// place a step's rule by it, and `krs kink` places every rule a document names by it, so the
/// two cannot place a sentence differently.
pub struct Origins {
    sources: Option<SourceText>,
    lines: BTreeMap<SourceFileId, Option<LineIndex>>,
}

impl Origins {
    /// Origins positioned in the text `sources` returns, or only named by file without it.
    #[must_use]
    pub fn new(sources: Option<SourceText>) -> Self {
        Self {
            sources,
            lines: BTreeMap::new(),
        }
    }

    /// The authored span of a KRS origin (its first authored frame), positioned at the range's
    /// start when its source text is available; `None` when no frame is authored.
    pub fn span(&mut self, origin: &NodeOrigin) -> Option<SourceSpan> {
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

/// The KRS item that wrote an emitted rule identity, with the package that declares it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ItemPath {
    /// The declaring package's K namespace, which tells the definition's packages apart.
    pub(crate) namespace: String,
    /// The declaring package's Rust crate name: its Cargo name with `-` written `_`.
    pub(crate) krate: String,
    /// The item's Rust path below its crate root (`interrupt::boundary_fetch`, `Arith::Add`
    /// for a variant of the enum family `Arith`).
    pub(crate) path: String,
}

/// The KRS item that wrote an emitted rule identity ([`ItemPath`]): the item the first frame of
/// its first KRS author's origin that names an authored item names. An item whose name holds
/// KRS's reserved marker (`__krs_`) is one the expansion generated, such as a production's
/// grammar registration, which no author writes and no Rust path of the source names; the
/// origin names the authored item it serves in a later frame (a strict variant's heat and cool
/// rules name the variant once the production is lowered). `None` for a rule of K's builtin
/// closure, or one whose origin names no authored item.
pub(crate) fn item_path(provenance: Option<&EmittedProvenance>) -> Option<ItemPath> {
    let Some(Author::Krs { origin, .. }) = provenance?.authors().first() else {
        return None;
    };
    let item = origin
        .origin()
        .frames()
        .iter()
        .find_map(|frame| match frame {
            OriginFrame::Ranged { item, .. } | OriginFrame::Transformation { item, .. } => item
                .as_ref()
                .filter(|item| !item.item_name().starts_with(krs_ir::ir::RESERVED_MARKER)),
            OriginFrame::Inserted { .. } => None,
        })?;
    // A variant of a constructor family is named in Rust through its enum, which its identity
    // holds as its disambiguator, never in its module path.
    let family = item
        .disambiguator()
        .strip_prefix(krs_ir::ENUM_VARIANT_DISAMBIGUATOR_PREFIX);
    let path = item
        .module_path()
        .iter()
        .map(String::as_str)
        .chain(family)
        .chain([item.item_name()])
        .collect::<Vec<_>>()
        .join("::");
    let package = item.package();
    Some(ItemPath {
        namespace: package.k_namespace().to_owned(),
        krate: package.cargo_name().replace('-', "_"),
        path,
    })
}

/// The Rust path below its crate root of the KRS item that wrote an emitted rule identity
/// ([`item_path`]).
pub(crate) fn item(provenance: Option<&EmittedProvenance>) -> Option<String> {
    item_path(provenance).map(|item| item.path)
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
