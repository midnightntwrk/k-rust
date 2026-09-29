//! Source ranges and layered provenance.

use std::error::Error;
use std::fmt;

use serde::{Deserialize, Deserializer, Serialize};

use crate::{ByteRange, SourceFileId, StableItemId};

/// A half-open byte range in one exact source-file revision.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub struct SourceRange {
    /// Source file containing the range.
    pub file: SourceFileId,
    /// Inclusive UTF-8 byte offset.
    pub start_byte: u32,
    /// Exclusive UTF-8 byte offset.
    pub end_byte: u32,
}

impl SourceRange {
    /// Creates a source range from checked in-memory byte offsets.
    ///
    /// # Errors
    ///
    /// Returns an error when either offset exceeds the `u32` wire limit.
    pub fn from_byte_range(
        file: SourceFileId,
        range: ByteRange,
    ) -> Result<Self, SourceRangeOverflow> {
        let start_byte = u32::try_from(range.start()).map_err(|_| SourceRangeOverflow)?;
        let end_byte = u32::try_from(range.end()).map_err(|_| SourceRangeOverflow)?;
        Ok(Self {
            file,
            start_byte,
            end_byte,
        })
    }

    /// Returns the checked in-memory byte range.
    ///
    /// # Errors
    ///
    /// Returns an error if wire data contains reversed offsets.
    pub fn byte_range(&self) -> Result<ByteRange, crate::CoordinateError> {
        ByteRange::new(self.start_byte as usize, self.end_byte as usize)
    }

    /// Creates a half-open range, rejecting reversed offsets.
    ///
    /// # Errors
    ///
    /// Returns [`SourceRangeError`] when `start_byte` is after `end_byte`.
    pub fn new(
        file: SourceFileId,
        start_byte: u32,
        end_byte: u32,
    ) -> Result<Self, SourceRangeError> {
        if ByteRange::new(start_byte as usize, end_byte as usize).is_err() {
            return Err(SourceRangeError {
                start_byte,
                end_byte,
            });
        }
        Ok(Self {
            file,
            start_byte,
            end_byte,
        })
    }
}

/// A source byte offset exceeds the `u32` wire limit.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SourceRangeOverflow;

impl fmt::Display for SourceRangeOverflow {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("source byte offset exceeds protocol limits")
    }
}

impl Error for SourceRangeOverflow {}

/// A reversed source range.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SourceRangeError {
    /// Supplied inclusive start.
    pub start_byte: u32,
    /// Supplied exclusive end.
    pub end_byte: u32,
}

impl fmt::Display for SourceRangeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "source range starts at {} but ends at {}",
            self.start_byte, self.end_byte
        )
    }
}

impl Error for SourceRangeError {}

/// Kind of frame backed by a concrete source or generated-output range.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RangedOriginKind {
    /// Tokens written directly by the author.
    Authored,
    /// Attribute or function-like macro invocation containing authored tokens.
    MacroInvocation,
    /// A range in emitted K or another generated artifact.
    GeneratedArtifact,
    /// A diagnostic range reported by a downstream frontend.
    FrontendDiagnostic,
}

impl RangedOriginKind {
    pub(crate) const fn code(self) -> u8 {
        match self {
            Self::Authored => 0,
            Self::MacroInvocation => 1,
            Self::GeneratedArtifact => 2,
            Self::FrontendDiagnostic => 3,
        }
    }

    pub(crate) fn from_code(code: u8) -> Option<Self> {
        match code {
            0 => Some(Self::Authored),
            1 => Some(Self::MacroInvocation),
            2 => Some(Self::GeneratedArtifact),
            3 => Some(Self::FrontendDiagnostic),
            _ => None,
        }
    }
}

/// Kind of logical transformation that has no honest source range of its own.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TransformationOriginKind {
    /// A field in the descriptor generated from the invocation.
    GeneratedDescriptor,
    /// A node produced by KRS semantic analysis.
    SemanticIr,
    /// A sentence or term in backend-independent Definition IR.
    DefinitionIr,
}

impl TransformationOriginKind {
    pub(crate) const fn code(self) -> u8 {
        match self {
            Self::GeneratedDescriptor => 4,
            Self::SemanticIr => 5,
            Self::DefinitionIr => 6,
        }
    }

    pub(crate) fn from_code(code: u8) -> Option<Self> {
        match code {
            4 => Some(Self::GeneratedDescriptor),
            5 => Some(Self::SemanticIr),
            6 => Some(Self::DefinitionIr),
            _ => None,
        }
    }
}

/// Collector frame shape and its kind, derived from its wire code.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum FrameKind {
    Ranged(RangedOriginKind),
    Transformation(TransformationOriginKind),
}

impl FrameKind {
    pub(crate) fn from_code(code: u8) -> Option<Self> {
        RangedOriginKind::from_code(code)
            .map(Self::Ranged)
            .or_else(|| TransformationOriginKind::from_code(code).map(Self::Transformation))
    }
}

/// One link in a source-to-generated provenance chain.
///
/// The wire representation explicitly distinguishes locations that have real
/// byte ranges from logical transforms. Semantic and Definition IR frames can
/// therefore never acquire a fabricated source range merely to satisfy the
/// data model.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(tag = "frame_type", rename_all = "snake_case")]
pub enum OriginFrame {
    /// Authored source, macro invocation, artifact, or diagnostic location.
    Ranged {
        /// Role of the concrete range.
        kind: RangedOriginKind,
        /// Content-addressed source or generated-artifact byte range.
        range: SourceRange,
        /// Stable item associated with the frame, when applicable.
        #[serde(skip_serializing_if = "Option::is_none")]
        item: Option<StableItemId>,
        /// Stable explanatory label, artifact name, or diagnostic code.
        #[serde(skip_serializing_if = "Option::is_none")]
        label: Option<String>,
    },
    /// Descriptor, semantic IR, or Definition IR transform metadata.
    Transformation {
        /// Logical transformation performed at this layer.
        kind: TransformationOriginKind,
        /// Stable item associated with the transform, when applicable.
        #[serde(skip_serializing_if = "Option::is_none")]
        item: Option<StableItemId>,
        /// Stable field or node identifier, not a rendered diagnostic.
        #[serde(skip_serializing_if = "Option::is_none")]
        label: Option<String>,
    },
}

impl OriginFrame {
    /// Creates an authored frame for the first position in an origin stack.
    #[must_use]
    pub fn authored(range: SourceRange) -> Self {
        Self::Ranged {
            kind: RangedOriginKind::Authored,
            range,
            item: None,
            label: None,
        }
    }

    /// Returns whether this is a ranged authored-source frame.
    #[must_use]
    pub const fn is_authored(&self) -> bool {
        matches!(
            self,
            Self::Ranged {
                kind: RangedOriginKind::Authored,
                ..
            }
        )
    }
}

/// Ordered provenance from the authored token toward later representations.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(transparent)]
pub struct OriginStack(Vec<OriginFrame>);

impl OriginStack {
    /// Starts a non-empty origin stack at an authored frame.
    #[must_use]
    pub fn authored(range: SourceRange) -> Self {
        Self(vec![OriginFrame::authored(range)])
    }

    /// Validates frames received across the collector protocol.
    ///
    /// # Errors
    ///
    /// Returns [`OriginStackError`] when the stack is empty or does not begin
    /// with the authored token from which later frames were derived.
    pub fn try_from_frames(frames: Vec<OriginFrame>) -> Result<Self, OriginStackError> {
        match frames.first() {
            None => Err(OriginStackError::Empty),
            Some(frame) if !frame.is_authored() => Err(OriginStackError::FirstFrameNotAuthored),
            Some(_) => Ok(Self(frames)),
        }
    }

    /// Appends a transformation toward the generated representation.
    pub fn push(&mut self, frame: OriginFrame) {
        self.0.push(frame);
    }

    /// Returns frames in authored-to-generated order.
    #[must_use]
    pub fn frames(&self) -> &[OriginFrame] {
        &self.0
    }
}

impl<'de> Deserialize<'de> for OriginStack {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let frames = Vec::<OriginFrame>::deserialize(deserializer)?;
        Self::try_from_frames(frames).map_err(serde::de::Error::custom)
    }
}

/// A provenance chain that cannot trace back to an authored token.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OriginStackError {
    /// The chain had no frames.
    Empty,
    /// The first frame described a later transformation.
    FirstFrameNotAuthored,
}

impl fmt::Display for OriginStackError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty => formatter.write_str("origin stack must not be empty"),
            Self::FirstFrameNotAuthored => {
                formatter.write_str("origin stack must begin with an authored frame")
            }
        }
    }
}

impl Error for OriginStackError {}

#[cfg(test)]
mod tests {
    use super::{FrameKind, RangedOriginKind, TransformationOriginKind};

    /// Changing a frame code requires advancing `collector::VERSION`.
    #[test]
    fn collector_frame_codes() {
        let ranged = [
            RangedOriginKind::Authored,
            RangedOriginKind::MacroInvocation,
            RangedOriginKind::GeneratedArtifact,
            RangedOriginKind::FrontendDiagnostic,
        ];
        let transformations = [
            TransformationOriginKind::GeneratedDescriptor,
            TransformationOriginKind::SemanticIr,
            TransformationOriginKind::DefinitionIr,
        ];
        for kind in ranged {
            let expected = match kind {
                RangedOriginKind::Authored => 0,
                RangedOriginKind::MacroInvocation => 1,
                RangedOriginKind::GeneratedArtifact => 2,
                RangedOriginKind::FrontendDiagnostic => 3,
            };
            assert_eq!(kind.code(), expected);
            assert_eq!(RangedOriginKind::from_code(kind.code()), Some(kind));
            assert_eq!(
                FrameKind::from_code(kind.code()),
                Some(FrameKind::Ranged(kind))
            );
            assert_eq!(TransformationOriginKind::from_code(kind.code()), None);
        }
        for kind in transformations {
            let expected = match kind {
                TransformationOriginKind::GeneratedDescriptor => 4,
                TransformationOriginKind::SemanticIr => 5,
                TransformationOriginKind::DefinitionIr => 6,
            };
            assert_eq!(kind.code(), expected);
            assert_eq!(TransformationOriginKind::from_code(kind.code()), Some(kind));
            assert_eq!(
                FrameKind::from_code(kind.code()),
                Some(FrameKind::Transformation(kind))
            );
            assert_eq!(RangedOriginKind::from_code(kind.code()), None);
        }
        for code in [7, u8::MAX] {
            assert_eq!(RangedOriginKind::from_code(code), None);
            assert_eq!(TransformationOriginKind::from_code(code), None);
            assert_eq!(FrameKind::from_code(code), None);
        }
    }
}
