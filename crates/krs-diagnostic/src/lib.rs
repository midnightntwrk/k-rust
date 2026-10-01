//! Located diagnostics shared by KRS producers and their renderers.
//!
//! This crate depends on `krs-ir` without features because that crate owns source coordinates.
//! `krs-ir` must not depend on this crate; implementations of [`ToDiagnostic`] for its errors belong here.
//! The optional `proc-macro2` feature preserves macro spans without requiring them for other hosts.

use std::borrow::Cow;
use std::fmt;

use krs_ir::{ByteRange, DisplayPath, SourceMapKey, SourceRange};
use serde::Serialize;

pub mod codes;
pub mod envelope;

/// An opaque diagnostic code, serialized as its string spelling.
///
/// KRS-owned codes must come from [`codes`].
/// Registered codes borrow static spellings and do not allocate when cloned.
/// Forwarded codes must use [`Code::foreign`] and are not registered.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(transparent)]
pub struct Code(Cow<'static, str>);

impl Code {
    const fn registered(spelling: &'static str) -> Self {
        Self(Cow::Borrowed(spelling))
    }

    /// Carries a code owned by another producer, such as rustc or a native frontend.
    ///
    /// The spelling is forwarded unchanged and is not added to the KRS registry.
    #[must_use]
    pub fn foreign(spelling: impl Into<Cow<'static, str>>) -> Self {
        Self(spelling.into())
    }

    /// Returns the spelling for renderers and existing string-based records.
    #[must_use]
    pub const fn as_str(&self) -> &str {
        match &self.0 {
            Cow::Borrowed(spelling) => spelling,
            Cow::Owned(spelling) => spelling.as_str(),
        }
    }
}

impl fmt::Display for Code {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}

/// The importance of a diagnostic.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Severity {
    /// A failure that prevents the requested operation.
    Error,
    /// A concern that does not prevent the requested operation.
    Warning,
}

/// Returns a nonempty token span range in the producer's input text.
/// Empty spans do not establish authored coordinates.
#[cfg(feature = "proc-macro2")]
#[must_use]
pub fn span_byte_range(span: proc_macro2::Span) -> Option<ByteRange> {
    let range = span.byte_range();
    ByteRange::new(range.start, range.end)
        .ok()
        .filter(|range| !range.is_empty())
}

/// A diagnostic location retained in the producer's coordinate system.
#[derive(Clone, Debug)]
pub enum Location {
    /// The producer has no location.
    None,
    /// A procedural-macro span in the producer's token-stream coordinates, retained for a macro renderer.
    #[cfg(feature = "proc-macro2")]
    Span(proc_macro2::Span),
    /// A half-open UTF-8 byte range in the exact input text given to the producer.
    /// The caller must supply the file containing that input text through [`Diagnostic::with_file`].
    Range(ByteRange),
    /// A half-open UTF-8 byte range within a file named by its package-relative display path.
    File {
        /// Normalized display path of the file.
        path: DisplayPath,
        /// Half-open UTF-8 byte range within the file.
        range: ByteRange,
    },
    /// A half-open UTF-8 byte range within the exact source-file revision identified by the range.
    Source(SourceRange),
    /// A key in the Definition source map supplied to the renderer.
    Definition(SourceMapKey),
    /// Exact downstream line/column range, retained without inferring authored coordinates.
    Generated(envelope::DiagnosticGeneratedRange),
}

/// A location and optional explanation attached to a diagnostic.
#[derive(Clone, Debug)]
pub struct Label {
    /// The location in the producer's coordinate system.
    pub location: Location,
    /// An explanation specific to this location.
    pub message: Option<String>,
}

impl Label {
    /// Creates a label without a location-specific explanation.
    #[must_use]
    pub const fn new(location: Location) -> Self {
        Self {
            location,
            message: None,
        }
    }

    /// Adds a location-specific explanation.
    #[must_use]
    pub fn with_message(mut self, message: impl Into<String>) -> Self {
        self.message = Some(message.into());
        self
    }
}

/// A diagnostic independent of any renderer or wire format.
#[derive(Clone, Debug)]
pub struct Diagnostic {
    /// Stable code supplied by the producer.
    pub code: Code,
    /// Whether the diagnostic prevents the operation.
    pub severity: Severity,
    /// The principal explanation.
    pub message: String,
    /// The principal location.
    pub primary: Label,
    /// Additional locations, in producer order.
    pub secondary: Vec<Label>,
    /// Additional explanations, in producer order.
    pub notes: Vec<String>,
}

impl Diagnostic {
    /// Creates an error with one primary location.
    #[must_use]
    pub fn error(code: Code, message: impl Into<String>, location: Location) -> Self {
        Self {
            code,
            severity: Severity::Error,
            message: message.into(),
            primary: Label::new(location),
            secondary: Vec::new(),
            notes: Vec::new(),
        }
    }

    /// Attaches the file containing the producer's input text to all input-relative ranges.
    /// Primary and secondary [`Location::Range`] labels become [`Location::File`] labels.
    /// Other locations retain their producer coordinates and file identities.
    #[must_use]
    pub fn with_file(mut self, path: &DisplayPath) -> Self {
        for label in std::iter::once(&mut self.primary).chain(&mut self.secondary) {
            if let Location::Range(range) = label.location {
                label.location = Location::File {
                    path: path.clone(),
                    range,
                };
            }
        }
        self
    }

    /// Appends an explanatory note.
    #[must_use]
    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.notes.push(note.into());
        self
    }

    /// Appends a secondary location and its optional explanation.
    #[must_use]
    pub fn with_secondary(mut self, label: Label) -> Self {
        self.secondary.push(label);
        self
    }
}

/// Converts a user-facing error to the shared diagnostic model.
///
/// Every user-facing error type must implement this trait so that its code and location are properties of the type, rather than choices made by its caller.
pub trait ToDiagnostic {
    /// Returns the error's code, severity, message, and locations.
    fn to_diagnostic(&self) -> Diagnostic;
}

#[cfg(test)]
mod tests;
