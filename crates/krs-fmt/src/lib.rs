//! Canonical formatting for Rust files containing KRS macro DSL bodies.
//!
//! Rustfmt owns ordinary Rust layout. KRS rule bodies are elided before that
//! subprocess runs, formatted through the shared `krs-syntax` parser, and
//! spliced back at the invocation's Rustfmt-selected indentation.

mod rules;
mod rustfmt;

use std::error::Error;
use std::fmt;
use std::path::{Path, PathBuf};
use std::str::FromStr;

pub use rules::TrailingCommentStyle;

/// Rust language edition passed to Rustfmt.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum Edition {
    /// Rust 2015.
    E2015,
    /// Rust 2018.
    E2018,
    /// Rust 2021.
    E2021,
    /// Rust 2024.
    #[default]
    E2024,
}

impl fmt::Display for Edition {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::E2015 => "2015",
            Self::E2018 => "2018",
            Self::E2021 => "2021",
            Self::E2024 => "2024",
        })
    }
}

impl FromStr for Edition {
    type Err = String;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        match value {
            "2015" => Ok(Self::E2015),
            "2018" => Ok(Self::E2018),
            "2021" => Ok(Self::E2021),
            "2024" => Ok(Self::E2024),
            _ => Err(format!("unknown Rust edition `{value}`")),
        }
    }
}

/// Formatter policy shared by file, stdin, editor, and CI entry points.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FormatOptions {
    /// Rust language edition for the input.
    pub edition: Edition,
    /// Layout policy for trailing comments on aligned single-cell clauses.
    pub trailing_comments: TrailingCommentStyle,
    /// Run and compose with the installed Rustfmt executable.
    pub rustfmt: bool,
    /// Format twice and require byte-identical output.
    pub check_idempotence: bool,
    /// Require direct Rustfmt to preserve the final formatted bytes.
    pub check_rustfmt_fixpoint: bool,
}

impl Default for FormatOptions {
    fn default() -> Self {
        Self {
            edition: Edition::default(),
            trailing_comments: TrailingCommentStyle::AlignedColumn,
            rustfmt: true,
            check_idempotence: true,
            check_rustfmt_fixpoint: true,
        }
    }
}

/// One successfully formatted file and whether its bytes changed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FormattedFile {
    /// Authored file path.
    pub path: PathBuf,
    /// Canonical output bytes.
    pub output: String,
    /// Whether output differs from the input bytes.
    pub changed: bool,
}

/// Stable formatter failure categories.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum FormatErrorKind {
    /// The input was not valid Rust syntax.
    RustSyntax,
    /// A KRS DSL body did not parse under `krs-syntax`.
    DslSyntax,
    /// A `rules!` invocation used parentheses or brackets.
    NonBraceRules,
    /// Rustfmt could not be started or rejected the elided source.
    Rustfmt,
    /// Formatting changed the token payload of a KRS DSL body.
    TokenPayloadChanged,
    /// Formatting dropped, duplicated, or reordered a line comment.
    CommentPayloadChanged,
    /// The formatted output no longer parsed.
    OutputDoesNotParse,
    /// A second formatter pass changed the first output.
    NonIdempotent,
    /// Direct Rustfmt changed the final KRS-formatted bytes.
    RustfmtFixpoint,
    /// A file could not be read or written.
    Io,
}

/// Typed formatter diagnostic.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FormatError {
    kind: FormatErrorKind,
    detail: String,
}

impl FormatError {
    pub(crate) fn new(kind: FormatErrorKind, detail: impl Into<String>) -> Self {
        Self {
            kind,
            detail: detail.into(),
        }
    }

    /// Returns the stable formatter failure category.
    #[must_use]
    pub const fn kind(&self) -> FormatErrorKind {
        self.kind
    }

    /// Returns contextual diagnostic detail.
    #[must_use]
    pub fn detail(&self) -> &str {
        &self.detail
    }
}

impl fmt::Display for FormatError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.detail)
    }
}

impl Error for FormatError {}

/// Formats one complete Rust source string and checks the formatter oracles.
///
/// # Errors
///
/// Returns a typed parse, Rustfmt, payload, idempotence, or fixpoint failure.
pub fn format_source(source: &str, options: FormatOptions) -> Result<String, FormatError> {
    format_source_in(source, options, Path::new("."))
}

/// Formats source using Rustfmt configuration found from `directory`.
///
/// # Errors
///
/// Returns a typed parse, Rustfmt, payload, idempotence, or fixpoint failure.
pub fn format_source_in(
    source: &str,
    options: FormatOptions,
    directory: &Path,
) -> Result<String, FormatError> {
    let output = format_source_once(source, options, directory)?;
    rustfmt::validate_token_payload(source, &output)?;
    rustfmt::validate_comment_payload(source, &output)?;
    syn::parse_file(&output).map_err(|error| {
        FormatError::new(
            FormatErrorKind::OutputDoesNotParse,
            format!("formatted output is not Rust syntax: {error}"),
        )
    })?;
    if options.check_idempotence {
        let repeated = format_source_once(&output, options, directory)?;
        if repeated != output {
            return Err(FormatError::new(
                FormatErrorKind::NonIdempotent,
                "formatter output changed on the second pass",
            ));
        }
    }
    if options.rustfmt && options.check_rustfmt_fixpoint {
        let direct = rustfmt::run(&output, options.edition, directory)?;
        if direct != output {
            return Err(FormatError::new(
                FormatErrorKind::RustfmtFixpoint,
                "direct Rustfmt changed the final KRS-formatted output",
            ));
        }
    }
    Ok(output)
}

fn format_source_once(
    source: &str,
    options: FormatOptions,
    directory: &Path,
) -> Result<String, FormatError> {
    let elided = rustfmt::elide_rule_bodies(source)?;
    let rust = if options.rustfmt {
        rustfmt::run(&elided.source, options.edition, directory)?
    } else {
        elided.source
    };
    rustfmt::splice_rule_bodies(&rust, &elided.bodies, options.trailing_comments)
}

/// Formats one file without writing it.
///
/// # Errors
///
/// Returns an I/O or source-formatting failure.
pub fn format_file(path: &Path, options: FormatOptions) -> Result<FormattedFile, FormatError> {
    let source = std::fs::read_to_string(path).map_err(|error| {
        FormatError::new(
            FormatErrorKind::Io,
            format!("cannot read `{}`: {error}", path.display()),
        )
    })?;
    let directory = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let output = format_source_in(&source, options, directory)?;
    Ok(FormattedFile {
        path: path.to_path_buf(),
        changed: output != source,
        output,
    })
}

/// Renders a unified source diff for `--check` diagnostics.
#[must_use]
pub fn unified_diff(path: &Path, before: &str, after: &str) -> String {
    similar::TextDiff::from_lines(before, after)
        .unified_diff()
        .header(
            &format!("a/{}", path.display()),
            &format!("b/{}", path.display()),
        )
        .to_string()
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use proc_macro2::{Spacing, TokenStream, TokenTree};

    use super::*;

    #[test]
    fn source_uses_selected_rust_edition() {
        let source = "use std::{u8, u16};\n";
        let edition_2021 = FormatOptions {
            edition: Edition::E2021,
            ..FormatOptions::default()
        };
        assert_eq!(
            format_source(source, edition_2021).expect("format 2021 source"),
            "use std::{u16, u8};\n"
        );
        assert_eq!(
            format_source(source, FormatOptions::default()).expect("format 2024 source"),
            source
        );
    }

    #[test]
    fn readable_corpus_is_at_every_formatter_fixpoint() {
        let corpus = [
            (
                "readable IMP",
                include_str!("../../../tests/imp/rust-definition/src/imp.rs"),
            ),
            (
                "normative IMP",
                include_str!("../../../docs-plan/authoring-spec/imp.rs"),
            ),
            (
                "identity adversary",
                include_str!("../../../tests/imp/rust-definition/src/identity_adversary.rs"),
            ),
        ];
        for (name, source) in corpus {
            let output = format_source(source, FormatOptions::default())
                .unwrap_or_else(|error| panic!("format {name}: {error}"));
            assert_eq!(output, source, "{name} is not a formatter fixed point");
        }
    }

    #[test]
    fn rustfmt_may_normalize_host_punctuation_without_changing_dsl_payload() {
        let source = r"fn definition(
    first: i32,
    second: i32,
) {
    let _ = (first, second);
    k::rules! {
        for Expr;
        one: A(value) => value;
    }
}
";
        let output = format_source(source, FormatOptions::default()).expect("format host Rust");
        assert!(output.contains("fn definition(first: i32, second: i32)"));
        assert!(output.contains("one: A(value) => value;"));
    }

    #[test]
    fn label_rename_changes_only_the_label_and_table_padding() {
        let source = r"fn definition() {
    k::rules! {
        for Expr;

        short: A(x) => x;
        medium: Pair(lhs, rhs) => rhs;
    }
}
";
        let renamed = source.replace("short", "considerably_longer");
        let options = FormatOptions {
            rustfmt: false,
            check_rustfmt_fixpoint: false,
            ..FormatOptions::default()
        };
        let before = format_source(source, options).expect("format original labels");
        let after = format_source(&renamed, options).expect("format renamed label");
        expect_test::expect![[r"fn definition() {
    k::rules! {
        for Expr;

        short : A(x)           => x;
        medium: Pair(lhs, rhs) => rhs;
    }
}
"]]
        .assert_eq(&before);
        expect_test::expect![[r"fn definition() {
    k::rules! {
        for Expr;

        considerably_longer: A(x)           => x;
        medium             : Pair(lhs, rhs) => rhs;
    }
}
"]]
        .assert_eq(&after);
    }

    #[test]
    fn trailing_comment_policies_have_distinct_stable_snapshots() {
        let source = r"fn definition() {
    k::rules! {
        for Expr;
        use Op::*;

        short: A(x) => x; // first
        considerably_longer: Pair(lhs, rhs) => rhs; // second
    }
}
";
        let mut options = FormatOptions {
            rustfmt: false,
            check_rustfmt_fixpoint: false,
            ..FormatOptions::default()
        };
        let aligned = format_source(source, options).expect("aligned comments");
        options.trailing_comments = TrailingCommentStyle::FixedGutter;
        let gutter = format_source(source, options).expect("gutter comments");
        expect_test::expect![[r"fn definition() {
    k::rules! {
        for Expr;
        use Op::*;

        short              : A(x)           => x;    // first
        considerably_longer: Pair(lhs, rhs) => rhs;  // second
    }
}
"]]
        .assert_eq(&aligned);
        expect_test::expect![[r"fn definition() {
    k::rules! {
        for Expr;
        use Op::*;

        short              : A(x)           => x;  // first
        considerably_longer: Pair(lhs, rhs) => rhs;  // second
    }
}
"]]
        .assert_eq(&gutter);
    }

    #[test]
    fn interior_comments_normalize_to_leading_without_reordering() {
        let source = r"fn definition() {
    k::rules! {
        for Expr;

        // before
        one: A(
            // interior
            value
        ) => value; // trailing
    }
}
";
        let options = FormatOptions {
            rustfmt: false,
            check_rustfmt_fixpoint: false,
            ..FormatOptions::default()
        };
        let output = format_source(source, options).expect("comments survive formatting");
        let before = output.find("// before").expect("leading comment");
        let interior = output.find("// interior").expect("interior comment");
        let clause = output.find("one: A(value)").expect("formatted clause");
        let trailing = output.find("// trailing").expect("trailing comment");
        assert!(before < interior && interior < clause && clause < trailing);
    }

    #[test]
    fn reports_exact_non_doc_block_comment_range() {
        let source = r"fn definition() {
    k::rules! {
        for Expr;
        one: A(/* forbidden */ value) => value;
    }
}
";
        let options = FormatOptions {
            rustfmt: false,
            check_idempotence: false,
            check_rustfmt_fixpoint: false,
            ..FormatOptions::default()
        };
        let error = format_source(source, options).expect_err("block comment must fail");
        assert_eq!(error.kind(), FormatErrorKind::DslSyntax);
        let start = source.find("/* forbidden */").expect("comment start");
        assert!(error.detail().contains(&format!(
            "bytes {start}..{}",
            start + "/* forbidden */".len()
        )));
    }

    #[test]
    fn uuid_comments_survive_in_order_at_every_safe_token_boundary() {
        let source = r"fn definition() {
    k::rules! {
        for Expr;
        use Op::*;
        one: A(value) => f(value) where value: Value;
    }
}
";
        let stream = TokenStream::from_str(source).expect("tokenize fixture");
        let mut offsets = Vec::new();
        collect_safe_token_ends(stream, &mut offsets);
        offsets.sort_unstable();
        offsets.dedup();
        let options = FormatOptions {
            rustfmt: false,
            check_rustfmt_fixpoint: false,
            ..FormatOptions::default()
        };
        for (index, offset) in offsets.into_iter().enumerate() {
            let marker = format!("// KRS-FMT-UUID-{index:04}");
            let mut injected = source.to_owned();
            injected.insert_str(offset, &format!(" {marker}\n"));
            let output = format_source(&injected, options)
                .unwrap_or_else(|error| panic!("UUID injection at byte {offset} failed: {error}"));
            assert_eq!(output.matches(&marker).count(), 1, "byte {offset}");
        }
    }

    fn collect_safe_token_ends(stream: TokenStream, output: &mut Vec<usize>) {
        for token in stream {
            match token {
                TokenTree::Group(group) => {
                    output.push(group.span_open().byte_range().end);
                    collect_safe_token_ends(group.stream(), output);
                    output.push(group.span_close().byte_range().end);
                }
                TokenTree::Punct(punct) if punct.spacing() == Spacing::Joint => {}
                token => output.push(token.span().byte_range().end),
            }
        }
    }
}
