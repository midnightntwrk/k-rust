//! Generated Rust source with a generated-to-authored source map.
//!
//! A host outside a procedural macro (the browser expander) must hand rustc
//! text, not a `proc_macro::TokenStream`, so rustc's span channel is gone.
//! [`print_with_map`] prints an expansion exactly as the `proc_macro2`
//! fallback `Display` does and records, for every printed byte, where it came
//! from. Outside a procedural macro every token is a fallback token: a token
//! copied from the authored file keeps the span it received when the whole
//! file was lexed ([`AuthoredFile::lex`]), and a token the expansion
//! synthesized has the call-site span or a span in a re-parsed string.
//!
//! Each [`Segment`] carries one of the four classes of the BL-006 comparison
//! contract ([`MappingClass`]). A segment is [`MappingClass::ExactAuthored`]
//! only when its token's span lies in the authored file and the authored bytes
//! equal the printed text, so the map never assigns an authored range the
//! expansion did not copy from authored tokens.
//!
//! The printer never changes a token: its text equals the fallback
//! `TokenStream::to_string()` of the printed stream.

use std::ops::Range;

use proc_macro2::{Delimiter, LexError, Spacing, Span, TokenStream, TokenTree};

/// Version of the [`SourceMap`] format.
pub const SOURCE_MAP_VERSION: u32 = 1;

/// The `proc_macro2` fallback file of `Span::call_site()` spans.
const CALL_SITE_FILE: &str = "<unspecified>";

/// One authored source file, lexed as a single `proc_macro2` fallback file.
///
/// Only meaningful outside a procedural macro, where `proc_macro2` uses its
/// fallback implementation and spans locate bytes of lexed strings, and only
/// until `proc_macro2::extra::invalidate_current_thread_spans` runs.
#[derive(Clone, Debug)]
pub struct AuthoredFile {
    display_file: String,
    source: String,
    fallback_file: Option<String>,
}

impl AuthoredFile {
    /// Lexes `source` and returns the file with its tokens.
    ///
    /// The returned tokens are the only tokens whose spans locate authored
    /// bytes; parse macro inputs from them (for example with `syn::parse2`),
    /// not by lexing `source` again, which creates another fallback file.
    ///
    /// # Errors
    ///
    /// Returns the lexer error when `source` is not a Rust token stream.
    pub fn lex(display_file: &str, source: &str) -> Result<(Self, TokenStream), LexError> {
        let tokens: TokenStream = source.parse()?;
        let fallback_file = tokens
            .clone()
            .into_iter()
            .next()
            .map(|tree| tree.span().file());
        Ok((
            Self {
                display_file: display_file.to_owned(),
                source: source.to_owned(),
                fallback_file,
            },
            tokens,
        ))
    }

    /// The display file of the authored source (rustc `Span::file`).
    #[must_use]
    pub fn display_file(&self) -> &str {
        &self.display_file
    }

    /// The authored source text.
    #[must_use]
    pub fn source(&self) -> &str {
        &self.source
    }

    /// Whether `span` locates bytes of this file.
    #[must_use]
    pub fn contains(&self, span: Span) -> bool {
        self.fallback_file
            .as_deref()
            .is_some_and(|file| span.file() == file)
    }

    /// The authored UTF-8 byte range of `span`, if `span` lies in this file.
    #[must_use]
    pub fn byte_range(&self, span: Span) -> Option<Range<usize>> {
        self.contains(span).then(|| span.byte_range())
    }
}

/// The BL-006 classification of a generated range.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum MappingClass {
    /// The generated text equals the authored text of the recorded range.
    ExactAuthored,
    /// The generated text maps only to its invocation's call site.
    InvocationLevel,
    /// The generated text has no authored counterpart.
    GeneratedOnly,
    /// No source range exists; produced only by [`lookup`].
    Unmappable,
}

impl MappingClass {
    /// The BL-006 `classification_values` spelling.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::ExactAuthored => "exact-authored",
            Self::InvocationLevel => "invocation-level",
            Self::GeneratedOnly => "generated-only",
            Self::Unmappable => "unmappable",
        }
    }
}

/// Index of an [`Invocation`] in [`SourceMap::invocations`].
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct InvocationId(pub usize);

/// One expanded macro invocation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Invocation {
    /// This invocation's index.
    pub id: InvocationId,
    /// The `krs-macros` entry-point name, such as `sorts` or `init`.
    pub kind: String,
    /// Authored byte range of the call site: the invoking `#[...]` attribute,
    /// or a function-like macro's path through its closing delimiter.
    pub call_site: Range<usize>,
    /// Authored byte range the expansion replaces: the attributed item from
    /// its first outer attribute, or the whole macro invocation.
    pub replaced: Range<usize>,
    /// The invocation whose expansion contained this one.
    pub parent: Option<InvocationId>,
}

/// One classified range of the generated text.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Segment {
    /// Generated byte range.
    pub generated: Range<usize>,
    /// Classification.
    pub class: MappingClass,
    /// Authored byte range; present exactly for [`MappingClass::ExactAuthored`],
    /// whose authored text equals the generated text.
    pub authored: Option<Range<usize>>,
    /// Innermost invocation whose expansion printed this range; `None` for
    /// text outside every expansion.
    pub owner: Option<InvocationId>,
    /// For one invocation-level token whose span lies in the authored file but
    /// whose text differs from the authored bytes (such as an identifier
    /// formatted from an authored one): the authored range of that span.
    ///
    /// rustc reports a diagnostic at such a token at this range. The map does
    /// not classify it exact-authored, because the generated text is not the
    /// authored text; comparing with rustc is the diagnostic comparison's call.
    pub respanned: Option<Range<usize>>,
}

/// A map from generated byte ranges to authored byte ranges.
///
/// Segments are sorted, do not overlap, and cover the generated text. All
/// ranges are UTF-8 byte offsets.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceMap {
    /// [`SOURCE_MAP_VERSION`].
    pub version: u32,
    /// Path of the generated file that rustc compiles.
    pub generated_file: String,
    /// Display file of the authored source.
    pub authored_file: String,
    /// Expanded invocations, indexed by [`InvocationId`].
    pub invocations: Vec<Invocation>,
    /// Classified ranges covering the generated text.
    pub segments: Vec<Segment>,
}

/// Generated Rust source and its [`SourceMap`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GeneratedSource {
    /// The generated text.
    pub text: String,
    /// The map of `text`.
    pub map: SourceMap,
}

impl GeneratedSource {
    /// An empty generated file for `authored`.
    #[must_use]
    pub fn new(generated_file: &str, authored: &AuthoredFile) -> Self {
        Self {
            text: String::new(),
            map: SourceMap {
                version: SOURCE_MAP_VERSION,
                generated_file: generated_file.to_owned(),
                authored_file: authored.display_file().to_owned(),
                invocations: Vec::new(),
                segments: Vec::new(),
            },
        }
    }

    /// Records an invocation and returns its id.
    pub fn begin_invocation(
        &mut self,
        kind: &str,
        call_site: Range<usize>,
        replaced: Range<usize>,
        parent: Option<InvocationId>,
    ) -> InvocationId {
        let id = InvocationId(self.map.invocations.len());
        self.map.invocations.push(Invocation {
            id,
            kind: kind.to_owned(),
            call_site,
            replaced,
            parent,
        });
        id
    }

    /// Appends authored text unchanged, mapped by identity.
    ///
    /// # Panics
    ///
    /// Panics when `range` is not a range of `authored`'s source.
    pub fn copy_authored(&mut self, authored: &AuthoredFile, range: Range<usize>) {
        let text = &authored.source()[range.clone()];
        self.push(text, MappingClass::ExactAuthored, Some(range), None, None);
    }

    /// Appends text that no invocation expansion produced, such as a
    /// registration table.
    pub fn push_generated(&mut self, text: &str) {
        self.push(text, MappingClass::GeneratedOnly, None, None, None);
    }

    fn push(
        &mut self,
        text: &str,
        class: MappingClass,
        authored: Option<Range<usize>>,
        owner: Option<InvocationId>,
        respanned: Option<Range<usize>>,
    ) {
        if text.is_empty() {
            return;
        }
        let start = self.text.len();
        self.text.push_str(text);
        let generated = start..self.text.len();
        if let Some(last) = self.map.segments.last_mut()
            && last.generated.end == generated.start
            && last.class == class
            && last.owner == owner
            && last.respanned.is_none()
            && respanned.is_none()
        {
            match (&mut last.authored, &authored) {
                (None, None) => {
                    last.generated.end = generated.end;
                    return;
                }
                (Some(previous), Some(next)) if previous.end == next.start => {
                    previous.end = next.end;
                    last.generated.end = generated.end;
                    return;
                }
                _ => {}
            }
        }
        self.map.segments.push(Segment {
            generated,
            class,
            authored,
            owner,
            respanned,
        });
    }
}

/// An invocation nested in an expansion, printed in place of the tokens that
/// invoke it.
#[derive(Clone, Debug)]
pub struct Splice {
    /// Position of the first replaced token tree: the indices of the groups
    /// entered from the top of the enclosing stream, then the tree's index.
    pub at: Vec<usize>,
    /// Number of replaced token trees.
    pub len: usize,
    /// The nested invocation.
    pub owner: InvocationId,
    /// The nested invocation's expansion.
    pub tokens: TokenStream,
    /// Invocations nested in `tokens`.
    pub splices: Vec<Splice>,
}

/// Replaces every splice's tokens with its expansion, recursively; this is
/// the token stream that [`print_with_map`] prints.
#[must_use]
pub fn splice_tokens(stream: &TokenStream, splices: &[Splice]) -> TokenStream {
    fn level(stream: &TokenStream, splices: &[Splice], path: &mut Vec<usize>) -> TokenStream {
        let trees = stream.clone().into_iter().collect::<Vec<_>>();
        let mut output = TokenStream::new();
        let mut index = 0;
        while index < trees.len() {
            path.push(index);
            let splice = splices.iter().find(|splice| splice.at == *path);
            if let Some(splice) = splice {
                path.pop();
                output.extend(splice_tokens(&splice.tokens, &splice.splices));
                index += splice.len.max(1);
                continue;
            }
            let tree = match &trees[index] {
                TokenTree::Group(group) => {
                    let mut replaced = proc_macro2::Group::new(
                        group.delimiter(),
                        level(&group.stream(), splices, path),
                    );
                    replaced.set_span(group.span());
                    TokenTree::Group(replaced)
                }
                other => other.clone(),
            };
            path.pop();
            output.extend([tree]);
            index += 1;
        }
        output
    }
    level(stream, splices, &mut Vec::new())
}

/// The tokens one [`print_with_map`] call printed, by classification and, for
/// [`MappingClass::InvocationLevel`] tokens, by the kind of their span.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct PrintReport {
    /// Leaf tokens and delimiters printed.
    pub tokens: usize,
    /// Tokens classified [`MappingClass::ExactAuthored`].
    pub exact_authored: usize,
    /// Tokens with a `Span::call_site()` (or `mixed_site`) span.
    pub call_site: usize,
    /// Tokens whose span lies in a string the expansion re-parsed.
    pub reparsed: usize,
    /// Tokens whose span lies in the authored file but whose printed text
    /// differs from the authored bytes (for example an identifier formatted
    /// from an authored one, or a doc comment's attribute tokens).
    pub respanned: usize,
}

/// A stream that [`print_with_map`] cannot print without changing its tokens.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PrintError {
    /// A `Delimiter::None` group prints without delimiters, so the re-lexed
    /// text could parse with different operator precedence.
    NoneDelimitedGroup {
        /// The invocation that produced the group.
        owner: InvocationId,
    },
}

impl std::fmt::Display for PrintError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoneDelimitedGroup { owner } => write!(
                f,
                "invocation {} produced an invisible-delimited group, which has no text form",
                owner.0
            ),
        }
    }
}

impl std::error::Error for PrintError {}

/// Prints `stream`, the expansion of `owner`, with `splices` printed in place,
/// and appends the text and its segments to `out`.
///
/// The appended text equals `splice_tokens(stream, splices).to_string()` under
/// the `proc_macro2` fallback implementation; call it only outside a
/// procedural macro.
///
/// # Errors
///
/// Returns [`PrintError::NoneDelimitedGroup`] for a `Delimiter::None` group;
/// `out` then holds the text printed before it.
pub fn print_with_map(
    stream: &TokenStream,
    authored: &AuthoredFile,
    owner: InvocationId,
    splices: &[Splice],
    out: &mut GeneratedSource,
) -> Result<PrintReport, PrintError> {
    let mut printer = Printer {
        authored,
        out,
        report: PrintReport::default(),
    };
    let entries = flatten(stream, owner, splices, &mut Vec::new());
    printer.level(&entries, owner)?;
    Ok(printer.report)
}

/// A token tree at one printing level, with the splices that apply inside it.
struct Entry<'a> {
    tree: TokenTree,
    owner: InvocationId,
    splices: &'a [Splice],
    path: Vec<usize>,
}

/// The trees of one stream level after splicing, in print order.
fn flatten<'a>(
    stream: &TokenStream,
    owner: InvocationId,
    splices: &'a [Splice],
    path: &mut Vec<usize>,
) -> Vec<Entry<'a>> {
    let trees = stream.clone().into_iter().collect::<Vec<_>>();
    let mut entries = Vec::with_capacity(trees.len());
    let mut index = 0;
    while index < trees.len() {
        path.push(index);
        if let Some(splice) = splices.iter().find(|splice| splice.at == *path) {
            path.pop();
            entries.extend(flatten(
                &splice.tokens,
                splice.owner,
                &splice.splices,
                &mut Vec::new(),
            ));
            index += splice.len.max(1);
            continue;
        }
        entries.push(Entry {
            tree: trees[index].clone(),
            owner,
            splices,
            path: path.clone(),
        });
        path.pop();
        index += 1;
    }
    entries
}

struct Printer<'a> {
    authored: &'a AuthoredFile,
    out: &'a mut GeneratedSource,
    report: PrintReport,
}

impl Printer<'_> {
    /// Prints one stream level with the fallback `Display` spacing: one space
    /// between trees unless the previous tree is a `Spacing::Joint` punct.
    fn level(
        &mut self,
        entries: &[Entry<'_>],
        level_owner: InvocationId,
    ) -> Result<(), PrintError> {
        let mut joint = false;
        for (index, entry) in entries.iter().enumerate() {
            if index != 0 && !joint {
                let previous = entries[index - 1].owner;
                let owner = if previous == entry.owner {
                    entry.owner
                } else {
                    level_owner
                };
                self.separator(" ", owner);
            }
            joint = false;
            match &entry.tree {
                TokenTree::Group(group) => {
                    let (open, close) = match group.delimiter() {
                        Delimiter::Parenthesis => ("(", ")"),
                        Delimiter::Brace => ("{", "}"),
                        Delimiter::Bracket => ("[", "]"),
                        Delimiter::None => {
                            return Err(PrintError::NoneDelimitedGroup { owner: entry.owner });
                        }
                    };
                    let mut path = entry.path.clone();
                    let inner = flatten(&group.stream(), entry.owner, entry.splices, &mut path);
                    self.token(open, group.span_open(), entry.owner);
                    if group.delimiter() == Delimiter::Brace {
                        self.separator(" ", entry.owner);
                    }
                    self.level(&inner, entry.owner)?;
                    if group.delimiter() == Delimiter::Brace && !inner.is_empty() {
                        self.separator(" ", entry.owner);
                    }
                    self.token(close, group.span_close(), entry.owner);
                }
                TokenTree::Ident(ident) => {
                    self.token(&ident.to_string(), ident.span(), entry.owner);
                }
                TokenTree::Punct(punct) => {
                    joint = punct.spacing() == Spacing::Joint;
                    let mut buffer = [0; 4];
                    self.token(
                        punct.as_char().encode_utf8(&mut buffer),
                        punct.span(),
                        entry.owner,
                    );
                }
                TokenTree::Literal(literal) => {
                    self.token(&literal.to_string(), literal.span(), entry.owner);
                }
            }
        }
        Ok(())
    }

    fn separator(&mut self, text: &str, owner: InvocationId) {
        self.out
            .push(text, MappingClass::InvocationLevel, None, Some(owner), None);
    }

    fn token(&mut self, text: &str, span: Span, owner: InvocationId) {
        self.report.tokens += 1;
        let authored = self.authored.byte_range(span);
        match authored {
            Some(range)
                if !range.is_empty() && self.authored.source().get(range.clone()) == Some(text) =>
            {
                self.report.exact_authored += 1;
                self.out.push(
                    text,
                    MappingClass::ExactAuthored,
                    Some(range),
                    Some(owner),
                    None,
                );
            }
            Some(range) => {
                self.report.respanned += 1;
                let respanned = (!range.is_empty()).then_some(range);
                self.out.push(
                    text,
                    MappingClass::InvocationLevel,
                    None,
                    Some(owner),
                    respanned,
                );
            }
            None => {
                if span.file() == CALL_SITE_FILE {
                    self.report.call_site += 1;
                } else {
                    self.report.reparsed += 1;
                }
                self.out
                    .push(text, MappingClass::InvocationLevel, None, Some(owner), None);
            }
        }
    }
}

/// The classification of one generated range.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Mapping {
    /// The range's tokens are authored tokens in authored order; `authored` is
    /// the authored range they span.
    ExactAuthored {
        /// Authored byte range.
        authored: Range<usize>,
        /// Owning invocation; `None` for text outside every expansion.
        owner: Option<InvocationId>,
    },
    /// The range maps only to an invocation's call site.
    InvocationLevel {
        /// The invocation.
        owner: InvocationId,
        /// Its authored call-site range.
        call_site: Range<usize>,
    },
    /// The range lies in text no invocation expansion produced.
    GeneratedOnly,
    /// The range has no source range.
    Unmappable,
}

impl Mapping {
    /// The BL-006 class of this mapping.
    #[must_use]
    pub const fn class(&self) -> MappingClass {
        match self {
            Self::ExactAuthored { .. } => MappingClass::ExactAuthored,
            Self::InvocationLevel { .. } => MappingClass::InvocationLevel,
            Self::GeneratedOnly => MappingClass::GeneratedOnly,
            Self::Unmappable => MappingClass::Unmappable,
        }
    }
}

/// Classifies a generated byte range, such as a rustc diagnostic span in the
/// generated file.
///
/// An empty range classifies the segment that contains its position, and a
/// range inside one segment takes that segment's class; an exact-authored
/// segment maps the corresponding authored subrange.
///
/// A range across several segments is classified in the innermost invocation
/// (or the text outside every invocation) that owns or encloses all of them,
/// its context. Every nested invocation it touches must lie wholly inside the
/// range, which then contains that invocation's whole expansion; the range is
/// unmappable otherwise. Ignoring whitespace, when the range starts and ends
/// with an exact-authored segment or a whole nested expansion (which stands for
/// the authored range it replaced), and the first authored range does not end
/// after the last one starts, the range is exact-authored from the first to
/// the last authored byte. This is how rustc spans a node whose first and last
/// tokens are authored, whatever the expansion put between them. Otherwise the
/// range is invocation-level in its context, generated-only when it lies in
/// generated-only text outside every invocation, and unmappable when it mixes
/// that text with other text. Finer rules belong to the diagnostic comparison
/// (IR-18).
#[must_use]
pub fn lookup(
    source: &GeneratedSource,
    authored: &AuthoredFile,
    generated: Range<usize>,
) -> Mapping {
    let map = &source.map;
    if generated.start > generated.end || generated.end > source.text.len() {
        return Mapping::Unmappable;
    }
    let touched = map
        .segments
        .iter()
        .filter(|segment| {
            if generated.is_empty() {
                segment.generated.contains(&generated.start)
            } else {
                segment.generated.start < generated.end && generated.start < segment.generated.end
            }
        })
        .collect::<Vec<_>>();
    let Some(first) = touched.first() else {
        return Mapping::Unmappable;
    };
    let mut enclosing = owner_chain(map, first.owner);
    for segment in &touched {
        let owners = owner_chain(map, segment.owner);
        enclosing.retain(|owner| owners.contains(owner));
    }
    let context = enclosing[0];
    let invocation_level = || {
        context
            .and_then(|owner| map.invocations.get(owner.0))
            .map_or(Mapping::Unmappable, |invocation| Mapping::InvocationLevel {
                owner: invocation.id,
                call_site: invocation.call_site.clone(),
            })
    };

    if let [segment] = touched.as_slice() {
        return match (segment.class, clipped_image(segment, &generated)) {
            (MappingClass::ExactAuthored, Some(authored)) => Mapping::ExactAuthored {
                authored,
                owner: context,
            },
            (MappingClass::InvocationLevel, _) => invocation_level(),
            (MappingClass::GeneratedOnly, _) => Mapping::GeneratedOnly,
            _ => Mapping::Unmappable,
        };
    }

    let Some(parts) = parts(source, &touched, &generated, context) else {
        return Mapping::Unmappable;
    };
    if let (Some((Some(first), true)), Some((Some(last), true))) = (parts.first(), parts.last())
        && first.start <= last.start
        && first.end <= last.end
        && authored.source().get(first.start..last.end).is_some()
    {
        return Mapping::ExactAuthored {
            authored: first.start..last.end,
            owner: context,
        };
    }
    let generated_only = touched
        .iter()
        .all(|segment| segment.class == MappingClass::GeneratedOnly);
    if context.is_some() {
        invocation_level()
    } else if generated_only {
        Mapping::GeneratedOnly
    } else {
        Mapping::Unmappable
    }
}

/// Owners from `owner` out to the text outside every invocation (`None`).
fn owner_chain(map: &SourceMap, owner: Option<InvocationId>) -> Vec<Option<InvocationId>> {
    let mut chain = vec![owner];
    let mut current = owner;
    while let Some(id) = current {
        current = map
            .invocations
            .get(id.0)
            .and_then(|invocation| invocation.parent);
        chain.push(current);
    }
    chain
}

/// The authored range of the part of an exact-authored `segment` inside
/// `generated`.
fn clipped_image(segment: &Segment, generated: &Range<usize>) -> Option<Range<usize>> {
    let authored = segment.authored.as_ref()?;
    let start = generated.start.max(segment.generated.start) - segment.generated.start;
    let end = generated.end.min(segment.generated.end) - segment.generated.start;
    Some(authored.start + start..authored.start + end)
}

/// The parts of a range across segments, whitespace aside, as (authored image,
/// exact): segments of `context`, and whole expansions of invocations that
/// `context` directly contains, which stand for the authored range they
/// replaced. `None` when the range contains only part of a nested expansion.
fn parts(
    source: &GeneratedSource,
    touched: &[&Segment],
    generated: &Range<usize>,
    context: Option<InvocationId>,
) -> Option<Vec<(Option<Range<usize>>, bool)>> {
    let map = &source.map;
    let mut parts = Vec::new();
    let mut nested_seen = None;
    for segment in touched {
        if segment.owner == context {
            nested_seen = None;
            let exact = segment.class == MappingClass::ExactAuthored;
            let whitespace = source.text[segment.generated.clone()]
                .chars()
                .all(char::is_whitespace);
            if exact || !whitespace {
                parts.push((clipped_image(segment, generated), exact));
            }
            continue;
        }
        let owners = owner_chain(map, segment.owner);
        let position = owners.iter().position(|owner| *owner == context)?;
        let child = owners.get(position.checked_sub(1)?).copied().flatten()?;
        if nested_seen == Some(child) {
            continue;
        }
        nested_seen = Some(child);
        let extent = map
            .segments
            .iter()
            .filter(|segment| owner_chain(map, segment.owner).contains(&Some(child)))
            .map(|segment| segment.generated.clone())
            .reduce(|extent, next| extent.start.min(next.start)..extent.end.max(next.end))?;
        if extent.start < generated.start || generated.end < extent.end {
            return None;
        }
        let replaced = map.invocations.get(child.0)?.replaced.clone();
        parts.push((Some(replaced), true));
    }
    Some(parts)
}

#[cfg(test)]
mod tests {
    use super::{
        AuthoredFile, GeneratedSource, InvocationId, Mapping, MappingClass, Splice, lookup,
        print_with_map, splice_tokens,
    };
    use proc_macro2::{TokenStream, TokenTree};
    use quote::quote;

    fn check_covering(source: &GeneratedSource) {
        let mut position = 0;
        for segment in &source.map.segments {
            assert_eq!(segment.generated.start, position);
            assert!(segment.generated.end > segment.generated.start);
            assert_eq!(
                segment.authored.is_some(),
                segment.class == MappingClass::ExactAuthored
            );
            position = segment.generated.end;
        }
        assert_eq!(position, source.text.len());
    }

    fn print(stream: &TokenStream, authored: &AuthoredFile) -> GeneratedSource {
        let mut out = GeneratedSource::new("generated.rs", authored);
        let owner = out.begin_invocation("test", 0..0, 0..0, None);
        print_with_map(stream, authored, owner, &[], &mut out).unwrap();
        out
    }

    #[test]
    fn printed_text_equals_the_fallback_display() {
        let (authored, tokens) = AuthoredFile::lex(
            "src/lib.rs",
            "fn f() -> u8 { let x = [1u8, 2]; x[0] += 1; 'a: loop { break 'a; } x.0 }\nstruct S {}\nmacro_rules! m { ($x:expr) => { $x }; }\n#[doc = \"d\"] /// doc\nconst C: &str = r#\"raw\"#;",
        )
        .unwrap();
        let synthetic = quote! {
            ::core::option::Option::<u8>::None; a && b || !c; x ..= y; f(); {} [] () {x}
            #tokens
            'b: loop {} 1.0e3 b"bytes" 'x' c"cstr" r#type
        };
        let reparsed: TokenStream = "x << = y . z ::< T >".parse().unwrap();
        for stream in [tokens.clone(), synthetic, reparsed, TokenStream::new()] {
            let out = print(&stream, &authored);
            assert_eq!(out.text, stream.to_string());
            check_covering(&out);
            for segment in &out.map.segments {
                if let Some(range) = &segment.authored {
                    assert_eq!(
                        &out.text[segment.generated.clone()],
                        &authored.source()[range.clone()]
                    );
                }
            }
        }
    }

    #[test]
    fn authored_tokens_map_exactly_and_synthetic_tokens_to_the_invocation() {
        let (authored, tokens) = AuthoredFile::lex("src/lib.rs", "Foo()   =>  Bar()").unwrap();
        let foo = tokens.clone().into_iter().take(2).collect::<TokenStream>();
        let stream = quote!(let x = #foo;);
        let out = print(&stream, &authored);
        assert_eq!(out.text, "let x = Foo () ;");
        check_covering(&out);
        let foo_start = out.text.find("Foo").unwrap();
        assert_eq!(
            lookup(&out, &authored, foo_start..foo_start + 6),
            Mapping::ExactAuthored {
                authored: 0..5,
                owner: Some(InvocationId(0))
            }
        );
        assert_eq!(
            lookup(&out, &authored, 0..3),
            Mapping::InvocationLevel {
                owner: InvocationId(0),
                call_site: 0..0
            }
        );
        assert_eq!(
            lookup(&out, &authored, 0..out.text.len()).class(),
            MappingClass::InvocationLevel
        );
        assert_eq!(
            lookup(&out, &authored, out.text.len()..out.text.len() + 1),
            Mapping::Unmappable
        );
    }

    #[test]
    fn respanned_and_reordered_tokens_are_not_exact() {
        let (authored, tokens) = AuthoredFile::lex("src/lib.rs", "a b").unwrap();
        let trees = tokens.into_iter().collect::<Vec<_>>();
        let (a, b) = (&trees[0], &trees[1]);
        let renamed = proc_macro2::Ident::new("c", a.span());
        let out = print(&quote!(#b #a #renamed), &authored);
        assert_eq!(out.text, "b a c");
        assert_eq!(
            lookup(&out, &authored, 0..1).class(),
            MappingClass::ExactAuthored
        );
        assert_eq!(
            lookup(&out, &authored, 0..3).class(),
            MappingClass::InvocationLevel
        );
        assert_eq!(
            lookup(&out, &authored, 4..5).class(),
            MappingClass::InvocationLevel
        );
    }

    #[test]
    fn a_range_between_authored_tokens_joins_like_rustc() {
        let (authored, tokens) = AuthoredFile::lex("src/lib.rs", "a  b").unwrap();
        let trees = tokens.into_iter().collect::<Vec<_>>();
        let (a, b) = (&trees[0], &trees[1]);
        let out = print(&quote!(#a :: wrap (x) #b), &authored);
        assert_eq!(out.text, "a :: wrap (x) b");
        assert_eq!(
            lookup(&out, &authored, 0..out.text.len()),
            Mapping::ExactAuthored {
                authored: 0..4,
                owner: Some(InvocationId(0))
            }
        );
        assert_eq!(
            lookup(&out, &authored, 0..6).class(),
            MappingClass::InvocationLevel
        );
    }

    #[test]
    fn splices_print_nested_expansions_in_place() {
        let (authored, tokens) = AuthoredFile::lex("src/lib.rs", "x").unwrap();
        let mut out = GeneratedSource::new("generated.rs", &authored);
        out.copy_authored(&authored, 0..0);
        let outer = out.begin_invocation("outer", 0..1, 0..1, None);
        let inner = out.begin_invocation("inner", 0..1, 0..1, Some(outer));
        let stream = quote!(
            fn f() {
                a![b];
            }
        );
        let splices = [Splice {
            at: vec![3, 0],
            len: 3,
            owner: inner,
            tokens: quote!({ #tokens }),
            splices: Vec::new(),
        }];
        print_with_map(&stream, &authored, outer, &splices, &mut out).unwrap();
        assert_eq!(out.text, splice_tokens(&stream, &splices).to_string());
        assert_eq!(out.text, "fn f () { { x } ; }");
        check_covering(&out);
        let x = out.text.find('x').unwrap();
        assert_eq!(
            lookup(&out, &authored, x..x + 1),
            Mapping::ExactAuthored {
                authored: 0..1,
                owner: Some(inner)
            }
        );
        assert_eq!(
            lookup(&out, &authored, x - 2..x + 3),
            Mapping::InvocationLevel {
                owner: inner,
                call_site: 0..1
            }
        );
        assert_eq!(lookup(&out, &authored, x - 4..x + 1), Mapping::Unmappable);
    }

    #[test]
    fn authored_code_around_a_whole_nested_expansion_maps_exactly() {
        let (authored, tokens) = AuthoredFile::lex("src/lib.rs", "outer(inner!(x))").unwrap();
        let TokenTree::Group(arguments) = tokens.clone().into_iter().nth(1).unwrap() else {
            panic!("a group");
        };
        let TokenTree::Group(call) = arguments.stream().into_iter().nth(2).unwrap() else {
            panic!("a group");
        };
        let x = call.stream();
        let mut out = GeneratedSource::new("generated.rs", &authored);
        let outer = out.begin_invocation("outer", 0..16, 0..16, None);
        let inner = out.begin_invocation("inner", 6..15, 6..15, Some(outer));
        let splices = [Splice {
            at: vec![1, 0],
            len: 3,
            owner: inner,
            tokens: quote!({ #x }),
            splices: Vec::new(),
        }];
        print_with_map(&tokens, &authored, outer, &splices, &mut out).unwrap();
        assert_eq!(out.text, "outer ({ x })");
        check_covering(&out);
        assert_eq!(
            lookup(&out, &authored, 0..out.text.len()),
            Mapping::ExactAuthored {
                authored: 0..16,
                owner: Some(outer)
            }
        );
        assert_eq!(
            lookup(&out, &authored, 7..12),
            Mapping::InvocationLevel {
                owner: inner,
                call_site: 6..15
            }
        );
        assert_eq!(
            lookup(&out, &authored, 7..13),
            Mapping::ExactAuthored {
                authored: 6..16,
                owner: Some(outer)
            }
        );
        assert_eq!(lookup(&out, &authored, 0..9), Mapping::Unmappable);
    }

    #[test]
    fn none_delimited_groups_are_rejected() {
        let (authored, _) = AuthoredFile::lex("src/lib.rs", "").unwrap();
        let group = proc_macro2::Group::new(proc_macro2::Delimiter::None, quote!(a + b));
        let mut out = GeneratedSource::new("generated.rs", &authored);
        let owner = out.begin_invocation("test", 0..0, 0..0, None);
        let error =
            print_with_map(&quote!(x * #group), &authored, owner, &[], &mut out).unwrap_err();
        assert_eq!(error, super::PrintError::NoneDelimitedGroup { owner });
    }

    #[test]
    fn identity_copies_and_generated_text_are_classified() {
        let (authored, _) = AuthoredFile::lex("src/lib.rs", "// c\nuse a;\n").unwrap();
        let mut out = GeneratedSource::new("generated.rs", &authored);
        out.copy_authored(&authored, 0..5);
        out.copy_authored(&authored, 5..12);
        out.push_generated("fn table() {}");
        check_covering(&out);
        assert_eq!(out.map.segments.len(), 2);
        assert_eq!(
            lookup(&out, &authored, 5..11),
            Mapping::ExactAuthored {
                authored: 5..11,
                owner: None
            }
        );
        assert_eq!(lookup(&out, &authored, 12..14), Mapping::GeneratedOnly);
        assert_eq!(lookup(&out, &authored, 10..14), Mapping::Unmappable);
    }
}
