mod sentence;
mod term;
mod token;

use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fmt,
};

use krs_diagnostic::{Diagnostic, Location, ToDiagnostic, codes};
use krs_ir::{
    ByteRange, CellAttribute, FixedCell, FixedCellContent, GroupAssociativity, ProductionGroupId,
    SentenceKind, SourceMapKey, StableText,
};
use krs_ir_levels::{
    DefinitionIr, DefinitionModule, DefinitionSentence, DefinitionSortRef, ProductionSentence,
    SymbolId,
    k_surface::{DefinitionIndex, ImportPolicy, VariableNaming, builtin_imports},
};

use crate::{
    LoweredDefinition, SourceMap, SymbolMap,
    sidecar::{GeneratedRanges, SidecarError},
};
use sentence::emit_sentence;
use term::Rendered;
use token::TokenLexicon;

/// Generated artifact holding the claim-free semantics.
pub use crate::artifacts::DEFINITION_ARTIFACT;

/// Generated artifact holding the claims, present only when a claim exists.
pub use crate::artifacts::SPEC_ARTIFACT;

/// Canonical K source and its deterministic shared sidecars.
///
/// Claims are proof obligations, which K accepts only outside an executable
/// definition, so they are rendered into a separate specification module that
/// `requires` the semantics and imports its main module.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EmittedK {
    source: String,
    spec: Option<EmittedSpec>,
    symbol_map: SymbolMap,
    source_map: SourceMap,
}

/// Canonical claims-only K specification.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EmittedSpec {
    source: String,
    module: String,
}

impl EmittedSpec {
    /// Returns canonical parseable `.k` source with one trailing newline.
    #[must_use]
    pub fn source(&self) -> &str {
        &self.source
    }

    /// Returns the specification module name, the main module suffixed `-SPEC`.
    #[must_use]
    pub fn module(&self) -> &str {
        &self.module
    }
}

impl EmittedK {
    /// Returns canonical parseable claim-free `.k` source with one trailing newline.
    #[must_use]
    pub fn source(&self) -> &str {
        &self.source
    }

    /// Returns the claims-only specification, or `None` when no claim exists.
    #[must_use]
    pub const fn spec(&self) -> Option<&EmittedSpec> {
        self.spec.as_ref()
    }

    /// Returns the symbol sidecar shared with non-source adapters.
    #[must_use]
    pub const fn symbol_map(&self) -> &SymbolMap {
        &self.symbol_map
    }

    /// Returns the source sidecar augmented with exact generated ranges.
    #[must_use]
    pub const fn source_map(&self) -> &SourceMap {
        &self.source_map
    }
}

/// Typed canonical-source emission failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EmitError {
    /// The checked Definition IR contains a source-level node that canonical-source emission does not support.
    UnsupportedShape {
        /// Structural node family.
        node: &'static str,
        /// Deterministic explanatory detail.
        detail: String,
    },
    /// A Definition symbol reference was absent or had the wrong role.
    InvalidReference(String),
    /// Two rendered nodes attempted to own one generated source range.
    DuplicateGeneratedRange(SourceMapKey),
    /// A shared sidecar invariant failed.
    InvalidSidecar(String),
}

impl ToDiagnostic for EmitError {
    fn to_diagnostic(&self) -> Diagnostic {
        let code = match self {
            Self::UnsupportedShape { .. } => codes::emit::UNSUPPORTED_SHAPE,
            Self::InvalidReference(_) => codes::emit::INVALID_REFERENCE,
            Self::DuplicateGeneratedRange(_) => codes::emit::DUPLICATE_GENERATED_RANGE,
            Self::InvalidSidecar(_) => codes::emit::INVALID_SIDECAR,
        };
        Diagnostic::error(
            code,
            self.to_string(),
            match self {
                Self::DuplicateGeneratedRange(key) => Location::Definition(key.clone()),
                _ => Location::None,
            },
        )
    }
}

impl fmt::Display for EmitError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsupportedShape { node, detail } => {
                write!(formatter, "unsupported source {node} shape: {detail}")
            }
            Self::InvalidReference(detail) => formatter.write_str(detail),
            Self::DuplicateGeneratedRange(key) => write!(
                formatter,
                "duplicate generated range for source-map key {}",
                key.as_str()
            ),
            Self::InvalidSidecar(detail) => write!(formatter, "invalid emitted sidecar: {detail}"),
        }
    }
}

impl Error for EmitError {}

impl From<SidecarError> for EmitError {
    fn from(value: SidecarError) -> Self {
        Self::InvalidSidecar(value.to_string())
    }
}

/// Structurally renders one lowered Definition IR as canonical `.k` source.
///
/// This function performs no semantic repair or frontend checking. Every term
/// is rendered from Definition IR structure, and unsupported shapes fail.
///
/// # Errors
///
/// Returns [`EmitError`] for an unsupported source shape, invalid reference,
/// duplicate range, or sidecar invariant failure.
pub fn emit_k(lowered: &LoweredDefinition) -> Result<EmittedK, EmitError> {
    let definition = lowered.definition();
    let context = EmitContext::new(definition);
    let mut writer = Writer::default();
    let mut claims = Vec::new();
    for (index, module) in definition.modules().iter().enumerate() {
        if index != 0 {
            writer.push("\n");
        }
        emit_module(module, &context, &mut writer, &mut claims)?;
    }
    if !writer.source.ends_with('\n') {
        writer.push("\n");
    }
    let mut spec_writer = Writer::default();
    let spec_module = if claims.is_empty() {
        None
    } else {
        let main = definition.main_module().as_str();
        let module = format!("{main}-SPEC");
        if definition
            .modules()
            .iter()
            .any(|candidate| candidate.id().as_str() == module)
        {
            return Err(EmitError::UnsupportedShape {
                node: "module",
                detail: format!("module {module:?} collides with the generated claims module"),
            });
        }
        spec_writer.push("requires \"");
        spec_writer.push(DEFINITION_ARTIFACT);
        spec_writer.push("\"\n\nmodule ");
        spec_writer.push(&module);
        spec_writer.push("\n  imports ");
        spec_writer.push(main);
        spec_writer.push("\n\n");
        for claim in claims {
            emit_sentence(claim, &context, &mut spec_writer)?;
        }
        spec_writer.push("endmodule\n");
        Some(module)
    };
    let source_map = lowered.source_map().clone().with_generated_ranges(&[
        (DEFINITION_ARTIFACT, &writer.source, &writer.ranges),
        (SPEC_ARTIFACT, &spec_writer.source, &spec_writer.ranges),
    ])?;
    Ok(EmittedK {
        source: writer.source,
        spec: spec_module.map(|module| EmittedSpec {
            source: spec_writer.source,
            module,
        }),
        symbol_map: lowered.symbol_map().clone(),
        source_map,
    })
}

struct EmitContext<'a> {
    index: DefinitionIndex<'a>,
    non_associative_groups: BTreeSet<ProductionGroupId>,
    repeated_ancestors: BTreeMap<SymbolId, SymbolId>,
    naming: VariableNaming,
    lexicon: TokenLexicon,
}

impl<'a> EmitContext<'a> {
    fn new(definition: &'a DefinitionIr) -> Self {
        let index = DefinitionIndex::new(definition);
        let mut non_associative_groups = BTreeSet::new();
        let mut repeated_ancestors = BTreeMap::new();
        for sentence in definition
            .modules()
            .iter()
            .flat_map(DefinitionModule::sentences)
        {
            if let DefinitionSentence::Associativity(associativity) = sentence
                && associativity.associativity() == GroupAssociativity::NonAssociative
            {
                non_associative_groups.extend(associativity.groups().iter().cloned());
            }
            if let DefinitionSentence::Configuration(configuration) = sentence {
                collect_repeated_ancestors(configuration.cells(), &mut repeated_ancestors, None);
            }
        }
        Self {
            index,
            non_associative_groups,
            repeated_ancestors,
            naming: VariableNaming::new(definition),
            lexicon: TokenLexicon::new(definition),
        }
    }

    /// Spells a token bare when K's rule parser lexes that spelling back to the same token of the
    /// same sort, and as `#token("<value>","<Sort>")` otherwise.
    fn token(&self, value: &str, sort: &DefinitionSortRef) -> Result<String, EmitError> {
        if let DefinitionSortRef::Builtin(builtin) = sort
            && self.lexicon.is_bare(*builtin, value)
        {
            return Ok(value.to_owned());
        }
        let sort = self.sort_name_ref(sort)?;
        match (token::token_literal(value), token::token_literal(sort)) {
            (Some(value), Some(sort)) => Ok(format!("#token({value},{sort})")),
            _ => Err(EmitError::UnsupportedShape {
                node: "token",
                detail: format!("{value:?} of sort {sort} has no exact `#token` spelling"),
            }),
        }
    }

    fn sort_name(&self, id: &SymbolId) -> Result<&str, EmitError> {
        self.index
            .sort_name(id)
            .ok_or_else(|| EmitError::InvalidReference(format!("missing source sort {id}")))
    }

    fn sort_name_ref(&self, sort: &DefinitionSortRef) -> Result<&str, EmitError> {
        match sort {
            DefinitionSortRef::Declared(id) => self.sort_name(id),
            DefinitionSortRef::Builtin(sort) => Ok(sort.k_name()),
        }
    }

    fn production(&self, id: &SymbolId) -> Result<&ProductionSentence, EmitError> {
        self.index
            .production(id)
            .ok_or_else(|| EmitError::InvalidReference(format!("missing source production {id}")))
    }

    fn group_name(&self, id: &ProductionGroupId) -> Result<&str, EmitError> {
        self.index
            .group_name(id)
            .ok_or_else(|| EmitError::InvalidReference(format!("missing production group {id}")))
    }

    fn cell_name(&self, id: &SymbolId) -> Result<&str, EmitError> {
        self.index
            .cell_name(id)
            .ok_or_else(|| EmitError::InvalidReference(format!("missing fixed cell {id}")))
    }

    fn repeated_ancestor(&self, id: &SymbolId) -> Option<&SymbolId> {
        self.repeated_ancestors.get(id)
    }

    fn context_alias_name(&self, id: &krs_ir::StableItemId) -> Result<&str, EmitError> {
        self.index
            .context_alias_name(id)
            .ok_or_else(|| EmitError::InvalidReference(format!("missing context alias {id}")))
    }

    fn is_non_associative(&self, group: &ProductionGroupId) -> bool {
        self.non_associative_groups.contains(group)
    }
}

fn collect_repeated_ancestors(
    cells: &[FixedCell<DefinitionSortRef, SymbolId>],
    repeated_ancestors: &mut BTreeMap<SymbolId, SymbolId>,
    repeated_ancestor: Option<&SymbolId>,
) {
    for cell in cells {
        let repeated_ancestor = if cell
            .attributes()
            .iter()
            .any(|attribute| matches!(attribute, CellAttribute::Multiplicity { .. }))
        {
            Some(cell.id())
        } else {
            repeated_ancestor
        };
        if let FixedCellContent::Children { children } = cell.content() {
            collect_repeated_ancestors(children, repeated_ancestors, repeated_ancestor);
        } else if let Some(ancestor) = repeated_ancestor {
            repeated_ancestors.insert(cell.id().clone(), ancestor.clone());
        }
    }
}

#[derive(Default)]
struct Writer {
    source: String,
    ranges: GeneratedRanges,
}

impl Writer {
    fn push(&mut self, text: &str) {
        self.source.push_str(text);
    }

    fn record(&mut self, key: &SourceMapKey, start: usize, end: usize) -> Result<(), EmitError> {
        let range = ByteRange::new(start, end).map_err(|_| SidecarError::InvalidGeneratedRange)?;
        if self.ranges.insert(key.clone(), range).is_some() {
            return Err(EmitError::DuplicateGeneratedRange(key.clone()));
        }
        Ok(())
    }

    fn append_rendered(&mut self, rendered: Rendered) -> Result<(), EmitError> {
        let base = self.source.len();
        self.source.push_str(&rendered.text);
        for (key, start, end) in rendered.ranges {
            self.record(&key, base + start, base + end)?;
        }
        Ok(())
    }
}

/// Renders `module` without its claims, which are appended to `claims`.
fn emit_module<'a>(
    module: &'a DefinitionModule,
    context: &EmitContext<'_>,
    writer: &mut Writer,
    claims: &mut Vec<&'a DefinitionSentence>,
) -> Result<(), EmitError> {
    let module_start = writer.source.len();
    writer.push("module ");
    writer.push(module.id().as_str());
    writer.push("\n");
    let imports = definition_module_imports(module);
    for import in &imports {
        writer.push("  imports ");
        writer.push(import);
        writer.push("\n");
    }
    let mut sentences = module.sentences().iter().collect::<Vec<_>>();
    sentences.sort_by_key(|sentence| sentence_key(sentence));
    let (module_claims, sentences): (Vec<_>, Vec<_>) = sentences
        .into_iter()
        .partition(|sentence| is_claim(sentence));
    claims.extend(module_claims);
    if !imports.is_empty() && !sentences.is_empty() {
        writer.push("\n");
    }
    let mut previous_group = None;
    for sentence in sentences {
        let group = sentence_group(sentence);
        if previous_group.is_some_and(|previous| previous != group) {
            writer.push("\n");
        }
        emit_sentence(sentence, context, writer)?;
        previous_group = Some(group);
    }
    writer.push("endmodule\n");
    writer.record(module.origin().key(), module_start, writer.source.len())?;
    Ok(())
}

/// Returns the exact authored and compiler-inferred imports emitted for a module.
#[must_use]
pub fn definition_module_imports(module: &DefinitionModule) -> BTreeSet<String> {
    module
        .imports()
        .iter()
        .map(|id| id.as_str().to_owned())
        .chain(
            builtin_imports(module, ImportPolicy::SourceText)
                .into_iter()
                .map(str::to_owned),
        )
        .collect()
}

/// Renders one typed sentence with the definition's canonical emission context.
///
/// This uses the same printer as [`emit_k`] and performs no normalization.
///
/// # Errors
///
/// Returns an emission error for unsupported structure or invalid references.
pub fn definition_sentence_source(
    definition: &DefinitionIr,
    sentence: &DefinitionSentence,
) -> Result<String, EmitError> {
    let mut writer = Writer::default();
    emit_sentence(sentence, &EmitContext::new(definition), &mut writer)?;
    Ok(writer.source)
}

fn is_claim(sentence: &DefinitionSentence) -> bool {
    matches!(sentence, DefinitionSentence::Rule(rule) if rule.kind() == SentenceKind::Claim)
}

fn sentence_group(sentence: &DefinitionSentence) -> u8 {
    match sentence {
        DefinitionSentence::SyntaxSort(_) => 0,
        DefinitionSentence::Production(_) => 1,
        DefinitionSentence::Subsort(_) => 2,
        DefinitionSentence::Precedence(_) => 3,
        DefinitionSentence::Associativity(_) => 4,
        DefinitionSentence::Configuration(_) => 5,
        DefinitionSentence::ContextAlias(_) => 6,
        DefinitionSentence::Rule(_) => 7,
    }
}

#[derive(Eq, Ord, PartialEq, PartialOrd)]
enum SentenceOrderKey {
    SyntaxSort(String),
    Production(String),
    Subsort(String),
    Precedence(String),
    Associativity(String),
    Configuration(String),
    ContextAlias(String),
    Rule(String),
}

fn sentence_key(sentence: &DefinitionSentence) -> SentenceOrderKey {
    match sentence {
        DefinitionSentence::SyntaxSort(sentence) => {
            SentenceOrderKey::SyntaxSort(sentence.symbol().emitted_name().to_owned())
        }
        DefinitionSentence::Production(sentence) => {
            SentenceOrderKey::Production(sentence.symbol().emitted_name().to_owned())
        }
        DefinitionSentence::Subsort(sentence) => SentenceOrderKey::Subsort(format!(
            "{}:{}",
            sentence.supersort().stable_text(),
            sentence.subsort().stable_text()
        )),
        // Origin keys are unique per definition, so ordering by their stable text is total.
        DefinitionSentence::Precedence(sentence) => {
            SentenceOrderKey::Precedence(sentence.origin().key().stable_text().into_owned())
        }
        DefinitionSentence::Associativity(sentence) => {
            SentenceOrderKey::Associativity(sentence.origin().key().stable_text().into_owned())
        }
        DefinitionSentence::Configuration(sentence) => {
            SentenceOrderKey::Configuration(sentence.origin().key().stable_text().into_owned())
        }
        DefinitionSentence::ContextAlias(sentence) => {
            SentenceOrderKey::ContextAlias(sentence.name().to_owned())
        }
        DefinitionSentence::Rule(sentence) => {
            SentenceOrderKey::Rule(sentence.label().emitted_name().to_owned())
        }
    }
}

/// Quotes a string literal of K's outer syntax (terminals and regex terminals).
///
/// The outer lexer (`Outer.jj` `STRING` and `STRING_REGEX`) accepts only the escapes
/// `\"`, `\\`, `\n`, `\r`, and `\t`, and reads every other character other than a
/// raw newline literally, so every other character is written as itself.
fn quoted_outer(value: &str) -> String {
    let mut result = String::from("\"");
    for character in value.chars() {
        match character {
            '\\' => result.push_str("\\\\"),
            '"' => result.push_str("\\\""),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            character => result.push(character),
        }
    }
    result.push('"');
    result
}

/// Quotes a `KString`, the token sort of configuration cell properties.
///
/// `KString` (`kast.md`) accepts the escapes `\"`, `\\`, `\n`, `\r`, `\t`, `\f`, and
/// `\xHH`, and forbids a raw newline or carriage return; other control characters are
/// written as `\xHH` so the emitted file stays printable.
fn quoted_kstring(value: &str) -> String {
    let mut result = String::from("\"");
    for character in value.chars() {
        match character {
            '\\' => result.push_str("\\\\"),
            '"' => result.push_str("\\\""),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            '\u{c}' => result.push_str("\\f"),
            character if character.is_control() => {
                use std::fmt::Write as _;
                // Every Unicode control character is below U+0100.
                write!(result, "\\x{:02X}", u32::from(character))
                    .expect("writing to String cannot fail");
            }
            character => result.push(character),
        }
    }
    result.push('"');
    result
}

#[cfg(test)]
mod tests;
