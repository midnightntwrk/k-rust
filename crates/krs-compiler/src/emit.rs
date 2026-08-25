use std::collections::BTreeMap;
use std::error::Error;
use std::fmt;

use krs_ir::{
    BuiltinSort, ConfigurationSentence, DefinitionIr, DefinitionModule, DefinitionSentence,
    DefinitionSortRef, DefinitionTerm, DefinitionTermKind, LabelIdentity, ProductionItem,
    ProductionSentence, RuleSentence, SemanticId, SentenceKind, SourceMapKey, SymbolId,
    SymbolIdentity, SymbolKind,
};

use crate::sidecar::SidecarError;
use crate::{LoweredDefinition, SourceMap, SymbolMap};

/// Canonical K source and its deterministic shared sidecars.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EmittedK {
    source: String,
    symbol_map: SymbolMap,
    source_map: SourceMap,
}

impl EmittedK {
    /// Returns canonical parseable `.k` source with one trailing newline.
    #[must_use]
    pub fn source(&self) -> &str {
        &self.source
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
    /// The checked Definition IR contains a source-level node outside M2 emission.
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

impl fmt::Display for EmitError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsupportedShape { node, detail } => {
                write!(formatter, "unsupported M2 source {node} shape: {detail}")
            }
            Self::InvalidReference(detail) => formatter.write_str(detail),
            Self::DuplicateGeneratedRange(key) => write!(
                formatter,
                "duplicate generated range for source-map key {:?}",
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
    let context = EmitContext::new(lowered.definition());
    let mut writer = Writer::default();
    let mut modules = lowered.definition().modules().iter().collect::<Vec<_>>();
    modules.sort_by(|left, right| left.id().cmp(right.id()));
    for (index, module) in modules.into_iter().enumerate() {
        if index != 0 {
            writer.push("\n");
        }
        emit_module(module, &context, &mut writer)?;
    }
    if !writer.source.ends_with('\n') {
        writer.push("\n");
    }
    let source_map = lowered
        .source_map()
        .clone()
        .with_generated_ranges(&writer.source, &writer.ranges)?;
    Ok(EmittedK {
        source: writer.source,
        symbol_map: lowered.symbol_map().clone(),
        source_map,
    })
}

struct EmitContext<'a> {
    sorts: BTreeMap<SymbolId, &'a SymbolIdentity>,
    productions: BTreeMap<SymbolId, &'a ProductionSentence>,
}

impl<'a> EmitContext<'a> {
    fn new(definition: &'a DefinitionIr) -> Self {
        let mut sorts = BTreeMap::new();
        let mut productions = BTreeMap::new();
        for sentence in definition
            .modules()
            .iter()
            .flat_map(DefinitionModule::sentences)
        {
            match sentence {
                DefinitionSentence::SyntaxSort(sentence) => {
                    sorts.insert(sentence.symbol().id().clone(), sentence.symbol());
                }
                DefinitionSentence::Production(sentence) => {
                    productions.insert(sentence.symbol().id().clone(), sentence);
                }
                _ => {}
            }
        }
        Self { sorts, productions }
    }

    fn sort_name(&self, id: &SymbolId) -> Result<&str, EmitError> {
        self.sorts
            .get(id)
            .map(|symbol| symbol.emitted_name())
            .ok_or_else(|| {
                EmitError::InvalidReference(format!("missing source sort {:?}", id.as_str()))
            })
    }

    fn production(&self, id: &SymbolId) -> Result<&ProductionSentence, EmitError> {
        self.productions.get(id).copied().ok_or_else(|| {
            EmitError::InvalidReference(format!("missing source production {:?}", id.as_str()))
        })
    }
}

#[derive(Default)]
struct Writer {
    source: String,
    ranges: BTreeMap<SourceMapKey, (usize, usize)>,
}

impl Writer {
    fn push(&mut self, text: &str) {
        self.source.push_str(text);
    }

    fn record(
        &mut self,
        key: &SourceMapKey,
        start: usize,
        end: usize,
    ) -> Result<(), EmitError> {
        if self.ranges.insert(key.clone(), (start, end)).is_some() {
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

fn emit_module(
    module: &DefinitionModule,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    let module_start = writer.source.len();
    writer.push("module ");
    writer.push(module.id().as_str());
    writer.push("\n");
    let mut imports = module.imports().to_vec();
    imports.sort();
    imports.dedup();
    for import in imports {
        writer.push("  imports ");
        writer.push(import.as_str());
        writer.push("\n");
    }
    if !module.imports().is_empty() && !module.sentences().is_empty() {
        writer.push("\n");
    }

    let mut sentences = module.sentences().iter().collect::<Vec<_>>();
    sentences.sort_by_key(|sentence| sentence_key(sentence));
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

fn emit_sentence(
    sentence: &DefinitionSentence,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    let start = writer.source.len();
    writer.push("  ");
    match sentence {
        DefinitionSentence::SyntaxSort(sentence) => {
            writer.push("syntax ");
            writer.push(sentence.symbol().emitted_name());
        }
        DefinitionSentence::Subsort(sentence) => {
            writer.push("syntax ");
            writer.push(context.sort_name(sentence.supersort())?);
            writer.push(" ::= ");
            writer.push(context.sort_name(sentence.subsort())?);
        }
        DefinitionSentence::Production(sentence) => emit_production(sentence, context, writer)?,
        DefinitionSentence::Configuration(sentence) => {
            emit_configuration(sentence, context, writer)?;
        }
        DefinitionSentence::Rule(sentence) => emit_rule(sentence, context, writer)?,
    }
    writer.push("\n");
    writer.record(sentence.origin().key(), start, writer.source.len())?;
    Ok(())
}

fn emit_production(
    sentence: &ProductionSentence,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    writer.push("syntax ");
    writer.push(context.sort_name(sentence.result_sort())?);
    writer.push(" ::= ");
    for (index, item) in sentence.items().iter().enumerate() {
        if index != 0 {
            writer.push(" ");
        }
        match item {
            ProductionItem::Terminal { text } => writer.push(&quoted(text)),
            ProductionItem::NonTerminal { sort } => writer.push(context.sort_name(sort)?),
        }
    }
    writer.push(" [symbol(");
    writer.push(sentence.symbol().emitted_name());
    writer.push(")]" );
    Ok(())
}

fn emit_configuration(
    sentence: &ConfigurationSentence,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    if sentence.cell().symbol().kind() != SymbolKind::Cell
        || sentence.cell().content_sort() != &DefinitionSortRef::Builtin(BuiltinSort::KSequence)
        || sentence.initializer().symbol().kind() != SymbolKind::Initializer
    {
        return Err(EmitError::UnsupportedShape {
            node: "configuration",
            detail: "expected one fixed KSequence cell and initializer".to_owned(),
        });
    }
    let DefinitionTermKind::KSequence { .. } = sentence.initializer().body().kind() else {
        return Err(EmitError::UnsupportedShape {
            node: "configuration initializer",
            detail: "initializer body is not a KSequence".to_owned(),
        });
    };
    writer.push("configuration ");
    let cell_start = writer.source.len();
    writer.push("<");
    writer.push(sentence.cell().symbol().emitted_name());
    writer.push("> ");
    writer.append_rendered(render_term(sentence.initializer().body(), context, false)?)?;
    writer.push(" </");
    writer.push(sentence.cell().symbol().emitted_name());
    writer.push(">");
    let cell_end = writer.source.len();
    writer.record(sentence.cell().origin().key(), cell_start, cell_end)?;
    // The initializer declaration has no independent source syntax. Its honest
    // generated range is the initializer expression used in the configuration.
    writer.record(sentence.initializer().origin().key(), cell_start, cell_end)?;
    Ok(())
}

fn emit_rule(
    sentence: &RuleSentence,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    if sentence.kind() != SentenceKind::Transition {
        return Err(EmitError::UnsupportedShape {
            node: "sentence",
            detail: format!("source emitter only supports transition rules, found {:?}", sentence.kind()),
        });
    }
    writer.push("rule ");
    writer.append_rendered(render_term(sentence.body(), context, true)?)?;
    writer.push(" [label(");
    emit_label(sentence.label(), writer);
    writer.push(")]" );
    Ok(())
}

fn emit_label(label: &LabelIdentity, writer: &mut Writer) {
    writer.push(label.emitted_name());
}

#[derive(Default)]
struct Rendered {
    text: String,
    ranges: Vec<(SourceMapKey, usize, usize)>,
}

impl Rendered {
    fn push(&mut self, text: &str) {
        self.text.push_str(text);
    }

    fn append(&mut self, child: Self) {
        let base = self.text.len();
        self.text.push_str(&child.text);
        self.ranges.extend(
            child
                .ranges
                .into_iter()
                .map(|(key, start, end)| (key, base + start, base + end)),
        );
    }

    fn finish(mut self, key: &SourceMapKey, start: usize) -> Self {
        self.ranges.push((key.clone(), start, self.text.len()));
        self
    }
}

fn render_term(
    term: &DefinitionTerm,
    context: &EmitContext<'_>,
    root_rewrite: bool,
) -> Result<Rendered, EmitError> {
    let mut output = Rendered::default();
    let start = 0;
    match term.kind() {
        DefinitionTermKind::Variable { variable } => {
            output.push(&variable_name(variable));
            let DefinitionSortRef::Declared(sort) = term.sort() else {
                return Err(EmitError::UnsupportedShape {
                    node: "variable",
                    detail: "builtin-sort variables are not in M2".to_owned(),
                });
            };
            output.push(":");
            output.push(context.sort_name(sort)?);
        }
        DefinitionTermKind::Application { symbol, arguments } => {
            let production = context.production(symbol)?;
            let mut arguments = arguments.iter();
            for (index, item) in production.items().iter().enumerate() {
                if index != 0 {
                    output.push(" ");
                }
                match item {
                    ProductionItem::Terminal { text } => output.push(text),
                    ProductionItem::NonTerminal { .. } => {
                        let Some(argument) = arguments.next() else {
                            return Err(EmitError::InvalidReference(format!(
                                "production {:?} has fewer application arguments than nonterminals",
                                symbol.as_str()
                            )));
                        };
                        output.append(render_term(argument, context, false)?);
                    }
                }
            }
            if arguments.next().is_some() {
                return Err(EmitError::InvalidReference(format!(
                    "production {:?} has more application arguments than nonterminals",
                    symbol.as_str()
                )));
            }
        }
        DefinitionTermKind::Token { value } => {
            let DefinitionSortRef::Declared(sort) = term.sort() else {
                return Err(EmitError::UnsupportedShape {
                    node: "token",
                    detail: "builtin-sort tokens are not in M2".to_owned(),
                });
            };
            output.push("#token(");
            output.push(&quoted(value));
            output.push(",");
            output.push(&quoted(context.sort_name(sort)?));
            output.push(")");
        }
        DefinitionTermKind::KSequence { items, .. } => {
            if items.is_empty() {
                output.push(".K");
            } else {
                for (index, item) in items.iter().enumerate() {
                    if index != 0 {
                        output.push(" ~> ");
                    }
                    output.append(render_term(item, context, false)?);
                }
            }
        }
        DefinitionTermKind::Rewrite { from, to } => {
            if !root_rewrite {
                output.push("(");
            }
            output.append(render_term(from, context, false)?);
            output.push(" => ");
            output.append(render_term(to, context, false)?);
            if !root_rewrite {
                output.push(")");
            }
        }
    }
    Ok(output.finish(term.origin().key(), start))
}

fn sentence_group(sentence: &DefinitionSentence) -> u8 {
    match sentence {
        DefinitionSentence::SyntaxSort(_) => 0,
        DefinitionSentence::Production(_) => 1,
        DefinitionSentence::Subsort(_) => 2,
        DefinitionSentence::Configuration(_) => 3,
        DefinitionSentence::Rule(_) => 4,
    }
}

fn sentence_key(sentence: &DefinitionSentence) -> (u8, String) {
    let text = match sentence {
        DefinitionSentence::SyntaxSort(sentence) => sentence.symbol().emitted_name().to_owned(),
        DefinitionSentence::Subsort(sentence) => {
            format!("{}:{}", sentence.supersort().as_str(), sentence.subsort().as_str())
        }
        DefinitionSentence::Production(sentence) => sentence.symbol().emitted_name().to_owned(),
        DefinitionSentence::Configuration(sentence) => {
            sentence.cell().symbol().emitted_name().to_owned()
        }
        DefinitionSentence::Rule(sentence) => sentence.label().emitted_name().to_owned(),
    };
    (sentence_group(sentence), text)
}

fn variable_name(variable: &SemanticId) -> String {
    let mut result = String::from("V");
    for byte in variable.as_str().as_bytes() {
        use std::fmt::Write as _;
        write!(result, "{byte:02X}").expect("writing to String cannot fail");
    }
    result
}

fn quoted(value: &str) -> String {
    let mut result = String::from("\"");
    for character in value.chars() {
        match character {
            '\\' => result.push_str("\\\\"),
            '"' => result.push_str("\\\""),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            character if character.is_control() => {
                use std::fmt::Write as _;
                write!(result, "\\u{{{:x}}}", u32::from(character))
                    .expect("writing to String cannot fail");
            }
            character => result.push(character),
        }
    }
    result.push('"');
    result
}
