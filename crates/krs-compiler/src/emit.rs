use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;

use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, CellAttribute, CellContentFrame, CellPost,
    ClaimModality, ConfigurationRoot, ContextAliasSentence, DefinitionClaimBinder, DefinitionIr,
    DefinitionModule, DefinitionRuleBody, DefinitionSentence, DefinitionSortRef, DefinitionTerm,
    DefinitionTermKind, FixedCell, FixedCellContent, FixedCellPattern, FixedConfiguration,
    FixedConfigurationVariable, FixedInitializerCell, FixedInitializerContent, FormatFragment,
    GrammarProductionItemKind, GroupAssociativity, LabelIdentity, ListOperation, MapOperation,
    ProductionAttribute, ProductionGroupId, ProductionSentence, RuleSentence, SemanticId,
    SentenceKind, SetOperation, SourceMapKey, StrictnessKind, SymbolId, SymbolIdentity,
};

use crate::sidecar::{GeneratedRanges, SidecarError};
use crate::{LoweredDefinition, SourceMap, SymbolMap};

/// Generated artifact holding the claim-free semantics.
pub const DEFINITION_ARTIFACT: &str = "definition.k";

/// Generated artifact holding the claims, present only when a claim exists.
pub const SPEC_ARTIFACT: &str = "spec.k";

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

impl fmt::Display for EmitError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsupportedShape { node, detail } => {
                write!(formatter, "unsupported source {node} shape: {detail}")
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
    let definition = lowered.definition();
    let context = EmitContext::new(definition);
    let mut writer = Writer::default();
    let mut claims = Vec::new();
    let mut modules = definition.modules().iter().collect::<Vec<_>>();
    modules.sort_by(|left, right| left.id().cmp(right.id()));
    for (index, module) in modules.into_iter().enumerate() {
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
    sorts: BTreeMap<SymbolId, &'a SymbolIdentity>,
    productions: BTreeMap<SymbolId, &'a ProductionSentence>,
    groups: BTreeMap<ProductionGroupId, &'a str>,
    non_associative_groups: BTreeSet<ProductionGroupId>,
    cells: BTreeMap<SymbolId, &'a str>,
    repeated_ancestors: BTreeMap<SymbolId, SymbolId>,
    context_aliases: BTreeMap<krs_ir::StableItemId, String>,
}

impl<'a> EmitContext<'a> {
    fn new(definition: &'a DefinitionIr) -> Self {
        let mut sorts = BTreeMap::new();
        let mut productions = BTreeMap::new();
        let mut groups = BTreeMap::new();
        let mut non_associative_groups = BTreeSet::new();
        let mut cells = BTreeMap::new();
        let mut repeated_ancestors = BTreeMap::new();
        let mut context_aliases = BTreeMap::new();
        for module in definition.modules() {
            for group in module.production_groups() {
                groups.insert(group.id().clone(), group.emitted_name());
            }
            for sentence in module.sentences() {
                if let DefinitionSentence::Associativity(associativity) = sentence
                    && associativity.associativity() == GroupAssociativity::NonAssociative
                {
                    non_associative_groups.extend(associativity.groups().iter().cloned());
                }
                if let DefinitionSentence::Configuration(configuration) = sentence {
                    collect_emit_cells(
                        configuration.cells(),
                        &mut cells,
                        &mut repeated_ancestors,
                        None,
                    );
                }
                if let DefinitionSentence::ContextAlias(alias) = sentence {
                    context_aliases.insert(alias.id().clone(), k_label_name(alias.name()));
                }
            }
        }
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
        Self {
            sorts,
            productions,
            groups,
            non_associative_groups,
            cells,
            repeated_ancestors,
            context_aliases,
        }
    }

    fn sort_name(&self, id: &SymbolId) -> Result<&str, EmitError> {
        self.sorts
            .get(id)
            .map(|symbol| symbol.emitted_name())
            .ok_or_else(|| {
                EmitError::InvalidReference(format!("missing source sort {:?}", id.as_str()))
            })
    }

    fn sort_name_ref(&self, sort: &DefinitionSortRef) -> Result<&str, EmitError> {
        match sort {
            DefinitionSortRef::Declared(id) => self.sort_name(id),
            DefinitionSortRef::Builtin(BuiltinSort::KSequence) => Ok("K"),
            DefinitionSortRef::Builtin(BuiltinSort::Int) => Ok("Int"),
            DefinitionSortRef::Builtin(BuiltinSort::Bool) => Ok("Bool"),
            DefinitionSortRef::Builtin(BuiltinSort::Id) => Ok("Id"),
            DefinitionSortRef::Builtin(BuiltinSort::Map) => Ok("Map"),
            DefinitionSortRef::Builtin(BuiltinSort::Bytes) => Ok("Bytes"),
            DefinitionSortRef::Builtin(BuiltinSort::String) => Ok("String"),
            DefinitionSortRef::Builtin(BuiltinSort::List) => Ok("List"),
            DefinitionSortRef::Builtin(BuiltinSort::Set) => Ok("Set"),
        }
    }

    fn production(&self, id: &SymbolId) -> Result<&ProductionSentence, EmitError> {
        self.productions.get(id).copied().ok_or_else(|| {
            EmitError::InvalidReference(format!("missing source production {:?}", id.as_str()))
        })
    }

    fn group_name(&self, id: &ProductionGroupId) -> Result<&str, EmitError> {
        self.groups.get(id).copied().ok_or_else(|| {
            EmitError::InvalidReference(format!("missing production group {:?}", id.as_str()))
        })
    }

    fn cell_name(&self, id: &SymbolId) -> Result<&str, EmitError> {
        self.cells.get(id).copied().ok_or_else(|| {
            EmitError::InvalidReference(format!("missing fixed cell {:?}", id.as_str()))
        })
    }

    fn repeated_ancestor(&self, id: &SymbolId) -> Option<&SymbolId> {
        self.repeated_ancestors.get(id)
    }

    fn context_alias_name(&self, id: &krs_ir::StableItemId) -> Result<&str, EmitError> {
        self.context_aliases
            .get(id)
            .map(String::as_str)
            .ok_or_else(|| EmitError::InvalidReference(format!("missing context alias {id:?}")))
    }

    fn is_non_associative(&self, group: &ProductionGroupId) -> bool {
        self.non_associative_groups.contains(group)
    }
}

fn collect_emit_cells<'a>(
    cells: &'a [FixedCell<DefinitionSortRef, SymbolId>],
    output: &mut BTreeMap<SymbolId, &'a str>,
    repeated_ancestors: &mut BTreeMap<SymbolId, SymbolId>,
    repeated_ancestor: Option<&SymbolId>,
) {
    for cell in cells {
        output.insert(cell.id().clone(), cell.name());
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
            collect_emit_cells(children, output, repeated_ancestors, repeated_ancestor);
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
    let mut imports = module
        .imports()
        .iter()
        .map(|import| import.as_str().to_owned())
        .collect::<Vec<_>>();
    imports.extend(builtin_imports(module));
    imports.sort();
    imports.dedup();
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

#[derive(Default)]
struct BuiltinRequirements {
    sorts: BTreeSet<BuiltinSort>,
    operations: BTreeSet<BuiltinSort>,
}

impl BuiltinRequirements {
    fn sort(&mut self, sort: &DefinitionSortRef) {
        if let DefinitionSortRef::Builtin(sort) = sort {
            self.sorts.insert(*sort);
        }
    }

    fn term(&mut self, term: &DefinitionTerm) {
        self.sort(term.sort());
        match term.kind() {
            DefinitionTermKind::Variable { .. } | DefinitionTermKind::Token { .. } => {}
            DefinitionTermKind::Application {
                application,
                arguments,
            } => {
                if let ApplicationRef::Builtin(operation) = application {
                    self.operations.insert(operation.result_sort());
                    for sort in operation.argument_sorts() {
                        self.operations.insert(*sort);
                    }
                }
                for argument in arguments {
                    self.term(argument);
                }
            }
            DefinitionTermKind::KSequence { item_sort, items } => {
                self.sort(item_sort);
                for item in items {
                    self.term(item);
                }
            }
            DefinitionTermKind::Map { arguments, .. } => {
                self.sorts.insert(BuiltinSort::Map);
                for argument in arguments {
                    self.term(argument);
                }
            }
            DefinitionTermKind::List { arguments, .. } => {
                self.sorts.insert(BuiltinSort::List);
                for argument in arguments {
                    self.term(argument);
                }
            }
            DefinitionTermKind::Set { arguments, .. } => {
                self.sorts.insert(BuiltinSort::Set);
                for argument in arguments {
                    self.term(argument);
                }
            }
            DefinitionTermKind::Rewrite { from, to } => {
                self.term(from);
                self.term(to);
            }
            DefinitionTermKind::Cell { children, .. } => {
                for child in children {
                    self.term(child);
                }
            }
        }
    }

    fn fixed_cells(&mut self, cells: &[FixedCell<DefinitionSortRef, SymbolId>]) {
        for cell in cells {
            match cell.content() {
                FixedCellContent::Term { sort } => self.sort(sort),
                FixedCellContent::Children { children } => self.fixed_cells(children),
            }
        }
    }

    fn initializer(&mut self, cells: &[FixedInitializerCell<SymbolId, DefinitionTerm>]) {
        for cell in cells {
            match cell.content() {
                FixedInitializerContent::Term { term } => self.term(term),
                FixedInitializerContent::Children { children } => self.initializer(children),
            }
        }
    }
}

fn builtin_imports(module: &DefinitionModule) -> Vec<String> {
    let mut requirements = BuiltinRequirements::default();
    for sentence in module.sentences() {
        match sentence {
            DefinitionSentence::SyntaxSort(_)
            | DefinitionSentence::Precedence(_)
            | DefinitionSentence::Associativity(_) => {}
            DefinitionSentence::Subsort(sentence) => {
                requirements.sort(sentence.subsort());
                requirements.sort(sentence.supersort());
            }
            DefinitionSentence::Production(sentence) => {
                requirements.sort(sentence.result_sort());
                for item in sentence.items() {
                    if let GrammarProductionItemKind::NonTerminal { sort, .. } = item.kind() {
                        requirements.sort(sort);
                    }
                }
                for attribute in sentence.attributes() {
                    if let ProductionAttribute::Strictness { result_sort, .. } = attribute {
                        requirements.sort(result_sort.sort());
                    }
                }
            }
            DefinitionSentence::Configuration(configuration) => {
                requirements.fixed_cells(configuration.cells());
                for variable in configuration.variables() {
                    requirements.sort(variable.sort());
                }
                requirements.initializer(configuration.initializer());
            }
            DefinitionSentence::ContextAlias(sentence) => {
                for variable in sentence.variables() {
                    requirements.sort(variable.sort());
                }
                for cell in sentence.body().cells() {
                    requirements.term(cell.pattern());
                }
            }
            DefinitionSentence::Rule(sentence) => {
                for variable in sentence.variables() {
                    requirements.sort(variable.sort());
                }
                match sentence.relational_body() {
                    DefinitionRuleBody::Term(term) => requirements.term(term),
                    DefinitionRuleBody::Configuration(rewrite) => {
                        for clause in rewrite.clauses() {
                            requirements.term(clause.before());
                            if let CellPost::Replace { term } = clause.after() {
                                requirements.term(term);
                            }
                        }
                    }
                }
                if let Some(condition) = sentence.requires() {
                    requirements.term(condition.term());
                }
            }
        }
    }
    let imports = requirements
        .sorts
        .into_iter()
        .filter_map(|sort| builtin_import(sort, &requirements.operations))
        .collect::<BTreeSet<_>>();
    imports.into_iter().map(str::to_owned).collect()
}

fn builtin_import(
    sort: BuiltinSort,
    operation_sorts: &BTreeSet<BuiltinSort>,
) -> Option<&'static str> {
    match sort {
        BuiltinSort::KSequence => None,
        BuiltinSort::Int => Some(if operation_sorts.contains(&BuiltinSort::Int) {
            "INT"
        } else {
            "INT-SYNTAX"
        }),
        BuiltinSort::Bool => Some(if operation_sorts.contains(&BuiltinSort::Bool) {
            "BOOL"
        } else {
            "BOOL-SYNTAX"
        }),
        BuiltinSort::Map => Some("MAP"),
        BuiltinSort::Id => Some("ID-SYNTAX"),
        BuiltinSort::Bytes => Some("BYTES"),
        BuiltinSort::String => Some("STRING-SYNTAX"),
        BuiltinSort::List => Some("LIST"),
        BuiltinSort::Set => Some("SET"),
    }
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
            writer.push(context.sort_name_ref(sentence.supersort())?);
            writer.push(" ::= ");
            writer.push(context.sort_name_ref(sentence.subsort())?);
        }
        DefinitionSentence::Production(sentence) => emit_production(sentence, context, writer)?,
        DefinitionSentence::Precedence(sentence) => {
            writer.push("syntax priority ");
            emit_group_list(sentence.higher(), context, writer)?;
            writer.push(" > ");
            emit_group_list(sentence.lower(), context, writer)?;
        }
        DefinitionSentence::Associativity(sentence) => {
            writer.push(match sentence.associativity() {
                GroupAssociativity::Left => "syntax left ",
                GroupAssociativity::Right => "syntax right ",
                GroupAssociativity::NonAssociative => "syntax non-assoc ",
            });
            emit_group_list(sentence.groups(), context, writer)?;
        }
        DefinitionSentence::Configuration(sentence) => {
            emit_fixed_configuration(sentence, context, writer)?;
        }
        DefinitionSentence::ContextAlias(sentence) => {
            emit_context_alias(sentence, context, writer)?;
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
    for attribute in sentence.attributes() {
        if let ProductionAttribute::Documentation { text, .. } = attribute {
            let start = writer.source.len();
            writer.push("// ");
            writer.push(text);
            writer.record(attribute.origin().key(), start, writer.source.len())?;
            writer.push("\n  ");
        }
    }
    writer.push("syntax ");
    writer.push(context.sort_name_ref(sentence.result_sort())?);
    writer.push(" ::= ");
    for (index, item) in sentence.items().iter().enumerate() {
        if index != 0 {
            writer.push(" ");
        }
        let start = writer.source.len();
        match item.kind() {
            GrammarProductionItemKind::Terminal { text } => writer.push(&quoted(text)),
            GrammarProductionItemKind::NonTerminal { sort, .. } => {
                writer.push(context.sort_name_ref(sort)?);
            }
            GrammarProductionItemKind::RegexTerminal { regex, .. } => {
                writer.push("r");
                writer.push(&quoted(regex));
            }
        }
        writer.record(item.origin().key(), start, writer.source.len())?;
    }
    // A token production denotes domain values of its sort, not a
    // constructor, so it carries no symbol: K's Haskell backend rejects a
    // constructor on a sort that has domain values. A bracket production is
    // parse-only, so no term contains its symbol; Java K declares a labelled
    // bracket as a constructor in definition.kore while k-rust declares none
    // (bracket-production-constructor), so an unlabelled bracket is the form
    // on which both routes agree.
    let is_parse_only = sentence.attributes().iter().any(|attribute| {
        matches!(
            attribute,
            ProductionAttribute::Token { .. } | ProductionAttribute::Bracket { .. }
        )
    });
    writer.push(" [");
    let mut first = true;
    if !is_parse_only {
        writer.push("symbol(");
        writer.push(sentence.symbol().emitted_name());
        writer.push(")");
        first = false;
    }
    for attribute in sentence.attributes() {
        if matches!(attribute, ProductionAttribute::Documentation { .. }) {
            continue;
        }
        if !first {
            writer.push(", ");
        }
        first = false;
        let start = writer.source.len();
        emit_production_attribute(attribute, sentence, context, writer)?;
        writer.record(attribute.origin().key(), start, writer.source.len())?;
    }
    writer.push("]");
    Ok(())
}

fn emit_group_list(
    groups: &[ProductionGroupId],
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    for (index, group) in groups.iter().enumerate() {
        if index != 0 {
            writer.push(" ");
        }
        writer.push(context.group_name(group)?);
    }
    Ok(())
}

#[allow(clippy::too_many_lines)]
fn emit_production_attribute(
    attribute: &krs_ir::DefinitionProductionAttribute,
    sentence: &ProductionSentence,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    match attribute {
        ProductionAttribute::Documentation { .. } => {}
        ProductionAttribute::Function { .. } => writer.push("function"),
        ProductionAttribute::Total { .. } => writer.push("total"),
        ProductionAttribute::Hook { operation, .. } => {
            writer.push("hook(");
            writer.push(match operation {
                krs_ir::HookOperation::KryptoKeccak256Raw => "KRYPTO.keccak256raw",
                krs_ir::HookOperation::KryptoSha256Raw => "KRYPTO.sha256raw",
                krs_ir::HookOperation::KryptoRipemd160Raw => "KRYPTO.ripemd160raw",
                krs_ir::HookOperation::KryptoEcdsaRecover => "KRYPTO.ecdsaRecover",
                krs_ir::HookOperation::KryptoBn128Valid => "KRYPTO.bn128valid",
                krs_ir::HookOperation::KryptoBn128Add => "KRYPTO.bn128add",
                krs_ir::HookOperation::KryptoBn128Mul => "KRYPTO.bn128mul",
                krs_ir::HookOperation::KryptoBn128G2Valid => "KRYPTO.bn128g2valid",
                krs_ir::HookOperation::KryptoBn128Ate => "KRYPTO.bn128ate",
            });
            writer.push(")");
        }
        ProductionAttribute::Alias { .. } => writer.push("alias"),
        ProductionAttribute::Token {
            lexical_precedence, ..
        } => {
            writer.push("token");
            if let Some(precedence) = lexical_precedence {
                writer.push(", prec(");
                writer.push(&precedence.to_string());
                writer.push(")");
            }
        }
        ProductionAttribute::Group { group, .. } => {
            writer.push("group(");
            writer.push(context.group_name(group)?);
            writer.push(")");
        }
        ProductionAttribute::Bracket { .. } => {
            writer.push("bracket, format(");
            for index in 1..=sentence.items().len() {
                writer.push("%");
                writer.push(&index.to_string());
            }
            writer.push(")");
        }
        ProductionAttribute::Avoid { .. } => writer.push("avoid"),
        ProductionAttribute::Format { fragments, .. } => {
            writer.push("format(");
            for fragment in fragments {
                match fragment {
                    FormatFragment::Literal(text) => {
                        for character in text.chars() {
                            if character == '%' {
                                writer.push("%%");
                            } else {
                                writer.push(&character.to_string());
                            }
                        }
                    }
                    FormatFragment::Item(index) => {
                        writer.push("%");
                        writer.push(&index.to_string());
                    }
                    FormatFragment::Newline => writer.push("%n"),
                    FormatFragment::Indent => writer.push("%i"),
                    FormatFragment::Dedent => writer.push("%d"),
                }
            }
            writer.push(")");
        }
        ProductionAttribute::Strictness {
            kind,
            using,
            fields,
            result_sort,
            ..
        } => {
            writer.push(match kind {
                StrictnessKind::Strict => "strict",
                StrictnessKind::SeqStrict => "seqstrict",
            });
            let nonterminals = sentence
                .items()
                .iter()
                .filter_map(|item| match item.kind() {
                    GrammarProductionItemKind::NonTerminal { field, .. } => Some(field),
                    _ => None,
                })
                .collect::<Vec<_>>();
            let selects_all = fields.len() == nonterminals.len()
                && fields
                    .iter()
                    .zip(&nonterminals)
                    .all(|(selected, field)| selected.field() == *field);
            if using.is_some() || !selects_all {
                writer.push("(");
                if let Some(using) = using {
                    let using_start = writer.source.len();
                    writer.push(context.context_alias_name(using.alias())?);
                    writer.record(using.origin().key(), using_start, writer.source.len())?;
                    if !fields.is_empty() {
                        writer.push("; ");
                    }
                }
                for (index, field) in fields.iter().enumerate() {
                    if index != 0 {
                        writer.push(",");
                    }
                    let position = nonterminals
                        .iter()
                        .position(|candidate| **candidate == *field.field())
                        .ok_or_else(|| {
                            EmitError::InvalidReference(format!(
                                "strictness references missing field {:?}",
                                field.field().as_str()
                            ))
                        })?;
                    let field_start = writer.source.len();
                    writer.push(&(position + 1).to_string());
                    writer.record(field.origin().key(), field_start, writer.source.len())?;
                }
                writer.push(")");
            }
            writer.push(", result(");
            let result_start = writer.source.len();
            writer.push(context.sort_name_ref(result_sort.sort())?);
            writer.record(
                result_sort.origin().key(),
                result_start,
                writer.source.len(),
            )?;
            writer.push(")");
        }
    }
    Ok(())
}

fn emit_fixed_configuration(
    configuration: &FixedConfiguration<DefinitionSortRef, SymbolId, DefinitionTerm>,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    writer.push("configuration");
    writer.push("\n");
    match configuration.root() {
        ConfigurationRoot::GeneratedTop => emit_fixed_cell_forest(
            configuration.cells(),
            configuration.initializer(),
            configuration.variables(),
            4,
            context,
            writer,
        )?,
        ConfigurationRoot::Named { origin, name } => {
            let start = writer.source.len();
            writer.push("    <");
            writer.push(name);
            writer.push(">\n");
            emit_fixed_cell_forest(
                configuration.cells(),
                configuration.initializer(),
                configuration.variables(),
                6,
                context,
                writer,
            )?;
            writer.push("    </");
            writer.push(name);
            writer.push(">");
            writer.record(origin.key(), start, writer.source.len())?;
        }
    }
    writer.record(
        configuration.initializer_origin().key(),
        writer.source.len(),
        writer.source.len(),
    )?;
    writer.push("\n");
    Ok(())
}

fn emit_fixed_cell_forest(
    cells: &[FixedCell<DefinitionSortRef, SymbolId>],
    initializer: &[FixedInitializerCell<SymbolId, DefinitionTerm>],
    variables: &[FixedConfigurationVariable<DefinitionSortRef>],
    indent: usize,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    for (index, cell) in cells.iter().enumerate() {
        if index != 0 {
            writer.push("\n");
        }
        let initialized_cell = initializer
            .iter()
            .find(|value| value.cell() == cell.id())
            .ok_or_else(|| {
                EmitError::InvalidReference(format!(
                    "missing initializer for fixed cell {:?}",
                    cell.id().as_str()
                ))
            })?;
        emit_fixed_cell(cell, initialized_cell, variables, indent, context, writer)?;
    }
    Ok(())
}

fn emit_fixed_cell(
    cell: &FixedCell<DefinitionSortRef, SymbolId>,
    initializer_cell: &FixedInitializerCell<SymbolId, DefinitionTerm>,
    variables: &[FixedConfigurationVariable<DefinitionSortRef>],
    indent: usize,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    let start = writer.source.len();
    writer.push(&" ".repeat(indent));
    writer.push("<");
    writer.push(cell.name());
    for attribute in cell.attributes() {
        match attribute {
            CellAttribute::Color { origin, value } => {
                let attribute_start = writer.source.len();
                writer.push(" color=");
                writer.push(&quoted(value.as_str()));
                writer.record(origin.key(), attribute_start, writer.source.len())?;
            }
            CellAttribute::Multiplicity { origin, value } => {
                let attribute_start = writer.source.len();
                writer.push(" multiplicity=");
                writer.push(&quoted(value.as_str()));
                writer.record(origin.key(), attribute_start, writer.source.len())?;
            }
            CellAttribute::CollectionType { origin, value } => {
                let attribute_start = writer.source.len();
                writer.push(" type=");
                writer.push(&quoted(value.as_str()));
                writer.record(origin.key(), attribute_start, writer.source.len())?;
            }
        }
    }
    writer.push(">");
    match (cell.content(), initializer_cell.content()) {
        (FixedCellContent::Term { .. }, FixedInitializerContent::Term { term }) => {
            writer.push(" ");
            emit_initializer_term(term, variables, context, writer)?;
            writer.push(" </");
            writer.push(cell.name());
            writer.push(">");
        }
        (
            FixedCellContent::Children { children },
            FixedInitializerContent::Children {
                children: initialized_children,
            },
        ) => {
            writer.push("\n");
            emit_fixed_cell_forest(
                children,
                initialized_children,
                variables,
                indent + 2,
                context,
                writer,
            )?;
            writer.push("\n");
            writer.push(&" ".repeat(indent));
            writer.push("</");
            writer.push(cell.name());
            writer.push(">");
        }
        _ => {
            return Err(EmitError::InvalidReference(format!(
                "fixed cell {:?} and initializer shapes disagree",
                cell.id().as_str()
            )));
        }
    }
    writer.record(initializer_cell.origin().key(), start, writer.source.len())?;
    writer.record(cell.origin().key(), start, writer.source.len())?;
    Ok(())
}

fn emit_initializer_term(
    term: &DefinitionTerm,
    variables: &[FixedConfigurationVariable<DefinitionSortRef>],
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    let (term, sequence_origin) = match term.kind() {
        DefinitionTermKind::KSequence { items, .. } if items.len() == 1 => (&items[0], Some(term)),
        _ => (term, None),
    };
    if let DefinitionTermKind::Variable { variable } = term.kind()
        && let Some(declaration) = variables.iter().find(|value| value.id() == variable)
    {
        let start = writer.source.len();
        writer.push("$");
        writer.push(declaration.external_name());
        writer.push(":");
        writer.push(context.sort_name_ref(term.sort())?);
        writer.record(term.origin().key(), start, writer.source.len())?;
        writer.record(declaration.origin().key(), start, writer.source.len())?;
        if let Some(sequence) = sequence_origin {
            writer.record(sequence.origin().key(), start, writer.source.len())?;
        }
    } else {
        writer.append_rendered(render_term(term, context, false)?)?;
    }
    Ok(())
}

fn emit_rule(
    sentence: &RuleSentence,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    let sentence_start = writer.source.len();
    if let DefinitionRuleBody::Configuration(body) = sentence.relational_body() {
        if sentence.kind() == SentenceKind::Claim {
            let claim_start = writer.source.len();
            writer.push("claim");
            if let Some(claim) = sentence.claim()
                && claim.modality() == ClaimModality::AllPaths
            {
                writer.record(
                    claim.modality_origin().key(),
                    claim_start,
                    writer.source.len(),
                )?;
            }
            writer.push(" [");
        } else {
            writer.push("rule [");
        }
        emit_label(sentence.label(), writer);
        writer.push("]:");
        let mut emitted_repeated = BTreeSet::new();
        for clause in body.clauses() {
            let Some(ancestor) = context.repeated_ancestor(clause.cell()) else {
                writer.push("\n");
                emit_cell_clause(clause, sentence, context, 4, writer)?;
                continue;
            };
            if !emitted_repeated.insert(ancestor.clone()) {
                continue;
            }
            writer.push("\n    <");
            writer.push(context.cell_name(ancestor)?);
            writer.push(">");
            for nested in body
                .clauses()
                .iter()
                .filter(|candidate| context.repeated_ancestor(candidate.cell()) == Some(ancestor))
            {
                writer.push("\n");
                emit_cell_clause(nested, sentence, context, 8, writer)?;
            }
            writer.push("\n        ...\n    </");
            writer.push(context.cell_name(ancestor)?);
            writer.push(">");
        }
        emit_requires(sentence, context, writer)?;
        emit_ensures(sentence, context, writer)?;
        emit_rule_attributes(sentence, writer)?;
        record_claim_binders(sentence, context, sentence_start, writer)?;
        return Ok(());
    }
    let DefinitionRuleBody::Term(body) = sentence.relational_body() else {
        unreachable!()
    };
    writer.push("rule ");
    writer.append_rendered(render_rule_term(body, sentence, context, true)?)?;
    emit_requires(sentence, context, writer)?;
    emit_term_rule_attributes(sentence, writer)?;
    Ok(())
}

fn emit_term_rule_attributes(
    sentence: &RuleSentence,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    writer.push(" [");
    if let Some(simplification) = sentence.simplification() {
        let start = writer.source.len();
        writer.push("simplification");
        if let Some(priority) = simplification.priority() {
            writer.push("(");
            let priority_start = writer.source.len();
            writer.push(&priority.value().to_string());
            writer.record(priority.origin().key(), priority_start, writer.source.len())?;
            writer.push(")");
        }
        writer.record(simplification.origin().key(), start, writer.source.len())?;
        writer.push(", ");
    }
    if let Some(priority) = sentence.priority() {
        let start = writer.source.len();
        writer.push("priority(");
        writer.push(&priority.value().to_string());
        writer.push("), ");
        writer.record(priority.origin().key(), start, writer.source.len() - 2)?;
    }
    writer.push("label(");
    emit_label(sentence.label(), writer);
    writer.push(")]");
    Ok(())
}

fn record_claim_binders(
    sentence: &RuleSentence,
    context: &EmitContext<'_>,
    sentence_start: usize,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    let Some(claim) = sentence.claim() else {
        return Ok(());
    };
    for (binder, existential) in claim
        .universals()
        .iter()
        .map(|binder| (binder, false))
        .chain(claim.existentials().iter().map(|binder| (binder, true)))
    {
        let name = if existential {
            format!("?{}", binder.id().as_str().to_ascii_uppercase())
        } else {
            variable_name(binder.id())
        };
        let rendered = format!("{name}:{}", context.sort_name_ref(binder.sort())?);
        let relative = writer.source[sentence_start..]
            .find(&rendered)
            .ok_or_else(|| {
                EmitError::InvalidReference(format!(
                    "claim binder {:?} has no rendered occurrence",
                    binder.id().as_str()
                ))
            })?;
        let start = sentence_start + relative;
        let end = start + rendered.len();
        for origin in [binder.origin(), binder.name_origin(), binder.sort_origin()] {
            writer.record(origin.key(), start, end)?;
        }
    }
    Ok(())
}

fn emit_ensures(
    sentence: &RuleSentence,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    let Some(ensures) = sentence.claim().and_then(|claim| claim.ensures()) else {
        return Ok(());
    };
    writer.push("\n    ensures ");
    let start = writer.source.len();
    writer.append_rendered(render_rule_term(ensures.term(), sentence, context, false)?)?;
    writer.record(ensures.origin().key(), start, writer.source.len())?;
    Ok(())
}

fn emit_rule_attributes(sentence: &RuleSentence, writer: &mut Writer) -> Result<(), EmitError> {
    let mut attributes = Vec::<(
        &str,
        Option<u32>,
        Option<&krs_ir::NodeOrigin>,
        Option<&krs_ir::NodeOrigin>,
    )>::new();
    if let Some(priority) = sentence.priority() {
        attributes.push((
            "priority",
            Some(priority.value()),
            Some(priority.origin()),
            None,
        ));
    }
    if let Some(simplification) = sentence.simplification() {
        attributes.push((
            "simplification",
            simplification
                .priority()
                .map(krs_ir::DefinitionSimplificationPriority::value),
            Some(simplification.origin()),
            simplification
                .priority()
                .map(krs_ir::DefinitionSimplificationPriority::origin),
        ));
    }
    if let Some(claim) = sentence.claim() {
        if claim.modality() == ClaimModality::OnePath {
            attributes.push(("one-path", None, Some(claim.modality_origin()), None));
        }
        if let Some(origin) = claim.circularity_origin() {
            attributes.push(("circularity", None, Some(origin), None));
        }
    }
    if attributes.is_empty() {
        return Ok(());
    }
    writer.push("\n    [");
    for (index, (name, value, origin, value_origin)) in attributes.into_iter().enumerate() {
        if index != 0 {
            writer.push(", ");
        }
        let start = writer.source.len();
        writer.push(name);
        if let Some(value) = value {
            writer.push("(");
            let value_start = writer.source.len();
            writer.push(&value.to_string());
            if let Some(value_origin) = value_origin {
                writer.record(value_origin.key(), value_start, writer.source.len())?;
            }
            writer.push(")");
        }
        if let Some(origin) = origin {
            writer.record(origin.key(), start, writer.source.len())?;
        }
    }
    writer.push("]");
    Ok(())
}

fn emit_requires(
    sentence: &RuleSentence,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    if let Some(condition) = sentence.requires() {
        writer.push("\n    requires ");
        let start = writer.source.len();
        writer.append_rendered(render_rule_term(
            condition.term(),
            sentence,
            context,
            false,
        )?)?;
        writer.record(condition.origin().key(), start, writer.source.len())?;
    }
    Ok(())
}

fn emit_cell_clause(
    clause: &krs_ir::FixedCellClause<SymbolId, DefinitionTerm>,
    sentence: &RuleSentence,
    context: &EmitContext<'_>,
    indent: usize,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    let start = writer.source.len();
    let name = context.cell_name(clause.cell())?;
    writer.push(&" ".repeat(indent));
    writer.push("<");
    writer.push(name);
    writer.push("> ");
    writer.append_rendered(render_rule_term(clause.before(), sentence, context, false)?)?;
    match clause.after() {
        CellPost::Preserve => emit_single_frame(clause.frame(), writer)?,
        CellPost::Replace { term } => {
            match clause.frame() {
                CellContentFrame::KSequenceTail {
                    binding: Some(binding),
                    ..
                } => emit_named_frame_suffix(writer, binding, "K", " ~> "),
                CellContentFrame::MapRemainder {
                    binding: Some(binding),
                    ..
                } => emit_named_frame_suffix(writer, binding, "Map", " "),
                CellContentFrame::Exact
                | CellContentFrame::KSequenceTail { binding: None, .. }
                | CellContentFrame::MapRemainder { binding: None, .. } => {}
            }
            writer.push(" => ");
            writer.append_rendered(render_rule_term(term, sentence, context, false)?)?;
            emit_single_frame(clause.frame(), writer)?;
        }
    }
    writer.push(" </");
    writer.push(name);
    writer.push(">");
    writer.record(clause.origin().key(), start, writer.source.len())?;
    Ok(())
}

fn emit_single_frame(frame: &CellContentFrame, writer: &mut Writer) -> Result<(), EmitError> {
    match frame {
        CellContentFrame::Exact => {}
        CellContentFrame::KSequenceTail { origin, binding } => {
            let frame_start = writer.source.len();
            if let Some(binding) = binding {
                emit_named_frame_suffix(writer, binding, "K", " ~> ");
            } else {
                writer.push(" ...");
            }
            writer.record(origin.key(), frame_start, writer.source.len())?;
        }
        CellContentFrame::MapRemainder { origin, binding } => {
            let frame_start = writer.source.len();
            if let Some(binding) = binding {
                emit_named_frame_suffix(writer, binding, "Map", " ");
            } else {
                writer.push(" ...");
            }
            writer.record(origin.key(), frame_start, writer.source.len())?;
        }
    }
    Ok(())
}

fn emit_named_frame_suffix(writer: &mut Writer, binding: &SemanticId, sort: &str, separator: &str) {
    writer.push(separator);
    writer.push(&variable_name(binding));
    writer.push(":");
    writer.push(sort);
}

fn emit_context_alias(
    sentence: &ContextAliasSentence,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    writer.push("context alias [");
    let name_start = writer.source.len();
    writer.push(&k_label_name(sentence.name()));
    writer.record(
        sentence.name_origin().key(),
        name_start,
        writer.source.len(),
    )?;
    writer.push("]:");
    for cell in sentence.body().cells() {
        writer.push("\n");
        emit_context_alias_cell(cell, sentence, context, writer)?;
    }
    Ok(())
}

fn emit_context_alias_cell(
    cell: &FixedCellPattern<SymbolId, DefinitionTerm>,
    sentence: &ContextAliasSentence,
    context: &EmitContext<'_>,
    writer: &mut Writer,
) -> Result<(), EmitError> {
    let start = writer.source.len();
    let name = context.cell_name(cell.cell())?;
    writer.push("    <");
    writer.push(name);
    writer.push("> ");
    writer.append_rendered(render_context_term(
        cell.pattern(),
        sentence.here(),
        sentence.here_origin(),
        context,
    )?)?;
    match cell.frame() {
        CellContentFrame::Exact => {}
        CellContentFrame::KSequenceTail { origin, binding } => {
            let frame_start = writer.source.len();
            if let Some(binding) = binding {
                writer.push(" ~> ");
                writer.push(&variable_name(binding));
                writer.push(":K");
            } else {
                writer.push(" ...");
            }
            writer.record(origin.key(), frame_start, writer.source.len())?;
        }
        CellContentFrame::MapRemainder { origin, binding } => {
            let frame_start = writer.source.len();
            writer.push(" ");
            if let Some(binding) = binding {
                writer.push(&variable_name(binding));
                writer.push(":Map");
            } else {
                writer.push("...");
            }
            writer.record(origin.key(), frame_start, writer.source.len())?;
        }
    }
    writer.push(" </");
    writer.push(name);
    writer.push(">");
    writer.record(cell.origin().key(), start, writer.source.len())?;
    Ok(())
}

fn render_context_term(
    term: &DefinitionTerm,
    here: &SemanticId,
    here_origin: &krs_ir::NodeOrigin,
    context: &EmitContext<'_>,
) -> Result<Rendered, EmitError> {
    if matches!(term.kind(), DefinitionTermKind::Variable { variable } if variable == here) {
        let mut output = Rendered::default();
        output.push("HERE");
        output.ranges.push((term.origin().key().clone(), 0, 4));
        output.ranges.push((here_origin.key().clone(), 0, 4));
        return Ok(output);
    }
    if let DefinitionTermKind::KSequence { items, .. } = term.kind() {
        let mut output = Rendered::default();
        for (index, item) in items.iter().enumerate() {
            if index != 0 {
                output.push(" ~> ");
            }
            output.append(render_context_term(item, here, here_origin, context)?);
        }
        if items.is_empty() {
            output.push(".K");
        }
        return Ok(output.finish(term.origin().key(), 0));
    }
    render_term(term, context, false)
}

fn emit_label(label: &LabelIdentity, writer: &mut Writer) {
    writer.push(label.emitted_name());
}

fn k_label_name(value: &str) -> String {
    let mut output = String::with_capacity(value.len());
    let mut uppercase_next = false;
    for character in value.chars() {
        if character == '_' {
            uppercase_next = true;
        } else if uppercase_next {
            output.extend(character.to_uppercase());
            uppercase_next = false;
        } else {
            output.push(character);
        }
    }
    output
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
    render_term_with_binders(term, context, root_rewrite, &[])
}

fn render_rule_term(
    term: &DefinitionTerm,
    sentence: &RuleSentence,
    context: &EmitContext<'_>,
    root_rewrite: bool,
) -> Result<Rendered, EmitError> {
    let existentials = sentence
        .claim()
        .map_or(&[][..], |claim| claim.existentials());
    render_term_with_binders(term, context, root_rewrite, existentials)
}

#[allow(clippy::too_many_lines)]
fn render_term_with_binders(
    term: &DefinitionTerm,
    context: &EmitContext<'_>,
    root_rewrite: bool,
    existentials: &[DefinitionClaimBinder],
) -> Result<Rendered, EmitError> {
    let mut output = Rendered::default();
    let start = 0;
    match term.kind() {
        DefinitionTermKind::Variable { variable } => {
            if variable.as_str().starts_with("__krs_wildcard_") {
                output.push("_");
            } else if let Some(name) = anonymous_name(variable) {
                output.push(name);
                output.push(":");
                output.push(context.sort_name_ref(term.sort())?);
            } else if existentials.iter().any(|binder| binder.id() == variable) {
                output.push("?");
                output.push(&variable.as_str().to_ascii_uppercase());
                output.push(":");
                output.push(context.sort_name_ref(term.sort())?);
            } else {
                output.push(&variable_name(variable));
                output.push(":");
                output.push(context.sort_name_ref(term.sort())?);
            }
        }
        DefinitionTermKind::Application {
            application,
            arguments,
        } => {
            if let ApplicationRef::Builtin(operation) = application {
                render_builtin_application(
                    *operation,
                    arguments,
                    context,
                    existentials,
                    &mut output,
                )?;
                return Ok(output.finish(term.origin().key(), start));
            }
            let ApplicationRef::Declared(symbol) = application else {
                unreachable!()
            };
            let production = context.production(symbol)?;
            let mut arguments = arguments.iter();
            for (index, item) in production.items().iter().enumerate() {
                if index != 0 {
                    output.push(" ");
                }
                match item.kind() {
                    GrammarProductionItemKind::Terminal { text } => output.push(text),
                    GrammarProductionItemKind::NonTerminal { .. } => {
                        let Some(argument) = arguments.next() else {
                            return Err(EmitError::InvalidReference(format!(
                                "production {:?} has fewer application arguments than nonterminals",
                                symbol.as_str()
                            )));
                        };
                        let parenthesize =
                            parenthesize_declared_child(production, argument, context)?;
                        if parenthesize {
                            output.push("(");
                        }
                        output.append(render_term_with_binders(
                            argument,
                            context,
                            false,
                            existentials,
                        )?);
                        if parenthesize {
                            output.push(")");
                        }
                    }
                    GrammarProductionItemKind::RegexTerminal { .. } => {
                        return Err(EmitError::UnsupportedShape {
                            node: "regex application",
                            detail: "regex productions are not term constructors".to_owned(),
                        });
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
            if matches!(term.sort(), DefinitionSortRef::Builtin(_)) {
                output.push(value);
            } else {
                output.push("#token(");
                output.push(&quoted(value));
                output.push(",");
                output.push(&quoted(context.sort_name_ref(term.sort())?));
                output.push(")");
            }
        }
        DefinitionTermKind::KSequence { items, .. } => {
            if items.is_empty() {
                output.push(".K");
            } else {
                for (index, item) in items.iter().enumerate() {
                    if index != 0 {
                        output.push(" ~> ");
                    }
                    output.append(render_term_with_binders(
                        item,
                        context,
                        false,
                        existentials,
                    )?);
                }
            }
        }
        DefinitionTermKind::Map {
            operation,
            arguments,
        } => render_map(
            term.sort(),
            *operation,
            arguments,
            context,
            existentials,
            &mut output,
        )?,
        DefinitionTermKind::List {
            operation,
            arguments,
        } => render_list(
            term.sort(),
            *operation,
            arguments,
            context,
            existentials,
            &mut output,
        )?,
        DefinitionTermKind::Set {
            operation,
            arguments,
        } => render_set(*operation, arguments, context, existentials, &mut output)?,
        DefinitionTermKind::Cell { cell, children } => {
            let name = context.cell_name(cell)?;
            output.push("<");
            output.push(name);
            output.push(">");
            if !children.is_empty() {
                output.push(" ");
            }
            for (index, child) in children.iter().enumerate() {
                if index != 0 {
                    output.push(" ");
                }
                output.append(render_term_with_binders(
                    child,
                    context,
                    false,
                    existentials,
                )?);
            }
            if !children.is_empty() {
                output.push(" ");
            }
            output.push("</");
            output.push(name);
            output.push(">");
        }
        DefinitionTermKind::Rewrite { from, to } => {
            if !root_rewrite {
                output.push("(");
            }
            output.append(render_term_with_binders(
                from,
                context,
                false,
                existentials,
            )?);
            output.push(" => ");
            output.append(render_term_with_binders(to, context, false, existentials)?);
            if !root_rewrite {
                output.push(")");
            }
        }
    }
    Ok(output.finish(term.origin().key(), start))
}

fn parenthesize_declared_child(
    parent: &ProductionSentence,
    child: &DefinitionTerm,
    context: &EmitContext<'_>,
) -> Result<bool, EmitError> {
    let Some(parent_group) = production_group(parent) else {
        return Ok(false);
    };
    let prefix_unary = matches!(
        parent.items(),
        [terminal, nonterminal]
            if matches!(terminal.kind(), GrammarProductionItemKind::Terminal { .. })
                && matches!(
                    nonterminal.kind(),
                    GrammarProductionItemKind::NonTerminal { .. }
                )
    );
    if !context.is_non_associative(parent_group) && !prefix_unary {
        return Ok(false);
    }
    let DefinitionTermKind::Application {
        application: ApplicationRef::Declared(child_symbol),
        ..
    } = child.kind()
    else {
        return Ok(false);
    };
    Ok(production_group(context.production(child_symbol)?).is_some())
}

fn production_group(production: &ProductionSentence) -> Option<&ProductionGroupId> {
    production
        .attributes()
        .iter()
        .find_map(|attribute| match attribute {
            ProductionAttribute::Group { group, .. } => Some(group),
            _ => None,
        })
}

#[allow(clippy::too_many_lines)] // Exhaustively renders the closed builtin-operation catalog.
fn render_builtin_application(
    operation: BuiltinOperation,
    arguments: &[DefinitionTerm],
    context: &EmitContext<'_>,
    existentials: &[DefinitionClaimBinder],
    output: &mut Rendered,
) -> Result<(), EmitError> {
    if operation == BuiltinOperation::BytesEmpty {
        if !arguments.is_empty() {
            return Err(EmitError::InvalidReference(format!(
                "builtin operation {operation:?} has invalid arity {}",
                arguments.len()
            )));
        }
        output.push(".Bytes");
        return Ok(());
    }
    if operation == BuiltinOperation::BytesLength {
        if arguments.len() != 1 {
            return Err(EmitError::InvalidReference(format!(
                "builtin operation {operation:?} has invalid arity {}",
                arguments.len()
            )));
        }
        output.push("lengthBytes(");
        output.append(render_term_with_binders(
            &arguments[0],
            context,
            false,
            existentials,
        )?);
        output.push(")");
        return Ok(());
    }
    if operation == BuiltinOperation::BytesGet {
        if arguments.len() != 2 {
            return Err(EmitError::InvalidReference(format!(
                "builtin operation {operation:?} has invalid arity {}",
                arguments.len()
            )));
        }
        output.append(render_builtin_argument(
            &arguments[0],
            context,
            existentials,
        )?);
        output.push(" [ ");
        output.append(render_builtin_argument(
            &arguments[1],
            context,
            existentials,
        )?);
        output.push(" ]");
        return Ok(());
    }
    if operation == BuiltinOperation::BytesUpdate {
        if arguments.len() != 3 {
            return Err(EmitError::InvalidReference(format!(
                "builtin operation {operation:?} has invalid arity {}",
                arguments.len()
            )));
        }
        output.append(render_builtin_argument(
            &arguments[0],
            context,
            existentials,
        )?);
        output.push(" [ ");
        output.append(render_builtin_argument(
            &arguments[1],
            context,
            existentials,
        )?);
        output.push(" <- ");
        output.append(render_builtin_argument(
            &arguments[2],
            context,
            existentials,
        )?);
        output.push(" ]");
        return Ok(());
    }
    if operation == BuiltinOperation::BytesPadRight {
        if arguments.len() != 3 {
            return Err(EmitError::InvalidReference(format!(
                "builtin operation {operation:?} has invalid arity {}",
                arguments.len()
            )));
        }
        output.push("padRightBytes(");
        for (index, argument) in arguments.iter().enumerate() {
            if index > 0 {
                output.push(", ");
            }
            output.append(render_term_with_binders(
                argument,
                context,
                false,
                existentials,
            )?);
        }
        output.push(")");
        return Ok(());
    }
    if operation == BuiltinOperation::BytesSubstring {
        if arguments.len() != 3 {
            return Err(EmitError::InvalidReference(format!(
                "builtin operation {operation:?} has invalid arity {}",
                arguments.len()
            )));
        }
        output.push("substrBytes(");
        for (index, argument) in arguments.iter().enumerate() {
            if index > 0 {
                output.push(", ");
            }
            output.append(render_term_with_binders(
                argument,
                context,
                false,
                existentials,
            )?);
        }
        output.push(")");
        return Ok(());
    }
    if operation == BuiltinOperation::IntPowMod {
        if arguments.len() != 3 {
            return Err(EmitError::InvalidReference(format!(
                "builtin operation {operation:?} has invalid arity {}",
                arguments.len()
            )));
        }
        output.append(render_builtin_argument(
            &arguments[0],
            context,
            existentials,
        )?);
        output.push(" ^%Int ");
        output.append(render_builtin_argument(
            &arguments[1],
            context,
            existentials,
        )?);
        output.push(" ");
        output.append(render_builtin_argument(
            &arguments[2],
            context,
            existentials,
        )?);
        return Ok(());
    }
    if operation == BuiltinOperation::IntLog2 {
        if arguments.len() != 1 {
            return Err(EmitError::InvalidReference(format!(
                "builtin operation {operation:?} has invalid arity {}",
                arguments.len()
            )));
        }
        output.push("log2Int(");
        output.append(render_term_with_binders(
            &arguments[0],
            context,
            false,
            existentials,
        )?);
        output.push(")");
        return Ok(());
    }
    let (prefix, infix, expected) = match operation {
        BuiltinOperation::IntAdd => (None, Some("+Int"), 2),
        BuiltinOperation::IntSub => (None, Some("-Int"), 2),
        BuiltinOperation::IntMul => (None, Some("*Int"), 2),
        BuiltinOperation::IntTDiv => (None, Some("/Int"), 2),
        BuiltinOperation::IntMod => (None, Some("modInt"), 2),
        BuiltinOperation::IntPowMod => unreachable!("modular power is rendered above"),
        BuiltinOperation::IntLog2 => unreachable!("integer logarithm is rendered above"),
        BuiltinOperation::IntShiftRight => (None, Some(">>Int"), 2),
        BuiltinOperation::IntShiftLeft => (None, Some("<<Int"), 2),
        BuiltinOperation::IntBitAnd => (None, Some("&Int"), 2),
        BuiltinOperation::IntBitXor => (None, Some("xorInt"), 2),
        BuiltinOperation::IntBitOr => (None, Some("|Int"), 2),
        BuiltinOperation::IntGreaterEqual => (None, Some(">=Int"), 2),
        BuiltinOperation::IntGreater => (None, Some(">Int"), 2),
        BuiltinOperation::IntLessEqual => (None, Some("<=Int"), 2),
        BuiltinOperation::IntLess => (None, Some("<Int"), 2),
        BuiltinOperation::IntEqual => (None, Some("==Int"), 2),
        BuiltinOperation::IntNotEqual => (None, Some("=/=Int"), 2),
        BuiltinOperation::BoolNot => (Some("notBool"), None, 1),
        BuiltinOperation::BoolEqual => (None, Some("==Bool"), 2),
        BuiltinOperation::BoolNotEqual => (None, Some("=/=Bool"), 2),
        BuiltinOperation::BoolAnd => (None, Some("andBool"), 2),
        BuiltinOperation::BoolOr => (None, Some("orBool"), 2),
        BuiltinOperation::BytesLength => unreachable!("Bytes length is rendered above"),
        BuiltinOperation::BytesGet => unreachable!("byte lookup is rendered above"),
        BuiltinOperation::BytesEmpty => unreachable!("empty Bytes is rendered above"),
        BuiltinOperation::BytesUpdate => unreachable!("byte update is rendered above"),
        BuiltinOperation::BytesPadRight => unreachable!("Bytes padding is rendered above"),
        BuiltinOperation::BytesSubstring => unreachable!("Bytes substring is rendered above"),
    };
    if arguments.len() != expected {
        return Err(EmitError::InvalidReference(format!(
            "builtin operation {operation:?} has invalid arity {}",
            arguments.len()
        )));
    }
    if let Some(prefix) = prefix {
        output.push(prefix);
        output.push(" ");
        output.append(render_builtin_argument(
            &arguments[0],
            context,
            existentials,
        )?);
    } else if let Some(infix) = infix {
        output.append(render_builtin_argument(
            &arguments[0],
            context,
            existentials,
        )?);
        output.push(" ");
        output.push(infix);
        output.push(" ");
        output.append(render_builtin_argument(
            &arguments[1],
            context,
            existentials,
        )?);
    }
    Ok(())
}

fn render_builtin_argument(
    argument: &DefinitionTerm,
    context: &EmitContext<'_>,
    existentials: &[DefinitionClaimBinder],
) -> Result<Rendered, EmitError> {
    let parenthesize = matches!(
        argument.kind(),
        DefinitionTermKind::Application {
            application: ApplicationRef::Builtin(_),
            ..
        }
    );
    let mut output = Rendered::default();
    if parenthesize {
        output.push("(");
    }
    output.append(render_term_with_binders(
        argument,
        context,
        false,
        existentials,
    )?);
    if parenthesize {
        output.push(")");
    }
    Ok(output)
}

fn render_map(
    result_sort: &DefinitionSortRef,
    operation: MapOperation,
    arguments: &[DefinitionTerm],
    context: &EmitContext<'_>,
    existentials: &[DefinitionClaimBinder],
    output: &mut Rendered,
) -> Result<(), EmitError> {
    match operation {
        MapOperation::Empty if arguments.is_empty() => output.push(".Map"),
        MapOperation::Item if !arguments.is_empty() && arguments.len().is_multiple_of(2) => {
            for (index, pair) in arguments.as_chunks::<2>().0.iter().enumerate() {
                if index != 0 {
                    output.push(" ");
                }
                output.append(render_term_with_binders(
                    &pair[0],
                    context,
                    false,
                    existentials,
                )?);
                output.push(" |-> ");
                output.append(render_term_with_binders(
                    &pair[1],
                    context,
                    false,
                    existentials,
                )?);
            }
        }
        MapOperation::Update if arguments.len() == 3 => {
            output.append(render_term_with_binders(
                &arguments[0],
                context,
                false,
                existentials,
            )?);
            output.push(" [ ");
            output.append(render_term_with_binders(
                &arguments[1],
                context,
                false,
                existentials,
            )?);
            output.push(" <- ");
            output.append(render_term_with_binders(
                &arguments[2],
                context,
                false,
                existentials,
            )?);
            output.push(" ]");
        }
        MapOperation::Get if arguments.len() == 2 => {
            output.push("{");
            output.append(render_term_with_binders(
                &arguments[0],
                context,
                false,
                existentials,
            )?);
            output.push(" [ ");
            output.append(render_term_with_binders(
                &arguments[1],
                context,
                false,
                existentials,
            )?);
            output.push(" ]}:>");
            output.push(context.sort_name_ref(result_sort)?);
        }
        MapOperation::InKeys if arguments.len() == 2 => {
            output.append(render_term_with_binders(
                &arguments[0],
                context,
                false,
                existentials,
            )?);
            output.push(" in_keys(");
            output.append(render_term_with_binders(
                &arguments[1],
                context,
                false,
                existentials,
            )?);
            output.push(")");
        }
        _ => {
            return Err(EmitError::InvalidReference(format!(
                "Map operation {operation:?} has invalid arity {}",
                arguments.len()
            )));
        }
    }
    Ok(())
}

fn render_set(
    operation: SetOperation,
    arguments: &[DefinitionTerm],
    context: &EmitContext<'_>,
    existentials: &[DefinitionClaimBinder],
    output: &mut Rendered,
) -> Result<(), EmitError> {
    let render = |argument: &DefinitionTerm| {
        render_term_with_binders(argument, context, false, existentials)
    };
    match operation {
        SetOperation::Empty if arguments.is_empty() => output.push(".Set"),
        SetOperation::Item if arguments.len() == 1 => {
            output.push("SetItem(");
            output.append(render(&arguments[0])?);
            output.push(")");
        }
        SetOperation::Concat if arguments.len() == 2 => {
            output.append(render(&arguments[0])?);
            output.push(" ");
            output.append(render(&arguments[1])?);
        }
        SetOperation::Union if arguments.len() == 2 => {
            output.append(render(&arguments[0])?);
            output.push(" |Set ");
            output.append(render(&arguments[1])?);
        }
        SetOperation::Contains if arguments.len() == 2 => {
            output.append(render(&arguments[0])?);
            output.push(" in ");
            output.append(render(&arguments[1])?);
        }
        _ => {
            return Err(EmitError::InvalidReference(format!(
                "Set operation {operation:?} has invalid arity {}",
                arguments.len()
            )));
        }
    }
    Ok(())
}

fn render_list(
    result_sort: &DefinitionSortRef,
    operation: ListOperation,
    arguments: &[DefinitionTerm],
    context: &EmitContext<'_>,
    existentials: &[DefinitionClaimBinder],
    output: &mut Rendered,
) -> Result<(), EmitError> {
    let render = |argument: &DefinitionTerm| {
        render_term_with_binders(argument, context, false, existentials)
    };
    match operation {
        ListOperation::Empty if arguments.is_empty() => output.push(".List"),
        ListOperation::Item if arguments.len() == 1 => {
            output.push("ListItem(");
            output.append(render(&arguments[0])?);
            output.push(")");
        }
        ListOperation::Concat if arguments.len() == 2 => {
            output.append(render(&arguments[0])?);
            output.push(" ");
            output.append(render(&arguments[1])?);
        }
        ListOperation::Get if arguments.len() == 2 => {
            output.push("{");
            output.append(render(&arguments[0])?);
            output.push(" [ ");
            output.append(render(&arguments[1])?);
            output.push(" ]}:>");
            output.push(context.sort_name_ref(result_sort)?);
        }
        ListOperation::Update if arguments.len() == 3 => {
            output.append(render(&arguments[0])?);
            output.push(" [ ");
            output.append(render(&arguments[1])?);
            output.push(" <- ");
            output.append(render(&arguments[2])?);
            output.push(" ]");
        }
        ListOperation::Size if arguments.len() == 1 => {
            output.push("size(");
            output.append(render(&arguments[0])?);
            output.push(")");
        }
        ListOperation::Make if arguments.len() == 2 => {
            output.push("makeList(");
            output.append(render(&arguments[0])?);
            output.push(", ");
            output.append(render(&arguments[1])?);
            output.push(")");
        }
        ListOperation::Range if arguments.len() == 3 => {
            output.push("range(");
            output.append(render(&arguments[0])?);
            output.push(", ");
            output.append(render(&arguments[1])?);
            output.push(", ");
            output.append(render(&arguments[2])?);
            output.push(")");
        }
        ListOperation::UpdateAll if arguments.len() == 3 => {
            output.push("updateList(");
            output.append(render(&arguments[0])?);
            output.push(", ");
            output.append(render(&arguments[1])?);
            output.push(", ");
            output.append(render(&arguments[2])?);
            output.push(")");
        }
        _ => {
            return Err(EmitError::InvalidReference(format!(
                "List operation {operation:?} has invalid arity {}",
                arguments.len()
            )));
        }
    }
    Ok(())
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

fn sentence_key(sentence: &DefinitionSentence) -> (u8, String) {
    let text = match sentence {
        DefinitionSentence::SyntaxSort(sentence) => sentence.symbol().emitted_name().to_owned(),
        DefinitionSentence::Subsort(sentence) => {
            format!("{:?}:{:?}", sentence.supersort(), sentence.subsort())
        }
        DefinitionSentence::Production(sentence) => sentence.symbol().emitted_name().to_owned(),
        DefinitionSentence::Precedence(sentence) => format!("{sentence:?}"),
        DefinitionSentence::Associativity(sentence) => format!("{sentence:?}"),
        DefinitionSentence::Configuration(sentence) => format!("{:?}", sentence.origin().key()),
        DefinitionSentence::ContextAlias(sentence) => sentence.name().to_owned(),
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

fn anonymous_name(variable: &SemanticId) -> Option<&str> {
    let (name, ordinal) = variable.as_str().rsplit_once("__krs_")?;
    (name.starts_with('_')
        && name.len() > 1
        && !ordinal.is_empty()
        && ordinal.bytes().all(|byte| byte.is_ascii_digit()))
    .then_some(name)
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

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use krs_ir::{
        BuiltinOperation, DefinitionApplicationRef, DefinitionSortRef, DefinitionTerm,
        ListOperation, MapOperation, NodeOrigin, SetOperation,
    };

    use super::{EmitContext, render_term};

    fn node(key: &str) -> NodeOrigin {
        krs_ir::testing::origin_in(
            key,
            krs_ir::testing::package("KRS-EMIT-TEST", "emit-test"),
            "src/lib.rs",
            krs_ir::testing::digest(),
            0,
            1,
        )
    }

    fn context() -> EmitContext<'static> {
        EmitContext {
            sorts: BTreeMap::new(),
            productions: BTreeMap::new(),
            groups: BTreeMap::new(),
            non_associative_groups: BTreeSet::new(),
            cells: BTreeMap::new(),
            repeated_ancestors: BTreeMap::new(),
            context_aliases: BTreeMap::new(),
        }
    }

    fn empty(key: &str) -> DefinitionTerm {
        DefinitionTerm::list(
            node(key),
            DefinitionSortRef::list(),
            ListOperation::Empty,
            vec![],
        )
    }

    fn int(key: &str, value: &str) -> DefinitionTerm {
        DefinitionTerm::token(node(key), DefinitionSortRef::int(), value).unwrap()
    }

    #[test]
    fn builtin_list_operations_have_exact_canonical_k_source() {
        let terms = [
            (empty("list.empty"), ".List"),
            (
                DefinitionTerm::list(
                    node("list.item"),
                    DefinitionSortRef::list(),
                    ListOperation::Item,
                    vec![int("list.item.value", "1")],
                ),
                "ListItem(1)",
            ),
            (
                DefinitionTerm::list(
                    node("list.concat"),
                    DefinitionSortRef::list(),
                    ListOperation::Concat,
                    vec![
                        empty("list.concat.left"),
                        DefinitionTerm::list(
                            node("list.concat.right"),
                            DefinitionSortRef::list(),
                            ListOperation::Item,
                            vec![int("list.concat.value", "1")],
                        ),
                    ],
                ),
                ".List ListItem(1)",
            ),
            (
                DefinitionTerm::list(
                    node("list.get"),
                    DefinitionSortRef::int(),
                    ListOperation::Get,
                    vec![empty("list.get.base"), int("list.get.index", "0")],
                ),
                "{.List [ 0 ]}:>Int",
            ),
            (
                DefinitionTerm::list(
                    node("list.update"),
                    DefinitionSortRef::list(),
                    ListOperation::Update,
                    vec![
                        empty("list.update.base"),
                        int("list.update.index", "0"),
                        int("list.update.value", "1"),
                    ],
                ),
                ".List [ 0 <- 1 ]",
            ),
            (
                DefinitionTerm::list(
                    node("list.size"),
                    DefinitionSortRef::int(),
                    ListOperation::Size,
                    vec![empty("list.size.base")],
                ),
                "size(.List)",
            ),
            (
                DefinitionTerm::list(
                    node("list.range"),
                    DefinitionSortRef::list(),
                    ListOperation::Range,
                    vec![
                        empty("list.range.base"),
                        int("list.range.front", "1"),
                        int("list.range.back", "2"),
                    ],
                ),
                "range(.List, 1, 2)",
            ),
            (
                DefinitionTerm::list(
                    node("list.update-all"),
                    DefinitionSortRef::list(),
                    ListOperation::UpdateAll,
                    vec![
                        empty("list.update-all.base"),
                        int("list.update-all.index", "1"),
                        empty("list.update-all.replacement"),
                    ],
                ),
                "updateList(.List, 1, .List)",
            ),
        ];
        let context = context();
        for (term, expected) in terms {
            assert_eq!(render_term(&term, &context, false).unwrap().text, expected);
        }
    }

    #[test]
    fn builtin_bytes_operations_have_exact_canonical_k_source() {
        let empty = || {
            DefinitionTerm::application(
                node("bytes.empty"),
                DefinitionSortRef::bytes(),
                DefinitionApplicationRef::Builtin(BuiltinOperation::BytesEmpty),
                vec![],
            )
        };
        let terms = [
            (empty(), ".Bytes"),
            (
                DefinitionTerm::application(
                    node("bytes.update"),
                    DefinitionSortRef::bytes(),
                    DefinitionApplicationRef::Builtin(BuiltinOperation::BytesUpdate),
                    vec![
                        empty(),
                        int("bytes.update.index", "0"),
                        int("bytes.update.value", "255"),
                    ],
                ),
                "(.Bytes) [ 0 <- 255 ]",
            ),
            (
                DefinitionTerm::application(
                    node("bytes.pad-right"),
                    DefinitionSortRef::bytes(),
                    DefinitionApplicationRef::Builtin(BuiltinOperation::BytesPadRight),
                    vec![
                        empty(),
                        int("bytes.pad-right.length", "32"),
                        int("bytes.pad-right.value", "0"),
                    ],
                ),
                "padRightBytes(.Bytes, 32, 0)",
            ),
            (
                DefinitionTerm::application(
                    node("bytes.substring"),
                    DefinitionSortRef::bytes(),
                    DefinitionApplicationRef::Builtin(BuiltinOperation::BytesSubstring),
                    vec![
                        empty(),
                        int("bytes.substring.start", "1"),
                        int("bytes.substring.end", "3"),
                    ],
                ),
                "substrBytes(.Bytes, 1, 3)",
            ),
        ];
        let context = context();
        for (term, expected) in terms {
            assert_eq!(render_term(&term, &context, false).unwrap().text, expected);
        }
    }

    #[test]
    fn builtin_map_lookup_and_set_operations_have_exact_canonical_k_source() {
        let map = || DefinitionTerm::map(node("map.empty"), MapOperation::Empty, vec![]);
        let set = || {
            DefinitionTerm::set(
                node("set.empty"),
                DefinitionSortRef::set(),
                SetOperation::Empty,
                vec![],
            )
        };
        let terms = [
            (
                DefinitionTerm::typed_map(
                    node("map.get"),
                    DefinitionSortRef::int(),
                    MapOperation::Get,
                    vec![map(), int("map.get.key", "1")],
                ),
                "{.Map [ 1 ]}:>Int",
            ),
            (
                DefinitionTerm::typed_map(
                    node("map.in-keys"),
                    DefinitionSortRef::bool(),
                    MapOperation::InKeys,
                    vec![int("map.in-keys.key", "1"), map()],
                ),
                "1 in_keys(.Map)",
            ),
            (set(), ".Set"),
            (
                DefinitionTerm::set(
                    node("set.item"),
                    DefinitionSortRef::set(),
                    SetOperation::Item,
                    vec![int("set.item.value", "1")],
                ),
                "SetItem(1)",
            ),
            (
                DefinitionTerm::set(
                    node("set.concat"),
                    DefinitionSortRef::set(),
                    SetOperation::Concat,
                    vec![set(), set()],
                ),
                ".Set .Set",
            ),
            (
                DefinitionTerm::set(
                    node("set.union"),
                    DefinitionSortRef::set(),
                    SetOperation::Union,
                    vec![set(), set()],
                ),
                ".Set |Set .Set",
            ),
            (
                DefinitionTerm::set(
                    node("set.contains"),
                    DefinitionSortRef::bool(),
                    SetOperation::Contains,
                    vec![int("set.contains.value", "1"), set()],
                ),
                "1 in .Set",
            ),
        ];
        let context = context();
        for (term, expected) in terms {
            assert_eq!(render_term(&term, &context, false).unwrap().text, expected);
        }
    }
}
