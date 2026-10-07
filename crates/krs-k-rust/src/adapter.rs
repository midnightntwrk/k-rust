mod sentence;
mod term;

use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fmt,
};

use k_rust::{
    definition::{
        self as native_definition, Attributes as NativeAttributes, FlatImport, FlatModule,
    },
    kast::Sort as NativeSort,
};
use krs_diagnostic::{Diagnostic, Location, ToDiagnostic, codes};
use krs_ir::{NodeOrigin, OriginFrame, ProductionGroupId, SemanticId, SourceMapKey, StableItemId};
use krs_ir_levels::{
    DefinitionIr, DefinitionSentence, DefinitionSortRef, SymbolId,
    k_surface::{
        DefinitionIndex, ImportPolicy, SentenceVariables, VariableNaming, builtin_imports,
    },
};
use serde_json::json;

use crate::{Backend, NativeDefinition};

/// Place occupied by one adapted native node.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum NativeNodePlace {
    /// The flat native module itself.
    Module,
    /// A node within a module-local native sentence.
    Sentence {
        /// Module-local native sentence index.
        index: usize,
        /// Structural role within the sentence.
        role: SentenceNodeRole,
    },
}

/// Stable role occupied by a node within an adapted native sentence.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum SentenceNodeRole {
    /// The native sentence itself.
    Sentence,
    /// Cell identity represented inside a configuration sentence.
    ConfigurationCell,
    /// Initializer identity represented inside a configuration sentence.
    ConfigurationInitializer,
    /// Authored name of a context-alias sentence.
    ContextAliasName,
    /// Authored binding selected as `HERE` in a context alias.
    ContextAliasHere,
    /// One cell pattern in a context alias.
    ContextAliasCell(u32),
    /// One explicit associative frame in a context alias.
    ContextAliasFrame(u32),
    /// Named context-alias selection on strictness metadata.
    StrictnessContextAlias,
    /// One selected strictness field.
    StrictnessField(u32),
    /// Result-predicate sort on strictness metadata.
    StrictnessResult,
    /// One grammar production item.
    ProductionItem(u32),
    /// One classified production attribute.
    ProductionAttribute(u32),
    /// One cell clause in a fixed-configuration rule.
    ConfigurationRuleCell(u32),
    /// One explicit frame in a fixed-configuration rule.
    ConfigurationRuleFrame(u32),
    /// One claim binder declaration.
    ClaimBinder(u32),
    /// One claim binder name.
    ClaimBinderName(u32),
    /// One claim binder sort.
    ClaimBinderSort(u32),
    /// A claim modality marker.
    ClaimModality,
    /// A claim circularity marker.
    ClaimCircularity,
    /// A rule applicability condition.
    Requires,
    /// A claim postcondition.
    Ensures,
    /// Structured term. Child indices form a deterministic preorder path from
    /// the sentence body (`0`/`1` for rewrite endpoints and application or
    /// sequence argument indices otherwise).
    Term(Vec<u32>),
}

/// Sidecar seam from an IR origin to its structural native destination.
///
/// Roles within a sentence serve diagnostics and editor mapping.
/// Emitted rule and claim identities join through [`SentenceNodeRole::Sentence`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OriginMapping {
    /// Stable key shared with KRS source-map sidecars.
    pub key: SourceMapKey,
    /// Complete authored-to-Definition-IR provenance.
    pub origin: NodeOrigin,
    /// Emitted module name containing the native destination.
    pub module: String,
    /// Structural destination within the native module.
    pub place: NativeNodePlace,
}

/// A native source definition structurally adapted from Definition IR.
///
/// This value is intentionally not a [`LoadedDefinition`](crate::LoadedDefinition). Its origin sidecar
/// retains exact byte ranges and transformation stacks. Native source
/// attributes retain a portable package-relative source name; a native
/// line/column location is omitted because Definition IR has byte ranges but
/// not source contents from which line/column coordinates could be derived
/// honestly.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AdaptedDefinition {
    pub(super) definition: NativeDefinition,
    pub(super) origins: Vec<OriginMapping>,
    pub(super) omitted_claims: usize,
}

impl AdaptedDefinition {
    /// Returns the pinned frontend's flat source Definition model.
    #[must_use]
    pub const fn definition(&self) -> &NativeDefinition {
        &self.definition
    }

    /// Returns the stable origin mapping in IR traversal order.
    #[must_use]
    pub fn origins(&self) -> &[OriginMapping] {
        &self.origins
    }

    /// Returns the number of claims left out for a backend that does not prove.
    #[must_use]
    pub const fn omitted_claims(&self) -> usize {
        self.omitted_claims
    }
}

/// Structural Definition-IR adaptation failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AdapterError {
    /// A validated symbol reference could not be found while indexing the IR.
    MissingSymbol {
        /// Origin of the referencing node.
        key: SourceMapKey,
        /// Missing stable symbol identity.
        symbol: SymbolId,
    },
    /// A validated nominal reference was absent from the adapter index.
    MissingReference {
        /// Origin of the referencing node.
        key: SourceMapKey,
        /// Reference family.
        kind: &'static str,
        /// Stable target identity.
        target: String,
    },
}

impl ToDiagnostic for AdapterError {
    fn to_diagnostic(&self) -> Diagnostic {
        let (code, key) = match self {
            Self::MissingSymbol { key, .. } => (codes::native::ADAPTER_MISSING_SYMBOL, key),
            Self::MissingReference { key, .. } => (codes::native::ADAPTER_MISSING_REFERENCE, key),
        };
        Diagnostic::error(code, self.to_string(), Location::Definition(key.clone()))
    }
}

impl fmt::Display for AdapterError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingSymbol { key, symbol } => write!(
                formatter,
                "Definition IR symbol {symbol} referenced at {key} is absent from the adapter index"
            ),
            Self::MissingReference { key, kind, target } => write!(
                formatter,
                "Definition IR {kind} reference {target:?} at {key} is absent from the adapter index"
            ),
        }
    }
}

impl Error for AdapterError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::MissingSymbol { .. } | Self::MissingReference { .. } => None,
        }
    }
}

/// Structurally maps schema-9 Definition IR to the pinned native source
/// Definition model.
///
/// Imports remain public, matching ordinary K `imports MODULE`. Sorts,
/// subsorts, production items, constructor labels, rule labels, and terms use
/// the emitted names stored in Definition IR. `KSequence` maps directly to
/// [`NativeTerm::Sequence`](k_rust::kast::Term::Sequence); no injection, `.K`, production ID, or KORE node
/// is manufactured here.
///
/// # Errors
///
/// Returns [`AdapterError`] for unsupported sentence/term positions or an
/// inconsistent symbol index.
pub fn adapt_definition(ir: &DefinitionIr) -> Result<AdaptedDefinition, AdapterError> {
    Adapter::new(ir, true).adapt(ir)
}

/// Adapt Definition IR as compiled for `backend`, omitting every claim when
/// [`Backend::proves_claims`] is false. Sentence indices and origin mappings
/// describe the adapted modules, so they stay consistent with the omission.
///
/// # Errors
///
/// Returns [`AdapterError`] under the same conditions as [`adapt_definition`].
pub fn adapt_definition_for(
    ir: &DefinitionIr,
    backend: Backend,
) -> Result<AdaptedDefinition, AdapterError> {
    Adapter::new(ir, backend.proves_claims()).adapt(ir)
}

struct Adapter<'a> {
    index: DefinitionIndex<'a>,
    initializer_variables: BTreeMap<SemanticId, String>,
    context_here: Option<SemanticId>,
    naming: VariableNaming,
    /// K spellings of the variables of the sentence being adapted.
    variable_names: SentenceVariables,
    origins: Vec<OriginMapping>,
    keep_claims: bool,
    omitted_claims: usize,
}

impl<'a> Adapter<'a> {
    fn new(ir: &'a DefinitionIr, keep_claims: bool) -> Self {
        Self {
            index: DefinitionIndex::new(ir),
            initializer_variables: BTreeMap::new(),
            context_here: None,
            naming: VariableNaming::new(ir),
            variable_names: SentenceVariables::default(),
            origins: Vec::new(),
            keep_claims,
            omitted_claims: 0,
        }
    }

    fn adapt(mut self, ir: &DefinitionIr) -> Result<AdaptedDefinition, AdapterError> {
        let modules = ir
            .modules()
            .iter()
            .map(|module| self.module(module))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(AdaptedDefinition {
            definition: NativeDefinition {
                main_module: ir.main_module().as_str().to_owned(),
                modules,
                attributes: NativeAttributes::default(),
            },
            origins: self.origins,
            omitted_claims: self.omitted_claims,
        })
    }

    fn module(
        &mut self,
        module: &krs_ir_levels::DefinitionModule,
    ) -> Result<FlatModule, AdapterError> {
        let module_name = module.id().as_str().to_owned();
        self.map_origin(module.origin(), &module_name, NativeNodePlace::Module);
        let mut local_sentences = Vec::with_capacity(module.sentences().len());
        for sentence in module.sentences() {
            if !self.keep_claims
                && matches!(sentence, DefinitionSentence::Rule(rule) if rule.claim().is_some())
            {
                self.omitted_claims += 1;
                continue;
            }
            let sentence_index = local_sentences.len();
            let native = self.sentence(sentence, &module_name, sentence_index)?;
            local_sentences.push(std::sync::Arc::new(native));
        }
        let mut imports = builtin_imports(module, ImportPolicy::NativeFrontend.for_module(module))
            .into_iter()
            .map(str::to_owned)
            .collect::<BTreeSet<_>>();
        imports.extend(
            module
                .imports()
                .iter()
                .map(|import| import.as_str().to_owned()),
        );
        Ok(FlatModule {
            name: module_name,
            imports: imports
                .into_iter()
                .map(|name| FlatImport { name, public: true })
                .collect(),
            local_sentences,
            attributes: attributes_for_origin(module.origin()),
        })
    }

    fn sort(
        &self,
        sort: &DefinitionSortRef,
        origin: &NodeOrigin,
    ) -> Result<NativeSort, AdapterError> {
        Ok(NativeSort::new(match sort {
            DefinitionSortRef::Declared(symbol) => self.symbol_name(symbol, origin)?,
            DefinitionSortRef::Builtin(sort) => sort.k_name(),
        }))
    }

    fn group_name(
        &self,
        group: &ProductionGroupId,
        origin: &NodeOrigin,
    ) -> Result<String, AdapterError> {
        self.index
            .group_name(group)
            .map(str::to_owned)
            .ok_or_else(|| AdapterError::MissingReference {
                key: origin.key().clone(),
                kind: "production group",
                target: group.as_str().to_owned(),
            })
    }

    fn context_alias_name(
        &self,
        alias: &StableItemId,
        origin: &NodeOrigin,
    ) -> Result<String, AdapterError> {
        self.index
            .context_alias_name(alias)
            .map(str::to_owned)
            .ok_or_else(|| AdapterError::MissingReference {
                key: origin.key().clone(),
                kind: "context alias",
                target: alias.to_string(),
            })
    }

    fn cell_name(&self, cell: &SymbolId, origin: &NodeOrigin) -> Result<&str, AdapterError> {
        self.index
            .cell_name(cell)
            .ok_or_else(|| AdapterError::MissingReference {
                key: origin.key().clone(),
                kind: "configuration cell",
                target: cell.as_str().to_owned(),
            })
    }

    fn symbol_name(&self, symbol: &SymbolId, origin: &NodeOrigin) -> Result<&str, AdapterError> {
        self.index
            .symbol_name(symbol)
            .ok_or_else(|| AdapterError::MissingSymbol {
                key: origin.key().clone(),
                symbol: symbol.clone(),
            })
    }

    fn map_origin(&mut self, origin: &NodeOrigin, module: &str, place: NativeNodePlace) {
        self.origins.push(OriginMapping {
            key: origin.key().clone(),
            origin: origin.clone(),
            module: module.to_owned(),
            place,
        });
    }

    fn map_sentence_origin(
        &mut self,
        origin: &NodeOrigin,
        module: &str,
        index: usize,
        role: SentenceNodeRole,
    ) {
        self.map_origin(origin, module, NativeNodePlace::Sentence { index, role });
    }
}

fn attributes_for_origin(origin: &NodeOrigin) -> NativeAttributes {
    let mut attributes = NativeAttributes::default();
    if let Some(source) = origin
        .origin()
        .frames()
        .iter()
        .find_map(|frame| match frame {
            OriginFrame::Ranged { range, .. } => Some(range.file.package_relative_path()),
            OriginFrame::Transformation { .. } => None,
        })
    {
        attributes.insert(native_definition::SOURCE_ATTRIBUTE, json!(source));
    }
    attributes
}

#[cfg(test)]
mod tests;
