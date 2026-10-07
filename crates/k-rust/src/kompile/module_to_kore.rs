//! ```toml algorithm
//! id = "kompile.kore.declarations"
//! name = "KORE declaration emission"
//! sites = ["declaration_modules", "declaration_modules_from_resolved", "declaration_modules_from_resolved_with_options", "DeclarationModules::semantics_definition", "module_to_kore_from_resolved_with_options"]
//! variable = "P = productions; A = declaration attributes; V = visible sentences; R = rules; S_c = collection-hooked sorts"
//! counters = ["KompileResolveCalls"]
//! consumes = [
//!   { type = "k_rust::definition::ResolvedDefinition", role = "resolved definition" },
//!   { type = "k_rust::definition::ProductionCatalog<'a>", role = "production lookup" },
//!   { type = "k_rust::definition::SortCatalog<'a>", role = "sort lookup" },
//!   { type = "k_rust::definition::PartialOrder<k_rust::kast::Sort>", role = "subsort order" },
//!   { type = "k_rust_kore::kore::ast::Sentence", role = "rule sentence" },
//! ]
//! produces = [
//!   { type = "k_rust_kore::kore::ast::Definition", role = "compiled definition" },
//! ]
//!
//! [[cost]]
//! mode = "one module"
//! bound = "O(P x A + V x A + R + S_c x P) plus one kompile.labels.backward_closure build and closure"
//! ```
//!
//! KORE emission builds declarations and generated axioms, then emits rules and equations with an owise competitor predicate.
//! Complexity: the declaration, axiom, rule, and owise cards state the bounds of their parts.
//! Catalog products and per-rule scans dominate; `KompileOwiseCompetitorScans` measures the competitor loop, and label dependency closure has a shared home.
//!
//! KORE emission of one compiled K module.

mod axioms;
mod equations;
mod roles;

#[cfg(any(debug_assertions, feature = "kompile-invariant-checks"))]
use super::invariants::emitted::{EmittedTheory, emitted_from};

use axioms::generated_axioms;
use equations::{
    OwiseCompetitors, RuleEmissionContext, check_variable_sorts, emit_rule_or_claim,
    resolve_equation_production,
};
use roles::{Declaration, SymbolClaims, SymbolRoles};

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use serde_json::Value;

use crate::definition::{
    AssociativityRelations, AttributeKey, Attributes as KAttributes, Definition as KDefinition,
    LabelHead, ModuleId, OverloadOrder, PartialOrder, ProductionCatalog, ProductionId,
    ProductionItem, RelationError, ResolveError, ResolvedDefinition, RuleCatalog, Sentence,
    SortCatalog, SortHead,
    production_kind::{
        BracketName, DeclaredTotality, ProductionKind, UnitInstance, UnitInstanceError,
        is_builtin_label, mentions_parameter,
    },
};
use crate::kast::{
    FrontendSort, InternalLabel, Label, ProductionIdentity, Sort, SortRole, Term, WellKnownModule,
    identifier,
};
use crate::kore::ast::{
    Attributes, Definition as KoreDefinition, Module, Pattern, Sentence as KoreSentence,
    Sort as KoreSort, Symbol, Variable, VariableKind,
};
use crate::names::{BuiltinSort, KoreAttribute, WellKnownSymbol};
use crate::provenance::{
    GeneratingPass, ProvenanceLink, seed_generated_sentence_origin, sentence_origin_links,
};

use super::compile::CompilationBackend;
use super::fresh_names::FreshNames;
use super::label_graph::LabelDependencyGraph;
use super::passes::number_sentence;
use super::sort_injections::{SortInjectionError, SortInjector};
use super::term_to_kore::{TermConversionError, TermConverter};

const COLLECTION_HOOKS: [&str; 4] = ["SET.Set", "MAP.Map", "LIST.List", "RANGEMAP.RangeMap"];
// K's builtin hook namespaces: a hook outside them is emitted as a hooked symbol only when the
// compilation admits its namespace through `ModuleToKoreOptions::hook_namespaces`.
pub(crate) const BUILTIN_HOOK_NAMESPACES: [&str; 19] = [
    "BOOL",
    "BUFFER",
    "BYTES",
    "FFI",
    "FLOAT",
    "INT",
    "IO",
    "KEQUAL",
    "KREFLECTION",
    "LIST",
    "MAP",
    "RANGEMAP",
    "MINT",
    "SET",
    "STRING",
    "SUBSTITUTION",
    "UNIFICATION",
    "JSON",
    "TIMER",
];

/// The declaration views and standalone macro axioms produced by KORE emission.
///
/// `semantics` carries backend-facing symbol attributes. `syntax` carries the
/// same declarations plus concrete-syntax formatting metadata. `macros` is the
/// bare sentence list written to `macros.kore`; it deliberately has no
/// enclosing KORE module.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeclarationModules {
    pub semantics: Module,
    pub syntax: Module,
    pub macros: Vec<KoreSentence>,
    pub definition_attributes: Attributes,
}

/// Backend-specific KORE generation switches.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ModuleToKoreOptions {
    /// Consumer of the emitted declarations, including its reading of irreducible value heads.
    pub backend: CompilationBackend,
    /// Generate the definedness axioms of hooked map constructions, which the symbolic Rust
    /// backend relies on.
    pub generate_map_ceil_axioms: bool,
    /// Treat otherwise-unqualified claims as all-path reachability claims.
    pub default_claims_to_all_path: bool,
    /// Plugin hook namespaces admitted as hooked symbols in addition to K's builtin set, the
    /// counterpart of `kompile --hook-namespaces`.
    pub hook_namespaces: Vec<String>,
    /// The kompiled definition module of a proof compilation. The claims of every module the
    /// specification imports are emitted unless the definition module's import closure already
    /// contains that module; without a definition module (or
    /// when it is the emitted module itself) only the module's local claims are emitted.
    pub definition_module: Option<String>,
}

impl Default for ModuleToKoreOptions {
    /// Defaults target the in-process Rust backend, so its plugin namespaces are admitted.
    fn default() -> Self {
        Self {
            backend: CompilationBackend::Rust,
            generate_map_ceil_axioms: false,
            default_claims_to_all_path: false,
            hook_namespaces: rust_backend_hook_namespaces(),
            definition_module: None,
        }
    }
}

/// The plugin hook namespaces the in-process Rust backend dispatches natively.
pub fn rust_backend_hook_namespaces() -> Vec<String> {
    k_rust_backend::builtin::PLUGIN_HOOK_NAMESPACES
        .iter()
        .map(|namespace| (*namespace).to_owned())
        .collect()
}

impl DeclarationModules {
    /// Wrap the backend-facing module in K's standard KORE prelude.
    pub fn semantics_definition(&self) -> KoreDefinition {
        self.definition_with(self.semantics.clone())
    }

    /// Print [`Self::semantics_definition`] without cloning the semantics module into it.
    pub fn print_semantics_definition(&self, printer: crate::kore::printer::Printer) -> String {
        self.print_definition_with(printer, &self.semantics)
    }

    /// Print the concrete-syntax module wrapped in K's standard KORE prelude.
    pub fn print_syntax_definition(&self, printer: crate::kore::printer::Printer) -> String {
        self.print_definition_with(printer, &self.syntax)
    }

    fn print_definition_with(
        &self,
        printer: crate::kore::printer::Printer,
        module: &Module,
    ) -> String {
        let prelude = standard_kore_prelude();
        printer.print_definition_parts(
            &self.definition_attributes,
            prelude.modules.iter().chain(std::iter::once(module)),
        )
    }

    fn definition_with(&self, module: Module) -> KoreDefinition {
        let mut definition = standard_kore_prelude();
        definition.attributes = self.definition_attributes.clone();
        definition.modules.push(module);
        definition
    }
}

/// Parse the canonical textual KORE prelude embedded by `kompile`.
pub fn standard_kore_prelude() -> KoreDefinition {
    crate::kore::parser::parse_definition(include_str!("prelude.kore"))
        .expect("the embedded KORE prelude must parse")
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ReachabilityMode {
    OnePath,
    AllPath,
}

#[derive(Clone, Debug, Default)]
struct SyntaxRelations {
    priorities: BTreeMap<String, Vec<Pattern>>,
    left: BTreeMap<String, Vec<Pattern>>,
    right: BTreeMap<String, Vec<Pattern>>,
}

impl SyntaxRelations {
    fn new(priorities: &PartialOrder<String>, associativities: &AssociativityRelations) -> Self {
        let priorities = priorities
            .elements()
            .map(|label| {
                let targets = priorities
                    .relations_from(label)
                    .into_iter()
                    .flatten()
                    .filter(|target| !is_builtin_label(target))
                    .map(|target| bare_label_pattern(target))
                    .collect();
                (label.clone(), targets)
            })
            .collect();
        Self {
            priorities,
            left: grouped_associativity(&associativities.left),
            right: grouped_associativity(&associativities.right),
        }
    }
}

/// The name a syntax-module declaration is made under, which decides whether it carries the syntax relations.
#[derive(Clone, Copy)]
enum SyntaxDeclaration<'a> {
    /// Under the production's own label: priority and associativity groups name that label, so the declaration carries the `priorities`, `left`, and `right` it is related by.
    UnderLabel(&'a SyntaxRelations),
    /// Under the `bracketLabel` of an unlabelled bracket: the declaration carries no `priorities`, `left`, or `right`.
    UnderBracketLabel,
}

fn grouped_associativity(relations: &BTreeSet<(String, String)>) -> BTreeMap<String, Vec<Pattern>> {
    let mut grouped = BTreeMap::<String, Vec<Pattern>>::new();
    for (parent, child) in relations {
        grouped
            .entry(parent.clone())
            .or_default()
            .push(bare_label_pattern(child));
    }
    grouped
}

fn bare_label_pattern(label: &str) -> Pattern {
    Pattern::Application {
        symbol: encode_kore_label(&Label::new(label)),
        arguments: Vec::new(),
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DeclarationError {
    Definition(ResolveError),
    MissingModule(String),
    Relations(RelationError),
    CircularPriority(Vec<String>),
    InvalidCollectionSort {
        sort: String,
        message: String,
    },
    InvalidCollectionLabel {
        label: String,
        productions: usize,
    },
    SchematicAttributeLabel {
        label: String,
        parameters: Vec<Sort>,
    },
    /// Two sort heads that differ only in arity would be declared under one KORE sort name.
    DuplicateSortName {
        name: String,
        first: String,
        second: String,
    },
}

/// A failure while extending KORE declarations with semantic rules or claims.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ModuleToKoreError {
    Declaration(DeclarationError),
    SortInjection(SortInjectionError),
    TermConversion(TermConversionError),
    ExpectedRewrite {
        sentence: &'static str,
    },
    ExpectedGeneratedTopCell {
        actual: Sort,
        rule: String,
    },
    MissingEquationProduction {
        label: String,
    },
    AmbiguousEquationProduction {
        label: String,
        productions: usize,
    },
    InvalidEquationProduction {
        production: String,
        message: String,
    },
    InvalidAlgebraicProduction {
        production: usize,
        attribute: &'static str,
        message: String,
    },
    InvalidOverloadProduction {
        production: usize,
        message: String,
    },
    EquationExistentials {
        variables: Vec<String>,
    },
    InconsistentVariableSorts {
        sentence: String,
        name: String,
        sorts: Vec<String>,
    },
    UnsupportedRuleKind {
        kind: String,
    },
    InvalidImportedProductionMetadata {
        module: String,
        production: String,
        message: String,
    },
    InvalidGeneratedMapAxiom {
        production: usize,
        message: String,
    },
}

impl fmt::Display for ModuleToKoreError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Declaration(error) => error.fmt(formatter),
            Self::SortInjection(error) => error.fmt(formatter),
            Self::TermConversion(error) => error.fmt(formatter),
            Self::ExpectedRewrite { sentence } => {
                write!(formatter, "cannot emit {sentence} without a rewrite body")
            }
            Self::ExpectedGeneratedTopCell { actual, rule } => write!(
                formatter,
                "ordinary semantic rules must rewrite GeneratedTopCell, found {actual} in rule {rule}"
            ),
            Self::MissingEquationProduction { label } => {
                write!(
                    formatter,
                    "cannot find the production for equation label {label:?}"
                )
            }
            Self::AmbiguousEquationProduction { label, productions } => write!(
                formatter,
                "cannot select one of {productions} productions for equation label {label:?}"
            ),
            Self::InvalidEquationProduction {
                production,
                message,
            } => write!(
                formatter,
                "cannot use production #{production} for equation emission: {message}"
            ),
            Self::InvalidAlgebraicProduction {
                production,
                attribute,
                message,
            } => write!(
                formatter,
                "cannot emit {attribute} axiom for production #{production}: {message}"
            ),
            Self::InvalidOverloadProduction {
                production,
                message,
            } => write!(
                formatter,
                "cannot use production #{production} for overload axiom emission: {message}"
            ),
            Self::EquationExistentials { variables } => write!(
                formatter,
                "cannot encode equations with existential variables: {}",
                variables.join(", ")
            ),
            Self::InconsistentVariableSorts {
                sentence,
                name,
                sorts,
            } => write!(
                formatter,
                "variable {name} occurs with sorts {} in one axiom ({sentence}); this can result from an authored sortless variable used at positions of different sorts or from a kompile pass reusing a variable name",
                sorts.join(" and ")
            ),
            Self::UnsupportedRuleKind { kind } => {
                write!(formatter, "KORE emission for {kind} is not implemented yet")
            }
            Self::InvalidImportedProductionMetadata {
                module,
                production,
                message,
            } => write!(
                formatter,
                "cannot rebase production #{production} from imported module {module:?}: {message}"
            ),
            Self::InvalidGeneratedMapAxiom {
                production,
                message,
            } => write!(
                formatter,
                "cannot generate MAP definedness axiom for production #{production}: {message}"
            ),
        }
    }
}

impl std::error::Error for ModuleToKoreError {}

impl From<DeclarationError> for ModuleToKoreError {
    fn from(error: DeclarationError) -> Self {
        Self::Declaration(error)
    }
}

impl From<SortInjectionError> for ModuleToKoreError {
    fn from(error: SortInjectionError) -> Self {
        Self::SortInjection(error)
    }
}

impl From<TermConversionError> for ModuleToKoreError {
    fn from(error: TermConversionError) -> Self {
        Self::TermConversion(error)
    }
}

impl fmt::Display for DeclarationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Definition(error) => error.fmt(formatter),
            Self::MissingModule(module) => {
                write!(formatter, "KORE source module {module:?} was not found")
            }
            Self::Relations(error) => error.fmt(formatter),
            Self::CircularPriority(path) => write!(
                formatter,
                "cannot emit declarations with circular priorities: {}",
                path.join(" > ")
            ),
            Self::InvalidCollectionSort { sort, message } => {
                write!(
                    formatter,
                    "cannot emit hooked collection sort {sort}: {message}"
                )
            }
            Self::InvalidCollectionLabel { label, productions } => write!(
                formatter,
                "Expected to find exactly one production for KLabel: {label} found: {productions}"
            ),
            Self::SchematicAttributeLabel { label, parameters } => write!(
                formatter,
                "attribute label {label} has sort parameters {parameters:?}; an attribute must name one symbol instance"
            ),
            Self::DuplicateSortName {
                name,
                first,
                second,
            } => write!(
                formatter,
                "cannot emit sort declarations: the sorts {first} and {second} are both named {name} in KORE"
            ),
        }
    }
}

impl std::error::Error for DeclarationError {}

/// Build the sort and symbol declaration views for one module.
pub fn declaration_modules(
    definition: &KDefinition,
    module: &str,
) -> Result<DeclarationModules, DeclarationError> {
    let resolved = ResolvedDefinition::resolve(definition).map_err(DeclarationError::Definition)?;
    declaration_modules_from_resolved(&resolved, module)
}

/// Build declarations while reusing an already-resolved definition.
pub fn declaration_modules_from_resolved(
    definition: &ResolvedDefinition,
    module: &str,
) -> Result<DeclarationModules, DeclarationError> {
    declaration_modules_from_resolved_with_options(
        definition,
        module,
        &rust_backend_hook_namespaces(),
    )
}

/// Build declarations, admitting `hook_namespaces` as hooked symbols beyond K's builtin set.
pub fn declaration_modules_from_resolved_with_options(
    definition: &ResolvedDefinition,
    module: &str,
    hook_namespaces: &[String],
) -> Result<DeclarationModules, DeclarationError> {
    let module_id = definition
        .module_id(module)
        .ok_or_else(|| DeclarationError::MissingModule(module.to_owned()))?;
    let productions = definition.production_catalog(module_id);
    let overloads = definition
        .overloads(module_id)
        .map_err(DeclarationError::Relations)?;
    let roles = SymbolRoles::classify(
        &productions,
        &definition.rule_catalog(module_id),
        &overloads,
    );
    declarations_with_roles(
        definition,
        module_id,
        module,
        &productions,
        &roles,
        hook_namespaces,
        CompilationBackend::Rust,
    )
}

/// The declarations of module `module` (`module_id`), whose productions are `productions`,
/// each declared with the claims `roles` classified for it.
fn declarations_with_roles(
    definition: &ResolvedDefinition,
    module_id: ModuleId,
    module: &str,
    productions: &ProductionCatalog<'_>,
    roles: &SymbolRoles,
    hook_namespaces: &[String],
    backend: CompilationBackend,
) -> Result<DeclarationModules, DeclarationError> {
    let visible = definition.sentences(module_id);
    let sorts = definition.sort_catalog(module_id);
    let valued_attributes = valued_attributes(&visible);
    let impure_labels = transitive_impure_labels(definition, module_id, productions);
    let priorities = definition
        .priorities(module_id)
        .map_err(|cycle| DeclarationError::CircularPriority(cycle.path))?;
    let associativities = definition.associativities(module_id);
    let syntax_relations = SyntaxRelations::new(&priorities, &associativities);

    let mut common = vec![KoreSentence::Import {
        module: WellKnownModule::K.as_str().into(),
        attributes: Attributes::default(),
    }];
    common.extend(sort_declarations(&sorts, productions, &valued_attributes)?);

    let mut semantic_sentences = common.clone();
    let mut syntax_sentences = common;
    for (id, production) in productions.productions() {
        let claims = roles.claims(id);
        debug_assert_eq!(
            claims.declaration() != Declaration::None,
            ProductionKind::of(production).declares_symbol(matches!(
                production,
                Sentence::Production { label: Some(_), .. }
            )),
            "the declaration claims and ProductionKind::declares_symbol partition productions alike"
        );
        let declared_semantically = match claims.declaration() {
            Declaration::SemanticAndSyntax => true,
            // A labelled bracket keeps its syntax-module declaration, which carries `bracket`,
            // `format`, and the priority and associativity tags its label names; it gets no
            // semantic-module declaration because no term contains it (`ProductionKind::Bracket`).
            Declaration::SyntaxOnly(BracketName::OwnLabel) => false,
            // An unlabelled bracket is declared under its `bracketLabel` below.
            Declaration::SyntaxOnly(BracketName::BracketLabel | BracketName::Undeclared)
            | Declaration::None => continue,
        };
        let Sentence::Production {
            label: Some(label),
            parameters,
            sort,
            items,
            attributes,
        } = production
        else {
            unreachable!("a production declared under its own label is labelled")
        };
        // A bracket's syntax declaration states the same production without `bracket`; every
        // other production has one kind.
        let kind = ProductionKind::of_unbracketed(production);
        let semantic_attributes = if declared_semantically {
            Some(symbol_attributes(
                attributes,
                label,
                sort,
                parameters,
                kind,
                claims,
                productions,
                &valued_attributes,
                &impure_labels,
                None,
                items,
                hook_namespaces,
                backend,
            )?)
        } else {
            None
        };
        let syntax_attributes = symbol_attributes(
            attributes,
            label,
            sort,
            parameters,
            kind,
            claims,
            productions,
            &valued_attributes,
            &impure_labels,
            Some(SyntaxDeclaration::UnderLabel(&syntax_relations)),
            items,
            hook_namespaces,
            backend,
        )?;
        let hooked = interpreted_hook(attributes, hook_namespaces).is_some();
        let declaration = |attributes| KoreSentence::SymbolDeclaration {
            hooked,
            symbol: encode_kore_label_with_formals(label, parameters),
            argument_sorts: items
                .iter()
                .filter_map(|item| match item {
                    ProductionItem::NonTerminal { sort, .. } => {
                        Some(encode_kore_sort_with_formals(sort, parameters))
                    }
                    ProductionItem::RegexTerminal { .. } | ProductionItem::Terminal(_) => None,
                })
                .collect(),
            result_sort: encode_kore_sort_with_formals(sort, parameters),
            attributes,
        };
        if let Some(semantic_attributes) = semantic_attributes {
            semantic_sentences.push(declaration(semantic_attributes));
        }
        syntax_sentences.push(declaration(syntax_attributes));
    }
    for (id, production) in productions.productions() {
        let claims = roles.claims(id);
        // An unlabelled bracket is declared in the syntax module under its `bracketLabel`.
        match claims.declaration() {
            Declaration::SyntaxOnly(BracketName::BracketLabel) => {}
            Declaration::SemanticAndSyntax
            | Declaration::SyntaxOnly(BracketName::OwnLabel | BracketName::Undeclared)
            | Declaration::None => continue,
        }
        let Sentence::Production {
            label: None,
            parameters,
            sort,
            items,
            attributes,
        } = production
        else {
            unreachable!("a bracket declared under its bracketLabel is an unlabelled production")
        };
        let Some(mut bracket_label) = attributes.label(AttributeKey::BracketLabel) else {
            unreachable!("a bracket declared under its bracketLabel carries a readable one")
        };
        if attributes.string(AttributeKey::BracketLabel).is_some() {
            bracket_label.parameters = parameters.clone();
        }
        let label = bracket_label;
        let hooked = interpreted_hook(attributes, hook_namespaces).is_some();
        let attributes = symbol_attributes(
            attributes,
            &label,
            sort,
            parameters,
            ProductionKind::of_unbracketed(production),
            claims,
            productions,
            &valued_attributes,
            &impure_labels,
            Some(SyntaxDeclaration::UnderBracketLabel),
            items,
            hook_namespaces,
            backend,
        )?;
        syntax_sentences.push(KoreSentence::SymbolDeclaration {
            hooked,
            symbol: encode_kore_label_with_formals(&label, parameters),
            argument_sorts: items
                .iter()
                .filter_map(|item| match item {
                    ProductionItem::NonTerminal { sort, .. } => {
                        Some(encode_kore_sort_with_formals(sort, parameters))
                    }
                    ProductionItem::RegexTerminal { .. } | ProductionItem::Terminal(_) => None,
                })
                .collect(),
            result_sort: encode_kore_sort_with_formals(sort, parameters),
            attributes,
        });
    }

    let module_name = identifier::encode(module);
    let module_attributes = emit_attributes(
        definition.module(module_id).attributes.semantic_entries(),
        &valued_attributes,
        &BTreeMap::new(),
    );
    let definition_attributes = definition_attributes(definition, module_id, productions);
    Ok(DeclarationModules {
        semantics: Module {
            name: module_name.clone(),
            sentences: semantic_sentences,
            attributes: module_attributes,
        },
        syntax: Module {
            name: module_name,
            sentences: syntax_sentences,
            attributes: Attributes::default(),
        },
        macros: Vec::new(),
        definition_attributes,
    })
}

fn definition_attributes(
    definition: &ResolvedDefinition,
    module_id: ModuleId,
    productions: &ProductionCatalog<'_>,
) -> Attributes {
    let mut attributes = Vec::new();
    if let Some(label) = productions
        .productions()
        .find_map(|(_, production)| match production {
            Sentence::Production {
                label: Some(label),
                sort,
                attributes,
                ..
            } if sort.name == BuiltinSort::GeneratedTopCell.k_name()
                && attributes.has(AttributeKey::Initializer) =>
            {
                Some(label)
            }
            Sentence::SyntaxSort { .. }
            | Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::Production { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::ContextAlias { .. }
            | Sentence::Context { .. }
            | Sentence::Rule { .. }
            | Sentence::Claim { .. }
            | Sentence::Configuration { .. }
            | Sentence::Bubble { .. } => None,
        })
    {
        attributes.push(Pattern::Application {
            symbol: Symbol {
                name: KoreAttribute::TopCellInitializer.as_str().into(),
                sort_parameters: Vec::new(),
            },
            arguments: vec![Pattern::Application {
                symbol: encode_kore_label(label),
                arguments: Vec::new(),
            }],
        });
    }
    if let Some(source) = definition.module(module_id).attributes.source() {
        attributes.push(Pattern::Application {
            symbol: Symbol {
                name: KoreAttribute::from(AttributeKey::Source).as_str().into(),
                sort_parameters: Vec::new(),
            },
            arguments: vec![Pattern::String(format!("Source({source})").into())],
        });
    }
    Attributes(attributes)
}

/// Emit declarations plus the ordinary semantic rules and local claims of one module.
///
/// Reachability claims are wrapped in the prelude aliases `weakExistsFinally` (one-path) and
/// `weakAlwaysFinally` (all-path). Macro and
/// alias rules are routed to the standalone `macros.kore` sentence list.
pub fn module_to_kore(
    definition: &KDefinition,
    module: &str,
) -> Result<DeclarationModules, ModuleToKoreError> {
    let resolved = ResolvedDefinition::resolve(definition).map_err(DeclarationError::Definition)?;
    module_to_kore_from_resolved(&resolved, module)
}

/// Emit semantic rules while reusing an already-resolved definition.
pub fn module_to_kore_from_resolved(
    definition: &ResolvedDefinition,
    module: &str,
) -> Result<DeclarationModules, ModuleToKoreError> {
    module_to_kore_from_resolved_with_options(definition, module, ModuleToKoreOptions::default())
}

/// Emit semantic rules with backend-specific generated axioms.
pub fn module_to_kore_from_resolved_with_options(
    definition: &ResolvedDefinition,
    module: &str,
    options: ModuleToKoreOptions,
) -> Result<DeclarationModules, ModuleToKoreError> {
    module_to_kore_from_resolved_with_options_and_sources(definition, module, options)
        .map(|(modules, _)| modules)
}

/// Return the source attributes of exactly the rules and claims emitted into the two KORE views.
pub(crate) fn module_to_kore_from_resolved_with_options_and_sources(
    definition: &ResolvedDefinition,
    module: &str,
    options: ModuleToKoreOptions,
) -> Result<(DeclarationModules, Vec<KAttributes>), ModuleToKoreError> {
    let module_id = definition
        .module_id(module)
        .ok_or_else(|| DeclarationError::MissingModule(module.to_owned()))?;
    let rules = definition.rule_catalog(module_id);
    let productions = definition.production_catalog(module_id);
    let overloads = definition
        .overloads(module_id)
        .map_err(DeclarationError::Relations)?;
    // One classification serves the declarations, the generated axioms and rule emission.
    let roles = SymbolRoles::classify(&productions, &rules, &overloads);
    let mut modules = declarations_with_roles(
        definition,
        module_id,
        module,
        &productions,
        &roles,
        &options.hook_namespaces,
        options.backend,
    )?;
    let visible = definition.sentences(module_id);
    let valued = valued_attributes(&visible);
    let sorts = definition.sort_catalog(module_id);
    let subsorts = definition
        .subsorts(module_id)
        .map_err(|error| DeclarationError::Relations(RelationError::CircularSubsort(error)))?;
    let injector = SortInjector::new(definition, module)?;
    let converter = TermConverter::new(definition, module)?;
    let default_reachability =
        reachability_mode(&definition.module(module_id).attributes).or(options
            .default_claims_to_all_path
            .then_some(ReachabilityMode::AllPath));
    let mut module_rules = Vec::with_capacity(rules.rules().len());
    for (_, rule) in rules.rules() {
        let owner = sentence_owner(definition, rule).unwrap_or(module_id);
        let propagated = propagate_macro_attribute(rule, &productions);
        if owner == module_id {
            module_rules.push(propagated);
            continue;
        }
        module_rules.push(propagated);
    }
    if options.generate_map_ceil_axioms {
        module_rules.extend(generate_map_ceil_rules(&productions)?);
    }
    let generated_axioms = generated_axioms(&productions, &sorts, &overloads, &subsorts, &roles)?;
    for sentence in generated_axioms
        .semantics
        .iter()
        .chain(&generated_axioms.syntax)
    {
        check_variable_sorts(sentence, &|| sentence.to_string())?;
    }
    modules
        .semantics
        .sentences
        .extend(generated_axioms.semantics);
    modules.syntax.sentences.extend(generated_axioms.syntax);
    // The declarations and generated axioms are the whole theory the emitted rules are read in:
    // rule emission adds neither sort declarations nor subsort axioms.
    #[cfg(any(debug_assertions, feature = "kompile-invariant-checks"))]
    let semantics_theory = checked_theory(&modules.semantics);
    #[cfg(any(debug_assertions, feature = "kompile-invariant-checks"))]
    checked_theory(&modules.syntax);

    // Keep ordinary rule injection separate: it resets sentence-local injector state and fixes
    // the error order. Only successful results from the first owise scan are reusable by later
    // owise scans over this immutable, already-rebased rule list.
    let mut owise_competitors = OwiseCompetitors::default();
    let emission_context = RuleEmissionContext {
        valued: &valued,
        productions: &productions,
        injector: &injector,
        converter: &converter,
        module_rules: &module_rules,
        default_reachability,
        roles: &roles,
    };
    let mut emitted_sources = Vec::new();
    // Invariant: `modules.macros` and `modules.semantics.sentences` hold the emitted sentences of the rules of `module_rules` before `rule`, and `owise_competitors` holds the module's owise competitors once an owise equation has scanned for them; each rule is emitted once.
    for rule in &module_rules {
        let emitted = emit_rule_or_claim(rule, false, &emission_context, &mut owise_competitors)?;
        check_variable_sorts(&emitted, &|| describe_source_sentence(rule))?;
        #[cfg(any(debug_assertions, feature = "kompile-invariant-checks"))]
        check_emitted_rule(&semantics_theory, &emitted, rule);
        if is_macro_rule(rule) {
            modules.macros.push(emitted);
        } else {
            modules.semantics.sentences.push(emitted);
        }
        emitted_sources.push(rule.attributes().clone());
    }
    for claim in specification_claims(
        definition,
        module_id,
        &rules,
        options.definition_module.as_deref(),
    ) {
        if is_macro_rule(claim) {
            return Err(ModuleToKoreError::UnsupportedRuleKind {
                kind: "macro claim".into(),
            });
        }
        let emitted = emit_rule_or_claim(claim, true, &emission_context, &mut owise_competitors)?;
        check_variable_sorts(&emitted, &|| describe_source_sentence(claim))?;
        #[cfg(any(debug_assertions, feature = "kompile-invariant-checks"))]
        check_emitted_rule(&semantics_theory, &emitted, claim);
        modules.semantics.sentences.push(emitted);
        emitted_sources.push(claim.attributes().clone());
    }
    Ok((modules, emitted_sources))
}

/// The claims a specification module emits: the module's local claims
/// plus the local claims of every transitively imported module outside the definition module's
/// import closure. Without a distinct definition module every import is inside that closure and
/// only the local claims remain.
fn specification_claims<'a>(
    definition: &ResolvedDefinition,
    module_id: ModuleId,
    rules: &RuleCatalog<'a>,
    definition_module: Option<&str>,
) -> Vec<&'a Sentence> {
    let definition_closure = definition_module
        .and_then(|name| definition.module_id(name))
        .filter(|definition_module| *definition_module != module_id)
        .map(|definition_module| {
            let mut closure = definition
                .transitive_imports(definition_module)
                .into_iter()
                .collect::<BTreeSet<_>>();
            closure.insert(definition_module);
            closure
        });
    match definition_closure {
        Some(closure) => rules
            .claims()
            .filter(|(_, claim)| {
                sentence_owner(definition, claim)
                    .is_none_or(|owner| owner == module_id || !closure.contains(&owner))
            })
            .map(|(_, claim)| claim)
            .collect(),
        None => rules.local_claims().map(|(_, claim)| claim).collect(),
    }
}

/// Build the emitted theory of `module` and check every sentence it holds before rules are
/// emitted: its declarations and generated axioms.
#[cfg(any(debug_assertions, feature = "kompile-invariant-checks"))]
fn checked_theory(module: &Module) -> EmittedTheory {
    k_rust_kore::measure::without_counting(|| {
        let theory = EmittedTheory::of(module);
        theory.check_module(module);
        theory
    })
}

/// Check the sentence `emitted` from the rule, claim or macro `source` against the semantics
/// theory, naming `source` and the pass of its origin record on a violation.
#[cfg(any(debug_assertions, feature = "kompile-invariant-checks"))]
fn check_emitted_rule(theory: &EmittedTheory, emitted: &KoreSentence, source: &Sentence) {
    k_rust_kore::measure::without_counting(|| {
        theory.check(emitted, &|| {
            emitted_from(
                &describe_source_sentence(source),
                source.attributes().origin_record(),
            )
        });
    });
}

fn describe_source_sentence(sentence: &Sentence) -> String {
    let attributes = sentence.attributes();
    if let Some(label) = attributes.string(AttributeKey::Label) {
        return label.to_owned();
    }
    if let Some(unique_id) = attributes.string(AttributeKey::UniqueId) {
        return unique_id.to_owned();
    }
    if let Some(location) = attributes.value(AttributeKey::Location) {
        return attribute_value_string(AttributeKey::Location.as_str(), location);
    }
    match sentence {
        Sentence::Rule { body, .. } | Sentence::Claim { body, .. } => body.to_string(),
        Sentence::SyntaxSort { .. }
        | Sentence::SortSynonym { .. }
        | Sentence::SyntaxLexical { .. }
        | Sentence::Production { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::ContextAlias { .. }
        | Sentence::Context { .. }
        | Sentence::Configuration { .. }
        | Sentence::Bubble { .. } => format!("{sentence:?}"),
    }
}

fn generate_map_ceil_rules(
    productions: &ProductionCatalog<'_>,
) -> Result<Vec<Sentence>, ModuleToKoreError> {
    let mut rules = Vec::new();
    for (in_keys_id, production) in productions.productions() {
        let Sentence::Production {
            label: Some(in_keys_label),
            items: in_keys_items,
            parameters,
            attributes,
            ..
        } = production
        else {
            continue;
        };
        if attributes.string(AttributeKey::Hook) != Some("MAP.in_keys") {
            continue;
        }
        let in_keys_sorts = nonterminal_sorts(in_keys_items);
        let Some(map_sort) = in_keys_sorts.get(1).cloned() else {
            return Err(ModuleToKoreError::InvalidGeneratedMapAxiom {
                production: in_keys_id.0,
                message: "MAP.in_keys must have a map as its second argument".into(),
            });
        };
        if mentions_parameter(&map_sort, parameters) {
            return Err(ModuleToKoreError::InvalidGeneratedMapAxiom {
                production: in_keys_id.0,
                message: format!(
                    "MAP.in_keys production {} has a map argument {map_sort} that mentions its sort parameters",
                    in_keys_label.name
                ),
            });
        }
        let map_productions = productions.productions_for_sort(&SortHead::from(&map_sort));
        let concat = hooked_production(productions, map_productions, "MAP.concat")?;
        let element = hooked_production(productions, map_productions, "MAP.element")?;
        let Some((concat_id, concat_label, _)) = concat else {
            return Err(ModuleToKoreError::InvalidGeneratedMapAxiom {
                production: in_keys_id.0,
                message: format!("map sort {map_sort} has no MAP.concat production"),
            });
        };
        let Some((element_id, element_label, element_sorts)) = element else {
            return Err(ModuleToKoreError::InvalidGeneratedMapAxiom {
                production: in_keys_id.0,
                message: format!("map sort {map_sort} has no MAP.element production"),
            });
        };
        if element_sorts.is_empty() {
            return Err(ModuleToKoreError::InvalidGeneratedMapAxiom {
                production: in_keys_id.0,
                message: "MAP.element must have at least one argument".into(),
            });
        }
        let origins = map_ceil_origin_links([
            production,
            productions.production(concat_id),
            productions.production(element_id),
        ]);

        let sort_parameter =
            Sort::with_parameters(FrontendSort::SortParam.as_str(), vec![Sort::new("Q")]);
        let rest = typed_variable("@Rest", map_sort.clone());
        let arguments = element_sorts
            .iter()
            .enumerate()
            .map(|(index, sort)| typed_variable(format!("@K{index}"), sort.clone()))
            .collect::<Vec<_>>();
        let top = Term::Apply {
            label: Label::with_parameters(
                InternalLabel::Top.as_str(),
                vec![sort_parameter.clone()],
            ),
            arguments: Vec::new(),
        };
        let ceils =
            arguments
                .iter()
                .zip(&element_sorts)
                .skip(1)
                .fold(top, |left, (argument, sort)| Term::Apply {
                    label: Label::with_parameters(
                        InternalLabel::And.as_str(),
                        vec![sort_parameter.clone()],
                    ),
                    arguments: vec![
                        left,
                        Term::Apply {
                            label: Label::with_parameters(
                                InternalLabel::Ceil.as_str(),
                                vec![sort.clone(), sort_parameter.clone()],
                            ),
                            arguments: vec![argument.clone()],
                        },
                    ],
                });
        let element = annotated_application(
            Label::new(&element_label.name),
            arguments.clone(),
            productions.identity(element_id),
        );
        let concat = annotated_application(
            Label::new(&concat_label.name),
            vec![element, rest.clone()],
            productions.identity(concat_id),
        );
        let left = Term::Apply {
            label: Label::with_parameters(
                InternalLabel::Ceil.as_str(),
                vec![map_sort.clone(), sort_parameter.clone()],
            ),
            arguments: vec![concat],
        };
        let in_keys = annotated_application(
            Label::new(&in_keys_label.name),
            vec![arguments[0].clone(), rest],
            productions.identity(in_keys_id),
        );
        let equals = Term::Apply {
            label: Label::with_parameters(
                InternalLabel::Equals.as_str(),
                vec![Sort::builtin(BuiltinSort::Bool), sort_parameter.clone()],
            ),
            arguments: vec![in_keys, bool_token(false)],
        };
        let right = Term::Apply {
            label: Label::with_parameters(InternalLabel::And.as_str(), vec![sort_parameter]),
            arguments: vec![equals, ceils],
        };
        let mut attributes = KAttributes::default();
        attributes.mark(AttributeKey::Simplification);
        let mut rule = Sentence::Rule {
            body: Term::Rewrite {
                left: Box::new(left),
                right: Box::new(right),
            },
            requires: bool_token(true),
            ensures: bool_token(true),
            attributes,
        };
        number_sentence(&mut rule);
        seed_generated_sentence_origin(&mut rule, GeneratingPass::ModuleToKoreMapCeil, origins);
        rules.push(rule);
    }
    Ok(rules)
}

fn map_ceil_origin_links(productions: [&Sentence; 3]) -> Vec<ProvenanceLink> {
    productions
        .into_iter()
        .flat_map(sentence_origin_links)
        // Invariant: `links` holds the distinct links seen so far in encounter order; each `link` is compared with `links` once, O(n^2) in the number of origin links of the three productions.
        .fold(Vec::new(), |mut links, link| {
            if !links.contains(&link) {
                links.push(link);
            }
            links
        })
}

fn nonterminal_sorts(items: &[ProductionItem]) -> Vec<Sort> {
    items
        .iter()
        .filter_map(|item| match item {
            ProductionItem::NonTerminal { sort, .. } => Some(sort.clone()),
            ProductionItem::RegexTerminal { .. } | ProductionItem::Terminal(_) => None,
        })
        .collect()
}

fn hooked_production(
    productions: &ProductionCatalog<'_>,
    candidates: &[ProductionId],
    hook: &str,
) -> Result<Option<(ProductionId, Label, Vec<Sort>)>, ModuleToKoreError> {
    for id in candidates {
        let Sentence::Production {
            label: Some(label),
            parameters,
            items,
            attributes,
            ..
        } = productions.production(*id)
        else {
            continue;
        };
        if attributes.string(AttributeKey::Hook) != Some(hook) {
            continue;
        }
        if !parameters.is_empty() {
            return Err(ModuleToKoreError::InvalidGeneratedMapAxiom {
                production: id.0,
                message: format!("{hook} production {} has sort parameters", label.name),
            });
        }
        return Ok(Some((*id, label.clone(), nonterminal_sorts(items))));
    }
    Ok(None)
}

fn typed_variable(name: impl Into<String>, sort: Sort) -> Term {
    Term::Variable {
        name: name.into(),
        sort: Some(sort),
    }
}

fn annotated_application(
    label: Label,
    arguments: Vec<Term>,
    production: ProductionIdentity,
) -> Term {
    Term::Apply { label, arguments }.with_metadata(crate::kast::TermMetadata {
        production: Some(production),
        ..crate::kast::TermMetadata::default()
    })
}

fn bool_token(value: bool) -> Term {
    Term::Token {
        token: value.to_string(),
        sort: Sort::builtin(BuiltinSort::Bool),
    }
}

fn sentence_owner(definition: &ResolvedDefinition, sentence: &Sentence) -> Option<ModuleId> {
    // Invariant: no module before `module` has a local sentence pointer-equal to `sentence`; each module scans its `local_sentences` once, so the cost is bounded by the local sentences of all of `definition.modules()`.
    definition.modules().find_map(|(module, resolved)| {
        resolved
            .local_sentences
            .iter()
            .any(|candidate| std::ptr::eq(candidate.as_ref(), sentence))
            .then_some(module)
    })
}

fn reachability_mode(attributes: &KAttributes) -> Option<ReachabilityMode> {
    if attributes.has(AttributeKey::OnePath) {
        Some(ReachabilityMode::OnePath)
    } else if attributes.has(AttributeKey::AllPath) {
        Some(ReachabilityMode::AllPath)
    } else {
        None
    }
}

fn is_macro_rule(sentence: &Sentence) -> bool {
    sentence.attributes().has_any(&AttributeKey::MACRO_LIKE)
}

fn propagate_macro_attribute(sentence: &Sentence, productions: &ProductionCatalog<'_>) -> Sentence {
    if is_macro_rule(sentence) || sentence.attributes().has(AttributeKey::Simplification) {
        return sentence.clone();
    }
    let Sentence::Rule {
        body,
        requires,
        ensures,
        attributes,
    } = sentence
    else {
        return sentence.clone();
    };
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "Term is not a sentence kind; only the listed variants are special here"
    )]
    let left = match body.unannotated() {
        Term::Rewrite { left, .. } => left.as_ref(),
        _ => body,
    };
    let application = peel_alias(left);
    let Term::Apply { label, .. } = application.unannotated() else {
        return sentence.clone();
    };
    let Ok(production) = resolve_equation_production(application, label, productions) else {
        return sentence.clone();
    };
    let Sentence::Production {
        attributes: production_attributes,
        ..
    } = production
    else {
        unreachable!("production catalogs contain productions")
    };
    let Some(attribute) = AttributeKey::MACRO_LIKE
        .into_iter()
        .find(|attribute| production_attributes.has(*attribute))
    else {
        return sentence.clone();
    };
    let mut attributes = attributes.clone();
    attributes.mark(attribute);
    Sentence::Rule {
        body: body.clone(),
        requires: requires.clone(),
        ensures: ensures.clone(),
        attributes,
    }
}

fn peel_alias(mut term: &Term) -> &Term {
    while let Term::As { pattern, .. } = term.unannotated() {
        term = pattern;
    }
    term
}

#[allow(clippy::too_many_arguments)]
fn transitive_impure_labels(
    definition: &ResolvedDefinition,
    module: ModuleId,
    productions: &ProductionCatalog<'_>,
) -> BTreeSet<String> {
    let rules = definition.rule_catalog(module);
    let graph = LabelDependencyGraph::build(productions, &rules, is_macro_rule);
    let impure = productions
        .productions()
        .filter_map(|(_, production)| match production {
            Sentence::Production {
                label: Some(label),
                attributes,
                ..
            } if attributes.has(AttributeKey::Impure) => Some(LabelHead::from(label)),
            Sentence::SyntaxSort { .. }
            | Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::Production { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::ContextAlias { .. }
            | Sentence::Context { .. }
            | Sentence::Rule { .. }
            | Sentence::Claim { .. }
            | Sentence::Configuration { .. }
            | Sentence::Bubble { .. } => None,
        })
        .collect::<BTreeSet<_>>();
    graph
        .backward_closure(impure)
        .into_iter()
        .map(|label| label.as_str().to_owned())
        .collect()
}

fn sort_declarations(
    sorts: &SortCatalog<'_>,
    productions: &ProductionCatalog<'_>,
    valued: &BTreeSet<String>,
) -> Result<Vec<KoreSentence>, DeclarationError> {
    let mut declarations = Vec::new();
    let mut declared_names: BTreeMap<String, &SortHead> = BTreeMap::new();
    // Invariant: `declarations` holds one sort declaration for every head of `sorts.sorted_defined_heads()` before `head` other than `K` and `KItem`, and the declared names are pairwise distinct; a collection-hooked head also scans `productions` once in `collection_attribute_overrides`.
    for head in sorts.sorted_defined_heads() {
        if head.as_str() == BuiltinSort::K.k_name() || head.as_str() == BuiltinSort::KItem.k_name()
        {
            continue;
        }
        let name = identifier::encode_sort_name(head.as_str());
        if let Some(previous) = declared_names.get(&name) {
            return Err(DeclarationError::DuplicateSortName {
                name,
                first: previous.to_string(),
                second: head.to_string(),
            });
        }
        declared_names.insert(name.clone(), head);
        let source_attributes = sorts.attributes_for(head).cloned().unwrap_or_default();
        let mut entries = source_attributes.semantic_entries().clone();
        // The definition checks and term conversion admit a domain value by
        // `SortCatalog::admits_domain_value`, whose sorts all have heads this predicate accepts,
        // so every `\dv` of the emitted theory is at a sort declared here with `hasDomainValues`.
        entries.remove(AttributeKey::HasDomainValues.as_str());
        if sorts.head_admits_domain_values(head) {
            entries.insert(
                AttributeKey::HasDomainValues.as_str().into(),
                Value::String(String::new()),
            );
        }
        if head.parameters() == 0 && SortRole::of_name(head.as_str()) == SortRole::Nat {
            entries.insert(
                AttributeKey::Nat.as_str().into(),
                Value::String(head.as_str().into()),
            );
        }
        let mut overrides = BTreeMap::new();
        if source_attributes
            .string(AttributeKey::Hook)
            .is_some_and(|hook| COLLECTION_HOOKS.contains(&hook))
        {
            collection_attribute_overrides(head, productions, &mut overrides)?;
        }
        declarations.push(KoreSentence::SortDeclaration {
            hooked: sorts.declares_hooked_sort(head),
            name,
            parameters: (0..head.parameters())
                .map(|parameter| format!("SortS{parameter}"))
                .collect(),
            attributes: emit_attributes(&entries, valued, &overrides),
        });
    }
    Ok(declarations)
}

fn collection_attribute_overrides(
    head: &SortHead,
    productions: &ProductionCatalog<'_>,
    overrides: &mut BTreeMap<String, Vec<Pattern>>,
) -> Result<(), DeclarationError> {
    let production = productions
        .productions()
        .map(|(_, production)| production)
        .find(|production| {
            matches!(
                production,
                Sentence::Production { sort, attributes, .. }
                    if SortHead::from(sort) == *head && attributes.string(AttributeKey::Element).is_some()
            )
        })
        .ok_or_else(|| DeclarationError::InvalidCollectionSort {
            sort: head.to_string(),
            message: "no production carries the `element` attribute".into(),
        })?;
    let Sentence::Production {
        label, attributes, ..
    } = production
    else {
        unreachable!()
    };
    let label = label
        .as_ref()
        .ok_or_else(|| DeclarationError::InvalidCollectionSort {
            sort: head.to_string(),
            message: "the collection concatenation production has no label".into(),
        })?;
    for (key, label_name) in [
        (
            AttributeKey::Element,
            attributes.string(AttributeKey::Element),
        ),
        (AttributeKey::Concat, Some(label.name.as_str())),
        (AttributeKey::Unit, attributes.string(AttributeKey::Unit)),
        (
            AttributeKey::Update,
            attributes.string(AttributeKey::Update),
        ),
    ] {
        if let Some(label_name) = label_name {
            overrides.insert(
                key.as_str().into(),
                vec![label_pattern(label_name, productions)?],
            );
        }
    }
    Ok(())
}

/// The attributes of one symbol declaration: the source's semantic attributes, the claims
/// `claims` states, the `macro` attribute of a macro-like `kind`, and, for a syntax-module
/// declaration, the concrete-syntax metadata.
#[allow(clippy::too_many_arguments)]
fn symbol_attributes(
    source: &KAttributes,
    label: &Label,
    sort: &Sort,
    parameters: &[Sort],
    kind: ProductionKind,
    claims: SymbolClaims,
    productions: &ProductionCatalog<'_>,
    valued: &BTreeSet<String>,
    impure_labels: &BTreeSet<String>,
    syntax: Option<SyntaxDeclaration<'_>>,
    items: &[ProductionItem],
    hook_namespaces: &[String],
    backend: CompilationBackend,
) -> Result<Attributes, DeclarationError> {
    let mut entries = source.semantic_entries().clone();
    for key in [
        AttributeKey::Constructor,
        AttributeKey::Hook,
        AttributeKey::Assoc,
        AttributeKey::Bracket,
        AttributeKey::Colors,
        AttributeKey::Comm,
        AttributeKey::Format,
        AttributeKey::Left,
        AttributeKey::Right,
    ] {
        entries.remove(key.as_str());
    }

    // A value head's totality is decided by its equations, including the functional axiom.
    // Discard deprecated source `functional` so it cannot contradict that shared judgement;
    // a source `function, total` instead states an explicit axiom of the definition.
    if matches!(
        kind.declared_totality(),
        DeclaredTotality::ValuesUnlessEquations
    ) {
        entries.remove(AttributeKey::Functional.as_str());
    }

    if let Some(hook) = interpreted_hook(source, hook_namespaces) {
        entries.insert(AttributeKey::Hook.as_str().into(), hook.clone());
    }
    let freeness = claims.freeness();
    if freeness.declares_constructor() {
        entries.insert(
            AttributeKey::Constructor.as_str().into(),
            Value::String(String::new()),
        );
    }
    if claims.functional() {
        entries.insert(
            AttributeKey::Functional.as_str().into(),
            Value::String(String::new()),
        );
    }
    // An irreducible application of a value production is a value even when some equations
    // can make other applications undefined. LLVM preserves that reading without `function`;
    // the Rust target pairs `function` for equation verification with `value-production`,
    // which restores the value reading in its backend. Neither spelling asserts totality.
    let partial_value_production = !claims.functional()
        && matches!(
            kind.declared_totality(),
            DeclaredTotality::ValuesUnlessEquations
        )
        && matches!(claims.declaration(), Declaration::SemanticAndSyntax);
    if partial_value_production {
        match backend {
            CompilationBackend::Llvm => {}
            CompilationBackend::Rust => {
                entries.insert(
                    AttributeKey::Function.as_str().into(),
                    Value::String(String::new()),
                );
            }
        }
    }
    if claims.anywhere() {
        entries.insert(
            AttributeKey::Anywhere.as_str().into(),
            Value::String(String::new()),
        );
    }
    if impure_labels.contains(&label.name) {
        entries.insert(
            AttributeKey::Impure.as_str().into(),
            Value::String(String::new()),
        );
    }
    if freeness.declares_injective() {
        entries.insert(
            AttributeKey::Injective.as_str().into(),
            Value::String(String::new()),
        );
    }
    // A macro-like rule headed by a production that is not itself macro-like adds no `macro`
    // attribute: that would claim every application is expanded away, while a rule whose left
    // side does not cover all arguments leaves others.
    if kind.is_macro_like() {
        entries.insert(
            AttributeKey::Macro.as_str().into(),
            Value::String(String::new()),
        );
    }

    let mut overrides = BTreeMap::new();
    if partial_value_production {
        overrides.insert(KoreAttribute::ValueProduction.as_str().into(), Vec::new());
    }
    if let Some(unit) = entries
        .get(AttributeKey::Unit.as_str())
        .and_then(Value::as_str)
    {
        let instance = UnitInstance::of(productions, unit, sort).map_err(|error| match error {
            UnitInstanceError::NotOneProduction { count } => {
                DeclarationError::InvalidCollectionLabel {
                    label: unit.into(),
                    productions: count,
                }
            }
            UnitInstanceError::Unbound { parameters } => {
                DeclarationError::SchematicAttributeLabel {
                    label: unit.into(),
                    parameters,
                }
            }
        })?;
        overrides.insert(
            AttributeKey::Unit.as_str().into(),
            vec![Pattern::Application {
                symbol: encode_kore_label_with_formals(instance.label(), parameters),
                arguments: Vec::new(),
            }],
        );
    }
    for key in [AttributeKey::Element, AttributeKey::Update] {
        if let Some(label) = entries.get(key.as_str()).and_then(Value::as_str) {
            overrides.insert(
                key.as_str().into(),
                vec![label_pattern(label, productions)?],
            );
        }
    }
    if let Some(syntax) = syntax {
        add_syntax_attributes(source, label, items, syntax, &mut entries, &mut overrides);
    }
    debug_assert!(
        syntax.is_some()
            || (backend == CompilationBackend::Llvm
                && overrides.contains_key(KoreAttribute::ValueProduction.as_str()))
            || [
                AttributeKey::Constructor,
                AttributeKey::Functional,
                AttributeKey::Function,
                AttributeKey::Anywhere,
                AttributeKey::Macro,
            ]
            .into_iter()
            .any(|key| entries.contains_key(key.as_str())),
        "production `{label}` has no backend semantic role; F3: a semantic production must \
         carry a totality or evaluation marker, or have irreducible applications that LLVM \
         treats as values",
    );
    Ok(emit_attributes(&entries, valued, &overrides))
}

fn add_syntax_attributes(
    source: &KAttributes,
    label: &Label,
    items: &[ProductionItem],
    syntax: SyntaxDeclaration<'_>,
    entries: &mut BTreeMap<String, Value>,
    overrides: &mut BTreeMap<String, Vec<Pattern>>,
) {
    let Some(mut format) = source
        .string(AttributeKey::Format)
        .map(str::to_owned)
        .or_else(|| default_format(items))
    else {
        return;
    };
    let mut nonterminal = 1;
    // Invariant: `format` has slots `%1` to `%index` replaced, and `nonterminal` is one more than the number of nonterminals in `items[..index]`; each `replace_format_slot` call rescans `format`, O(|items| * |format|).
    for (index, item) in items.iter().enumerate() {
        let replacement = match item {
            ProductionItem::NonTerminal { .. } => {
                let replacement = format!("%{nonterminal}");
                nonterminal += 1;
                replacement
            }
            ProductionItem::Terminal(value) => {
                format!("%c{}%r", value.replace('%', "%%"))
            }
            ProductionItem::RegexTerminal { .. } => return,
        };
        format = replace_format_slot(&format, index + 1, &replacement);
    }
    entries.insert(
        AttributeKey::Format.as_str().into(),
        Value::String(format.clone()),
    );
    for key in [
        AttributeKey::Assoc,
        AttributeKey::Bracket,
        AttributeKey::Colors,
        AttributeKey::Comm,
    ] {
        if let Some(value) = source.value(key) {
            entries.insert(key.as_str().into(), value.clone());
        }
    }
    if let Some(color) = source.string(AttributeKey::Color) {
        let colors = format
            .match_indices("%c")
            .map(|_| color)
            .collect::<Vec<_>>();
        entries.insert(
            AttributeKey::Colors.as_str().into(),
            Value::String(colors.join(",")),
        );
    }
    entries.insert(
        AttributeKey::Terminals.as_str().into(),
        Value::String(
            items
                .iter()
                .map(|item| {
                    if matches!(item, ProductionItem::NonTerminal { .. }) {
                        '0'
                    } else {
                        '1'
                    }
                })
                .collect(),
        ),
    );
    let SyntaxDeclaration::UnderLabel(syntax_relations) = syntax else {
        return;
    };
    for key in [
        AttributeKey::Priorities,
        AttributeKey::Left,
        AttributeKey::Right,
    ] {
        entries.insert(key.as_str().into(), Value::String(String::new()));
    }
    overrides.insert(
        AttributeKey::Priorities.as_str().into(),
        syntax_relations
            .priorities
            .get(&label.name)
            .cloned()
            .unwrap_or_default(),
    );
    overrides.insert(
        AttributeKey::Left.as_str().into(),
        syntax_relations
            .left
            .get(&label.name)
            .cloned()
            .unwrap_or_default(),
    );
    overrides.insert(
        AttributeKey::Right.as_str().into(),
        syntax_relations
            .right
            .get(&label.name)
            .cloned()
            .unwrap_or_default(),
    );
}

fn default_format(items: &[ProductionItem]) -> Option<String> {
    if is_named_prefix_production(items) {
        Some(
            items
                .iter()
                .enumerate()
                .map(|(index, item)| match item {
                    ProductionItem::Terminal(value) if value == "(" => {
                        format!("%{}...", index + 1)
                    }
                    ProductionItem::Terminal(_) => format!("%{}", index + 1),
                    ProductionItem::NonTerminal {
                        name: Some(name), ..
                    } => {
                        format!("{name}: %{}", index + 1)
                    }
                    ProductionItem::RegexTerminal { .. }
                    | ProductionItem::NonTerminal { name: None, .. } => unreachable!(),
                })
                .collect::<Vec<_>>()
                .join(" "),
        )
    } else {
        Some(
            (1..=items.len())
                .map(|index| format!("%{index}"))
                .collect::<Vec<_>>()
                .join(" "),
        )
    }
}

fn is_named_prefix_production(items: &[ProductionItem]) -> bool {
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "ProductionItem is not a sentence kind; only the listed variants are special here"
    )]
    let nonterminals = items
        .iter()
        .filter_map(|item| match item {
            ProductionItem::NonTerminal { name, .. } => Some(name),
            _ => None,
        })
        .collect::<Vec<_>>();
    !nonterminals.is_empty()
        && nonterminals.iter().all(|name| name.is_some())
        && is_prefix_production(items)
}

fn is_prefix_production(items: &[ProductionItem]) -> bool {
    let mut state = 0;
    for item in items {
        state = match (state, item) {
            (0, ProductionItem::Terminal(value)) if value == "(" => 1,
            (0, ProductionItem::Terminal(_)) => 0,
            (1, ProductionItem::NonTerminal { .. }) => 2,
            (1, ProductionItem::Terminal(value)) if value == ")" => 4,
            (2, ProductionItem::Terminal(value)) if value == "," => 3,
            (2, ProductionItem::Terminal(value)) if value == ")" => 4,
            (3, ProductionItem::NonTerminal { .. }) => 2,
            _ => return false,
        };
    }
    state == 4
}

fn replace_format_slot(format: &str, slot: usize, replacement: &str) -> String {
    let needle = format!("%{slot}");
    let mut result = String::with_capacity(format.len() + replacement.len());
    let mut remaining = format;
    // Invariant: `result` is the prefix of `format` before `remaining` with every standalone `%slot` replaced; each iteration moves `remaining` past one occurrence of `needle`, so the loop is linear in `format.len()`.
    while let Some(index) = remaining.find(&needle) {
        result.push_str(&remaining[..index]);
        let after = &remaining[index + needle.len()..];
        if after.starts_with(|character: char| character.is_ascii_digit()) {
            result.push_str(&needle);
        } else {
            result.push_str(replacement);
        }
        remaining = after;
    }
    result.push_str(remaining);
    result
}

fn valued_attributes(sentences: &[&Sentence]) -> BTreeSet<String> {
    let mut valued = [
        AttributeKey::Nat,
        AttributeKey::Terminals,
        AttributeKey::Colors,
        AttributeKey::Priority,
    ]
    .into_iter()
    .map(|key| key.as_str().to_owned())
    .collect::<BTreeSet<_>>();
    for attributes in sentences.iter().map(|sentence| sentence.attributes()) {
        for (key, value) in attributes.semantic_entries() {
            if !attribute_value_string(key, value).is_empty() {
                valued.insert(key.clone());
            }
        }
    }
    if valued.contains(AttributeKey::Token.as_str()) {
        valued.remove(AttributeKey::HasDomainValues.as_str());
    }
    // This frontend-only typed attribute serves only to declare an axiom's sort variables, so it
    // is not counted among the valued attributes.
    valued.remove(AttributeKey::SortParams.as_str());
    valued
}

fn emit_attributes(
    entries: &BTreeMap<String, Value>,
    valued: &BTreeSet<String>,
    overrides: &BTreeMap<String, Vec<Pattern>>,
) -> Attributes {
    let keys = entries
        .keys()
        .chain(overrides.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    let patterns = keys
        .into_iter()
        .filter(|key| {
            overrides.contains_key(key)
                || AttributeKey::from_name(key).is_some_and(AttributeKey::emits)
        })
        .map(|key| {
            let arguments = overrides.get(&key).cloned().unwrap_or_else(|| {
                if valued.contains(&key) {
                    vec![Pattern::String(
                        entries
                            .get(&key)
                            .map(|value| attribute_value_string(&key, value))
                            .unwrap_or_default()
                            .into(),
                    )]
                } else {
                    Vec::new()
                }
            });
            Pattern::Application {
                symbol: Symbol {
                    name: kore_attribute_name(&key),
                    sort_parameters: Vec::new(),
                },
                arguments,
            }
        })
        .collect();
    Attributes(patterns)
}

/// The KORE symbol of an emitted attribute: the vocabulary's spelling for a well-known key
/// that reaches `definition.kore`, the encoder for an override-only key (`left`, `right`).
fn kore_attribute_name(key: &str) -> String {
    match AttributeKey::from_name(key) {
        Some(key) if key.emits() => KoreAttribute::from(key).as_str().to_owned(),
        _ => identifier::encode(key),
    }
}

/// The KORE attribute symbol of every key with `emits()`; the kore crate does not learn K keys,
/// so the link lives with the emitter. `every_emitted_key_names_the_kore_attribute_the_backend_reads`
/// pins each spelling against `identifier::encode` and reaches every non-marker variant.
impl From<AttributeKey> for KoreAttribute {
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "AttributeKey is not a sentence kind; only the listed variants are special here"
    )]
    fn from(key: AttributeKey) -> Self {
        match key {
            AttributeKey::Label => Self::Label,
            AttributeKey::Concrete => Self::Concrete,
            AttributeKey::Symbolic => Self::Symbolic,
            AttributeKey::Token => Self::Token,
            AttributeKey::Hook => Self::Hook,
            AttributeKey::Comm => Self::Comm,
            AttributeKey::Priority => Self::Priority,
            AttributeKey::Circularity => Self::Circularity,
            AttributeKey::Trusted => Self::Trusted,
            AttributeKey::Depends => Self::Depends,
            AttributeKey::Cool => Self::Cool,
            AttributeKey::NonExecutable => Self::NonExecutable,
            AttributeKey::Owise => Self::Owise,
            AttributeKey::PreservesDefinedness => Self::PreservesDefinedness,
            AttributeKey::SmtLemma => Self::SmtLemma,
            AttributeKey::Anywhere => Self::Anywhere,
            AttributeKey::Simplification => Self::Simplification,
            AttributeKey::Syntactic => Self::Syntactic,
            AttributeKey::Colors => Self::Colors,
            AttributeKey::Element => Self::Element,
            AttributeKey::Format => Self::Format,
            AttributeKey::Klabel => Self::Klabel,
            AttributeKey::Smtlib => Self::Smtlib,
            AttributeKey::SmtHook => Self::SmtHook,
            AttributeKey::Unit => Self::Unit,
            AttributeKey::Update => Self::Update,
            AttributeKey::Symbol => Self::Symbol,
            AttributeKey::Alias => Self::Alias,
            AttributeKey::AliasRec => Self::AliasRec,
            AttributeKey::Assoc => Self::Assoc,
            AttributeKey::Binder => Self::Binder,
            AttributeKey::Bracket => Self::Bracket,
            AttributeKey::Cell => Self::Cell,
            AttributeKey::Constructor => Self::Constructor,
            AttributeKey::Deprecated => Self::Deprecated,
            AttributeKey::FreshGenerator => Self::FreshGenerator,
            AttributeKey::Function => Self::Function,
            AttributeKey::Functional => Self::Functional,
            AttributeKey::Idem => Self::Idem,
            AttributeKey::Impure => Self::Impure,
            AttributeKey::Injective => Self::Injective,
            AttributeKey::Macro => Self::Macro,
            AttributeKey::MacroRec => Self::MacroRec,
            AttributeKey::Memo => Self::Memo,
            AttributeKey::NoEvaluators => Self::NoEvaluators,
            AttributeKey::Total => Self::Total,
            AttributeKey::Concat => Self::Concat,
            AttributeKey::CoolLike => Self::CoolLike,
            AttributeKey::HasDomainValues => Self::HasDomainValues,
            AttributeKey::Nat => Self::Nat,
            AttributeKey::Priorities => Self::Priorities,
            AttributeKey::Source => Self::Source,
            AttributeKey::Location => Self::Location,
            AttributeKey::SymbolOverload => Self::SymbolOverload,
            AttributeKey::Terminals => Self::Terminals,
            AttributeKey::UniqueId => Self::UniqueId,
            _ => unreachable!("{key:?} does not reach definition.kore"),
        }
    }
}

/// The string emission writes as the argument of the attribute `key` with value `value`.
pub(crate) fn attribute_value_string(key: &str, value: &Value) -> String {
    let key = AttributeKey::from_name(key);
    if key == Some(AttributeKey::Location)
        && let Some(values) = value.as_array()
        && let [start_line, start_column, end_line, end_column] = values.as_slice()
    {
        return format!("Location({start_line},{start_column},{end_line},{end_column})");
    }
    if key == Some(AttributeKey::Source)
        && let Some(source) = value.as_str()
    {
        return format!("Source({source})");
    }
    match value {
        Value::String(value) => value.clone(),
        Value::Null => "null".into(),
        Value::Bool(value) => value.to_string(),
        Value::Number(value) => value.to_string(),
        Value::Array(_) | Value::Object(_) => value.to_string(),
    }
}

fn label_pattern(
    label: &str,
    productions: &ProductionCatalog<'_>,
) -> Result<Pattern, DeclarationError> {
    let head = LabelHead::new(label);
    let matches = productions.productions_for(&head);
    let [production] = matches else {
        return Err(DeclarationError::InvalidCollectionLabel {
            label: label.into(),
            productions: matches.len(),
        });
    };
    let parameters = match productions.production(*production) {
        Sentence::Production {
            label: production_label,
            parameters,
            ..
        } => {
            if !parameters.is_empty() {
                return Err(DeclarationError::SchematicAttributeLabel {
                    label: label.into(),
                    parameters: parameters.clone(),
                });
            }
            production_label.as_ref()
        }
        Sentence::SyntaxSort { .. }
        | Sentence::SortSynonym { .. }
        | Sentence::SyntaxLexical { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::ContextAlias { .. }
        | Sentence::Context { .. }
        | Sentence::Rule { .. }
        | Sentence::Claim { .. }
        | Sentence::Configuration { .. }
        | Sentence::Bubble { .. } => None,
    }
    .map(|label| label.parameters.clone())
    .unwrap_or_default();
    Ok(Pattern::Application {
        symbol: encode_kore_label(&Label::with_parameters(label, parameters)),
        arguments: Vec::new(),
    })
}

/// Whether `attributes` carry a hook whose namespace is builtin or admitted by
/// `hook_namespaces`, which a hooked-symbol declaration would name.
pub(crate) fn is_real_hook(attributes: &KAttributes, hook_namespaces: &[String]) -> bool {
    attributes.string(AttributeKey::Hook).is_some_and(|hook| {
        hook.split_once('.').is_some_and(|(namespace, _)| {
            BUILTIN_HOOK_NAMESPACES.contains(&namespace)
                || hook_namespaces.iter().any(|admitted| admitted == namespace)
        })
    })
}

/// The hook a symbol declaration names, and then declares a hooked symbol for.
///
/// A hook names the builtin implementation of a function: the backend evaluates the symbol's
/// applications by it. Only a `function` production's symbol is evaluated, so only it is
/// declared hooked; every other symbol's meaning is fixed by its constructor or macro axioms,
/// and a hook on it would name an implementation nothing evaluates. Deriving both the
/// `hooked-symbol` keyword and the `hook` attribute from this one predicate means a declaration
/// carries the attribute exactly when it is a hooked symbol. A non-function production with a
/// real hook is rejected before emission (`uninterpreted_hook_diagnostics` in `compile.rs`).
fn interpreted_hook<'a>(
    attributes: &'a KAttributes,
    hook_namespaces: &[String],
) -> Option<&'a Value> {
    if attributes.has(AttributeKey::Function) && is_real_hook(attributes, hook_namespaces) {
        attributes.value(AttributeKey::Hook)
    } else {
        None
    }
}

/// Encode a K label as a KORE symbol head.
pub fn encode_kore_label(label: &Label) -> Symbol {
    encode_kore_label_with_formals(label, &[])
}

fn encode_kore_label_with_formals(label: &Label, formals: &[Sort]) -> Symbol {
    Symbol {
        name: if label.is(WellKnownSymbol::Inj) {
            label.name.clone()
        } else {
            identifier::encode_label(&label.name)
        },
        sort_parameters: label
            .parameters
            .iter()
            .map(|sort| encode_kore_sort_with_formals(sort, formals))
            .collect(),
    }
}

/// Encode a K sort as a concrete KORE sort application.
pub fn encode_kore_sort(sort: &Sort) -> KoreSort {
    encode_kore_sort_with_formals(sort, &[])
}

// Invariant: each call encodes one node of `sort` and recurses only into its `parameters`, so the finite `sort` bounds the calls; `formals` is the same at every depth.
pub(crate) fn encode_kore_sort_with_formals(sort: &Sort, formals: &[Sort]) -> KoreSort {
    let name = identifier::encode_sort_name(&sort.name);
    if formals.contains(sort) {
        KoreSort::Variable(name)
    } else {
        KoreSort::Application {
            name,
            arguments: sort
                .parameters
                .iter()
                .map(|parameter| encode_kore_sort_with_formals(parameter, formals))
                .collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use indoc::indoc;
    use serde_json::json;

    use super::*;

    fn mn1_modules(source: &str, backend: CompilationBackend) -> DeclarationModules {
        let parsed = crate::outer::parse("mn1.k", source).expect("definition should parse");
        let lowered = crate::outer::lower(&parsed, "MAIN").expect("definition should lower");
        let definition =
            crate::inner::resolve_rule_bubbles(&lowered).expect("rules should resolve");
        let definition = crate::kompile::resolve_semantic_casts(&definition)
            .expect("semantic casts should resolve");
        let resolved = ResolvedDefinition::resolve(&definition).expect("definition should resolve");
        module_to_kore_from_resolved_with_options(
            &resolved,
            "MAIN",
            ModuleToKoreOptions {
                backend,
                ..ModuleToKoreOptions::default()
            },
        )
        .expect("unchecked library definition should emit")
    }

    fn mn1_symbol_attributes<'a>(module: &'a Module, name: &str) -> &'a Attributes {
        module
            .sentences
            .iter()
            .find_map(|sentence| match sentence {
                KoreSentence::SymbolDeclaration {
                    symbol, attributes, ..
                } if symbol.name == name => Some(attributes),
                KoreSentence::Import { .. }
                | KoreSentence::SortDeclaration { .. }
                | KoreSentence::SymbolDeclaration { .. }
                | KoreSentence::AliasDeclaration { .. }
                | KoreSentence::Axiom { .. }
                | KoreSentence::Claim { .. } => None,
            })
            .expect("symbol should be declared")
    }

    fn mn1_has_attribute(attributes: &Attributes, name: &str) -> bool {
        attributes.0.iter().any(|attribute| {
            matches!(attribute, Pattern::Application { symbol, arguments }
                if symbol.name == name && symbol.sort_parameters.is_empty() && arguments.is_empty())
        })
    }

    #[test]
    fn mn1_rule_level_partial_macro_has_a_role_on_both_targets() {
        let source = indoc! {r#"
            module MAIN
              syntax S ::= "z" [symbol(z)]
                         | "plain(" S ")" [symbol(plain)]
                         | "partial(" S ")" [function, symbol(partial)]
              rule plain(X:S) => partial(X:S) [macro]
            endmodule
        "#};
        for backend in [CompilationBackend::Rust, CompilationBackend::Llvm] {
            let modules = mn1_modules(source, backend);
            for module in [&modules.semantics, &modules.syntax] {
                let attributes = mn1_symbol_attributes(module, "Lblplain");
                assert!(mn1_has_attribute(attributes, "value-production"));
                assert_eq!(
                    mn1_has_attribute(attributes, "function"),
                    backend == CompilationBackend::Rust
                );
                for absent in ["constructor", "functional", "anywhere", "macro"] {
                    assert!(!mn1_has_attribute(attributes, absent), "{absent}");
                }
            }
            assert_eq!(modules.macros.len(), 1);
        }
    }

    #[test]
    fn mn1_deprecated_functional_on_a_function_emits_the_totality_axiom() {
        for totality in ["functional", "total"] {
            let modules = mn1_modules(
                &format!(
                    "module MAIN
                       syntax S ::= f(S) [function, {totality}, symbol(f)]
                     endmodule"
                ),
                CompilationBackend::Rust,
            );
            for module in [&modules.semantics, &modules.syntax] {
                assert!(mn1_has_attribute(
                    mn1_symbol_attributes(module, "Lblf"),
                    "functional"
                ));
            }
            let functional_axiom = modules.semantics.sentences.iter().any(|sentence| {
                let KoreSentence::Axiom { pattern, attributes, .. } = sentence else {
                    return false;
                };
                let Pattern::Exists { variable, body, .. } = pattern.as_ref() else {
                    return false;
                };
                let Pattern::Equals { left, right, .. } = body.as_ref() else {
                    return false;
                };
                mn1_has_attribute(attributes, "functional")
                    && matches!(left.as_ref(), Pattern::Variable(value) if value == variable.as_ref())
                    && matches!(right.as_ref(), Pattern::Application { symbol, .. } if symbol.name == "Lblf")
            });
            println!(
                "[function, {totality}]: declaration functional=true, functional axiom={functional_axiom}"
            );
            assert!(functional_axiom, "{totality} must state a totality axiom");
        }
    }

    #[test]
    fn generates_symbolic_backend_map_definedness_rule() {
        let source = indoc! {r#"
            module MAIN
              syntax Bool
              syntax Key
              syntax Value
              syntax Map
              syntax Map ::= Key "|->" Value [function, hook(MAP.element), symbol(mapItem)]
              syntax Map ::= Map Map [function, hook(MAP.concat), symbol(mapConcat)]
              syntax Bool ::= Key "in_keys" Map [function, hook(MAP.in_keys), symbol(inKeys)]
            endmodule
        "#};
        let parsed = crate::outer::parse("map.k", source).expect("definition should parse");
        let definition = crate::outer::lower(&parsed, "MAIN").expect("definition should lower");
        let resolved = ResolvedDefinition::resolve(&definition).expect("definition should resolve");
        let module = resolved.module_id("MAIN").unwrap();
        let productions = resolved.production_catalog(module);
        let rules = generate_map_ceil_rules(&productions).expect("MAP rule should generate");
        let mut snapshot_rules = rules.clone();
        for rule in &mut snapshot_rules {
            rule.attributes_mut()
                .remove(crate::provenance::ORIGIN_ATTRIBUTE);
        }

        insta::with_settings!({
            description => format!("K definition:\n\n{source}"),
            omit_expression => true,
            prepend_module_to_snapshot => true,
        }, {
            insta::assert_debug_snapshot!(snapshot_rules);
        });
        assert!(rules.iter().all(|rule| {
            rule.attributes()
                .get(crate::provenance::ORIGIN_ATTRIBUTE)
                .is_some_and(|receipt| {
                    receipt["pass"]
                        == crate::provenance::GeneratingPass::ModuleToKoreMapCeil.as_str()
                        && receipt["origins"]
                            .as_array()
                            .is_some_and(|origins| !origins.is_empty())
                })
        }));
        let source_link = |sentence: &str| {
            let start = source.find(sentence).unwrap();
            json!({
                "kind": "source",
                "source": 0,
                "start": start,
                "end": start + sentence.len(),
            })
        };
        assert_eq!(
            rules[0]
                .attributes()
                .get(crate::provenance::ORIGIN_ATTRIBUTE)
                .unwrap()["origins"],
            json!([
                source_link("Key \"in_keys\" Map [function, hook(MAP.in_keys), symbol(inKeys)]"),
                source_link("Map Map [function, hook(MAP.concat), symbol(mapConcat)]"),
                source_link("Key \"|->\" Value [function, hook(MAP.element), symbol(mapItem)]"),
            ]),
        );
    }

    #[test]
    fn map_ceil_origin_links_deduplicate_without_reordering() {
        let source_link = |start, end| ProvenanceLink::Source {
            span: crate::kast::TermSpan {
                source: crate::provenance::SourceId(0),
                start,
                end,
            },
        };
        let shared = ProvenanceLink::Sentence {
            unique_id: "shared".into(),
        };
        let sentence = |origins: Vec<crate::provenance::ProvenanceLink>| {
            let mut attributes = KAttributes::default();
            attributes.insert(
                crate::provenance::ORIGIN_ATTRIBUTE,
                crate::provenance::OriginRecord {
                    pass: GeneratingPass::MacroExpansion,
                    origins: origins.into(),
                    destination: None,
                }
                .to_value(),
            );
            Sentence::SyntaxSort {
                parameters: Vec::new(),
                sort: Sort::new("Map"),
                attributes,
            }
        };
        let in_keys = sentence(vec![source_link(30, 40), shared.clone()]);
        let concat = sentence(vec![shared.clone(), source_link(20, 30)]);
        let element = sentence(vec![source_link(30, 40), source_link(10, 20)]);

        assert_eq!(
            map_ceil_origin_links([&in_keys, &concat, &element]),
            [
                source_link(30, 40),
                shared,
                source_link(20, 30),
                source_link(10, 20)
            ],
        );
    }

    /// The emitter and the backend agree on every attribute spelling: each emitted key's
    /// encoded name is its `KoreAttribute`, and every variant a key can produce is produced.
    #[test]
    fn every_emitted_key_names_the_kore_attribute_the_backend_reads() {
        let mut reached = BTreeSet::new();
        for key in AttributeKey::ALL.into_iter().filter(|key| key.emits()) {
            let attribute = KoreAttribute::from(key);
            assert_eq!(
                identifier::encode(key.as_str()),
                attribute.as_str(),
                "{key:?}"
            );
            reached.insert(attribute.as_str());
        }
        for attribute in KoreAttribute::ALL {
            assert_eq!(
                reached.contains(attribute.as_str()),
                !KoreAttribute::WITHOUT_KEY.contains(&attribute),
                "{attribute:?}"
            );
        }
    }
}
