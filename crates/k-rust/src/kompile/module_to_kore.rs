//! The declaration-producing prefix of Java's `ModuleToKORE`.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use petgraph::Direction::Incoming;
use petgraph::graph::{DiGraph, NodeIndex};
use serde_json::Value;

use crate::definition::{
    AssociativityRelations, Attributes as KAttributes, Definition as KDefinition,
    LOCATION_ATTRIBUTE, LabelHead, ModuleId, OverloadOrder, PartialOrder, ProductionCatalog,
    ProductionId, ProductionItem, RelationError, ResolveError, ResolvedDefinition,
    SOURCE_ATTRIBUTE, Sentence, SortCatalog, SortHead, match_rule_label,
};
use crate::kast::{Label, ResolvedProductionId, Sort, Term};
use crate::kore::ast::{
    Attributes, Module, Pattern, Sentence as KoreSentence, Sort as KoreSort, Symbol, Variable,
    VariableKind,
};

use super::sort_injections::{SortInjectionError, SortInjector};
use super::term_to_kore::{TermConversionError, TermConverter};

const PROGRAM_BUILTIN_MODULE: &str = "K";
const COLLECTION_HOOKS: [&str; 4] = ["SET.Set", "MAP.Map", "LIST.List", "RANGEMAP.RangeMap"];
const HOOK_NAMESPACES: [&str; 19] = [
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
const BUILTIN_LABELS: [&str; 14] = [
    "#Bottom",
    "#Top",
    "#Or",
    "#And",
    "#Not",
    "#Ceil",
    "#Floor",
    "#Equals",
    "#Implies",
    "#Exists",
    "#Forall",
    "#AG",
    "weakExistsFinally",
    "weakAlwaysFinally",
];

/// The declaration views and standalone macro axioms produced by `ModuleToKORE`.
///
/// `semantics` carries backend-facing symbol attributes. `syntax` carries the
/// same declarations plus concrete-syntax formatting metadata. `macros` is the
/// bare sentence list written to Java's `macros.kore`; it deliberately has no
/// enclosing KORE module.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeclarationModules {
    pub semantics: Module,
    pub syntax: Module,
    pub macros: Vec<KoreSentence>,
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
    InvalidCollectionSort { sort: String, message: String },
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
    },
    MissingEquationProduction {
        label: String,
    },
    AmbiguousEquationProduction {
        label: String,
        productions: usize,
    },
    InvalidEquationProduction {
        production: usize,
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
    UnsupportedRuleKind {
        kind: String,
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
            Self::ExpectedGeneratedTopCell { actual } => write!(
                formatter,
                "ordinary semantic rules must rewrite GeneratedTopCell, found {actual}"
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
            Self::UnsupportedRuleKind { kind } => {
                write!(formatter, "KORE emission for {kind} is not implemented yet")
            }
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
    let module_id = definition
        .module_id(module)
        .ok_or_else(|| DeclarationError::MissingModule(module.to_owned()))?;
    let visible = definition.sentences(module_id);
    let sorts = definition.sort_catalog(module_id);
    let productions = definition.production_catalog(module_id);
    let valued_attributes = valued_attributes(&visible);
    let impure_labels = transitive_impure_labels(definition, module_id, &productions);
    let overloads = definition
        .overloads(module_id)
        .map_err(DeclarationError::Relations)?;
    let overloaded_greater = overloads
        .order()
        .elements()
        .flat_map(|lesser| {
            overloads
                .order()
                .relations_from(lesser)
                .into_iter()
                .flatten()
                .copied()
        })
        .collect::<BTreeSet<_>>();
    let anywhere_labels = definition
        .rule_catalog(module_id)
        .rules()
        .filter(|(_, rule)| rule.attributes().get("anywhere").is_some())
        .map(|(_, rule)| match_rule_label(rule).name)
        .collect::<BTreeSet<_>>();
    let priorities = definition
        .priorities(module_id)
        .map_err(|cycle| DeclarationError::CircularPriority(cycle.path))?;
    let associativities = definition.associativities(module_id);
    let syntax_relations = SyntaxRelations::new(&priorities, &associativities);

    let mut common = vec![KoreSentence::Import {
        module: PROGRAM_BUILTIN_MODULE.into(),
        attributes: Attributes::default(),
    }];
    common.extend(sort_declarations(&sorts, &productions, &valued_attributes)?);

    let mut semantic_sentences = common.clone();
    let mut syntax_sentences = common;
    for (id, production) in productions.sorted_productions() {
        let Sentence::Production {
            label: Some(label),
            parameters,
            sort,
            items,
            attributes,
        } = production
        else {
            continue;
        };
        if is_builtin_label(&label.name) {
            continue;
        }
        let semantic_attributes = symbol_attributes(
            attributes,
            label,
            id,
            &productions,
            &valued_attributes,
            &overloaded_greater,
            &anywhere_labels,
            &impure_labels,
            false,
            items,
            &syntax_relations,
        );
        let syntax_attributes = symbol_attributes(
            attributes,
            label,
            id,
            &productions,
            &valued_attributes,
            &overloaded_greater,
            &anywhere_labels,
            &impure_labels,
            true,
            items,
            &syntax_relations,
        );
        let hooked = attributes.get("function").is_some() && is_real_hook(attributes);
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
        semantic_sentences.push(declaration(semantic_attributes));
        syntax_sentences.push(declaration(syntax_attributes));
    }

    let module_name = encode_kore_identifier(module);
    let module_attributes = emit_attributes(
        definition.module(module_id).attributes.entries(),
        &valued_attributes,
        &BTreeMap::new(),
    );
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
    })
}

/// Emit declarations plus the ordinary semantic rules and local claims of one module.
///
/// Reachability claims use Java's `weakExistsFinally` and `weakAlwaysFinally` wrappers. Macro and
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
    let mut modules = declaration_modules_from_resolved(definition, module)?;
    let module_id = definition
        .module_id(module)
        .ok_or_else(|| DeclarationError::MissingModule(module.to_owned()))?;
    let visible = definition.sentences(module_id);
    let valued = valued_attributes(&visible);
    let rules = definition.rule_catalog(module_id);
    let productions = definition.production_catalog(module_id);
    let sorts = definition.sort_catalog(module_id);
    let overloads = definition
        .overloads(module_id)
        .map_err(DeclarationError::Relations)?;
    let subsorts = definition
        .subsorts(module_id)
        .map_err(|error| DeclarationError::Relations(RelationError::CircularSubsort(error)))?;
    let injector = SortInjector::new(definition, module)?;
    let converter = TermConverter::new(definition, module)?;
    let default_reachability = reachability_mode(&definition.module(module_id).attributes);
    let sorted_rules = rules
        .sorted_rules()
        .map(|(_, rule)| propagate_macro_attribute(rule, &productions))
        .collect::<Vec<_>>();
    let constructors = constructor_productions(&productions, &overloads, &rules);

    let generated_axioms =
        generated_axioms(&productions, &sorts, &overloads, &subsorts, &constructors)?;
    modules
        .semantics
        .sentences
        .extend(generated_axioms.semantics);
    modules.syntax.sentences.extend(generated_axioms.syntax);

    for rule in &sorted_rules {
        let emitted = emit_rule_or_claim(
            rule,
            false,
            &valued,
            &productions,
            &injector,
            &converter,
            &sorted_rules,
            default_reachability,
        )?;
        if is_macro_rule(rule) {
            modules.macros.push(emitted);
        } else {
            modules.semantics.sentences.push(emitted);
        }
    }
    for (_, claim) in rules.local_claims() {
        if is_macro_rule(claim) {
            return Err(ModuleToKoreError::UnsupportedRuleKind {
                kind: "macro claim".into(),
            });
        }
        modules.semantics.sentences.push(emit_rule_or_claim(
            claim,
            true,
            &valued,
            &productions,
            &injector,
            &converter,
            &sorted_rules,
            default_reachability,
        )?);
    }
    Ok(modules)
}

struct GeneratedAxioms {
    semantics: Vec<KoreSentence>,
    syntax: Vec<KoreSentence>,
}

fn generated_axioms(
    productions: &ProductionCatalog<'_>,
    sorts: &SortCatalog<'_>,
    overloads: &OverloadOrder<'_>,
    subsorts: &PartialOrder<Sort>,
    constructors: &BTreeSet<ProductionId>,
) -> Result<GeneratedAxioms, ModuleToKoreError> {
    let mut semantics = Vec::new();
    let mut syntax = Vec::new();
    let mut no_confusion_pairs = BTreeSet::new();
    for (id, production) in productions.sorted_productions() {
        if let Some(axiom) = subsort_axiom(production) {
            semantics.push(axiom.clone());
            syntax.push(axiom);
            continue;
        }
        if is_builtin_production(production) {
            continue;
        }
        semantics.extend(algebraic_axioms(id, production, subsorts)?);
        if let Some(axiom) = functional_axiom(production) {
            semantics.push(axiom);
        }
        if constructors.contains(&id) {
            semantics.extend(no_confusion_axioms(
                id,
                productions,
                constructors,
                &mut no_confusion_pairs,
            ));
        }
    }
    semantics.extend(no_junk_axioms(productions, sorts, subsorts));

    for (lesser, _) in overloads.catalog().sorted_productions() {
        let Some(greater_productions) = overloads.order().relations_from(&lesser) else {
            continue;
        };
        for (greater, _) in overloads.catalog().sorted_productions() {
            if greater_productions.contains(&greater) {
                let axiom = overload_axiom(overloads, lesser, greater)?;
                semantics.push(axiom.clone());
                syntax.push(axiom);
            }
        }
    }
    Ok(GeneratedAxioms { semantics, syntax })
}

fn constructor_productions(
    productions: &ProductionCatalog<'_>,
    overloads: &OverloadOrder<'_>,
    rules: &crate::definition::RuleCatalog<'_>,
) -> BTreeSet<ProductionId> {
    let overloaded_greater = overloads
        .order()
        .elements()
        .flat_map(|lesser| {
            overloads
                .order()
                .relations_from(lesser)
                .into_iter()
                .flatten()
                .copied()
        })
        .collect::<BTreeSet<_>>();
    let anywhere_labels = rules
        .rules()
        .filter(|(_, rule)| rule.attributes().get("anywhere").is_some())
        .map(|(_, rule)| match_rule_label(rule))
        .collect::<BTreeSet<_>>();
    productions
        .sorted_productions()
        .filter_map(|(id, production)| {
            let Sentence::Production {
                label: Some(label),
                attributes,
                ..
            } = production
            else {
                return None;
            };
            let algebraic = ["assoc", "comm", "idem"]
                .iter()
                .any(|key| attributes.get(key).is_some());
            let is_macro = ["macro", "macro-rec", "alias", "alias-rec"]
                .iter()
                .any(|key| attributes.get(key).is_some());
            (attributes.get("function").is_none()
                && !algebraic
                && !is_macro
                && !overloaded_greater.contains(&id)
                && !anywhere_labels.contains(label)
                && !is_builtin_label(&label.name))
            .then_some(id)
        })
        .collect()
}

fn no_confusion_axioms(
    id: ProductionId,
    productions: &ProductionCatalog<'_>,
    constructors: &BTreeSet<ProductionId>,
    emitted_pairs: &mut BTreeSet<(ProductionId, ProductionId)>,
) -> Vec<KoreSentence> {
    let production = productions.production(id);
    let Some(current) = generated_production(production) else {
        return Vec::new();
    };
    let mut axioms = Vec::new();
    if !current.arguments.is_empty() {
        let left = generated_application(&current, "X");
        let right = generated_application(&current, "Y");
        let merged = Pattern::Application {
            symbol: current.symbol.clone(),
            arguments: current
                .arguments
                .iter()
                .enumerate()
                .map(|(index, sort)| Pattern::And {
                    sort: sort.clone(),
                    arguments: vec![
                        generated_variable("X", index, sort),
                        generated_variable("Y", index, sort),
                    ],
                })
                .collect(),
        };
        axioms.push(KoreSentence::Axiom {
            parameters: current.parameters.clone(),
            pattern: Box::new(Pattern::Implies {
                sort: current.result.clone(),
                left: Box::new(Pattern::And {
                    sort: current.result.clone(),
                    arguments: vec![left, right],
                }),
                right: Box::new(merged),
            }),
            attributes: marker_attribute("constructor"),
        });
    }

    let result_head = match production {
        Sentence::Production { sort, .. } => SortHead::from(sort),
        _ => unreachable!("production catalogs contain productions"),
    };
    for (other_id, other_production) in productions.sorted_productions() {
        if other_id == id
            || !constructors.contains(&other_id)
            || emitted_pairs.contains(&(id, other_id))
        {
            continue;
        }
        let Sentence::Production {
            sort: other_sort, ..
        } = other_production
        else {
            unreachable!("production catalogs contain productions")
        };
        if SortHead::from(other_sort) != result_head {
            continue;
        }
        let Some(other) = generated_production(other_production) else {
            continue;
        };
        emitted_pairs.insert((id, other_id));
        emitted_pairs.insert((other_id, id));
        axioms.push(KoreSentence::Axiom {
            parameters: current.parameters.clone(),
            pattern: Box::new(Pattern::Not {
                sort: current.result.clone(),
                argument: Box::new(Pattern::And {
                    sort: current.result.clone(),
                    arguments: vec![
                        generated_application(&current, "X"),
                        generated_application(&other, "Y"),
                    ],
                }),
            }),
            attributes: marker_attribute("constructor"),
        });
    }
    axioms
}

struct GeneratedProduction {
    parameters: Vec<String>,
    symbol: Symbol,
    arguments: Vec<KoreSort>,
    result: KoreSort,
}

fn generated_production(production: &Sentence) -> Option<GeneratedProduction> {
    let Sentence::Production {
        label: Some(label),
        parameters,
        sort,
        items,
        ..
    } = production
    else {
        return None;
    };
    Some(GeneratedProduction {
        parameters: generated_sort_parameters(parameters),
        symbol: encode_kore_label_with_formals(label, parameters),
        arguments: items
            .iter()
            .filter_map(|item| match item {
                ProductionItem::NonTerminal { sort, .. } => {
                    Some(encode_kore_sort_with_formals(sort, parameters))
                }
                ProductionItem::RegexTerminal { .. } | ProductionItem::Terminal(_) => None,
            })
            .collect(),
        result: encode_kore_sort_with_formals(sort, parameters),
    })
}

fn generated_application(production: &GeneratedProduction, prefix: &str) -> Pattern {
    Pattern::Application {
        symbol: production.symbol.clone(),
        arguments: production
            .arguments
            .iter()
            .enumerate()
            .map(|(index, sort)| generated_variable(prefix, index, sort))
            .collect(),
    }
}

fn generated_variable(prefix: &str, index: usize, sort: &KoreSort) -> Pattern {
    Pattern::Variable(Variable {
        kind: VariableKind::Element,
        name: format!("{prefix}{index}"),
        sort: sort.clone(),
    })
}

fn no_junk_axioms(
    productions: &ProductionCatalog<'_>,
    sorts: &SortCatalog<'_>,
    subsorts: &PartialOrder<Sort>,
) -> Vec<KoreSentence> {
    let mut axioms = Vec::new();
    for sort in sorts.sorted_all_sorts() {
        let result_sort = encode_kore_sort(sort);
        let result_head = SortHead::from(sort);
        let mut alternatives = Vec::new();
        let mut has_token = false;
        for (_, production) in productions.sorted_productions() {
            let Sentence::Production {
                label,
                sort: production_sort,
                attributes,
                ..
            } = production
            else {
                unreachable!("production catalogs contain productions")
            };
            if SortHead::from(production_sort) != result_head
                || attributes.get("function").is_some()
                || is_subsort_production(production)
                || is_builtin_production(production)
                || is_macro_production(production)
            {
                continue;
            }
            if attributes.get("token").is_some() && !has_token {
                alternatives.push(Pattern::Top {
                    sort: result_sort.clone(),
                });
                has_token = true;
            } else if label.is_some()
                && let Some(production) = generated_production_for_sort(production, sort)
            {
                let mut alternative = generated_application(&production, "X");
                for (index, argument_sort) in production.arguments.iter().enumerate().rev() {
                    alternative = Pattern::Exists {
                        sort: result_sort.clone(),
                        variable: Variable {
                            kind: VariableKind::Element,
                            name: format!("X{index}"),
                            sort: argument_sort.clone(),
                        },
                        body: Box::new(alternative),
                    };
                }
                alternatives.push(alternative);
            }
        }
        if sort.name != "K" {
            for subsort in sorts
                .sorted_all_sorts()
                .filter(|subsort| subsorts.less_than(subsort, sort))
            {
                let subsort = encode_kore_sort(subsort);
                let variable = Variable {
                    kind: VariableKind::Element,
                    name: "Val".into(),
                    sort: subsort.clone(),
                };
                alternatives.push(Pattern::Exists {
                    sort: result_sort.clone(),
                    variable: variable.clone(),
                    body: Box::new(Pattern::Application {
                        symbol: Symbol {
                            name: "inj".into(),
                            sort_parameters: vec![subsort, result_sort.clone()],
                        },
                        arguments: vec![Pattern::Variable(variable)],
                    }),
                });
            }
        }
        if !has_token
            && sorts
                .attributes_for(&result_head)
                .is_some_and(|attributes| attributes.get("token").is_some())
        {
            alternatives.push(Pattern::Top {
                sort: result_sort.clone(),
            });
        }
        if alternatives.is_empty() {
            continue;
        }
        let mut pattern = Pattern::Bottom {
            sort: result_sort.clone(),
        };
        for alternative in alternatives.into_iter().rev() {
            pattern = Pattern::Or {
                sort: result_sort.clone(),
                arguments: vec![alternative, pattern],
            };
        }
        axioms.push(KoreSentence::Axiom {
            parameters: Vec::new(),
            pattern: Box::new(pattern),
            attributes: marker_attribute("constructor"),
        });
    }
    axioms
}

fn generated_production_for_sort(
    production: &Sentence,
    target: &Sort,
) -> Option<GeneratedProduction> {
    let Sentence::Production {
        label: Some(label),
        parameters,
        sort,
        items,
        ..
    } = production
    else {
        return None;
    };
    let mut substitution = BTreeMap::new();
    match_sort_parameters(sort, target, parameters, &mut substitution)?;
    let concrete_label = Label::with_parameters(
        &label.name,
        label
            .parameters
            .iter()
            .map(|sort| substitute_equation_sort(sort, &substitution))
            .collect(),
    );
    Some(GeneratedProduction {
        parameters: Vec::new(),
        symbol: encode_kore_label(&concrete_label),
        arguments: items
            .iter()
            .filter_map(|item| match item {
                ProductionItem::NonTerminal { sort, .. } => Some(encode_kore_sort(
                    &substitute_equation_sort(sort, &substitution),
                )),
                ProductionItem::RegexTerminal { .. } | ProductionItem::Terminal(_) => None,
            })
            .collect(),
        result: encode_kore_sort(target),
    })
}

fn match_sort_parameters(
    pattern: &Sort,
    concrete: &Sort,
    parameters: &[Sort],
    substitution: &mut BTreeMap<Sort, Sort>,
) -> Option<()> {
    if parameters.contains(pattern) {
        return match substitution.get(pattern) {
            Some(existing) if existing != concrete => None,
            Some(_) => Some(()),
            None => {
                substitution.insert(pattern.clone(), concrete.clone());
                Some(())
            }
        };
    }
    if pattern.name != concrete.name || pattern.parameters.len() != concrete.parameters.len() {
        return None;
    }
    for (pattern, concrete) in pattern.parameters.iter().zip(&concrete.parameters) {
        match_sort_parameters(pattern, concrete, parameters, substitution)?;
    }
    Some(())
}

fn is_subsort_production(production: &Sentence) -> bool {
    matches!(
        production,
        Sentence::Production { label: None, items, .. }
            if matches!(items.as_slice(), [ProductionItem::NonTerminal { .. }])
    )
}

fn is_macro_production(production: &Sentence) -> bool {
    ["macro", "macro-rec", "alias", "alias-rec"]
        .iter()
        .any(|attribute| production.attributes().get(attribute).is_some())
}

fn functional_axiom(production: &Sentence) -> Option<KoreSentence> {
    let Sentence::Production {
        label: Some(label),
        parameters,
        sort,
        items,
        attributes,
    } = production
    else {
        return None;
    };
    if attributes.get("function").is_some() && attributes.get("total").is_none() {
        return None;
    }
    let result_sort = encode_kore_sort_with_formals(sort, parameters);
    let arguments = items
        .iter()
        .filter_map(|item| match item {
            ProductionItem::NonTerminal { sort, .. } => {
                Some(encode_kore_sort_with_formals(sort, parameters))
            }
            ProductionItem::RegexTerminal { .. } | ProductionItem::Terminal(_) => None,
        })
        .enumerate()
        .map(|(index, sort)| {
            Pattern::Variable(Variable {
                kind: VariableKind::Element,
                name: format!("K{index}"),
                sort,
            })
        })
        .collect();
    let value = Variable {
        kind: VariableKind::Element,
        name: "Val".into(),
        sort: result_sort.clone(),
    };
    Some(KoreSentence::Axiom {
        parameters: generated_axiom_parameters(parameters),
        pattern: Box::new(Pattern::Exists {
            sort: KoreSort::Variable("R".into()),
            variable: value.clone(),
            body: Box::new(Pattern::Equals {
                operand_sort: result_sort,
                result_sort: KoreSort::Variable("R".into()),
                left: Box::new(Pattern::Variable(value)),
                right: Box::new(Pattern::Application {
                    symbol: encode_kore_label_with_formals(label, parameters),
                    arguments,
                }),
            }),
        }),
        attributes: marker_attribute("functional"),
    })
}

fn is_builtin_production(production: &Sentence) -> bool {
    matches!(
        production,
        Sentence::Production { label: Some(label), .. } if is_builtin_label(&label.name)
    )
}

fn algebraic_axioms(
    id: ProductionId,
    production: &Sentence,
    subsorts: &PartialOrder<Sort>,
) -> Result<Vec<KoreSentence>, ModuleToKoreError> {
    let Sentence::Production {
        label,
        parameters,
        sort,
        items,
        attributes,
    } = production
    else {
        unreachable!("production catalogs contain productions")
    };
    let assoc = attributes.get("assoc").is_some();
    let idem = attributes.get("idem").is_some();
    let unit = attributes
        .get_str("unit")
        .filter(|_| attributes.get("function").is_some());
    if !assoc && !idem && unit.is_none() {
        return Ok(Vec::new());
    }
    let Some(label) = label else {
        return Err(invalid_algebraic(
            id,
            if assoc {
                "assoc"
            } else if idem {
                "idem"
            } else {
                "unit"
            },
            "the production has no symbol label",
        ));
    };
    let arguments = items
        .iter()
        .filter_map(|item| match item {
            ProductionItem::NonTerminal { sort, .. } => Some(sort),
            ProductionItem::RegexTerminal { .. } | ProductionItem::Terminal(_) => None,
        })
        .collect::<Vec<_>>();
    let symbol = encode_kore_label_with_formals(label, parameters);
    let result_sort = encode_kore_sort_with_formals(sort, parameters);
    let axiom_parameters = generated_axiom_parameters(parameters);
    let mut axioms = Vec::new();

    if assoc {
        if arguments.len() != 2 {
            return Err(invalid_algebraic(
                id,
                "assoc",
                format!("expected arity 2, found {}", arguments.len()),
            ));
        }
        if !arguments
            .iter()
            .all(|argument| subsorts.less_than_eq(sort, argument))
        {
            return Err(invalid_algebraic(
                id,
                "assoc",
                "the result sort must be a subsort of both argument sorts",
            ));
        }
        let variables = ["K1", "K2", "K3"].map(|name| Variable {
            kind: VariableKind::Element,
            name: name.into(),
            sort: result_sort.clone(),
        });
        let apply = |arguments| Pattern::Application {
            symbol: symbol.clone(),
            arguments,
        };
        axioms.push(KoreSentence::Axiom {
            parameters: axiom_parameters.clone(),
            pattern: Box::new(Pattern::Equals {
                operand_sort: result_sort.clone(),
                result_sort: KoreSort::Variable("R".into()),
                left: Box::new(apply(vec![
                    apply(vec![
                        Pattern::Variable(variables[0].clone()),
                        Pattern::Variable(variables[1].clone()),
                    ]),
                    Pattern::Variable(variables[2].clone()),
                ])),
                right: Box::new(apply(vec![
                    Pattern::Variable(variables[0].clone()),
                    apply(vec![
                        Pattern::Variable(variables[1].clone()),
                        Pattern::Variable(variables[2].clone()),
                    ]),
                ])),
            }),
            attributes: marker_attribute("assoc"),
        });
    }

    if idem {
        if arguments.len() != 2 {
            return Err(invalid_algebraic(
                id,
                "idem",
                format!("expected arity 2, found {}", arguments.len()),
            ));
        }
        if arguments.iter().any(|argument| *argument != sort) {
            return Err(invalid_algebraic(
                id,
                "idem",
                "the result and both argument sorts must be equal",
            ));
        }
        let variable = Variable {
            kind: VariableKind::Element,
            name: "K".into(),
            sort: result_sort.clone(),
        };
        axioms.push(KoreSentence::Axiom {
            parameters: axiom_parameters.clone(),
            pattern: Box::new(Pattern::Equals {
                operand_sort: result_sort.clone(),
                result_sort: KoreSort::Variable("R".into()),
                left: Box::new(Pattern::Application {
                    symbol: symbol.clone(),
                    arguments: vec![
                        Pattern::Variable(variable.clone()),
                        Pattern::Variable(variable.clone()),
                    ],
                }),
                right: Box::new(Pattern::Variable(variable)),
            }),
            attributes: marker_attribute("idem"),
        });
    }

    if let Some(unit) = unit {
        if arguments.len() != 2 {
            return Err(invalid_algebraic(
                id,
                "unit",
                format!("expected arity 2, found {}", arguments.len()),
            ));
        }
        if arguments.iter().any(|argument| *argument != sort) {
            return Err(invalid_algebraic(
                id,
                "unit",
                "the result and both argument sorts must be equal",
            ));
        }
        let variable = Variable {
            kind: VariableKind::Element,
            name: "K".into(),
            sort: result_sort.clone(),
        };
        let unit = Pattern::Application {
            symbol: encode_kore_label(&Label::new(unit)),
            arguments: Vec::new(),
        };
        for arguments in [
            vec![Pattern::Variable(variable.clone()), unit.clone()],
            vec![unit, Pattern::Variable(variable.clone())],
        ] {
            axioms.push(KoreSentence::Axiom {
                parameters: axiom_parameters.clone(),
                pattern: Box::new(Pattern::Equals {
                    operand_sort: result_sort.clone(),
                    result_sort: KoreSort::Variable("R".into()),
                    left: Box::new(Pattern::Application {
                        symbol: symbol.clone(),
                        arguments,
                    }),
                    right: Box::new(Pattern::Variable(variable.clone())),
                }),
                attributes: marker_attribute("unit"),
            });
        }
    }

    Ok(axioms)
}

fn invalid_algebraic(
    production: ProductionId,
    attribute: &'static str,
    message: impl Into<String>,
) -> ModuleToKoreError {
    ModuleToKoreError::InvalidAlgebraicProduction {
        production: production.0,
        attribute,
        message: message.into(),
    }
}

fn generated_axiom_parameters(parameters: &[Sort]) -> Vec<String> {
    let mut names = vec!["R".into()];
    names.extend(generated_sort_parameters(parameters));
    names
}

fn generated_sort_parameters(parameters: &[Sort]) -> Vec<String> {
    parameters
        .iter()
        .map(|parameter| {
            let KoreSort::Variable(name) = encode_kore_sort_with_formals(parameter, parameters)
            else {
                unreachable!("production parameters encode as KORE sort variables")
            };
            name
        })
        .collect()
}

fn marker_attribute(name: &str) -> Attributes {
    Attributes(vec![Pattern::Application {
        symbol: Symbol {
            name: name.into(),
            sort_parameters: Vec::new(),
        },
        arguments: Vec::new(),
    }])
}

fn subsort_axiom(production: &Sentence) -> Option<KoreSentence> {
    let Sentence::Production {
        label: None,
        parameters,
        sort,
        items,
        ..
    } = production
    else {
        return None;
    };
    let [ProductionItem::NonTerminal { sort: subsort, .. }] = items.as_slice() else {
        return None;
    };
    if sort.name == "K" {
        return None;
    }

    let subsort = encode_kore_sort_with_formals(subsort, parameters);
    let sort = encode_kore_sort_with_formals(sort, parameters);
    let value = Variable {
        kind: VariableKind::Element,
        name: "Val".into(),
        sort: sort.clone(),
    };
    let from = Variable {
        kind: VariableKind::Element,
        name: "From".into(),
        sort: subsort.clone(),
    };
    let injection = Pattern::Application {
        symbol: Symbol {
            name: "inj".into(),
            sort_parameters: vec![subsort.clone(), sort.clone()],
        },
        arguments: vec![Pattern::Variable(from)],
    };
    Some(KoreSentence::Axiom {
        parameters: vec!["R".into()],
        pattern: Box::new(Pattern::Exists {
            sort: KoreSort::Variable("R".into()),
            variable: value.clone(),
            body: Box::new(Pattern::Equals {
                operand_sort: sort.clone(),
                result_sort: KoreSort::Variable("R".into()),
                left: Box::new(Pattern::Variable(value)),
                right: Box::new(injection),
            }),
        }),
        attributes: Attributes(vec![Pattern::Application {
            symbol: Symbol {
                name: "subsort".into(),
                sort_parameters: vec![subsort, sort],
            },
            arguments: Vec::new(),
        }]),
    })
}

fn overload_axiom(
    overloads: &OverloadOrder<'_>,
    lesser_id: ProductionId,
    greater_id: ProductionId,
) -> Result<KoreSentence, ModuleToKoreError> {
    let lesser = overload_production(overloads, lesser_id)?;
    let greater = overload_production(overloads, greater_id)?;
    if lesser.arguments.len() != greater.arguments.len() {
        return Err(ModuleToKoreError::InvalidOverloadProduction {
            production: lesser_id.0,
            message: format!(
                "its arity {} does not match production #{} with arity {}",
                lesser.arguments.len(),
                greater_id.0,
                greater.arguments.len()
            ),
        });
    }

    let variables = lesser
        .arguments
        .iter()
        .enumerate()
        .map(|(index, sort)| Variable {
            kind: VariableKind::Element,
            name: format!("K{index}"),
            sort: sort.clone(),
        })
        .collect::<Vec<_>>();
    let greater_arguments = variables
        .iter()
        .zip(&lesser.arguments)
        .zip(&greater.arguments)
        .map(|((variable, lesser_sort), greater_sort)| {
            inject_if_needed(
                Pattern::Variable(variable.clone()),
                lesser_sort,
                greater_sort,
            )
        })
        .collect();
    let lesser_application = Pattern::Application {
        symbol: lesser.symbol.clone(),
        arguments: variables.into_iter().map(Pattern::Variable).collect(),
    };
    let right = inject_if_needed(lesser_application, &lesser.result, &greater.result);
    Ok(KoreSentence::Axiom {
        parameters: vec!["R".into()],
        pattern: Box::new(Pattern::Equals {
            operand_sort: greater.result,
            result_sort: KoreSort::Variable("R".into()),
            left: Box::new(Pattern::Application {
                symbol: greater.symbol.clone(),
                arguments: greater_arguments,
            }),
            right: Box::new(right),
        }),
        attributes: Attributes(vec![Pattern::Application {
            symbol: Symbol {
                name: "symbol-overload".into(),
                sort_parameters: Vec::new(),
            },
            arguments: vec![
                Pattern::Application {
                    symbol: greater.symbol,
                    arguments: Vec::new(),
                },
                Pattern::Application {
                    symbol: lesser.symbol,
                    arguments: Vec::new(),
                },
            ],
        }]),
    })
}

struct OverloadProduction {
    symbol: Symbol,
    arguments: Vec<KoreSort>,
    result: KoreSort,
}

fn overload_production(
    overloads: &OverloadOrder<'_>,
    id: ProductionId,
) -> Result<OverloadProduction, ModuleToKoreError> {
    let Sentence::Production {
        label,
        parameters,
        sort,
        items,
        ..
    } = overloads.production(id)
    else {
        unreachable!("overload catalogs contain productions")
    };
    let Some(label) = label else {
        return Err(ModuleToKoreError::InvalidOverloadProduction {
            production: id.0,
            message: "the production has no symbol label".into(),
        });
    };
    Ok(OverloadProduction {
        symbol: encode_kore_label_with_formals(label, parameters),
        arguments: items
            .iter()
            .filter_map(|item| match item {
                ProductionItem::NonTerminal { sort, .. } => {
                    Some(encode_kore_sort_with_formals(sort, parameters))
                }
                ProductionItem::RegexTerminal { .. } | ProductionItem::Terminal(_) => None,
            })
            .collect(),
        result: encode_kore_sort_with_formals(sort, parameters),
    })
}

fn inject_if_needed(pattern: Pattern, from: &KoreSort, to: &KoreSort) -> Pattern {
    if from == to {
        pattern
    } else {
        Pattern::Application {
            symbol: Symbol {
                name: "inj".into(),
                sort_parameters: vec![from.clone(), to.clone()],
            },
            arguments: vec![pattern],
        }
    }
}

fn reachability_mode(attributes: &KAttributes) -> Option<ReachabilityMode> {
    if attributes.get("one-path").is_some() {
        Some(ReachabilityMode::OnePath)
    } else if attributes.get("all-path").is_some() {
        Some(ReachabilityMode::AllPath)
    } else {
        None
    }
}

fn is_macro_rule(sentence: &Sentence) -> bool {
    ["macro", "macro-rec", "alias", "alias-rec"]
        .iter()
        .any(|attribute| sentence.attributes().get(attribute).is_some())
}

fn propagate_macro_attribute(sentence: &Sentence, productions: &ProductionCatalog<'_>) -> Sentence {
    if is_macro_rule(sentence) || sentence.attributes().get("simplification").is_some() {
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
    let Some(attribute) = ["macro", "macro-rec", "alias", "alias-rec"]
        .into_iter()
        .find(|attribute| production_attributes.get(attribute).is_some())
    else {
        return sentence.clone();
    };
    let mut attributes = attributes.clone();
    attributes.insert(attribute, Value::String(String::new()));
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
fn emit_rule_or_claim(
    sentence: &Sentence,
    claim: bool,
    valued: &BTreeSet<String>,
    productions: &ProductionCatalog<'_>,
    injector: &SortInjector<'_>,
    converter: &TermConverter<'_>,
    sorted_rules: &[Sentence],
    default_reachability: Option<ReachabilityMode>,
) -> Result<KoreSentence, ModuleToKoreError> {
    let injected = injector.inject_sentence(sentence)?;
    let (body, requires, ensures, attributes) = match &injected {
        Sentence::Rule {
            body,
            requires,
            ensures,
            attributes,
        }
        | Sentence::Claim {
            body,
            requires,
            ensures,
            attributes,
        } => (body, requires, ensures, attributes),
        _ => unreachable!("only rules and claims are emitted"),
    };
    let body_sort = injector.term_sort(body, None)?;
    let (left, right) = match body.unannotated() {
        Term::Rewrite { left, right } => (left.as_ref(), right.as_ref()),
        _ if claim => (body, body),
        _ => {
            return Err(ModuleToKoreError::ExpectedRewrite { sentence: "rule" });
        }
    };
    let existentials = existential_variables(right, ensures, converter)?;
    let equation = equation_info(left, attributes, productions)?;
    if equation.is_some() && !existentials.is_empty() {
        return Err(ModuleToKoreError::EquationExistentials {
            variables: existential_names(right, ensures),
        });
    }
    if let Some(equation) = equation {
        return emit_equation(
            equation,
            left,
            right,
            requires,
            ensures,
            attributes,
            claim,
            valued,
            converter,
            productions,
            injector,
            sorted_rules,
        );
    }
    if is_macro_rule(&injected) {
        if !existentials.is_empty() {
            return Err(ModuleToKoreError::EquationExistentials {
                variables: existential_names(right, ensures),
            });
        }
        return emit_macro_axiom(left, right, attributes, valued, injector, converter);
    }
    if !claim && body_sort != Sort::new("GeneratedTopCell") {
        return Err(ModuleToKoreError::ExpectedGeneratedTopCell { actual: body_sort });
    }
    let result_sort = encode_kore_sort(&body_sort);
    let left = converter.convert(left)?;
    let right = converter.convert(right)?;
    let requires = side_condition(requires, &result_sort, converter)?;
    let ensures = side_condition(ensures, &result_sort, converter)?;
    let mut right = Pattern::And {
        sort: result_sort.clone(),
        arguments: vec![right, ensures],
    };
    for variable in existentials.into_iter().rev() {
        right = Pattern::Exists {
            sort: result_sort.clone(),
            variable,
            body: Box::new(right),
        };
    }
    if let Some(mode) = reachability_mode(attributes).or(default_reachability) {
        right = Pattern::Application {
            symbol: Symbol {
                name: match mode {
                    ReachabilityMode::OnePath => "weakExistsFinally",
                    ReachabilityMode::AllPath => "weakAlwaysFinally",
                }
                .into(),
                sort_parameters: vec![result_sort.clone()],
            },
            arguments: vec![right],
        };
    }
    let pattern = if claim {
        Pattern::Implies {
            sort: result_sort.clone(),
            left: Box::new(Pattern::And {
                sort: result_sort,
                arguments: vec![requires, left],
            }),
            right: Box::new(right),
        }
    } else {
        Pattern::Rewrites {
            sort: result_sort.clone(),
            left: Box::new(Pattern::And {
                sort: result_sort,
                arguments: vec![left, requires],
            }),
            right: Box::new(right),
        }
    };
    let attributes = emit_attributes(attributes.entries(), valued, &BTreeMap::new());
    Ok(if claim {
        KoreSentence::Claim {
            parameters: Vec::new(),
            pattern: Box::new(pattern),
            attributes,
        }
    } else {
        KoreSentence::Axiom {
            parameters: Vec::new(),
            pattern: Box::new(pattern),
            attributes,
        }
    })
}

fn emit_macro_axiom(
    left: &Term,
    right: &Term,
    attributes: &KAttributes,
    valued: &BTreeSet<String>,
    injector: &SortInjector<'_>,
    converter: &TermConverter<'_>,
) -> Result<KoreSentence, ModuleToKoreError> {
    let parameters = equation_parameters(attributes);
    let converter = converter.with_sort_variables(parameters.iter().skip(1).cloned());
    let result_sort = converter.convert_sort(&injector.term_sort(left, None)?);
    let pattern = Pattern::Equals {
        operand_sort: result_sort,
        result_sort: KoreSort::Variable("R".into()),
        left: Box::new(converter.convert(left)?),
        right: Box::new(converter.convert(right)?),
    };
    let mut attributes = attributes.clone();
    let priority = attributes
        .get("priority")
        .map(|value| attribute_value_string("priority", value))
        .filter(|value| !value.is_empty())
        .unwrap_or_else(|| {
            if attributes.get("owise").is_some() {
                "200".into()
            } else {
                "50".into()
            }
        });
    attributes.insert("priority", Value::String(priority));
    equation_sentence(false, pattern, &attributes, valued, parameters)
}

#[derive(Clone, Debug)]
struct EquationInfo<'a> {
    label: &'a Label,
    children: &'a [Term],
    argument_sorts: Vec<Sort>,
    result_sort: Sort,
    direct: bool,
}

fn equation_info<'a>(
    left: &'a Term,
    attributes: &KAttributes,
    productions: &ProductionCatalog<'_>,
) -> Result<Option<EquationInfo<'a>>, ModuleToKoreError> {
    let application = peel_alias(left);
    let Term::Apply { label, arguments } = application.unannotated() else {
        return Ok(None);
    };
    let production = resolve_equation_production(application, label, productions)?;
    let Sentence::Production {
        parameters,
        sort,
        items,
        attributes: production_attributes,
        ..
    } = production
    else {
        unreachable!("production catalogs contain productions")
    };
    let simplification = attributes.get("simplification").is_some();
    let anywhere = attributes.get("anywhere").is_some();
    if production_attributes.get("function").is_none() && !simplification && !anywhere {
        return Ok(None);
    }
    let substitution = parameters
        .iter()
        .cloned()
        .zip(label.parameters.iter().cloned())
        .collect::<BTreeMap<_, _>>();
    let argument_sorts = items
        .iter()
        .filter_map(|item| match item {
            ProductionItem::NonTerminal { sort, .. } => {
                Some(substitute_equation_sort(sort, &substitution))
            }
            ProductionItem::RegexTerminal { .. } | ProductionItem::Terminal(_) => None,
        })
        .collect::<Vec<_>>();
    if argument_sorts.len() != arguments.len() {
        return Err(ModuleToKoreError::InvalidEquationProduction {
            production: application
                .metadata()
                .and_then(|metadata| metadata.production)
                .map_or(0, |id| id.0),
            message: format!(
                "expected {} arguments but the equation has {}",
                argument_sorts.len(),
                arguments.len()
            ),
        });
    }
    Ok(Some(EquationInfo {
        label,
        children: arguments,
        argument_sorts,
        result_sort: substitute_equation_sort(sort, &substitution),
        direct: simplification,
    }))
}

fn resolve_equation_production<'a>(
    application: &Term,
    label: &Label,
    productions: &ProductionCatalog<'a>,
) -> Result<&'a Sentence, ModuleToKoreError> {
    if let Some(ResolvedProductionId(index)) = application
        .metadata()
        .and_then(|metadata| metadata.production)
    {
        if index >= productions.len() {
            return Err(ModuleToKoreError::InvalidEquationProduction {
                production: index,
                message: "the resolved production is outside this module's catalog".into(),
            });
        }
        let production = productions.production(ProductionId(index));
        if !matches!(
            production,
            Sentence::Production { label: Some(candidate), .. } if candidate.name == label.name
        ) {
            return Err(ModuleToKoreError::InvalidEquationProduction {
                production: index,
                message: format!("its label does not match {:?}", label.name),
            });
        }
        return Ok(production);
    }
    let candidates = productions.productions_for(&LabelHead::from(label));
    match candidates {
        [] => Err(ModuleToKoreError::MissingEquationProduction {
            label: label.name.clone(),
        }),
        [id] => Ok(productions.production(*id)),
        candidates => Err(ModuleToKoreError::AmbiguousEquationProduction {
            label: label.name.clone(),
            productions: candidates.len(),
        }),
    }
}

#[allow(clippy::too_many_arguments)]
fn emit_equation(
    equation: EquationInfo<'_>,
    left: &Term,
    right: &Term,
    requires: &Term,
    ensures: &Term,
    attributes: &KAttributes,
    claim: bool,
    valued: &BTreeSet<String>,
    converter: &TermConverter<'_>,
    productions: &ProductionCatalog<'_>,
    injector: &SortInjector<'_>,
    sorted_rules: &[Sentence],
) -> Result<KoreSentence, ModuleToKoreError> {
    let parameters = equation_parameters(attributes);
    let converter = converter.with_sort_variables(parameters.iter().skip(1).cloned());
    let predicate_sort = KoreSort::Variable("R".into());
    let result_sort = converter.convert_sort(&equation.result_sort);
    let avoid_variables = variable_names([left, requires]);
    let requires = side_condition(requires, &predicate_sort, &converter)?;
    let ensures = side_condition(ensures, &result_sort, &converter)?;
    let right = Pattern::And {
        sort: result_sort.clone(),
        arguments: vec![converter.convert(right)?, ensures],
    };
    if attributes.get("owise").is_some() {
        if claim {
            return Err(ModuleToKoreError::UnsupportedRuleKind {
                kind: "owise claim".into(),
            });
        }
        return emit_owise_equation(
            equation,
            right,
            requires,
            attributes,
            valued,
            &converter,
            productions,
            injector,
            sorted_rules,
            parameters,
            &avoid_variables,
        );
    }
    let equals = if equation.direct || claim {
        Pattern::Equals {
            operand_sort: result_sort,
            result_sort: predicate_sort.clone(),
            left: Box::new(converter.convert(left)?),
            right: Box::new(right),
        }
    } else {
        let variables = equation
            .argument_sorts
            .iter()
            .enumerate()
            .map(|(index, sort)| Variable {
                kind: VariableKind::Element,
                name: format!("X{index}"),
                sort: converter.convert_sort(sort),
            })
            .collect::<Vec<_>>();
        let application = Pattern::Application {
            symbol: converter.convert_label(equation.label),
            arguments: variables.iter().cloned().map(Pattern::Variable).collect(),
        };
        let mut matches = Pattern::Top {
            sort: predicate_sort.clone(),
        };
        for ((variable, child), sort) in variables
            .iter()
            .zip(equation.children)
            .zip(&equation.argument_sorts)
            .rev()
        {
            matches = Pattern::And {
                sort: predicate_sort.clone(),
                arguments: vec![
                    Pattern::In {
                        operand_sort: converter.convert_sort(sort),
                        result_sort: predicate_sort.clone(),
                        left: Box::new(Pattern::Variable(variable.clone())),
                        right: Box::new(converter.convert(child)?),
                    },
                    matches,
                ],
            };
        }
        return equation_sentence(
            claim,
            Pattern::Implies {
                sort: predicate_sort.clone(),
                left: Box::new(Pattern::And {
                    sort: predicate_sort.clone(),
                    arguments: vec![requires, matches],
                }),
                right: Box::new(Pattern::Equals {
                    operand_sort: result_sort,
                    result_sort: predicate_sort,
                    left: Box::new(application),
                    right: Box::new(right),
                }),
            },
            attributes,
            valued,
            parameters,
        );
    };
    equation_sentence(
        claim,
        Pattern::Implies {
            sort: predicate_sort,
            left: Box::new(requires),
            right: Box::new(equals),
        },
        attributes,
        valued,
        parameters,
    )
}

#[allow(clippy::too_many_arguments)]
fn emit_owise_equation(
    equation: EquationInfo<'_>,
    right: Pattern,
    requires: Pattern,
    attributes: &KAttributes,
    valued: &BTreeSet<String>,
    converter: &TermConverter<'_>,
    productions: &ProductionCatalog<'_>,
    injector: &SortInjector<'_>,
    sorted_rules: &[Sentence],
    parameters: Vec<String>,
    avoid_variables: &BTreeSet<String>,
) -> Result<KoreSentence, ModuleToKoreError> {
    let predicate_sort = KoreSort::Variable("R".into());
    let result_sort = converter.convert_sort(&equation.result_sort);
    let variables = equation_variables(&equation, converter);
    let own_matches = equation_matches(
        &variables,
        equation.children,
        &equation.argument_sorts,
        &predicate_sort,
        converter,
    )?;

    let mut counter = 0;
    let mut competitors = Vec::new();
    for sentence in sorted_rules {
        let injected = injector.inject_sentence(sentence)?;
        let Sentence::Rule {
            body,
            requires: competitor_requires,
            ensures: competitor_ensures,
            ..
        } = &injected
        else {
            continue;
        };
        let competitor_left = match body.unannotated() {
            Term::Rewrite { left, .. } => left.as_ref(),
            _ => body,
        };
        let Some(competitor) = equation_info(competitor_left, sentence.attributes(), productions)?
        else {
            continue;
        };
        if competitor.label != equation.label
            || competitor.argument_sorts != equation.argument_sorts
        {
            continue;
        }

        let mut renames = BTreeMap::new();
        // Java refreshes the complete rule before filtering ignored competitors, so unused
        // RHS and condition variables still consume names from the shared `_GenN` counter.
        let refreshed_body = refresh_variables(body, avoid_variables, &mut counter, &mut renames);
        let refreshed_requires = refresh_variables(
            competitor_requires,
            avoid_variables,
            &mut counter,
            &mut renames,
        );
        let _refreshed_ensures = refresh_variables(
            competitor_ensures,
            avoid_variables,
            &mut counter,
            &mut renames,
        );
        if ignore_owise_competitor(sentence) {
            continue;
        }
        let refreshed_left = match refreshed_body.unannotated() {
            Term::Rewrite { left, .. } => left.as_ref(),
            _ => &refreshed_body,
        };
        let Term::Apply {
            arguments: competitor_children,
            ..
        } = peel_alias(refreshed_left).unannotated()
        else {
            return Err(ModuleToKoreError::UnsupportedRuleKind {
                kind: "non-application function competitor for owise".into(),
            });
        };
        let condition = side_condition(&refreshed_requires, &predicate_sort, converter)?;
        let matches = equation_matches(
            &variables,
            competitor_children,
            &equation.argument_sorts,
            &predicate_sort,
            converter,
        )?;
        let mut candidate = Pattern::And {
            sort: predicate_sort.clone(),
            arguments: vec![condition, matches],
        };
        let quantified = variable_terms([refreshed_left, &refreshed_requires]);
        for term in quantified.into_values().rev() {
            let Pattern::Variable(variable) = converter.convert(&term)? else {
                unreachable!("collected terms are variables")
            };
            candidate = Pattern::Exists {
                sort: predicate_sort.clone(),
                variable,
                body: Box::new(candidate),
            };
        }
        competitors.push(candidate);
    }

    let mut any_competitor = Pattern::Bottom {
        sort: predicate_sort.clone(),
    };
    for competitor in competitors.into_iter().rev() {
        any_competitor = Pattern::Or {
            sort: predicate_sort.clone(),
            arguments: vec![competitor, any_competitor],
        };
    }
    let negative_match = Pattern::Not {
        sort: predicate_sort.clone(),
        argument: Box::new(any_competitor),
    };
    let application = Pattern::Application {
        symbol: converter.convert_label(equation.label),
        arguments: variables.iter().cloned().map(Pattern::Variable).collect(),
    };
    equation_sentence(
        false,
        Pattern::Implies {
            sort: predicate_sort.clone(),
            left: Box::new(Pattern::And {
                sort: predicate_sort.clone(),
                arguments: vec![
                    negative_match,
                    Pattern::And {
                        sort: predicate_sort.clone(),
                        arguments: vec![requires, own_matches],
                    },
                ],
            }),
            right: Box::new(Pattern::Equals {
                operand_sort: result_sort,
                result_sort: predicate_sort,
                left: Box::new(application),
                right: Box::new(right),
            }),
        },
        attributes,
        valued,
        parameters,
    )
}

fn ignore_owise_competitor(sentence: &Sentence) -> bool {
    ["owise", "simplification", "non-executable"]
        .into_iter()
        .any(|attribute| sentence.attributes().get(attribute).is_some())
}

fn equation_variables(equation: &EquationInfo<'_>, converter: &TermConverter<'_>) -> Vec<Variable> {
    equation
        .argument_sorts
        .iter()
        .enumerate()
        .map(|(index, sort)| Variable {
            kind: VariableKind::Element,
            name: format!("X{index}"),
            sort: converter.convert_sort(sort),
        })
        .collect()
}

fn equation_matches(
    variables: &[Variable],
    children: &[Term],
    sorts: &[Sort],
    predicate_sort: &KoreSort,
    converter: &TermConverter<'_>,
) -> Result<Pattern, TermConversionError> {
    let mut matches = Pattern::Top {
        sort: predicate_sort.clone(),
    };
    for ((variable, child), sort) in variables.iter().zip(children).zip(sorts).rev() {
        matches = Pattern::And {
            sort: predicate_sort.clone(),
            arguments: vec![
                Pattern::In {
                    operand_sort: converter.convert_sort(sort),
                    result_sort: predicate_sort.clone(),
                    left: Box::new(Pattern::Variable(variable.clone())),
                    right: Box::new(converter.convert(child)?),
                },
                matches,
            ],
        };
    }
    Ok(matches)
}

fn variable_names<'a>(roots: impl IntoIterator<Item = &'a Term>) -> BTreeSet<String> {
    variable_terms(roots).into_keys().collect()
}

fn variable_terms<'a>(roots: impl IntoIterator<Item = &'a Term>) -> BTreeMap<String, Term> {
    let mut variables = BTreeMap::new();
    for root in roots {
        root.visit_preorder(&mut |term| {
            if let Term::Variable { name, .. } = term.unannotated() {
                variables
                    .entry(name.clone())
                    .or_insert_with(|| term.clone());
            }
        });
    }
    variables
}

fn refresh_variables(
    term: &Term,
    avoid: &BTreeSet<String>,
    counter: &mut usize,
    renames: &mut BTreeMap<String, String>,
) -> Term {
    let refreshed = match term.unannotated() {
        Term::Variable { name, sort } => {
            let name = renames.entry(name.clone()).or_insert_with(|| {
                loop {
                    let candidate = format!("_Gen{counter}");
                    *counter += 1;
                    if !avoid.contains(&candidate) {
                        break candidate;
                    }
                }
            });
            Term::Variable {
                name: name.clone(),
                sort: sort.clone(),
            }
        }
        Term::Rewrite { left, right } => Term::Rewrite {
            left: Box::new(refresh_variables(left, avoid, counter, renames)),
            right: Box::new(refresh_variables(right, avoid, counter, renames)),
        },
        Term::As { pattern, alias } => Term::As {
            pattern: Box::new(refresh_variables(pattern, avoid, counter, renames)),
            alias: Box::new(refresh_variables(alias, avoid, counter, renames)),
        },
        Term::Sequence(items) => Term::Sequence(
            items
                .iter()
                .map(|item| refresh_variables(item, avoid, counter, renames))
                .collect(),
        ),
        Term::Apply { label, arguments } => Term::Apply {
            label: label.clone(),
            arguments: arguments
                .iter()
                .map(|argument| refresh_variables(argument, avoid, counter, renames))
                .collect(),
        },
        Term::InjectedLabel(label) => Term::InjectedLabel(label.clone()),
        Term::Token { token, sort } => Term::Token {
            token: token.clone(),
            sort: sort.clone(),
        },
        Term::Annotated { .. } => unreachable!(),
    };
    refreshed.with_metadata(term.metadata().cloned().unwrap_or_default())
}

fn equation_sentence(
    claim: bool,
    pattern: Pattern,
    attributes: &KAttributes,
    valued: &BTreeSet<String>,
    parameters: Vec<String>,
) -> Result<KoreSentence, ModuleToKoreError> {
    let attributes = emit_attributes(attributes.entries(), valued, &BTreeMap::new());
    Ok(if claim {
        KoreSentence::Claim {
            parameters,
            pattern: Box::new(pattern),
            attributes,
        }
    } else {
        KoreSentence::Axiom {
            parameters,
            pattern: Box::new(pattern),
            attributes,
        }
    })
}

fn equation_parameters(attributes: &KAttributes) -> Vec<String> {
    let mut parameters = vec!["R".into()];
    let Some(sort_parameters) = attributes
        .get("sortParams")
        .and_then(Value::as_object)
        .and_then(|sort| sort.get("params"))
        .and_then(Value::as_array)
    else {
        return parameters;
    };
    parameters.extend(sort_parameters.iter().filter_map(|sort| {
        sort.as_object()
            .and_then(|sort| sort.get("name"))
            .and_then(Value::as_str)
            .map(str::to_owned)
    }));
    parameters
}

fn substitute_equation_sort(sort: &Sort, substitution: &BTreeMap<Sort, Sort>) -> Sort {
    substitution.get(sort).cloned().unwrap_or_else(|| {
        Sort::with_parameters(
            &sort.name,
            sort.parameters
                .iter()
                .map(|parameter| substitute_equation_sort(parameter, substitution))
                .collect(),
        )
    })
}

fn side_condition(
    condition: &Term,
    result_sort: &KoreSort,
    converter: &TermConverter<'_>,
) -> Result<Pattern, TermConversionError> {
    if is_true(condition) {
        return Ok(Pattern::Top {
            sort: result_sort.clone(),
        });
    }
    let bool_sort = encode_kore_sort(&Sort::new("Bool"));
    Ok(Pattern::Equals {
        operand_sort: bool_sort.clone(),
        result_sort: result_sort.clone(),
        left: Box::new(converter.convert(condition)?),
        right: Box::new(Pattern::DomainValue {
            sort: bool_sort,
            value: "true".into(),
        }),
    })
}

fn is_true(term: &Term) -> bool {
    matches!(
        term.unannotated(),
        Term::Token { token, sort } if token == "true" && sort == &Sort::new("Bool")
    )
}

fn existential_variables(
    right: &Term,
    ensures: &Term,
    converter: &TermConverter<'_>,
) -> Result<Vec<Variable>, TermConversionError> {
    let mut terms = BTreeMap::<String, Term>::new();
    for root in [right, ensures] {
        root.visit_preorder(&mut |term| {
            if let Term::Variable { name, .. } = term.unannotated()
                && name.starts_with('?')
            {
                terms.entry(name.clone()).or_insert_with(|| term.clone());
            }
        });
    }
    terms
        .into_values()
        .map(|term| match converter.convert(&term)? {
            Pattern::Variable(variable) => Ok(variable),
            _ => unreachable!("collected terms are variables"),
        })
        .collect()
}

fn existential_names(right: &Term, ensures: &Term) -> Vec<String> {
    let mut names = BTreeSet::new();
    for root in [right, ensures] {
        root.visit_preorder(&mut |term| {
            if let Term::Variable { name, .. } = term.unannotated()
                && name.starts_with('?')
            {
                names.insert(name.clone());
            }
        });
    }
    names.into_iter().collect()
}

fn transitive_impure_labels(
    definition: &ResolvedDefinition,
    module: ModuleId,
    productions: &ProductionCatalog<'_>,
) -> BTreeSet<String> {
    let rules = definition.rule_catalog(module);
    let function_labels = productions.function_labels();
    let anywhere_labels = rules
        .rules()
        .filter(|(_, rule)| !is_macro_rule(rule))
        .filter(|(_, rule)| rule.attributes().get("anywhere").is_some())
        .filter_map(|(_, rule)| anywhere_lhs_label(rule))
        .collect::<BTreeSet<_>>();

    let mut graph = DiGraph::<LabelHead, ()>::new();
    let mut nodes = BTreeMap::<LabelHead, NodeIndex>::new();
    let node = |label: LabelHead,
                graph: &mut DiGraph<LabelHead, ()>,
                nodes: &mut BTreeMap<LabelHead, NodeIndex>| {
        *nodes
            .entry(label.clone())
            .or_insert_with(|| graph.add_node(label))
    };

    for (_, rule) in rules.rules() {
        let current = LabelHead::from(&match_rule_label(rule));
        if !function_labels.contains(&current) {
            continue;
        }
        let current_node = node(current, &mut graph, &mut nodes);
        let Sentence::Rule { body, requires, .. } = rule else {
            unreachable!("rule catalogs contain rules")
        };
        for root in [body, requires] {
            root.visit_preorder(&mut |term| {
                let Term::Apply { label, .. } = term.unannotated() else {
                    return;
                };
                if label.name == "inj" {
                    return;
                }
                let dependency = LabelHead::from(label);
                if function_labels.contains(&dependency) || anywhere_labels.contains(&dependency) {
                    let dependency_node = node(dependency, &mut graph, &mut nodes);
                    graph.add_edge(current_node, dependency_node, ());
                }
            });
        }
    }

    let mut impure = productions
        .sorted_productions()
        .filter_map(|(_, production)| match production {
            Sentence::Production {
                label: Some(label),
                attributes,
                ..
            } if attributes.get("impure").is_some() => Some(LabelHead::from(label)),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let mut pending = impure.iter().cloned().collect::<Vec<_>>();
    while let Some(label) = pending.pop() {
        let label_node = node(label, &mut graph, &mut nodes);
        for predecessor in graph.neighbors_directed(label_node, Incoming) {
            let predecessor = graph[predecessor].clone();
            if impure.insert(predecessor.clone()) {
                pending.push(predecessor);
            }
        }
    }
    impure
        .into_iter()
        .map(|label| label.as_str().to_owned())
        .collect()
}

fn anywhere_lhs_label(rule: &Sentence) -> Option<LabelHead> {
    let Sentence::Rule { body, .. } = rule else {
        return None;
    };
    let left = match body.unannotated() {
        Term::Rewrite { left, .. } => left.as_ref(),
        _ => body,
    };
    let Term::Apply { label, arguments } = left.unannotated() else {
        return None;
    };
    if label.name != "inj" {
        return Some(LabelHead::from(label));
    }
    let Term::Apply { label, .. } = arguments.first()?.unannotated() else {
        return None;
    };
    Some(LabelHead::from(label))
}

fn sort_declarations(
    sorts: &SortCatalog<'_>,
    productions: &ProductionCatalog<'_>,
    valued: &BTreeSet<String>,
) -> Result<Vec<KoreSentence>, DeclarationError> {
    let token_heads = sorts
        .token_sorts()
        .iter()
        .map(SortHead::from)
        .collect::<BTreeSet<_>>();
    let mut declarations = Vec::new();
    for head in sorts.sorted_defined_heads() {
        if matches!(head.as_str(), "K" | "KItem") {
            continue;
        }
        let source_attributes = sorts.attributes_for(head).cloned().unwrap_or_default();
        let mut entries = source_attributes.entries().clone();
        entries.remove("hasDomainValues");
        if token_heads.contains(head) {
            entries.insert("hasDomainValues".into(), Value::String(String::new()));
        }
        if head.parameters() == 0 && head.as_str().parse::<i32>().is_ok() {
            entries.insert("nat".into(), Value::String(head.as_str().into()));
        }
        let mut overrides = BTreeMap::new();
        if source_attributes
            .get_str("hook")
            .is_some_and(|hook| COLLECTION_HOOKS.contains(&hook))
        {
            collection_attribute_overrides(head, productions, &mut overrides)?;
        }
        declarations.push(KoreSentence::SortDeclaration {
            hooked: source_attributes.get("hook").is_some(),
            name: format!("Sort{}", encode_kore_identifier(head.as_str())),
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
        .sorted_productions()
        .map(|(_, production)| production)
        .find(|production| {
            matches!(
                production,
                Sentence::Production { sort, attributes, .. }
                    if SortHead::from(sort) == *head && attributes.get_str("element").is_some()
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
        ("element", attributes.get_str("element")),
        ("concat", Some(label.name.as_str())),
        ("unit", attributes.get_str("unit")),
        ("update", attributes.get_str("update")),
    ] {
        if let Some(label_name) = label_name {
            overrides.insert(key.into(), vec![label_pattern(label_name, productions)]);
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn symbol_attributes(
    source: &KAttributes,
    label: &Label,
    id: crate::definition::ProductionId,
    productions: &ProductionCatalog<'_>,
    valued: &BTreeSet<String>,
    overloaded_greater: &BTreeSet<crate::definition::ProductionId>,
    anywhere_labels: &BTreeSet<String>,
    impure_labels: &BTreeSet<String>,
    with_syntax: bool,
    items: &[ProductionItem],
    syntax_relations: &SyntaxRelations,
) -> Attributes {
    let mut entries = source.entries().clone();
    for key in [
        "constructor",
        "hook",
        "assoc",
        "bracket",
        "colors",
        "comm",
        "format",
        "left",
        "right",
    ] {
        entries.remove(key);
    }

    let function = source.get("function").is_some();
    let base_constructor = !function
        && source.get("assoc").is_none()
        && source.get("comm").is_none()
        && source.get("idem").is_none();
    let injective = base_constructor;
    let macro_like = ["macro", "macro-rec", "alias", "alias-rec"]
        .iter()
        .any(|key| source.get(key).is_some());
    let anywhere = overloaded_greater.contains(&id) || anywhere_labels.contains(&label.name);
    if is_real_hook(source)
        && let Some(hook) = source.get("hook")
    {
        entries.insert("hook".into(), hook.clone());
    }
    if base_constructor && !macro_like && !anywhere {
        entries.insert("constructor".into(), Value::String(String::new()));
    }
    if !function || source.get("total").is_some() {
        entries.insert("functional".into(), Value::String(String::new()));
    }
    if anywhere {
        entries.insert("anywhere".into(), Value::String(String::new()));
    }
    if impure_labels.contains(&label.name) {
        entries.insert("impure".into(), Value::String(String::new()));
    }
    if injective {
        entries.insert("injective".into(), Value::String(String::new()));
    }
    if macro_like {
        entries.insert("macro".into(), Value::String(String::new()));
    }

    let mut overrides = BTreeMap::new();
    for key in ["unit", "element", "update"] {
        if let Some(label) = entries.get(key).and_then(Value::as_str) {
            overrides.insert(key.into(), vec![label_pattern(label, productions)]);
        }
    }
    if with_syntax {
        add_syntax_attributes(
            source,
            label,
            items,
            syntax_relations,
            &mut entries,
            &mut overrides,
        );
    }
    emit_attributes(&entries, valued, &overrides)
}

fn add_syntax_attributes(
    source: &KAttributes,
    label: &Label,
    items: &[ProductionItem],
    syntax_relations: &SyntaxRelations,
    entries: &mut BTreeMap<String, Value>,
    overrides: &mut BTreeMap<String, Vec<Pattern>>,
) {
    let Some(mut format) = source
        .get_str("format")
        .map(str::to_owned)
        .or_else(|| default_format(items))
    else {
        return;
    };
    let mut nonterminal = 1;
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
    entries.insert("format".into(), Value::String(format.clone()));
    for key in ["assoc", "bracket", "colors", "comm"] {
        if let Some(value) = source.get(key) {
            entries.insert(key.into(), value.clone());
        }
    }
    if let Some(color) = source.get_str("color") {
        let colors = format
            .match_indices("%c")
            .map(|_| color)
            .collect::<Vec<_>>();
        entries.insert("colors".into(), Value::String(colors.join(",")));
    }
    entries.insert(
        "terminals".into(),
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
    entries.insert("priorities".into(), Value::String(String::new()));
    entries.insert("left".into(), Value::String(String::new()));
    entries.insert("right".into(), Value::String(String::new()));
    overrides.insert(
        "priorities".into(),
        syntax_relations
            .priorities
            .get(&label.name)
            .cloned()
            .unwrap_or_default(),
    );
    overrides.insert(
        "left".into(),
        syntax_relations
            .left
            .get(&label.name)
            .cloned()
            .unwrap_or_default(),
    );
    overrides.insert(
        "right".into(),
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
    let mut valued = ["nat", "terminals", "colors", "priority"]
        .into_iter()
        .map(str::to_owned)
        .collect::<BTreeSet<_>>();
    for attributes in sentences.iter().map(|sentence| sentence.attributes()) {
        for (key, value) in attributes.entries() {
            if !attribute_value_string(key, value).is_empty() {
                valued.insert(key.clone());
            }
        }
    }
    if valued.contains("token") {
        valued.remove("hasDomainValues");
    }
    // Java uses this typed attribute to declare axiom sort variables, but emits the
    // attribute marker itself without serializing its internal `KSort` value.
    valued.remove("sortParams");
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
        .filter(|key| should_emit(key))
        .map(|key| {
            let arguments = overrides.get(&key).cloned().unwrap_or_else(|| {
                if valued.contains(&key) {
                    vec![Pattern::String(
                        entries
                            .get(&key)
                            .map(|value| attribute_value_string(&key, value))
                            .unwrap_or_default(),
                    )]
                } else {
                    Vec::new()
                }
            });
            Pattern::Application {
                symbol: Symbol {
                    name: encode_kore_identifier(&key),
                    sort_parameters: Vec::new(),
                },
                arguments,
            }
        })
        .collect();
    Attributes(patterns)
}

fn attribute_value_string(key: &str, value: &Value) -> String {
    if key == LOCATION_ATTRIBUTE
        && let Some(values) = value.as_array()
        && let [start_line, start_column, end_line, end_column] = values.as_slice()
    {
        return format!("Location({start_line},{start_column},{end_line},{end_column})");
    }
    match value {
        Value::String(value) => value.clone(),
        Value::Null => "null".into(),
        Value::Bool(value) => value.to_string(),
        Value::Number(value) => value.to_string(),
        Value::Array(_) | Value::Object(_) => value.to_string(),
    }
}

fn label_pattern(label: &str, productions: &ProductionCatalog<'_>) -> Pattern {
    let head = LabelHead::new(label);
    let parameters = productions
        .productions_for(&head)
        .first()
        .and_then(|id| match productions.production(*id) {
            Sentence::Production { label, .. } => label.as_ref(),
            _ => None,
        })
        .map(|label| label.parameters.clone())
        .unwrap_or_default();
    Pattern::Application {
        symbol: encode_kore_label(&Label::with_parameters(label, parameters)),
        arguments: Vec::new(),
    }
}

fn should_emit(key: &str) -> bool {
    matches!(
        key,
        "alias"
            | "alias-rec"
            | "all-path"
            | "anywhere"
            | "assoc"
            | "binder"
            | "bracket"
            | "cell"
            | "circularity"
            | "colors"
            | "comm"
            | "concrete"
            | "constructor"
            | "cool"
            | "depends"
            | "deprecated"
            | "element"
            | "format"
            | "freshGenerator"
            | "function"
            | "functional"
            | "hook"
            | "idem"
            | "impure"
            | "injective"
            | "klabel"
            | "label"
            | "macro"
            | "macro-rec"
            | "memo"
            | "non-executable"
            | "no-evaluators"
            | "one-path"
            | "owise"
            | "preserves-definedness"
            | "priority"
            | "simplification"
            | "smtlib"
            | "smt-hook"
            | "smt-lemma"
            | "symbol"
            | "symbolic"
            | "syntactic"
            | "token"
            | "total"
            | "trusted"
            | "unit"
            | "update"
            | "concat"
            | "cool-like"
            | "hasDomainValues"
            | "left"
            | "nat"
            | "priorities"
            | "right"
            | "symbol-overload"
            | "sortParams"
            | "terminals"
            | "UNIQUE_ID"
            | LOCATION_ATTRIBUTE
            | SOURCE_ATTRIBUTE
    )
}

fn is_real_hook(attributes: &KAttributes) -> bool {
    attributes.get_str("hook").is_some_and(|hook| {
        hook.split_once('.')
            .is_some_and(|(namespace, _)| HOOK_NAMESPACES.contains(&namespace))
    })
}

fn is_builtin_label(label: &str) -> bool {
    BUILTIN_LABELS.contains(&label)
}

/// Encode a K name with Java `ModuleToKORE`'s KORE identifier encoding.
pub fn encode_kore_identifier(name: &str) -> String {
    if matches!(
        name,
        "module"
            | "endmodule"
            | "sort"
            | "hooked-sort"
            | "symbol"
            | "hooked-symbol"
            | "alias"
            | "axiom"
    ) {
        return format!("{name}'Kywd'");
    }
    let mut encoded = String::new();
    let mut in_identifier = true;
    for unit in name.encode_utf16() {
        if is_identifier_unit(unit) {
            if !in_identifier {
                encoded.push('\'');
                in_identifier = true;
            }
            encoded.push(char::from_u32(u32::from(unit)).expect("ASCII identifier unit"));
        } else {
            if in_identifier {
                encoded.push('\'');
                in_identifier = false;
            }
            if let Some(mnemonic) = mnemonic(unit) {
                encoded.push_str(mnemonic);
            } else {
                use std::fmt::Write;
                write!(encoded, "{unit:04x}").expect("writing to a string cannot fail");
            }
        }
    }
    if !in_identifier {
        encoded.push('\'');
    }
    encoded
}

/// Encode a K label as a KORE symbol head.
pub fn encode_kore_label(label: &Label) -> Symbol {
    encode_kore_label_with_formals(label, &[])
}

fn encode_kore_label_with_formals(label: &Label, formals: &[Sort]) -> Symbol {
    Symbol {
        name: if label.name == "inj" {
            label.name.clone()
        } else {
            format!("Lbl{}", encode_kore_identifier(&label.name))
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

fn encode_kore_sort_with_formals(sort: &Sort, formals: &[Sort]) -> KoreSort {
    let name = format!("Sort{}", encode_kore_identifier(&sort.name));
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

fn is_identifier_unit(unit: u16) -> bool {
    (unit <= u16::from(u8::MAX) && char::from(unit as u8).is_ascii_alphanumeric())
        || unit == u16::from(b'-')
}

fn mnemonic(unit: u16) -> Option<&'static str> {
    Some(match unit {
        0x20 => "Spce",
        0x21 => "Bang",
        0x22 => "Quot",
        0x23 => "Hash",
        0x24 => "Dolr",
        0x25 => "Perc",
        0x26 => "And-",
        0x27 => "Apos",
        0x28 => "LPar",
        0x29 => "RPar",
        0x2a => "Star",
        0x2b => "Plus",
        0x2c => "Comm",
        0x2d => "-",
        0x2e => "Stop",
        0x2f => "Slsh",
        0x3a => "Coln",
        0x3b => "SCln",
        0x3c => "-LT-",
        0x3d => "Eqls",
        0x3e => "-GT-",
        0x3f => "Ques",
        0x40 => "-AT-",
        0x5b => "LSqB",
        0x5c => "Bash",
        0x5d => "RSqB",
        0x5e => "Xor-",
        0x5f => "Unds",
        0x60 => "BQuo",
        0x7b => "LBra",
        0x7c => "Pipe",
        0x7d => "RBra",
        0x7e => "Tild",
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    #[test]
    fn equation_sort_parameters_are_declared_but_not_serialized_as_attribute_values() {
        let mut entries = BTreeMap::new();
        entries.insert(
            "sortParams".into(),
            json!({
                "node": "KSort",
                "name": "#SortParam",
                "params": [
                    { "node": "KSort", "name": "Q0", "params": [] },
                    { "node": "KSort", "name": "Q1", "params": [] }
                ]
            }),
        );
        let attributes = KAttributes::new(entries);
        assert_eq!(equation_parameters(&attributes), ["R", "Q0", "Q1"]);

        let truth = Term::Token {
            token: "true".into(),
            sort: Sort::new("Bool"),
        };
        let sentence = Sentence::Claim {
            body: truth.clone(),
            requires: truth.clone(),
            ensures: truth,
            attributes: attributes.clone(),
        };
        let valued = valued_attributes(&[&sentence]);
        assert!(!valued.contains("sortParams"));
        assert_eq!(
            emit_attributes(attributes.entries(), &valued, &BTreeMap::new()),
            Attributes(vec![Pattern::Application {
                symbol: Symbol {
                    name: "sortParams".into(),
                    sort_parameters: Vec::new(),
                },
                arguments: Vec::new(),
            }])
        );
    }
}
