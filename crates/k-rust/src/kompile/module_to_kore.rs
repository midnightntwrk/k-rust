//! The declaration-producing prefix of Java's `ModuleToKORE`.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use serde_json::Value;

use crate::definition::{
    AssociativityRelations, Attributes as KAttributes, Definition as KDefinition,
    LOCATION_ATTRIBUTE, LabelHead, PartialOrder, ProductionCatalog, ProductionItem, RelationError,
    ResolveError, ResolvedDefinition, SOURCE_ATTRIBUTE, Sentence, SortCatalog, SortHead,
    match_rule_label,
};
use crate::kast::{Label, Sort};
use crate::kore::ast::{
    Attributes, Module, Pattern, Sentence as KoreSentence, Sort as KoreSort, Symbol,
};

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

/// The two declaration views produced by `ModuleToKORE`.
///
/// `semantics` carries backend-facing symbol attributes. `syntax` carries the
/// same declarations plus concrete-syntax formatting metadata.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeclarationModules {
    pub semantics: Module,
    pub syntax: Module,
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
    })
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
