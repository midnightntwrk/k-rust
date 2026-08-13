//! Expansion of parsed configuration declarations into generated sentences.

use std::collections::BTreeSet;
use std::fmt;

use serde_json::{Value, json};

use super::{
    Attributes, Definition, LabelHead, ProductionCatalog, ProductionItem, ResolveError,
    ResolvedDefinition, Sentence, checks::is_builtin_attribute, sentence_equivalent,
    sort_sentences,
};
use crate::kast::string::unquote;
use crate::kast::{Label, Sort, Term};

const CELL_NAME_SORT: &str = "#CellName";
const CONFIG_VAR_SORT: &str = "KConfigVar";
const GENERATED_TOP_CELL_NAME: &str = "generatedTop";

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ConfigurationError {
    Definition(ResolveError),
    Invalid {
        module: String,
        source: Option<String>,
        location: Option<super::Location>,
        message: String,
    },
}

impl fmt::Display for ConfigurationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Definition(error) => error.fmt(formatter),
            Self::Invalid {
                module, message, ..
            } => write!(
                formatter,
                "invalid configuration in module {module:?}: {message}"
            ),
        }
    }
}

impl std::error::Error for ConfigurationError {}

/// Expand every structured configuration in dependency-first module order.
///
/// The generated cells from imported modules are therefore visible while
/// resolving external-cell declarations in importing modules.
pub fn expand_configurations(definition: &Definition) -> Result<Definition, ConfigurationError> {
    let initial =
        ResolvedDefinition::resolve(definition).map_err(ConfigurationError::Definition)?;
    let module_names = initial
        .dependency_order()
        .iter()
        .map(|id| initial.module(*id).name.clone())
        .collect::<Vec<_>>();
    let mut transformed = definition.clone();

    for module_name in module_names {
        let module_index = transformed
            .modules
            .iter()
            .position(|module| module.name == module_name)
            .expect("resolved modules came from the flat definition");
        if !transformed.modules[module_index]
            .local_sentences
            .iter()
            .any(|sentence| matches!(sentence, Sentence::Configuration { .. }))
        {
            continue;
        }

        let resolved =
            ResolvedDefinition::resolve(&transformed).map_err(ConfigurationError::Definition)?;
        let module_id = resolved
            .module_id(&module_name)
            .expect("the module remains present while configurations are expanded");
        let catalog = resolved.production_catalog(module_id);
        let existing_labels: BTreeSet<String> = catalog
            .defined_labels()
            .map(|label| label.as_str().to_owned())
            .collect();
        let local = transformed.modules[module_index].local_sentences.clone();
        let mut output = local
            .iter()
            .filter(|sentence| !matches!(sentence, Sentence::Configuration { .. }))
            .cloned()
            .collect::<Vec<_>>();
        let mut generated = Vec::new();
        let module_attributes = transformed.modules[module_index].attributes.clone();

        for sentence in &local {
            let Sentence::Configuration {
                body,
                ensures,
                attributes,
            } = sentence
            else {
                continue;
            };
            let mut generator = Generator {
                module: &module_name,
                catalog: &catalog,
                existing_labels: existing_labels.clone(),
                generated: &mut generated,
                attributes,
                module_attributes: &module_attributes,
            };
            generator.generate_top(body, ensures)?;
        }

        sort_sentences(&mut generated)
            .expect("configuration expansion emits only orderable sentence kinds");
        output.extend(generated);
        transformed.modules[module_index].local_sentences = output;
    }

    ResolvedDefinition::resolve(&transformed).map_err(ConfigurationError::Definition)?;
    Ok(transformed)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Multiplicity {
    One,
    Optional,
    Star,
}

struct GeneratedNode {
    child_sorts: Vec<Sort>,
    initializer: Term,
    leaf: bool,
    initializer_takes_map: bool,
}

struct Generator<'a, 'catalog> {
    module: &'a str,
    catalog: &'catalog ProductionCatalog<'catalog>,
    existing_labels: BTreeSet<String>,
    generated: &'a mut Vec<Sentence>,
    attributes: &'a Attributes,
    module_attributes: &'a Attributes,
}

impl Generator<'_, '_> {
    fn generate_top(&mut self, body: &Term, ensures: &Term) -> Result<(), ConfigurationError> {
        self.generate(body, Some(ensures))?;
        Ok(())
    }

    fn generate(
        &mut self,
        term: &Term,
        ensures: Option<&Term>,
    ) -> Result<GeneratedNode, ConfigurationError> {
        match term.unannotated() {
            Term::Apply { label, arguments } if label.name == "#configCell" => {
                self.generate_cell(arguments, ensures)
            }
            Term::Apply { label, arguments } if label.name == "#externalCell" => {
                self.generate_external(arguments)
            }
            Term::Apply { label, arguments } if label.name == "#cells" => {
                if ensures.is_some() {
                    let name = cell_name_token(GENERATED_TOP_CELL_NAME);
                    return self.generate_cell(
                        &[
                            name.clone(),
                            Term::apply("#cellPropertyListTerminator", vec![]),
                            term.clone(),
                            name,
                        ],
                        ensures,
                    );
                }
                let mut cells = Vec::new();
                flatten_cells(arguments, &mut cells);
                let mut child_sorts = Vec::new();
                let mut initializers = Vec::new();
                let mut initializer_takes_map = false;
                for cell in cells {
                    let generated = self.generate(cell, None)?;
                    child_sorts.extend(generated.child_sorts);
                    initializers.push(generated.initializer);
                    initializer_takes_map |= generated.initializer_takes_map;
                }
                Ok(GeneratedNode {
                    child_sorts,
                    initializer: Term::apply("#cells", initializers),
                    leaf: false,
                    initializer_takes_map,
                })
            }
            Term::Token { sort, .. } => Ok(GeneratedNode {
                child_sorts: vec![sort.clone()],
                initializer: leaf_initializer(term),
                leaf: true,
                initializer_takes_map: has_configuration_or_regular_variable(term),
            }),
            Term::Sequence(_) | Term::Variable { .. } | Term::InjectedLabel(_) => {
                Ok(GeneratedNode {
                    child_sorts: vec![Sort::new("K")],
                    initializer: leaf_initializer(term),
                    leaf: true,
                    initializer_takes_map: has_configuration_or_regular_variable(term),
                })
            }
            Term::Apply { label, .. } => {
                let sort = semantic_cast_sort(label).or_else(|| {
                    self.catalog
                        .result_sort_for(&LabelHead::new(&label.name))
                        .cloned()
                });
                let Some(sort) = sort else {
                    return Err(self.error(format!(
                        "cannot determine the sort of configuration term {:?}",
                        label.name
                    )));
                };
                Ok(GeneratedNode {
                    child_sorts: vec![sort],
                    initializer: leaf_initializer(term),
                    leaf: true,
                    initializer_takes_map: has_configuration_or_regular_variable(term),
                })
            }
            Term::Rewrite { .. } | Term::As { .. } => {
                Err(self.error("unexpected rewrite or as-pattern in configuration declaration"))
            }
            Term::Annotated { .. } => unreachable!(),
        }
    }

    fn generate_external(&self, arguments: &[Term]) -> Result<GeneratedNode, ConfigurationError> {
        let [name] = arguments else {
            return Err(self.error("malformed external cell in configuration declaration"));
        };
        let name = expect_cell_name(name)
            .ok_or_else(|| self.error("malformed external cell in configuration declaration"))?;
        let sort = Sort::new(cell_sort_name(name));
        let init_label = init_label(&sort);
        let mut productions = self
            .catalog
            .productions_for(&LabelHead::new(&init_label))
            .iter()
            .filter_map(|id| match self.catalog.production(*id) {
                production @ Sentence::Production { .. }
                    if !self
                        .catalog
                        .production(*id)
                        .attributes()
                        .get("recordPrd")
                        .is_some() =>
                {
                    Some(production)
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        productions.extend(self.generated.iter().filter(|sentence| match sentence {
            Sentence::Production {
                label: Some(label), ..
            } => label.name == init_label,
            _ => false,
        }));
        let mut unique: Vec<&Sentence> = Vec::new();
        for production in productions {
            if !unique
                .iter()
                .any(|existing| sentence_equivalent(existing, production))
            {
                unique.push(production);
            }
        }
        let (initializer, initializer_takes_map) = match unique.as_slice() {
            [Sentence::Production { items, .. }] if items.len() == 1 => {
                (Some(Term::apply(init_label, vec![])), false)
            }
            [Sentence::Production { items, .. }] if items.len() == 4 => {
                (Some(Term::apply(init_label, vec![init_variable()])), true)
            }
            _ => (None, false),
        };
        let Some(initializer) = initializer else {
            return Err(self.error(format!(
                "external cell <{name}/> does not resolve to one initializer production"
            )));
        };
        Ok(GeneratedNode {
            child_sorts: vec![sort],
            initializer,
            leaf: true,
            initializer_takes_map,
        })
    }

    fn generate_cell(
        &mut self,
        arguments: &[Term],
        ensures: Option<&Term>,
    ) -> Result<GeneratedNode, ConfigurationError> {
        let [start, properties, contents, end] = arguments else {
            return Err(self.error("malformed cell in configuration declaration"));
        };
        let start = expect_cell_name(start)
            .ok_or_else(|| self.error("malformed cell in configuration declaration"))?;
        let end = expect_cell_name(end)
            .ok_or_else(|| self.error("malformed cell in configuration declaration"))?;
        if start != end {
            return Err(self.error(format!("cell <{start}> is closed by mismatched </{end}>")));
        }
        let properties = self.parse_properties(properties, start)?;
        let multiplicity = match properties.get_str("multiplicity") {
            None | Some("1") => Multiplicity::One,
            Some("?") => Multiplicity::Optional,
            Some("*") => Multiplicity::Star,
            Some(value) => {
                return Err(self.error(format!(
                    "invalid multiplicity found in cell <{start}>: {value}"
                )));
            }
        };
        let stream = properties.get("stream").is_some();
        let children = self.generate(contents, None)?;
        let has_variables = children.initializer_takes_map
            || has_configuration_or_regular_variable(contents)
            || contains_external_map_initializer(contents, self.catalog, self.generated);
        self.compute_cell(
            start,
            properties,
            multiplicity,
            stream,
            children,
            ensures,
            has_variables,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn compute_cell(
        &mut self,
        cell_name: &str,
        properties: Attributes,
        multiplicity: Multiplicity,
        stream: bool,
        mut children: GeneratedNode,
        ensures: Option<&Term>,
        has_variables: bool,
    ) -> Result<GeneratedNode, ConfigurationError> {
        let sort = Sort::new(cell_sort_name(cell_name));
        if properties.get("maincell").is_some() {
            if !children.leaf || children.child_sorts.len() != 1 {
                return Err(self.error(format!(
                    "main cell <{cell_name}> must contain exactly one leaf term"
                )));
            }
            children.child_sorts = vec![Sort::new("K")];
        }
        let label = format!("<{cell_name}>");
        let init_label = init_label(&sort);
        let collection_sort = properties.get_str("type").unwrap_or("Bag").to_owned();
        if multiplicity != Multiplicity::Star && properties.get("type").is_some() {
            return Err(self.error(format!(
                "cell <{cell_name}> specifies type without multiplicity=\"*\""
            )));
        }

        let items = cell_items(cell_name, &children.child_sorts);
        let mut cell_attributes = merge_attributes(&properties, self.attributes);
        if properties.get("format").is_none() {
            cell_attributes.insert("format", json!(cell_format(children.child_sorts.len())));
        }

        if multiplicity != Multiplicity::Optional && !self.label_exists(&label) {
            self.push(production(
                Some(label.clone()),
                sort.clone(),
                items.clone(),
                cell_attributes.clone(),
            ));
        }

        let initializer_takes_map = has_variables || stream;
        let init_sort = if multiplicity == Multiplicity::Star {
            Sort::new(format!("{}{collection_sort}", sort.name))
        } else {
            sort.clone()
        };
        if !self.label_exists(&init_label) {
            self.push(initializer_production(
                &init_label,
                init_sort,
                initializer_takes_map,
            ));
        }
        let lhs = Term::apply(
            &init_label,
            if initializer_takes_map {
                vec![init_variable()]
            } else {
                vec![]
            },
        );
        self.push(Sentence::Rule {
            body: Term::Rewrite {
                left: Box::new(lhs),
                right: Box::new(incomplete_cell(&label, children.initializer.clone())),
            },
            requires: truth(),
            ensures: ensures.cloned().unwrap_or_else(truth),
            attributes: attributes(&[("initializer", json!(""))]),
        });

        if !children.leaf {
            self.generate_fragment(cell_name, &sort, &children.child_sorts);
        }

        let (parent_sort, initializer) = match multiplicity {
            Multiplicity::Star => {
                let collection = self.generate_collection(
                    cell_name,
                    &sort,
                    &collection_sort,
                    &children.child_sorts,
                )?;
                (
                    collection,
                    optional_initializer(&init_label, has_variables, &properties),
                )
            }
            Multiplicity::Optional => {
                let unit_label = format!(".{}", sort.name);
                self.push(production(
                    Some(unit_label.clone()),
                    sort.clone(),
                    vec![ProductionItem::Terminal(unit_label.clone())],
                    Attributes::default(),
                ));
                if !self.label_exists(&label) {
                    let mut attributes = cell_attributes;
                    attributes.insert("unit", json!(unit_label));
                    self.push(production(
                        Some(label.clone()),
                        sort.clone(),
                        items,
                        attributes,
                    ));
                }
                (
                    sort.clone(),
                    optional_initializer(&init_label, has_variables, &properties),
                )
            }
            Multiplicity::One => (
                sort.clone(),
                Term::apply(
                    init_label,
                    if initializer_takes_map {
                        vec![init_variable()]
                    } else {
                        vec![]
                    },
                ),
            ),
        };

        if properties.get("exit").is_some() {
            self.generate_exit(cell_name, &label);
        }
        Ok(GeneratedNode {
            child_sorts: vec![parent_sort],
            initializer,
            leaf: false,
            initializer_takes_map,
        })
    }

    fn generate_fragment(&mut self, name: &str, sort: &Sort, children: &[Sort]) {
        let fragment_label = format!("<{name}>-fragment");
        let fragment_sort = Sort::new(format!("{}Fragment", sort.name));
        let mut items = vec![ProductionItem::Terminal(fragment_label.clone())];
        for child in children {
            if child.name.ends_with("Cell") {
                let optional =
                    Sort::with_parameters(format!("{}Opt", child.name), child.parameters.clone());
                items.push(nonterminal_sort(optional.clone()));
                self.push(production(
                    None,
                    optional.clone(),
                    vec![nonterminal_sort(child.clone())],
                    Attributes::default(),
                ));
                let absent = format!("no{child}");
                if !self.label_exists(&absent) {
                    self.push(production(
                        Some(absent.clone()),
                        optional,
                        vec![ProductionItem::Terminal(absent)],
                        attributes(&[("cellOptAbsent", sort_value(child))]),
                    ));
                }
            } else {
                items.push(nonterminal_sort(child.clone()));
            }
        }
        items.push(ProductionItem::Terminal(format!("</{name}>-fragment")));
        if !self.label_exists(&fragment_label) {
            self.push(production(
                Some(fragment_label),
                fragment_sort,
                items,
                attributes(&[("cellFragment", sort_value(sort))]),
            ));
        }
    }

    fn generate_collection(
        &mut self,
        cell_name: &str,
        cell_sort: &Sort,
        collection_type: &str,
        child_sorts: &[Sort],
    ) -> Result<Sort, ConfigurationError> {
        if !matches!(collection_type, "Bag" | "Set" | "Map" | "List") {
            return Err(self.error(format!(
                "unexpected type for multiplicity * cell <{cell_name}>: {collection_type}; expected Set, Bag, List, or Map"
            )));
        }
        if collection_type == "Map" && child_sorts.is_empty() {
            return Err(self.error(format!(
                "map cell <{cell_name}> expects at least one child cell as its key"
            )));
        }
        let sort = Sort::new(format!("{}{collection_type}", cell_sort.name));
        let upper = collection_type.to_uppercase();
        self.push(Sentence::SyntaxSort {
            parameters: vec![],
            sort: sort.clone(),
            attributes: attributes(&[
                ("hook", json!(format!("{upper}.{collection_type}"))),
                ("cellCollection", json!("")),
            ]),
        });
        self.push(production(
            None,
            sort.clone(),
            vec![nonterminal_sort(cell_sort.clone())],
            Attributes::default(),
        ));

        let item_label = format!("{}Item", sort.name);
        let (item_items, format) = if collection_type == "Map" {
            (
                vec![
                    ProductionItem::Terminal(item_label.clone()),
                    ProductionItem::Terminal("(".into()),
                    nonterminal_sort(child_sorts[0].clone()),
                    ProductionItem::Terminal(",".into()),
                    nonterminal_sort(cell_sort.clone()),
                    ProductionItem::Terminal(")".into()),
                ],
                "%5",
            )
        } else {
            (
                vec![
                    ProductionItem::Terminal(item_label.clone()),
                    ProductionItem::Terminal("(".into()),
                    nonterminal_sort(cell_sort.clone()),
                    ProductionItem::Terminal(")".into()),
                ],
                "%3",
            )
        };
        self.push(production(
            Some(item_label),
            sort.clone(),
            item_items,
            attributes(&[
                ("hook", json!(format!("{upper}.element"))),
                ("function", json!("")),
                ("format", json!(format)),
            ]),
        ));
        let unit = format!(".{}", sort.name);
        self.push(production(
            Some(unit.clone()),
            sort.clone(),
            vec![ProductionItem::Terminal(unit.clone())],
            attributes(&[
                ("hook", json!(format!("{upper}.unit"))),
                ("function", json!("")),
            ]),
        ));
        let concat = format!("_{}_", sort.name);
        let mut concat_attributes = attributes(&[
            ("assoc", json!("")),
            ("cellCollection", json!("")),
            ("element", json!(format!("{}Item", sort.name))),
            ("wrapElement", json!(format!("<{cell_name}>"))),
            ("unit", json!(unit)),
            ("hook", json!(format!("{upper}.concat"))),
            ("avoid", json!("")),
            ("function", json!("")),
        ]);
        match collection_type {
            "Set" => {
                concat_attributes.insert("idem", json!(""));
                concat_attributes.insert("comm", json!(""));
            }
            "Map" => {
                concat_attributes.insert("comm", json!(""));
            }
            "Bag" => {
                concat_attributes.insert("comm", json!(""));
                concat_attributes.insert("bag", json!(""));
            }
            "List" => {}
            _ => unreachable!(),
        }
        self.push(production(
            Some(concat),
            sort.clone(),
            vec![
                nonterminal_sort(sort.clone()),
                nonterminal_sort(sort.clone()),
            ],
            concat_attributes,
        ));

        if collection_type == "Map" {
            self.generate_map_collection_helpers(cell_name, cell_sort, &sort, &child_sorts[0]);
        }
        Ok(sort)
    }

    fn generate_map_collection_helpers(
        &mut self,
        cell_name: &str,
        cell_sort: &Sort,
        map_sort: &Sort,
        key_sort: &Sort,
    ) {
        self.push(production(
            Some(format!("{}:in_keys", map_sort.name)),
            Sort::new("Bool"),
            vec![
                nonterminal_sort(key_sort.clone()),
                ProductionItem::Terminal("in_keys".into()),
                ProductionItem::Terminal("(".into()),
                nonterminal_sort(map_sort.clone()),
                ProductionItem::Terminal(")".into()),
            ],
            attributes(&[
                ("hook", json!("MAP.in_keys")),
                ("function", json!("")),
                ("total", json!("")),
            ]),
        ));
        let key_label = format!("{}Key", map_sort.name);
        self.push(production(
            Some(key_label.clone()),
            key_sort.clone(),
            vec![
                ProductionItem::Terminal(key_label.clone()),
                ProductionItem::Terminal("(".into()),
                nonterminal_sort(cell_sort.clone()),
                ProductionItem::Terminal(")".into()),
            ],
            attributes(&[("function", json!("")), ("total", json!(""))]),
        ));
        let key = Term::Variable {
            name: "Key".into(),
            sort: Some(key_sort.clone()),
        };
        self.push(Sentence::Rule {
            body: Term::Rewrite {
                left: Box::new(Term::apply(
                    key_label,
                    vec![incomplete_cell_with_dots(
                        &format!("<{cell_name}>"),
                        key.clone(),
                        false,
                        true,
                    )],
                )),
                right: Box::new(key),
            },
            requires: truth(),
            ensures: truth(),
            attributes: Attributes::default(),
        });
    }

    fn generate_exit(&mut self, _cell_name: &str, label: &str) {
        if !self.label_exists("getExitCode") {
            self.push(production(
                Some("getExitCode".into()),
                Sort::new("Int"),
                vec![
                    ProductionItem::Terminal("getExitCode".into()),
                    ProductionItem::Terminal("(".into()),
                    nonterminal("GeneratedTopCell"),
                    ProductionItem::Terminal(")".into()),
                ],
                attributes(&[("function", json!(""))]),
            ));
        }
        self.push(Sentence::SyntaxSort {
            parameters: vec![],
            sort: Sort::new("GeneratedTopCell"),
            attributes: Attributes::default(),
        });
        let exit = Term::Variable {
            name: "Exit".into(),
            sort: Some(Sort::new("Int")),
        };
        self.push(Sentence::Rule {
            body: Term::Rewrite {
                left: Box::new(Term::apply(
                    "getExitCode",
                    vec![incomplete_cell_with_dots(
                        "<generatedTop>",
                        incomplete_cell(label, exit.clone()),
                        true,
                        true,
                    )],
                )),
                right: Box::new(exit),
            },
            requires: truth(),
            ensures: truth(),
            attributes: Attributes::default(),
        });
    }

    fn parse_properties(
        &self,
        term: &Term,
        cell_name: &str,
    ) -> Result<Attributes, ConfigurationError> {
        let mut properties = Attributes::default();
        properties.insert("cell", json!(""));
        properties.insert("cellName", json!(cell_name));
        if cell_name == "k" {
            properties.insert("maincell", json!(""));
        }
        parse_property_list(term, &mut properties).map_err(|message| self.error(message))?;
        Ok(properties)
    }

    fn label_exists(&self, label: &str) -> bool {
        self.existing_labels.contains(label)
            || self.generated.iter().any(|sentence| {
                matches!(
                    sentence,
                    Sentence::Production { label: Some(existing), .. }
                        if existing.name == label
                )
            })
    }

    fn push(&mut self, sentence: Sentence) {
        if !self
            .generated
            .iter()
            .any(|existing| sentence_equivalent(existing, &sentence))
        {
            self.generated.push(sentence);
        }
    }

    fn error(&self, message: impl Into<String>) -> ConfigurationError {
        let source = self
            .attributes
            .source()
            .or_else(|| self.module_attributes.source())
            .map(str::to_owned);
        let location = self
            .attributes
            .location()
            .or_else(|| self.module_attributes.location());
        ConfigurationError::Invalid {
            module: self.module.to_owned(),
            source,
            location,
            message: message.into(),
        }
    }
}

fn parse_property_list(term: &Term, output: &mut Attributes) -> Result<(), String> {
    match term.unannotated() {
        Term::Apply { label, arguments }
            if label.name == "#cellPropertyListTerminator" && arguments.is_empty() =>
        {
            Ok(())
        }
        Term::Apply { label, arguments }
            if label.name == "#cellPropertyList" && arguments.len() == 2 =>
        {
            let (key, value) = parse_property(&arguments[0])?;
            output.insert(key, json!(value));
            parse_property_list(&arguments[1], output)
        }
        _ => Err("malformed cell properties".into()),
    }
}

fn parse_property(term: &Term) -> Result<(String, String), String> {
    let Term::Apply { label, arguments } = term.unannotated() else {
        return Err("malformed cell property".into());
    };
    let [key, value] = arguments.as_slice() else {
        return Err("malformed cell property".into());
    };
    if label.name != "#cellProperty" {
        return Err("malformed cell property".into());
    }
    let key = expect_cell_name(key).ok_or("malformed cell property key")?;
    if !is_builtin_attribute(key) {
        return Err(format!("unrecognized cell property {key:?}"));
    }
    let Term::Token { token, sort } = value.unannotated() else {
        return Err("malformed cell property value".into());
    };
    if sort.name != "KString" {
        return Err("malformed cell property value".into());
    }
    let value = unquote(token)?;
    if value.is_empty() && attribute_requires_value(key) {
        return Err(format!("cell property {key:?} requires a value"));
    }
    if !value.is_empty() && attribute_forbids_value(key) {
        return Err(format!("cell property {key:?} does not accept a value"));
    }
    Ok((key.to_owned(), value))
}

fn attribute_requires_value(key: &str) -> bool {
    matches!(
        key,
        "applyPriority"
            | "cellName"
            | "color"
            | "colors"
            | "context"
            | "depends"
            | "element"
            | "format"
            | "group"
            | "hook"
            | "index"
            | "klabel"
            | "label"
            | "latex"
            | "multiplicity"
            | "overload"
            | "parser"
            | "prec"
            | "priority"
            | "result"
            | "smt-hook"
            | "smtlib"
            | "syntactic"
            | "terminator-symbol"
            | "type"
            | "unboundVariables"
            | "unit"
            | "update"
            | "wrapElement"
    )
}

fn attribute_forbids_value(key: &str) -> bool {
    is_builtin_attribute(key)
        && !attribute_requires_value(key)
        && !matches!(
            key,
            "concrete"
                | "hybrid"
                | "seqstrict"
                | "simplification"
                | "stream"
                | "strict"
                | "symbol"
                | "symbolic"
        )
}

fn expect_cell_name(term: &Term) -> Option<&str> {
    match term.unannotated() {
        Term::Token { token, sort } if sort.name == CELL_NAME_SORT => Some(token),
        _ => None,
    }
}

fn flatten_cells<'a>(terms: &'a [Term], output: &mut Vec<&'a Term>) {
    for term in terms {
        match term.unannotated() {
            Term::Apply { label, arguments } if label.name == "#cells" => {
                flatten_cells(arguments, output);
            }
            _ => output.push(term),
        }
    }
}

fn contains_external_map_initializer(
    term: &Term,
    catalog: &ProductionCatalog<'_>,
    generated: &[Sentence],
) -> bool {
    let mut found = false;
    term.visit_preorder(&mut |term| {
        let Term::Apply { label, arguments } = term else {
            return;
        };
        if label.name != "#externalCell" {
            return;
        }
        let Some(name) = arguments.first().and_then(expect_cell_name) else {
            return;
        };
        let init = init_label(&Sort::new(cell_sort_name(name)));
        found = catalog
            .productions_for(&LabelHead::new(&init))
            .iter()
            .any(|id| matches!(catalog.production(*id), Sentence::Production { items, .. } if items.len() == 4))
            || generated.iter().any(|sentence| matches!(
                sentence,
                Sentence::Production { label: Some(label), items, .. }
                    if label.name == init && items.len() == 4
            ));
    });
    found
}

fn has_configuration_or_regular_variable(term: &Term) -> bool {
    let mut found = false;
    term.visit_preorder(&mut |term| match term {
        Term::Token { sort, .. } if sort.name == CONFIG_VAR_SORT => found = true,
        Term::Variable { .. } => found = true,
        _ => {}
    });
    found
}

fn leaf_initializer(term: &Term) -> Term {
    fn transform(term: &Term, sort: Option<&Sort>) -> Term {
        let replaces_source_node = matches!(
            term.unannotated(),
            Term::Token { sort, .. } if sort.name == CONFIG_VAR_SORT
        );
        let transformed = match term.unannotated() {
            Term::Token {
                token,
                sort: token_sort,
            } if token_sort.name == CONFIG_VAR_SORT => {
                let project = sort
                    .filter(|sort| sort.name != "K")
                    .cloned()
                    .unwrap_or_else(|| Sort::new("KItem"));
                Term::apply(
                    format!("project:{project}"),
                    vec![Term::apply(
                        "Map:lookup",
                        vec![
                            init_variable(),
                            Term::Token {
                                token: token.clone(),
                                sort: token_sort.clone(),
                            },
                        ],
                    )],
                )
            }
            Term::Apply { label, arguments } => {
                let next_sort = semantic_cast_sort(label);
                Term::Apply {
                    label: label.clone(),
                    arguments: arguments
                        .iter()
                        .map(|argument| transform(argument, next_sort.as_ref().or(sort)))
                        .collect(),
                }
            }
            Term::Rewrite { left, right } => Term::Rewrite {
                left: Box::new(transform(left, sort)),
                right: Box::new(transform(right, sort)),
            },
            Term::As { pattern, alias } => Term::As {
                pattern: Box::new(transform(pattern, sort)),
                alias: Box::new(transform(alias, sort)),
            },
            Term::Sequence(items) => {
                Term::Sequence(items.iter().map(|item| transform(item, sort)).collect())
            }
            _ => term.unannotated().clone(),
        };
        if let Some(metadata) = term.metadata() {
            let mut metadata = metadata.clone();
            if replaces_source_node {
                metadata.production = None;
                // The replacement is a generated projection, not the source token/cast whose
                // inferred sort this metadata described. Let the projection production determine
                // its result sort during final sort-injection materialization.
                metadata.sort = None;
            }
            transformed.with_metadata(metadata)
        } else {
            transformed
        }
    }
    transform(term, None)
}

fn semantic_cast_sort(label: &Label) -> Option<Sort> {
    label
        .name
        .strip_prefix("#SemanticCastTo")
        .filter(|name| !name.is_empty())
        .map(Sort::new)
}

fn optional_initializer(label: &str, has_variables: bool, properties: &Attributes) -> Term {
    if has_variables {
        Term::apply(label, vec![init_variable()])
    } else if properties.get("initial").is_some() {
        Term::apply(label, vec![])
    } else {
        Term::apply("#cells", vec![])
    }
}

fn initializer_production(label: &str, sort: Sort, takes_map: bool) -> Sentence {
    let items = if takes_map {
        vec![
            ProductionItem::Terminal(label.into()),
            ProductionItem::Terminal("(".into()),
            nonterminal("Map"),
            ProductionItem::Terminal(")".into()),
        ]
    } else {
        vec![ProductionItem::Terminal(label.into())]
    };
    let mut attributes = attributes(&[("initializer", json!("")), ("function", json!(""))]);
    if !takes_map {
        attributes.insert("total", json!(""));
    }
    production(Some(label.into()), sort, items, attributes)
}

fn production(
    label: Option<String>,
    sort: Sort,
    items: Vec<ProductionItem>,
    attributes: Attributes,
) -> Sentence {
    Sentence::Production {
        label: label.map(Label::new),
        parameters: vec![],
        sort,
        items,
        attributes,
    }
}

fn cell_items(name: &str, children: &[Sort]) -> Vec<ProductionItem> {
    std::iter::once(ProductionItem::Terminal(format!("<{name}>")))
        .chain(children.iter().cloned().map(nonterminal_sort))
        .chain(std::iter::once(ProductionItem::Terminal(format!(
            "</{name}>"
        ))))
        .collect()
}

fn cell_format(children: usize) -> String {
    let mut format = String::from("%1%i");
    for index in 2..2 + children {
        format.push_str(&format!("%n%{index}"));
    }
    format.push_str(&format!("%d%n%{}", children + 2));
    format
}

fn incomplete_cell(label: &str, child: Term) -> Term {
    incomplete_cell_with_dots(label, child, false, false)
}

fn incomplete_cell_with_dots(label: &str, child: Term, open_left: bool, open_right: bool) -> Term {
    Term::apply(
        label,
        vec![
            Term::apply(if open_left { "#dots" } else { "#noDots" }, vec![]),
            child,
            Term::apply(if open_right { "#dots" } else { "#noDots" }, vec![]),
        ],
    )
}

fn init_variable() -> Term {
    Term::Variable {
        name: "Init".into(),
        sort: Some(Sort::new("Map")),
    }
}

fn truth() -> Term {
    Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    }
}

fn init_label(sort: &Sort) -> String {
    format!("init{sort}")
}

pub fn cell_sort_name(cell_name: &str) -> String {
    let mut output = String::new();
    let mut uppercase = true;
    for character in cell_name.chars() {
        if character == '-' {
            uppercase = true;
        } else if uppercase {
            output.extend(character.to_uppercase());
            uppercase = false;
        } else {
            output.push(character);
        }
    }
    output.push_str("Cell");
    output
}

fn cell_name_token(name: &str) -> Term {
    Term::Token {
        token: name.into(),
        sort: Sort::new(CELL_NAME_SORT),
    }
}

fn nonterminal(name: &str) -> ProductionItem {
    nonterminal_sort(Sort::new(name))
}

fn nonterminal_sort(sort: Sort) -> ProductionItem {
    ProductionItem::NonTerminal { sort, name: None }
}

fn attributes(entries: &[(&str, Value)]) -> Attributes {
    Attributes::new(
        entries
            .iter()
            .map(|(key, value)| ((*key).into(), value.clone()))
            .collect(),
    )
}

fn merge_attributes(base: &Attributes, overlay: &Attributes) -> Attributes {
    let mut entries = base.entries().clone();
    entries.extend(
        overlay
            .entries()
            .iter()
            .map(|(key, value)| (key.clone(), value.clone())),
    );
    Attributes::new(entries)
}

fn sort_value(sort: &Sort) -> Value {
    json!({
        "node": "KSort",
        "name": sort.name,
        "params": sort.parameters.iter().map(sort_value).collect::<Vec<_>>(),
    })
}
