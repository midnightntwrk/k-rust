//! Typed projections of emitted K artifacts.

use krs_compiler::{MappedIdentity, SourceMap, SymbolMap, definition_module_imports};
use krs_ir::{
    ApplicationRef, CellPost, DefinitionIr, DefinitionRuleBody, DefinitionSentence,
    DefinitionSortRef, DefinitionTerm, DefinitionTermKind, DescriptorBundle, DescriptorPayload,
    FixedCell, FixedCellContent, FixedInitializerCell, FixedInitializerContent,
    GrammarProductionItemKind, OriginFrame, ProductionAttribute, RangedOriginKind, SemanticTheory,
    SentenceKind, SymbolId,
};
use serde::{Deserialize, Serialize, de::DeserializeOwned};
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fs,
    path::Path,
};

mod projections;

type QueryResult = Result<Value, Box<dyn Error>>;

#[derive(Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
enum Query {
    DescriptorDetails {
        #[serde(default)]
        module_path: Option<Vec<String>>,
        #[serde(default)]
        item_name: Option<String>,
        #[serde(default)]
        public_only: bool,
    },
    HeadRuleWalkthrough {
        item_name: String,
    },
    SymbolProjection {
        emitted_names: Vec<String>,
    },
    SourceToken {
        authored: String,
        package_relative_path: String,
        token: String,
        artifact: String,
    },
    ReplacementParity {
        reference: String,
        module: String,
        module_path: Vec<String>,
    },
    Files {},
    Modules {},
    SemanticModules {},
    Sentences {
        #[serde(default)]
        module: Option<String>,
        #[serde(default)]
        sentence_kind: Option<String>,
        #[serde(default)]
        label: Option<String>,
    },
    Productions {
        #[serde(default)]
        module: Option<String>,
        #[serde(default)]
        sort: Option<String>,
        #[serde(default)]
        symbol: Option<String>,
    },
    Vocabulary {},
    Applications {
        #[serde(default)]
        operation: Option<String>,
        #[serde(default)]
        symbol: Option<String>,
        #[serde(default)]
        result_sort: Option<String>,
        #[serde(default)]
        argument_sorts: Option<Vec<String>>,
        #[serde(default)]
        arguments: Option<Vec<TermPattern>>,
    },
    Descriptors {
        #[serde(default)]
        descriptor_kind: Option<String>,
        #[serde(default)]
        item_kind: Option<String>,
    },
    Symbols {
        #[serde(default)]
        emitted_name: Option<String>,
        #[serde(default)]
        identity_kind: Option<String>,
        #[serde(default)]
        symbol_kind: Option<String>,
    },
    Sources {
        #[serde(default)]
        key: Option<String>,
        #[serde(default)]
        node_kind: Option<String>,
        #[serde(default)]
        artifact: Option<String>,
    },
    DefinitionShape {},
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct TermPattern {
    #[serde(default)]
    kind: Option<String>,
    #[serde(default)]
    sort: Option<String>,
    #[serde(default)]
    symbol: Option<String>,
    #[serde(default)]
    operation: Option<String>,
    #[serde(default)]
    token: Option<String>,
    #[serde(default)]
    variable: Option<String>,
    #[serde(default)]
    arguments: Option<Vec<Self>>,
}

impl TermPattern {
    fn matches(&self, fact: &Value) -> bool {
        [
            (&self.kind, "kind"),
            (&self.sort, "sort"),
            (&self.symbol, "symbol"),
            (&self.operation, "operation"),
            (&self.token, "token"),
            (&self.variable, "variable"),
        ]
        .iter()
        .all(|(expected, key)| expected.as_ref().is_none_or(|value| fact[*key] == *value))
            && self.arguments.as_ref().is_none_or(|patterns| {
                fact["arguments"].as_array().is_some_and(|arguments| {
                    patterns.len() == arguments.len()
                        && patterns.iter().zip(arguments).all(|(p, a)| p.matches(a))
                })
            })
    }
}

fn read<T: DeserializeOwned + Send>(directory: &Path, name: &str) -> Result<T, Box<dyn Error>> {
    Ok(krs_ir::json::from_slice(&fs::read(directory.join(name))?)?)
}
fn encoded<T: Serialize>(value: &T) -> Value {
    serde_json::to_value(value).expect("IR values serialize")
}
fn enum_name<T: Serialize>(value: &T) -> String {
    encoded(value)
        .as_str()
        .expect("enum has a string encoding")
        .to_owned()
}
fn accepts(filter: Option<&str>, value: &str) -> bool {
    filter.is_none_or(|filter| filter == value)
}

struct Context<'a> {
    names: BTreeMap<&'a SymbolId, &'a str>,
    cells: BTreeMap<&'a SymbolId, &'a str>,
    hooks: BTreeMap<&'a SymbolId, String>,
}
impl<'a> Context<'a> {
    fn new(definition: &'a DefinitionIr) -> Self {
        let mut context = Self {
            names: BTreeMap::new(),
            cells: BTreeMap::new(),
            hooks: BTreeMap::new(),
        };
        for module in definition.modules() {
            for sentence in module.sentences() {
                match sentence {
                    DefinitionSentence::SyntaxSort(s) => {
                        context
                            .names
                            .insert(s.symbol().id(), s.symbol().emitted_name());
                    }
                    DefinitionSentence::Production(p) => {
                        context
                            .names
                            .insert(p.symbol().id(), p.symbol().emitted_name());
                        for attribute in p.attributes() {
                            if let ProductionAttribute::Hook { operation, .. } = attribute {
                                context.hooks.insert(p.symbol().id(), enum_name(operation));
                            }
                        }
                    }
                    DefinitionSentence::Configuration(c) => context.cell_names(c.cells()),
                    _ => {}
                }
            }
        }
        context
    }
    fn cell_names(&mut self, cells: &'a [FixedCell<DefinitionSortRef, SymbolId>]) {
        for cell in cells {
            self.cells.insert(cell.id(), cell.name());
            if let FixedCellContent::Children { children } = cell.content() {
                self.cell_names(children);
            }
        }
    }
    fn sort(&self, sort: &DefinitionSortRef) -> String {
        match sort {
            DefinitionSortRef::Declared(id) => self.names[id].to_owned(),
            DefinitionSortRef::Builtin(sort) => sort.k_name().to_owned(),
        }
    }
    fn term(&self, term: &DefinitionTerm) -> Value {
        let mut fact = json!({"sort":self.sort(term.sort())});
        let (kind, arguments) = match term.kind() {
            DefinitionTermKind::Variable { variable } => {
                fact["variable"] = json!(variable.as_str());
                ("variable", None)
            }
            DefinitionTermKind::Token { value } => {
                fact["token"] = json!(value);
                ("token", None)
            }
            DefinitionTermKind::Application {
                application,
                arguments,
            } => {
                match application {
                    ApplicationRef::Declared(id) => {
                        fact["symbol"] = json!(self.names[id]);
                    }
                    ApplicationRef::Builtin(operation) => {
                        fact["operation"] = json!(enum_name(operation));
                    }
                }
                ("application", Some(arguments))
            }
            DefinitionTermKind::KSequence { items, .. } => ("k_sequence", Some(items)),
            DefinitionTermKind::Map {
                operation,
                arguments,
            } => {
                fact["operation"] = json!(format!("map.{}", enum_name(operation)));
                ("map", Some(arguments))
            }
            DefinitionTermKind::List {
                operation,
                arguments,
            } => {
                fact["operation"] = json!(format!("list.{}", enum_name(operation)));
                ("list", Some(arguments))
            }
            DefinitionTermKind::Set {
                operation,
                arguments,
            } => {
                fact["operation"] = json!(format!("set.{}", enum_name(operation)));
                ("set", Some(arguments))
            }
            DefinitionTermKind::Cell { cell, children } => {
                fact["cell"] = json!(self.cells[cell]);
                ("cell", Some(children))
            }
            DefinitionTermKind::Rewrite { from, to } => {
                fact["from"] = self.term(from);
                fact["to"] = self.term(to);
                ("rewrite", None)
            }
        };
        fact["kind"] = json!(kind);
        if let Some(arguments) = arguments {
            fact["arguments"] = json!(arguments.iter().map(|t| self.term(t)).collect::<Vec<_>>());
        }
        fact
    }
    fn operation_rows(
        &self,
        term: &DefinitionTerm,
        rows: &mut Vec<Value>,
        module: &str,
        label: &str,
        filter: &dyn Fn(&Value) -> bool,
        include_arguments: bool,
    ) {
        let children = match term.kind() {
            DefinitionTermKind::Application { arguments, .. }
            | DefinitionTermKind::Map { arguments, .. }
            | DefinitionTermKind::List { arguments, .. }
            | DefinitionTermKind::Set { arguments, .. } => {
                let (symbol, operation) = match term.kind() {
                    DefinitionTermKind::Application {
                        application: ApplicationRef::Declared(id),
                        ..
                    } => (Some(self.names[id].to_owned()), None),
                    DefinitionTermKind::Application {
                        application: ApplicationRef::Builtin(op),
                        ..
                    } => (None, Some(enum_name(op))),
                    DefinitionTermKind::Map { operation, .. } => {
                        (None, Some(format!("map.{}", enum_name(operation))))
                    }
                    DefinitionTermKind::List { operation, .. } => {
                        (None, Some(format!("list.{}", enum_name(operation))))
                    }
                    DefinitionTermKind::Set { operation, .. } => {
                        (None, Some(format!("set.{}", enum_name(operation))))
                    }
                    _ => unreachable!("operation term"),
                };
                let hook = match term.kind() {
                    DefinitionTermKind::Application {
                        application: ApplicationRef::Declared(id),
                        ..
                    } => self.hooks.get(id),
                    _ => None,
                };
                let mut row = json!({"module":module,"label":label,"symbol":symbol,"operation":operation,"hook":hook,
                    "result_sort":self.sort(term.sort()),"argument_sorts":arguments.iter().map(|t| self.sort(t.sort())).collect::<Vec<_>>()});
                if filter(&row) {
                    if include_arguments {
                        row["arguments"] =
                            json!(arguments.iter().map(|t| self.term(t)).collect::<Vec<_>>());
                    }
                    rows.push(row);
                }
                arguments.as_slice()
            }
            DefinitionTermKind::KSequence { items, .. } => items,
            DefinitionTermKind::Cell { children, .. } => children,
            DefinitionTermKind::Rewrite { from, to } => {
                self.operation_rows(from, rows, module, label, filter, include_arguments);
                self.operation_rows(to, rows, module, label, filter, include_arguments);
                return;
            }
            _ => return,
        };
        for child in children {
            self.operation_rows(child, rows, module, label, filter, include_arguments);
        }
    }
}

fn sentence_kind(sentence: &DefinitionSentence) -> &'static str {
    match sentence {
        DefinitionSentence::SyntaxSort(_) => "syntax_sort",
        DefinitionSentence::Subsort(_) => "subsort",
        DefinitionSentence::Production(_) => "production",
        DefinitionSentence::Precedence(_) => "precedence",
        DefinitionSentence::Associativity(_) => "associativity",
        DefinitionSentence::Configuration(_) => "configuration",
        DefinitionSentence::ContextAlias(_) => "context_alias",
        DefinitionSentence::Rule(rule) if rule.kind() == SentenceKind::Claim => "claim",
        DefinitionSentence::Rule(_) => "rule",
    }
}

fn frame_fact(frame: &krs_ir::CellContentFrame) -> Value {
    let (kind, binding) = match frame {
        krs_ir::CellContentFrame::Exact => ("exact", None),
        krs_ir::CellContentFrame::KSequenceTail { binding, .. } => {
            ("k_sequence_tail", binding.as_ref())
        }
        krs_ir::CellContentFrame::MapRemainder { binding, .. } => {
            ("map_remainder", binding.as_ref())
        }
    };
    json!({"kind":kind,"binding":binding})
}

fn rule_body(context: &Context<'_>, body: &DefinitionRuleBody) -> Value {
    match body {
        DefinitionRuleBody::Term(term) => context.term(term),
        DefinitionRuleBody::Configuration(body) => {
            json!({"kind":"configuration_rewrite","clauses":body.clauses().iter().map(|clause|
        json!({"cell":context.cells[clause.cell()],"from":context.term(clause.before()),"to":match clause.after(){CellPost::Preserve=>context.term(clause.before()),CellPost::Replace{term}=>context.term(term)},"frame":frame_fact(clause.frame())})).collect::<Vec<_>>() })
        }
    }
}
fn initializer_rows(
    context: &Context<'_>,
    initializers: &[FixedInitializerCell<SymbolId, DefinitionTerm>],
    rows: &mut Vec<Value>,
) {
    for cell in initializers {
        match cell.content() {
            FixedInitializerContent::Term { term } => {
                rows.push(json!({"cell":context.cells[cell.cell()],"term":context.term(term)}));
            }
            FixedInitializerContent::Children { children } => {
                initializer_rows(context, children, rows);
            }
        }
    }
}
fn productions(
    definition: &DefinitionIr,
    context: &Context<'_>,
    module_filter: Option<&str>,
    sort_filter: Option<&str>,
    symbol_filter: Option<&str>,
) -> Vec<Value> {
    let mut rows = Vec::new();
    for module in definition.modules() {
        if !accepts(module_filter, module.id().as_str()) {
            continue;
        }
        for sentence in module.sentences() {
            if let DefinitionSentence::Production(p) = sentence {
                let sort = context.sort(p.result_sort());
                let symbol = p.symbol().emitted_name();
                if !accepts(sort_filter, &sort) || !accepts(symbol_filter, symbol) {
                    continue;
                }
                let terminals = p
                    .items()
                    .iter()
                    .filter_map(|item| match item.kind() {
                        GrammarProductionItemKind::Terminal { text } => Some(text.clone()),
                        _ => None,
                    })
                    .collect::<Vec<_>>();
                let items=p.items().iter().map(|item| match item.kind(){GrammarProductionItemKind::NonTerminal{field,sort}=>json!({"item_kind":"non_terminal","field":field,"sort":context.sort(sort)}),kind=>encoded(kind)}).collect::<Vec<_>>();
                rows.push(json!({"module":module.id(),"sort":sort,"symbol":symbol,"terminals":terminals,"items":items,"attributes":p.attributes()}));
            }
        }
    }
    rows.sort_by(|a, b| {
        (a["module"].as_str(), a["symbol"].as_str())
            .cmp(&(b["module"].as_str(), b["symbol"].as_str()))
    });
    rows
}

fn operations(
    definition: &DefinitionIr,
    context: &Context<'_>,
    filter: &dyn Fn(&Value) -> bool,
    include_arguments: bool,
) -> Vec<Value> {
    let mut rows = Vec::new();
    for module in definition.modules() {
        for sentence in module.sentences() {
            if let DefinitionSentence::Rule(rule) = sentence {
                let name = module.id().as_str();
                let label = rule.label().emitted_name();
                match rule.relational_body() {
                    DefinitionRuleBody::Term(t) => {
                        context.operation_rows(
                            t,
                            &mut rows,
                            name,
                            label,
                            filter,
                            include_arguments,
                        );
                    }
                    DefinitionRuleBody::Configuration(c) => {
                        for clause in c.clauses() {
                            context.operation_rows(
                                clause.before(),
                                &mut rows,
                                name,
                                label,
                                filter,
                                include_arguments,
                            );
                            if let CellPost::Replace { term } = clause.after() {
                                context.operation_rows(
                                    term,
                                    &mut rows,
                                    name,
                                    label,
                                    filter,
                                    include_arguments,
                                );
                            }
                        }
                    }
                }
                if let Some(condition) = rule.requires() {
                    context.operation_rows(
                        condition.term(),
                        &mut rows,
                        name,
                        label,
                        filter,
                        include_arguments,
                    );
                }
                if let Some(condition) = rule.claim().and_then(krs_ir::DefinitionClaim::ensures) {
                    context.operation_rows(
                        condition.term(),
                        &mut rows,
                        name,
                        label,
                        filter,
                        include_arguments,
                    );
                }
            }
        }
    }
    rows
}

fn cell_rows(
    context: &Context<'_>,
    cells: &[FixedCell<DefinitionSortRef, SymbolId>],
    initializers: &[Value],
    variables: &BTreeMap<String, String>,
    rows: &mut Vec<Value>,
) {
    for cell in cells {
        let (sort, variable) = match cell.content() {
            FixedCellContent::Term { sort } => (
                Some(context.sort(sort)),
                initializers
                    .iter()
                    .find(|i| i["cell"] == cell.name())
                    .and_then(|i| i["term"]["variable"].as_str())
                    .and_then(|v| variables.get(v)),
            ),
            FixedCellContent::Children { children } => {
                cell_rows(context, children, initializers, variables, rows);
                (None, None)
            }
        };
        rows.push(json!({"name":cell.name(),"sort":sort,"configuration_variable":variable}));
    }
}

fn vocabulary(definition: &DefinitionIr, context: &Context<'_>) -> Value {
    let mut sorts = BTreeSet::new();
    let mut labels = BTreeSet::new();
    let mut imports = BTreeSet::new();
    let mut cells = Vec::new();
    let mut subsorts = Vec::new();
    for module in definition.modules() {
        imports.extend(definition_module_imports(module));
        for sentence in module.sentences() {
            match sentence {
                DefinitionSentence::SyntaxSort(s) => {
                    sorts.insert(s.symbol().emitted_name().to_owned());
                }
                DefinitionSentence::Rule(r) => {
                    labels.insert(r.label().emitted_name().to_owned());
                }
                DefinitionSentence::Subsort(s) => subsorts.push(
                    json!({"sort":context.sort(s.supersort()),"subsort":context.sort(s.subsort())}),
                ),
                DefinitionSentence::Configuration(c) => {
                    let mut initializers = Vec::new();
                    initializer_rows(context, c.initializer(), &mut initializers);
                    let vars = c
                        .variables()
                        .iter()
                        .map(|v| (v.id().as_str().to_owned(), v.external_name().to_owned()))
                        .collect();
                    cell_rows(context, c.cells(), &initializers, &vars, &mut cells);
                }
                _ => {}
            }
        }
    }
    let productions = productions(definition, context, None, None, None);
    let symbols = productions
        .iter()
        .map(|p| p["symbol"].as_str().unwrap().to_owned())
        .collect::<BTreeSet<_>>();
    let terminals = productions
        .iter()
        .flat_map(|p| p["terminals"].as_array().unwrap())
        .map(|t| t.as_str().unwrap().to_owned())
        .collect::<BTreeSet<_>>();
    json!({"sorts":sorts,"production_symbols":symbols,"terminals":terminals,"rule_labels":labels,"imports":imports,"cells":cells,"subsorts":subsorts,"applied_operations":operations(definition,context,&|_|true,false)})
}

/// Dispatches an independent artifact-query session request.
///
/// # Errors
///
/// Returns an error for missing paths, missing query objects, or failed queries.
pub fn dispatch(request: &Value) -> QueryResult {
    let directory = request
        .get("artifacts")
        .and_then(Value::as_str)
        .ok_or("ir.query requires string `artifacts`")?;
    query(
        Path::new(directory),
        request.get("query").ok_or("ir.query requires `query`")?,
    )
}

/// Answers one closed query using the version-checked artifact readers.
///
/// # Errors
///
/// Returns an error for unknown fields, invalid artifacts, unsupported schemas, or unreadable required files.
#[allow(clippy::too_many_lines)]
pub fn query(directory: &Path, request: &Value) -> QueryResult {
    let query: Query = serde_json::from_value(request.clone())?;
    match query {
        Query::DescriptorDetails {
            module_path,
            item_name,
            public_only,
        } => projections::descriptor_details(
            directory,
            module_path.as_deref(),
            item_name.as_deref(),
            public_only,
        ),
        Query::HeadRuleWalkthrough { item_name } => {
            projections::head_rule_walkthrough(directory, &item_name)
        }
        Query::SymbolProjection { emitted_names } => {
            projections::symbol_projection(directory, &emitted_names)
        }
        Query::SourceToken {
            authored,
            package_relative_path,
            token,
            artifact,
        } => projections::source_token(
            directory,
            Path::new(&authored),
            &package_relative_path,
            &token,
            &artifact,
        ),
        Query::ReplacementParity {
            reference,
            module,
            module_path,
        } => {
            projections::replacement_parity(Path::new(&reference), directory, &module, &module_path)
        }
        Query::Descriptors {
            descriptor_kind,
            item_kind,
        } => {
            let bundle: DescriptorBundle = read(directory, krs_compiler::DESCRIPTOR_ARTIFACT)?;
            let mut rows = Vec::new();
            let mut kinds = BTreeMap::<String, usize>::new();
            let mut items = BTreeMap::<String, usize>::new();
            for d in &bundle.descriptors {
                let kind = match &d.payload {
                    DescriptorPayload::Sort(_) => "sort",
                    DescriptorPayload::Constructor(_) => "constructor",
                    DescriptorPayload::Grammar(_) => "grammar",
                    DescriptorPayload::StructuredRule(_) => "structured_rule",
                    DescriptorPayload::FixedConfiguration(_) => "fixed_configuration",
                    DescriptorPayload::Cell(_) => "cell",
                    DescriptorPayload::ConfigurationRule(_) => "configuration_rule",
                    DescriptorPayload::HeadRule(_) => "head_rule",
                    DescriptorPayload::ContextAlias(_) => "context_alias",
                };
                let item = enum_name(&d.id.item_kind());
                if accepts(descriptor_kind.as_deref(), kind) && accepts(item_kind.as_deref(), &item)
                {
                    *kinds.entry(kind.to_owned()).or_default() += 1;
                    *items.entry(item.clone()).or_default() += 1;
                    rows.push(json!({"id":d.id,"descriptor_kind":kind,"item_kind":item,"cargo_name":d.id.package().cargo_name()}));
                }
            }
            Ok(json!({"counts":{"descriptor_kind":kinds,"item_kind":items},"rows":rows}))
        }
        Query::SemanticModules {} => {
            let theory: SemanticTheory = read(directory, krs_compiler::SEMANTIC_ARTIFACT)?;
            Ok(
                json!({"rows":theory.modules().iter().map(|m|json!({"name":m.id(),"production_count":m.productions().len(),"rule_count":m.rules().len(),"has_configuration":m.configuration().is_some()})).collect::<Vec<_>>()}),
            )
        }
        Query::Symbols {
            emitted_name,
            identity_kind,
            symbol_kind,
        } => {
            let map: SymbolMap = read(directory, krs_compiler::SYMBOLS_ARTIFACT)?;
            Ok(
                json!({"rows":map.entries().iter().filter(|row|{let kind=match row.identity(){MappedIdentity::Module(_)=>"module",MappedIdentity::Symbol(_)=>"symbol",MappedIdentity::Label(_)=>"label",MappedIdentity::ContextAlias(_)=>"context_alias"};accepts(emitted_name.as_deref(),row.emitted_name())&&accepts(identity_kind.as_deref(),kind)&&symbol_kind.as_ref().is_none_or(|kind|row.symbol_kind().is_some_and(|value|enum_name(&value)==*kind))}).collect::<Vec<_>>()}),
            )
        }
        Query::Sources {
            key,
            node_kind,
            artifact,
        } => {
            let map: SourceMap = read(directory, krs_compiler::SOURCES_ARTIFACT)?;
            let rows=map.entries().iter().filter(|r|accepts(key.as_deref(),r.key().as_str())&&accepts(node_kind.as_deref(),&enum_name(&r.node_kind()))&&artifact.as_ref().is_none_or(|a|r.generated().is_some_and(|g|g.artifact()==a))).map(|row|{let mut fact=encoded(row);fact["authored"]=json!(row.origin().frames().iter().filter_map(|f|match f{OriginFrame::Ranged{kind:RangedOriginKind::Authored,range,..}=>Some(json!({"k_namespace":range.file.package().k_namespace(),"cargo_name":range.file.package().cargo_name(),"package_relative_path":range.file.package_relative_path(),"content_sha256":range.file.content_sha256()})),_=>None}).collect::<Vec<_>>());fact["ranged"]=json!(row.origin().frames().iter().filter_map(|f|match f{OriginFrame::Ranged{kind,range,..}=>Some(json!({"frame_kind":kind,"k_namespace":range.file.package().k_namespace(),"cargo_name":range.file.package().cargo_name(),"package_relative_path":range.file.package_relative_path(),"content_sha256":range.file.content_sha256()})),OriginFrame::Transformation{..}=>None}).collect::<Vec<_>>());fact}).collect::<Vec<_>>();
            Ok(json!({"rows":rows}))
        }
        query => {
            let definition: DefinitionIr = read(directory, krs_compiler::DEFINITION_IR_ARTIFACT)?;
            let context = Context::new(&definition);
            match query {
                Query::Files {} => {
                    let has_claims=definition.modules().iter().flat_map(krs_ir::DefinitionModule::sentences).any(|s|matches!(s,DefinitionSentence::Rule(r) if r.kind()==SentenceKind::Claim));
                    let mut actual = fs::read_dir(directory)?
                        .map(|entry| {
                            entry.map(|entry| entry.file_name().to_string_lossy().into_owned())
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    actual.sort();
                    let owned = fs::read(directory.join(krs_compiler::ARTIFACT_MARKER_FILE))
                        .is_ok_and(|bytes| bytes == krs_compiler::ARTIFACT_MARKER.as_bytes());
                    Ok(
                        json!({"expected":krs_compiler::emitted_artifact_names(has_claims),"actual":actual,"owned":owned,"has_claims":has_claims}),
                    )
                }
                Query::Modules {} => Ok(
                    json!({"main_module":definition.main_module(),"rows":definition.modules().iter().map(|m|json!({"name":m.id(),"imports":definition_module_imports(m)})).collect::<Vec<_>>()}),
                ),
                Query::Sentences {
                    module,
                    sentence_kind: kind,
                    label,
                } => {
                    let sources: SourceMap = read(directory, krs_compiler::SOURCES_ARTIFACT)?;
                    let mut rows = Vec::new();
                    for m in definition.modules() {
                        if !accepts(module.as_deref(), m.id().as_str()) {
                            continue;
                        }
                        for s in m.sentences() {
                            let name = if let DefinitionSentence::Rule(r) = s {
                                Some(r.label().emitted_name())
                            } else {
                                None
                            };
                            if !accepts(kind.as_deref(), sentence_kind(s))
                                || label.as_ref().is_some_and(|l| Some(l.as_str()) != name)
                            {
                                continue;
                            }
                            let (rule_kind, body) = if let DefinitionSentence::Rule(r) = s {
                                (
                                    Some(enum_name(&r.kind())),
                                    rule_body(&context, r.relational_body()),
                                )
                            } else {
                                (None, Value::Null)
                            };
                            let range = sources
                                .entries()
                                .iter()
                                .find(|row| row.key() == s.origin().key())
                                .and_then(krs_compiler::SourceMapEntry::generated);
                            let mut initializers = Vec::new();
                            if let DefinitionSentence::Configuration(c) = s {
                                initializer_rows(&context, c.initializer(), &mut initializers);
                            }
                            rows.push(json!({"module":m.id(),"kind":sentence_kind(s),"label":name,"rule_kind":rule_kind,"source_map_key":s.origin().key(),"generated":range,"body":body,"initializers":initializers,"associativity":match s{DefinitionSentence::Associativity(a)=>Some(a.associativity()),_=>None}}));
                        }
                    }
                    rows.sort_by(|a, b| {
                        let range = |v: &Value| {
                            (
                                v["generated"]["artifact"].as_str().unwrap_or("").to_owned(),
                                v["generated"]["start_byte"].as_u64().unwrap_or(0),
                            )
                        };
                        range(a).cmp(&range(b))
                    });
                    Ok(json!({"rows":rows}))
                }
                Query::Productions {
                    module,
                    sort,
                    symbol,
                } => Ok(
                    json!({"rows":productions(&definition,&context,module.as_deref(),sort.as_deref(),symbol.as_deref())}),
                ),
                Query::Vocabulary {} => Ok(vocabulary(&definition, &context)),
                Query::Applications {
                    operation,
                    symbol,
                    result_sort,
                    argument_sorts,
                    arguments,
                } => {
                    let rows = operations(
                        &definition,
                        &context,
                        &|r| {
                            [
                                (&operation, "operation"),
                                (&symbol, "symbol"),
                                (&result_sort, "result_sort"),
                            ]
                            .iter()
                            .all(|(f, k)| f.as_ref().is_none_or(|v| r[*k] == *v))
                                && argument_sorts
                                    .as_ref()
                                    .is_none_or(|sorts| r["argument_sorts"] == json!(sorts))
                        },
                        true,
                    )
                    .into_iter()
                    .filter(|r| {
                        arguments.as_ref().is_none_or(|patterns| {
                            r["arguments"].as_array().is_some_and(|args| {
                                patterns.len() == args.len()
                                    && patterns.iter().zip(args).all(|(p, a)| p.matches(a))
                            })
                        })
                    })
                    .collect::<Vec<_>>();
                    Ok(json!({"rows":rows}))
                }
                Query::DefinitionShape {} => Ok(definition_shape(&definition)),
                _ => unreachable!("sidecar query was already handled"),
            }
        }
    }
}

fn definition_shape(definition: &DefinitionIr) -> Value {
    let mut value = encoded(definition);
    value["modules"] = json!(definition.modules().iter().map(|module| {
        let mut row = encoded(module);
        row["sentences"] = json!(module.sentences().iter().map(|sentence| {
            if let DefinitionSentence::Rule(rule) = sentence {
                json!({"sentence_kind":"rule", "sentence":{"kind":rule.kind(), "label":rule.label()}})
            } else {
                encoded(sentence)
            }
        }).collect::<Vec<_>>());
        row
    }).collect::<Vec<_>>());
    strip_provenance(&mut value);
    value
}

fn strip_provenance(value: &mut Value) {
    match value {
        Value::Object(object) => {
            for key in ["origin", "name_origin", "here_origin", "initializer_origin"] {
                object.remove(key);
            }
            for v in object.values_mut() {
                strip_provenance(v);
            }
        }
        Value::Array(values) => {
            for v in values {
                strip_provenance(v);
            }
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use krs_ir::testing;
    use krs_ir::{
        ConfigurationRoot, FixedConfiguration, ItemKind, ModuleId, NodeOrigin, PackageId,
        SemanticId, SemanticModule, SemanticProduction, SemanticProductionItem, SemanticRule,
        SemanticSort, SemanticSortRef, SemanticSubsort, SemanticTerm, StableItemId,
        TransformationOriginKind,
    };
    fn package() -> PackageId {
        testing::package("KRS-FOO-BAR", "foo-bar-semantics")
    }

    fn item(module: &str, name: &str, kind: ItemKind) -> StableItemId {
        testing::item_in(package(), module, name, kind)
    }

    fn origin(key: &str) -> NodeOrigin {
        origin_with_label(key, None)
    }

    fn origin_with_label(key: &str, label: Option<&str>) -> NodeOrigin {
        let mut stack = testing::authored_in(package(), "src/lib.rs", testing::digest(), 0, 3);
        stack.push(OriginFrame::Transformation {
            kind: TransformationOriginKind::SemanticIr,
            item: None,
            label: label.map(str::to_owned).or_else(|| Some(key.to_owned())),
        });
        NodeOrigin::new(krs_ir::SourceMapKey::new(key).unwrap(), stack)
    }

    #[allow(clippy::too_many_lines)]
    fn theory() -> SemanticTheory {
        theory_with_claims(false)
    }

    #[allow(clippy::too_many_lines)]
    fn theory_with_claims(with_claims: bool) -> SemanticTheory {
        let k_item = item("syntax", "KItem", ItemKind::Sort);
        let k_result = item("syntax", "KResult", ItemKind::Sort);
        let object = item("syntax", "Obj", ItemKind::Sort);
        let foo_production = item("syntax", "Foo", ItemKind::Constructor);
        let bar = item("syntax", "Bar", ItemKind::Constructor);
        let rule = item("rules", "foo_to_bar", ItemKind::Rule);
        let sorts = vec![
            SemanticSort::new(origin("sem.sort.kitem"), k_item.clone()),
            SemanticSort::new(origin("sem.sort.kresult"), k_result.clone()),
            SemanticSort::new(origin("sem.sort.object"), object.clone()),
        ];
        let subsorts = vec![
            SemanticSubsort::new(
                origin("sem.subsort.kresult-kitem"),
                SemanticSortRef::Declared(k_result.clone()),
                SemanticSortRef::Declared(k_item.clone()),
            ),
            SemanticSubsort::new(
                origin("sem.subsort.object-kresult"),
                SemanticSortRef::Declared(object.clone()),
                SemanticSortRef::Declared(k_result),
            ),
        ];
        let productions = vec![
            SemanticProduction::new(
                origin("sem.production.foo"),
                foo_production.clone(),
                SemanticSortRef::Declared(object.clone()),
                vec![
                    SemanticProductionItem::terminal(origin("sem.production.foo.item"), "foo")
                        .unwrap(),
                ],
                vec![],
            )
            .unwrap(),
            SemanticProduction::new(
                origin("sem.production.bar"),
                bar.clone(),
                SemanticSortRef::Declared(object.clone()),
                vec![
                    SemanticProductionItem::terminal(origin("sem.production.bar.item"), "bar")
                        .unwrap(),
                ],
                vec![],
            )
            .unwrap(),
        ];
        let k_cell = SemanticId::new("machine.k").unwrap();
        let configuration = FixedConfiguration::new(
            origin("sem.configuration"),
            SemanticId::new("machine").unwrap(),
            ConfigurationRoot::GeneratedTop,
            vec![
                FixedCell::leaf(
                    origin("sem.cell.k"),
                    k_cell.clone(),
                    "k",
                    vec![],
                    SemanticSortRef::k_sequence(),
                )
                .unwrap(),
            ],
            origin("sem.initializer"),
            SemanticId::new("machine.init").unwrap(),
            vec![],
            vec![FixedInitializerCell::term(
                origin("sem.initializer.k"),
                k_cell,
                SemanticTerm::k_sequence(
                    origin("sem.term.init.sequence"),
                    SemanticSortRef::Declared(k_item.clone()),
                    vec![SemanticTerm::application(
                        origin("sem.term.init.foo"),
                        SemanticSortRef::Declared(object.clone()),
                        ApplicationRef::Declared(foo_production.clone()),
                        vec![],
                    )],
                ),
            )],
        )
        .unwrap();
        let rewrite = SemanticTerm::rewrite(
            origin("sem.term.rule.rewrite"),
            SemanticSortRef::Declared(object.clone()),
            SemanticTerm::application(
                origin("sem.term.rule.foo"),
                SemanticSortRef::Declared(object.clone()),
                ApplicationRef::Declared(foo_production),
                vec![],
            ),
            SemanticTerm::application(
                origin("sem.term.rule.bar"),
                SemanticSortRef::Declared(object),
                ApplicationRef::Declared(bar),
                vec![],
            ),
        )
        .unwrap();
        let rule = SemanticRule::new(
            origin("sem.rule.foo-to-bar"),
            rule,
            SentenceKind::Transition,
            vec![],
            rewrite,
        )
        .unwrap();
        let mut rules = vec![rule];
        if with_claims {
            for label in ["z-last", "a-first"] {
                let key = |suffix: &str| format!("claim.{label}.{suffix}");
                let claim = SemanticRule::new_configuration(
                    origin(&key("sentence")),
                    item("claims", label, ItemKind::Claim),
                    SentenceKind::Claim,
                    vec![],
                    krs_ir::FixedConfigurationRewrite::new(
                        origin(&key("rewrite")),
                        SemanticId::new("machine").unwrap(),
                        vec![krs_ir::FixedCellClause::new(
                            origin(&key("cell")),
                            SemanticId::new("machine.k").unwrap(),
                            SemanticTerm::k_sequence(
                                origin(&key("empty")),
                                SemanticSortRef::Declared(k_item.clone()),
                                vec![],
                            ),
                            CellPost::Preserve,
                            krs_ir::CellContentFrame::Exact,
                        )],
                        vec![],
                    )
                    .unwrap(),
                )
                .unwrap()
                .with_label(Some(
                    krs_ir::SemanticRuleLabel::new(origin(&key("label")), label).unwrap(),
                ))
                .with_claim(Some(krs_ir::SemanticClaim::new(
                    origin(&key("modality")),
                    krs_ir::ClaimModality::AllPaths,
                    None,
                    vec![],
                    vec![],
                    None,
                )));
                rules.push(claim);
            }
        }
        SemanticTheory::new(vec![SemanticModule::new(
            origin("sem.module.main"),
            ModuleId::new("KRS-FOO-BAR").unwrap(),
            vec![],
            sorts,
            subsorts,
            productions,
            vec![],
            vec![],
            Some(configuration),
            rules,
        )])
        .unwrap()
    }
    fn artifacts() -> krs_test_support::TempDir {
        artifacts_with_claims(false)
    }

    fn artifacts_with_claims(with_claims: bool) -> krs_test_support::TempDir {
        let directory = krs_test_support::temp_dir();
        let theory = if with_claims {
            theory_with_claims(true)
        } else {
            theory()
        };
        let lowered = krs_compiler::lower_semantic_theory(&theory).unwrap();
        let emitted = krs_compiler::emit_k(&lowered).unwrap();
        let files = [
            (
                krs_compiler::DEFINITION_IR_ARTIFACT,
                lowered.definition().to_canonical_json().unwrap(),
            ),
            (
                krs_compiler::SEMANTIC_ARTIFACT,
                theory.to_canonical_json().unwrap(),
            ),
            (krs_compiler::DESCRIPTOR_ARTIFACT, {
                let key = krs_ir::ProvenanceKey::new(krs_ir::ProvenanceRole::SortDeclaration, 0);
                let descriptor = krs_ir::Descriptor {
                    id: item("syntax", "Obj", ItemKind::Sort),
                    cfg: BTreeMap::new(),
                    provenance: krs_ir::DescriptorProvenance::new(
                        key.clone(),
                        vec![krs_ir::DescriptorNodeOrigin::new(
                            key,
                            testing::authored_in(package(), "src/lib.rs", testing::digest(), 0, 3),
                        )],
                    )
                    .unwrap(),
                    payload: DescriptorPayload::Sort(krs_ir::SortDescriptor {
                        parents: BTreeSet::new(),
                    }),
                };
                DescriptorBundle::new(vec![descriptor])
                    .to_canonical_json()
                    .unwrap()
            }),
            (
                krs_compiler::SYMBOLS_ARTIFACT,
                emitted.symbol_map().to_canonical_json().unwrap(),
            ),
            (
                krs_compiler::SOURCES_ARTIFACT,
                emitted.source_map().to_canonical_json().unwrap(),
            ),
            (
                krs_compiler::DEFINITION_ARTIFACT,
                emitted.source().to_owned(),
            ),
            (
                krs_compiler::ARTIFACT_MARKER_FILE,
                krs_compiler::ARTIFACT_MARKER.to_owned(),
            ),
        ];
        if let Some(spec) = emitted.spec() {
            fs::write(
                directory.path().join(krs_compiler::SPEC_ARTIFACT),
                spec.source(),
            )
            .unwrap();
        }
        for (name, source) in files {
            fs::write(directory.path().join(name), source).unwrap();
        }
        directory
    }
    #[test]
    fn queries_read_typed_artifacts_and_project_all_kinds() {
        let directory = artifacts();
        let read = |q| query(directory.path(), &q).unwrap();
        let files = read(json!({"kind":"files"}));
        assert_eq!(files["expected"], files["actual"]);
        assert_eq!(files["owned"], true);
        assert_eq!(files["has_claims"], false);
        let modules = read(json!({"kind":"modules"}));
        assert_eq!(modules["main_module"], "KRS-FOO-BAR");
        assert_eq!(modules["rows"].as_array().unwrap().len(), 1);
        let semantic = read(json!({"kind":"semantic_modules"}));
        assert_eq!(semantic["rows"][0]["production_count"], 2);
        assert_eq!(semantic["rows"][0]["rule_count"], 1);
        let sentences = read(json!({"kind":"sentences","sentence_kind":"rule"}));
        assert_eq!(sentences["rows"].as_array().unwrap().len(), 1);
        assert_eq!(sentences["rows"][0]["body"]["kind"], "rewrite");
        assert_eq!(
            sentences["rows"][0]["generated"]["artifact"],
            "definition.k"
        );
        let productions = read(json!({"kind":"productions"}));
        assert_eq!(productions["rows"].as_array().unwrap().len(), 2);
        assert!(
            productions["rows"]
                .as_array()
                .unwrap()
                .iter()
                .any(|p| p["terminals"] == json!(["foo"]))
        );
        let vocabulary = read(json!({"kind":"vocabulary"}));
        assert_eq!(vocabulary["sorts"].as_array().unwrap().len(), 3);
        assert_eq!(vocabulary["cells"][0]["name"], "k");
        assert_eq!(vocabulary["subsorts"].as_array().unwrap().len(), 2);
        let apps = read(json!({"kind":"applications","arguments":[]}));
        assert_eq!(apps["rows"].as_array().unwrap().len(), 2);
        assert!(
            read(json!({"kind":"applications","arguments":[{}]}))["rows"]
                .as_array()
                .unwrap()
                .is_empty()
        );
        let descriptors =
            read(json!({"kind":"descriptors","descriptor_kind":"sort","item_kind":"sort"}));
        assert_eq!(descriptors["counts"]["descriptor_kind"]["sort"], 1);
        assert_eq!(descriptors["counts"]["item_kind"]["sort"], 1);
        assert_eq!(descriptors["rows"][0]["cargo_name"], "foo-bar-semantics");
        assert_eq!(
            read(json!({"kind":"symbols","identity_kind":"label"}))["rows"]
                .as_array()
                .unwrap()
                .len(),
            1
        );
        let sources = read(json!({"kind":"sources","node_kind":"rule","artifact":"definition.k"}));
        assert_eq!(sources["rows"].as_array().unwrap().len(), 1);
        assert_eq!(
            sources["rows"][0]["authored"][0]["cargo_name"],
            "foo-bar-semantics"
        );
        assert_eq!(sources["rows"][0]["ranged"][0]["frame_kind"], "authored");
        let shape = read(json!({"kind":"definition_shape"}));
        assert_eq!(shape["main_module"], "KRS-FOO-BAR");
        assert!(
            !serde_json::to_string(&shape)
                .unwrap()
                .contains("start_byte")
        );
    }
    #[test]
    fn descriptor_and_symbol_projections_are_closed_and_filtered() {
        let dir = artifacts();
        let details = query(
            dir.path(),
            &json!({"kind":"descriptor_details","module_path":["syntax"],"item_name":"Obj"}),
        )
        .unwrap();
        assert_eq!(details["rows"].as_array().unwrap().len(), 1);
        assert_eq!(
            details["rows"][0]["visibility"],
            json!({"visibility":"inherited"})
        );
        assert_eq!(
            details["rows"][0]["normalized"]["id"]["package"],
            json!({"k_namespace":"KRS-FOO-BAR"})
        );
        assert!(details["rows"][0]["normalized"].get("provenance").is_none());
        assert_eq!(
            query(
                dir.path(),
                &json!({"kind":"descriptor_details","public_only":true})
            )
            .unwrap()["rows"],
            json!([])
        );
        let bundle: DescriptorBundle = read(dir.path(), "descriptor-bundle.json").unwrap();
        let mut descriptor = bundle.descriptors[0].clone();
        let mut origins = descriptor.provenance.origins().to_vec();
        origins.push(krs_ir::DescriptorNodeOrigin::new(
            krs_ir::ProvenanceKey::new(krs_ir::ProvenanceRole::StableSymbol, 0),
            testing::authored_in(package(), "src/lib.rs", testing::digest(), 0, 3),
        ));
        descriptor.provenance =
            krs_ir::DescriptorProvenance::new(descriptor.provenance.primary_key().clone(), origins)
                .unwrap();
        let declaration = krs_ir::DescriptorDeclaration::new(
            descriptor.id.clone(),
            krs_ir::RustVisibility::Public,
            Some(krs_ir::ExplicitSymbol::new("api::Obj").unwrap()),
        );
        let bundle =
            DescriptorBundle::with_declarations(vec![descriptor], vec![declaration]).unwrap();
        fs::write(
            dir.path().join("descriptor-bundle.json"),
            bundle.to_canonical_json().unwrap(),
        )
        .unwrap();
        let public = query(
            dir.path(),
            &json!({"kind":"descriptor_details","public_only":true}),
        )
        .unwrap();
        assert_eq!(public["rows"][0]["explicit_symbol"], "api::Obj");
        assert_eq!(
            public["rows"][0]["visibility"],
            json!({"visibility":"public"})
        );
        let symbols = query(
            dir.path(),
            &json!({"kind":"symbol_projection","emitted_names":["foo"]}),
        )
        .unwrap();
        assert_eq!(symbols["rows"].as_array().unwrap().len(), 1);
        assert_eq!(symbols["source_keys"].as_array().unwrap().len(), 1);
        assert!(
            query(
                dir.path(),
                &json!({"kind":"descriptor_details","unknown":true})
            )
            .is_err()
        );
        assert!(
            query(
                dir.path(),
                &json!({"kind":"symbol_projection","emitted_names":[],"unknown":true})
            )
            .is_err()
        );
    }

    #[test]
    fn exact_source_token_uses_unique_diagnostic_translation() {
        use sha2::{Digest, Sha256};
        let dir = krs_test_support::temp_dir();
        let authored = dir.path().join("authored.rs");
        fs::write(&authored, "before Exact after").unwrap();
        fs::write(dir.path().join("spec.k"), "claim exact\n").unwrap();
        let digest =
            krs_ir::Sha256Digest::new(krs_ir::lower_hex(&Sha256::digest(b"before Exact after")))
                .unwrap();
        let origin = testing::authored_in(package(), "src/lib.rs", digest, 7, 12);
        let entry = json!({"key":"exact.token","node_kind":"term","origin":origin,"generated":{
            "artifact":"spec.k","start_byte":6,"end_byte":11,"start_line":1,"start_column":7,"end_line":1,"end_column":12,
        }});
        let write = |entries: Vec<Value>| {
            fs::write(
                dir.path().join("sources.json"),
                json!({"schema_version":2,"entries":entries}).to_string(),
            )
            .unwrap();
        };
        write(vec![entry.clone()]);
        let request = json!({"kind":"source_token","authored":authored,"package_relative_path":"src/lib.rs","token":"Exact","artifact":"spec.k"});
        let result = query(dir.path(), &request).unwrap();
        assert_eq!(result["authored_range"]["start_byte"], 7);
        assert_eq!(result["generated"]["start_byte"], 6);
        let mut surrounding = entry.clone();
        surrounding["key"] = json!("surrounding.condition");
        surrounding["origin"][0]["range"]["end_byte"] = json!(18);
        write(vec![entry.clone(), surrounding]);
        assert_eq!(query(dir.path(), &request).unwrap(), result);
        fs::write(&authored, "before Wrong after").unwrap();
        assert!(query(dir.path(), &request).is_err());
        fs::write(&authored, "before Exact after").unwrap();
        let mut duplicate = entry.clone();
        duplicate["key"] = json!("duplicate.token");
        write(vec![entry.clone(), duplicate]);
        assert!(query(dir.path(), &request).is_err());
        let mut ambiguous = entry;
        ambiguous["origin"]
            .as_array_mut()
            .unwrap()
            .push(encoded(origin.frames().first().unwrap()));
        write(vec![ambiguous]);
        assert!(query(dir.path(), &request).is_err());
    }

    #[test]
    fn replacement_projection_preserves_sentence_multiplicity_and_changes() {
        let left = artifacts();
        let right = artifacts();
        let request = json!({"kind":"replacement_parity","reference":left.path(),"module":"KRS-FOO-BAR","module_path":["syntax"]});
        let facts = query(right.path(), &request).unwrap();
        assert_eq!(facts["non_rule_counts"], json!({"sort":1}));
        assert_eq!(facts["non_rule_count"], 1);
        assert_eq!(facts["reference_rules"], json!({}));
        assert!(facts["sentence_count"].as_u64().unwrap() > 1);
        let path = right.path().join("definition-ir.json");
        let mut definition =
            encoded(&read::<DefinitionIr>(right.path(), "definition-ir.json").unwrap());
        let rule = definition["modules"][0]["sentences"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|s| s["sentence_kind"] == "rule")
            .unwrap();
        rule["sentence"]["label"]["emitted_name"] = json!("changed-label");
        fs::write(path, definition.to_string()).unwrap();
        assert!(
            query(right.path(), &request)
                .unwrap_err()
                .to_string()
                .contains("sentence multiset")
        );
    }

    #[test]
    fn replacement_subsort_names_follow_distinct_typed_relations() {
        use krs_ir::{
            DescriptorSortRef, DescriptorSortReference, GrammarDescriptor, ProvenanceKey,
            ProvenanceRole,
        };
        let left = artifacts();
        let right = artifacts();
        let key = |role| ProvenanceKey::new(role, 0);
        let descriptors = |prefix: &str| {
            ["Obj", "KResult"]
                .iter()
                .enumerate()
                .map(|(i, sort)| {
                    let roles = [
                        ProvenanceRole::SubsortDeclaration,
                        ProvenanceRole::SubsortSubSort,
                        ProvenanceRole::SubsortSuperSort,
                    ];
                    krs_ir::Descriptor {
                        id: item("syntax", &format!("{prefix}_{i}"), ItemKind::Grammar),
                        cfg: BTreeMap::new(),
                        provenance: krs_ir::DescriptorProvenance::new(
                            key(roles[0]),
                            roles
                                .iter()
                                .map(|role| {
                                    krs_ir::DescriptorNodeOrigin::new(
                                        key(*role),
                                        testing::authored_in(
                                            package(),
                                            "src/lib.rs",
                                            testing::digest(),
                                            0,
                                            3,
                                        ),
                                    )
                                })
                                .collect(),
                        )
                        .unwrap(),
                        payload: DescriptorPayload::Grammar(Box::new(GrammarDescriptor::Subsort {
                            key: key(roles[0]),
                            subsort: DescriptorSortReference {
                                key: key(roles[1]),
                                sort: DescriptorSortRef::Declared(item(
                                    "syntax",
                                    sort,
                                    ItemKind::Sort,
                                )),
                            },
                            supersort: DescriptorSortReference {
                                key: key(roles[2]),
                                sort: DescriptorSortRef::Declared(item(
                                    "syntax",
                                    "KItem",
                                    ItemKind::Sort,
                                )),
                            },
                        })),
                    }
                })
                .collect::<Vec<_>>()
        };
        for (dir, prefix) in [(&left, "generated_span"), (&right, "readable")] {
            fs::write(
                dir.path().join("descriptor-bundle.json"),
                DescriptorBundle::new(descriptors(prefix))
                    .to_canonical_json()
                    .unwrap(),
            )
            .unwrap();
        }
        let request = json!({"kind":"replacement_parity","reference":left.path(),"module":"KRS-FOO-BAR","module_path":["syntax"]});
        let result = query(right.path(), &request).unwrap();
        assert_eq!(result["subsort_count"], 2);
        assert_eq!(result["non_rule_counts"], json!({"grammar":2}));
        let mut changed = descriptors("readable");
        let DescriptorPayload::Grammar(grammar) = &mut changed[0].payload else {
            unreachable!()
        };
        let GrammarDescriptor::Subsort { supersort, .. } = &mut **grammar else {
            unreachable!()
        };
        supersort.sort = DescriptorSortRef::Builtin(krs_ir::BuiltinSort::Int);
        fs::write(
            right.path().join("descriptor-bundle.json"),
            DescriptorBundle::new(changed).to_canonical_json().unwrap(),
        )
        .unwrap();
        assert!(
            query(right.path(), &request)
                .unwrap_err()
                .to_string()
                .contains("non-rule descriptors")
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn replacement_frame_normalization_is_limited_to_the_old_transport_shapes() {
        let lowered = krs_compiler::lower_semantic_theory(&theory()).unwrap();
        let definition = lowered.definition();
        let mut context = Context::new(definition);
        let cell = *context
            .cells
            .iter()
            .find(|(_, name)| **name == "k")
            .unwrap()
            .0;
        let ordinary = definition.modules()[0]
            .sentences()
            .iter()
            .find_map(|s| match s {
                DefinitionSentence::Rule(r) => Some(r),
                _ => None,
            })
            .unwrap();
        let DefinitionRuleBody::Term(rewrite) = ordinary.relational_body() else {
            unreachable!()
        };
        let DefinitionTermKind::Rewrite { from, to } = rewrite.kind() else {
            unreachable!()
        };
        let make = |frame: krs_ir::CellContentFrame, after: CellPost<DefinitionTerm>| {
            DefinitionSentence::Rule(krs_ir::RuleSentence::new_configuration(
                ordinary.origin().clone(),
                ordinary.label().clone(),
                ordinary.kind(),
                vec![krs_ir::DefinitionVariable::new(
                    SemanticId::new("tail").unwrap(),
                    DefinitionSortRef::k_sequence(),
                )],
                krs_ir::FixedConfigurationRewrite::new(
                    origin("test.rewrite"),
                    SemanticId::new("machine").unwrap(),
                    vec![krs_ir::FixedCellClause::new(
                        origin("test.clause"),
                        (*cell).clone(),
                        DefinitionTerm::k_sequence(
                            origin("test.before"),
                            from.sort().clone(),
                            vec![(**from).clone()],
                        ),
                        after,
                        frame,
                    )],
                    vec![],
                )
                .unwrap(),
            ))
        };
        let tail = || krs_ir::CellContentFrame::KSequenceTail {
            origin: origin("test.frame"),
            binding: Some(SemanticId::new("tail").unwrap()),
        };
        let replace = || CellPost::Replace {
            term: DefinitionTerm::k_sequence(
                origin("test.after"),
                to.sort().clone(),
                vec![(**to).clone()],
            ),
        };
        let input = make(tail(), replace());
        let normalized = encoded(&projections::frame_normalized(&input, &context).unwrap());
        assert!(
            normalized["sentence"]["body"]["clauses"][0]["frame"]
                .get("binding")
                .is_none()
        );
        assert_eq!(normalized["sentence"]["variables"], json!([]));
        let left = artifacts();
        let right = artifacts();
        for (dir, sentence) in [(&left, normalized.clone()), (&right, encoded(&input))] {
            let mut value = encoded(definition);
            let rule = value["modules"][0]["sentences"]
                .as_array_mut()
                .unwrap()
                .iter_mut()
                .find(|s| s["sentence_kind"] == "rule")
                .unwrap();
            *rule = sentence;
            fs::write(dir.path().join("definition-ir.json"), value.to_string()).unwrap();
        }
        assert!(query(right.path(), &json!({"kind":"replacement_parity","reference":left.path(),"module":"KRS-FOO-BAR","module_path":["syntax"]})).is_ok());
        let preserved = make(tail(), CellPost::Preserve);
        assert_eq!(
            projections::frame_normalized(&preserved, &context).unwrap(),
            preserved
        );
        context.cells.insert(cell, "env");
        let map = || krs_ir::CellContentFrame::MapRemainder {
            origin: origin("test.frame"),
            binding: Some(SemanticId::new("tail").unwrap()),
        };
        let preserved = make(map(), CellPost::Preserve);
        assert!(encoded(&projections::frame_normalized(&preserved,&context).unwrap())["sentence"]["body"]["clauses"][0]["frame"].get("binding").is_none());
        let replaced = make(map(), replace());
        assert_eq!(
            projections::frame_normalized(&replaced, &context).unwrap(),
            replaced
        );
        context.cells.insert(cell, "other");
        assert_eq!(
            projections::frame_normalized(&input, &context).unwrap(),
            input
        );
    }

    #[test]
    fn head_rule_walkthrough_projects_typed_named_and_positional_arguments() {
        use krs_ir::{
            DescriptorApplicationRef, DescriptorApplicationReference, DescriptorHeadRule,
            DescriptorHeadRuleBinding, DescriptorHeadRuleResult, DescriptorTerm,
            DescriptorTermArgument, ProvenanceKey, ProvenanceRole,
        };
        let dir = artifacts();
        let original: DescriptorBundle = read(dir.path(), "descriptor-bundle.json").unwrap();
        let mut descriptor = original.descriptors[0].clone();
        let key = |role| ProvenanceKey::new(role, 0);
        let var = |name: &str| DescriptorTerm::Variable {
            key: key(ProvenanceRole::RuleLeftReference),
            path_key: key(ProvenanceRole::RuleLeftReference),
            name: name.into(),
        };
        let application = |head, args| DescriptorTerm::Application {
            head_class: krs_ir::DescriptorApplicationHeadClass::Applied,
            reference: DescriptorApplicationReference {
                key: key(ProvenanceRole::RuleLeftReference),
                application: head,
            },
            path_key: key(ProvenanceRole::RuleLeftReference),
            arguments: args,
        };
        let config = item("machine", "Machine", ItemKind::Configuration);
        descriptor.id = item("rules", "eval_add", ItemKind::Rule);
        descriptor.payload = DescriptorPayload::HeadRule(Box::new(DescriptorHeadRule {
            sentence_kind: SentenceKind::Transition,
            label: Some(krs_ir::DescriptorRuleLabel {
                key: key(ProvenanceRole::RuleLabel),
                name: "eval-add".into(),
            }),
            priority: None,
            pattern_key: key(ProvenanceRole::RulePattern),
            result_key: key(ProvenanceRole::RuleResult),
            head_sort: None,
            configuration: config.clone(),
            computation_cell: krs_ir::DescriptorCellReference {
                key: key(ProvenanceRole::RuleLeftCellsField),
                cell: krs_ir::DescriptorCellIdentity {
                    owner: config,
                    field: "k".into(),
                },
            },
            bindings: vec![
                DescriptorHeadRuleBinding {
                    name: "lhs".into(),
                    refinement: None,
                },
                DescriptorHeadRuleBinding {
                    name: "rhs".into(),
                    refinement: None,
                },
            ],
            subject: application(
                DescriptorApplicationRef::Declared(item("syntax", "Add", ItemKind::Constructor)),
                ["lhs", "rhs"]
                    .iter()
                    .map(|name| DescriptorTermArgument::Named {
                        key: key(ProvenanceRole::RuleLeftReference),
                        field: krs_ir::ProductionFieldId::new(*name).unwrap(),
                        value: Box::new(var(name)),
                    })
                    .collect(),
            ),
            result: DescriptorHeadRuleResult::Replace(application(
                DescriptorApplicationRef::Builtin(krs_ir::BuiltinOperation::IntAdd),
                ["lhs", "rhs"]
                    .iter()
                    .map(|name| DescriptorTermArgument::Positional {
                        value: Box::new(var(name)),
                    })
                    .collect(),
            )),
            requires: None,
            extras: vec![],
        }));
        fs::write(
            dir.path().join("descriptor-bundle.json"),
            DescriptorBundle::new(vec![descriptor])
                .to_canonical_json()
                .unwrap(),
        )
        .unwrap();
        let request = json!({"kind":"head_rule_walkthrough","item_name":"eval_add"});
        let value = query(dir.path(), &request).unwrap();
        assert_eq!(
            value,
            json!({"id":"eval_add","kind":"head_rule","sentence_kind":"transition","label":"eval-add","configuration":"Machine","cell":"k","bindings":["lhs","rhs"],"subject":{"application":"Add","arguments":["lhs","rhs"]},"result":{"application":"builtin:int_add","arguments":["lhs","rhs"]}})
        );
        assert!(
            query(
                dir.path(),
                &json!({"kind":"head_rule_walkthrough","item_name":"absent"})
            )
            .is_err()
        );
    }

    #[test]
    fn definition_shape_ignores_explicit_rule_tail_bindings() {
        let lowered = krs_compiler::lower_semantic_theory(&theory()).unwrap();
        let definition = lowered.definition();
        let modules = definition
            .modules()
            .iter()
            .map(|module| {
                let sentences = module
                    .sentences()
                    .iter()
                    .map(|sentence| {
                        if let DefinitionSentence::Rule(rule) = sentence {
                            let DefinitionRuleBody::Term(body) = rule.relational_body() else {
                                panic!("fixture has an ordinary rewrite");
                            };
                            let tail = SemanticId::new("tail").unwrap();
                            let sort = DefinitionSortRef::k_sequence();
                            let variables =
                                vec![krs_ir::DefinitionVariable::new(tail.clone(), sort.clone())];
                            let body = DefinitionTerm::rewrite(
                                body.origin().clone(),
                                sort.clone(),
                                DefinitionTerm::variable(
                                    origin("tail.before"),
                                    sort.clone(),
                                    tail.clone(),
                                ),
                                DefinitionTerm::variable(origin("tail.after"), sort, tail),
                            )
                            .unwrap();
                            DefinitionSentence::Rule(
                                krs_ir::RuleSentence::new(
                                    rule.origin().clone(),
                                    rule.label().clone(),
                                    rule.kind(),
                                    variables,
                                    body,
                                )
                                .unwrap(),
                            )
                        } else {
                            sentence.clone()
                        }
                    })
                    .collect();
                krs_ir::DefinitionModule::new(
                    module.origin().clone(),
                    module.id().clone(),
                    module.imports().iter().cloned().collect(),
                    module.production_groups().to_vec(),
                    sentences,
                )
            })
            .collect();
        let expanded = DefinitionIr::new(definition.main_module().clone(), modules).unwrap();
        assert_ne!(encoded(definition), encoded(&expanded));
        assert_eq!(definition_shape(definition), definition_shape(&expanded));
        let shape = definition_shape(definition);
        let configuration = shape["modules"][0]["sentences"]
            .as_array()
            .unwrap()
            .iter()
            .find(|sentence| sentence["sentence_kind"] == "configuration")
            .unwrap();
        assert!(configuration["sentence"].get("initializer").is_some());
    }

    #[test]
    fn claim_rows_follow_emitted_order_and_slice_exact_spec_sentences() {
        let directory = artifacts_with_claims(true);
        let files = query(directory.path(), &json!({"kind":"files"})).unwrap();
        assert_eq!(files["has_claims"], true);
        assert_eq!(files["expected"], files["actual"]);
        let claims = query(
            directory.path(),
            &json!({"kind":"sentences","sentence_kind":"claim"}),
        )
        .unwrap();
        let rows = claims["rows"].as_array().unwrap();
        assert_eq!(
            rows.iter()
                .map(|r| r["label"].as_str().unwrap())
                .collect::<Vec<_>>(),
            vec!["a-first", "z-last"]
        );
        let source = fs::read(directory.path().join(krs_compiler::SPEC_ARTIFACT)).unwrap();
        for row in rows {
            let range = &row["generated"];
            assert_eq!(range["artifact"], "spec.k");
            let start = usize::try_from(range["start_byte"].as_u64().unwrap()).unwrap();
            let end = usize::try_from(range["end_byte"].as_u64().unwrap()).unwrap();
            let excerpt = std::str::from_utf8(&source[start..end]).unwrap();
            assert!(excerpt.starts_with(&format!("  claim [{}]:", row["label"].as_str().unwrap())));
            assert!(excerpt.ends_with('\n'));
        }
        assert_eq!(
            rows[0]["generated"]["end_byte"],
            rows[1]["generated"]["start_byte"]
        );
    }

    #[test]
    fn queries_reject_unknown_fields_and_read_only_required_files() {
        let directory = artifacts();
        for q in [
            json!({"kind":"files","extra":true}),
            json!({"kind":"productions","unknown":false}),
            json!({"kind":"applications","arguments":[{"extra":false}]}),
            json!({"kind":"missing"}),
        ] {
            assert!(
                query(directory.path(), &q).is_err(),
                "unexpected accepted query: {q}"
            );
        }
        fs::remove_file(directory.path().join(krs_compiler::DEFINITION_IR_ARTIFACT)).unwrap();
        assert!(query(directory.path(), &json!({"kind":"symbols"})).is_ok());
        assert!(query(directory.path(), &json!({"kind":"sources"})).is_ok());
        assert!(query(directory.path(), &json!({"kind":"descriptors"})).is_ok());
        assert!(query(directory.path(), &json!({"kind":"modules"})).is_err());
    }
    #[test]
    fn recursive_term_patterns_match_only_declared_facts() {
        let p: TermPattern = serde_json::from_value(
            json!({"symbol":"wrappingRange","arguments":[{"token":"1"},{"token":"0"}]}),
        )
        .unwrap();
        assert!(p.matches(&json!({"kind":"application","symbol":"wrappingRange","arguments":[{"kind":"token","token":"1"},{"kind":"token","token":"0"}]})));
        assert!(
            !p.matches(
                &json!({"symbol":"wrappingRange","arguments":[{"token":"0"},{"token":"1"}]})
            )
        );
    }
}
