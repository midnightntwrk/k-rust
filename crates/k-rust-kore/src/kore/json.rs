//! KORE JSON version 1 serialization.
//!
//! The text, JSON, and binary codecs and every traversal of [`Pattern`] are iterative and impose no depth limit.
//! Host APIs likewise apply no deliberate parser depth cap, but host envelopes that retain [`serde_json::Value`] remain bounded by their thread's native stack during value serialization and destruction.
//! KAST term traits and text codecs, backend pattern internalization, and backend term passes retain their own native-stack bounds.
//!
//! ```toml algorithm
//! id = "kore.json.encode_source"
//! name = "encode KORE JSON from a pattern source"
//! sites = ["to_value_source", "source_to_string", "pattern_fields"]
//! variable = "p = expanded KORE pattern nodes"
//! counters = []
//! no_counter = "observation JSON counts are recorded by its backend caller"
//!
//! [[cost]]
//! mode = "one JSON value"
//! bound = "O(p) source reads and JSON nodes; the returned JSON value has O(p) space"
//!
//! [[cost]]
//! mode = "one compact JSON string"
//! bound = "O(p) source reads and output bytes; the stack follows source depth and the returned string holds output bytes"
//! ```

use crate::json_tree::{self, Node};
use smallvec::{SmallVec, smallvec};
use std::borrow::Cow;

use super::{
    ast::{Associativity, KoreString, Pattern, Sort, Symbol, Variable, VariableKind},
    lexical::{self, Problem},
    node::{PatternNode, PatternSource},
};

pub const FORMAT: &str = "KORE";
pub const VERSION: u32 = 1;

#[derive(Debug)]
pub enum Error {
    Syntax {
        line: usize,
        column: usize,
        message: String,
    },
    Shape(String),
    Lexical {
        kind: &'static str,
        text: String,
        problems: Vec<Problem>,
    },
    UnsupportedFormat(String),
    UnsupportedVersion(u32),
    EmptyAssociativeApplication,
    EmptyMultiOr,
}

impl std::fmt::Display for Error {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Syntax {
                line,
                column,
                message,
            } => write!(formatter, "{message} at line {line} column {column}"),
            Self::Shape(message) => formatter.write_str(message),
            Self::Lexical {
                kind,
                text,
                problems,
            } => {
                write!(
                    formatter,
                    "Lexical {} in {kind} : {text}",
                    if problems.len() == 1 {
                        "error"
                    } else {
                        "errors"
                    }
                )?;
                for problem in problems {
                    write!(formatter, " * {problem}")?;
                }
                Ok(())
            }
            Self::UnsupportedFormat(format) => {
                write!(formatter, "unsupported KORE JSON format {format:?}")
            }
            Self::UnsupportedVersion(version) => {
                write!(formatter, "unsupported KORE JSON version {version}")
            }
            Self::EmptyAssociativeApplication => {
                formatter.write_str("associative application requires at least one argument")
            }
            Self::EmptyMultiOr => formatter.write_str("MultiOr requires at least one argument"),
        }
    }
}

impl std::error::Error for Error {}

impl From<json_tree::Error> for Error {
    fn from(error: json_tree::Error) -> Self {
        Self::Syntax {
            line: error.line,
            column: error.column,
            message: error.message,
        }
    }
}

struct Fields {
    values: Vec<(String, Node)>,
}

impl Fields {
    fn new(node: Node) -> Result<Self, Error> {
        let kind = node.kind();
        Ok(Self {
            values: node
                .into_object()
                .ok_or_else(|| Error::Shape(format!("invalid type: {kind}, expected an object")))?,
        })
    }

    fn take(&mut self, name: &str) -> Option<Node> {
        self.values
            .iter()
            .position(|(key, _)| key == name)
            .map(|index| self.values.swap_remove(index).1)
    }

    fn required(&mut self, name: &str) -> Result<Node, Error> {
        self.take(name)
            .ok_or_else(|| Error::Shape(format!("missing field `{name}`")))
    }

    fn string(&mut self, name: &str) -> Result<String, Error> {
        expect_string(self.required(name)?, name)
    }

    fn array(&mut self, name: &str) -> Result<Vec<Node>, Error> {
        expect_array(self.required(name)?, name)
    }

    fn finish(self) -> Result<(), Error> {
        if let Some((name, _)) = self.values.first() {
            Err(Error::Shape(format!("unknown field `{name}`")))
        } else {
            Ok(())
        }
    }
}

fn expect_string(node: Node, field: &str) -> Result<String, Error> {
    let kind = node.kind();
    node.into_string().ok_or_else(|| {
        Error::Shape(format!(
            "invalid type: {kind}, expected a string for field `{field}`"
        ))
    })
}

fn expect_array(node: Node, field: &str) -> Result<Vec<Node>, Error> {
    let kind = node.kind();
    node.into_array().ok_or_else(|| {
        Error::Shape(format!(
            "invalid type: {kind}, expected an array for field `{field}`"
        ))
    })
}

fn expect_u32(mut node: Node, field: &str) -> Result<u32, Error> {
    let kind = node.kind();
    let value = match &mut node {
        Node::Number(value) => std::mem::take(value),
        _ => {
            return Err(Error::Shape(format!(
                "invalid type: {kind}, expected u32 for field `{field}`"
            )));
        }
    };
    value.parse().map_err(|_| {
        Error::Shape(format!(
            "invalid value: {value}, expected u32 for field `{field}`"
        ))
    })
}

fn require_lexical(kind: &'static str, text: &str, problems: Vec<Problem>) -> Result<(), Error> {
    if problems.is_empty() {
        Ok(())
    } else {
        Err(Error::Lexical {
            kind,
            text: text.to_owned(),
            problems,
        })
    }
}

pub fn from_str(input: &str) -> Result<Pattern, Error> {
    let root = json_tree::parse(input)?;
    let mut envelope = Fields::new(root)?;
    let format = envelope.string("format")?;
    let version = expect_u32(envelope.required("version")?, "version")?;
    let term = envelope.required("term")?;
    // Version-one producers are allowed to attach metadata beside the envelope.
    if format != FORMAT {
        return Err(Error::UnsupportedFormat(format));
    }
    if version != VERSION {
        return Err(Error::UnsupportedVersion(version));
    }
    build_pattern(term)
}

/// Compatibility alias for the now-unbounded from_str.
#[deprecated(note = "from_str has no depth limit")]
pub fn from_str_unbounded(input: &str) -> Result<Pattern, Error> {
    from_str(input)
}

pub fn to_string(pattern: &Pattern) -> Result<String, Error> {
    Ok(json_tree::to_string(&source_to_node(pattern), false))
}

pub fn to_string_pretty(pattern: &Pattern) -> Result<String, Error> {
    Ok(json_tree::to_string(&source_to_node(pattern), true))
}

pub fn to_value(pattern: &Pattern) -> Result<serde_json::Value, Error> {
    to_value_source(pattern)
}

/// Encode a pattern one node at a time, without materializing its KORE tree.
pub fn to_value_source<'a, S: PatternSource<'a>>(source: S) -> Result<serde_json::Value, Error> {
    Ok(source_to_node(source).into_value())
}

enum EncodeTask<'a, S> {
    Text(&'static str),
    Number(String),
    Static(&'static str),
    String(Cow<'a, str>),
    Pattern(S),
    PatternArray(Vec<S>),
    Sort(Cow<'a, Sort>),
    SortArray(Cow<'a, [Sort]>),
}

type EncodeFields<'a, S> = SmallVec<[(&'static str, EncodeTask<'a, S>); 5]>;

fn string_task<'a, S>(value: impl Into<Cow<'a, str>>) -> EncodeTask<'a, S> {
    EncodeTask::String(value.into())
}

fn symbol_tasks<'a, S>(symbol: Cow<'a, Symbol>) -> (EncodeTask<'a, S>, EncodeTask<'a, S>) {
    match symbol {
        Cow::Borrowed(symbol) => (
            string_task(symbol.name.as_str()),
            EncodeTask::SortArray(Cow::Borrowed(&symbol.sort_parameters)),
        ),
        Cow::Owned(symbol) => (
            string_task(symbol.name),
            EncodeTask::SortArray(Cow::Owned(symbol.sort_parameters)),
        ),
    }
}

fn variable_tasks<'a, S>(
    variable: Cow<'a, Variable>,
) -> (VariableKind, EncodeTask<'a, S>, EncodeTask<'a, S>) {
    match variable {
        Cow::Borrowed(variable) => (
            variable.kind,
            string_task(variable.name.as_str()),
            EncodeTask::Sort(Cow::Borrowed(&variable.sort)),
        ),
        Cow::Owned(variable) => (
            variable.kind,
            string_task(variable.name),
            EncodeTask::Sort(Cow::Owned(variable.sort)),
        ),
    }
}

fn pattern_array<'a, S>(patterns: Vec<S>) -> EncodeTask<'a, S> {
    EncodeTask::PatternArray(patterns)
}

fn envelope_fields<'a, S>(source: S) -> EncodeFields<'a, S> {
    smallvec![
        ("format", EncodeTask::Static(FORMAT)),
        ("version", EncodeTask::Number(VERSION.to_string())),
        ("term", EncodeTask::Pattern(source)),
    ]
}

/// Serialize the KORE JSON envelope directly from a pattern source. The task stack follows the
/// expanded tree, while the output buffer holds only its final JSON bytes.
pub fn source_to_string<'a, S: PatternSource<'a>>(source: S) -> String {
    let mut output = Vec::new();
    let mut stack = Vec::new();
    push_string_object(envelope_fields(source), &mut stack);
    while let Some(task) = stack.pop() {
        match task {
            EncodeTask::Text(value) => output.extend_from_slice(value.as_bytes()),
            EncodeTask::Number(value) => output.extend_from_slice(value.as_bytes()),
            EncodeTask::Static(value) => {
                // Invariant: schema keys and tags contain only ASCII letters and digits.
                output.push(b'"');
                output.extend_from_slice(value.as_bytes());
                output.push(b'"');
            }
            EncodeTask::String(value) => {
                serde_json::to_writer(&mut output, &value).expect("writing to a Vec cannot fail");
            }
            EncodeTask::PatternArray(patterns) => {
                stack.push(EncodeTask::Text("]"));
                for (index, pattern) in patterns.into_iter().enumerate().rev() {
                    stack.push(EncodeTask::Pattern(pattern));
                    if index != 0 {
                        stack.push(EncodeTask::Text(","));
                    }
                }
                stack.push(EncodeTask::Text("["));
            }
            EncodeTask::SortArray(sorts) => {
                stack.push(EncodeTask::Text("]"));
                match sorts {
                    Cow::Borrowed(sorts) => {
                        for (index, sort) in sorts.iter().enumerate().rev() {
                            stack.push(EncodeTask::Sort(Cow::Borrowed(sort)));
                            if index != 0 {
                                stack.push(EncodeTask::Text(","));
                            }
                        }
                    }
                    Cow::Owned(sorts) => {
                        for (index, sort) in sorts.into_iter().enumerate().rev() {
                            stack.push(EncodeTask::Sort(Cow::Owned(sort)));
                            if index != 0 {
                                stack.push(EncodeTask::Text(","));
                            }
                        }
                    }
                }
                stack.push(EncodeTask::Text("["));
            }
            EncodeTask::Sort(sort) => push_string_object(sort_fields(sort), &mut stack),
            EncodeTask::Pattern(pattern) => {
                push_string_object(pattern_fields(pattern.node()), &mut stack);
            }
        }
    }
    String::from_utf8(output).expect("JSON serialization emits UTF-8")
}

fn push_string_object<'a, S>(mut fields: EncodeFields<'a, S>, stack: &mut Vec<EncodeTask<'a, S>>) {
    fields.sort_by(|left, right| left.0.cmp(right.0));
    stack.push(EncodeTask::Text("}"));
    for (index, (key, value)) in fields.into_iter().enumerate().rev() {
        stack.push(value);
        stack.push(EncodeTask::Text(":"));
        stack.push(EncodeTask::Static(key));
        if index != 0 {
            stack.push(EncodeTask::Text(","));
        }
    }
    stack.push(EncodeTask::Text("{"));
}

fn sort_fields<'a, S>(sort: Cow<'a, Sort>) -> EncodeFields<'a, S> {
    enum Parts<'a> {
        Variable(Cow<'a, str>),
        Application(Cow<'a, str>, Cow<'a, [Sort]>),
    }
    let parts = match sort {
        Cow::Borrowed(Sort::Variable(name)) => Parts::Variable(Cow::Borrowed(name)),
        Cow::Owned(Sort::Variable(name)) => Parts::Variable(Cow::Owned(name)),
        Cow::Borrowed(Sort::Application { name, arguments }) => {
            Parts::Application(Cow::Borrowed(name), Cow::Borrowed(arguments))
        }
        Cow::Owned(Sort::Application { name, arguments }) => {
            Parts::Application(Cow::Owned(name), Cow::Owned(arguments))
        }
    };
    match parts {
        Parts::Variable(name) => {
            smallvec![
                ("tag", EncodeTask::Static("SortVar")),
                ("name", string_task(name)),
            ]
        }
        Parts::Application(name, arguments) => smallvec![
            ("tag", EncodeTask::Static("SortApp")),
            ("name", string_task(name)),
            ("args", EncodeTask::SortArray(arguments)),
        ],
    }
}

fn pattern_fields<'a, S: PatternSource<'a>>(node: PatternNode<'a, S>) -> EncodeFields<'a, S> {
    match node {
        PatternNode::String(value) => smallvec![
            ("tag", EncodeTask::Static("String")),
            ("value", string_task(json_string_value(&value))),
        ],
        PatternNode::Variable(variable) => {
            let (kind, name, sort) = variable_tasks(variable);
            smallvec![
                (
                    "tag",
                    EncodeTask::Static(if kind == VariableKind::Element {
                        "EVar"
                    } else {
                        "SVar"
                    })
                ),
                ("name", name),
                ("sort", sort),
            ]
        }
        PatternNode::Application { symbol, arguments } => {
            let (name, sorts) = symbol_tasks(symbol);
            smallvec![
                ("tag", EncodeTask::Static("App")),
                ("name", name),
                ("sorts", sorts),
                ("args", pattern_array(arguments)),
            ]
        }
        PatternNode::Top { sort } => smallvec![
            ("tag", EncodeTask::Static("Top")),
            ("sort", EncodeTask::Sort(sort)),
        ],
        PatternNode::Bottom { sort } => smallvec![
            ("tag", EncodeTask::Static("Bottom")),
            ("sort", EncodeTask::Sort(sort)),
        ],
        PatternNode::And { sort, arguments } => smallvec![
            ("tag", EncodeTask::Static("And")),
            ("sort", EncodeTask::Sort(sort)),
            ("patterns", pattern_array(arguments)),
        ],
        PatternNode::Or { sort, arguments } => smallvec![
            ("tag", EncodeTask::Static("Or")),
            ("sort", EncodeTask::Sort(sort)),
            ("patterns", pattern_array(arguments)),
        ],
        PatternNode::Not { sort, argument } => smallvec![
            ("tag", EncodeTask::Static("Not")),
            ("sort", EncodeTask::Sort(sort)),
            ("arg", EncodeTask::Pattern(argument)),
        ],
        PatternNode::Next { sort, argument } => smallvec![
            ("tag", EncodeTask::Static("Next")),
            ("sort", EncodeTask::Sort(sort)),
            ("dest", EncodeTask::Pattern(argument)),
        ],
        PatternNode::Implies { sort, left, right } => smallvec![
            ("tag", EncodeTask::Static("Implies")),
            ("sort", EncodeTask::Sort(sort)),
            ("first", EncodeTask::Pattern(left)),
            ("second", EncodeTask::Pattern(right)),
        ],
        PatternNode::Iff { sort, left, right } => smallvec![
            ("tag", EncodeTask::Static("Iff")),
            ("sort", EncodeTask::Sort(sort)),
            ("first", EncodeTask::Pattern(left)),
            ("second", EncodeTask::Pattern(right)),
        ],
        PatternNode::Rewrites { sort, left, right } => smallvec![
            ("tag", EncodeTask::Static("Rewrites")),
            ("sort", EncodeTask::Sort(sort)),
            ("source", EncodeTask::Pattern(left)),
            ("dest", EncodeTask::Pattern(right)),
        ],
        PatternNode::Exists {
            sort,
            variable,
            body,
        } => {
            let (_, name, var_sort) = variable_tasks(variable);
            smallvec![
                ("tag", EncodeTask::Static("Exists")),
                ("sort", EncodeTask::Sort(sort)),
                ("var", name),
                ("varSort", var_sort),
                ("arg", EncodeTask::Pattern(body)),
            ]
        }
        PatternNode::Forall {
            sort,
            variable,
            body,
        } => {
            let (_, name, var_sort) = variable_tasks(variable);
            smallvec![
                ("tag", EncodeTask::Static("Forall")),
                ("sort", EncodeTask::Sort(sort)),
                ("var", name),
                ("varSort", var_sort),
                ("arg", EncodeTask::Pattern(body)),
            ]
        }
        PatternNode::Mu { variable, body } => {
            let (_, name, var_sort) = variable_tasks(variable);
            smallvec![
                ("tag", EncodeTask::Static("Mu")),
                ("var", name),
                ("varSort", var_sort),
                ("arg", EncodeTask::Pattern(body)),
            ]
        }
        PatternNode::Nu { variable, body } => {
            let (_, name, var_sort) = variable_tasks(variable);
            smallvec![
                ("tag", EncodeTask::Static("Nu")),
                ("var", name),
                ("varSort", var_sort),
                ("arg", EncodeTask::Pattern(body)),
            ]
        }
        PatternNode::Ceil {
            operand_sort,
            result_sort,
            argument,
        } => smallvec![
            ("tag", EncodeTask::Static("Ceil")),
            ("argSort", EncodeTask::Sort(operand_sort)),
            ("sort", EncodeTask::Sort(result_sort)),
            ("arg", EncodeTask::Pattern(argument)),
        ],
        PatternNode::Floor {
            operand_sort,
            result_sort,
            argument,
        } => smallvec![
            ("tag", EncodeTask::Static("Floor")),
            ("argSort", EncodeTask::Sort(operand_sort)),
            ("sort", EncodeTask::Sort(result_sort)),
            ("arg", EncodeTask::Pattern(argument)),
        ],
        PatternNode::Equals {
            operand_sort,
            result_sort,
            left,
            right,
        } => smallvec![
            ("tag", EncodeTask::Static("Equals")),
            ("argSort", EncodeTask::Sort(operand_sort)),
            ("sort", EncodeTask::Sort(result_sort)),
            ("first", EncodeTask::Pattern(left)),
            ("second", EncodeTask::Pattern(right)),
        ],
        PatternNode::In {
            operand_sort,
            result_sort,
            left,
            right,
        } => smallvec![
            ("tag", EncodeTask::Static("In")),
            ("argSort", EncodeTask::Sort(operand_sort)),
            ("sort", EncodeTask::Sort(result_sort)),
            ("first", EncodeTask::Pattern(left)),
            ("second", EncodeTask::Pattern(right)),
        ],
        PatternNode::DomainValue { sort, value } => smallvec![
            ("tag", EncodeTask::Static("DV")),
            ("sort", EncodeTask::Sort(sort)),
            ("value", string_task(json_string_value(&value))),
        ],
        PatternNode::AssociativeApplication {
            associativity,
            symbol,
            arguments,
        } => {
            let (name, sorts) = symbol_tasks(symbol);
            smallvec![
                (
                    "tag",
                    EncodeTask::Static(if associativity == Associativity::Left {
                        "LeftAssoc"
                    } else {
                        "RightAssoc"
                    })
                ),
                ("symbol", name),
                ("sorts", sorts),
                ("argss", pattern_array(arguments)),
            ]
        }
    }
}

fn source_to_node<'a, S: PatternSource<'a>>(source: S) -> Node {
    enum Build<'a, S> {
        Enter(EncodeTask<'a, S>),
        Array(usize),
        Object(SmallVec<[&'static str; 5]>),
    }

    fn push_node_object<'a, S>(fields: EncodeFields<'a, S>, tasks: &mut Vec<Build<'a, S>>) {
        let (keys, children): (SmallVec<[_; 5]>, SmallVec<[_; 5]>) = fields.into_iter().unzip();
        tasks.push(Build::Object(keys));
        tasks.extend(children.into_iter().rev().map(Build::Enter));
    }

    let mut tasks = Vec::new();
    push_node_object(envelope_fields(source), &mut tasks);
    let mut values = Vec::new();
    // Invariant: each finish task follows its children, which are appended to values in field order.
    while let Some(task) = tasks.pop() {
        match task {
            Build::Enter(EncodeTask::Text(_)) => {
                unreachable!("JSON punctuation is not a node field")
            }
            Build::Enter(EncodeTask::Number(value)) => values.push(Node::Number(value)),
            Build::Enter(EncodeTask::Static(value)) => values.push(Node::String(value.to_owned())),
            Build::Enter(EncodeTask::String(value)) => {
                values.push(Node::String(value.into_owned()))
            }
            Build::Enter(EncodeTask::Pattern(source)) => {
                push_node_object(pattern_fields(source.node()), &mut tasks);
            }
            Build::Enter(EncodeTask::Sort(sort)) => {
                push_node_object(sort_fields(sort), &mut tasks);
            }
            Build::Enter(EncodeTask::PatternArray(patterns)) => {
                tasks.push(Build::Array(patterns.len()));
                tasks.extend(
                    patterns
                        .into_iter()
                        .rev()
                        .map(|pattern| Build::Enter(EncodeTask::Pattern(pattern))),
                );
            }
            Build::Enter(EncodeTask::SortArray(sorts)) => {
                tasks.push(Build::Array(sorts.len()));
                match sorts {
                    Cow::Borrowed(sorts) => tasks.extend(
                        sorts
                            .iter()
                            .rev()
                            .map(|sort| Build::Enter(EncodeTask::Sort(Cow::Borrowed(sort)))),
                    ),
                    Cow::Owned(sorts) => tasks.extend(
                        sorts
                            .into_iter()
                            .rev()
                            .map(|sort| Build::Enter(EncodeTask::Sort(Cow::Owned(sort)))),
                    ),
                }
            }
            Build::Array(count) => {
                let children = values.split_off(values.len() - count);
                values.push(Node::Array(children));
            }
            Build::Object(keys) => {
                let start = values.len() - keys.len();
                let fields = keys
                    .into_iter()
                    .map(str::to_owned)
                    .zip(values.drain(start..))
                    .collect();
                values.push(Node::Object(fields));
            }
        }
    }
    values.pop().expect("the source has a root node")
}

enum SortHead {
    Variable(String),
    Application(String),
}

fn sort_head(node: Node) -> Result<(SortHead, Vec<Node>), Error> {
    let mut fields = Fields::new(node)?;
    let tag = fields.string("tag")?;
    let result = match tag.as_str() {
        "SortVar" => (SortHead::Variable(fields.string("name")?), Vec::new()),
        "SortApp" => (
            SortHead::Application(fields.string("name")?),
            fields.array("args")?,
        ),
        _ => {
            return Err(Error::Shape(format!(
                "unknown variant `{tag}`, expected `SortVar` or `SortApp`"
            )));
        }
    };
    fields.finish()?;
    Ok(result)
}

fn build_sort(root: Node) -> Result<Sort, Error> {
    struct Frame {
        head: SortHead,
        remaining: std::vec::IntoIter<Node>,
        built: Vec<Sort>,
    }

    impl Frame {
        fn new(node: Node) -> Result<Self, Error> {
            let (head, children) = sort_head(node)?;
            Ok(Self {
                head,
                remaining: children.into_iter(),
                built: Vec::new(),
            })
        }

        fn finish(self) -> Sort {
            match self.head {
                SortHead::Variable(name) => Sort::Variable(name),
                SortHead::Application(name) => Sort::Application {
                    name,
                    arguments: self.built,
                },
            }
        }
    }

    let mut stack = vec![Frame::new(root)?];
    loop {
        if let Some(child) = stack.last_mut().and_then(|frame| frame.remaining.next()) {
            stack.push(Frame::new(child)?);
            continue;
        }
        let sort = stack.pop().expect("the root sort frame remains").finish();
        if let Some(parent) = stack.last_mut() {
            parent.built.push(sort);
        } else {
            return Ok(sort);
        }
    }
}

#[derive(Clone, Copy)]
enum LeftRight {
    Left,
    Right,
}

enum PatternHead {
    String(String),
    Variable(Variable),
    Application(Symbol),
    Top(Sort),
    Bottom(Sort),
    And(Sort),
    Or(Sort),
    Not(Sort),
    Next(Sort),
    Implies(Sort),
    Iff(Sort),
    Rewrites(Sort),
    Exists(Sort, Variable),
    Forall(Sort, Variable),
    Mu(Variable),
    Nu(Variable),
    Ceil(Sort, Sort),
    Floor(Sort, Sort),
    Equals(Sort, Sort),
    In(Sort, Sort),
    DomainValue(Sort, String),
    MultiOr(LeftRight, Sort),
    Associative(Associativity, Symbol),
}

fn json_string_bytes(value: &str) -> KoreString {
    KoreString::from(
        value
            .chars()
            .map(|character| {
                u8::try_from(u32::from(character))
                    .expect("JSON KORE lexical validation limits strings to Latin-1")
            })
            .collect::<Vec<_>>(),
    )
}

fn json_string_value(value: &KoreString) -> String {
    value.as_bytes().iter().copied().map(char::from).collect()
}

fn variable(kind: VariableKind, name: String, sort: Sort) -> Variable {
    Variable { kind, name, sort }
}

fn symbol(name: String, sorts: Vec<Node>) -> Result<Symbol, Error> {
    Ok(Symbol {
        name,
        sort_parameters: sorts
            .into_iter()
            .map(build_sort)
            .collect::<Result<_, _>>()?,
    })
}

fn pattern_head(node: Node) -> Result<(PatternHead, Vec<Node>), Error> {
    let mut fields = Fields::new(node)?;
    let tag = fields.string("tag")?;
    let mut children = Vec::new();
    let head = match tag.as_str() {
        "String" => {
            let value = fields.string("value")?;
            require_lexical("string literal", &value, lexical::latin1_problems(&value))?;
            PatternHead::String(value)
        }
        "EVar" | "SVar" => {
            let kind = if tag == "EVar" {
                VariableKind::Element
            } else {
                VariableKind::Set
            };
            let name = fields.string("name")?;
            let problems = if kind == VariableKind::Element {
                lexical::identifier_problems(&name)
            } else {
                lexical::set_variable_problems(&name)
            };
            require_lexical(
                if kind == VariableKind::Element {
                    "element variable"
                } else {
                    "set variable"
                },
                &name,
                problems,
            )?;
            PatternHead::Variable(variable(kind, name, build_sort(fields.required("sort")?)?))
        }
        "App" => {
            let name = fields.string("name")?;
            require_lexical("app symbol", &name, lexical::symbol_problems(&name))?;
            let head = PatternHead::Application(symbol(name, fields.array("sorts")?)?);
            children = fields.array("args")?;
            head
        }
        "Top" => PatternHead::Top(build_sort(fields.required("sort")?)?),
        "Bottom" => PatternHead::Bottom(build_sort(fields.required("sort")?)?),
        "And" | "Or" => {
            let sort = build_sort(fields.required("sort")?)?;
            children = if let Some(patterns) = fields.take("patterns") {
                if fields.take("first").is_some() {
                    return Err(Error::Shape("unknown field `first`".into()));
                }
                if fields.take("second").is_some() {
                    return Err(Error::Shape("unknown field `second`".into()));
                }
                expect_array(patterns, "patterns")?
            } else {
                vec![fields.required("first")?, fields.required("second")?]
            };
            if tag == "And" {
                PatternHead::And(sort)
            } else {
                PatternHead::Or(sort)
            }
        }
        "Not" => {
            let head = PatternHead::Not(build_sort(fields.required("sort")?)?);
            children.push(fields.required("arg")?);
            head
        }
        "Next" => {
            let head = PatternHead::Next(build_sort(fields.required("sort")?)?);
            children.push(fields.required("dest")?);
            head
        }
        "Implies" | "Iff" => {
            let sort = build_sort(fields.required("sort")?)?;
            children.push(fields.required("first")?);
            children.push(fields.required("second")?);
            if tag == "Implies" {
                PatternHead::Implies(sort)
            } else {
                PatternHead::Iff(sort)
            }
        }
        "Rewrites" => {
            let head = PatternHead::Rewrites(build_sort(fields.required("sort")?)?);
            children.push(fields.required("source")?);
            children.push(fields.required("dest")?);
            head
        }
        "Exists" | "Forall" => {
            let sort = build_sort(fields.required("sort")?)?;
            let name = fields.string("var")?;
            require_lexical(
                "quantifier variable",
                &name,
                lexical::identifier_problems(&name),
            )?;
            let variable = variable(
                VariableKind::Element,
                name,
                build_sort(fields.required("varSort")?)?,
            );
            children.push(fields.required("arg")?);
            if tag == "Exists" {
                PatternHead::Exists(sort, variable)
            } else {
                PatternHead::Forall(sort, variable)
            }
        }
        "Mu" | "Nu" => {
            let name = fields.string("var")?;
            require_lexical(
                "fixpoint expression variable",
                &name,
                lexical::set_variable_problems(&name),
            )?;
            let variable = variable(
                VariableKind::Set,
                name,
                build_sort(fields.required("varSort")?)?,
            );
            children.push(fields.required("arg")?);
            if tag == "Mu" {
                PatternHead::Mu(variable)
            } else {
                PatternHead::Nu(variable)
            }
        }
        "Ceil" | "Floor" => {
            let operand = build_sort(fields.required("argSort")?)?;
            let result = build_sort(fields.required("sort")?)?;
            children.push(fields.required("arg")?);
            if tag == "Ceil" {
                PatternHead::Ceil(operand, result)
            } else {
                PatternHead::Floor(operand, result)
            }
        }
        "Equals" | "In" => {
            let operand = build_sort(fields.required("argSort")?)?;
            let result = build_sort(fields.required("sort")?)?;
            children.push(fields.required("first")?);
            children.push(fields.required("second")?);
            if tag == "Equals" {
                PatternHead::Equals(operand, result)
            } else {
                PatternHead::In(operand, result)
            }
        }
        "DV" => {
            let sort = build_sort(fields.required("sort")?)?;
            let value = fields.string("value")?;
            require_lexical(
                "domain value string",
                &value,
                lexical::latin1_problems(&value),
            )?;
            PatternHead::DomainValue(sort, value)
        }
        "MultiOr" => {
            let associativity = match fields.string("assoc")?.as_str() {
                "Left" => LeftRight::Left,
                "Right" => LeftRight::Right,
                other => {
                    return Err(Error::Shape(format!(
                        "unknown variant `{other}`, expected `Left` or `Right`"
                    )));
                }
            };
            let head = PatternHead::MultiOr(associativity, build_sort(fields.required("sort")?)?);
            children = fields.array("argss")?;
            head
        }
        "LeftAssoc" | "RightAssoc" => {
            let name = fields.string("symbol")?;
            require_lexical("left-assoc symbol", &name, lexical::symbol_problems(&name))?;
            let associativity = if tag == "LeftAssoc" {
                Associativity::Left
            } else {
                Associativity::Right
            };
            let head =
                PatternHead::Associative(associativity, symbol(name, fields.array("sorts")?)?);
            children = fields.array("argss")?;
            head
        }
        _ => {
            return Err(Error::Shape(format!(
                "unknown variant `{tag}`, expected a KORE pattern tag"
            )));
        }
    };
    fields.finish()?;
    Ok((head, children))
}

fn build_pattern(root: Node) -> Result<Pattern, Error> {
    struct Frame {
        head: PatternHead,
        remaining: std::vec::IntoIter<Node>,
        built: Vec<Pattern>,
    }

    impl Frame {
        fn new(node: Node) -> Result<Self, Error> {
            let (head, children) = pattern_head(node)?;
            Ok(Self {
                head,
                remaining: children.into_iter(),
                built: Vec::new(),
            })
        }

        fn finish(self) -> Result<Pattern, Error> {
            let mut children = self.built.into_iter();
            let mut child = || {
                Box::new(
                    children
                        .next()
                        .expect("the JSON frame supplies every pattern child"),
                )
            };
            Ok(match self.head {
                PatternHead::String(value) => Pattern::String(json_string_bytes(&value)),
                PatternHead::Variable(variable) => Pattern::Variable(variable),
                PatternHead::Application(symbol) => Pattern::Application {
                    symbol,
                    arguments: children.collect(),
                },
                PatternHead::Top(sort) => Pattern::Top { sort },
                PatternHead::Bottom(sort) => Pattern::Bottom { sort },
                PatternHead::And(sort) => Pattern::And {
                    sort,
                    arguments: children.collect(),
                },
                PatternHead::Or(sort) => Pattern::Or {
                    sort,
                    arguments: children.collect(),
                },
                PatternHead::Not(sort) => Pattern::Not {
                    sort,
                    argument: child(),
                },
                PatternHead::Next(sort) => Pattern::Next {
                    sort,
                    argument: child(),
                },
                PatternHead::Implies(sort) => Pattern::Implies {
                    sort,
                    left: child(),
                    right: child(),
                },
                PatternHead::Iff(sort) => Pattern::Iff {
                    sort,
                    left: child(),
                    right: child(),
                },
                PatternHead::Rewrites(sort) => Pattern::Rewrites {
                    sort,
                    left: child(),
                    right: child(),
                },
                PatternHead::Exists(sort, variable) => Pattern::Exists {
                    sort,
                    variable: Box::new(variable),
                    body: child(),
                },
                PatternHead::Forall(sort, variable) => Pattern::Forall {
                    sort,
                    variable: Box::new(variable),
                    body: child(),
                },
                PatternHead::Mu(variable) => Pattern::Mu {
                    variable: Box::new(variable),
                    body: child(),
                },
                PatternHead::Nu(variable) => Pattern::Nu {
                    variable: Box::new(variable),
                    body: child(),
                },
                PatternHead::Ceil(operand_sort, result_sort) => Pattern::Ceil {
                    operand_sort: Box::new(operand_sort),
                    result_sort,
                    argument: child(),
                },
                PatternHead::Floor(operand_sort, result_sort) => Pattern::Floor {
                    operand_sort: Box::new(operand_sort),
                    result_sort,
                    argument: child(),
                },
                PatternHead::Equals(operand_sort, result_sort) => Pattern::Equals {
                    operand_sort: Box::new(operand_sort),
                    result_sort,
                    left: child(),
                    right: child(),
                },
                PatternHead::In(operand_sort, result_sort) => Pattern::In {
                    operand_sort: Box::new(operand_sort),
                    result_sort,
                    left: child(),
                    right: child(),
                },
                PatternHead::DomainValue(sort, value) => Pattern::DomainValue {
                    sort,
                    value: json_string_bytes(&value),
                },
                PatternHead::MultiOr(associativity, sort) => {
                    let mut arguments = children;
                    let first = arguments.next().ok_or(Error::EmptyMultiOr)?;
                    match associativity {
                        LeftRight::Left => arguments.fold(first, |left, right| Pattern::Or {
                            sort: sort.clone(),
                            arguments: vec![left, right],
                        }),
                        LeftRight::Right => {
                            let mut arguments = std::iter::once(first).chain(arguments).rev();
                            let last = arguments.next().expect("MultiOr has at least one argument");
                            arguments.fold(last, |right, left| Pattern::Or {
                                sort: sort.clone(),
                                arguments: vec![left, right],
                            })
                        }
                    }
                }
                PatternHead::Associative(associativity, symbol) => {
                    let arguments: Vec<_> = children.collect();
                    if arguments.is_empty() {
                        return Err(Error::EmptyAssociativeApplication);
                    }
                    Pattern::AssociativeApplication {
                        associativity,
                        symbol,
                        arguments,
                    }
                }
            })
        }
    }

    let mut stack = vec![Frame::new(root)?];
    loop {
        if let Some(child) = stack.last_mut().and_then(|frame| frame.remaining.next()) {
            stack.push(Frame::new(child)?);
            continue;
        }
        let pattern = stack
            .pop()
            .expect("the root pattern frame remains")
            .finish()?;
        if let Some(parent) = stack.last_mut() {
            parent.built.push(pattern);
        } else {
            return Ok(pattern);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kore::parser::parse_pattern;
    use serde_json::{Value, json};

    #[test]
    fn source_writer_matches_value_serialization() {
        for source in [
            r#"\top{S{}}()"#,
            r#"\bottom{S{}}()"#,
            r#"\and{S{}}(\dv{S{}}("a"), X:S{})"#,
            r#"\not{S{}}(\or{S{}}(X:S{}, Y:S{}))"#,
            r#"\exists{S{}}(X:S{}, \equals{S{}, S{}}(X:S{}, Y:S{}))"#,
            r#"\rewrites{S{}}(\ceil{S{}, S{}}(X:S{}), \floor{S{}, S{}}(Y:S{}))"#,
        ] {
            let pattern = parse_pattern(source).unwrap();
            assert_eq!(
                source_to_string(&pattern),
                serde_json::to_string(&to_value(&pattern).unwrap()).unwrap(),
                "{source}"
            );
        }
    }

    fn sort() -> Value {
        json!({ "tag": "SortApp", "name": "S", "args": [] })
    }

    fn app(name: &str) -> Value {
        json!({ "tag": "App", "name": name, "sorts": [], "args": [] })
    }

    fn document(term: Value) -> String {
        json!({ "format": "KORE", "version": 1, "term": term }).to_string()
    }

    fn decode(term: Value) -> Result<Pattern, Error> {
        from_str(&document(term))
    }

    #[test]
    fn accepts_binary_and_or_fields_from_legacy_version_one_producers() {
        let decoded = from_str(
            r#"{
                "format": "KORE",
                "version": 1,
                "term": {
                    "tag": "And",
                    "sort": { "tag": "SortApp", "name": "SortK", "args": [] },
                    "first": {
                        "tag": "EVar",
                        "name": "X",
                        "sort": { "tag": "SortApp", "name": "SortK", "args": [] }
                    },
                    "second": {
                        "tag": "EVar",
                        "name": "Y",
                        "sort": { "tag": "SortApp", "name": "SortK", "args": [] }
                    }
                }
            }"#,
        )
        .unwrap();

        assert_eq!(
            decoded,
            parse_pattern(r"\and{SortK{}}(X:SortK{}, Y:SortK{})").unwrap()
        );
    }

    #[test]
    fn serializes_variadic_and_or_fields_without_collapsing_arity() {
        let pattern = parse_pattern(r"\or{SortK{}}()").unwrap();
        let encoded = to_string(&pattern).unwrap();

        assert!(encoded.contains(r#""patterns":[]"#));
        assert!(!encoded.contains(r#""first""#));
        assert_eq!(from_str(&encoded).unwrap(), pattern);
    }

    #[test]
    fn round_trips_arbitrary_string_bytes() {
        let pattern = Pattern::DomainValue {
            sort: Sort::Application {
                name: "SortString".into(),
                arguments: Vec::new(),
            },
            value: KoreString::from(vec![0xff, 0x80, 0x00, b'A']),
        };
        let encoded = to_string(&pattern).unwrap();
        assert_eq!(from_str(&encoded).unwrap(), pattern);
    }

    #[test]
    fn both_json_entry_points_decode_without_a_depth_limit() {
        let sort = r#"{"tag":"SortApp","name":"SortK","args":[]}"#;
        let mut term = format!(r#"{{"tag":"Top","sort":{sort}}}"#);
        for _ in 0..140 {
            term = format!(r#"{{"tag":"Not","sort":{sort},"arg":{term}}}"#);
        }
        let source = format!(r#"{{"format":"KORE","version":1,"term":{term}}}"#);

        assert!(from_str(&source).is_ok());
        #[allow(deprecated)]
        {
            assert!(from_str_unbounded(&source).is_ok());
        }
    }

    #[test]
    fn converts_deep_kore_patterns_to_json_values_without_a_depth_limit() {
        let sort = Sort::Application {
            name: "SortK".into(),
            arguments: Vec::new(),
        };
        let pattern = (0..160).fold(Pattern::Top { sort: sort.clone() }, |argument, _| {
            Pattern::Not {
                sort: sort.clone(),
                argument: Box::new(argument),
            }
        });

        assert!(to_value(&pattern).is_ok());
    }

    #[test]
    fn rejects_reference_lexical_errors() {
        let cases = [
            (
                json!({ "tag": "SVar", "name": "X", "sort": sort() }),
                "Lexical errors in set variable : X",
            ),
            (
                json!({ "tag": "EVar", "name": "foo bar", "sort": sort() }),
                "Lexical error in element variable : foo bar",
            ),
            (
                json!({ "tag": "EVar", "name": "é", "sort": sort() }),
                "Lexical error in element variable : é",
            ),
            (
                json!({ "tag": "App", "name": "a b", "sorts": [], "args": [] }),
                "Lexical error in app symbol : a b",
            ),
            (
                json!({ "tag": "App", "name": "", "sorts": [], "args": [] }),
                "Lexical error in app symbol : ",
            ),
            (
                json!({ "tag": "DV", "sort": sort(), "value": "≤" }),
                "Lexical error in domain value string : ≤",
            ),
            (
                json!({ "tag": "String", "value": "Ā" }),
                "Lexical error in string literal : Ā",
            ),
            (
                json!({ "tag": "Mu", "var": "X", "varSort": sort(), "arg": app("a") }),
                "Lexical errors in fixpoint expression variable : X",
            ),
        ];

        for (term, expected_prefix) in cases {
            let error = decode(term).expect_err("reference lexical error must be rejected");
            assert!(
                error.to_string().starts_with(expected_prefix),
                "expected {expected_prefix:?}, got {error}"
            );
        }
    }

    #[test]
    fn rejects_unknown_fields_below_the_envelope_only() {
        assert!(
            decode(json!({ "tag": "Top", "sort": sort(), "bogus": 1 }))
                .unwrap_err()
                .to_string()
                .contains("unknown field")
        );
        assert!(
            decode(json!({
                "tag": "Top",
                "sort": { "tag": "SortApp", "name": "S", "args": [], "bogus": 1 }
            }))
            .unwrap_err()
            .to_string()
            .contains("unknown field")
        );
        assert!(
            decode(json!({
                "tag": "And",
                "sort": sort(),
                "patterns": [app("a")],
                "first": app("b")
            }))
            .unwrap_err()
            .to_string()
            .contains("unknown field `first`")
        );

        let source = json!({
            "format": "KORE",
            "version": 1,
            "term": { "tag": "Top", "sort": sort() },
            "extra": 1
        })
        .to_string();
        assert!(from_str(&source).is_ok());
    }

    #[test]
    fn decodes_multi_or_as_the_reference_expands_it() {
        let multi_or = |assoc: &str, argss: Vec<Value>| json!({ "tag": "MultiOr", "assoc": assoc, "sort": sort(), "argss": argss });
        let left = decode(multi_or("Left", vec![app("a"), app("b"), app("c")])).unwrap();
        let right = decode(multi_or("Right", vec![app("a"), app("b"), app("c")])).unwrap();
        let one = decode(multi_or("Left", vec![app("a")])).unwrap();

        assert_eq!(
            left,
            parse_pattern(r"\or{S{}}(\or{S{}}(a{}(), b{}()), c{}())").unwrap()
        );
        assert_eq!(
            right,
            parse_pattern(r"\or{S{}}(a{}(), \or{S{}}(b{}(), c{}()))").unwrap()
        );
        assert_eq!(one, parse_pattern("a{}()").unwrap());
        assert_eq!(
            decode(multi_or("Left", Vec::new()))
                .unwrap_err()
                .to_string(),
            "MultiOr requires at least one argument"
        );
        assert!(decode(multi_or("Middle", vec![app("a")])).is_err());
    }

    #[test]
    fn accepted_names_round_trip_through_text() {
        for term in [
            json!({ "tag": "EVar", "name": "X-1'", "sort": sort() }),
            json!({ "tag": "SVar", "name": "@X-1'", "sort": sort() }),
            json!({ "tag": "App", "name": "\\foo", "sorts": [], "args": [] }),
        ] {
            let pattern = decode(term).unwrap();
            assert_eq!(parse_pattern(&pattern.to_string()).unwrap(), pattern);
        }
    }
}
