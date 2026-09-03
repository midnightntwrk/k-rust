//! KORE JSON version 1 serialization.

use crate::json_tree::{self, Node};

use super::{
    ast::{Associativity, Pattern, Sort, Symbol, Variable, VariableKind},
    lexical::{self, Problem},
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
    Ok(json_tree::to_string(&envelope_node(pattern), false))
}

pub fn to_string_pretty(pattern: &Pattern) -> Result<String, Error> {
    Ok(json_tree::to_string(&envelope_node(pattern), true))
}

pub fn to_value(pattern: &Pattern) -> Result<serde_json::Value, Error> {
    Ok(envelope_node(pattern).into_value())
}

fn envelope_node(pattern: &Pattern) -> Node {
    Node::Object(vec![
        ("format".into(), Node::String(FORMAT.into())),
        ("version".into(), Node::Number(VERSION.to_string())),
        ("term".into(), pattern_node(pattern)),
    ])
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

fn sort_node(root: &Sort) -> Node {
    struct Frame<'a> {
        sort: &'a Sort,
        next: usize,
        built: Vec<Node>,
    }

    fn children(sort: &Sort) -> &[Sort] {
        match sort {
            Sort::Variable(_) => &[],
            Sort::Application { arguments, .. } => arguments,
        }
    }

    let mut stack = vec![Frame {
        sort: root,
        next: 0,
        built: Vec::new(),
    }];
    loop {
        let frame = stack.last_mut().expect("the root sort frame remains");
        if let Some(child) = children(frame.sort).get(frame.next) {
            frame.next += 1;
            stack.push(Frame {
                sort: child,
                next: 0,
                built: Vec::new(),
            });
            continue;
        }
        let frame = stack.pop().expect("the completed sort frame is present");
        let node = match frame.sort {
            Sort::Variable(name) => Node::Object(vec![
                ("tag".into(), Node::String("SortVar".into())),
                ("name".into(), Node::String(name.clone())),
            ]),
            Sort::Application { name, .. } => Node::Object(vec![
                ("tag".into(), Node::String("SortApp".into())),
                ("name".into(), Node::String(name.clone())),
                ("args".into(), Node::Array(frame.built)),
            ]),
        };
        if let Some(parent) = stack.last_mut() {
            parent.built.push(node);
        } else {
            return node;
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
                PatternHead::String(value) => Pattern::String(value),
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
                    variable,
                    body: child(),
                },
                PatternHead::Forall(sort, variable) => Pattern::Forall {
                    sort,
                    variable,
                    body: child(),
                },
                PatternHead::Mu(variable) => Pattern::Mu {
                    variable,
                    body: child(),
                },
                PatternHead::Nu(variable) => Pattern::Nu {
                    variable,
                    body: child(),
                },
                PatternHead::Ceil(operand_sort, result_sort) => Pattern::Ceil {
                    operand_sort,
                    result_sort,
                    argument: child(),
                },
                PatternHead::Floor(operand_sort, result_sort) => Pattern::Floor {
                    operand_sort,
                    result_sort,
                    argument: child(),
                },
                PatternHead::Equals(operand_sort, result_sort) => Pattern::Equals {
                    operand_sort,
                    result_sort,
                    left: child(),
                    right: child(),
                },
                PatternHead::In(operand_sort, result_sort) => Pattern::In {
                    operand_sort,
                    result_sort,
                    left: child(),
                    right: child(),
                },
                PatternHead::DomainValue(sort, value) => Pattern::DomainValue { sort, value },
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

fn array_nodes<'a>(values: impl IntoIterator<Item = &'a Sort>) -> Node {
    Node::Array(values.into_iter().map(sort_node).collect())
}

fn pattern_node(pattern: &Pattern) -> Node {
    super::walk::rebuild(pattern, |pattern, children| {
        let mut children = children.into_iter();
        let mut child = || {
            children
                .next()
                .expect("the traversal supplies every pattern child")
        };
        match pattern {
            Pattern::String(value) => Node::Object(vec![
                ("tag".into(), Node::String("String".into())),
                ("value".into(), Node::String(value.clone())),
            ]),
            Pattern::Variable(variable) => Node::Object(vec![
                (
                    "tag".into(),
                    Node::String(
                        if variable.kind == VariableKind::Element {
                            "EVar"
                        } else {
                            "SVar"
                        }
                        .into(),
                    ),
                ),
                ("name".into(), Node::String(variable.name.clone())),
                ("sort".into(), sort_node(&variable.sort)),
            ]),
            Pattern::Application { symbol, .. } => Node::Object(vec![
                ("tag".into(), Node::String("App".into())),
                ("name".into(), Node::String(symbol.name.clone())),
                ("sorts".into(), array_nodes(symbol.sort_parameters.iter())),
                ("args".into(), Node::Array(children.collect())),
            ]),
            Pattern::Top { sort } | Pattern::Bottom { sort } => Node::Object(vec![
                (
                    "tag".into(),
                    Node::String(
                        if matches!(pattern, Pattern::Top { .. }) {
                            "Top"
                        } else {
                            "Bottom"
                        }
                        .into(),
                    ),
                ),
                ("sort".into(), sort_node(sort)),
            ]),
            Pattern::And { sort, .. } | Pattern::Or { sort, .. } => Node::Object(vec![
                (
                    "tag".into(),
                    Node::String(
                        if matches!(pattern, Pattern::And { .. }) {
                            "And"
                        } else {
                            "Or"
                        }
                        .into(),
                    ),
                ),
                ("sort".into(), sort_node(sort)),
                ("patterns".into(), Node::Array(children.collect())),
            ]),
            Pattern::Not { sort, .. } | Pattern::Next { sort, .. } => Node::Object(vec![
                (
                    "tag".into(),
                    Node::String(
                        if matches!(pattern, Pattern::Not { .. }) {
                            "Not"
                        } else {
                            "Next"
                        }
                        .into(),
                    ),
                ),
                ("sort".into(), sort_node(sort)),
                (
                    if matches!(pattern, Pattern::Not { .. }) {
                        "arg"
                    } else {
                        "dest"
                    }
                    .into(),
                    child(),
                ),
            ]),
            Pattern::Implies { sort, .. } | Pattern::Iff { sort, .. } => Node::Object(vec![
                (
                    "tag".into(),
                    Node::String(
                        if matches!(pattern, Pattern::Implies { .. }) {
                            "Implies"
                        } else {
                            "Iff"
                        }
                        .into(),
                    ),
                ),
                ("sort".into(), sort_node(sort)),
                ("first".into(), child()),
                ("second".into(), child()),
            ]),
            Pattern::Rewrites { sort, .. } => Node::Object(vec![
                ("tag".into(), Node::String("Rewrites".into())),
                ("sort".into(), sort_node(sort)),
                ("source".into(), child()),
                ("dest".into(), child()),
            ]),
            Pattern::Exists { sort, variable, .. } | Pattern::Forall { sort, variable, .. } => {
                Node::Object(vec![
                    (
                        "tag".into(),
                        Node::String(
                            if matches!(pattern, Pattern::Exists { .. }) {
                                "Exists"
                            } else {
                                "Forall"
                            }
                            .into(),
                        ),
                    ),
                    ("sort".into(), sort_node(sort)),
                    ("var".into(), Node::String(variable.name.clone())),
                    ("varSort".into(), sort_node(&variable.sort)),
                    ("arg".into(), child()),
                ])
            }
            Pattern::Mu { variable, .. } | Pattern::Nu { variable, .. } => Node::Object(vec![
                (
                    "tag".into(),
                    Node::String(
                        if matches!(pattern, Pattern::Mu { .. }) {
                            "Mu"
                        } else {
                            "Nu"
                        }
                        .into(),
                    ),
                ),
                ("var".into(), Node::String(variable.name.clone())),
                ("varSort".into(), sort_node(&variable.sort)),
                ("arg".into(), child()),
            ]),
            Pattern::Ceil {
                operand_sort,
                result_sort,
                ..
            }
            | Pattern::Floor {
                operand_sort,
                result_sort,
                ..
            } => Node::Object(vec![
                (
                    "tag".into(),
                    Node::String(
                        if matches!(pattern, Pattern::Ceil { .. }) {
                            "Ceil"
                        } else {
                            "Floor"
                        }
                        .into(),
                    ),
                ),
                ("argSort".into(), sort_node(operand_sort)),
                ("sort".into(), sort_node(result_sort)),
                ("arg".into(), child()),
            ]),
            Pattern::Equals {
                operand_sort,
                result_sort,
                ..
            }
            | Pattern::In {
                operand_sort,
                result_sort,
                ..
            } => Node::Object(vec![
                (
                    "tag".into(),
                    Node::String(
                        if matches!(pattern, Pattern::Equals { .. }) {
                            "Equals"
                        } else {
                            "In"
                        }
                        .into(),
                    ),
                ),
                ("argSort".into(), sort_node(operand_sort)),
                ("sort".into(), sort_node(result_sort)),
                ("first".into(), child()),
                ("second".into(), child()),
            ]),
            Pattern::DomainValue { sort, value } => Node::Object(vec![
                ("tag".into(), Node::String("DV".into())),
                ("sort".into(), sort_node(sort)),
                ("value".into(), Node::String(value.clone())),
            ]),
            Pattern::AssociativeApplication {
                associativity,
                symbol,
                ..
            } => Node::Object(vec![
                (
                    "tag".into(),
                    Node::String(
                        if *associativity == Associativity::Left {
                            "LeftAssoc"
                        } else {
                            "RightAssoc"
                        }
                        .into(),
                    ),
                ),
                ("symbol".into(), Node::String(symbol.name.clone())),
                ("sorts".into(), array_nodes(symbol.sort_parameters.iter())),
                ("argss".into(), Node::Array(children.collect())),
            ]),
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kore::parser::parse_pattern;
    use serde_json::{Value, json};

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
