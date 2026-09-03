//! KAST JSON version 4 serialization.

use serde::{Deserialize, Serialize};

use k_rust_kore::json_tree::{self, Node};

use super::ast::{Label, Sort, Term};

pub const FORMAT: &str = "KAST";
pub const VERSION: u32 = 4;

#[derive(Debug)]
pub enum Error {
    Syntax(json_tree::Error),
    Shape(String),
    UnsupportedFormat(String),
    UnsupportedVersion(u32),
    InvalidArity {
        node: &'static str,
        declared: usize,
        actual: usize,
    },
}

impl std::fmt::Display for Error {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Syntax(error) => error.fmt(formatter),
            Self::Shape(message) => formatter.write_str(message),
            Self::UnsupportedFormat(format) => {
                write!(formatter, "unsupported KAST format {format:?}")
            }
            Self::UnsupportedVersion(version) => {
                write!(formatter, "unsupported KAST version {version}")
            }
            Self::InvalidArity {
                node,
                declared,
                actual,
            } => write!(
                formatter,
                "{node} declares arity {declared}, but contains {actual} children"
            ),
        }
    }
}

impl std::error::Error for Error {}

impl From<json_tree::Error> for Error {
    fn from(error: json_tree::Error) -> Self {
        Self::Syntax(error)
    }
}

pub fn from_str(input: &str) -> Result<Term, Error> {
    let mut envelope = Fields::new(json_tree::parse(input)?)?;
    let format = envelope.string("format")?;
    let version = envelope.u32("version")?;
    let term = envelope.required("term")?;
    if format != FORMAT {
        return Err(Error::UnsupportedFormat(format));
    }
    if version != VERSION {
        return Err(Error::UnsupportedVersion(version));
    }
    build_term(term)
}

pub fn to_string(term: &Term) -> Result<String, Error> {
    Ok(json_tree::to_string(&envelope_node(term), false))
}

pub fn to_string_pretty(term: &Term) -> Result<String, Error> {
    Ok(json_tree::to_string(&envelope_node(term), true))
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
        let mut node = self.required(name)?;
        let kind = node.kind();
        match &mut node {
            Node::String(value) => Ok(std::mem::take(value)),
            _ => Err(Error::Shape(format!(
                "invalid type: {kind}, expected a string for field `{name}`"
            ))),
        }
    }

    fn array(&mut self, name: &str) -> Result<Vec<Node>, Error> {
        let node = self.required(name)?;
        let kind = node.kind();
        node.into_array().ok_or_else(|| {
            Error::Shape(format!(
                "invalid type: {kind}, expected an array for field `{name}`"
            ))
        })
    }

    fn number<T: std::str::FromStr>(&mut self, name: &str, expected: &str) -> Result<T, Error> {
        let mut node = self.required(name)?;
        let kind = node.kind();
        let value = match &mut node {
            Node::Number(value) => std::mem::take(value),
            _ => {
                return Err(Error::Shape(format!(
                    "invalid type: {kind}, expected {expected} for field `{name}`"
                )));
            }
        };
        value.parse().map_err(|_| {
            Error::Shape(format!(
                "invalid value: {value}, expected {expected} for field `{name}`"
            ))
        })
    }

    fn u32(&mut self, name: &str) -> Result<u32, Error> {
        self.number(name, "u32")
    }

    fn usize(&mut self, name: &str) -> Result<usize, Error> {
        self.number(name, "usize")
    }
}

fn sort_head(node: Node) -> Result<(String, Vec<Node>), Error> {
    let mut fields = Fields::new(node)?;
    let node = fields.string("node")?;
    if node != "KSort" {
        return Err(Error::Shape(format!(
            "unknown variant `{node}`, expected `KSort`"
        )));
    }
    Ok((fields.string("name")?, fields.array("params")?))
}

fn build_sort(root: Node) -> Result<Sort, Error> {
    struct Frame {
        name: String,
        remaining: std::vec::IntoIter<Node>,
        built: Vec<Sort>,
    }

    impl Frame {
        fn new(node: Node) -> Result<Self, Error> {
            let (name, children) = sort_head(node)?;
            Ok(Self {
                name,
                remaining: children.into_iter(),
                built: Vec::new(),
            })
        }
    }

    let mut stack = vec![Frame::new(root)?];
    loop {
        if let Some(child) = stack.last_mut().and_then(|frame| frame.remaining.next()) {
            stack.push(Frame::new(child)?);
            continue;
        }
        let frame = stack.pop().expect("the root sort frame remains");
        let sort = Sort {
            name: frame.name,
            parameters: frame.built,
        };
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

    let mut stack = vec![Frame {
        sort: root,
        next: 0,
        built: Vec::new(),
    }];
    loop {
        let frame = stack.last_mut().expect("the root sort frame remains");
        if let Some(child) = frame.sort.parameters.get(frame.next) {
            frame.next += 1;
            stack.push(Frame {
                sort: child,
                next: 0,
                built: Vec::new(),
            });
            continue;
        }
        let frame = stack.pop().expect("the completed sort frame is present");
        let node = Node::Object(vec![
            ("node".into(), Node::String("KSort".into())),
            ("name".into(), Node::String(frame.sort.name.clone())),
            ("params".into(), Node::Array(frame.built)),
        ]);
        if let Some(parent) = stack.last_mut() {
            parent.built.push(node);
        } else {
            return node;
        }
    }
}

fn build_label(node: Node) -> Result<Label, Error> {
    let mut fields = Fields::new(node)?;
    let node = fields.string("node")?;
    if node != "KLabel" {
        return Err(Error::Shape(format!(
            "unknown variant `{node}`, expected `KLabel`"
        )));
    }
    Ok(Label {
        name: fields.string("name")?,
        parameters: fields
            .array("params")?
            .into_iter()
            .map(build_sort)
            .collect::<Result<_, _>>()?,
    })
}

fn label_node(label: &Label) -> Node {
    Node::Object(vec![
        ("node".into(), Node::String("KLabel".into())),
        ("name".into(), Node::String(label.name.clone())),
        (
            "params".into(),
            Node::Array(label.parameters.iter().map(sort_node).collect()),
        ),
    ])
}

enum TermHead {
    Token(Sort, String),
    Apply(Label, usize),
    Sequence(usize),
    Variable(String, Option<Sort>),
    Rewrite,
    As,
    InjectedLabel(Label),
}

fn term_head(node: Node) -> Result<(TermHead, Vec<Node>), Error> {
    let mut fields = Fields::new(node)?;
    let node = fields.string("node")?;
    let mut children = Vec::new();
    let head = match node.as_str() {
        "KToken" => TermHead::Token(
            build_sort(fields.required("sort")?)?,
            fields.string("token")?,
        ),
        "KApply" => {
            let label = build_label(fields.required("label")?)?;
            let arity = fields.usize("arity")?;
            children = fields.array("args")?;
            TermHead::Apply(label, arity)
        }
        "KSequence" => {
            let arity = fields.usize("arity")?;
            children = fields.array("items")?;
            TermHead::Sequence(arity)
        }
        "KVariable" => TermHead::Variable(
            fields.string("name")?,
            fields.take("sort").map(build_sort).transpose()?,
        ),
        "KRewrite" => {
            children.push(fields.required("lhs")?);
            children.push(fields.required("rhs")?);
            TermHead::Rewrite
        }
        "KAs" => {
            children.push(fields.required("pattern")?);
            children.push(fields.required("alias")?);
            TermHead::As
        }
        "InjectedKLabel" => TermHead::InjectedLabel(build_label(fields.required("label")?)?),
        _ => {
            return Err(Error::Shape(format!(
                "unknown variant `{node}`, expected a KAST term node"
            )));
        }
    };
    // JsonTerm intentionally ignores unknown fields, matching its former serde representation.
    Ok((head, children))
}

fn build_term(root: Node) -> Result<Term, Error> {
    struct Frame {
        head: TermHead,
        remaining: std::vec::IntoIter<Node>,
        built: Vec<Term>,
    }

    impl Frame {
        fn new(node: Node) -> Result<Self, Error> {
            let (head, children) = term_head(node)?;
            Ok(Self {
                head,
                remaining: children.into_iter(),
                built: Vec::new(),
            })
        }

        fn finish(self) -> Result<Term, Error> {
            let mut children = self.built.into_iter();
            let result = match self.head {
                TermHead::Token(sort, token) => Term::Token { token, sort },
                TermHead::Apply(label, declared) => {
                    let arguments: Vec<_> = children.collect();
                    if declared != arguments.len() {
                        return Err(Error::InvalidArity {
                            node: "KApply",
                            declared,
                            actual: arguments.len(),
                        });
                    }
                    Term::Apply { label, arguments }
                }
                TermHead::Sequence(declared) => {
                    let items: Vec<_> = children.collect();
                    if declared != items.len() {
                        return Err(Error::InvalidArity {
                            node: "KSequence",
                            declared,
                            actual: items.len(),
                        });
                    }
                    Term::Sequence(items)
                }
                TermHead::Variable(name, sort) => Term::Variable { name, sort },
                TermHead::Rewrite => Term::Rewrite {
                    left: Box::new(children.next().expect("KRewrite has a left child")),
                    right: Box::new(children.next().expect("KRewrite has a right child")),
                },
                TermHead::As => Term::As {
                    pattern: Box::new(children.next().expect("KAs has a pattern child")),
                    alias: Box::new(children.next().expect("KAs has an alias child")),
                },
                TermHead::InjectedLabel(label) => Term::InjectedLabel(label),
            };
            Ok(result)
        }
    }

    let mut stack = vec![Frame::new(root)?];
    loop {
        if let Some(child) = stack.last_mut().and_then(|frame| frame.remaining.next()) {
            stack.push(Frame::new(child)?);
            continue;
        }
        let term = stack.pop().expect("the root term frame remains").finish()?;
        if let Some(parent) = stack.last_mut() {
            parent.built.push(term);
        } else {
            return Ok(term);
        }
    }
}

fn term_children(term: &Term) -> Vec<&Term> {
    match term.unannotated() {
        Term::Apply { arguments, .. } | Term::Sequence(arguments) => arguments.iter().collect(),
        Term::Rewrite { left, right } => vec![left, right],
        Term::As { pattern, alias } => vec![pattern, alias],
        Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => Vec::new(),
        Term::Annotated { .. } => unreachable!(),
    }
}

fn term_node(root: &Term) -> Node {
    struct Frame<'a> {
        term: &'a Term,
        children: Vec<&'a Term>,
        next: usize,
        built: Vec<Node>,
    }

    impl<'a> Frame<'a> {
        fn new(term: &'a Term) -> Self {
            let term = term.unannotated();
            Self {
                term,
                children: term_children(term),
                next: 0,
                built: Vec::new(),
            }
        }

        fn finish(self) -> Node {
            let mut children = self.built.into_iter();
            match self.term {
                Term::Token { token, sort } => Node::Object(vec![
                    ("node".into(), Node::String("KToken".into())),
                    ("sort".into(), sort_node(sort)),
                    ("token".into(), Node::String(token.clone())),
                ]),
                Term::Apply { label, arguments } => Node::Object(vec![
                    ("node".into(), Node::String("KApply".into())),
                    ("label".into(), label_node(label)),
                    ("arity".into(), Node::Number(arguments.len().to_string())),
                    ("args".into(), Node::Array(children.collect())),
                ]),
                Term::Sequence(items) => Node::Object(vec![
                    ("node".into(), Node::String("KSequence".into())),
                    ("arity".into(), Node::Number(items.len().to_string())),
                    ("items".into(), Node::Array(children.collect())),
                ]),
                Term::Variable { name, sort } => {
                    let mut fields = vec![
                        ("node".into(), Node::String("KVariable".into())),
                        ("name".into(), Node::String(name.clone())),
                    ];
                    if let Some(sort) = sort {
                        fields.push(("sort".into(), sort_node(sort)));
                    }
                    Node::Object(fields)
                }
                Term::Rewrite { .. } => Node::Object(vec![
                    ("node".into(), Node::String("KRewrite".into())),
                    (
                        "lhs".into(),
                        children.next().expect("KRewrite has a left child"),
                    ),
                    (
                        "rhs".into(),
                        children.next().expect("KRewrite has a right child"),
                    ),
                ]),
                Term::As { .. } => Node::Object(vec![
                    ("node".into(), Node::String("KAs".into())),
                    (
                        "pattern".into(),
                        children.next().expect("KAs has a pattern child"),
                    ),
                    (
                        "alias".into(),
                        children.next().expect("KAs has an alias child"),
                    ),
                ]),
                Term::InjectedLabel(label) => Node::Object(vec![
                    ("node".into(), Node::String("InjectedKLabel".into())),
                    ("label".into(), label_node(label)),
                ]),
                Term::Annotated { .. } => unreachable!(),
            }
        }
    }

    let mut stack = vec![Frame::new(root)];
    loop {
        let frame = stack.last_mut().expect("the root term frame remains");
        if let Some(child) = frame.children.get(frame.next).copied() {
            frame.next += 1;
            stack.push(Frame::new(child));
            continue;
        }
        let node = stack
            .pop()
            .expect("the completed term frame is present")
            .finish();
        if let Some(parent) = stack.last_mut() {
            parent.built.push(node);
        } else {
            return node;
        }
    }
}

fn envelope_node(term: &Term) -> Node {
    Node::Object(vec![
        ("format".into(), Node::String(FORMAT.into())),
        ("version".into(), Node::Number(VERSION.to_string())),
        ("term".into(), term_node(term)),
    ])
}

#[derive(Clone, Serialize, Deserialize)]
pub(crate) struct JsonSort {
    node: SortNode,
    pub(crate) name: String,
    pub(crate) params: Vec<JsonSort>,
}

#[derive(Clone, Copy, Serialize, Deserialize)]
enum SortNode {
    KSort,
}

#[derive(Clone, Serialize, Deserialize)]
pub(crate) struct JsonLabel {
    node: LabelNode,
    pub(crate) name: String,
    pub(crate) params: Vec<JsonSort>,
}

#[derive(Clone, Copy, Serialize, Deserialize)]
enum LabelNode {
    KLabel,
}

impl From<&Sort> for JsonSort {
    fn from(sort: &Sort) -> Self {
        Self {
            node: SortNode::KSort,
            name: sort.name.clone(),
            params: sort.parameters.iter().map(Into::into).collect(),
        }
    }
}

impl From<JsonSort> for Sort {
    fn from(sort: JsonSort) -> Self {
        Self {
            name: sort.name,
            parameters: sort.params.into_iter().map(Into::into).collect(),
        }
    }
}

impl From<&Label> for JsonLabel {
    fn from(label: &Label) -> Self {
        Self {
            node: LabelNode::KLabel,
            name: label.name.clone(),
            params: label.parameters.iter().map(Into::into).collect(),
        }
    }
}

impl From<JsonLabel> for Label {
    fn from(label: JsonLabel) -> Self {
        Self {
            name: label.name,
            parameters: label.params.into_iter().map(Into::into).collect(),
        }
    }
}

#[derive(Serialize, Deserialize)]
#[serde(tag = "node")]
pub(crate) enum JsonTerm {
    KToken {
        sort: JsonSort,
        token: String,
    },
    KApply {
        label: JsonLabel,
        arity: usize,
        args: Vec<JsonTerm>,
    },
    KSequence {
        arity: usize,
        items: Vec<JsonTerm>,
    },
    KVariable {
        name: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        sort: Option<JsonSort>,
    },
    KRewrite {
        lhs: Box<JsonTerm>,
        rhs: Box<JsonTerm>,
    },
    KAs {
        pattern: Box<JsonTerm>,
        alias: Box<JsonTerm>,
    },
    InjectedKLabel {
        label: JsonLabel,
    },
}

impl From<&Term> for JsonTerm {
    fn from(term: &Term) -> Self {
        match term.unannotated() {
            Term::Token { token, sort } => Self::KToken {
                sort: sort.into(),
                token: token.clone(),
            },
            Term::Apply { label, arguments } => Self::KApply {
                label: label.into(),
                arity: arguments.len(),
                args: arguments.iter().map(Into::into).collect(),
            },
            Term::Sequence(items) => Self::KSequence {
                arity: items.len(),
                items: items.iter().map(Into::into).collect(),
            },
            Term::Variable { name, sort } => Self::KVariable {
                name: name.clone(),
                sort: sort.as_ref().map(Into::into),
            },
            Term::Rewrite { left, right } => Self::KRewrite {
                lhs: Box::new(left.as_ref().into()),
                rhs: Box::new(right.as_ref().into()),
            },
            Term::As { pattern, alias } => Self::KAs {
                pattern: Box::new(pattern.as_ref().into()),
                alias: Box::new(alias.as_ref().into()),
            },
            Term::InjectedLabel(label) => Self::InjectedKLabel {
                label: label.into(),
            },
            Term::Annotated { .. } => unreachable!(),
        }
    }
}

impl TryFrom<JsonTerm> for Term {
    type Error = Error;

    fn try_from(term: JsonTerm) -> Result<Self, Self::Error> {
        fn boxed(term: JsonTerm) -> Result<Box<Term>, Error> {
            Ok(Box::new(term.try_into()?))
        }
        fn terms(values: Vec<JsonTerm>) -> Result<Vec<Term>, Error> {
            values.into_iter().map(TryInto::try_into).collect()
        }
        fn checked(
            node: &'static str,
            declared: usize,
            values: Vec<JsonTerm>,
        ) -> Result<Vec<Term>, Error> {
            if declared != values.len() {
                return Err(Error::InvalidArity {
                    node,
                    declared,
                    actual: values.len(),
                });
            }
            terms(values)
        }

        Ok(match term {
            JsonTerm::KToken { sort, token } => Self::Token {
                token,
                sort: sort.into(),
            },
            JsonTerm::KApply { label, arity, args } => Self::Apply {
                label: label.into(),
                arguments: checked("KApply", arity, args)?,
            },
            JsonTerm::KSequence { arity, items } => {
                Self::Sequence(checked("KSequence", arity, items)?)
            }
            JsonTerm::KVariable { name, sort } => Self::Variable {
                name,
                sort: sort.map(Into::into),
            },
            JsonTerm::KRewrite { lhs, rhs } => Self::Rewrite {
                left: boxed(*lhs)?,
                right: boxed(*rhs)?,
            },
            JsonTerm::KAs { pattern, alias } => Self::As {
                pattern: boxed(*pattern)?,
                alias: boxed(*alias)?,
            },
            JsonTerm::InjectedKLabel { label } => Self::InjectedLabel(label.into()),
        })
    }
}
