//! Stack-safe JSON syntax tree used by the KORE and KAST codecs.

use std::fmt;

#[derive(Debug)]
pub enum Node {
    Null,
    Bool(bool),
    Number(String),
    String(String),
    Array(Vec<Node>),
    Object(Vec<(String, Node)>),
}

impl Node {
    pub fn kind(&self) -> &'static str {
        match self {
            Self::Null => "null",
            Self::Bool(_) => "boolean",
            Self::Number(_) => "number",
            Self::String(_) => "string",
            Self::Array(_) => "array",
            Self::Object(_) => "object",
        }
    }

    pub fn into_array(mut self) -> Option<Vec<Self>> {
        match &mut self {
            Self::Array(values) => Some(std::mem::take(values)),
            _ => None,
        }
    }

    pub fn into_object(mut self) -> Option<Vec<(String, Self)>> {
        match &mut self {
            Self::Object(fields) => Some(std::mem::take(fields)),
            _ => None,
        }
    }

    pub fn into_string(mut self) -> Option<String> {
        match &mut self {
            Self::String(value) | Self::Number(value) => Some(std::mem::take(value)),
            _ => None,
        }
    }

    pub fn into_value(mut self) -> serde_json::Value {
        enum Head {
            Array,
            Object(Vec<String>),
        }

        struct Frame {
            head: Head,
            remaining: std::vec::IntoIter<Node>,
            values: Vec<serde_json::Value>,
        }

        fn primitive(node: &mut Node) -> Option<serde_json::Value> {
            match node {
                Node::Null => Some(serde_json::Value::Null),
                Node::Bool(value) => Some(serde_json::Value::Bool(*value)),
                Node::Number(value) => Some(serde_json::Value::Number(
                    std::mem::take(value)
                        .parse()
                        .expect("json_tree validates number tokens"),
                )),
                Node::String(value) => Some(serde_json::Value::String(std::mem::take(value))),
                Node::Array(_) | Node::Object(_) => None,
            }
        }

        let mut stack: Vec<Frame> = Vec::new();
        let mut value = None;
        loop {
            if value.is_none() {
                if let Some(primitive) = primitive(&mut self) {
                    value = Some(primitive);
                } else {
                    let (head, children) = match &mut self {
                        Node::Array(children) => (Head::Array, std::mem::take(children)),
                        Node::Object(fields) => {
                            let fields = std::mem::take(fields);
                            let (keys, values): (Vec<_>, Vec<_>) = fields.into_iter().unzip();
                            (Head::Object(keys), values)
                        }
                        _ => unreachable!("primitive nodes were handled above"),
                    };
                    let mut remaining = children.into_iter();
                    if let Some(next) = remaining.next() {
                        stack.push(Frame {
                            head,
                            remaining,
                            values: Vec::new(),
                        });
                        self = next;
                        continue;
                    }
                    value = Some(match head {
                        Head::Array => serde_json::Value::Array(Vec::new()),
                        Head::Object(_) => serde_json::Value::Object(serde_json::Map::new()),
                    });
                }
            }

            let completed = value.take().expect("a JSON value was built");
            let Some(frame) = stack.last_mut() else {
                return completed;
            };
            frame.values.push(completed);
            if let Some(next) = frame.remaining.next() {
                self = next;
                continue;
            }

            let frame = stack.pop().expect("the completed JSON frame is present");
            value = Some(match frame.head {
                Head::Array => serde_json::Value::Array(frame.values),
                Head::Object(keys) => serde_json::Value::Object(
                    keys.into_iter()
                        .zip(frame.values)
                        .collect::<serde_json::Map<_, _>>(),
                ),
            });
        }
    }
}

impl Drop for Node {
    fn drop(&mut self) {
        fn take_children(node: &mut Node) -> Vec<Node> {
            match node {
                Node::Array(values) => std::mem::take(values),
                Node::Object(fields) => std::mem::take(fields)
                    .into_iter()
                    .map(|(_, value)| value)
                    .collect(),
                Node::Null | Node::Bool(_) | Node::Number(_) | Node::String(_) => Vec::new(),
            }
        }

        let mut work = take_children(self);
        while let Some(mut child) = work.pop() {
            work.extend(take_children(&mut child));
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Error {
    pub line: usize,
    pub column: usize,
    pub message: String,
}

impl fmt::Display for Error {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "{} at line {} column {}",
            self.message, self.line, self.column
        )
    }
}

impl std::error::Error for Error {}

pub fn parse(input: &str) -> Result<Node, Error> {
    enum Frame {
        Array(Vec<Node>),
        Object {
            fields: Vec<(String, Node)>,
            key: Option<String>,
        },
    }

    enum Action {
        Value,
        ArrayValueOrEnd,
        ArrayDelimiter,
        ObjectKeyOrEnd,
        ObjectKey,
        ObjectDelimiter,
        Finished,
    }

    fn attach(
        value: Node,
        stack: &mut [Frame],
        root: &mut Option<Node>,
    ) -> Result<Action, &'static str> {
        match stack.last_mut() {
            Some(Frame::Array(values)) => {
                values.push(value);
                Ok(Action::ArrayDelimiter)
            }
            Some(Frame::Object { fields, key }) => {
                let key = key.take().ok_or("object value has no key")?;
                fields.push((key, value));
                Ok(Action::ObjectDelimiter)
            }
            None => {
                *root = Some(value);
                Ok(Action::Finished)
            }
        }
    }

    let mut parser = Parser { input, cursor: 0 };
    let mut stack: Vec<Frame> = Vec::new();
    let mut root = None;
    let mut action = Action::Value;
    loop {
        parser.whitespace();
        action = match action {
            Action::Value => match parser.value()? {
                ValueStart::Value(value) => {
                    attach(value, &mut stack, &mut root).map_err(|message| parser.error(message))?
                }
                ValueStart::Array => {
                    stack.push(Frame::Array(Vec::new()));
                    Action::ArrayValueOrEnd
                }
                ValueStart::Object => {
                    stack.push(Frame::Object {
                        fields: Vec::new(),
                        key: None,
                    });
                    Action::ObjectKeyOrEnd
                }
            },
            Action::ArrayValueOrEnd if parser.consume(b']') => {
                let Some(Frame::Array(values)) = stack.pop() else {
                    unreachable!("array action has an array frame")
                };
                attach(Node::Array(values), &mut stack, &mut root)
                    .map_err(|message| parser.error(message))?
            }
            Action::ArrayValueOrEnd => Action::Value,
            Action::ArrayDelimiter if parser.consume(b',') => Action::Value,
            Action::ArrayDelimiter if parser.consume(b']') => {
                let Some(Frame::Array(values)) = stack.pop() else {
                    unreachable!("array action has an array frame")
                };
                attach(Node::Array(values), &mut stack, &mut root)
                    .map_err(|message| parser.error(message))?
            }
            Action::ArrayDelimiter => {
                return Err(parser.error("expected `,` or `]`"));
            }
            Action::ObjectKeyOrEnd if parser.consume(b'}') => {
                let Some(Frame::Object { fields, .. }) = stack.pop() else {
                    unreachable!("object action has an object frame")
                };
                attach(Node::Object(fields), &mut stack, &mut root)
                    .map_err(|message| parser.error(message))?
            }
            Action::ObjectKeyOrEnd | Action::ObjectKey => {
                let key = parser.string()?;
                let Some(Frame::Object {
                    fields,
                    key: pending,
                }) = stack.last_mut()
                else {
                    unreachable!("object-key action has an object frame")
                };
                if fields.iter().any(|(existing, _)| existing == &key) {
                    return Err(parser.error(format!("duplicate field `{key}`")));
                }
                parser.whitespace();
                parser.expect(b':', "expected `:` after object key")?;
                *pending = Some(key);
                Action::Value
            }
            Action::ObjectDelimiter if parser.consume(b',') => Action::ObjectKey,
            Action::ObjectDelimiter if parser.consume(b'}') => {
                let Some(Frame::Object { fields, .. }) = stack.pop() else {
                    unreachable!("object action has an object frame")
                };
                attach(Node::Object(fields), &mut stack, &mut root)
                    .map_err(|message| parser.error(message))?
            }
            Action::ObjectDelimiter => {
                return Err(parser.error("expected `,` or `}`"));
            }
            Action::Finished => {
                if parser.cursor != input.len() {
                    return Err(parser.error("trailing characters"));
                }
                return root.ok_or_else(|| parser.error("expected a JSON value"));
            }
        };
    }
}

enum ValueStart {
    Value(Node),
    Array,
    Object,
}

struct Parser<'a> {
    input: &'a str,
    cursor: usize,
}

impl Parser<'_> {
    fn value(&mut self) -> Result<ValueStart, Error> {
        let Some(byte) = self.input.as_bytes().get(self.cursor).copied() else {
            return Err(self.error("expected a JSON value"));
        };
        match byte {
            b'{' => {
                self.cursor += 1;
                Ok(ValueStart::Object)
            }
            b'[' => {
                self.cursor += 1;
                Ok(ValueStart::Array)
            }
            b'"' => self.string().map(Node::String).map(ValueStart::Value),
            b't' => self.literal("true", Node::Bool(true)),
            b'f' => self.literal("false", Node::Bool(false)),
            b'n' => self.literal("null", Node::Null),
            b'-' | b'0'..=b'9' => self.number().map(Node::Number).map(ValueStart::Value),
            _ => Err(self.error("expected a JSON value")),
        }
    }

    fn literal(&mut self, token: &str, value: Node) -> Result<ValueStart, Error> {
        if self.input[self.cursor..].starts_with(token) {
            self.cursor += token.len();
            Ok(ValueStart::Value(value))
        } else {
            Err(self.error(format!("expected `{token}`")))
        }
    }

    fn number(&mut self) -> Result<String, Error> {
        let start = self.cursor;
        while self
            .input
            .as_bytes()
            .get(self.cursor)
            .is_some_and(|byte| !matches!(byte, b' ' | b'\t' | b'\r' | b'\n' | b',' | b']' | b'}'))
        {
            self.cursor += 1;
        }
        let token = &self.input[start..self.cursor];
        serde_json::from_str::<serde_json::Number>(token)
            .map_err(|error| self.error(error.to_string()))?;
        Ok(token.to_owned())
    }

    fn string(&mut self) -> Result<String, Error> {
        let start = self.cursor;
        self.expect(b'"', "expected a string")?;
        while let Some(byte) = self.input.as_bytes().get(self.cursor).copied() {
            match byte {
                b'"' => {
                    self.cursor += 1;
                    return serde_json::from_str(&self.input[start..self.cursor])
                        .map_err(|error| self.error(error.to_string()));
                }
                b'\\' => {
                    self.cursor += 1;
                    if self.cursor == self.input.len() {
                        return Err(self.error("unterminated escape sequence"));
                    }
                    self.cursor += 1;
                }
                0..=0x1f => return Err(self.error("control character in string")),
                _ => self.cursor += 1,
            }
        }
        Err(self.error("unterminated string"))
    }

    fn whitespace(&mut self) {
        while self
            .input
            .as_bytes()
            .get(self.cursor)
            .is_some_and(|byte| matches!(byte, b' ' | b'\t' | b'\r' | b'\n'))
        {
            self.cursor += 1;
        }
    }

    fn consume(&mut self, byte: u8) -> bool {
        if self.input.as_bytes().get(self.cursor) == Some(&byte) {
            self.cursor += 1;
            true
        } else {
            false
        }
    }

    fn expect(&mut self, byte: u8, message: &str) -> Result<(), Error> {
        if self.consume(byte) {
            Ok(())
        } else {
            Err(self.error(message))
        }
    }

    fn error(&self, message: impl Into<String>) -> Error {
        let prefix = &self.input[..self.cursor.min(self.input.len())];
        let line = prefix.bytes().filter(|byte| *byte == b'\n').count() + 1;
        let line_start = prefix.rfind('\n').map_or(0, |index| index + 1);
        let column = prefix[line_start..].chars().count() + 1;
        Error {
            line,
            column,
            message: message.into(),
        }
    }
}

pub fn to_string(root: &Node, pretty: bool) -> String {
    enum Task<'a> {
        Node(&'a Node, usize),
        Raw(&'static str),
        String(&'a str),
        Newline(usize),
    }

    let mut output = String::new();
    let mut stack = vec![Task::Node(root, 0)];
    while let Some(task) = stack.pop() {
        match task {
            Task::Raw(raw) => output.push_str(raw),
            Task::String(value) => output.push_str(
                &serde_json::to_string(value).expect("serializing a Rust string cannot fail"),
            ),
            Task::Newline(indent) => {
                output.push('\n');
                output.extend(std::iter::repeat_n(' ', indent * 2));
            }
            Task::Node(node, depth) => match node {
                Node::Null => output.push_str("null"),
                Node::Bool(value) => output.push_str(if *value { "true" } else { "false" }),
                Node::Number(value) => output.push_str(value),
                Node::String(value) => output.push_str(
                    &serde_json::to_string(value).expect("serializing a Rust string cannot fail"),
                ),
                Node::Array(values) if values.is_empty() => output.push_str("[]"),
                Node::Array(values) => {
                    output.push('[');
                    let mut tasks = Vec::new();
                    if pretty {
                        tasks.push(Task::Newline(depth + 1));
                    }
                    for (index, value) in values.iter().enumerate() {
                        if index > 0 {
                            tasks.push(Task::Raw(","));
                            if pretty {
                                tasks.push(Task::Newline(depth + 1));
                            }
                        }
                        tasks.push(Task::Node(value, depth + 1));
                    }
                    if pretty {
                        tasks.push(Task::Newline(depth));
                    }
                    tasks.push(Task::Raw("]"));
                    stack.extend(tasks.into_iter().rev());
                }
                Node::Object(fields) if fields.is_empty() => output.push_str("{}"),
                Node::Object(fields) => {
                    output.push('{');
                    let mut tasks = Vec::new();
                    if pretty {
                        tasks.push(Task::Newline(depth + 1));
                    }
                    for (index, (key, value)) in fields.iter().enumerate() {
                        if index > 0 {
                            tasks.push(Task::Raw(","));
                            if pretty {
                                tasks.push(Task::Newline(depth + 1));
                            }
                        }
                        tasks.push(Task::String(key));
                        tasks.push(Task::Raw(if pretty { ": " } else { ":" }));
                        tasks.push(Task::Node(value, depth + 1));
                    }
                    if pretty {
                        tasks.push(Task::Newline(depth));
                    }
                    tasks.push(Task::Raw("}"));
                    stack.extend(tasks.into_iter().rev());
                }
            },
        }
    }
    output
}

#[cfg(test)]
mod tests {
    use super::{Node, parse, to_string};

    #[test]
    fn parses_and_prints_like_serde_json() {
        let source = r#"{"a":[null,true,false,-125.0,"x\n\u263a"],"b":{}}"#;
        let node = parse(source).unwrap();
        let value = serde_json::from_str::<serde_json::Value>(source).unwrap();
        assert_eq!(
            to_string(&node, false),
            serde_json::to_string(&value).unwrap()
        );
        assert_eq!(
            to_string(&node, true),
            serde_json::to_string_pretty(&value).unwrap()
        );
        assert_eq!(
            node.into_value(),
            serde_json::from_str::<serde_json::Value>(source).unwrap()
        );
    }

    #[test]
    fn rejects_duplicate_fields_and_trailing_commas() {
        assert!(parse(r#"{"a":1,"a":2}"#).is_err());
        assert!(parse(r#"{"a":1,}"#).is_err());
        assert!(parse("[1,]").is_err());
    }

    #[test]
    fn drops_deep_trees_iteratively() {
        let mut source = "[".repeat(100_000);
        source.push_str("null");
        source.push_str(&"]".repeat(100_000));
        std::thread::Builder::new()
            .stack_size(1 << 20)
            .spawn(move || drop(parse(&source).unwrap()))
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn node_kinds_are_stable() {
        assert_eq!(Node::Null.kind(), "null");
    }
}
