//! The scanner that frames a connection's byte stream into JSON-RPC messages
//! ([`super::read_json_message`]), and the frames it produces.
//!
//! [`Scanner`] is resumable: given the bytes buffered so far, it stops where it needs a byte past
//! them and continues from there once more are appended, so each byte of a frame is examined
//! once. It accepts exactly the JSON that serde_json's raw-value parser accepts (the grammar of
//! `ignore_value`; strings checked for escapes and control characters but not for valid
//! surrogates; the value checked for UTF-8 once it is complete), and it examines a byte past the
//! buffer exactly where that parser asks for one, so a connection reads at the same moments as
//! when serde_json read it. While it scans an object it records the members the server reads,
//! so the frame's text, taken out of the buffer without a copy, is not scanned again before its
//! parameters are decoded.

use std::{borrow::Cow, ops::Range};

/// One message: its JSON text and, for an object, the members the server reads.
pub(super) struct Frame {
    /// The frame's bytes: the whitespace before the value, then the value.
    text: String,
    /// Where the value starts in `text`.
    start: usize,
    /// The value's members, when it is an object every member name of which decodes.
    members: Option<Members>,
}

/// Where the members of a request object are in its frame's text.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Members {
    /// The last `jsonrpc`, `method`, `id` and `params` member values.
    request: [Option<Range<usize>>; 4],
    /// The last `params` member's `haskell-logging` member value, when that `params` is an object
    /// every member name of which decodes.
    haskell_logging: Option<Range<usize>>,
}

const REQUEST_MEMBERS: [&str; 4] = ["jsonrpc", "method", "id", "params"];
const PARAMS: usize = 3;

/// The members of a request object, as the text of each value.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(super) struct RequestMembers<'a> {
    pub(super) jsonrpc: Option<&'a str>,
    pub(super) method: Option<&'a str>,
    pub(super) id: Option<&'a str>,
    pub(super) params: Option<&'a str>,
    /// The `haskell-logging` member of `params`, when `params` is an object every member name of
    /// which decodes.
    pub(super) haskell_logging: Option<&'a str>,
}

impl Frame {
    /// The message's JSON text.
    pub(super) fn value(&self) -> &str {
        &self.text[self.start..]
    }

    /// The members of the message, or `None` when it is not an object or one of its member names
    /// does not decode; a repeated member keeps its last value.
    pub(super) fn members(&self) -> Option<RequestMembers<'_>> {
        let members = self.members.as_ref()?;
        let slice = |range: &Option<Range<usize>>| range.clone().map(|range| &self.text[range]);
        let [jsonrpc, method, id, params] = &members.request;
        Some(RequestMembers {
            jsonrpc: slice(jsonrpc),
            method: slice(method),
            id: slice(id),
            params: slice(params),
            haskell_logging: slice(&members.haskell_logging),
        })
    }

    /// The message that `scanner` found ending at `end`, taken out of `buffer` without copying
    /// it; `None`, with `buffer` unchanged, when it is not UTF-8.
    pub(super) fn take(buffer: &mut Vec<u8>, scanner: &Scanner, end: usize) -> Option<Self> {
        let rest = buffer.split_off(end);
        let bytes = std::mem::replace(buffer, rest);
        match String::from_utf8(bytes) {
            Ok(text) => Some(Self {
                text,
                start: scanner.value_start,
                members: scanner.members(),
            }),
            Err(error) => {
                let mut bytes = error.into_bytes();
                bytes.extend_from_slice(buffer);
                *buffer = bytes;
                None
            }
        }
    }

    /// The frame's bytes, the whitespace before the value included.
    #[cfg(test)]
    pub(super) fn raw(&self) -> &str {
        &self.text
    }

    /// The message whose text is `text`, as a frame of a connection would hold it; `None` when
    /// `text` is not one JSON value with optional whitespace around it.
    #[cfg(test)]
    pub(super) fn parse(text: &str) -> Option<Self> {
        let value = serde_json::from_str::<Box<serde_json::value::RawValue>>(text).ok()?;
        let text = value.get().to_owned();
        let mut scanner = Scanner::default();
        let outcome = scanner.scan(text.as_bytes(), true);
        assert!(
            matches!(outcome, Outcome::Complete(end) if end == text.len()),
            "serde_json accepted a value the scanner does not frame: {text}"
        );
        let members = scanner.members();
        Some(Self {
            text,
            start: 0,
            members,
        })
    }
}

/// What the scanner found in the bytes it was given.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Outcome {
    /// The value ends at this offset.
    Complete(usize),
    /// The bytes are not a JSON value, whatever follows them.
    Syntax,
    /// The value is unfinished at the end of the stream, or the stream has no value.
    Eof,
    /// The scanner needs the byte after the bytes it was given.
    NeedByte,
}

/// Which string the scanner is in.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Role {
    Value,
    Key,
}

/// The scanner's position in the grammar. Each state examines the next byte (a state named for
/// a number examines it as `\0` at the end of the stream, every other state as the end).
#[derive(Clone, Copy, Debug)]
enum State {
    /// Whitespace before the message.
    Start,
    /// Whitespace before a value, then its first byte.
    Value,
    /// The rest of `null`, `true` or `false`.
    Literal(&'static [u8]),
    /// The first digit of a number, after its sign.
    IntegerFirst,
    /// After a leading `0`: another digit is an error.
    IntegerZero,
    IntegerDigits,
    /// After the integer part: a fraction, an exponent, or the end of the number.
    NumberTail,
    FractionFirst,
    FractionDigits,
    /// After the fraction: an exponent, or the end of the number.
    FractionTail,
    ExponentSign,
    ExponentFirst,
    ExponentDigits,
    String(Role),
    Escape(Role),
    /// The `n`th hexadecimal digit of a `\u` escape.
    Hex(Role, u8),
    /// After an opening bracket (`accept_comma` false) or a member or element.
    Inner {
        accept_comma: bool,
    },
    /// Whitespace before a member name.
    KeyQuote,
    /// Whitespace before the colon after a member name.
    Colon,
    /// After a scalar message: the byte after it must not continue it.
    PeekEnd,
    /// The message is complete.
    Done,
}

/// A resumable scanner of one JSON value. [`Scanner::scan`] continues where it stopped when it
/// is given the same bytes with more appended.
pub(super) struct Scanner {
    state: State,
    /// The offset of the next byte to examine.
    pos: usize,
    /// The open arrays and objects, innermost last.
    stack: Vec<u8>,
    /// The first byte of the value, once found.
    root: Option<u8>,
    value_start: usize,
    /// Where the member name being read starts.
    key_start: usize,
    members: MemberScan,
}

impl Default for Scanner {
    fn default() -> Self {
        Self {
            state: State::Start,
            pos: 0,
            stack: Vec::new(),
            root: None,
            value_start: 0,
            key_start: 0,
            members: MemberScan::default(),
        }
    }
}

const fn is_whitespace(byte: u8) -> bool {
    matches!(byte, b' ' | b'\n' | b'\t' | b'\r')
}

impl Scanner {
    /// Whether the value is a scalar: a number or a literal.
    pub(super) fn is_scalar(&self) -> bool {
        matches!(self.root, Some(b't' | b'f' | b'n' | b'-' | b'0'..=b'9'))
    }

    fn members(&self) -> Option<Members> {
        (self.root == Some(b'{') && self.members.names_decode).then(|| Members {
            request: self.members.request.clone(),
            haskell_logging: self.members.haskell_logging.clone(),
        })
    }

    /// Continues scanning `bytes`; `at_end` says that no byte follows them.
    pub(super) fn scan(&mut self, bytes: &[u8], at_end: bool) -> Outcome {
        loop {
            if let State::Done = self.state {
                return Outcome::Complete(self.pos);
            }
            let byte = match bytes.get(self.pos) {
                Some(&byte) => Some(byte),
                None if at_end => None,
                None => return Outcome::NeedByte,
            };
            match self.state {
                State::Start => match byte {
                    Some(byte) if is_whitespace(byte) => self.pos += 1,
                    Some(byte) => {
                        self.root = Some(byte);
                        self.value_start = self.pos;
                        self.state = State::Value;
                    }
                    None => return Outcome::Eof,
                },
                State::Value => match byte {
                    Some(byte) if is_whitespace(byte) => self.pos += 1,
                    Some(byte) => {
                        self.members.value_starts(self.stack.len(), self.pos, byte);
                        match byte {
                            b'n' => self.literal(b"ull"),
                            b't' => self.literal(b"rue"),
                            b'f' => self.literal(b"alse"),
                            b'-' => {
                                self.pos += 1;
                                self.state = State::IntegerFirst;
                            }
                            b'0'..=b'9' => self.state = State::IntegerFirst,
                            b'"' => {
                                self.pos += 1;
                                self.state = State::String(Role::Value);
                            }
                            b'[' | b'{' => {
                                self.stack.push(byte);
                                self.pos += 1;
                                self.state = State::Inner {
                                    accept_comma: false,
                                };
                            }
                            _ => return Outcome::Syntax,
                        }
                    }
                    None => return Outcome::Eof,
                },
                State::Literal(rest) => match byte {
                    Some(byte) if byte == rest[0] => {
                        self.pos += 1;
                        if rest.len() == 1 {
                            self.value_done();
                        } else {
                            self.state = State::Literal(&rest[1..]);
                        }
                    }
                    Some(_) => return Outcome::Syntax,
                    None => return Outcome::Eof,
                },
                State::IntegerFirst => match byte {
                    Some(b'0') => {
                        self.pos += 1;
                        self.state = State::IntegerZero;
                    }
                    Some(b'1'..=b'9') => {
                        self.pos += 1;
                        self.state = State::IntegerDigits;
                    }
                    _ => return Outcome::Syntax,
                },
                State::IntegerZero => match byte {
                    Some(b'0'..=b'9') => return Outcome::Syntax,
                    _ => self.state = State::NumberTail,
                },
                State::IntegerDigits => match byte {
                    Some(b'0'..=b'9') => self.pos += 1,
                    _ => self.state = State::NumberTail,
                },
                State::NumberTail => match byte {
                    Some(b'.') => {
                        self.pos += 1;
                        self.state = State::FractionFirst;
                    }
                    Some(b'e' | b'E') => {
                        self.pos += 1;
                        self.state = State::ExponentSign;
                    }
                    _ => self.value_done(),
                },
                State::FractionFirst => match byte {
                    Some(b'0'..=b'9') => {
                        self.pos += 1;
                        self.state = State::FractionDigits;
                    }
                    _ => return Outcome::Syntax,
                },
                State::FractionDigits => match byte {
                    Some(b'0'..=b'9') => self.pos += 1,
                    _ => self.state = State::FractionTail,
                },
                State::FractionTail => match byte {
                    Some(b'e' | b'E') => {
                        self.pos += 1;
                        self.state = State::ExponentSign;
                    }
                    _ => self.value_done(),
                },
                State::ExponentSign => {
                    if let Some(b'+' | b'-') = byte {
                        self.pos += 1;
                    }
                    self.state = State::ExponentFirst;
                }
                State::ExponentFirst => match byte {
                    Some(b'0'..=b'9') => {
                        self.pos += 1;
                        self.state = State::ExponentDigits;
                    }
                    _ => return Outcome::Syntax,
                },
                State::ExponentDigits => match byte {
                    Some(b'0'..=b'9') => self.pos += 1,
                    _ => self.value_done(),
                },
                State::String(role) => {
                    if byte.is_none() {
                        return Outcome::Eof;
                    }
                    let rest = &bytes[self.pos..];
                    match rest
                        .iter()
                        .position(|&byte| byte == b'"' || byte == b'\\' || byte < 0x20)
                    {
                        None => self.pos = bytes.len(),
                        Some(offset) => {
                            self.pos += offset + 1;
                            match rest[offset] {
                                b'"' => self.string_done(role, bytes),
                                b'\\' => self.state = State::Escape(role),
                                _ => return Outcome::Syntax,
                            }
                        }
                    }
                }
                State::Escape(role) => match byte {
                    Some(b'"' | b'\\' | b'/' | b'b' | b'f' | b'n' | b'r' | b't') => {
                        self.pos += 1;
                        self.state = State::String(role);
                    }
                    Some(b'u') => {
                        self.pos += 1;
                        self.state = State::Hex(role, 0);
                    }
                    Some(_) => return Outcome::Syntax,
                    None => return Outcome::Eof,
                },
                State::Hex(role, digit) => match byte {
                    Some(_) => {
                        self.pos += 1;
                        if digit < 3 {
                            self.state = State::Hex(role, digit + 1);
                        } else if bytes[self.pos - 4..self.pos]
                            .iter()
                            .all(u8::is_ascii_hexdigit)
                        {
                            self.state = State::String(role);
                        } else {
                            return Outcome::Syntax;
                        }
                    }
                    None => return Outcome::Eof,
                },
                State::Inner { accept_comma } => {
                    let open = *self.stack.last().expect("an open array or object");
                    match byte {
                        Some(byte) if is_whitespace(byte) => self.pos += 1,
                        Some(b',') if accept_comma => {
                            self.pos += 1;
                            self.next_member_or_element(open);
                        }
                        Some(b']') if open == b'[' => self.close(),
                        Some(b'}') if open == b'{' => self.close(),
                        Some(_) if accept_comma => return Outcome::Syntax,
                        Some(_) => self.next_member_or_element(open),
                        None => return Outcome::Eof,
                    }
                }
                State::KeyQuote => match byte {
                    Some(byte) if is_whitespace(byte) => self.pos += 1,
                    Some(b'"') => {
                        self.key_start = self.pos;
                        self.pos += 1;
                        self.state = State::String(Role::Key);
                    }
                    Some(_) => return Outcome::Syntax,
                    None => return Outcome::Eof,
                },
                State::Colon => match byte {
                    Some(byte) if is_whitespace(byte) => self.pos += 1,
                    Some(b':') => {
                        self.pos += 1;
                        self.state = State::Value;
                    }
                    Some(_) => return Outcome::Syntax,
                    None => return Outcome::Eof,
                },
                State::PeekEnd => match byte {
                    None
                    | Some(
                        b' ' | b'\n' | b'\t' | b'\r' | b'"' | b'[' | b']' | b'{' | b'}' | b','
                        | b':',
                    ) => self.state = State::Done,
                    Some(_) => return Outcome::Syntax,
                },
                State::Done => unreachable!("handled before a byte is examined"),
            }
        }
    }

    fn literal(&mut self, rest: &'static [u8]) {
        self.pos += 1;
        self.state = State::Literal(rest);
    }

    fn next_member_or_element(&mut self, open: u8) {
        self.state = if open == b'{' {
            State::KeyQuote
        } else {
            State::Value
        };
    }

    fn close(&mut self) {
        self.pos += 1;
        self.stack.pop();
        self.value_done();
    }

    fn string_done(&mut self, role: Role, bytes: &[u8]) {
        match role {
            Role::Value => self.value_done(),
            Role::Key => {
                self.members
                    .key(self.stack.len(), &bytes[self.key_start..self.pos]);
                self.state = State::Colon;
            }
        }
    }

    /// A value has ended at `pos`: continue in its array or object, or end the message.
    fn value_done(&mut self) {
        self.members.value_ends(self.stack.len(), self.pos);
        self.state = if !self.stack.is_empty() {
            State::Inner { accept_comma: true }
        } else if self.is_scalar() {
            State::PeekEnd
        } else {
            State::Done
        };
    }
}

/// The members of an object message, recorded while it is scanned. Only a message whose root
/// is an object reads them ([`Scanner::members`]); its members are at depth 1, and those of its
/// `params` object at depth 2.
struct MemberScan {
    /// Whether every depth-1 member name decoded.
    names_decode: bool,
    request: [Option<Range<usize>>; 4],
    haskell_logging: Option<Range<usize>>,
    /// The depth-1 member being read: its index in [`REQUEST_MEMBERS`], if it is one of them.
    member: Option<usize>,
    member_start: usize,
    /// Whether the depth-1 member being read is `params` and its value is an object.
    in_params: bool,
    /// Whether every member name of that `params` object decoded so far.
    params_names_decode: bool,
    /// Its last `haskell-logging` member so far.
    params_logging: Option<Range<usize>>,
    /// Whether the depth-2 member being read is its `haskell-logging`.
    logging_member: bool,
    logging_start: usize,
}

impl Default for MemberScan {
    fn default() -> Self {
        Self {
            names_decode: true,
            request: Default::default(),
            haskell_logging: None,
            member: None,
            member_start: 0,
            in_params: false,
            params_names_decode: true,
            params_logging: None,
            logging_member: false,
            logging_start: 0,
        }
    }
}

impl MemberScan {
    /// A member name (with its quotes) ends inside an object `depth` deep.
    fn key(&mut self, depth: usize, key: &[u8]) {
        match depth {
            1 => {
                let name = decode_name(key);
                self.names_decode &= name.is_some();
                self.member =
                    name.and_then(|name| REQUEST_MEMBERS.iter().position(|member| *member == name));
            }
            2 if self.in_params => {
                let name = decode_name(key);
                self.params_names_decode &= name.is_some();
                self.logging_member = name.is_some_and(|name| name == "haskell-logging");
            }
            _ => {}
        }
    }

    /// A value whose first byte is `first` starts at `start`, `depth` arrays and objects deep.
    fn value_starts(&mut self, depth: usize, start: usize, first: u8) {
        match depth {
            1 => {
                self.member_start = start;
                if self.member == Some(PARAMS) {
                    self.in_params = first == b'{';
                    self.params_names_decode = true;
                    self.params_logging = None;
                }
            }
            2 if self.in_params => self.logging_start = start,
            _ => {}
        }
    }

    /// A value ends at `end`, inside `depth` arrays and objects.
    fn value_ends(&mut self, depth: usize, end: usize) {
        match depth {
            1 => {
                if let Some(member) = self.member {
                    self.request[member] = Some(self.member_start..end);
                }
                if self.member == Some(PARAMS) {
                    self.haskell_logging = self
                        .params_logging
                        .take()
                        .filter(|_| self.in_params && self.params_names_decode);
                    self.in_params = false;
                }
            }
            2 if self.in_params && self.logging_member => {
                self.params_logging = Some(self.logging_start..end);
            }
            _ => {}
        }
    }
}

/// The value of a member name given as its JSON string, `None` when it does not decode: when it is
/// not UTF-8 or a `\u` escape is not a Unicode scalar value.
fn decode_name(key: &[u8]) -> Option<Cow<'_, str>> {
    let text = std::str::from_utf8(key).ok()?;
    let inner = &text[1..text.len() - 1];
    if inner.contains('\\') {
        serde_json::from_str::<String>(text).ok().map(Cow::Owned)
    } else {
        Some(Cow::Borrowed(inner))
    }
}

#[cfg(test)]
mod tests;
