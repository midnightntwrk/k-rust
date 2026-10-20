//! The framer against the framer it replaced, which ran serde_json's raw-value stream parser over
//! the connection one byte per call ([`oracle`]): on every byte stream, cut into reads at every
//! boundary, with read errors between them, both return the same messages and errors, keep the
//! same unframed bytes, and read the same chunks; and the members recorded while framing are
//! those [`object_members`](super::super::object_members) reads from the message.

use std::{
    collections::VecDeque,
    io::{self, Read},
};

use proptest::{
    collection::vec,
    prelude::*,
    sample::{Index, select},
};
use serde_json::value::RawValue;

use super::{Frame, RequestMembers};
use crate::rpc::{object_members, read_json_message, with_request_members};

/// The framer as it was before it scanned its buffer itself: serde_json's stream parser over a
/// reader that hands out one buffered byte per call.
mod oracle {
    use std::io::{self, Read};

    use serde_json::value::RawValue;

    pub(super) struct FramedMessage {
        pub(super) value: Option<Box<RawValue>>,
        pub(super) raw: String,
    }

    pub(super) fn read_json_message(
        reader: &mut impl Read,
        buffer: &mut Vec<u8>,
    ) -> io::Result<Option<FramedMessage>> {
        struct Input<'a, R> {
            reader: &'a mut R,
            buffer: &'a mut Vec<u8>,
            offset: usize,
            scalar_root: Option<bool>,
            chunk_end: &'a mut bool,
        }

        impl<R: Read> Read for Input<'_, R> {
            fn read(&mut self, destination: &mut [u8]) -> io::Result<usize> {
                if self.offset == self.buffer.len() {
                    if self.scalar_root == Some(true) {
                        *self.chunk_end = true;
                        return Ok(0);
                    }
                    let mut chunk = [0; 4096];
                    let read = self.reader.read(&mut chunk)?;
                    self.buffer.extend_from_slice(&chunk[..read]);
                }
                if self.scalar_root.is_none() {
                    self.scalar_root = self
                        .buffer
                        .iter()
                        .find(|byte| !byte.is_ascii_whitespace())
                        .map(|byte| matches!(byte, b't' | b'f' | b'n' | b'-' | b'0'..=b'9'));
                }
                let available = &self.buffer[self.offset..];
                let count = destination.len().min(available.len());
                destination[..count].copy_from_slice(&available[..count]);
                self.offset += count;
                Ok(count)
            }
        }

        loop {
            let mut chunk_end = false;
            let (parsed, parsed_bytes) = {
                let input = Input {
                    reader,
                    scalar_root: buffer
                        .iter()
                        .find(|byte| !byte.is_ascii_whitespace())
                        .map(|byte| matches!(byte, b't' | b'f' | b'n' | b'-' | b'0'..=b'9')),
                    buffer,
                    offset: 0,
                    chunk_end: &mut chunk_end,
                };
                let mut values =
                    serde_json::Deserializer::from_reader(input).into_iter::<Box<RawValue>>();
                let parsed = values.next();
                (parsed, values.byte_offset())
            };
            let (consumed, value) = match parsed {
                Some(Ok(value)) => (parsed_bytes, Some(value)),
                Some(Err(error)) if !error.is_eof() => buffer
                    .iter()
                    .position(|byte| *byte == b'\n')
                    .map_or((buffer.len(), None), |newline| (newline + 1, None)),
                Some(Err(_)) | None if chunk_end => {
                    let mut chunk = [0; 4096];
                    let read = reader.read(&mut chunk)?;
                    if read != 0 {
                        buffer.extend_from_slice(&chunk[..read]);
                        continue;
                    }
                    (buffer.len(), None)
                }
                Some(Err(_)) | None => {
                    if buffer.iter().all(u8::is_ascii_whitespace) {
                        buffer.clear();
                        return Ok(None);
                    }
                    (buffer.len(), None)
                }
            };
            let raw = std::str::from_utf8(&buffer[..consumed])
                .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?
                .to_owned();
            buffer.drain(..consumed);
            return Ok(Some(FramedMessage { value, raw }));
        }
    }
}

/// One result of a read: some bytes, or an error.
#[derive(Clone, Debug)]
enum Step {
    Data(Vec<u8>),
    Fail(io::ErrorKind),
}

/// A connection that returns its steps in order, then the end of the stream forever.
#[derive(Clone, Debug)]
struct Script(VecDeque<Step>);

impl Read for Script {
    fn read(&mut self, destination: &mut [u8]) -> io::Result<usize> {
        assert_eq!(destination.len(), 4096, "every read is one 4096-byte chunk");
        match self.0.pop_front() {
            None => Ok(0),
            Some(Step::Data(bytes)) => {
                destination[..bytes.len()].copy_from_slice(&bytes);
                Ok(bytes.len())
            }
            Some(Step::Fail(kind)) => Err(kind.into()),
        }
    }
}

/// What one call returned: the frame's bytes and its value's text, or the error's kind.
type Observed = Result<Option<(String, Option<String>)>, io::ErrorKind>;

/// The request members as owned text, to compare members read by both sides.
type OwnedMembers = Option<[Option<String>; 5]>;

fn owned(members: Option<RequestMembers<'_>>) -> OwnedMembers {
    members.map(|members| {
        [
            members.jsonrpc,
            members.method,
            members.id,
            members.params,
            members.haskell_logging,
        ]
        .map(|member| member.map(str::to_owned))
    })
}

/// Whether the members recorded while framing are those `object_members` reads from the value,
/// for every set of names the server asks for.
fn members_match(frame: &Frame) -> Result<(), TestCaseError> {
    let value = frame.value();
    let expected = with_request_members(value, owned);
    let actual = owned(frame.members());
    prop_assert_eq!(&actual, &expected, "members of {}", value);
    let id = |members: Option<[Option<Box<RawValue>>; 1]>| {
        members.map(|[id]| id.map(|id| id.get().to_owned()))
    };
    prop_assert_eq!(
        actual.as_ref().map(|members| members[2].clone()),
        id(object_members(value, ["id"]))
    );
    let cancel = object_members(value, ["jsonrpc", "method", "id"])
        .map(|members| members.map(|member| member.map(|member| member.get().to_owned())));
    prop_assert_eq!(
        actual.map(|[jsonrpc, method, id, _, _]| [jsonrpc, method, id]),
        cancel
    );
    Ok(())
}

/// Frames `steps` with both framers until the stream ends or a call fails, and checks that every
/// call returns the same thing, leaves the same unframed bytes and has read the same steps.
fn assert_same_framing(steps: &[Step]) -> Result<usize, TestCaseError> {
    let mut old = Script(steps.iter().cloned().collect());
    let mut new = old.clone();
    let (mut old_buffer, mut new_buffer) = (Vec::new(), Vec::new());
    let bytes: usize = steps
        .iter()
        .map(|step| match step {
            Step::Data(bytes) => bytes.len(),
            Step::Fail(_) => 1,
        })
        .sum();
    for call in 0..4 * bytes + 16 {
        let expected: Observed = oracle::read_json_message(&mut old, &mut old_buffer)
            .map(|message| {
                message.map(|message| {
                    (
                        message.raw,
                        message.value.map(|value| value.get().to_owned()),
                    )
                })
            })
            .map_err(|error| error.kind());
        let mut frame = None;
        let actual: Observed = read_json_message(&mut new, &mut new_buffer)
            .map(|message| {
                message.map(|message| {
                    let value = message.value.as_ref().map(|value| value.value().to_owned());
                    frame = message.value;
                    (message.raw, value)
                })
            })
            .map_err(|error| error.kind());
        prop_assert_eq!(&actual, &expected, "call {}", call);
        prop_assert_eq!(
            &new_buffer,
            &old_buffer,
            "unframed bytes after call {}",
            call
        );
        prop_assert_eq!(new.0.len(), old.0.len(), "steps read by call {}", call);
        if let Some(frame) = &frame {
            members_match(frame)?;
        }
        if !matches!(expected, Ok(Some(_))) {
            return Ok(call + 1);
        }
    }
    Err(TestCaseError::fail("the stream did not end"))
}

fn chunks(bytes: &[u8], size: usize) -> Vec<Step> {
    bytes
        .chunks(size)
        .map(|chunk| Step::Data(chunk.to_vec()))
        .collect()
}

fn data(parts: &[&[u8]]) -> Vec<Step> {
    parts.iter().map(|part| Step::Data(part.to_vec())).collect()
}

/// The messages and errors the new framer returns for `steps`, after checking them against the
/// oracle.
fn framed(steps: &[Step]) -> Vec<Observed> {
    assert_same_framing(steps).unwrap();
    let mut reader = Script(steps.iter().cloned().collect());
    let mut buffer = Vec::new();
    let mut observed = Vec::new();
    loop {
        let next: Observed = read_json_message(&mut reader, &mut buffer)
            .map(|message| {
                message.map(|message| {
                    let value = message.value.map(|value| value.value().to_owned());
                    (message.raw, value)
                })
            })
            .map_err(|error| error.kind());
        let more = matches!(next, Ok(Some(_)));
        observed.push(next);
        if !more {
            return observed;
        }
    }
}

fn message(raw: &str, value: Option<&str>) -> Observed {
    Ok(Some((raw.to_owned(), value.map(str::to_owned))))
}

#[test]
fn a_scalar_ends_where_the_bytes_read_so_far_end() {
    assert_eq!(
        framed(&data(&[b"12", b"34"])),
        [
            message("12", Some("12")),
            message("34", Some("34")),
            Ok(None)
        ]
    );
    assert_eq!(
        framed(&data(&[b"0", b"1"])),
        [message("0", Some("0")), message("1", Some("1")), Ok(None)]
    );
    // A number that cannot end at the end of the bytes is malformed; the rest is a new frame.
    assert_eq!(
        framed(&data(&[b"1.", b"5"])),
        [message("1.", None), message("5", Some("5")), Ok(None)]
    );
    assert_eq!(
        framed(&data(&[b"-", b"1"])),
        [message("-", None), message("1", Some("1")), Ok(None)]
    );
    // An unfinished literal reads once more.
    assert_eq!(
        framed(&data(&[b" tr", b"ue "])),
        [message(" true", Some("true")), Ok(None)]
    );
    assert_eq!(framed(&data(&[b"nu"])), [message("nu", None), Ok(None)]);
    // The read after an unfinished literal ends the connection when it fails, even when it was
    // interrupted.
    assert_eq!(
        framed(&[
            Step::Data(b"fal".to_vec()),
            Step::Fail(io::ErrorKind::Interrupted)
        ]),
        [Err(io::ErrorKind::Interrupted)]
    );
    // A scalar followed by a byte that continues no JSON token is malformed up to the line feed.
    assert_eq!(
        framed(&data(&[b"12x 3\n4"])),
        [message("12x 3\n", None), message("4", Some("4")), Ok(None)]
    );
}

#[test]
fn a_malformed_frame_ends_at_the_first_buffered_line_feed() {
    assert_eq!(
        framed(&data(&[b"\n\n{bad"])),
        [
            message("\n", None),
            message("\n", None),
            message("{bad", None),
            Ok(None)
        ]
    );
    // A pretty-printed malformed message is answered once per line, and a string on one of its
    // lines is a message of its own.
    assert_eq!(
        framed(&data(&[b"{\n\"a\" x}\n"])),
        [
            message("{\n", None),
            message("\"a\"", Some("\"a\"")),
            message(" x}\n", None),
            Ok(None)
        ]
    );
    // Bytes that are not UTF-8 in a malformed frame end the connection.
    assert_eq!(
        framed(&data(&[b"{\"a\":\"\xff\"}\n"])),
        [Err(io::ErrorKind::InvalidData)]
    );
    // A valid JSON value that is not UTF-8 is malformed: here only its first line is dropped.
    assert_eq!(
        framed(&data(&[b"[1,\n\"\xff\"]"])),
        [message("[1,\n", None), Err(io::ErrorKind::InvalidData)]
    );
}

#[test]
fn a_read_error_inside_a_frame_makes_it_malformed() {
    assert_eq!(
        framed(&[
            Step::Data(b"{\"id\":".to_vec()),
            Step::Fail(io::ErrorKind::ConnectionReset),
            Step::Data(b"1}".to_vec()),
        ]),
        [
            message("{\"id\":", None),
            message("1", Some("1")),
            message("}", None),
            Ok(None)
        ]
    );
    // An interrupted read is retried.
    assert_eq!(
        framed(&[
            Step::Data(b"{\"id\":".to_vec()),
            Step::Fail(io::ErrorKind::Interrupted),
            Step::Data(b"1}".to_vec()),
        ]),
        [message("{\"id\":1}", Some("{\"id\":1}")), Ok(None)]
    );
}

#[test]
fn deep_frames_are_framed_like_the_oracle_frames_them() {
    let levels = 100_000;
    let valid = format!("{}{}", "[".repeat(levels), "]".repeat(levels));
    let malformed = format!("{{\"a\":{}}}", "[".repeat(levels));
    let stream = format!(
        "{malformed}\n{valid}\n{{\"jsonrpc\":\"2.0\"}}\n{}",
        "[".repeat(levels)
    );
    assert_eq!(
        assert_same_framing(&chunks(stream.as_bytes(), 4096)).unwrap(),
        5
    );
}

#[test]
fn a_framed_message_takes_its_bytes_out_of_the_buffer() {
    let request = format!(
        r#"{{"jsonrpc":"2.0","id":1,"method":"execute","params":{{"state":"{}"}}}}"#,
        "x".repeat(1 << 20)
    );
    let mut reader = Script(chunks(format!("{request}\n{{}}").as_bytes(), 4096).into());
    let mut buffer = Vec::new();
    let message = read_json_message(&mut reader, &mut buffer)
        .unwrap()
        .unwrap();
    assert_eq!(message.value.unwrap().value(), request);
    assert!(
        buffer.capacity() <= 4096,
        "the connection keeps only the bytes after the message: {}",
        buffer.capacity()
    );
}

#[test]
fn members_are_those_object_members_reads() {
    for text in [
        r#"{"jsonrpc":"2.0","id":1,"method":"execute","params":{"state":1,"haskell-logging":["Rewrite"]}}"#,
        r#"{"id":1,"id":"two","params":{"haskell-logging":1},"params":[{"haskell-logging":2}]}"#,
        r#"{"par\u0061ms":{"haskell\u002dlogging":["a"]},"\u0069d":null}"#,
        r#"{"id":1,"\ud800":2}"#,
        r#"{"params":{"haskell-logging":["a"],"\udc00":1}}"#,
        r#"{"params":{"haskell-logging":["a"]},"params":{"state":{}}}"#,
        r#"{"params":{"x":{"haskell-logging":1}}}"#,
        r#"[{"id":1}]"#,
        r#""id""#,
        "12",
    ] {
        members_match(&Frame::parse(text).unwrap()).unwrap();
    }
}

const WHITESPACE: &[&str] = &["", "", "", " ", "\n", "\t", "\r\n", "  \n  "];

fn whitespace() -> impl Strategy<Value = &'static str> {
    select(WHITESPACE)
}

fn number() -> impl Strategy<Value = String> {
    (
        any::<bool>(),
        select(&["0", "1", "12", "907", "9007199254740993"][..]),
        proptest::option::of(select(&["0", "5", "25"][..])),
        proptest::option::of((
            select(&["e", "E"][..]),
            select(&["", "+", "-"][..]),
            select(&["0", "7", "308"][..]),
        )),
    )
        .prop_map(|(negative, integer, fraction, exponent)| {
            let mut number = String::new();
            if negative {
                number.push('-');
            }
            number.push_str(integer);
            if let Some(fraction) = fraction {
                number.push('.');
                number.push_str(fraction);
            }
            if let Some((e, sign, digits)) = exponent {
                number.push_str(e);
                number.push_str(sign);
                number.push_str(digits);
            }
            number
        })
}

const STRING_PARTS: &[&str] = &[
    "a",
    "Lbl'-LT-'k'-GT-'",
    "SortInt",
    "\\\"",
    "\\\\",
    "\\/",
    "\\b",
    "\\f",
    "\\n",
    "\\r",
    "\\t",
    "\\u0041",
    "\\u00e9",
    "\\ud83d\\ude00",
    "\\ud800",
    "\\udc00",
    "\u{e9}",
    "\u{20ac}",
    "\u{1f600}",
    " ",
    "\u{7f}",
];

fn string() -> impl Strategy<Value = String> {
    vec(select(STRING_PARTS), 0..5).prop_map(|parts| format!("\"{}\"", parts.concat()))
}

const NAMES: &[&str] = &[
    "\"jsonrpc\"",
    "\"method\"",
    "\"id\"",
    "\"params\"",
    "\"haskell-logging\"",
    "\"state\"",
    "\"\\u0069d\"",
    "\"par\\u0061ms\"",
    "\"haskell\\u002dlogging\"",
    "\"\\ud800\"",
    "\"x\"",
];

fn name() -> impl Strategy<Value = String> {
    prop_oneof![
        4 => select(NAMES).prop_map(str::to_owned),
        1 => string(),
    ]
}

fn object(members: Vec<(&str, String, &str, &str, String, &str)>) -> String {
    let members = members
        .iter()
        .map(|(a, name, b, c, value, d)| format!("{a}{name}{b}:{c}{value}{d}"))
        .collect::<Vec<_>>();
    format!("{{{}}}", members.join(","))
}

/// A JSON value with whitespace anywhere between its tokens.
fn value() -> impl Strategy<Value = String> {
    let leaf = prop_oneof![
        number(),
        string(),
        select(&["true", "false", "null"][..]).prop_map(str::to_owned),
    ];
    leaf.prop_recursive(4, 48, 5, |inner| {
        prop_oneof![
            vec((whitespace(), inner.clone(), whitespace()), 0..5).prop_map(|elements| {
                let elements = elements
                    .iter()
                    .map(|(a, element, b)| format!("{a}{element}{b}"))
                    .collect::<Vec<_>>();
                format!("[{}]", elements.join(","))
            }),
            vec(
                (
                    whitespace(),
                    name(),
                    whitespace(),
                    whitespace(),
                    inner,
                    whitespace()
                ),
                0..5
            )
            .prop_map(object),
        ]
    })
}

/// A request object: the members the server reads, repeated or not, among others.
fn request() -> impl Strategy<Value = String> {
    let params = vec(
        (
            whitespace(),
            prop_oneof![
                Just("\"haskell-logging\"".to_owned()),
                Just("\"state\"".to_owned()),
                name()
            ],
            whitespace(),
            whitespace(),
            prop_oneof![
                Just(r#"["Rewrite","Simplify"]"#.to_owned()),
                Just("[]".to_owned()),
                value()
            ],
            whitespace(),
        ),
        0..4,
    )
    .prop_map(object);
    let member = prop_oneof![
        Just(("\"jsonrpc\"".to_owned(), "\"2.0\"".to_owned())),
        select(&["\"execute\"", "\"cancel\"", "\"simplify\"", "1"][..])
            .prop_map(|method| ("\"method\"".to_owned(), method.to_owned())),
        prop_oneof![number(), string(), Just("null".to_owned()), value()]
            .prop_map(|id| ("\"id\"".to_owned(), id)),
        prop_oneof![3 => params, 1 => value()].prop_map(|params| ("\"params\"".to_owned(), params)),
        (name(), value()),
    ];
    vec(
        (
            whitespace(),
            member,
            whitespace(),
            whitespace(),
            whitespace(),
        ),
        0..6,
    )
    .prop_map(|members| {
        object(
            members
                .into_iter()
                .map(|(a, (name, value), b, c, d)| (a, name, b, c, value, d))
                .collect(),
        )
    })
}

const FRAGMENTS: &[&str] = &[
    "1.",
    "-",
    "1e",
    "1e+",
    "01",
    "-0",
    "tr",
    "nul",
    "fals",
    "true",
    "null",
    "12",
    "\"\\u12",
    "\"\\x\"",
    "\"a\nb\"",
    "{bad}",
    "{\"a\":1,}",
    "[1,]",
    "[1 2]",
    "{\"a\" 1}",
    "{1:2}",
    "}",
    "]",
    ",",
    ":",
    "\n",
    "\n\n",
    "\r\n",
    "\u{c}",
    "[",
    "{",
    "\"",
];

const ALPHABET: &[u8] = b"{}[],:\"\\ \n\t\r0123456789-+.eEtrufalsnx\x00\x0c\x1f\x7f\x80\xbf\xc3\xa9\xe2\x82\xac\xf0\x9f\xff";

fn piece() -> impl Strategy<Value = Vec<u8>> {
    prop_oneof![
        4 => request().prop_map(String::into_bytes),
        3 => value().prop_map(String::into_bytes),
        2 => select(FRAGMENTS).prop_map(|fragment| fragment.as_bytes().to_vec()),
        1 => vec(select(ALPHABET), 0..8),
        1 => vec(request(), 1..3).prop_map(|requests| format!("[{}]", requests.join(",")).into_bytes()),
    ]
}

fn stream() -> impl Strategy<Value = Vec<u8>> {
    (
        vec(
            (piece(), select(&["", "\n", " ", "\r\n", "\n\n"][..])),
            0..8,
        ),
        vec((any::<Index>(), 0..3u8, select(ALPHABET)), 0..3),
    )
        .prop_map(|(pieces, mutations)| {
            let mut bytes = Vec::new();
            for (piece, separator) in pieces {
                bytes.extend(piece);
                bytes.extend(separator.as_bytes());
            }
            for (at, operation, byte) in mutations {
                if bytes.is_empty() {
                    bytes.push(byte);
                    continue;
                }
                let at = at.index(bytes.len());
                match operation {
                    0 => bytes[at] = byte,
                    1 => bytes.insert(at, byte),
                    _ => {
                        bytes.remove(at);
                    }
                }
            }
            bytes
        })
}

/// `bytes` cut into reads of the given sizes (the last size repeats), with read errors before
/// some of them.
fn steps(bytes: &[u8], sizes: &[usize], failures: &[(Index, io::ErrorKind)]) -> Vec<Step> {
    let mut steps = Vec::new();
    let mut rest = bytes;
    let mut size = sizes.iter().copied().chain(std::iter::repeat(4096));
    while !rest.is_empty() {
        let (chunk, tail) = rest.split_at(size.next().unwrap().min(rest.len()));
        steps.push(Step::Data(chunk.to_vec()));
        rest = tail;
    }
    for (at, kind) in failures {
        let at = at.index(steps.len() + 1);
        steps.insert(at, Step::Fail(*kind));
    }
    steps
}

fn read_sizes() -> impl Strategy<Value = Vec<usize>> {
    vec(
        prop_oneof![3 => 1usize..=3, 3 => 1usize..=64, 1 => 1usize..=4096],
        0..48,
    )
}

fn failures() -> impl Strategy<Value = Vec<(Index, io::ErrorKind)>> {
    prop_oneof![
        4 => Just(Vec::new()),
        1 => vec(
            (
                any::<Index>(),
                select(
                    &[
                        io::ErrorKind::Interrupted,
                        io::ErrorKind::ConnectionReset,
                        io::ErrorKind::WouldBlock,
                    ][..]
                )
            ),
            1..3
        ),
    ]
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(4000))]

    #[test]
    fn framing_matches_the_oracle(
        bytes in stream(),
        sizes in read_sizes(),
        failures in failures(),
    ) {
        assert_same_framing(&steps(&bytes, &sizes, &failures))?;
    }

    #[test]
    fn request_members_match_object_members(request in request()) {
        members_match(&Frame::parse(&request).unwrap())?;
    }
}
