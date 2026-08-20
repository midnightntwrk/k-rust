//! Binary KORE encoding and decoding.
//!
//! Binary KORE is a postfix stack encoding used by K backends. Versions 1.0,
//! 1.1, and 1.2 are accepted, matching the pinned Haskell backend. Version 1.2
//! adds an eight-byte payload length to the header.

use std::{collections::BTreeMap, error::Error, fmt};

use super::ast::{Associativity, Pattern, Sort, Symbol, Variable, VariableKind};

const MAGIC: &[u8; 5] = b"\x7fKORE";
const HEADER_SIZE_V1_0: usize = 11;
const HEADER_SIZE_V1_2: usize = 19;

const COMPOSITE_PATTERN: u8 = 0x04;
const STRING_PATTERN: u8 = 0x05;
const COMPOSITE_SORT: u8 = 0x06;
const SORT_VARIABLE: u8 = 0x07;
const SYMBOL: u8 = 0x08;
const VARIABLE_PATTERN: u8 = 0x09;
const VARIABLE: u8 = 0x0d;

/// A supported binary KORE wire-format version.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Version {
    pub major: i16,
    pub minor: i16,
    pub patch: i16,
}

impl Version {
    pub const V1_0_0: Self = Self::new(1, 0, 0);
    pub const V1_1_0: Self = Self::new(1, 1, 0);
    pub const V1_2_0: Self = Self::new(1, 2, 0);
    pub const LATEST: Self = Self::V1_2_0;

    pub const fn new(major: i16, minor: i16, patch: i16) -> Self {
        Self {
            major,
            minor,
            patch,
        }
    }

    fn is_supported(self) -> bool {
        self.major == 1 && (0..=2).contains(&self.minor)
    }

    fn uses_fixed_lengths(self) -> bool {
        self.major == 1 && self.minor == 0
    }

    fn has_payload_length(self) -> bool {
        self >= Self::V1_2_0
    }
}

impl fmt::Display for Version {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}.{}.{}", self.major, self.minor, self.patch)
    }
}

/// A term followed by zero or more side-condition patterns.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConstrainedPattern {
    pub term: Pattern,
    pub constraints: Vec<Pattern>,
}

impl ConstrainedPattern {
    pub fn new(term: Pattern, constraints: Vec<Pattern>) -> Self {
        Self { term, constraints }
    }
}

/// A binary KORE encoding or decoding failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BinaryError {
    pub offset: usize,
    pub message: String,
}

impl BinaryError {
    fn new(offset: usize, message: impl Into<String>) -> Self {
        Self {
            offset,
            message: message.into(),
        }
    }
}

impl fmt::Display for BinaryError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "binary KORE error at byte {}: {}",
            self.offset, self.message
        )
    }
}

impl Error for BinaryError {}

/// Decode a single binary KORE term.
pub fn decode_term(input: &[u8]) -> Result<Pattern, BinaryError> {
    let mut roots = Decoder::new(input)?.decode_block()?;
    if roots.len() != 1 {
        return Err(BinaryError::new(
            input.len(),
            format!("expected one term, found {} stack values", roots.len()),
        ));
    }
    match roots.pop() {
        Some(Block::Pattern(pattern)) => Ok(pattern),
        Some(other) => Err(BinaryError::new(
            input.len(),
            format!("expected a term, found {}", other.kind()),
        )),
        None => unreachable!("the stack length was checked"),
    }
}

/// Decode a term followed by zero or more constraint patterns.
pub fn decode_pattern(input: &[u8]) -> Result<ConstrainedPattern, BinaryError> {
    let roots = Decoder::new(input)?.decode_block()?;
    let mut roots = roots.into_iter();
    let term = expect_pattern(roots.next(), input.len(), "a term")?;
    let constraints = roots
        .map(|block| expect_pattern(Some(block), input.len(), "a constraint"))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(ConstrainedPattern { term, constraints })
}

/// Encode a term with the latest supported binary KORE version.
pub fn encode_term(term: &Pattern) -> Result<Vec<u8>, BinaryError> {
    encode_term_with_version(term, Version::LATEST)
}

/// Encode a term with a selected supported binary KORE version.
pub fn encode_term_with_version(term: &Pattern, version: Version) -> Result<Vec<u8>, BinaryError> {
    encode_roots(std::iter::once(term), version)
}

/// Encode a constrained pattern with the latest supported version.
pub fn encode_pattern(pattern: &ConstrainedPattern) -> Result<Vec<u8>, BinaryError> {
    encode_pattern_with_version(pattern, Version::LATEST)
}

/// Encode a constrained pattern with a selected supported version.
pub fn encode_pattern_with_version(
    pattern: &ConstrainedPattern,
    version: Version,
) -> Result<Vec<u8>, BinaryError> {
    encode_roots(
        std::iter::once(&pattern.term).chain(pattern.constraints.iter()),
        version,
    )
}

fn encode_roots<'a>(
    roots: impl IntoIterator<Item = &'a Pattern>,
    version: Version,
) -> Result<Vec<u8>, BinaryError> {
    if !version.is_supported() {
        return Err(BinaryError::new(
            0,
            format!("unsupported binary KORE version {version}"),
        ));
    }
    let mut payload = Vec::new();
    for root in roots {
        Encoder {
            output: &mut payload,
            version,
        }
        .pattern(root)?;
    }

    let mut output = Vec::with_capacity(
        if version.has_payload_length() {
            HEADER_SIZE_V1_2
        } else {
            HEADER_SIZE_V1_0
        } + payload.len(),
    );
    output.extend_from_slice(MAGIC);
    output.extend_from_slice(&version.major.to_le_bytes());
    output.extend_from_slice(&version.minor.to_le_bytes());
    output.extend_from_slice(&version.patch.to_le_bytes());
    if version.has_payload_length() {
        let length = u64::try_from(payload.len())
            .map_err(|_| BinaryError::new(0, "binary KORE payload is too large"))?;
        output.extend_from_slice(&length.to_le_bytes());
    }
    output.extend(payload);
    Ok(output)
}

fn expect_pattern(
    block: Option<Block>,
    offset: usize,
    expected: &str,
) -> Result<Pattern, BinaryError> {
    match block {
        Some(Block::Pattern(pattern)) => Ok(pattern),
        Some(other) => Err(BinaryError::new(
            offset,
            format!("expected {expected}, found {}", other.kind()),
        )),
        None => Err(BinaryError::new(offset, format!("expected {expected}"))),
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Block {
    Pattern(Pattern),
    String(String),
    Sort(Sort),
    Symbol(Symbol),
}

impl Block {
    fn kind(&self) -> &'static str {
        match self {
            Self::Pattern(_) => "term",
            Self::String(_) => "string",
            Self::Sort(_) => "sort",
            Self::Symbol(_) => "symbol",
        }
    }
}

struct Decoder<'a> {
    input: &'a [u8],
    cursor: usize,
    end: usize,
    version: Version,
    strings: BTreeMap<usize, String>,
    stack: Vec<Block>,
}

impl<'a> Decoder<'a> {
    fn new(input: &'a [u8]) -> Result<Self, BinaryError> {
        if input.len() < HEADER_SIZE_V1_0 || input.get(..MAGIC.len()) != Some(MAGIC) {
            return Err(BinaryError::new(0, "invalid magic header"));
        }
        let version = Version::new(
            i16::from_le_bytes([input[5], input[6]]),
            i16::from_le_bytes([input[7], input[8]]),
            i16::from_le_bytes([input[9], input[10]]),
        );
        if !version.is_supported() {
            return Err(BinaryError::new(
                5,
                format!("unsupported binary KORE version {version}"),
            ));
        }

        let (cursor, end) = if version.has_payload_length() {
            if input.len() < HEADER_SIZE_V1_2 {
                return Err(BinaryError::new(
                    input.len(),
                    "truncated version 1.2 header",
                ));
            }
            let payload_length = u64::from_le_bytes(
                input[11..HEADER_SIZE_V1_2]
                    .try_into()
                    .expect("the header slice has eight bytes"),
            );
            if payload_length == 0 {
                (HEADER_SIZE_V1_2, input.len())
            } else {
                let payload_length = usize::try_from(payload_length)
                    .map_err(|_| BinaryError::new(11, "payload length does not fit usize"))?;
                let end = HEADER_SIZE_V1_2
                    .checked_add(payload_length)
                    .ok_or_else(|| BinaryError::new(11, "payload length overflows usize"))?;
                if end > input.len() {
                    return Err(BinaryError::new(
                        11,
                        format!(
                            "declared payload length {payload_length} exceeds {} available bytes",
                            input.len() - HEADER_SIZE_V1_2
                        ),
                    ));
                }
                if end < input.len() {
                    return Err(BinaryError::new(
                        end,
                        "trailing bytes after binary KORE payload",
                    ));
                }
                (HEADER_SIZE_V1_2, end)
            }
        } else {
            (HEADER_SIZE_V1_0, input.len())
        };

        Ok(Self {
            input,
            cursor,
            end,
            version,
            strings: BTreeMap::new(),
            stack: Vec::new(),
        })
    }

    fn decode_block(mut self) -> Result<Vec<Block>, BinaryError> {
        while self.cursor < self.end {
            let offset = self.cursor;
            match self.byte()? {
                COMPOSITE_PATTERN => self.composite_pattern(offset)?,
                STRING_PATTERN => {
                    let string = self.string()?;
                    self.stack.push(Block::String(string));
                }
                COMPOSITE_SORT => {
                    let arity = self.length(2)?;
                    let name = self.string()?;
                    let arguments = self.pop_sorts(arity, offset)?;
                    self.stack
                        .push(Block::Sort(Sort::Application { name, arguments }));
                }
                SORT_VARIABLE => {
                    let name = self.string()?;
                    self.stack.push(Block::Sort(Sort::Variable(name)));
                }
                SYMBOL => {
                    let arity = self.length(2)?;
                    let name = self.string()?;
                    let sort_parameters = self.pop_sorts(arity, offset)?;
                    self.stack.push(Block::Symbol(Symbol {
                        name,
                        sort_parameters,
                    }));
                }
                VARIABLE_PATTERN => {}
                VARIABLE => {
                    let name = self.string()?;
                    let mut sorts = self.pop_sorts(1, offset)?;
                    let sort = sorts.pop().expect("one sort was requested");
                    let kind = if name.starts_with('@') {
                        VariableKind::Set
                    } else {
                        VariableKind::Element
                    };
                    self.stack.push(Block::Pattern(Pattern::Variable(Variable {
                        kind,
                        name,
                        sort,
                    })));
                }
                tag => {
                    return Err(BinaryError::new(
                        offset,
                        format!("invalid block tag 0x{tag:02x}"),
                    ));
                }
            }
        }
        Ok(self.stack)
    }

    fn composite_pattern(&mut self, offset: usize) -> Result<(), BinaryError> {
        let symbol = match self.stack.pop() {
            Some(Block::Symbol(symbol)) => symbol,
            Some(other) => {
                return Err(BinaryError::new(
                    offset,
                    format!("expected symbol before application, found {}", other.kind()),
                ));
            }
            None => return Err(BinaryError::new(offset, "application has no symbol")),
        };
        let arity = self.length(2)?;
        let arguments = self.pop(arity, offset)?;
        let pattern = application(symbol, arguments, offset)?;
        self.stack.push(Block::Pattern(pattern));
        Ok(())
    }

    fn pop(&mut self, count: usize, offset: usize) -> Result<Vec<Block>, BinaryError> {
        if count > self.stack.len() {
            return Err(BinaryError::new(
                offset,
                format!(
                    "cannot pop {count} values from a stack containing {}",
                    self.stack.len()
                ),
            ));
        }
        Ok(self.stack.split_off(self.stack.len() - count))
    }

    fn pop_sorts(&mut self, count: usize, offset: usize) -> Result<Vec<Sort>, BinaryError> {
        self.pop(count, offset)?
            .into_iter()
            .map(|block| match block {
                Block::Sort(sort) => Ok(sort),
                other => Err(BinaryError::new(
                    offset,
                    format!("expected sort, found {}", other.kind()),
                )),
            })
            .collect()
    }

    fn string(&mut self) -> Result<String, BinaryError> {
        let tag_offset = self.cursor;
        match self.byte()? {
            0x01 => {
                let position = self.cursor;
                let length = self.length(4)?;
                let bytes = self.bytes(length)?;
                let string = std::str::from_utf8(bytes)
                    .map_err(|error| {
                        BinaryError::new(
                            self.cursor - length + error.valid_up_to(),
                            "string is not valid UTF-8",
                        )
                    })?
                    .to_owned();
                self.strings.insert(position, string.clone());
                Ok(string)
            }
            0x02 => {
                let distance = self.length(4)?;
                let target = self.cursor.checked_sub(distance).ok_or_else(|| {
                    BinaryError::new(tag_offset, "string back-reference precedes the input")
                })?;
                self.strings.get(&target).cloned().ok_or_else(|| {
                    BinaryError::new(
                        tag_offset,
                        format!("string back-reference has unknown target {target}"),
                    )
                })
            }
            tag => Err(BinaryError::new(
                tag_offset,
                format!("invalid string tag 0x{tag:02x}"),
            )),
        }
    }

    fn length(&mut self, fixed_width: usize) -> Result<usize, BinaryError> {
        if self.version.uses_fixed_lengths() {
            let bytes = self.bytes(fixed_width)?;
            let mut value = 0usize;
            for byte in bytes {
                value = value
                    .checked_shl(8)
                    .and_then(|value| value.checked_add(usize::from(*byte)))
                    .ok_or_else(|| BinaryError::new(self.cursor, "length overflows usize"))?;
            }
            return Ok(value);
        }

        let start = self.cursor;
        let mut value = 0usize;
        for step in 0..9 {
            let byte = self.byte()?;
            let chunk = usize::from(byte & 0x7f);
            let shifted = chunk
                .checked_shl(7 * step)
                .ok_or_else(|| BinaryError::new(start, "length overflows usize"))?;
            value = value
                .checked_add(shifted)
                .ok_or_else(|| BinaryError::new(start, "length overflows usize"))?;
            if byte & 0x80 == 0 {
                return Ok(value);
            }
        }
        Err(BinaryError::new(
            start,
            "variable-length field has no terminating byte",
        ))
    }

    fn byte(&mut self) -> Result<u8, BinaryError> {
        let offset = self.cursor;
        let byte = self
            .input
            .get(self.cursor)
            .copied()
            .ok_or_else(|| BinaryError::new(offset, "unexpected end of binary KORE payload"))?;
        if self.cursor >= self.end {
            return Err(BinaryError::new(
                offset,
                "read past declared binary KORE payload",
            ));
        }
        self.cursor += 1;
        Ok(byte)
    }

    fn bytes(&mut self, count: usize) -> Result<&'a [u8], BinaryError> {
        let start = self.cursor;
        let end = start
            .checked_add(count)
            .ok_or_else(|| BinaryError::new(start, "byte count overflows usize"))?;
        if end > self.end {
            return Err(BinaryError::new(
                start,
                format!("expected {count} bytes, only {} remain", self.end - start),
            ));
        }
        self.cursor = end;
        Ok(&self.input[start..end])
    }
}

fn application(
    symbol: Symbol,
    arguments: Vec<Block>,
    offset: usize,
) -> Result<Pattern, BinaryError> {
    let name = symbol.name.as_str();
    if name == "\\dv" {
        let [sort] = symbol.sort_parameters.as_slice() else {
            return malformed_application(offset, name, "one sort parameter");
        };
        let [Block::String(value)] = arguments.as_slice() else {
            return malformed_application(offset, name, "one string argument");
        };
        return Ok(Pattern::DomainValue {
            sort: sort.clone(),
            value: value.clone(),
        });
    }

    let arguments = arguments
        .into_iter()
        .map(|block| match block {
            Block::Pattern(pattern) => Ok(pattern),
            Block::String(value) => Ok(Pattern::String(value)),
            other => Err(BinaryError::new(
                offset,
                format!(
                    "application {name} expected term argument, found {}",
                    other.kind()
                ),
            )),
        })
        .collect::<Result<Vec<_>, _>>()?;
    let sorts = &symbol.sort_parameters;

    // Booster's constrained-pattern encoding uses an unparameterized
    // `\equals(predicate, true)` wrapper. It is not a well-sorted standalone
    // KORE pattern, so preserve it as an application for the backend adapter.
    if name == "\\equals" && sorts.is_empty() {
        return Ok(Pattern::Application { symbol, arguments });
    }

    match name {
        "\\top" => {
            let sort = one_sort(sorts, offset, name)?;
            expect_arity(&arguments, 0, offset, name)?;
            Ok(Pattern::Top { sort })
        }
        "\\bottom" => {
            let sort = one_sort(sorts, offset, name)?;
            expect_arity(&arguments, 0, offset, name)?;
            Ok(Pattern::Bottom { sort })
        }
        "\\and" | "\\or" => {
            let sort = one_sort(sorts, offset, name)?;
            if name == "\\and" {
                Ok(Pattern::And { sort, arguments })
            } else {
                Ok(Pattern::Or { sort, arguments })
            }
        }
        "\\not" | "\\next" => {
            let sort = one_sort(sorts, offset, name)?;
            let [argument] = arguments.as_slice() else {
                return malformed_application(offset, name, "one term argument");
            };
            if name == "\\not" {
                Ok(Pattern::Not {
                    sort,
                    argument: Box::new(argument.clone()),
                })
            } else {
                Ok(Pattern::Next {
                    sort,
                    argument: Box::new(argument.clone()),
                })
            }
        }
        "\\implies" | "\\iff" | "\\rewrites" => {
            let sort = one_sort(sorts, offset, name)?;
            let [left, right] = arguments.as_slice() else {
                return malformed_application(offset, name, "two term arguments");
            };
            let (left, right) = (Box::new(left.clone()), Box::new(right.clone()));
            match name {
                "\\implies" => Ok(Pattern::Implies { sort, left, right }),
                "\\iff" => Ok(Pattern::Iff { sort, left, right }),
                _ => Ok(Pattern::Rewrites { sort, left, right }),
            }
        }
        "\\exists" | "\\forall" => {
            let sort = one_sort(sorts, offset, name)?;
            let [Pattern::Variable(variable), body] = arguments.as_slice() else {
                return malformed_application(offset, name, "a variable and a body");
            };
            if variable.kind != VariableKind::Element {
                return malformed_application(offset, name, "an element variable and a body");
            }
            if name == "\\exists" {
                Ok(Pattern::Exists {
                    sort,
                    variable: variable.clone(),
                    body: Box::new(body.clone()),
                })
            } else {
                Ok(Pattern::Forall {
                    sort,
                    variable: variable.clone(),
                    body: Box::new(body.clone()),
                })
            }
        }
        "\\mu" | "\\nu" => {
            expect_sort_arity(sorts, 0, offset, name)?;
            let [Pattern::Variable(variable), body] = arguments.as_slice() else {
                return malformed_application(offset, name, "a set variable and a body");
            };
            if variable.kind != VariableKind::Set {
                return malformed_application(offset, name, "a set variable and a body");
            }
            if name == "\\mu" {
                Ok(Pattern::Mu {
                    variable: variable.clone(),
                    body: Box::new(body.clone()),
                })
            } else {
                Ok(Pattern::Nu {
                    variable: variable.clone(),
                    body: Box::new(body.clone()),
                })
            }
        }
        "\\ceil" | "\\floor" => {
            let [operand_sort, result_sort] = sorts.as_slice() else {
                return malformed_application(offset, name, "two sort parameters");
            };
            let [argument] = arguments.as_slice() else {
                return malformed_application(offset, name, "one term argument");
            };
            if name == "\\ceil" {
                Ok(Pattern::Ceil {
                    operand_sort: operand_sort.clone(),
                    result_sort: result_sort.clone(),
                    argument: Box::new(argument.clone()),
                })
            } else {
                Ok(Pattern::Floor {
                    operand_sort: operand_sort.clone(),
                    result_sort: result_sort.clone(),
                    argument: Box::new(argument.clone()),
                })
            }
        }
        "\\equals" | "\\in" => {
            let [operand_sort, result_sort] = sorts.as_slice() else {
                return malformed_application(offset, name, "two sort parameters");
            };
            let [left, right] = arguments.as_slice() else {
                return malformed_application(offset, name, "two term arguments");
            };
            let fields = (
                operand_sort.clone(),
                result_sort.clone(),
                Box::new(left.clone()),
                Box::new(right.clone()),
            );
            if name == "\\equals" {
                Ok(Pattern::Equals {
                    operand_sort: fields.0,
                    result_sort: fields.1,
                    left: fields.2,
                    right: fields.3,
                })
            } else {
                Ok(Pattern::In {
                    operand_sort: fields.0,
                    result_sort: fields.1,
                    left: fields.2,
                    right: fields.3,
                })
            }
        }
        "\\left-assoc" | "\\right-assoc" => {
            expect_sort_arity(sorts, 0, offset, name)?;
            let [Pattern::Application { symbol, arguments }] = arguments.as_slice() else {
                return malformed_application(offset, name, "one symbol application");
            };
            Ok(Pattern::AssociativeApplication {
                associativity: if name == "\\left-assoc" {
                    Associativity::Left
                } else {
                    Associativity::Right
                },
                symbol: symbol.clone(),
                arguments: arguments.clone(),
            })
        }
        _ => Ok(Pattern::Application { symbol, arguments }),
    }
}

fn one_sort(sorts: &[Sort], offset: usize, symbol: &str) -> Result<Sort, BinaryError> {
    let [sort] = sorts else {
        return malformed_application(offset, symbol, "one sort parameter");
    };
    Ok(sort.clone())
}

fn expect_sort_arity(
    sorts: &[Sort],
    expected: usize,
    offset: usize,
    symbol: &str,
) -> Result<(), BinaryError> {
    if sorts.len() == expected {
        Ok(())
    } else {
        malformed_application(offset, symbol, &format!("{expected} sort parameters"))
    }
}

fn expect_arity(
    arguments: &[Pattern],
    expected: usize,
    offset: usize,
    symbol: &str,
) -> Result<(), BinaryError> {
    if arguments.len() == expected {
        Ok(())
    } else {
        malformed_application(offset, symbol, &format!("{expected} term arguments"))
    }
}

fn malformed_application<T>(offset: usize, symbol: &str, expected: &str) -> Result<T, BinaryError> {
    Err(BinaryError::new(
        offset,
        format!("application {symbol} expected {expected}"),
    ))
}

struct Encoder<'a> {
    output: &'a mut Vec<u8>,
    version: Version,
}

impl Encoder<'_> {
    fn pattern(&mut self, pattern: &Pattern) -> Result<(), BinaryError> {
        match pattern {
            Pattern::String(value) => {
                self.output.push(STRING_PATTERN);
                self.string(value)?;
            }
            Pattern::Variable(variable) => {
                self.sort(&variable.sort)?;
                self.output.push(VARIABLE_PATTERN);
                self.output.push(VARIABLE);
                self.string(&variable.name)?;
            }
            Pattern::Application { symbol, arguments } => {
                self.application(symbol, arguments)?;
            }
            Pattern::Top { sort } => self.ml_application("\\top", &[sort], &[])?,
            Pattern::Bottom { sort } => self.ml_application("\\bottom", &[sort], &[])?,
            Pattern::And { sort, arguments } => {
                let arguments = arguments.iter().collect::<Vec<_>>();
                self.ml_application("\\and", &[sort], &arguments)?;
            }
            Pattern::Or { sort, arguments } => {
                let arguments = arguments.iter().collect::<Vec<_>>();
                self.ml_application("\\or", &[sort], &arguments)?;
            }
            Pattern::Not { sort, argument } => {
                self.ml_application("\\not", &[sort], &[argument.as_ref()])?;
            }
            Pattern::Next { sort, argument } => {
                self.ml_application("\\next", &[sort], &[argument.as_ref()])?;
            }
            Pattern::Implies { sort, left, right } => {
                self.ml_application("\\implies", &[sort], &[left.as_ref(), right.as_ref()])?;
            }
            Pattern::Iff { sort, left, right } => {
                self.ml_application("\\iff", &[sort], &[left.as_ref(), right.as_ref()])?;
            }
            Pattern::Rewrites { sort, left, right } => {
                self.ml_application("\\rewrites", &[sort], &[left.as_ref(), right.as_ref()])?;
            }
            Pattern::Exists {
                sort,
                variable,
                body,
            } => self.quantifier("\\exists", sort, variable, body)?,
            Pattern::Forall {
                sort,
                variable,
                body,
            } => self.quantifier("\\forall", sort, variable, body)?,
            Pattern::Mu { variable, body } => self.fixed_point("\\mu", variable, body)?,
            Pattern::Nu { variable, body } => self.fixed_point("\\nu", variable, body)?,
            Pattern::Ceil {
                operand_sort,
                result_sort,
                argument,
            } => {
                self.ml_application("\\ceil", &[operand_sort, result_sort], &[argument.as_ref()])?
            }
            Pattern::Floor {
                operand_sort,
                result_sort,
                argument,
            } => self.ml_application(
                "\\floor",
                &[operand_sort, result_sort],
                &[argument.as_ref()],
            )?,
            Pattern::Equals {
                operand_sort,
                result_sort,
                left,
                right,
            } => self.ml_application(
                "\\equals",
                &[operand_sort, result_sort],
                &[left.as_ref(), right.as_ref()],
            )?,
            Pattern::In {
                operand_sort,
                result_sort,
                left,
                right,
            } => self.ml_application(
                "\\in",
                &[operand_sort, result_sort],
                &[left.as_ref(), right.as_ref()],
            )?,
            Pattern::DomainValue { sort, value } => {
                self.output.push(STRING_PATTERN);
                self.string(value)?;
                self.symbol("\\dv", std::slice::from_ref(sort))?;
                self.output.push(COMPOSITE_PATTERN);
                self.length(1, 2)?;
            }
            Pattern::AssociativeApplication {
                associativity,
                symbol,
                arguments,
            } => {
                self.application(symbol, arguments)?;
                let name = match associativity {
                    Associativity::Left => "\\left-assoc",
                    Associativity::Right => "\\right-assoc",
                };
                self.symbol(name, &[])?;
                self.output.push(COMPOSITE_PATTERN);
                self.length(1, 2)?;
            }
        }
        Ok(())
    }

    fn quantifier(
        &mut self,
        name: &str,
        sort: &Sort,
        variable: &Variable,
        body: &Pattern,
    ) -> Result<(), BinaryError> {
        self.pattern(&Pattern::Variable(variable.clone()))?;
        self.pattern(body)?;
        self.symbol(name, std::slice::from_ref(sort))?;
        self.output.push(COMPOSITE_PATTERN);
        self.length(2, 2)
    }

    fn fixed_point(
        &mut self,
        name: &str,
        variable: &Variable,
        body: &Pattern,
    ) -> Result<(), BinaryError> {
        self.pattern(&Pattern::Variable(variable.clone()))?;
        self.pattern(body)?;
        self.symbol(name, &[])?;
        self.output.push(COMPOSITE_PATTERN);
        self.length(2, 2)
    }

    fn ml_application(
        &mut self,
        name: &str,
        sorts: &[&Sort],
        arguments: &[&Pattern],
    ) -> Result<(), BinaryError> {
        for argument in arguments {
            self.pattern(argument)?;
        }
        for sort in sorts {
            self.sort(sort)?;
        }
        self.output.push(SYMBOL);
        self.length(sorts.len(), 2)?;
        self.string(name)?;
        self.output.push(COMPOSITE_PATTERN);
        self.length(arguments.len(), 2)
    }

    fn application(&mut self, symbol: &Symbol, arguments: &[Pattern]) -> Result<(), BinaryError> {
        for argument in arguments {
            self.pattern(argument)?;
        }
        self.symbol(&symbol.name, &symbol.sort_parameters)?;
        self.output.push(COMPOSITE_PATTERN);
        self.length(arguments.len(), 2)
    }

    fn symbol(&mut self, name: &str, sorts: &[Sort]) -> Result<(), BinaryError> {
        for sort in sorts {
            self.sort(sort)?;
        }
        self.output.push(SYMBOL);
        self.length(sorts.len(), 2)?;
        self.string(name)
    }

    fn sort(&mut self, sort: &Sort) -> Result<(), BinaryError> {
        match sort {
            Sort::Variable(name) => {
                self.output.push(SORT_VARIABLE);
                self.string(name)
            }
            Sort::Application { name, arguments } => {
                for argument in arguments {
                    self.sort(argument)?;
                }
                self.output.push(COMPOSITE_SORT);
                self.length(arguments.len(), 2)?;
                self.string(name)
            }
        }
    }

    fn string(&mut self, value: &str) -> Result<(), BinaryError> {
        self.output.push(0x01);
        self.length(value.len(), 4)?;
        self.output.extend_from_slice(value.as_bytes());
        Ok(())
    }

    fn length(&mut self, mut value: usize, fixed_width: usize) -> Result<(), BinaryError> {
        if self.version.uses_fixed_lengths() {
            let max = if fixed_width >= std::mem::size_of::<usize>() {
                usize::MAX
            } else {
                (1usize << (fixed_width * 8)) - 1
            };
            if value > max {
                return Err(BinaryError::new(
                    self.output.len(),
                    format!("length {value} does not fit {fixed_width} bytes"),
                ));
            }
            for shift in (0..fixed_width).rev() {
                self.output.push(((value >> (shift * 8)) & 0xff) as u8);
            }
            return Ok(());
        }

        loop {
            let mut byte = (value & 0x7f) as u8;
            value >>= 7;
            if value != 0 {
                byte |= 0x80;
            }
            self.output.push(byte);
            if value == 0 {
                return Ok(());
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kore::parser::parse_pattern;

    fn parsed(source: &str) -> Pattern {
        parse_pattern(source).expect("test pattern should parse")
    }

    #[test]
    fn matches_the_haskell_domain_value_encoding() {
        let encoded =
            encode_term_with_version(&parsed(r#"\dv{SortInt{}}("42")"#), Version::V1_1_0).unwrap();
        assert_eq!(
            encoded,
            b"\x7fKORE\x01\x00\x01\x00\x00\x00\x05\x01\x02\x34\x32\x06\x00\x01\x07SortInt\x08\x01\x01\x03\\dv\x04\x01"
        );
    }

    #[test]
    fn round_trips_every_pattern_form() {
        let sources = [
            r#"foo{S, List{T}}(X:S, @Set:SortSet{}, "value")"#,
            r"\top{S}()",
            r"\bottom{S}()",
            r"\and{S}()",
            r"\and{S}(a{}())",
            r"\or{S}(a{}(), b{}(), c{}())",
            r"\not{S}(a{}())",
            r"\next{S}(a{}())",
            r"\implies{S}(a{}(), b{}())",
            r"\iff{S}(a{}(), b{}())",
            r"\rewrites{S}(a{}(), b{}())",
            r"\exists{S}(X:T, a{}(X:T))",
            r"\forall{S}(X:T, a{}(X:T))",
            r"\mu{}(@X:SortSet{}, \next{SortSet{}}(@X:SortSet{}))",
            r"\nu{}(@X:SortSet{}, \next{SortSet{}}(@X:SortSet{}))",
            r"\ceil{S, SortBool{}}(a{}())",
            r"\floor{S, SortBool{}}(a{}())",
            r"\equals{S, SortBool{}}(a{}(), b{}())",
            r"\in{S, SortBool{}}(a{}(), b{}())",
            r#"\dv{SortString{}}("hello")"#,
            r"\left-assoc{}(f{S}(a{}(), b{}(), c{}()))",
            r"\right-assoc{}(f{S}(a{}(), b{}(), c{}()))",
        ];
        for version in [Version::V1_0_0, Version::V1_1_0, Version::V1_2_0] {
            for source in sources {
                let pattern = parsed(source);
                let encoded = encode_term_with_version(&pattern, version).unwrap();
                assert_eq!(
                    decode_term(&encoded).unwrap(),
                    pattern,
                    "version {version}, source {source}"
                );
            }
        }
    }

    #[test]
    fn round_trips_constrained_patterns() {
        let pattern = ConstrainedPattern::new(
            parsed("state{}(X:S)"),
            vec![
                parsed(r"\equals{S, SortBool{}}(X:S, value{}())"),
                parsed(r"\ceil{S, SortBool{}}(X:S)"),
            ],
        );
        let encoded = encode_pattern(&pattern).unwrap();
        assert_eq!(decode_pattern(&encoded).unwrap(), pattern);
        assert!(decode_term(&encoded).is_err());
    }

    #[test]
    fn preserves_booster_predicate_wrappers() {
        let wrapper = Pattern::Application {
            symbol: Symbol {
                name: "\\equals".into(),
                sort_parameters: Vec::new(),
            },
            arguments: vec![
                parsed("predicate{}()"),
                parsed(r#"\dv{SortBool{}}("true")"#),
            ],
        };
        let pattern = ConstrainedPattern::new(parsed("state{}()"), vec![wrapper]);
        assert_eq!(
            decode_pattern(&encode_pattern(&pattern).unwrap()).unwrap(),
            pattern
        );
    }

    #[test]
    fn decodes_relative_string_back_references() {
        let mut encoded = encode_term_with_version(&parsed("f{}(X:S, Y:S)"), Version::V1_1_0)
            .expect("term should encode");
        let second_literal = encoded
            .windows(3)
            .enumerate()
            .filter(|(_, window)| *window == b"\x01\x01S")
            .nth(1)
            .map(|(offset, _)| offset)
            .expect("sort name occurs twice");
        let first_position = encoded
            .windows(3)
            .position(|window| window == b"\x01\x01S")
            .expect("sort name occurs once")
            + 1;
        let position_after_reference = second_literal + 2;
        let distance = position_after_reference - first_position;
        assert!(distance < 128);
        encoded.splice(second_literal..second_literal + 3, [0x02, distance as u8]);
        assert_eq!(decode_term(&encoded).unwrap(), parsed("f{}(X:S, Y:S)"));
    }

    #[test]
    fn validates_header_lengths_and_stack_shapes() {
        assert_eq!(decode_term(b"not kore").unwrap_err().offset, 0);

        let mut unsupported = encode_term(&parsed("a{}()")).unwrap();
        unsupported[5..7].copy_from_slice(&2_i16.to_le_bytes());
        assert!(unsupported_version(&decode_term(&unsupported).unwrap_err()));

        let mut truncated = encode_term(&parsed("a{}()")).unwrap();
        truncated.pop();
        assert!(decode_term(&truncated).is_err());

        let mut trailing = encode_term(&parsed("a{}()")).unwrap();
        trailing.push(0);
        assert!(decode_term(&trailing).is_err());

        let empty = encode_roots(std::iter::empty(), Version::V1_1_0).unwrap();
        assert!(decode_term(&empty).is_err());
    }

    fn unsupported_version(error: &BinaryError) -> bool {
        error.message.contains("unsupported binary KORE version")
    }
}
