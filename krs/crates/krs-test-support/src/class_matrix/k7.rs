//! K7's generator data: what a case's sentence must do when it runs.
//!
//! K7 runs each accepted case on a program and checks that the case's sentence applied, and where
//! the generator states it, the value it built. What the run must show is stated here from what
//! each construct denotes, never from what KRS emits or runs, as the oracle states what a
//! construct means: a disagreement with KRS is a finding.
//!
//! - A spelling at a matched position has a *witness*, a ground term it matches, with the
//!   template's binders at their fixed values (`x` is 1): `Cmd::Hold(x)` matches `Cmd::Hold(1)`.
//! - A spelling at a built position has a *value*, what it denotes under the same binders:
//!   `x + 1` is 2, `map![x -> 1, 2 -> 3]` the map `{1 ↦ 1, 2 ↦ 3}`.
//! - A spelling with no witness (no ground term matches it) or no stated value says why
//!   ([`Meaning`]); K7 then checks only that the sentence applied, or nothing ([`Status`]).
//!
//! Each slot of the term families has a *driver* (`terms::drivers`): the program that applies the
//! case's command to the witness, or writes the case's alias or desugar subject, and the cells the
//! run must end with. Those are a [`Run`]; a case K7 does not run has a [`Skip`] with its reason.

use std::collections::BTreeMap;
use std::fmt;

/// A ground term the generator states: a witness, a value, or a cell's content after a run.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Ground {
    /// An `Int`.
    Int(i64),
    /// A `Bool`.
    Bool(bool),
    /// A `String`.
    String(String),
    /// A `Float`, by the shortest decimal text of its `f64` (`1.5`).
    Float(String),
    /// A `Bytes`.
    Bytes(Vec<u8>),
    /// A token of a sort without a builtin hook: an `Id` (`$x`) or a declared token sort's.
    Token {
        /// The sort's name: `Id`, or the token sort's Rust path (`Word`).
        sort: String,
        /// The token's text.
        text: String,
    },
    /// A constructor application: its production's Rust path from the crate root (`Cmd::Hold`)
    /// and its fields in declaration order.
    Ctor {
        /// The production's path.
        path: String,
        /// The fields, in declaration order.
        fields: Vec<Ground>,
    },
    /// The application of a function no equation of the definition evaluates, which stays as
    /// written (`Size(1)`, `size(1)` in K): its K label and its arguments.
    Unevaluated {
        /// The function's K label.
        label: String,
        /// The arguments.
        arguments: Vec<Ground>,
    },
    /// A `List`.
    List(Vec<Ground>),
    /// A `Set`, its elements ordered and distinct ([`Ground::set`]).
    Set(Vec<Ground>),
    /// A `Map`, one entry per key, ordered by key ([`Ground::map`]).
    Map(Vec<(Ground, Ground)>),
    /// A K sequence, the computation cell's content.
    Seq(Vec<Ground>),
    /// An optional cell the state does not hold.
    Absent,
    /// Any term: a run must show that the sentence applied, but the generator states no value.
    Any,
    /// A term a run showed that has no form above (a freezer, a variable, `\bottom`'s parts),
    /// by its text. The generator never states one, and it agrees only with [`Ground::Any`].
    Opaque(String),
}

impl Ground {
    /// A constructor application.
    #[must_use]
    pub fn ctor(path: &str, fields: Vec<Self>) -> Self {
        Self::Ctor {
            path: path.to_owned(),
            fields,
        }
    }

    /// A `String`.
    #[must_use]
    pub fn string(text: &str) -> Self {
        Self::String(text.to_owned())
    }

    /// A `Float` of `value`.
    #[must_use]
    pub fn float(value: f64) -> Self {
        Self::Float(format!("{value:?}"))
    }

    /// A token of `sort`.
    #[must_use]
    pub fn token(sort: &str, text: &str) -> Self {
        Self::Token {
            sort: sort.to_owned(),
            text: text.to_owned(),
        }
    }

    /// An application no equation evaluates.
    #[must_use]
    pub fn unevaluated(label: &str, arguments: Vec<Self>) -> Self {
        Self::Unevaluated {
            label: label.to_owned(),
            arguments,
        }
    }

    /// A `Set` of `elements`: the same set whatever their order, each element once.
    #[must_use]
    pub fn set(elements: Vec<Self>) -> Self {
        let mut elements = elements;
        elements.sort();
        elements.dedup();
        Self::Set(elements)
    }

    /// A `Map` of `entries`, each written over the map before it: of two entries at one key,
    /// the later one's value is the map's.
    #[must_use]
    pub fn map(entries: Vec<(Self, Self)>) -> Self {
        Self::Map(
            entries
                .into_iter()
                .collect::<BTreeMap<_, _>>()
                .into_iter()
                .collect(),
        )
    }

    /// Whether the term is of the terms base's `Stmt`, which a program is: an `Int` (below
    /// `Value`) or an application of a `Cmd` variant.
    #[must_use]
    pub fn is_statement(&self) -> bool {
        match self {
            Self::Int(_) => true,
            Self::Ctor { path, .. } => path.starts_with("Cmd::"),
            _ => false,
        }
    }

    /// Whether a run's term `observed` is this term: [`Ground::Any`] agrees with every term, and
    /// a constructor's path with every path that ends with it at a `::`.
    #[must_use]
    pub fn agrees(&self, observed: &Self) -> bool {
        let all = |expected: &[Self], observed: &[Self]| {
            expected.len() == observed.len()
                && expected
                    .iter()
                    .zip(observed)
                    .all(|(expected, observed)| expected.agrees(observed))
        };
        match (self, observed) {
            (Self::Any, _) => true,
            (
                Self::Ctor { path, fields },
                Self::Ctor {
                    path: other,
                    fields: values,
                },
            ) => {
                (path == other
                    || other
                        .strip_suffix(path.as_str())
                        .is_some_and(|prefix| prefix.ends_with("::")))
                    && all(fields, values)
            }
            (
                Self::Unevaluated { label, arguments },
                Self::Unevaluated {
                    label: other,
                    arguments: values,
                },
            ) => label == other && all(arguments, values),
            (Self::List(expected), Self::List(observed))
            | (Self::Set(expected), Self::Set(observed))
            | (Self::Seq(expected), Self::Seq(observed)) => all(expected, observed),
            (Self::Map(expected), Self::Map(observed)) => {
                expected.len() == observed.len()
                    && expected.iter().zip(observed).all(|(expected, observed)| {
                        expected.0.agrees(&observed.0) && expected.1.agrees(&observed.1)
                    })
            }
            _ => self == observed,
        }
    }

    /// The term in the program grammar of the terms base, which a driver's program writes, or
    /// `None` for a term no program writes. Each constructor is written by its terminal, the
    /// variant's name in lower case; a `Wrap` at the `KItem` instance, a collection and the `Id`
    /// `$x`, which the grammar has no syntax for, by the base's makers (`wk`, `lone`, `sone`,
    /// `mput`, `idx`, ..), each a function that evaluates to exactly that value.
    #[must_use]
    pub fn program(&self) -> Option<String> {
        self.written(true)
    }

    /// The term as a program writes it without a maker, or `None`: what a static clause's
    /// expansion of a program meets, as it rewrites the program as written, before any function
    /// is evaluated.
    #[must_use]
    pub fn literal_program(&self) -> Option<String> {
        self.written(false)
    }

    fn written(&self, makers: bool) -> Option<String> {
        let list = |terms: &[Self]| -> Option<String> {
            let written = terms
                .iter()
                .map(|term| term.written(makers))
                .collect::<Option<Vec<_>>>()?;
            Some(written.join(", "))
        };
        let made = |text: String| makers.then_some(text);
        Some(match self {
            Self::Int(value) => value.to_string(),
            Self::Bool(value) => value.to_string(),
            Self::String(text) => format!("{text:?}"),
            Self::Float(text) => text.clone(),
            Self::Bytes(bytes) => bytes_literal(bytes),
            Self::Token { sort, text } if sort == "Id" && text == "$x" => made("idx".to_owned())?,
            Self::Token { sort, text } if sort == "Word" => text.clone(),
            Self::Ctor { path, fields } => {
                let name = path.rsplit("::").next().unwrap_or(path).to_lowercase();
                let name = if name == "wrap" {
                    made("wk".to_owned())?
                } else {
                    name
                };
                if fields.is_empty() {
                    name
                } else {
                    format!("{name}({})", list(fields)?)
                }
            }
            Self::Unevaluated { label, arguments } => format!("{label}({})", list(arguments)?),
            Self::List(items) => made(
                items
                    .iter()
                    .map(|item| Some(format!("lone({})", item.written(makers)?)))
                    .reduce(|left, right| Some(format!("lcat({}, {})", left?, right?)))
                    .unwrap_or_else(|| Some("lemp".to_owned()))?,
            )?,
            Self::Set(elements) => made(
                elements
                    .iter()
                    .map(|element| Some(format!("sone({})", element.written(makers)?)))
                    .reduce(|left, right| Some(format!("sunion({}, {})", left?, right?)))
                    .unwrap_or_else(|| Some("semp".to_owned()))?,
            )?,
            Self::Map(entries) => {
                let mut written = made("memp".to_owned())?;
                for (key, value) in entries {
                    written = format!(
                        "mput({written}, {}, {})",
                        key.written(makers)?,
                        value.written(makers)?
                    );
                }
                written
            }
            Self::Token { .. } | Self::Seq(_) | Self::Absent | Self::Any | Self::Opaque(_) => {
                return None;
            }
        })
    }
}

impl fmt::Display for Ground {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let list = |formatter: &mut fmt::Formatter<'_>, terms: &[Self]| {
            for (index, term) in terms.iter().enumerate() {
                if index > 0 {
                    formatter.write_str(", ")?;
                }
                write!(formatter, "{term}")?;
            }
            Ok(())
        };
        match self {
            Self::Int(value) => write!(formatter, "{value}"),
            Self::Bool(value) => write!(formatter, "{value}"),
            Self::String(text) => write!(formatter, "{text:?}"),
            Self::Float(text) | Self::Token { text, .. } => formatter.write_str(text),
            Self::Bytes(bytes) => formatter.write_str(&bytes_literal(bytes)),
            Self::Ctor { path, fields } => {
                write!(formatter, "{path}(")?;
                list(formatter, fields)?;
                formatter.write_str(")")
            }
            Self::Unevaluated { label, arguments } => {
                write!(formatter, "{label}(")?;
                list(formatter, arguments)?;
                formatter.write_str(")")
            }
            Self::List(items) => {
                formatter.write_str("[")?;
                list(formatter, items)?;
                formatter.write_str("]")
            }
            Self::Set(elements) => {
                formatter.write_str("set{")?;
                list(formatter, elements)?;
                formatter.write_str("}")
            }
            Self::Map(entries) => {
                formatter.write_str("map{")?;
                for (index, (key, value)) in entries.iter().enumerate() {
                    if index > 0 {
                        formatter.write_str(", ")?;
                    }
                    write!(formatter, "{key} -> {value}")?;
                }
                formatter.write_str("}")
            }
            Self::Seq(items) => {
                formatter.write_str("k[")?;
                list(formatter, items)?;
                formatter.write_str("]")
            }
            Self::Absent => formatter.write_str("absent"),
            Self::Any => formatter.write_str("_"),
            Self::Opaque(text) => write!(formatter, "<{text}>"),
        }
    }
}

/// The Bytes literal a program writes for `bytes`, by K's lexical syntax for Bytes (`domains.md`,
/// `BYTES-SYNTAX`), in the one spelling KRS writes a Bytes value in: a printable ASCII character
/// but `"` and `\` as itself, `\` and a newline, a tab, a carriage return and a form feed by their
/// one-letter escapes, and any other byte as `\xHH`, `"` included, which emitted K's `#token`
/// cannot carry as `\"`. (Rust's `escape_ascii` writes `\'`, which K's lexer refuses.)
fn bytes_literal(bytes: &[u8]) -> String {
    let mut literal = String::from("b\"");
    for &byte in bytes {
        match byte {
            b'\\' => literal.push_str("\\\\"),
            b'"' => literal.push_str("\\x22"),
            b'\n' => literal.push_str("\\n"),
            b'\t' => literal.push_str("\\t"),
            b'\r' => literal.push_str("\\r"),
            0x0c => literal.push_str("\\f"),
            b' '..=b'~' => literal.push(char::from(byte)),
            _ => {
                use std::fmt::Write as _;
                write!(literal, "\\x{byte:02x}").expect("writing to a String cannot fail");
            }
        }
    }
    literal.push('"');
    literal
}

/// What a spelling denotes where it is built, with the template's binders at their fixed values.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Meaning {
    /// The value.
    Value(Ground),
    /// A value the generator does not state, with the reason: K7 checks only that the sentence
    /// applied.
    Unstated(&'static str),
    /// No value: the term is undefined under the binders' values, with the reason. K7 checks
    /// nothing at a position that builds it, but where it is a condition, which then does not
    /// hold, so the sentence must not apply.
    Undefined(&'static str),
    /// No term: a pattern-only construct, a predicate, an anonymous variable or a cell fragment,
    /// which builds no value of the position, with the reason. K7 checks nothing where it is built.
    NoTerm(&'static str),
}

/// What K7 checks of a case that it runs.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Status {
    /// The sentence applied, and the value the generator states for the case's construct is the
    /// one the run built or looked up.
    Value,
    /// The sentence applied: on the construct's witness, where it is matched, or to a value the
    /// generator does not state.
    Liveness,
    /// A static clause's counter run: its subject does not match the program, so the program's
    /// expansion leaves the case's production unexpanded, which `krs run` refuses to execute.
    Unexpanded,
}

impl Status {
    /// The status's name, as a shard prints it.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Value => "value",
            Self::Liveness => "liveness",
            Self::Unexpanded => "unexpanded",
        }
    }
}

/// A case's run: its program, given to the run commands' path as `krs run` reads a file, and
/// what the run must show.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Run {
    /// The program, bound to `$PGM`.
    pub program: String,
    /// The configuration variables, as `krs run -c NAME=TEXT` binds them.
    pub variables: Vec<(String, String)>,
    /// The run's step bound. A sentence that applies again to what it wrote is observed after
    /// the steps the driver counts, not run on.
    pub depth: u64,
    /// The rewrite steps the run takes when the case's sentence applies as stated: the driver's
    /// setup steps and the sentence's own. Fewer steps is a sentence that did not apply.
    pub steps: u64,
    /// The cells the final state holds, by the Rust path of their fields (`k`, `env`,
    /// `frame.ret`). A repeated cell is read by its path and its instances' children, each instance
    /// the constructor named after the collection's field of its children's values:
    /// `queue.job[payload]` a List collection's, a [`Ground::List`] in order, and `shelf.bag{key,m}`
    /// a Set collection's, a [`Ground::Set`]. An optional cell the state does not hold is
    /// [`Ground::Absent`].
    pub cells: Vec<(String, Ground)>,
    /// What the run checks.
    pub status: Status,
}

/// Why K7 does not run a case.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum SkipKind {
    /// The case's form or slot has no driver.
    Form,
    /// The case's construct has no witness at a matched position, or none a program can write.
    Witness,
    /// The case's construct has no value at a built position.
    Value,
}

impl SkipKind {
    /// The kind's name, as a shard prints it.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Form => "no driver",
            Self::Witness => "no witness",
            Self::Value => "no value",
        }
    }
}

/// A case K7 does not run, and why.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Skip {
    /// What is missing.
    pub kind: SkipKind,
    /// Why.
    pub reason: String,
}

/// What K7 does with a case.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum K7 {
    /// It runs the case.
    Run(Run),
    /// It does not.
    Skip(Skip),
}

impl K7 {
    /// A case K7 does not run.
    #[must_use]
    pub fn skip(kind: SkipKind, reason: impl Into<String>) -> Self {
        Self::Skip(Skip {
            kind,
            reason: reason.into(),
        })
    }

    /// The case's status: its run's, or its skip's kind.
    #[must_use]
    pub fn status(&self) -> &'static str {
        match self {
            Self::Run(run) => run.status.name(),
            Self::Skip(skip) => skip.kind.name(),
        }
    }
}
