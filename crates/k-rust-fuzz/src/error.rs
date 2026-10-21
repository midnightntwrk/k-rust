//! The errors [`crate::Campaign::new`] reports for a specification it refuses (ARCHITECTURE 9.2).
//!
//! A campaign that starts never fails: what goes wrong while it runs is a case class, an engine
//! defect or an aborted outcome in its [`crate::FuzzReport`].

use std::fmt;

/// Why a hole's span does not address exactly one literal (ARCHITECTURE 2.2, T-9).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SpanProblem {
    /// The span names a program other than the campaign's.
    UnknownProgram,
    /// The addressed line does not exist.
    LineOutOfRange,
    /// `find` occurs this many times (not once) in the addressed line or program.
    FindCount(usize),
    /// `literal` occurs this many times (not once) inside `find`.
    LiteralCount(usize),
    /// The hole addresses a configuration variable the definition does not declare, or one the
    /// program binds in no way the hole can replace.
    UnknownConfigVar,
    /// The hole addresses a variable that is not free in the KORE template, or the template has
    /// a free variable that no hole addresses.
    KoreVariable,
    /// A configuration-variable hole's sort is neither the variable's declared sort (given here)
    /// nor a subsort of it, so its values are not values of the variable.
    ConfigVarSort(String),
}

/// Why a hole's sort is refused (ARCHITECTURE 2.4, 3).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SortRefusal {
    /// The sort is not declared by the definition.
    Unknown,
    /// `K`, `KItem` or a cell sort: a hole is data, never a computation.
    Computation,
    /// A user sort in the closure of the program start sort's productions: a sort programs are
    /// written in (`AExp`, `Stmt` in IMP).
    ProgramSyntax,
    /// A user token sort such as `Id`, which names a declaration of the program.
    Token,
    /// A hooked sort without a generator (`Float`, `KVar`, IO handles).
    NoGenerator,
    /// A collection sort without declared element sorts, or with element sorts of the wrong
    /// shape (entries for a list, one element sort for a map).
    Collection,
    /// A collection hole's declared element, key or value sort is refused, for `reason`.
    ElementRefused {
        /// The refused element sort, as declared.
        element: String,
        /// Why it is refused.
        reason: Box<SortRefusal>,
    },
    /// A collection hole declares an element sort that its sort's element production does not
    /// take (`Int` for a list of `Stmt`), so its values would hold ill-sorted elements; no
    /// override admits it.
    ElementNotHeld {
        /// The declared element sort.
        declared: String,
        /// The sort the element production takes at that place.
        element: String,
    },
    /// The sort is missing on one side of a differential campaign (ARCHITECTURE 4.3, R-14).
    MissingOnSide {
        /// `"baseline"` or `"mutant"`.
        side: &'static str,
    },
}

/// Why a target is refused (ARCHITECTURE 4.2, 9.2).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TargetProblem {
    /// No catalog entry matches the rule reference.
    UnknownRule,
    /// Several catalog entries match the rule reference; their ids.
    AmbiguousRule(Vec<String>),
    /// The entry's id is shared by different entries (`shared_identity`).
    SharedIdentity,
    /// The entry is not executable.
    NotExecutable,
    /// The entry's id is `UNKNOWN`.
    UnknownId,
    /// The entry is an equation; equation targets are refused in M1.
    Equation,
    /// The pattern does not compile in the execution definition.
    Pattern(String),
    /// The target kind or option is not provided by this milestone or build (for example
    /// `at: any-state` before G-4, or an observer before FZ-10).
    Unsupported(String),
}

/// A specification [`crate::Campaign::new`] refuses.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CampaignError {
    /// A definition cannot be used: its KORE does not parse, has no digest, or its backend
    /// cannot be built on the route the specification names.
    Definition {
        /// What failed.
        message: String,
    },
    /// The definitions do not match the target: a mutant without a differential target, or a
    /// differential target without a mutant.
    DefinitionsMismatch,
    /// Two holes have the same name.
    DuplicateHole {
        /// The name.
        hole: String,
    },
    /// A hole's location does not address exactly one literal.
    HoleSpan {
        /// The hole's name.
        hole: String,
        /// Why.
        problem: SpanProblem,
    },
    /// Two holes' spans overlap.
    OverlappingHoles {
        /// The first hole's name.
        first: String,
        /// The second hole's name.
        second: String,
    },
    /// A hole's anchor value does not parse back at the hole's sort.
    AnchorDoesNotParse {
        /// The hole's name.
        hole: String,
        /// The parser's message.
        message: String,
    },
    /// A hole's sort is refused, and no override admits it.
    RefusedHoleSort {
        /// The hole's name.
        hole: String,
        /// The sort as declared.
        sort: String,
        /// Why.
        reason: SortRefusal,
    },
    /// A hole's constraints are inconsistent with each other or with its sort.
    InvalidConstraints {
        /// The hole's name.
        hole: String,
        /// Why.
        message: String,
    },
    /// An explicit assignment names an unknown hole or violates a hole's constraints.
    ExplicitAssignment {
        /// The assignment's index in [`crate::ProposerConfig::explicit`].
        index: usize,
        /// The hole's name.
        hole: String,
        /// Why.
        message: String,
    },
    /// The target is unknown, ambiguous or refused.
    Target(TargetProblem),
    /// The program does not assemble, or the backend refuses its initial state, with the holes'
    /// anchor values.
    Program {
        /// What failed.
        message: String,
    },
    /// The normal-termination pattern is missing (the definition does not have exactly one
    /// `<k>` cell) or does not compile.
    NormalEndPattern {
        /// What failed.
        message: String,
    },
    /// The options or proposer configuration are invalid, or name a proposer this milestone or
    /// build does not provide.
    InvalidOptions {
        /// What is wrong.
        message: String,
    },
}

impl fmt::Display for CampaignError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Definition { message } => write!(f, "definition: {message}"),
            Self::DefinitionsMismatch => {
                f.write_str("a mutant definition is given exactly when the target is differential")
            }
            Self::DuplicateHole { hole } => write!(f, "hole `{hole}` is declared twice"),
            Self::HoleSpan { hole, problem } => {
                write!(f, "hole `{hole}`: ")?;
                match problem {
                    SpanProblem::UnknownProgram => f.write_str("names an unknown program"),
                    SpanProblem::LineOutOfRange => f.write_str("its line does not exist"),
                    SpanProblem::FindCount(count) => {
                        write!(f, "`find` occurs {count} times, not once")
                    }
                    SpanProblem::LiteralCount(count) => {
                        write!(f, "`literal` occurs {count} times in `find`, not once")
                    }
                    SpanProblem::UnknownConfigVar => {
                        f.write_str("names a configuration variable it cannot replace")
                    }
                    SpanProblem::KoreVariable => {
                        f.write_str("does not match the KORE template's free variables")
                    }
                    SpanProblem::ConfigVarSort(variable_sort) => write!(
                        f,
                        "its sort is neither the configuration variable's sort `{variable_sort}` \
                         nor a subsort of it"
                    ),
                }
            }
            Self::OverlappingHoles { first, second } => {
                write!(f, "holes `{first}` and `{second}` overlap")
            }
            Self::AnchorDoesNotParse { hole, message } => {
                write!(
                    f,
                    "hole `{hole}`: anchor value does not parse back: {message}"
                )
            }
            Self::RefusedHoleSort { hole, sort, reason } => {
                write!(f, "hole `{hole}`: sort `{sort}` is refused: {reason:?}")
            }
            Self::InvalidConstraints { hole, message } => {
                write!(f, "hole `{hole}`: invalid constraints: {message}")
            }
            Self::ExplicitAssignment {
                index,
                hole,
                message,
            } => write!(f, "explicit assignment {index}, hole `{hole}`: {message}"),
            Self::Target(problem) => write!(f, "target refused: {problem:?}"),
            Self::Program { message } => write!(f, "program: {message}"),
            Self::NormalEndPattern { message } => {
                write!(f, "normal-termination pattern: {message}")
            }
            Self::InvalidOptions { message } => write!(f, "options: {message}"),
        }
    }
}

impl std::error::Error for CampaignError {}

/// A backend failure while a campaign is validated (for example inside
/// `Backend::with_solver`, which hole and value resolution run in) is a definition problem.
impl From<k_rust::backend::BackendError> for CampaignError {
    fn from(error: k_rust::backend::BackendError) -> Self {
        Self::Definition {
            message: error.to_string(),
        }
    }
}

/// A stop while a campaign is validated (`Backend::with_solver`'s stop boundary) is a
/// definition problem: validation runs outside any case and outside the caller's token.
impl From<k_rust::backend::StopCause> for CampaignError {
    fn from(cause: k_rust::backend::StopCause) -> Self {
        Self::Definition {
            message: format!("validation stopped: {cause}"),
        }
    }
}
