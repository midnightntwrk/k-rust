//! The errors [`crate::Campaign::new`] reports for a specification it refuses (ARCHITECTURE 9.2).
//!
//! A campaign that starts never fails: what goes wrong while it runs is a case class, an engine
//! defect or an aborted outcome in its [`crate::FuzzReport`].

use std::fmt;

use crate::target::{RuleName, RuleRef};

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
    /// A `column` is given without a `line`.
    ColumnWithoutLine,
    /// The text at `line` and `column` is not `literal` (or the line is shorter).
    LiteralNotAtColumn,
    /// A `column` places the literal, and `find` is neither empty nor the literal: the two
    /// addresses could disagree.
    FindWithColumn,
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
    /// A value of the hole's sort may contain `sort`, which is refused for `reason`: reached
    /// from the hole's sort through the sorts `through` (none when the hole's sort's own
    /// constructors take it), each of them data that holds the next.
    Contains {
        /// The refused sort a value may contain.
        sort: String,
        /// The data sorts between the hole's sort and it, outermost first.
        through: Vec<String>,
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

/// The words of a refusal: why the sort is refused and, where an author can act, what to do.
impl fmt::Display for SortRefusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        const OVERRIDE: &str = "a hole's `allow-refused-sort = true` (library \
                                `HoleDecl::allow_refused_sort`) admits it, and the report \
                                records the override";
        match self {
            Self::Unknown => f.write_str("the definition declares no sort of that name"),
            Self::Computation => f.write_str(
                "it is `K`, `KItem` or a cell sort: a hole is data, never a computation",
            ),
            Self::ProgramSyntax => write!(
                f,
                "programs are written in it (it lies in the closure of the program start \
                 sort's productions), and a hole is data, never program text; {OVERRIDE}"
            ),
            Self::Token => write!(
                f,
                "it is a user token sort, whose tokens name declarations of the program (as an \
                 `Id` does), so a value of it edits the program; {OVERRIDE}, and its values are \
                 then written as tokens, such as `{{ token = {{ sort = \"Id\", text = \"n\" }} }}`"
            ),
            Self::NoGenerator => f.write_str(
                "it is hooked to a builtin that has no value generator (such as `Float` or an \
                 input/output handle)",
            ),
            Self::Collection => f.write_str(
                "it is a collection whose element sorts are not declared, or not in the shape \
                 its kind takes: declare `elements = { element = \"Int\" }` for a list or a \
                 set, `elements = { key = \"Id\", value = \"Int\" }` for a map",
            ),
            Self::ElementRefused { element, reason } => {
                write!(f, "its element sort `{element}` is refused: {reason}")
            }
            Self::Contains {
                sort,
                through,
                reason,
            } => {
                write!(f, "its values may contain `{sort}`")?;
                if !through.is_empty() {
                    let through = through
                        .iter()
                        .map(|sort| format!("`{sort}`"))
                        .collect::<Vec<_>>()
                        .join(", then ");
                    write!(f, " (through {through})")?;
                }
                write!(f, ", which is refused: {reason}")
            }
            Self::ElementNotHeld { declared, element } => write!(
                f,
                "its declared element sort `{declared}` is not what the collection's element \
                 production takes there (`{element}`), so its values would hold ill-sorted \
                 elements; no override admits it"
            ),
            Self::MissingOnSide { side } => write!(
                f,
                "the {side} definition of the differential pair does not declare it, so a value \
                 of it means nothing there"
            ),
        }
    }
}

/// Why a target is refused (ARCHITECTURE 4.2, 9.2). [`fmt::Display`] says why in words, with
/// the rules an author can name instead.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TargetProblem {
    /// No catalog entry matches the rule reference.
    UnknownRule(Box<UnknownRule>),
    /// Catalog entries with different ids match the rule reference: each id, in order, with its
    /// names.
    AmbiguousRule(Vec<(String, RuleName)>),
    /// A source position whose file names several files of the catalog, whatever its line
    /// ([`RuleRef::Source`]): the line of a rule in one file may be a comment in another.
    AmbiguousSource {
        /// The source as given.
        source: String,
        /// The files it names, each by the shortest reference that names it alone.
        files: Vec<String>,
    },
    /// The entry's id is shared by different entries (`shared_identity`).
    SharedIdentity,
    /// The entry is not executable.
    NotExecutable,
    /// The entry's id is `UNKNOWN`.
    UnknownId,
    /// The entry is an equation; equation targets are refused in M1.
    Equation,
    /// The pattern does not compile in the execution definition, or is refused (a `requires`
    /// that reads a variable its configuration does not bind). Positions in the message are
    /// lines and columns of the pattern's own text (`line 1, column 23`).
    Pattern(String),
    /// The target kind or option is not provided by this milestone or build (for example
    /// `at: any-state` before G-4, or an observer before FZ-10).
    Unsupported(String),
}

/// A rule reference that no catalog entry matches, with what the definition offers instead
/// (ARCHITECTURE 4.2).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UnknownRule {
    /// The reference as given.
    pub reference: RuleRef,
    /// The entries the reference may have meant, each id with its names, nearest first: for a
    /// label, the entries whose label is nearest it, then those whose id starts with it; for a
    /// unique id, the entries whose id starts with it; for a source position in a file that
    /// holds entries, the entries of that file written nearest the line.
    pub candidates: Vec<(String, RuleName)>,
    /// For a label: the definition's executable rewrite rules without a label, which only their
    /// source position or unique id names.
    pub unlabelled: usize,
    /// For a source position in a file that holds no catalog entry: the files that hold
    /// rewrite rules, each by the shortest reference that names it alone
    /// ([`crate::target::RuleLocation::reference`]).
    pub sources: Vec<String>,
}

/// Candidate rules as lines of a refusal ([`RuleName::describe`]).
fn write_rules(f: &mut fmt::Formatter<'_>, rules: &[(String, RuleName)]) -> fmt::Result {
    for (id, name) in rules {
        write!(f, "\n  {}", name.describe(id))?;
    }
    Ok(())
}

impl fmt::Display for UnknownRule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.reference {
            RuleRef::Label(label) => {
                write!(f, "no rule has the label `{label}`")?;
                if !self.candidates.is_empty() {
                    f.write_str("; the nearest are:")?;
                }
            }
            RuleRef::UniqueId(id) => {
                write!(
                    f,
                    "no rule or equation has the unique id `{id}` (an id is a digest of the \
                     rule's text, so an edited rule has another id)"
                )?;
                if !self.candidates.is_empty() {
                    f.write_str("; the ids that start with it are:")?;
                }
            }
            RuleRef::Source { source, line } if !self.sources.is_empty() => {
                write!(
                    f,
                    "no rule is written in `{source}` (line {line}); the rules are written in:"
                )?;
                for written in &self.sources {
                    write!(f, "\n  {written}")?;
                }
            }
            RuleRef::Source { source, line } => {
                write!(f, "no rule or equation spans line {line} of `{source}`")?;
                if !self.candidates.is_empty() {
                    f.write_str("; the nearest are:")?;
                }
            }
        }
        write_rules(f, &self.candidates)?;
        match self.unlabelled {
            0 => {}
            1 => f.write_str(
                "\n1 rewrite rule has no label: name it by its source position (FILE:LINE, any \
                 line of the rule) or its unique id",
            )?,
            unlabelled => write!(
                f,
                "\n{unlabelled} rewrite rules have no label: name one by its source position \
                 (FILE:LINE, any line of the rule) or its unique id"
            )?,
        }
        Ok(())
    }
}

impl fmt::Display for TargetProblem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownRule(unknown) => write!(f, "{unknown}"),
            Self::AmbiguousRule(rules) => {
                write!(
                    f,
                    "the reference names {} different rules; name one by its unique id:",
                    rules.len()
                )?;
                write_rules(f, rules)
            }
            Self::AmbiguousSource { source, files } => {
                write!(
                    f,
                    "`{source}` names {} files of the definition; name one by a longer path:",
                    files.len()
                )?;
                for file in files {
                    write!(f, "\n  {file}")?;
                }
                Ok(())
            }
            Self::SharedIdentity => f.write_str(
                "the rule's unique id is shared by other catalog entries, so coverage and \
                 traces, which record ids, cannot tell its steps from theirs",
            ),
            Self::NotExecutable => {
                f.write_str("the rule is not executable, so no step of a run applies it")
            }
            Self::UnknownId => f.write_str(
                "the rule has the generated id `UNKNOWN`, which other generated sentences share",
            ),
            Self::Equation => f.write_str(
                "the reference names an equation, not a rewrite rule; a rule target names a \
                 rewrite rule (target a rewrite rule whose step evaluates the function instead)",
            ),
            Self::Pattern(message) => write!(f, "the target pattern is refused: {message}"),
            Self::Unsupported(message) => f.write_str(message),
        }
    }
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
                    SpanProblem::ColumnWithoutLine => {
                        f.write_str("its `column` needs a `line` to count in")
                    }
                    SpanProblem::LiteralNotAtColumn => f.write_str(
                        "its `literal` does not start at its `line` and `column` (columns are \
                         one-based and count characters)",
                    ),
                    SpanProblem::FindWithColumn => f.write_str(
                        "its `column` places the literal, so `find` must be left out (or be the \
                         literal itself)",
                    ),
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
                write!(f, "hole `{hole}`: sort `{sort}` is refused: {reason}")
            }
            Self::InvalidConstraints { hole, message } => {
                write!(f, "hole `{hole}`: invalid constraints: {message}")
            }
            Self::ExplicitAssignment {
                index,
                hole,
                message,
            } => write!(f, "explicit assignment {index}, hole `{hole}`: {message}"),
            Self::Target(problem) => write!(f, "target refused: {problem}"),
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

#[cfg(test)]
mod tests {
    use super::*;

    /// FZ-POLISH S6: every sort refusal prints words, never a Rust variant name.
    #[test]
    fn every_sort_refusal_prints_human_text() {
        let refusals = [
            SortRefusal::Unknown,
            SortRefusal::Computation,
            SortRefusal::ProgramSyntax,
            SortRefusal::Token,
            SortRefusal::NoGenerator,
            SortRefusal::Collection,
            SortRefusal::ElementRefused {
                element: "Stmt".into(),
                reason: Box::new(SortRefusal::ProgramSyntax),
            },
            SortRefusal::ElementNotHeld {
                declared: "Int".into(),
                element: "Stmt".into(),
            },
            SortRefusal::MissingOnSide { side: "mutant" },
            SortRefusal::Contains {
                sort: "Stmt".into(),
                through: vec!["Job".into()],
                reason: Box::new(SortRefusal::ProgramSyntax),
            },
        ];
        let identifiers = [
            "Unknown",
            "Computation",
            "ProgramSyntax",
            "Token",
            "NoGenerator",
            "Collection",
            "ElementRefused",
            "ElementNotHeld",
            "MissingOnSide",
            "Contains",
            "Box(",
        ];
        for refusal in refusals {
            let error = CampaignError::RefusedHoleSort {
                hole: "H".into(),
                sort: "Map".into(),
                reason: refusal.clone(),
            }
            .to_string();
            for identifier in identifiers {
                assert!(!error.contains(identifier), "{refusal:?}: {error}");
            }
            assert!(
                error.len() > "hole `H`: sort `Map` is refused: ".len() + 10,
                "{error}"
            );
        }
    }

    /// FZ-POLISH S6: every target problem prints words, never a Rust variant name.
    #[test]
    fn every_target_problem_prints_human_text() {
        let problems = [
            TargetProblem::SharedIdentity,
            TargetProblem::NotExecutable,
            TargetProblem::UnknownId,
            TargetProblem::Equation,
            TargetProblem::Pattern("line 1, column 3: no".into()),
            TargetProblem::Unsupported("not here".into()),
            TargetProblem::AmbiguousRule(Vec::new()),
            TargetProblem::AmbiguousSource {
                source: "a.k".into(),
                files: vec!["x/a.k".into()],
            },
        ];
        for problem in problems {
            let text = CampaignError::Target(problem.clone()).to_string();
            for identifier in [
                "SharedIdentity",
                "NotExecutable",
                "UnknownId",
                "Equation",
                "Pattern(",
                "Unsupported(",
                "AmbiguousRule",
                "AmbiguousSource",
            ] {
                assert!(!text.contains(identifier), "{problem:?}: {text}");
            }
        }
    }
}
