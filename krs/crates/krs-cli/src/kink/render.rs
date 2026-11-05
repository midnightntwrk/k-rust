//! A kill's evidence at the KRS level: kink-flow's [`EndRenderer`] implemented with krs-exec's
//! comparison of ends, so that a kill's difference is the document that comparison writes
//! wherever KRS shows two ends differ (`krs-difference/1`, as `krs run --case` shows an unmet
//! expectation): the cell by Rust field path and both values as their canonical documents.
//!
//! kink gives the renderer the two sets of ends its slot compared, final configurations of the
//! K the front end emitted. Each is read as a krs-exec end of the definition the K was emitted
//! from ([`krs_exec::Semantics::read_configuration`]), with the cells the slot leaves out not
//! stated: the slot replaced each by `\top` of its sort, which states nothing of it. The
//! comparison then compares every observable leaf cell the ends state, which are the cells the
//! slot compared, and chooses its pair of ends by krs-exec's rule, which is kink's (an end
//! outside the other set and its nearest end there); the sides are named `baseline` and
//! `mutant`.
//!
//! Every end kink compares is an end of the system its run explores (truncated at its stop, when
//! the corpus has one): a state with no successor there, compared by its configuration alone, so
//! a path stopped at a configuration and a path stuck at it give one end. The renderer is given
//! no class, so it states none: krs-exec's comparison is given each end with one class, `stuck`,
//! so that it compares the cells alone, and each side of the document leaves its `class` out.
//!
//! The renderer judges nothing: kink's slot proved the kill. Two decoded values are equal exactly
//! when their terms are, so the comparison finds a difference wherever the slot did in a cell the
//! definition declares; where it does not (a difference only in compilation's cells, an end it
//! cannot read, a native compile that fails), kink gives its own evidence with the reason.
//!
//! The documents depend on the ends, on the Definition IR's names and types (cells by Rust field,
//! constructors and fields by Rust name) and on krs's build. The tier-1 context names the build
//! (`kink_build`, the running executable) and the emitted K up to positions (the execution
//! digest), but a constructor's field names never reach the K: its non-terminals are emitted as
//! sorts. So the renderer's identity ([`EndRenderer::identity`]) is the SHA-256 of the Definition
//! IR's JSON without its provenance tables, which hold the IR's source positions and which no
//! document reads; a field renamed under the same syntax changes it, an edit that only moves
//! text does not.
//!
//! # Expectations
//!
//! The renderer also reads a case's expectation, the `expect` table of a case document, as
//! `krs run --case` reads it ([`krs_exec::Semantics::expectation`]: cells by Rust field path,
//! values as documents of the encoding, the stop rule named as `--stop-before` names one), and
//! checks it against the ends of the case's baseline run by krs-exec's rule
//! ([`krs_exec::Semantics::check_expectation`]: met when every end agrees with it on the class and
//! the compared cells), each end read as above, the sides named `expected` and `baseline`.
//!
//! An end's class is what kink's observation of the run says of it. Without `[stop]` every end
//! kink keeps is a state of no successor, `stuck`, so the class is compared. With `[stop]` an end
//! is stuck, or stopped at a rule of the stop, and the ends do not say which: a run merges the
//! paths that reach one configuration, whichever way each reached it. So the halt of an
//! expectation of a stuck end, or of one stopped at a rule the stop stops at, is not observed:
//! its cells are compared, an end that differs on them makes it unmet (whatever the halt, the
//! end is not the one expected), and the detail says the halt was not compared, but ends that
//! agree on every compared cell make it inconclusive, not met, since met is agreement on the
//! halt as well. The halt of an expectation of another halt is decided, since no end of the
//! truncated system has it: it is compared with ends of class `stuck`, which differ from it at
//! the class, the baseline's side of its difference stating no class, and the detail says so.
//! An expectation kink's observation cannot decide is inconclusive, saying why: an end stopped
//! at a rule the corpus does not stop at, or with no `[stop]`, and a `depth-bound` end, since
//! kink reads no case's `run` and a baseline its depth bound cuts is not comparable. A cell the
//! expectation compares that the corpus's `[result]` leaves out is not in the ends kink keeps,
//! which makes the check inconclusive too.

use std::collections::BTreeSet;
use std::sync::{Arc, OnceLock};

use k_rust::kast::identifier::label_or_name;
use k_rust::kore::ast::Pattern;
use kink_flow::{
    CheckedExpectation, EndRenderer, ExpectationCheck, ExpectationVerdict, StopSection,
};
use krs_exec::{
    CellInfo, Compared, Comparison, DIFFERENCE_FORMAT, End, EndClass, EndError, Ends, Expectation,
    Halt, Semantics, Side,
};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

use super::inputs::{KrsInputs, ManifestFiles};

/// The renderer of one emission's kill evidence, over the decoder's native compile.
pub(crate) struct KrsEnds {
    inputs: Arc<KrsInputs>,
    /// The renderer's identity, computed on first use (tier 1 is off under Z3, which never asks).
    identity: OnceLock<Result<Value, String>>,
}

impl KrsEnds {
    pub(crate) const fn new(inputs: Arc<KrsInputs>) -> Self {
        Self {
            inputs,
            identity: OnceLock::new(),
        }
    }
}

impl EndRenderer for KrsEnds {
    fn format(&self) -> &'static str {
        DIFFERENCE_FORMAT
    }

    fn identity(&self) -> Result<Value, String> {
        self.identity
            .get_or_init(|| {
                definition_digest(self.inputs.definition())
                    .map(|digest| json!({ "definition_ir": digest }))
            })
            .clone()
    }

    fn difference(
        &self,
        baseline: &BTreeSet<Pattern>,
        mutant: &BTreeSet<Pattern>,
        mutant_complete: bool,
        not_compared: &[String],
    ) -> Result<Value, String> {
        self.inputs
            .with_semantics("showing a kill's evidence at the KRS level", |semantics| {
                difference(semantics, baseline, mutant, mutant_complete, not_compared)
            })
    }

    fn read_expectation(
        &self,
        expect: &toml::Table,
        files: &mut dyn kink_flow::admit::InputFiles,
    ) -> Result<(), String> {
        let document = expectation_document(expect)?;
        self.inputs
            .with_semantics("reading a case's expectation", |semantics| {
                semantics
                    .expectation(&document, None, &mut ManifestFiles(files))
                    .map(|_| ())
                    .map_err(|error| error.to_string())
            })
    }

    fn check_expectation(&self, check: ExpectationCheck<'_>) -> Result<CheckedExpectation, String> {
        let document = expectation_document(check.expect)?;
        let rule = check
            .expect
            .get("rule")
            .and_then(toml::Value::as_str)
            .map(str::to_owned);
        let ExpectationCheck {
            files,
            ends,
            not_compared,
            stop,
            ..
        } = check;
        self.inputs
            .with_semantics("checking a case's expectation", |semantics| {
                let expectation = semantics
                    .expectation(&document, None, &mut ManifestFiles(files))
                    .map_err(|error| error.to_string())?;
                checked_expectation(
                    semantics,
                    &expectation,
                    rule.as_deref(),
                    ends,
                    not_compared,
                    stop,
                )
            })
    }
}

/// An `expect` table in the JSON data model, as krs-exec reads a case document's.
fn expectation_document(expect: &toml::Table) -> Result<Value, String> {
    krs_exec::toml_document(&toml::Value::Table(expect.clone())).map_err(|error| error.to_string())
}

/// What an end kink keeps under `[stop]` is (module documentation, "Expectations").
const HALT_UNDER_STOP: &str = "under [stop] an end kink keeps is stuck or stopped at a rule of \
     the stop";

/// Why the ends do not say an end's halt under `[stop]`, after [`HALT_UNDER_STOP`].
const HALT_UNOBSERVED: &str = "and the ends do not say which, since a run merges the paths that \
     reach one configuration";

/// How the check treats the expectation's halt (module documentation, "Expectations").
#[derive(Clone, Copy, PartialEq, Eq)]
enum HaltCheck {
    /// Without `[stop]`: every end is `stuck`, and the class is compared.
    Compared,
    /// Under `[stop]`, a halt no end has: unmet at the class, the baseline's class unstated.
    Decided,
    /// Under `[stop]`, a halt an end may have: only the cells are compared.
    Unobserved,
}

/// The check of `expectation` (whose `rule` is written `rule`) against the baseline's ends
/// `ends` (module documentation, "Expectations").
fn checked_expectation(
    semantics: &Semantics,
    expectation: &Expectation,
    rule: Option<&str>,
    ends: &BTreeSet<Pattern>,
    not_compared: &[String],
    stop: Option<&StopSection>,
) -> Result<CheckedExpectation, String> {
    let expected = &expectation.end.class;
    let stuck = EndClass {
        halt: Halt::Stuck,
        rule: None,
    };
    // The class each end is read with, and how the halt is checked.
    let (class, halt) = match (expected.halt, stop) {
        (Halt::DepthBound, _) => {
            return Ok(CheckedExpectation::inconclusive(
                "the expectation's end is `depth-bound`, and no end kink compares is: a baseline \
                 its depth bound cuts is not comparable, and kink reads no case's `run`",
            ));
        }
        (Halt::Stopped, None) => {
            return Ok(CheckedExpectation::inconclusive(format!(
                "the expectation's end is stopped at `{}`, and the corpus declares no [stop]: \
                 kink runs every program as the corpus says",
                rule.unwrap_or_default()
            )));
        }
        (Halt::Stopped, Some(stop)) => {
            let Some(rule) = rule else {
                return Ok(CheckedExpectation::inconclusive(
                    "the expectation's end is stopped, at a rule it does not name",
                ));
            };
            let selected = semantics
                .stop_rules(rule)
                .map_err(|error| error.to_string())?;
            if !selected
                .iter()
                .filter_map(|(_, label)| label.as_deref())
                .any(|label| stop.names(label))
            {
                return Ok(CheckedExpectation::inconclusive(format!(
                    "the expectation's end is stopped at `{rule}`, a rule the corpus's [stop] \
                     does not stop at"
                )));
            }
            (expected.clone(), HaltCheck::Unobserved)
        }
        (Halt::Stuck, Some(_)) => (expected.clone(), HaltCheck::Unobserved),
        (_, Some(_)) => (stuck, HaltCheck::Decided),
        (_, None) => (stuck, HaltCheck::Compared),
    };
    let cells = semantics.cells();
    let unstated = unstated(&cells, not_compared);
    let baseline = Ends {
        ends: read_ends(semantics, ends, &class, &unstated)?,
        incomplete: None,
    };
    let compared = semantics.check_expectation(
        &expectation.comparison,
        Side {
            name: "expected",
            ends: &Ends::one(expectation.end.clone()),
        },
        Side {
            name: "baseline",
            ends: &baseline,
        },
    );
    checked(compared, halt)
}

/// The verdict of `compared`, krs-exec's check of the expectation, whose halt is checked by
/// `halt` (module documentation, "Expectations").
fn checked(
    compared: Result<Compared, EndError>,
    halt: HaltCheck,
) -> Result<CheckedExpectation, String> {
    let detail = match halt {
        HaltCheck::Compared => None,
        HaltCheck::Decided => Some(format!(
            "the halt is compared: {HALT_UNDER_STOP}, and the expectation's end is neither"
        )),
        HaltCheck::Unobserved => Some(format!(
            "the halt is not compared: {HALT_UNDER_STOP}, {HALT_UNOBSERVED}"
        )),
    };
    Ok(match compared {
        Err(error @ EndError::MissingCell { .. }) => CheckedExpectation::inconclusive(format!(
            "{error}: the ends kink keeps leave out the cells the corpus does not compare \
             ([result], unobservable cells)"
        )),
        Err(error) => return Err(error.to_string()),
        Ok(Compared::Equal) if halt == HaltCheck::Unobserved => {
            CheckedExpectation::inconclusive(format!(
                "every end agrees with the expectation on the compared cells, but its halt is not \
                 observed: {HALT_UNDER_STOP}, {HALT_UNOBSERVED}"
            ))
        }
        Ok(Compared::Equal) => CheckedExpectation {
            verdict: ExpectationVerdict::Met,
            detail,
            difference: None,
        },
        Ok(Compared::Differs(difference)) => {
            let mut document =
                serde_json::to_value(&*difference).map_err(|error| error.to_string())?;
            if halt != HaltCheck::Compared
                && let Some(side) = document["right"].as_object_mut()
            {
                side.remove("class");
            }
            CheckedExpectation {
                verdict: ExpectationVerdict::Unmet,
                detail,
                difference: Some(document),
            }
        }
        Ok(Compared::Inconclusive(reason)) => CheckedExpectation::inconclusive(reason),
    })
}

/// The cells of `cells` that `not_compared` (by K cell name) leaves out.
fn unstated<'c>(cells: &'c [CellInfo], not_compared: &[String]) -> Vec<&'c CellInfo> {
    let labels = not_compared
        .iter()
        .map(|name| format!("<{name}>"))
        .collect::<BTreeSet<_>>();
    cells
        .iter()
        .filter(|cell| labels.contains(&label_or_name(&cell.symbol)))
        .collect()
}

/// Each configuration of `set` read as an end of class `class`, the cells of `unstated` not
/// stated.
fn read_ends(
    semantics: &Semantics,
    set: &BTreeSet<Pattern>,
    class: &EndClass,
    unstated: &[&CellInfo],
) -> Result<Vec<End>, String> {
    let symbols = unstated
        .iter()
        .map(|cell| cell.symbol.as_str())
        .collect::<BTreeSet<_>>();
    set.iter()
        .map(|configuration| {
            semantics
                .read_configuration(configuration, class.clone(), &symbols)
                .map_err(|error| format!("an end does not read as the definition's: {error}"))
        })
        .collect()
}

/// The krs-exec comparison of the slot's two sets of ends (module documentation).
fn difference(
    semantics: &Semantics,
    baseline: &BTreeSet<Pattern>,
    mutant: &BTreeSet<Pattern>,
    mutant_complete: bool,
    not_compared: &[String],
) -> Result<Value, String> {
    let cells = semantics.cells();
    let unstated = unstated(&cells, not_compared);
    let stuck = EndClass {
        halt: Halt::Stuck,
        rule: None,
    };
    let baseline = Ends {
        ends: read_ends(semantics, baseline, &stuck, &unstated)?,
        incomplete: None,
    };
    let mutant = Ends {
        ends: read_ends(semantics, mutant, &stuck, &unstated)?,
        incomplete: (!mutant_complete).then(|| {
            "the mutant's run reached its work budget: these are the ends of its explored complete \
             paths that killed"
                .to_owned()
        }),
    };
    // The observable leaf cells the ends state: every one unless the slot left some out.
    let left_out = |path: &str| {
        unstated.iter().any(|cell| {
            path == cell.path
                || path
                    .strip_prefix(cell.path.as_str())
                    .is_some_and(|rest| rest.starts_with('.'))
        })
    };
    let compare = (!unstated.is_empty()).then(|| {
        cells
            .iter()
            .filter(|cell| cell.ty.is_some() && !cell.unobservable && !left_out(&cell.path))
            .map(|cell| cell.path.clone())
            .collect::<Vec<_>>()
    });
    let comparison = Comparison {
        compare,
        ..Comparison::default()
    };
    let compared = semantics
        .compare_ends(
            &comparison,
            Side {
                name: "baseline",
                ends: &baseline,
            },
            Side {
                name: "mutant",
                ends: &mutant,
            },
        )
        .map_err(|error| error.to_string())?;
    evidence(compared, mutant_complete)
}

/// The SHA-256 of `definition`'s JSON without its provenance tables (module documentation), in
/// lowercase hexadecimal.
fn definition_digest(definition: &krs_ir_levels::DefinitionIr) -> Result<String, String> {
    let mut value = serde_json::to_value(definition)
        .map_err(|error| format!("the Definition IR does not serialize: {error}"))?;
    if let Some(root) = value.as_object_mut() {
        root.remove(krs_ir::provenance_table::PROVENANCE_FIELD);
    }
    let bytes = serde_json::to_vec(&value).map_err(|error| error.to_string())?;
    Ok(krs_ir::identity::lower_hex(&Sha256::digest(&bytes)))
}

/// The evidence of the kill whose ends krs-exec compared as `compared`, or why there is none.
///
/// Both sides have ends, and every end has the class `stuck`, so the comparison is inconclusive
/// only where the side it needs complete is not: no end of the mutant lies outside the
/// baseline's ends in the cells the definition declares, and the baseline's ends are not all
/// among an incomplete mutant's. The slot's kill of an incomplete mutant is a mutant end outside
/// the baseline's set (a baseline end the mutant's explored paths lack proves nothing), so there,
/// as for equal ends of two complete sides, the slot's difference lies in a cell compilation adds.
fn evidence(compared: Compared, mutant_complete: bool) -> Result<Value, String> {
    match compared {
        Compared::Differs(difference) => {
            let mut document =
                serde_json::to_value(&*difference).map_err(|error| error.to_string())?;
            // The renderer was given no class (module documentation): the sides state none.
            for side in ["left", "right"] {
                if let Some(side) = document[side].as_object_mut() {
                    side.remove("class");
                }
            }
            Ok(document)
        }
        Compared::Equal => Err(
            "the ends are equal in every cell the definition declares: the slot's difference is \
             in a cell of compilation's"
                .to_owned(),
        ),
        Compared::Inconclusive(_) if !mutant_complete => Err(
            "every end of the mutant's explored paths agrees with a baseline end in every cell \
             the definition declares: the slot's difference is in a cell of compilation's"
                .to_owned(),
        ),
        Compared::Inconclusive(reason) => Err(reason),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use krs_exec::{Difference, DifferenceAt, DifferenceSide};

    fn side(name: &str, complete: bool) -> DifferenceSide {
        DifferenceSide {
            name: name.to_owned(),
            ends: 1,
            complete,
            class: EndClass {
                halt: Halt::Stuck,
                rule: None,
            },
            value: None,
        }
    }

    /// A difference keeps krs-exec's document but states no class; equal ends, and an
    /// inconclusive comparison of an incomplete mutant, place the slot's difference in a cell
    /// compilation adds; another inconclusive comparison keeps krs-exec's reason.
    #[test]
    fn the_evidence_states_no_class_and_names_why_it_has_none() {
        let difference = Difference {
            format: DIFFERENCE_FORMAT,
            at: DifferenceAt::Cell,
            cell: Some("k".to_owned()),
            path: Some("k[0]".to_owned()),
            segments: vec!["[0]".to_owned()],
            outside: "mutant".to_owned(),
            also_differ: Vec::new(),
            compared: vec!["k".to_owned()],
            not_compared: Vec::new(),
            views: std::collections::BTreeMap::new(),
            left: side("baseline", true),
            right: side("mutant", false),
        };
        let document = evidence(Compared::Differs(Box::new(difference)), false).unwrap();
        assert_eq!(document["format"], DIFFERENCE_FORMAT);
        assert_eq!(document["path"], "k[0]");
        for name in ["left", "right"] {
            assert_eq!(document[name].get("class"), None, "{document:#}");
            assert!(document[name].get("complete").is_some(), "{document:#}");
        }
        for complete in [true, false] {
            assert!(
                evidence(Compared::Equal, complete)
                    .unwrap_err()
                    .ends_with("the slot's difference is in a cell of compilation's")
            );
        }
        let incomplete = Compared::Inconclusive("the mutant side's ends are incomplete".into());
        let reason = evidence(incomplete.clone(), false).unwrap_err();
        assert!(reason.starts_with("every end of the mutant's explored paths agrees"));
        assert!(reason.ends_with("the slot's difference is in a cell of compilation's"));
        assert_eq!(
            evidence(incomplete, true).unwrap_err(),
            "the mutant side's ends are incomplete"
        );
    }
}
