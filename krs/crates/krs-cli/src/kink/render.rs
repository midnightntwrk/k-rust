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

use std::collections::BTreeSet;
use std::sync::{Arc, OnceLock};

use k_rust::kast::identifier::label_or_name;
use k_rust::kore::ast::Pattern;
use kink_flow::EndRenderer;
use krs_exec::{
    Compared, Comparison, DIFFERENCE_FORMAT, End, EndClass, Ends, Halt, Semantics, Side,
};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

use super::inputs::KrsInputs;

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
    let labels = not_compared
        .iter()
        .map(|name| format!("<{name}>"))
        .collect::<BTreeSet<_>>();
    let unstated = cells
        .iter()
        .filter(|cell| labels.contains(&label_or_name(&cell.symbol)))
        .collect::<Vec<_>>();
    let symbols = unstated
        .iter()
        .map(|cell| cell.symbol.as_str())
        .collect::<BTreeSet<_>>();
    let read = |set: &BTreeSet<Pattern>| {
        set.iter()
            .map(|configuration| {
                semantics
                    .read_configuration(
                        configuration,
                        EndClass {
                            halt: Halt::Stuck,
                            rule: None,
                        },
                        &symbols,
                    )
                    .map_err(|error| format!("an end does not read as the definition's: {error}"))
            })
            .collect::<Result<Vec<End>, String>>()
    };
    let baseline = Ends {
        ends: read(baseline)?,
        incomplete: None,
    };
    let mutant = Ends {
        ends: read(mutant)?,
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
