//! The mutation checks only the krs front end can make, because they read what KRS knows and
//! the K does not say: which nodes of an edited sentence KRS generated, and which rules KRS's
//! own overlap analysis would refuse to see overlap.
//!
//! A check reads the emission and the corpus and refuses mutations by id, each with an
//! [`InvalidMutation`] whose reason is [`kink_flow::InvalidReason::External`]. The refusals reach
//! kink-flow through [`kink_flow::FrontEnd::refused`]: `run` gives each refused mutation the row
//! of a mutation that does not resolve and runs nothing for it, `check --mutations` adds the
//! refusal to its row, and a `fuzz` kill job of one is refused. Refusing before the engine is
//! conservative: a refused mutation has no outcome, and no verdict of another depends on it.
//!
//! No check is registered yet ([`all`]); the generated-only and overlap checks are to come.

use std::collections::BTreeMap;

use kink_flow::{FlowCommand, FlowManifest, InvalidMutation, MutationList, cli::FuzzJobRequest};

use crate::EmittedDefinition;

/// What a check reads.
#[expect(
    dead_code,
    reason = "no check is registered yet; the generated-only and overlap checks read these"
)]
pub(crate) struct CheckInput<'a> {
    /// The emission `kink/definition.k` holds, with its rule table and source map.
    pub emitted: &'a EmittedDefinition,
    /// The bound corpus manifest.
    pub manifest: &'a FlowManifest,
    /// The mutation list the command reads.
    pub mutations: &'a MutationList,
}

/// One check of the krs front end.
pub(crate) trait KrsCheck {
    /// The mutations of `input.mutations` this check refuses, by id.
    fn refusals(&self, input: &CheckInput<'_>) -> BTreeMap<String, InvalidMutation>;
}

/// Every check the front end makes, in the order their refusals take precedence.
pub(crate) fn all() -> Vec<Box<dyn KrsCheck>> {
    Vec::new()
}

/// The mutations `checks` refuse for `command`, by id: for the commands that read a mutation
/// list (`check` given one, `run`, a `fuzz` kill job), the first refusal of each refused id in
/// `checks`' order. Nothing is read when there is no check, and a list that does not decode
/// refuses nothing here, since kink-flow refuses it for the command.
pub(crate) fn refused(
    checks: &[Box<dyn KrsCheck>],
    emitted: &EmittedDefinition,
    manifest: &FlowManifest,
    command: &FlowCommand,
) -> BTreeMap<String, InvalidMutation> {
    if checks.is_empty() {
        return BTreeMap::new();
    }
    let path = match command {
        FlowCommand::Check(options) => options.mutations.as_deref(),
        FlowCommand::Run { mutations, .. } => Some(mutations.as_path()),
        FlowCommand::Fuzz { request, .. } => match &request.job {
            FuzzJobRequest::Kill { mutations, .. } => Some(mutations.as_path()),
            _ => None,
        },
        _ => None,
    };
    let Some(Ok(mutations)) = path.map(MutationList::read) else {
        return BTreeMap::new();
    };
    let input = CheckInput {
        emitted,
        manifest,
        mutations: &mutations,
    };
    merge(checks.iter().map(|check| check.refusals(&input)))
}

/// The refusals of several checks: for each id, the first check's.
fn merge(
    refusals: impl IntoIterator<Item = BTreeMap<String, InvalidMutation>>,
) -> BTreeMap<String, InvalidMutation> {
    let mut merged = BTreeMap::new();
    for refusal in refusals {
        for (id, invalid) in refusal {
            merged.entry(id).or_insert(invalid);
        }
    }
    merged
}

#[cfg(test)]
mod tests {
    use super::{all, merge};
    use kink_flow::{InvalidMutation, InvalidReason};
    use std::collections::BTreeMap;

    /// A check's refusals of `ids`, with the check's reason `name`.
    fn refusing(name: &'static str, ids: &[&str]) -> BTreeMap<String, InvalidMutation> {
        ids.iter()
            .map(|id| {
                (
                    (*id).to_owned(),
                    InvalidMutation {
                        edit: Some(0),
                        reason: InvalidReason::External {
                            name,
                            next: "edit the authored node instead",
                        },
                        detail: format!("{name} refuses it"),
                    },
                )
            })
            .collect()
    }

    #[test]
    fn no_check_is_registered_yet() {
        assert!(all().is_empty());
    }

    #[test]
    fn the_first_check_that_refuses_a_mutation_gives_its_refusal() {
        let merged = merge([
            refusing("generated-only", &["a"]),
            refusing("overlapping-rules", &["a", "b"]),
        ]);
        let reason = |id: &str| merged.get(id).map(|invalid| invalid.reason.as_str());
        assert_eq!(reason("a"), Some("generated-only"));
        assert_eq!(reason("b"), Some("overlapping-rules"));
        assert_eq!(merged.len(), 2);
        assert_eq!(
            merged["a"].reason.status(),
            InvalidReason::UnknownLabel.status(),
            "a front end's refusal is an invalid mutation, as a resolution failure is"
        );
    }
}
