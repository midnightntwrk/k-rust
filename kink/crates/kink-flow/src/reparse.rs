//! A grammar mutation's cases parsed again under the mutant's grammar, and the direction of a
//! grammar kill (PJ-34).
//!
//! A grammar mutant keeps every rule's term (`crate::mutation`, "Grammar edits") and changes
//! which program text parses to which term. So `run`'s search assembles every case's initial
//! configuration again under the mutant's grammar (`crate::admit::reassemble`, with the mutant's
//! input grammar built once per mutation, apart from the specification's) and compares what each
//! side's pipeline does with the case, before it runs anything:
//!
//! - A program of O (a comparable program, which a rule mutant runs on) the mutant parses to the
//!   baseline's initial configuration (`same`) is the mutant's run of the baseline's test case,
//!   which the campaign call judges as for a rule mutant (`Verdict::Run`).
//! - One the mutant does not parse (`rejected`; an ambiguous text is not parsed) kills in the
//!   direction `mutant-rejects` where the baseline accepts it (README.md D2: acceptance is the
//!   whole pipeline's, here the baseline's run, by phase 0's rule,
//!   [`crate::projected::baseline_acceptance`]), agrees where the baseline rejects it (both
//!   reject, at different stages, which D2 does not observe), and is `unknown` where the
//!   baseline's acceptance is not decided: in a flow without declared ends an end is accepted
//!   only where a path reached it at the `[stop]`.
//! - One the mutant parses to another configuration (`different`) is run: in the campaign call
//!   its test's mutant side starts from the mutant's configuration (kink-campaign
//!   `run_campaign_multi_started`) while its baseline side runs the baseline's, and a kill by it
//!   is a `parses-differently` witness: both sides parse the case, to different terms, and the
//!   runs differ under the projection, the run's own slots in a flow with no `[[projection]]`.
//!   A configuration that is not concrete is not run (`grammar-mutant-refuses`).
//! - A program stating `expect = { rejected = "parse" }` whose statement is met is not run, but
//!   it is parsed: the mutant rejecting it too agrees, and the mutant parsing it is a
//!   `mutant-accepts` witness only where the mutant's whole pipeline accepts it (D2: a later
//!   layer may reject it), which needs a run of the mutant alone on its own term, with no
//!   baseline run beside it, which the campaign's pairs do not make: `unknown` until then.
//! - Any other refusal of the mutant's assembly (no parser for a variable's module, a missing
//!   variable) is a fault of the mutant's grammar, not of the text: `unknown`.
//!
//! The direction is read from the witness, never from the edit's form. A row is killed by the
//! recorded killer while it kills, else by the first killing case in O's order; `unknown` while
//! some case is undecided; and otherwise left to the campaign call over O, each `different`
//! case's mutant side started from its own term, which `read_call` reads for a grammar mutant.

use crate::admit::Reassembly;
use crate::compare::Acceptance;
use crate::projected::baseline_acceptance;
use k_rust::kore::ast::Pattern;
use serde_json::{Map, Value, json};

/// The `killer_source` of a kill the reparse decides with no run of the mutant.
pub const SOURCE_REPARSE: &str = "reparse";

/// Reason: the mutant rejects a program of O at parse, and whether the baseline accepts it is
/// not decided (its acceptance's own reason in the detail).
pub const ACCEPTANCE_NOT_DECIDED: &str = "grammar-acceptance-not-decided";
/// Reason: a case's verdict needs a run of the mutant kink does not make: its run alone of a
/// case the baseline rejects at parse (`mutant-accepts`), or, for a mutant that compiles to the
/// baseline's definition (which the runner runs no test of), its run of a case parsed to
/// another term.
pub const RUN_NOT_SUPPORTED: &str = "grammar-run-not-supported";
/// Reason: the mutant's assembly of a case is refused otherwise than at parse.
pub const MUTANT_REFUSES: &str = "grammar-mutant-refuses";
/// Reason: a case both grammars parse to one term kills by its run: the parse outcome does not
/// differ, so the kill has no grammar direction, and the row fails closed.
pub const SAME_PARSE_RUN_DIFFERS: &str = "same-parse-run-differs";
/// Reason of a survivor whose every case parses alike and whose compilation is the baseline's
/// (kink-campaign `equivalent-compilation`): every case agrees, and the mutant is no equivalent,
/// since its parser differs.
pub const SAME_PARSE_EQUIVALENT: &str = "same-parse-equivalent-compilation";

/// Which side of a grammar kill accepts the witness.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Direction {
    /// The baseline rejects the case at parse, and the mutant accepts it.
    MutantAccepts,
    /// The baseline accepts the case, and the mutant rejects it.
    MutantRejects,
    /// Both parse the case, to different terms, and the runs differ under the projection.
    ParsesDifferently,
}

impl Direction {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::MutantAccepts => "mutant-accepts",
            Self::MutantRejects => "mutant-rejects",
            Self::ParsesDifferently => "parses-differently",
        }
    }
}

/// One case's verdict on a grammar mutant from its reparse.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Verdict {
    Killed(Direction),
    Agree,
    Unknown(&'static str),
    /// The campaign call decides: by the mutant's run of the baseline's test case where the
    /// case is parsed alike, from the case's own [`Case::start`] where it is parsed to another
    /// term.
    Run,
}

/// One reparsed case of a grammar mutation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Case {
    pub program: String,
    /// The program states `expect = { rejected = "parse" }` (met on the baseline).
    pub stated: bool,
    /// `same`, `different`, `rejected` or `refused`.
    pub reparse: &'static str,
    pub verdict: Verdict,
    pub detail: String,
    /// The initial configuration the mutant's grammar assembles where it is not the baseline's
    /// (`different`) and is concrete: the start of the case's mutant side in the campaign call.
    pub start: Option<Pattern>,
}

impl Case {
    /// The case's entry in the row's `grammar` member.
    pub fn value(&self) -> Value {
        let (verdict, direction, reason) = match &self.verdict {
            Verdict::Killed(direction) => ("killed", Some(direction.as_str()), None),
            Verdict::Agree => ("agree", None, None),
            Verdict::Unknown(reason) => ("unknown", None, Some(*reason)),
            Verdict::Run => ("run", None, None),
        };
        json!({
            "program": self.program,
            "stated": self.stated.then_some("parse"),
            "reparse": self.reparse,
            "verdict": verdict,
            "direction": direction,
            "reason": reason,
            "detail": self.detail,
        })
    }
}

/// The case of a program of O: `initial` its baseline initial configuration, `row` its program
/// row (its acceptance), `reassembly` what the mutant's grammar assembles from its inputs.
pub(crate) fn listed(
    program: &str,
    initial: &Pattern,
    row: &Value,
    reassembly: Reassembly,
) -> Case {
    let case = |reparse, verdict, detail: String| Case {
        program: program.to_owned(),
        stated: false,
        reparse,
        verdict,
        detail,
        start: None,
    };
    match reassembly {
        Reassembly::Assembled(mutant) if mutant == *initial => case(
            "same",
            Verdict::Run,
            "the mutant's grammar parses the case to the baseline's initial configuration"
                .to_owned(),
        ),
        Reassembly::Assembled(mutant) if mutant.free_variables().is_empty() => Case {
            start: Some(mutant),
            ..case(
                "different",
                Verdict::Run,
                "the mutant's grammar parses the case to another initial configuration, which \
                 the mutant runs from: a kill by it is `parses-differently`"
                    .to_owned(),
            )
        },
        Reassembly::Assembled(_) => case(
            "different",
            Verdict::Unknown(MUTANT_REFUSES),
            "the mutant's grammar parses the case to an initial configuration that is not \
             concrete, which kink does not run"
                .to_owned(),
        ),
        Reassembly::ParseRejected(detail) => match baseline_acceptance(row) {
            Acceptance::Accepted => case(
                "rejected",
                Verdict::Killed(Direction::MutantRejects),
                format!(
                    "the baseline accepts the case and the mutant's grammar rejects it at \
                     parse: {detail}"
                ),
            ),
            Acceptance::Rejected => case(
                "rejected",
                Verdict::Agree,
                format!(
                    "the baseline's run rejects the case and the mutant's grammar rejects it at \
                     parse (acceptance ignores the stage): {detail}"
                ),
            ),
            Acceptance::NotCompared(not) => case(
                "rejected",
                Verdict::Unknown(ACCEPTANCE_NOT_DECIDED),
                format!(
                    "the mutant's grammar rejects the case at parse ({detail}), and whether the \
                     baseline accepts it is not decided: {}",
                    not.detail()
                ),
            ),
        },
        Reassembly::Refused(detail) => case(
            "refused",
            Verdict::Unknown(MUTANT_REFUSES),
            format!("the mutant's grammar refuses the case otherwise than at parse: {detail}"),
        ),
    }
}

/// The case of a program whose met statement says the baseline rejects it at parse.
pub(crate) fn stated(program: &str, reassembly: Reassembly) -> Case {
    let case = |reparse, verdict, detail: String| Case {
        program: program.to_owned(),
        stated: true,
        reparse,
        verdict,
        detail,
        start: None,
    };
    match reassembly {
        Reassembly::ParseRejected(detail) => case(
            "rejected",
            Verdict::Agree,
            format!("both grammars reject the case at parse: {detail}"),
        ),
        Reassembly::Assembled(_) => case(
            "different",
            Verdict::Unknown(RUN_NOT_SUPPORTED),
            "the baseline rejects the case at parse and the mutant's grammar parses it: a kill \
             (`mutant-accepts`) needs the mutant's whole pipeline to accept it (its admission \
             checks and its run alone, with no baseline run), which kink does not run yet"
                .to_owned(),
        ),
        Reassembly::Refused(detail) => case(
            "refused",
            Verdict::Unknown(MUTANT_REFUSES),
            format!("the mutant's grammar refuses the case otherwise than at parse: {detail}"),
        ),
    }
}

/// What a grammar mutation's cases decide before any run.
#[derive(Debug, Eq, PartialEq)]
pub(crate) enum Decision<'c> {
    /// Killed by `killer`: the recorded killer while it kills, else the first killing case.
    Killed(&'c Case),
    /// Some case is undecided and none kills: the first undecided case.
    Unknown(&'c Case),
    /// Every case agrees or is parsed alike: the campaign call over O decides.
    Call,
}

/// The decision of `cases` (O's order, then the stated cases), `recorded` the lock's killer.
pub(crate) fn decide<'c>(cases: &'c [Case], recorded: Option<&str>) -> Decision<'c> {
    let kills = || {
        cases
            .iter()
            .filter(|case| matches!(case.verdict, Verdict::Killed(_)))
    };
    if let Some(killer) = kills()
        .find(|case| Some(case.program.as_str()) == recorded)
        .or_else(|| kills().next())
    {
        return Decision::Killed(killer);
    }
    cases
        .iter()
        .find(|case| matches!(case.verdict, Verdict::Unknown(_)))
        .map_or(Decision::Call, Decision::Unknown)
}

/// The campaign call's row of a grammar mutation whose every case (`cases`) agrees or is run,
/// read for a grammar mutant (module documentation). A kill by a case parsed to another term is
/// `parses-differently`, with the call's killer. A kill by a case parsed alike is `unknown`,
/// since its parse outcome does not differ and the kill has no grammar direction. `equivalent`
/// (by its compilation: the runner runs no test of the mutant) is a survivor where every case
/// parses alike, since each then executes as the baseline does, and `unknown` where a case is
/// parsed to another term, whose run from that term was not made. `rules` is the row's rule
/// texts, which an unknown row keeps. Every other row is the call's.
pub(crate) fn read_call(row: &mut Map<String, Value>, rules: &Value, cases: &[Case]) {
    let status = row["status"].as_str().unwrap_or_default().to_owned();
    let different = |program: &str| {
        cases
            .iter()
            .any(|case| case.program == program && case.start.is_some())
    };
    match status.as_str() {
        "equivalent" if cases.iter().any(|case| case.start.is_some()) => {
            row.insert("status".into(), json!("unknown"));
            row.insert("reason".into(), json!(RUN_NOT_SUPPORTED));
            row.insert(
                "detail".into(),
                json!(
                    "the mutant compiles to the baseline's definition, so no test of it runs, and \
                     a case its grammar parses to another term is judged only by a run from that \
                     term"
                ),
            );
        }
        // Only `equivalent-compilation` gives a grammar mutant this status (no grammar edit
        // weakens an equation), and no reason makes a mutant whose parser differs equivalent.
        "equivalent" => {
            row.insert("status".into(), json!("survived"));
            row.insert("reason".into(), json!(SAME_PARSE_EQUIVALENT));
        }
        "killed" if row["killer"].as_str().is_some_and(different) => {
            row.insert(
                "direction".into(),
                json!(Direction::ParsesDifferently.as_str()),
            );
            return;
        }
        "killed" => {
            let killer = row["killer"].clone();
            row.insert("status".into(), json!("unknown"));
            row.insert("reason".into(), json!(SAME_PARSE_RUN_DIFFERS));
            row.insert(
                "detail".into(),
                json!(format!(
                    "the case {killer} kills the mutant by its run, and both grammars parse it to \
                     one term: its parse outcome does not differ, so the kill has no grammar \
                     direction"
                )),
            );
            row.insert("killer".into(), Value::Null);
            row.insert("killer_source".into(), Value::Null);
            row.insert("killer_from_cache".into(), json!(false));
            row.insert("rules".into(), rules.clone());
        }
        _ => return,
    }
    let action = crate::report::action(
        row["status"].as_str().unwrap_or_default(),
        row["reason"].as_str(),
    );
    row.insert("action".into(), json!(action));
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int(value: &str) -> Pattern {
        Pattern::DomainValue {
            sort: k_rust::kore::ast::Sort::Application {
                name: "SortInt".into(),
                arguments: Vec::new(),
            },
            value: value.into(),
        }
    }

    fn row(halt: &str) -> Value {
        json!({"class": "comparable", "ends": [{"halt": halt}]})
    }

    #[test]
    fn a_listed_case_takes_its_direction_from_both_sides() {
        let one = int("1");
        let same = listed("p", &one, &row("own"), Reassembly::Assembled(int("1")));
        assert_eq!((same.reparse, &same.verdict), ("same", &Verdict::Run));
        assert_eq!(same.start, None);
        let different = listed("p", &one, &row("own"), Reassembly::Assembled(int("2")));
        assert_eq!(
            (different.reparse, &different.verdict, &different.start),
            ("different", &Verdict::Run, &Some(int("2")))
        );
        let open = Pattern::Variable(k_rust::kore::ast::Variable {
            kind: k_rust::kore::ast::VariableKind::Element,
            name: "VarX".into(),
            sort: k_rust::kore::ast::Sort::Application {
                name: "SortInt".into(),
                arguments: Vec::new(),
            },
        });
        let symbolic = listed("p", &one, &row("own"), Reassembly::Assembled(open));
        assert_eq!(
            (&symbolic.verdict, &symbolic.start),
            (&Verdict::Unknown(MUTANT_REFUSES), &None)
        );
        let rejects = listed(
            "p",
            &one,
            &row("stop"),
            Reassembly::ParseRejected("no".into()),
        );
        assert_eq!(rejects.verdict, Verdict::Killed(Direction::MutantRejects));
        assert_eq!(rejects.value()["direction"], "mutant-rejects");
        // No declared class and no stop: the baseline's acceptance is not decided.
        let undecided = listed(
            "p",
            &one,
            &row("own"),
            Reassembly::ParseRejected("no".into()),
        );
        assert_eq!(undecided.verdict, Verdict::Unknown(ACCEPTANCE_NOT_DECIDED));
        let rejected_row =
            json!({"class": "comparable", "ends": [{"halt": "own", "declared": "refused"}]});
        let both = listed(
            "p",
            &one,
            &rejected_row,
            Reassembly::ParseRejected("no".into()),
        );
        assert_eq!(both.verdict, Verdict::Agree);
        let refused = listed("p", &one, &row("stop"), Reassembly::Refused("x".into()));
        assert_eq!(refused.verdict, Verdict::Unknown(MUTANT_REFUSES));
    }

    #[test]
    fn a_stated_case_agrees_only_while_the_mutant_rejects_it() {
        assert_eq!(
            stated("s", Reassembly::ParseRejected("no".into())).verdict,
            Verdict::Agree
        );
        let parsed = stated("s", Reassembly::Assembled(int("1")));
        assert_eq!(parsed.verdict, Verdict::Unknown(RUN_NOT_SUPPORTED));
        assert_eq!(parsed.value()["stated"], "parse");
    }

    #[test]
    fn the_recorded_killer_is_kept_while_it_kills() {
        let case = |program: &str, verdict| Case {
            program: program.into(),
            stated: false,
            reparse: "rejected",
            verdict,
            detail: String::new(),
            start: None,
        };
        let cases = [
            case("a", Verdict::Unknown(ACCEPTANCE_NOT_DECIDED)),
            case("b", Verdict::Killed(Direction::MutantRejects)),
            case("c", Verdict::Killed(Direction::MutantRejects)),
        ];
        assert_eq!(decide(&cases, None), Decision::Killed(&cases[1]));
        assert_eq!(decide(&cases, Some("c")), Decision::Killed(&cases[2]));
        assert_eq!(decide(&cases, Some("a")), Decision::Killed(&cases[1]));
        assert_eq!(decide(&cases[..1], None), Decision::Unknown(&cases[0]));
        let alike = [case("a", Verdict::Run), case("s", Verdict::Agree)];
        assert_eq!(decide(&alike, None), Decision::Call);
    }

    #[test]
    fn a_call_is_read_for_a_grammar_mutant() {
        let one = int("1");
        let alike = [listed(
            "p",
            &one,
            &row("own"),
            Reassembly::Assembled(int("1")),
        )];
        let apart = [
            alike[0].clone(),
            listed("q", &one, &row("own"), Reassembly::Assembled(int("2"))),
        ];
        let mut equivalent = Map::new();
        equivalent.insert("status".into(), json!("equivalent"));
        equivalent.insert("reason".into(), json!("equivalent-compilation"));
        let mut unrun = equivalent.clone();
        read_call(&mut unrun, &Value::Null, &apart);
        assert_eq!(
            (&unrun["status"], &unrun["reason"]),
            (&json!("unknown"), &json!(RUN_NOT_SUPPORTED))
        );
        read_call(&mut equivalent, &Value::Null, &alike);
        assert_eq!(
            (&equivalent["status"], &equivalent["reason"]),
            (&json!("survived"), &json!(SAME_PARSE_EQUIVALENT))
        );
        let mut killed = Map::new();
        killed.insert("status".into(), json!("killed"));
        killed.insert("reason".into(), Value::Null);
        killed.insert("killer".into(), json!("p"));
        let mut differently = killed.clone();
        differently.insert("killer".into(), json!("q"));
        read_call(&mut differently, &json!(["r"]), &apart);
        assert_eq!(
            (&differently["status"], &differently["killer"]),
            (&json!("killed"), &json!("q"))
        );
        assert_eq!(differently["direction"], "parses-differently");
        read_call(&mut killed, &json!(["r"]), &apart);
        assert_eq!(killed["status"], "unknown");
        assert_eq!(killed["reason"], SAME_PARSE_RUN_DIFFERS);
        assert_eq!(killed["killer"], Value::Null);
        assert_eq!(killed["rules"], json!(["r"]));
        let mut survived = Map::new();
        survived.insert("status".into(), json!("survived"));
        survived.insert("reason".into(), Value::Null);
        read_call(&mut survived, &Value::Null, &apart);
        assert!(!survived.contains_key("action"));
    }
}
