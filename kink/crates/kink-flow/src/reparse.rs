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
//! - A program stating `expect = { rejected = "parse" }` whose statement is met has no run of the
//!   specification, but it is parsed: the mutant rejecting it too agrees, and the mutant parsing
//!   it to a concrete configuration is a `mutant-accepts` witness where the mutant's whole
//!   pipeline accepts it (D2: a later layer may reject it). That is decided by a run of the
//!   mutant alone from its own term, with no specification run beside it (kink-campaign
//!   `run_mutant_alone`), read by the acceptance rule of the baseline's side
//!   ([`crate::projected::mutant_acceptance`]): accepted kills, rejected agrees, anything else is
//!   `unknown` ([`alone`]).
//! - Any other refusal of the mutant's assembly (no parser for a variable's module, a missing
//!   variable) is a fault of the mutant's grammar, not of the text: `unknown`.
//!
//! The direction is read from the witness, never from the edit's form. The row's cases are in
//! its grammar order, O's order then the stated cases in corpus order, and the row is killed by
//! the recorded killer while it kills, else by the first kill in that order: O is decided first
//! (a kill the reparse decides, the recorded killer among them while it kills, else the first in
//! O's order; else the campaign call over O, each `different` case's mutant side started from
//! its own term, which `read_call` reads for a grammar mutant), and the stated cases are run
//! alone only where O kills nothing, the first of them that kills being the killer
//! ([`fold_alone`]); a recorded killer that is a stated case is run first. A row is `unknown`
//! while some case is undecided and none kills.

use crate::admit::Reassembly;
use crate::compare::Acceptance;
use crate::projected::baseline_acceptance;
use k_rust::kore::ast::Pattern;
use serde_json::{Map, Value, json};

/// The `killer_source` of a kill the reparse decides with no run of the mutant.
pub const SOURCE_REPARSE: &str = "reparse";
/// The `killer_source` of a `mutant-accepts` kill: the mutant's run alone of a case the
/// specification rejects at parse.
pub const SOURCE_ALONE: &str = "alone";

/// Reason: the mutant rejects a program of O at parse, and whether the baseline accepts it is
/// not decided (its acceptance's own reason in the detail).
pub const ACCEPTANCE_NOT_DECIDED: &str = "grammar-acceptance-not-decided";
/// Reason: a case's verdict needs a run of the mutant kink does not make: for a mutant that
/// compiles to the baseline's definition (which the runner runs no test of), its run of a case
/// parsed to another term, or its run alone of a case the baseline rejects at parse.
pub const RUN_NOT_SUPPORTED: &str = "grammar-run-not-supported";
/// Reason: the mutant parses a case the baseline rejects at parse, and whether the mutant's
/// pipeline accepts it is not decided by its run alone (the reason in the detail).
pub const MUTANT_ACCEPTANCE_NOT_DECIDED: &str = "grammar-mutant-acceptance-not-decided";
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
    /// (`different`) and is concrete: the start of the case's mutant side in the campaign call
    /// over O, or, for a stated case, of the mutant's run alone.
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
        Reassembly::Assembled(mutant) if mutant.free_variables().is_empty() => Case {
            start: Some(mutant),
            ..case(
                "different",
                Verdict::Run,
                "the baseline rejects the case at parse and the mutant's grammar parses it: the \
                 mutant runs alone from its configuration, and a kill (`mutant-accepts`) needs its \
                 whole pipeline to accept it"
                    .to_owned(),
            )
        },
        Reassembly::Assembled(_) => case(
            "different",
            Verdict::Unknown(MUTANT_REFUSES),
            "the baseline rejects the case at parse and the mutant's grammar parses it to an \
             initial configuration that is not concrete, which kink does not run"
                .to_owned(),
        ),
        Reassembly::Refused(detail) => case(
            "refused",
            Verdict::Unknown(MUTANT_REFUSES),
            format!("the mutant's grammar refuses the case otherwise than at parse: {detail}"),
        ),
    }
}

/// Whether `case` is a stated case left to the mutant's run alone (its verdict is not yet known).
pub(crate) fn pending(case: &Case) -> bool {
    case.stated && case.verdict == Verdict::Run
}

/// The verdict of a stated case from the mutant's run alone of its configuration: `acceptance`
/// the run's acceptance ([`crate::projected::mutant_acceptance`]; `Err` where its run gives no
/// side). The baseline rejects the case, so accepted kills (`mutant-accepts`), rejected agrees
/// (both reject, at different stages, which D2 does not observe) and anything else is
/// `unknown`.
pub(crate) fn alone(case: &mut Case, acceptance: Result<Acceptance, String>) {
    let (verdict, detail) = match acceptance {
        Ok(Acceptance::Accepted) => (
            Verdict::Killed(Direction::MutantAccepts),
            "the baseline rejects the case at parse, and the mutant's grammar parses it and its \
             run alone accepts it"
                .to_owned(),
        ),
        Ok(Acceptance::Rejected) => (
            Verdict::Agree,
            "the baseline rejects the case at parse, and the mutant's run alone of its parse \
             rejects it (acceptance ignores the stage)"
                .to_owned(),
        ),
        Ok(Acceptance::NotCompared(not)) => (
            Verdict::Unknown(MUTANT_ACCEPTANCE_NOT_DECIDED),
            format!(
                "the baseline rejects the case at parse and the mutant's grammar parses it, and \
                 whether its run alone accepts it is not decided: {}",
                not.detail()
            ),
        ),
        Err(reason) => (
            Verdict::Unknown(MUTANT_ACCEPTANCE_NOT_DECIDED),
            format!(
                "the baseline rejects the case at parse and the mutant's grammar parses it, and \
                 whether its run alone accepts it is not decided: {reason}"
            ),
        ),
    };
    case.verdict = verdict;
    case.detail = detail;
}

/// The verdict of a stated case the mutant ran no case alone for: `failure` the mutant-scope
/// failure that refused it (kebab-case), `equivalent` whether it is its compilation to the
/// baseline's definition, which runs no test.
pub(crate) fn not_alone(case: &mut Case, failure: &str, equivalent: bool) {
    if equivalent {
        case.verdict = Verdict::Unknown(RUN_NOT_SUPPORTED);
        "the mutant compiles to the baseline's definition, so it runs no test, and a case the \
         baseline rejects at parse and its grammar parses is judged only by its run alone"
            .clone_into(&mut case.detail);
    } else {
        case.verdict = Verdict::Unknown(MUTANT_ACCEPTANCE_NOT_DECIDED);
        case.detail = format!(
            "the baseline rejects the case at parse and the mutant's grammar parses it, and the \
             mutant runs no case alone (`{failure}`)"
        );
    }
}

/// The row of a grammar mutation once O is decided (`row`, a search's or a decided row), with
/// the stated cases' verdicts from the mutant's runs alone (`cases`, each stated case judged by
/// [`alone`] or [`not_alone`] where it was run): where O kills nothing (a `survived`, `unknown`
/// or `timeout` row), the first stated case that kills in corpus order kills the row
/// (`mutant-accepts`, `killer_source` `alone`), and a survivor some stated case leaves undecided
/// is `unknown` with that case's reason. Every other row is O's. `executed` and `calls` are the
/// runs alone's entries and calls, appended to the row's.
pub(crate) fn fold_alone(
    row: &mut Map<String, Value>,
    cases: &[Case],
    executed: &[Value],
    calls: &[(Value, Value)],
) {
    let append = |row: &mut Map<String, Value>, key: &str, values: Vec<Value>| {
        if let Some(Value::Array(entries)) = row.get_mut(key) {
            entries.extend(values);
        }
    };
    append(row, "executed", executed.to_vec());
    append(
        row,
        "calls",
        calls.iter().map(|(call, _)| call.clone()).collect(),
    );
    append(
        row,
        "call_wall_ms",
        calls.iter().map(|(_, wall)| wall.clone()).collect(),
    );
    row.insert(
        "grammar".into(),
        json!(cases.iter().map(Case::value).collect::<Vec<_>>()),
    );
    let status = row["status"].as_str().unwrap_or_default().to_owned();
    if !matches!(status.as_str(), "survived" | "unknown" | "timeout") {
        return;
    }
    let stated = || cases.iter().filter(|case| case.stated);
    if let Some(killer) = stated().find(|case| matches!(case.verdict, Verdict::Killed(_))) {
        row.insert("status".into(), json!("killed"));
        row.insert("reason".into(), Value::Null);
        row.insert("detail".into(), json!(killer.detail));
        row.insert("direction".into(), json!(Direction::MutantAccepts.as_str()));
        row.insert("killer".into(), json!(killer.program));
        row.insert("killer_source".into(), json!(SOURCE_ALONE));
        row.insert("killer_from_cache".into(), json!(false));
        row.insert("rules".into(), Value::Null);
        row.remove("horizon");
    } else if status == "survived"
        && let Some(open) = stated().find(|case| matches!(case.verdict, Verdict::Unknown(_)))
    {
        let Verdict::Unknown(reason) = open.verdict else {
            unreachable!("an undecided case has an unknown verdict");
        };
        row.insert("status".into(), json!("unknown"));
        row.insert("reason".into(), json!(reason));
        row.insert("detail".into(), json!(open.detail));
        row.remove("horizon");
    } else {
        return;
    }
    let action = crate::report::action(
        row["status"].as_str().unwrap_or_default(),
        row["reason"].as_str(),
    );
    row.insert("action".into(), json!(action));
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
    // A program of O parsed to another configuration; a stated case's start is its run alone's.
    let apart = |case: &&Case| !case.stated && case.start.is_some();
    let different = |program: &str| {
        cases
            .iter()
            .filter(apart)
            .any(|case| case.program == program)
    };
    match status.as_str() {
        "equivalent" if cases.iter().any(|case| apart(&case)) => {
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

    fn variable() -> Pattern {
        Pattern::Variable(k_rust::kore::ast::Variable {
            kind: k_rust::kore::ast::VariableKind::Element,
            name: "VarX".into(),
            sort: k_rust::kore::ast::Sort::Application {
                name: "SortInt".into(),
                arguments: Vec::new(),
            },
        })
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
        assert_eq!(
            (&parsed.verdict, &parsed.start),
            (&Verdict::Run, &Some(int("1")))
        );
        assert!(pending(&parsed));
        assert_eq!(parsed.value()["stated"], "parse");
        let symbolic = stated("s", Reassembly::Assembled(variable()));
        assert_eq!(
            (&symbolic.verdict, &symbolic.start),
            (&Verdict::Unknown(MUTANT_REFUSES), &None)
        );
        assert!(!pending(&symbolic));
    }

    /// A stated case's verdict from the mutant's run alone: accepted kills, rejected agrees,
    /// anything else (not decided, no side) is unknown with the reason; a mutant that runs no
    /// case alone leaves it unknown, `grammar-run-not-supported` for an equivalent compilation.
    #[test]
    fn a_stated_case_run_alone_kills_only_where_the_mutant_accepts_it() {
        let parsed = stated("s", Reassembly::Assembled(int("1")));
        let judged = |acceptance| {
            let mut case = parsed.clone();
            alone(&mut case, acceptance);
            case
        };
        let accepted = judged(Ok(Acceptance::Accepted));
        assert_eq!(accepted.verdict, Verdict::Killed(Direction::MutantAccepts));
        assert_eq!(accepted.value()["direction"], "mutant-accepts");
        assert!(!pending(&accepted));
        assert_eq!(judged(Ok(Acceptance::Rejected)).verdict, Verdict::Agree);
        let undecided = judged(Ok(Acceptance::NotCompared(
            crate::compare::NotCompared::Undecided("several-ends".into()),
        )));
        assert_eq!(
            undecided.verdict,
            Verdict::Unknown(MUTANT_ACCEPTANCE_NOT_DECIDED)
        );
        assert!(undecided.detail.contains("several-ends"), "{undecided:?}");
        let no_side = judged(Err("cut".into()));
        assert_eq!(
            no_side.verdict,
            Verdict::Unknown(MUTANT_ACCEPTANCE_NOT_DECIDED)
        );
        let mut equivalent = parsed.clone();
        not_alone(&mut equivalent, "equivalent-compilation", true);
        assert_eq!(equivalent.verdict, Verdict::Unknown(RUN_NOT_SUPPORTED));
        let mut rejected = parsed;
        not_alone(&mut rejected, "rejected", false);
        assert_eq!(
            rejected.verdict,
            Verdict::Unknown(MUTANT_ACCEPTANCE_NOT_DECIDED)
        );
        assert!(rejected.detail.contains("`rejected`"), "{rejected:?}");
    }

    /// O decides first: a row O kills keeps its killer; a survivor or an unknown is killed by the
    /// first stated case that kills, `alone`; a survivor a stated case leaves undecided is
    /// unknown; the runs' entries and calls are appended whatever the row.
    #[test]
    fn a_stated_kill_is_read_only_where_o_kills_nothing() {
        let listed_case = listed("p", &int("1"), &row("own"), Reassembly::Assembled(int("1")));
        let run = |acceptance| {
            let mut case = stated("s", Reassembly::Assembled(int("2")));
            alone(&mut case, acceptance);
            case
        };
        let killing = run(Ok(Acceptance::Accepted));
        let mut later = run(Ok(Acceptance::Accepted));
        later.program = "t".into();
        let undecided = run(Err("cut".into()));
        let row_of = |status: &str| {
            let mut row = Map::new();
            row.insert("status".into(), json!(status));
            row.insert("reason".into(), Value::Null);
            row.insert("killer".into(), Value::Null);
            row.insert("rules".into(), json!(["r"]));
            row.insert("executed".into(), json!([{"program": "p"}]));
            row.insert("calls".into(), json!([]));
            row.insert("call_wall_ms".into(), json!([]));
            row
        };
        let entry = [json!({"program": "s", "alone": true})];
        let call = [(json!({"programs": ["s"], "alone": true}), json!(3))];
        for status in ["survived", "unknown", "timeout"] {
            let mut row = row_of(status);
            let cases = [
                listed_case.clone(),
                undecided.clone(),
                killing.clone(),
                later.clone(),
            ];
            fold_alone(&mut row, &cases, &entry, &call);
            assert_eq!(
                (&row["status"], &row["killer"], &row["killer_source"]),
                (&json!("killed"), &json!("s"), &json!(SOURCE_ALONE)),
                "{status}"
            );
            assert_eq!(row["direction"], "mutant-accepts");
            assert_eq!(row["rules"], Value::Null);
            assert_eq!(row["executed"].as_array().unwrap().len(), 2);
            assert_eq!(row["call_wall_ms"], json!([3]));
            assert_eq!(row["grammar"][2]["verdict"], "killed");
        }
        let mut killed = row_of("killed");
        killed.insert("killer".into(), json!("p"));
        fold_alone(&mut killed, &[listed_case.clone(), killing], &entry, &call);
        assert_eq!(
            (&killed["status"], &killed["killer"]),
            (&json!("killed"), &json!("p"))
        );
        assert_eq!(killed["executed"].as_array().unwrap().len(), 2);
        let mut open = row_of("survived");
        fold_alone(
            &mut open,
            &[listed_case.clone(), undecided.clone()],
            &[],
            &[],
        );
        assert_eq!(
            (&open["status"], &open["reason"]),
            (&json!("unknown"), &json!(MUTANT_ACCEPTANCE_NOT_DECIDED))
        );
        let mut unknown = row_of("unknown");
        unknown.insert("reason".into(), json!(SAME_PARSE_RUN_DIFFERS));
        fold_alone(&mut unknown, &[listed_case.clone(), undecided], &[], &[]);
        assert_eq!(unknown["reason"], SAME_PARSE_RUN_DIFFERS);
        let mut not_admitted = row_of("not-admitted");
        fold_alone(
            &mut not_admitted,
            &[listed_case, run(Ok(Acceptance::Accepted))],
            &[],
            &[],
        );
        assert_eq!(not_admitted["status"], "not-admitted");
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
        // A stated case's start is its run alone's: an equivalent compilation with every program
        // of O parsed alike survives, and a killer of that name is no program parsed apart.
        let with_stated = [
            alike[0].clone(),
            stated("q", Reassembly::Assembled(int("2"))),
        ];
        let mut equivalent = Map::new();
        equivalent.insert("status".into(), json!("equivalent"));
        read_call(&mut equivalent, &Value::Null, &with_stated);
        assert_eq!(equivalent["reason"], SAME_PARSE_EQUIVALENT);
        let mut by_stated = killed_row("q");
        read_call(&mut by_stated, &json!(["r"]), &with_stated);
        assert_eq!(by_stated["reason"], SAME_PARSE_RUN_DIFFERS);
    }

    fn killed_row(killer: &str) -> Map<String, Value> {
        let mut row = Map::new();
        row.insert("status".into(), json!("killed"));
        row.insert("reason".into(), Value::Null);
        row.insert("killer".into(), json!(killer));
        row
    }
}
