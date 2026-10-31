//! The attribute axis's cases ([`super::super::attributes`]): every attribute on every sentence
//! form, written on the form's subject slot template, and what K7 runs each accepted one on.
//!
//! A case's item is its slot's template with the slot's hole holding the form's spelling (`_`,
//! `x` or `1`), the marker's own keys removed (a rule's `label = "case-TAG"`: a rule fn's label
//! is its name by default), and the attribute written into the marker or beside it. Its spelling
//! is the attribute as written. An attribute that orders a sentence among others (`owise`,
//! `priority`, `nondet`) is written beside a sibling of the form, one sentence of the same kind
//! over the case's command whose subject also matches the command at `2`
//! ([`sibling`]); an attribute whose meaning needs a use (an existential, a fresh value, a
//! desugar clause's unbound name) has its result use the name ([`result_use`]).
//!
//! **K7.** Each case's run is its slot's driver plan (`super::drivers`) on the hole's spelling,
//! changed where the attribute changes what the sentence does:
//! - a condition that does not hold, a postcondition that does not hold (the step has no result
//!   state, so it is not taken), and `symbolic` on a run of concrete values: the sentence must
//!   not apply ([`unapplied`]);
//! - `owise`: the sentence applies where its sibling does not, and the counter run, where both
//!   match, shows the sibling's result (the sibling has priority 60, so a sentence that dropped
//!   `owise`, at the default 50, would win there);
//! - `priority = 20` and `priority = 40`, beside a sibling of priority 30: the run where both
//!   match shows the case's result for the first and, as its counter run, the sibling's for the
//!   second. The two have opposite winners, so a key dropped from both sentences (one priority
//!   for both, a tie) shows in one of them whichever way the tie breaks. `owise` has no such
//!   pair: an `owise` sentence never wins where its sibling matches;
//! - `heat`: the sentence applies where its hole, `x`, is no result (`word`, a token of a sort
//!   below no `KResult`), and the counter run, at `x` = 1 (an `Int`, a result), leaves it;
//!   `cool` the other way round; `heat, hole = x, result = Word` applies at `x` = 1, which is no
//!   `Word` (where the default `KResult` would leave it), and leaves `word`;
//! - an existential or a fresh value in the result: the sentence applies, with a value the
//!   generator does not state;
//! - every other accepted attribute (a label, `anywhere`, `nondet`, `concrete`, `smt_lemma`, a
//!   condition that holds, `ensures` that holds, a context's `result`): the sentence applies as
//!   the slot's plan states. `concrete` and `concrete(x)` are run on concrete values only, where
//!   they let the sentence apply: what they restrict, a symbolic application, needs a symbolic
//!   run, which K7 does not make.
//!
//! The extra cases ([`super::super::attributes::EXTRAS`]) run their slot's plan where the
//! sentence applies as without them, and the unapplied run where it does not (a condition before
//! the marker or a second condition that fails, `#[cfg(any())]`); a sentence about the solver's
//! function has no driver.
//!
//! The case's sentences are its own and its sibling's, both over its own command, and the base's
//! driver rules have priority 10: a case's priority (20) and its sibling's (30, 60) lie after the
//! drivers', so a driver rule, which matches only the driver commands, applies first where a
//! program sets cells up, and never meets the case's command; and no case's priority equals
//! theirs, so no driver rule shares a priority with a case's to overlap it
//! (`tests/attributes.rs` pins both).

use super::super::attributes::{
    Attribute, Effect, Extra, Form, OWISE_SIBLING_PRIORITY, PRIORITY_SIBLING_PRIORITY, Pair,
    Written, pairs,
};
use super::super::k7::{Ground, K7, Run, SkipKind, Status};
use super::super::{
    Base, Case, CaseSpec, Command, Family, ItemBuilder, OwnReason, Packaging, Side,
};
use super::drivers;
use super::{Slot, Spelling, go, hold, int, slots, spellings};

/// Every case of the attribute axis.
pub(in super::super) fn cases(cases: &mut Vec<Case>) {
    let slots = slots();
    let spellings = spellings();
    for pair in pairs() {
        let form = pair.form();
        let slot = slots
            .iter()
            .find(|slot| {
                slot.form == form.name && slot.position == form.position && slot.opener.is_none()
            })
            .unwrap_or_else(|| panic!("no slot {}/{}", form.name, form.position));
        let spelling = spellings
            .iter()
            .find(|spelling| spelling.text == form.hole)
            .unwrap_or_else(|| panic!("no spelling {}", form.hole));
        cases.push(case(pair, slot, spelling));
    }
}

/// The marker of the production a static form's clause is of, with `key`.
fn production_marker(form: Form, key: &str) -> &'static str {
    match (form.name, key) {
        ("desugar", "recursive") => "#[k::desugar(recursive)]",
        ("alias", "recursive") => "#[k::alias(recursive)]",
        (name, key) => unreachable!("no production marker of {name} with {key}"),
    }
}

/// The item of a sentence about a function the solver has a symbol for: the function, declared
/// with `smtlib`, and the form's sentence about it, `ATTRIBUTE` standing for the key.
fn solver_template(form: Form) -> String {
    let function = "/// A function the solver has a symbol for.\n#[k::function(partial, sort = Int, syntax = \"twinTAG({a}, {b})\", smtlib = \"twinTAG\")]\npub struct TwinTAG {\n    pub a: Term<Int>,\n    pub b: Term<Int>,\n}\n\n";
    let sentence = match form.name {
        "equation" => {
            "#[k::equation(ATTRIBUTE)]\nfn case_TAG(k::term![TwinTAG(x, 1)]: Term<Int>) -> Term<Int> {\n    x\n}\n"
        }
        "table" => {
            "k::equations! {\n    for TwinTAG;\n\n    #[k::equation(ATTRIBUTE)]\n    case_TAG: (x, 1) => x;\n}\n"
        }
        "simplification" => {
            "#[k::simplification(ATTRIBUTE)]\nfn case_TAG(k::term![TwinTAG(x, 1)]: Term<Int>) -> Term<Int> {\n    x\n}\n"
        }
        name => unreachable!("{name} states no sentence about a function"),
    };
    format!("{function}{sentence}")
}

fn case(pair: Pair, slot: &Slot, spelling: &Spelling) -> Case {
    let form = pair.form();
    let written = pair.written();
    let text = written.text();
    let spec = CaseSpec {
        family: Family::Attributes,
        base: Base::Terms,
        side: Side::Subject,
        kind: None,
        slot: vec![form.name.to_owned()],
        construct: pair.name().to_owned(),
    };
    let tag = spec.tag();
    let marker = match written {
        Written::Production(key) => Some(production_marker(form, key)),
        _ => slot.marker,
    };
    let command = Command::with_fields(&spec.id(), slot.arity, "KItem").marked(marker);
    let attribute = match pair {
        Pair::Attribute(_, attribute) => Some(attribute),
        Pair::Malformed(..) | Pair::Extra(..) => None,
    };
    let mut template = match written {
        Written::SolverFunction(_) => solver_template(form),
        _ => slot.template.replace("HOLE", form.hole),
    };
    if let Some(used) = attribute.and_then(|attribute| result_use(form, attribute)) {
        template = used;
    }
    let template = write_attribute(form, &template, written, attribute);
    // A production's key is written on the case's command, outside its item: the spelling is
    // the clause's own marker, which the key is about.
    let spelled = match written {
        Written::Production(_) => marker_of(form).trim(),
        _ => text,
    };
    let sibling = attribute
        .and_then(|attribute| sibling(form, attribute))
        .unwrap_or_default();
    let expand = |text: &str| {
        text.replace("TAG", &tag)
            .replace("NAME", &command.name)
            .replace("UPPER", &tag.to_uppercase())
            .replace("USES", "    use Cmd::*;\n")
            .replace("BINDERS", &slot.binders(form.hole))
    };
    let template = expand(&template);
    let sibling = expand(&sibling);
    let (before, after) = template
        .split_once("ATTRIBUTE")
        .expect("every attribute template has the attribute's place");
    let mut item = ItemBuilder::new();
    item.push(before)
        .term(&spelled.replace("TAG", &tag))
        .push(after)
        .push(&sibling);
    // A restriction of one equation of `Probe` asks that the function's other equations be
    // restricted alike, which other cases' are not: such a case is rendered alone.
    let restricts = matches!(form.name, "equation" | "table" | "simplification")
        && ["concrete", "symbolic", "smt_lemma"]
            .iter()
            .any(|key| text.contains(key));
    let packaging = if form.name == "init" {
        Packaging::Own(OwnReason::Initializer)
    } else if restricts {
        Packaging::Alone(command.clone())
    } else {
        Packaging::Shared(command.clone())
    };
    let mut case = spec.finish(packaging, &item);
    case.attribute = Some(pair);
    let (plan, counter) = match pair {
        Pair::Attribute(_, attribute) => plan(form, attribute, slot, spelling, &command),
        Pair::Malformed(..) => (
            K7::skip(SkipKind::Form, "a malformed attribute is refused"),
            None,
        ),
        Pair::Extra(_, extra) => extra_plan(form, extra, slot, spelling, &command),
    };
    case.k7 = plan;
    case.k7_counters = counter.into_iter().collect();
    case
}

/// The marker a form's template writes, its attribute path, its own keys (which a case keeps),
/// and its indentation; `None` for a clause or a row, which has no marker of its own.
fn marker(
    form: Form,
) -> Option<(
    &'static str,
    &'static str,
    &'static [&'static str],
    &'static str,
)> {
    Some(match form.name {
        "rule" | "local-rule" | "cells" | "cells-local" => {
            ("#[k::rule(label = \"case-TAG\")]\n", "rule", &[], "")
        }
        "claim" => (
            "    #[k::claim(all_paths)]\n",
            "claim",
            &["all_paths"],
            "    ",
        ),
        "cells-claim" => (
            "#[k::claim(all_paths, label = \"case-TAG\")]\n",
            "claim",
            &["all_paths", "label = \"case-TAG\""],
            "",
        ),
        "equation" => ("#[k::equation]\n", "equation", &[], ""),
        "shorthand" => (
            "#[k::function(partial, internal)]\n",
            "function",
            &["partial", "internal"],
            "",
        ),
        "simplification" => ("#[k::simplification]\n", "simplification", &[], ""),
        "context" => ("#[k::context(hole = h)]\n", "context", &["hole = h"], ""),
        "context-alias" => (
            "#[k::context_alias(name = case_TAG, here = site)]\n",
            "context_alias",
            &["name = case_TAG", "here = site"],
            "",
        ),
        "desugar" => ("#[k::desugar]\n", "desugar", &[], ""),
        "alias" => ("#[k::alias]\n", "alias", &[], ""),
        "init" => ("    #[k::init]\n", "init", &[], "    "),
        "constant" => ("#[k::constant]\n", "constant", &[], ""),
        _ => return None,
    })
}

/// The marker line a form's template writes; `""` for a clause or a row.
fn marker_of(form: Form) -> &'static str {
    marker(form).map_or("", |(old, ..)| old)
}

/// `template` with `written` in its place, `ATTRIBUTE` standing for its text: a key after the
/// marker's own keys (a modality in place of a claim's `all_paths`, a `cells!` claim's label in
/// place of its base label), a helper on the line after the marker. A clause or a row, which has
/// no marker, gets one before it for a key (`#[k::rule(..)]`, a row's `#[k::equation(..)]`), and
/// its helper after that.
fn write_attribute(
    form: Form,
    template: &str,
    written: Written,
    attribute: Option<Attribute>,
) -> String {
    let claim = matches!(form.name, "claim" | "cells-claim");
    let (key, helper) = match written {
        // The solver's template has the key's place already.
        Written::SolverFunction(_) => return template.to_owned(),
        Written::Production(_) => {
            let old = marker_of(form);
            assert_eq!(template.matches(old).count(), 1, "{}: {old:?}", form.name);
            return template.replacen(old.trim(), "ATTRIBUTE", 1);
        }
        Written::Modality(_) if claim => (None, None),
        Written::Key(_) | Written::Modality(_) => (Some("ATTRIBUTE"), None),
        Written::Helper(_) | Written::HelperBefore(_) => (None, Some("ATTRIBUTE")),
    };
    let before = matches!(written, Written::HelperBefore(_));
    if let Some((old, path, own, indent)) = marker(form) {
        assert_eq!(template.matches(old).count(), 1, "{}: {old:?}", form.name);
        let mut parts = own
            .iter()
            .filter(|part| !(attribute == Some(Attribute::Label) && part.starts_with("label")))
            .map(|part| match written {
                Written::Modality(_) if claim && *part == "all_paths" => "ATTRIBUTE",
                _ => part,
            })
            .collect::<Vec<_>>();
        parts.extend(key);
        let marker = if parts.is_empty() {
            format!("{indent}#[k::{path}]\n")
        } else {
            format!("{indent}#[k::{path}({})]\n", parts.join(", "))
        };
        let helper = helper.map_or_else(String::new, |helper| format!("{indent}{helper}\n"));
        let written = if before {
            format!("{helper}{marker}")
        } else {
            format!("{marker}{helper}")
        };
        return template.replacen(old, &written, 1);
    }
    assert!(
        !before,
        "{}: a helper before a marker the form has none of",
        form.name
    );
    let at = "    case_TAG:";
    assert_eq!(template.matches(at).count(), 1, "{}: {at:?}", form.name);
    let path = if form.name == "table" {
        "equation"
    } else {
        "rule"
    };
    let marker = key.map_or_else(String::new, |key| format!("    #[k::{path}({key})]\n"));
    let helper = helper.map_or_else(String::new, |helper| format!("    {helper}\n"));
    template.replacen(at, &format!("{marker}{helper}{at}"), 1)
}

/// The template with its result using the name `attribute` needs a use of to mean what it
/// says, wherever the form writes a result: an existential's and a fresh value's (whose
/// placement is then the only thing the case can be refused for), and a desugar clause's
/// unbound name, which only a desugar clause's key admits. A static clause's result keeps the
/// subject's `x`, which an alias clause's printing needs.
fn result_use(form: Form, attribute: Attribute) -> Option<String> {
    let name = attribute.used_name()?;
    let template = slots_template(form);
    let (old, new) = match (attribute, form.name) {
        (Attribute::UnboundVariables, "desugar") => {
            ("    Cmd::Hold(x)\n}", "    Cmd::Pair(x, NAMEUSE)\n}")
        }
        (Attribute::UnboundVariables, _) => return None,
        (_, "desugar" | "alias") => ("    Cmd::Hold(x)\n}", "    Cmd::Pair(x, NAMEUSE)\n}"),
        (_, "rule") => ("    Cmd::Hold(x)\n}", "    Cmd::Hold(NAMEUSE)\n}"),
        (_, "sort-rule") => ("=> Cmd::Hold(x);", "=> Cmd::Hold(NAMEUSE);"),
        (_, "local-rule" | "cells-local") => (
            "k::rewrite!(x => Cmd::Go())",
            "k::rewrite!(x => Cmd::Hold(NAMEUSE))",
        ),
        (_, "readable" | "claim") => ("=> { k: [..] }", "=> { k: [Cmd::Hold(NAMEUSE), ..] }"),
        (_, "cells" | "cells-claim") => (
            "k::configuration::KCell(..tail)",
            "k::configuration::KCell(Cmd::Hold(NAMEUSE), ..tail)",
        ),
        (_, "equation" | "simplification") => ("    0\n}", "    NAMEUSE\n}"),
        (_, "table") => ("=> 0;", "=> NAMEUSE;"),
        (_, "shorthand") => ("Size(x)", "Size(NAMEUSE)"),
        _ => return None,
    };
    assert_eq!(template.matches(old).count(), 1, "{}: {old:?}", form.name);
    Some(template.replacen(old, new, 1).replace("NAMEUSE", name))
}

/// The template of `form`'s slot with its hole holding the form's spelling.
fn slots_template(form: Form) -> String {
    slots()
        .into_iter()
        .find(|slot| {
            slot.form == form.name && slot.position == form.position && slot.opener.is_none()
        })
        .map(|slot| slot.template.replace("HOLE", form.hole))
        .expect("every form has its slot")
}

/// The sentence an ordering attribute's case is written beside: one of the form's kind, over
/// the case's command, whose subject also matches it at `2`, with `priority = 60` beside
/// `owise`, `priority = 30` beside `priority = 20`, and the case's group beside `nondet`. Only
/// the forms whose sentences are ordered among others of their kind, and that K7 runs, have
/// one; `nondet`'s only among transitions.
fn sibling(form: Form, attribute: Attribute) -> Option<String> {
    let key = match attribute {
        Attribute::Owise => format!("priority = {OWISE_SIBLING_PRIORITY}"),
        Attribute::Priority | Attribute::PriorityLate => {
            format!("priority = {PRIORITY_SIBLING_PRIORITY}")
        }
        Attribute::Nondet if !matches!(form.name, "equation" | "table") => {
            "nondet = gTAG".to_owned()
        }
        _ => return None,
    };
    Some(match form.name {
        "rule" => format!(
            "\n#[k::rule({key})]\nfn sib_TAG(k::term![Cmd::NAME(2, _)]: Term<Stmt>) -> Term<Stmt> {{\n    Cmd::Go()\n}}\n"
        ),
        "local-rule" => format!(
            "\n#[k::rule({key})]\nfn sib_TAG(k::term![Cmd::NAME(k::rewrite!(2 => 3), _)]: Term<Stmt>) {{}}\n"
        ),
        "sort-rule" => format!(
            "\nk::rules! {{\n    for Stmt;\nUSES\n    #[k::rule({key})]\n    sib_TAG: Cmd::NAME(2, _) => Cmd::Go();\n}}\n"
        ),
        "readable" => format!(
            "\nk::rules! {{\n    for Machine;\nUSES\n    #[k::rule({key})]\n    sib_TAG: {{ k: [Cmd::NAME(2, _), ..] }} => {{ k: [Cmd::Go(), ..] }};\n}}\n"
        ),
        "cells" => format!(
            "\n#[k::rule({key})]\npub fn sib_TAG(\n    k::cells! {{ k: k::configuration::KCell(Cmd::NAME(2, _), tail @ ..), state @ .. }}: Machine,\n) -> Machine {{\n    k::cells! {{ k: k::configuration::KCell(Cmd::Go(), ..tail), ..state }}\n}}\n"
        ),
        "cells-local" => format!(
            "\n#[k::rule({key})]\npub fn sib_TAG(\n    k::cells! {{ k: k::configuration::KCell(Cmd::NAME(k::rewrite!(2 => 3), _), ..), state @ .. }}: Machine,\n) {{\n}}\n"
        ),
        "equation" => format!(
            "\n#[k::equation({key})]\nfn sib_TAG(k::term![Probe(Cmd::NAME(), 2)]: Term<Int>) -> Term<Int> {{\n    2\n}}\n"
        ),
        "table" => format!(
            "\nk::equations! {{\n    for Probe;\n\n    #[k::equation({key})]\n    sib_TAG: (Cmd::NAME(), 2) => 2;\n}}\n"
        ),
        _ => return None,
    })
}

/// The case's command applied to `fields`.
fn command(command: &Command, fields: Vec<Ground>) -> Ground {
    Ground::ctor(&format!("Cmd::{}", command.name), fields)
}

/// The token `word`, of a sort below no `KResult`.
fn word() -> Ground {
    Ground::token("Word", "word")
}

/// A run of `program` that ends with the computation cell `items` after `steps` steps.
fn run(program: &Ground, steps: u64, items: Vec<Ground>, status: Status) -> Run {
    Run {
        program: program
            .program()
            .expect("an attribute case's program is in the program grammar"),
        variables: Vec::new(),
        depth: steps,
        steps,
        cells: vec![("k".to_owned(), Ground::Seq(items))],
        status,
        forward_only: Vec::new(),
    }
}

/// A run of `program` in which the case's sentence must not apply: the base's step, if any,
/// stays (an equation's call leaves `Probe` unevaluated), and the case's is not taken.
fn unapplied(form: Form, program: &Ground, cmd: &Command) -> Run {
    match form.name {
        "equation" | "table" => {
            let Ground::Ctor { fields, .. } = program else {
                unreachable!("an equation's program is `call(..)`")
            };
            let argument = fields[1].clone();
            run(
                program,
                1,
                vec![hold(Ground::unevaluated(
                    "probe",
                    vec![command(cmd, Vec::new()), argument],
                ))],
                Status::Value,
            )
        }
        _ => Run {
            depth: 1,
            ..run(program, 0, vec![program.clone()], Status::Value)
        },
    }
}

/// The program a form's driver writes with the command's first field `first` and its second the
/// hole's witness, `0`, or an equation's call at `first`.
fn program_at(form: Form, cmd: &Command, first: Ground) -> Ground {
    match form.name {
        "equation" | "table" => Ground::ctor("Cmd::Call", vec![command(cmd, Vec::new()), first]),
        _ => command(cmd, vec![first, int(0)]),
    }
}

/// The computation cell a transition of `form` leaves after applying to the command at `first`:
/// its result `Cmd::Hold(x)` (or, where the result uses `name`, its value `used`), a readable
/// or `cells!` rule's nothing, a single-body rule's command with `go` (or `Cmd::Hold(used)`) in
/// place of its first field.
fn applied_items(form: Form, cmd: &Command, first: Ground, used: Option<Ground>) -> Vec<Ground> {
    match form.name {
        "rule" | "sort-rule" => vec![hold(used.unwrap_or(first))],
        "readable" | "cells" => used.map(hold).into_iter().collect(),
        "local-rule" | "cells-local" => {
            vec![command(cmd, vec![used.map_or_else(go, hold), int(0)])]
        }
        name => unreachable!("{name} is no transition form"),
    }
}

/// What K7 runs an accepted case on, and its counter run ([module docs](self)).
fn plan(
    form: Form,
    attribute: Attribute,
    slot: &Slot,
    spelling: &Spelling,
    cmd: &Command,
) -> (K7, Option<Run>) {
    let base = drivers::plan(slot, spelling, cmd);
    if matches!(base, K7::Skip(_)) {
        return (base, None);
    }
    let transition = matches!(
        form.name,
        "rule" | "local-rule" | "sort-rule" | "readable" | "cells" | "cells-local"
    );
    let equation = matches!(form.name, "equation" | "table");
    let at = |first: Ground| program_at(form, cmd, first);
    let sibling_wins = || {
        if equation {
            run(&at(int(2)), 1, vec![hold(int(2))], Status::Value)
        } else if matches!(form.name, "local-rule" | "cells-local") {
            run(
                &at(int(2)),
                1,
                vec![command(cmd, vec![int(3), int(0)])],
                Status::Value,
            )
        } else {
            run(&at(int(2)), 1, vec![go()], Status::Value)
        }
    };
    match attribute {
        Attribute::RequiresFails | Attribute::Symbolic if transition || equation => {
            (K7::Run(unapplied(form, &at(int(1)), cmd)), None)
        }
        // A postcondition that does not hold leaves the step no result state: it is not taken.
        Attribute::EnsuresFails if transition => (K7::Run(unapplied(form, &at(int(1)), cmd)), None),
        Attribute::RequiresFails if form.name == "context" => {
            let program = command(cmd, vec![word(), int(1), int(0)]);
            (K7::Run(unapplied(form, &program, cmd)), None)
        }
        // `owise`, and a priority after the sibling's: the sentence applies where its sibling
        // does not, and the sibling wins where both match.
        Attribute::Owise | Attribute::PriorityLate if transition || equation => {
            (base, Some(sibling_wins()))
        }
        Attribute::Priority if transition || equation => {
            let wins = if equation {
                run(&at(int(2)), 1, vec![hold(int(0))], Status::Value)
            } else {
                run(
                    &at(int(2)),
                    1,
                    applied_items(form, cmd, int(2), None),
                    Status::Value,
                )
            };
            (K7::Run(wins), None)
        }
        Attribute::Heat if transition => {
            let heated = run(
                &at(word()),
                1,
                applied_items(form, cmd, word(), None),
                Status::Value,
            );
            (K7::Run(heated), Some(unapplied(form, &at(int(1)), cmd)))
        }
        Attribute::Cool if transition => (base, Some(unapplied(form, &at(word()), cmd))),
        // Heated where its hole is no `Word`: at `x` = 1, which the default `KResult` leaves.
        Attribute::HeatResult if transition => {
            let heated = run(
                &at(int(1)),
                1,
                applied_items(form, cmd, int(1), None),
                Status::Value,
            );
            (K7::Run(heated), Some(unapplied(form, &at(word()), cmd)))
        }
        // An anywhere rule rewrites its subject wherever it occurs, as the program's
        // configuration is built too: below `hold(..)`, before any step.
        Attribute::Anywhere if transition => {
            let below = hold(at(int(1)));
            let items = applied_items(form, cmd, int(1), None)
                .into_iter()
                .map(hold)
                .collect::<Vec<_>>();
            (
                K7::Run(Run {
                    depth: 1,
                    ..run(&below, 0, items, Status::Value)
                }),
                None,
            )
        }
        Attribute::Exists | Attribute::Fresh if transition => (
            K7::Run(run(
                &at(int(1)),
                1,
                applied_items(form, cmd, int(1), Some(Ground::Any)),
                Status::Liveness,
            )),
            None,
        ),
        Attribute::UnboundVariables => (
            K7::skip(
                SkipKind::Witness,
                "the clause's result leaves `y` to the sentence it is expanded in, and a program binds no name",
            ),
            None,
        ),
        _ => (base, None),
    }
}

/// What K7 runs an extra case on: the slot's plan where the sentence applies as without the
/// attribute, the unapplied run where it does not; a sentence about the solver's function has no
/// driver.
fn extra_plan(
    form: Form,
    extra: Extra,
    slot: &Slot,
    spelling: &Spelling,
    cmd: &Command,
) -> (K7, Option<Run>) {
    if matches!(extra.written, Written::SolverFunction(_)) {
        return (
            K7::skip(
                SkipKind::Form,
                "the function the case declares for the solver has no driver command",
            ),
            None,
        );
    }
    let base = drivers::plan(slot, spelling, cmd);
    if matches!(base, K7::Skip(_)) {
        return (base, None);
    }
    match extra.effect {
        Effect::Applies => (base, None),
        Effect::Unapplied => (
            K7::Run(unapplied(form, &program_at(form, cmd, int(1)), cmd)),
            None,
        ),
    }
}
