//! K7, the full tier: an accepted case's program, run on the definition K6 judged, shows that
//! the case's sentence applied, and with the value the generator states
//! ([`krs_test_support::class_matrix::k7`]).
//!
//! A program goes through the run commands' own path: [`Semantics::configure`] parses it with
//! the definition's program grammar, expands its desugars and aliases, and builds the initial
//! configuration, as `krs run FILE` does, and [`Semantics::run`] follows one path. The run is
//! bounded by the plan's step count and by a time limit, enforced by cancelling the backend's
//! request from a watchdog thread; a run that reaches the limit is a deviation, not a hang.

use std::sync::mpsc;
use std::time::Duration;

use k_rust::backend::CancellationToken;
use k_rust::kore::ast::Pattern;
use krs_exec::{
    CellError, ConfigInputs, Halt, ProgramInput, ReadBack, RunOptions, RunReport, Semantics,
    SortRef, StateView, Term, Value, ValueIndex, View, unparse,
};
use krs_test_support::class_matrix::k7::{Ground, Run, Status};

/// K7's verdict on one run.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Ran {
    /// The run showed what the plan states.
    Conforms(Status),
    /// It did not: what it showed instead.
    Deviates(String),
}

impl Ran {
    /// The verdict as the pending list records it.
    #[must_use]
    pub fn signature(&self) -> String {
        match self {
            // A run as stated is not always one where the sentence applied: an `undefined` run's
            // sentence must not apply.
            Self::Conforms(status) => format!("ran as stated ({})", status.name()),
            Self::Deviates(observed) => observed.clone(),
        }
    }
}

/// How a case's run ended on a definition without what the case states (K7's dependency check,
/// `pipeline::Worker::check_dependency`), judged by the plan's steps and cells only: a print is
/// the printer's, not the sentence's, so it is not read back here.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Without {
    /// The run completed and ended otherwise than the plan states, in its steps or its cells
    /// (or, for a static clause's counter run, in whether the program expands): what it showed.
    Differs(String),
    /// The run completed and ended as the plan states.
    Same,
    /// The run did not complete (the program does not configure, the time limit, a state that
    /// does not decode, more than one state), so it shows neither: why.
    NotMade(String),
}

/// Run `run` on `semantics`, a definition without what the case states, within `limit`
/// ([`Without`]). Where `declared_only` (the base's own initializer in place of the case's), a
/// configuration variable the definition does not declare is the case's initializer's own input,
/// which the run without that initializer does not take.
pub fn run_without(
    semantics: &mut Semantics,
    run: &Run,
    limit: Duration,
    declared_only: bool,
) -> Without {
    let mut inputs = inputs(run);
    if declared_only {
        let declared = semantics.variables();
        inputs.variables.retain(|(name, _)| {
            declared
                .iter()
                .any(|variable| variable.name == *name || variable.parameter == *name)
        });
    }
    let report = match bounded(semantics, &inputs, run.depth, limit) {
        Ok(_) if run.status == Status::Unexpanded => {
            return Without::Differs("expanded where the plan states it is not".to_owned());
        }
        Err(deviation)
            if run.status == Status::Unexpanded && deviation.contains("survived expansion") =>
        {
            return Without::Same;
        }
        Ok(report) => report,
        Err(deviation) => return Without::NotMade(deviation),
    };
    let views = match semantics.views(&report.state) {
        Ok(views) => views,
        Err(error) => {
            return steps_deviation(run, &report, "").map_or_else(
                || Without::NotMade(format!("the state does not decode: {error}")),
                Without::Differs,
            );
        }
    };
    let index = semantics.values();
    let observed = match views.as_slice() {
        [View::State(view)] => run
            .cells
            .iter()
            .map(|(cell, expected)| (cell, expected, read(view, index, cell)))
            .collect::<Vec<_>>(),
        _ => Vec::new(),
    };
    if let Some(deviation) = steps_deviation(run, &report, &shown_cells(&observed)) {
        return Without::Differs(deviation);
    }
    match views.as_slice() {
        [View::State(_)] => match verdict(run, &report, &observed) {
            Ran::Conforms(_) => Without::Same,
            Ran::Deviates(deviation) => Without::Differs(deviation),
        },
        [View::Bottom] => Without::Differs(format!(
            "no configuration (\\bottom) after {} of {} steps",
            report.steps, run.steps
        )),
        _ => Without::NotMade(format!(
            "{} states after {} of {} steps",
            views.len(),
            report.steps,
            run.steps
        )),
    }
}

/// The inputs `krs run` gives `run`'s program: the program as `$PGM`, and its variables.
fn inputs(run: &Run) -> ConfigInputs {
    ConfigInputs {
        program: Some(ProgramInput {
            name: "program".to_owned(),
            text: run.program.clone(),
        }),
        variables: run
            .variables
            .iter()
            .map(|(name, text)| (name.clone(), text.as_str().into()))
            .collect(),
        stdin: None,
    }
}

/// Run `run` on `semantics`, the definition `krs run` loads, within `limit`; `own` is the name of
/// the case's command (`C64289ea3`), whose aliases the case prints with beside the base's.
pub fn run_case(semantics: &mut Semantics, run: &Run, limit: Duration, own: Option<&str>) -> Ran {
    let inputs = inputs(run);
    let report = match bounded(semantics, &inputs, run.depth, limit) {
        Ok(_) if run.status == Status::Unexpanded => {
            return Ran::Deviates("expanded where the subject should not match".to_owned());
        }
        Err(deviation)
            if run.status == Status::Unexpanded && deviation.contains("survived expansion") =>
        {
            return Ran::Conforms(Status::Unexpanded);
        }
        Ok(report) => report,
        Err(deviation) => return Ran::Deviates(deviation),
    };
    let views = match semantics.views(&report.state) {
        Ok(views) => views,
        Err(error) => {
            return Ran::Deviates(format!("failed: the state does not decode: {error}"));
        }
    };
    let view = match views.as_slice() {
        [View::State(view)] => view,
        // A first state with no value is no configuration: a static clause's result or an
        // initializer that builds a term with no value, which no step precedes.
        [View::Bottom] if run.status == Status::UndefinedResult && report.steps == run.steps => {
            return Ran::Conforms(Status::UndefinedResult);
        }
        [View::Bottom] => {
            return Ran::Deviates(format!(
                "no configuration (\\bottom) after {} of {} steps",
                report.steps, run.steps
            ));
        }
        _ => {
            return Ran::Deviates(format!(
                "{} states after {} of {} steps",
                views.len(),
                report.steps,
                run.steps
            ));
        }
    };
    let index = semantics.values();
    let observed = run
        .cells
        .iter()
        .map(|(cell, expected)| (cell, expected, read(view, index, cell)))
        .collect::<Vec<_>>();
    match verdict(run, &report, &observed) {
        Ran::Conforms(status) => {
            printed_reads_back(semantics, &report.state, own, &run.forward_only)
                .or_else(|| program_reads_back(semantics, &run.program, own))
                .map_or(Ran::Conforms(status), Ran::Deviates)
        }
        deviates @ Ran::Deviates(_) => deviates,
    }
}

/// Whether the state, as `krs run` prints it, is the state: the computation cell's first item and
/// every other leaf cell's content, each printed and read back as a program reads it, must be the
/// term the state holds, value for value, instance for instance ([`Semantics::read_back`], the
/// rule `KRS_CHECK_PRINTS=1` checks `krs run`'s prints with: the program grammar where the
/// content is program text throughout, the main module's grammar elsewhere, tokens by text
/// there, and a stated skip where no grammar writes a part). `None` when each is; otherwise the
/// first deviation.
///
/// The printer is the one the case prints with alone ([`case_printer`]), so that a verdict does
/// not depend on the batch.
///
/// Before it is read back, a print must reverse exactly the aliases the plan states: it must be
/// the print of a printer that reverses every alias of the definition but those `forward_only`
/// names (the plan's [`Run::forward_only`]: clauses whose written results compute, or whose
/// subject's token no program reads back). A print through one of those names a term the author
/// did not write, though the alias read back denotes the value; a print that leaves out another
/// keeps a constructing clause forward only. Either is a deviation.
fn printed_reads_back(
    semantics: &mut Semantics,
    state: &Term,
    own: Option<&str>,
    forward_only: &[String],
) -> Option<String> {
    let case = case_printer(semantics.unparser(), own);
    let stated = case_printer(&semantics.unparser().reversing_every_alias(), own)
        .retaining_aliases(|symbol| {
            !forward_only
                .iter()
                .any(|name| symbol.strip_prefix("Lblcmd") == Some(name.as_str()))
        });
    let options = unparse::Options::new(unparse::Mode::Pretty);
    for cell in semantics.printed_cells(&case, state) {
        let expected = stated.print_kore(cell.content, &options);
        if expected.text != cell.printed.text {
            return Some(format!(
                "{} printed `{}`, where reversing the aliases the plan states prints `{}`",
                cell.place, cell.printed.text, expected.text
            ));
        }
        match semantics.read_back(&cell) {
            Ok(ReadBack::Reads | ReadBack::Skipped(_)) => {}
            Ok(ReadBack::Fails(deviation)) => return Some(deviation),
            Err(error) => {
                return Some(format!(
                    "{} printed `{}`, which cannot be read back: {}",
                    cell.place,
                    cell.printed.text,
                    first_line(&error.to_string())
                ));
            }
        }
    }
    None
}

/// Whether the case's program, as `krs parse --output program` prints it with the case's printer
/// ([`case_printer`], [`Semantics::unparse_program_by`]), reads back as the program
/// ([`Semantics::read_back_program`]): so every production shape the generated cases write
/// (prefix, postfix, mixfix, infix under each priority and associativity, through the aliases
/// the case reverses) is printed and read back with the program grammar. `None` when it reads
/// back, or where its print states that it cannot; otherwise the deviation.
fn program_reads_back(
    semantics: &mut Semantics,
    program: &str,
    own: Option<&str>,
) -> Option<String> {
    let case = case_printer(semantics.unparser(), own);
    let input = ProgramInput {
        name: "program".to_owned(),
        text: program.to_owned(),
    };
    let read = semantics
        .unparse_program_by(&case, None, &input)
        .and_then(|printed| semantics.read_back_program(None, &input, &printed));
    match read {
        Ok(ReadBack::Reads | ReadBack::Skipped(_)) => None,
        Ok(ReadBack::Fails(deviation)) => Some(deviation),
        Err(error) => Some(format!(
            "the program does not print as program text: {}",
            first_line(&error.to_string())
        )),
    }
}

/// The printer of the case whose command is `own` alone: the definition's, without the aliases
/// of the other cases' commands (a production `Lblcmd` + `C` and eight hexadecimal digits,
/// [`krs_test_support::class_matrix::Command`]), which a batch's definition holds beside it.
fn case_printer(printer: &unparse::Unparser, own: Option<&str>) -> unparse::Unparser {
    let own = own.map(|name| format!("Lblcmd{name}"));
    printer.retaining_aliases(|symbol| {
        let other_case = symbol.strip_prefix("LblcmdC").is_some_and(|digits| {
            digits.len() == 8 && digits.bytes().all(|byte| byte.is_ascii_hexdigit())
        });
        !other_case || own.as_deref() == Some(symbol)
    })
}

/// How a twin check's run ([`krs_test_support::class_matrix::twin_runs`]) of `run` ended, within
/// `limit`: `builds T`, where it took its steps and `T` is the term at its result's hole as the
/// state holds it, in KORE, its instances and injections included (the computation's first item,
/// or where `root` is false that item's last argument); `has no value`, where the result it
/// reached is undefined; `does not apply`, where the sentence's subject does not match the
/// program (a rule that takes no step; a static clause whose production survives the program's
/// expansion, which `krs run` refuses to execute); or what else it showed. Twins compare these
/// texts.
pub fn twin_end(semantics: &mut Semantics, run: &Run, root: bool, limit: Duration) -> String {
    let inputs = inputs(run);
    let report = match bounded(semantics, &inputs, run.depth, limit) {
        Ok(report) => report,
        Err(deviation) if deviation.contains("survived expansion") => {
            return "does not apply".to_owned();
        }
        Err(deviation) => return deviation,
    };
    // The result has no value: the backend decided it undefined, before the step it would have
    // ended in, or the state the run reached holds a term with no value, at any step.
    if report.steps <= run.steps && report.halt == Halt::Undefined {
        return "has no value".to_owned();
    }
    if report.steps == 0 && run.steps > 0 && report.halt == Halt::Stuck {
        return "does not apply".to_owned();
    }
    if report.steps != run.steps {
        return format!(
            "stops after {} of {} steps, {}",
            report.steps,
            run.steps,
            report.halt.as_str()
        );
    }
    let views = match semantics.views(&report.state) {
        Ok(views) => views,
        Err(error) => return format!("failed: the state does not decode: {error}"),
    };
    let view = match views.as_slice() {
        [View::State(view)] => view,
        [View::Bottom] => return "has no value".to_owned(),
        _ => return format!("{} states", views.len()),
    };
    match view.content("k") {
        Ok(content) => hole(content, root).map_or_else(
            || format!("no hole in `{content}`"),
            |term| format!("builds {term}"),
        ),
        Err(error) => format!("no computation cell: {error}"),
    }
}

/// The term at a result's hole in the computation cell's content `k`: its first item, or where
/// `root` is false that item's last argument, below the item's own injection into `KItem`.
fn hole(k: &Pattern, root: bool) -> Option<&Pattern> {
    let Pattern::Application { symbol, arguments } = k else {
        return None;
    };
    let ("kseq", [item, _]) = (symbol.name.as_str(), arguments.as_slice()) else {
        return None;
    };
    if root {
        return Some(item);
    }
    let mut term = item;
    while let Pattern::Application { symbol, arguments } = term
        && symbol.name.as_str() == "inj"
        && let [argument] = arguments.as_slice()
    {
        term = argument;
    }
    match term {
        Pattern::Application { arguments, .. } => arguments.last(),
        _ => None,
    }
}

/// Whether K7 checks that each run reported stuck ended where no rule applies, at a state that is
/// its own value (`krs_exec::RunOptions::check_ends`): on unless `KRS_CHECK_ENDS=0`. A run that
/// fails the check deviates with the check's message.
fn check_ends() -> bool {
    std::env::var_os(krs_test_support::CHECK_ENDS).as_deref() != Some(std::ffi::OsStr::new("0"))
}

/// Configure `inputs` and run the state within `depth` steps, both within `limit`: the program's
/// parse and expansion and the run are one request of the backend's, cancelled from a watchdog
/// thread at the limit. The report, or the deviation.
fn bounded(
    semantics: &mut Semantics,
    inputs: &ConfigInputs,
    depth: u64,
    limit: Duration,
) -> Result<RunReport, String> {
    let token = CancellationToken::new();
    let (done, finished) = mpsc::channel::<()>();
    let watchdog = {
        let token = token.clone();
        std::thread::spawn(move || {
            if finished.recv_timeout(limit) == Err(mpsc::RecvTimeoutError::Timeout) {
                token.cancel();
            }
        })
    };
    let report = token.scope(|| {
        let state = semantics
            .configure(inputs)
            .map_err(|error| format!("failed: {}", first_line(&error.to_string())))?;
        semantics
            .run(
                &state,
                RunOptions {
                    depth: Some(depth),
                    trace: false,
                    check_ends: check_ends(),
                },
            )
            .map_err(|error| format!("failed: {}", first_line(&error.to_string())))
    });
    let _ = done.send(());
    let _ = watchdog.join();
    if token.is_cancelled() {
        return Err(format!("time limit: no end within {} s", limit.as_secs()));
    }
    report
}

/// K7's verdict on a run that ended after `report.steps` steps with the cells `observed`, each
/// beside the term the plan states.
fn verdict(run: &Run, report: &RunReport, observed: &[(&String, &Ground, Ground)]) -> Ran {
    let shown = shown_cells(observed);
    if let Some(deviation) = steps_deviation(run, report, &shown) {
        return Ran::Deviates(deviation);
    }
    if observed
        .iter()
        .all(|(_, expected, value)| expected.agrees(value))
    {
        Ran::Conforms(run.status)
    } else {
        let expected = observed
            .iter()
            .map(|(cell, expected, _)| format!("{cell} = {expected}"))
            .collect::<Vec<_>>()
            .join(", ");
        Ran::Deviates(format!(
            "another value: {shown}, where the plan states {expected}"
        ))
    }
}

/// The cells a run ended with, as a deviation shows them.
fn shown_cells(observed: &[(&String, &Ground, Ground)]) -> String {
    observed
        .iter()
        .map(|(cell, _, value)| format!("{cell} = {value}"))
        .collect::<Vec<_>>()
        .join(", ")
}

/// How a run that ended after `report.steps` steps took other steps than the plan states, if it
/// did, with the cells it ended with (`shown`, which may be empty).
fn steps_deviation(run: &Run, report: &RunReport, shown: &str) -> Option<String> {
    // The cells, after a separator, where the plan reads any.
    let cells = if shown.is_empty() {
        String::new()
    } else {
        format!("; {shown}")
    };
    // Where the sentence's result has no value at the run's input the sentence applies and its
    // next state is undefined: the run ends undefined after the steps before the sentence's, not
    // stuck (a sentence that did not apply) nor at a state that holds the term as a value.
    if run.status == Status::UndefinedResult {
        return (report.halt != Halt::Undefined || report.steps != run.steps).then(|| {
            format!(
                "ended {} after {} steps, where the sentence's result has no value, so the sentence applies and the run ends undefined after {} steps{cells}",
                report.halt.as_str(),
                report.steps,
                run.steps,
            )
        });
    }
    // A rule that matched and whose result has no value ends the run undefined, which is no
    // stuck rule.
    if report.steps < run.steps && report.halt == Halt::Undefined {
        return Some(format!(
            "no defined result: after {} of {} steps, the next state is undefined{cells}",
            report.steps, run.steps,
        ));
    }
    if report.steps < run.steps {
        return Some(format!(
            "not applied: {} of {} steps, then {}{cells}",
            report.steps,
            run.steps,
            report.halt.as_str(),
        ));
    }
    if report.steps > run.steps {
        return Some(format!(
            "applied where it should not: {} steps where the plan takes {}{cells}",
            report.steps, run.steps,
        ));
    }
    // Where the construct has no value the sentence does not apply: no rule applies after the
    // steps before it, and the run ends stuck, not at an undefined state (a sentence that applied
    // to a term with no value) or another halt.
    if run.status == Status::Undefined && report.halt != Halt::Stuck {
        return Some(format!(
            "ended {} after {} steps, where the construct has no value, so the sentence does not apply and the run ends stuck{cells}",
            report.halt.as_str(),
            report.steps,
        ));
    }
    None
}

/// The cell at `path` as the generator states it (`Run::cells`): a leaf's content, an optional
/// cell the state does not hold as [`Ground::Absent`], and a repeated cell's instances by
/// `PATH[CHILD,..]` (a List collection's, in order) or `PATH{CHILD,..}` (a Set collection's, as a
/// set), each the constructor named after the collection of its children's contents.
fn read(view: &StateView<'_>, index: &ValueIndex, path: &str) -> Ground {
    let Some((cell, children, set)) = path
        .strip_suffix(']')
        .and_then(|path| path.split_once('['))
        .map(|(cell, children)| (cell, children, false))
        .or_else(|| {
            path.strip_suffix('}')
                .and_then(|path| path.split_once('{'))
                .map(|(cell, children)| (cell, children, true))
        })
    else {
        return leaf(view, index, path);
    };
    let instances = match view.instances(cell) {
        Ok(instances) => instances,
        Err(error) => return Ground::Opaque(error.to_string()),
    };
    let name = cell.rsplit('.').next().unwrap_or(cell);
    let items = instances
        .iter()
        .map(|instance| {
            Ground::ctor(
                name,
                children
                    .split(',')
                    .map(|child| leaf(instance, index, child))
                    .collect(),
            )
        })
        .collect();
    if set {
        Ground::set(items)
    } else {
        Ground::List(items)
    }
}

/// The content of the leaf cell at `path`.
fn leaf(view: &StateView<'_>, index: &ValueIndex, path: &str) -> Ground {
    match view.value(path) {
        Ok(value) => ground(index, &value),
        Err(CellError::Absent { .. }) => Ground::Absent,
        Err(error) => Ground::Opaque(error.to_string()),
    }
}

fn first_line(text: &str) -> &str {
    text.lines().next().unwrap_or_default()
}

/// A run's term as the generator's [`Ground`]: an application of a function no equation
/// evaluated by its K label, anything else without a ground form by its KORE text.
fn ground(index: &ValueIndex, value: &Value) -> Ground {
    let all = |values: &[Value]| values.iter().map(|value| ground(index, value)).collect();
    match value {
        Value::Ctor(ctor) => Ground::ctor(
            local(ctor.decl().path()),
            ctor.fields()
                .iter()
                .map(|(_, value)| ground(index, value))
                .collect(),
        ),
        Value::Int(value) => {
            i64::try_from(value).map_or_else(|_| Ground::Opaque(value.to_string()), Ground::Int)
        }
        Value::Bool(value) => Ground::Bool(*value),
        Value::String(text) => Ground::String(text.clone()),
        Value::Bytes(bytes) => Ground::Bytes(bytes.clone()),
        Value::Float(float) => float
            .to_f64()
            .map_or_else(|| Ground::Opaque(float.literal().to_owned()), Ground::float),
        Value::Token { sort, text } => Ground::Token {
            sort: match sort {
                SortRef::Declared(decl) => local(decl.path()).to_owned(),
                SortRef::Builtin(builtin) => builtin.k_name().to_owned(),
            },
            text: text.clone(),
        },
        Value::Seq(items) => Ground::Seq(all(items)),
        Value::List(items) => Ground::List(all(items)),
        Value::Set(elements) => {
            Ground::set(elements.iter().map(|value| ground(index, value)).collect())
        }
        Value::Map(entries) => Ground::map(
            entries
                .iter()
                .map(|(key, value)| (ground(index, key), ground(index, value)))
                .collect(),
        ),
        Value::Opaque(pattern) => opaque(index, pattern),
    }
}

/// A declaration's path from the batch package's root: the package's name, which its source
/// names, left out, so that a path reads alike in every batch.
fn local(path: &str) -> &str {
    match path.split_once("::") {
        Some((package, rest)) if package.starts_with("krs_class_") => rest,
        _ => path,
    }
}

/// A pattern with no KRS description: a function's application that stayed as written, by the
/// label of its K symbol (`Lblsize` is `size`), below its injection into a wider sort, or the
/// pattern's text.
fn opaque(index: &ValueIndex, pattern: &Pattern) -> Ground {
    if let Pattern::Application { symbol, arguments } = pattern
        && symbol.name.as_str() == "inj"
        && let [argument] = arguments.as_slice()
    {
        return match index.decode(argument) {
            Ok(Value::Opaque(inner)) => opaque(index, &inner),
            Ok(value) => ground(index, &value),
            Err(_) => Ground::Opaque(pattern.to_string()),
        };
    }
    if let Pattern::Application { symbol, arguments } = pattern
        && let Some(label) = symbol.name.as_str().strip_prefix("Lbl")
        && let Ok(arguments) = arguments
            .iter()
            .map(|argument| index.decode(argument))
            .collect::<Result<Vec<_>, _>>()
    {
        return Ground::unevaluated(
            label,
            arguments
                .iter()
                .map(|argument| ground(index, argument))
                .collect(),
        );
    }
    Ground::Opaque(pattern.to_string())
}
