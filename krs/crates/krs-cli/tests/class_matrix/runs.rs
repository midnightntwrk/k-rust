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
use k_rust::kore::ast::{Pattern, Sort as KoreSort};
use krs_exec::{
    CellError, ConfigInputs, Halt, ProgramInput, RunOptions, RunReport, Semantics, SortRef,
    StateView, Term, Value, ValueIndex, View, unparse,
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
            Self::Conforms(status) => format!("applied as stated ({})", status.name()),
            Self::Deviates(observed) => observed.clone(),
        }
    }
}

/// Run `run` on `semantics`, the definition `krs run` loads, within `limit`; `own` is the name of
/// the case's command (`C64289ea3`), whose aliases the case prints with beside the base's.
pub fn run_case(semantics: &mut Semantics, run: &Run, limit: Duration, own: Option<&str>) -> Ran {
    let inputs = ConfigInputs {
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
    };
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
                .map_or(Ran::Conforms(status), Ran::Deviates)
        }
        deviates @ Ran::Deviates(_) => deviates,
    }
}

/// Whether the state, as `krs run` prints it, is the state: the computation cell's first item and
/// every other leaf cell's content, each printed and read back with the definition's grammar
/// (which expands its aliases again, [`Semantics::parse_k_head`], [`Semantics::parse_cell`]),
/// must be the term the state holds, value for value. `None` when each is; otherwise the first
/// deviation.
///
/// The printer is the one the case prints with alone ([`case_printer`]), so that a verdict does
/// not depend on the batch. A print with a warning (a symbol printed as KAST) is not read back,
/// and neither is a cell of a sort with parameters, nor a print that does not parse where the
/// term printed without reversing an alias does not parse either. Tokens compare by text
/// ([`untyped_tokens`]).
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
    let as_held = unparse::Options {
        reverse_aliases: false,
        ..options
    };
    let mut cells = Vec::new();
    if let Some(Some(item)) = state.k_head_kore() {
        cells.push(("<k>".to_owned(), None, item));
    }
    for (symbol, content) in state.leaf_cells() {
        let label = unparse::label_name(symbol);
        if label == "<k>" {
            continue;
        }
        let Some(sort) = case
            .argument_sorts(symbol)
            .and_then(<[KoreSort]>::first)
            .and_then(k_sort)
        else {
            continue;
        };
        cells.push((label, Some(sort), content));
    }
    for (cell, sort, content) in cells {
        let printed = case.print_kore(content, &options);
        let place = if sort.is_none() {
            "<k> head"
        } else {
            cell.as_str()
        };
        let expected = stated.print_kore(content, &options);
        if expected.text != printed.text {
            return Some(format!(
                "{place} printed `{}`, where reversing the aliases the plan states prints `{}`",
                printed.text, expected.text
            ));
        }
        if !printed.warnings.is_empty() {
            continue;
        }
        let name = cell.trim_start_matches('<').trim_end_matches('>');
        let mut read_back = |text: &str| match &sort {
            None => semantics.parse_k_head(text),
            Some(sort) => semantics.parse_cell(name, sort, text),
        };
        let read = match read_back(&printed.text) {
            Ok(read) => read,
            // Where the term printed as the state holds it does not parse either, the grammar
            // has no syntax for a part of it (an `Id` token `$x`, a parametric instance), which
            // is no property of the print.
            Err(_) if read_back(&case.print_kore(content, &as_held).text).is_err() => {
                continue;
            }
            Err(error) => {
                return Some(format!(
                    "{place} printed `{}`, which does not read back: {}",
                    printed.text,
                    first_line(&error.to_string())
                ));
            }
        };
        let index = semantics.values();
        let value = |pattern: &Pattern| {
            untyped_tokens(index.decode(pattern).map_or_else(
                |_| Ground::Opaque(pattern.to_string()),
                |value| ground(index, &value),
            ))
        };
        let (held, read) = (value(content), value(&read));
        if held != read {
            return Some(format!(
                "{place} printed `{}`, which reads back as {read}, where the state holds {held}",
                printed.text
            ));
        }
    }
    None
}

/// `ground` with every token's sort left out: a token prints as its text alone, so where two
/// token sorts read the same text (`word`, a `Word` and an `Id`), the text reads back as the one
/// the grammar picks, and the print says no more than the text.
fn untyped_tokens(ground: Ground) -> Ground {
    let all = |items: Vec<Ground>| items.into_iter().map(untyped_tokens).collect();
    match ground {
        Ground::Token { text, .. } => Ground::Token {
            sort: String::new(),
            text,
        },
        Ground::Ctor { path, fields } => Ground::Ctor {
            path,
            fields: all(fields),
        },
        Ground::Unevaluated { label, arguments } => Ground::Unevaluated {
            label,
            arguments: all(arguments),
        },
        Ground::List(items) => Ground::List(all(items)),
        Ground::Seq(items) => Ground::Seq(all(items)),
        Ground::Set(elements) => Ground::set(all(elements)),
        Ground::Map(entries) => Ground::map(
            entries
                .into_iter()
                .map(|(key, value)| (untyped_tokens(key), untyped_tokens(value)))
                .collect(),
        ),
        other => other,
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

/// The K name of a KORE sort without parameters (`SortMap{}` is `Map`).
fn k_sort(sort: &KoreSort) -> Option<String> {
    match sort {
        KoreSort::Application { name, arguments } if arguments.is_empty() => {
            name.strip_prefix("Sort").map(unparse::decode_kore)
        }
        _ => None,
    }
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
    let inputs = ConfigInputs {
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
    };
    let report = match bounded(semantics, &inputs, run.depth, limit) {
        Ok(report) => report,
        Err(deviation) if deviation.contains("survived expansion") => {
            return "does not apply".to_owned();
        }
        Err(deviation) => return deviation,
    };
    if report.steps < run.steps && report.halt == Halt::Undefined {
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
    let show = |side: fn(&(&String, &Ground, Ground)) -> String| {
        observed.iter().map(side).collect::<Vec<_>>().join(", ")
    };
    let shown = show(|(cell, _, value)| format!("{cell} = {value}"));
    // The cells, after a separator, where the plan reads any.
    let cells = if shown.is_empty() {
        String::new()
    } else {
        format!("; {shown}")
    };
    // A rule that matched and whose result has no value ends the run undefined, which is no
    // stuck rule.
    if report.steps < run.steps && report.halt == Halt::Undefined {
        return Ran::Deviates(format!(
            "no defined result: after {} of {} steps, the next state is undefined{cells}",
            report.steps, run.steps,
        ));
    }
    if report.steps < run.steps {
        return Ran::Deviates(format!(
            "not applied: {} of {} steps, then {}{cells}",
            report.steps,
            run.steps,
            report.halt.as_str(),
        ));
    }
    if report.steps > run.steps {
        return Ran::Deviates(format!(
            "applied where it should not: {} steps where the plan takes {}{cells}",
            report.steps, run.steps,
        ));
    }
    if observed
        .iter()
        .all(|(_, expected, value)| expected.agrees(value))
    {
        Ran::Conforms(run.status)
    } else {
        let expected = show(|(cell, expected, _)| format!("{cell} = {expected}"));
        Ran::Deviates(format!(
            "another value: {shown}, where the plan states {expected}"
        ))
    }
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

#[cfg(test)]
mod tests {
    use super::{Ground, untyped_tokens};

    /// A token read back as another sort's token of the same text (`word`, a `Word` the state
    /// holds, an `Id` the grammar reads) is the same print; another text is not.
    #[test]
    fn a_token_reads_back_by_its_text() {
        let token = |sort: &str, text: &str| Ground::Token {
            sort: sort.to_owned(),
            text: text.to_owned(),
        };
        let held = Ground::ctor("Cmd::Hold", vec![Ground::set(vec![token("Word", "word")])]);
        let read = Ground::ctor("Cmd::Hold", vec![Ground::set(vec![token("Id", "word")])]);
        assert_eq!(untyped_tokens(held.clone()), untyped_tokens(read));
        let other = Ground::ctor("Cmd::Hold", vec![Ground::set(vec![token("Word", "wa")])]);
        assert_ne!(untyped_tokens(held), untyped_tokens(other));
    }
}
