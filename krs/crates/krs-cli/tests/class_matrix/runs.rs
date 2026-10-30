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
    CellError, ConfigInputs, Halt, ProgramInput, RunOptions, RunReport, Semantics, SortRef,
    StateView, Value, ValueIndex, View,
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

/// Run `run` on `semantics`, the definition `krs run` loads, within `limit`.
pub fn run_case(semantics: &mut Semantics, run: &Run, limit: Duration) -> Ran {
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
    verdict(run, &report, &observed)
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
