//! `--trace-aggregate`: aggregate algorithm and phase spans in memory and write only the result.
//!
//! `--trace` writes one Chrome event per span, and some algorithm spans open once per call, so a
//! long execution writes gigabytes and spends much of its time writing them. This layer feeds the
//! same spans to [`SpanAggregator`], the aggregation `algo-graph join` applies to a Chrome trace,
//! so the join reads either file and applies one rule. A begin is taken when a span is created and
//! an end when it closes, the points at which `tracing_chrome`'s threaded style writes its events.

use std::{
    cell::OnceCell,
    collections::{BTreeMap, HashMap},
    fmt::Debug,
    fs, io,
    path::{Path, PathBuf},
    sync::{Arc, Mutex},
    time::Instant,
};

use k_rust_kore::trace_aggregate::{SpanAggregator, SpanKind};
use tracing::{
    Subscriber,
    field::{Field, Visit},
    span,
};
use tracing_subscriber::{Layer, layer::Context};

#[derive(Default)]
struct State {
    aggregator: SpanAggregator,
    events: usize,
    error: Option<String>,
    /// Name of every open span by id, for the end event and its nesting check.
    open: HashMap<u64, &'static str>,
    /// Counter deltas recorded on an open span by id; an `algo` span records them just before
    /// it closes.
    counters: HashMap<u64, String>,
}

impl State {
    fn apply(&mut self, event: impl FnOnce(&mut SpanAggregator, usize) -> Result<(), String>) {
        if self.error.is_some() {
            return;
        }
        let index = self.events;
        self.events += 1;
        if let Err(error) = event(&mut self.aggregator, index) {
            self.error = Some(error);
        }
    }
}

/// The layer that aggregates spans.
pub(crate) struct AggregateLayer {
    started: Instant,
    state: Arc<Mutex<State>>,
}

/// Writes the aggregate once every span has closed.
pub(crate) struct AggregateOutput {
    path: PathBuf,
    file: fs::File,
    rule: &'static str,
    state: Arc<Mutex<State>>,
}

/// Create the output file now, so a bad path fails before the command runs.
pub(crate) fn layer(
    path: &Path,
    rule: &'static str,
) -> Result<(AggregateLayer, AggregateOutput), io::Error> {
    let file = fs::File::create(path).map_err(|error| {
        io::Error::new(
            error.kind(),
            format!(
                "could not create trace aggregate file `{}`: {error}",
                path.display()
            ),
        )
    })?;
    let state = Arc::new(Mutex::new(State::default()));
    Ok((
        AggregateLayer {
            started: Instant::now(),
            state: state.clone(),
        },
        AggregateOutput {
            path: path.to_owned(),
            file,
            rule,
            state,
        },
    ))
}

impl AggregateOutput {
    /// Write the aggregate. Called after the subscriber is no longer the default, so no span
    /// can open or close meanwhile.
    pub(crate) fn write(self) -> Result<(), String> {
        let state = std::mem::take(&mut *self.state.lock().map_err(|_| "poisoned state")?);
        if let Some(error) = state.error {
            return Err(error);
        }
        let aggregate = state.aggregator.finish()?;
        serde_json::to_writer(io::BufWriter::new(self.file), &aggregate.to_json(self.rule))
            .map_err(|error| format!("could not write `{}`: {error}", self.path.display()))
    }
}

/// The `id`, `name`, and `counters` fields of an `algo` or `phase` span, as displayed.
#[derive(Default)]
struct Fields {
    id: Option<String>,
    name: Option<String>,
    counters: Option<String>,
}

impl Visit for Fields {
    fn record_str(&mut self, field: &Field, value: &str) {
        self.set(field, value.to_owned());
    }

    fn record_debug(&mut self, field: &Field, value: &dyn Debug) {
        // `tracing::field::display` values format through `Debug` as their `Display` text.
        self.set(field, format!("{value:?}"));
    }
}

impl Fields {
    /// What a span named `name` opens; `index` names it in an error.
    fn kind(self, name: &str, index: usize) -> Result<SpanKind, String> {
        let missing = |field: &str| format!("span {index} ({name}) has no {field} field");
        Ok(match name {
            "algo" => SpanKind::Algorithm(self.id.ok_or_else(|| missing("id"))?),
            "phase" => SpanKind::Phase(self.name.ok_or_else(|| missing("name"))?),
            _ => SpanKind::Other,
        })
    }

    fn set(&mut self, field: &Field, value: String) {
        match field.name() {
            "id" => self.id = Some(value),
            "name" => self.name = Some(value),
            "counters" => self.counters = Some(value),
            _ => {}
        }
    }
}

thread_local! {
    static THREAD: OnceCell<String> = const { OnceCell::new() };
}

/// Run `f` with a key naming the current thread.
fn with_thread_key<T>(f: impl FnOnce(&str) -> T) -> T {
    THREAD.with(|key| f(key.get_or_init(|| format!("{:?}", std::thread::current().id()))))
}

impl AggregateLayer {
    fn micros(&self) -> f64 {
        self.started.elapsed().as_nanos() as f64 / 1000.0
    }

    fn with_state(&self, f: impl FnOnce(&mut State)) {
        if let Ok(mut state) = self.state.lock() {
            f(&mut state);
        }
    }
}

impl<S: Subscriber> Layer<S> for AggregateLayer {
    fn on_new_span(&self, attributes: &span::Attributes<'_>, id: &span::Id, _: Context<'_, S>) {
        let mut fields = Fields::default();
        attributes.record(&mut fields);
        let name = attributes.metadata().name();
        let timestamp = self.micros();
        with_thread_key(|thread| {
            self.with_state(|state| {
                state.open.insert(id.into_u64(), name);
                state.apply(|aggregator, index| {
                    let kind = fields.kind(name, index)?;
                    aggregator.begin(index, thread, name, kind, timestamp)
                });
            });
        });
    }

    fn on_record(&self, id: &span::Id, values: &span::Record<'_>, _: Context<'_, S>) {
        let mut fields = Fields::default();
        values.record(&mut fields);
        if let Some(counters) = fields.counters {
            self.with_state(|state| {
                state.counters.insert(id.into_u64(), counters);
            });
        }
    }

    fn on_close(&self, id: span::Id, _: Context<'_, S>) {
        let timestamp = self.micros();
        with_thread_key(|thread| {
            self.with_state(|state| {
                let name = state.open.remove(&id.into_u64());
                let counters = state.counters.remove(&id.into_u64());
                state.apply(|aggregator, index| {
                    let name =
                        name.ok_or_else(|| format!("span {index} closes but never opened"))?;
                    // Counter names are identifiers, so they borrow from the recorded text.
                    let counters = match &counters {
                        Some(counters) => serde_json::from_str::<BTreeMap<&str, u64>>(counters)
                            .map_err(|error| {
                                format!("span {index} ({name}) has invalid counters: {error}")
                            })?,
                        None => BTreeMap::new(),
                    };
                    let counters = counters.into_iter().collect::<Vec<_>>();
                    aggregator.end(index, thread, Some(name), &counters, timestamp)
                });
            });
        });
    }
}
