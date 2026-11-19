//! A KRS corpus's projections (`[[projection]]`), resolved once per command: what each end
//! projection observes (its cells by Rust path, the functions by cell its `views` names, and the
//! observer they are resolved in), read from its keys, its observer prepared, every function
//! resolved and its comparison checked before anything runs, and the identity of its
//! observation.
//!
//! A view of an `[[implementation]]` that names a projection (`{ projection = NAME }`) is
//! compared under the projection's observation, looked up by name; a view written inline is an
//! anonymous projection, whose observation is read from its own keys
//! ([`Observation::of_view`]). The two differ in one default: a projection without `compare`
//! compares every observable leaf cell, so a cell the implementation omits is one the view
//! compares (`not-compared`, `omitted`), while an inline view without `compare` compares every
//! observable leaf cell the implementation states ([`Cells`]).
//!
//! A projection's `compare` names cells as the result record reads them ([`super::cells`]): by
//! Rust path, else by K name. Its observation holds them by path, the spelling every krs
//! comparison reads.
//!
//! A resolved view (krs-exec [`krs_exec::CellViews`]) holds the value index of the observer and
//! of the compared definition it was resolved in, and is evaluated in those instances only.
//! Both are loaded per thread, so resolving once per command does not give one resolved view: it
//! gives the functions, checked once, which each thread binds once in the instances it has
//! loaded ([`super::render::Observers::bound_views`]).
//!
//! The identity of a projection with `views` or `observer` is `{observer: {definition,
//! definition_ir}, views}` as `[observe]`'s is built ([`super::observe`]): the observer's name as
//! written (`null` for the definition) and its Definition IR digest, and the views by cell path as
//! written; with a named observer also `subject: {definition_ir}`, the definition's digest, since
//! a named observer reads the cells with the definition's declarations. A projection without
//! either is identified by its keys alone.

use std::collections::BTreeMap;
use std::sync::Arc;

use kink_flow::{FlowManifest, ProjectionKind, ProjectionSection, ViewSection};
use krs_exec::{CellInfo, Comparison, Semantics};
use serde_json::{Value, json};

use super::cells::CellNames;
use super::inputs::KrsInputs;
use super::render::{Observer, Observers, definition_digest};
use super::stop::Unbound;

/// Whether the cell at `path` is `cell` or lies inside it.
pub(super) fn within(path: &str, cell: &str) -> bool {
    path == cell
        || path
            .strip_prefix(cell)
            .is_some_and(|rest| rest.starts_with('.'))
}

/// The observable leaf cells, by declared path, none inside a cell of `left_out`.
pub(super) fn leaves<'c>(cells: &'c [CellInfo], left_out: &[&str]) -> Vec<&'c str> {
    cells
        .iter()
        .filter(|cell| cell.ty.is_some() && !cell.unobservable)
        .map(|cell| cell.path.as_str())
        .filter(|path| !left_out.iter().any(|out| within(path, out)))
        .collect()
}

/// Which cells an end observation compares.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Cells {
    /// The cells `compare` names, by declared path.
    Named(Vec<String>),
    /// Every observable leaf cell the implementation states: an inline view without `compare`.
    Stated,
    /// Every observable leaf cell: a projection without `compare`.
    Observable,
}

/// What an end observation reads: its cells, the function applied to each viewed cell (by
/// declared path), and the observer the functions are resolved in (`None`: the definition).
#[derive(Clone, Debug)]
pub(crate) struct Observation {
    pub(crate) cells: Cells,
    pub(crate) views: BTreeMap<String, String>,
    pub(crate) observer: Option<String>,
}

impl Observation {
    /// The observation an inline view's keys state (`compare`, `views`, `observer`).
    pub(crate) fn of_view(view: &ViewSection) -> Self {
        Self::of_keys(&view.front_end, Cells::Stated, str::to_owned)
    }

    /// The observation `projection` states, each cell of its `compare` read to its declared path
    /// as the record reads it (`names`).
    fn of_projection(projection: &ProjectionSection, names: &CellNames) -> Self {
        let mut keys = projection.front_end.clone();
        if let Some(compare) = &projection.compare {
            keys.insert("compare".into(), json!(compare));
        }
        Self::of_keys(&keys, Cells::Observable, |written| {
            names
                .read(written)
                .and_then(|name| names.path_of(name))
                .unwrap_or(written)
                .to_owned()
        })
    }

    fn of_keys(
        keys: &serde_json::Map<String, Value>,
        default: Cells,
        path: impl Fn(&str) -> String,
    ) -> Self {
        let cells = keys
            .get("compare")
            .and_then(Value::as_array)
            .map_or(default, |cells| {
                Cells::Named(cells.iter().filter_map(Value::as_str).map(path).collect())
            });
        let views = keys
            .get("views")
            .and_then(Value::as_object)
            .map(|views| {
                views
                    .iter()
                    .filter_map(|(cell, function)| {
                        Some((cell.clone(), function.as_str()?.to_owned()))
                    })
                    .collect()
            })
            .unwrap_or_default();
        let observer = keys
            .get("observer")
            .and_then(Value::as_str)
            .map(str::to_owned);
        Self {
            cells,
            views,
            observer,
        }
    }

    /// The cells the observation names before any implementation's `omits` applies: its
    /// `compare`; every observable leaf cell for a projection without one, none inside a cell of
    /// `left_out`; and only the viewed cells for an inline view without one, whose other cells
    /// are those the implementation states.
    pub(crate) fn named(&self, cells: &[CellInfo], left_out: &[&str]) -> Vec<String> {
        match &self.cells {
            Cells::Named(named) => named.clone(),
            Cells::Observable => leaves(cells, left_out)
                .into_iter()
                .map(str::to_owned)
                .collect(),
            Cells::Stated => self.views.keys().cloned().collect(),
        }
    }
}

/// One end projection resolved: its observation, its observer prepared (`None`: the definition),
/// and its identity where it has `views` or `observer`.
pub(crate) struct Projection {
    pub(crate) observation: Arc<Observation>,
    pub(crate) observer: Option<Arc<Observer>>,
    identity: Option<Value>,
}

/// A corpus's end projections, resolved once per command ([`Self::resolve`]).
#[derive(Default)]
pub(crate) struct KrsProjections {
    by_name: BTreeMap<String, Arc<Projection>>,
    /// How many projections had functions to resolve (`views` or `observer`): each was resolved
    /// once, here.
    resolved: usize,
}

impl KrsProjections {
    /// Every end projection of `manifest` (its declared ones, else the implicit `default`)
    /// resolved: its `compare` read by path (`names`), and, where it has `views` or `observer`,
    /// its observer prepared from `observers`, every function resolved in it and its comparison
    /// checked against `decoder`'s native compile, and its identity (`definition` the corpus's
    /// Definition IR). A projection no view names is resolved too: the manifest states it.
    ///
    /// # Errors
    ///
    /// `projection-unresolved`, naming the projection, with krs's refusal of its observer or of a
    /// view, or why the definition does not compile natively.
    pub(crate) fn resolve(
        manifest: &FlowManifest,
        decoder: &Arc<KrsInputs>,
        observers: &Observers,
        names: &CellNames,
        definition: &krs_ir_levels::DefinitionIr,
    ) -> Result<Self, Unbound> {
        let mut projections = Self::default();
        for projection in manifest.projections() {
            if projection.kind != ProjectionKind::End {
                continue;
            }
            let unresolved = |detail: String| Unbound {
                reason: "projection-unresolved",
                detail: format!("the projection `{}`: {detail}", projection.name),
            };
            let observation = Observation::of_projection(&projection, names);
            let observer = match &observation.observer {
                Some(name) => observers
                    .get(name)
                    .map_err(|reason| unresolved(format!("`observer`: {reason}")))?,
                None => None,
            };
            let identity = if projection.has_front_end_keys() {
                check(&observation, observer.as_ref(), decoder, observers).map_err(unresolved)?;
                projections.resolved += 1;
                Some(identity(&observation, observer.as_deref(), definition).map_err(unresolved)?)
            } else {
                None
            };
            projections.by_name.insert(
                projection.name.clone(),
                Arc::new(Projection {
                    observation: Arc::new(observation),
                    observer,
                    identity,
                }),
            );
        }
        Ok(projections)
    }

    /// The end projection `name`, resolved.
    pub(crate) fn get(&self, name: &str) -> Option<&Arc<Projection>> {
        self.by_name.get(name)
    }

    /// How many projections had functions to resolve, each once.
    pub(crate) const fn resolved(&self) -> usize {
        self.resolved
    }

    /// The identity of the observation of the projection `name` (module documentation), where it
    /// has `views` or `observer`: what kink-flow's documents name as the projection's
    /// `observation` ([`FlowManifest::with_projection_observation`]).
    pub(crate) fn observation(&self, name: &str) -> Option<Value> {
        self.by_name.get(name)?.identity.clone()
    }
}

/// Resolve every function of `observation` in its observer (`observer`, else the definition)
/// and check its comparison, as a view's are checked before any run: a function that does not
/// apply to its cell, or applies to a cell the observation does not compare, is refused.
fn check(
    observation: &Observation,
    observer: Option<&Arc<Observer>>,
    decoder: &KrsInputs,
    observers: &Observers,
) -> Result<(), String> {
    decoder.with_semantics("resolving a projection's views", |semantics| {
        let check = |loaded: Option<&Semantics>| {
            let views = observers
                .bound_views(semantics, loaded, &observation.views)
                .map_err(|error| error.to_string())?;
            let comparison = Comparison {
                compare: Some(observation.named(&semantics.cells(), &[])),
                views,
            };
            semantics
                .check_comparison(&comparison)
                .map_err(|error| error.to_string())
        };
        match observer {
            Some(observer) => observer.with_loaded(|loaded| check(Some(loaded))),
            None => check(None),
        }
    })
}

/// The identity of `observation` (module documentation), its observer `observer` (`None`: the
/// definition, `definition`).
fn identity(
    observation: &Observation,
    observer: Option<&Observer>,
    definition: &krs_ir_levels::DefinitionIr,
) -> Result<Value, String> {
    let digest = definition_digest(observer.map_or(definition, Observer::definition))?;
    let mut identity = json!({
        "observer": {"definition": observation.observer, "definition_ir": digest},
        "views": observation.views,
    });
    if observer.is_some() {
        identity["subject"] = json!({"definition_ir": definition_digest(definition)?});
    }
    Ok(identity)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// An inline view without `compare` compares the cells the implementation states, a
    /// projection without one every observable cell; a projection's `compare` is read by path.
    #[test]
    fn a_projection_without_compare_compares_every_observable_cell() {
        let manifest = FlowManifest::decode(
            "[spec]\nentry = \"calc.k\"\nmain_module = \"CALC\"\n\n[[projection]]\nname = \
             \"every\"\n\n[[projection]]\nname = \"regs\"\ncompare = [\"regs\"]\nviews = { \
             \"cpu.regs\" = \"View\" }\n",
            std::path::Path::new("corpus"),
        )
        .unwrap();
        let names = CellNames::default();
        let every =
            Observation::of_projection(manifest.projection("every").as_ref().unwrap(), &names);
        assert_eq!(every.cells, Cells::Observable);
        assert!(every.views.is_empty());
        let view = ViewSection {
            name: "whole".into(),
            required: false,
            channels: None,
            accepts: false,
            front_end: serde_json::Map::new(),
            projection: None,
        };
        assert_eq!(Observation::of_view(&view).cells, Cells::Stated);
        let regs = manifest.projection("regs").unwrap();
        // No cell is known here, so the entry stays as written; with the configuration's cells
        // the K name `regs` is read to its path, as the record reads it.
        let unknown = Observation::of_projection(&regs, &names);
        assert_eq!(unknown.cells, Cells::Named(vec!["regs".into()]));
        let known = CellNames::of_names(&[("cpu", "cpu"), ("cpu.regs", "regs")]);
        let regs = Observation::of_projection(&regs, &known);
        assert_eq!(regs.cells, Cells::Named(vec!["cpu.regs".into()]));
        assert_eq!(regs.views["cpu.regs"], "View");
        // The identity is the projection's where it has one, for kink-flow's documents.
        let identity = json!({"observer": {"definition": null, "definition_ir": "0"}, "views": {}});
        let mut projections = KrsProjections::default();
        for (name, identity) in [("regs", Some(identity.clone())), ("every", None)] {
            projections.by_name.insert(
                name.to_owned(),
                Arc::new(Projection {
                    observation: Arc::new(every.clone()),
                    observer: None,
                    identity,
                }),
            );
        }
        assert_eq!(projections.observation("regs"), Some(identity));
        assert_eq!(projections.observation("every"), None);
        assert_eq!(projections.observation("nope"), None);
    }
}
